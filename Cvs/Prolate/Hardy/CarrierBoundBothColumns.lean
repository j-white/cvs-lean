import Mathlib
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CentralRungExpansion
import Cvs.Prolate.Hardy.ColumnRungCoefficients
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.ExteriorSincColumns
import Cvs.Prolate.Hardy.FilteredColumnCarriers
import Cvs.Prolate.Hardy.FourierDefectColumns
import Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude
import Cvs.Prolate.SincTopIsRung

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The carrier bound controls both exterior columns, the filtered one with a `c^{−1/4}` factor

If `‖J Re(A e^{icx})|_I‖ ≤ C sup_E |A|` for `A` differentiable on `D ⊆ {|z| < 1}`, `E ⊆ {|Re| ≤ L, |Im| ≤ B}`,
`L + B < 1`, then `‖JQe_u‖ ≤ C/(π(u − L − B))` and `‖JQFe_u‖ ≤ C K_c (u − 1)^{−3/4}`, `K_c = O(c^{−1/4})`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open Complex (I)
open ComplexConjugate

namespace Cvs.Prolate.Hardy.CarrierBoundBothColumns
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.CentralResolventTrace (L2I)
open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R extS extO colA colF)
open Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude (lapG)
open Cvs.Prolate.Hardy.FilteredColumnCarriers (kap posAmp negAmp)

/-- The closed ellipse `E = {z : (Re z/L)² + (Im z/B)² ≤ 1}`. -/
def ellipse (L B : ℝ) : Set ℂ := {z | (z.re / L) ^ 2 + (z.im / B) ^ 2 ≤ 1}

/-- **The carrier bound** of HARDY_EXTENSION.md eq. (7): `‖J Re(A(x)e^{icx})|_I‖ ≤ C·M` for every `A` complex
differentiable at each point of `D` with `|A| ≤ M` on `E`. -/
def CarrierBound (c : ℝ) (D E : Set ℂ) (C : ℝ) (J : L2I →L[ℝ] L2R) : Prop :=
  ∀ (A : ℂ → ℂ) (M : ℝ), (∀ z ∈ D, DifferentiableAt ℂ A z) → (∀ z ∈ E, ‖A z‖ ≤ M) → ∀ f : L2I,
      (f : ℝ → ℝ) =ᵐ[volume.restrict Cvs.Prolate.Gram.CentralResolventTrace.cI] (fun x : ℝ => (A x * Complex.exp (I * (c * x))).re) →
        ‖J f‖ ≤ C * M

theorem abs_re_le {L B : ℝ} (hL : 0 < L) {z : ℂ} (hz : z ∈ ellipse L B) : |z.re| ≤ L := by
  have h : (z.re / L) ^ 2 ≤ 1 := le_trans (le_add_of_nonneg_right (sq_nonneg _)) hz
  rw [sq_le_one_iff_abs_le_one, abs_div, abs_of_pos hL, div_le_one hL] at h
  exact h

theorem abs_im_le {L B : ℝ} (hB : 0 < B) {z : ℂ} (hz : z ∈ ellipse L B) : |z.im| ≤ B := by
  have h : (z.im / B) ^ 2 ≤ 1 := le_trans (le_add_of_nonneg_left (sq_nonneg _)) hz
  rw [sq_le_one_iff_abs_le_one, abs_div, abs_of_pos hB, div_le_one hB] at h
  exact h

theorem norm_le_of_box {L B : ℝ} {z : ℂ} (hre : |z.re| ≤ L) (him : |z.im| ≤ B) : ‖z‖ ≤ L + B :=
  (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hre him)

/-! ### The central column `Qe_u` -/

theorem differentiableOn_amp {c u : ℝ} (hu : 1 < u) :
    DifferentiableOn ℂ (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u) (Metric.ball 0 1) := by
  unfold Cvs.Prolate.Hardy.ExteriorSincColumns.amp
  have h1 : DifferentiableOn ℂ (fun z : ℂ => (u : ℂ) * (Real.sin (c * u) : ℂ) + I * z * (Real.cos (c * u) : ℂ))
      (Metric.ball 0 1) := by fun_prop
  have h2 : DifferentiableOn ℂ (fun z : ℂ => (π : ℂ) * ((u : ℂ) ^ 2 - z ^ 2)) (Metric.ball 0 1) := by fun_prop
  refine DifferentiableOn.div (c := fun z : ℂ => (u : ℂ) * (Real.sin (c * u) : ℂ) + I * z * (Real.cos (c * u) : ℂ))
    (d := fun z : ℂ => (π : ℂ) * ((u : ℂ) ^ 2 - z ^ 2)) h1 h2 fun z hz => ?_
  rw [Metric.mem_ball, dist_zero_right] at hz
  refine mul_ne_zero (by exact_mod_cast Real.pi_pos.ne') fun h => ?_
  have h2 : z ^ 2 = (u : ℂ) ^ 2 := by linear_combination -h
  have := congrArg norm h2
  rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
  nlinarith [norm_nonneg z]

/-- `‖JQe_u‖ ≤ C/(π(u − (L + B)))` under the carrier bound. -/
theorem norm_J_colA_le {c L B C u : ℝ} {D E : Set ℂ} (hD : D ⊆ Metric.ball 0 1)
    (hE : ∀ z ∈ E, |z.re| ≤ L ∧ |z.im| ≤ B) (hLB : L + B < 1) {J : L2I →L[ℝ] L2R}
    (hJ : CarrierBound c D E C J) (hu : 1 < u) : ‖J (colA c u)‖ ≤ C * (1 / (π * (u - (L + B)))) := by
  rw [colA, dite_eq_left hu]
  refine hJ (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u) _ (fun z hz => (differentiableOn_amp hu).differentiableAt
    (Metric.isOpen_ball.mem_nhds (hD hz)))
    (fun z hz => Cvs.Prolate.Hardy.ExteriorSincColumns.norm_amp_le (norm_le_of_box (hE z hz).1 (hE z hz).2) (by linarith)) _ ?_
  · filter_upwards [Cvs.Prolate.Hardy.CentralRungExpansion.coeFn_qI (Cvs.Prolate.Hardy.ColumnRungCoefficients.continuous_eC c hu), ae_restrict_mem measurableSet_Icc] with x hx hmem
    rw [hx, Cvs.Prolate.Hardy.ExteriorSincColumns.re_amp_mul_exp]
    have hx1 : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    rw [Cvs.Prolate.Hardy.ColumnRungCoefficients.eC, Cvs.Prolate.SincTopIsRung.clampExt_of_mem hx1, Cvs.Prolate.Hardy.FourierDefectColumns.evenCol]
    exact Cvs.Prolate.Hardy.ExteriorSincColumns.even_sinc (by linarith [hmem.2]) (by linarith [hmem.1])

/-! ### The filtered column `QFe_u` as one positive carrier -/

/-- The single positive-carrier amplitude `P_u(z) + conj N_u(conj z)` of `QFe_u`. -/
def oddAmp (c u : ℝ) (z : ℂ) : ℂ := posAmp c u z + conj (negAmp c u (conj z))

/-- The strip `|Re z| < 1`. -/
def strip : Set ℂ := {z | -1 < z.re ∧ z.re < 1}

theorem isOpen_strip : IsOpen strip := by
  change IsOpen ({z : ℂ | -1 < z.re} ∩ {z : ℂ | z.re < 1})
  exact (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)

theorem differentiableOn_lapG_add {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    DifferentiableOn ℂ (fun z => lapG c a (1 + z)) strip :=
  (Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude.differentiableOn_lapG hc ha).comp (by fun_prop) fun z hz => by
    show 0 < (1 + z).re; simp only [Complex.add_re, Complex.one_re]; linarith [hz.1]

theorem differentiableOn_lapG_sub {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    DifferentiableOn ℂ (fun z => lapG c a (1 - z)) strip :=
  (Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude.differentiableOn_lapG hc ha).comp (by fun_prop) fun z hz => by
    show 0 < (1 - z).re; simp only [Complex.sub_re, Complex.one_re]; linarith [hz.2]

theorem differentiableOn_posAmp {c u : ℝ} (hc : 0 < c) (hu : 1 < u) : DifferentiableOn ℂ (posAmp c u) strip := by
  unfold posAmp
  exact DifferentiableOn.const_mul (((differentiableOn_lapG_add hc (by linarith)).const_mul _).sub
    ((differentiableOn_lapG_sub hc (by linarith)).const_mul _)) _

theorem differentiableOn_negAmp {c u : ℝ} (hc : 0 < c) (hu : 1 < u) : DifferentiableOn ℂ (negAmp c u) strip := by
  unfold negAmp
  exact DifferentiableOn.const_mul (((differentiableOn_lapG_sub hc (by linarith)).const_mul _).sub
    ((differentiableOn_lapG_add hc (by linarith)).const_mul _)) _

theorem conj_mem_strip {z : ℂ} (hz : z ∈ strip) : conj z ∈ strip := by
  simpa [strip] using hz

theorem differentiableOn_oddAmp {c u : ℝ} (hc : 0 < c) (hu : 1 < u) : DifferentiableOn ℂ (oddAmp c u) strip := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  refine ((differentiableOn_posAmp hc hu).differentiableAt (isOpen_strip.mem_nhds hz)).add ?_
  have h : DifferentiableAt ℂ (negAmp c u) (conj z) :=
    (differentiableOn_negAmp hc hu).differentiableAt (isOpen_strip.mem_nhds (conj_mem_strip hz))
  exact (differentiableAt_conj_conj_iff (f := negAmp c u)).2 h

theorem ball_subset_strip : Metric.ball (0 : ℂ) 1 ⊆ strip := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have h2 : |z.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm z) hz
  exact ⟨by linarith [(abs_lt.1 h2).1], (abs_lt.1 h2).2⟩

theorem norm_exp_I_mul (r : ℝ) : ‖Complex.exp (I * r)‖ = 1 := Complex.norm_exp_I_mul_ofReal r

theorem norm_exp_neg_I_mul (r : ℝ) : ‖Complex.exp (-(I * r))‖ = 1 := by
  rw [show -(I * r) = I * ((-r : ℝ) : ℂ) by push_cast; ring]; exact norm_exp_I_mul _

/-- The `c`-scale `K_c = 8Γ(3/4)κ_c(1/(c(1 − L − B)))^{3/4}` of the filtered-column bound. -/
def scaleK (c L B : ℝ) : ℝ := 8 * Gamma (3 / 4) * kap c * (1 / (c * (1 - L - B))) ^ (3 / 4 : ℝ)

theorem norm_lapG_box {c a L B : ℝ} (hc : 0 < c) (ha : 0 < a) (hLB : L + B < 1)
    {z : ℂ} (hre : |z.re| ≤ L) (him : |z.im| ≤ B) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ‖lapG c a (1 + s * z)‖ ≤ 2 * Gamma (3 / 4) * (1 / (c * (1 - L - B))) ^ (3 / 4 : ℝ) * (1 / a) ^ (3 / 4 : ℝ) := by
  refine Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude.norm_lapG_le hc ha (by linarith) ?_
  have hre := abs_le.1 hre
  rcases hs with rfl | rfl
  · simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, Complex.ofReal_one, one_mul,
      zero_add]
    linarith
  · simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, Complex.ofReal_neg,
      Complex.ofReal_one, neg_mul, one_mul, Complex.neg_re, Complex.neg_im, zero_add, abs_neg]
    linarith

theorem one_div_rpow_le {u : ℝ} (hu : 1 < u) :
    (1 / (u + 1)) ^ (3 / 4 : ℝ) ≤ (1 / (u - 1)) ^ (3 / 4 : ℝ) :=
  Real.rpow_le_rpow (by positivity) (one_div_le_one_div_of_le (by linarith) (by linarith)) (by norm_num)

theorem norm_carrierAmp_le {c u L B : ℝ} (hc : 0 < c) (hu : 1 < u) (hLB : L + B < 1)
    {z : ℂ} (hre : |z.re| ≤ L) (him : |z.im| ≤ B) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ‖kap c * I * (Complex.exp (I * (c * (1 - u))) * lapG c (u - 1) (1 + s * z) -
      Complex.exp (-(I * (c * (1 + u)))) * lapG c (u + 1) (1 + -s * z))‖ ≤ scaleK c L B / 2 *
        (1 / (u - 1)) ^ (3 / 4 : ℝ) := by
  have hk : 0 ≤ kap c := by unfold kap; positivity
  have h1 := norm_lapG_box hc (by linarith : 0 < u - 1) hLB hre him s hs
  have h2 := norm_lapG_box hc (by linarith : 0 < u + 1) hLB hre him (-s)
    (by rcases hs with rfl | rfl <;> norm_num)
  have h3 := one_div_rpow_le hu
  have hG := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
  have hP : 0 ≤ (1 / (c * (1 - L - B))) ^ (3 / 4 : ℝ) := by
    have : 0 < 1 - L - B := by linarith
    positivity
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk]
  have e1 : ‖Complex.exp (I * (c * (1 - u)))‖ = 1 := by
    rw [show I * ((c : ℂ) * (1 - u)) = I * ((c * (1 - u) : ℝ) : ℂ) by push_cast; ring]; exact norm_exp_I_mul _
  have e2 : ‖Complex.exp (-(I * (c * (1 + u))))‖ = 1 := by
    rw [show -(I * ((c : ℂ) * (1 + u))) = -(I * ((c * (1 + u) : ℝ) : ℂ)) by push_cast; ring]
    exact norm_exp_neg_I_mul _
  have ht := norm_sub_le (Complex.exp (I * (c * (1 - u))) * lapG c (u - 1) (1 + s * z))
    (Complex.exp (-(I * (c * (1 + u)))) * lapG c (u + 1) (1 + -s * z))
  rw [norm_mul, norm_mul, e1, e2, one_mul, one_mul] at ht
  have hneg : ((-s : ℝ) : ℂ) = -(s : ℂ) := by push_cast; ring
  rw [hneg] at h2
  unfold scaleK
  set P := (1 / (c * (1 - L - B))) ^ (3 / 4 : ℝ)
  set Q := (1 / (u - 1)) ^ (3 / 4 : ℝ)
  set R := (1 / (u + 1)) ^ (3 / 4 : ℝ)
  have hR : 0 ≤ R := by positivity
  have hsum : ‖Complex.exp (I * (c * (1 - u))) * lapG c (u - 1) (1 + s * z) -
      Complex.exp (-(I * (c * (1 + u)))) * lapG c (u + 1) (1 + -s * z)‖ ≤ 4 * Gamma (3 / 4) * P * Q := by
    have : 2 * Gamma (3 / 4) * P * R ≤ 2 * Gamma (3 / 4) * P * Q :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  calc kap c * ‖Complex.exp (I * (c * (1 - u))) * lapG c (u - 1) (1 + s * z) -
        Complex.exp (-(I * (c * (1 + u)))) * lapG c (u + 1) (1 + -s * z)‖
      ≤ kap c * (4 * Gamma (3 / 4) * P * Q) := mul_le_mul_of_nonneg_left hsum hk
    _ = 8 * Gamma (3 / 4) * kap c * P / 2 * Q := by ring

/-- The amplitude bound `|P_u(z) + conj N_u(conj z)| ≤ K_c(1/(u − 1))^{3/4}` on `|Re z| ≤ L`, `|Im z| ≤ B`. -/
theorem norm_oddAmp_le {c u L B : ℝ} (hc : 0 < c) (hu : 1 < u) (hLB : L + B < 1)
    {z : ℂ} (hre : |z.re| ≤ L) (him : |z.im| ≤ B) : ‖oddAmp c u z‖ ≤ scaleK c L B * (1 / (u - 1)) ^ (3 / 4 : ℝ) := by
  have hre' : |(conj z).re| ≤ L := by rwa [Complex.conj_re]
  have him' : |(conj z).im| ≤ B := by rwa [Complex.conj_im, abs_neg]
  have h1 := norm_carrierAmp_le hc hu hLB hre him 1 (Or.inl rfl)
  have h2 := norm_carrierAmp_le hc hu hLB hre' him' (-1) (Or.inr rfl)
  have e1 : posAmp c u z = kap c * I * (Complex.exp (I * (c * (1 - u))) * lapG c (u - 1) (1 + ((1 : ℝ) : ℂ) * z) -
      Complex.exp (-(I * (c * (1 + u)))) * lapG c (u + 1) (1 + -((1 : ℝ) : ℂ) * z)) := by
    unfold posAmp; simp [sub_eq_add_neg]
  have e2 : negAmp c u (conj z) = kap c * I * (Complex.exp (I * (c * (1 - u))) *
      lapG c (u - 1) (1 + ((-1 : ℝ) : ℂ) * conj z) -
      Complex.exp (-(I * (c * (1 + u)))) * lapG c (u + 1) (1 + -((-1 : ℝ) : ℂ) * conj z)) := by
    unfold negAmp; simp [sub_eq_add_neg]
  unfold oddAmp
  calc ‖posAmp c u z + conj (negAmp c u (conj z))‖ ≤ ‖posAmp c u z‖ + ‖negAmp c u (conj z)‖ := by
        rw [← Complex.norm_conj (negAmp c u (conj z))]; exact norm_add_le _ _
    _ ≤ scaleK c L B / 2 * (1 / (u - 1)) ^ (3 / 4 : ℝ) + scaleK c L B / 2 * (1 / (u - 1)) ^ (3 / 4 : ℝ) := by
        rw [e1, e2]; exact add_le_add h1 h2
    _ = _ := by ring

/-- On the real line the filtered column is the positive carrier of `P_u + conj N_u(conj ·)`. -/
theorem Fop_eC_eq_oddAmp {c u x : ℝ} (hc : 0 < c) (hu : 1 < u) (hx : |x| < 1) :
    Cvs.Prolate.Hardy.FourierDefectColumns.Fop c (Cvs.Prolate.Hardy.ColumnRungCoefficients.eC c u) x = (oddAmp c u x * Complex.exp (I * (c * x))).re := by
  rw [Cvs.Prolate.Hardy.FilteredColumnCarriers.Fop_eC_eq hc hu hx, oddAmp, add_mul, Complex.add_re]
  congr 1
  have : Complex.exp (I * (c * x)) = conj (Complex.exp (-(I * (c * x)))) := by
    rw [← Complex.exp_conj]; congr 1
    simp [Complex.conj_ofReal]
  rw [this, Complex.conj_ofReal, ← map_mul, Complex.conj_re]

/-- `‖JQFe_u‖ ≤ C K_c(1/(u − 1))^{3/4}` under the carrier bound. -/
theorem norm_J_colF_le {c L B C u : ℝ} {D E : Set ℂ} (hc : 0 < c) (hD : D ⊆ Metric.ball 0 1)
    (hE : ∀ z ∈ E, |z.re| ≤ L ∧ |z.im| ≤ B) (hLB : L + B < 1)
    {J : L2I →L[ℝ] L2R} (hJ : CarrierBound c D E C J) (hu : 1 < u) :
    ‖J (colF c u)‖ ≤ C * (scaleK c L B * (1 / (u - 1)) ^ (3 / 4 : ℝ)) := by
  rw [colF, dite_eq_left hu]
  refine hJ (oddAmp c u) _ (fun z hz => (differentiableOn_oddAmp hc hu).differentiableAt
    (isOpen_strip.mem_nhds (ball_subset_strip (hD hz))))
    (fun z hz => norm_oddAmp_le hc hu hLB (hE z hz).1 (hE z hz).2) _ ?_
  filter_upwards [Cvs.Prolate.Hardy.CentralRungExpansion.coeFn_qI (Cvs.Prolate.Hardy.FourierDefectColumns.continuous_Fop c (Cvs.Prolate.Hardy.ColumnRungCoefficients.continuous_eC c hu)),
    ae_restrict_mem measurableSet_Icc] with x hx hmem
  rw [hx]
  exact Fop_eC_eq_oddAmp hc hu (abs_lt.2 ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)

end Cvs.Prolate.Hardy.CarrierBoundBothColumns

end
