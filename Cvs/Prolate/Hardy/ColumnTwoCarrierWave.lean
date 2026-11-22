import Mathlib
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CarrierNegativeFreqRate
import Cvs.Prolate.Hardy.CarrierNegativeFrequencies
import Cvs.Prolate.Hardy.CarrierUpperHalfPlane
import Cvs.Prolate.Hardy.CentralRungExpansion
import Cvs.Prolate.Hardy.ColumnRungCoefficients
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.ExteriorSincColumns
import Cvs.Prolate.Hardy.FourierDefectColumns
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.LipSymmetricPieces
import Cvs.Prolate.Hardy.ReflectedWaveSplit
import Cvs.Prolate.Hardy.SpectrumCosineHighpass
import Cvs.Prolate.SincTopIsRung
import Cvs.Upstream.FourierLpConjReflect
import Cvs.Upstream.HardyProjectionReal

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `J_c` on an exterior column is the reflected two-carrier wave plus five Hardy errors

For `e_u = Re[A_u e^{icx}]` and `h = 1_I A_u e^{icx}/w`, `J_c(Qe_u) = Re[w(P₊h + conj(h − P₊h))]`; with the lips cut at
`½ < α ≤ x₀ ≤ ℓ ≤ x₁ ≤ 3/5`, `J_c(Qe_u)` differs from `Re[w(h + m − m̄)]`, `m = 1_{symS ½ ℓ}H`, by at most twice the
sum of `‖(1 − P₊)k‖`, `‖(1 − P₊)m₁‖`, `‖P₊m₂‖` and the two remainders.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.Hardy.ColumnTwoCarrierWave
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.CentralResolventTrace (L2I)
open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI)
open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R colA)
open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C posProj mulOp reLp ofRealLp ext0 wR wInvI hardyJ)
open Cvs.Upstream.FourierLpConjReflect (conjLp)
open Cvs.Prolate.Hardy.CarrierNegativeFrequencies (carH kC)
open Cvs.Prolate.Hardy.LipSymmetricPieces (symS)

open Classical in
/-- The class in `L²(ℝ, ℂ)` of a function (zero if it is not square integrable). -/
def toL2 (f : ℝ → ℂ) : L2C := if h : MemLp f 2 (volume : Measure ℝ) then h.toLp f else 0

theorem toL2_eq {f : ℝ → ℂ} (h : MemLp f 2 (volume : Measure ℝ)) : toL2 f = h.toLp f := by
  rw [toL2, dite_eq_left h]

theorem coeFn_toL2 {f : ℝ → ℂ} (h : MemLp f 2 (volume : Measure ℝ)) : (toL2 f : ℝ → ℂ) =ᵐ[volume] f := by
  rw [toL2_eq h]; exact h.coeFn_toLp

/-! ### The amplitude of an exterior column -/

theorem amp_ne {u : ℝ} (hu : 1 < u) {z : ℂ} (hz : ‖z‖ < 1) : (u : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
  intro h
  have : ‖z‖ ^ 2 = u ^ 2 := by
    have e : z ^ 2 = (u : ℂ) ^ 2 := by linear_combination -h
    have := congrArg norm e
    rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
    exact this
  nlinarith [norm_nonneg z]

theorem differentiableOn_amp (c : ℝ) {u : ℝ} (hu : 1 < u) :
    DifferentiableOn ℂ (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u) (Metric.ball 0 1) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  unfold Cvs.Prolate.Hardy.ExteriorSincColumns.amp
  have hf : DifferentiableAt ℂ (fun z : ℂ => (u : ℂ) * (Real.sin (c * u) : ℂ) + Complex.I * z * (Real.cos (c * u) : ℂ)) z := by
    fun_prop
  have hg : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) * ((u : ℂ) ^ 2 - z ^ 2)) z := by fun_prop
  have hne : (π : ℂ) * ((u : ℂ) ^ 2 - z ^ 2) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_pos.ne') (amp_ne hu hz)
  exact (DifferentiableAt.div (c := fun z : ℂ => (u : ℂ) * (Real.sin (c * u) : ℂ) + Complex.I * z * (Real.cos (c * u) : ℂ))
    (d := fun z : ℂ => (π : ℂ) * ((u : ℂ) ^ 2 - z ^ 2)) hf hg hne).differentiableWithinAt

theorem differentiableAt_amp (c : ℝ) {u : ℝ} (hu : 1 < u) {z : ℂ} (hz : ‖z‖ ≤ 3 / 5) :
    DifferentiableAt ℂ (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u) z :=
  (differentiableOn_amp c hu).differentiableAt (Metric.isOpen_ball.mem_nhds (by
    rw [Metric.mem_ball, dist_zero_right]; linarith))

/-! ### The pieces in `L²` -/

theorem memLp_cI_of (c : ℝ) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z) :
    MemLp (cI.indicator (carH c A)) 2 (volume : Measure ℝ) := by
  have hc : ContinuousOn (carH c A) cI :=
    (Cvs.Prolate.Hardy.CarrierNegativeFreqRate.continuousOn_carH c hA).mono (Icc_subset_Icc (by norm_num) (by norm_num))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 (MemLp.of_bound
    (hc.aestronglyMeasurable measurableSet_Icc) C ?_)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

theorem memLp_symS_of (c : ℝ) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 3 / 5) : MemLp ((symS a b).indicator (carH c A)) 2 (volume : Measure ℝ) := by
  rw [Cvs.Prolate.Hardy.LipSymmetricPieces.indicator_symS ha]
  exact (Cvs.Prolate.Hardy.CarrierNegativeFreqRate.integrable_memLp_indicator ((Cvs.Prolate.Hardy.CarrierNegativeFreqRate.continuousOn_carH c hA).mono
      (Icc_subset_Icc (by linarith) hb))).2.add
    (Cvs.Prolate.Hardy.CarrierNegativeFreqRate.integrable_memLp_indicator ((Cvs.Prolate.Hardy.CarrierNegativeFreqRate.continuousOn_carH c hA).mono
      (Icc_subset_Icc (by linarith) (by linarith)))).2

theorem memLp_cI (c : ℝ) {u : ℝ} (hu : 1 < u) :
    MemLp (cI.indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))) 2 (volume : Measure ℝ) :=
  memLp_cI_of c fun _ hz => differentiableAt_amp c hu hz

theorem memLp_symS (c : ℝ) {u : ℝ} (hu : 1 < u) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 3 / 5) :
    MemLp ((symS a b).indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))) 2 (volume : Measure ℝ) :=
  memLp_symS_of c (fun _ hz => differentiableAt_amp c hu hz) ha hb

theorem memLp_kC (c : ℝ) {u : ℝ} (hu : 1 < u) : MemLp (kC c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u)) 2 (volume : Measure ℝ) :=
  Cvs.Prolate.Hardy.CarrierNegativeFreqRate.memLp_kC c fun _ hz => differentiableAt_amp c hu hz

/-- The interior carrier `h = 1_I H` in `L²`. -/
def hI (c u : ℝ) : L2C := toL2 (cI.indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u)))

/-- The lip piece `1_{symS a b}H` in `L²`. -/
def piece (c u a b : ℝ) : L2C := toL2 ((symS a b).indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u)))

/-- The fixed-ellipse carrier `k = 1_{(−3/5, 3/5]}H` in `L²`. -/
def kL2 (c u : ℝ) : L2C := toL2 (kC c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))

theorem piece_split (c : ℝ) {u : ℝ} (hu : 1 < u) {a b d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    (hd : d ≤ 3 / 5) : piece c u a d = piece c u a b + piece c u b d := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toL2 (memLp_symS c hu ha hd), coeFn_toL2 (memLp_symS c hu ha (hbd.trans hd)),
    coeFn_toL2 (memLp_symS c hu (ha.trans hab) hd), Lp.coeFn_add (piece c u a b) (piece c u b d)]
    with x h1 h2 h3 h4
  simp only [piece] at h4 ⊢
  rw [h1, h4, Pi.add_apply, h2, h3, Cvs.Prolate.Hardy.LipSymmetricPieces.indicator_symS_split ha hab hbd]
  rfl

theorem hI_eq (c : ℝ) {u : ℝ} (hu : 1 < u) : hI c u = kL2 c u - piece c u (1 / 2) (3 / 5) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toL2 (memLp_cI c hu), coeFn_toL2 (memLp_kC c hu),
    coeFn_toL2 (memLp_symS c hu (a := 1 / 2) (by norm_num) le_rfl), Lp.coeFn_sub (kL2 c u) (piece c u (1 / 2) (3 / 5)),
    Cvs.Prolate.Hardy.SpectrumCosineHighpass.ae_ne (-(1 / 2))] with x h1 h2 h3 h4 hx
  simp only [hI, kL2, piece] at h4 ⊢
  rw [h1, h4, Pi.sub_apply, h2, h3, ← Cvs.Prolate.Hardy.LipSymmetricPieces.kC_sub_indicator c _ hx]
  ring

/-! ### `J_c` on the column -/

theorem eC_eq_re {c u x : ℝ} (hu : 1 < u) (hx : x ∈ cI) :
    Cvs.Prolate.Hardy.ColumnRungCoefficients.eC c u x = (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u x * Complex.exp (Complex.I * (c * x))).re := by
  have hx1 : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 : x - u ≠ 0 := by linarith [hx.2]
  have h2 : -x - u ≠ 0 := by linarith [hx.1]
  rw [Cvs.Prolate.Hardy.ColumnRungCoefficients.eC, Cvs.Prolate.SincTopIsRung.clampExt_of_mem hx1, Cvs.Prolate.Hardy.FourierDefectColumns.evenCol, Cvs.Prolate.Hardy.ExteriorSincColumns.even_sinc h1 h2, Cvs.Prolate.Hardy.ExteriorSincColumns.re_amp_mul_exp]

/-- The real input `1_I f / w = (h + h̄)/2` for `f = Re(Ae^{icx})` on `I`. -/
theorem input_eq_of {c : ℝ} (hc : 0 ≤ c) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z)
    {f : L2I} (hf : (f : ℝ → ℝ) =ᵐ[volume.restrict cI] fun x : ℝ => (A x * Complex.exp (Complex.I * (c * x))).re) :
    mulOp (wInvI (c / 2)) (ofRealLp (ext0 f)) =
      (1 / 2 : ℝ) • (toL2 (cI.indicator (carH c A)) + conjLp (toL2 (cI.indicator (carH c A)))) := by
  have hb : 0 ≤ c / 2 := by positivity
  set H := toL2 (cI.indicator (carH c A))
  have hE : (ext0 f : ℝ → ℝ) =ᵐ[volume] cI.indicator (f : ℝ → ℝ) :=
    MemLp.coeFn_toLp (Cvs.Prolate.Hardy.HardyExtensionOperator.memLp_indicator_L2I f)
  have hE' := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1 hf
  have hFc : (ofRealLp (ext0 f) : ℝ → ℂ) =ᵐ[volume] fun x => ((ext0 f : ℝ → ℝ) x : ℂ) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  refine Lp.ext ?_
  filter_upwards [Cvs.Upstream.HardyProjectionReal.coeFn_mulOp (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wInvI hb) (ofRealLp (ext0 f)), hFc, hE, hE',
    Lp.coeFn_smul (1 / 2 : ℝ) (H + conjLp H), Lp.coeFn_add H (conjLp H),
    Cvs.Upstream.FourierLpConjReflect.coeFn_conjLp H, coeFn_toL2 (memLp_cI_of c hA)] with x h1 h2 h3 h4 h5 h6 h7 h8
  rw [h1, h2, h3, h4, h5, Pi.smul_apply, h6, Pi.add_apply, h7]
  simp only [H] at h8 ⊢
  rw [h8]
  by_cases hx : x ∈ cI
  · rw [indicator_of_mem hx, indicator_of_mem hx, Cvs.Prolate.Hardy.HardyExtensionOperator.wInvI, indicator_of_mem hx]
    set r := Real.exp (-(c / 2) * (Cvs.Prolate.Hardy.HardyExtensionOperator.sS x).im)
    have hw : wR (c / 2) x = (r : ℂ) := Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wR_on_I hx
    unfold carH
    rw [hw, ← Complex.ofReal_inv, show Complex.I * (c : ℂ) * x = Complex.I * (c * x) by ring]
    set z := A x * Complex.exp (Complex.I * (c * x))
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
    · simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp

/-- **`J_c` on a carrier input**: `J_c f = Re[w(P₊h + conj(h − P₊h))]` for `f = Re(Ae^{icx})` on `I`. -/
theorem hardyJ_eq_of {c : ℝ} (hc : 0 ≤ c) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z)
    {f : L2I} (hf : (f : ℝ → ℝ) =ᵐ[volume.restrict cI] fun x : ℝ => (A x * Complex.exp (Complex.I * (c * x))).re) :
    hardyJ c f = reLp (mulOp (wR (c / 2)) (posProj (toL2 (cI.indicator (carH c A))) +
      conjLp (toL2 (cI.indicator (carH c A)) - posProj (toL2 (cI.indicator (carH c A)))))) := by
  have hJ : hardyJ c f =
      (2 : ℝ) • reLp (mulOp (wR (c / 2)) (posProj (mulOp (wInvI (c / 2)) (ofRealLp (ext0 f))))) := rfl
  rw [hJ, input_eq_of hc hA hf, ContinuousLinearMap.map_smul_of_tower, map_add, Cvs.Prolate.Hardy.ReflectedWaveSplit.posProj_conjLp,
    ContinuousLinearMap.map_smul_of_tower, map_smul, smul_smul]
  norm_num

/-- **`J_c` on an exterior column**: `J_c(Qe_u) = Re[w(P₊h + conj(h − P₊h))]`. -/
theorem hardyJ_colA (c : ℝ) (hc : 0 ≤ c) {u : ℝ} (hu : 1 < u) :
    hardyJ c (colA c u) =
      reLp (mulOp (wR (c / 2)) (posProj (hI c u) + conjLp (hI c u - posProj (hI c u)))) := by
  refine hardyJ_eq_of hc (fun _ hz => differentiableAt_amp c hu hz) ?_
  have hf : (colA c u : ℝ → ℝ) =ᵐ[volume.restrict cI] Cvs.Prolate.Hardy.ColumnRungCoefficients.eC c u := by
    simp only [colA, dite_eq_left hu]; exact Cvs.Prolate.Hardy.CentralRungExpansion.coeFn_qI _
  filter_upwards [hf, ae_restrict_mem measurableSet_Icc] with x h1 h2
  rw [h1, eC_eq_re hu h2]

/-- The two-carrier wave `V = Re[w(h + m − m̄)]`, `m = 1_{symS ½ ℓ}H`. -/
def waveV (c u ℓ : ℝ) : L2R :=
  reLp (mulOp (wR (c / 2)) (hI c u + piece c u (1 / 2) ℓ - conjLp (piece c u (1 / 2) ℓ)))

/-- **The column error bound**: for `½ ≤ α ≤ x₀ ≤ ℓ ≤ x₁ ≤ 3/5`,
`‖J_c(Qe_u) − V‖ ≤ 2(‖(1 − P₊)k‖ + ‖(1 − P₊)m₁‖ + ‖P₊m₂‖ + ‖r₂‖ + ‖r₂'‖ + ‖r₁‖)`. -/
theorem norm_hardyJ_sub_waveV_le (c : ℝ) (hc : 0 ≤ c) {u : ℝ} (hu : 1 < u) {α x₀ ℓ x₁ : ℝ}
    (hα : 1 / 2 ≤ α) (h1 : α ≤ x₀) (h2 : x₀ ≤ ℓ) (h3 : ℓ ≤ x₁) (h4 : x₁ ≤ 3 / 5) :
    ‖hardyJ c (colA c u) - waveV c u ℓ‖ ≤
      2 * (‖kL2 c u - posProj (kL2 c u)‖ + ‖piece c u x₁ (3 / 5) - posProj (piece c u x₁ (3 / 5))‖ +
        ‖posProj (piece c u α x₀)‖ + (‖piece c u (1 / 2) α‖ + ‖piece c u x₀ ℓ‖) + ‖piece c u ℓ x₁‖) := by
  have hb : 0 ≤ c / 2 := by positivity
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  set k := kL2 c u
  set m₁ := piece c u x₁ (3 / 5)
  set m₂ := piece c u α x₀
  set r₁ := piece c u ℓ x₁
  set r₂ := piece c u (1 / 2) α + piece c u x₀ ℓ
  have hm : piece c u (1 / 2) ℓ = m₂ + r₂ := by
    rw [piece_split c hu h0 hα (h1.trans h2) (h3.trans h4),
      piece_split c hu (h0.trans hα) h1 h2 (h3.trans h4)]
    simp only [m₂, r₂]; abel
  have hh : hI c u = k - m₁ - (m₂ + r₂) - r₁ := by
    rw [hI_eq c hu, piece_split c hu h0 (hα.trans (h1.trans h2)) (h3.trans h4) le_rfl,
      piece_split c hu (h0.trans (hα.trans (h1.trans h2))) h3 h4 le_rfl, hm]
    abel
  rw [hardyJ_colA c hc hu, Cvs.Prolate.Hardy.ReflectedWaveSplit.split _ k m₁ m₂ r₁ r₂ hh, waveV, hm, map_add, map_add, add_sub_cancel_left]
  have hw1 : ∀ x, ‖wR (c / 2) x‖ ≤ 1 := Cvs.Prolate.Hardy.CarrierUpperHalfPlane.norm_wR_le hb
  refine (Cvs.Prolate.Hardy.ReflectedWaveSplit.norm_reflect_le (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wR hb) hw1 _).trans ?_
  have := Cvs.Prolate.Hardy.ReflectedWaveSplit.norm_err_le k m₁ m₂ r₁ r₂
  have hr₂ : ‖r₂‖ ≤ ‖piece c u (1 / 2) α‖ + ‖piece c u x₀ ℓ‖ := norm_add_le _ _
  linarith

end Cvs.Prolate.Hardy.ColumnTwoCarrierWave

end
