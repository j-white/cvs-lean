import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorBandCoupling
import Cvs.L2a.FullSpanFrameFloor
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.SubfamilyDefectCharge
import Cvs.Prolate.BandMassLaw
import Cvs.Prolate.CosineChristoffelDarboux
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.LandauHalfEvenSpectrum
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungMirrorIdentity
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# BAND-COUPLING with `θ̄ = √(2q′κ̄D̄)`, and L2a-FULL with `(BC)` discharged
L1 (Cvs.L2a.SubfamilyDefectCharge) with Landau's `λ ≥ ½` on the band gives `(BC)` from a per-rung coupling `⟨ψⱼ, 2E − wΦ⟩² ≤ κ̄MⱼP` and a
deficit `Σ_𝓑(1 − λⱼ) ≤ D̄`. The arm `⟨ψⱼ, w_FΦ⟩² ≤ f̄MⱼP` is `BandMassLaw`'s far fraction at `3/2`; with the E-coupling
`⟨ψⱼ, E⟩² ≤ ēMⱼP` this is `κ̄ = (√f̄ + 2√ē)²`. `D̄ = plungeBound c` by Cvs.Prolate.PlungeMassTrace paired with partner rungs (ORD, Cvs.Prolate.SlepianEvenOrdering).
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.CoreArmIdentity

namespace Cvs.L2a.BandCouplingDischarged

local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))

/-! ### The constants -/

/-- The route-T band constant `θ̄(κ̄, D̄) = √(2q′κ̄D̄)`, `q′ = (3 − 2√2)/2`. -/
def thetaBar (κ D : ℝ) : ℝ := √(2 * ((3 - 2 * √2) / 2) * (κ * D))

/-- The arm fraction bound `f̄(c) = log 5·(1 + δ_c(3/2))/(log(1 + c) − 2k(2, 5))`. -/
def fBar (c : ℝ) : ℝ :=
  Real.log 5 * (1 + Cvs.Prolate.BandMassLaw.deltaC c (3 / 2))
    / (Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 5)

/-- The combined coupling of the Cauchy–Schwarz split, `κ̄(c, ē) = (√f̄ + 2√ē)²`. -/
def kapBar (c e : ℝ) : ℝ := (√(fBar c) + 2 * √e) ^ 2

theorem two_q_nonneg : 0 ≤ 2 * ((3 - 2 * √2) / 2) := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

/-- `w̄(c, 2) ≤ 1`. -/
theorem wBar_two_le_one {c : ℝ} (hc : 0 < c) : Cvs.Prolate.BandMassLaw.wBar c 2 ≤ 1 := by
  unfold Cvs.Prolate.BandMassLaw.wBar
  have h : 0 < 2 / c := by positivity
  rw [div_le_one (by positivity)]
  linarith

/-- `2k(2, 5) ≤ 25/8`. -/
theorem twoK_two_five_le {c : ℝ} (hc : 0 < c) : Cvs.Prolate.BandMassLaw.twoK c 2 5 ≤ 25 / 8 := by
  have h := Cvs.Prolate.BandMassLaw.twoK_le (c := c) (r₀ := 2) (s := 5) hc (by norm_num) (by norm_num)
  have hw := wBar_two_le_one hc
  have h1 : 1 / 2 ≤ 1 - Cvs.Prolate.BandMassLaw.wBar c 2 / 2 := by linarith
  have h2 : 1 / (1 - Cvs.Prolate.BandMassLaw.wBar c 2 / 2) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- `log(1 + c) > 4` for `c ≥ 80`. -/
theorem four_lt_log {c : ℝ} (hc : 80 ≤ c) : 4 < Real.log (1 + c) := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have h := Real.exp_one_lt_d9
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h0 := Real.exp_pos 1
  calc Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
    _ < 1 + c := by norm_num; linarith

/-- The denominator of `f̄` is positive for `c ≥ 80`. -/
theorem fBar_den_pos {c : ℝ} (hc : 80 ≤ c) : 0 < Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 5 := by
  have := twoK_two_five_le (by linarith : (0 : ℝ) < c)
  have := four_lt_log hc
  linarith

/-- `δ_c(3/2) ≥ 0` for `c ≥ 80`. -/
theorem deltaC_three_halves_nonneg {c : ℝ} (hc : 80 ≤ c) : 0 ≤ Cvs.Prolate.BandMassLaw.deltaC c (3 / 2) := by
  have hc0 : 0 < c := by linarith
  have hp : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP (3 / 2 : ℝ) = 5 / 4 := by unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP; norm_num
  have hl : 0 < Cvs.Prolate.BandMassLaw.ellF (3 / 2) := Cvs.Prolate.BandMassLaw.ellF_pos (by norm_num)
  have hw : Cvs.Prolate.BandMassLaw.wUp c (3 / 2) = 12 / (5 * c) := by
    unfold Cvs.Prolate.BandMassLaw.wUp; rw [hp]; field_simp; ring
  unfold Cvs.Prolate.BandMassLaw.deltaC
  rw [hw, hp]
  have h1 : 1 ≤ 1 + 2 / (c * (5 / 4) * Cvs.Prolate.BandMassLaw.ellF (3 / 2)) := by
    have : 0 ≤ 2 / (c * (5 / 4) * Cvs.Prolate.BandMassLaw.ellF (3 / 2)) := by positivity
    linarith
  have h2 : 0 < 12 / (5 * c) := by positivity
  have h3 : 12 / (5 * c) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have h4 : 0 < (1 - 12 / (5 * c) / 2) ^ 2 := by
    have : 0 < 1 - 12 / (5 * c) / 2 := by linarith
    positivity
  have h5 : (1 - 12 / (5 * c) / 2) ^ 2 ≤ 1 := by nlinarith
  rw [sub_nonneg, le_div_iff₀ h4]
  nlinarith

/-- `f̄(c) ≥ 0` for `c ≥ 80`. -/
theorem fBar_nonneg {c : ℝ} (hc : 80 ≤ c) : 0 ≤ fBar c := by
  have h1 := deltaC_three_halves_nonneg hc
  have h2 := fBar_den_pos hc
  have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  unfold fBar
  positivity

theorem kapBar_nonneg (c e : ℝ) : 0 ≤ kapBar c e := sq_nonneg _

/-! ### The arm coupling -/

/-- **The arm on a band rung**: for `0 ≤ χ < c²`, `c² − χ ≤ 5c`, `c ≥ 80`, `∫_{3/2}^∞ ψ² ≤ f̄(c)·∫_1^∞ ψ²`
(`BandMassLaw`'s far fraction at `r₀ = 2`, `ξ = 3/2`). -/
theorem far_le_fBar {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hband : c ^ 2 - χ ≤ 5 * c) :
    ∫ t in Ioi (3 / 2), psi c g t ^ 2 ≤ fBar c * ∫ t in Ioi 1, psi c g t ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hξ : 1 + 2 / c ≤ 3 / 2 := by
    have : 2 / c ≤ 1 / 2 := by rw [div_le_iff₀ hc0]; linarith
    linarith
  have h := Cvs.Prolate.BandMassLaw.rung_band_far_fraction (ξ := 3 / 2) (r₀ := 2) hg hg₁ hg₂c hang hc0 hχ hχc
    (by norm_num) (Cvs.Prolate.BandMassLaw.wBar_lt_two hc0 (by norm_num)) hξ
  have hl : Cvs.Prolate.BandMassLaw.ellF (3 / 2) = Real.log 5 := by
    unfold Cvs.Prolate.BandMassLaw.ellF; norm_num
  have hlog : Real.log (1 + 2 * c / 2) = Real.log (1 + c) := by congr 1; ring
  rw [hl, hlog] at h
  have hs : (c ^ 2 - χ) / c ≤ 5 := by rw [div_le_iff₀ hc0]; linarith
  have hmono := Cvs.Prolate.BandMassLaw.twoK_mono (c := c) (r₀ := 2) hc0 (by norm_num) hs
  have hF : 0 ≤ ∫ t in Ioi (3 / 2), psi c g t ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hD := fBar_den_pos hc
  have h2 : (∫ t in Ioi (3 / 2), psi c g t ^ 2) * (Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 5)
      ≤ (∫ t in Ioi (3 / 2), psi c g t ^ 2)
        * (Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 ((c ^ 2 - χ) / c)) :=
    mul_le_mul_of_nonneg_left (by linarith) hF
  unfold fBar
  rw [div_mul_eq_mul_div, le_div_iff₀ hD]
  linarith

/-- **Cauchy–Schwarz for the arm**: for `0 ≤ w ≤ 1` vanishing on `(−∞, 3/2]`,
`(∫_1^∞ ψ·wΦ)² ≤ (∫_{3/2}^∞ ψ²)(∫_1^∞ Φ²)`. -/
theorem sq_integral_mul_weight_le {ψ Φ w : ℝ → ℝ} (hψ : MemLp ψ 2 μ₁) (hΦ : MemLp Φ 2 μ₁)
    (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) (hw32 : ∀ x, x ≤ 3 / 2 → w x = 0) :
    (∫ x in Ioi 1, ψ x * (w x * Φ x)) ^ 2 ≤ (∫ x in Ioi (3 / 2), ψ x ^ 2) * ∫ x in Ioi 1, Φ x ^ 2 := by
  have hf : MemLp (fun x => w x * ψ x) 2 μ₁ :=
    hψ.of_le (hwm.aestronglyMeasurable.mul hψ.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
        exact mul_le_of_le_one_left (abs_nonneg _) (hw1 x))
  have e : (fun x => ψ x * (w x * Φ x)) = fun x => (w x * ψ x) * Φ x := funext fun x => by ring
  have hcs := Cvs.L2a.FullTailConvergence.abs_setIntegral_mul_le (S := Ioi 1) hf.integrable_sq hΦ.integrable_sq
    (hf.integrable_mul hΦ)
  have hψ2 : IntegrableOn (fun x => ψ x ^ 2) (Ioi 1) := hψ.integrable_sq
  have hA : ∫ x in Ioi 1, (w x * ψ x) ^ 2 ≤ ∫ x in Ioi (3 / 2), ψ x ^ 2 := by
    calc ∫ x in Ioi 1, (w x * ψ x) ^ 2
        ≤ ∫ x in Ioi 1, (Ioi (3 / 2 : ℝ)).indicator (fun x => ψ x ^ 2) x := by
          refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
            (hψ2.indicator measurableSet_Ioi) (ae_of_all _ fun x => ?_)
          show (w x * ψ x) ^ 2 ≤ _
          by_cases hx : x ∈ Ioi (3 / 2 : ℝ)
          · rw [indicator_of_mem hx, mul_pow]
            have h0 := hw0 x
            have h1 := hw1 x
            have : w x ^ 2 ≤ 1 := by nlinarith
            nlinarith [sq_nonneg (ψ x)]
          · rw [indicator_of_notMem hx, hw32 x (not_lt.1 hx)]; simp
      _ = ∫ x in Ioi (3 / 2 : ℝ), ψ x ^ 2 := by
          rw [setIntegral_indicator measurableSet_Ioi,
            Set.inter_eq_right.2 (Ioi_subset_Ioi (by norm_num))]
  have hA0 : 0 ≤ ∫ x in Ioi 1, (w x * ψ x) ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ ∫ x in Ioi 1, Φ x ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  rw [e, ← sq_abs]
  calc |∫ x in Ioi 1, w x * ψ x * Φ x| ^ 2
      ≤ (√(∫ x in Ioi 1, (w x * ψ x) ^ 2) * √(∫ x in Ioi 1, Φ x ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcs 2
    _ = (∫ x in Ioi 1, (w x * ψ x) ^ 2) * ∫ x in Ioi 1, Φ x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    _ ≤ (∫ x in Ioi (3 / 2), ψ x ^ 2) * ∫ x in Ioi 1, Φ x ^ 2 := mul_le_mul_of_nonneg_right hA hB0

/-- `(2x − y)² ≤ (√f + 2√e)²MP` from `x² ≤ eMP` and `y² ≤ fMP`. -/
theorem sq_two_mul_sub_le {x y e f M P : ℝ} (he : 0 ≤ e) (hf : 0 ≤ f) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (hx : x ^ 2 ≤ e * M * P) (hy : y ^ 2 ≤ f * M * P) : (2 * x - y) ^ 2 ≤ (√f + 2 * √e) ^ 2 * M * P := by
  have hMP : 0 ≤ M * P := mul_nonneg hM hP
  have hx' : |x| ≤ √e * √(M * P) := by
    rw [← Real.sqrt_mul he]; exact Real.abs_le_sqrt (by rw [← mul_assoc]; exact hx)
  have hy' : |y| ≤ √f * √(M * P) := by
    rw [← Real.sqrt_mul hf]; exact Real.abs_le_sqrt (by rw [← mul_assoc]; exact hy)
  have h : |2 * x - y| ≤ (√f + 2 * √e) * √(M * P) := by
    calc |2 * x - y| ≤ |2 * x| + |y| := abs_sub _ _
      _ = 2 * |x| + |y| := by rw [abs_mul, abs_two]
      _ ≤ (√f + 2 * √e) * √(M * P) := by linarith
  rw [← sq_abs, mul_assoc]
  calc |2 * x - y| ^ 2 ≤ ((√f + 2 * √e) * √(M * P)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (√f + 2 * √e) ^ 2 * (M * P) := by rw [mul_pow, Real.sq_sqrt hMP]

/-- A rung mass on `(1, ∞)` is positive when its mass on `(1, 3)` is. -/
theorem mass_Ioi_pos {ψ : ℝ → ℝ} (hψ : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1))
    (h : 0 < ∫ t in (1 : ℝ)..3, ψ t ^ 2) : 0 < ∫ t in Ioi 1, ψ t ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num)] at h
  exact h.trans_le (setIntegral_mono_set hψ (ae_of_all _ fun _ => sq_nonneg _) Ioc_subset_Ioi_self.eventuallySubset)

/-! ### BAND-COUPLING from a per-rung coupling (L1 with Landau) -/

section core
variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}

/-- `Σ_S aᵢ²Mᵢ ≤ ∫_1^∞ Φ²` by orthogonality on `(1, ∞)` (Cvs.Prolate.RungExactOrthogonality). -/
theorem sum_sq_mass_le (a : ι → ℝ) (S : Finset ι)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) :
    ∑ i ∈ S, a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 ≤ ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  rw [Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc hχ]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ =>
    mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)

/-- **(BC) from per-rung couplings**: if `τᵢ ≥ 0`, `τᵢ² ≥ ½` and `⟨ψᵢ, 2E − wΦ⟩² ≤ κᵢMᵢP` on `S`, and
`Σ_S (1 − τᵢ²)κᵢ ≤ K`, then `BandCoupling` holds with `θ = √(2q′K)`. -/
theorem bandCoupling_of_kappa (a : ι → ℝ) (S : Finset ι)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hg0 : ∀ i ∈ S, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0) (hM : ∀ i ∈ S, 0 < ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2)
    (hτ0 : ∀ i ∈ S, 0 ≤ μ i * √(c / (2 * π))) (hland : ∀ i ∈ S, 1 / 2 ≤ (μ i * √(c / (2 * π))) ^ 2)
    (w : ℝ → ℝ) (X : ℝ) (κ : ι → ℝ) {K : ℝ}
    (hκ : ∀ i ∈ S, (∫ x in Ioi 1, psi c (g i) x
        * (2 * dilSum (fun ξ => ∑ j, a j * psi c (g j) ξ) X x - w x * ∑ j, a j * psi c (g j) x)) ^ 2
      ≤ κ i * (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) * ∫ ξ in Ioi 1, (∑ j, a j * psi c (g j) ξ) ^ 2)
    (hK : ∑ i ∈ S, (1 - (μ i * √(c / (2 * π))) ^ 2) * κ i ≤ K) :
    Cvs.L2a.FrameFloorBandCoupling.BandCoupling c g μ a S w X (√(2 * ((3 - 2 * √2) / 2) * K)) := by
  set P := ∫ ξ in Ioi 1, (∑ j, a j * psi c (g j) ξ) ^ 2 with hPdef
  have hP : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have h := Cvs.L2a.SubfamilyDefectCharge.eone_coupling_landau_span a S hg hc heven hμ hg0 hM hτ0 hland
    (fun x => 2 * dilSum (fun ξ => ∑ j, a j * psi c (g j) ξ) X x - w x * ∑ j, a j * psi c (g j) x) κ hP hκ
  have h1 : √(2 * ((3 - 2 * √2) / 2) * ∑ i ∈ S, (1 - (μ i * √(c / (2 * π))) ^ 2) * κ i)
      ≤ √(2 * ((3 - 2 * √2) / 2) * K) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hK two_q_nonneg)
  have h2 : √(∑ i ∈ S, a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) ≤ √P :=
    Real.sqrt_le_sqrt (sum_sq_mass_le a S hg hg₁ hg₂c hang hc hχ)
  unfold Cvs.L2a.FrameFloorBandCoupling.BandCoupling
  refine h.trans ?_
  calc √(2 * ((3 - 2 * √2) / 2) * ∑ i ∈ S, (1 - (μ i * √(c / (2 * π))) ^ 2) * κ i)
        * √(∑ i ∈ S, a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) * √P
      ≤ √(2 * ((3 - 2 * √2) / 2) * K) * √P * √P := by
        gcongr
    _ = √(2 * ((3 - 2 * √2) / 2) * K) * P := by rw [mul_assoc, Real.mul_self_sqrt hP]

/-- **Route T**: with one `κ̄ ≥ 0` for every band rung and `Σ_S (1 − τᵢ²) ≤ D̄`, `BandCoupling` holds with
`θ̄ = √(2q′κ̄D̄)`. -/
theorem bandCoupling_routeT (a : ι → ℝ) (S : Finset ι)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hg0 : ∀ i ∈ S, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0) (hM : ∀ i ∈ S, 0 < ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2)
    (hτ0 : ∀ i ∈ S, 0 ≤ μ i * √(c / (2 * π))) (hland : ∀ i ∈ S, 1 / 2 ≤ (μ i * √(c / (2 * π))) ^ 2)
    (w : ℝ → ℝ) (X : ℝ) {κb D : ℝ} (hκb : 0 ≤ κb)
    (hκ : ∀ i ∈ S, (∫ x in Ioi 1, psi c (g i) x
        * (2 * dilSum (fun ξ => ∑ j, a j * psi c (g j) ξ) X x - w x * ∑ j, a j * psi c (g j) x)) ^ 2
      ≤ κb * (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) * ∫ ξ in Ioi 1, (∑ j, a j * psi c (g j) ξ) ^ 2)
    (hD : ∑ i ∈ S, (1 - (μ i * √(c / (2 * π))) ^ 2) ≤ D) :
    Cvs.L2a.FrameFloorBandCoupling.BandCoupling c g μ a S w X (thetaBar κb D) := by
  have hK : ∑ i ∈ S, (1 - (μ i * √(c / (2 * π))) ^ 2) * κb ≤ κb * D := by
    rw [← Finset.sum_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hD hκb
  exact bandCoupling_of_kappa a S hg hg₁ hg₂c hang hc hχ heven hμ hg0 hM hτ0 hland w X (fun _ => κb) hκ hK

end core

/-! ### The E-coupling and the combined coupling -/

section coupling
variable {ι : Type} [Fintype ι]

/-- **The E-coupling on `S`** (THEOREM E, Corollary E1): for every integer `M ≥ 3` and `j ∈ S`,
`⟨ψⱼ, dilSum(Φ, M)⟩² ≤ ē·Mⱼ·P` with `Mⱼ = ∫_1^∞ ψⱼ²`, `P = ∫_1^∞ Φ²`. -/
def ECoupling (c : ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (S : Finset ι) (e : ℝ) : Prop :=
  ∀ M : ℕ, 3 ≤ M → ∀ j ∈ S, Cvs.L2a.BandRungOutgoingWave.eCoup c (g j) a g M ^ 2
    ≤ e * (∫ ξ in Ioi 1, psi c (g j) ξ ^ 2) * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2

/-- **The combined coupling on `S`**: for every integer `M ≥ 3` and `j ∈ S`,
`⟨ψⱼ, 2 dilSum(Φ, M) − wΦ⟩² ≤ κ̄·Mⱼ·P`. -/
def RungCoupling (c : ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (S : Finset ι) (w : ℝ → ℝ) (κ : ℝ) : Prop :=
  ∀ M : ℕ, 3 ≤ M → ∀ j ∈ S, (∫ x in Ioi 1, psi c (g j) x
      * (2 * dilSum (fun ξ => ∑ i, a i * psi c (g i) ξ) M x - w x * ∑ i, a i * psi c (g i) x)) ^ 2
    ≤ κ * (∫ ξ in Ioi 1, psi c (g j) ξ ^ 2) * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2

variable {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

/-- **E plus arm**: on band rungs (`0 ≤ χⱼ < c²`, `c² − χⱼ ≤ 5c`, `c ≥ 80`) the E-coupling `ē` gives the combined
coupling with `w_F` and `κ̄ = (√f̄ + 2√ē)²`. -/
theorem rungCoupling_of_eCoupling (a : ι → ℝ) (S : Finset ι)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i ∈ S, 0 ≤ χ i) (hχc : ∀ i ∈ S, χ i < c ^ 2)
    (hband : ∀ i ∈ S, c ^ 2 - χ i ≤ 5 * c) {e : ℝ} (he : 0 ≤ e) (hE : ECoupling c g a S e) :
    RungCoupling c g a S Cvs.L2a.FarIntegrationByParts.wF (kapBar c e) := by
  intro M hM j hj
  have hc0 : 0 < c := by linarith
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦdef
  have hψ : ∀ i, MemLp (psi c (g i)) 2 μ₁ := fun i =>
    Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc0
  have hΦ : MemLp Φ 2 μ₁ := memLp_finsetSum Finset.univ fun i _ => (hψ i).const_mul (a i)
  have hX : (1 : ℝ) ≤ (M : ℝ) := by
    have : (3 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hE0 := Cvs.L2a.FrameFloorBandCoupling.memLp_frame (w := fun _ => (0 : ℝ)) hX hΦ measurable_const
    (fun _ => le_rfl) (fun _ => zero_le_one)
  have hEL : MemLp (dilSum Φ M) 2 μ₁ := by
    refine MemLp.ae_eq (ae_of_all _ fun x => ?_) (hE0.const_mul (1 / 2 : ℝ))
    simp only [zero_mul, sub_zero]
    ring
  have hwm : Measurable Cvs.L2a.FarIntegrationByParts.wF := Cvs.L2a.FarIntegrationByParts.continuous_wF.1.measurable
  have hw0 : ∀ x, 0 ≤ Cvs.L2a.FarIntegrationByParts.wF x := fun x => (Cvs.L2a.FarFarBound.wF_bounds x).1
  have hw1 : ∀ x, Cvs.L2a.FarIntegrationByParts.wF x ≤ 1 := fun x => (Cvs.L2a.FarFarBound.wF_bounds x).2.1
  have hwΦ : MemLp (fun x => Cvs.L2a.FarIntegrationByParts.wF x * Φ x) 2 μ₁ :=
    hΦ.of_le (hwm.aestronglyMeasurable.mul hΦ.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
        exact mul_le_of_le_one_left (abs_nonneg _) (hw1 x))
  have hI1 : Integrable (fun x => psi c (g j) x * dilSum Φ M x) μ₁ := (hψ j).integrable_mul hEL
  have hI2 : Integrable (fun x => psi c (g j) x * (Cvs.L2a.FarIntegrationByParts.wF x * Φ x)) μ₁ :=
    (hψ j).integrable_mul hwΦ
  have hsplit : ∫ x in Ioi 1, psi c (g j) x * (2 * dilSum Φ M x - Cvs.L2a.FarIntegrationByParts.wF x * Φ x)
      = 2 * Cvs.L2a.BandRungOutgoingWave.eCoup c (g j) a g M
        - ∫ x in Ioi 1, psi c (g j) x * (Cvs.L2a.FarIntegrationByParts.wF x * Φ x) := by
    have e1 : (fun x => psi c (g j) x * (2 * dilSum Φ M x - Cvs.L2a.FarIntegrationByParts.wF x * Φ x))
        = fun x => 2 * (psi c (g j) x * dilSum Φ M x)
          - psi c (g j) x * (Cvs.L2a.FarIntegrationByParts.wF x * Φ x) := funext fun x => by ring
    rw [e1, integral_sub (hI1.const_mul 2) hI2, integral_const_mul]
    rfl
  have harm := sq_integral_mul_weight_le (hψ j) hΦ hwm hw0 hw1
    (fun x hx => Cvs.L2a.FarFarBound.wF_eq_zero_of_le hx)
  have hfar := far_le_fBar (hg j) (hg₁ j) (hg₂c j) (hang j) hc (hχ0 j hj) (hχc j hj) (hband j hj)
  have hP : 0 ≤ ∫ x in Ioi 1, Φ x ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hMj : 0 ≤ ∫ ξ in Ioi 1, psi c (g j) ξ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hy : (∫ x in Ioi 1, psi c (g j) x * (Cvs.L2a.FarIntegrationByParts.wF x * Φ x)) ^ 2
      ≤ fBar c * (∫ ξ in Ioi 1, psi c (g j) ξ ^ 2) * ∫ x in Ioi 1, Φ x ^ 2 :=
    harm.trans (mul_le_mul_of_nonneg_right hfar hP)
  have hx := hE M hM j hj
  show (∫ x in Ioi 1, psi c (g j) x * (2 * dilSum Φ M x - Cvs.L2a.FarIntegrationByParts.wF x * Φ x)) ^ 2 ≤ _
  rw [hsplit]
  exact sq_two_mul_sub_le he (fBar_nonneg hc) hMj hP hx hy

end coupling

/-! ### THEOREM E in the coupling form, and the edge value against the mass -/

section bridge
variable {ι : Type} [Fintype ι]

/-- **THEOREM E (Cvs.L2a.BandRungOutgoingWave) as a coupling bound**: under `ecoupling_le_unif`'s hypotheses, if its bracket is at most
`√(ē·Mⱼ)`, then `⟨ψⱼ, dilSum(Φ, M)⟩² ≤ ē·Mⱼ·P`. -/
theorem eCoup_sq_le_of_unif {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {gj gj₁ gj₂ : ℝ → ℝ} {χj : ℝ} {M : ℕ} {d δ t r K0 Kb T ηB e : ℝ} {ν₁ ν₂ ν₃ : ℕ → ℝ → ℂ}
    {N : ℕ → ℕ → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hgj : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hgj₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hgj₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hangj : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (hevenj : ∀ s ∈ Icc (-1 : ℝ) 1, gj (-s) = gj s) (hχj0 : 0 ≤ χj) (hχjc : χj < c ^ 2)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2)
    (hd : 0 < d) (hd2 : d ≤ 1 / 2) (hδ : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) (hr : 0 < r)
    (hK0 : 0 ≤ K0) (hKb : 0 ≤ Kb) (he : 0 ≤ e)
    (hμ : ∀ m ∈ Finset.Ico 2 M, Cvs.L2a.BandTransferBandForm.IsBandMult
      (fun η => Cvs.L2a.BandRungOutgoingWave.nuCut c gj m m (c * η))
      (ν₁ m) (ν₂ m) (ν₃ m) δ (Cvs.L2a.OrbitGapIntegerM.Ymax m) (N m))
    (hN0 : ∀ m ∈ Finset.Ico 2 M, N m 0 ≤ K0 / m)
    (hN : ∀ m ∈ Finset.Ico 2 M, ∀ j ≤ 3, N m j ≤ Kb / m * ((j.factorial : ℝ) / r ^ j))
    (htop : |Cvs.L2a.BandRungOutgoingWave.topE c gj a χ g M|
      ≤ T * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2))
    (hbulk : |Cvs.L2a.BandRungOutgoingWave.bulkE c gj a χ g M|
      ≤ ηB * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2))
    (hbr : √(psi c gj 1 ^ 2 * Cvs.L2a.BandRungOutgoingWave.lamHat (Cvs.Prolate.BandMassLaw.wUp c 2)
          * Cvs.L2a.BandRungOutgoingWave.cE / c)
        + Cvs.L2a.BandRungOutgoingWave.gL1 gj * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3))
        + K0 * √(c * Cvs.L2a.BandRungOutgoingWave.collarK δ t)
        + Kb * Cvs.L2a.BandRungOutgoingWave.tauBar c d δ r * √(8 * (1 + 1 / t) * (Fintype.card ι : ℝ))
        + T + ηB ≤ √(e * ∫ ξ in Ioi 1, psi c gj ξ ^ 2)) :
    Cvs.L2a.BandRungOutgoingWave.eCoup c gj a g M ^ 2
      ≤ e * (∫ ξ in Ioi 1, psi c gj ξ ^ 2) * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  have h := Cvs.L2a.BandRungOutgoingWave.ecoupling_le_unif a hg hg₁ hg₂c hang hc hχ0 hχc hχi hgj hgj₁ hgj₂c hangj
    hevenj hχj0 hχjc hmass hd hd2 hδ hδ1 ht hr hK0 hKb hμ hN0 hN htop hbulk
  have hP : 0 ≤ ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hMj : 0 ≤ ∫ ξ in Ioi 1, psi c gj ξ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have h2 := h.trans (mul_le_mul_of_nonneg_right hbr (Real.sqrt_nonneg _))
  have h3 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (mul_nonneg he hMj), Real.sq_sqrt hP] at h3
  exact h3

end bridge

/-! ### The plunge deficit -/

section plunge
variable {ι : Type} [DecidableEq ι]

/-- `psi c (g/N) = (psi c g)/N`. -/
theorem psi_div_const (c : ℝ) (g : ℝ → ℝ) (N ξ : ℝ) : psi c (fun s => g s / N) ξ = psi c g ξ / N := by
  unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
  rw [← intervalIntegral.integral_div]
  congr 1
  funext s
  ring

/-- **The even Bessel bound without normalisation**: `PlungeMassTrace`'s `Σ_S λᵢ(1 − λᵢ) ≤ plungeBound c` for even angular
eigen-rungs at distinct `χᵢ`, each nonzero on `[−1, 1]`. -/
theorem sum_plunge_le_unnorm (S : Finset ι) {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ} (hc : 1 ≤ c)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ : Set.InjOn χ S) (heven : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hg0 : ∀ i ∈ S, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s) :
    ∑ i ∈ S, (μ i * √(c / (2 * π))) ^ 2 * (1 - (μ i * √(c / (2 * π))) ^ 2)
      ≤ Cvs.Prolate.PlungeMassTrace.plungeBound c := by
  set N : ι → ℝ := fun i => √(∫ s in (-1 : ℝ)..1, g i s ^ 2) with hN
  have hpos : ∀ i ∈ S, 0 < ∫ s in (-1 : ℝ)..1, g i s ^ 2 := fun i hi => by
    obtain ⟨s₀, hs₀, hne⟩ := hg0 i hi
    have hgc : ContinuousOn (g i) (Icc (-1) 1) := Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt (hg i)
    exact intervalIntegral.integral_pos (by norm_num) (hgc.pow 2) (fun x _ => sq_nonneg _)
      ⟨s₀, hs₀, by positivity⟩
  refine Cvs.Prolate.PlungeMassTrace.sum_plunge_le_angular S (g := fun i s => g i s / N i)
    (g₁ := fun i s => g₁ i s / N i) (g₂ := fun i s => g₂ i s / N i) hc
    (fun i s hs => (hg i s hs).div_const _) (fun i s hs => (hg₁ i s hs).div_const _) ?_ hχ ?_ ?_ ?_
  · intro i s hs
    show (1 - s ^ 2) * (g₂ i s / N i) - 2 * s * (g₁ i s / N i) - c ^ 2 * s ^ 2 * (g i s / N i)
      + χ i * (g i s / N i) = 0
    calc _ = ((1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s) / N i := by ring
      _ = 0 := by rw [hang i s hs, zero_div]
  · intro i hi
    have hI := hpos i hi
    show ∫ s in (-1 : ℝ)..1, (g i s / N i) ^ 2 = 1
    simp only [div_pow]
    rw [intervalIntegral.integral_div, hN, Real.sq_sqrt hI.le, div_self hI.ne']
  · intro i hi s hs
    show g i (-s) / N i = g i s / N i
    rw [heven i hi s hs]
  · intro i hi s hs
    show psi c (fun s => g i s / N i) s = μ i * (g i s / N i)
    rw [psi_div_const, hμ i hi s hs]
    ring

/-- **The paired deficit** (Bessel, no completeness): with a partner rung `hᵢ` at `χ'ᵢ ≥ χᵢ` having `λ'ᵢ ≥ ½`,
all levels distinct, `Σ_S (1 − λᵢ) ≤ Σ_S (λᵢ(1 − λᵢ) + λ'ᵢ(1 − λ'ᵢ)) ≤ plungeBound c` (ORD from Cvs.Prolate.SlepianEvenOrdering). -/
theorem sum_one_sub_le_plunge_paired (S : Finset ι) {g g₁ g₂ h h₁ h₂ : ι → ℝ → ℝ} {c : ℝ}
    {χ χ' μ μ' : ι → ℝ} (hc : 1 ≤ c)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hh : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hh₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hh₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang' : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ' i * h i s = 0)
    (hχ : Set.InjOn χ S) (hχ' : Set.InjOn χ' S) (hχχ' : ∀ i ∈ S, ∀ j ∈ S, χ i ≠ χ' j)
    (heven : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hg0 : ∀ i ∈ S, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (heven' : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s)
    (hh0 : ∀ i ∈ S, ∃ s ∈ Icc (-1 : ℝ) 1, h i s ≠ 0)
    (hμ' : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ' i * h i s)
    (hord : ∀ i ∈ S, χ i ≤ χ' i) (hland' : ∀ i ∈ S, 1 / 2 ≤ (μ' i * √(c / (2 * π))) ^ 2) :
    ∑ i ∈ S, (1 - (μ i * √(c / (2 * π))) ^ 2) ≤ Cvs.Prolate.PlungeMassTrace.plungeBound c := by
  have hc0 : 0 < c := by linarith
  have hP := sum_plunge_le_unnorm (S.disjSum S) (g := Sum.elim g h) (g₁ := Sum.elim g₁ h₁)
    (g₂ := Sum.elim g₂ h₂) (χ := Sum.elim χ χ') (μ := Sum.elim μ μ') hc
    (by rintro (i | i) s hs; exacts [hg i s hs, hh i s hs])
    (by rintro (i | i) s hs; exacts [hg₁ i s hs, hh₁ i s hs])
    (by rintro (i | i) s hs; exacts [hang i s hs, hang' i s hs])
    (by
      rintro (i | i) hi (j | j) hj hij <;>
        simp only [Finset.mem_coe, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Sum.elim_inl,
          Sum.elim_inr] at hi hj hij
      · rw [hχ hi hj hij]
      · exact absurd hij (hχχ' i hi j hj)
      · exact absurd hij.symm (hχχ' j hj i hi)
      · rw [hχ' hi hj hij])
    (by
      rintro (i | i) hi s hs <;>
        simp only [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] at hi
      exacts [heven i hi s hs, heven' i hi s hs])
    (by
      rintro (i | i) hi <;> simp only [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] at hi
      exacts [hg0 i hi, hh0 i hi])
    (by
      rintro (i | i) hi s hs <;>
        simp only [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] at hi
      exacts [hμ i hi s hs, hμ' i hi s hs])
  rw [Finset.sum_disjSum] at hP
  simp only [Sum.elim_inl, Sum.elim_inr] at hP
  have hpair : ∀ i ∈ S, 1 - (μ i * √(c / (2 * π))) ^ 2
      ≤ (μ i * √(c / (2 * π))) ^ 2 * (1 - (μ i * √(c / (2 * π))) ^ 2)
        + (μ' i * √(c / (2 * π))) ^ 2 * (1 - (μ' i * √(c / (2 * π))) ^ 2) := fun i hi => by
    have habs := Cvs.Prolate.RungMirrorIdentity.abs_tau_le_one hc0
      (Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt (hg i)) (heven i hi) (hμ i hi) (hg0 i hi)
    have h1 : (μ i * √(c / (2 * π))) ^ 2 ≤ 1 := by rw [sq_le_one_iff_abs_le_one]; exact habs
    have hle := Cvs.Prolate.SlepianEvenOrdering.lam_le_of_chi_le hc0 (hg i) (hg₁ i) (hg₂c i) (hang i) (heven i hi)
      (hg0 i hi) (hh i) (hh₁ i) (hh₂c i) (hang' i) (heven' i hi) (hh0 i hi) (hμ i hi) (hμ' i hi) (hord i hi)
    exact Cvs.Prolate.PlungeMassTrace.one_sub_le_pair h1 (hland' i hi) hle
  calc ∑ i ∈ S, (1 - (μ i * √(c / (2 * π))) ^ 2)
      ≤ ∑ i ∈ S, ((μ i * √(c / (2 * π))) ^ 2 * (1 - (μ i * √(c / (2 * π))) ^ 2)
        + (μ' i * √(c / (2 * π))) ^ 2 * (1 - (μ' i * √(c / (2 * π))) ^ 2)) := Finset.sum_le_sum hpair
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := hP

end plunge

/-! ### THEOREM L2a-FULL with `(BC)` discharged -/

section main
variable {ι : Type} [Fintype ι]

/-- **(BC) on the band from a rung coupling**: for `c ≥ 10¹⁶` with `FullSpanConditional`'s structural list, Landau's lower pivot
at `k` above every band index, the combined coupling `κ̄ ≥ 0` on `𝓑` and `Σ_𝓑(1 − λᵢ) ≤ D̄`, `(BC)` holds at
every integer `M ≥ 3` with `θ̄ = √(2q′κ̄D̄)`. -/
theorem bandCoupling_band {μ : ι → ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, psi c (g i) t ^ 2)
    {k : ℕ} (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower c k)
    (hk : ∀ i ∈ Cvs.L2a.FullSpanFrameFloor.bandSet c χ,
      (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard ≤ k)
    {κb D : ℝ} (hκb : 0 ≤ κb)
    (hRC : RungCoupling c g a (Cvs.L2a.FullSpanFrameFloor.bandSet c χ) Cvs.L2a.FarIntegrationByParts.wF κb)
    (hD : ∑ i ∈ Cvs.L2a.FullSpanFrameFloor.bandSet c χ, (1 - (μ i * √(c / (2 * π))) ^ 2) ≤ D) :
    ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorBandCoupling.BandCoupling c g μ a (Cvs.L2a.FullSpanFrameFloor.bandSet c χ)
      Cvs.L2a.FarIntegrationByParts.wF M (thetaBar κb D) := fun M hM =>
  bandCoupling_routeT a (Cvs.L2a.FullSpanFrameFloor.bandSet c χ) hg hg₁ hg₂c hang hc hχi heven hμ
    (fun i _ => hg0 i)
    (fun i _ => mass_Ioi_pos (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).integrable_sq
      (hmass i))
    (fun i _ => (mul_pos (Cvs.Prolate.SlepianEvenOrdering.mu_pos_of_even_index hc (hg i) (hg₁ i) (hg₂c i) (hang i)
      (heven i) (hg0 i) (hμ i) (hidx i)) (Real.sqrt_pos.2 (by positivity))).le)
    (fun i hi => Cvs.Prolate.LandauHalfEvenSpectrum.half_le_lam_of_lower hc hL (hg i) (hg₁ i) (hg₂c i) (hang i) (heven i)
      (hg0 i) (hμ i) (hk i hi))
    Cvs.L2a.FarIntegrationByParts.wF M hκb (hRC M hM) hD

end main

end Cvs.L2a.BandCouplingDischarged
