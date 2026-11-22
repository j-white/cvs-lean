import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SingletonRegularisationColumn
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.MirrorFloor
import Cvs.L2a.ModeTailNormCrossForm
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.SincTopIsRung
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.OddPoleTermBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Bernstein and Nikolskii on the rung span

`ψ_φ(ξ) = ∫_{−1}^{1} φ(s) cos(cξs) ds` and its derivative are dominated by the Fourier transform of `1_{[−1,1]}φ`
at `cξ/2π`, so Plancherel gives `∫_ℝ ψ_φ² ≤ (2π/c)‖φ‖²` and `∫_ℝ ψ_φ′² ≤ 2πc‖sφ‖²`. On the span of the rungs `h_{2i}`,
`i < x`, the profile is `ψ_φ` with `φ = Σ b_i μ_i⁻¹ h_{2i}`, and `μ_i⁻² = c/(2πλ_i)` turns these into
`‖G′‖² ≤ (c²/λ)‖G‖²`, `G(t)² ≤ (2c/(πλ))‖G‖²` and `G′(t)² ≤ (2c³/(3πλ))‖G‖²` on `L²(0, 1)`.
-/

noncomputable section

open Real Set MeasureTheory
open scoped FourierTransform Interval

namespace Cvs.Prolate.RungSpanBernsteinNikolskii
open Cvs.ZeroCounting

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SlepianCommutingRelation (kint)
open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx rung rung₁ rung_spec muR lamR psi_rung)

/-! ### The extension and its derivative -/

/-- The derivative `ψ_φ′(ξ) = −∫_{−1}^{1} φ(s) cs sin(cξs) ds` of the extension. -/
def psiD (c : ℝ) (φ : ℝ → ℝ) (ξ : ℝ) : ℝ := kint φ (fun ξ s => -(c * s * sin (c * ξ * s))) ξ

/-- `ψ_φ` has derivative `ψ_φ′` everywhere. -/
theorem hasDerivAt_psi' {c : ℝ} {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) (ξ : ℝ) :
    HasDerivAt (psi c φ) (psiD c φ ξ) ξ :=
  Cvs.Prolate.SincTopIsRung.hasDerivAt_psi hφ ξ

/-- `ψ_φ` is continuous. -/
theorem continuous_psi {c : ℝ} {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) : Continuous (psi c φ) :=
  continuous_iff_continuousAt.2 fun ξ => (hasDerivAt_psi' hφ ξ).continuousAt

/-- `ψ_φ′` is continuous. -/
theorem continuous_psiD {c : ℝ} {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) : Continuous (psiD c φ) :=
  continuous_iff_continuousAt.2 fun ξ => (Cvs.Prolate.SincTopIsRung.hasDerivAt_psi₁ hφ ξ).continuousAt

/-- `ψ_φ` is even. -/
theorem psi_neg (c : ℝ) (φ : ℝ → ℝ) (ξ : ℝ) : psi c φ (-ξ) = psi c φ ξ := by
  simp only [psi, kint]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [show c * -ξ * s = -(c * ξ * s) by ring, cos_neg]

/-- `ψ_φ′` is odd. -/
theorem psiD_neg (c : ℝ) (φ : ℝ → ℝ) (ξ : ℝ) : psiD c φ (-ξ) = -psiD c φ ξ := by
  simp only [psiD, kint]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [show c * -ξ * s = -(c * ξ * s) by ring, sin_neg]
  ring

/-! ### Pointwise bounds -/

/-- **Nikolskii for the extension**: `ψ_φ(ξ)² ≤ 2∫_{−1}^{1} φ²`. -/
theorem psi_sq_le {c : ℝ} {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) (ξ : ℝ) :
    psi c φ ξ ^ 2 ≤ 2 * ∫ s in (-1 : ℝ)..1, φ s ^ 2 := by
  have hk : ContinuousOn (fun s => cos (c * ξ * s)) (uIcc (-1) 1) := by fun_prop
  have h := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le (by norm_num : (-1 : ℝ) ≤ 1) (f := φ)
    (w := fun s => cos (c * ξ * s)) (hφ.pow 2).intervalIntegrable (hk.pow 2).intervalIntegrable
    (hφ.mul hk).intervalIntegrable
  have hcos : ∫ s in (-1 : ℝ)..1, cos (c * ξ * s) ^ 2 ≤ 2 := by
    have : ∫ s in (-1 : ℝ)..1, cos (c * ξ * s) ^ 2 ≤ ∫ _ in (-1 : ℝ)..1, (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by norm_num) (hk.pow 2).intervalIntegrable
        intervalIntegrable_const fun s _ => cos_sq_le_one (c * ξ * s)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
    linarith
  have hφ0 : 0 ≤ ∫ s in (-1 : ℝ)..1, φ s ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  show (∫ s in (-1 : ℝ)..1, φ s * cos (c * ξ * s)) ^ 2 ≤ _
  calc _ ≤ _ := h
    _ ≤ (∫ s in (-1 : ℝ)..1, φ s ^ 2) * 2 := mul_le_mul_of_nonneg_left hcos hφ0
    _ = _ := by ring

/-- **Nikolskii for the derivative**: `ψ_φ′(ξ)² ≤ (2c²/3)∫_{−1}^{1} φ²`. -/
theorem psiD_sq_le {c : ℝ} {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) (ξ : ℝ) :
    psiD c φ ξ ^ 2 ≤ 2 * c ^ 2 / 3 * ∫ s in (-1 : ℝ)..1, φ s ^ 2 := by
  have hk : ContinuousOn (fun s => -(c * s * sin (c * ξ * s))) (uIcc (-1) 1) := by fun_prop
  have h := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le (by norm_num : (-1 : ℝ) ≤ 1) (f := φ)
    (w := fun s => -(c * s * sin (c * ξ * s))) (hφ.pow 2).intervalIntegrable (hk.pow 2).intervalIntegrable
    (hφ.mul hk).intervalIntegrable
  have hsin : ∫ s in (-1 : ℝ)..1, (-(c * s * sin (c * ξ * s))) ^ 2 ≤ 2 * c ^ 2 / 3 := by
    have : ∫ s in (-1 : ℝ)..1, (-(c * s * sin (c * ξ * s))) ^ 2 ≤ ∫ s in (-1 : ℝ)..1, c ^ 2 * s ^ 2 :=
      intervalIntegral.integral_mono_on (by norm_num) (hk.pow 2).intervalIntegrable
        ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _) fun s _ => by
          nlinarith [sin_sq_le_one (c * ξ * s), sq_nonneg (c * s)]
    rw [intervalIntegral.integral_const_mul, integral_pow] at this
    norm_num at this
    simp only [neg_sq]
    linarith
  have hφ0 : 0 ≤ ∫ s in (-1 : ℝ)..1, φ s ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  show (∫ s in (-1 : ℝ)..1, φ s * -(c * s * sin (c * ξ * s))) ^ 2 ≤ _
  calc _ ≤ _ := h
    _ ≤ (∫ s in (-1 : ℝ)..1, φ s ^ 2) * (2 * c ^ 2 / 3) := mul_le_mul_of_nonneg_left hsin hφ0
    _ = _ := by ring

/-! ### The Fourier transform of the window lift -/

/-- The window lift `1_{[−1,1]}φ`, as a complex function on `ℝ`. -/
def winLift (φ : ℝ → ℝ) : ℝ → ℂ := (Icc (-1 : ℝ) 1).indicator fun t => (φ t : ℂ)

/-- `‖1_{[−1,1]}φ‖² = 1_{[−1,1]}φ²` pointwise. -/
theorem norm_winLift_sq (φ : ℝ → ℝ) (t : ℝ) :
    ‖winLift φ t‖ ^ 2 = (Icc (-1 : ℝ) 1).indicator (fun t => φ t ^ 2) t := by
  by_cases ht : t ∈ Icc (-1 : ℝ) 1 <;> simp [winLift, ht, Complex.norm_real, sq_abs]

/-- The window lift is integrable. -/
theorem integrable_winLift {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) : Integrable (winLift φ) := by
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hφ
  exact (integrable_indicator_iff measurableSet_Icc).2
    ((Complex.continuous_ofReal.comp_continuousOn hφ).integrableOn_Icc)

/-- `∫_ℝ ‖1_{[−1,1]}φ‖² = ∫_{−1}^{1} φ²`. -/
theorem integral_norm_winLift_sq (φ : ℝ → ℝ) :
    ∫ t, ‖winLift φ t‖ ^ 2 = ∫ s in (-1 : ℝ)..1, φ s ^ 2 := by
  simp only [norm_winLift_sq]
  rw [integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le (by norm_num),
    integral_Icc_eq_integral_Ioc]

/-- The window lift is square integrable. -/
theorem memLp_winLift {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) : MemLp (winLift φ) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (integrable_winLift hφ).aestronglyMeasurable).2 ?_
  simp only [norm_winLift_sq]
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hφ
  exact (integrable_indicator_iff measurableSet_Icc).2 (hφ.pow 2).integrableOn_Icc

/-- **The transform of the window lift**: `𝓕(1_{[−1,1]}φ)(w) = ∫φ cos(2πwt) − i∫φ sin(2πwt)`. -/
theorem fourier_winLift {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) (w : ℝ) :
    𝓕 (winLift φ) w = ((∫ t in (-1 : ℝ)..1, φ t * cos (2 * π * w * t) : ℝ) : ℂ)
      - ((∫ t in (-1 : ℝ)..1, φ t * sin (2 * π * w * t) : ℝ) : ℂ) * Complex.I := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) • winLift φ v
      = (Icc (-1 : ℝ) 1).indicator (fun v => ((φ v * cos (2 * π * w * v) : ℝ) : ℂ)
          - ((φ v * sin (2 * π * w * v) : ℝ) : ℂ) * Complex.I) v := fun v => by
    by_cases hv : v ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hv, winLift, indicator_of_mem hv, smul_eq_mul, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        show -2 * π * v * w = -(2 * π * w * v) by ring, Real.cos_neg, Real.sin_neg]
      push_cast; ring
    · rw [indicator_of_notMem hv, winLift, indicator_of_notMem hv, smul_zero]
  simp only [e]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have h1 : ContinuousOn (fun v => φ v * cos (2 * π * w * v)) (uIcc (-1) 1) := hφ.mul (by fun_prop)
  have h2 : ContinuousOn (fun v => φ v * sin (2 * π * w * v)) (uIcc (-1) 1) := hφ.mul (by fun_prop)
  have i1 : IntervalIntegrable (fun v => ((φ v * cos (2 * π * w * v) : ℝ) : ℂ)) volume (-1) 1 :=
    (Complex.continuous_ofReal.comp_continuousOn h1).intervalIntegrable
  have i2 : IntervalIntegrable (fun v => ((φ v * sin (2 * π * w * v) : ℝ) : ℂ) * Complex.I) volume (-1) 1 :=
    ((Complex.continuous_ofReal.comp_continuousOn h2).mul continuousOn_const).intervalIntegrable
  rw [intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]

/-- `‖a − ib‖² = a² + b²` for real `a`, `b`. -/
theorem norm_sub_mul_I_sq (a b : ℝ) : ‖(a : ℂ) - (b : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp; ring

/-- `‖𝓕(1_{[−1,1]}φ)‖²` is integrable. -/
theorem integrable_fourier_winLift_sq {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) :
    Integrable fun w => ‖𝓕 (winLift φ) w‖ ^ 2 := by
  have hae := Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq (integrable_winLift hφ) (memLp_winLift hφ)
  have hm : MemLp (𝓕 (winLift φ)) 2 volume := (Lp.memLp _).ae_eq hae
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm

/-- **Plancherel for the window lift**: `∫_ℝ ‖𝓕(1_{[−1,1]}φ)‖² = ∫_{−1}^{1} φ²`. -/
theorem integral_fourier_winLift_sq {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) :
    ∫ w, ‖𝓕 (winLift φ) w‖ ^ 2 = ∫ s in (-1 : ℝ)..1, φ s ^ 2 := by
  rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_norm_sq_fourier (integrable_winLift hφ) (memLp_winLift hφ),
    integral_norm_winLift_sq]

/-- The extension at `ξ` is dominated by the transform at `cξ/2π`. -/
theorem psi_sq_le_fourier {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) (ξ : ℝ) :
    psi c φ ξ ^ 2 ≤ ‖𝓕 (winLift φ) (c / (2 * π) * ξ)‖ ^ 2 := by
  rw [fourier_winLift hφ, norm_sub_mul_I_sq]
  have e : ∀ t, 2 * π * (c / (2 * π) * ξ) * t = c * ξ * t := fun t => by field_simp
  simp only [e]
  have := sq_nonneg (∫ t in (-1 : ℝ)..1, φ t * sin (c * ξ * t))
  show (∫ t in (-1 : ℝ)..1, φ t * cos (c * ξ * t)) ^ 2 ≤ _
  linarith

/-- The derivative at `ξ` is dominated by `c` times the transform of `sφ` at `cξ/2π`. -/
theorem psiD_sq_le_fourier {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) (ξ : ℝ) :
    psiD c φ ξ ^ 2 ≤ c ^ 2 * ‖𝓕 (winLift fun s => s * φ s) (c / (2 * π) * ξ)‖ ^ 2 := by
  have hsφ : ContinuousOn (fun s => s * φ s) (uIcc (-1) 1) := continuousOn_id.mul hφ
  rw [fourier_winLift hsφ, norm_sub_mul_I_sq]
  have e : ∀ t, 2 * π * (c / (2 * π) * ξ) * t = c * ξ * t := fun t => by field_simp
  simp only [e]
  have hD : psiD c φ ξ = -c * ∫ t in (-1 : ℝ)..1, t * φ t * sin (c * ξ * t) := by
    rw [psiD, kint, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hD]
  have := sq_nonneg (∫ t in (-1 : ℝ)..1, t * φ t * cos (c * ξ * t))
  nlinarith [sq_nonneg c]

/-! ### Plancherel on the line -/

/-- `ξ ↦ ‖𝓕(1_{[−1,1]}φ)(cξ/2π)‖²` is integrable with integral `(2π/c)∫_{−1}^{1} φ²`. -/
theorem fourier_scaled {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) :
    Integrable (fun ξ => ‖𝓕 (winLift φ) (c / (2 * π) * ξ)‖ ^ 2) ∧
      ∫ ξ, ‖𝓕 (winLift φ) (c / (2 * π) * ξ)‖ ^ 2 = 2 * π / c * ∫ s in (-1 : ℝ)..1, φ s ^ 2 := by
  have ha : c / (2 * π) ≠ 0 := by positivity
  refine ⟨(integrable_fourier_winLift_sq hφ).comp_mul_left' ha, ?_⟩
  rw [Measure.integral_comp_mul_left (fun w => ‖𝓕 (winLift φ) w‖ ^ 2), integral_fourier_winLift_sq hφ,
    smul_eq_mul, inv_div, abs_of_pos (by positivity)]

/-- `ψ_φ²` is integrable on `ℝ`. -/
theorem integrable_psi_sq {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) :
    Integrable fun ξ => psi c φ ξ ^ 2 :=
  (fourier_scaled hc hφ).1.mono' ((continuous_psi hφ).pow 2).aestronglyMeasurable
    (ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact psi_sq_le_fourier hc hφ ξ)

/-- **The extension on the line**: `∫_ℝ ψ_φ² ≤ (2π/c)∫_{−1}^{1} φ²`. -/
theorem integral_psi_sq_le {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) :
    ∫ ξ, psi c φ ξ ^ 2 ≤ 2 * π / c * ∫ s in (-1 : ℝ)..1, φ s ^ 2 :=
  (integral_mono (integrable_psi_sq hc hφ) (fourier_scaled hc hφ).1 fun ξ => psi_sq_le_fourier hc hφ ξ).trans_eq
    (fourier_scaled hc hφ).2

/-- `ψ_φ′²` is integrable on `ℝ`. -/
theorem integrable_psiD_sq {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) :
    Integrable fun ξ => psiD c φ ξ ^ 2 :=
  ((fourier_scaled hc (φ := fun s => s * φ s) (continuousOn_id.mul hφ)).1.const_mul (c ^ 2)).mono'
    ((continuous_psiD hφ).pow 2).aestronglyMeasurable
    (ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact psiD_sq_le_fourier hc hφ ξ)

/-- **Bernstein on the line**: `∫_ℝ ψ_φ′² ≤ 2πc∫_{−1}^{1} s²φ²`. -/
theorem integral_psiD_sq_le_moment {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) :
    ∫ ξ, psiD c φ ξ ^ 2 ≤ 2 * π * c * ∫ s in (-1 : ℝ)..1, s ^ 2 * φ s ^ 2 := by
  have hsφ : ContinuousOn (fun s => s * φ s) (uIcc (-1) 1) := continuousOn_id.mul hφ
  have hF := fourier_scaled hc hsφ
  refine (integral_mono (integrable_psiD_sq hc hφ) (hF.1.const_mul (c ^ 2))
    fun ξ => psiD_sq_le_fourier hc hφ ξ).trans_eq ?_
  rw [integral_const_mul, hF.2]
  have e : ∫ s in (-1 : ℝ)..1, (s * φ s) ^ 2 = ∫ s in (-1 : ℝ)..1, s ^ 2 * φ s ^ 2 :=
    intervalIntegral.integral_congr fun s _ => by ring
  rw [e]
  field_simp

/-- **Bernstein on the line**: `∫_ℝ ψ_φ′² ≤ 2πc∫_{−1}^{1} φ²`. -/
theorem integral_psiD_sq_le {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) :
    ∫ ξ, psiD c φ ξ ^ 2 ≤ 2 * π * c * ∫ s in (-1 : ℝ)..1, φ s ^ 2 := by
  refine (integral_psiD_sq_le_moment hc hφ).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine intervalIntegral.integral_mono_on (by norm_num) ((continuousOn_pow 2).mul (hφ.pow 2)).intervalIntegrable
    (hφ.pow 2).intervalIntegrable fun s hs => ?_
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  nlinarith [sq_nonneg (φ s)]

/-! ### The rung span -/

/-- The span combination `Σ_{i<x} d_i h_{2i}`. -/
def spanG (c : ℝ) (x : ℕ) (d : ℕ → ℝ) (s : ℝ) : ℝ := ∑ i ∈ Finset.range x, d i * rung c (2 * i) s

/-- The source `φ = Σ_{i<x} b_i μ_{2i}⁻¹ h_{2i}` of the span profile with coefficients `b`. -/
def spanPhi (c : ℝ) (x : ℕ) (b : ℕ → ℝ) : ℝ → ℝ := spanG c x fun i => b i / muR c (2 * i)

section Span

variable {c lam : ℝ} {x : ℕ}

/-- A span combination is continuous on `[−1, 1]`. -/
theorem continuousOn_spanG (hex : ∀ i < x, ∃ χ, IsLevelIdx c (2 * i) χ) (d : ℕ → ℝ) :
    ContinuousOn (spanG c x d) (uIcc (-1) 1) := by
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  unfold spanG
  exact continuousOn_finsetSum _ fun i hi =>
    continuousOn_const.mul (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung (hex i (Finset.mem_range.1 hi)))

/-- **Parseval on the span**: `∫_{−1}^{1} (Σ_{i<x} d_i h_{2i})² = Σ_{i<x} d_i²`. -/
theorem integral_spanG_sq (hex : ∀ i < x, ∃ χ, IsLevelIdx c (2 * i) χ) (d : ℕ → ℝ) :
    ∫ s in (-1 : ℝ)..1, spanG c x d s ^ 2 = ∑ i ∈ Finset.range x, d i ^ 2 := by
  have hcont : ∀ i ∈ Finset.range x, ContinuousOn (rung c (2 * i)) (uIcc (-1) 1) := fun i hi => by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Cvs.Prolate.EvenRungsByIndex.continuousOn_rung (hex i (Finset.mem_range.1 hi))
  unfold spanG
  rw [Cvs.L2a.ModeTailNormCrossForm.integral_sq_finset_sum (fun m θ => d m * rung c (2 * m) θ)
    fun m hm m' hm' => ((continuousOn_const.mul (hcont m hm)).mul
      (continuousOn_const.mul (hcont m' hm'))).intervalIntegrable]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_eq_single m]
  · have e : ∫ θ in (-1 : ℝ)..1, d m * rung c (2 * m) θ * (d m * rung c (2 * m) θ)
        = d m ^ 2 * ∫ θ in (-1 : ℝ)..1, rung c (2 * m) θ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun θ _ => by ring
    rw [e, (rung_spec (hex m (Finset.mem_range.1 hm))).2.2.2.2.2, mul_one]
  · intro m' hm' hne
    have e : ∫ θ in (-1 : ℝ)..1, d m * rung c (2 * m) θ * (d m' * rung c (2 * m') θ)
        = d m * d m' * ∫ θ in (-1 : ℝ)..1, rung c (2 * m) θ * rung c (2 * m') θ := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun θ _ => by ring
    have hk : (⟨2 * m, hex m (Finset.mem_range.1 hm)⟩ : Cvs.Prolate.EvenRungParseval.LevelIdx c)
        ≠ ⟨2 * m', hex m' (Finset.mem_range.1 hm')⟩ := fun h => hne (by
      have := congrArg Subtype.val h; simp only at this; omega)
    rw [e, Cvs.Prolate.EvenRungParseval.integral_rung_mul_rung hk, mul_zero]
  · intro h; exact absurd hm h

/-- A positive floor `λ ≤ λ_k` forces `μ_k ≠ 0`. -/
theorem muR_ne_zero_of_lam {k : ℕ} (hlam0 : 0 < lam) (hl : lam ≤ lamR c k) : muR c k ≠ 0 := by
  intro h
  rw [lamR, h, zero_mul] at hl
  norm_num at hl
  linarith

/-- **The span profile is the extension of its source** on `[−1, 1]`: `ψ_φ = G`. -/
theorem psi_spanPhi (hex : ∀ i < x, ∃ χ, IsLevelIdx c (2 * i) χ) (hlam0 : 0 < lam)
    (hlam : ∀ i < x, lam ≤ lamR c (2 * i)) (b : ℕ → ℝ) :
    ∀ s ∈ Icc (-1 : ℝ) 1, psi c (spanPhi c x b) s = spanG c x b s := by
  intro s hs
  have hcont : ∀ i ∈ Finset.range x, ContinuousOn (rung c (2 * i)) (uIcc (-1) 1) := fun i hi => by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Cvs.Prolate.EvenRungsByIndex.continuousOn_rung (hex i (Finset.mem_range.1 hi))
  simp only [psi, kint, spanPhi, spanG, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum
    (f := fun i t => b i / muR c (2 * i) * rung c (2 * i) t * cos (c * s * t)) fun i hi =>
    ((continuousOn_const.mul (hcont i hi)).mul (by fun_prop)).intervalIntegrable]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have e : ∫ t in (-1 : ℝ)..1, b i / muR c (2 * i) * rung c (2 * i) t * cos (c * s * t)
      = b i / muR c (2 * i) * psi c (rung c (2 * i)) s := by
    rw [psi, kint, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [e, psi_rung (hex i hi') s hs]
  field_simp [muR_ne_zero_of_lam hlam0 (hlam i hi')]

/-- **The source norm**: `∫_{−1}^{1} φ² ≤ (c/(2πλ)) ∫_{−1}^{1} G²`, from `μ_{2i}⁻² = c/(2πλ_{2i})`. -/
theorem integral_spanPhi_sq_le (hc : 0 < c) (hex : ∀ i < x, ∃ χ, IsLevelIdx c (2 * i) χ) (hlam0 : 0 < lam)
    (hlam : ∀ i < x, lam ≤ lamR c (2 * i)) (b : ℕ → ℝ) :
    ∫ s in (-1 : ℝ)..1, spanPhi c x b s ^ 2 ≤ c / (2 * π * lam) * ∫ s in (-1 : ℝ)..1, spanG c x b s ^ 2 := by
  rw [spanPhi, integral_spanG_sq hex, integral_spanG_sq hex, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hμ := muR_ne_zero_of_lam hlam0 (hlam i hi')
  have hL : lamR c (2 * i) = muR c (2 * i) ^ 2 * (c / (2 * π)) := by
    rw [lamR, mul_pow, sq_sqrt (by positivity)]
  have hLpos : 0 < lamR c (2 * i) := lt_of_lt_of_le hlam0 (hlam i hi')
  have e : (b i / muR c (2 * i)) ^ 2 = b i ^ 2 * (c / (2 * π)) / lamR c (2 * i) := by
    rw [hL]; field_simp
  rw [e, show c / (2 * π * lam) * b i ^ 2 = b i ^ 2 * (c / (2 * π)) / lam by field_simp]
  exact div_le_div_of_nonneg_left (by positivity) hlam0 (hlam i hi')

variable {G G₁ : ℝ → ℝ} {b : ℕ → ℝ}

/-- The source norm against `‖G‖²` on `(0, 1)`: `∫_{−1}^{1} φ² ≤ (c/(πλ))∫₀¹ G²`. -/
theorem integral_spanPhi_sq_le_half (hc : 0 < c) (hex : ∀ i < x, ∃ χ, IsLevelIdx c (2 * i) χ) (hlam0 : 0 < lam)
    (hlam : ∀ i < x, lam ≤ lamR c (2 * i)) (hG : ∀ s ∈ Icc (-1 : ℝ) 1, G s = spanG c x b s) :
    ∫ s in (-1 : ℝ)..1, spanPhi c x b s ^ 2 ≤ c / (π * lam) * ∫ s in (0 : ℝ)..1, G s ^ 2 := by
  have hφ : ContinuousOn (spanPhi c x b) (uIcc (-1) 1) := continuousOn_spanG hex _
  have hψ := psi_spanPhi hex hlam0 hlam b
  have e1 : ∫ s in (-1 : ℝ)..1, spanG c x b s ^ 2 = ∫ s in (-1 : ℝ)..1, psi c (spanPhi c x b) s ^ 2 :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs; rw [hψ s hs]
  have e2 : ∫ s in (0 : ℝ)..1, G s ^ 2 = ∫ s in (0 : ℝ)..1, psi c (spanPhi c x b) s ^ 2 :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le zero_le_one] at hs
      have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
      rw [hψ s hs', hG s hs']
  have hev := Cvs.Prolate.SincTopIsRung.integral_even_eq_two_mul
    (v := fun s => psi c (spanPhi c x b) s ^ 2) ((continuous_psi hφ).pow 2)
    fun s => by simp only [psi_neg]
  have h := integral_spanPhi_sq_le hc hex hlam0 hlam b
  rw [e1, hev, ← e2] at h
  calc _ ≤ _ := h
    _ = _ := by field_simp

/-- On `[−1, 1]` the derivative `G₁` of the span profile is `ψ_φ′`. -/
theorem deriv_eq_psiD (hex : ∀ i < x, ∃ χ, IsLevelIdx c (2 * i) χ) (hlam0 : 0 < lam)
    (hlam : ∀ i < x, lam ≤ lamR c (2 * i)) (hG : ∀ s ∈ Icc (-1 : ℝ) 1, G s = spanG c x b s)
    (hG₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s) :
    ∀ s ∈ Icc (-1 : ℝ) 1, G₁ s = psiD c (spanPhi c x b) s := by
  intro s hs
  have hφ : ContinuousOn (spanPhi c x b) (uIcc (-1) 1) := continuousOn_spanG hex _
  have hψ := psi_spanPhi hex hlam0 hlam b
  have hs' : s ∈ uIcc (-1 : ℝ) 1 := by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have h1 : HasDerivWithinAt (psi c (spanPhi c x b)) (G₁ s) (Icc (-1) 1) s :=
    (hG₁ s hs').hasDerivWithinAt.congr_of_mem (fun t ht => (hψ t ht).trans (hG t ht).symm) hs
  exact (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1) s hs).eq_deriv _ h1
    (hasDerivAt_psi' hφ s).hasDerivWithinAt

/-! ### Bernstein and Nikolskii on the span -/

/-- **Nikolskii on the span**: `G(t)² ≤ (2c/(πλ))∫₀¹ G²` for `t ∈ [−1, 1]`. -/
theorem sq_le_nikolskii (hc : 0 < c) (hex : ∀ i < x, ∃ χ, IsLevelIdx c (2 * i) χ) (hlam0 : 0 < lam)
    (hlam : ∀ i < x, lam ≤ lamR c (2 * i)) (hG : ∀ s ∈ Icc (-1 : ℝ) 1, G s = spanG c x b s) :
    ∀ t ∈ Icc (-1 : ℝ) 1, G t ^ 2 ≤ 2 * c / (π * lam) * ∫ s in (0 : ℝ)..1, G s ^ 2 := by
  intro t ht
  have hφ : ContinuousOn (spanPhi c x b) (uIcc (-1) 1) := continuousOn_spanG hex _
  have h := integral_spanPhi_sq_le_half hc hex hlam0 hlam hG
  rw [hG t ht, ← psi_spanPhi hex hlam0 hlam b t ht]
  calc _ ≤ 2 * ∫ s in (-1 : ℝ)..1, spanPhi c x b s ^ 2 := psi_sq_le hφ t
    _ ≤ 2 * (c / (π * lam) * ∫ s in (0 : ℝ)..1, G s ^ 2) := by linarith
    _ = _ := by ring

/-- **Nikolskii for the derivative on the span**: `G₁(t)² ≤ (2c³/(3πλ))∫₀¹ G²` for `t ∈ [−1, 1]`. -/
theorem deriv_sq_le_nikolskii (hc : 0 < c) (hex : ∀ i < x, ∃ χ, IsLevelIdx c (2 * i) χ) (hlam0 : 0 < lam)
    (hlam : ∀ i < x, lam ≤ lamR c (2 * i)) (hG : ∀ s ∈ Icc (-1 : ℝ) 1, G s = spanG c x b s)
    (hG₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s) :
    ∀ t ∈ Icc (-1 : ℝ) 1, G₁ t ^ 2 ≤ 2 * c ^ 3 / (3 * π * lam) * ∫ s in (0 : ℝ)..1, G s ^ 2 := by
  intro t ht
  have hφ : ContinuousOn (spanPhi c x b) (uIcc (-1) 1) := continuousOn_spanG hex _
  have h := integral_spanPhi_sq_le_half hc hex hlam0 hlam hG
  rw [deriv_eq_psiD hex hlam0 hlam hG hG₁ t ht]
  calc _ ≤ 2 * c ^ 2 / 3 * ∫ s in (-1 : ℝ)..1, spanPhi c x b s ^ 2 := psiD_sq_le hφ t
    _ ≤ 2 * c ^ 2 / 3 * (c / (π * lam) * ∫ s in (0 : ℝ)..1, G s ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

end Span

/-! ### The spine profile at `c = 2πx` -/

open Classical in
/-- The span coefficients of the spine profile: `b_i = a_i·1_{i∈S} − 1_{i=0}·Σ_j a_j α_j`. -/
def spineCoef (c : ℝ) (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (i : ℕ) : ℝ :=
  (if h : i ∈ Cvs.Approximant.SpineSubspace.SF x then a ⟨i, h⟩ else 0)
    - if i = 0 then ∑ j, a j * Cvs.Approximant.DeepIndexSpineSpan.alpha c j else 0

/-- **The spine profile lies in the rung span**: `G_a = Σ_{i<x} b_i h_{2i}` for `1 ≤ x`. -/
theorem spineG_eq_spanG (c : ℝ) {x : ℕ} (hx : 1 ≤ x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (s : ℝ) :
    Cvs.Approximant.DeepIndexSpineSpan.spineG c a s = spanG c x (spineCoef c x a) s := by
  classical
  have hsub : Cvs.Approximant.SpineSubspace.SF x ⊆ Finset.range x := fun j hj =>
    Finset.mem_range.2 (Cvs.Approximant.SpineSubspace.SF_lt x j hj)
  simp only [spanG, spineCoef, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, dite_mul]
  rw [Finset.sum_ite_eq' (Finset.range x) 0, ite_eq_left (Finset.mem_range.2 hx),
    ← Finset.sum_subset hsub (fun i _ hi => by rw [dite_eq_right hi])]
  rw [← Finset.sum_attach (Cvs.Approximant.SpineSubspace.SF x)]
  simp only [Finset.coe_mem, dite_eq_left, Subtype.coe_eta]
  unfold Cvs.Approximant.DeepIndexSpineSpan.spineG
  rw [Finset.univ_eq_attach]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, mul_zero, mul_assoc]

/-- The spine hypotheses at `c = 2πx`: every rung `h_{2i}`, `i < x`, exists and has `λ ≥ ½` (Landau). -/
theorem spine_landau {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    (∀ i < x, ∃ χ, IsLevelIdx (2 * π * x) (2 * i) χ) ∧ ∀ i < x, (1 : ℝ) / 2 ≤ lamR (2 * π * x) (2 * i) :=
  ⟨fun i hi => Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨i, Finset.mem_range.2 hi⟩,
    fun _ hi => Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hi⟩

/-- `80 ≤ 2πx` forces `1 ≤ x`. -/
theorem one_le_of_scale {x : ℕ} (hx : 80 ≤ 2 * π * x) : 1 ≤ x := by
  rcases Nat.eq_zero_or_pos x with h | h
  · rw [h] at hx; simp at hx; linarith
  · exact h

/-- **Nikolskii for the spine profile**: `G(t)² ≤ (4c/π)∫₀¹ G² = 8x∫₀¹ G²` on `[−1, 1]` at `c = 2πx`. -/
theorem spine_nikolskii {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∀ t ∈ Icc (-1 : ℝ) 1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a t ^ 2
      ≤ 8 * x * ∫ s in (0 : ℝ)..1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a s ^ 2 := by
  obtain ⟨hex, hlam⟩ := spine_landau hx
  intro t ht
  have h := sq_le_nikolskii (by linarith) hex (by norm_num) hlam
    (fun s _ => spineG_eq_spanG _ (one_le_of_scale hx) a s) t ht
  calc _ ≤ _ := h
    _ = _ := by field_simp; ring

/-- **Nikolskii for the spine derivative**: `G₁(t)² ≤ (4c³/(3π))∫₀¹ G²` on `[−1, 1]` at `c = 2πx`. -/
theorem spine_deriv_nikolskii {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ)
    {G₁ : ℝ → ℝ}
    (hG₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) (G₁ s) s) :
    ∀ t ∈ Icc (-1 : ℝ) 1, G₁ t ^ 2
      ≤ 4 * (2 * π * x) ^ 3 / (3 * π) * ∫ s in (0 : ℝ)..1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a s ^ 2 := by
  obtain ⟨hex, hlam⟩ := spine_landau hx
  intro t ht
  have h := deriv_sq_le_nikolskii (by linarith) hex (by norm_num) hlam
    (fun s _ => spineG_eq_spanG _ (one_le_of_scale hx) a s) hG₁ t ht
  calc _ ≤ _ := h
    _ = _ := by field_simp; ring

end Cvs.Prolate.RungSpanBernsteinNikolskii
