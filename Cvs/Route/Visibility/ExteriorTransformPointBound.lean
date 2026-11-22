import Mathlib
import Cvs.Prolate.Mellin.TailMellinPlancherel
import Cvs.Route.Visibility.ExteriorTransformHolomorphy
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior transform at a point is bounded by the exterior Plancherel integral

With `X = M[1_{(1,∞)}E_G]` and `Ext(σ) = ∫₁^∞ E_G(θ)² θ^{2σ−1} dθ`: `Ext` is increasing on `σ < 1`,
each line `g ↦ |X(σ + ig)|²` is integrable, and for `0 < r`, `Re s₀ + r < 1`,
`|X(s₀)|² ≤ (4/r)·Ext(Re s₀ + r)`; at `r = 2δ` this is `|X(s₀)|² ≤ (2/δ)·Ext(Re s₀ + 2δ)`,
stated also for the spine profile at `a = 1/x`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology Metric
open Cvs.Xi.EImageWindowPoisson (eimage)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Prolate.Mellin.TailMellinPlancherel (logTail)
open scoped FourierTransform

namespace Cvs.Route.Visibility.ExteriorTransformPointBound

/-- The exterior Plancherel integral `Ext(σ) = ∫₁^∞ E_G(θ)² θ^{2σ−1} dθ`. -/
def extInt (a : ℝ) (G : ℝ → ℝ) (σ : ℝ) : ℝ := ∫ θ in Ioi 1, eimage a G θ ^ 2 * θ ^ (2 * σ - 1)

/-! ### (a) `Ext` is increasing -/

/-- For `σ < 1` the integrand of `Ext(σ)` is integrable on `(1, ∞)`. -/
theorem integrableOn_extInt {F : ℝ → ℝ} (hF : Measurable F) {K : ℝ}
    (hK : ∀ w, 1 < w → |F w| ≤ K / w) {σ : ℝ} (hσ : σ < 1) :
    IntegrableOn (fun θ => F θ ^ 2 * θ ^ (2 * σ - 1)) (Ioi 1) := by
  have hdom : IntegrableOn (fun θ : ℝ => K ^ 2 * θ ^ (2 * σ - 3)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine hdom.mono' ((hF.pow_const 2).mul (measurable_id.pow_const _)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun θ (hθ : 1 < θ) => ?_)
  have hθ0 : 0 < θ := lt_trans one_pos hθ
  have hp : 0 < θ ^ (2 * σ - 1) := Real.rpow_pos_of_pos hθ0 _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos hp]
  have h1 : F θ ^ 2 ≤ (K / θ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hK θ hθ) 2
  calc F θ ^ 2 * θ ^ (2 * σ - 1) ≤ (K / θ) ^ 2 * θ ^ (2 * σ - 1) :=
        mul_le_mul_of_nonneg_right h1 hp.le
    _ = K ^ 2 * θ ^ (2 * σ - 3) := by
        rw [div_pow, show 2 * σ - 3 = (2 * σ - 1) + (-2 : ℝ) by ring,
          Real.rpow_add hθ0, Real.rpow_neg hθ0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
        field_simp

/-- **`Ext` is increasing**: for `σ ≤ σ' < 1`, `Ext(σ) ≤ Ext(σ')`. -/
theorem extInt_mono {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {σ σ' : ℝ} (hle : σ ≤ σ') (hσ' : σ' < 1) :
    extInt a G σ ≤ extInt a G σ' := by
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  obtain ⟨K, -, hK⟩ := Cvs.Xi.EImageMellin.abs_eimage_le ha hG hG₁ hGi
  have hm := Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc
  have hK' : ∀ w, 1 < w → |eimage a G w| ≤ K / w := fun w hw => hK w (lt_trans one_pos hw)
  refine setIntegral_mono_on (integrableOn_extInt hm hK' (lt_of_le_of_lt hle hσ'))
    (integrableOn_extInt hm hK' hσ') measurableSet_Ioi fun θ (hθ : 1 < θ) => ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hθ.le (by linarith))
    (sq_nonneg _)

/-! ### (b) each vertical line is square integrable -/

/-- For measurable `F` with `|F(θ)| ≤ K/θ` on `θ > 1` and `σ < 1`,
`g ↦ |M[1_{(1,∞)}F](σ + ig)|²` is integrable on `ℝ`. -/
theorem integrable_norm_sq_mellinR_indicator {F : ℝ → ℝ} (hF : Measurable F) {K : ℝ}
    (hK : ∀ w, 1 < w → |F w| ≤ K / w) {σ : ℝ} (hσ : σ < 1) :
    Integrable fun g : ℝ => ‖mellinR ((Ioi (1 : ℝ)).indicator F) (σ + g * I)‖ ^ 2 := by
  set f : ℝ → ℝ := fun w => F w * w ^ (σ - 1 / 2) with hfdef
  have hfm : Measurable f := hF.mul (measurable_id.pow_const _)
  have hb : 0 < 1 - σ := by linarith
  have hdom : ∀ u, ‖logTail f u‖
      ≤ (Ioi (0 : ℝ)).indicator (fun u => K * Real.exp (-(1 - σ) * u)) u := fun u => by
    have := Cvs.Route.Visibility.ExteriorTransformHolomorphy.norm_logTail_le (F := F) (σ := σ) hK u
    rw [show (fun u : ℝ => K * Real.exp ((σ - 1) * u)) = fun u => K * Real.exp (-(1 - σ) * u) from
      funext fun u => by ring_nf] at this
    exact this
  have hmeas := Cvs.Prolate.Mellin.TailMellinPlancherel.measurable_logTail hfm
  have hint : Integrable (logTail f) :=
    (Cvs.Route.Visibility.ExteriorTransformHolomorphy.integrable_indicator_exp hb).mono' hmeas.aestronglyMeasurable (ae_of_all _ hdom)
  have hL2 : MemLp (logTail f) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 ?_
    refine (Cvs.Route.Visibility.ExteriorTransformHolomorphy.integrable_indicator_exp (K := K ^ 2) (by linarith : 0 < 2 * (1 - σ))).mono'
      (hmeas.norm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := hdom u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hu] at h ⊢
      calc ‖logTail f u‖ ^ 2 ≤ (K * Real.exp (-(1 - σ) * u)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = K ^ 2 * Real.exp (-(2 * (1 - σ)) * u) := by
            rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    · rw [indicator_of_notMem hu] at h ⊢
      have : ‖logTail f u‖ = 0 := le_antisymm h (norm_nonneg _)
      rw [this]; norm_num
  have hFi : Integrable fun ξ => ‖𝓕 (logTail f) ξ‖ ^ 2 := by
    have hae := Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hint hL2
    have hLp := (Lp.memLp (𝓕 (hL2.toLp (logTail f)) : Lp ℂ 2 (volume : Measure ℝ)))
    refine ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 hLp).congr ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ]
  simp only [Cvs.Route.Visibility.ExteriorTransformHolomorphy.mellinR_indicator_eq, Cvs.Prolate.Mellin.TailMellinPlancherel.mellin_eq_fourier_logTail]
  have e : ∀ t : ℝ, -(t / (2 * Real.pi)) = (-(2 * Real.pi)⁻¹) * t := fun t => by ring
  simp only [e]
  exact hFi.comp_mul_left' (by simp [Real.pi_ne_zero])

/-! ### (c) disc integral bounded by line integrals -/

/-! ### (d) the pointwise bound -/

end Cvs.Route.Visibility.ExteriorTransformPointBound
