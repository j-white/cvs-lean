import Mathlib
import Cvs.WeilForm.GaussianRegulariser
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The spectral density of a window test function is integrable

    ∫ ‖𝓕 (cf f) ξ‖² dξ < ∞

`Cvs.WeilForm.RegularisedSpectralMass`'s bound does not depend on the regularisation, and the multipliers rise to `1`, so
monotone convergence removes them.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Filter
open scoped FourierTransform ENNReal

namespace Cvs.WeilForm.SpectralDensityIntegrable

/-- **The spectral density is integrable.**  Plancherel's conclusion for a time-limited
function, as an inequality. -/
theorem integrable_fourier_sq {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hfint : Integrable f (volume : Measure ℝ)) :
    Integrable (fun ξ : ℝ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2) (volume : Measure ℝ) := by
  have hcf : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf f) (volume : Measure ℝ) := hfint.ofReal
  have hFc : Continuous (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hcf
  have hFcont : Continuous (fun ξ : ℝ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2) :=
    hFc.norm.pow 2
  refine ⟨hFcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  set F : ℝ → ℝ := fun ξ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 with hFdef
  set E : ℝ := ∫ x : ℝ, f x ^ 2 with hE
  set c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hc
  have hcpos : ∀ n, 0 < c n := fun n => by rw [hc]; positivity
  have hFnn : ∀ ξ, 0 ≤ F ξ := fun ξ => sq_nonneg _
  -- the regularised integrands
  set g : ℕ → ℝ → ℝ≥0∞ :=
    fun n ξ => ENNReal.ofReal (F ξ * Cvs.WeilForm.GaussianRegulariser.gauss (c n) ξ) with hg
  have hgmeas : ∀ n, AEMeasurable (g n) (volume : Measure ℝ) := by
    intro n
    refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
    exact (hFcont.mul (by unfold Cvs.WeilForm.GaussianRegulariser.gauss; fun_prop)).measurable
  have hcmono : ∀ {m n : ℕ}, m ≤ n → c n ≤ c m := by
    intro m n hmn
    rw [hc]
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.succ_le_succ hmn
  have hgmono : ∀ ξ, Monotone fun n => g n ξ := by
    intro ξ m n hmn
    rw [hg]
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_left
      (Cvs.WeilForm.GaussianRegulariser.gauss_mono (hcmono hmn)) (hFnn ξ)
  have hgtend : ∀ ξ, Tendsto (fun n => g n ξ) atTop (nhds (ENNReal.ofReal (F ξ))) := by
    intro ξ
    have hcz : Tendsto c atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · rw [hc]; exact tendsto_one_div_add_atTop_nhds_zero_nat
      · exact Filter.Eventually.of_forall fun n => hcpos n
    have h1 : Tendsto (fun n => Cvs.WeilForm.GaussianRegulariser.gauss (c n) ξ) atTop (nhds 1) :=
      (Cvs.WeilForm.GaussianRegulariser.tendsto_gauss ξ).comp hcz
    have h2 : Tendsto (fun n => F ξ * Cvs.WeilForm.GaussianRegulariser.gauss (c n) ξ) atTop
        (nhds (F ξ)) := by
      have := h1.const_mul (F ξ)
      simpa using this
    exact (ENNReal.continuous_ofReal.tendsto _).comp h2
  -- monotone convergence
  have hmct := lintegral_tendsto_of_tendsto_of_monotone (μ := (volume : Measure ℝ))
    hgmeas (Filter.Eventually.of_forall hgmono) (Filter.Eventually.of_forall hgtend)
  -- each regularised integral is below the energy
  have hMbd : ∀ ξ, F ξ ≤ (∫ x : ℝ, ‖Cvs.WeilForm.SelfConvolutionTransform.cf f x‖) ^ 2 := by
    intro ξ
    have h := VectorFourier.norm_fourierIntegral_le_integral_norm
      (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (L := innerₗ ℝ)
      (f := Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ
    have hnn : 0 ≤ ∫ x : ℝ, ‖Cvs.WeilForm.SelfConvolutionTransform.cf f x‖ :=
      integral_nonneg fun x => norm_nonneg _
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hint_n : ∀ n, Integrable
      (fun ξ : ℝ => F ξ * Cvs.WeilForm.GaussianRegulariser.gauss (c n) ξ) (volume : Measure ℝ) := by
    intro n
    set M : ℝ := (∫ x : ℝ, ‖Cvs.WeilForm.SelfConvolutionTransform.cf f x‖) ^ 2 with hM
    have hgaussInt : Integrable (Cvs.WeilForm.GaussianRegulariser.gauss (c n)) (volume : Measure ℝ) := by
      have hpc : (0:ℝ) < π * c n := by have := hcpos n; positivity
      have hgi := integrable_exp_neg_mul_sq hpc
      refine hgi.congr (Filter.Eventually.of_forall fun x => ?_)
      rw [Cvs.WeilForm.GaussianRegulariser.gauss]
      exact congrArg Real.exp (by ring)
    refine (hgaussInt.const_mul M).mono'
      (hFcont.aestronglyMeasurable.mul hgaussInt.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFnn ξ),
      abs_of_pos (Cvs.WeilForm.GaussianRegulariser.gauss_pos (c n) ξ)]
    exact mul_le_mul_of_nonneg_right (hMbd ξ)
      (Cvs.WeilForm.GaussianRegulariser.gauss_pos (c n) ξ).le
  have hle_n : ∀ n, (∫⁻ ξ : ℝ, g n ξ) ≤ ENNReal.ofReal E := by
    intro n
    have hnn : 0 ≤ᵐ[(volume : Measure ℝ)]
        fun ξ : ℝ => F ξ * Cvs.WeilForm.GaussianRegulariser.gauss (c n) ξ :=
      Filter.Eventually.of_forall fun ξ =>
        mul_nonneg (hFnn ξ) (Cvs.WeilForm.GaussianRegulariser.gauss_pos (c n) ξ).le
    rw [hg, ← ofReal_integral_eq_lintegral_ofReal (hint_n n) hnn]
    exact ENNReal.ofReal_le_ofReal
      (Cvs.WeilForm.RegularisedSpectralMass.integral_fourier_sq_gauss_le (hcpos n) hf hfint)
  -- pass to the limit
  have hlim : (∫⁻ ξ : ℝ, ENNReal.ofReal (F ξ)) ≤ ENNReal.ofReal E :=
    le_of_tendsto hmct (Filter.Eventually.of_forall hle_n)
  have henorm : (∫⁻ ξ : ℝ, ‖F ξ‖ₑ) = ∫⁻ ξ : ℝ, ENNReal.ofReal (F ξ) := by
    refine lintegral_congr fun ξ => ?_
    rw [Real.eNorm_eq_ofReal (hFnn ξ)]
  rw [henorm]
  exact lt_of_le_of_lt hlim ENNReal.ofReal_lt_top

end Cvs.WeilForm.SpectralDensityIntegrable
