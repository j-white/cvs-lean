import Mathlib
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.PlancherelL1L2SpectralDensity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cosine synthesis from `I = [−½, ½]` and its Plancherel bound

`S_c g(t) = ∫_I cos(cst) g(s) ds` is the real part of `𝓕(1_I g)(ct/2π)`, so `∫_ℝ (S_c g)² ≤ (2π/c)∫_I g²`;
and `∫_I f · S_c g = ∫_I g · ∫_I cos(cst) f(t) dt` for `f ∈ L¹(I)` and continuous `g`.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform

namespace Cvs.Prolate.Hardy.CosineSynthesisPlancherel

/-- The central interval `I = [−1/2, 1/2]`. -/
abbrev cI : Set ℝ := Icc (-1 / 2) (1 / 2)

/-- The cosine synthesis `S_c g(t) = ∫_I cos(cst) g(s) ds`. -/
def synth (c : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in cI, cos (c * s * t) * g s

/-- The complex zero extension `1_I g`. -/
def ext (g : ℝ → ℝ) : ℝ → ℂ := cI.indicator fun s => (g s : ℂ)

theorem integrable_ext {g : ℝ → ℝ} (hg : Continuous g) : Integrable (ext g) := by
  unfold ext
  rw [integrable_indicator_iff measurableSet_Icc]
  exact (Complex.continuous_ofReal.comp hg).continuousOn.integrableOn_compact isCompact_Icc

theorem memLp_ext {g : ℝ → ℝ} (hg : Continuous g) : MemLp (ext g) 2 (volume : Measure ℝ) := by
  unfold ext
  rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_ofReal.comp hg).continuousOn (s := cI)
  refine MemLp.of_bound ((Complex.continuous_ofReal.comp hg).aestronglyMeasurable) M ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hM s hs

/-- `S_c g(t) = Re 𝓕(1_I g)(ct/2π)`. -/
theorem synth_eq_re (c : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    synth c g t = (𝓕 (ext g) (c / (2 * π) * t)).re := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hint : Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * (c / (2 * π) * t)) * Complex.I) • ext g v) := by
    refine (integrable_ext hg).bdd_mul (c := 1) ?_ ?_
    · exact (Continuous.cexp (by fun_prop)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [Complex.norm_exp_ofReal_mul_I]
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
  unfold ext synth
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  ext v
  by_cases hv : v ∈ cI
  · simp only [indicator_of_mem hv, smul_eq_mul, Complex.reCLM_apply]
    rw [Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
    rw [show -2 * π * v * (c / (2 * π) * t) = -(c * v * t) by field_simp, Real.cos_neg]
  · rw [indicator_of_notMem hv, indicator_of_notMem hv]; simp

theorem memLp_fourier_ext {g : ℝ → ℝ} (hg : Continuous g) : MemLp (𝓕 (ext g)) 2 (volume : Measure ℝ) :=
  (Lp.memLp _).ae_eq (Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq (integrable_ext hg) (memLp_ext hg))

theorem continuous_synth (c : ℝ) {g : ℝ → ℝ} (hg : Continuous g) : Continuous (synth c g) := by
  have hF : Continuous (𝓕 (ext g)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) (integrable_ext hg)
  have : synth c g = fun t => (𝓕 (ext g) (c / (2 * π) * t)).re := funext (synth_eq_re c hg)
  rw [this]
  exact Complex.continuous_re.comp (hF.comp (continuous_const.mul continuous_id))

/-- `∫_ℝ ‖1_I g‖² = ∫_I g²`. -/
theorem integral_norm_sq_ext (g : ℝ → ℝ) : ∫ s, ‖ext g s‖ ^ 2 = ∫ s in cI, g s ^ 2 := by
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  ext s
  by_cases hs : s ∈ cI
  · rw [indicator_of_mem hs]; simp [ext, indicator_of_mem hs, Complex.norm_real, sq_abs]
  · rw [indicator_of_notMem hs]; simp [ext, indicator_of_notMem hs]

theorem integrable_norm_sq_fourier_comp {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun t => ‖𝓕 (ext g) (c / (2 * π) * t)‖ ^ 2) := by
  have h := (memLp_two_iff_integrable_sq_norm (memLp_fourier_ext hg).aestronglyMeasurable).1 (memLp_fourier_ext hg)
  exact h.comp_mul_left' (by positivity)

theorem sq_synth_le (c : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    synth c g t ^ 2 ≤ ‖𝓕 (ext g) (c / (2 * π) * t)‖ ^ 2 := by
  rw [synth_eq_re c hg, sq, ← Complex.normSq_eq_norm_sq]
  exact Complex.re_sq_le_normSq _

theorem integrable_synth_sq {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun t => synth c g t ^ 2) :=
  (integrable_norm_sq_fourier_comp hc hg).mono' ((continuous_synth c hg).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact sq_synth_le c hg t)

theorem memLp_synth {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : Continuous g) :
    MemLp (synth c g) 2 (volume : Measure ℝ) :=
  (memLp_two_iff_integrable_sq (continuous_synth c hg).aestronglyMeasurable).2 (integrable_synth_sq hc hg)

/-- **Plancherel for the synthesis**: `∫_ℝ (S_c g)² ≤ (2π/c)∫_I g²`. -/
theorem integral_synth_sq_le {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ t, synth c g t ^ 2 ≤ 2 * π / c * ∫ s in cI, g s ^ 2 := by
  calc ∫ t, synth c g t ^ 2 ≤ ∫ t, ‖𝓕 (ext g) (c / (2 * π) * t)‖ ^ 2 :=
        integral_mono (integrable_synth_sq hc hg) (integrable_norm_sq_fourier_comp hc hg) (sq_synth_le c hg)
    _ = 2 * π / c * ∫ s in cI, g s ^ 2 := by
        rw [Measure.integral_comp_mul_left (fun ξ => ‖𝓕 (ext g) ξ‖ ^ 2),
          Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_norm_sq_fourier (integrable_ext hg) (memLp_ext hg), integral_norm_sq_ext,
          smul_eq_mul, inv_div, abs_of_pos (by positivity)]

/-- **Fubini**: `∫_I f · S_c g = ∫_I g(s) ∫_I cos(cst) f(t) dt ds`. -/
theorem integral_mul_synth (c : ℝ) {f g : ℝ → ℝ} (hf : IntegrableOn f cI) (hg : Continuous g) :
    ∫ t in cI, f t * synth c g t = ∫ s in cI, g s * ∫ t in cI, cos (c * s * t) * f t := by
  have hgI : IntegrableOn g cI := hg.continuousOn.integrableOn_compact isCompact_Icc
  have hint : Integrable (Function.uncurry fun t s => f t * (cos (c * s * t) * g s))
      ((volume.restrict cI).prod (volume.restrict cI)) := by
    refine (hf.norm.mul_prod hgI.norm).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact hf.aestronglyMeasurable.comp_fst.mul
        ((Real.continuous_cos.comp (by fun_prop : Continuous fun z : ℝ × ℝ => c * z.2 * z.1)).aestronglyMeasurable.mul
          hgI.aestronglyMeasurable.comp_snd)
    · change |f z.1 * (cos (c * z.2 * z.1) * g z.2)| ≤ ‖f z.1‖ * ‖g z.2‖
      rw [abs_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := abs_cos_le_one (c * z.2 * z.1)
      calc |f z.1| * (|cos (c * z.2 * z.1)| * |g z.2|) ≤ |f z.1| * (1 * |g z.2|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) (abs_nonneg _)
        _ = |f z.1| * |g z.2| := by ring
  have e1 : ∫ t in cI, f t * synth c g t = ∫ t in cI, ∫ s in cI, f t * (cos (c * s * t) * g s) := by
    congr 1; ext t; rw [synth, integral_const_mul]
  have e2 : ∫ s in cI, g s * ∫ t in cI, cos (c * s * t) * f t =
      ∫ s in cI, ∫ t in cI, f t * (cos (c * s * t) * g s) := by
    congr 1; ext s; rw [← integral_const_mul]; congr 1; ext t; ring
  rw [e1, e2, integral_integral_swap hint]

end Cvs.Prolate.Hardy.CosineSynthesisPlancherel

end
