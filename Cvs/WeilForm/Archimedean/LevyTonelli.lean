import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchTrigonometricData
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyMeasure
import Cvs.WeilForm.Archimedean.SymbolIncrementMeasurable
import Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.WeilPositivityStatement

/-!
# HWA from the domain condition, by Tonelli

    ∫_{u>0} levy f u du  =  ∫ specDensity f t · (archSymbol t − archSymbol 0) dt

Both factors of the kernel are nonnegative, so the two orders agree in `[0,∞]` with no
integrability assumed, and finiteness passes from the shift side to the spectral side.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Set Function Cvs.Zeta.Explicit.Weil
open scoped FourierTransform ENNReal

namespace Cvs.WeilForm.Archimedean.LevyTonelli

/-- The spectral density is continuous, hence measurable. -/
theorem continuous_specDensity {f : ℝ → ℝ} (hfint : Integrable f (volume : Measure ℝ)) :
    Continuous (Cvs.WeilForm.SelfConvolutionCosine.specDensity f) := by
  have hFc : Continuous (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
      hfint.ofReal
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
  exact ((hFc.comp (continuous_id.div_const (2 * π))).norm.pow 2).div_const _

/-- The kernel of the exchange, in the pair variable. -/
def ker (f : ℝ → ℝ) (u t : ℝ) : ℝ :=
  (1 - Real.cos (t / 2 * u)) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u
    * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t

theorem ker_eq (f : ℝ → ℝ) (u t : ℝ) :
    ker f u t = Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand t u
      * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  rw [ker, Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand]

theorem ker_nonneg {f : ℝ → ℝ} {u : ℝ} (hu : 0 < u) (t : ℝ) : 0 ≤ ker f u t := by
  rw [ker]
  have h1 : 0 ≤ 1 - Real.cos (t / 2 * u) := by
    have := Real.cos_le_one (t / 2 * u); linarith
  have h2 : 0 ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u := (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu).le
  have h3 := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t
  positivity

theorem measurable_ker {f : ℝ → ℝ} (hfint : Integrable f (volume : Measure ℝ)) :
    Measurable (uncurry (ker f)) := by
  have hWc := (continuous_specDensity hfint).measurable
  have h1 : Measurable fun p : ℝ × ℝ => 1 - Real.cos (p.2 / 2 * p.1) :=
    measurable_const.sub
      (Real.measurable_cos.comp ((measurable_snd.div_const 2).mul measurable_fst))
  have h2 : Measurable fun p : ℝ × ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU p.1 :=
    Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.comp measurable_fst
  have h3 : Measurable fun p : ℝ × ℝ => Cvs.WeilForm.SelfConvolutionCosine.specDensity f p.2 :=
    hWc.comp measurable_snd
  exact (h1.mul h2).mul h3

/-- Each slice in `t` is integrable. -/
theorem integrable_ker_right {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ)) (u : ℝ) :
    Integrable (fun t : ℝ => ker f u t) (volume : Measure ℝ) := by
  have hW := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  have hWc := continuous_specDensity hfint
  refine (hW.const_mul (2 * |Cvs.WeilForm.Archimedean.LevyDensity.densityU u|)).mono'
    (((measurable_ker hfint).comp (measurable_prodMk_left)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [ker, Real.norm_eq_abs, abs_mul, abs_mul]
  have hc : |1 - Real.cos (t / 2 * u)| ≤ 2 := by
    have h1 := Real.neg_one_le_cos (t / 2 * u)
    have h2 := Real.cos_le_one (t / 2 * u)
    rw [abs_le]; constructor <;> linarith
  have hWnn : |Cvs.WeilForm.SelfConvolutionCosine.specDensity f t|
      = Cvs.WeilForm.SelfConvolutionCosine.specDensity f t :=
    abs_of_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)
  rw [hWnn]
  have hdnn : 0 ≤ |Cvs.WeilForm.Archimedean.LevyDensity.densityU u| := abs_nonneg _
  have hs := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t
  have hstep : |1 - Real.cos (t / 2 * u)| * |Cvs.WeilForm.Archimedean.LevyDensity.densityU u|
      ≤ 2 * |Cvs.WeilForm.Archimedean.LevyDensity.densityU u| := mul_le_mul_of_nonneg_right hc hdnn
  nlinarith [hstep, hs, hdnn]

/-- Each slice in `u` is integrable on the half-line. -/
theorem integrableOn_ker_left {f : ℝ → ℝ} (t : ℝ) :
    IntegrableOn (fun u : ℝ => ker f u t) (Set.Ioi (0:ℝ)) (volume : Measure ℝ) := by
  have h := (Cvs.WeilForm.Archimedean.ArchTrigonometricData.integrableOn_levyIntegrand t).const_mul
    (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [ker_eq]
  ring

/-- **The exchange.**  The archimedean energy, in the two orders. -/
theorem lintegral_levy_eq {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ)) :
    (∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u))
      = ∫⁻ t : ℝ, ENNReal.ofReal (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
          * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t
            - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)) := by
  have hstep1 : (∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u))
      = ∫⁻ u in Set.Ioi (0:ℝ), ∫⁻ t : ℝ, ENNReal.ofReal (ker f u t) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.levy_eq_integral hf hfint u]
    rw [show (∫ t : ℝ, Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand t u
        * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) = ∫ t : ℝ, ker f u t from
      integral_congr_ae (Filter.Eventually.of_forall fun t => (ker_eq f u t).symm)]
    exact ofReal_integral_eq_lintegral_ofReal (integrable_ker_right hf hfint u)
      (Filter.Eventually.of_forall fun t => ker_nonneg hu t)
  have hswap : (∫⁻ u in Set.Ioi (0:ℝ), ∫⁻ t : ℝ, ENNReal.ofReal (ker f u t))
      = ∫⁻ t : ℝ, ∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (ker f u t) := by
    refine lintegral_lintegral_swap ?_
    exact ((ENNReal.measurable_ofReal.comp (measurable_ker hfint)).aemeasurable)
  have hstep3 : ∀ t : ℝ, (∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (ker f u t))
      = ENNReal.ofReal (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
          * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)) := by
    intro t
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_ker_left t)
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun u hu => ker_nonneg hu t))]
    congr 1
    rw [show (∫ u in Set.Ioi (0:ℝ), ker f u t)
        = ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
            * Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand t u from
      setIntegral_congr_ae measurableSet_Ioi
        (Filter.Eventually.of_forall fun u _ => by rw [ker_eq]; ring)]
    rw [integral_const_mul, Cvs.WeilForm.Archimedean.ArchTrigonometricData.integral_levyIntegrand t]
  rw [hstep1, hswap]
  exact lintegral_congr hstep3

/-- **`hWA` from the domain condition.**  The density is integrable against the symbol's
increment as soon as the Lévy integral converges — the same quantity, read in the other
order. -/
theorem integrable_specDensity_mul_arch {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ))
    (hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)) :
    Integrable (fun t : ℝ => Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t
        - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)) (volume : Measure ℝ) := by
  have hnn : ∀ t : ℝ, 0 ≤ Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) := fun t =>
    mul_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)
      (Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic.archSymbol_sub_nonneg t)
  refine ⟨((continuous_specDensity hfint).aestronglyMeasurable).mul
    Cvs.WeilForm.Archimedean.SymbolIncrementMeasurable.stronglyMeasurable_archSymbol_sub.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have henorm : (∫⁻ t : ℝ, ‖Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)‖ₑ)
      = ∫⁻ t : ℝ, ENNReal.ofReal (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
          * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t
            - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)) :=
    lintegral_congr fun t => Real.enorm_eq_ofReal (hnn t)
  rw [henorm, ← lintegral_levy_eq hf hfint]
  have hlevynn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))]
      Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun u hu => ?_)
    have hd : 0 < Cvs.WeilForm.Archimedean.LevyDensity.densityU u := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu
    have hg : selfConvolution f (u / 2) ≤ selfConvolution f 0 :=
      Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.selfConvolution_le_zero_shift (u / 2) hf
    exact mul_nonneg hd.le (by linarith)
  rw [← ofReal_integral_eq_lintegral_ofReal hdom hlevynn]
  exact ENNReal.ofReal_lt_top

end Cvs.WeilForm.Archimedean.LevyTonelli
