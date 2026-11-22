import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.WeilForm.PoleChannelL2Continuous
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The transforms of unit window functions are equicontinuous

    ∫ |x|·|f x| dx ≤ √(L³/3)      for `f` supported in `(0, L]` of unit energy

a uniform first moment, which is what `Cvs.WeilForm.WindowTransformsEquicontinuous` turns into a common Lipschitz constant for the
transforms.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Set

namespace Cvs.WeilForm.UnitWindowTransformEquicontinuous

/-- The window's first-moment weight. -/
def momentWeight (L : ℝ) : ℝ → ℝ := Set.indicator (Set.Ioc (0:ℝ) L) (fun x => |x|)

theorem memLp_momentWeight (L : ℝ) : MemLp (momentWeight L) 2 (volume : Measure ℝ) :=
  Cvs.WeilForm.PoleChannelL2Continuous.memLp_indicator_of_continuous continuous_abs

/-- The weight's energy is the window's third moment. -/
theorem integral_momentWeight_sq {L : ℝ} (hL : 0 ≤ L) :
    (∫ x : ℝ, momentWeight L x ^ 2) = L ^ 3 / 3 := by
  have hpt : ∀ x : ℝ, momentWeight L x ^ 2
      = Set.indicator (Set.Ioc (0:ℝ) L) (fun y => y ^ 2) x := by
    intro x
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L <;>
      simp [momentWeight, Set.indicator_of_mem, Set.indicator_of_notMem, hx, sq_abs]
  simp only [hpt]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hL,
    integral_pow]
  norm_num

/-- The moment integrand is integrable. -/
theorem integrable_moment {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) :
    Integrable (fun x : ℝ => |x| * ‖Cvs.WeilForm.SelfConvolutionTransform.cf f x‖) (volume : Measure ℝ) := by
  have habs : MemLp (fun x : ℝ => |f x|) 2 (volume : Measure ℝ) := hf.abs
  have hprod : Integrable (fun x : ℝ => momentWeight L x * |f x|) (volume : Measure ℝ) :=
    (memLp_momentWeight L).integrable_mul habs
  refine hprod.congr (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Set.Ioc (0:ℝ) L
  · simp [momentWeight, Set.indicator_of_mem hx, Cvs.WeilForm.SelfConvolutionTransform.cf, Complex.norm_real]
  · simp [momentWeight, Set.indicator_of_notMem hx, hsupp x hx, Cvs.WeilForm.SelfConvolutionTransform.cf]

/-- **The first moment is uniformly bounded on the window.** -/
theorem moment_le {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hnorm : (∫ x : ℝ, f x ^ 2) = 1) :
    (∫ x : ℝ, |x| * ‖Cvs.WeilForm.SelfConvolutionTransform.cf f x‖) ≤ Real.sqrt (L ^ 3 / 3) := by
  have habs : MemLp (fun x : ℝ => |f x|) 2 (volume : Measure ℝ) := hf.abs
  have heq : (∫ x : ℝ, |x| * ‖Cvs.WeilForm.SelfConvolutionTransform.cf f x‖)
      = ∫ x : ℝ, momentWeight L x * |f x| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L
    · simp [momentWeight, Set.indicator_of_mem hx, Cvs.WeilForm.SelfConvolutionTransform.cf, Complex.norm_real]
    · simp [momentWeight, Set.indicator_of_notMem hx, hsupp x hx, Cvs.WeilForm.SelfConvolutionTransform.cf]
  rw [heq]
  have hcs := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le (memLp_momentWeight L) habs
  have habs_sq : (∫ x : ℝ, |f x| ^ 2) = 1 := by
    rw [← hnorm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => sq_abs (f x))
  rw [integral_momentWeight_sq hL, habs_sq, Real.sqrt_one, mul_one] at hcs
  exact le_trans (le_abs_self _) hcs

end Cvs.WeilForm.UnitWindowTransformEquicontinuous
