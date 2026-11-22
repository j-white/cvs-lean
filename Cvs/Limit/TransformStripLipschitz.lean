import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.PoleChannelL2Continuous
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TransformNowhereLocallyZero

/-!
# The transform moves by at most the L² distance, times a strip constant

    ‖𝓛 f z − 𝓛 h z‖ ≤ ‖f − h‖₂ · √L · exp(L·|z.im|)

for `f, h` supported in `(0, L]`, so an `L²`-convergent sequence has transforms converging
uniformly on every set of bounded imaginary part.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real

namespace Cvs.Limit.TransformStripLipschitz

/-- The strip weight: the kernel's modulus, truncated to the window. -/
def stripWeight (L : ℝ) (b : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Ioc (0:ℝ) L) (fun t => Real.exp (-(t * b)))

theorem memLp_stripWeight (L b : ℝ) : MemLp (stripWeight L b) 2 (volume : Measure ℝ) :=
  Cvs.WeilForm.PoleChannelL2Continuous.memLp_indicator_of_continuous
    (Real.continuous_exp.comp (continuous_id.mul continuous_const).neg)

/-- **The weight's energy is controlled by the strip.** -/
theorem integral_stripWeight_sq_le {L : ℝ} (hL : 0 ≤ L) (b : ℝ) :
    (∫ t : ℝ, stripWeight L b t ^ 2) ≤ Real.exp (2 * L * |b|) * L := by
  have hpt : ∀ t : ℝ, stripWeight L b t ^ 2
      ≤ Set.indicator (Set.Ioc (0:ℝ) L) (fun _ => Real.exp (2 * L * |b|)) t := by
    intro t
    by_cases ht : t ∈ Set.Ioc (0:ℝ) L
    · rw [stripWeight, Set.indicator_of_mem ht, Set.indicator_of_mem ht, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have h1 : 0 < t := ht.1
      have h2 : t ≤ L := ht.2
      have h3 : -(t * b) ≤ t * |b| := by
        have := neg_abs_le (t * b)
        have habs : |t * b| = t * |b| := by rw [abs_mul, abs_of_pos h1]
        linarith [habs ▸ this]
      push_cast
      nlinarith [abs_nonneg b, h1, h2]
    · rw [stripWeight, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      simp
  have hint : Integrable
      (Set.indicator (Set.Ioc (0:ℝ) L) (fun _ : ℝ => Real.exp (2 * L * |b|)))
      (volume : Measure ℝ) := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioc
    refine integrableOn_const ?_
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hsq : Integrable (fun t : ℝ => stripWeight L b t ^ 2) (volume : Measure ℝ) :=
    (memLp_stripWeight L b).integrable_sq
  refine le_trans (integral_mono hsq hint hpt) ?_
  rw [integral_indicator measurableSet_Ioc, setIntegral_const, Real.volume_real_Ioc]
  rw [max_eq_left (by linarith : (0:ℝ) ≤ L - 0)]
  simp [mul_comm]

/-- **The transform moves by at most the `L²` distance, times a strip constant.** -/
theorem norm_fourierLaplace_sub_le {L : ℝ} (hL : 0 ≤ L) {f h : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hh : MemLp h 2 (volume : Measure ℝ))
    (hfs : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) (hhs : ∀ s ∉ Set.Ioc (0:ℝ) L, h s = 0)
    (z : ℂ) :
    ‖FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z
        - FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf h) z‖
      ≤ Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2)
          * Real.sqrt (Real.exp (2 * L * |z.im|) * L) := by
  have hfint : Integrable f (volume : Measure ℝ) :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hf hfs
  have hhint : Integrable h (volume : Measure ℝ) :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hh hhs
  have hcf : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf f) (volume : Measure ℝ) := hfint.ofReal
  have hch : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf h) (volume : Measure ℝ) := hhint.ofReal
  have hkf := FourierLaplace.integrable_mul_kernel hcf
    (Cvs.WeilForm.TransformNowhereLocallyZero.hasCompactSupport_cf hfs) z
  have hkh := FourierLaplace.integrable_mul_kernel hch
    (Cvs.WeilForm.TransformNowhereLocallyZero.hasCompactSupport_cf hhs) z
  -- the difference is one integral
  have hsub : FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z
      - FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf h) z
      = ∫ t : ℝ, ((f t - h t : ℝ) : ℂ) * Complex.exp (Complex.I * z * (t : ℂ)) := by
    rw [FourierLaplace.fourierLaplace, FourierLaplace.fourierLaplace, ← integral_sub hkf hkh]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Cvs.WeilForm.SelfConvolutionTransform.cf]
    push_cast
    ring
  rw [hsub]
  -- bound the integral by the pointwise product
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hpt : ∀ t : ℝ, ‖((f t - h t : ℝ) : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))‖
      = |f t - h t| * Real.exp (-(t * z.im)) := by
    intro t
    rw [norm_mul, FourierLaplace.norm_exp_I_mul, Complex.norm_real, Real.norm_eq_abs]
  simp only [hpt]
  -- off the window the integrand vanishes, so the weight may be truncated
  have hw : ∀ t : ℝ, |f t - h t| * Real.exp (-(t * z.im))
      = |f t - h t| * stripWeight L z.im t := by
    intro t
    by_cases ht : t ∈ Set.Ioc (0:ℝ) L
    · rw [stripWeight, Set.indicator_of_mem ht]
    · rw [stripWeight, Set.indicator_of_notMem ht, hfs t ht, hhs t ht]
      simp
  simp only [hw]
  have habs : MemLp (fun t : ℝ => |f t - h t|) 2 (volume : Measure ℝ) := (hf.sub hh).abs
  have hcs := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le habs (memLp_stripWeight L z.im)
  have hsq : (∫ x : ℝ, |f x - h x| ^ 2) = ∫ x : ℝ, (f x - h x) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => sq_abs _)
  rw [hsq] at hcs
  refine le_trans (le_trans (le_abs_self _) hcs) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (integral_stripWeight_sq_le hL z.im)

end Cvs.Limit.TransformStripLipschitz
