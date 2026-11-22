import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.WindowTransformCubicDecay

/-!
# The window transform is entire, and the squared test is even
-/

namespace Cvs.Detection

open Complex intervalIntegral MeasureTheory Filter
open scoped Real Topology

/-- The character's derivative in the *frequency*, not the time. -/
theorem hasDerivAt_char_freq (s : ℝ) (ξ : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-((s : ℂ) * w) * I))
      (Complex.exp (-((s : ℂ) * ξ) * I) * (-((s : ℂ) * I))) ξ := by
  have hlin : HasDerivAt (fun w : ℂ => w * (-((s : ℂ) * I))) (-((s : ℂ) * I)) ξ := by
    simpa using (hasDerivAt_id ξ).mul_const (-((s : ℂ) * I))
  have hfun : (fun w : ℂ => w * (-((s : ℂ) * I))) = fun w : ℂ => -((s : ℂ) * w) * I := by
    funext w; ring
  rw [hfun] at hlin
  exact hlin.cexp

/-- **The window transform is entire.**  Differentiation under the integral, with
the domination supplied by compactness of `[0, L]`. -/
theorem differentiable_windowTransform {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ}
    (hf : Continuous f) : Differentiable ℂ (Cvs.Detection.windowTransform L f) := by
  intro ξ₀
  obtain ⟨M, hM⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn
    hf.continuousOn
  have hMnn : (0 : ℝ) ≤ M := le_trans (norm_nonneg (f 0)) (hM 0 (by
    rw [Set.uIcc_of_le hL, Set.mem_Icc]; exact ⟨le_rfl, hL⟩))
  set F : ℂ → ℝ → ℂ := fun w s => Complex.exp (-((s : ℂ) * w) * I) * f s with hF
  set F' : ℂ → ℝ → ℂ := fun w s =>
    Complex.exp (-((s : ℂ) * w) * I) * (-((s : ℂ) * I)) * f s with hF'
  set K : ℝ := L * (Real.exp (L * (|ξ₀.im| + 1)) * M) with hK
  have hcont : ∀ w : ℂ, Continuous (F w) := by
    intro w; rw [hF]; fun_prop
  have hball : Metric.ball ξ₀ 1 ∈ 𝓝 ξ₀ := Metric.ball_mem_nhds ξ₀ one_pos
  -- every ξ in the ball has Im ξ ≤ |Im ξ₀| + 1
  have him : ∀ w ∈ Metric.ball ξ₀ 1, w.im ≤ |ξ₀.im| + 1 := by
    intro w hw
    have h1 : |w.im - ξ₀.im| ≤ ‖w - ξ₀‖ := by
      simpa using Complex.abs_im_le_norm (w - ξ₀)
    have h2 : ‖w - ξ₀‖ < 1 := by simpa [Complex.dist_eq] using hw
    have h3 : w.im - ξ₀.im ≤ |w.im - ξ₀.im| := le_abs_self _
    have h4 : ξ₀.im ≤ |ξ₀.im| := le_abs_self _
    linarith
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) L →
      ∀ w ∈ Metric.ball ξ₀ 1, ‖F' w t‖ ≤ K := by
    refine Filter.Eventually.of_forall fun t ht w hw => ?_
    rw [Set.uIoc_of_le hL, Set.mem_Ioc] at ht
    rw [hF', norm_mul, norm_mul, Cvs.Detection.norm_char]
    have hchar : Real.exp (t * w.im) ≤ Real.exp (L * (|ξ₀.im| + 1)) := by
      refine Real.exp_le_exp.mpr ?_
      have hpos : (0 : ℝ) ≤ |ξ₀.im| + 1 := by positivity
      calc t * w.im ≤ t * (|ξ₀.im| + 1) :=
            mul_le_mul_of_nonneg_left (him w hw) (le_of_lt ht.1)
        _ ≤ L * (|ξ₀.im| + 1) := mul_le_mul_of_nonneg_right ht.2 hpos
    have hs : ‖-((t : ℂ) * I)‖ ≤ L := by
      rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt ht.1)]
      exact ht.2
    have hft : ‖f t‖ ≤ M := hM t (by rw [Set.uIcc_of_le hL, Set.mem_Icc]; exact ⟨ht.1.le, ht.2⟩)
    rw [hK]
    calc Real.exp (t * w.im) * ‖-((t : ℂ) * I)‖ * ‖f t‖
        ≤ Real.exp (L * (|ξ₀.im| + 1)) * L * M := by
          refine mul_le_mul (mul_le_mul hchar hs (norm_nonneg _) (Real.exp_nonneg _)) hft
            (norm_nonneg _) (by positivity)
      _ = L * (Real.exp (L * (|ξ₀.im| + 1)) * M) := by ring
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) L →
      ∀ w ∈ Metric.ball ξ₀ 1, HasDerivAt (fun w : ℂ => F w t) (F' w t) w := by
    refine Filter.Eventually.of_forall fun t _ w _ => ?_
    rw [hF, hF']
    exact (hasDerivAt_char_freq t w).mul_const (f t)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0 : ℝ)) (b := L) (bound := fun _ => K) hball
    (Filter.Eventually.of_forall fun w => (hcont w).aestronglyMeasurable)
    ((hcont ξ₀).intervalIntegrable 0 L)
    ((by rw [hF']; fun_prop : Continuous (F' ξ₀)).aestronglyMeasurable)
    hbound (intervalIntegrable_const) hdiff
  have hshow : (fun w : ℂ => ∫ t in (0 : ℝ)..L, F w t) = Cvs.Detection.windowTransform L f := by
    funext w; rw [Cvs.Detection.windowTransform, hF]
  rw [hshow] at key
  exact key.2.differentiableAt

/-- **A squared test is even, for free.**  Only commutativity is used. -/
theorem sq_even (W : ℂ → ℂ) (w : ℂ) :
    (fun ξ => W ξ * W (-ξ)) (-w) = (fun ξ => W ξ * W (-ξ)) w := by
  simp only [neg_neg]
  ring

/-- The squared test inherits differentiability. -/
theorem differentiable_sq {W : ℂ → ℂ} (hW : Differentiable ℂ W) :
    Differentiable ℂ (fun ξ => W ξ * W (-ξ)) :=
  hW.mul (hW.comp differentiable_neg)

end Cvs.Detection
