import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The odd sector as derivatives: the primitive of an odd function, and the transform of a derivative

On a symmetric interval an odd function is the derivative of an even primitive vanishing at both
ends, and the transform of a derivative with vanishing ends is `i t` times the transform of the
primitive.
-/

noncomputable section

open MeasureTheory intervalIntegral Set Complex

namespace Cvs.StepA.OddSectorAsDerivatives

variable {H : ℝ} {f : ℝ → ℝ}

/-- The character `s ↦ e^{−its}` and its derivative. -/
theorem hasDerivAt_char (t x : ℝ) :
    HasDerivAt (fun s : ℝ => cexp (-(I * t) * s)) (cexp (-(I * t) * x) * (-(I * t))) x := by
  have h1 : HasDerivAt (fun s : ℝ => -(I * t) * (s : ℂ)) (-(I * t)) x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (-(I * t))
  exact h1.cexp

/-- **Integration by parts against a character, with vanishing ends.** -/
theorem integral_deriv_mul_cexp {a b t : ℝ} (hab : a ≤ b) {g : ℝ → ℂ} {f : ℝ → ℂ}
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ x ∈ Ioo a b, HasDerivWithinAt g (f x) (Ioi x) x)
    (hf : IntervalIntegrable f volume a b)
    (ha : g a = 0) (hb : g b = 0) :
    ∫ s in a..b, f s * cexp (-(I * t) * s) = I * t * ∫ s in a..b, g s * cexp (-(I * t) * s) := by
  have hcont : ContinuousOn (fun s : ℝ => cexp (-(I * t) * s)) (uIcc a b) :=
    fun x _ => (hasDerivAt_char t x).continuousAt.continuousWithinAt
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hgi : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hg.integrableOn_compact isCompact_Icc
  have key := integral_deriv_mul_eq_sub_of_hasDeriv_right (u := g)
    (v := fun s : ℝ => cexp (-(I * t) * s)) (u' := f)
    (v' := fun x => cexp (-(I * t) * x) * (-(I * t))) (a := a) (b := b)
    (by rw [huIcc]; exact hg) hcont
    (by rw [min_eq_left hab, max_eq_right hab]; exact hg')
    (by intro x _; exact (hasDerivAt_char t x).hasDerivWithinAt) hf
    (by
      apply Continuous.intervalIntegrable
      exact (by fun_prop : Continuous fun x : ℝ => cexp (-(I * t) * x)).mul continuous_const)
  rw [ha, hb, zero_mul, zero_mul, sub_zero] at key
  have hv' : Continuous fun x : ℝ => cexp (-(I * t) * x) * (-(I * t)) :=
    (by fun_prop : Continuous fun x : ℝ => cexp (-(I * t) * x)).mul continuous_const
  have hsplit : (∫ x in a..b, f x * cexp (-(I * t) * x) + g x * (cexp (-(I * t) * x) * (-(I * t))))
      = (∫ x in a..b, f x * cexp (-(I * t) * x))
        + ∫ x in a..b, g x * (cexp (-(I * t) * x) * (-(I * t))) := by
    apply intervalIntegral.integral_add
    · exact hf.mul_continuousOn hcont
    · exact hgi.mul_continuousOn hv'.continuousOn
  rw [hsplit] at key
  have h2 : ∫ x in a..b, g x * (cexp (-(I * t) * x) * (-(I * t)))
      = -(I * t) * ∫ x in a..b, g x * cexp (-(I * t) * x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  rw [h2] at key
  linear_combination key

end Cvs.StepA.OddSectorAsDerivatives
