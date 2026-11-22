import Mathlib
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaCriticalAsymptotic

/-!
# The archimedean side cannot be a bounded operator

    no_bounded_archOperator : no `A : E →L[ℝ] E` has `⟪A (e t), e t⟫ = archSymbol t`
                              on unit vectors

RH.md §3.21 carries what this does to the shape of the criterion.
-/

set_option maxHeartbeats 1600000

noncomputable section

set_option maxHeartbeats 1600000
set_option autoImplicit false

open scoped InnerProductSpace

noncomputable section

namespace Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-- The archimedean symbol: `Re ψ(¼ + it/2) − log π`, the weight the archimedean term of
the explicit formula puts on frequency `t`. -/
noncomputable def archSymbol (t : ℝ) : ℝ :=
  (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re - Real.log Real.pi

/-- **The symbol grows like `log t`.**  `DigammaCriticalAsymptotic`'s digamma asymptotic, rearranged. -/
theorem archSymbol_ge {t : ℝ} (ht : 2 ≤ t) :
    Real.log (t / 2) - 57 / t - Real.log Real.pi ≤ archSymbol t := by
  have h := DigammaAsym.abs_re_digamma_sub_log_le t ht
  have h' := (abs_le.mp h).1
  unfold archSymbol
  linarith

/-- **The symbol is unbounded above.** -/
theorem exists_lower_gt (C : ℝ) :
    ∃ t : ℝ, 2 ≤ t ∧ C < Real.log (t / 2) - 57 / t - Real.log Real.pi := by
  set t : ℝ := 2 * Real.pi * Real.exp (|C| + 30) with ht
  have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi : (3:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have he1 : (1:ℝ) ≤ Real.exp (|C| + 30) := by
    rw [Real.one_le_exp_iff]
    have := abs_nonneg C
    linarith
  have ht2 : (2:ℝ) ≤ t := by rw [ht]; nlinarith
  refine ⟨t, ht2, ?_⟩
  have hlog : Real.log (t / 2) = Real.log Real.pi + (|C| + 30) := by
    have h : t / 2 = Real.pi * Real.exp (|C| + 30) := by rw [ht]; ring
    rw [h, Real.log_mul (ne_of_gt hpi0) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have h57 : 57 / t ≤ 57 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht2
  have hCabs : C ≤ |C| := le_abs_self C
  rw [hlog]
  linarith

/-- **The symbol is unbounded above.** -/
theorem archSymbol_unbounded (C : ℝ) : ∃ t : ℝ, 2 ≤ t ∧ C < archSymbol t := by
  obtain ⟨t, ht2, hgt⟩ := exists_lower_gt C
  exact ⟨t, ht2, lt_of_lt_of_le hgt (archSymbol_ge ht2)⟩

/-! ## The archimedean quadratic form

Unbounded above, so it is a form and not a bounded operator.  Stated over coefficient
sequences against a frequency assignment, which is what a Fourier basis supplies.
-/

end Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
