import Mathlib
import Cvs.WeilForm.PoleVectorModes

/-!
# The pole term on a cosine combination is the rank one

    ∫_{−L/2}^{L/2} (∑ₙ aₙ cos(ωₙ s))·e^{s/2} ds = ∑ₙ aₙ·poleCoeff L n

and on an even function the two pole functionals agree, so `2·A·M = 2·⟨v,a⟩²`.  That is the
rank one the whole even-sector argument is built on, identified with the Weil pole term.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Cvs.WeilForm.PoleVectorModes

namespace Cvs.WeilForm.PoleTermCosineRankOne

/-- A finite cosine combination on the symmetric window. -/
def evenFn (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) : ℝ → ℝ :=
  fun x => ∑ n ∈ s, a n * Real.cos (2 * π * n / L * x)

/-- **The pole functional reads off the coefficients.** -/
theorem integral_evenFn_exp (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x in (-(L/2))..(L/2), evenFn L s a x * Real.exp (x / 2))
      = ∑ n ∈ s, a n * poleCoeff L n := by
  unfold evenFn poleCoeff
  have hrw : ∀ x : ℝ, (∑ n ∈ s, a n * Real.cos (2 * π * n / L * x)) * Real.exp (x / 2)
      = ∑ n ∈ s, a n * (Real.cos (2 * π * n / L * x) * Real.exp (x / 2)) := by
    intro x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [intervalIntegral.integral_congr (fun x _ => hrw x)]
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun n _ => by
      rw [intervalIntegral.integral_const_mul]
  · intro n _
    apply Continuous.intervalIntegrable
    fun_prop

/-- **An even function pairs the same against both poles.** -/
theorem integral_evenFn_exp_neg (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x in (-(L/2))..(L/2), evenFn L s a x * Real.exp (-(x / 2)))
      = ∫ x in (-(L/2))..(L/2), evenFn L s a x * Real.exp (x / 2) := by
  have heven : ∀ x : ℝ, evenFn L s a (-x) = evenFn L s a x := by
    intro x
    unfold evenFn
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show 2 * π * (n : ℝ) / L * (-x) = -(2 * π * (n : ℝ) / L * x) by ring, Real.cos_neg]
  calc (∫ x in (-(L/2))..(L/2), evenFn L s a x * Real.exp (-(x / 2)))
      = ∫ x in (-(L/2))..(L/2), (fun y : ℝ => evenFn L s a y * Real.exp (y / 2)) (-x) := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only
        rw [heven x]
        congr 2
        ring
    _ = ∫ x in (-(L/2))..(L/2), evenFn L s a x * Real.exp (x / 2) := by
        rw [intervalIntegral.integral_comp_neg
          (fun y : ℝ => evenFn L s a y * Real.exp (y / 2))]
        norm_num

/-- **So the pole term is the rank one**, at twice the square of the pairing. -/
theorem poleForm_evenFn (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    2 * (∫ x in (-(L/2))..(L/2), evenFn L s a x * Real.exp (x / 2))
        * (∫ x in (-(L/2))..(L/2), evenFn L s a x * Real.exp (-(x / 2)))
      = 2 * (∑ n ∈ s, a n * poleCoeff L n) ^ 2 := by
  rw [integral_evenFn_exp_neg, integral_evenFn_exp]
  ring

end Cvs.WeilForm.PoleTermCosineRankOne
