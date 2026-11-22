import Mathlib
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window truncates the prime side

`f` vanishing off `[-L/2, L/2]` makes `selfConvolution f` vanish off `[-L, L]`, so every
prime power past `e^L` contributes nothing and the prime side of `Cvs.WeilForm.SelfConvolutionFunctional`'s form is a sum over
the prime powers the window reaches.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WindowTruncatesPrimes

/-- **The self-convolution vanishes past twice the window.**  Two translates of a function
supported in `[-L/2, L/2]` have disjoint supports once the shift exceeds `L`. -/
theorem selfConvolution_eq_zero {f : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ x, x ∉ Icc (-(L / 2)) (L / 2) → f x = 0) {u : ℝ} (hu : L < |u|) :
    selfConvolution f u = 0 := by
  have hzero : ∀ x : ℝ, f x * f (x + u) = 0 := by
    intro x
    by_cases hx : x ∈ Icc (-(L / 2)) (L / 2)
    · refine mul_eq_zero.mpr (Or.inr (hsupp _ fun hxu => ?_))
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hxu
      rcases abs_cases u with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hu <;> linarith
    · exact mul_eq_zero.mpr (Or.inl (hsupp x hx))
  unfold selfConvolution
  simp [hzero]

/-- The prime powers a window of length `L` reaches. -/
def windowIndex (P R : ℕ) (L : ℝ) : Finset ℕ :=
  (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter fun k => Real.log k ≤ L

/-- **The prime side is a sum over the prime powers inside the window.**  Everything past
`e^L` is charged weight zero, whatever the truncation `P`, `R` reaches. -/
theorem primePowerSideTruncated_eq_window {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hsupp : ∀ x, x ∉ Icc (-(L / 2)) (L / 2) → f x = 0) (P R : ℕ) :
    primePowerSideTruncated P R (selfConvolution f)
      = ∑ k ∈ windowIndex P R L,
          (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
            * (selfConvolution f (Real.log k) + selfConvolution f (-(Real.log k))) := by
  classical
  rw [Cvs.WeilForm.PrimePowerIndexed.primePowerSideTruncated_eq_image]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro k hk hkf
  have hgt : L < Real.log k := by
    by_contra hc
    exact hkf (Finset.mem_filter.mpr ⟨hk, not_lt.mp hc⟩)
  have habs : |Real.log k| = Real.log k := abs_of_nonneg (le_trans hL hgt.le)
  have h1 : selfConvolution f (Real.log k) = 0 :=
    selfConvolution_eq_zero hsupp (by rw [habs]; exact hgt)
  have h2 : selfConvolution f (-(Real.log k)) = 0 :=
    selfConvolution_eq_zero hsupp (by rw [abs_neg, habs]; exact hgt)
  rw [h1, h2]
  ring

end Cvs.WeilForm.WindowTruncatesPrimes
