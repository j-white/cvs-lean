import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.ZeroCounting.XiGrowthZeroCount
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A dyadic block of zeros, weighed by the count

On `H < |γ| ≤ 2H` an integrand bounded by its value at `H` weighs at most `f H` times the
block's mass, and `Cvs.Zeta.ZeroCounting.XiGrowthZeroCount` prices that mass at `8·H·log (2H)`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Cvs.Zeta.Explicit.Venue

open scoped Classical

namespace Cvs.Zeta.ZeroCounting.DyadicZeroBlock
open Cvs.ZeroFree

/-- The height windows are nested. -/
theorem window_subset {S T : ℝ} (hST : S ≤ T) :
    nontrivialZetaZeroWindowFinset S ⊆ nontrivialZetaZeroWindowFinset T := by
  intro rho hrho
  rw [mem_nontrivialZetaZeroWindowFinset] at hrho ⊢
  linarith

/-- The count is the multiplicity-weighted mass of its window. -/
theorem count_eq_sum (T : ℝ) :
    (nontrivialZetaZeroCount T : ℝ)
      = ∑ rho ∈ nontrivialZetaZeroWindowFinset T,
          (completedZetaZeroMultiplicity rho : ℝ) := by
  rw [nontrivialZetaZeroCount]
  push_cast
  ring

/-- **The mass of a dyadic block is a difference of counts.** -/
theorem block_mass {H : ℝ} (hH : 0 ≤ H) :
    ∑ rho ∈ nontrivialZetaZeroWindowFinset (2 * H) \ nontrivialZetaZeroWindowFinset H,
        (completedZetaZeroMultiplicity rho : ℝ)
      = (nontrivialZetaZeroCount (2 * H) : ℝ) - (nontrivialZetaZeroCount H : ℝ) := by
  have hsub : nontrivialZetaZeroWindowFinset H ⊆ nontrivialZetaZeroWindowFinset (2 * H) :=
    window_subset (by linarith)
  have h := Finset.sum_sdiff (f := fun rho => (completedZetaZeroMultiplicity rho : ℝ)) hsub
  rw [count_eq_sum, count_eq_sum]
  linarith [h]

/-- **A decreasing integrand on the block weighs at most `f H` times its mass.** -/
theorem block_le {H : ℝ} {f : ℝ → ℝ} (hf : ∀ t, H ≤ t → f t ≤ f H) :
    ∑ rho ∈ nontrivialZetaZeroWindowFinset (2 * H) \ nontrivialZetaZeroWindowFinset H,
        (completedZetaZeroMultiplicity rho : ℝ)
          * f |(nontrivialZetaZeroValue rho).im|
      ≤ f H * ∑ rho ∈ nontrivialZetaZeroWindowFinset (2 * H) \
          nontrivialZetaZeroWindowFinset H, (completedZetaZeroMultiplicity rho : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun rho hrho => ?_
  have hmem := Finset.mem_sdiff.mp hrho
  have hnot : ¬ (|(nontrivialZetaZeroValue rho).im| ≤ H) := by
    simpa [mem_nontrivialZetaZeroWindowFinset] using hmem.2
  have hge : H ≤ |(nontrivialZetaZeroValue rho).im| := le_of_lt (not_le.mp hnot)
  have hm : (0:ℝ) ≤ (completedZetaZeroMultiplicity rho : ℝ) := Nat.cast_nonneg _
  calc (completedZetaZeroMultiplicity rho : ℝ) * f |(nontrivialZetaZeroValue rho).im|
      ≤ (completedZetaZeroMultiplicity rho : ℝ) * f H :=
        mul_le_mul_of_nonneg_left (hf _ hge) hm
    _ = f H * (completedZetaZeroMultiplicity rho : ℝ) := mul_comm _ _

/-- **The tail block, priced by `Cvs.Zeta.ZeroCounting.XiGrowthZeroCount`.** -/
theorem block_le_count {H : ℝ} (hH : 9 + Real.exp 1 ≤ 2 * H) {f : ℝ → ℝ}
    (hf : ∀ t, H ≤ t → f t ≤ f H) (hfH : 0 ≤ f H) :
    ∑ rho ∈ nontrivialZetaZeroWindowFinset (2 * H) \ nontrivialZetaZeroWindowFinset H,
        (completedZetaZeroMultiplicity rho : ℝ)
          * f |(nontrivialZetaZeroValue rho).im|
      ≤ f H * (8 * H * Real.log (2 * H)) := by
  have hH0 : (0:ℝ) ≤ H := by linarith [Real.exp_pos 1]
  have hN := Cvs.Zeta.ZeroCounting.XiGrowthZeroCount.nontrivialZetaZeroCount_le_four hH
  have hNH : (0:ℝ) ≤ (nontrivialZetaZeroCount H : ℝ) := Nat.cast_nonneg _
  have hmass : ∑ rho ∈ nontrivialZetaZeroWindowFinset (2 * H) \
      nontrivialZetaZeroWindowFinset H, (completedZetaZeroMultiplicity rho : ℝ)
      ≤ 8 * H * Real.log (2 * H) := by
    rw [block_mass hH0]
    linarith
  exact (block_le hf).trans (mul_le_mul_of_nonneg_left hmass hfH)

end Cvs.Zeta.ZeroCounting.DyadicZeroBlock
