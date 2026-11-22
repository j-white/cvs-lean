import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card

/-!
# Choosing a height that avoids the zeros

The contour argument for the explicit formula integrates along horizontal lines, and needs
those lines to stay away from the zeros of `ζ`.
-/

open Finset

namespace Cvs.Zeta

/-- **A finite set of reals cannot block every height.** For any finite `A ⊆ ℝ` there is a `T'` in
`[T, T+1]` at distance at least `1/(2(|A|+1))` from every element of `A`. -/
theorem exists_far_from_finset (A : Finset ℝ) (T : ℝ) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      ∀ a ∈ A, 1 / (2 * (A.card + 1)) ≤ |T' - a| := by
  classical
  set n : ℕ := A.card with hn
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set idx : ℝ → ℕ := fun a => ⌊(a - T) * ((n : ℝ) + 1)⌋₊ with hidx
  have hcard : (A.image idx).card < (Finset.range (n + 1)).card := by
    calc (A.image idx).card ≤ A.card := Finset.card_image_le
      _ = n := hn.symm
      _ < n + 1 := Nat.lt_succ_self n
      _ = (Finset.range (n + 1)).card := (Finset.card_range _).symm
  obtain ⟨j, hj, hjnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hjle : (j : ℝ) ≤ n := by
    have := Finset.mem_range.mp hj
    exact_mod_cast Nat.lt_succ_iff.mp this
  refine ⟨T + ((j : ℝ) + 1 / 2) / ((n : ℝ) + 1), ?_, ?_, ?_⟩
  · have : (0 : ℝ) ≤ ((j : ℝ) + 1 / 2) / ((n : ℝ) + 1) := by positivity
    linarith
  · have : ((j : ℝ) + 1 / 2) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hnpos]; linarith
    linarith
  · intro a ha
    by_contra hcon
    push_neg at hcon
    -- `a` lands in the `j`-th interval, contradicting the choice of `j`
    have hmid : |T + ((j : ℝ) + 1 / 2) / ((n : ℝ) + 1) - a| < 1 / (2 * ((n : ℝ) + 1)) := by
      simpa [hn] using hcon
    -- rewrite so the denominator cancels: `|j + 1/2 − u| < 1/2` with `u = (a−T)(n+1)`
    have hne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hnpos
    have e1 : T + ((j : ℝ) + 1 / 2) / ((n : ℝ) + 1) - a
        = ((j : ℝ) + 1 / 2 - (a - T) * ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
      field_simp
      ring
    rw [e1, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos] at hmid
    have hhalf : 1 / (2 * ((n : ℝ) + 1)) * ((n : ℝ) + 1) = 1 / 2 := by field_simp
    rw [hhalf, abs_lt] at hmid
    have hlow : (j : ℝ) ≤ (a - T) * ((n : ℝ) + 1) := by linarith [hmid.2]
    have hhigh : (a - T) * ((n : ℝ) + 1) < (j : ℝ) + 1 := by linarith [hmid.1]
    have hu0 : (0 : ℝ) ≤ (a - T) * ((n : ℝ) + 1) :=
      le_trans (Nat.cast_nonneg j) hlow
    have hfl : idx a = j := by
      rw [hidx]
      exact (Nat.floor_eq_iff hu0).mpr ⟨hlow, by exact_mod_cast hhigh⟩
    exact hjnot (Finset.mem_image.mpr ⟨a, ha, hfl⟩)

/-- The form the zero count consumes: only an *upper bound* on the number of ordinates is
known, not the number itself. -/
theorem exists_far_from_finset_of_card_le (A : Finset ℝ) (T : ℝ) {N : ℕ} (hN : A.card ≤ N) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      ∀ a ∈ A, 1 / (2 * ((N : ℝ) + 1)) ≤ |T' - a| := by
  obtain ⟨T', h1, h2, h3⟩ := exists_far_from_finset A T
  refine ⟨T', h1, h2, fun a ha => le_trans ?_ (h3 a ha)⟩
  have hNn : (A.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h0 : (0 : ℝ) < 2 * ((A.card : ℝ) + 1) := by positivity
  refine one_div_le_one_div_of_le h0 ?_
  linarith

end Cvs.Zeta
