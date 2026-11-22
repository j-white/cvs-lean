import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The weighted Schur test for the rung envelope

A symmetric nonnegative envelope `E` with `Σ_j E i j · w j ≤ e · w i` for some positive weights `w` satisfies
`Σ_{i,j} |aᵢ||aⱼ| E i j ≤ e Σ aᵢ²`; with the Perron weights this is the operator norm of `E`, so the correlation
hypothesis of Cvs.L2a.FarMassPlateau follows from per-pair envelopes with `r = 2e/λ` for the best weights, not only for the row sums.
-/

namespace Cvs.Prolate.RungEnvelopeSchurTest

open Real Set MeasureTheory

variable {ι : Type} [Fintype ι]

/-- **The weighted Schur test**: positive weights `w` with `Σ_j E i j w j ≤ e w i` give
`Σ_{i,j} |aᵢ||aⱼ| E i j ≤ e Σ aᵢ²`. -/
theorem schur_bound_weighted (a : ι → ℝ) (E : ι → ι → ℝ) (w : ι → ℝ) {e : ℝ} (hE0 : ∀ i j, 0 ≤ E i j)
    (hsym : ∀ i j, E i j = E j i) (hw : ∀ i, 0 < w i) (hrow : ∀ i, ∑ j, E i j * w j ≤ e * w i) :
    ∑ i, ∑ j, |a i| * |a j| * E i j ≤ e * ∑ i, a i ^ 2 := by
  -- `|aᵢ||aⱼ| ≤ (aᵢ² wⱼ/wᵢ + aⱼ² wᵢ/wⱼ)/2`
  have hab : ∀ i j, |a i| * |a j| * E i j
      ≤ (a i ^ 2 / 2) * (E i j * w j / w i) + (a j ^ 2 / 2) * (E i j * w i / w j) := by
    intro i j
    have hwi := hw i
    have hwj := hw j
    have h : |a i| * |a j| ≤ a i ^ 2 / 2 * (w j / w i) + a j ^ 2 / 2 * (w i / w j) := by
      set x := w j / w i with hx
      have hx0 : 0 < x := by positivity
      have hy' : w i / w j = 1 / x := by rw [hx]; field_simp
      have h0 : 2 * x * (|a i| * |a j|) ≤ x ^ 2 * a i ^ 2 + a j ^ 2 := by
        nlinarith [sq_nonneg (x * |a i| - |a j|), sq_abs (a i), sq_abs (a j)]
      rw [hy']
      calc |a i| * |a j| = (2 * x * (|a i| * |a j|)) / (2 * x) := by field_simp
        _ ≤ (x ^ 2 * a i ^ 2 + a j ^ 2) / (2 * x) := div_le_div_of_nonneg_right h0 (by positivity)
        _ = a i ^ 2 / 2 * x + a j ^ 2 / 2 * (1 / x) := by field_simp
    calc |a i| * |a j| * E i j ≤ (a i ^ 2 / 2 * (w j / w i) + a j ^ 2 / 2 * (w i / w j)) * E i j :=
          mul_le_mul_of_nonneg_right h (hE0 i j)
      _ = (a i ^ 2 / 2) * (E i j * w j / w i) + (a j ^ 2 / 2) * (E i j * w i / w j) := by ring
  have key : ∑ i, ∑ j, ((a i ^ 2 / 2) * (E i j * w j / w i) + (a j ^ 2 / 2) * (E i j * w i / w j))
      = ∑ i, a i ^ 2 / w i * ∑ j, E i j * w j := by
    have h₁ : ∑ i, ∑ j, (a j ^ 2 / 2) * (E i j * w i / w j) = ∑ i, ∑ j, (a i ^ 2 / 2) * (E j i * w j / w i) :=
      Finset.sum_comm
    have h₂ : ∀ i, ∑ j, (a i ^ 2 / 2) * (E j i * w j / w i) = ∑ j, (a i ^ 2 / 2) * (E i j * w j / w i) :=
      fun i => Finset.sum_congr rfl fun j _ => by rw [hsym j i]
    simp only [Finset.sum_add_distrib]
    rw [h₁, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [h₂ i, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    have := (hw i).ne'
    field_simp
    ring
  calc ∑ i, ∑ j, |a i| * |a j| * E i j
      ≤ ∑ i, ∑ j, ((a i ^ 2 / 2) * (E i j * w j / w i) + (a j ^ 2 / 2) * (E i j * w i / w j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hab i j
    _ = ∑ i, a i ^ 2 / w i * ∑ j, E i j * w j := key
    _ ≤ ∑ i, a i ^ 2 / w i * (e * w i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (by have := hw i; positivity)
    _ = e * ∑ i, a i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        have := (hw i).ne'
        field_simp

end Cvs.Prolate.RungEnvelopeSchurTest
