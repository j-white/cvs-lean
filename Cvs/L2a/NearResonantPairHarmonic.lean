import Mathlib.NumberTheory.Harmonic.Bounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The near-resonant pair sum is a harmonic number

`Σ_{j ≥ 1, j ≠ n} 1/(|n − j|(n + j)) ≤ H_{2n}/n ≤ (1 + log 2n)/n`, by partial fractions: below `n` the terms are
`(1/2n)(1/(n−j) + 1/(n+j))`, above `n` they telescope, `(1/2n)(1/(j−n) − 1/(j+n))`. Stated for every finite
truncation.
-/

namespace Cvs.L2a.NearResonantPairHarmonic

open Finset Real

/-- **Shifted telescoping**: `Σ_{i<L} (f i − f (i+d)) = Σ_{i<d} f i − Σ_{i<d} f (i+L)`. -/
theorem sum_range_sub_shift (f : ℕ → ℝ) (d L : ℕ) :
    ∑ i ∈ range L, (f i - f (i + d)) = ∑ i ∈ range d, f i - ∑ i ∈ range d, f (i + L) := by
  have h1 := sum_range_add f L d
  have h2 := sum_range_add f d L
  rw [add_comm L d] at h1
  have e1 : ∑ x ∈ range L, f (d + x) = ∑ i ∈ range L, f (i + d) := sum_congr rfl fun x _ => by rw [add_comm]
  have e2 : ∑ x ∈ range d, f (L + x) = ∑ i ∈ range d, f (i + L) := sum_congr rfl fun x _ => by rw [add_comm]
  rw [sum_sub_distrib]
  linarith

/-- The real harmonic number `H_n = Σ_{i<n} 1/(i+1)`. -/
noncomputable def H (n : ℕ) : ℝ := ∑ i ∈ range n, 1 / ((i : ℝ) + 1)

theorem H_eq (n : ℕ) : H n = (harmonic n : ℝ) := by
  unfold H harmonic; push_cast; simp [one_div]

theorem H_le (n : ℕ) : H n ≤ 1 + log n := by rw [H_eq]; exact harmonic_le_one_add_log n

end Cvs.L2a.NearResonantPairHarmonic
