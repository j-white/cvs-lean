import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Cvs.L2a.OrbitGapIntegerM

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The top-corner constants `κ̂_m`, `κ_m` and their sums over `2 ≤ m ≤ M − 1`

With `ΔY x = Ymax x − 1`, `p = M/m` and `η = Ymax p / m`, put `κ̂_m = 2√(ΔY M · ΔY p)/(π m (1 − η²))` and
`κ_m = 2√(ΔY M · ΔY p)/(π m (1 − η))`. The orbit gap gives `1 − η² ≥ 11/20`, `ΔY x < 1/(2(x² − 1))` and
`m²(p² − 1) = M² − m²` give `κ̂_m² < (400/(121π²))/((M² − 1)(M² − m²))`, and the sum is a harmonic number.
-/

namespace Cvs.L2a.TopCornerConstants

open Real Finset
open Cvs.L2a.OrbitGapIntegerM (Ymax)

/-- `ΔY x = Ymax x − 1 = x/√(x² − 1) − 1`. -/
noncomputable def dY (x : ℝ) : ℝ := Ymax x - 1

theorem dY_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ dY x := by
  have hpos : 0 < x ^ 2 - 1 := by nlinarith
  have hs := Real.sqrt_pos.2 hpos
  have hsx : √(x ^ 2 - 1) ≤ x := by
    rw [Real.sqrt_le_left (by linarith)]; linarith
  unfold dY Ymax
  rw [sub_nonneg, le_div_iff₀ hs, one_mul]
  exact hsx

/-- `ΔY x < 1/(2(x² − 1))`: `ΔY x = (x − s)/s` with `s = √(x² − 1) < x` and `x² − s² = 1`. -/
theorem dY_lt {x : ℝ} (hx : 1 < x) : dY x < 1 / (2 * (x ^ 2 - 1)) := by
  have hpos : 0 < x ^ 2 - 1 := by nlinarith
  set s := √(x ^ 2 - 1) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hpos
  have hs2 : s ^ 2 = x ^ 2 - 1 := Real.sq_sqrt hpos.le
  have hsx : s < x := by nlinarith
  unfold dY Ymax
  rw [← hs_def, ← hs2, sub_lt_iff_lt_add, div_lt_iff₀ hs]
  rw [show (1 / (2 * s ^ 2) + 1) * s = 1 / (2 * s) + s by field_simp]
  have h : x - s < 1 / (2 * s) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- `Σ_{2 ≤ m ≤ M − 1} 1/(M − m) = H_{M−2}`. -/
theorem sum_inv_sub_eq_harmonic (M : ℕ) (hM : 2 ≤ M) :
    ∑ m ∈ Ico 2 M, 1 / ((M : ℝ) - m) = (harmonic (M - 2) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  apply Finset.sum_nbij' (fun m => M - m) (fun k => M - k)
  · intro m hm; simp only [Finset.mem_Ico, Finset.mem_Icc] at hm ⊢; omega
  · intro k hk; simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢; omega
  · intro m hm; simp only [Finset.mem_Ico] at hm; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro m hm
    simp only [mem_Ico] at hm
    rw [Nat.cast_sub (by omega), one_div]

theorem harmonic_nonneg (n : ℕ) : (0 : ℝ) ≤ harmonic n := by
  rw [harmonic_eq_sum_Icc]; push_cast; positivity

end Cvs.L2a.TopCornerConstants
