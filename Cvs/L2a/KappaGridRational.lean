import Mathlib
import Cvs.L2a.CutEstimateFrameFloor
import Cvs.L2a.CutRemainderDensity
import Cvs.L2a.KappaUniformInX
import Cvs.L2a.RampCutSumsUniform
import Cvs.Upstream.LogFiveSevenBounds
import Cvs.Upstream.SineSquaredRamp

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `KappaUniformInX`'s grid in rational form

On the ramp grid `5/4 + j/32`, `nsRamp = log θ·sin²(jπ/16)` with `sin²(jπ/16) = ½ ∓ cos(jπ/8)/2` in radicals and
`log θ = log(3/2) + log(1 − (8 − j)/48)`; `L₃` on the tail grid from `log 2, 3, 5, 7`; `g₁₂`, `G₃` under
square-root witnesses with `ζ(3) ≤ 29/24`; and the three cell inequalities of `gridSum`.
-/

noncomputable section

open Real Set Cvs.L2a.CutEstimateFrameFloor Cvs.L2a.RampCutSumsUniform Cvs.L2a.CutRemainderDensity Cvs.L2a.KappaUniformInX

namespace Cvs.L2a.KappaGridRational

theorem sqrt_two_bounds : (141421356 / 100000000 : ℝ) ≤ √2 ∧ √2 ≤ 141421357 / 100000000 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem sqrt_two_add_bounds : (184775906 / 100000000 : ℝ) ≤ √(2 + √2) ∧ √(2 + √2) ≤ 184775907 / 100000000 := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  constructor
  · rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  · rw [Real.sqrt_le_left (by norm_num)]; nlinarith

theorem sqrt_two_sub_bounds : (76536685 / 100000000 : ℝ) ≤ √(2 - √2) ∧ √(2 - √2) ≤ 76536687 / 100000000 := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  constructor
  · rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  · rw [Real.sqrt_le_left (by norm_num)]; nlinarith

/-- `cos(3π/8) = sin(π/8)`. -/
theorem cos_three_pi_div_eight : Real.cos (3 * π / 8) = √(2 - √2) / 2 := by
  rw [show 3 * π / 8 = π / 2 - π / 8 by ring, Real.cos_pi_div_two_sub, Real.sin_pi_div_eight]

/-- `sin²(jπ/16) = ½ − cos(jπ/8)/2`, in closed form for `j = 1, …, 7`. -/
theorem sin_sq_grid :
    Real.sin (π / 16) ^ 2 = 1 / 2 - √(2 + √2) / 4 ∧ Real.sin (2 * π / 16) ^ 2 = 1 / 2 - √2 / 4
    ∧ Real.sin (3 * π / 16) ^ 2 = 1 / 2 - √(2 - √2) / 4 ∧ Real.sin (4 * π / 16) ^ 2 = 1 / 2
    ∧ Real.sin (5 * π / 16) ^ 2 = 1 / 2 + √(2 - √2) / 4 ∧ Real.sin (6 * π / 16) ^ 2 = 1 / 2 + √2 / 4
    ∧ Real.sin (7 * π / 16) ^ 2 = 1 / 2 + √(2 + √2) / 4 := by
  have e : ∀ x : ℝ, Real.sin x ^ 2 = 1 / 2 - Real.cos (2 * x) / 2 := fun x => Real.sin_sq_eq_half_sub x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, show 2 * (π / 16) = π / 8 by ring, Real.cos_pi_div_eight]; ring
  · rw [e, show 2 * (2 * π / 16) = π / 4 by ring, Real.cos_pi_div_four]; ring
  · rw [e, show 2 * (3 * π / 16) = 3 * π / 8 by ring, cos_three_pi_div_eight]; ring
  · rw [e, show 2 * (4 * π / 16) = π / 2 by ring, Real.cos_pi_div_two]; ring
  · rw [e, show 2 * (5 * π / 16) = π - 3 * π / 8 by ring, Real.cos_pi_sub, cos_three_pi_div_eight]; ring
  · rw [e, show 2 * (6 * π / 16) = π - π / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]; ring
  · rw [e, show 2 * (7 * π / 16) = π - π / 8 by ring, Real.cos_pi_sub, Real.cos_pi_div_eight]; ring

/-- On the ramp grid, `nsRamp(5/4 + j/32) = log(5/4 + j/32)·sin²(jπ/16)` for `1 ≤ j ≤ 7`. -/
theorem nsRamp_gridA {j : ℕ} (h1 : 1 ≤ j) (h7 : j ≤ 7) :
    nsRamp (gridA j) = Real.log (gridA j) * Real.sin (j * π / 16) ^ 2 := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast h1
  have hj7 : (j : ℝ) ≤ 7 := by exact_mod_cast h7
  unfold nsRamp Cvs.Upstream.SineSquaredRamp.ramp gridA
  rw [if_neg (by linarith), if_pos (by linarith)]
  congr 3
  ring

/-- `log(5/4 + j/32) = log(3/2) + log(1 − (8 − j)/48)`. -/
theorem log_gridA (j : ℕ) (h8 : j ≤ 8) :
    Real.log (gridA j) = Real.log (3 / 2) + Real.log (1 - (8 - (j : ℝ)) / 48) := by
  have hj8 : (j : ℝ) ≤ 8 := by exact_mod_cast h8
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold gridA
  rw [← Real.log_mul (by norm_num) (by linarith)]
  congr 1; ring

theorem log_three_halves_bounds :
    (4054651077 / 10000000000 : ℝ) ≤ Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ 4054651085 / 10000000000 := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9]

/-- `log(1 − x)` for `x = k/48`, from six terms of the series. -/
theorem log_one_sub_bounds (k : ℕ) (hk : k ≤ 7) :
    -(∑ i ∈ Finset.range 6, ((k : ℝ) / 48) ^ (i + 1) / (i + 1)) - ((k : ℝ) / 48) ^ 7 / (1 - (k : ℝ) / 48)
      ≤ Real.log (1 - (k : ℝ) / 48)
    ∧ Real.log (1 - (k : ℝ) / 48)
      ≤ -(∑ i ∈ Finset.range 6, ((k : ℝ) / 48) ^ (i + 1) / (i + 1)) + ((k : ℝ) / 48) ^ 7 / (1 - (k : ℝ) / 48) := by
  have hk7 : (k : ℝ) ≤ 7 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hx : |(k : ℝ) / 48| < 1 := by rw [abs_of_nonneg (by positivity)]; rw [div_lt_one (by norm_num)]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 6
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) / 48)] at h
  constructor <;> linarith [(abs_le.1 h).1, (abs_le.1 h).2]

/-! ### Grid points -/

theorem gridA_vals : gridA 0 = 5 / 4 ∧ gridA 1 = 41 / 32 ∧ gridA 2 = 21 / 16 ∧ gridA 3 = 43 / 32 ∧ gridA 4 = 11 / 8
    ∧ gridA 5 = 45 / 32 ∧ gridA 6 = 23 / 16 ∧ gridA 7 = 47 / 32 ∧ gridA 8 = 3 / 2 := by
  unfold gridA; norm_num

theorem gridB_vals : gridB 0 = 3 / 2 ∧ gridB 1 = 7 / 4 ∧ gridB 2 = 2 ∧ gridB 3 = 5 / 2 ∧ gridB 4 = 3
    ∧ gridB 5 = 4 ∧ gridB 6 = 6 := by
  simp [gridB]

/-! ### `nsRamp` on the ramp grid -/

theorem nsRamp_gridA_1 : (29477 / 3125000 : ℝ) ≤ nsRamp (gridA 1) ∧ nsRamp (gridA 1) ≤ (471639 / 50000000 : ℝ) := by
  rw [nsRamp_gridA (j := 1) (by norm_num) (by norm_num), log_gridA 1 (by norm_num)]
  have hs := sin_sq_grid.1
  rw [show ((1 : ℕ) : ℝ) * π / 16 = π / 16 by push_cast; ring, hs]
  have hl := log_one_sub_bounds 7 (by norm_num)
  have h32 := log_three_halves_bounds
  obtain ⟨a1, a2⟩ := sqrt_two_bounds
  obtain ⟨b1, b2⟩ := sqrt_two_add_bounds
  obtain ⟨c1, c2⟩ := sqrt_two_sub_bounds
  norm_num [Finset.sum_range_succ] at hl ⊢
  have hL1 : (7281901114423894837 / 29382082560000000000 : ℝ) ≤ Real.log (3 / 2) + Real.log (1 - 7 / 48) := by norm_num at hl ⊢; linarith [hl.1, h32.1]
  have hL2 : Real.log (3 / 2) + Real.log (1 - 7 / 48) ≤ (1456399529374974677 / 5876416512000000000 : ℝ) := by norm_num at hl ⊢; linarith [hl.2, h32.2]
  norm_num at hL1 hL2 ⊢
  constructor <;> nlinarith

theorem nsRamp_gridA_2 : (398237 / 10000000 : ℝ) ≤ nsRamp (gridA 2) ∧ nsRamp (gridA 2) ≤ (3982387 / 100000000 : ℝ) := by
  rw [nsRamp_gridA (j := 2) (by norm_num) (by norm_num), log_gridA 2 (by norm_num)]
  have hs := sin_sq_grid.2.1
  rw [show ((2 : ℕ) : ℝ) * π / 16 = 2 * π / 16 by push_cast; ring, hs]
  have hl := log_one_sub_bounds 6 (by norm_num)
  have h32 := log_three_halves_bounds
  obtain ⟨a1, a2⟩ := sqrt_two_bounds
  obtain ⟨b1, b2⟩ := sqrt_two_add_bounds
  obtain ⟨c1, c2⟩ := sqrt_two_sub_bounds
  norm_num [Finset.sum_range_succ] at hl ⊢
  have hL1 : (29238262676779 / 107520000000000 : ℝ) ≤ Real.log (3 / 2) + Real.log (1 - 6 / 48) := by norm_num at hl ⊢; linarith [hl.1, h32.1]
  have hL2 : Real.log (3 / 2) + Real.log (1 - 6 / 48) ≤ (5847675990059 / 21504000000000 : ℝ) := by norm_num at hl ⊢; linarith [hl.2, h32.2]
  norm_num at hL1 hL2 ⊢
  constructor <;> nlinarith

theorem nsRamp_gridA_3 : (9119743 / 100000000 : ℝ) ≤ nsRamp (gridA 3) ∧ nsRamp (gridA 3) ≤ (4559877 / 50000000 : ℝ) := by
  rw [nsRamp_gridA (j := 3) (by norm_num) (by norm_num), log_gridA 3 (by norm_num)]
  have hs := sin_sq_grid.2.2.1
  rw [show ((3 : ℕ) : ℝ) * π / 16 = 3 * π / 16 by push_cast; ring, hs]
  have hl := log_one_sub_bounds 5 (by norm_num)
  have h32 := log_three_halves_bounds
  obtain ⟨a1, a2⟩ := sqrt_two_bounds
  obtain ⟨b1, b2⟩ := sqrt_two_add_bounds
  obtain ⟨c1, c2⟩ := sqrt_two_sub_bounds
  norm_num [Finset.sum_range_succ] at hl ⊢
  have hL1 : (9104830629129404951 / 30815354880000000000 : ℝ) ≤ Real.log (3 / 2) + Real.log (1 - 5 / 48) := by norm_num at hl ⊢; linarith [hl.1, h32.1]
  have hL2 : Real.log (3 / 2) + Real.log (1 - 5 / 48) ≤ (1820967961811025271 / 6163070976000000000 : ℝ) := by norm_num at hl ⊢; linarith [hl.2, h32.2]
  norm_num at hL1 hL2 ⊢
  constructor <;> nlinarith

theorem nsRamp_gridA_4 : (3184537 / 20000000 : ℝ) ≤ nsRamp (gridA 4) ∧ nsRamp (gridA 4) ≤ (15922689 / 100000000 : ℝ) := by
  rw [nsRamp_gridA (j := 4) (by norm_num) (by norm_num), log_gridA 4 (by norm_num)]
  have hs := sin_sq_grid.2.2.2.1
  rw [show ((4 : ℕ) : ℝ) * π / 16 = 4 * π / 16 by push_cast; ring, hs]
  have hl := log_one_sub_bounds 4 (by norm_num)
  have h32 := log_three_halves_bounds
  obtain ⟨a1, a2⟩ := sqrt_two_bounds
  obtain ⟨b1, b2⟩ := sqrt_two_add_bounds
  obtain ⟨c1, c2⟩ := sqrt_two_sub_bounds
  norm_num [Finset.sum_range_succ] at hl ⊢
  have hL1 : (612883261659487 / 1924560000000000 : ℝ) ≤ Real.log (3 / 2) + Real.log (1 - 4 / 48) := by norm_num at hl ⊢; linarith [hl.1, h32.1]
  have hL2 : Real.log (3 / 2) + Real.log (1 - 4 / 48) ≤ (122576676077327 / 384912000000000 : ℝ) := by norm_num at hl ⊢; linarith [hl.2, h32.2]
  norm_num at hL1 hL2 ⊢
  constructor <;> nlinarith

theorem nsRamp_gridA_5 : (5892419 / 25000000 : ℝ) ≤ nsRamp (gridA 5) ∧ nsRamp (gridA 5) ≤ (11784839 / 50000000 : ℝ) := by
  rw [nsRamp_gridA (j := 5) (by norm_num) (by norm_num), log_gridA 5 (by norm_num)]
  have hs := sin_sq_grid.2.2.2.2.1
  rw [show ((5 : ℕ) : ℝ) * π / 16 = 5 * π / 16 by push_cast; ring, hs]
  have hl := log_one_sub_bounds 3 (by norm_num)
  have h32 := log_three_halves_bounds
  obtain ⟨a1, a2⟩ := sqrt_two_bounds
  obtain ⟨b1, b2⟩ := sqrt_two_add_bounds
  obtain ⟨c1, c2⟩ := sqrt_two_sub_bounds
  norm_num [Finset.sum_range_succ] at hl ⊢
  have hL1 : (335144468301533 / 983040000000000 : ℝ) ≤ Real.log (3 / 2) + Real.log (1 - 3 / 48) := by norm_num at hl ⊢; linarith [hl.1, h32.1]
  have hL2 : Real.log (3 / 2) + Real.log (1 - 3 / 48) ≤ (67028895380093 / 196608000000000 : ℝ) := by norm_num at hl ⊢; linarith [hl.2, h32.2]
  norm_num at hL1 hL2 ⊢
  constructor <;> nlinarith

theorem nsRamp_gridA_6 : (30975921 / 100000000 : ℝ) ≤ nsRamp (gridA 6) ∧ nsRamp (gridA 6) ≤ (15487961 / 50000000 : ℝ) := by
  rw [nsRamp_gridA (j := 6) (by norm_num) (by norm_num), log_gridA 6 (by norm_num)]
  have hs := sin_sq_grid.2.2.2.2.2.1
  rw [show ((6 : ℕ) : ℝ) * π / 16 = 6 * π / 16 by push_cast; ring, hs]
  have hl := log_one_sub_bounds 2 (by norm_num)
  have h32 := log_three_halves_bounds
  obtain ⟨a1, a2⟩ := sqrt_two_bounds
  obtain ⟨b1, b2⟩ := sqrt_two_add_bounds
  obtain ⟨c1, c2⟩ := sqrt_two_sub_bounds
  norm_num [Finset.sum_range_succ] at hl ⊢
  have hL1 : (93463087143525499 / 257541120000000000 : ℝ) ≤ Real.log (3 / 2) + Real.log (1 - 2 / 48) := by norm_num at hl ⊢; linarith [hl.1, h32.1]
  have hL2 : Real.log (3 / 2) + Real.log (1 - 2 / 48) ≤ (18692617493349179 / 51508224000000000 : ℝ) := by norm_num at hl ⊢; linarith [hl.2, h32.2]
  norm_num at hL1 hL2 ⊢
  constructor <;> nlinarith

theorem nsRamp_gridA_7 : (36978089 / 100000000 : ℝ) ≤ nsRamp (gridA 7) ∧ nsRamp (gridA 7) ≤ (36978091 / 100000000 : ℝ) := by
  rw [nsRamp_gridA (j := 7) (by norm_num) (by norm_num), log_gridA 7 (by norm_num)]
  have hs := sin_sq_grid.2.2.2.2.2.2
  rw [show ((7 : ℕ) : ℝ) * π / 16 = 7 * π / 16 by push_cast; ring, hs]
  have hl := log_one_sub_bounds 1 (by norm_num)
  have h32 := log_three_halves_bounds
  obtain ⟨a1, a2⟩ := sqrt_two_bounds
  obtain ⟨b1, b2⟩ := sqrt_two_add_bounds
  obtain ⟨c1, c2⟩ := sqrt_two_sub_bounds
  norm_num [Finset.sum_range_succ] at hl ⊢
  have hL1 : (12947716203212300179 / 33681899520000000000 : ℝ) ≤ Real.log (3 / 2) + Real.log (1 - 1 / 48) := by norm_num at hl ⊢; linarith [hl.1, h32.1]
  have hL2 : Real.log (3 / 2) + Real.log (1 - 1 / 48) ≤ (2589543246055001459 / 6736379904000000000 : ℝ) := by norm_num at hl ⊢; linarith [hl.2, h32.2]
  norm_num at hL1 hL2 ⊢
  constructor <;> nlinarith

theorem nsRamp_gridA_0 : nsRamp (gridA 0) = 0 := nsRamp_of_le (by rw [gridA_vals.1])

theorem nsRamp_gridA_8 : (40546510 / 100000000 : ℝ) ≤ nsRamp (gridA 8) ∧ nsRamp (gridA 8) ≤ 40546511 / 100000000 := by
  rw [nsRamp_of_ge (by rw [gridA_vals.2.2.2.2.2.2.2.2]), gridA_vals.2.2.2.2.2.2.2.2]
  have := log_three_halves_bounds
  constructor <;> linarith [this.1, this.2]

/-! ### `L₃` on the tail grid -/

theorem L3_gridB_0 : (50303617 / 250000000 : ℝ) ≤ L3 (gridB 0) ∧ L3 (gridB 0) ≤ (201214469 / 1000000000 : ℝ) := by
  rw [gridB_vals.1]
  unfold L3
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have l3 := Real.log_three_gt_d9
  have l3' := Real.log_three_lt_d9
  have l5 := Cvs.Enclosure.log_five_bounds'
  have l7 := Cvs.Enclosure.log_seven_bounds'
  have h32 := log_three_halves_bounds
  have e74 : Real.log (7 / 4) = Real.log 7 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e52 : Real.log (5 / 2) = Real.log 5 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [e74, e52, e4, e6]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]
  · rw [div_le_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]

theorem L3_gridB_1 : (172998471 / 1000000000 : ℝ) ≤ L3 (gridB 1) ∧ L3 (gridB 1) ≤ (43249659 / 250000000 : ℝ) := by
  rw [gridB_vals.2.1]
  unfold L3
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have l3 := Real.log_three_gt_d9
  have l3' := Real.log_three_lt_d9
  have l5 := Cvs.Enclosure.log_five_bounds'
  have l7 := Cvs.Enclosure.log_seven_bounds'
  have h32 := log_three_halves_bounds
  have e74 : Real.log (7 / 4) = Real.log 7 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e52 : Real.log (5 / 2) = Real.log 5 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [e74, e52, e4, e6]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]
  · rw [div_le_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]

theorem L3_gridB_2 : (149143397 / 1000000000 : ℝ) ≤ L3 (gridB 2) ∧ L3 (gridB 2) ≤ (74571699 / 500000000 : ℝ) := by
  rw [gridB_vals.2.2.1]
  unfold L3
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have l3 := Real.log_three_gt_d9
  have l3' := Real.log_three_lt_d9
  have l5 := Cvs.Enclosure.log_five_bounds'
  have l7 := Cvs.Enclosure.log_seven_bounds'
  have h32 := log_three_halves_bounds
  have e74 : Real.log (7 / 4) = Real.log 7 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e52 : Real.log (5 / 2) = Real.log 5 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [e74, e52, e4, e6]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]
  · rw [div_le_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]

theorem L3_gridB_3 : (22660637 / 200000000 : ℝ) ≤ L3 (gridB 3) ∧ L3 (gridB 3) ≤ (56651673 / 500000000 : ℝ) := by
  rw [gridB_vals.2.2.2.1]
  unfold L3
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have l3 := Real.log_three_gt_d9
  have l3' := Real.log_three_lt_d9
  have l5 := Cvs.Enclosure.log_five_bounds'
  have l7 := Cvs.Enclosure.log_seven_bounds'
  have h32 := log_three_halves_bounds
  have e74 : Real.log (7 / 4) = Real.log 7 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e52 : Real.log (5 / 2) = Real.log 5 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [e74, e52, e4, e6]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]
  · rw [div_le_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]

theorem L3_gridB_4 : (88811793 / 1000000000 : ℝ) ≤ L3 (gridB 4) ∧ L3 (gridB 4) ≤ (44405897 / 500000000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.1]
  unfold L3
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have l3 := Real.log_three_gt_d9
  have l3' := Real.log_three_lt_d9
  have l5 := Cvs.Enclosure.log_five_bounds'
  have l7 := Cvs.Enclosure.log_seven_bounds'
  have h32 := log_three_halves_bounds
  have e74 : Real.log (7 / 4) = Real.log 7 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e52 : Real.log (5 / 2) = Real.log 5 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [e74, e52, e4, e6]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]
  · rw [div_le_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]

theorem L3_gridB_5 : (29473349 / 500000000 : ℝ) ≤ L3 (gridB 5) ∧ L3 (gridB 5) ≤ (58946699 / 1000000000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.2.1]
  unfold L3
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have l3 := Real.log_three_gt_d9
  have l3' := Real.log_three_lt_d9
  have l5 := Cvs.Enclosure.log_five_bounds'
  have l7 := Cvs.Enclosure.log_seven_bounds'
  have h32 := log_three_halves_bounds
  have e74 : Real.log (7 / 4) = Real.log 7 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e52 : Real.log (5 / 2) = Real.log 5 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [e74, e52, e4, e6]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]
  · rw [div_le_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]

theorem L3_gridB_6 : (3978749 / 125000000 : ℝ) ≤ L3 (gridB 6) ∧ L3 (gridB 6) ≤ (31829993 / 1000000000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.2.2]
  unfold L3
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have l3 := Real.log_three_gt_d9
  have l3' := Real.log_three_lt_d9
  have l5 := Cvs.Enclosure.log_five_bounds'
  have l7 := Cvs.Enclosure.log_seven_bounds'
  have h32 := log_three_halves_bounds
  have e74 : Real.log (7 / 4) = Real.log 7 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e52 : Real.log (5 / 2) = Real.log 5 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num [e74, e52, e4, e6]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]
  · rw [div_le_iff₀ (by norm_num)]; linarith [l5.1, l5.2, l7.1, l7.2, h32.1, h32.2]

/-! ### The kernels at the grid points -/

theorem g12_le_at {t w1 w2 : ℝ} (ht : 5 / 4 ≤ t) (hw1 : 0 < w1) (h1 : w1 ^ 2 ≤ 4 * t ^ 2 - 1)
    (hw2 : 0 ≤ w2) (h2 : t ^ 2 - 1 ≤ w2 ^ 2) :
    g12 t ≤ (t / w1 + 4 * t * w2 / (4 * t ^ 2 - 1)) / (3 * t ^ 2 - 4) := by
  unfold g12
  have hd : 0 < 3 * t ^ 2 - 4 := by nlinarith
  apply div_le_div_of_nonneg_right _ hd.le
  have hs1 : w1 ≤ √(4 * t ^ 2 - 1) := Real.le_sqrt_of_sq_le h1
  have hs2 : √(t ^ 2 - 1) ≤ w2 := by rw [Real.sqrt_le_left hw2]; exact h2
  have hq : 0 < 4 * t ^ 2 - 1 := by nlinarith
  have ht0 : 0 < t := by linarith
  have a : t / √(4 * t ^ 2 - 1) ≤ t / w1 := div_le_div_of_nonneg_left ht0.le hw1 hs1
  have b : 4 * t * √(t ^ 2 - 1) / (4 * t ^ 2 - 1) ≤ 4 * t * w2 / (4 * t ^ 2 - 1) := by
    apply div_le_div_of_nonneg_right _ hq.le
    exact mul_le_mul_of_nonneg_left hs2 (by positivity)
  linarith

theorem zeta3_le : zeta3 ≤ 29 / 24 := by
  unfold zeta3
  have key : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 3), 1 / (k : ℝ) ^ 3
      ≤ 29 / 24 - 1 / (2 * ((n : ℝ) + 3) * ((n : ℝ) + 2)) := by
    intro n
    induction n with
    | zero => norm_num [Finset.sum_range_succ]
    | succ n ih =>
      rw [show n + 1 + 3 = (n + 3) + 1 by ring, Finset.sum_range_succ]
      push_cast
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h : 1 / (2 * ((n : ℝ) + 3) * ((n : ℝ) + 2)) - 1 / (2 * ((n : ℝ) + 1 + 3) * ((n : ℝ) + 1 + 2))
          = 1 / (((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4)) := by
        field_simp; ring
      have e : 1 / ((n : ℝ) + 3) ^ 3 ≤ 1 / (((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4)) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      linarith
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun n => ?_
  have hmono : ∑ k ∈ Finset.range n, 1 / (k : ℝ) ^ 3 ≤ ∑ k ∈ Finset.range (n + 3), 1 / (k : ℝ) ^ 3 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) (fun i _ _ => by positivity)
  have h1 := key n
  have h2 : 0 ≤ 1 / (2 * ((n : ℝ) + 3) * ((n : ℝ) + 2)) := by positivity
  linarith

theorem zeta3_ge : 9 / 8 ≤ zeta3 := by
  have := sum_inv_cube_le 2
  simp at this
  linarith

theorem G3_le_at {t w3 w4 : ℝ} (ht : 5 / 4 ≤ t) (hw3 : 0 < w3) (h3 : w3 ^ 2 ≤ (3 * t) ^ 2 - 1)
    (hw4 : 0 < w4) (h4 : w4 ^ 2 ≤ t ^ 2 - 1) :
    G3 t ≤ ((29 / 24 - 9 / 8) * (3 * t / w3) / (t ^ 2 - 1)
      + (16449345 / 10000000 - 5 / 4) * aU (3 * t) / (t * w4)) / (1 - aU t / 9) := by
  unfold G3
  have ht0 : 0 < t := by linarith
  have hp : 0 < t ^ 2 - 1 := by nlinarith
  have haU : aU t ≤ 25 / 9 := by
    have := aU_anti (by norm_num : (1 : ℝ) < 5 / 4) ht
    have e : aU (5 / 4) = 25 / 9 := by unfold aU; norm_num
    linarith
  have hd : 0 < 1 - aU t / 9 := by linarith
  apply div_le_div_of_nonneg_right _ hd.le
  have hz := zeta3_le
  have hz0 := zeta3_ge
  have hk : kU (3 * t) ≤ 3 * t / w3 := by
    unfold kU
    exact div_le_div_of_nonneg_left (by linarith) hw3 (Real.le_sqrt_of_sq_le h3)
  have hk0 : 0 ≤ kU (3 * t) := (kU_pos (by linarith)).le
  have hpi : π ^ 2 / 6 ≤ 16449345 / 10000000 := by nlinarith [Real.pi_lt_d6, Real.pi_pos]
  have hpi0 : 0 ≤ π ^ 2 / 6 - 5 / 4 := by nlinarith [Real.pi_gt_d6]
  have ha3 : 0 ≤ aU (3 * t) := by
    unfold aU; have : 0 < (3 * t) ^ 2 - 1 := by nlinarith
    exact div_nonneg (sq_nonneg _) this.le
  have hs4 : w4 ≤ √(t ^ 2 - 1) := Real.le_sqrt_of_sq_le h4
  have a : (zeta3 - 9 / 8) * kU (3 * t) / (t ^ 2 - 1) ≤ (29 / 24 - 9 / 8) * (3 * t / w3) / (t ^ 2 - 1) := by
    apply div_le_div_of_nonneg_right _ hp.le
    exact mul_le_mul (by linarith) hk hk0 (by norm_num)
  have b : (π ^ 2 / 6 - 5 / 4) * aU (3 * t) / (t * √(t ^ 2 - 1))
      ≤ (16449345 / 10000000 - 5 / 4) * aU (3 * t) / (t * w4) := by
    apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (by linarith) ha3) (by positivity)
    exact mul_le_mul_of_nonneg_left hs4 ht0.le
  linarith

/-! ### The cells -/

theorem ramp_cell {f fh n0 n1 a ah lo0 hi1 C : ℝ} (hf0 : 0 ≤ f) (hf : f ≤ fh) (ha0 : 0 ≤ a) (ha : a ≤ ah)
    (hn0 : lo0 ≤ n0) (hn1 : n1 ≤ hi1) (hn01 : n0 ≤ n1) (hn10 : 0 ≤ n1)
    (hC : fh * (hi1 - lo0 + ah * hi1 / 32) ≤ C) : f * (n1 - n0 + a * n1 / 32) ≤ C := by
  have h1 : a * n1 ≤ ah * hi1 := mul_le_mul ha hn1 hn10 (ha0.trans ha)
  have hb0 : 0 ≤ n1 - n0 + a * n1 / 32 := by have := mul_nonneg ha0 hn10; linarith
  have hb : n1 - n0 + a * n1 / 32 ≤ hi1 - lo0 + ah * hi1 / 32 := by linarith
  exact (mul_le_mul hf hb hb0 (hf0.trans hf)).trans hC

theorem tail_cell {f fh b b1 l l1 L L1 a ah C : ℝ} (hf0 : 0 ≤ f) (hf : f ≤ fh) (ha0 : 0 ≤ a) (ha : a ≤ ah)
    (hb : 0 < b) (hbb : b ≤ b1) (hl : l ≤ L) (hl1 : L1 ≤ l1) (hll : l1 ≤ l)
    (hC : fh * b ^ 2 * ((1 / b ^ 2 - 1 / b1 ^ 2) / 2 + ah * b * (L - L1)) ≤ C) :
    f * b ^ 2 * ((1 / b ^ 2 - 1 / b1 ^ 2) / 2 + a * b * (l - l1)) ≤ C := by
  have hsq : 1 / b1 ^ 2 ≤ 1 / b ^ 2 := one_div_le_one_div_of_le (pow_pos hb 2) (pow_le_pow_left₀ hb.le hbb 2)
  have h1 : a * b * (l - l1) ≤ ah * b * (L - L1) :=
    mul_le_mul (mul_le_mul_of_nonneg_right ha hb.le) (by linarith) (by linarith) (mul_nonneg (ha0.trans ha) hb.le)
  have hb0 : 0 ≤ (1 / b ^ 2 - 1 / b1 ^ 2) / 2 + a * b * (l - l1) := by
    have : 0 ≤ a * b * (l - l1) := mul_nonneg (mul_nonneg ha0 hb.le) (by linarith)
    linarith
  have hfb : f * b ^ 2 ≤ fh * b ^ 2 := mul_le_mul_of_nonneg_right hf (by positivity)
  exact (mul_le_mul hfb (by linarith) hb0 (mul_nonneg (hf0.trans hf) (sq_nonneg b))).trans hC

theorem last_cell {f fh l L a ah C : ℝ} (hf0 : 0 ≤ f) (hf : f ≤ fh) (ha0 : 0 ≤ a) (ha : a ≤ ah)
    (hl0 : 0 ≤ l) (hl : l ≤ L) (hC : fh * 6 ^ 2 * (1 / 6 ^ 2 / 2 + ah * 6 * L) ≤ C) :
    f * 6 ^ 2 * (1 / 6 ^ 2 / 2 + a * 6 * l) ≤ C := by
  have h1 : a * 6 * l ≤ ah * 6 * L := mul_le_mul (by linarith) hl hl0 (by linarith)
  have hb0 : 0 ≤ 1 / 6 ^ 2 / 2 + a * 6 * l := by positivity
  exact (mul_le_mul (mul_le_mul_of_nonneg_right hf (by norm_num)) (by linarith) hb0
    (mul_nonneg (hf0.trans hf) (by norm_num))).trans hC

end Cvs.L2a.KappaGridRational
