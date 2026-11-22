import Mathlib
import Cvs.L2a.WindowFormDeepSpan
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The deep index set at `c = 2πx` and the pole-free spine span

`deepSet x` collects the `j < x` whose even level of index `2j` exists and satisfies `5c ≤ c² − χ` at `c = 2πx`.
It is an initial segment of `range x` containing `0` once `c0 ≤ 2πx`. The spine span is cut out by subtracting the
ground rung with weight `α_j = ∫h_{4j}/∫h₀`, so every member has vanishing integral.
-/

noncomputable section

open Real Set MeasureTheory Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Approximant.DeepIndexSpineSpan

/-! ### The deep index set -/

open Classical in
/-- The deep indices at `c = 2πx`: `j < x` whose level of index `2j` exists and lies at or below `c² − 5c`. -/
def deepSet (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun j => ∃ χ, IsLevelIdx (2 * π * x) (2 * j) χ ∧ 5 * (2 * π * x) ≤ (2 * π * x) ^ 2 - χ

/-- Membership in `deepSet x`, stated through `lev`. -/
theorem mem_deepSet {x j : ℕ} :
    j ∈ deepSet x ↔ j < x ∧ (∃ χ, IsLevelIdx (2 * π * x) (2 * j) χ) ∧
      5 * (2 * π * x) ≤ (2 * π * x) ^ 2 - lev (2 * π * x) (2 * j) := by
  simp only [deepSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, χ, hχ, h5⟩
    exact ⟨hj, ⟨χ, hχ⟩, by rwa [lev_eq hχ]⟩
  · rintro ⟨hj, hex, h5⟩
    exact ⟨hj, _, lev_spec hex, h5⟩

/-- `c0 ≥ 10¹⁶`. -/
theorem c0_ge : (10 : ℝ) ^ 16 ≤ Cvs.L2a.WindowFormDeepSpan.c0 := le_max_left _ _

/-- **The ground index is deep** once `c0 ≤ 2πx`. -/
theorem zero_mem_deepSet {x : ℕ} (hx : Cvs.L2a.WindowFormDeepSpan.c0 ≤ 2 * π * x) : 0 ∈ deepSet x := by
  have hc : (10 : ℝ) ^ 16 ≤ 2 * π * x := c0_ge.trans hx
  have hx1 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h
      norm_num at hc
    · exact h
  simp only [deepSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨hx1, groundLevel (2 * π * x), by simpa using isLevelIdx_zero (2 * π * x), ?_⟩
  exact five_mul_le_sub_groundLevel (by linarith)

/-- **A count certificate for depth**: `2j` below the number of even levels under `c² − 5c` makes `j` deep. -/
theorem mem_deepSet_of_lt_ncard {x j : ℕ} (hj : j < x)
    (h : 2 * j < (evenSpec (sqC (2 * π * x)) ∩ Iio ((2 * π * x) ^ 2 - 5 * (2 * π * x))).ncard) :
    j ∈ deepSet x := by
  obtain ⟨χ, hχ, hidx⟩ := exists_isLevelIdx_of_lt_ncard h
  simp only [deepSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨hj, χ, hidx, by linarith⟩

/-- **The deep set has at most `c/4 + 1` members** at `c = 2πx`. -/
theorem card_deepSet_le (x : ℕ) : ((deepSet x).card : ℝ) ≤ 2 * π * x / 4 + 1 := by
  have hsub : (deepSet x).card ≤ x := by
    have h : deepSet x ⊆ Finset.range x := fun j hj => Finset.mem_range.mpr (mem_deepSet.mp hj).1
    exact (Finset.card_le_card h).trans (Finset.card_range x).le
  have hcast : ((deepSet x).card : ℝ) ≤ x := by exact_mod_cast hsub
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  nlinarith [Real.pi_gt_three]

/-! ### The pole-free spine span -/

/-- The ground weight `α_j = ∫h_{4j} / ∫h₀` of the rung of even index `2j`. -/
def alpha (c : ℝ) (j : ℕ) : ℝ := (∫ s in (-1 : ℝ)..1, rung c (2 * j) s) / ∫ s in (-1 : ℝ)..1, rung c 0 s

/-- The spine profile `Σ_j a_j (h_{4j} − α_j h₀)` over an index set `S`. -/
def spineG (c : ℝ) {S : Finset ℕ} (a : S → ℝ) (s : ℝ) : ℝ :=
  ∑ j, a j * (rung c (2 * (j : ℕ)) s - alpha c j * rung c 0 s)

/-- The raw rung is continuous on `[−1, 1]` at every `χ` (it is `0` off the even spectrum). -/
theorem continuousOn_rawRung (c χ : ℝ) : ContinuousOn (rawRung c χ).1 (Icc (-1) 1) := by
  by_cases hχ : χ ∈ evenSpec (sqC c)
  · obtain ⟨hg, -⟩ := rawRung_spec hχ
    exact fun s hs =>
      (hg s (by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)])).continuousAt.continuousWithinAt
  · unfold rawRung
    rw [dif_neg hχ]
    exact continuousOn_const

/-- Every rung is interval integrable on `[−1, 1]`. -/
theorem intervalIntegrable_rung (c : ℝ) (k : ℕ) : IntervalIntegrable (rung c k) volume (-1) 1 := by
  have h : ContinuousOn (rung c k) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact (continuousOn_rawRung c (lev c k)).div_const _
  exact h.intervalIntegrable

/-- **The spine profile has vanishing integral**: every member of the span is pole-free. -/
theorem integral_spineG {c : ℝ} (hc : 0 < c) {S : Finset ℕ} (a : S → ℝ) :
    ∫ s in (-1 : ℝ)..1, spineG c a s = 0 := by
  have hI0 := integral_rung_zero_ne hc
  have hint : ∀ j : S, IntervalIntegrable
      (fun s => a j * (rung c (2 * (j : ℕ)) s - alpha c j * rung c 0 s)) volume (-1) 1 := fun j =>
    ((intervalIntegrable_rung c _).sub ((intervalIntegrable_rung c 0).const_mul _)).const_mul _
  unfold spineG
  rw [intervalIntegral.integral_finsetSum fun j _ => hint j]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (intervalIntegrable_rung c _)
    ((intervalIntegrable_rung c 0).const_mul _), intervalIntegral.integral_const_mul]
  unfold alpha
  rw [div_mul_cancel₀ _ hI0, sub_self, mul_zero]

/-! ### The prime-power window sizes -/

/-- **The window sizes**: `P = x` and `R = ⌈log₂ x⌉` satisfy the size conditions at `c = 2πx`. -/
theorem sizes_PR {x : ℕ} (hx : 1 ≤ x) :
    1 / (2 * π / (2 * π * x)) ≤ (x : ℝ) ∧
      Real.log (1 / (2 * π / (2 * π * x))) ≤ (Nat.clog 2 x : ℝ) * Real.log 2 := by
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have he : 1 / (2 * π / (2 * π * x)) = (x : ℝ) := by
    field_simp
  rw [he]
  refine ⟨le_rfl, ?_⟩
  have hpow : (x : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 x := by exact_mod_cast Nat.le_pow_clog (by norm_num) x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  calc Real.log x ≤ Real.log ((2 : ℝ) ^ Nat.clog 2 x) := Real.log_le_log hxpos hpow
    _ = (Nat.clog 2 x : ℝ) * Real.log 2 := Real.log_pow _ _

end Cvs.Approximant.DeepIndexSpineSpan
