import Mathlib
import Cvs.Prolate.EvenRungsByIndex

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung operator is four central-square operators plus three dilation squares

With `L_{a,c} f = −((a − s²) f′)′ + c²s² f`, the rung operator `L_{1,c}` equals `4 L_{¼,c/2} + 3 E*E` for the
dilation generator `E = s ∂`, so every rung solves `4 L_{¼,c/2} h + 3 E*E h = χ h` on `[−1, 1]`. On symbols this is
`H = 4H′ + 3s²u²`; along the level-zero curve of `4H′` the rung symbol is `¾ + 3(2y − 1)²/(4(4y − 1))` at `y = s²`,
and the overlap saddle equation `3y² − 4Ty + T = 0` has real roots exactly when `T(4T − 3) ≥ 0`.
-/

noncomputable section

open Real Set

namespace Cvs.Prolate.RungOperatorCentralSquares

open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev)

/-- The prolate operator `L_{a,c} f = −((a − s²) f′)′ + c²s² f` in terms of `f, f′, f″`. -/
def slepOp (a c : ℝ) (f f₁ f₂ : ℝ → ℝ) (s : ℝ) : ℝ := -((a - s ^ 2) * f₂ s - 2 * s * f₁ s) + c ^ 2 * s ^ 2 * f s

/-- The square `E*E f = −(s² f′)′` of the dilation generator `E = s ∂`, in terms of `f′, f″`. -/
def dilSq (f₁ f₂ : ℝ → ℝ) (s : ℝ) : ℝ := -(s ^ 2 * f₂ s + 2 * s * f₁ s)

/-- `slepOp a c` is the divergence form: `((a − s²) f′)′ = (a − s²) f″ − 2s f′`. -/
theorem hasDerivAt_weighted {a : ℝ} {f₁ f₂ : ℝ → ℝ} {s : ℝ} (h : HasDerivAt f₁ (f₂ s) s) :
    HasDerivAt (fun t => (a - t ^ 2) * f₁ t) ((a - s ^ 2) * f₂ s - 2 * s * f₁ s) s := by
  have h2 : HasDerivAt (fun t : ℝ => a - t ^ 2) (-(2 * s)) s := by
    have := (hasDerivAt_pow 2 s).const_sub a
    simpa using this
  exact (h2.mul h).congr_deriv (by ring)

/-- `dilSq` is `E*E`: `(s² f′)′ = s² f″ + 2s f′`. -/
theorem hasDerivAt_dilSq {f₁ f₂ : ℝ → ℝ} {s : ℝ} (h : HasDerivAt f₁ (f₂ s) s) :
    HasDerivAt (fun t => t ^ 2 * f₁ t) (s ^ 2 * f₂ s + 2 * s * f₁ s) s := by
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  exact (h2.mul h).congr_deriv (by ring)

/-- **The central-square split**: `L_{1,c} = 4 L_{¼,c/2} + 3 E*E`. -/
theorem slepOp_split (c : ℝ) (f f₁ f₂ : ℝ → ℝ) (s : ℝ) :
    slepOp 1 c f f₁ f₂ s = 4 * slepOp (1 / 4) (c / 2) f f₁ f₂ s + 3 * dilSq f₁ f₂ s := by
  unfold slepOp dilSq
  ring

/-- **Each rung splits**: `4 L_{¼,c/2} h + 3 E*E h = χ h` on `[−1, 1]` for `h = rung c k` at `χ = lev c k`. -/
theorem rung_split {c : ℝ} {k : ℕ} (h : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c k χ) {s : ℝ} (hs : s ∈ uIcc (-1 : ℝ) 1) :
    4 * slepOp (1 / 4) (c / 2) (rung c k) (rung₁ c k) (rung₂ c k) s + 3 * dilSq (rung₁ c k) (rung₂ c k) s
      = lev c k * rung c k s := by
  rw [← slepOp_split]
  have e := (Cvs.Prolate.EvenRungsByIndex.rung_spec h).2.2.2.1 s hs
  unfold slepOp
  linarith

/-- **The symbol split**: `(1 − s²)u² + s² = ((1 − 4s²)u² + s²) + 3s²u²`. -/
theorem symbol_split (s u : ℝ) :
    (1 - s ^ 2) * u ^ 2 + s ^ 2 = ((1 - 4 * s ^ 2) * u ^ 2 + s ^ 2) + 3 * s ^ 2 * u ^ 2 := by
  ring

/-- On the level-zero curve `u²(4y − 1) = y` of `4H′`, the rung symbol is `3y²/(4y − 1)`. -/
theorem symbol_on_tail {y v : ℝ} (hy : 1 / 4 < y) (hv : v * (4 * y - 1) = y) :
    (1 - y) * v + y = 3 * y ^ 2 / (4 * y - 1) := by
  have h : 4 * y - 1 ≠ 0 := by linarith
  rw [eq_div_iff h]
  linear_combination (1 - y) * hv

/-- **The lowest level on the leaked tail**: `3y²/(4y − 1) = ¾ + 3(2y − 1)²/(4(4y − 1))` for `y > ¼`. -/
theorem tail_level_eq {y : ℝ} (hy : 1 / 4 < y) :
    3 * y ^ 2 / (4 * y - 1) = 3 / 4 + 3 * (2 * y - 1) ^ 2 / (4 * (4 * y - 1)) := by
  have h : 4 * y - 1 ≠ 0 := by linarith
  have h4 : (4 : ℝ) * (4 * y - 1) ≠ 0 := by positivity
  rw [eq_comm, div_add_div _ _ (by norm_num : (4 : ℝ) ≠ 0) h4, div_eq_div_iff (by positivity) h]
  ring

/-- The leaked tail of `4H′ = 0` lies at rung level at least `¾`, with equality only at `y = ½`. -/
theorem three_fourths_le_tail_level {y : ℝ} (hy : 1 / 4 < y) : 3 / 4 ≤ 3 * y ^ 2 / (4 * y - 1) := by
  rw [tail_level_eq hy]
  have : 0 < 4 * (4 * y - 1) := by linarith
  have : 0 ≤ 3 * (2 * y - 1) ^ 2 / (4 * (4 * y - 1)) := by positivity
  linarith

/-- The tail level equals `¾` exactly at `y = ½`. -/
theorem tail_level_eq_three_fourths_iff {y : ℝ} (hy : 1 / 4 < y) :
    3 * y ^ 2 / (4 * y - 1) = 3 / 4 ↔ y = 1 / 2 := by
  rw [tail_level_eq hy]
  have hp : 0 < 4 * (4 * y - 1) := by linarith
  constructor
  · intro h
    have h0 : 3 * (2 * y - 1) ^ 2 / (4 * (4 * y - 1)) = 0 := by linarith
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · nlinarith [sq_nonneg (2 * y - 1)]
    · linarith
  · rintro rfl
    norm_num

/-- **The saddle equation** `3y² − 4Ty + T = 0` has a real root iff `T(4T − 3) ≥ 0`. -/
theorem exists_saddle_iff (T : ℝ) : (∃ y : ℝ, 3 * y ^ 2 - 4 * T * y + T = 0) ↔ 0 ≤ T * (4 * T - 3) := by
  constructor
  · rintro ⟨y, hy⟩
    nlinarith [sq_nonneg (3 * y - 2 * T)]
  · intro h
    refine ⟨(2 * T + √(T * (4 * T - 3))) / 3, ?_⟩
    have hs := Real.sq_sqrt h
    linear_combination hs / 3

/-- For a positive level `T`, the overlap saddle is real iff `T ≥ ¾`. -/
theorem exists_saddle_iff_of_pos {T : ℝ} (hT : 0 < T) :
    (∃ y : ℝ, 3 * y ^ 2 - 4 * T * y + T = 0) ↔ 3 / 4 ≤ T := by
  rw [exists_saddle_iff]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    nlinarith
  · intro h
    nlinarith

end Cvs.Prolate.RungOperatorCentralSquares

end
