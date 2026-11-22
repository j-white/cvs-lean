import Mathlib
import Cvs.L2a.FullSpanIndexFloor
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RegularSolutionEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung of index `k` is `rung(1)` times the regular solution at its level

On `(−1, 1]` the normalised rung `Cvs.Prolate.EvenRungsByIndex.rung c k` equals `rung c k 1 · regSol (sqC c) (lev c k)` with
`rung c k 1 ≠ 0`, so it has the same zeros there. The top-rung counts of Cvs.Prolate.TopRungZeroSplitHalf (`top_total`, `top_half`,
`top_kstar`) therefore hold for `rung (2πx) (2(x − 1))` itself.
-/

noncomputable section

namespace Cvs.Prolate.RungEqRegularSolution

open Real Set
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)
open Cvs.Prolate.EvenRungsByIndex (rung lev IsLevelIdx)

/-! ### Zeros of a nonzero multiple -/

/-! ### The rung and the regular solution -/

/-- **The rung is a nonzero multiple of the regular solution**: on `(−1, 1]`,
`rung c k = rung c k 1 · regSol (sqC c) (lev c k)`, and `rung c k 1 ≠ 0`. -/
theorem rung_eq_mul_regSol {c : ℝ} {k : ℕ} (hex : ∃ χ, IsLevelIdx c k χ) :
    rung c k 1 ≠ 0 ∧ ∀ s ∈ Ioc (-1 : ℝ) 1, rung c k s = rung c k 1 * regSol (sqC c) (lev c k) s := by
  obtain ⟨hg, hg₁, -, hang, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec hex
  exact ⟨Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero hex, Cvs.Prolate.RegularSolutionEdge.angular_eq_mul_regSol hg hg₁ hang⟩

/-! ### The top rung -/

/-- The level of index `2(x − 1)` exists at `c = 2πx ≥ 80`, `x ≥ 1`. -/
theorem exists_top {x : ℕ} (hx : 80 ≤ 2 * π * x) (hx1 : 1 ≤ x) :
    ∃ χ, IsLevelIdx (2 * π * x) (2 * (x - 1)) χ :=
  (Cvs.L2a.FullSpanIndexFloor.full_index x hx (j := x - 1) (by omega)).1

/-- The scale `80 ≤ 2πx` from `x ≥ 31`. -/
theorem scale_of_31 {x : ℕ} (hx : 31 ≤ x) : 80 ≤ 2 * π * x := by
  have hpi1 := Real.pi_gt_d2
  have hx' : (31 : ℝ) ≤ x := by exact_mod_cast hx
  nlinarith

end Cvs.Prolate.RungEqRegularSolution
