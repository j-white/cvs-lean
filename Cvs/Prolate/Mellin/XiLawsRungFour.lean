import Mathlib
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungKatoTemple
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Ξ laws for the rung `h₄`

For `c ≥ 256`, `c − 1 ≤ χ₄ ≤ 9c` and `|χ₄ − 9c| ≤ 11` (from `|χ₄ − (9c − 43/4)| ≤ 64/c`), so the relative laws of
an earlier result (below `2c`) and an earlier result (past `2c`) hold for the rung of index `2` with `K = κ = 9`, `D = 11`, unconditionally.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Prolate.Mellin.XiLawsRungFour
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx lev rung)

/-- **The level `χ₄` in the window of the excited laws**: for `c ≥ 256` the level of index `2` exists,
`c − 1 ≤ χ₄ ≤ 9c` and `|χ₄ − 9c| ≤ 11`. -/
theorem lev_two_bounds {c : ℝ} (hc : 256 ≤ c) :
    (∃ χ, IsLevelIdx c 2 χ) ∧ c - 1 ≤ lev c 2 ∧ lev c 2 ≤ 9 * c ∧ |lev c 2 - 9 * c| ≤ 11 := by
  have hc0 : 0 < c := by linarith
  have hl := Cvs.Prolate.EvenRungKatoTemple.abs_lev_two_sub_le (by linarith : (200 : ℝ) ≤ c)
  rw [Cvs.Prolate.EvenRungDavisKahan.mu_two] at hl
  have h64 : 64 / c ≤ 1 / 4 := by rw [div_le_iff₀ hc0]; linarith
  have h64' : 0 ≤ 64 / c := by positivity
  obtain ⟨hl1, hl2⟩ := abs_le.mp hl
  refine ⟨Cvs.Prolate.EvenRungDavisKahan.exists_isLevelIdx_of_le_three (by linarith) (by norm_num),
    by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩

end Cvs.Prolate.Mellin.XiLawsRungFour
