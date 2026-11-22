import Mathlib
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Prolate.HermiteTrialsSixEight

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The level of index three lies within `37/2` of `μ₆ = 13c − 87/4`

The `F₆` trial gives an even level `χ` with `|χ − μ₆| ≤ 37/2` for `c ≥ 40`. Since `lev c 2 ≤ 9c − 43/4 + 1033/100`, its
index is at least three, so `lev c 3 ≤ 13c − 13/4`; since every level of index at least four lies at or above
`15c − 241/2`, for `c ≥ 59` its index is exactly three.
-/

noncomputable section

open Real

namespace Cvs.Prolate.LevelThreeNearMuSix
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx lev lev_spec lev_eq)
open Cvs.Prolate.HermiteTrialResiduals (mu kap2)

/-- **A level within `37/2` of `μ₆`** for `c ≥ 40`. -/
theorem exists_abs_sub_mu_three_le {c : ℝ} (hc : 40 ≤ c) :
    ∃ k χ, IsLevelIdx c k χ ∧ (χ - mu c 3) ^ 2 ≤ 1001 / 1000 * kap2 3 ∧
      |χ - (13 * c - 87 / 4)| ≤ 37 / 2 := by
  obtain ⟨k, χ, hχ, hle⟩ := Cvs.Prolate.HermiteTrialsSixEight.exists_sq_sub_mu_le hc (m := 3) (by norm_num)
  refine ⟨k, χ, hχ, hle, ?_⟩
  rw [Cvs.Prolate.HermiteTrialsSixEight.kap2_three_four.1, Cvs.Prolate.HermiteTrialsSixEight.mu_three] at hle
  exact abs_le_of_sq_le_sq' (hle.trans (by norm_num)) (by norm_num) |> abs_le.2

/-- `lev c 2 ≤ 9c − 43/4 + 1033/100` for `c ≥ 31`. -/
theorem lev_two_le {c : ℝ} (hc : 31 ≤ c) : lev c 2 ≤ 9 * c - 43 / 4 + 1033 / 100 := by
  have h := Cvs.Prolate.EvenRungDavisKahan.sq_lev_two_sub_le hc
  rw [Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.2, Cvs.Prolate.EvenRungDavisKahan.mu_two] at h
  have := abs_le_of_sq_le_sq' (h.trans (by norm_num : _ ≤ (1033 / 100 : ℝ) ^ 2)) (by norm_num)
  linarith [this.2]

/-- **`lev c 3 ≤ 13c − 13/4`** for `c ≥ 40`. -/
theorem lev_three_le {c : ℝ} (hc : 40 ≤ c) : lev c 3 ≤ 13 * c - 13 / 4 := by
  obtain ⟨j, χ, hχ, -, hb⟩ := exists_abs_sub_mu_three_le hc
  have hb := abs_le.1 hb
  rcases Nat.lt_or_ge j 3 with hj | hj
  · exfalso
    have h2 : χ ≤ lev c 2 :=
      hχ.le (lev_spec (Cvs.Prolate.EvenRungDavisKahan.exists_isLevelIdx_of_le_three (by linarith) (by norm_num))) (by omega)
    linarith [lev_two_le (c := c) (by linarith)]
  · rw [← lev_eq hχ] at hb
    exact (Cvs.Prolate.EvenRungsByIndex.lev_le ⟨χ, hχ⟩ hj).trans (by linarith)

end Cvs.Prolate.LevelThreeNearMuSix
