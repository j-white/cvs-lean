import Mathlib
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungKatoTemple
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Prolate.HermiteTrialsSixEight
import Cvs.Prolate.Mellin.XiLawsRungFour
import Cvs.Prolate.RungEightKatoTemple
import Cvs.Prolate.SepticLevelComparison

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Ξ laws for the rung `h₈`, and `χ_n/c → 2n + 1`

For `c ≥ 1024`, `c − 1 ≤ χ₈ ≤ 17c` and `|χ₈ − 17c| ≤ 37` (from Cvs.Prolate.RungEightKatoTemple), so the relative laws of an earlier result and an earlier result hold
for the rung of index `4` with `K = κ = 17`, `D = 37`. A level with `|χ − (4j + 1)c| ≤ D` eventually has
`χ/c → 4j + 1`; in particular `χ₀/c → 1`, `χ₄/c → 9` and `χ₈/c → 17`.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Prolate.Mellin.XiLawsRungEight
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx lev rung)

/-- **The level `χ₈` in the window of the excited laws**: for `c ≥ 1024` the level of index `4` exists,
`c − 1 ≤ χ₈ ≤ 17c` and `|χ₈ − 17c| ≤ 37`. -/
theorem lev_four_bounds {c : ℝ} (hc : 1024 ≤ c) :
    (∃ χ, IsLevelIdx c 4 χ) ∧ c - 1 ≤ lev c 4 ∧ lev c 4 ≤ 17 * c ∧ |lev c 4 - 17 * c| ≤ 37 := by
  have hc0 : 0 < c := by linarith
  have hl := Cvs.Prolate.RungEightKatoTemple.abs_lev_four_sub_le (by linarith : (400 : ℝ) ≤ c)
  rw [Cvs.Prolate.HermiteTrialsSixEight.mu_four] at hl
  have h256 : 256 / c ≤ 1 / 4 := by rw [div_le_iff₀ hc0]; linarith
  have h256' : 0 ≤ 256 / c := by positivity
  obtain ⟨hl1, hl2⟩ := abs_le.mp hl
  refine ⟨Cvs.Prolate.SepticLevelComparison.exists_isLevelIdx_of_le_four (by linarith [Real.pi_lt_d2]) le_rfl,
    by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- **`χ/c → κ`** for a level with `|χ − κc| ≤ D` eventually. -/
theorem tendsto_div_of_abs_sub_le {χ : ℝ → ℝ} {κ D : ℝ} (h : ∀ᶠ c : ℝ in atTop, |χ c - κ * c| ≤ D) :
    Tendsto (fun c => χ c / c) atTop (𝓝 κ) := by
  have hD : Tendsto (fun c : ℝ => D / c) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hD
  filter_upwards [h, eventually_gt_atTop 0] with c hc hc0
  rw [Real.norm_eq_abs, show χ c / c - κ = (χ c - κ * c) / c by field_simp, abs_div, abs_of_pos hc0]
  exact div_le_div_of_nonneg_right hc hc0.le

/-- **`χ₀/c → 1`**. -/
theorem tendsto_lev_zero_div : Tendsto (fun c => lev c 0 / c) atTop (𝓝 1) := by
  refine tendsto_div_of_abs_sub_le (D := 1) ?_
  filter_upwards [eventually_ge_atTop 200] with c hc
  have hl := Cvs.Prolate.EvenRungKatoTemple.abs_lev_zero_sub_le hc
  rw [Cvs.Prolate.EvenRungDavisKahan.mu_zero] at hl
  have h1 : 1 / c ≤ 1 / 4 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h0 : 0 ≤ 1 / c := by have : 0 < c := by linarith
                            positivity
  obtain ⟨a, b⟩ := abs_le.mp hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **`χ₄/c → 9`**. -/
theorem tendsto_lev_two_div : Tendsto (fun c => lev c 2 / c) atTop (𝓝 9) :=
  tendsto_div_of_abs_sub_le (D := 11) (by
    filter_upwards [eventually_ge_atTop 256] with c hc
    exact (Cvs.Prolate.Mellin.XiLawsRungFour.lev_two_bounds hc).2.2.2)

/-- **`χ₈/c → 17`**. -/
theorem tendsto_lev_four_div : Tendsto (fun c => lev c 4 / c) atTop (𝓝 17) :=
  tendsto_div_of_abs_sub_le (D := 37) (by
    filter_upwards [eventually_ge_atTop 1024] with c hc
    exact (lev_four_bounds hc).2.2.2)

end Cvs.Prolate.Mellin.XiLawsRungEight
