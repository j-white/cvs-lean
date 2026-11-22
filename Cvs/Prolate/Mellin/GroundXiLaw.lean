import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.BootstrapLargeBandwidth
import Cvs.Prolate.Mellin.FrozenForcingLineSum
import Cvs.Prolate.Mellin.GroundRatioLineModulus
import Cvs.Prolate.Mellin.GroundRatioStepErrors
import Cvs.Prolate.Mellin.GroundXiLawModulus
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Prolate.Mellin.NearRegionBootstrap
import Cvs.Prolate.Mellin.WkbPhaseLineStart

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Ξ law for the ground prolate

For every `0 < ε ≤ 1/16` and `η > 0`, for all large `c`, uniformly in `|z| ≤ (2 − ε)c` with `sin θ = z/(2c)`:
`|log‖P₀(½ + iz)‖ − log‖P₀(½)‖ − (c(θ sin θ + cos θ − 1) − ½ log cos θ − ¼ log((1 + cos θ)/2))| ≤ η`.
-/

noncomputable section

open Filter Topology Complex

namespace Cvs.Prolate.Mellin.GroundXiLaw
open Cvs.ZeroCounting

open Cvs.Prolate.Mellin.LawRatioRecurrence Cvs.Prolate.Mellin.GroundRatioStepErrors Cvs.Prolate.Mellin.BootstrapLargeBandwidth Cvs.Prolate.Mellin.FrozenForcingLineSum Cvs.Prolate.Mellin.GroundRatioLineModulus Cvs.Prolate.Mellin.WkbPhaseLineStart Cvs.Prolate.Mellin.GroundXiLawModulus

variable {ε : ℝ}

theorem tendsto_inv : Tendsto (fun c : ℝ => 1 / c) atTop (𝓝 0) := by
  simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)

theorem tendsto_inv_sq : Tendsto (fun c : ℝ => 1 / c ^ 2) atTop (𝓝 0) := by
  have := tendsto_inv.mul tendsto_inv
  simp only [mul_zero] at this
  refine this.congr fun c => ?_
  ring

theorem tendsto_log_term : Tendsto (fun c : ℝ => (1 + Real.log (1 + c / 2)) / (2 * c)) atTop (𝓝 0) := by
  have hl := (Real.isLittleO_log_id_atTop).tendsto_div_nhds_zero
  have h1 : Tendsto (fun c : ℝ => 1 / (2 * c)) atTop (𝓝 0) := by
    have := tendsto_inv.const_mul (1 / 2)
    simp only [mul_zero] at this
    exact this.congr fun c => by ring
  have hb := h1.add (hl.const_mul (1 / 2))
  rw [mul_zero, add_zero] at hb
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_gt_atTop 0] with c hc
    have : 0 ≤ Real.log (1 + c / 2) := Real.log_nonneg (by linarith [show 0 ≤ c / 2 by positivity])
    positivity
  · filter_upwards [eventually_ge_atTop 2] with c hc
    have hc0 : 0 < c := by linarith
    have hlog : Real.log (1 + c / 2) ≤ Real.log c := Real.log_le_log (by positivity) (by linarith)
    calc (1 + Real.log (1 + c / 2)) / (2 * c) ≤ (1 + Real.log c) / (2 * c) := by gcongr
      _ = 1 / (2 * c) + 1 / 2 * (Real.log c / id c) := by simp only [id]; field_simp

theorem tendsto_G1 (hε : 0 < ε) : Tendsto (G1 ε) atTop (𝓝 0) := by
  set a := Real.sqrt (3 * ε)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have e : ∀ᶠ c : ℝ in atTop, (1 / 2 + 1 / a) * (1 / c) + (1 / (4 * a) + 1 / (2 * a ^ 2) + 1 / a ^ 3) * (1 / c ^ 2)
      = G1 ε c := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    unfold G1; field_simp; ring
  refine Tendsto.congr' e ?_
  have := (tendsto_inv.const_mul (1 / 2 + 1 / a)).add (tendsto_inv_sq.const_mul (1 / (4 * a) + 1 / (2 * a ^ 2) + 1 / a ^ 3))
  simpa using this

theorem tendsto_gam (hε : 0 < ε) : Tendsto (gam ε) atTop (𝓝 0) := by
  have e : ∀ᶠ c : ℝ in atTop, (80 / (ε / 4) ^ 5 + 1 / (2 * ε)) * (1 / c) + 2 * G1 ε c = gam ε c := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    unfold gam; field_simp; ring
  refine Tendsto.congr' e ?_
  have := (tendsto_inv.const_mul (80 / (ε / 4) ^ 5 + 1 / (2 * ε))).add ((tendsto_G1 hε).const_mul 2)
  simpa using this

theorem tendsto_E2 (hε : 0 < ε) : Tendsto (E2 ε) atTop (𝓝 0) := by
  have e : ∀ c : ℝ, ((10848 / ε) ^ 2 + 15000000000 / ε ^ 3) * (1 / c)
      + 468 / Real.sqrt ε * ((1 + Real.log (1 + c / 2)) / (2 * c)) = E2 ε c := fun c => by
    unfold E2; ring
  refine Tendsto.congr e ?_
  have := (tendsto_inv.const_mul ((10848 / ε) ^ 2 + 15000000000 / ε ^ 3)).add
    (tendsto_log_term.const_mul (468 / Real.sqrt ε))
  simpa using this

theorem tendsto_Etot (hε : 0 < ε) : Tendsto (Etot ε) atTop (𝓝 0) := by
  have e : ∀ c : ℝ, E1 ε c + E2 ε c + 42 * (1 + 2 / Real.sqrt (3 * ε)) / Real.sqrt (3 * ε) * (1 / c)
      + 160 / (ε / 4) ^ 5 * ((1 + Real.log (1 + c / 2)) / (2 * c)) = Etot ε c := fun c => by
    unfold Etot; ring
  refine Tendsto.congr e ?_
  have := (((tendsto_E1 hε).add (tendsto_E2 hε)).add
    (tendsto_inv.const_mul (42 * (1 + 2 / Real.sqrt (3 * ε)) / Real.sqrt (3 * ε)))).add
    (tendsto_log_term.const_mul (160 / (ε / 4) ^ 5))
  simpa using this

/-- The largeness conditions hold for all large `c`. -/
theorem eventually_large (hε : 0 < ε) (hε16 : ε ≤ 1 / 16) : ∀ᶠ c : ℝ in atTop, Large ε c := by
  have hcond := eventually_conditions hε
  have hγ := (tendsto_gam hε).eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hη := ((tendsto_gam hε).const_mul 2 |>.add (tendsto_inv.const_mul 2)).eventually
    (ge_mem_nhds (show 2 * (0 : ℝ) + 2 * 0 < ε / 4 by linarith))
  filter_upwards [hcond, hγ, hη, eventually_ge_atTop (64 / ε ^ 2), eventually_ge_atTop 7500,
    eventually_ge_atTop (100000 / ε ^ 2)] with c h1 h2 h3 h4 h5 h6
  refine ⟨hε, hε16, h4, h5, h6, h1.1, h1.2, by linarith, ?_⟩
  have : 2 * (1 / c) = 2 / c := by ring
  linarith

/-- **The Ξ law for the ground prolate (modulus).** -/
theorem xi_law (hε : 0 < ε) (hε16 : ε ≤ 1 / 16) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop, ∀ z : ℝ, |z| ≤ (2 - ε) * c →
      |Real.log ‖lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) ((1 / 2 : ℂ) + I * z)‖
        - Real.log ‖lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (1 / 2)‖ - law c z| ≤ η := by
  have herr : Tendsto (fun c => 2 * Etot ε c + 3 * (2 * gam ε c + 2 / c) / ε + 6 * G1 ε c) atTop (𝓝 0) := by
    have := (((tendsto_Etot hε).const_mul 2).add
      ((((tendsto_gam hε).const_mul 2).add (tendsto_inv.const_mul 2)).const_mul 3 |>.div_const ε)).add
      ((tendsto_G1 hε).const_mul 6)
    simp only [mul_zero, add_zero, zero_div] at this
    exact this.congr fun c => by ring
  filter_upwards [eventually_large hε hε16, herr.eventually (ge_mem_nhds hη)] with c hL hb z hz
  exact (xi_law_bound hL hz).trans hb

end Cvs.Prolate.Mellin.GroundXiLaw
