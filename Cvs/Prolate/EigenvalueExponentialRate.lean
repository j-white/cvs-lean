import Mathlib
import Cvs.Approximant.SingletonRegularisationColumn
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.GroundRungEndpoint
import Cvs.Prolate.LowRungEndpointSmall
import Cvs.Prolate.ModeEnergyArcsineLaw
import Cvs.Prolate.RungEndpointMass

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `λ_j → 1` along `c = 2πx`, with an exponential rate

For `j = 0, 2, 4`, eventually in `x : ℕ`, `1 − λ_j(2πx) ≤ 200 c³ e^{−c/16}` at `c = 2πx`; hence `λ_j(2πx) → 1`.
-/

noncomputable section

open Real Set Filter Topology

namespace Cvs.Prolate.EigenvalueExponentialRate
open Cvs.ZeroCounting

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx rung lamR muR lev rung_spec psi_rung)

/-- `c = 2πx → ∞` along `ℕ`. -/
theorem tendsto_scale : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)

/-- **`1 − λ_j ≤ 200 c³ e^{−c/16}`** at `c = 2πx`, eventually in `x : ℕ`, `j = 0, 2, 4`. -/
theorem eventually_one_sub_lamR_le {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) :
    ∀ᶠ x : ℕ in atTop,
      1 - lamR (2 * π * x) j ≤ 200 * (2 * π * x) ^ 3 * exp (-(2 * π * x / 16)) := by
  obtain ⟨K, hK⟩ := Cvs.Prolate.ModeEnergyArcsineLaw.hlev_even hj
  have hKc : ∀ᶠ c : ℝ in atTop, K * c ≤ 2 / 5 * c ^ 2 := by
    filter_upwards [eventually_ge_atTop (max (5 / 2 * K) 0)] with c hc
    have h1 : 5 / 2 * K ≤ c := (le_max_left _ _).trans hc
    have h2 : 0 ≤ c := (le_max_right _ _).trans hc
    nlinarith
  have hD := Cvs.Prolate.RungEndpointMass.abs_rung_one_sq_sub_le hj (η := 1 / 2) (by norm_num)
  filter_upwards [tendsto_scale.eventually (hK.and (hD.and (hKc.and (eventually_ge_atTop 100)))),
    eventually_gt_atTop 2] with x ⟨⟨hlev, hl0, hlK⟩, hDx, hKx, h100⟩ hx2
  set c : ℝ := 2 * π * x with hcdef
  have hc0 : 0 < c := by linarith
  have hhalf : 1 / 2 ≤ lamR c j := by
    obtain ⟨i, rfl, hi⟩ : ∃ i, j = 2 * i ∧ i < x := by
      rcases hj with rfl | rfl | rfl
      exacts [⟨0, rfl, by omega⟩, ⟨1, rfl, by omega⟩, ⟨2, rfl, by omega⟩]
    exact Cvs.L2a.WindowChainInputsProlate.half_le_lamR (by linarith) hi
  have hev : Even j := by rcases hj with rfl | rfl | rfl <;> decide
  have hμ0 := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc0 hlev hev
  have hlam : lamR c j = muR c j ^ 2 * (c / (2 * π)) := by
    rw [lamR, mul_pow, sq_sqrt (by positivity)]
  have hμc : 1 / c ≤ muR c j := by
    by_contra h
    push Not at h
    have hsq : muR c j ^ 2 < (1 / c) ^ 2 := pow_lt_pow_left₀ h hμ0.le two_ne_zero
    have hlt : lamR c j < (1 / c) ^ 2 * (c / (2 * π)) := by
      rw [hlam]; exact mul_lt_mul_of_pos_right hsq (by positivity)
    have he : (1 / c) ^ 2 * (c / (2 * π)) = 1 / (2 * π * c) := by field_simp
    rw [he] at hlt
    have : 1 / (2 * π * c) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pi_gt_three]
    linarith
  obtain ⟨hg, hg₁, hg₂c, hang, heven, hnorm⟩ := rung_spec hlev
  have hend := Cvs.Prolate.LowRungEndpointSmall.endpoint_sq_le hg hg₁ hg₂c hang heven hnorm (psi_rung hlev) h100 hl0
    (hlK.trans hKx) hμc
  have hlow := (abs_le.1 hDx).1
  have hD2 : c * (1 - lamR c j) ≤ c * (200 * c ^ 3 * exp (-(c / 16))) := by
    have : c * (200 * c ^ 3 * exp (-(c / 16))) = 2 * (100 * c ^ 4 * exp (-(c / 16))) := by ring
    rw [this]
    linarith
  have e : -(c / 16) = -(2 * π * x / 16) := by rw [hcdef]
  rw [← e]
  exact le_of_mul_le_mul_left hD2 hc0

/-- `200 c³ e^{−c/16} → 0`. -/
theorem tendsto_bound : Tendsto (fun c : ℝ => 200 * c ^ 3 * exp (-(c / 16))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 16))
  have h2 := h.const_mul (200 * 16 ^ 3)
  rw [mul_zero] at h2
  refine h2.congr fun c => ?_
  simp only [Function.comp, id]
  ring

/-- **`1 − λ_j(2πx) → 0`** along `ℕ`, `j = 0, 2, 4`. -/
theorem tendsto_one_sub_lamR_nat {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) :
    Tendsto (fun x : ℕ => 1 - lamR (2 * π * x) j) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := Cvs.Prolate.ModeEnergyArcsineLaw.hlev_even hj
  refine squeeze_zero' ?_ (eventually_one_sub_lamR_le hj) (tendsto_bound.comp tendsto_scale)
  filter_upwards [tendsto_scale.eventually (hK.and (eventually_gt_atTop 0))] with x ⟨⟨hlev, _, _⟩, hc⟩
  exact sub_nonneg.2 (Cvs.Prolate.GroundRungEndpoint.lamR_le_one hc hlev)

/-- **`λ_j(2πx) → 1`** along `ℕ`, `j = 0, 2, 4`. -/
theorem tendsto_lamR_nat {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) :
    Tendsto (fun x : ℕ => lamR (2 * π * x) j) atTop (𝓝 1) := by
  have h := (tendsto_one_sub_lamR_nat hj).const_sub 1
  rw [sub_zero] at h
  exact h.congr fun x => by ring

end Cvs.Prolate.EigenvalueExponentialRate
