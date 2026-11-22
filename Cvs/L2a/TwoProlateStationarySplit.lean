import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.StationaryCrossPairSplit
import Cvs.L2a.TwoProlateCrossBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The three-way stationary split for modes of two prolates

`StationaryCrossPairSplit`'s split with the partner mode `r` carrying its own `χ'`: `StationaryCrossPairSplit`'s generic telescoping bounds with `TwoProlateCrossBound`'s
separated numerators.
-/

namespace Cvs.L2a.TwoProlateStationarySplit

open intervalIntegral Real Set Cvs.L2a.NonresonantCrossIntegral Cvs.L2a.StationaryCrossPairSplit Cvs.L2a.TwoProlateCrossBound

variable {c χ χ' m r : ℝ}

theorem hasDerivAt_A2 (hm : m ≠ 0) (hr : r ≠ 0) {τ : ℝ} (hD : Dmr2 c χ χ' m r τ ≠ 0) :
    HasDerivAt (fun τ => 1 * pm m τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ' r τ))
      ((2 * τ * Dmr2 c χ χ' m r τ - pm m τ * dDmr2 c χ χ' m r τ) / Dmr2 c χ χ' m r τ ^ 2) τ := by
  have := (hasDerivAt_pm hm τ).div (hasDerivAt_Dmr2 (c := c) (χ := χ) (χ' := χ') hm hr τ) hD
  have e : (fun τ => 1 * pm m τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ' r τ)) = pm m / Dmr2 c χ χ' m r := by
    funext τ; simp [Dmr2]
  rw [e]; exact this

theorem hasDerivAt_B2 (hm : m ≠ 0) (hr : r ≠ 0) {τ : ℝ} (hD : Dmr2 c χ χ' m r τ ≠ 0) :
    HasDerivAt (fun τ => 1 * pm r τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ' r τ))
      ((2 * τ * Dmr2 c χ χ' m r τ - pm r τ * dDmr2 c χ χ' m r τ) / Dmr2 c χ χ' m r τ ^ 2) τ := by
  have := (hasDerivAt_pm hr τ).div (hasDerivAt_Dmr2 (c := c) (χ := χ) (χ' := χ') hm hr τ) hD
  have e : (fun τ => 1 * pm r τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ' r τ)) = pm r / Dmr2 c χ χ' m r := by
    funext τ; simp [Dmr2]
  rw [e]; exact this

theorem numA2_nonpos (hr : 0 < r) (hrm : r < m) (hχ : χ < c ^ 2) {τ : ℝ} (hτ : 0 ≤ τ) :
    2 * τ * Dmr2 c χ χ' m r τ - pm m τ * dDmr2 c χ χ' m r τ ≤ 0 := by
  have hm : 0 < m := hr.trans hrm
  rw [numA2_eq hm.ne' hr.ne']
  have : 0 ≤ (m ^ 2 - r ^ 2) := by nlinarith
  have : 0 ≤ (c ^ 2 - χ) / (m ^ 2 * r ^ 2) := div_nonneg (by linarith) (by positivity)
  have : 0 ≤ (m ^ 2 - r ^ 2) * (2 * τ) * (c ^ 2 * (τ ^ 2 - 1 / m ^ 2) ^ 2 + (c ^ 2 - χ) / (m ^ 2 * r ^ 2)) := by
    positivity
  linarith

theorem numB2_nonpos (hr : 0 < r) (hrm : r < m) (hχ' : χ' < c ^ 2) {τ : ℝ} (hτ : 0 ≤ τ) :
    2 * τ * Dmr2 c χ χ' m r τ - pm r τ * dDmr2 c χ χ' m r τ ≤ 0 := by
  have hm : 0 < m := hr.trans hrm
  rw [numB2_eq hm.ne' hr.ne']
  have : 0 ≤ (m ^ 2 - r ^ 2) := by nlinarith
  have : 0 ≤ (c ^ 2 - χ') / (m ^ 2 * r ^ 2) := div_nonneg (by linarith) (by positivity)
  have : 0 ≤ (m ^ 2 - r ^ 2) * (2 * τ) * (c ^ 2 * (τ ^ 2 - 1 / r ^ 2) ^ 2 + (c ^ 2 - χ') / (m ^ 2 * r ^ 2)) := by
    positivity
  linarith

/-- **The stationary cross pair of two prolates, split three ways.** For the modes `m > r > 0`, `1 < ra`,
`a ≤ t_l ≤ t_r ≤ b`, `D < 0` on `[a, t_l]`, `D > 0` on `[t_r, b]`, `χ, χ' < c²`:
`|∫_a^b f₁f₂| ≤ 2(p_m M_z + p_r M_v)/|D| at t_l + (t_r − t_l) F₁F₂ + 2(p_m M_z' + p_r M_v')/D at t_r`. -/
theorem prolate_stationary2_le {f₁ u₁ f₂ u₂ : ℝ → ℝ} {a tl tr b MzL MvL MzR MvR F₁ F₂ : ℝ}
    (hr : 0 < r) (hrm : r < m) (hra : 1 < r * a) (hχ : χ < c ^ 2) (hχ' : χ' < c ^ 2)
    (hal : a ≤ tl) (hlr : tl ≤ tr) (hrb : tr ≤ b)
    (hDL : ∀ τ ∈ Icc a tl, Dmr2 c χ χ' m r τ < 0) (hDR : ∀ τ ∈ Icc tr b, 0 < Dmr2 c χ χ' m r τ)
    (hf₁ : ∀ τ ∈ Icc a b, HasDerivAt f₁ (u₁ τ / pm m τ) τ)
    (hu₁ : ∀ τ ∈ Icc a b, HasDerivAt u₁ (-(qm c χ m τ * f₁ τ)) τ)
    (hf₂ : ∀ τ ∈ Icc a b, HasDerivAt f₂ (u₂ τ / pm r τ) τ)
    (hu₂ : ∀ τ ∈ Icc a b, HasDerivAt u₂ (-(qm c χ' r τ * f₂ τ)) τ)
    (hZL : ∀ τ ∈ Icc a tl, |f₁ τ * u₂ τ| ≤ MzL) (hVL : ∀ τ ∈ Icc a tl, |u₁ τ * f₂ τ| ≤ MvL)
    (hZR : ∀ τ ∈ Icc tr b, |f₁ τ * u₂ τ| ≤ MzR) (hVR : ∀ τ ∈ Icc tr b, |u₁ τ * f₂ τ| ≤ MvR)
    (hF₁ : ∀ τ ∈ Icc tl tr, |f₁ τ| ≤ F₁) (hF₂ : ∀ τ ∈ Icc tl tr, |f₂ τ| ≤ F₂) :
    |∫ τ in a..b, f₁ τ * f₂ τ|
      ≤ 2 * (-(pm m tl / Dmr2 c χ χ' m r tl) * MzL + -(pm r tl / Dmr2 c χ χ' m r tl) * MvL)
        + (tr - tl) * (F₁ * F₂)
        + 2 * (pm m tr * MzR + pm r tr * MvR) / Dmr2 c χ χ' m r tr := by
  have hm : 0 < m := hr.trans hrm
  have ha0 : 0 < a := by by_contra h; push Not at h; nlinarith
  have hpos : ∀ τ, a ≤ τ → 0 < pm r τ ∧ 0 < pm m τ := fun τ hτ => by
    have h1 : 1 < r * τ := lt_of_lt_of_le hra (by nlinarith)
    have h2 : 1 < m * τ := lt_of_lt_of_le h1 (by nlinarith)
    unfold pm; constructor <;> apply div_pos <;> nlinarith
  have subL : Icc a tl ⊆ Icc a b := Icc_subset_Icc_right (hlr.trans hrb)
  have subM : Icc tl tr ⊆ Icc a b := Icc_subset_Icc hal hrb
  have subR : Icc tr b ⊆ Icc a b := Icc_subset_Icc_left (hal.trans hlr)
  have cont : ∀ f : ℝ → ℝ, (∀ τ ∈ Icc a b, DifferentiableAt ℝ f τ) → ContinuousOn f (Icc a b) :=
    fun f hf τ hτ => (hf τ hτ).continuousAt.continuousWithinAt
  have hf₁c := cont f₁ fun τ hτ => (hf₁ τ hτ).differentiableAt
  have hf₂c := cont f₂ fun τ hτ => (hf₂ τ hτ).differentiableAt
  have hDc : ContinuousOn (Dmr2 c χ χ' m r) univ := by unfold Dmr2 pm qm; fun_prop
  have hdDc : ContinuousOn (dDmr2 c χ χ' m r) univ := by unfold dDmr2 pm qm; fun_prop
  have hpmc : ∀ k : ℝ, ContinuousOn (pm k) univ := fun k => by unfold pm; fun_prop
  have hqmc : ∀ (x k : ℝ), ContinuousOn (qm c x k) univ := fun x k => by unfold qm; fun_prop
  have hDmr : ∀ τ, Dmr2 c χ χ' m r τ = pm r τ * qm c χ m τ - pm m τ * qm c χ' r τ := fun _ => rfl
  -- left piece
  have left := cross_abs_le_neg (σ := fun _ => 1) (Mz := MzL) (Mv := MvL) hal
    (fun τ hτ => (hpos τ hτ.1).2.ne') (fun τ hτ => (hpos τ hτ.1).1.ne')
    (fun τ hτ => by rw [← hDmr]; exact (hDL τ hτ).ne)
    (fun τ hτ => hf₁ τ (subL hτ)) (fun τ hτ => hu₁ τ (subL hτ))
    (fun τ hτ => hf₂ τ (subL hτ)) (fun τ hτ => hu₂ τ (subL hτ))
    (fun τ hτ => hasDerivAt_A2 hm.ne' hr.ne' (hDL τ hτ).ne)
    (fun τ hτ => hasDerivAt_B2 hm.ne' hr.ne' (hDL τ hτ).ne)
    (((continuousOn_const.mul continuousOn_id).mul (hDc.mono (subset_univ _))).sub
      (((hpmc m).mono (subset_univ _)).mul (hdDc.mono (subset_univ _))) |>.div
      ((hDc.mono (subset_univ _)).pow 2) fun τ hτ => pow_ne_zero 2 (hDL τ hτ).ne)
    (((continuousOn_const.mul continuousOn_id).mul (hDc.mono (subset_univ _))).sub
      (((hpmc r).mono (subset_univ _)).mul (hdDc.mono (subset_univ _))) |>.div
      ((hDc.mono (subset_univ _)).pow 2) fun τ hτ => pow_ne_zero 2 (hDL τ hτ).ne)
    (continuousOn_const.mul ((hf₁c.mono subL).mul (hf₂c.mono subL)))
    ((hqmc χ m).mono (subset_univ _)) ((hqmc χ' r).mono (subset_univ _))
    ((hpmc m).mono (subset_univ _)) ((hpmc r).mono (subset_univ _))
    (fun τ hτ => div_nonpos_of_nonpos_of_nonneg (numA2_nonpos hr hrm hχ (le_trans ha0.le hτ.1)) (sq_nonneg _))
    (fun τ hτ => div_nonpos_of_nonpos_of_nonneg (numB2_nonpos hr hrm hχ' (le_trans ha0.le hτ.1)) (sq_nonneg _))
    (by
      have := hDL a (left_mem_Icc.mpr hal); have := (hpos a le_rfl).2
      rw [one_mul, ← hDmr]; exact div_nonpos_of_nonneg_of_nonpos this.le (hDL a (left_mem_Icc.mpr hal)).le)
    (by
      have := (hpos a le_rfl).1
      rw [one_mul, ← hDmr]; exact div_nonpos_of_nonneg_of_nonpos this.le (hDL a (left_mem_Icc.mpr hal)).le)
    hZL hVL
  simp only [one_mul, ← hDmr] at left
  -- right piece
  have right := prolate_cross2_le hrb hr hrm (lt_of_lt_of_le hra (by nlinarith [hal.trans hlr])) hχ hχ' hDR
    (fun τ hτ => hf₁ τ (subR hτ)) (fun τ hτ => hu₁ τ (subR hτ))
    (fun τ hτ => hf₂ τ (subR hτ)) (fun τ hτ => hu₂ τ (subR hτ)) hZR hVR
  -- middle
  have mid := window_le hlr (hf₁c.mono subM) (hf₂c.mono subM) hF₁ hF₂
  -- additivity
  have i1 : IntervalIntegrable (fun τ => f₁ τ * f₂ τ) MeasureTheory.volume a tl :=
    ((hf₁c.mul hf₂c).mono subL).intervalIntegrable_of_Icc hal
  have i2 : IntervalIntegrable (fun τ => f₁ τ * f₂ τ) MeasureTheory.volume tl tr :=
    ((hf₁c.mul hf₂c).mono subM).intervalIntegrable_of_Icc hlr
  have i3 : IntervalIntegrable (fun τ => f₁ τ * f₂ τ) MeasureTheory.volume tr b :=
    ((hf₁c.mul hf₂c).mono subR).intervalIntegrable_of_Icc hrb
  rw [← intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  calc |(∫ τ in a..tl, f₁ τ * f₂ τ) + (∫ τ in tl..tr, f₁ τ * f₂ τ) + ∫ τ in tr..b, f₁ τ * f₂ τ|
      ≤ |∫ τ in a..tl, f₁ τ * f₂ τ| + |∫ τ in tl..tr, f₁ τ * f₂ τ| + |∫ τ in tr..b, f₁ τ * f₂ τ| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ _ := by linarith

end Cvs.L2a.TwoProlateStationarySplit
