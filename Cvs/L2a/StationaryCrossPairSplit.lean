import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.Prolate.LiouvilleGreen.SturmProductByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A stationary cross pair, split three ways

Before the stationary point `D < 0`, and `A = p₁/D`, `B = p₂/D` are negative and decreasing, so Cvs.Prolate.LiouvilleGreen.SturmProductByParts telescopes to
`2(|A(t)| M_z + |B(t)| M_v)` at the right end; across a window `[t_l, t_r]` the product is at most
`(t_r − t_l) sup|f₁| sup|f₂|`; after it Cvs.L2a.NonresonantCrossIntegral applies. The three bounds add.
-/

namespace Cvs.L2a.StationaryCrossPairSplit

open intervalIntegral Real Set Cvs.L2a.NonresonantCrossIntegral

variable {f₁ u₁ p₁ q₁ f₂ u₂ p₂ q₂ σ α β : ℝ → ℝ}

/-- **The telescoped bound where `D < 0`.** -/
theorem cross_abs_le_neg {s t Mz Mv : ℝ} (hst : s ≤ t)
    (hp₁ : ∀ r ∈ Icc s t, p₁ r ≠ 0) (hp₂ : ∀ r ∈ Icc s t, p₂ r ≠ 0)
    (hD : ∀ r ∈ Icc s t, p₂ r * q₁ r - p₁ r * q₂ r ≠ 0)
    (hf₁ : ∀ r ∈ Icc s t, HasDerivAt f₁ (u₁ r / p₁ r) r)
    (hu₁ : ∀ r ∈ Icc s t, HasDerivAt u₁ (-(q₁ r * f₁ r)) r)
    (hf₂ : ∀ r ∈ Icc s t, HasDerivAt f₂ (u₂ r / p₂ r) r)
    (hu₂ : ∀ r ∈ Icc s t, HasDerivAt u₂ (-(q₂ r * f₂ r)) r)
    (hA : ∀ r ∈ Icc s t, HasDerivAt (fun r => σ r * p₁ r / (p₂ r * q₁ r - p₁ r * q₂ r)) (α r) r)
    (hB : ∀ r ∈ Icc s t, HasDerivAt (fun r => σ r * p₂ r / (p₂ r * q₁ r - p₁ r * q₂ r)) (β r) r)
    (hαc : ContinuousOn α (Icc s t)) (hβc : ContinuousOn β (Icc s t))
    (hc : ContinuousOn (fun r => σ r * (f₁ r * f₂ r)) (Icc s t))
    (hq₁ : ContinuousOn q₁ (Icc s t)) (hq₂ : ContinuousOn q₂ (Icc s t))
    (hpc₁ : ContinuousOn p₁ (Icc s t)) (hpc₂ : ContinuousOn p₂ (Icc s t))
    (hα : ∀ r ∈ Icc s t, α r ≤ 0) (hβ : ∀ r ∈ Icc s t, β r ≤ 0)
    (hA0 : σ s * p₁ s / (p₂ s * q₁ s - p₁ s * q₂ s) ≤ 0)
    (hB0 : σ s * p₂ s / (p₂ s * q₁ s - p₁ s * q₂ s) ≤ 0)
    (hZ : ∀ r ∈ Icc s t, |f₁ r * u₂ r| ≤ Mz) (hV : ∀ r ∈ Icc s t, |u₁ r * f₂ r| ≤ Mv) :
    |∫ r in s..t, σ r * (f₁ r * f₂ r)|
      ≤ 2 * (-(σ t * p₁ t / (p₂ t * q₁ t - p₁ t * q₂ t)) * Mz
        + -(σ t * p₂ t / (p₂ t * q₁ t - p₁ t * q₂ t)) * Mv) := by
  have hI : uIcc s t = Icc s t := uIcc_of_le hst
  have hmem0 : s ∈ Icc s t := left_mem_Icc.mpr hst
  have hmem1 : t ∈ Icc s t := right_mem_Icc.mpr hst
  have cont : ∀ f : ℝ → ℝ, (∀ r ∈ Icc s t, DifferentiableAt ℝ f r) → ContinuousOn f (Icc s t) :=
    fun f hf r hr => (hf r hr).continuousAt.continuousWithinAt
  have hf₁c := cont f₁ fun r hr => (hf₁ r hr).differentiableAt
  have hu₁c := cont u₁ fun r hr => (hu₁ r hr).differentiableAt
  have hf₂c := cont f₂ fun r hr => (hf₂ r hr).differentiableAt
  have hu₂c := cont u₂ fun r hr => (hu₂ r hr).differentiableAt
  have hid := Cvs.Prolate.LiouvilleGreen.SturmProductByParts.integral_cross hst hp₁ hp₂ hD hf₁ hu₁ hf₂ hu₂ hA hB hαc hβc hc
    hq₁ hq₂ hpc₁ hpc₂
  set A := fun r => σ r * p₁ r / (p₂ r * q₁ r - p₁ r * q₂ r)
  set B := fun r => σ r * p₂ r / (p₂ r * q₁ r - p₁ r * q₂ r)
  have hAint : ∫ r in s..t, α r = A t - A s :=
    integral_eq_sub_of_hasDerivAt (fun r hr => hA r (hI ▸ hr)) (hαc.intervalIntegrable_of_Icc hst)
  have hBint : ∫ r in s..t, β r = B t - B s :=
    integral_eq_sub_of_hasDerivAt (fun r hr => hB r (hI ▸ hr)) (hβc.intervalIntegrable_of_Icc hst)
  have iαZ : IntervalIntegrable (fun r => α r * (f₁ r * u₂ r)) MeasureTheory.volume s t :=
    (hαc.mul (hf₁c.mul hu₂c)).intervalIntegrable_of_Icc hst
  have iβV : IntervalIntegrable (fun r => β r * (u₁ r * f₂ r)) MeasureTheory.volume s t :=
    (hβc.mul (hu₁c.mul hf₂c)).intervalIntegrable_of_Icc hst
  have iα : IntervalIntegrable (fun r => -α r * Mz) MeasureTheory.volume s t :=
    ((hαc.neg).mul continuousOn_const).intervalIntegrable_of_Icc hst
  have iβ : IntervalIntegrable (fun r => -β r * Mv) MeasureTheory.volume s t :=
    ((hβc.neg).mul continuousOn_const).intervalIntegrable_of_Icc hst
  have bαZ : |∫ r in s..t, α r * (f₁ r * u₂ r)| ≤ (A s - A t) * Mz := by
    have h1 := abs_integral_le_integral_abs (μ := MeasureTheory.volume) (f := fun r => α r * (f₁ r * u₂ r)) hst
    have h2 : ∫ r in s..t, |α r * (f₁ r * u₂ r)| ≤ ∫ r in s..t, -α r * Mz := by
      apply integral_mono_on hst (iαZ.abs) iα
      intro r hr
      rw [abs_mul, abs_of_nonpos (hα r hr)]
      exact mul_le_mul_of_nonneg_left (hZ r hr) (by linarith [hα r hr])
    have h3 : ∫ r in s..t, -α r * Mz = (A s - A t) * Mz := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg, hAint]; ring
    linarith
  have bβV : |∫ r in s..t, β r * (u₁ r * f₂ r)| ≤ (B s - B t) * Mv := by
    have h1 := abs_integral_le_integral_abs (μ := MeasureTheory.volume) (f := fun r => β r * (u₁ r * f₂ r)) hst
    have h2 : ∫ r in s..t, |β r * (u₁ r * f₂ r)| ≤ ∫ r in s..t, -β r * Mv := by
      apply integral_mono_on hst (iβV.abs) iβ
      intro r hr
      rw [abs_mul, abs_of_nonpos (hβ r hr)]
      exact mul_le_mul_of_nonneg_left (hV r hr) (by linarith [hβ r hr])
    have h3 : ∫ r in s..t, -β r * Mv = (B s - B t) * Mv := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg, hBint]; ring
    linarith
  have hAs : A t ≤ A s := by
    have h : 0 ≤ ∫ r in s..t, -α r := integral_nonneg hst (fun r hr => neg_nonneg.mpr (hα r hr))
    rw [intervalIntegral.integral_neg, hAint] at h; linarith
  have hBs : B t ≤ B s := by
    have h : 0 ≤ ∫ r in s..t, -β r := integral_nonneg hst (fun r hr => neg_nonneg.mpr (hβ r hr))
    rw [intervalIntegral.integral_neg, hBint] at h; linarith
  have hA0' : A s ≤ 0 := hA0
  have hB0' : B s ≤ 0 := hB0
  have hMz : 0 ≤ Mz := le_trans (abs_nonneg _) (hZ s hmem0)
  have hMv : 0 ≤ Mv := le_trans (abs_nonneg _) (hV s hmem0)
  have eZt : |A t * (f₁ t * u₂ t)| ≤ -A t * Mz := by
    rw [abs_mul, abs_of_nonpos (hAs.trans hA0')]
    exact mul_le_mul_of_nonneg_left (hZ t hmem1) (by linarith)
  have eVt : |B t * (u₁ t * f₂ t)| ≤ -B t * Mv := by
    rw [abs_mul, abs_of_nonpos (hBs.trans hB0')]
    exact mul_le_mul_of_nonneg_left (hV t hmem1) (by linarith)
  have eZs : |A s * (f₁ s * u₂ s)| ≤ -A s * Mz := by
    rw [abs_mul, abs_of_nonpos hA0']; exact mul_le_mul_of_nonneg_left (hZ s hmem0) (by linarith)
  have eVs : |B s * (u₁ s * f₂ s)| ≤ -B s * Mv := by
    rw [abs_mul, abs_of_nonpos hB0']; exact mul_le_mul_of_nonneg_left (hV s hmem0) (by linarith)
  have hid' : ∫ r in s..t, σ r * (f₁ r * f₂ r)
      = (A t * (f₁ t * u₂ t) - B t * (u₁ t * f₂ t)) - (A s * (f₁ s * u₂ s) - B s * (u₁ s * f₂ s))
        - (∫ r in s..t, α r * (f₁ r * u₂ r)) + ∫ r in s..t, β r * (u₁ r * f₂ r) := hid
  rw [hid', abs_le]
  constructor
  · nlinarith [abs_le.mp eZt, abs_le.mp eVt, abs_le.mp eZs, abs_le.mp eVs, abs_le.mp bαZ, abs_le.mp bβV]
  · nlinarith [abs_le.mp eZt, abs_le.mp eVt, abs_le.mp eZs, abs_le.mp eVs, abs_le.mp bαZ, abs_le.mp bβV]

/-- **The window bound**: `|∫_s^t f₁f₂| ≤ (t − s) F₁ F₂` when `|f₁| ≤ F₁`, `|f₂| ≤ F₂`. -/
theorem window_le {s t F₁ F₂ : ℝ} (hst : s ≤ t) (h₁ : ContinuousOn f₁ (Icc s t))
    (h₂ : ContinuousOn f₂ (Icc s t)) (hF₁ : ∀ r ∈ Icc s t, |f₁ r| ≤ F₁) (hF₂ : ∀ r ∈ Icc s t, |f₂ r| ≤ F₂) :
    |∫ r in s..t, f₁ r * f₂ r| ≤ (t - s) * (F₁ * F₂) := by
  have hb : ∀ r ∈ Set.uIoc s t, ‖f₁ r * f₂ r‖ ≤ F₁ * F₂ := by
    intro r hr
    have hr' : r ∈ Icc s t := by
      rw [uIoc_of_le hst] at hr; exact ⟨hr.1.le, hr.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hF₁ r hr') (hF₂ r hr') (abs_nonneg _) (le_trans (abs_nonneg _) (hF₁ r hr'))
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst)] at this
  linarith

section prolate
variable {c χ m r : ℝ}

theorem hasDerivAt_A (hm : m ≠ 0) (hr : r ≠ 0) {τ : ℝ} (hD : Dmr c χ m r τ ≠ 0) :
    HasDerivAt (fun τ => 1 * pm m τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ r τ))
      ((2 * τ * Dmr c χ m r τ - pm m τ * dDmr c χ m r τ) / Dmr c χ m r τ ^ 2) τ := by
  have := (hasDerivAt_pm hm τ).div (hasDerivAt_Dmr (c := c) (χ := χ) hm hr τ) hD
  have e : (fun τ => 1 * pm m τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ r τ)) = pm m / Dmr c χ m r := by
    funext τ; simp [Dmr]
  rw [e]; exact this

theorem hasDerivAt_B (hm : m ≠ 0) (hr : r ≠ 0) {τ : ℝ} (hD : Dmr c χ m r τ ≠ 0) :
    HasDerivAt (fun τ => 1 * pm r τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ r τ))
      ((2 * τ * Dmr c χ m r τ - pm r τ * dDmr c χ m r τ) / Dmr c χ m r τ ^ 2) τ := by
  have := (hasDerivAt_pm hr τ).div (hasDerivAt_Dmr (c := c) (χ := χ) hm hr τ) hD
  have e : (fun τ => 1 * pm r τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ r τ)) = pm r / Dmr c χ m r := by
    funext τ; simp [Dmr]
  rw [e]; exact this

theorem numA_nonpos (hr : 0 < r) (hrm : r < m) (hχ : χ < c ^ 2) {τ : ℝ} (hτ : 0 ≤ τ) :
    2 * τ * Dmr c χ m r τ - pm m τ * dDmr c χ m r τ ≤ 0 := by
  have hm : 0 < m := hr.trans hrm
  rw [numA_eq hm.ne' hr.ne']
  have : 0 ≤ (m ^ 2 - r ^ 2) := by nlinarith
  have : 0 ≤ (c ^ 2 - χ) / (m ^ 2 * r ^ 2) := div_nonneg (by linarith) (by positivity)
  have : 0 ≤ (m ^ 2 - r ^ 2) * (2 * τ) * (c ^ 2 * (τ ^ 2 - 1 / m ^ 2) ^ 2 + (c ^ 2 - χ) / (m ^ 2 * r ^ 2)) := by
    positivity
  linarith

theorem numB_nonpos (hr : 0 < r) (hrm : r < m) (hχ : χ < c ^ 2) {τ : ℝ} (hτ : 0 ≤ τ) :
    2 * τ * Dmr c χ m r τ - pm r τ * dDmr c χ m r τ ≤ 0 := by
  have hm : 0 < m := hr.trans hrm
  rw [numB_eq hm.ne' hr.ne']
  have : 0 ≤ (m ^ 2 - r ^ 2) := by nlinarith
  have : 0 ≤ (c ^ 2 - χ) / (m ^ 2 * r ^ 2) := div_nonneg (by linarith) (by positivity)
  have : 0 ≤ (m ^ 2 - r ^ 2) * (2 * τ) * (c ^ 2 * (τ ^ 2 - 1 / r ^ 2) ^ 2 + (c ^ 2 - χ) / (m ^ 2 * r ^ 2)) := by
    positivity
  linarith

/-- **The stationary prolate cross pair, split three ways.** For the modes `m > r > 0`, `1 < ra`,
`a ≤ t_l ≤ t_r ≤ b`, `D < 0` on `[a, t_l]`, `D > 0` on `[t_r, b]`, `χ < c²`:
`|∫_a^b f₁f₂| ≤ 2(p_m M_z + p_r M_v)/|D| at t_l + (t_r − t_l) F₁F₂ + 2(p_m M_z' + p_r M_v')/D at t_r`. -/
theorem prolate_stationary_le {f₁ u₁ f₂ u₂ : ℝ → ℝ} {a tl tr b MzL MvL MzR MvR F₁ F₂ : ℝ}
    (hr : 0 < r) (hrm : r < m) (hra : 1 < r * a) (hχ : χ < c ^ 2)
    (hal : a ≤ tl) (hlr : tl ≤ tr) (hrb : tr ≤ b)
    (hDL : ∀ τ ∈ Icc a tl, Dmr c χ m r τ < 0) (hDR : ∀ τ ∈ Icc tr b, 0 < Dmr c χ m r τ)
    (hf₁ : ∀ τ ∈ Icc a b, HasDerivAt f₁ (u₁ τ / pm m τ) τ)
    (hu₁ : ∀ τ ∈ Icc a b, HasDerivAt u₁ (-(qm c χ m τ * f₁ τ)) τ)
    (hf₂ : ∀ τ ∈ Icc a b, HasDerivAt f₂ (u₂ τ / pm r τ) τ)
    (hu₂ : ∀ τ ∈ Icc a b, HasDerivAt u₂ (-(qm c χ r τ * f₂ τ)) τ)
    (hZL : ∀ τ ∈ Icc a tl, |f₁ τ * u₂ τ| ≤ MzL) (hVL : ∀ τ ∈ Icc a tl, |u₁ τ * f₂ τ| ≤ MvL)
    (hZR : ∀ τ ∈ Icc tr b, |f₁ τ * u₂ τ| ≤ MzR) (hVR : ∀ τ ∈ Icc tr b, |u₁ τ * f₂ τ| ≤ MvR)
    (hF₁ : ∀ τ ∈ Icc tl tr, |f₁ τ| ≤ F₁) (hF₂ : ∀ τ ∈ Icc tl tr, |f₂ τ| ≤ F₂) :
    |∫ τ in a..b, f₁ τ * f₂ τ|
      ≤ 2 * (-(pm m tl / Dmr c χ m r tl) * MzL + -(pm r tl / Dmr c χ m r tl) * MvL)
        + (tr - tl) * (F₁ * F₂)
        + 2 * (pm m tr * MzR + pm r tr * MvR) / Dmr c χ m r tr := by
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
  have hDc : ContinuousOn (Dmr c χ m r) univ := by unfold Dmr pm qm; fun_prop
  have hdDc : ContinuousOn (dDmr c χ m r) univ := by unfold dDmr pm qm; fun_prop
  have hpmc : ∀ k : ℝ, ContinuousOn (pm k) univ := fun k => by unfold pm; fun_prop
  have hqmc : ∀ k : ℝ, ContinuousOn (qm c χ k) univ := fun k => by unfold qm; fun_prop
  have hDmr : ∀ τ, Dmr c χ m r τ = pm r τ * qm c χ m τ - pm m τ * qm c χ r τ := fun _ => rfl
  -- left piece
  have left := cross_abs_le_neg (σ := fun _ => 1) (Mz := MzL) (Mv := MvL) hal
    (fun τ hτ => (hpos τ hτ.1).2.ne') (fun τ hτ => (hpos τ hτ.1).1.ne')
    (fun τ hτ => by rw [← hDmr]; exact (hDL τ hτ).ne)
    (fun τ hτ => hf₁ τ (subL hτ)) (fun τ hτ => hu₁ τ (subL hτ))
    (fun τ hτ => hf₂ τ (subL hτ)) (fun τ hτ => hu₂ τ (subL hτ))
    (fun τ hτ => hasDerivAt_A hm.ne' hr.ne' (hDL τ hτ).ne)
    (fun τ hτ => hasDerivAt_B hm.ne' hr.ne' (hDL τ hτ).ne)
    (((continuousOn_const.mul continuousOn_id).mul (hDc.mono (subset_univ _))).sub
      (((hpmc m).mono (subset_univ _)).mul (hdDc.mono (subset_univ _))) |>.div
      ((hDc.mono (subset_univ _)).pow 2) fun τ hτ => pow_ne_zero 2 (hDL τ hτ).ne)
    (((continuousOn_const.mul continuousOn_id).mul (hDc.mono (subset_univ _))).sub
      (((hpmc r).mono (subset_univ _)).mul (hdDc.mono (subset_univ _))) |>.div
      ((hDc.mono (subset_univ _)).pow 2) fun τ hτ => pow_ne_zero 2 (hDL τ hτ).ne)
    (continuousOn_const.mul ((hf₁c.mono subL).mul (hf₂c.mono subL)))
    ((hqmc m).mono (subset_univ _)) ((hqmc r).mono (subset_univ _))
    ((hpmc m).mono (subset_univ _)) ((hpmc r).mono (subset_univ _))
    (fun τ hτ => div_nonpos_of_nonpos_of_nonneg (numA_nonpos hr hrm hχ (le_trans ha0.le hτ.1)) (sq_nonneg _))
    (fun τ hτ => div_nonpos_of_nonpos_of_nonneg (numB_nonpos hr hrm hχ (le_trans ha0.le hτ.1)) (sq_nonneg _))
    (by
      have := hDL a (left_mem_Icc.mpr hal); have := (hpos a le_rfl).2
      rw [one_mul, ← hDmr]; exact div_nonpos_of_nonneg_of_nonpos this.le (hDL a (left_mem_Icc.mpr hal)).le)
    (by
      have := (hpos a le_rfl).1
      rw [one_mul, ← hDmr]; exact div_nonpos_of_nonneg_of_nonpos this.le (hDL a (left_mem_Icc.mpr hal)).le)
    hZL hVL
  simp only [one_mul, ← hDmr] at left
  -- right piece
  have right := prolate_cross_le hrb hr hrm (lt_of_lt_of_le hra (by nlinarith [hal.trans hlr])) hχ hDR
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

end prolate

end Cvs.L2a.StationaryCrossPairSplit
