import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.NonresonantCrossIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prolate cross bound for modes of two prolates

For the mode `m` of a prolate with `χ` and the mode `r` of one with `χ'` (same `c`), `D = p_r q_m − p_m q'_r`;
`p_m' D − p_m D'` involves `χ` only and `p_r' D − p_r D'` involves `χ'` only, each exactly as in Cvs.L2a.NonresonantCrossIntegral, so `NonresonantCrossIntegral`'s
non-resonant bound holds verbatim with each mode keeping its own `χ`.
-/

namespace Cvs.L2a.TwoProlateCrossBound

open intervalIntegral Real Set Cvs.L2a.NonresonantCrossIntegral

variable {c χ χ' m r : ℝ}

/-- `D = p_r q_m − p_m q_r`, the partner `r` with its own `χ'`. -/
noncomputable def Dmr2 (c χ χ' m r t : ℝ) : ℝ := pm r t * qm c χ m t - pm m t * qm c χ' r t
/-- `D'`. -/
noncomputable def dDmr2 (c χ χ' m r t : ℝ) : ℝ :=
  2 * t * qm c χ m t + pm r t * (2 * c ^ 2 * m ^ 2 * t) - (2 * t * qm c χ' r t + pm m t * (2 * c ^ 2 * r ^ 2 * t))

theorem hasDerivAt_Dmr2 (hm : m ≠ 0) (hr : r ≠ 0) (t : ℝ) :
    HasDerivAt (Dmr2 c χ χ' m r) (dDmr2 c χ χ' m r t) t := by
  have := ((hasDerivAt_pm hr t).mul (hasDerivAt_qm (c := c) (χ := χ) m t)).sub
    ((hasDerivAt_pm hm t).mul (hasDerivAt_qm (c := c) (χ := χ') r t))
  refine this.congr_deriv ?_; unfold dDmr2; ring

/-- `p_m' D − p_m D' = −(m² − r²) 2t [c²(t² − 1/m²)² + (c² − χ)/(m²r²)]`. -/
theorem numA2_eq (hm : m ≠ 0) (hr : r ≠ 0) (t : ℝ) :
    2 * t * Dmr2 c χ χ' m r t - pm m t * dDmr2 c χ χ' m r t
      = -((m ^ 2 - r ^ 2) * (2 * t) * (c ^ 2 * (t ^ 2 - 1 / m ^ 2) ^ 2 + (c ^ 2 - χ) / (m ^ 2 * r ^ 2))) := by
  unfold Dmr2 dDmr2 pm qm; field_simp; ring

/-- `p_r' D − p_r D' = −(m² − r²) 2t [c²(t² − 1/r²)² + (c² − χ)/(m²r²)]`. -/
theorem numB2_eq (hm : m ≠ 0) (hr : r ≠ 0) (t : ℝ) :
    2 * t * Dmr2 c χ χ' m r t - pm r t * dDmr2 c χ χ' m r t
      = -((m ^ 2 - r ^ 2) * (2 * t) * (c ^ 2 * (t ^ 2 - 1 / r ^ 2) ^ 2 + (c ^ 2 - χ') / (m ^ 2 * r ^ 2))) := by
  unfold Dmr2 dDmr2 pm qm; field_simp; ring

/-- **The non-resonant prolate cross bound.** For solutions of the scaled prolate systems of the modes
`m > r > 0` on `[s, t]`, `1 < rs`, with `χ < c²`, `D > 0` there, and `|f₁u₂| ≤ M_z`, `|u₁f₂| ≤ M_v`,
`|∫ f₁f₂| ≤ 2 (p_m(s) M_z + p_r(s) M_v)/D(s)`. -/
theorem prolate_cross2_le {f₁ u₁ f₂ u₂ : ℝ → ℝ} {s t Mz Mv : ℝ} (hst : s ≤ t) (hr : 0 < r) (hrm : r < m)
    (hrs : 1 < r * s) (hχ : χ < c ^ 2) (hχ' : χ' < c ^ 2) (hD : ∀ τ ∈ Icc s t, 0 < Dmr2 c χ χ' m r τ)
    (hf₁ : ∀ τ ∈ Icc s t, HasDerivAt f₁ (u₁ τ / pm m τ) τ)
    (hu₁ : ∀ τ ∈ Icc s t, HasDerivAt u₁ (-(qm c χ m τ * f₁ τ)) τ)
    (hf₂ : ∀ τ ∈ Icc s t, HasDerivAt f₂ (u₂ τ / pm r τ) τ)
    (hu₂ : ∀ τ ∈ Icc s t, HasDerivAt u₂ (-(qm c χ' r τ * f₂ τ)) τ)
    (hZ : ∀ τ ∈ Icc s t, |f₁ τ * u₂ τ| ≤ Mz) (hV : ∀ τ ∈ Icc s t, |u₁ τ * f₂ τ| ≤ Mv) :
    |∫ τ in s..t, f₁ τ * f₂ τ| ≤ 2 * (pm m s * Mz + pm r s * Mv) / Dmr2 c χ χ' m r s := by
  have hm : 0 < m := hr.trans hrm
  have hs0 : 0 < s := by
    by_contra h; push Not at h; nlinarith
  have hpos : ∀ τ ∈ Icc s t, 0 < pm r τ ∧ 0 < pm m τ := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    have h1 : 1 < r * τ := lt_of_lt_of_le hrs (by nlinarith [hτ.1])
    have h2 : 1 < m * τ := lt_of_lt_of_le h1 (by nlinarith)
    unfold pm
    constructor <;> apply div_pos <;> nlinarith
  have hDmr : ∀ τ ∈ Icc s t, Dmr2 c χ χ' m r τ = pm r τ * qm c χ m τ - pm m τ * qm c χ' r τ := fun _ _ => rfl
  have hAd : ∀ τ ∈ Icc s t, HasDerivAt (fun τ => 1 * pm m τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ' r τ))
      ((2 * τ * Dmr2 c χ χ' m r τ - pm m τ * dDmr2 c χ χ' m r τ) / Dmr2 c χ χ' m r τ ^ 2) τ := fun τ hτ => by
    have := (hasDerivAt_pm hm.ne' τ).div (hasDerivAt_Dmr2 (c := c) (χ := χ) (χ' := χ') hm.ne' hr.ne' τ) (hD τ hτ).ne'
    have e : (fun τ => 1 * pm m τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ' r τ)) = pm m / Dmr2 c χ χ' m r := by
      funext τ; simp [Dmr2]
    rw [e]; exact this
  have hBd : ∀ τ ∈ Icc s t, HasDerivAt (fun τ => 1 * pm r τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ' r τ))
      ((2 * τ * Dmr2 c χ χ' m r τ - pm r τ * dDmr2 c χ χ' m r τ) / Dmr2 c χ χ' m r τ ^ 2) τ := fun τ hτ => by
    have := (hasDerivAt_pm hr.ne' τ).div (hasDerivAt_Dmr2 (c := c) (χ := χ) (χ' := χ') hm.ne' hr.ne' τ) (hD τ hτ).ne'
    have e : (fun τ => 1 * pm r τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ' r τ)) = pm r / Dmr2 c χ χ' m r := by
      funext τ; simp [Dmr2]
    rw [e]; exact this
  have hDc : ContinuousOn (Dmr2 c χ χ' m r) (Icc s t) := by unfold Dmr2 pm qm; fun_prop
  have hdDc : ContinuousOn (dDmr2 c χ χ' m r) (Icc s t) := by unfold dDmr2 pm qm; fun_prop
  have hpmc : ∀ k : ℝ, ContinuousOn (pm k) (Icc s t) := fun k => by unfold pm; fun_prop
  have hqmc : ∀ (x k : ℝ), ContinuousOn (qm c x k) (Icc s t) := fun x k => by unfold qm; fun_prop
  have hint := fun (τ : ℝ) (hτ : τ ∈ Icc s t) => (hD τ hτ).ne'
  have hsq : ∀ τ ∈ Icc s t, Dmr2 c χ χ' m r τ ^ 2 ≠ 0 := fun τ hτ => pow_ne_zero 2 (hint τ hτ)
  have key := cross_abs_le (σ := fun _ => 1) (Mz := Mz) (Mv := Mv) hst
    (fun τ hτ => (hpos τ hτ).2.ne') (fun τ hτ => (hpos τ hτ).1.ne')
    (fun τ hτ => by rw [← hDmr τ hτ]; exact (hD τ hτ).ne') hf₁ hu₁ hf₂ hu₂ hAd hBd
    (((continuousOn_const.mul continuousOn_id).mul hDc).sub ((hpmc m).mul hdDc) |>.div (hDc.pow 2) hsq)
    (((continuousOn_const.mul continuousOn_id).mul hDc).sub ((hpmc r).mul hdDc) |>.div (hDc.pow 2) hsq)
    (by
      have h1 : ContinuousOn f₁ (Icc s t) := fun τ hτ => (hf₁ τ hτ).continuousAt.continuousWithinAt
      have h2 : ContinuousOn f₂ (Icc s t) := fun τ hτ => (hf₂ τ hτ).continuousAt.continuousWithinAt
      exact continuousOn_const.mul (h1.mul h2))
    (hqmc χ m) (hqmc χ' r) (hpmc m) (hpmc r)
    (fun τ hτ => by
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      rw [numA2_eq hm.ne' hr.ne']
      have : 0 ≤ (m ^ 2 - r ^ 2) := by nlinarith
      have hτ0 : 0 ≤ τ := le_trans hs0.le hτ.1
      have : 0 ≤ (c ^ 2 - χ) / (m ^ 2 * r ^ 2) := div_nonneg (by linarith) (by positivity)
      have : 0 ≤ c ^ 2 * (τ ^ 2 - 1 / m ^ 2) ^ 2 := by positivity
      have : 0 ≤ (m ^ 2 - r ^ 2) * (2 * τ) * (c ^ 2 * (τ ^ 2 - 1 / m ^ 2) ^ 2 + (c ^ 2 - χ) / (m ^ 2 * r ^ 2)) := by
        positivity
      linarith)
    (fun τ hτ => by
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      rw [numB2_eq hm.ne' hr.ne']
      have : 0 ≤ (m ^ 2 - r ^ 2) := by nlinarith
      have hτ0 : 0 ≤ τ := le_trans hs0.le hτ.1
      have : 0 ≤ (c ^ 2 - χ') / (m ^ 2 * r ^ 2) := div_nonneg (by linarith) (by positivity)
      have : 0 ≤ (m ^ 2 - r ^ 2) * (2 * τ) * (c ^ 2 * (τ ^ 2 - 1 / r ^ 2) ^ 2 + (c ^ 2 - χ') / (m ^ 2 * r ^ 2)) := by
        positivity
      linarith)
    (by
      have := hD t (right_mem_Icc.mpr hst); have := (hpos t (right_mem_Icc.mpr hst)).2
      rw [← hDmr t (right_mem_Icc.mpr hst)]; positivity)
    (by
      have := hD t (right_mem_Icc.mpr hst); have := (hpos t (right_mem_Icc.mpr hst)).1
      rw [← hDmr t (right_mem_Icc.mpr hst)]; positivity)
    hZ hV
  simp only [one_mul] at key
  rw [← hDmr s (left_mem_Icc.mpr hst)] at key
  calc |∫ τ in s..t, f₁ τ * f₂ τ| ≤ 2 * (pm m s / Dmr2 c χ χ' m r s * Mz + pm r s / Dmr2 c χ χ' m r s * Mv) := key
    _ = 2 * (pm m s * Mz + pm r s * Mv) / Dmr2 c χ χ' m r s := by ring

end Cvs.L2a.TwoProlateCrossBound
