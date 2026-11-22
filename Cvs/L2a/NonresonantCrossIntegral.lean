import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.SturmProductByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A non-resonant cross integral is at most twice its edge coefficient times the energy

When `A = σp₁/D` and `B = σp₂/D` are nonnegative and decreasing, `SturmProductByParts`'s integral terms telescope:
`|∫ σ f₁f₂| ≤ 2 (A(s) sup|f₁u₂| + B(s) sup|u₁f₂|)`. For two prolate modes `ψ(mt)`, `ψ(rt)`, `m > r > 0`,
`D = (m² − r²) E` and `(p₁/E)' = −2t[c²(t² − 1/m²)² + (c² − χ)/(m²r²)]/E²`, negative when `χ < c²`.
-/

namespace Cvs.L2a.NonresonantCrossIntegral

open intervalIntegral Real Set

variable {f₁ u₁ p₁ q₁ f₂ u₂ p₂ q₂ σ α β : ℝ → ℝ}

/-- **The telescoped cross bound.** -/
theorem cross_abs_le {s t Mz Mv : ℝ} (hst : s ≤ t)
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
    (hA0 : 0 ≤ σ t * p₁ t / (p₂ t * q₁ t - p₁ t * q₂ t))
    (hB0 : 0 ≤ σ t * p₂ t / (p₂ t * q₁ t - p₁ t * q₂ t))
    (hZ : ∀ r ∈ Icc s t, |f₁ r * u₂ r| ≤ Mz) (hV : ∀ r ∈ Icc s t, |u₁ r * f₂ r| ≤ Mv) :
    |∫ r in s..t, σ r * (f₁ r * f₂ r)|
      ≤ 2 * (σ s * p₁ s / (p₂ s * q₁ s - p₁ s * q₂ s) * Mz
        + σ s * p₂ s / (p₂ s * q₁ s - p₁ s * q₂ s) * Mv) := by
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
  -- A s − A t = −∫ α, and similarly for B
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
    have h1 : |∫ r in s..t, α r * (f₁ r * u₂ r)| ≤ ∫ r in s..t, |α r * (f₁ r * u₂ r)| :=
      abs_integral_le_integral_abs hst
    have h2 : ∫ r in s..t, |α r * (f₁ r * u₂ r)| ≤ ∫ r in s..t, -α r * Mz := by
      apply integral_mono_on hst (iαZ.abs) iα
      intro r hr
      rw [abs_mul, abs_of_nonpos (hα r hr)]
      exact mul_le_mul_of_nonneg_left (hZ r hr) (by linarith [hα r hr])
    have h3 : ∫ r in s..t, -α r * Mz = (A s - A t) * Mz := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg, hAint]; ring
    linarith
  have bβV : |∫ r in s..t, β r * (u₁ r * f₂ r)| ≤ (B s - B t) * Mv := by
    have h1 : |∫ r in s..t, β r * (u₁ r * f₂ r)| ≤ ∫ r in s..t, |β r * (u₁ r * f₂ r)| :=
      abs_integral_le_integral_abs hst
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
  have hA0' : 0 ≤ A t := hA0
  have hB0' : 0 ≤ B t := hB0
  have eZt : |A t * (f₁ t * u₂ t)| ≤ A t * Mz := by
    rw [abs_mul, abs_of_nonneg hA0']; exact mul_le_mul_of_nonneg_left (hZ t hmem1) hA0'
  have eVt : |B t * (u₁ t * f₂ t)| ≤ B t * Mv := by
    rw [abs_mul, abs_of_nonneg hB0']; exact mul_le_mul_of_nonneg_left (hV t hmem1) hB0'
  have eZs : |A s * (f₁ s * u₂ s)| ≤ A s * Mz := by
    rw [abs_mul, abs_of_nonneg (hA0'.trans hAs)]
    exact mul_le_mul_of_nonneg_left (hZ s hmem0) (hA0'.trans hAs)
  have eVs : |B s * (u₁ s * f₂ s)| ≤ B s * Mv := by
    rw [abs_mul, abs_of_nonneg (hB0'.trans hBs)]
    exact mul_le_mul_of_nonneg_left (hV s hmem0) (hB0'.trans hBs)
  have hMz : 0 ≤ Mz := le_trans (abs_nonneg _) (hZ s hmem0)
  have hMv : 0 ≤ Mv := le_trans (abs_nonneg _) (hV s hmem0)
  have hid' : ∫ r in s..t, σ r * (f₁ r * f₂ r)
      = (A t * (f₁ t * u₂ t) - B t * (u₁ t * f₂ t)) - (A s * (f₁ s * u₂ s) - B s * (u₁ s * f₂ s))
        - (∫ r in s..t, α r * (f₁ r * u₂ r)) + ∫ r in s..t, β r * (u₁ r * f₂ r) := hid
  rw [hid', abs_le]
  constructor
  · nlinarith [abs_le.mp eZt, abs_le.mp eVt, abs_le.mp eZs, abs_le.mp eVs, abs_le.mp bαZ, abs_le.mp bβV]
  · nlinarith [abs_le.mp eZt, abs_le.mp eVt, abs_le.mp eZs, abs_le.mp eVs, abs_le.mp bαZ, abs_le.mp bβV]

section prolate
variable {c χ m r : ℝ}

/-- `p = (m²t² − 1)/m²`, the scaled prolate `p` for the mode `ψ(mt)`. -/
noncomputable def pm (m t : ℝ) : ℝ := (m ^ 2 * t ^ 2 - 1) / m ^ 2
/-- `q = c²m²t² − χ`. -/
def qm (c χ m t : ℝ) : ℝ := c ^ 2 * m ^ 2 * t ^ 2 - χ
/-- `D = p_r q_m − p_m q_r`. -/
noncomputable def Dmr (c χ m r t : ℝ) : ℝ := pm r t * qm c χ m t - pm m t * qm c χ r t
/-- `D'`. -/
noncomputable def dDmr (c χ m r t : ℝ) : ℝ :=
  2 * t * qm c χ m t + pm r t * (2 * c ^ 2 * m ^ 2 * t) - (2 * t * qm c χ r t + pm m t * (2 * c ^ 2 * r ^ 2 * t))

theorem hasDerivAt_pm {k : ℝ} (hk : k ≠ 0) (t : ℝ) : HasDerivAt (pm k) (2 * t) t := by
  have := (((hasDerivAt_pow 2 t).const_mul (k ^ 2)).sub_const 1).div_const (k ^ 2)
  refine this.congr_deriv ?_; field_simp; ring

theorem hasDerivAt_qm (k t : ℝ) : HasDerivAt (qm c χ k) (2 * c ^ 2 * k ^ 2 * t) t := by
  have := ((hasDerivAt_pow 2 t).const_mul (c ^ 2 * k ^ 2)).sub_const χ
  exact this.congr_deriv (by ring)

theorem hasDerivAt_Dmr (hm : m ≠ 0) (hr : r ≠ 0) (t : ℝ) :
    HasDerivAt (Dmr c χ m r) (dDmr c χ m r t) t := by
  have := ((hasDerivAt_pm hr t).mul (hasDerivAt_qm (c := c) (χ := χ) m t)).sub
    ((hasDerivAt_pm hm t).mul (hasDerivAt_qm (c := c) (χ := χ) r t))
  refine this.congr_deriv ?_; unfold dDmr; ring

/-- `p_m' D − p_m D' = −(m² − r²) 2t [c²(t² − 1/m²)² + (c² − χ)/(m²r²)]`. -/
theorem numA_eq (hm : m ≠ 0) (hr : r ≠ 0) (t : ℝ) :
    2 * t * Dmr c χ m r t - pm m t * dDmr c χ m r t
      = -((m ^ 2 - r ^ 2) * (2 * t) * (c ^ 2 * (t ^ 2 - 1 / m ^ 2) ^ 2 + (c ^ 2 - χ) / (m ^ 2 * r ^ 2))) := by
  unfold Dmr dDmr pm qm; field_simp; ring

/-- `p_r' D − p_r D' = −(m² − r²) 2t [c²(t² − 1/r²)² + (c² − χ)/(m²r²)]`. -/
theorem numB_eq (hm : m ≠ 0) (hr : r ≠ 0) (t : ℝ) :
    2 * t * Dmr c χ m r t - pm r t * dDmr c χ m r t
      = -((m ^ 2 - r ^ 2) * (2 * t) * (c ^ 2 * (t ^ 2 - 1 / r ^ 2) ^ 2 + (c ^ 2 - χ) / (m ^ 2 * r ^ 2))) := by
  unfold Dmr dDmr pm qm; field_simp; ring

/-- **The non-resonant prolate cross bound.** For solutions of the scaled prolate systems of the modes
`m > r > 0` on `[s, t]`, `1 < rs`, with `χ < c²`, `D > 0` there, and `|f₁u₂| ≤ M_z`, `|u₁f₂| ≤ M_v`,
`|∫ f₁f₂| ≤ 2 (p_m(s) M_z + p_r(s) M_v)/D(s)`. -/
theorem prolate_cross_le {f₁ u₁ f₂ u₂ : ℝ → ℝ} {s t Mz Mv : ℝ} (hst : s ≤ t) (hr : 0 < r) (hrm : r < m)
    (hrs : 1 < r * s) (hχ : χ < c ^ 2) (hD : ∀ τ ∈ Icc s t, 0 < Dmr c χ m r τ)
    (hf₁ : ∀ τ ∈ Icc s t, HasDerivAt f₁ (u₁ τ / pm m τ) τ)
    (hu₁ : ∀ τ ∈ Icc s t, HasDerivAt u₁ (-(qm c χ m τ * f₁ τ)) τ)
    (hf₂ : ∀ τ ∈ Icc s t, HasDerivAt f₂ (u₂ τ / pm r τ) τ)
    (hu₂ : ∀ τ ∈ Icc s t, HasDerivAt u₂ (-(qm c χ r τ * f₂ τ)) τ)
    (hZ : ∀ τ ∈ Icc s t, |f₁ τ * u₂ τ| ≤ Mz) (hV : ∀ τ ∈ Icc s t, |u₁ τ * f₂ τ| ≤ Mv) :
    |∫ τ in s..t, f₁ τ * f₂ τ| ≤ 2 * (pm m s * Mz + pm r s * Mv) / Dmr c χ m r s := by
  have hm : 0 < m := hr.trans hrm
  have hs0 : 0 < s := by
    by_contra h; push Not at h; nlinarith
  have hpos : ∀ τ ∈ Icc s t, 0 < pm r τ ∧ 0 < pm m τ := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le hs0 hτ.1
    have h1 : 1 < r * τ := lt_of_lt_of_le hrs (by nlinarith [hτ.1])
    have h2 : 1 < m * τ := lt_of_lt_of_le h1 (by nlinarith)
    unfold pm
    constructor <;> apply div_pos <;> nlinarith
  have hDmr : ∀ τ ∈ Icc s t, Dmr c χ m r τ = pm r τ * qm c χ m τ - pm m τ * qm c χ r τ := fun _ _ => rfl
  have hAd : ∀ τ ∈ Icc s t, HasDerivAt (fun τ => 1 * pm m τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ r τ))
      ((2 * τ * Dmr c χ m r τ - pm m τ * dDmr c χ m r τ) / Dmr c χ m r τ ^ 2) τ := fun τ hτ => by
    have := (hasDerivAt_pm hm.ne' τ).div (hasDerivAt_Dmr (c := c) (χ := χ) hm.ne' hr.ne' τ) (hD τ hτ).ne'
    have e : (fun τ => 1 * pm m τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ r τ)) = pm m / Dmr c χ m r := by
      funext τ; simp [Dmr]
    rw [e]; exact this
  have hBd : ∀ τ ∈ Icc s t, HasDerivAt (fun τ => 1 * pm r τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ r τ))
      ((2 * τ * Dmr c χ m r τ - pm r τ * dDmr c χ m r τ) / Dmr c χ m r τ ^ 2) τ := fun τ hτ => by
    have := (hasDerivAt_pm hr.ne' τ).div (hasDerivAt_Dmr (c := c) (χ := χ) hm.ne' hr.ne' τ) (hD τ hτ).ne'
    have e : (fun τ => 1 * pm r τ / (pm r τ * qm c χ m τ - pm m τ * qm c χ r τ)) = pm r / Dmr c χ m r := by
      funext τ; simp [Dmr]
    rw [e]; exact this
  have hDc : ContinuousOn (Dmr c χ m r) (Icc s t) := by unfold Dmr pm qm; fun_prop
  have hdDc : ContinuousOn (dDmr c χ m r) (Icc s t) := by unfold dDmr pm qm; fun_prop
  have hpmc : ∀ k : ℝ, ContinuousOn (pm k) (Icc s t) := fun k => by unfold pm; fun_prop
  have hqmc : ∀ k : ℝ, ContinuousOn (qm c χ k) (Icc s t) := fun k => by unfold qm; fun_prop
  have hint := fun (τ : ℝ) (hτ : τ ∈ Icc s t) => (hD τ hτ).ne'
  have hsq : ∀ τ ∈ Icc s t, Dmr c χ m r τ ^ 2 ≠ 0 := fun τ hτ => pow_ne_zero 2 (hint τ hτ)
  have key := cross_abs_le (σ := fun _ => 1) (Mz := Mz) (Mv := Mv) hst
    (fun τ hτ => (hpos τ hτ).2.ne') (fun τ hτ => (hpos τ hτ).1.ne')
    (fun τ hτ => by rw [← hDmr τ hτ]; exact (hD τ hτ).ne') hf₁ hu₁ hf₂ hu₂ hAd hBd
    (((continuousOn_const.mul continuousOn_id).mul hDc).sub ((hpmc m).mul hdDc) |>.div (hDc.pow 2) hsq)
    (((continuousOn_const.mul continuousOn_id).mul hDc).sub ((hpmc r).mul hdDc) |>.div (hDc.pow 2) hsq)
    (by
      have h1 : ContinuousOn f₁ (Icc s t) := fun τ hτ => (hf₁ τ hτ).continuousAt.continuousWithinAt
      have h2 : ContinuousOn f₂ (Icc s t) := fun τ hτ => (hf₂ τ hτ).continuousAt.continuousWithinAt
      exact continuousOn_const.mul (h1.mul h2))
    (hqmc m) (hqmc r) (hpmc m) (hpmc r)
    (fun τ hτ => by
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      rw [numA_eq hm.ne' hr.ne']
      have : 0 ≤ (m ^ 2 - r ^ 2) := by nlinarith
      have hτ0 : 0 ≤ τ := le_trans hs0.le hτ.1
      have : 0 ≤ (c ^ 2 - χ) / (m ^ 2 * r ^ 2) := div_nonneg (by linarith) (by positivity)
      have : 0 ≤ c ^ 2 * (τ ^ 2 - 1 / m ^ 2) ^ 2 := by positivity
      have : 0 ≤ (m ^ 2 - r ^ 2) * (2 * τ) * (c ^ 2 * (τ ^ 2 - 1 / m ^ 2) ^ 2 + (c ^ 2 - χ) / (m ^ 2 * r ^ 2)) := by
        positivity
      linarith)
    (fun τ hτ => by
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      rw [numB_eq hm.ne' hr.ne']
      have : 0 ≤ (m ^ 2 - r ^ 2) := by nlinarith
      have hτ0 : 0 ≤ τ := le_trans hs0.le hτ.1
      have : 0 ≤ (c ^ 2 - χ) / (m ^ 2 * r ^ 2) := div_nonneg (by linarith) (by positivity)
      have : 0 ≤ (m ^ 2 - r ^ 2) * (2 * τ) * (c ^ 2 * (τ ^ 2 - 1 / r ^ 2) ^ 2 + (c ^ 2 - χ) / (m ^ 2 * r ^ 2)) := by
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
  calc |∫ τ in s..t, f₁ τ * f₂ τ| ≤ 2 * (pm m s / Dmr c χ m r s * Mz + pm r s / Dmr c χ m r s * Mv) := key
    _ = 2 * (pm m s * Mz + pm r s * Mv) / Dmr c χ m r s := by ring

end prolate

end Cvs.L2a.NonresonantCrossIntegral
