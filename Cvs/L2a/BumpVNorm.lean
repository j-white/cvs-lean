import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.LeftRight
import Cvs.L2a.WeightedDerivativeMajorant
import Cvs.Upstream.SineSquaredBump

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `V`-norm through the bump: no boundary term, an explicit majorant

For a system `f' = u/p`, `u' = −q̄f + r̄` with `p, q̄ > 0` on `[α, β]` and the weight `w = bump/q̄` (Cvs.Upstream.SineSquaredBump),
Cvs.L2a.WeightedDerivativeMajorant gives `(1 − ε/2)∫ (bump/q̄) u²/p ≤ (1/2ε)∫ W₂ f² + ∫ (bump/q̄)(q̄f² − f r̄)` with
`W₂ = 2p((π/h)²/q̄ + q̄'²/q̄³)`, the boundary term vanishing with the bump; and `∫_{α+h}^{β−h} u²/(pq̄)` is at most
the bump-weighted norm. This is the `V`-norm of the cutoff route (`V = u/ā`, `ā² = pq̄`).
-/

namespace Cvs.L2a.BumpVNorm

open Real Set intervalIntegral Cvs.Upstream.SineSquaredBump

/-- **The `V`-norm through the bump.** -/
theorem V_norm_bump_le {f u p qb qb' rb : ℝ → ℝ} {α β h ε : ℝ} (hh : 0 < h) (hαβ : α + h ≤ β - h) (hε : 0 < ε)
    (hp : ∀ θ ∈ Icc α β, 0 < p θ) (hqb : ∀ θ ∈ Icc α β, 0 < qb θ)
    (hf : ∀ θ ∈ Icc α β, HasDerivAt f (u θ / p θ) θ)
    (hu : ∀ θ ∈ Icc α β, HasDerivAt u (-(qb θ * f θ) + rb θ) θ)
    (hqb' : ∀ θ ∈ Icc α β, HasDerivAt qb (qb' θ) θ) (hqb'c : ContinuousOn qb' (Icc α β))
    (hpc : ContinuousOn p (Icc α β)) (hrc : ContinuousOn rb (Icc α β)) :
    (1 - ε / 2) * ∫ θ in α..β, bump α β h θ / qb θ * (u θ ^ 2 / p θ)
      ≤ 1 / (2 * ε) * (∫ θ in α..β, 2 * p θ * ((Real.pi / h) ^ 2 / qb θ + qb' θ ^ 2 / qb θ ^ 3) * f θ ^ 2)
        + ∫ θ in α..β, bump α β h θ / qb θ * (qb θ * f θ ^ 2 - f θ * rb θ) := by
  have hab : α ≤ β := by linarith
  have hqbc : ContinuousOn qb (Icc α β) := fun θ hθ => (hqb' θ hθ).continuousAt.continuousWithinAt
  have hne : ∀ θ ∈ Icc α β, qb θ ≠ 0 := fun θ hθ => (hqb θ hθ).ne'
  have hbc : Continuous (bump α β h) :=
    continuous_iff_continuousAt.mpr fun θ => (hasDerivAt_bump hh θ).continuousAt
  -- the weight and its derivative
  set w : ℝ → ℝ := fun θ => bump α β h θ / qb θ with hw
  set w' : ℝ → ℝ := fun θ => bump' α β h θ / qb θ - bump α β h θ * qb' θ / qb θ ^ 2 with hw'
  set W₂ : ℝ → ℝ := fun θ => 2 * p θ * ((Real.pi / h) ^ 2 / qb θ + qb' θ ^ 2 / qb θ ^ 3) with hW₂
  have hwd : ∀ θ ∈ Icc α β, HasDerivAt w (w' θ) θ := fun θ hθ => by
    have := (hasDerivAt_bump (L := α) (R := β) hh θ).div (hqb' θ hθ) (hne θ hθ)
    refine this.congr_deriv ?_
    have := hne θ hθ
    simp only [hw']; field_simp
  have hw0 : ∀ θ ∈ Icc α β, 0 ≤ w θ := fun θ hθ => div_nonneg (bump_nonneg _ _ _ _) (hqb θ hθ).le
  have hW0 : ∀ θ ∈ Icc α β, 0 ≤ W₂ θ := fun θ hθ => by
    have := hp θ hθ; have := hqb θ hθ; simp only [hW₂]; positivity
  have hmaj : ∀ θ ∈ Icc α β, w' θ ^ 2 * p θ ≤ W₂ θ * w θ := fun θ hθ => by
    have hP := hp θ hθ
    have hQ := hqb θ hθ
    have hb0 := bump_nonneg α β h θ
    have hb1 := bump_le_one α β h θ
    have hb' := bump'_sq_le hh hαβ θ
    -- `(b'Q − bQ')² ≤ 2b((π/h)²Q² + Q'²)`
    have key : (bump' α β h θ * qb θ - bump α β h θ * qb' θ) ^ 2
        ≤ 2 * bump α β h θ * ((Real.pi / h) ^ 2 * qb θ ^ 2 + qb' θ ^ 2) := by
      have hsq : bump α β h θ ^ 2 ≤ bump α β h θ := by nlinarith
      nlinarith [sq_nonneg (bump' α β h θ * qb θ + bump α β h θ * qb' θ), sq_nonneg (qb θ),
        mul_le_mul_of_nonneg_right hb' (sq_nonneg (qb θ)), mul_le_mul_of_nonneg_right hsq (sq_nonneg (qb' θ))]
    have e1 : w' θ ^ 2 * p θ = p θ * (bump' α β h θ * qb θ - bump α β h θ * qb' θ) ^ 2 / qb θ ^ 4 := by
      simp only [hw']; field_simp
    have e2 : W₂ θ * w θ = p θ * (2 * bump α β h θ * ((Real.pi / h) ^ 2 * qb θ ^ 2 + qb' θ ^ 2)) / qb θ ^ 4 := by
      simp only [hW₂, hw]; field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left key hP.le) (by positivity)
  have hw'c : ContinuousOn w' (Icc α β) := by
    simp only [hw']
    exact (((continuous_bump' hh).continuousOn.div hqbc hne)).sub
      (((hbc.continuousOn.mul hqb'c).div (hqbc.pow 2) fun θ hθ => pow_ne_zero 2 (hne θ hθ)))
  have hWc : ContinuousOn W₂ (Icc α β) := by
    simp only [hW₂]
    exact (continuousOn_const.mul hpc).mul ((continuousOn_const.div hqbc hne).add
      ((hqb'c.pow 2).div (hqbc.pow 3) fun θ hθ => pow_ne_zero 3 (hne θ hθ)))
  have h := Cvs.L2a.WeightedDerivativeMajorant.integral_w_u_sq_div_p_le_maj hab hε hp hw0 hW0 hmaj hf hu hwd hw'c hWc hpc hqbc hrc
  have hwα : w α = 0 := by simp only [hw]; rw [bump_of_le le_rfl, zero_div]
  have hwβ : w β = 0 := by simp only [hw]; rw [bump_of_ge le_rfl, zero_div]
  rw [hwα, hwβ] at h
  simpa only [hw, hW₂, zero_mul, sub_zero, zero_add] using h

/-- **The inner norm is below the bump-weighted norm**: `∫_{α+h}^{β−h} u²/(pq̄) ≤ ∫_α^β (bump/q̄) u²/p`. -/
theorem V_norm_inner_le {u p qb : ℝ → ℝ} {α β h : ℝ} (hh : 0 < h) (hαβ : α + h ≤ β - h)
    (hp : ∀ θ ∈ Icc α β, 0 < p θ) (hqb : ∀ θ ∈ Icc α β, 0 < qb θ)
    (huc : ContinuousOn u (Icc α β)) (hpc : ContinuousOn p (Icc α β)) (hqbc : ContinuousOn qb (Icc α β)) :
    ∫ θ in (α + h)..(β - h), u θ ^ 2 / (p θ * qb θ) ≤ ∫ θ in α..β, bump α β h θ / qb θ * (u θ ^ 2 / p θ) := by
  have hab : α ≤ β := by linarith
  have hF : ContinuousOn (fun θ => bump α β h θ / qb θ * (u θ ^ 2 / p θ)) (Icc α β) :=
    ((continuous_iff_continuousAt.mpr fun θ => (hasDerivAt_bump hh θ).continuousAt).continuousOn.div hqbc
      fun θ hθ => (hqb θ hθ).ne').mul ((huc.pow 2).div hpc fun θ hθ => (hp θ hθ).ne')
  have hI : ∀ s t, α ≤ s → s ≤ t → t ≤ β →
      IntervalIntegrable (fun θ => bump α β h θ / qb θ * (u θ ^ 2 / p θ)) MeasureTheory.volume s t :=
    fun s t hs hst ht => (hF.mono (Icc_subset_Icc hs ht)).intervalIntegrable_of_Icc hst
  have hnn : ∀ θ ∈ Icc α β, 0 ≤ bump α β h θ / qb θ * (u θ ^ 2 / p θ) := fun θ hθ =>
    mul_nonneg (div_nonneg (bump_nonneg _ _ _ _) (hqb θ hθ).le) (div_nonneg (sq_nonneg _) (hp θ hθ).le)
  have h1 : α ≤ α + h := by linarith
  have h2 : α + h ≤ β - h := hαβ
  have h3 : β - h ≤ β := by linarith
  rw [← integral_add_adjacent_intervals (hI α (α + h) le_rfl h1 (by linarith)) (hI (α + h) β h1 (by linarith) le_rfl),
    ← integral_add_adjacent_intervals (hI (α + h) (β - h) h1 h2 h3) (hI (β - h) β (by linarith) h3 le_rfl)]
  have hz1 : 0 ≤ ∫ θ in α..(α + h), bump α β h θ / qb θ * (u θ ^ 2 / p θ) :=
    integral_nonneg h1 fun θ hθ => hnn θ ⟨hθ.1, by linarith [hθ.2]⟩
  have hz3 : 0 ≤ ∫ θ in (β - h)..β, bump α β h θ / qb θ * (u θ ^ 2 / p θ) :=
    integral_nonneg h3 fun θ hθ => hnn θ ⟨by linarith [hθ.1], hθ.2⟩
  have hmid : ∫ θ in (α + h)..(β - h), u θ ^ 2 / (p θ * qb θ)
      = ∫ θ in (α + h)..(β - h), bump α β h θ / qb θ * (u θ ^ 2 / p θ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ hθ => ?_)
    rw [uIoc_of_le h2] at hθ
    have hne : qb θ ≠ 0 := (hqb θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩).ne'
    have hpne : p θ ≠ 0 := (hp θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩).ne'
    rw [bump_eq_one hh hθ.1.le hθ.2]
    field_simp
  rw [hmid]
  linarith

end Cvs.L2a.BumpVNorm
