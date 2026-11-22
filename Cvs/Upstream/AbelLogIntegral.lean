import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Abel log integral `∫_0^∞ (log|u² − A| − log|u² − B|) du = π(√(−A)₊ − √(−B)₊)`

`log|u² − A|` has the antiderivative `(u − β)log|u − β| + (u + β)log(u + β) − 2u` for `A = β² ≥ 0` and
`u log(u² + α²) − 2u + 2α arctan(u/α)` for `A = −α² < 0`; both are `u log u² − 2u + π√(−A)₊ + o(1)` at `∞`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.Upstream.AbelLogIntegral

/-- The antiderivative of `u ↦ log|u² − A|` vanishing at `0`. -/
def lgAnti (A u : ℝ) : ℝ :=
  if 0 ≤ A then (u - √A) * log (u - √A) + (u + √A) * log (u + √A) - 2 * u
  else u * log (u ^ 2 - A) - 2 * u + 2 * √(-A) * arctan (u / √(-A))

theorem lgAnti_zero (A : ℝ) : lgAnti A 0 = 0 := by
  unfold lgAnti
  split_ifs
  · rw [zero_sub, zero_add, Real.log_neg_eq_log]; ring
  · simp

theorem continuous_lgAnti (A : ℝ) : Continuous (lgAnti A) := by
  unfold lgAnti
  split_ifs with hA
  · have h1 : Continuous fun u : ℝ => (u - √A) * log (u - √A) :=
      continuous_mul_log.comp (continuous_id.sub continuous_const)
    have h2 : Continuous fun u : ℝ => (u + √A) * log (u + √A) :=
      continuous_mul_log.comp (continuous_id.add continuous_const)
    exact (h1.add h2).sub (continuous_const.mul continuous_id)
  · push Not at hA
    have hα : 0 < √(-A) := Real.sqrt_pos.mpr (by linarith)
    refine ((continuous_id.mul ?_).sub (continuous_const.mul continuous_id)).add
      (continuous_const.mul (continuous_arctan.comp (continuous_id.div_const _)))
    exact (show Continuous fun u : ℝ => u ^ 2 - A by fun_prop).log fun u => by nlinarith [sq_nonneg u]

/-- `(lgAnti A)' = log(u² − A)` at `u > 0` with `u² ≠ A`. -/
theorem hasDerivAt_lgAnti {A u : ℝ} (hu : 0 < u) (huA : u ^ 2 ≠ A) :
    HasDerivAt (lgAnti A) (log (u ^ 2 - A)) u := by
  unfold lgAnti
  split_ifs with hA
  · set β := √A with hβ
    have hβ0 : 0 ≤ β := Real.sqrt_nonneg A
    have hββ : β ^ 2 = A := Real.sq_sqrt hA
    have h1 : u - β ≠ 0 := fun h => huA (by rw [← hββ, show u = β by linarith])
    have h2 : u + β ≠ 0 := by linarith
    have d1 := (hasDerivAt_mul_log h1).comp u ((hasDerivAt_id u).sub_const β)
    have d2 := (hasDerivAt_mul_log h2).comp u ((hasDerivAt_id u).add_const β)
    have d := (d1.add d2).sub ((hasDerivAt_id u).const_mul 2)
    refine d.congr_deriv ?_
    rw [show u ^ 2 - A = (u - β) * (u + β) by rw [← hββ]; ring, Real.log_mul h1 h2]
    ring
  · push Not at hA
    set α := √(-A) with hα
    have hα0 : 0 < α := Real.sqrt_pos.mpr (by linarith)
    have hαα : α ^ 2 = -A := Real.sq_sqrt (by linarith)
    have hq : 0 < u ^ 2 - A := by nlinarith [sq_nonneg u]
    have dl : HasDerivAt (fun v => log (v ^ 2 - A)) ((2 * u) / (u ^ 2 - A)) u := by
      have := ((hasDerivAt_pow 2 u).sub_const A).log hq.ne'
      refine this.congr_deriv ?_
      push_cast; ring
    have da : HasDerivAt (fun v => arctan (v / α)) (1 / (1 + (u / α) ^ 2) * (1 / α)) u := by
      have := (hasDerivAt_arctan (u / α)).comp u ((hasDerivAt_id u).div_const α)
      simpa [Function.comp_def] using this
    have d := (((hasDerivAt_id u).mul dl).sub ((hasDerivAt_id u).const_mul 2)).add (da.const_mul (2 * α))
    refine d.congr_deriv ?_
    simp only [id]
    have hA' : A = -α ^ 2 := by linarith
    have hq' : 0 < u ^ 2 + α ^ 2 := by positivity
    have hden : 2 * α * (1 / (1 + (u / α) ^ 2) * (1 / α)) = 2 * α ^ 2 / (u ^ 2 + α ^ 2) := by
      field_simp; ring
    have hmid : u * (2 * u / (u ^ 2 - A)) = 2 * u ^ 2 / (u ^ 2 + α ^ 2) := by
      rw [hA', sub_neg_eq_add]; ring
    have hsum : 2 * u ^ 2 / (u ^ 2 + α ^ 2) + 2 * α ^ 2 / (u ^ 2 + α ^ 2) = 2 := by
      field_simp
    rw [hden, hmid]
    linarith

/-- `log(u² − A)` is interval integrable on every interval. -/
theorem intervalIntegrable_log_sq_sub (A a b : ℝ) :
    IntervalIntegrable (fun u => log (u ^ 2 - A)) volume a b := by
  have h : MeromorphicOn (fun u : ℝ => u ^ 2 - A) (uIcc a b) := by
    intro u _
    exact ((analyticAt_id.pow 2).sub analyticAt_const).meromorphicAt
  exact h.intervalIntegrable_log

/-- `u log(1 − A/u²) → 0`, in the form `u log(u² − A) − u log u² → 0`. -/
theorem tendsto_mul_log_ratio (A : ℝ) :
    Tendsto (fun u : ℝ => u * log (u ^ 2 - A) - u * log (u ^ 2)) atTop (𝓝 0) := by
  have hb : ∀ᶠ u : ℝ in atTop, |u * log (u ^ 2 - A) - u * log (u ^ 2)| ≤ 2 * |A| / u := by
    filter_upwards [eventually_ge_atTop (2 * |A| + 1)] with u hu
    have hA := abs_nonneg A
    have hu0 : 0 < u := by linarith
    have hu2 : 2 * |A| < u ^ 2 := by nlinarith
    have hq : 0 < u ^ 2 - A := by nlinarith [le_abs_self A]
    have hq2 : u ^ 2 / 2 ≤ u ^ 2 - A := by nlinarith [le_abs_self A]
    have hs : 0 < u ^ 2 := by positivity
    have e : u * log (u ^ 2 - A) - u * log (u ^ 2) = u * log ((u ^ 2 - A) / u ^ 2) := by
      rw [Real.log_div hq.ne' hs.ne']; ring
    rw [e, abs_mul, abs_of_pos hu0]
    set y := (u ^ 2 - A) / u ^ 2 with hy
    have hy0 : 0 < y := div_pos hq hs
    have up : log y ≤ y - 1 := log_le_sub_one_of_pos hy0
    have lo : 1 - 1 / y ≤ log y := by
      have := log_le_sub_one_of_pos (inv_pos.mpr hy0)
      rw [Real.log_inv] at this
      rw [one_div]; linarith
    have e1 : y - 1 = -A / u ^ 2 := by rw [hy]; field_simp; ring
    have e2 : 1 - 1 / y = -A / (u ^ 2 - A) := by rw [hy]; field_simp; ring
    have b1 : |-A / u ^ 2| ≤ 2 * |A| / u ^ 2 := by
      rw [abs_div, abs_neg, abs_of_pos hs]
      exact div_le_div_of_nonneg_right (by linarith) hs.le
    have b2 : |-A / (u ^ 2 - A)| ≤ 2 * |A| / u ^ 2 := by
      rw [abs_div, abs_neg, abs_of_pos hq, div_le_div_iff₀ hq hs]
      nlinarith
    have hlog : |log y| ≤ 2 * |A| / u ^ 2 := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (-A / (u ^ 2 - A))]
      · linarith [le_abs_self (-A / u ^ 2)]
    calc u * |log y| ≤ u * (2 * |A| / u ^ 2) := mul_le_mul_of_nonneg_left hlog hu0.le
      _ = 2 * |A| / u := by field_simp
  have ht : Tendsto (fun u : ℝ => 2 * |A| / u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hb) ht

/-- **The constant at infinity**: `lgAnti A u − (u log u² − 2u) → π√(−A)`. -/
theorem tendsto_lgAnti (A : ℝ) :
    Tendsto (fun u => lgAnti A u - (u * log (u ^ 2) - 2 * u)) atTop (𝓝 (π * √(-A))) := by
  by_cases hA : 0 ≤ A
  · rw [Real.sqrt_eq_zero_of_nonpos (by linarith : -A ≤ 0), mul_zero]
    set β := √A with hβ
    have hββ : β ^ 2 = A := Real.sq_sqrt hA
    have hβ0 : 0 ≤ β := Real.sqrt_nonneg A
    have hr : Tendsto (fun u : ℝ => β * (log (u + β) - log (u - β))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun u : ℝ => (u + β) / (u - β)) atTop (𝓝 1) := by
        have : Tendsto (fun u : ℝ => (1 + β / u) / (1 - β / u)) atTop (𝓝 ((1 + 0) / (1 - 0))) := by
          have hd : Tendsto (fun u : ℝ => β / u) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
          exact ((tendsto_const_nhds.add hd).div (tendsto_const_nhds.sub hd) (by norm_num))
        rw [show ((1 : ℝ) + 0) / (1 - 0) = 1 by norm_num] at this
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop (β + 1)] with u hu
        have hu0 : u ≠ 0 := by linarith
        field_simp
      have h2 := (h1.log one_ne_zero).const_mul β
      rw [Real.log_one, mul_zero] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop (β + 1)] with u hu
      rw [Real.log_div (by linarith) (by linarith)]
    have := (tendsto_mul_log_ratio A).add hr
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (β + 1)] with u hu
    simp only [lgAnti, if_pos hA, ← hβ]
    rw [show u ^ 2 - A = (u - β) * (u + β) by rw [← hββ]; ring,
      Real.log_mul (by linarith) (by linarith)]
    ring
  · push Not at hA
    set α := √(-A) with hα
    have hα0 : 0 < α := Real.sqrt_pos.mpr (by linarith)
    have ha : Tendsto (fun u : ℝ => 2 * α * arctan (u / α)) atTop (𝓝 (2 * α * (π / 2))) :=
      (tendsto_nhds_of_tendsto_nhdsWithin (tendsto_arctan_atTop.comp
        (tendsto_id.atTop_div_const hα0))).const_mul _
    have := (tendsto_mul_log_ratio A).add ha
    rw [zero_add, show 2 * α * (π / 2) = π * α by ring] at this
    refine this.congr' (Eventually.of_forall fun u => ?_)
    simp only [lgAnti, if_neg (not_le.mpr hA)]
    ring

/-- `lgAnti A − lgAnti B → π(√(−A) − √(−B))`. -/
theorem tendsto_lgAnti_sub (A B : ℝ) :
    Tendsto (fun u => lgAnti A u - lgAnti B u) atTop (𝓝 (π * √(-A) - π * √(-B))) :=
  ((tendsto_lgAnti A).sub (tendsto_lgAnti B)).congr fun u => by ring

/-- A point with `u² = A` and `u > 0` is `√A`. -/
theorem eq_sqrt_of_sq_eq {A u : ℝ} (hu : 0 < u) (h : u ^ 2 = A) : u = √A := by
  rw [← h, Real.sqrt_sq hu.le]

/-- FTC for `log(u² − A) − log(u² − B)` on `[0, Y]`. -/
theorem integral_log_sub (A B : ℝ) {Y : ℝ} (hY : 0 ≤ Y) :
    ∫ u in (0 : ℝ)..Y, (log (u ^ 2 - A) - log (u ^ 2 - B)) = lgAnti A Y - lgAnti B Y := by
  have h := integral_eq_of_hasDerivAt_off_countable_of_le (fun u => lgAnti A u - lgAnti B u)
    (fun u => log (u ^ 2 - A) - log (u ^ 2 - B)) hY (s := {√A, √B}) (by simp)
    ((continuous_lgAnti A).sub (continuous_lgAnti B)).continuousOn ?_
    ((intervalIntegrable_log_sq_sub A 0 Y).sub (intervalIntegrable_log_sq_sub B 0 Y))
  · rw [h, lgAnti_zero, lgAnti_zero]; ring
  · intro u hu
    simp only [Set.mem_sdiff, mem_Ioo, mem_insert_iff, mem_singleton_iff, not_or] at hu
    obtain ⟨⟨hu0, -⟩, hA, hB⟩ := hu
    exact (hasDerivAt_lgAnti hu0 fun h => hA (eq_sqrt_of_sq_eq hu0 h)).sub
      (hasDerivAt_lgAnti hu0 fun h => hB (eq_sqrt_of_sq_eq hu0 h))

/-- `log(u² − A) − log(u² − B)` is integrable on `(0, ∞)`. -/
theorem integrableOn_log_sub (A B : ℝ) :
    IntegrableOn (fun u => log (u ^ 2 - A) - log (u ^ 2 - B)) (Ioi 0) := by
  set R := |A| + |B| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hRA : ∀ u, R < u → A < u ^ 2 ∧ B < u ^ 2 := fun u hu => by
    have h1 : R ≤ u ^ 2 := by nlinarith [abs_nonneg A, abs_nonneg B]
    constructor <;> linarith [le_abs_self A, le_abs_self B, abs_nonneg A, abs_nonneg B]
  rw [← Ioc_union_Ioi_eq_Ioi hR0]
  refine IntegrableOn.union ?_ ?_
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR0).mp
      ((intervalIntegrable_log_sq_sub A 0 R).sub (intervalIntegrable_log_sq_sub B 0 R))
  · have hc : ContinuousWithinAt (fun u => lgAnti A u - lgAnti B u) (Ici R) R :=
      ((continuous_lgAnti A).sub (continuous_lgAnti B)).continuousWithinAt
    have hd : ∀ u ∈ Ioi R, HasDerivAt (fun u => lgAnti A u - lgAnti B u)
        (log (u ^ 2 - A) - log (u ^ 2 - B)) u := fun u hu => by
      have hu0 : 0 < u := by linarith [mem_Ioi.mp hu]
      obtain ⟨h1, h2⟩ := hRA u hu
      exact (hasDerivAt_lgAnti hu0 (by linarith)).sub (hasDerivAt_lgAnti hu0 (by linarith))
    rcases le_total A B with hAB | hAB
    · refine integrableOn_Ioi_deriv_of_nonneg hc hd (fun u hu => ?_) (tendsto_lgAnti_sub A B)
      obtain ⟨h1, h2⟩ := hRA u hu
      exact sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
    · refine integrableOn_Ioi_deriv_of_nonpos hc hd (fun u hu => ?_) (tendsto_lgAnti_sub A B)
      obtain ⟨h1, h2⟩ := hRA u hu
      exact sub_nonpos.mpr (Real.log_le_log (by linarith) (by linarith))

/-- **The Abel log integral**: `∫_0^∞ (log|u² − A| − log|u² − B|) du = π(√(−A)₊ − √(−B)₊)`. -/
theorem integral_log_sq_sub (A B : ℝ) :
    ∫ u in Ioi (0 : ℝ), (log (u ^ 2 - A) - log (u ^ 2 - B)) = π * √(-A) - π * √(-B) := by
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_log_sub A B) tendsto_id) ?_
  refine (tendsto_lgAnti_sub A B).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with Y hY
  rw [id, integral_log_sub A B hY]

end Cvs.Upstream.AbelLogIntegral

end
