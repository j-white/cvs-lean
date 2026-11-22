import Mathlib
import Cvs.Prolate.ConverseLevelCount
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Prolate.QuinticLevelComparison
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Prolate.SturmPolyGaussComparison

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Davis–Kahan for the even rungs

For even `F` with `(1−s²)F'' − 2sF' − c²s²F + μF = −R` on `[−1, 1]`, `(χ_k − μ)⟨F, h_k⟩ = ⟨R, h_k⟩`.
Parseval over the rungs then gives a level `χ` with `(χ − μ)²‖F‖² ≤ ‖R‖²`, and
`δ²‖F − ⟨F, h_k⟩h_k‖² ≤ ‖R‖²` when every other level is `δ` from `μ`. For the Hermite trials at
`c ≥ 31`, levels `0, 1, 2` are within `√(1.001κ'²)` of `μ₀, μ₂, μ₄`, gaps `2c − 19/4`, `2c − 203/4`.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped Interval

namespace Cvs.Prolate.EvenRungDavisKahan
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx lev rung rung₁ rung₂ rung_spec lev_spec lev_eq)
open Cvs.Prolate.EvenRungParseval (LevelIdx)
open Cvs.Prolate.HermiteTrialResiduals (pg pg₁ pg₂ herm rq mu kap2)

/-! ### Weighted square sums -/

section Sums

variable {ι : Type*} {a χ : ι → ℝ} {A B μ : ℝ}

/-- If `Σ aᵢ² = A > 0` and `Σ (χᵢ − μ)² aᵢ² = B`, some `i` has `(χᵢ − μ)² A ≤ B`. -/
theorem exists_sq_mul_le (ha : HasSum (fun i => a i ^ 2) A)
    (hb : HasSum (fun i => (χ i - μ) ^ 2 * a i ^ 2) B) (hA : 0 < A) :
    ∃ i, (χ i - μ) ^ 2 * A ≤ B := by
  by_contra h
  push Not at h
  have hlt : ∀ i, B / A < (χ i - μ) ^ 2 := fun i => (div_lt_iff₀ hA).2 (h i)
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
    by_contra h0
    push Not at h0
    have : HasSum (fun i => a i ^ 2) 0 := by simp [h0, hasSum_zero]
    exact hA.ne' (ha.unique this)
  have hs := hasSum_lt (f := fun i => B / A * a i ^ 2) (i := i₀)
    (fun i => mul_le_mul_of_nonneg_right (hlt i).le (sq_nonneg _))
    (mul_lt_mul_of_pos_right (hlt i₀) (by positivity)) (ha.mul_left (B / A)) hb
  rw [div_mul_cancel₀ _ hA.ne'] at hs
  exact lt_irrefl _ hs

/-- If every `i ≠ i₀` has `δ ≤ |χᵢ − μ|`, then `δ² (A − a_{i₀}²) ≤ B`. -/
theorem sq_mul_sub_sq_le (ha : HasSum (fun i => a i ^ 2) A)
    (hb : HasSum (fun i => (χ i - μ) ^ 2 * a i ^ 2) B) {i₀ : ι} {δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : ∀ i, i ≠ i₀ → δ ≤ |χ i - μ|) : δ ^ 2 * (A - a i₀ ^ 2) ≤ B := by
  classical
  have h1 := (ha.mul_left (δ ^ 2)).update i₀ 0
  have hle := hasSum_le (fun i => ?_) h1 hb
  · linarith
  · by_cases hi : i = i₀
    · subst hi
      simp only [Function.update_self]
      positivity
    · rw [Function.update_of_ne hi]
      have h2 : δ ^ 2 ≤ (χ i - μ) ^ 2 := by
        rw [← sq_abs (χ i - μ)]
        exact pow_le_pow_left₀ hδ (hgap i hi) 2
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

end Sums

/-! ### The Green identity against the rungs -/

section Green

variable {c μ : ℝ} {F F₁ F₂ R : ℝ → ℝ}

/-- The residual of a `C²` function under the prolate operator is continuous on `[−1, 1]`. -/
theorem continuousOn_of_ode (hF : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F (F₁ s) s)
    (hF₁ : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F₁ (F₂ s) s) (hF₂ : ContinuousOn F₂ [[(-1 : ℝ), 1]])
    (hode : ∀ s ∈ [[(-1 : ℝ), 1]],
      (1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s + μ * F s = -R s) :
    ContinuousOn R [[(-1 : ℝ), 1]] := by
  have hFc : ContinuousOn F [[(-1 : ℝ), 1]] :=
    fun s hs => (hF s hs).continuousAt.continuousWithinAt
  have hF₁c : ContinuousOn F₁ [[(-1 : ℝ), 1]] :=
    fun s hs => (hF₁ s hs).continuousAt.continuousWithinAt
  have h : ContinuousOn (fun s => -((1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s
      + μ * F s)) [[(-1 : ℝ), 1]] := by fun_prop
  exact h.congr fun s hs => by simp only [hode s hs, neg_neg]

/-- **Green identity**: `(χ_k − μ) ∫ F h_k = ∫ R h_k` for the rung `h_k` at the level `χ_k`. -/
theorem sub_mul_integral_mul_rung {k : ℕ} (hk : ∃ χ, IsLevelIdx c k χ)
    (hF : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F (F₁ s) s)
    (hF₁ : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F₁ (F₂ s) s) (hF₂ : ContinuousOn F₂ [[(-1 : ℝ), 1]])
    (hode : ∀ s ∈ [[(-1 : ℝ), 1]],
      (1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s + μ * F s = -R s) :
    (lev c k - μ) * ∫ s in (-1 : ℝ)..1, F s * rung c k s
      = ∫ s in (-1 : ℝ)..1, R s * rung c k s := by
  obtain ⟨hh, hh₁, hh₂, hang, -, -⟩ := rung_spec hk
  have ibp := Cvs.Prolate.SlepianCommutingRelation.ibp_weighted hh hh₁ hF hF₁ hh₂ hF₂
  have hRc := continuousOn_of_ode hF hF₁ hF₂ hode
  have hFc : ContinuousOn F [[(-1 : ℝ), 1]] :=
    fun s hs => (hF s hs).continuousAt.continuousWithinAt
  have hhc : ContinuousOn (rung c k) [[(-1 : ℝ), 1]] :=
    fun s hs => (hh s hs).continuousAt.continuousWithinAt
  have iA : IntervalIntegrable (fun s => rung c k s * (c ^ 2 * s ^ 2 * F s)) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (by fun_prop)
  have iF : IntervalIntegrable (fun s => F s * rung c k s) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (by fun_prop)
  have iR : IntervalIntegrable (fun s => R s * rung c k s) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (by fun_prop)
  have e1 : ∫ s in (-1 : ℝ)..1, rung c k s * ((1 - s ^ 2) * F₂ s - 2 * s * F₁ s)
      = (∫ s in (-1 : ℝ)..1, rung c k s * (c ^ 2 * s ^ 2 * F s))
        - μ * (∫ s in (-1 : ℝ)..1, F s * rung c k s) - ∫ s in (-1 : ℝ)..1, R s * rung c k s := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iA (iF.const_mul μ),
      ← intervalIntegral.integral_sub (iA.sub (iF.const_mul μ)) iR]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have := hode s hs
    linear_combination rung c k s * this
  have e2 : ∫ s in (-1 : ℝ)..1, ((1 - s ^ 2) * rung₂ c k s - 2 * s * rung₁ c k s) * F s
      = (∫ s in (-1 : ℝ)..1, rung c k s * (c ^ 2 * s ^ 2 * F s))
        - lev c k * ∫ s in (-1 : ℝ)..1, F s * rung c k s := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iA
      (iF.const_mul _)]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have := hang s hs
    linear_combination F s * this
  linarith

/-- **Parseval for the residual**: `Σ_k (χ_k − μ)² (∫ F h_k)² = ∫ R²` for even `F` and `R`. -/
theorem hasSum_sq_sub_mul_sq (hc : c ≠ 0) (hF : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F (F₁ s) s)
    (hF₁ : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F₁ (F₂ s) s) (hF₂ : ContinuousOn F₂ [[(-1 : ℝ), 1]])
    (hode : ∀ s ∈ [[(-1 : ℝ), 1]],
      (1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s + μ * F s = -R s)
    (hRe : ∀ s ∈ Icc (-1 : ℝ) 1, R (-s) = R s) :
    HasSum (fun k : LevelIdx c =>
        (lev c k - μ) ^ 2 * (∫ s in (-1 : ℝ)..1, F s * rung c k s) ^ 2)
      (∫ s in (-1 : ℝ)..1, R s ^ 2) := by
  have hRc := continuousOn_of_ode hF hF₁ hF₂ hode
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hRc
  convert Cvs.Prolate.EvenRungParseval.hasSum_sq_integral_mul_rung hc hRc hRe using 1
  funext k
  rw [← mul_pow, sub_mul_integral_mul_rung k.2 hF hF₁ hF₂ hode]

/-- `∫ (F − a h_k)² = ∫ F² − a²` with `a = ∫ F h_k`. -/
theorem integral_sub_mul_rung_sq {k : ℕ} (hk : ∃ χ, IsLevelIdx c k χ)
    (hFc : ContinuousOn F [[(-1 : ℝ), 1]]) :
    ∫ s in (-1 : ℝ)..1, (F s - (∫ t in (-1 : ℝ)..1, F t * rung c k t) * rung c k s) ^ 2
      = (∫ s in (-1 : ℝ)..1, F s ^ 2) - (∫ s in (-1 : ℝ)..1, F s * rung c k s) ^ 2 := by
  obtain ⟨hh, -, -, -, -, hsq⟩ := rung_spec hk
  have hhc : ContinuousOn (rung c k) [[(-1 : ℝ), 1]] :=
    fun s hs => (hh s hs).continuousAt.continuousWithinAt
  set a := ∫ s in (-1 : ℝ)..1, F s * rung c k s
  have i1 : IntervalIntegrable (fun s => F s ^ 2) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (by fun_prop)
  have i2 : IntervalIntegrable (fun s => F s * rung c k s) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (by fun_prop)
  have i3 : IntervalIntegrable (fun s => rung c k s ^ 2) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (hhc.pow 2)
  have e : ∀ s, (F s - a * rung c k s) ^ 2
      = F s ^ 2 - 2 * a * (F s * rung c k s) + a ^ 2 * rung c k s ^ 2 := fun s => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (i1.sub (i2.const_mul _)) (i3.const_mul _),
    intervalIntegral.integral_sub i1 (i2.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hsq]
  ring

/-- **A level near `μ`**: some even level `χ` has `(χ − μ)² ∫ F² ≤ ∫ R²`. -/
theorem exists_sq_mul_integral_sq_le (hc : c ≠ 0)
    (hF : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F (F₁ s) s)
    (hF₁ : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F₁ (F₂ s) s) (hF₂ : ContinuousOn F₂ [[(-1 : ℝ), 1]])
    (hode : ∀ s ∈ [[(-1 : ℝ), 1]],
      (1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s + μ * F s = -R s)
    (hFe : ∀ s ∈ Icc (-1 : ℝ) 1, F (-s) = F s) (hRe : ∀ s ∈ Icc (-1 : ℝ) 1, R (-s) = R s)
    (hpos : 0 < ∫ s in (-1 : ℝ)..1, F s ^ 2) :
    ∃ k χ, IsLevelIdx c k χ ∧
      (χ - μ) ^ 2 * ∫ s in (-1 : ℝ)..1, F s ^ 2 ≤ ∫ s in (-1 : ℝ)..1, R s ^ 2 := by
  have hFc : ContinuousOn F (Icc (-1) 1) := by
    rw [← uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact fun s hs => (hF s hs).continuousAt.continuousWithinAt
  obtain ⟨k, hk⟩ := exists_sq_mul_le
    (a := fun k : LevelIdx c => ∫ s in (-1 : ℝ)..1, F s * rung c k s) (χ := fun k => lev c k)
    (Cvs.Prolate.EvenRungParseval.hasSum_sq_integral_mul_rung hc hFc hFe)
    (hasSum_sq_sub_mul_sq hc hF hF₁ hF₂ hode hRe) hpos
  exact ⟨k, lev c k, lev_spec k.2, hk⟩

/-- **Davis–Kahan**: if every even level other than `χ_k` is at least `δ` from `μ`, then
`δ² ∫ (F − (∫ F h_k) h_k)² ≤ ∫ R²`. -/
theorem sq_mul_integral_sub_sq_le (hc : c ≠ 0)
    (hF : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F (F₁ s) s)
    (hF₁ : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F₁ (F₂ s) s) (hF₂ : ContinuousOn F₂ [[(-1 : ℝ), 1]])
    (hode : ∀ s ∈ [[(-1 : ℝ), 1]],
      (1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s + μ * F s = -R s)
    (hFe : ∀ s ∈ Icc (-1 : ℝ) 1, F (-s) = F s) (hRe : ∀ s ∈ Icc (-1 : ℝ) 1, R (-s) = R s)
    {k : ℕ} (hk : ∃ χ, IsLevelIdx c k χ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : ∀ j χ, IsLevelIdx c j χ → j ≠ k → δ ≤ |χ - μ|) :
    δ ^ 2 * ∫ s in (-1 : ℝ)..1, (F s - (∫ t in (-1 : ℝ)..1, F t * rung c k t) * rung c k s) ^ 2
      ≤ ∫ s in (-1 : ℝ)..1, R s ^ 2 := by
  have hFu : ContinuousOn F [[(-1 : ℝ), 1]] :=
    fun s hs => (hF s hs).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (Icc (-1) 1) := by
    rwa [← uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [integral_sub_mul_rung_sq hk hFu]
  exact sq_mul_sub_sq_le (a := fun k : LevelIdx c => ∫ s in (-1 : ℝ)..1, F s * rung c k s)
    (χ := fun k => lev c k) (i₀ := (⟨k, hk⟩ : LevelIdx c))
    (Cvs.Prolate.EvenRungParseval.hasSum_sq_integral_mul_rung hc hFc hFe)
    (hasSum_sq_sub_mul_sq hc hF hF₁ hF₂ hode hRe) hδ
    fun j hj => hgap j (lev c j) (lev_spec j.2) fun h => hj (Subtype.ext h)

end Green

/-! ### The Hermite trials `F_{2m}` -/

section Trials

variable {c : ℝ} {m : ℕ}

theorem mu_zero (c : ℝ) : mu c 0 = c - 3 / 4 := by norm_num [mu]

theorem mu_one (c : ℝ) : mu c 1 = 5 * c - 15 / 4 := by norm_num [mu]

theorem mu_two (c : ℝ) : mu c 2 = 9 * c - 43 / 4 := by norm_num [mu]

/-- `F_{2m}` has positive mass on `[−1, 1]`. -/
theorem integral_trial_sq_pos (c : ℝ) (hm : m ≤ 2) :
    0 < ∫ s in (-1 : ℝ)..1, pg c (herm m) s ^ 2 := by
  refine Cvs.Prolate.EvenRungsByIndex.integral_sq_pos (Cvs.Prolate.HermiteTrialResiduals.continuous_pg c _).continuousOn
    ⟨0, by norm_num, ?_⟩
  interval_cases m
  · simp [pg, herm]
  · norm_num [pg, Cvs.Prolate.HermiteTrialResiduals.herm_one]
  · norm_num [pg, Cvs.Prolate.HermiteTrialResiduals.herm_two]

/-- **A level near `μ_{2m}`**: some even level `χ` has
`(χ − μ_{2m})² ∫_{−1}^{1} F_{2m}² ≤ κ'² ‖F_{2m}‖²_{L²(ℝ)}`. -/
theorem exists_sq_sub_mu_mul_le (hc : 0 < c) (hm : m ≤ 2) :
    ∃ k χ, IsLevelIdx c k χ ∧ (χ - mu c m) ^ 2 * ∫ s in (-1 : ℝ)..1, pg c (herm m) s ^ 2
      ≤ kap2 m * ∫ s, pg c (herm m) s ^ 2 := by
  obtain ⟨k, χ, hχ, h⟩ := exists_sq_mul_integral_sq_le hc.ne'
    (fun s _ => Cvs.Prolate.HermiteTrialResiduals.hasDerivAt_pg c _ s) (fun s _ => Cvs.Prolate.HermiteTrialResiduals.hasDerivAt_pg₁ c _ s)
    (Cvs.Prolate.HermiteTrialResiduals.continuous_pg₂ c _).continuousOn (fun s _ => Cvs.Prolate.HermiteTrialResiduals.trial_ode hm c s)
    (fun s _ => Cvs.Prolate.HermiteTrialResiduals.pg_neg c _ s) (fun s _ => Cvs.Prolate.HermiteTrialResiduals.pg_neg c _ s) (integral_trial_sq_pos c hm)
  exact ⟨k, χ, hχ, h.trans (Cvs.Prolate.HermiteTrialResiduals.integral_resid_sq_Icc_le hc hm)⟩

/-- **Davis–Kahan for `F_{2m}`**: if every even level other than `χ_k` is at least `δ` from
`μ_{2m}`, then `δ² ∫_{−1}^{1} (F_{2m} − (∫ F_{2m} h_k) h_k)² ≤ κ'² ‖F_{2m}‖²_{L²(ℝ)}`. -/
theorem sq_mul_integral_sub_trial_le (hc : 0 < c) (hm : m ≤ 2) {k : ℕ}
    (hk : ∃ χ, IsLevelIdx c k χ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : ∀ j χ, IsLevelIdx c j χ → j ≠ k → δ ≤ |χ - mu c m|) :
    δ ^ 2 * ∫ s in (-1 : ℝ)..1,
        (pg c (herm m) s - (∫ t in (-1 : ℝ)..1, pg c (herm m) t * rung c k t) * rung c k s) ^ 2
      ≤ kap2 m * ∫ s, pg c (herm m) s ^ 2 :=
  (sq_mul_integral_sub_sq_le hc.ne' (fun s _ => Cvs.Prolate.HermiteTrialResiduals.hasDerivAt_pg c _ s)
    (fun s _ => Cvs.Prolate.HermiteTrialResiduals.hasDerivAt_pg₁ c _ s) (Cvs.Prolate.HermiteTrialResiduals.continuous_pg₂ c _).continuousOn
    (fun s _ => Cvs.Prolate.HermiteTrialResiduals.trial_ode hm c s) (fun s _ => Cvs.Prolate.HermiteTrialResiduals.pg_neg c _ s)
    (fun s _ => Cvs.Prolate.HermiteTrialResiduals.pg_neg c _ s) hk hδ hgap).trans (Cvs.Prolate.HermiteTrialResiduals.integral_resid_sq_Icc_le hc hm)

/-- For `c ≥ 31`, `1000 ‖F_{2m}‖²_{L²(ℝ)} ≤ 1001 ∫_{−1}^{1} F_{2m}²`. -/
theorem mul_integral_trial_sq_le (hc : 31 ≤ c) (hm : m ≤ 2) :
    1000 * ∫ s, pg c (herm m) s ^ 2 ≤ 1001 * ∫ s in (-1 : ℝ)..1, pg c (herm m) s ^ 2 := by
  have hc0 : 0 < c := by linarith
  have ht := Cvs.Prolate.HermiteTrialResiduals.integral_pg_sq_sub_le (half_pos hc0) (half_le_self hc0.le) (herm m)
  have h2 : c / (c / 2) = 2 := by field_simp
  have hs : √(π / (c / 2)) = √2 * √(π / c) := by
    rw [← Real.sqrt_mul (by norm_num)]
    congr 1
    field_simp
  rw [h2, hs, Cvs.Prolate.HermiteTrialResiduals.integral_trial_sq hc0 hm] at ht
  rw [Cvs.Prolate.HermiteTrialResiduals.integral_trial_sq hc0 hm]
  have hS : 0 < √(π / c) := Real.sqrt_pos.mpr (by positivity)
  have he : 80000 ≤ exp (c / 2) := by
    have h8 := Real.pow_div_factorial_le_exp (c / 2) (by positivity) 8
    have h31 : (31 / 2 : ℝ) ^ 8 ≤ (c / 2) ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
    have hf : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
    rw [hf] at h8
    norm_num at h31
    linarith
  have hexp : exp (-(c - c / 2)) ≤ 1 / 80000 := by
    rw [show -(c - c / 2) = -(c / 2) by ring, Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) he
  have hsq2 : √2 ≤ 1415 / 1000 := by
    calc √2 ≤ √((1415 / 1000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 1415 / 1000 := Real.sqrt_sq (by norm_num)
  have hg0 : 0 ≤ Cvs.Prolate.HermiteTrialResiduals.gE 2 (herm m ^ 2) := by
    interval_cases m
    · rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_zero]; norm_num
    · rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_one]; norm_num
    · rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_two]; norm_num
  have key : exp (-(c - c / 2)) * (Cvs.Prolate.HermiteTrialResiduals.gE 2 (herm m ^ 2) * (√2 * √(π / c)))
      ≤ 1 / 80000 * (Cvs.Prolate.HermiteTrialResiduals.gE 2 (herm m ^ 2) * (1415 / 1000 * √(π / c))) :=
    mul_le_mul hexp (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq2 hS.le) hg0)
      (by positivity) (by norm_num)
  interval_cases m
  · rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_zero] at key ht
    norm_num at ht key ⊢
    linarith
  · rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_one] at key ht
    norm_num [Nat.factorial] at ht key ⊢
    linarith
  · rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_two] at key ht
    norm_num [Nat.factorial] at ht key ⊢
    linarith

/-- **A level within `√(1.001 κ'²)` of `μ_{2m}`** for `c ≥ 31`. -/
theorem exists_sq_sub_mu_le (hc : 31 ≤ c) (hm : m ≤ 2) :
    ∃ k χ, IsLevelIdx c k χ ∧ (χ - mu c m) ^ 2 ≤ 1001 / 1000 * kap2 m := by
  obtain ⟨k, χ, hχ, hle⟩ := exists_sq_sub_mu_mul_le (by linarith : (0 : ℝ) < c) hm
  refine ⟨k, χ, hχ, le_of_mul_le_mul_right ?_ (integral_trial_sq_pos c hm)⟩
  have h1 := mul_integral_trial_sq_le hc hm
  have hk : 0 ≤ kap2 m := by unfold kap2; positivity
  nlinarith

/-- **The gap at `μ₀`**: every even level of index `j ≠ 0` lies at distance at least `2c − 19/4`
from `μ₀ = c − 3/4`. -/
theorem le_abs_sub_mu_zero (hc : 0 < c) {j : ℕ} {χ : ℝ} (hχ : IsLevelIdx c j χ) (hj : j ≠ 0) :
    2 * c - 19 / 4 ≤ |χ - mu c 0| := by
  have h1 := Cvs.Prolate.ConverseLevelCount.le_of_isLevelIdx_one_le hc.ne' hχ (Nat.one_le_iff_ne_zero.2 hj)
  have h2 := Cvs.Prolate.SturmPolyGaussComparison.abs_sub_le_gOne c
  rw [abs_of_pos hc] at h2
  rw [mu_zero]
  exact (by linarith : 2 * c - 19 / 4 ≤ χ - (c - 3 / 4)).trans (le_abs_self _)

/-- **`lev c 0` lies within `√(1.001 κ'₀²)` of `μ₀ = c − 3/4`** for `c ≥ 31`. -/
theorem sq_lev_zero_sub_le (hc : 31 ≤ c) : (lev c 0 - mu c 0) ^ 2 ≤ 1001 / 1000 * kap2 0 := by
  obtain ⟨k, χ, hχ, hle⟩ := exists_sq_sub_mu_le hc (m := 0) (by norm_num)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rwa [lev_eq hχ]
  · have hg := le_abs_sub_mu_zero (by linarith) hχ hk.ne'
    have : (2 * c - 19 / 4) ^ 2 ≤ (χ - mu c 0) ^ 2 := by
      rw [← sq_abs (χ - mu c 0)]
      exact pow_le_pow_left₀ (by linarith) hg 2
    rw [Cvs.Prolate.HermiteTrialResiduals.kap2_values.1] at hle
    nlinarith

/-- **`lev c 1 ≤ 5c + 1`** for `c ≥ 31`. -/
theorem lev_one_le (hc : 31 ≤ c) : lev c 1 ≤ 5 * c + 1 := by
  obtain ⟨j, χ, hχ, hle⟩ := exists_sq_sub_mu_le hc (m := 1) (by norm_num)
  rw [Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.1, mu_one] at hle
  have hb := abs_le_of_sq_le_sq' (hle.trans (by norm_num : _ ≤ (19 / 4 : ℝ) ^ 2)) (by norm_num)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exfalso
    have h0 := sq_lev_zero_sub_le hc
    rw [lev_eq hχ, Cvs.Prolate.HermiteTrialResiduals.kap2_values.1, mu_zero] at h0
    have hb0 := abs_le_of_sq_le_sq' (h0.trans (by norm_num : _ ≤ (5 / 4 : ℝ) ^ 2)) (by norm_num)
    linarith
  · rw [← lev_eq hχ] at hb
    exact (Cvs.Prolate.EvenRungsByIndex.lev_le ⟨χ, hχ⟩ hj).trans (by linarith)

/-- The levels of index `0` to `3` exist for `c ≥ 31`. -/
theorem exists_isLevelIdx_of_le_three (hc : 31 ≤ c) {k : ℕ} (hk : k ≤ 3) :
    ∃ χ, IsLevelIdx c k χ :=
  Cvs.Prolate.ConverseLevelCount.exists_isLevelIdx_of_le_three (by linarith [Real.pi_lt_d2]) hk

/-- **`lev c 2` lies within `√(1.001 κ'₄²)` of `μ₄ = 9c − 43/4`** for `c ≥ 31`. -/
theorem sq_lev_two_sub_le (hc : 31 ≤ c) : (lev c 2 - mu c 2) ^ 2 ≤ 1001 / 1000 * kap2 2 := by
  obtain ⟨j, χ, hχ, hle⟩ := exists_sq_sub_mu_le hc (m := 2) (by norm_num)
  have hb := abs_le_of_sq_le_sq' (hle.trans (by rw [Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.2]; norm_num :
    _ ≤ (1033 / 100 : ℝ) ^ 2)) (by norm_num)
  rw [mu_two] at hb
  rcases lt_trichotomy j 2 with hj | rfl | hj
  · exfalso
    have h1 : χ ≤ lev c 1 :=
      hχ.le (lev_spec (exists_isLevelIdx_of_le_three hc (by norm_num))) (by omega)
    linarith [lev_one_le hc]
  · rwa [lev_eq hχ]
  · exfalso
    have h3 := Cvs.Prolate.QuinticLevelComparison.le_of_isLevelIdx_three_le (by nlinarith) hχ hj
    have hg := Cvs.Prolate.QuinticLevelComparison.abs_sub_le_gThree c
    rw [abs_of_pos (by linarith)] at hg
    linarith

/-- **`lev c 1` lies within `√(1.001 κ'₂²)` of `μ₂ = 5c − 15/4`** for `c ≥ 31`. -/
theorem sq_lev_one_sub_le (hc : 31 ≤ c) : (lev c 1 - mu c 1) ^ 2 ≤ 1001 / 1000 * kap2 1 := by
  obtain ⟨j, χ, hχ, hle⟩ := exists_sq_sub_mu_le hc (m := 1) (by norm_num)
  have hb := abs_le_of_sq_le_sq' (hle.trans (by rw [Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.1]; norm_num :
    _ ≤ (19 / 4 : ℝ) ^ 2)) (by norm_num)
  rw [mu_one] at hb
  rcases lt_trichotomy j 1 with hj | rfl | hj
  · exfalso
    obtain rfl : j = 0 := by omega
    have h0 := sq_lev_zero_sub_le hc
    rw [lev_eq hχ, Cvs.Prolate.HermiteTrialResiduals.kap2_values.1, mu_zero] at h0
    have hb0 := abs_le_of_sq_le_sq' (h0.trans (by norm_num : _ ≤ (5 / 4 : ℝ) ^ 2)) (by norm_num)
    linarith
  · rwa [lev_eq hχ]
  · exfalso
    have h2 : lev c 2 ≤ χ := (lev_spec (exists_isLevelIdx_of_le_three hc (by norm_num))).le hχ hj
    have h4 := sq_lev_two_sub_le hc
    rw [Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.2, mu_two] at h4
    have hb4 := abs_le_of_sq_le_sq' (h4.trans (by norm_num : _ ≤ (1033 / 100 : ℝ) ^ 2))
      (by norm_num)
    linarith

/-- **The gap at `μ₄`**: for `c ≥ 31` every even level of index `j ≠ 2` is at least
`2c − 203/4` from `μ₄ = 9c − 43/4`. -/
theorem le_abs_sub_mu_two (hc : 31 ≤ c) {j : ℕ} {χ : ℝ} (hχ : IsLevelIdx c j χ) (hj : j ≠ 2) :
    2 * c - 203 / 4 ≤ |χ - mu c 2| := by
  rw [mu_two]
  rcases lt_or_gt_of_ne hj with hj | hj
  · have h1 : χ ≤ lev c 1 :=
      hχ.le (lev_spec (exists_isLevelIdx_of_le_three hc (by norm_num))) (by omega)
    have := lev_one_le hc
    exact (by linarith : 2 * c - 203 / 4 ≤ -(χ - (9 * c - 43 / 4))).trans (neg_le_abs _)
  · have h3 := Cvs.Prolate.QuinticLevelComparison.le_of_isLevelIdx_three_le (by nlinarith) hχ hj
    have hg := Cvs.Prolate.QuinticLevelComparison.abs_sub_le_gThree c
    rw [abs_of_pos (by linarith)] at hg
    exact (by linarith : 2 * c - 203 / 4 ≤ χ - (9 * c - 43 / 4)).trans (le_abs_self _)

/-- **Davis–Kahan at `μ₀`**: `(2c − 19/4)² ∫_{−1}^{1} (F₀ − a₀ h₀)² ≤ κ'₀² ‖F₀‖²_{L²(ℝ)}` with
`a₀ = ∫ F₀ h₀`, for `c ≥ 19/8`. -/
theorem sq_mul_integral_sub_rung_zero_le (hc : 19 / 8 ≤ c) :
    (2 * c - 19 / 4) ^ 2 * ∫ s in (-1 : ℝ)..1,
        (pg c (herm 0) s - (∫ t in (-1 : ℝ)..1, pg c (herm 0) t * rung c 0 t) * rung c 0 s) ^ 2
      ≤ kap2 0 * ∫ s, pg c (herm 0) s ^ 2 :=
  sq_mul_integral_sub_trial_le (by linarith) (by norm_num)
    (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c) (by linarith)
    fun _ _ hχ hj => le_abs_sub_mu_zero (by linarith) hχ hj

/-- **Davis–Kahan at `μ₄`**: `(2c − 203/4)² ∫_{−1}^{1} (F₄ − a₄ h₄)² ≤ κ'₄² ‖F₄‖²_{L²(ℝ)}` with
`a₄ = ∫ F₄ h₄` and `h₄ = rung c 2`, for `c ≥ 31`. -/
theorem sq_mul_integral_sub_rung_two_le (hc : 31 ≤ c) :
    (2 * c - 203 / 4) ^ 2 * ∫ s in (-1 : ℝ)..1,
        (pg c (herm 2) s - (∫ t in (-1 : ℝ)..1, pg c (herm 2) t * rung c 2 t) * rung c 2 s) ^ 2
      ≤ kap2 2 * ∫ s, pg c (herm 2) s ^ 2 :=
  sq_mul_integral_sub_trial_le (by linarith) le_rfl
    (exists_isLevelIdx_of_le_three hc (by norm_num)) (by linarith)
    fun _ _ hχ hj => le_abs_sub_mu_two hc hχ hj

end Trials

end Cvs.Prolate.EvenRungDavisKahan
