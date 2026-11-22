import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.QuarticHermiteWindowPhi
import Cvs.Approximant.StripApproxFromHermite
import Cvs.Finite.SymmetricModeSet
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Route.GroundRouteJointGap
import Cvs.WeilForm.OddPoleTermBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The spine profile is the quartic Hermite profile up to `O(c^{−3/4})`

A sign `σ` puts `h₀`, `h₄` within `κ'/δ` of the unit trials `f₀`, `f₄`. With `G = h₄ − αh₀`,
`g_H = F₄ − 12F₀` and `a₄ = ∫ F₄ h₄`, at `c = 2πx` with `x ≥ 16` we get
`∫₀¹ (G − g_H/a₄)² ≤ (80217/4) x^{−3/2}` and `|1/a₄| ≥ x^{1/4}/20`, so Connes' vectors are strip
approximable.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped Interval

namespace Cvs.Approximant.SpineNearQuarticHermite
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx lev rung rung_spec)
open Cvs.Prolate.HermiteTrialResiduals (pg herm kap2)

/-! ### Cauchy–Schwarz on `[−1, 1]` and the rungs -/

/-- `(∫_{−1}^{1} f)² ≤ 2 ∫_{−1}^{1} f²` for `f` continuous on `[−1, 1]`. -/
theorem sq_integral_le {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    (∫ s in (-1 : ℝ)..1, f s) ^ 2 ≤ 2 * ∫ s in (-1 : ℝ)..1, f s ^ 2 := by
  have hf' : ContinuousOn f [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  have h := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le (by norm_num : (-1 : ℝ) ≤ 1) (f := f)
    (w := fun _ => 1) (hf'.pow 2).intervalIntegrable (by simp)
    (by simpa using hf'.intervalIntegrable)
  norm_num at h
  linarith

/-- Every rung is continuous on `[−1, 1]`. -/
theorem continuousOn_rung (c : ℝ) (k : ℕ) : ContinuousOn (rung c k) (Icc (-1) 1) :=
  (Cvs.Approximant.DeepIndexSpineSpan.continuousOn_rawRung c (lev c k)).div_const _

/-- **Sign alignment**: if `∫_{−1}^{1} F² ≤ N²`, a sign `σ` gives
`∫ (h_k − σF/N)² ≤ E/N² + (1 − a²/N²)²` with `a = ∫ F h_k` and `E = ∫ (F − a h_k)²`. -/
theorem exists_sign_integral_sub_sq_le {c : ℝ} {k : ℕ} (hk : ∃ χ, IsLevelIdx c k χ)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc (-1) 1)) {N : ℝ} (hN : 0 < N)
    (hI : ∫ s in (-1 : ℝ)..1, F s ^ 2 ≤ N ^ 2) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∫ s in (-1 : ℝ)..1, (rung c k s - σ * (F s / N)) ^ 2
      ≤ (∫ s in (-1 : ℝ)..1,
            (F s - (∫ t in (-1 : ℝ)..1, F t * rung c k t) * rung c k s) ^ 2) / N ^ 2
        + (1 - (∫ s in (-1 : ℝ)..1, F s * rung c k s) ^ 2 / N ^ 2) ^ 2 := by
  have hFu : ContinuousOn F [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  have hhu : ContinuousOn (rung c k) [[(-1 : ℝ), 1]] := by
    rw [uIcc_of_le (by norm_num)]; exact continuousOn_rung c k
  rw [Cvs.Prolate.EvenRungDavisKahan.integral_sub_mul_rung_sq hk hFu]
  obtain ⟨-, -, -, -, -, hsq⟩ := rung_spec hk
  set a := ∫ s in (-1 : ℝ)..1, F s * rung c k s
  set I := ∫ s in (-1 : ℝ)..1, F s ^ 2
  have hE : 0 ≤ I - a ^ 2 := by
    rw [← Cvs.Prolate.EvenRungDavisKahan.integral_sub_mul_rung_sq hk hFu]
    exact intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  set σ : ℝ := if 0 ≤ a then 1 else -1 with hσ
  have hσa : σ * a = |a| := by
    rw [hσ]; split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hσ2 : σ ^ 2 = 1 := by rw [hσ]; split_ifs <;> norm_num
  refine ⟨σ, by rw [hσ]; split_ifs <;> simp, ?_⟩
  have i1 : IntervalIntegrable (fun s => rung c k s ^ 2) volume (-1) 1 :=
    (hhu.pow 2).intervalIntegrable
  have i2 : IntervalIntegrable (fun s => F s * rung c k s) volume (-1) 1 :=
    (hFu.mul hhu).intervalIntegrable
  have i3 : IntervalIntegrable (fun s => F s ^ 2) volume (-1) 1 := (hFu.pow 2).intervalIntegrable
  have e : ∀ s, (rung c k s - σ * (F s / N)) ^ 2
      = rung c k s ^ 2 - 2 * σ / N * (F s * rung c k s) + σ ^ 2 / N ^ 2 * F s ^ 2 := fun s => by
    field_simp; ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (i1.sub (i2.const_mul _)) (i3.const_mul _),
    intervalIntegral.integral_sub i1 (i2.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hsq, hσ2]
  have hN2 : 0 < N ^ 2 := by positivity
  set r := |a| / N with hr
  have hr0 : 0 ≤ r := by positivity
  have hra : r ^ 2 = a ^ 2 / N ^ 2 := by rw [hr, div_pow, sq_abs]
  have hr1 : r ≤ 1 := by
    have : r ^ 2 ≤ 1 := by rw [hra, div_le_one hN2]; linarith
    nlinarith
  have hlhs : 1 - 2 * σ / N * a + 1 / N ^ 2 * I = (1 - r) ^ 2 + (I - a ^ 2) / N ^ 2 := by
    have h2 : 2 * σ / N * a = 2 * |a| / N := by rw [← hσa]; ring
    rw [h2, hr]
    field_simp; nlinarith [sq_abs a]
  rw [hlhs, ← hra]
  have : (1 - r) ^ 2 ≤ (1 - r ^ 2) ^ 2 := by
    have h1 : 0 ≤ 1 - r := by linarith
    have : (1 - r) ^ 2 * 1 ≤ (1 - r) ^ 2 * (1 + r) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    nlinarith
  linarith

/-! ### The rungs `h₀` and `h₄` against the unit trials -/

section Trials

variable {c : ℝ} {m : ℕ}

/-- `∫_{−1}^{1} F_{2m}² ≤ ‖F_{2m}‖²_{L²(ℝ)}`. -/
theorem integral_trial_sq_Icc_le (hc : 0 < c) (m : ℕ) :
    ∫ s in (-1 : ℝ)..1, pg c (herm m) s ^ 2 ≤ ∫ s, pg c (herm m) s ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  exact setIntegral_le_integral (Cvs.Prolate.HermiteTrialResiduals.integrable_pg_sq hc _)
    (Eventually.of_forall fun w => sq_nonneg _)

/-- If `δ² ∫ (F_{2m} − a h_k)² ≤ κ'² ‖F_{2m}‖²`, a sign `σ` gives, with `f = F_{2m}/‖F_{2m}‖`,
`∫ (h_k − σ f)² ≤ κ'²/δ² + (1 − ∫_{−1}^{1} f² + κ'²/δ²)²`. -/
theorem exists_sign_integral_rung_sub_trial_sq_le (hc : 0 < c) (hm : m ≤ 2) {k : ℕ}
    (hk : ∃ χ, IsLevelIdx c k χ) {δ : ℝ} (hδ : 0 < δ)
    (hDK : δ ^ 2 * ∫ s in (-1 : ℝ)..1,
        (pg c (herm m) s - (∫ t in (-1 : ℝ)..1, pg c (herm m) t * rung c k t) * rung c k s) ^ 2
      ≤ kap2 m * ∫ s, pg c (herm m) s ^ 2) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∫ s in (-1 : ℝ)..1,
        (rung c k s - σ * (pg c (herm m) s / √(∫ t, pg c (herm m) t ^ 2))) ^ 2
      ≤ kap2 m / δ ^ 2 + (1 - (∫ s in (-1 : ℝ)..1, pg c (herm m) s ^ 2)
          / (∫ s, pg c (herm m) s ^ 2) + kap2 m / δ ^ 2) ^ 2 := by
  set F := pg c (herm m)
  set M := ∫ s, F s ^ 2
  have hM : 0 < M := by
    simp only [M, F]; rw [Cvs.Prolate.HermiteTrialResiduals.integral_trial_sq hc hm]; positivity
  have hN : 0 < √M := Real.sqrt_pos.mpr hM
  have hN2 : √M ^ 2 = M := Real.sq_sqrt hM.le
  have hJ : ∫ s in (-1 : ℝ)..1, F s ^ 2 ≤ √M ^ 2 := by
    rw [hN2]; exact integral_trial_sq_Icc_le hc m
  have hFc : ContinuousOn F (Icc (-1) 1) := (Cvs.Prolate.HermiteTrialResiduals.continuous_pg c _).continuousOn
  obtain ⟨σ, hσ, h⟩ := exists_sign_integral_sub_sq_le hk hFc hN hJ
  refine ⟨σ, hσ, h.trans ?_⟩
  have hFu : ContinuousOn F [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  rw [hN2, Cvs.Prolate.EvenRungDavisKahan.integral_sub_mul_rung_sq hk hFu] at *
  set a := ∫ s in (-1 : ℝ)..1, F s * rung c k s
  set J := ∫ s in (-1 : ℝ)..1, F s ^ 2
  have hE0 : 0 ≤ J - a ^ 2 := by
    rw [← Cvs.Prolate.EvenRungDavisKahan.integral_sub_mul_rung_sq hk hFu]
    exact intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  have hE : (J - a ^ 2) / M ≤ kap2 m / δ ^ 2 := by
    rw [div_le_div_iff₀ hM (by positivity)]; linarith
  have hJM : J ≤ M := hN2 ▸ hJ
  have h1 : 0 ≤ 1 - a ^ 2 / M := by
    rw [sub_nonneg, div_le_one hM]; linarith
  have h2 : 1 - a ^ 2 / M = 1 - J / M + (J - a ^ 2) / M := by field_simp; ring
  have h3 : 1 - a ^ 2 / M ≤ 1 - J / M + kap2 m / δ ^ 2 := by rw [h2]; linarith
  have := pow_le_pow_left₀ h1 h3 2
  linarith

/-- **`h₀` is the unit ground trial up to `κ'₀/δ₀`**: for `c > 19/8` a sign `σ` gives
`∫ (h₀ − σf₀)² ≤ κ'₀²/δ₀² + (1 − ∫_{−1}^{1} f₀² + κ'₀²/δ₀²)²` with `δ₀ = 2c − 19/4`. -/
theorem exists_sign_integral_rung_zero_sub_sq_le (hc : 19 / 8 < c) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∫ s in (-1 : ℝ)..1,
        (rung c 0 s - σ * (pg c (herm 0) s / √(∫ t, pg c (herm 0) t ^ 2))) ^ 2
      ≤ kap2 0 / (2 * c - 19 / 4) ^ 2 + (1 - (∫ s in (-1 : ℝ)..1, pg c (herm 0) s ^ 2)
          / (∫ s, pg c (herm 0) s ^ 2) + kap2 0 / (2 * c - 19 / 4) ^ 2) ^ 2 :=
  exists_sign_integral_rung_sub_trial_sq_le (by linarith) (by norm_num)
    (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c) (by linarith)
    (Cvs.Prolate.EvenRungDavisKahan.sq_mul_integral_sub_rung_zero_le hc.le)

/-- **`h₄` is the unit quartic trial up to `κ'₄/δ₄`**: for `c ≥ 31` a sign `σ` gives
`∫ (h₄ − σf₄)² ≤ κ'₄²/δ₄² + (1 − ∫_{−1}^{1} f₄² + κ'₄²/δ₄²)²` with `δ₄ = 2c − 203/4`. -/
theorem exists_sign_integral_rung_two_sub_sq_le (hc : 31 ≤ c) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∫ s in (-1 : ℝ)..1,
        (rung c 2 s - σ * (pg c (herm 2) s / √(∫ t, pg c (herm 2) t ^ 2))) ^ 2
      ≤ kap2 2 / (2 * c - 203 / 4) ^ 2 + (1 - (∫ s in (-1 : ℝ)..1, pg c (herm 2) s ^ 2)
          / (∫ s, pg c (herm 2) s ^ 2) + kap2 2 / (2 * c - 203 / 4) ^ 2) ^ 2 :=
  exists_sign_integral_rung_sub_trial_sq_le (by linarith) le_rfl
    (Cvs.Prolate.EvenRungDavisKahan.exists_isLevelIdx_of_le_three hc (by norm_num)) (by linarith)
    (Cvs.Prolate.EvenRungDavisKahan.sq_mul_integral_sub_rung_two_le hc)

end Trials

/-! ### The profile identity -/

section Identity

/-- With `D = a₀I₀` and `P = a₄I₂`, `a₄D((h₂ − (I₂/I₀)h₀) − (F₄ − 12F₀)/a₄)` equals
`−D(F₄ − a₄h₂) + P(F₀ − a₀h₀) + (12D − P)F₀`. -/
theorem mul_profile_sub_eq {a₀ a₄ I₀ I₂ F₀ F₄ h₀ h₂ : ℝ} (ha : a₄ ≠ 0) (hD : a₀ * I₀ ≠ 0) :
    a₄ * (a₀ * I₀) * ((h₂ - I₂ / I₀ * h₀) - (F₄ - 12 * F₀) / a₄)
      = -(a₀ * I₀) * (F₄ - a₄ * h₂) + a₄ * I₂ * (F₀ - a₀ * h₀)
        + (12 * (a₀ * I₀) - a₄ * I₂) * F₀ := by
  have hI : I₀ ≠ 0 := right_ne_zero_of_mul hD
  field_simp
  ring

/-- A square integral over `[0, 1]` is at most the integral over `[−1, 1]` of a pointwise bound. -/
theorem setIntegral_sq_le {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hg : ContinuousOn g (Icc (-1) 1)) (h : ∀ u ∈ Icc (-1 : ℝ) 1, f u ^ 2 ≤ g u) :
    ∫ u in Icc (0 : ℝ) 1, f u ^ 2 ≤ ∫ u in (-1 : ℝ)..1, g u := by
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := Icc_subset_Icc (by norm_num) le_rfl
  have hgi : IntegrableOn g (Icc (-1) 1) := hg.integrableOn_Icc
  calc ∫ u in Icc (0 : ℝ) 1, f u ^ 2 ≤ ∫ u in Icc (0 : ℝ) 1, g u :=
        setIntegral_mono_on ((hf.mono hsub).pow 2).integrableOn_Icc (hgi.mono_set hsub)
          measurableSet_Icc fun u hu => h u (hsub hu)
    _ ≤ ∫ u in Icc (-1 : ℝ) 1, g u :=
        setIntegral_mono_set hgi ((ae_restrict_iff' measurableSet_Icc).2
          (Eventually.of_forall fun u hu => (sq_nonneg _).trans (h u hu))) (Eventually.of_forall fun u hu => hsub hu)
    _ = ∫ u in (-1 : ℝ)..1, g u := by
        rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]

/-- **The profile defect**: with `D = a₀I₀`, `P = a₄I₂`, `e₀ = F₀ − a₀h₀`, `e₄ = F₄ − a₄h₂`,
`∫₀¹ ((h₂ − (I₂/I₀)h₀) − (F₄ − 12F₀)/a₄)² ≤ 3(D²∫e₄² + P²∫e₀² + (12D − P)²∫F₀²)/(a₄D)²`. -/
theorem integral_profile_sub_sq_le {F₀ F₄ h₀ h₂ : ℝ → ℝ} (hF₀ : ContinuousOn F₀ (Icc (-1) 1))
    (hF₄ : ContinuousOn F₄ (Icc (-1) 1)) (hh₀ : ContinuousOn h₀ (Icc (-1) 1))
    (hh₂ : ContinuousOn h₂ (Icc (-1) 1)) {a₀ a₄ I₀ I₂ : ℝ} (ha : a₄ ≠ 0) (hD : a₀ * I₀ ≠ 0) :
    ∫ u in Icc (0 : ℝ) 1, ((h₂ u - I₂ / I₀ * h₀ u) - (F₄ u - 12 * F₀ u) / a₄) ^ 2
      ≤ 3 / (a₄ * (a₀ * I₀)) ^ 2 * ((a₀ * I₀) ^ 2 * (∫ s in (-1 : ℝ)..1, (F₄ s - a₄ * h₂ s) ^ 2)
        + (a₄ * I₂) ^ 2 * (∫ s in (-1 : ℝ)..1, (F₀ s - a₀ * h₀ s) ^ 2)
        + (12 * (a₀ * I₀) - a₄ * I₂) ^ 2 * ∫ s in (-1 : ℝ)..1, F₀ s ^ 2) := by
  set D := a₀ * I₀
  set P := a₄ * I₂
  set Q := 12 * D - P
  have hK : (0 : ℝ) < (a₄ * D) ^ 2 := by positivity
  have hfc : ContinuousOn (fun u => (h₂ u - I₂ / I₀ * h₀ u) - (F₄ u - 12 * F₀ u) / a₄)
      (Icc (-1) 1) :=
    (hh₂.sub (continuousOn_const.mul hh₀)).sub ((hF₄.sub (continuousOn_const.mul hF₀)).div_const a₄)
  have hgc : ContinuousOn (fun u => 3 / (a₄ * D) ^ 2 * (D ^ 2 * (F₄ u - a₄ * h₂ u) ^ 2
      + P ^ 2 * (F₀ u - a₀ * h₀ u) ^ 2 + Q ^ 2 * F₀ u ^ 2)) (Icc (-1) 1) :=
    continuousOn_const.mul (((continuousOn_const.mul ((hF₄.sub (continuousOn_const.mul hh₂)).pow 2)).add
      (continuousOn_const.mul ((hF₀.sub (continuousOn_const.mul hh₀)).pow 2))).add
      (continuousOn_const.mul (hF₀.pow 2)))
  have hle := setIntegral_sq_le (f := fun u => (h₂ u - I₂ / I₀ * h₀ u) - (F₄ u - 12 * F₀ u) / a₄)
    (g := fun u => 3 / (a₄ * D) ^ 2 * (D ^ 2 * (F₄ u - a₄ * h₂ u) ^ 2
      + P ^ 2 * (F₀ u - a₀ * h₀ u) ^ 2 + Q ^ 2 * F₀ u ^ 2)) hfc hgc
    fun u _ => by
      have e := mul_profile_sub_eq (F₀ := F₀ u) (F₄ := F₄ u) (h₀ := h₀ u) (h₂ := h₂ u)
        (I₂ := I₂) ha hD
      set x := (h₂ u - I₂ / I₀ * h₀ u) - (F₄ u - 12 * F₀ u) / a₄
      set y₁ := F₄ u - a₄ * h₂ u
      set y₂ := F₀ u - a₀ * h₀ u
      have hx : x ^ 2 = (-D * y₁ + P * y₂ + Q * F₀ u) ^ 2 / (a₄ * D) ^ 2 := by
        rw [← e]; field_simp; simp only [D]; ring
      rw [hx, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hK]
      nlinarith [sq_nonneg (D * y₁ + P * y₂), sq_nonneg (D * y₁ + Q * F₀ u),
        sq_nonneg (P * y₂ - Q * F₀ u)]
  refine hle.trans (le_of_eq ?_)
  have c₀ : ContinuousOn F₀ [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  have c₄ : ContinuousOn F₄ [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  have d₀ : ContinuousOn h₀ [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  have d₂ : ContinuousOn h₂ [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  have i₁ : IntervalIntegrable (fun s => (F₄ s - a₄ * h₂ s) ^ 2) volume (-1) 1 :=
    ((c₄.sub (continuousOn_const.mul d₂)).pow 2).intervalIntegrable
  have i₂ : IntervalIntegrable (fun s => (F₀ s - a₀ * h₀ s) ^ 2) volume (-1) 1 :=
    ((c₀.sub (continuousOn_const.mul d₀)).pow 2).intervalIntegrable
  have i₃ : IntervalIntegrable (fun s => F₀ s ^ 2) volume (-1) 1 :=
    (c₀.pow 2).intervalIntegrable
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    ((i₁.const_mul _).add (i₂.const_mul _)) (i₃.const_mul _),
    intervalIntegral.integral_add (i₁.const_mul _) (i₂.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

end Identity

/-! ### The quartic Hermite profile -/

section Hermite

variable {c : ℝ}

open Polynomial in
/-- `g_H` is the trial of `16t² − 48t`. -/
theorem gH_eq_pg (c w : ℝ) : Cvs.Approximant.QuarticHermiteWindowPhi.gH c w = pg c (16 * X ^ 2 - 48 * X) w := by
  simp only [Cvs.Approximant.QuarticHermiteWindowPhi.gH, pg, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
  congr 1
  · ring
  · congr 1; ring

/-- `g_H = F₄ − 12F₀`. -/
theorem gH_eq_sub (c w : ℝ) : Cvs.Approximant.QuarticHermiteWindowPhi.gH c w = pg c (herm 2) w - 12 * pg c (herm 0) w := by
  rw [← Cvs.Prolate.HermiteTrialResiduals.gH_eq]; unfold Cvs.Approximant.QuarticHermiteWindowPhi.gH; congr 2; ring

open Polynomial in
/-- **The cut of `g_H`**: `|∫_{−1}^{1} g_H| ≤ 576 √(π/c) e^{−c/4}`. -/
theorem abs_integral_gH_le (hc : 0 < c) :
    |∫ s in (-1 : ℝ)..1, Cvs.Approximant.QuarticHermiteWindowPhi.gH c s| ≤ 576 * √(π / c) * exp (-(c / 4)) := by
  have hμ : 0 < c / 4 := by positivity
  have h := Cvs.Prolate.HermiteTrialResiduals.abs_integral_pg_sub_le (c := c) hμ (by linarith) (16 * X ^ 2 - 48 * X)
  have h0 : Cvs.Prolate.HermiteTrialResiduals.gE 2 (16 * X ^ 2 - 48 * X : ℝ[X]) = 0 := by
    rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 3) (fun k => ([0, -48, 16] : List ℝ).getD k 0)
      (fun t => by simp [Finset.sum_range_succ]; ring)]
    simp [Cvs.Prolate.HermiteTrialResiduals.gm, Finset.sum_range_succ, Nat.factorial]; norm_num
  rw [Cvs.Prolate.HermiteTrialResiduals.integral_pg hc, h0, zero_mul, zero_sub, abs_neg,
    show -(c / 2 - c / 4) = -(c / 4) by ring] at h
  simp_rw [← gH_eq_pg] at h
  have hb : ∫ w, |(16 * X ^ 2 - 48 * X : ℝ[X]).eval (c * w ^ 2)| * exp (-(c / 4) * w ^ 2)
      ≤ 576 * √(π / c) := by
    have hi := Cvs.Prolate.HermiteTrialResiduals.integrable_eval_mul_gaussian hμ c (16 * X ^ 2 + 48 * X)
    have hi' : Integrable fun w =>
        |(16 * X ^ 2 - 48 * X : ℝ[X]).eval (c * w ^ 2)| * exp (-(c / 4) * w ^ 2) := by
      refine (Cvs.Prolate.HermiteTrialResiduals.integrable_eval_mul_gaussian hμ c (16 * X ^ 2 - 48 * X)).abs.congr
        (Eventually.of_forall fun w => ?_)
      simp only [abs_mul, abs_of_pos (exp_pos _)]
    refine (integral_mono hi' hi fun w => ?_).trans (le_of_eq ?_)
    · refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
      have ht : 0 ≤ c * w ^ 2 := by positivity
      simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
      rw [abs_le]; constructor <;> nlinarith
    · rw [Cvs.Prolate.HermiteTrialResiduals.integral_eval_mul_gaussian hμ, show c / (c / 4) = 4 by field_simp,
        Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 3) (fun k => ([0, 48, 16] : List ℝ).getD k 0)
          (fun t => by simp [Finset.sum_range_succ]; ring),
        show π / (c / 4) = 2 ^ 2 * (π / c) by field_simp; ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
      simp [Cvs.Prolate.HermiteTrialResiduals.gm, Finset.sum_range_succ, Nat.factorial]; ring
  calc _ ≤ _ := h
    _ ≤ exp (-(c / 4)) * (576 * √(π / c)) := mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = _ := by ring

/-- `∫_{−1}^{1} F₀ ≥ √2 √(π/c) − 2√(π/c) e^{−c/4}`. -/
theorem integral_trial_zero_ge (hc : 0 < c) :
    √2 * √(π / c) - 2 * √(π / c) * exp (-(c / 4)) ≤ ∫ s in (-1 : ℝ)..1, pg c (herm 0) s := by
  have hμ : 0 < c / 4 := by positivity
  have h := Cvs.Prolate.HermiteTrialResiduals.abs_integral_pg_sub_le (c := c) hμ (by linarith) (herm 0)
  rw [Cvs.Prolate.HermiteTrialResiduals.integral_trial hc (m := 0) (by norm_num), show -(c / 2 - c / 4) = -(c / 4) by ring] at h
  have he : ∫ w, |(herm 0).eval (c * w ^ 2)| * exp (-(c / 4) * w ^ 2) = 2 * √(π / c) := by
    simp only [Cvs.Prolate.HermiteTrialResiduals.herm, Polynomial.eval_one, abs_one, one_mul]
    rw [integral_gaussian, show π / (c / 4) = 2 ^ 2 * (π / c) by field_simp; ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [he, show 2 * π / c = 2 * (π / c) by ring, Real.sqrt_mul (by norm_num)] at h
  norm_num at h
  have := (abs_le.mp h).2
  linarith

end Hermite

/-! ### The spine profile against `g_H` -/

section Profile

variable {c : ℝ}

/-- The overlap `a₄ = ∫_{−1}^{1} F₄ h₄` of the quartic trial with the rung `h₄ = rung c 2`. -/
def overlap (c : ℝ) : ℝ := ∫ s in (-1 : ℝ)..1, pg c (herm 2) s * rung c 2 s

/-- The spine profile of `{1}` is `h₄ − α h₀`. -/
theorem spineG_one (c s : ℝ) :
    Cvs.Approximant.DeepIndexSpineSpan.spineG c (S := {1}) (fun _ => 1) s = rung c 2 s - Cvs.Approximant.DeepIndexSpineSpan.alpha c 1 * rung c 0 s := by
  simp [Cvs.Approximant.DeepIndexSpineSpan.spineG]

/-- **The overlap**: for `c ≥ 100`, `192 √(π/c) ≤ a₄² ≤ 384 √(π/c)`. -/
theorem sq_overlap_mem (hc : 100 ≤ c) :
    192 * √(π / c) ≤ overlap c ^ 2 ∧ overlap c ^ 2 ≤ 384 * √(π / c) := by
  have hc0 : 0 < c := by linarith
  have uF₄ : ContinuousOn (pg c (herm 2)) [[(-1 : ℝ), 1]] :=
    (Cvs.Prolate.HermiteTrialResiduals.continuous_pg c _).continuousOn
  have hN₄ : ∫ t, pg c (herm 2) t ^ 2 = 384 * √(π / c) := by
    rw [Cvs.Prolate.HermiteTrialResiduals.integral_trial_sq hc0 (m := 2) le_rfl]; norm_num [Nat.factorial]
  have hk₂ := Cvs.Prolate.EvenRungDavisKahan.exists_isLevelIdx_of_le_three (by linarith : (31 : ℝ) ≤ c) (k := 2)
    (by norm_num)
  have hDK₄ := Cvs.Prolate.EvenRungDavisKahan.sq_mul_integral_sub_rung_two_le (by linarith : (31 : ℝ) ≤ c)
  rw [Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.2, hN₄] at hDK₄
  set E₄ := ∫ t in (-1 : ℝ)..1, (pg c (herm 2) t - overlap c * rung c 2 t) ^ 2
  change (2 * c - 203 / 4) ^ 2 * E₄ ≤ 213 / 2 * (384 * √(π / c)) at hDK₄
  have ha₄ : E₄ = (∫ t in (-1 : ℝ)..1, pg c (herm 2) t ^ 2) - overlap c ^ 2 :=
    Cvs.Prolate.EvenRungDavisKahan.integral_sub_mul_rung_sq hk₂ uF₄
  have hE₄0 : 0 ≤ E₄ := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  have hc2 : (100 : ℝ) ^ 2 ≤ (2 * c - 203 / 4) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have h1 := mul_le_mul_of_nonneg_right hc2 hE₄0
  have hJ₄' : 1000 * (384 * √(π / c)) ≤ 1001 * ∫ t in (-1 : ℝ)..1, pg c (herm 2) t ^ 2 :=
    hN₄ ▸ Cvs.Prolate.EvenRungDavisKahan.mul_integral_trial_sq_le (by linarith : (31 : ℝ) ≤ c) (m := 2) le_rfl
  have hJ₄ : ∫ t in (-1 : ℝ)..1, pg c (herm 2) t ^ 2 ≤ 384 * √(π / c) :=
    hN₄ ▸ integral_trial_sq_Icc_le hc0 2
  constructor <;> nlinarith

/-- The scalar step: with `D ≥ s`, `a₄² ≥ 192s`, `c²E₀ ≤ 3s/2`, `c²E₄ ≤ 40896s` and the defect
`Q = −A − 12B + C`, `3(D²E₄ + P²E₀ + Q²J₀)/(a₄D)² ≤ 639/c² + 15453/(4c²s) + 15552ε`. -/
theorem profile_arith {c s a₄ D I₂ E₀ E₄ J₀ A B C ε : ℝ} (hc : 100 ≤ c) (hs : 0 < s)
    (hE₀ : c ^ 2 * E₀ ≤ 3 / 2 * s) (hE₄ : c ^ 2 * E₄ ≤ 40896 * s) (ha₄ : 192 * s ≤ a₄ ^ 2)
    (hJ₀ : J₀ ≤ s) (hI₂ : I₂ ^ 2 ≤ 2) (hD : s ≤ D) (hB : B ^ 2 ≤ 2 * E₀)
    (hC : C ^ 2 ≤ 2 * E₄) (hA : A ^ 2 ≤ 331776 * s ^ 2 * ε) :
    3 / (a₄ * D) ^ 2 * (D ^ 2 * E₄ + (a₄ * I₂) ^ 2 * E₀ + (-A - 12 * B + C) ^ 2 * J₀)
      ≤ 639 / c ^ 2 + 15453 / (4 * c ^ 2 * s) + 15552 * ε := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hD0 : 0 < D := hs.trans_le hD
  have hDs : s ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hs.le hD 2
  have hD2 : 0 < D ^ 2 := by positivity
  have hA2 : 0 < a₄ ^ 2 := (by positivity : (0 : ℝ) < 192 * s).trans_le ha₄
  have ha₀ : a₄ ≠ 0 := fun h => by rw [h] at hA2; norm_num at hA2
  have t₁ : 3 / (a₄ * D) ^ 2 * (D ^ 2 * E₄) ≤ 639 / c ^ 2 := by
    rw [show 3 / (a₄ * D) ^ 2 * (D ^ 2 * E₄) = 3 * E₄ / a₄ ^ 2 by field_simp,
      div_le_div_iff₀ hA2 hc2]
    linarith
  have t₂ : 3 / (a₄ * D) ^ 2 * ((a₄ * I₂) ^ 2 * E₀) ≤ 9 / (c ^ 2 * s) := by
    rw [show 3 / (a₄ * D) ^ 2 * ((a₄ * I₂) ^ 2 * E₀) = 3 * I₂ ^ 2 * E₀ / D ^ 2 by
      field_simp, div_le_div_iff₀ hD2 (by positivity)]
    have h1 : I₂ ^ 2 * (c ^ 2 * E₀) ≤ 2 * (3 / 2 * s) :=
      mul_le_mul hI₂ hE₀ (by nlinarith) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left h1 hs.le
    have h3 := mul_le_mul_of_nonneg_left hDs (by norm_num : (0 : ℝ) ≤ 9)
    linarith
  have hQ : (-A - 12 * B + C) ^ 2 ≤ 995328 * s ^ 2 * ε + 246672 * s / c ^ 2 := by
    have h3 : (-A - 12 * B + C) ^ 2 ≤ 3 * (A ^ 2 + 144 * B ^ 2 + C ^ 2) := by
      nlinarith [sq_nonneg (A - 12 * B), sq_nonneg (A + C), sq_nonneg (12 * B + C)]
    have h₀ : B ^ 2 ≤ 3 * s / c ^ 2 := by
      rw [le_div_iff₀ hc2]; nlinarith
    have h₄ : C ^ 2 ≤ 81792 * s / c ^ 2 := by
      rw [le_div_iff₀ hc2]; nlinarith
    have : 246672 * s / c ^ 2 = 3 * (144 * (3 * s / c ^ 2) + 81792 * s / c ^ 2) := by ring
    rw [this]
    linarith
  have t₃ : 3 / (a₄ * D) ^ 2 * ((-A - 12 * B + C) ^ 2 * J₀)
      ≤ 15552 * ε + 15417 / (4 * c ^ 2 * s) := by
    set Q := -A - 12 * B + C
    calc 3 / (a₄ * D) ^ 2 * (Q ^ 2 * J₀) ≤ Q ^ 2 / (64 * s ^ 2) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : 192 * s ^ 2 * J₀ ≤ (a₄ * D) ^ 2 := by
            rw [mul_pow]
            calc 192 * s ^ 2 * J₀ ≤ 192 * s * s ^ 2 := by nlinarith
              _ ≤ a₄ ^ 2 * D ^ 2 := mul_le_mul ha₄ hDs (by positivity) (by positivity)
          nlinarith [sq_nonneg Q]
      _ ≤ (995328 * s ^ 2 * ε + 246672 * s / c ^ 2) / (64 * s ^ 2) :=
          div_le_div_of_nonneg_right hQ (by positivity)
      _ = _ := by field_simp; ring
  rw [mul_add, mul_add]
  have e : 9 / (c ^ 2 * s) + 15417 / (4 * c ^ 2 * s) = 15453 / (4 * c ^ 2 * s) := by
    field_simp; ring
  linarith

/-- **The profile at `c ≥ 100`**:
`∫₀¹ (G − g_H/a₄)² ≤ 639/c² + 15453/(4c²√(π/c)) + 15552 e^{−c/2}`. -/
theorem integral_spineG_sub_sq_le (hc : 100 ≤ c) :
    ∫ u in Icc (0 : ℝ) 1,
        (Cvs.Approximant.DeepIndexSpineSpan.spineG c (S := {1}) (fun _ => 1) u - (overlap c)⁻¹ * Cvs.Approximant.QuarticHermiteWindowPhi.gH c u) ^ 2
      ≤ 639 / c ^ 2 + 15453 / (4 * c ^ 2 * √(π / c)) + 15552 * exp (-(c / 2)) := by
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < √(π / c) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : √(π / c) ^ 2 * c = π := by rw [Real.sq_sqrt (by positivity)]; field_simp
  have cF₀ : ContinuousOn (pg c (herm 0)) (Icc (-1) 1) := (Cvs.Prolate.HermiteTrialResiduals.continuous_pg c _).continuousOn
  have cF₄ : ContinuousOn (pg c (herm 2)) (Icc (-1) 1) := (Cvs.Prolate.HermiteTrialResiduals.continuous_pg c _).continuousOn
  have uF₀ : ContinuousOn (pg c (herm 0)) [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  have uF₄ : ContinuousOn (pg c (herm 2)) [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  have iF₀ := uF₀.intervalIntegrable (μ := volume)
  have iF₄ := uF₄.intervalIntegrable (μ := volume)
  have uh₀ : ContinuousOn (rung c 0) [[(-1 : ℝ), 1]] := by
    rw [uIcc_of_le (by norm_num)]; exact continuousOn_rung c 0
  have uh₂ : ContinuousOn (rung c 2) [[(-1 : ℝ), 1]] := by
    rw [uIcc_of_le (by norm_num)]; exact continuousOn_rung c 2
  have ih₀ := uh₀.intervalIntegrable (μ := volume)
  have ih₂ := uh₂.intervalIntegrable (μ := volume)
  -- the trials' norms on the line
  have hN₀ : ∫ t, pg c (herm 0) t ^ 2 = √(π / c) := by
    rw [Cvs.Prolate.HermiteTrialResiduals.integral_trial_sq hc0 (m := 0) (by norm_num)]; simp
  have hN₄ : ∫ t, pg c (herm 2) t ^ 2 = 384 * √(π / c) := by
    rw [Cvs.Prolate.HermiteTrialResiduals.integral_trial_sq hc0 (m := 2) le_rfl]; norm_num [Nat.factorial]
  -- Davis–Kahan
  have hk₂ := Cvs.Prolate.EvenRungDavisKahan.exists_isLevelIdx_of_le_three (by linarith : (31 : ℝ) ≤ c) (k := 2)
    (by norm_num)
  have hDK₀ := Cvs.Prolate.EvenRungDavisKahan.sq_mul_integral_sub_rung_zero_le (by linarith : 19 / 8 ≤ c)
  have hDK₄ := Cvs.Prolate.EvenRungDavisKahan.sq_mul_integral_sub_rung_two_le (by linarith : (31 : ℝ) ≤ c)
  rw [Cvs.Prolate.HermiteTrialResiduals.kap2_values.1, hN₀] at hDK₀
  rw [Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.2, hN₄] at hDK₄
  set a₀ := ∫ t in (-1 : ℝ)..1, pg c (herm 0) t * rung c 0 t
  set a₄ := overlap c
  set E₀ := ∫ t in (-1 : ℝ)..1, (pg c (herm 0) t - a₀ * rung c 0 t) ^ 2
  set E₄ := ∫ t in (-1 : ℝ)..1, (pg c (herm 2) t - a₄ * rung c 2 t) ^ 2
  have hE₀0 : 0 ≤ E₀ := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  have hE₄0 : 0 ≤ E₄ := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  have hE₀ : c ^ 2 * E₀ ≤ 3 / 2 * √(π / c) :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0.le (by linarith) 2) hE₀0).trans hDK₀
  have hE₄ : c ^ 2 * E₄ ≤ 40896 * √(π / c) := by
    have := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0.le (by linarith) 2) hE₄0).trans
      hDK₄
    linarith
  have hc2 : (100 : ℝ) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by norm_num) hc 2
  -- the overlap `a₄`
  have ha₄l : 192 * √(π / c) ≤ a₄ ^ 2 := (sq_overlap_mem hc).1
  have ha₄0 : a₄ ≠ 0 := fun h => by rw [h] at ha₄l; norm_num at ha₄l; linarith
  -- `I₂² ≤ 2`
  have hI₂ : (∫ t in (-1 : ℝ)..1, rung c 2 t) ^ 2 ≤ 2 := by
    have := sq_integral_le (continuousOn_rung c 2)
    rwa [(rung_spec hk₂).2.2.2.2.2, mul_one] at this
  -- the defect integrals
  have he₀ : (∫ t in (-1 : ℝ)..1, (pg c (herm 0) t - a₀ * rung c 0 t)) ^ 2 ≤ 2 * E₀ :=
    sq_integral_le (cF₀.sub ((continuousOn_rung c 0).const_smul a₀))
  have he₄ : (∫ t in (-1 : ℝ)..1, (pg c (herm 2) t - a₄ * rung c 2 t)) ^ 2 ≤ 2 * E₄ :=
    sq_integral_le (cF₄.sub ((continuousOn_rung c 2).const_smul a₄))
  set I₀ := ∫ t in (-1 : ℝ)..1, rung c 0 t
  set I₂ := ∫ t in (-1 : ℝ)..1, rung c 2 t
  set B := ∫ t in (-1 : ℝ)..1, (pg c (herm 0) t - a₀ * rung c 0 t)
  set C := ∫ t in (-1 : ℝ)..1, (pg c (herm 2) t - a₄ * rung c 2 t)
  set A := ∫ t in (-1 : ℝ)..1, Cvs.Approximant.QuarticHermiteWindowPhi.gH c t
  have hD : a₀ * I₀ = (∫ t in (-1 : ℝ)..1, pg c (herm 0) t) - B := by
    simp only [B]
    rw [intervalIntegral.integral_sub iF₀ (ih₀.const_mul _), intervalIntegral.integral_const_mul]
    ring
  have hP : a₄ * I₂ = (∫ t in (-1 : ℝ)..1, pg c (herm 2) t) - C := by
    simp only [C]
    rw [intervalIntegral.integral_sub iF₄ (ih₂.const_mul _), intervalIntegral.integral_const_mul]
    ring
  have hgH : A = (∫ t in (-1 : ℝ)..1, pg c (herm 2) t) - 12 * ∫ t in (-1 : ℝ)..1, pg c (herm 0) t
      := by
    simp only [A]
    simp_rw [gH_eq_sub]
    rw [intervalIntegral.integral_sub iF₄ (iF₀.const_mul _), intervalIntegral.integral_const_mul]
  -- small exponentials
  have hx4 : exp (-(c / 4)) ≤ 1 / 20 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp (c / 4)])
  have hx2 : exp (-(c / 2)) = exp (-(c / 4)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- `D ≥ s`
  have hsc : 100 ≤ √(π / c) * c ^ 2 := by
    have h1 : (√(π / c) * c ^ 2) ^ 2 = π * c ^ 3 := by
      calc (√(π / c) * c ^ 2) ^ 2 = (√(π / c) ^ 2 * c) * c ^ 3 := by ring
        _ = _ := by rw [hs2]
    have h3 := pow_le_pow_left₀ (by norm_num) hc 3
    have h2 : (100 : ℝ) ^ 2 ≤ (√(π / c) * c ^ 2) ^ 2 := by
      rw [h1]; nlinarith [Real.pi_gt_three]
    exact (pow_le_pow_iff_left₀ (by norm_num) (by positivity) two_ne_zero).mp h2
  have hB : B ^ 2 ≤ (3 / 10 * √(π / c)) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hsc hE₀0
    have h2 := mul_le_mul_of_nonneg_left hE₀ hs0.le
    nlinarith
  have hB' := (abs_le_of_sq_le_sq' hB (by positivity)).2
  have hF₀i := integral_trial_zero_ge hc0
  have hr2 : 14 / 10 ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hDl : √(π / c) ≤ a₀ * I₀ := by
    rw [hD]
    have := mul_le_mul_of_nonneg_right hr2 hs0.le
    have := mul_le_mul_of_nonneg_left hx4 hs0.le
    linarith
  have hD0 : a₀ * I₀ ≠ 0 := by linarith
  -- the `α` defect
  have hT := abs_integral_gH_le hc0
  have hA : A ^ 2 ≤ 331776 * √(π / c) ^ 2 * exp (-(c / 2)) := by
    rw [hx2, ← sq_abs]
    calc |A| ^ 2 ≤ (576 * √(π / c) * exp (-(c / 4))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hT 2
      _ = _ := by ring
  have hQ : 12 * (a₀ * I₀) - a₄ * I₂ = -A - 12 * B + C := by
    rw [hD, hP, hgH]; ring
  -- the profile in the trial variables
  have hfun : ∀ u, Cvs.Approximant.DeepIndexSpineSpan.spineG c (S := {1}) (fun _ => 1) u - a₄⁻¹ * Cvs.Approximant.QuarticHermiteWindowPhi.gH c u
      = (rung c 2 u - I₂ / I₀ * rung c 0 u) - (pg c (herm 2) u - 12 * pg c (herm 0) u) / a₄ := by
    intro u
    rw [spineG_one, gH_eq_sub]
    simp only [Cvs.Approximant.DeepIndexSpineSpan.alpha, mul_one, I₀, I₂]
    ring
  simp_rw [hfun]
  refine (integral_profile_sub_sq_le cF₀ cF₄ (continuousOn_rung c 0) (continuousOn_rung c 2)
    ha₄0 hD0).trans ?_
  rw [hQ]
  exact profile_arith hc hs0 hE₀ hE₄ ha₄l (hN₀ ▸ integral_trial_sq_Icc_le hc0 0) hI₂ hDl
    (he₀.trans le_rfl) he₄ hA

end Profile

/-! ### At scale `x` -/

section Scale

/-- `x^{−3/2} = 1/(x √x)` for `x > 0`. -/
theorem rpow_neg_three_halves {x : ℝ} (hx : 0 < x) : x ^ (-(3 / 2 : ℝ)) = (x * √x)⁻¹ := by
  rw [Real.rpow_neg hx.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, Real.sqrt_eq_rpow]

/-- **The profile at scale `x ≥ 16`**: with `c = 2πx`,
`∫₀¹ (G − g_H/a₄)² ≤ (80217/4) x^{−3/2}`. -/
theorem integral_spineG_sub_sq_le_rpow {x : ℝ} (hx : 16 ≤ x) :
    ∫ u in Icc (0 : ℝ) 1, (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) (fun _ => 1) u
        - (overlap (2 * π * x))⁻¹ * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2
      ≤ 80217 / 4 * x ^ (-(3 / 2 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set c := 2 * π * x with hc
  have hc100 : 100 ≤ c := by rw [hc]; nlinarith [Real.pi_gt_d2]
  have hc0 : 0 < c := by linarith
  refine (integral_spineG_sub_sq_le hc100).trans ?_
  rw [rpow_neg_three_halves hx0]
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hxx : 0 < x * √x := by positivity
  have hs0 : 0 < √(π / c) := Real.sqrt_pos.mpr (by positivity)
  -- `x √x ≤ c²`
  have h1 : x * √x ≤ c ^ 2 := by
    have : √x ≤ x := Real.sqrt_le_iff.mpr ⟨hx0.le, by nlinarith⟩
    have hπ : 1 ≤ 4 * π ^ 2 := by nlinarith [Real.pi_gt_three]
    calc x * √x ≤ x * x := mul_le_mul_of_nonneg_left this hx0.le
      _ ≤ 4 * π ^ 2 * (x * x) := le_mul_of_one_le_left (by positivity) hπ
      _ = c ^ 2 := by rw [hc]; ring
  -- `x √x ≤ c² √(π/c)`
  have h2 : x * √x ≤ c ^ 2 * √(π / c) := by
    refine (pow_le_pow_iff_left₀ hxx.le (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hx0.le, Real.sq_sqrt (by positivity)]
    have : (c ^ 2) ^ 2 * (π / c) = 8 * π ^ 4 * x ^ 3 := by rw [hc]; field_simp; ring
    rw [this]
    have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) Real.pi_gt_three.le 4
    have hx3 := pow_pos hx0 3
    nlinarith
  -- `e^{−c/2} ≤ 1/c²`
  have h3 : exp (-(c / 2)) ≤ (c ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    refine inv_anti₀ (by positivity) ?_
    have h := Real.pow_div_factorial_le_exp (c / 2) (by positivity) 4
    have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf] at h
    have : c ^ 2 ≤ (c / 2) ^ 4 / 24 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith [pow_le_pow_left₀ (by norm_num) hc100 2]
    linarith
  have hinv : (c ^ 2)⁻¹ ≤ (x * √x)⁻¹ := inv_anti₀ hxx h1
  have t₁ : 639 / c ^ 2 ≤ 639 * (x * √x)⁻¹ := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hinv (by norm_num)
  have t₂ : 15453 / (4 * c ^ 2 * √(π / c)) ≤ 15453 / 4 * (x * √x)⁻¹ := by
    rw [show 4 * c ^ 2 * √(π / c) = 4 * (c ^ 2 * √(π / c)) by ring, ← div_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hxx h2) (by norm_num)
  have t₃ : 15552 * exp (-(c / 2)) ≤ 15552 * (x * √x)⁻¹ :=
    mul_le_mul_of_nonneg_left (h3.trans hinv) (by norm_num)
  linarith

/-- **The weight**: for `x ≥ 16`, `|1/a₄| ≥ x^{1/4}/20` at `c = 2πx`. -/
theorem le_abs_inv_overlap {x : ℝ} (hx : 16 ≤ x) :
    1 / 20 * x ^ (1 / 4 : ℝ) ≤ |(overlap (2 * π * x))⁻¹| := by
  have hx0 : 0 < x := by linarith
  set c := 2 * π * x with hc
  have hc100 : 100 ≤ c := by rw [hc]; nlinarith [Real.pi_gt_d2]
  obtain ⟨hl, hu⟩ := sq_overlap_mem hc100
  set a := overlap c
  have hs0 : 0 < √(π / c) := Real.sqrt_pos.mpr (by positivity)
  have ha : 0 < |a| := by
    rw [← sq_abs] at hl
    exact abs_pos.mpr fun h => by rw [h, abs_zero] at hl; norm_num at hl; linarith
  have hq : (x ^ (1 / 4 : ℝ)) ^ 2 = √x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]; norm_num
  have hxs : √x * √(π / c) ≤ 1 := by
    rw [← Real.sqrt_mul hx0.le, hc, show x * (π / (2 * π * x)) = 1 / 2 by field_simp]
    rw [Real.sqrt_le_one]; norm_num
  have hy : 1 / 20 * x ^ (1 / 4 : ℝ) * |a| ≤ 1 := by
    have h0 : 0 ≤ 1 / 20 * x ^ (1 / 4 : ℝ) * |a| := by positivity
    refine (pow_le_one_iff_of_nonneg h0 two_ne_zero).mp ?_
    rw [mul_pow, mul_pow, hq, sq_abs]
    have := mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg x)
    nlinarith
  rw [abs_inv, ← one_div, le_div_iff₀ ha]
  exact hy

/-- **Strip approximability of Connes' vectors**: every truncation with `N x ≥ ⌈x^{1/4}⌉`
eventually gives strip approximable normalised coefficient vectors of the spine profile. -/
theorem stripApproximable_connesVec (N : ℝ → ℕ)
    (hN : ∀ᶠ x in atTop, ⌈x ^ (1 / 4 : ℝ)⌉₊ ≤ N x) :
    Cvs.Route.GroundRouteJointGap.StripApproximable N (Cvs.Approximant.ConnesVectorRealScale.connesVec N) := by
  rw [Cvs.Approximant.StripApproxFromHermite.connesVec_eq_profileVec]
  refine Cvs.Approximant.StripApproxFromHermite.stripApproximable_profileVec_of_ceil_le N _ (fun x => (overlap (2 * π * x))⁻¹)
    (b₀ := 1 / 20) (C := 80217 / 4) (by norm_num) (Eventually.of_forall fun x =>
      (Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ _).mono (Icc_subset_Icc (by norm_num) le_rfl)) ?_ ?_ hN
  · filter_upwards [eventually_ge_atTop 16] with x hx using le_abs_inv_overlap hx
  · filter_upwards [eventually_ge_atTop 16] with x hx using integral_spineG_sub_sq_le_rpow hx

end Scale

end Cvs.Approximant.SpineNearQuarticHermite
