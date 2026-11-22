import Mathlib
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Hermite trials `F₆` and `F₈`: residuals, norms and a level near `μ_{2m}` for `m ≤ 4`

`F_n = H_n(√c w)e^{−cw²/2}` at `n = 6, 8` has `(1−w²)F'' − 2wF' − c²w²F + μ_nF = −R_n` with
`μ_n = (2n+1)c − (2n²+2n+3)/4` and `R_n = H_{n+4}/16 + n(n−1)(n−2)(n−3)H_{n−4}`, `∫R_n² = κ'²‖F_n‖²`,
`κ'² = 675/2, 1695/2`. For `c ≥ 40`, `1000‖F_{2m}‖²_{L²(ℝ)} ≤ 1001 ∫_{−1}^{1} F_{2m}²` at every `m ≤ 4`, so some even
level `χ` has `(χ − μ_{2m})² ≤ 1.001 κ'²`.
-/

noncomputable section

open Real MeasureTheory Polynomial

namespace Cvs.Prolate.HermiteTrialsSixEight
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx)
open Cvs.Prolate.HermiteTrialResiduals (pg pg₁ pg₂ herm rq mu kap2 aOp bOp dq gE gm)

/-! ### The Hermite polynomials `H₁₀` and `H₁₂` -/

theorem herm_five : herm 5 = 1024 * X ^ 5 - 23040 * X ^ 4 + 161280 * X ^ 3 - 403200 * X ^ 2
    + 302400 * X - 30240 := by
  rw [herm, Cvs.Prolate.HermiteTrialResiduals.herm_four]; simp; simp only [map_ofNat C]; ring

theorem herm_six : herm 6 = 4096 * X ^ 6 - 135168 * X ^ 5 + 1520640 * X ^ 4 - 7096320 * X ^ 3
    + 13305600 * X ^ 2 - 7983360 * X + 665280 := by
  rw [herm, herm_five]; simp; simp only [map_ofNat C]; ring

/-! ### The Hermite equation and the residuals at `n = 6, 8` -/

/-- The Hermite equation in `t = y²`: `aOp H_{2m} = −(4m + 1) H_{2m}` for `m ≤ 4`. -/
theorem aOp_herm {m : ℕ} (hm : m ≤ 4) : aOp (herm m) = C (-(4 * m + 1 : ℝ)) * herm m := by
  rcases Nat.lt_or_ge m 3 with h | h
  · exact Cvs.Prolate.HermiteTrialResiduals.aOp_herm (by omega)
  refine Polynomial.funext fun t => ?_
  interval_cases m
  · simp [aOp, dq, Cvs.Prolate.HermiteTrialResiduals.herm_three]; ring
  · simp [aOp, dq, Cvs.Prolate.HermiteTrialResiduals.herm_four]; ring

/-- `bOp H_n = K_{nn} H_n + H_{n+4}/16 + n(n−1)(n−2)(n−3) H_{n−4}` at `n = 2m ≤ 8`. -/
theorem bOp_herm {m : ℕ} (hm : m ≤ 4) :
    bOp (herm m) = C (-(8 * m ^ 2 + 4 * m + 3) / 4 : ℝ) * herm m
      + C (1 / 16 : ℝ) * herm (m + 2) + C ((2 * m).descFactorial 4 : ℝ) * herm (m - 2) := by
  rcases Nat.lt_or_ge m 3 with h | h
  · exact Cvs.Prolate.HermiteTrialResiduals.bOp_herm (by omega)
  refine Polynomial.funext fun t => ?_
  interval_cases m
  · simp [bOp, dq, Cvs.Prolate.HermiteTrialResiduals.herm_three, herm_five, Cvs.Prolate.HermiteTrialResiduals.herm_one, Nat.descFactorial]; ring
  · simp [bOp, dq, Cvs.Prolate.HermiteTrialResiduals.herm_four, herm_six, Cvs.Prolate.HermiteTrialResiduals.herm_two, Nat.descFactorial]; ring

/-- `F = H_{2m}(√c w) e^{−cw²/2}` has `(1−w²)F'' − 2wF' − c²w²F + μF = −R`, `R = pg c (rq m)`, for `m ≤ 4`. -/
theorem trial_ode {m : ℕ} (hm : m ≤ 4) (c w : ℝ) :
    (1 - w ^ 2) * pg₂ c (herm m) w - 2 * w * pg₁ c (herm m) w - c ^ 2 * w ^ 2 * pg c (herm m) w
      + mu c m * pg c (herm m) w = -pg c (rq m) w := by
  rw [Cvs.Prolate.HermiteTrialResiduals.prolateOp_pg, aOp_herm hm, bOp_herm hm]
  simp only [pg, rq, mu, eval_add, eval_mul, eval_C]
  ring

theorem kap2_three_four : kap2 3 = 675 / 2 ∧ kap2 4 = 1695 / 2 := by
  norm_num [kap2, Nat.descFactorial]

theorem mu_three (c : ℝ) : mu c 3 = 13 * c - 87 / 4 := by norm_num [mu]

theorem mu_four (c : ℝ) : mu c 4 = 17 * c - 147 / 4 := by norm_num [mu]

/-! ### Gaussian norms -/

theorem gE_herm_sq_three (r : ℝ) :
    gE r (herm 3 ^ 2) = 14400 - 86400 * r + 475200 * r ^ 2 - 1324800 * r ^ 3
      + 2116800 * r ^ 4 - 1814400 * r ^ 5 + 665280 * r ^ 6 := by
  rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 7)
    (fun k => ([14400, -172800, 633600, -706560, 322560, -61440, 4096] : List ℝ).getD k 0)
    (fun t => by simp [Cvs.Prolate.HermiteTrialResiduals.herm_three, Finset.sum_range_succ]; ring)]
  simp [gm, Finset.sum_range_succ, Nat.factorial]; ring

theorem gE_herm_sq_four (r : ℝ) :
    gE r (herm 4 ^ 2) = 2822400 - 22579200 * r + 169344000 * r ^ 2 - 699955200 * r ^ 3
      + 1823270400 * r ^ 4 - 3048192000 * r ^ 5 + 3203988480 * r ^ 6 - 1937295360 * r ^ 7
      + 518918400 * r ^ 8 := by
  rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 9)
    (fun k => ([2822400, -45158400, 225792000, -373309440, 277831680, -103219200, 19726336,
      -1835008, 65536] : List ℝ).getD k 0)
    (fun t => by simp [Cvs.Prolate.HermiteTrialResiduals.herm_four, Finset.sum_range_succ]; ring)]
  simp [gm, Finset.sum_range_succ, Nat.factorial]; ring

/-- `‖H_n‖²` against `e^{−y²}` is `2ⁿ n! √π`: `gE 1 (H_{2m}²) = 4^m (2m)!` for `m ≤ 4`. -/
theorem gE_one_herm_sq {m : ℕ} (hm : m ≤ 4) :
    gE 1 (herm m ^ 2) = 4 ^ m * ((2 * m).factorial : ℝ) := by
  rcases Nat.lt_or_ge m 3 with h | h
  · exact Cvs.Prolate.HermiteTrialResiduals.gE_one_herm_sq (by omega)
  interval_cases m
  · rw [gE_herm_sq_three]; simp [Nat.factorial]; norm_num
  · rw [gE_herm_sq_four]; simp [Nat.factorial]; norm_num

theorem gE_one_rq_sq {m : ℕ} (hm : m ≤ 4) :
    gE 1 (rq m ^ 2) = kap2 m * (4 ^ m * ((2 * m).factorial : ℝ)) := by
  rcases Nat.lt_or_ge m 3 with h | h
  · exact Cvs.Prolate.HermiteTrialResiduals.gE_one_rq_sq (by omega)
  interval_cases m
  · rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 11) (fun k => ([6812100, -106174800, 545259600,
      -1077753600, 1052611200, -566945280, 176785920, -32256000, 3363840, -184320, 4096] :
      List ℝ).getD k 0)
      (fun t => by simp [rq, herm_five, Cvs.Prolate.HermiteTrialResiduals.herm_one, Finset.sum_range_succ,
        Nat.descFactorial]; ring)]
    simp [gm, kap2, Finset.sum_range_succ, Nat.factorial, Nat.descFactorial]; norm_num
  · rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 13) (fun k => ([3811827600, -71569008000,
      441941270400, -1049915865600, 1262851833600, -872719626240, 369714401280, -99105914880,
      16965857280, -1832878080, 120029184, -4325376, 65536] : List ℝ).getD k 0)
      (fun t => by simp [rq, herm_six, Cvs.Prolate.HermiteTrialResiduals.herm_two, Finset.sum_range_succ,
        Nat.descFactorial]; ring)]
    simp [gm, kap2, Finset.sum_range_succ, Nat.factorial, Nat.descFactorial]; norm_num

/-- `‖F_{2m}‖²_{L²(ℝ)} = 4^m (2m)! √(π/c)` for `m ≤ 4`. -/
theorem integral_trial_sq {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : m ≤ 4) :
    ∫ w, pg c (herm m) w ^ 2 = 4 ^ m * ((2 * m).factorial : ℝ) * √(π / c) := by
  rw [Cvs.Prolate.HermiteTrialResiduals.integral_pg_sq hc, gE_one_herm_sq hm]

/-- `∫_{−1}^{1} R_{2m}² ≤ κ'² ‖F_{2m}‖²_{L²(ℝ)}` for `m ≤ 4`. -/
theorem integral_resid_sq_Icc_le {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : m ≤ 4) :
    ∫ w in (-1 : ℝ)..1, pg c (rq m) w ^ 2 ≤ kap2 m * ∫ w, pg c (herm m) w ^ 2 := by
  have h : ∫ w, pg c (rq m) w ^ 2 = kap2 m * ∫ w, pg c (herm m) w ^ 2 := by
    rw [Cvs.Prolate.HermiteTrialResiduals.integral_pg_sq hc, Cvs.Prolate.HermiteTrialResiduals.integral_pg_sq hc, gE_one_rq_sq hm, gE_one_herm_sq hm]
    ring
  rw [← h, intervalIntegral.integral_of_le (by norm_num)]
  exact setIntegral_le_integral (Cvs.Prolate.HermiteTrialResiduals.integrable_pg_sq hc _)
    (Filter.Eventually.of_forall fun w => sq_nonneg _)

/-- `F_{2m}` has positive mass on `[−1, 1]` for `m ≤ 4`. -/
theorem integral_trial_sq_pos (c : ℝ) {m : ℕ} (hm : m ≤ 4) :
    0 < ∫ s in (-1 : ℝ)..1, pg c (herm m) s ^ 2 := by
  refine Cvs.Prolate.EvenRungsByIndex.integral_sq_pos (Cvs.Prolate.HermiteTrialResiduals.continuous_pg c _).continuousOn
    ⟨0, by norm_num, ?_⟩
  interval_cases m
  · simp [pg, herm]
  · norm_num [pg, Cvs.Prolate.HermiteTrialResiduals.herm_one]
  · norm_num [pg, Cvs.Prolate.HermiteTrialResiduals.herm_two]
  · norm_num [pg, Cvs.Prolate.HermiteTrialResiduals.herm_three]
  · norm_num [pg, Cvs.Prolate.HermiteTrialResiduals.herm_four]

/-- For `c ≥ 40` and `m ≤ 4`, `1000 ‖F_{2m}‖²_{L²(ℝ)} ≤ 1001 ∫_{−1}^{1} F_{2m}²`. -/
theorem mul_integral_trial_sq_le {c : ℝ} (hc : 40 ≤ c) {m : ℕ} (hm : m ≤ 4) :
    1000 * ∫ s, pg c (herm m) s ^ 2 ≤ 1001 * ∫ s in (-1 : ℝ)..1, pg c (herm m) s ^ 2 := by
  have hc0 : 0 < c := by linarith
  have ht := Cvs.Prolate.HermiteTrialResiduals.integral_pg_sq_sub_le (half_pos hc0) (half_le_self hc0.le) (herm m)
  have h2 : c / (c / 2) = 2 := by field_simp
  have hs : √(π / (c / 2)) = √2 * √(π / c) := by
    rw [← Real.sqrt_mul (by norm_num)]
    congr 1
    field_simp
  rw [h2, hs, integral_trial_sq hc0 hm] at ht
  rw [integral_trial_sq hc0 hm]
  have hS : 0 < √(π / c) := Real.sqrt_pos.mpr (by positivity)
  have he : 8000000 ≤ exp (c / 2) := by
    have h12 := Real.pow_div_factorial_le_exp (c / 2) (by positivity) 12
    have h20 : (20 : ℝ) ^ 12 ≤ (c / 2) ^ 12 := pow_le_pow_left₀ (by norm_num) (by linarith) 12
    have hf : ((Nat.factorial 12 : ℕ) : ℝ) = 479001600 := by norm_num [Nat.factorial]
    rw [hf] at h12
    norm_num at h20
    linarith
  have hexp : exp (-(c - c / 2)) ≤ 1 / 8000000 := by
    rw [show -(c - c / 2) = -(c / 2) by ring, Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) he
  have hsq2 : √2 ≤ 1415 / 1000 := by
    calc √2 ≤ √((1415 / 1000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 1415 / 1000 := Real.sqrt_sq (by norm_num)
  have hg0 : 0 ≤ gE 2 (herm m ^ 2) := by
    interval_cases m
    · rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_zero]; norm_num
    · rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_one]; norm_num
    · rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_two]; norm_num
    · rw [gE_herm_sq_three]; norm_num
    · rw [gE_herm_sq_four]; norm_num
  have key : exp (-(c - c / 2)) * (gE 2 (herm m ^ 2) * (√2 * √(π / c)))
      ≤ 1 / 8000000 * (gE 2 (herm m ^ 2) * (1415 / 1000 * √(π / c))) :=
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
  · rw [gE_herm_sq_three] at key ht
    norm_num [Nat.factorial] at ht key ⊢
    linarith
  · rw [gE_herm_sq_four] at key ht
    norm_num [Nat.factorial] at ht key ⊢
    linarith

/-! ### A level near `μ_{2m}` -/

/-- **A level within `√(1.001 κ'²)` of `μ_{2m}`** for `c ≥ 40` and `m ≤ 4`. -/
theorem exists_sq_sub_mu_le {c : ℝ} (hc : 40 ≤ c) {m : ℕ} (hm : m ≤ 4) :
    ∃ k χ, IsLevelIdx c k χ ∧ (χ - mu c m) ^ 2 ≤ 1001 / 1000 * kap2 m := by
  have hc0 : 0 < c := by linarith
  obtain ⟨k, χ, hχ, hle⟩ := Cvs.Prolate.EvenRungDavisKahan.exists_sq_mul_integral_sq_le hc0.ne'
    (fun s _ => Cvs.Prolate.HermiteTrialResiduals.hasDerivAt_pg c _ s) (fun s _ => Cvs.Prolate.HermiteTrialResiduals.hasDerivAt_pg₁ c _ s)
    (Cvs.Prolate.HermiteTrialResiduals.continuous_pg₂ c _).continuousOn (fun s _ => trial_ode hm c s)
    (fun s _ => Cvs.Prolate.HermiteTrialResiduals.pg_neg c _ s) (fun s _ => Cvs.Prolate.HermiteTrialResiduals.pg_neg c _ s) (integral_trial_sq_pos c hm)
  have hle' := hle.trans (integral_resid_sq_Icc_le hc0 hm)
  refine ⟨k, χ, hχ, le_of_mul_le_mul_right ?_ (integral_trial_sq_pos c hm)⟩
  have h1 := mul_integral_trial_sq_le hc hm
  have hk : 0 ≤ kap2 m := by unfold kap2; positivity
  nlinarith

end Cvs.Prolate.HermiteTrialsSixEight
