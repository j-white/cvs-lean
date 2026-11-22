import Mathlib
import Cvs.Upstream.GaussianMomentRecursion
import Cvs.Upstream.GaussianMomentsLine
import Cvs.Upstream.PolyGaussianIntegrable

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Hermite trials for the prolate operator: exact residuals and Gaussian norms

`F = Q(cw²)e^{−cw²/2}` has `(1−w²)F'' − 2wF' − c²w²F = c·pg (aOp Q) − pg (bOp Q)`. At
`F_n = H_n(√c w)e^{−cw²/2}`, `n = 0, 2, 4`, and `μ_n = (2n+1)c − (2n²+2n+3)/4` the residual is
`H_{n+4}/16 + n(n−1)(n−2)(n−3)H_{n−4}` with `∫R² = κ'²‖F_n‖²`, `‖F_n‖² = 2ⁿn!√(π/c)`, mass off
`[−1, 1]` at most `e^{−(c−μ)}` times a Gaussian moment, and `∫(F₄ − 12F₀) = 0`.
-/

noncomputable section

open Real MeasureTheory Polynomial

namespace Cvs.Prolate.HermiteTrialResiduals

/-! ### Gaussian moments of polynomials in `w²` -/

/-- `γ_k = (2k)!/(k! 4^k)`, so that `∫ y^{2k} e^{−y²} = γ_k √π`. -/
def gm (k : ℕ) : ℝ := ((2 * k).factorial : ℝ) / ((k.factorial : ℝ) * 4 ^ k)

theorem gm_succ (k : ℕ) : gm (k + 1) = (2 * k + 1) / 2 * gm k := by
  unfold gm
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ]
  push_cast
  have h1 : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have h2 : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The even Gaussian moments: `∫ w^{2k} e^{−λw²} = γ_k λ^{−k} √(π/λ)`. -/
theorem integral_pow_mul_gaussian {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    ∫ w : ℝ, w ^ (2 * k) * exp (-lam * w ^ 2) = gm k / lam ^ k * √(π / lam) := by
  induction k with
  | zero => simpa [gm] using integral_gaussian lam
  | succ k ih =>
    rw [Cvs.Moments.moment_real hlam, show 2 * (k + 1) = 2 * k + 2 by ring,
      Cvs.Moments.moment_rec hlam, ← mul_assoc,
      mul_comm 2, mul_assoc, ← Cvs.Moments.moment_real hlam, ih, gm_succ, pow_succ]
    field_simp

/-- A polynomial in `r w²` against `e^{−λw²}` is integrable. -/
theorem integrable_sum_mul_gaussian {lam : ℝ} (hlam : 0 < lam) (r : ℝ) (s : Finset ℕ)
    (a : ℕ → ℝ) :
    Integrable fun w : ℝ => (∑ k ∈ s, a k * (r * w ^ 2) ^ k) * exp (-lam * w ^ 2) := by
  simp_rw [Finset.sum_mul]
  refine integrable_finsetSum _ fun k _ => ?_
  refine ((Cvs.Moments.integrable_pow_mul_gaussian hlam k).const_mul (a k * r ^ k)).congr
    (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [mul_pow, pow_mul]
  ring

/-- `∫ (Σ a_k (r w²)^k) e^{−λw²} = (Σ a_k γ_k (r/λ)^k) √(π/λ)`. -/
theorem integral_sum_mul_gaussian {lam : ℝ} (hlam : 0 < lam) (r : ℝ) (s : Finset ℕ)
    (a : ℕ → ℝ) :
    ∫ w : ℝ, (∑ k ∈ s, a k * (r * w ^ 2) ^ k) * exp (-lam * w ^ 2)
      = (∑ k ∈ s, a k * gm k * (r / lam) ^ k) * √(π / lam) := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun k _ => by
    simpa [Finset.sum_mul] using integrable_sum_mul_gaussian hlam r {k} a]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (fun w : ℝ => a k * (r * w ^ 2) ^ k * exp (-lam * w ^ 2))
      = fun w => (a k * r ^ k) * (w ^ (2 * k) * exp (-lam * w ^ 2)) := by
    funext w
    rw [mul_pow, pow_mul]
    ring
  rw [h, integral_const_mul, integral_pow_mul_gaussian hlam, div_pow]
  ring

/-- A polynomial in `r w²` against `e^{−λw²}` is integrable. -/
theorem integrable_eval_mul_gaussian {lam : ℝ} (hlam : 0 < lam) (r : ℝ) (P : ℝ[X]) :
    Integrable fun w : ℝ => P.eval (r * w ^ 2) * exp (-lam * w ^ 2) := by
  simp_rw [eval_eq_sum_range]
  exact integrable_sum_mul_gaussian hlam r _ _

/-- The Gaussian functional `P ↦ Σ_k P_k γ_k r^k`. -/
def gE (r : ℝ) (P : ℝ[X]) : ℝ := P.sum fun k a => a * gm k * r ^ k

/-- `∫ P(r w²) e^{−λw²} = gE (r/λ) P · √(π/λ)`. -/
theorem integral_eval_mul_gaussian {lam : ℝ} (hlam : 0 < lam) (r : ℝ) (P : ℝ[X]) :
    ∫ w : ℝ, P.eval (r * w ^ 2) * exp (-lam * w ^ 2) = gE (r / lam) P * √(π / lam) := by
  simp_rw [eval_eq_sum, Polynomial.sum_def]
  rw [integral_sum_mul_gaussian hlam r P.support P.coeff, gE, Polynomial.sum_def]

/-- `gE` read off any monomial expansion of `P`. -/
theorem gE_eq_of_eval {P : ℝ[X]} (s : Finset ℕ) (a : ℕ → ℝ)
    (h : ∀ t, P.eval t = ∑ k ∈ s, a k * t ^ k) (r : ℝ) :
    gE r P = ∑ k ∈ s, a k * gm k * r ^ k := by
  have h1 := integral_eval_mul_gaussian one_pos r P
  simp_rw [h, integral_sum_mul_gaussian one_pos r s a, div_one] at h1
  have hpi : √π ≠ 0 := by positivity
  exact (mul_right_cancel₀ hpi h1).symm

/-! ### The tail beyond `|w| = 1` -/

/-- Off `[−1, 1]` the factor `e^{−(λ−μ)w²}` is at most `e^{−(λ−μ)}`. -/
theorem abs_integral_sub_intervalIntegral_le {p : ℝ → ℝ} (hp : Continuous p) {lam mu : ℝ}
    (hml : mu ≤ lam) (hi : Integrable fun w => |p w| * exp (-mu * w ^ 2)) :
    |(∫ w, p w * exp (-lam * w ^ 2)) - ∫ w in (-1 : ℝ)..1, p w * exp (-lam * w ^ 2)|
      ≤ exp (-(lam - mu)) * ∫ w, |p w| * exp (-mu * w ^ 2) := by
  have hle : ∀ w : ℝ, exp (-lam * w ^ 2) ≤ exp (-mu * w ^ 2) := fun w =>
    exp_le_exp.2 (by nlinarith [sq_nonneg w])
  have hf : Integrable fun w => p w * exp (-lam * w ^ 2) := by
    refine hi.mono' (by fun_prop) (Filter.Eventually.of_forall fun w => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hle w) (abs_nonneg _)
  set s : Set ℝ := Set.Ioc (-1) 1
  have hs : MeasurableSet s := measurableSet_Ioc
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_add_compl hs hf,
    add_sub_cancel_left]
  have hout : ∀ w ∈ sᶜ, |p w * exp (-lam * w ^ 2)|
      ≤ exp (-(lam - mu)) * (|p w| * exp (-mu * w ^ 2)) := by
    intro w hw
    have hw1 : 1 ≤ w ^ 2 := by
      simp only [s, Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hw
      rcases hw with hw | hw <;> nlinarith
    rw [abs_mul, abs_of_pos (exp_pos _), mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← exp_add]
    exact exp_le_exp.2 (by nlinarith)
  calc |∫ w in sᶜ, p w * exp (-lam * w ^ 2)|
      ≤ ∫ w in sᶜ, |p w * exp (-lam * w ^ 2)| := abs_integral_le_integral_abs
    _ ≤ ∫ w in sᶜ, exp (-(lam - mu)) * (|p w| * exp (-mu * w ^ 2)) :=
        setIntegral_mono_on hf.abs.integrableOn (hi.const_mul _).integrableOn hs.compl hout
    _ ≤ ∫ w, exp (-(lam - mu)) * (|p w| * exp (-mu * w ^ 2)) :=
        setIntegral_le_integral (hi.const_mul _)
          (Filter.Eventually.of_forall fun w => by positivity)
    _ = _ := integral_const_mul _ _

/-! ### Polynomial–Gaussian trials and the prolate operator -/

/-- The even trial `Q(c w²) e^{−c w²/2}`. -/
def pg (c : ℝ) (Q : ℝ[X]) (w : ℝ) : ℝ := Q.eval (c * w ^ 2) * exp (-(c / 2) * w ^ 2)

/-- The polynomial `2Q' − Q` with `(pg c Q)' = c w · pg c (2Q' − Q)`. -/
def dq (Q : ℝ[X]) : ℝ[X] := 2 * derivative Q - Q

/-- The first derivative of `pg c Q`. -/
def pg₁ (c : ℝ) (Q : ℝ[X]) (w : ℝ) : ℝ := c * w * pg c (dq Q) w

/-- The second derivative of `pg c Q`. -/
def pg₂ (c : ℝ) (Q : ℝ[X]) (w : ℝ) : ℝ :=
  c * pg c (dq Q) w + c ^ 2 * w ^ 2 * pg c (dq (dq Q)) w

theorem hasDerivAt_pg (c : ℝ) (Q : ℝ[X]) (w : ℝ) : HasDerivAt (pg c Q) (pg₁ c Q w) w := by
  have h1 : HasDerivAt (fun w : ℝ => c * w ^ 2) (c * (2 * w)) w := by
    simpa using (hasDerivAt_pow 2 w).const_mul c
  have h2 : HasDerivAt (fun w : ℝ => -(c / 2) * w ^ 2) (-(c / 2) * (2 * w)) w := by
    simpa using (hasDerivAt_pow 2 w).const_mul (-(c / 2))
  refine (((Q.hasDerivAt _).comp w h1).mul h2.exp).congr_deriv ?_
  simp only [pg₁, pg, dq, eval_sub, eval_mul, eval_ofNat, Function.comp_apply]
  ring

theorem hasDerivAt_pg₁ (c : ℝ) (Q : ℝ[X]) (w : ℝ) :
    HasDerivAt (pg₁ c Q) (pg₂ c Q w) w := by
  refine (((hasDerivAt_id w).const_mul c).mul (hasDerivAt_pg c (dq Q) w)).congr_deriv ?_
  simp only [pg₂, pg₁, id]
  ring

theorem continuous_pg (c : ℝ) (Q : ℝ[X]) : Continuous (pg c Q) := by
  unfold pg; fun_prop

theorem continuous_pg₂ (c : ℝ) (Q : ℝ[X]) : Continuous (pg₂ c Q) := by
  unfold pg₂
  exact (continuous_const.mul (continuous_pg c (dq Q))).add
    ((continuous_const.mul (continuous_id.pow 2)).mul (continuous_pg c (dq (dq Q))))

theorem pg_neg (c : ℝ) (Q : ℝ[X]) (w : ℝ) : pg c Q (-w) = pg c Q w := by
  simp [pg]

/-- The `c`-linear part of the operator on trials: `P + t(2P' − P) − tQ`, `P = 2Q' − Q`. -/
def aOp (Q : ℝ[X]) : ℝ[X] := dq Q + X * dq (dq Q) - X * Q

/-- The `c`-free part of the operator on trials: `3t·(2Q' − Q) + t²·(2P' − P)`. -/
def bOp (Q : ℝ[X]) : ℝ[X] := 3 * X * dq Q + X ^ 2 * dq (dq Q)

/-- `(1 − w²)F'' − 2wF' − c²w²F = c·pg c (aOp Q) − pg c (bOp Q)` for `F = pg c Q`. -/
theorem prolateOp_pg (c : ℝ) (Q : ℝ[X]) (w : ℝ) :
    (1 - w ^ 2) * pg₂ c Q w - 2 * w * pg₁ c Q w - c ^ 2 * w ^ 2 * pg c Q w
      = c * pg c (aOp Q) w - pg c (bOp Q) w := by
  simp only [pg₂, pg₁, pg, aOp, bOp, eval_sub, eval_add, eval_mul, eval_X, eval_pow, eval_ofNat]
  ring

theorem pg_sq (c : ℝ) (Q : ℝ[X]) (w : ℝ) :
    pg c Q w ^ 2 = (Q ^ 2).eval (c * w ^ 2) * exp (-c * w ^ 2) := by
  rw [pg, mul_pow, eval_pow, ← exp_nat_mul]
  congr 2
  push_cast
  ring

/-- `∫ (pg c Q)² = gE 1 (Q²) · √(π/c)`. -/
theorem integral_pg_sq {c : ℝ} (hc : 0 < c) (Q : ℝ[X]) :
    ∫ w, pg c Q w ^ 2 = gE 1 (Q ^ 2) * √(π / c) := by
  simp_rw [pg_sq]
  rw [integral_eval_mul_gaussian hc, div_self hc.ne']

theorem integrable_pg_sq {c : ℝ} (hc : 0 < c) (Q : ℝ[X]) :
    Integrable fun w => pg c Q w ^ 2 := by
  simp_rw [pg_sq]
  exact integrable_eval_mul_gaussian hc _ _

theorem integrable_pg {c : ℝ} (hc : 0 < c) (Q : ℝ[X]) : Integrable (pg c Q) :=
  integrable_eval_mul_gaussian (half_pos hc) c Q

/-- `∫ pg c Q = gE 2 Q · √(2π/c)`. -/
theorem integral_pg {c : ℝ} (hc : 0 < c) (Q : ℝ[X]) :
    ∫ w, pg c Q w = gE 2 Q * √(2 * π / c) := by
  unfold pg
  rw [integral_eval_mul_gaussian (half_pos hc)]
  congr 2 <;> field_simp

/-- The mass of `(pg c Q)²` off `[−1, 1]` is at most `e^{−(c−μ)} gE (c/μ) (Q²) √(π/μ)`. -/
theorem integral_pg_sq_sub_le {c mu : ℝ} (hmu : 0 < mu) (hmc : mu ≤ c) (Q : ℝ[X]) :
    (∫ w, pg c Q w ^ 2) - ∫ w in (-1 : ℝ)..1, pg c Q w ^ 2
      ≤ exp (-(c - mu)) * (gE (c / mu) (Q ^ 2) * √(π / mu)) := by
  have hnn : ∀ w, 0 ≤ (Q ^ 2).eval (c * w ^ 2) := fun w => by rw [eval_pow]; positivity
  have hi : Integrable fun w => |(Q ^ 2).eval (c * w ^ 2)| * exp (-mu * w ^ 2) := by
    simp_rw [abs_of_nonneg (hnn _)]
    exact integrable_eval_mul_gaussian hmu c _
  have h := abs_integral_sub_intervalIntegral_le (p := fun w => (Q ^ 2).eval (c * w ^ 2))
    (by fun_prop) hmc hi
  simp_rw [abs_of_nonneg (hnn _), integral_eval_mul_gaussian hmu] at h
  simp_rw [pg_sq]
  exact (le_abs_self _).trans h

/-- Cutting `pg c Q` to `[−1, 1]` moves its integral by at most `e^{−(c/2−μ)} ∫|Q(cw²)|e^{−μw²}`. -/
theorem abs_integral_pg_sub_le {c mu : ℝ} (hmu : 0 < mu) (hmc : mu ≤ c / 2) (Q : ℝ[X]) :
    |(∫ w, pg c Q w) - ∫ w in (-1 : ℝ)..1, pg c Q w|
      ≤ exp (-(c / 2 - mu)) * ∫ w, |Q.eval (c * w ^ 2)| * exp (-mu * w ^ 2) := by
  have hi : Integrable fun w => |Q.eval (c * w ^ 2)| * exp (-mu * w ^ 2) := by
    refine (integrable_eval_mul_gaussian hmu c Q).abs.congr
      (Filter.Eventually.of_forall fun w => ?_)
    simp only [abs_mul, abs_of_pos (exp_pos _)]
  exact abs_integral_sub_intervalIntegral_le (p := fun w => Q.eval (c * w ^ 2)) (by fun_prop)
    hmc hi

/-! ### Even Hermite polynomials -/

/-- `H_{2m}(y) = (herm m).eval (y²)`, from `H_{n+2} = (4y² − 2)H_n − 4yH_n' + H_n''`. -/
def herm : ℕ → ℝ[X]
  | 0 => 1
  | m + 1 => (4 * X - 2) * herm m - (8 * X - 2) * derivative (herm m)
      + 4 * X * derivative (derivative (herm m))

theorem herm_one : herm 1 = 4 * X - 2 := by
  simp [herm]

theorem herm_two : herm 2 = 16 * X ^ 2 - 48 * X + 12 := by
  rw [herm, herm_one]; simp; ring

theorem herm_three : herm 3 = 64 * X ^ 3 - 480 * X ^ 2 + 720 * X - 120 := by
  rw [herm, herm_two]; simp; ring

theorem herm_four :
    herm 4 = 256 * X ^ 4 - 3584 * X ^ 3 + 13440 * X ^ 2 - 13440 * X + 1680 := by
  rw [herm, herm_three]; simp; simp only [map_ofNat C]; ring

/-- The Hermite equation in `t = y²`: `aOp H_{2m} = −(4m + 1) H_{2m}`. -/
theorem aOp_herm {m : ℕ} (hm : m ≤ 2) : aOp (herm m) = C (-(4 * m + 1 : ℝ)) * herm m := by
  refine Polynomial.funext fun t => ?_
  interval_cases m
  · simp [aOp, dq, herm]
  · simp [aOp, dq, herm_one]; ring
  · simp [aOp, dq, herm_two]; ring

/-- `bOp H_n = K_{nn} H_n + H_{n+4}/16 + n(n−1)(n−2)(n−3) H_{n−4}` at `n = 2m`,
with `K_{nn} = −(2n² + 2n + 3)/4`. -/
theorem bOp_herm {m : ℕ} (hm : m ≤ 2) :
    bOp (herm m) = C (-(8 * m ^ 2 + 4 * m + 3) / 4 : ℝ) * herm m
      + C (1 / 16 : ℝ) * herm (m + 2) + C ((2 * m).descFactorial 4 : ℝ) * herm (m - 2) := by
  refine Polynomial.funext fun t => ?_
  interval_cases m
  · simp [bOp, dq, herm]; ring
  · simp [bOp, dq, herm_one, herm_three]; ring
  · simp [bOp, dq, herm, Nat.descFactorial]; ring

/-! ### The trials `F_{2m}` and their residuals -/

/-- `μ_n = (2n + 1)c − (2n² + 2n + 3)/4` at `n = 2m`. -/
def mu (c : ℝ) (m : ℕ) : ℝ := (4 * m + 1) * c - (8 * m ^ 2 + 4 * m + 3) / 4

/-- The residual polynomial `H_{n+4}/16 + n(n−1)(n−2)(n−3) H_{n−4}` at `n = 2m`. -/
def rq (m : ℕ) : ℝ[X] :=
  C (1 / 16 : ℝ) * herm (m + 2) + C ((2 * m).descFactorial 4 : ℝ) * herm (m - 2)

/-- `κ'² = ((n+4)(n+3)(n+2)(n+1) + n(n−1)(n−2)(n−3))/16` at `n = 2m`. -/
def kap2 (m : ℕ) : ℝ := (((2 * m + 4).descFactorial 4 + (2 * m).descFactorial 4 : ℕ) : ℝ) / 16

theorem kap2_values : kap2 0 = 3 / 2 ∧ kap2 1 = 45 / 2 ∧ kap2 2 = 213 / 2 := by
  norm_num [kap2, Nat.descFactorial]

/-- `F = H_{2m}(√c w) e^{−cw²/2}` has `(1−w²)F'' − 2wF' − c²w²F + μF = −R`, `R = pg c (rq m)`. -/
theorem trial_ode {m : ℕ} (hm : m ≤ 2) (c w : ℝ) :
    (1 - w ^ 2) * pg₂ c (herm m) w - 2 * w * pg₁ c (herm m) w - c ^ 2 * w ^ 2 * pg c (herm m) w
      + mu c m * pg c (herm m) w = -pg c (rq m) w := by
  rw [prolateOp_pg, aOp_herm hm, bOp_herm hm]
  simp only [pg, rq, mu, eval_add, eval_mul, eval_C]
  ring

theorem gE_herm_sq_zero (r : ℝ) : gE r (herm 0 ^ 2) = 1 := by
  rw [gE_eq_of_eval (Finset.range 1) (fun _ => 1) (fun t => by simp [herm])]
  simp [gm]

theorem gE_herm_sq_one (r : ℝ) : gE r (herm 1 ^ 2) = 4 - 8 * r + 12 * r ^ 2 := by
  rw [gE_eq_of_eval (Finset.range 3) (fun k => ([4, -16, 16] : List ℝ).getD k 0)
    (fun t => by simp [herm_one, Finset.sum_range_succ]; ring)]
  simp [gm, Finset.sum_range_succ, Nat.factorial]; ring

theorem gE_herm_sq_two (r : ℝ) :
    gE r (herm 2 ^ 2) = 144 - 576 * r + 2016 * r ^ 2 - 2880 * r ^ 3 + 1680 * r ^ 4 := by
  rw [gE_eq_of_eval (Finset.range 5)
    (fun k => ([144, -1152, 2688, -1536, 256] : List ℝ).getD k 0)
    (fun t => by simp [herm_two, Finset.sum_range_succ]; ring)]
  simp [gm, Finset.sum_range_succ, Nat.factorial]; ring

/-- `‖H_n‖²` against `e^{−y²}` is `2ⁿ n! √π`: `gE 1 (H_{2m}²) = 4^m (2m)!`. -/
theorem gE_one_herm_sq {m : ℕ} (hm : m ≤ 2) :
    gE 1 (herm m ^ 2) = 4 ^ m * ((2 * m).factorial : ℝ) := by
  interval_cases m
  · simp [gE_herm_sq_zero]
  · rw [gE_herm_sq_one]; simp [Nat.factorial]; norm_num
  · rw [gE_herm_sq_two]; simp [Nat.factorial]; norm_num

theorem gE_one_rq_sq {m : ℕ} (hm : m ≤ 2) :
    gE 1 (rq m ^ 2) = kap2 m * (4 ^ m * ((2 * m).factorial : ℝ)) := by
  interval_cases m
  · rw [gE_eq_of_eval (Finset.range 5)
      (fun k => ([9/16, -9/2, 21/2, -6, 1] : List ℝ).getD k 0)
      (fun t => by simp [rq, herm, Finset.sum_range_succ]; ring)]
    simp [gm, kap2, Finset.sum_range_succ, Nat.factorial, Nat.descFactorial]; norm_num
  · rw [gE_eq_of_eval (Finset.range 7)
      (fun k => ([225/4, -675, 2475, -2760, 1260, -240, 16] : List ℝ).getD k 0)
      (fun t => by simp [rq, herm_three, Finset.sum_range_succ, Nat.descFactorial]; ring)]
    simp [gm, kap2, Finset.sum_range_succ, Nat.factorial, Nat.descFactorial]; norm_num
  · rw [gE_eq_of_eval (Finset.range 9) (fun k => ([16641, -216720, 922320, -1468992, 1086048,
      -403200, 77056, -7168, 256] : List ℝ).getD k 0)
      (fun t => by simp [rq, herm, Finset.sum_range_succ, Nat.descFactorial]; ring)]
    simp [gm, kap2, Finset.sum_range_succ, Nat.factorial, Nat.descFactorial]; norm_num

/-- `‖F_{2m}‖²_{L²(ℝ)} = 4^m (2m)! √(π/c)`; at `m = 2`, `384 √(π/c)`. -/
theorem integral_trial_sq {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : m ≤ 2) :
    ∫ w, pg c (herm m) w ^ 2 = 4 ^ m * ((2 * m).factorial : ℝ) * √(π / c) := by
  rw [integral_pg_sq hc, gE_one_herm_sq hm]

/-- `∫_ℝ R_{2m}² = κ'² ‖F_{2m}‖²`, with `κ'² = 3/2, 45/2, 213/2` at `n = 0, 2, 4`. -/
theorem integral_resid_sq {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : m ≤ 2) :
    ∫ w, pg c (rq m) w ^ 2 = kap2 m * ∫ w, pg c (herm m) w ^ 2 := by
  rw [integral_pg_sq hc, integral_pg_sq hc, gE_one_rq_sq hm, gE_one_herm_sq hm]
  ring

theorem integral_resid_sq_Icc_le {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : m ≤ 2) :
    ∫ w in (-1 : ℝ)..1, pg c (rq m) w ^ 2 ≤ kap2 m * ∫ w, pg c (herm m) w ^ 2 := by
  rw [← integral_resid_sq hc hm, intervalIntegral.integral_of_le (by norm_num)]
  exact setIntegral_le_integral (integrable_pg_sq hc _)
    (Filter.Eventually.of_forall fun w => sq_nonneg _)

/-- `∫_ℝ F_{2m} = (2m)!/m! · √(2π/c)`. -/
theorem integral_trial {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : m ≤ 2) :
    ∫ w, pg c (herm m) w = ((2 * m).factorial : ℝ) / (m.factorial : ℝ) * √(2 * π / c) := by
  rw [integral_pg hc]
  congr 1
  interval_cases m
  · rw [gE_eq_of_eval (Finset.range 1) (fun _ => 1) (fun t => by simp [herm])]; simp [gm]
  · rw [gE_eq_of_eval (Finset.range 2) (fun k => ([-2, 4] : List ℝ).getD k 0)
      (fun t => by simp [herm_one, Finset.sum_range_succ]; ring)]
    simp [gm, Finset.sum_range_succ, Nat.factorial]; norm_num
  · rw [gE_eq_of_eval (Finset.range 3) (fun k => ([12, -48, 16] : List ℝ).getD k 0)
      (fun t => by simp [herm_two, Finset.sum_range_succ]; ring)]
    simp [gm, Finset.sum_range_succ, Nat.factorial]; norm_num

/-- `g_H = (16c²w⁴ − 48cw²) e^{−cw²/2}` is `F₄ − 12 F₀`. -/
theorem gH_eq (c w : ℝ) : (16 * c ^ 2 * w ^ 4 - 48 * c * w ^ 2) * exp (-(c / 2) * w ^ 2)
    = pg c (herm 2) w - 12 * pg c (herm 0) w := by
  simp only [pg, herm]; simp; ring

/-- `g_H = F₄ − 12 F₀` has integral zero over `ℝ`. -/
theorem integral_gH {c : ℝ} (hc : 0 < c) :
    ∫ w, (16 * c ^ 2 * w ^ 4 - 48 * c * w ^ 2) * exp (-(c / 2) * w ^ 2) = 0 := by
  simp_rw [gH_eq]
  rw [integral_sub (integrable_pg hc _) ((integrable_pg hc _).const_mul 12), integral_const_mul,
    integral_trial hc le_rfl, integral_trial hc (by norm_num)]
  simp [Nat.factorial]; ring

/-- `∫_{−1}^{1} F_{2m}² ≥ (1 − e^{1−c} √c gE c (H_{2m}²)/(4^m (2m)!)) ‖F_{2m}‖²` for `c ≥ 1`. -/
theorem integral_trial_sq_Icc_ge {c : ℝ} (hc : 1 ≤ c) {m : ℕ} (hm : m ≤ 2) :
    (1 - exp (1 - c) * √c * gE c (herm m ^ 2) / (4 ^ m * ((2 * m).factorial : ℝ)))
        * ∫ w, pg c (herm m) w ^ 2
      ≤ ∫ w in (-1 : ℝ)..1, pg c (herm m) w ^ 2 := by
  have hc0 : 0 < c := one_pos.trans_le hc
  have h := integral_pg_sq_sub_le one_pos hc (herm m)
  rw [div_one, div_one] at h
  have hN : (0 : ℝ) < 4 ^ m * ((2 * m).factorial : ℝ) := by positivity
  have hs : √c * √(π / c) = √π := by
    rw [← Real.sqrt_mul hc0.le, mul_div_cancel₀ _ hc0.ne']
  rw [integral_trial_sq hc0 hm] at h ⊢
  have he : exp (1 - c) = exp (-(c - 1)) := by ring_nf
  rw [he]
  have : (1 - exp (-(c - 1)) * √c * gE c (herm m ^ 2) / (4 ^ m * ((2 * m).factorial : ℝ)))
      * (4 ^ m * ((2 * m).factorial : ℝ) * √(π / c))
      = 4 ^ m * ((2 * m).factorial : ℝ) * √(π / c)
        - exp (-(c - 1)) * (gE c (herm m ^ 2) * (√c * √(π / c))) := by
    field_simp
  rw [this, hs]
  linarith

end Cvs.Prolate.HermiteTrialResiduals
