import Mathlib
import Cvs.Approximant.ScalingLaplacianMellin
import Cvs.Finite.WindowCoefficientIntertwining
import Cvs.Prolate.HermiteTrialResiduals

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# CCM's algebraic form `W = (θ + ½)² + H − ¼` and the Hermite band at every level

For `C²` `f`, `−((a − v²)f′)′ + κ²v²f = (θ + ½)²f + (−af″ + κ²v²f) − f/4`: at `a = λ²`, `κ = 2πλ` CCM's `W_λ`, at
`t = v/λ` the angular `W_c`, `c = 2πλ²`. On `F_{2m} = pg c (herm m)` of Cvs.Prolate.HermiteTrialResiduals, for every `m`: `H_cF_{2m} = c(4m + 1)F_{2m}`,
`(θ + ½)F_{2m} = −F_{2m+2}/4 + 2m(2m − 1)F_{2m−2}`, and `W_cF_{2m} = μ_mF_{2m} + pg c (rq m)` (`HermiteTrialResiduals`'s `trial_ode`, `m ≤ 2`).
-/

noncomputable section

open Real Polynomial

namespace Cvs.Prolate.CcmAlgebraicFormHermite

open Cvs.Prolate.HermiteTrialResiduals (pg pg₁ pg₂ dq aOp bOp herm hasDerivAt_pg hasDerivAt_pg₁)
open Cvs.Finite.WindowCoefficientIntertwining (negScal2)

/-! ### The operators -/

/-- The scaling operator `(θ + ½)f = v f′ + f/2`. -/
def scal (f : ℝ → ℝ) : ℝ → ℝ := fun v => v * deriv f v + f v / 2

/-- The Hermite-type operator `−a f″ + κ²v² f`; `a = 1`, `κ = c` is `H_c`, `a = 1`, `κ = 2π` is CCM's `H`. -/
def hOp (a κ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun v => -(a * deriv (deriv f) v) + κ ^ 2 * v ^ 2 * f v

/-- The prolate wave operator `−((a − v²)f′)′ + κ²v² f`. -/
def wOp (a κ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun v => -deriv (fun u => (a - u ^ 2) * deriv f u) v + κ ^ 2 * v ^ 2 * f v

/-- **`(θ + ½)² = −negScal2`**: for `C²` `f`, `(θ + ½)((θ + ½)f) = v²f″ + 2vf′ + f/4`. -/
theorem scal_scal {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : scal (scal f) = fun v => -negScal2 f v := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  funext v
  have h : HasDerivAt (scal f) (1 * deriv f v + v * deriv (deriv f) v + deriv f v / 2) v :=
    (((hasDerivAt_id v).mul (hdd v).hasDerivAt).add ((hd v).hasDerivAt.div_const 2))
  simp only [scal, h.deriv, negScal2]
  ring

/-- `ScalingLaplacianMellin`'s complex `(θ + ½)²` applied to `f, f′, f″` of a real profile is `−negScal2 f`. -/
theorem scal2_ofReal (f : ℝ → ℝ) (v : ℝ) :
    Cvs.Approximant.ScalingLaplacianMellin.scal2 (fun u => ((f u : ℝ) : ℂ)) (fun u => ((deriv f u : ℝ) : ℂ))
        (fun u => ((deriv (deriv f) u : ℝ) : ℂ)) v
      = ((-negScal2 f v : ℝ) : ℂ) := by
  simp only [Cvs.Approximant.ScalingLaplacianMellin.scal2, negScal2]
  push_cast
  ring

/-! ### The algebraic form -/

/-- **CCM's algebraic form**: for `C²` `f`, `−((a − v²)f′)′ + κ²v²f = (θ + ½)²f + (−af″ + κ²v²f) − f/4`. -/
theorem wOp_eq (a κ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (v : ℝ) :
    wOp a κ f v = -negScal2 f v + hOp a κ f v - f v / 4 := by
  have hdd : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have hp : HasDerivAt (fun u : ℝ => a - u ^ 2) (-(2 * v)) v := by
    simpa using ((hasDerivAt_pow 2 v).const_sub a)
  have h : HasDerivAt (fun u => (a - u ^ 2) * deriv f u)
      (-(2 * v) * deriv f v + (a - v ^ 2) * deriv (deriv f) v) v := hp.mul (hdd v).hasDerivAt
  simp only [wOp, negScal2, hOp]
  rw [h.deriv]
  ring

/-- `λ²H` at `a = λ²`, `κ = 2πλ`: `hOp λ² (2πλ) = λ² · hOp 1 (2π)`. -/
theorem hOp_ccm (lam : ℝ) (f : ℝ → ℝ) (v : ℝ) :
    hOp (lam ^ 2) (2 * π * lam) f v = lam ^ 2 * hOp 1 (2 * π) f v := by
  simp only [hOp]; ring

/-- **CCM's `W_λ = −D² + λ²H − ¼`**, `D² = −(θ + ½)²`, `H = −d² + (2πv)²`, for `C²` `f`. -/
theorem wOp_ccm (lam : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (v : ℝ) :
    wOp (lam ^ 2) (2 * π * lam) f v = -negScal2 f v + lam ^ 2 * hOp 1 (2 * π) f v - f v / 4 := by
  rw [wOp_eq _ _ hf, hOp_ccm]

/-- `(f(λ·))′ = λ f′(λ·)` and `(f(λ·))″ = λ² f″(λ·)`. -/
theorem deriv_comp_mul (lam : ℝ) (f : ℝ → ℝ) :
    deriv (fun t => f (lam * t)) = (fun t => lam * deriv f (lam * t)) ∧
      deriv (deriv fun t => f (lam * t)) = fun t => lam ^ 2 * deriv (deriv f) (lam * t) := by
  have h1 : deriv (fun t => f (lam * t)) = fun t => lam * deriv f (lam * t) := by
    funext t; rw [deriv_comp_mul_left, smul_eq_mul]
  refine ⟨h1, ?_⟩
  rw [h1, deriv_const_mul_field']
  funext t; rw [deriv_comp_mul_left, smul_eq_mul]; ring

/-- **The angular variable**: with `g(t) = f(λt)`, `W_c g(t) = W_λ f(λt)` at `c = 2πλ²` (`λ = √x` gives `c = 2πx`). -/
theorem wOp_comp_mul (lam : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) :
    wOp 1 (2 * π * lam ^ 2) (fun t => f (lam * t)) t = wOp (lam ^ 2) (2 * π * lam) f (lam * t) := by
  have hg : ContDiff ℝ 2 (fun t => f (lam * t)) := hf.comp (contDiff_const.mul contDiff_id)
  obtain ⟨h1, h2⟩ := deriv_comp_mul lam f
  rw [wOp_eq _ _ hg, wOp_eq _ _ hf]
  simp only [negScal2, hOp]
  rw [h2, h1]
  ring

/-! ### Even Hermite polynomials at every level -/

/-- The Hermite operator in `X = y²`: `lag Q = 4XQ″ + (2 − 4X)Q′`, i.e. `d² − 2y d` on `Q(y²)`. -/
def lag (Q : ℝ[X]) : ℝ[X] := 4 * X * derivative (derivative Q) + (2 - 4 * X) * derivative Q

/-- The double raising operator in `X = y²`, `(2y − d)²` on `Q(y²)`. -/
def rais (Q : ℝ[X]) : ℝ[X] :=
  (4 * X - 2) * Q - (8 * X - 2) * derivative Q + 4 * X * derivative (derivative Q)

/-- `aOp = lag − 1`. -/
theorem aOp_eq_lag (Q : ℝ[X]) : aOp Q = lag Q - Q := by
  simp only [aOp, dq, lag, derivative_sub, derivative_mul, derivative_ofNat, zero_mul,
    zero_add]
  ring

/-- `H_{2m+2} = (2y − d)² H_{2m}` in `X = y²`. -/
theorem herm_succ_eq (m : ℕ) : herm (m + 1) = rais (herm m) := rfl

/-- **The commutation `lag ∘ rais = rais ∘ lag − 4 rais`**. -/
theorem lag_rais (Q : ℝ[X]) : lag (rais Q) = rais (lag Q) - 4 * rais Q := by
  simp only [lag, rais, derivative_sub, derivative_add, derivative_mul, derivative_ofNat,
    derivative_X, derivative_one, derivative_zero, zero_mul, zero_add]
  ring

/-- `rais` is linear over constants. -/
theorem rais_C_mul (r : ℝ) (Q : ℝ[X]) : rais (C r * Q) = C r * rais Q := by
  simp only [rais, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

/-- **The Laguerre form of the Hermite equation**: `lag H_{2m} = −4m H_{2m}` for every `m`. -/
theorem lag_herm (m : ℕ) : lag (herm m) = C (-(4 * m : ℝ)) * herm m := by
  induction m with
  | zero =>
    simp [lag, herm]
  | succ m ih =>
    rw [herm_succ_eq, lag_rais, ih, rais_C_mul]
    have : (C (-(4 * (m + 1 : ℕ) : ℝ)) : ℝ[X]) = C (-(4 * m : ℝ)) - 4 := by
      rw [show (4 : ℝ[X]) = C 4 from rfl, ← C_sub]; congr 1; push_cast; ring
    rw [this]; ring

/-- **`HermiteTrialResiduals`'s Hermite equation at every level**: `aOp H_{2m} = −(4m + 1) H_{2m}`. -/
theorem aOp_herm (m : ℕ) : aOp (herm m) = C (-(4 * m + 1 : ℝ)) * herm m := by
  rw [aOp_eq_lag, lag_herm]
  have : (C (-(4 * m + 1 : ℝ)) : ℝ[X]) = C (-(4 * m : ℝ)) - 1 := by
    rw [← C_1, ← C_sub]; congr 1; ring
  rw [this]; ring

/-- The second derivative in `X = y²`: `low Q = 2Q′ + 4XQ″`, i.e. `d²` on `Q(y²)`. -/
def low (Q : ℝ[X]) : ℝ[X] := 2 * derivative Q + 4 * X * derivative (derivative Q)

/-- **The commutation `low ∘ rais = rais ∘ low − 8 lag + 8`**, the `X = y²` form of `[d², (2y − d)²] = 8 − 8(d² − 2yd)`. -/
theorem low_rais (Q : ℝ[X]) : low (rais Q) = rais (low Q) - 8 * lag Q + 8 * Q := by
  simp only [low, lag, rais, derivative_sub, derivative_add, derivative_mul, derivative_ofNat,
    derivative_X, derivative_one, derivative_zero, zero_mul, zero_add]
  ring

/-- **The lowering law**: `d² H_{2m} = 4·2m(2m − 1) H_{2m−2}`, i.e. `low H_{2m} = (16m² − 8m) H_{2m−2}`. -/
theorem low_herm (m : ℕ) : low (herm m) = C (16 * (m : ℝ) ^ 2 - 8 * m) * herm (m - 1) := by
  induction m with
  | zero => simp [low, herm]
  | succ m ih =>
    rw [herm_succ_eq, low_rais, ih, rais_C_mul, lag_herm]
    rcases m with _ | k
    · refine Polynomial.funext fun t => ?_
      simp only [eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, Nat.cast_zero, Nat.zero_sub, zero_add,
        Nat.sub_self, Nat.cast_one]
      ring
    · rw [show k + 1 - 1 = k from rfl, ← herm_succ_eq, show k + 1 + 1 - 1 = k + 1 from rfl]
      refine Polynomial.funext fun t => ?_
      simp only [eval_add, eval_sub, eval_mul, eval_C, eval_ofNat]
      push_cast; ring

/-- The dilation in `X = y²`: `aA Q = 2XQ′ − XQ + Q/2`, the Gaussian conjugate `θ − y² + ½` of `θ + ½`. -/
def aA (Q : ℝ[X]) : ℝ[X] := 2 * X * derivative Q - X * Q + C (1 / 2) * Q

/-- `aA = (low − rais)/4`. -/
theorem aA_eq (Q : ℝ[X]) : aA Q = C (1 / 4) * (low Q - rais Q) := by
  refine Polynomial.funext fun t => ?_
  simp only [aA, low, rais, eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, eval_X]
  ring

/-- **The dilation on the Hermite levels**: `aA H_{2m} = −H_{2m+2}/4 + 2m(2m − 1) H_{2m−2}` for every `m`. -/
theorem aA_herm (m : ℕ) :
    aA (herm m) = C (-1 / 4) * herm (m + 1) + C (4 * (m : ℝ) ^ 2 - 2 * m) * herm (m - 1) := by
  rw [aA_eq, low_herm, ← herm_succ_eq]
  refine Polynomial.funext fun t => ?_
  simp only [eval_add, eval_sub, eval_mul, eval_C]
  ring

theorem aA_add (P Q : ℝ[X]) : aA (P + Q) = aA P + aA Q := by
  simp only [aA, derivative_add]; ring

theorem aA_C_mul (r : ℝ) (Q : ℝ[X]) : aA (C r * Q) = C r * aA Q := by
  simp only [aA, derivative_mul, derivative_C, zero_mul, zero_add]; ring

/-- **`bOp = aA² − ¼`**: `HermiteTrialResiduals`'s `c`-free part is the square of the dilation, less a quarter. -/
theorem bOp_eq_aA (Q : ℝ[X]) : bOp Q = aA (aA Q) - C (1 / 4) * Q := by
  simp only [bOp, aA, dq, derivative_sub, derivative_add, derivative_mul, derivative_ofNat, derivative_X,
    derivative_C, zero_mul, zero_add]
  refine Polynomial.funext fun t => ?_
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, eval_X, eval_pow, eval_one]
  ring

/-- `(2m).descFactorial 4 = (4m² − 2m)(4(m − 1)² − 2(m − 1))` over `ℝ`. -/
theorem descFactorial_eq (m : ℕ) :
    ((2 * m).descFactorial 4 : ℝ) = (4 * (m : ℝ) ^ 2 - 2 * m) * (4 * ((m - 1 : ℕ) : ℝ) ^ 2 - 2 * ((m - 1 : ℕ) : ℝ)) := by
  match m with
  | 0 => simp
  | 1 => simp [Nat.descFactorial]
  | k + 2 =>
    rw [show 2 * (k + 2) = (2 * k + 1) + 3 by ring]
    simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_zero, show k + 2 - 1 = k + 1 from rfl]
    push_cast; ring

/-- **The Jacobi band at every level** (`HermiteTrialResiduals`'s `bOp_herm` without `m ≤ 2`): `bOp H_{2m} = −(8m² + 4m + 3)/4 · H_{2m}
+ H_{2m+4}/16 + (2m)(2m − 1)(2m − 2)(2m − 3) H_{2m−4}`. -/
theorem bOp_herm (m : ℕ) :
    bOp (herm m) = C (-(8 * m ^ 2 + 4 * m + 3) / 4 : ℝ) * herm m
      + C (1 / 16 : ℝ) * herm (m + 2) + C ((2 * m).descFactorial 4 : ℝ) * herm (m - 2) := by
  rw [bOp_eq_aA, aA_herm, aA_add, aA_C_mul, aA_C_mul, aA_herm, aA_herm, descFactorial_eq]
  match m with
  | 0 =>
    refine Polynomial.funext fun t => ?_
    simp only [eval_add, eval_sub, eval_mul, eval_C]
    push_cast; ring
  | 1 =>
    refine Polynomial.funext fun t => ?_
    simp only [eval_add, eval_sub, eval_mul, eval_C, show (1 : ℕ) - 1 = 0 from rfl,
      show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 + 1 = 1 + 2 from rfl]
    push_cast; ring
  | k + 2 =>
    refine Polynomial.funext fun t => ?_
    simp only [eval_add, eval_sub, eval_mul, eval_C, show k + 2 - 1 = k + 1 from rfl, show k + 1 + 1 = k + 2 from rfl,
      show k + 1 - 1 = k from rfl, show k + 2 + 1 + 1 = k + 2 + 2 from rfl, show k + 2 + 1 - 1 = k + 2 from rfl,
      show k + 2 - 2 = k from rfl]
    push_cast; ring

/-- **The Jacobi band of the prolate operator at every level** (`HermiteTrialResiduals`'s `trial_ode` without `m ≤ 2`):
`(1 − w²)F″ − 2wF′ − c²w²F + μ_mF = −pg c (rq m)` for `F = F_{2m}`. -/
theorem trial_ode (m : ℕ) (c w : ℝ) :
    (1 - w ^ 2) * pg₂ c (herm m) w - 2 * w * pg₁ c (herm m) w - c ^ 2 * w ^ 2 * pg c (herm m) w
      + Cvs.Prolate.HermiteTrialResiduals.mu c m * pg c (herm m) w = -pg c (Cvs.Prolate.HermiteTrialResiduals.rq m) w := by
  rw [Cvs.Prolate.HermiteTrialResiduals.prolateOp_pg, aOp_herm, bOp_herm]
  simp only [pg, Cvs.Prolate.HermiteTrialResiduals.rq, Cvs.Prolate.HermiteTrialResiduals.mu, eval_add, eval_mul, eval_C]
  ring

/-! ### The operators on the trials `pg c Q` -/

/-- `pg c Q` is smooth. -/
theorem contDiff_pg (c : ℝ) (Q : ℝ[X]) (n : WithTop ℕ∞) : ContDiff ℝ n (pg c Q) := by
  have hQ : ContDiff ℝ n (fun y : ℝ => Q.eval y) := by
    simpa [Polynomial.coe_aeval_eq_eval] using Q.contDiff_aeval (𝕜 := ℝ) n
  unfold pg
  exact (hQ.comp (contDiff_const.mul (contDiff_id.pow 2))).mul (by fun_prop)

/-- `pg c Q′ = pg₁ c Q` and `pg c Q″ = pg₂ c Q`. -/
theorem deriv_pg (c : ℝ) (Q : ℝ[X]) :
    deriv (pg c Q) = pg₁ c Q ∧ deriv (deriv (pg c Q)) = pg₂ c Q := by
  have h1 : deriv (pg c Q) = pg₁ c Q := funext fun w => (hasDerivAt_pg c Q w).deriv
  exact ⟨h1, by rw [h1]; exact funext fun w => (hasDerivAt_pg₁ c Q w).deriv⟩

/-- **`θ + ½` on the trials**: `(θ + ½)(pg c Q) = pg c (aA Q)`. -/
theorem scal_pg (c : ℝ) (Q : ℝ[X]) : scal (pg c Q) = pg c (aA Q) := by
  obtain ⟨h1, -⟩ := deriv_pg c Q
  funext w
  simp only [scal, h1, Cvs.Prolate.HermiteTrialResiduals.pg₁, pg, dq, aA, eval_sub, eval_add, eval_mul, eval_X, eval_C, eval_ofNat]
  ring

/-- **The dilation is tridiagonal on the Hermite functions**: `(θ + ½)F_{2m} = −F_{2m+2}/4 + 2m(2m − 1)F_{2m−2}`. -/
theorem scal_herm (c : ℝ) (m : ℕ) (w : ℝ) :
    scal (pg c (herm m)) w = -(1 / 4) * pg c (herm (m + 1)) w + (4 * (m : ℝ) ^ 2 - 2 * m) * pg c (herm (m - 1)) w := by
  rw [scal_pg, aA_herm]
  simp only [pg, eval_add, eval_mul, eval_C]
  ring

/-- **`H_c` on the trials**: `H_c(pg c Q) = −c · pg c (aOp Q)`. -/
theorem hOp_pg (c : ℝ) (Q : ℝ[X]) (w : ℝ) : hOp 1 c (pg c Q) w = -c * pg c (aOp Q) w := by
  obtain ⟨-, h2⟩ := deriv_pg c Q
  simp only [hOp, h2, pg₂, pg, aOp, eval_sub, eval_add, eval_mul, eval_X]
  ring

/-- **`θ(θ + 1)` on the trials**: `(θ + ½)²(pg c Q) − pg c Q/4 = pg c (bOp Q)`. -/
theorem thetaTheta_pg (c : ℝ) (Q : ℝ[X]) (w : ℝ) :
    -negScal2 (pg c Q) w - pg c Q w / 4 = pg c (bOp Q) w := by
  obtain ⟨h1, h2⟩ := deriv_pg c Q
  simp only [negScal2]
  rw [h2, h1]
  simp only [pg₂, pg₁, pg, bOp, eval_add, eval_mul, eval_X, eval_pow, eval_ofNat]
  ring

/-- `HermiteTrialResiduals`'s prolate operator is `−W_c`: `W_c(pg c Q) = pg c (bOp Q) − c · pg c (aOp Q)`. -/
theorem wOp_pg (c : ℝ) (Q : ℝ[X]) (w : ℝ) :
    wOp 1 c (pg c Q) w = pg c (bOp Q) w - c * pg c (aOp Q) w
      ∧ wOp 1 c (pg c Q) w
        = -((1 - w ^ 2) * pg₂ c Q w - 2 * w * pg₁ c Q w - c ^ 2 * w ^ 2 * pg c Q w) := by
  have h := wOp_eq 1 c (contDiff_pg c Q 2) w
  rw [hOp_pg] at h
  refine ⟨by rw [h, ← thetaTheta_pg]; ring, ?_⟩
  rw [Cvs.Prolate.HermiteTrialResiduals.prolateOp_pg, h, ← thetaTheta_pg]; ring

/-- `pg c (C r * Q) = r · pg c Q`. -/
theorem pg_C_mul (c r : ℝ) (Q : ℝ[X]) (w : ℝ) : pg c (C r * Q) w = r * pg c Q w := by
  simp only [pg, eval_mul, eval_C]; ring

/-- **The Hermite eigen-equation**: `H_c F_{2m} = c(4m + 1) F_{2m}` for `F_{2m} = pg c (herm m)` and every `m`. -/
theorem hOp_herm (c : ℝ) (m : ℕ) (w : ℝ) :
    hOp 1 c (pg c (herm m)) w = c * (4 * m + 1) * pg c (herm m) w := by
  rw [hOp_pg, aOp_herm, pg_C_mul]; ring

/-- **CCM's grading on the level `m`**: `W_c F_{2m} = (θ + ½)²F_{2m} + (c(4m + 1) − ¼)F_{2m}`. -/
theorem wOp_herm (c : ℝ) (m : ℕ) (w : ℝ) :
    wOp 1 c (pg c (herm m)) w
      = -negScal2 (pg c (herm m)) w + (c * (4 * m + 1) - 1 / 4) * pg c (herm m) w := by
  rw [wOp_eq 1 c (contDiff_pg c _ 2), hOp_herm]; ring

/-- **The prolate operator on `F_{2m}` at every level**: `W_cF_{2m} = μ_mF_{2m} + pg c (rq m)`. -/
theorem wOp_herm_band (c : ℝ) (m : ℕ) (w : ℝ) :
    wOp 1 c (pg c (herm m)) w = Cvs.Prolate.HermiteTrialResiduals.mu c m * pg c (herm m) w + pg c (Cvs.Prolate.HermiteTrialResiduals.rq m) w := by
  rw [(wOp_pg c (herm m) w).2]
  linarith [trial_ode m c w]

end Cvs.Prolate.CcmAlgebraicFormHermite
