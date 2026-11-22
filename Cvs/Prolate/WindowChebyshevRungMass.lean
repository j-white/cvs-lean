import Mathlib
import Cvs.Approximant.XiKrylovHermiteSpan
import Cvs.Finite.WindowCoefficientIntertwining
import Cvs.Prolate.CcmAlgebraicFormHermite
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Xi.NodeValuesWindowImage

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window Chebyshev bound: rung mass of the level `E_N` above `χ = M` is `≤ c(4N + 1)‖f‖²_ℝ/M`

On `P(w)e^{−cw²/2}`, `c > 0`: `θ + ½` is antisymmetric and `H_c` symmetric in `L²(ℝ)`, the `F_{2k}` are orthogonal, so
`⟨H_cf, f⟩_ℝ ≤ c(4N + 1)‖f‖²_ℝ` on `E_N`; the window energy `∫_{−1}^1 f·W_cf` is at most `⟨H_cf, f⟩_ℝ`, and Parseval
(Cvs.Prolate.EvenRungParseval) with the Green identity (Cvs.Prolate.EvenRungDavisKahan) gives `M Σ_{χ_k ≥ M}(∫_{−1}^1 fh_k)² ≤ c(4N + 1)‖f‖²_ℝ`. On the line,
`⟨W_cF_{2m}, F_{2m}⟩_ℝ = μ_m‖F_{2m}‖²_ℝ` (Cvs.Prolate.CcmAlgebraicFormHermite). The `Ξ` ladder `u_j ∈ E_{2j+2}` has mass `≤ (8j + 9)/c · ‖u_j‖²_ℝ` on `χ ≥ c²`.
-/

noncomputable section

open Real Polynomial MeasureTheory

namespace Cvs.Prolate.WindowChebyshevRungMass
open Cvs.ZeroCounting

open Cvs.Prolate.HermiteTrialResiduals (pg herm)
open Cvs.Finite.WindowCoefficientIntertwining (negScal2)

variable {c : ℝ}

/-! ### Polynomial–Gaussian calculus -/

/-- `P(w)e^{−cw²/2}` for any real polynomial `P`. -/
def pgw (c : ℝ) (P : ℝ[X]) (w : ℝ) : ℝ := P.eval w * exp (-(c / 2) * w ^ 2)

/-- The derivative polynomial `P′ − cXP`, so that `(pgw c P)′ = pgw c (P′ − cXP)`. -/
def dL (c : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] := derivative - LinearMap.mulLeft ℝ (C c * X)

/-- The scaling polynomial `X·dL P + P/2`, so that `(θ + ½) pgw c P = pgw c (sL P)`. -/
def sL (c : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] := LinearMap.mulLeft ℝ X ∘ₗ dL c + (1 / 2 : ℝ) • LinearMap.id

/-- The Hermite polynomial operator `−dL(dL P) + c²X²P`, so that `H_c pgw c P = pgw c (hL P)`. -/
def hL (c : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] := -(dL c ∘ₗ dL c) + LinearMap.mulLeft ℝ (C (c ^ 2) * X ^ 2)

theorem dL_apply (P : ℝ[X]) : dL c P = derivative P - C c * X * P := rfl

theorem sL_apply (P : ℝ[X]) : sL c P = X * dL c P + C (1 / 2) * P := by
  simp [sL, smul_eq_C_mul]

theorem hL_apply (P : ℝ[X]) : hL c P = -dL c (dL c P) + C (c ^ 2) * X ^ 2 * P := by
  simp [hL, mul_assoc]

theorem hasDerivAt_pgw (c : ℝ) (P : ℝ[X]) (w : ℝ) : HasDerivAt (pgw c P) (pgw c (dL c P) w) w := by
  have h2 : HasDerivAt (fun w : ℝ => -(c / 2) * w ^ 2) (-(c / 2) * (2 * w)) w := by
    simpa using (hasDerivAt_pow 2 w).const_mul (-(c / 2))
  refine ((P.hasDerivAt w).mul h2.exp).congr_deriv ?_
  simp only [pgw, dL_apply, eval_sub, eval_mul, eval_C, eval_X]
  ring

theorem deriv_pgw (c : ℝ) (P : ℝ[X]) : deriv (pgw c P) = pgw c (dL c P) :=
  funext fun w => (hasDerivAt_pgw c P w).deriv

theorem contDiff_pgw (c : ℝ) (P : ℝ[X]) (n : WithTop ℕ∞) : ContDiff ℝ n (pgw c P) := by
  have hP : ContDiff ℝ n (fun y : ℝ => P.eval y) := by
    simpa [Polynomial.coe_aeval_eq_eval] using P.contDiff_aeval (𝕜 := ℝ) n
  unfold pgw
  exact hP.mul (by fun_prop)

/-- `HermiteTrialResiduals`'s trial in the window variable: `pg c Q = pgw c (Q(cX²))`. -/
theorem pg_eq_pgw (c : ℝ) (Q : ℝ[X]) : pg c Q = pgw c (Q.comp (C c * X ^ 2)) := by
  funext w; simp [pg, pgw, eval_comp]

theorem pgw_add (P R : ℝ[X]) : pgw c (P + R) = pgw c P + pgw c R := by
  funext w; simp only [pgw, eval_add, Pi.add_apply]; ring

theorem pgw_C_mul (r : ℝ) (P : ℝ[X]) : pgw c (C r * P) = fun w => r * pgw c P w := by
  funext w; simp only [pgw, eval_mul, eval_C]; ring

/-- `pgw` is injective in the polynomial. -/
theorem pgw_injective {P R : ℝ[X]} (h : pgw c P = pgw c R) : P = R := by
  refine Polynomial.funext fun w => ?_
  have := congrFun h w
  simp only [pgw] at this
  exact mul_right_cancel₀ (exp_pos _).ne' this

/-- `pgw c P · pgw c R = (PR)(w) e^{−cw²}`. -/
theorem pgw_mul (P R : ℝ[X]) (w : ℝ) : pgw c P w * pgw c R w = (P * R).eval w * exp (-c * w ^ 2) := by
  simp only [pgw, eval_mul]
  rw [show P.eval w * exp (-(c / 2) * w ^ 2) * (R.eval w * exp (-(c / 2) * w ^ 2))
      = P.eval w * R.eval w * (exp (-(c / 2) * w ^ 2) * exp (-(c / 2) * w ^ 2)) by ring, ← exp_add]
  congr 2; ring

/-- Every `P(w)e^{−bw²}`, `b > 0`, is integrable on `ℝ`. -/
theorem integrable_eval_mul_gauss {b : ℝ} (hb : 0 < b) (P : ℝ[X]) :
    Integrable fun w : ℝ => P.eval w * exp (-b * w ^ 2) := by
  induction P using Polynomial.induction_on' with
  | add P R hP hR =>
    refine (hP.add hR).congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply, eval_add, add_mul]
  | monomial n a =>
    have hn : (-1 : ℝ) < n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have h := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (n : ℝ)) hn).const_mul a
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [eval_monomial, Real.rpow_natCast]; ring

/-! ### The Gaussian functional -/

/-- The Gaussian functional `I(P) = ∫ P(w)e^{−cw²} dw` as a linear map. -/
def IL (c : ℝ) (hc : 0 < c) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := ∫ w, P.eval w * exp (-c * w ^ 2)
  map_add' P R := by
    simp only [eval_add, add_mul]
    exact integral_add (integrable_eval_mul_gauss hc P) (integrable_eval_mul_gauss hc R)
  map_smul' r P := by
    simp only [eval_smul, smul_eq_mul, mul_assoc, RingHom.id_apply]
    exact integral_const_mul r _

theorem IL_apply (hc : 0 < c) (P : ℝ[X]) : IL c hc P = ∫ w, P.eval w * exp (-c * w ^ 2) := rfl

/-- `∫ pgw c P · pgw c R = I(PR)`. -/
theorem integral_pgw_mul (hc : 0 < c) (P R : ℝ[X]) : ∫ w, pgw c P w * pgw c R w = IL c hc (P * R) := by
  simp_rw [pgw_mul]; rfl

theorem integrable_pgw_mul (hc : 0 < c) (P R : ℝ[X]) : Integrable fun w => pgw c P w * pgw c R w := by
  simp_rw [pgw_mul]; exact integrable_eval_mul_gauss hc _

/-- `I(P²) ≥ 0`. -/
theorem IL_sq_nonneg (hc : 0 < c) (P : ℝ[X]) : 0 ≤ IL c hc (P * P) := by
  rw [← integral_pgw_mul]
  exact integral_nonneg fun w => mul_self_nonneg _

/-- **Integration by parts on `ℝ`**: `I(dL P · R) = −I(P · dL R)`. -/
theorem IL_dL_mul (hc : 0 < c) (P R : ℝ[X]) : IL c hc (dL c P * R) = -IL c hc (P * dL c R) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := pgw c R) (v := pgw c P)
    (u' := pgw c (dL c R)) (v' := pgw c (dL c P))
    (fun w _ => hasDerivAt_pgw c R w) (fun w _ => hasDerivAt_pgw c P w)
    (integrable_pgw_mul hc R (dL c P)) (integrable_pgw_mul hc (dL c R) P) (integrable_pgw_mul hc R P)
  rw [integral_pgw_mul hc, integral_pgw_mul hc] at h
  rw [mul_comm (dL c P), h, mul_comm (dL c R)]

/-- **`θ + ½` is antisymmetric**: `I(sL P · R) = −I(P · sL R)`. -/
theorem IL_sL_mul (hc : 0 < c) (P R : ℝ[X]) : IL c hc (sL c P * R) = -IL c hc (P * sL c R) := by
  have e1 : sL c P * R = dL c P * (X * R) + C (1 / 2) * (P * R) := by rw [sL_apply]; ring
  have e2 : dL c (X * R) = R + X * dL c R := by
    simp only [dL_apply, derivative_mul, derivative_X]; ring
  have e3 : P * sL c R = P * (X * dL c R) + C (1 / 2) * (P * R) := by rw [sL_apply]; ring
  have hC : ∀ Q : ℝ[X], IL c hc (C (1 / 2) * Q) = 1 / 2 * IL c hc Q := fun Q => by
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  rw [e1, e3, map_add, map_add, IL_dL_mul, e2, hC, mul_add, map_add]
  ring

/-- **`H_c` is symmetric**: `I(hL P · R) = I(P · hL R)`. -/
theorem IL_hL_mul (hc : 0 < c) (P R : ℝ[X]) : IL c hc (hL c P * R) = IL c hc (P * hL c R) := by
  have e1 : hL c P * R = -(dL c (dL c P) * R) + C (c ^ 2) * (X ^ 2 * P * R) := by rw [hL_apply]; ring
  have e2 : P * hL c R = -(P * dL c (dL c R)) + C (c ^ 2) * (X ^ 2 * P * R) := by rw [hL_apply]; ring
  rw [e1, e2, map_add, map_add, map_neg, map_neg, IL_dL_mul, ← IL_dL_mul hc P (dL c R)]
  ring

/-! ### The operators on `pgw` -/

theorem scal_pgw (c : ℝ) (P : ℝ[X]) : Cvs.Prolate.CcmAlgebraicFormHermite.scal (pgw c P) = pgw c (sL c P) := by
  funext w; simp only [Cvs.Prolate.CcmAlgebraicFormHermite.scal, deriv_pgw, pgw, sL_apply, eval_add, eval_mul, eval_X, eval_C]; ring

theorem negScal2_pgw (c : ℝ) (P : ℝ[X]) : negScal2 (pgw c P) = fun w => -pgw c (sL c (sL c P)) w := by
  have h := Cvs.Prolate.CcmAlgebraicFormHermite.scal_scal (contDiff_pgw c P 2)
  rw [scal_pgw, scal_pgw] at h
  funext w; rw [h]; ring

theorem hOp_pgw (c : ℝ) (P : ℝ[X]) : Cvs.Prolate.CcmAlgebraicFormHermite.hOp 1 c (pgw c P) = pgw c (hL c P) := by
  funext w; simp only [Cvs.Prolate.CcmAlgebraicFormHermite.hOp, deriv_pgw, pgw, hL_apply, eval_add, eval_neg, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- `W_c pgw c P = pgw c (sL(sL P) + hL P − P/4)`. -/
theorem wOp_pgw (c : ℝ) (P : ℝ[X]) :
    Cvs.Prolate.CcmAlgebraicFormHermite.wOp 1 c (pgw c P) = pgw c (sL c (sL c P) + hL c P - C (1 / 4) * P) := by
  funext w
  rw [Cvs.Prolate.CcmAlgebraicFormHermite.wOp_eq 1 c (contDiff_pgw c P 2), negScal2_pgw, hOp_pgw]
  simp only [pgw, eval_add, eval_sub, eval_mul, eval_C]; ring

/-! ### The Hermite levels -/

/-- The even Hermite function `F_{2k} = pg c (herm k)` as a `pgw` polynomial. -/
def hw (c : ℝ) (k : ℕ) : ℝ[X] := (herm k).comp (C c * X ^ 2)

/-- **The eigen-equation in polynomial form**: `hL (hw k) = c(4k + 1) hw k`. -/
theorem hL_hw (c : ℝ) (k : ℕ) : hL c (hw c k) = C (c * (4 * k + 1)) * hw c k := by
  refine pgw_injective (c := c) ?_
  rw [← hOp_pgw, hw, ← pg_eq_pgw, pgw_C_mul, ← pg_eq_pgw]
  funext w; exact Cvs.Prolate.CcmAlgebraicFormHermite.hOp_herm c k w

/-- **Orthogonality of the Hermite levels**: `∫ F_{2k}F_{2l} = 0` for `k ≠ l`. -/
theorem IL_hw_mul_hw (hc : 0 < c) {k l : ℕ} (hkl : k ≠ l) : IL c hc (hw c k * hw c l) = 0 := by
  have h := IL_hL_mul hc (hw c k) (hw c l)
  have h1 : hL c (hw c k) * hw c l = C (c * (4 * k + 1)) * (hw c k * hw c l) := by rw [hL_hw]; ring
  have h2 : hw c k * hL c (hw c l) = C (c * (4 * l + 1)) * (hw c k * hw c l) := by rw [hL_hw]; ring
  rw [h1, h2, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  have hne : c * (4 * k + 1) - c * (4 * l + 1) ≠ 0 := by
    have : (k : ℝ) ≠ l := by exact_mod_cast hkl
    intro h0; apply this; nlinarith [mul_pos hc hc]
  have : (c * (4 * k + 1) - c * (4 * l + 1)) * IL c hc (hw c k * hw c l) = 0 := by
    linarith
  exact (mul_eq_zero.1 this).resolve_left hne

/-- **The energy bound on the level**: if `P = Σ_{k ∈ s} a_k F_{2k}` with `s ⊆ {k ≤ N}`, then
`I(hL P · P) ≤ c(4N + 1) I(P²)`. -/
theorem IL_hL_le (hc : 0 < c) {N : ℕ} (s : Finset ℕ) (hs : ∀ k ∈ s, k ≤ N) (a : ℕ → ℝ) :
    IL c hc (hL c (∑ k ∈ s, a k • hw c k) * ∑ k ∈ s, a k • hw c k)
      ≤ c * (4 * N + 1) * IL c hc ((∑ k ∈ s, a k • hw c k) * ∑ k ∈ s, a k • hw c k) := by
  have diag : ∀ g : ℕ → ℝ, (∀ k l, k ≠ l → g k = 0 ∨ IL c hc (hw c k * hw c l) = 0) →
      IL c hc ((∑ k ∈ s, (a k * g k) • hw c k) * ∑ k ∈ s, a k • hw c k)
        = ∑ k ∈ s, a k ^ 2 * g k * IL c hc (hw c k * hw c k) := by
    intro g _
    rw [Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [map_sum, Finset.sum_eq_single k]
    · rw [smul_mul_smul_comm, map_smul, smul_eq_mul]; ring
    · intro l _ hlk
      rw [smul_mul_smul_comm, map_smul, IL_hw_mul_hw hc (Ne.symm hlk), smul_zero]
    · intro h; exact absurd hk h
  have hH : hL c (∑ k ∈ s, a k • hw c k) = ∑ k ∈ s, (a k * (c * (4 * k + 1))) • hw c k := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hL_hw, ← smul_eq_C_mul, smul_smul]
  have h1 := diag (fun k => c * (4 * k + 1)) (fun k l h => Or.inr (IL_hw_mul_hw hc h))
  have h0 := diag (fun _ => 1) (fun k l h => Or.inr (IL_hw_mul_hw hc h))
  simp only [mul_one] at h0
  rw [hH, h1, h0, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hs k hk
  have hI := IL_sq_nonneg hc (hw c k)
  have : c * (4 * k + 1) ≤ c * (4 * N + 1) := by nlinarith
  have hsq : 0 ≤ a k ^ 2 * IL c hc (hw c k * hw c k) := mul_nonneg (sq_nonneg _) hI
  nlinarith

/-- A member of the level space `E_N` is `pgw c P` with `P = Σ_{k ≤ N} a_k F_{2k}`. -/
theorem exists_of_mem_level {N : ℕ} {f : ℝ → ℝ} (hf : f ∈ Cvs.Approximant.XiKrylovHermiteSpan.level c N) :
    ∃ a : ℕ → ℝ, f = pgw c (∑ k ∈ Finset.Iic N, a k • hw c k) := by
  rw [Cvs.Approximant.XiKrylovHermiteSpan.level, ← Finset.coe_Iic, Submodule.mem_span_image_finset_iff_exists_fun'] at hf
  obtain ⟨a, ha⟩ := hf
  refine ⟨a, ?_⟩
  rw [← ha]
  funext w
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pgw, eval_finsetSum, eval_smul, Finset.sum_mul,
    pg_eq_pgw, hw]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### The bounds on functions -/

/-- **`(θ + ½)²` is negative semidefinite**: `∫ (θ + ½)²f · f = −∫ ((θ + ½)f)² ≤ 0` on `pgw c P`. -/
theorem integral_scal2_mul_self (hc : 0 < c) (P : ℝ[X]) :
    ∫ w, -negScal2 (pgw c P) w * pgw c P w = -∫ w, Cvs.Prolate.CcmAlgebraicFormHermite.scal (pgw c P) w ^ 2
      ∧ ∫ w, -negScal2 (pgw c P) w * pgw c P w ≤ 0 := by
  have e : ∫ w, -negScal2 (pgw c P) w * pgw c P w = IL c hc (sL c (sL c P) * P) := by
    rw [negScal2_pgw, ← integral_pgw_mul hc]; simp
  have e2 : ∫ w, Cvs.Prolate.CcmAlgebraicFormHermite.scal (pgw c P) w ^ 2 = IL c hc (sL c P * sL c P) := by
    rw [scal_pgw, ← integral_pgw_mul hc]; simp [sq]
  rw [e, e2, IL_sL_mul]
  exact ⟨rfl, neg_nonpos.2 (IL_sq_nonneg hc _)⟩

/-- **The Hermite bound on `E_N`**: `∫ H_cf · f ≤ c(4N + 1) ∫ f²`. -/
theorem integral_hOp_le (hc : 0 < c) {N : ℕ} {f : ℝ → ℝ} (hf : f ∈ Cvs.Approximant.XiKrylovHermiteSpan.level c N) :
    ∫ w, Cvs.Prolate.CcmAlgebraicFormHermite.hOp 1 c f w * f w ≤ c * (4 * N + 1) * ∫ w, f w ^ 2 := by
  obtain ⟨a, rfl⟩ := exists_of_mem_level hf
  simp_rw [hOp_pgw, sq, integral_pgw_mul hc]
  exact IL_hL_le hc _ (fun k hk => Finset.mem_Iic.1 hk) a

/-- **The line form on the level**: on `E_N`, `∫_ℝ W_cf · f ≤ (c(4N + 1) − ¼) ∫_ℝ f²`. -/
theorem integral_wOp_le (hc : 0 < c) {N : ℕ} {f : ℝ → ℝ} (hf : f ∈ Cvs.Approximant.XiKrylovHermiteSpan.level c N) :
    ∫ w, Cvs.Prolate.CcmAlgebraicFormHermite.wOp 1 c f w * f w ≤ (c * (4 * N + 1) - 1 / 4) * ∫ w, f w ^ 2 := by
  have hH := integral_hOp_le hc hf
  obtain ⟨a, rfl⟩ := exists_of_mem_level hf
  set P := ∑ k ∈ Finset.Iic N, a k • hw c k
  have hS := (integral_scal2_mul_self hc P).2
  rw [negScal2_pgw] at hS
  simp only [neg_neg] at hS
  simp_rw [hOp_pgw, sq, integral_pgw_mul hc] at hH ⊢
  rw [integral_pgw_mul hc] at hS
  have e : (sL c (sL c P) + hL c P - C (1 / 4) * P) * P = sL c (sL c P) * P + hL c P * P - C (1 / 4) * (P * P) := by
    ring
  rw [wOp_pgw, integral_pgw_mul hc, e, map_sub, map_add, ← smul_eq_C_mul, map_smul, smul_eq_mul]
  linarith

/-- The line form on the `Ξ` ladder: at `c = 2πx > 0`, `u_j = (−(θ + ½)²)^jG_Ξ` has
`∫_ℝ W_cu_j · u_j ≤ (c(8j + 9) − ¼) ∫_ℝ u_j²`. -/
theorem integral_wOp_ladder_le {x : ℝ} (hx : 0 < x) (j : ℕ) :
    ∫ w, Cvs.Prolate.CcmAlgebraicFormHermite.wOp 1 (2 * π * x) (negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x)) w * negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) w
      ≤ (2 * π * x * (8 * j + 9) - 1 / 4) * ∫ w, negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) w ^ 2 := by
  have h := integral_wOp_le (by positivity) (Cvs.Approximant.XiKrylovHermiteSpan.ladder_mem_level x j)
  push_cast at h
  convert h using 2; ring

/-- **The exact line diagonal**: `∫_ℝ W_cF_{2m} · F_{2m} = μ_m ∫_ℝ F_{2m}²` for every `m`, `c > 0`. -/
theorem integral_wOp_herm_mul_self (hc : 0 < c) (m : ℕ) :
    ∫ w, Cvs.Prolate.CcmAlgebraicFormHermite.wOp 1 c (pg c (herm m)) w * pg c (herm m) w = Cvs.Prolate.HermiteTrialResiduals.mu c m * ∫ w, pg c (herm m) w ^ 2 := by
  have hR : ∫ w, pg c (Cvs.Prolate.HermiteTrialResiduals.rq m) w * pg c (herm m) w = 0 := by
    have e : (Cvs.Prolate.HermiteTrialResiduals.rq m).comp (C c * X ^ 2)
        = C (1 / 16 : ℝ) * hw c (m + 2) + C ((2 * m).descFactorial 4 : ℝ) * hw c (m - 2) := by
      simp only [Cvs.Prolate.HermiteTrialResiduals.rq, hw, add_comp, mul_comp, C_comp]
    rw [pg_eq_pgw, pg_eq_pgw, integral_pgw_mul hc, e, ← hw, add_mul, map_add, mul_assoc, mul_assoc,
      ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul, map_smul, IL_hw_mul_hw hc (by omega), smul_zero, zero_add,
      smul_eq_mul]
    rcases Nat.lt_or_ge m 2 with h | h
    · have : ((2 * m).descFactorial 4 : ℝ) = 0 := by exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
      rw [this, zero_mul]
    · rw [IL_hw_mul_hw hc (by omega), mul_zero]
  have hi : ∀ Q : ℝ[X], Integrable fun w => pg c Q w * pg c (herm m) w := fun Q => by
    simp only [pg_eq_pgw]; exact integrable_pgw_mul hc _ _
  have e : (fun w => Cvs.Prolate.CcmAlgebraicFormHermite.wOp 1 c (pg c (herm m)) w * pg c (herm m) w)
      = fun w => Cvs.Prolate.HermiteTrialResiduals.mu c m * (pg c (herm m) w * pg c (herm m) w) + pg c (Cvs.Prolate.HermiteTrialResiduals.rq m) w * pg c (herm m) w := by
    funext w; rw [Cvs.Prolate.CcmAlgebraicFormHermite.wOp_herm_band]; ring
  rw [e, integral_add ((hi _).const_mul _) (hi _), hR, add_zero, integral_const_mul]
  simp only [sq]

/-! ### The window: a Chebyshev bound on the prolate mass -/

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx lev rung)
open Cvs.Prolate.EvenRungParseval (LevelIdx)

/-- A member of the level space is even. -/
theorem pgw_hw_sum_neg (c : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (w : ℝ) :
    pgw c (∑ k ∈ s, a k • hw c k) (-w) = pgw c (∑ k ∈ s, a k • hw c k) w := by
  simp [pgw, hw, eval_finsetSum, eval_comp]

/-- The derivative of an even function is odd. -/
theorem deriv_neg_of_even {f : ℝ → ℝ} (hf : ∀ w, f (-w) = f w) (s : ℝ) : deriv f (-s) = -deriv f s := by
  have h := deriv_comp_neg (f := f) (x := s)
  rw [show (fun x => f (-x)) = f from funext hf] at h
  linarith

/-- The derivative of an odd function is even. -/
theorem deriv_neg_of_odd {g : ℝ → ℝ} (hg : ∀ w, g (-w) = -g w) (s : ℝ) : deriv g (-s) = deriv g s := by
  have h := deriv_comp_neg (f := g) (x := s)
  rw [show (fun x => g (-x)) = -g from funext hg, deriv.neg] at h
  linarith

/-- **The window energy is at most the line energy**: for `f = pgw c P`, `c > 0`,
`∫_{−1}^1 f · W_cf ≤ ∫_ℝ H_cf · f`. -/
theorem integral_window_le (hc : 0 < c) (P : ℝ[X]) :
    ∫ s in (-1 : ℝ)..1, pgw c P s * -((1 - s ^ 2) * pgw c (dL c (dL c P)) s - 2 * s * pgw c (dL c P) s
        - c ^ 2 * s ^ 2 * pgw c P s)
      ≤ IL c hc (hL c P * P) := by
  set F := pgw c P
  set F₁ := pgw c (dL c P)
  set F₂ := pgw c (dL c (dL c P))
  have cF : Continuous F := (contDiff_pgw c P 0).continuous
  have cF₁ : Continuous F₁ := (contDiff_pgw c _ 0).continuous
  have cF₂ : Continuous F₂ := (contDiff_pgw c _ 0).continuous
  have ci : ∀ {u : ℝ → ℝ}, Continuous u → IntervalIntegrable u volume (-1) 1 := fun h => h.intervalIntegrable _ _
  -- one integration by parts on `[−1, 1]`; the flux `(1 − s²)F′F` vanishes at `±1`
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -1) (b := 1) (u := F)
    (v := fun s => (1 - s ^ 2) * F₁ s) (u' := F₁) (v' := fun s => -(2 * s) * F₁ s + (1 - s ^ 2) * F₂ s)
    (fun s _ => hasDerivAt_pgw c P s)
    (fun s _ => by
      have h1 : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := by
        simpa using (hasDerivAt_pow 2 s).const_sub 1
      exact h1.mul (hasDerivAt_pgw c (dL c P) s))
    (ci cF₁) (ci (by fun_prop))
  have hA : ∫ s in (-1 : ℝ)..1, F s * (-(2 * s) * F₁ s + (1 - s ^ 2) * F₂ s)
      = -∫ s in (-1 : ℝ)..1, (1 - s ^ 2) * F₁ s ^ 2 := by
    rw [ibp]
    simp only [show (1 : ℝ) - 1 ^ 2 = 0 by norm_num, show (1 : ℝ) - (-1) ^ 2 = 0 by norm_num, zero_mul, mul_zero,
      sub_zero, zero_sub]
    congr 1
    exact intervalIntegral.integral_congr fun s _ => by ring
  have e : (fun s => F s * -((1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s))
      = fun s => -(F s * (-(2 * s) * F₁ s + (1 - s ^ 2) * F₂ s)) + c ^ 2 * s ^ 2 * F s ^ 2 := by
    funext s; ring
  have e1 : ∫ s in (-1 : ℝ)..1, F s * -((1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s)
      = ∫ s in (-1 : ℝ)..1, ((1 - s ^ 2) * F₁ s ^ 2 + c ^ 2 * s ^ 2 * F s ^ 2) := by
    rw [e, intervalIntegral.integral_add (ci (by fun_prop)) (ci (by fun_prop)), intervalIntegral.integral_neg, hA,
      neg_neg, intervalIntegral.integral_add (ci (by fun_prop)) (ci (by fun_prop))]
  rw [e1]
  -- the line energy `∫ F′² + c²s²F²`
  have iB : Integrable fun s => c ^ 2 * s ^ 2 * F s ^ 2 := by
    refine ((integrable_eval_mul_gauss hc (X ^ 2 * P * P)).const_mul (c ^ 2)).congr
      (Filter.Eventually.of_forall fun s => ?_)
    simp only [F, sq, pgw_mul, eval_mul, eval_X]; ring_nf
  have iA : Integrable fun s => F₁ s ^ 2 := by simpa only [sq] using integrable_pgw_mul hc (dL c P) (dL c P)
  have hint : Integrable fun s => F₁ s ^ 2 + c ^ 2 * s ^ 2 * F s ^ 2 := iA.add iB
  have eL : IL c hc (hL c P * P) = ∫ s, (F₁ s ^ 2 + c ^ 2 * s ^ 2 * F s ^ 2) := by
    have e : hL c P * P = -(dL c (dL c P) * P) + C (c ^ 2) * (X ^ 2 * P * P) := by rw [hL_apply]; ring
    rw [e, map_add, map_neg, IL_dL_mul, neg_neg, ← smul_eq_C_mul, map_smul, smul_eq_mul, ← integral_pgw_mul hc,
      IL_apply, ← integral_const_mul, integral_add iA iB]
    simp only [sq]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [F, pgw_mul, eval_mul, eval_X]; ring_nf
  rw [eL, intervalIntegral.integral_of_le (by norm_num)]
  calc ∫ s in Set.Ioc (-1 : ℝ) 1, ((1 - s ^ 2) * F₁ s ^ 2 + c ^ 2 * s ^ 2 * F s ^ 2)
      ≤ ∫ s in Set.Ioc (-1 : ℝ) 1, (F₁ s ^ 2 + c ^ 2 * s ^ 2 * F s ^ 2) := by
        refine setIntegral_mono_on ?_ hint.integrableOn measurableSet_Ioc fun s _ => ?_
        · exact (Continuous.integrableOn_Ioc (by fun_prop))
        · nlinarith [sq_nonneg (F₁ s), sq_nonneg s, mul_nonneg (sq_nonneg s) (sq_nonneg (F₁ s))]
    _ ≤ ∫ s, (F₁ s ^ 2 + c ^ 2 * s ^ 2 * F s ^ 2) :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun s => by positivity)

/-- **The window Chebyshev bound**, finite form: for `f ∈ E_N`, `c > 0`, and finitely many even levels `χ_k ≥ M`,
`M Σ_k (∫_{−1}^1 f h_k)² ≤ c(4N + 1) ∫_ℝ f²`. -/
theorem sum_sq_window_le (hc : 0 < c) {N : ℕ} {f : ℝ → ℝ} (hf : f ∈ Cvs.Approximant.XiKrylovHermiteSpan.level c N) {M : ℝ}
    (S : Finset (LevelIdx c)) (hS : ∀ k ∈ S, M ≤ lev c k) :
    M * ∑ k ∈ S, (∫ s in (-1 : ℝ)..1, f s * rung c k s) ^ 2 ≤ c * (4 * N + 1) * ∫ w, f w ^ 2 := by
  have hH := integral_hOp_le hc hf
  obtain ⟨a, rfl⟩ := exists_of_mem_level hf
  simp_rw [hOp_pgw, sq, integral_pgw_mul hc] at hH
  set P := ∑ k ∈ Finset.Iic N, a k • hw c k
  set F := pgw c P
  set F₁ := pgw c (dL c P)
  set F₂ := pgw c (dL c (dL c P))
  set R : ℝ → ℝ := fun s => -((1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s)
  have cF : Continuous F := (contDiff_pgw c P 0).continuous
  have cF₁ : Continuous F₁ := (contDiff_pgw c _ 0).continuous
  have cF₂ : Continuous F₂ := (contDiff_pgw c _ 0).continuous
  have hFe : ∀ s, F (-s) = F s := pgw_hw_sum_neg c _ a
  have hF₁o : ∀ s, F₁ (-s) = -F₁ s := fun s => by
    simp only [F₁, ← deriv_pgw]; exact deriv_neg_of_even hFe s
  have hF₂e : ∀ s, F₂ (-s) = F₂ s := fun s => by
    simp only [F₂, ← deriv_pgw]; exact deriv_neg_of_odd (by simpa only [F₁, deriv_pgw] using hF₁o) s
  have hRe : ∀ s, R (-s) = R s := fun s => by simp only [R, hF₁o, hF₂e, hFe]; ring
  -- the Green identity `χ_k ⟨F, h_k⟩ = ⟨W_cF, h_k⟩`
  have green : ∀ k : LevelIdx c,
      lev c k * (∫ s in (-1 : ℝ)..1, F s * rung c k s) = ∫ s in (-1 : ℝ)..1, R s * rung c k s := by
    intro k
    have h := Cvs.Prolate.EvenRungDavisKahan.sub_mul_integral_mul_rung (c := c) (μ := 0) (F := F) (F₁ := F₁) (F₂ := F₂) (R := R) k.2
      (fun s _ => hasDerivAt_pgw c P s) (fun s _ => hasDerivAt_pgw c (dL c P) s) cF₂.continuousOn
      (fun s _ => by simp only [R]; ring)
    simpa using h
  have hsum := Cvs.Prolate.EvenRungParseval.hasSum_integral_mul_rung (c := c) (f := F) (g := R) hc.ne' cF.continuousOn
    (fun s _ => hFe s) (by simp only [R]; fun_prop) (fun s _ => hRe s)
  have hsum' : HasSum (fun k : LevelIdx c => lev c k * (∫ s in (-1 : ℝ)..1, F s * rung c k s) ^ 2)
      (∫ s in (-1 : ℝ)..1, F s * R s) := by
    convert hsum using 1; funext k
    rw [show (∫ s in (-1 : ℝ)..1, rung c k s * R s) = ∫ s in (-1 : ℝ)..1, R s * rung c k s from
      intervalIntegral.integral_congr fun s _ => mul_comm _ _, ← green]
    ring
  have hnn : ∀ k : LevelIdx c, 0 ≤ lev c k * (∫ s in (-1 : ℝ)..1, F s * rung c k s) ^ 2 := fun k =>
    mul_nonneg (Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c (Cvs.Prolate.EvenRungsByIndex.lev_spec k.2).1) (sq_nonneg _)
  have hpart := sum_le_hasSum S (fun k _ => hnn k) hsum'
  have hwin := integral_window_le hc P
  have hcheb : M * ∑ k ∈ S, (∫ s in (-1 : ℝ)..1, F s * rung c k s) ^ 2
      ≤ ∑ k ∈ S, lev c k * (∫ s in (-1 : ℝ)..1, F s * rung c k s) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hS k hk) (sq_nonneg _)
  have hF2 : ∫ w, F w ^ 2 = IL c hc (P * P) := by simp only [sq]; exact integral_pgw_mul hc P P
  rw [hF2]
  have : ∫ s in (-1 : ℝ)..1, F s * R s ≤ IL c hc (hL c P * P) := hwin
  linarith

/-- The ladder's rung mass on `χ ≥ c²`, finite form: at `c = 2πx > 0`, over finitely many even levels `χ_k ≥ c²`,
`Σ_k (∫_{−1}^1 u_j h_k)² ≤ ((8j + 9)/c) ∫_ℝ u_j²` for `u_j = (−(θ + ½)²)^jG_Ξ`. -/
theorem ladder_mass_above_plunge {x : ℝ} (hx : 0 < x) (j : ℕ) (S : Finset (LevelIdx (2 * π * x)))
    (hS : ∀ k ∈ S, (2 * π * x) ^ 2 ≤ lev (2 * π * x) k) :
    ∑ k ∈ S, (∫ s in (-1 : ℝ)..1, negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) s * rung (2 * π * x) k s) ^ 2
      ≤ (8 * j + 9) / (2 * π * x) * ∫ w, negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) w ^ 2 := by
  have hc : 0 < 2 * π * x := by positivity
  have h := sum_sq_window_le hc (Cvs.Approximant.XiKrylovHermiteSpan.ladder_mem_level x j) S hS
  push_cast at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith

/-- **The window Chebyshev bound**: for `f ∈ E_N`, `c > 0`, `0 ≤ M`, summed over every even level `χ_k ≥ M`,
`M Σ'_k (∫_{−1}^1 f h_k)² ≤ c(4N + 1) ∫_ℝ f²`. -/
theorem tsum_sq_window_le (hc : 0 < c) {N : ℕ} {f : ℝ → ℝ} (hf : f ∈ Cvs.Approximant.XiKrylovHermiteSpan.level c N) {M : ℝ} (hM : 0 ≤ M) :
    M * ∑' k : {k : LevelIdx c // M ≤ lev c k}, (∫ s in (-1 : ℝ)..1, f s * rung c k s) ^ 2
      ≤ c * (4 * N + 1) * ∫ w, f w ^ 2 := by
  rw [← tsum_mul_left]
  refine Real.tsum_le_of_sum_le (fun k => mul_nonneg hM (sq_nonneg _)) fun u => ?_
  have h := sum_sq_window_le hc hf (u.map (Function.Embedding.subtype _)) fun k hk => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hk; exact i.2
  rw [Finset.sum_map, Finset.mul_sum] at h
  exact h

/-- **The ladder's rung mass on `χ ≥ c²`**: at `c = 2πx > 0`, `Σ'_{χ_k ≥ c²} (∫_{−1}^1 u_j h_k)² ≤ ((8j + 9)/c) ∫_ℝ u_j²`. -/
theorem tsum_ladder_mass_le {x : ℝ} (hx : 0 < x) (j : ℕ) :
    ∑' k : {k : LevelIdx (2 * π * x) // (2 * π * x) ^ 2 ≤ lev (2 * π * x) k},
        (∫ s in (-1 : ℝ)..1, negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) s * rung (2 * π * x) k s) ^ 2
      ≤ (8 * j + 9) / (2 * π * x) * ∫ w, negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) w ^ 2 := by
  refine Real.tsum_le_of_sum_le (fun k => sq_nonneg _) fun u => ?_
  have h := ladder_mass_above_plunge hx j (u.map (Function.Embedding.subtype _)) fun k hk => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hk; exact i.2
  rwa [Finset.sum_map] at h

/-- **The ladder's off-window mass** (`HermiteTrialResiduals`'s Gaussian tail on `u_j = pg (2πx) Q_j`): for `0 < μ ≤ c = 2πx`,
`∫_ℝ u_j² − ∫_{−1}^1 u_j² ≤ e^{−(c − μ)} gE(c/μ, Q_j²) √(π/μ)`. -/
theorem ladder_offWindow_le (x : ℝ) (j : ℕ) {mu : ℝ} (hmu : 0 < mu) (hmc : mu ≤ 2 * π * x) :
    (∫ w, negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) w ^ 2) - ∫ w in (-1 : ℝ)..1, negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) w ^ 2
      ≤ exp (-(2 * π * x - mu)) * (Cvs.Prolate.HermiteTrialResiduals.gE (2 * π * x / mu) (Cvs.Approximant.XiKrylovHermiteSpan.qLad j ^ 2) * √(π / mu)) := by
  rw [Cvs.Approximant.XiKrylovHermiteSpan.negScal2_iterate_GXi]
  exact Cvs.Prolate.HermiteTrialResiduals.integral_pg_sq_sub_le hmu hmc _

/-- **The ladder's rung mass against the window norm**: at `c = 2πx`, `0 < μ ≤ c`, `Σ'_{χ_k ≥ c²} (∫_{−1}^1 u_j h_k)²
≤ ((8j + 9)/c)(∫_{−1}^1 u_j² + e^{−(c − μ)} gE(c/μ, Q_j²) √(π/μ))`. -/
theorem tsum_ladder_mass_le_window {x : ℝ} (hx : 0 < x) (j : ℕ) {mu : ℝ} (hmu : 0 < mu) (hmc : mu ≤ 2 * π * x) :
    ∑' k : {k : LevelIdx (2 * π * x) // (2 * π * x) ^ 2 ≤ lev (2 * π * x) k},
        (∫ s in (-1 : ℝ)..1, negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) s * rung (2 * π * x) k s) ^ 2
      ≤ (8 * j + 9) / (2 * π * x) * ((∫ w in (-1 : ℝ)..1, negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) w ^ 2)
          + exp (-(2 * π * x - mu)) * (Cvs.Prolate.HermiteTrialResiduals.gE (2 * π * x / mu) (Cvs.Approximant.XiKrylovHermiteSpan.qLad j ^ 2) * √(π / mu))) := by
  refine (tsum_ladder_mass_le hx j).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith [ladder_offWindow_le x j hmu hmc]

end Cvs.Prolate.WindowChebyshevRungMass
