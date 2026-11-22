import Mathlib
import Cvs.Finite.ReducedSecularPolynomial
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity

/-!
# The RH spine on the moments alone
`shiftP p` removes the zeros of `p` at the origin: `p = X^m · shiftP p` with `m` the trailing degree, and
`shiftP p` has a nonzero constant term. The ground state's `shiftP` is real-rooted with nonzero roots and zero-free
off the axes in `z²`, whether or not `x₀ = 0`. `riemannHypothesis_of_moments''`: if for every `j` the ground-state
secular polynomial's coefficient `j` places above its trailing one, over the trailing one, converges to `xiCoeff j`,
then RH. There is no per-scale hypothesis; when `x₀ ≠ 0` this is `Cvs.Limit.MomentSpineConstantCoeff`'s statement.
-/

noncomputable section

open Polynomial Filter Topology Finset

namespace Cvs.Limit.MomentSpineAlone
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet Cvs.Finite.ReducedSecularPolynomial

/-- `p` with its zeros at the origin removed. -/
def shiftP (p : ℂ[X]) : ℂ[X] :=
  ∑ i ∈ range (p.natDegree + 1), C (p.coeff (i + p.natTrailingDegree)) * X ^ i

theorem coeff_shiftP (p : ℂ[X]) (j : ℕ) : (shiftP p).coeff j = p.coeff (j + p.natTrailingDegree) := by
  simp only [shiftP, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · symm; apply coeff_eq_zero_of_natDegree_lt; omega

theorem X_pow_mul_shiftP (p : ℂ[X]) : X ^ p.natTrailingDegree * shiftP p = p := by
  ext j
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_shiftP]; congr 1; omega
  · symm; exact coeff_eq_zero_of_lt_natTrailingDegree (by omega)

theorem eval_eq_pow_mul (p : ℂ[X]) (w : ℂ) : p.eval w = w ^ p.natTrailingDegree * (shiftP p).eval w := by
  conv_lhs => rw [← X_pow_mul_shiftP p]
  simp [eval_mul]

theorem shiftP_eval_zero {p : ℂ[X]} (hp : p ≠ 0) : (shiftP p).eval 0 ≠ 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_shiftP, zero_add]
  exact trailingCoeff_nonzero_iff_nonzero.mpr hp

theorem roots_shiftP {p : ℂ[X]} (hp : p ≠ 0) (hreal : ∀ r : ℂ, p.eval r = 0 → r.im = 0) :
    ∀ r ∈ (shiftP p).roots, r.im = 0 ∧ r.re ≠ 0 := by
  intro r hr
  have hq : (shiftP p).eval r = 0 := (Polynomial.mem_roots'.mp hr).2.eq_zero
  have hpr : p.eval r = 0 := by rw [eval_eq_pow_mul, hq, mul_zero]
  refine ⟨hreal r hpr, fun hre => ?_⟩
  have hr0 : r = 0 := Complex.ext hre (hreal r hpr)
  rw [hr0] at hq
  exact shiftP_eval_zero hp hq

/-- The ground state's secular polynomial has only real roots. -/
theorem ground_real {L : ℝ} (hL : 0 < L) (P R N : ℕ) (r : ℂ)
    (hr : (Cvs.Finite.SecularCoefficientLimits.secPolyP L N (Cvs.Limit.SpineWithoutSimplicity.ground P R L hL N)).eval r = 0) :
    r.im = 0 := by
  rw [Cvs.Finite.SecularCoefficientLimits.eval_secPolyP] at hr
  by_contra him
  set u : ℂ := r ^ ((2 : ℕ)⁻¹ : ℂ) with hu
  have hu2 : u ^ 2 = r := Complex.cpow_nat_inv_pow r (by norm_num)
  have huim : (u ^ 2).im = 2 * u.re * u.im := by rw [sq, Complex.mul_im]; ring
  have hure : u.re ≠ 0 := by intro h; apply him; rw [← hu2, huim, h]; ring
  have huim' : u.im ≠ 0 := by intro h; apply him; rw [← hu2, huim, h]; ring
  exact secPoly_ground_ne_zero hL P R N ⟨hure, huim'⟩ (by rw [hu2]; exact hr)

theorem ground_ne_zero {L : ℝ} (hL : 0 < L) (P R N : ℕ) :
    Cvs.Finite.SecularCoefficientLimits.secPolyP L N (Cvs.Limit.SpineWithoutSimplicity.ground P R L hL N) ≠ 0 := by
  intro h
  have hz : (1 + Complex.I : ℂ) ∈ Cvs.Limit.OffAxesLimit.offAxes := ⟨by simp, by simp⟩
  apply secPoly_ground_ne_zero hL P R N hz
  rw [← Cvs.Finite.SecularCoefficientLimits.eval_secPolyP, h, eval_zero]

end Cvs.Limit.MomentSpineAlone
