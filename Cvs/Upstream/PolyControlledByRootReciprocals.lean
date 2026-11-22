import Mathlib
import Cvs.Limit.MomentLimitsBoundedUnique
import Cvs.Limit.PairingRouteRootsDischarged
import Cvs.Upstream.PositiveRootPolyFirstCoeff

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A polynomial is controlled by the reciprocals of its roots, and real roots pin it from below

A polynomial that does not vanish at the origin is its value there times `∏ (1 - w / ρ)` over
its roots.  Each factor is at most `exp (‖w‖ / ‖ρ‖)`, which bounds the polynomial by the sum of
the reciprocal moduli of its roots; and when the roots are real and `w` is purely imaginary each
factor has modulus at least one.  The ground state's secular polynomial has real roots.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Polynomial

namespace Cvs.Upstream.PolyControlledByRootReciprocals
open Cvs.ZeroCounting

/-- **A product of factors `1 - w / ρ` is at most the exponential of `‖w‖ ∑ 1 / ‖ρ‖`.** -/
theorem norm_prod_one_sub_le (s : Multiset ℂ) (w : ℂ) :
    ‖(s.map fun r => 1 - r⁻¹ * w).prod‖
      ≤ Real.exp (‖w‖ * (s.map fun r => ‖r‖⁻¹).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, norm_mul,
      mul_add, Real.exp_add]
    have hfac : ‖1 - a⁻¹ * w‖ ≤ Real.exp (‖w‖ * ‖a‖⁻¹) := by
      calc ‖1 - a⁻¹ * w‖ ≤ ‖(1 : ℂ)‖ + ‖a⁻¹ * w‖ := norm_sub_le _ _
        _ = ‖w‖ * ‖a‖⁻¹ + 1 := by rw [norm_one, norm_mul, norm_inv]; ring
        _ ≤ Real.exp (‖w‖ * ‖a‖⁻¹) := Real.add_one_le_exp _
    exact mul_le_mul hfac ih (norm_nonneg _) (Real.exp_pos _).le

/-- **With real roots and a purely imaginary argument every factor has modulus at least one.** -/
theorem one_le_norm_prod_one_sub (s : Multiset ℂ) (hs : ∀ r ∈ s, r.im = 0) {w : ℂ}
    (hw : w.re = 0) :
    1 ≤ ‖(s.map fun r => 1 - r⁻¹ * w).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have ha : a.im = 0 := hs a (Multiset.mem_cons_self a s)
    have hre : (1 - a⁻¹ * w).re = 1 := by
      rw [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.inv_im, ha, hw]
      simp
    have hfac : 1 ≤ ‖1 - a⁻¹ * w‖ := by
      have h := Complex.abs_re_le_norm (1 - a⁻¹ * w)
      rw [hre, abs_one] at h
      exact h
    have hrest := ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ‖1 - a⁻¹ * w‖ * ‖(s.map fun r => 1 - r⁻¹ * w).prod‖ :=
          mul_le_mul hfac hrest zero_le_one (norm_nonneg _)

/-- **A polynomial grows no faster than its roots' reciprocals allow.** -/
theorem norm_eval_le {p : ℂ[X]} (hp : ∀ r ∈ p.roots, r ≠ 0) (w : ℂ) :
    ‖p.eval w‖ ≤ ‖p.eval 0‖ * Real.exp (‖w‖ * (p.roots.map fun r => ‖r‖⁻¹).sum) := by
  rw [Cvs.Upstream.PositiveRootPolyFirstCoeff.eval_eq_eval_zero_mul_prod hp w, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_prod_one_sub_le _ _) (norm_nonneg _)

/-- **With real roots, the value at the origin is the smallest along the imaginary axis.** -/
theorem norm_eval_zero_le {p : ℂ[X]} (hp : ∀ r ∈ p.roots, r.im = 0 ∧ r ≠ 0) {w : ℂ}
    (hw : w.re = 0) :
    ‖p.eval 0‖ ≤ ‖p.eval w‖ := by
  rw [Cvs.Upstream.PositiveRootPolyFirstCoeff.eval_eq_eval_zero_mul_prod (fun r hr => (hp r hr).2) w, norm_mul]
  have h := one_le_norm_prod_one_sub p.roots (fun r hr => (hp r hr).1) hw
  calc ‖p.eval 0‖ = ‖p.eval 0‖ * 1 := by ring
    _ ≤ ‖p.eval 0‖ * ‖(p.roots.map fun r => 1 - r⁻¹ * w).prod‖ :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- **Normalised on the imaginary axis, a real-rooted polynomial is bounded by one scalar.** -/
theorem norm_eval_le_of_real_roots {p : ℂ[X]} (hp : ∀ r ∈ p.roots, r.im = 0 ∧ r ≠ 0) {w₀ : ℂ}
    (hw₀ : w₀.re = 0) (w : ℂ) :
    ‖p.eval w‖ ≤ ‖p.eval w₀‖ * Real.exp (‖w‖ * (p.roots.map fun r => ‖r‖⁻¹).sum) :=
  le_trans (norm_eval_le (fun r hr => (hp r hr).2) w)
    (mul_le_mul_of_nonneg_right (norm_eval_zero_le hp hw₀) (Real.exp_pos _).le)

/-- **The ground state's secular polynomial**, whose roots are real and non-zero
unconditionally. -/
theorem norm_eval_gpoly_le {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ) (n : ℕ) {w₀ : ℂ}
    (hw₀ : w₀.re = 0) (w : ℂ) :
    ‖(Cvs.Limit.MomentLimitsBoundedUnique.gpoly hL P R N n).eval w‖
      ≤ ‖(Cvs.Limit.MomentLimitsBoundedUnique.gpoly hL P R N n).eval w₀‖
        * Real.exp (‖w‖ * ((Cvs.Limit.MomentLimitsBoundedUnique.gpoly hL P R N n).roots.map
            fun r => ‖r‖⁻¹).sum) := by
  refine norm_eval_le_of_real_roots (fun r hr => ?_) hw₀ w
  have h := Cvs.Limit.PairingRouteRootsDischarged.gpoly_roots_real hL P R N n r hr
  refine ⟨h.1, fun h0 => h.2 ?_⟩
  rw [h0]; rfl

end Cvs.Upstream.PolyControlledByRootReciprocals
