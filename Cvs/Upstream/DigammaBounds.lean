import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-
Copyright (c) 2026 Jesse White. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse White
-/

/-!
# The size of the digamma function

Mathlib defines `Complex.digamma` and gives its value at `0`, `1` and `1/2` together with the
recurrence, but nothing about its size.
-/

open Real Nat Set

namespace Complex

/-- **Digamma on the naturals.** `ψ(n+1) = -γ + Hₙ`. -/
theorem digamma_natCast_add_one (n : ℕ) :
    Complex.digamma ((n : ℂ) + 1) = -(Real.eulerMascheroniConstant : ℂ) + (harmonic n : ℂ) := by
  have hfac : Complex.Gamma ((n : ℂ) + 1) = (n ! : ℂ) := Complex.Gamma_nat_eq_factorial n
  have hfac0 : (n ! : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [Complex.digamma_def, logDeriv_apply, Complex.deriv_Gamma_nat n, hfac]
  field_simp

end Complex

namespace Real

private theorem ne_neg_natCast {x : ℝ} (hx : 0 < x) : ∀ m : ℕ, x ≠ -(m : ℝ) := by
  intro m hc
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [hc] at hx
  linarith

theorem differentiableAt_log_Gamma {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x :=
  (Real.differentiableAt_log (Real.Gamma_pos_of_pos hx).ne').comp x
    (Real.differentiableAt_Gamma (ne_neg_natCast hx))

/-- The derivative of `log ∘ Γ` is the digamma function. -/
theorem deriv_log_Gamma {x : ℝ} (hx : 0 < x) :
    deriv (Real.log ∘ Real.Gamma) x = logDeriv Real.Gamma x := by
  have hG : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have hd : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (ne_neg_natCast hx)
  rw [deriv_comp x (Real.differentiableAt_log hG) hd, Real.deriv_log', logDeriv_apply]
  ring

/-- **The real digamma is monotone on the positive reals.** -/
theorem monotoneOn_logDeriv_Gamma : MonotoneOn (logDeriv Real.Gamma) (Ioi 0) := by
  have hmono := Real.convexOn_log_Gamma.monotoneOn_deriv
    (fun x hx => differentiableAt_log_Gamma (mem_Ioi.mp hx))
  intro a ha b hb hab
  rw [← deriv_log_Gamma (mem_Ioi.mp ha), ← deriv_log_Gamma (mem_Ioi.mp hb)]
  exact hmono ha hb hab

end Real
