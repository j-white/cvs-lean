import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A conjugate pair of exponents is a cosine

Two exponents differing only in the sign of their imaginary part give powers that are conjugate at a
positive base, and their sum is twice the real power times a cosine of the logarithm. At the
critical line the pair the functional equation exchanges is of exactly that shape.
-/

noncomputable section

open Complex

namespace Cvs.Xi.ConjugateExponentsCosine

theorem exp_add_exp_neg (z : ℂ) :
    Complex.exp (z * I) + Complex.exp (-z * I) = 2 * Complex.cos z := by
  have h1 : Complex.exp (z * I) = Complex.cos z + Complex.sin z * I := Complex.exp_mul_I z
  have h2 : Complex.exp (-z * I) = Complex.cos (-z) + Complex.sin (-z) * I :=
    Complex.exp_mul_I (-z)
  rw [h1, h2, Complex.cos_neg, Complex.sin_neg]
  ring

/-- **A conjugate pair of exponents gives a cosine.** -/
theorem cpow_add_cpow_conj {x : ℝ} (hx : 0 < x) (a θ : ℝ) :
    ((x : ℂ)) ^ ((a : ℂ) + (θ : ℂ) * I) + ((x : ℂ)) ^ ((a : ℂ) - (θ : ℂ) * I)
      = 2 * ((x : ℂ) ^ (a : ℂ)) * ((Real.cos (θ * Real.log x) : ℝ) : ℂ) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have key : ∀ b : ℂ, ((x : ℝ) : ℂ) ^ b = Complex.exp (((Real.log x : ℝ) : ℂ) * b) := fun b => by
    rw [Complex.cpow_def_of_ne_zero hxne, Complex.ofReal_log hx.le]
  have hz : ((Real.log x : ℝ) : ℂ) * ((θ : ℂ) * I)
      = ((θ * Real.log x : ℝ) : ℂ) * I := by push_cast; ring
  have hz' : ((Real.log x : ℝ) : ℂ) * (-((θ : ℂ) * I))
      = -((θ * Real.log x : ℝ) : ℂ) * I := by push_cast; ring
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hxne, Complex.cpow_add _ _ hxne,
    key ((θ : ℂ) * I), key (-((θ : ℂ) * I)), hz, hz', ← mul_add,
    exp_add_exp_neg, Complex.ofReal_cos]
  ring

/-- **The pair the functional equation exchanges, on the critical line.** -/
theorem bracket_eq {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    ((x : ℂ)) ^ (((1 : ℂ) / 2 + (τ : ℂ) * I) / 2 - 1)
        + ((x : ℂ)) ^ ((1 : ℂ) / 2 - ((1 : ℂ) / 2 + (τ : ℂ) * I) / 2 - 1)
      = 2 * ((x : ℂ) ^ ((-3 / 4 : ℝ) : ℂ)) * ((Real.cos (τ / 2 * Real.log x) : ℝ) : ℂ) := by
  have e1 : ((1 : ℂ) / 2 + (τ : ℂ) * I) / 2 - 1
      = ((-3 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have e2 : (1 : ℂ) / 2 - ((1 : ℂ) / 2 + (τ : ℂ) * I) / 2 - 1
      = ((-3 / 4 : ℝ) : ℂ) - ((τ / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [e1, e2, cpow_add_cpow_conj hx (-3 / 4) (τ / 2)]

end Cvs.Xi.ConjugateExponentsCosine
