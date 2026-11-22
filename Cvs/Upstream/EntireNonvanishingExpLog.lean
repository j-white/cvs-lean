import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-
An entire non-vanishing function is the exponential of an entire function.

This is the step of Hadamard's factorization that turns `f / Π E₁(z/ρ)` — entire
and zero-free, once the canonical product has absorbed the zeros — into
`exp` of an entire function, whose growth is then pinned to a degree-`1`
polynomial by Borel–Carathéodory.

Everything needed is in pinned Mathlib, and rather more than
`MATHLIB.md` credits:

* `Differentiable.isExactOn_univ` (`Analysis/Complex/HasPrimitives.lean`) — an
  entire function has a primitive on all of `ℂ`;
* `Differentiable.deriv` (`Analysis/Complex/CauchyIntegral.lean`) — the
  derivative of an entire function is entire;
* `is_const_of_fderiv_eq_zero` (`Analysis/Calculus/MeanValue.lean`);
* `Complex.borelCaratheodory` (`Analysis/Complex/BorelCaratheodory.lean`) — the
  growth step, listed as absent in `MATHLIB.md` but in fact fully proved.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex

/-- **An entire non-vanishing function is `exp` of an entire function.** The logarithmic
derivative `g'/g` is entire, so it has a primitive `H` on `ℂ`; normalising `H` by a constant
so that `exp (h 0) = g 0` makes `g · exp (-h)` have vanishing derivative, hence constant `1`. -/
theorem exists_differentiable_exp_eq {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hg0 : ∀ z, g z ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z, g z = Complex.exp (h z) := by
  -- the logarithmic derivative is entire, hence exact on `ℂ`
  have hld : Differentiable ℂ fun z => deriv g z / g z := fun z =>
    (hg.deriv z).div (hg z) (hg0 z)
  obtain ⟨H, hH⟩ := hld.isExactOn_univ
  have hHd : Differentiable ℂ H := fun z => (hH z (Set.mem_univ z)).differentiableAt
  -- normalise so that `exp (h 0) = g 0`
  set h : ℂ → ℂ := fun z => H z + (Complex.log (g 0) - H 0) with hhdef
  have hhd : Differentiable ℂ h := hHd.add_const _
  have hh0 : Complex.exp (h 0) = g 0 := by
    have : h 0 = Complex.log (g 0) := by simp [hhdef]
    rw [this]
    exact Complex.exp_log (hg0 0)
  refine ⟨h, hhd, fun z => ?_⟩
  -- `g · exp (-h)` has vanishing derivative
  have hderiv : ∀ x : ℂ, HasDerivAt (fun y => g y * Complex.exp (-(h y))) 0 x := by
    intro x
    have hgx : HasDerivAt g (deriv g x) x := hg.differentiableAt.hasDerivAt
    have hhx : HasDerivAt h (deriv g x / g x) x := by
      simpa [hhdef] using
        (hH x (Set.mem_univ x)).add_const (Complex.log (g 0) - H 0)
    have hd : HasDerivAt (fun y => Complex.exp (-(h y)))
        (Complex.exp (-(h x)) * -(deriv g x / g x)) x := hhx.neg.cexp
    have hgx0 : g x ≠ 0 := hg0 x
    have hzero : deriv g x * Complex.exp (-(h x))
        + g x * (Complex.exp (-(h x)) * -(deriv g x / g x)) = 0 := by
      field_simp
      ring
    exact hzero ▸ hgx.mul hd
  have hconst : ∀ x y : ℂ, (fun y => g y * Complex.exp (-(h y))) x
      = (fun y => g y * Complex.exp (-(h y))) y := by
    refine is_const_of_fderiv_eq_zero (fun x => (hderiv x).differentiableAt) ?_
    intro x
    simpa using (hderiv x).hasFDerivAt.fderiv
  have hz : g z * Complex.exp (-(h z)) = g 0 * Complex.exp (-(h 0)) := hconst z 0
  have hrhs : g 0 * Complex.exp (-(h 0)) = 1 := by
    rw [← hh0, Complex.exp_neg]
    exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
  rw [hrhs, Complex.exp_neg] at hz
  have hne : Complex.exp (h z) ≠ 0 := Complex.exp_ne_zero _
  field_simp at hz
  exact hz

end Cvs.Zeta
