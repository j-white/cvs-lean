import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The normalised energy of a forced oscillator

For `e′ = u/P`, `u′ = −Qe + F` and `a² = PQ` with `a > 0`, the normalised energy `Z = e² + u²/a²` has
`Z′ = 2uF/a² − 2u²a′/a³`: the oscillation cancels exactly, and for `a′ ≥ 0` it is at most `2√Z·|F|/a`. This is
the growth law behind the error of Olver's approximant, whose residual is `F` (Cvs.Prolate.LiouvilleGreen.OlverResidualIdentity).
-/

namespace Cvs.Upstream.ForcedOscillatorEnergy

open Real

/-- **The derivative of the normalised energy.** -/
theorem hasDerivAt_normEnergy {e u a P Q F : ℝ → ℝ} {e' u' a' : ℝ} {x : ℝ}
    (he : HasDerivAt e e' x) (hu : HasDerivAt u u' x) (ha : HasDerivAt a a' x)
    (ha0 : a x ≠ 0) (hP0 : P x ≠ 0) (he' : e' = u x / P x) (hu' : u' = -(Q x * e x) + F x)
    (haPQ : a x ^ 2 = P x * Q x) :
    HasDerivAt (fun x => e x ^ 2 + u x ^ 2 / a x ^ 2)
      (2 * u x * F x / a x ^ 2 - 2 * u x ^ 2 * a' / a x ^ 3) x := by
  have hf : (fun x => e x ^ 2 + u x ^ 2 / a x ^ 2) = fun x => e x * e x + u x * u x / (a x * a x) := by
    funext y; ring
  rw [hf]
  have h := HasDerivAt.add (HasDerivAt.mul he he)
    (HasDerivAt.div (HasDerivAt.mul hu hu) (HasDerivAt.mul ha ha) (mul_ne_zero ha0 ha0))
  refine HasDerivAt.congr_deriv h ?_
  simp only [Pi.mul_apply]
  rw [he', hu']
  have hQ : Q x = a x ^ 2 / P x := by field_simp; linarith
  rw [hQ]
  field_simp
  ring

/-- **The growth bound**: for `a′ ≥ 0`, `Z′ ≤ 2√Z·|F|/a`. -/
theorem normEnergy_deriv_le {u F a a' Z : ℝ} (ha : 0 < a) (ha' : 0 ≤ a') (hZ : u ^ 2 / a ^ 2 ≤ Z) :
    2 * u * F / a ^ 2 - 2 * u ^ 2 * a' / a ^ 3 ≤ 2 * √Z * |F| / a := by
  have h1 : 0 ≤ 2 * u ^ 2 * a' / a ^ 3 := by positivity
  have hua : |u| / a ≤ √Z := by
    rw [div_le_iff₀ ha]
    have : (|u| / a) ^ 2 ≤ Z := by rw [div_pow, sq_abs]; exact hZ
    have hs := Real.sqrt_le_sqrt this
    rw [Real.sqrt_sq (by positivity)] at hs
    rw [div_le_iff₀ ha] at hs; exact hs
  have h2 : 2 * u * F / a ^ 2 ≤ 2 * (|u| / a) * |F| / a := by
    have : 2 * u * F ≤ 2 * |u| * |F| := by
      have := le_abs_self (u * F); rw [abs_mul] at this; linarith
    calc 2 * u * F / a ^ 2 ≤ 2 * |u| * |F| / a ^ 2 := div_le_div_of_nonneg_right this (by positivity)
      _ = 2 * (|u| / a) * |F| / a := by field_simp
  have h3 : 2 * (|u| / a) * |F| / a ≤ 2 * √Z * |F| / a := by
    apply div_le_div_of_nonneg_right _ ha.le
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  linarith

end Cvs.Upstream.ForcedOscillatorEnergy
