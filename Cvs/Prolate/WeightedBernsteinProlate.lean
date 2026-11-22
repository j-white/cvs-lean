import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A weighted Bernstein inequality from the operator

`∫_a^T p u′² = [p u u′]_a^T − ∫_a^T u (pu′)′` by parts; so if `(pu′)′ = g − κ u` with `κ` a weight and
`∫_a^T u g ≥ 0`, then `∫_a^T p u′² ≤ [p u u′]_a^T + ∫_a^T κ u²`. For a rung span, `g = LΦ` with `L` the prolate
operator, `κ = c²ξ²`, and `∫ΦLΦ = Σχᵢaᵢ²‖ψᵢ‖² ≥ 0` by orthogonality: the derivative of any span is bounded by
`c²∫ξ²Φ²` up to one boundary term.
-/

namespace Cvs.Prolate.WeightedBernsteinProlate

open Real Set MeasureTheory intervalIntegral

/-- **The energy identity**: `∫ p u′² = [p u u′] − ∫ u (pu′)′`. -/
theorem integral_p_deriv_sq {p u u' w : ℝ → ℝ} {a T : ℝ}
    (hu : ∀ x ∈ uIcc a T, HasDerivAt u (u' x) x)
    (hpu : ∀ x ∈ uIcc a T, HasDerivAt (fun x => p x * u' x) (w x) x)
    (hu'c : ContinuousOn u' (uIcc a T)) (hwc : ContinuousOn w (uIcc a T)) :
    ∫ x in a..T, p x * u' x ^ 2
      = p T * u T * u' T - p a * u a * u' a - ∫ x in a..T, u x * w x := by
  have hibp := integral_mul_deriv_eq_deriv_mul hu hpu hu'c.intervalIntegrable hwc.intervalIntegrable
  have e : ∫ x in a..T, p x * u' x ^ 2 = ∫ x in a..T, u' x * (p x * u' x) := by
    congr 1; funext x; ring
  rw [e]
  linarith [hibp, show u T * (p T * u' T) = p T * u T * u' T by ring,
    show u a * (p a * u' a) = p a * u a * u' a by ring]

/-- **The Bernstein inequality**: with `(pu′)′ = g − κu` and `∫ug ≥ 0`, `∫ p u′² ≤ [p u u′] + ∫ κ u²`. -/
theorem integral_p_deriv_sq_le {p u u' g κ : ℝ → ℝ} {a T : ℝ}
    (hu : ∀ x ∈ uIcc a T, HasDerivAt u (u' x) x)
    (hpu : ∀ x ∈ uIcc a T, HasDerivAt (fun x => p x * u' x) (g x - κ x * u x) x)
    (hu'c : ContinuousOn u' (uIcc a T)) (hgc : ContinuousOn g (uIcc a T)) (hκc : ContinuousOn κ (uIcc a T))
    (hpos : 0 ≤ ∫ x in a..T, u x * g x) :
    ∫ x in a..T, p x * u' x ^ 2 ≤ p T * u T * u' T - p a * u a * u' a + ∫ x in a..T, κ x * u x ^ 2 := by
  have huc : ContinuousOn u (uIcc a T) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hwc : ContinuousOn (fun x => g x - κ x * u x) (uIcc a T) := hgc.sub (hκc.mul huc)
  rw [integral_p_deriv_sq hu hpu hu'c hwc]
  have hsplit : ∫ x in a..T, u x * (g x - κ x * u x) = (∫ x in a..T, u x * g x) - ∫ x in a..T, κ x * u x ^ 2 := by
    have i1 : IntervalIntegrable (fun x => u x * g x) volume a T := (huc.mul hgc).intervalIntegrable
    have i2 : IntervalIntegrable (fun x => κ x * u x ^ 2) volume a T := (hκc.mul (huc.pow 2)).intervalIntegrable
    rw [← intervalIntegral.integral_sub i1 i2]
    congr 1; funext x; ring
  rw [hsplit]
  linarith

end Cvs.Prolate.WeightedBernsteinProlate
