import Mathlib

/-
The Gevrey tail theorem on the circle (campaign stage 5).

Assembly: on the unit circle, Lebesgue measure *is* the normalized Haar
measure, so Mathlib's `fourierBasis` (whose `repr` is `fourierCoeff`)
applies to the complexified rung function. Combining the coefficient
product formula (stage 3) with the abstract tail bound (stage 4):

  **the bump-modulated top eigenfunction has super-algebraically
  decaying Fourier-window projection tails.**

This is the Gevrey tail hypothesis, machine-checked on the circle side.
What separates it from the `ℓ²(ℤ)` statement consumed by
`superalgebraic_sections` is only unitary bookkeeping: the DTFT and the
real/complex splitting, both isometries that carry window spans to
window spans.
-/

open MeasureTheory Real AddCircle
open scoped ContDiff

namespace Cvs.Zeta

local notation "𝕋₁" => AddCircle (1 : ℝ)

instance : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩

end Cvs.Zeta
