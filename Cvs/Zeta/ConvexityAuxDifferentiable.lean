import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Cvs.Zeta.ConvexityEvenBranch

/-!
# The auxiliary function is differentiable on the strip

`PhragmenLindelof.vertical_strip` asks for three things: `DiffContOnCl` on the strip, a growth
allowance, and constant bounds on the two edges.
-/

open Complex

namespace Cvs.Zeta.ConvexityAuxDifferentiable
open Cvs.ArchScore

/-- The strip, as a set. -/
def strip (α β : ℝ) : Set ℂ := Complex.re ⁻¹' Set.Ioo α β

/-- The auxiliary function, on the even branch. -/
noncomputable def aux (f : ℂ → ℂ) (c K a' b' : ℝ) (s : ℂ) : ℂ :=
  f s * Complex.exp (-((a' : ℂ) + (b' : ℂ) * s) * Cvs.ArchScore.evenLog c K s)

end Cvs.Zeta.ConvexityAuxDifferentiable
