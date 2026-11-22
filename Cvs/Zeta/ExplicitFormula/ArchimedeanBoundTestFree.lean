import Mathlib
import Cvs.Zeta.Digamma

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The archimedean bound, with no test in it
-/

namespace Cvs.Detection

open MeasureTheory

/-- The archimedean weight, relative to its value at the origin. -/
noncomputable def W (u : ℝ) : ℝ :=
  ((Complex.digamma (Cvs.Zeta.digammaArg u 0)).re
    - (Complex.digamma (Cvs.Zeta.digammaArg 0 0)).re) / 2

end Cvs.Detection
