import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Complex Set Filter Topology

namespace Cvs.Digamma

/-!
# `Re ψ` on a vertical line dominates its value on the axis

The archimedean channel needs `Re ψ(x + iy) ≥ ψ(x)`.
-/

/-- On the axis the reciprocal is real. -/
theorem re_inv_ofReal {t : ℝ} : (1 / (t : ℂ)).re = 1 / t := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]

end Cvs.Digamma
