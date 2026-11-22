import Mathlib
import Cvs.Zeta.Digamma.DigammaDuplicationReflection
import Cvs.Zeta.Digamma.DigammaQuarterConstant

/-!
# The identification, reduced to one Fourier pair
-/

namespace Cvs.Enclosure

open scoped Real

/-- `ψ(1/4)` in closed form, from `DigammaDuplicationReflection`'s reflection and duplication. -/
theorem digamma_quarter :
    Complex.digamma (1 / 4)
      = -(Real.eulerMascheroniConstant : ℂ) - 3 * Complex.log 2 - (π : ℂ) / 2 :=
  Cvs.Moments.digamma_quarter_of Cvs.Moments.reflection_at_quarter Cvs.Moments.duplication_at_quarter

end Cvs.Enclosure
