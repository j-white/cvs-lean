import Mathlib
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-!
# The moments and the Hankel form on the zero side
-/

set_option maxHeartbeats 1000000

noncomputable section

open Complex MeasureTheory Finset

namespace Cvs.ZeroCounting

/-- The point of the zero side attached to `ρ`: `-i(ρ - ½)`, which is `γ - iδ`. -/
noncomputable def zPoint (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) : ℂ :=
  -Complex.I * ((rho : ℂ) - 1 / 2)

/-- A zero on the critical line sits at a real point of the zero side. -/
theorem zPoint_of_re_eq_half {rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet}
    (h : (rho : ℂ).re = 1 / 2) : zPoint rho = ((rho : ℂ).im : ℂ) := by
  unfold zPoint
  apply Complex.ext <;> simp [h]

/-- The zero side of a kernel, weighted by multiplicity. Linear in the kernel — which
is what carries `an earlier result`'s expansion through to the quadratic form. -/
noncomputable def kernelZeroSide (h : ℂ → ℂ) (lam a : ℝ) : ℝ :=
  ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
    (Cvs.Criterion.divisorWeight rho : ℝ) * (h (zPoint rho)).re

end Cvs.ZeroCounting
