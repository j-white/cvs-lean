import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZetaZeroWindows

/-!
# The divisor weight in the criterion's coordinates

`DivisorWeightExpansion` proved summability at the divisor weight over `Cvs.Zeta.Explicit.Venue`'s zero type.
-/

namespace Cvs.Criterion

/-- **The two zero types agree.**  A nested subtype of the preimage against a flat subtype
of `ℂ`, with the same two strip conditions. -/
def zeroEquiv :
    Cvs.Zeta.Explicit.Venue.nontrivialRiemannZetaZeros ≃ Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet where
  toFun rho := ⟨(rho.1 : ℂ), rho.1.2, rho.2.1, rho.2.2⟩
  invFun rho := ⟨⟨(rho : ℂ), rho.2.1⟩, rho.2.2.1, rho.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coe_zeroEquiv (rho : Cvs.Zeta.Explicit.Venue.nontrivialRiemannZetaZeros) :
    ((zeroEquiv rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) : ℂ)
      = Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue rho := rfl

/-- The divisor weight, in the criterion's coordinates. -/
noncomputable def divisorWeight (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) : ℕ :=
  Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity (zeroEquiv.symm rho)

end Cvs.Criterion
