import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiVertical

/-!
# The zero gas is reflection-symmetric, and that is not RH

Rung 3's closed form is, read as physics, the field of a one-dimensional Coulomb gas: `ξ'/ξ(z)
= Σ_ρ 1/(z−ρ) + …` is the complex field of unit charges at the zeros, and the `+1/ρ` of the
genus-1 normalisation is the neutralising background that makes the sum converge.
-/

noncomputable section

open Complex Filter Topology Finset Cvs.Zeta

namespace Cvs.ZeroFree

/-- **The field vanishes at the centre of symmetry.**  `1 − 1/2 = 1/2`, so the reflection
identity forces `ξ'/ξ(1/2) = −ξ'/ξ(1/2)`.  No numerical input, and in particular no need to
know `ζ(1/2) ≠ 0`. -/
theorem logDeriv_riemannXi_half : logDeriv riemannXi (1 / 2) = 0 := by
  have h := logDeriv_riemannXi_one_sub (1 / 2 : ℂ)
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring] at h
  linear_combination h / 2

end Cvs.ZeroFree
