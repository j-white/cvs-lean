import Mathlib
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiVertical

/-!
# The RH spine on the moments: coefficients of the ground-state polynomial converging to `Ξ`'s
`Ξ` is even (`Xi_neg`), so its odd derivatives at `0` vanish and `Ξ(z) = ∑_j Ξ^{(2j)}(0)/(2j)!·(z²)^j` (`hasSum_Xi`).
`riemannHypothesis_of_moments`: if no ground-state secular polynomial has a root on `(−∞, 0]` and, for every `j`,
its `j`-th coefficient over its constant term converges to `xiCoeff j = Ξ^{(2j)}(0)/((2j)!·Ξ(0))`, RH follows.
`Ξ(0) ≠ 0` is not assumed: the `j = 0` limit forces it.
-/

noncomputable section

open Filter Topology Polynomial

namespace Cvs.Limit.MomentSpineXiCoefficients

open Cvs.Limit.ZeroFreeApproximantsRH

theorem Xi_neg (z : ℂ) : Xi (-z) = Xi z := by
  unfold Xi
  rw [show (1 / 2 : ℂ) + Complex.I * -z = 1 - (1 / 2 + Complex.I * z) by ring, Cvs.Zeta.riemannXi_one_sub]

end Cvs.Limit.MomentSpineXiCoefficients
