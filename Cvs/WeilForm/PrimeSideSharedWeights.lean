import Mathlib
import Cvs.Zeta.PrimePowerSideTruncated

/-!
# The two shapes of the prime side share their weights

    Λ(pʳ)·(pʳ)^{−1/2} = primePowerWeight p r

and every non-prime-power weighs nothing.  RH.md §3.21 carries what else the identification
needs.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.WeilForm.PrimeSideSharedWeights

open ArithmeticFunction

/-- **The weights agree at a prime power.**  `Λ(p^r) = log p` and `(p^r)^{−1/2} = p^{−r/2}`,
so `an earlier result`'s coefficient at `k = p^r` is the operator side's at `(p, r)`. -/
theorem weight_eq_primePowerWeight {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    (Λ (p ^ r)) * ((p ^ r : ℝ) ^ (-(1/2) : ℝ))
      = Cvs.Zeta.Explicit.Weil.primePowerWeight p r := by
  have hp0 : (0:ℝ) < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hlam : Λ (p ^ r) = Real.log p := by
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
  have hpow : ((p : ℝ) ^ r) ^ (-(1/2) : ℝ) = (p : ℝ) ^ (-(r : ℝ) / 2) := by
    rw [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp0.le]
    congr 1
    ring
  rw [hlam, Cvs.Zeta.Explicit.Weil.primePowerWeight]
  exact congrArg _ hpow

end Cvs.WeilForm.PrimeSideSharedWeights
