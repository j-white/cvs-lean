import Mathlib
import Cvs.WeilForm.PrimePowerReindex
import Cvs.WeilForm.PrimeSideSharedWeights
import Cvs.Zeta.PrimePowerSideTruncated

/-!
# The truncated prime side, indexed by prime powers

    primePowerSideTruncated P R G = ∑_{k ∈ image} Λ(k)·k^{−1/2}·(G (log k) + G (−log k))

`Cvs.WeilForm.PrimeSideSharedWeights` matches the weights and `Cvs.WeilForm.PrimePowerReindex` the index sets, so the operator's double sum over
`(p, r)` is a single sum over prime powers — the shape the explicit formula uses.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.PrimePowerIndexed

/-- The prime powers the truncation reaches. -/
def primePowIndex (P R : ℕ) : Finset ℕ :=
  Finset.image (fun pr : ℕ × ℕ => pr.1 ^ pr.2)
    ((Finset.range (P + 1)).filter Nat.Prime ×ˢ Finset.Icc 1 R)

/-- **The prime side, as a sum over prime powers.** -/
theorem primePowerSideTruncated_eq_image (P R : ℕ) (G : ℝ → ℝ) :
    primePowerSideTruncated P R G
      = ∑ k ∈ primePowIndex P R,
          (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
            * (G (Real.log k) + G (-(Real.log k))) := by
  classical
  have hterm : ∀ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∀ r ∈ Finset.Icc 1 R,
      primePowerWeight p r * (G (r * Real.log p) + G (-(r * Real.log p)))
        = (fun k : ℕ => (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
            * (G (Real.log k) + G (-(Real.log k)))) (p ^ r) := by
    intro p hp r hr
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hlog : Real.log ((p : ℝ) ^ r) = r * Real.log p := by
      rw [Real.log_pow]
    have hcast : ((p ^ r : ℕ) : ℝ) = (p : ℝ) ^ r := by push_cast; ring
    simp only
    rw [hcast, hlog, Cvs.WeilForm.PrimeSideSharedWeights.weight_eq_primePowerWeight hpp hr1]
  rw [primePowerSideTruncated]
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun r hr => hterm p hp r hr))]
  rw [primePowIndex]
  have h := Cvs.WeilForm.PrimePowerReindex.sum_primePow_eq_image P R
    (fun k : ℕ => (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
      * (G (Real.log k) + G (-(Real.log k))))
  simpa using h

end Cvs.WeilForm.PrimePowerIndexed
