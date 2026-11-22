import Mathlib
import Cvs.L2a.TailLogScaleTest
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The truncated prime side of a tail, in the multiplicative variable

`Σ_{p ≤ P, r ≤ R} log p · p^{−r/2} ((f⋆f)(r log p) + (f⋆f)(−r log p)) = 2 Σ_{p ≤ P, r ≤ R} log p ∫_{θ>1} F(θ) F(p^r θ)`
for `f = logScale F`.
-/

namespace Cvs.L2a.TailPrimeSideMultiplicative

open Real Set MeasureTheory Cvs.L2a.TailLogScaleTest

/-- **The prime side of a tail.** -/
theorem primeSide_eq (F : ℝ → ℝ) (hF : ∀ θ ≤ 1, F θ = 0) (P R : ℕ) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F))
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
          2 * Real.log p * ∫ θ in Ioi 1, F θ * F ((p : ℝ) ^ r * θ) := by
  unfold Cvs.Zeta.Explicit.Weil.primePowerSideTruncated
  apply Finset.sum_congr rfl
  intro p hp
  have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  apply Finset.sum_congr rfl
  intro r _
  have hk : (0 : ℝ) < (p : ℝ) ^ r := pow_pos hp0 r
  have hlog : (r : ℝ) * Real.log p = Real.log ((p : ℝ) ^ r) := by rw [Real.log_pow]
  rw [hlog, selfConvolution_neg_log, selfConvolution_log F hF hk]
  unfold Cvs.Zeta.Explicit.Weil.primePowerWeight
  have hs : √((p : ℝ) ^ r) * (p : ℝ) ^ (-(r : ℝ) / 2) = 1 := by
    rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hp0.le, ← rpow_add hp0]
    ring_nf; exact rpow_zero _
  calc Real.log p * (p : ℝ) ^ (-(r : ℝ) / 2)
        * (√((p : ℝ) ^ r) * (∫ θ in Ioi 1, F θ * F ((p : ℝ) ^ r * θ))
          + √((p : ℝ) ^ r) * ∫ θ in Ioi 1, F θ * F ((p : ℝ) ^ r * θ))
      = 2 * Real.log p * (√((p : ℝ) ^ r) * (p : ℝ) ^ (-(r : ℝ) / 2))
          * ∫ θ in Ioi 1, F θ * F ((p : ℝ) ^ r * θ) := by ring
    _ = _ := by rw [hs, mul_one]

end Cvs.L2a.TailPrimeSideMultiplicative
