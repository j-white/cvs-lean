import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.WeightedDominator
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.DyadicZeroTail
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The dyadic tail, in the zero side's coordinates

`Cvs.Zeta.ZeroCounting.DyadicZeroTail` weighs a dyadic block in the venue's indexing; `zeroEquiv` carries it to the
`nonTrivialZeroSet` the zero side sums over, where the weight is `divisorWeight` and the
ordinate is `gam`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Cvs.Zeta.Explicit.Venue

open scoped Classical

namespace Cvs.Zeta.ZeroCounting.DyadicTailZeroSide

/-- **The dyadic tail, transported along `zeroEquiv`.** -/
theorem tail_le_zeroSet {H : ℝ} (hH : 9 + Real.exp 1 ≤ 2 * H) {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, H ≤ a → a ≤ b → f b ≤ f a)
    (hf0 : ∀ t : ℝ, H ≤ t → 0 ≤ f t) (n : ℕ) :
    ∑ rho ∈ (nontrivialZetaZeroWindowFinset ((2:ℝ) ^ n * H) \
        nontrivialZetaZeroWindowFinset H).map Cvs.Criterion.zeroEquiv.toEmbedding,
        (Cvs.Criterion.divisorWeight rho : ℝ) * f |Cvs.GaussKernel.gam rho|
      ≤ ∑ j ∈ Finset.range n,
          f ((2:ℝ) ^ j * H) * (8 * ((2:ℝ) ^ j * H) * Real.log (2 * ((2:ℝ) ^ j * H))) := by
  rw [Finset.sum_map]
  refine le_trans (le_of_eq ?_) (Cvs.Zeta.ZeroCounting.DyadicZeroTail.tail_le hH hf hf0 n)
  refine Finset.sum_congr rfl fun rho _ => ?_
  have hw : (Cvs.Criterion.divisorWeight (Cvs.Criterion.zeroEquiv rho) : ℝ)
      = (completedZetaZeroMultiplicity rho : ℝ) := by
    rw [Cvs.Criterion.divisorWeight, Equiv.symm_apply_apply]
  have hg : Cvs.GaussKernel.gam (Cvs.Criterion.zeroEquiv rho)
      = (nontrivialZetaZeroValue rho).im := by
    rw [Cvs.GaussKernel.gam, Cvs.Criterion.coe_zeroEquiv]
  simp only [Equiv.coe_toEmbedding]
  rw [hw, hg]

end Cvs.Zeta.ZeroCounting.DyadicTailZeroSide
