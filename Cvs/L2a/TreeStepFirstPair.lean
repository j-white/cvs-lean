import Mathlib
import Cvs.L2a.HierarchyModePairNode
import Cvs.L2a.HierarchyPathWeight
import Cvs.L2a.PathWeightTwoConstants
import Cvs.L2a.RungChiHierarchy

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The step of the project for a pair `(1, k)`

For the pair `(1, m₂)`, `2 ≤ m₂`, on `[L, R]`, `4/3 ≤ L`, with a cutoff `σ`, the node of a path `p` is
`node p = ∫ σ·pw_p · G_k G_l(m₂·)` (`k`, `l` the false and true steps), and `|node p| ≤ E(k, l) κ₁^l κ₂^k χ^{k+l} N₀
+ m₂² |node (p ++ [true])| + |node (p ++ [false])|` with an explicit `E`: the node cost (Cvs.L2a.BoundaryFreeNodeCostFirst) with its norms
by the masses (Cvs.L2a.HierarchyLevelNorms), its weights by the path-weight bounds (Cvs.L2a.HierarchyNodeWeight), and the free `λ`s balanced between the levels.
-/

namespace Cvs.L2a.TreeStepFirstPair

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.L2a.HierarchyPathWeight Cvs.L2a.HierarchyModePairNode Cvs.L2a.PathWeightTwoConstants

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The node of a path for the pair `(1, m₂)`: the false steps raise the first level, the true steps the second. -/
noncomputable def nodeFirst (c m₂ L R : ℝ) (σ : ℝ → ℝ) (a χ : ι → ℝ) (ψ : ι → ℝ → ℝ) (p : List Bool) : ℝ :=
  ∫ θ in L..R, σ θ * pathWeight (g₁ c 1 (m₂ ^ 2)) (g₂ c 1 (m₂ ^ 2)) p θ
    * (Gk a χ ψ (lfalse p) θ * Gk a χ ψ (ktrue p) (m₂ * θ))

end Cvs.L2a.TreeStepFirstPair
