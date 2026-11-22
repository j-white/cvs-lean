import Mathlib
import Cvs.L2a.HierarchyModePairNode
import Cvs.L2a.HierarchyPathWeight
import Cvs.L2a.PathWeightTwoConstants
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.TreeStepFirstPair
import Cvs.L2a.TreeStepModePair

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cross terms of the tail floor are the nodes at the empty path

`G = G_0 = Σ a_iψ_i` (Cvs.L2a.RungChiHierarchy), the node of the empty path is the plain weighted pair integral (`pw [] = 1`), and a
weighted integral over `[1, b]` with a weight vanishing on `[1, L]` is the integral over `[L, b]`: so the mode pairs
`∫ σ G(m·)G(m'·)` of Cvs.L2a.CutoffTailFloor are `node c m m' (19/20) (3/2) σ []` and the first-mode pairs `∫₁ᵇ η G G(m·)` are
`nodeFirst c m (4/3) b η []` when the ramp starts at `4/3`.
-/

namespace Cvs.L2a.CutoffCrossTermsAsNodes

open Real Set Finset intervalIntegral Cvs.L2a.RungChiHierarchy Cvs.L2a.HierarchyPathWeight Cvs.L2a.PathWeightTwoConstants Cvs.L2a.TreeStepModePair Cvs.L2a.TreeStepFirstPair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Gk_zero (a χ : ι → ℝ) (ψ : ι → ℝ → ℝ) (ξ : ℝ) : Gk a χ ψ 0 ξ = ∑ i, a i * ψ i ξ := by
  unfold Gk; simp

/-- The node of the empty path is the weighted pair integral of `G_0`. -/
theorem node_nil (c m₁ m₂ L R : ℝ) (σ : ℝ → ℝ) (a χ : ι → ℝ) (ψ : ι → ℝ → ℝ) :
    node c m₁ m₂ L R σ a χ ψ [] = ∫ θ in L..R, σ θ * (Gk a χ ψ 0 (m₁ * θ) * Gk a χ ψ 0 (m₂ * θ)) := by
  unfold node
  simp [pathWeight, ktrue, lfalse]

theorem nodeFirst_nil (c m₂ L R : ℝ) (σ : ℝ → ℝ) (a χ : ι → ℝ) (ψ : ι → ℝ → ℝ) :
    nodeFirst c m₂ L R σ a χ ψ [] = ∫ θ in L..R, σ θ * (Gk a χ ψ 0 θ * Gk a χ ψ 0 (m₂ * θ)) := by
  unfold nodeFirst
  simp [pathWeight, ktrue, lfalse]

/-- A weight vanishing on `[1, L]` restricts the integral to `[L, b]`. -/
theorem integral_eq_of_zero_left {η F : ℝ → ℝ} {L b : ℝ} (hL : 1 ≤ L) (hb : L ≤ b) (hη : ∀ θ ∈ Icc 1 L, η θ = 0)
    (hηc : Continuous η) (hFc : Continuous F) :
    ∫ θ in (1 : ℝ)..b, η θ * F θ = ∫ θ in L..b, η θ * F θ := by
  have hI : ∀ s t : ℝ, IntervalIntegrable (fun θ => η θ * F θ) MeasureTheory.volume s t := fun s t =>
    (hηc.mul hFc).intervalIntegrable s t
  rw [← integral_add_adjacent_intervals (hI 1 L) (hI L b)]
  have z : ∫ θ in (1 : ℝ)..L, η θ * F θ = ∫ θ in (1 : ℝ)..L, (0 : ℝ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ hθ => ?_)
    rw [uIoc_of_le hL] at hθ
    rw [hη θ ⟨hθ.1.le, hθ.2⟩, zero_mul]
  rw [z, integral_zero, zero_add]

/-- **The mode pairs of Cvs.L2a.CutoffTailFloor are nodes**: with `G = G_0`, `∫_{19/20}^{3/2} σ G(mθ)G(m'θ) = node c m m' … []`. -/
theorem cross_eq_node (c : ℝ) (m m' : ℕ) (σ : ℝ → ℝ) (a χ : ι → ℝ) (ψ : ι → ℝ → ℝ) :
    ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (Gk a χ ψ 0 (m * θ) * Gk a χ ψ 0 (m' * θ))
      = node c (m : ℝ) (m' : ℝ) (19 / 20) (3 / 2) σ a χ ψ [] := (node_nil _ _ _ _ _ _ _ _ _).symm

/-- **The first-mode pairs of Cvs.L2a.CutoffTailFloor are nodes**: with the ramp vanishing on `[1, 4/3]`,
`∫₁ᵇ η G(θ)G(mθ) = nodeFirst c m (4/3) b η … []`. -/
theorem first_eq_nodeFirst (c : ℝ) (m : ℕ) {b : ℝ} (hb : 4 / 3 ≤ b) {η : ℝ → ℝ} (hηc : Continuous η)
    (hη : ∀ θ ∈ Icc (1 : ℝ) (4 / 3), η θ = 0) (a χ : ι → ℝ) (ψ : ι → ℝ → ℝ) (hψc : ∀ i, Continuous (ψ i)) :
    ∫ θ in (1 : ℝ)..b, η θ * (Gk a χ ψ 0 θ * Gk a χ ψ 0 (m * θ)) = nodeFirst c (m : ℝ) (4 / 3) b η a χ ψ [] := by
  rw [nodeFirst_nil]
  have hGc : Continuous (Gk a χ ψ 0) := by
    unfold Gk; exact continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  exact integral_eq_of_zero_left (by norm_num) hb hη hηc (hGc.mul (hGc.comp (continuous_const.mul continuous_id)))

end Cvs.L2a.CutoffCrossTermsAsNodes
