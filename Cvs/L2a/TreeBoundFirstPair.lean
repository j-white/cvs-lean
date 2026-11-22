import Mathlib
import Cvs.L2a.BoundaryFreeNodeCostFirst
import Cvs.L2a.FluxTermNormVNorm
import Cvs.L2a.HierarchyLevelNorms
import Cvs.L2a.HierarchyModePairNode
import Cvs.L2a.HierarchyPathWeight
import Cvs.L2a.PathWeightDerivative
import Cvs.L2a.PathWeightTwoConstants
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.TreeStepFirstPair

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tree bound of a pair `(1, k)`

Normalising the nodes of Cvs.L2a.TreeStepFirstPair by `κ₁^l κ₂^k χ^{k+l} N₀`, the step of the project reads
`x p ≤ E(|p|) + m₂²κ₁χ x(p ++ [true]) + κ₂χ x(p ++ [false])` with `E(n)` the level cost at depth `(n, n)`, the
leaves obey `x p ≤ (1 + 1/m₂)/2` by the balanced product bound, and the project sum (Cvs.Upstream.BinaryTreeDepthSum) gives
`|∫ σ G(θ) G(m₂θ)| ≤ (Σ_{j<N} ρ^j E(j) + ρ^N (1 + 1/m₂)/2) N₀`, `ρ = m₂²κ₁χ + κ₂χ`, for every depth `N`.
-/

namespace Cvs.L2a.TreeBoundFirstPair

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.L2a.HierarchyPathWeight Cvs.L2a.HierarchyModePairNode Cvs.L2a.PathWeightTwoConstants Cvs.L2a.PathWeightDerivative Cvs.L2a.TreeStepFirstPair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The leaf bound**: `|node p| ≤ (1 + 1/m₂)/2 · κ₁^l κ₂^k χ^{k+l} N₀`. -/
theorem node_leaf_first {c m₂ L R χm κ₁ κ₂ : ℝ} {a χ Mm : ι → ℝ} {ψ : ι → ℝ → ℝ} (K : ι → ι → ℝ) {σ : ℝ → ℝ}
    (p : List Bool) (hc : 0 < c) (hm₂ : 2 ≤ m₂) (hL : 4 / 3 ≤ L) (hLR : L ≤ R)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hχm : 0 < χm) (hM : ∀ i, 0 ≤ Mm i)
    (hψc : ∀ i, Continuous (ψ i))
    (hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hσc : ContinuousOn σ (Icc L R)) (hσ1 : ∀ θ ∈ Icc L R, |σ θ| ≤ 1)
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂)
    (hg₁ : ∀ θ ∈ Icc L R, |g₁ c 1 (m₂ ^ 2) θ| ≤ κ₁) (hg₂ : ∀ θ ∈ Icc L R, |g₂ c 1 (m₂ ^ 2) θ| ≤ κ₂) :
    |nodeFirst c m₂ L R σ a χ ψ p|
      ≤ (1 / 1 + 1 / m₂) / 2 * (κ₁ ^ ktrue p * κ₂ ^ lfalse p * χm ^ (ktrue p + lfalse p) * ∑ i, a i ^ 2 * Mm i) := by
  set k := lfalse p with hk_def
  set l := ktrue p with hl_def
  set N₀ := ∑ i, a i ^ 2 * Mm i with hN₀
  set Kp := κ₁ ^ l * κ₂ ^ k with hKp
  have ht : 4 ≤ m₂ ^ 2 := by nlinarith
  have hm₂0 : 0 < m₂ := by linarith
  have hL0 : 0 < L := by linarith
  have hθL : ∀ θ ∈ Icc L R, 4 / 3 ≤ θ := fun θ hθ => hL.trans hθ.1
  have hKp0 : 0 < Kp := by positivity
  have hN₀ : 0 ≤ N₀ := Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (a i), hM i]
  obtain ⟨hg₁c, hg₂c, -, -⟩ := Cvs.L2a.BoundaryFreeNodeCostFirst.continuousOn_factors_first (R := R) hc ht hL
  have hw := abs_pathWeight_le₂ (s := Icc L R) hκ₁.le hκ₂.le hg₁ hg₂ p
  have hGc : ∀ j m, Continuous fun θ => Gk a χ ψ j (m * θ) := fun j m => by
    unfold Gk
    exact continuous_finsetSum _ fun i _ => continuous_const.mul ((hψc i).comp (continuous_const.mul continuous_id))
  have hGc0 : ∀ j, Continuous (Gk a χ ψ j) := fun j => by
    unfold Gk
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  set lam := χm ^ l / (χm ^ k * Kp) with hlam
  have hl0 : 0 < lam := by positivity
  have hpwc : ContinuousOn (fun θ => σ θ * pathWeight (g₁ c 1 (m₂ ^ 2)) (g₂ c 1 (m₂ ^ 2)) p θ) (Icc L R) :=
    hσc.mul (continuousOn_pathWeight hg₁c hg₂c p)
  have h := Cvs.L2a.FluxTermNormVNorm.fu_term_le_prod (P := fun _ => (1 : ℝ))
    (al := fun θ => σ θ * pathWeight (g₁ c 1 (m₂ ^ 2)) (g₂ c 1 (m₂ ^ 2)) p θ)
    (f := Gk a χ ψ k) (u := fun θ => Gk a χ ψ l (m₂ * θ)) hLR hl0 (fun _ _ => one_pos) hpwc
    (hGc0 k).continuousOn (hGc l m₂).continuousOn continuousOn_const
  have e0 : nodeFirst c m₂ L R σ a χ ψ p = ∫ θ in L..R,
      σ θ * pathWeight (g₁ c 1 (m₂ ^ 2)) (g₂ c 1 (m₂ ^ 2)) p θ
        * (Gk a χ ψ k θ * Gk a χ ψ l (m₂ * θ)) := rfl
  rw [e0]
  have hcont : ∀ i, ContinuousOn (ψ i) (Ici 1) := fun i => (hψc i).continuousOn
  have hL₁ : 1 ≤ 1 * L := by linarith
  have hL₂ : 1 ≤ m₂ * L := by
    have := mul_le_mul_of_nonneg_right hm₂ hL0.le
    linarith
  have hRL₂ : m₂ * L ≤ m₂ * R := mul_le_mul_of_nonneg_left hLR hm₂0.le
  have hn₁ : ∫ θ in L..R, Gk a χ ψ k θ ^ 2 ≤ 1 / 1 * (χm ^ (2 * k) * N₀) := by
    have := Cvs.L2a.HierarchyLevelNorms.level_norm_le (a := a) (m := 1) K k one_pos hL₁ hLR hχ hM hcont
      (fun i j hij t ht => hcross i j hij t (by linarith)) (fun i t ht => hmass i t (by linarith))
    simpa only [one_mul] using this
  have hn₂ : ∫ θ in L..R, Gk a χ ψ l (m₂ * θ) ^ 2 ≤ 1 / m₂ * (χm ^ (2 * l) * N₀) :=
    Cvs.L2a.HierarchyLevelNorms.level_norm_le K l hm₂0 hL₂ hLR hχ hM hcont (fun i j hij t ht => hcross i j hij t (by linarith))
      (fun i t ht => hmass i t (by linarith))
  have hI1 : IntervalIntegrable (fun θ => Gk a χ ψ k θ ^ 2) MeasureTheory.volume L R :=
    ((hGc0 k).pow 2).intervalIntegrable L R
  have hw2 : ∫ θ in L..R, (σ θ * pathWeight (g₁ c 1 (m₂ ^ 2)) (g₂ c 1 (m₂ ^ 2)) p θ) ^ 2 * 1
        * Gk a χ ψ k θ ^ 2
      ≤ Kp ^ 2 * ∫ θ in L..R, Gk a χ ψ k θ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_on hLR ?_ (hI1.const_mul _) fun θ hθ => ?_
    · exact (((hpwc.pow 2).mul continuousOn_const).mul ((hGc0 k).pow 2).continuousOn).intervalIntegrable_of_Icc hLR
    · have hb : |σ θ * pathWeight (g₁ c 1 (m₂ ^ 2)) (g₂ c 1 (m₂ ^ 2)) p θ| ≤ Kp := by
        rw [abs_mul]
        calc _ ≤ 1 * (κ₁ ^ l * κ₂ ^ k) := mul_le_mul (hσ1 θ hθ) (hw θ hθ) (abs_nonneg _) zero_le_one
          _ = Kp := by rw [one_mul]
      have hsq : (σ θ * pathWeight (g₁ c 1 (m₂ ^ 2)) (g₂ c 1 (m₂ ^ 2)) p θ) ^ 2 ≤ Kp ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hdiv : ∫ θ in L..R, Gk a χ ψ l (m₂ * θ) ^ 2 / 1 = ∫ θ in L..R, Gk a χ ψ l (m₂ * θ) ^ 2 := by simp
  rw [hdiv] at h
  calc _ ≤ _ := h
    _ ≤ lam / 2 * (Kp ^ 2 * (1 / 1 * (χm ^ (2 * k) * N₀))) + 1 / (2 * lam) * (1 / m₂ * (χm ^ (2 * l) * N₀)) := by
        gcongr
        exact hw2.trans (mul_le_mul_of_nonneg_left hn₁ (by positivity))
    _ = (1 / 1 + 1 / m₂) / 2 * (κ₁ ^ l * κ₂ ^ k * χm ^ (l + k) * N₀) := by
        rw [hlam, hKp]; field_simp; ring

end Cvs.L2a.TreeBoundFirstPair
