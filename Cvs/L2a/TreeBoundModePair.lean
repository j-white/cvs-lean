import Mathlib
import Cvs.L2a.BoundaryFreeNodeCostModes
import Cvs.L2a.FluxTermNormVNorm
import Cvs.L2a.HierarchyLevelNorms
import Cvs.L2a.HierarchyModePairNode
import Cvs.L2a.HierarchyNodeWeight
import Cvs.L2a.HierarchyPathWeight
import Cvs.L2a.PathWeightDerivative
import Cvs.L2a.PathWeightTwoConstants
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.TreeStepModePair
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Upstream.BinaryTreeDepthSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tree bound of a mode pair `≥ 2`

Normalising the nodes of Cvs.L2a.TreeStepModePair by `κ₁^l κ₂^k χ^{k+l} N₀`, the step of the project reads
`x p ≤ E(|p|) + m₂²κ₁χ x(p ++ [true]) + m₁²κ₂χ x(p ++ [false])` with `E(n)` the level cost at depth `(n, n)`, the
leaves obey `x p ≤ (1/m₁ + 1/m₂)/2` by the balanced product bound, and the project sum (Cvs.Upstream.BinaryTreeDepthSum) gives
`|∫ σ G(m₁θ) G(m₂θ)| ≤ (Σ_{j<N} ρ^j E(j) + ρ^N (1/m₁ + 1/m₂)/2) N₀`, `ρ = m₂²κ₁χ + m₁²κ₂χ`, for every depth `N`.
-/

namespace Cvs.L2a.TreeBoundModePair

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.L2a.HierarchyPathWeight Cvs.L2a.HierarchyModePairNode Cvs.L2a.PathWeightTwoConstants Cvs.L2a.PathWeightDerivative Cvs.L2a.HierarchyNodeWeight Cvs.L2a.TreeStepModePair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ktrue_add_lfalse (p : List Bool) : ktrue p + lfalse p = p.length := by
  unfold ktrue lfalse
  induction p with
  | nil => simp
  | cons a p ih => cases a <;> simp [List.count_cons] <;> omega

/-- The level cost is monotone in the depth: `Ecost k l ≤ Ecost n n` for `k, l ≤ n`. -/
theorem Ecost_mono {m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hμ₁ : 0 < μ₁)
    (hμ₂ : 0 < μ₂) (hS' : 0 < S') (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hκ₁' : 0 ≤ κ₁') (hκ₂' : 0 ≤ κ₂')
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) {k l n : ℕ} (hk : k ≤ n) (hl : l ≤ n) :
    Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ k l ≤ Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ n n := by
  have hg : grow0 κ₁ κ₂ κ₁' κ₂' k l ≤ grow0 κ₁ κ₂ κ₁' κ₂' n n := by
    unfold grow0
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    have hl' : (l : ℝ) ≤ n := by exact_mod_cast hl
    have := mul_le_mul_of_nonneg_right hl' (div_nonneg hκ₁' hκ₁.le)
    have := mul_le_mul_of_nonneg_right hk' (div_nonneg hκ₂' hκ₂.le)
    linarith
  have hg0 : 0 ≤ grow0 κ₁ κ₂ κ₁' κ₂' k l := by unfold grow0; positivity
  unfold Ecost
  have h1 : (1 + grow0 κ₁ κ₂ κ₁' κ₂' k l / S') ^ 2 ≤ (1 + grow0 κ₁ κ₂ κ₁' κ₂' n n / S') ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith [div_le_div_of_nonneg_right hg hS'.le]
  have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ μ₁ / 2)) hC₁) hm₁.le
  have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ μ₂ / 2)) hC₂) hm₂.le
  linarith

/-- **The leaf bound**: `|node p| ≤ (1/m₁ + 1/m₂)/2 · κ₁^l κ₂^k χ^{k+l} N₀`. -/
theorem node_leaf {c m₁ m₂ L R χm κ₁ κ₂ : ℝ} {a χ Mm : ι → ℝ} {ψ : ι → ℝ → ℝ} (K : ι → ι → ℝ) {σ : ℝ → ℝ}
    (p : List Bool) (hc : 0 < c) (hm₁ : 2 ≤ m₁) (hm₁₂ : m₁ + 1 ≤ m₂) (hL : 19 / 20 ≤ L) (hLR : L ≤ R)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hχm : 0 < χm) (hM : ∀ i, 0 ≤ Mm i)
    (hψc : ∀ i, Continuous (ψ i))
    (hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hσc : ContinuousOn σ (Icc L R)) (hσ1 : ∀ θ ∈ Icc L R, |σ θ| ≤ 1)
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂)
    (hg₁ : ∀ θ ∈ Icc L R, |g₁ c (m₁ ^ 2) (m₂ ^ 2) θ| ≤ κ₁) (hg₂ : ∀ θ ∈ Icc L R, |g₂ c (m₁ ^ 2) (m₂ ^ 2) θ| ≤ κ₂) :
    |node c m₁ m₂ L R σ a χ ψ p|
      ≤ (1 / m₁ + 1 / m₂) / 2 * (κ₁ ^ ktrue p * κ₂ ^ lfalse p * χm ^ (ktrue p + lfalse p) * ∑ i, a i ^ 2 * Mm i) := by
  set k := lfalse p with hk_def
  set l := ktrue p with hl_def
  set N₀ := ∑ i, a i ^ 2 * Mm i with hN₀
  set Kp := κ₁ ^ l * κ₂ ^ k with hKp
  have hs : 4 ≤ m₁ ^ 2 := by nlinarith
  have hst : m₁ ^ 2 + 5 ≤ m₂ ^ 2 := by nlinarith
  have hm₁0 : 0 < m₁ := by linarith
  have hm₂0 : 0 < m₂ := by linarith
  have hL0 : 0 < L := by linarith
  have hθL : ∀ θ ∈ Icc L R, 19 / 20 ≤ θ := fun θ hθ => hL.trans hθ.1
  have hKp0 : 0 < Kp := by positivity
  have hN₀ : 0 ≤ N₀ := Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (a i), hM i]
  obtain ⟨hg₁c, hg₂c, -, -⟩ := Cvs.L2a.BoundaryFreeNodeCostModes.continuousOn_factors (R := R) hc hs hst hL
  have hw := abs_pathWeight_le₂ (s := Icc L R) hκ₁.le hκ₂.le hg₁ hg₂ p
  have hGc : ∀ j m, Continuous fun θ => Gk a χ ψ j (m * θ) := fun j m => by
    unfold Gk
    exact continuous_finsetSum _ fun i _ => continuous_const.mul ((hψc i).comp (continuous_const.mul continuous_id))
  set lam := χm ^ l / (χm ^ k * Kp) with hlam
  have hl0 : 0 < lam := by positivity
  have hpwc : ContinuousOn (fun θ => σ θ * pathWeight (g₁ c (m₁ ^ 2) (m₂ ^ 2)) (g₂ c (m₁ ^ 2) (m₂ ^ 2)) p θ) (Icc L R) :=
    hσc.mul (continuousOn_pathWeight hg₁c hg₂c p)
  have h := Cvs.L2a.FluxTermNormVNorm.fu_term_le_prod (P := fun _ => (1 : ℝ))
    (al := fun θ => σ θ * pathWeight (g₁ c (m₁ ^ 2) (m₂ ^ 2)) (g₂ c (m₁ ^ 2) (m₂ ^ 2)) p θ)
    (f := fun θ => Gk a χ ψ k (m₁ * θ)) (u := fun θ => Gk a χ ψ l (m₂ * θ)) hLR hl0 (fun _ _ => one_pos) hpwc
    (hGc k m₁).continuousOn (hGc l m₂).continuousOn continuousOn_const
  have e0 : node c m₁ m₂ L R σ a χ ψ p = ∫ θ in L..R,
      σ θ * pathWeight (g₁ c (m₁ ^ 2) (m₂ ^ 2)) (g₂ c (m₁ ^ 2) (m₂ ^ 2)) p θ
        * (Gk a χ ψ k (m₁ * θ) * Gk a χ ψ l (m₂ * θ)) := rfl
  rw [e0]
  -- the weighted norm of the first level
  have hcont : ∀ i, ContinuousOn (ψ i) (Ici 1) := fun i => (hψc i).continuousOn
  have hL₁ : 1 ≤ m₁ * L := by nlinarith
  have hL₂ : 1 ≤ m₂ * L := by nlinarith
  have hRL₁ : m₁ * L ≤ m₁ * R := mul_le_mul_of_nonneg_left hLR hm₁0.le
  have hRL₂ : m₂ * L ≤ m₂ * R := mul_le_mul_of_nonneg_left hLR hm₂0.le
  have hn₁ : ∫ θ in L..R, Gk a χ ψ k (m₁ * θ) ^ 2 ≤ 1 / m₁ * (χm ^ (2 * k) * N₀) :=
    Cvs.L2a.HierarchyLevelNorms.level_norm_le K k hm₁0 hL₁ hLR hχ hM hcont (fun i j hij t ht => hcross i j hij t (by linarith))
      (fun i t ht => hmass i t (by linarith))
  have hn₂ : ∫ θ in L..R, Gk a χ ψ l (m₂ * θ) ^ 2 ≤ 1 / m₂ * (χm ^ (2 * l) * N₀) :=
    Cvs.L2a.HierarchyLevelNorms.level_norm_le K l hm₂0 hL₂ hLR hχ hM hcont (fun i j hij t ht => hcross i j hij t (by linarith))
      (fun i t ht => hmass i t (by linarith))
  have hI1 : IntervalIntegrable (fun θ => Gk a χ ψ k (m₁ * θ) ^ 2) MeasureTheory.volume L R :=
    ((hGc k m₁).pow 2).intervalIntegrable L R
  have hw2 : ∫ θ in L..R, (σ θ * pathWeight (g₁ c (m₁ ^ 2) (m₂ ^ 2)) (g₂ c (m₁ ^ 2) (m₂ ^ 2)) p θ) ^ 2 * 1
        * Gk a χ ψ k (m₁ * θ) ^ 2
      ≤ Kp ^ 2 * ∫ θ in L..R, Gk a χ ψ k (m₁ * θ) ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_on hLR ?_ (hI1.const_mul _) fun θ hθ => ?_
    · exact (((hpwc.pow 2).mul continuousOn_const).mul ((hGc k m₁).pow 2).continuousOn).intervalIntegrable_of_Icc hLR
    · have hb : |σ θ * pathWeight (g₁ c (m₁ ^ 2) (m₂ ^ 2)) (g₂ c (m₁ ^ 2) (m₂ ^ 2)) p θ| ≤ Kp := by
        rw [abs_mul]
        calc _ ≤ 1 * (κ₁ ^ l * κ₂ ^ k) := mul_le_mul (hσ1 θ hθ) (hw θ hθ) (abs_nonneg _) zero_le_one
          _ = Kp := by rw [one_mul]
      have hsq : (σ θ * pathWeight (g₁ c (m₁ ^ 2) (m₂ ^ 2)) (g₂ c (m₁ ^ 2) (m₂ ^ 2)) p θ) ^ 2 ≤ Kp ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hdiv : ∫ θ in L..R, Gk a χ ψ l (m₂ * θ) ^ 2 / 1 = ∫ θ in L..R, Gk a χ ψ l (m₂ * θ) ^ 2 := by simp
  rw [hdiv] at h
  calc _ ≤ _ := h
    _ ≤ lam / 2 * (Kp ^ 2 * (1 / m₁ * (χm ^ (2 * k) * N₀))) + 1 / (2 * lam) * (1 / m₂ * (χm ^ (2 * l) * N₀)) := by
        gcongr
        exact hw2.trans (mul_le_mul_of_nonneg_left hn₁ (by positivity))
    _ = (1 / m₁ + 1 / m₂) / 2 * (κ₁ ^ l * κ₂ ^ k * χm ^ (l + k) * N₀) := by
        rw [hlam, hKp]; field_simp; ring

set_option maxHeartbeats 800000 in
/-- **The tree bound of a mode pair**: for every depth `N`,
`|∫ σ G(m₁θ) G(m₂θ)| ≤ (Σ_{j<N} ρ^j E(j) + ρ^N (1/m₁ + 1/m₂)/2) N₀`, `ρ = m₂²κ₁χ + m₁²κ₂χ`. -/
theorem pair_tree_bound {c m₁ m₂ L R χb χm Sp h ε δ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' A₁ B₁ A₂ B₂ C₁ C₂ : ℝ}
    {a χ Mm : ι → ℝ} {ψ u : ι → ℝ → ℝ} (K : ι → ι → ℝ) {σ σ' : ℝ → ℝ}
    (hc : 0 < c) (hm₁ : 2 ≤ m₁) (hm₁₂ : m₁ + 1 ≤ m₂) (hL : 19 / 20 ≤ L) (hLR : L ≤ R) (hh : 0 < h)
    (hα₁ : 1 < m₁ * (L - h)) (hχb₁ : χb < c ^ 2 * m₁ ^ 2 * (L - h) ^ 2)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hχm : 0 < χm) (hM : ∀ i, 0 ≤ Mm i) (hS : ∀ i, |χ i - χb| ≤ Sp)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hψ : ∀ i, ∀ ξ, 1 < ξ → HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hψc : ∀ i, Continuous (ψ i)) (huc : ∀ i, Continuous (u i))
    (hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hσ : ∀ θ ∈ Icc L R, HasDerivAt σ (σ' θ) θ) (hσ'c : ContinuousOn σ' (Icc L R)) (hσL : σ L = 0) (hσR : σ R = 0)
    (hσ1 : ∀ θ ∈ Icc L R, |σ θ| ≤ 1) (hσ'b : ∀ θ ∈ Icc L R, |σ' θ| ≤ S') (hS' : 0 < S')
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hκ₁' : 0 ≤ κ₁') (hκ₂' : 0 ≤ κ₂')
    (hg₁ : ∀ θ ∈ Icc L R, |g₁ c (m₁ ^ 2) (m₂ ^ 2) θ| ≤ κ₁) (hg₂ : ∀ θ ∈ Icc L R, |g₂ c (m₁ ^ 2) (m₂ ^ 2) θ| ≤ κ₂)
    (hg₁' : ∀ θ ∈ Icc L R, |g₁' c (m₁ ^ 2) (m₂ ^ 2) θ| ≤ κ₁') (hg₂' : ∀ θ ∈ Icc L R, |g₂' c (m₁ ^ 2) (m₂ ^ 2) θ| ≤ κ₂')
    (hA₁ : ∀ θ ∈ Icc (L - h) (R + h), 2 * (m₁ ^ 2 * θ ^ 2 - 1)
      * ((Real.pi / h) ^ 2 / (c ^ 2 * m₁ ^ 4 * θ ^ 2 - m₁ ^ 2 * χb)
        + (2 * c ^ 2 * m₁ ^ 4 * θ) ^ 2 / (c ^ 2 * m₁ ^ 4 * θ ^ 2 - m₁ ^ 2 * χb) ^ 3) ≤ A₁)
    (hB₁ : ∀ θ ∈ Icc (L - h) (R + h), 1 / (c ^ 2 * m₁ ^ 4 * θ ^ 2 - m₁ ^ 2 * χb) ^ 2 ≤ B₁)
    (hA₂ : ∀ θ ∈ Icc (L - h) (R + h), 2 * (m₂ ^ 2 * θ ^ 2 - 1)
      * ((Real.pi / h) ^ 2 / (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb)
        + (2 * c ^ 2 * m₂ ^ 4 * θ) ^ 2 / (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb) ^ 3) ≤ A₂)
    (hB₂ : ∀ θ ∈ Icc (L - h) (R + h), 1 / (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb) ^ 2 ≤ B₂)
    (hC₁ : ∀ θ ∈ Icc L R, (S' * |g₁ c (m₁ ^ 2) (m₂ ^ 2) θ| + |g₁' c (m₁ ^ 2) (m₂ ^ 2) θ|) ^ 2
      * ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb)) ≤ C₁)
    (hC₂ : ∀ θ ∈ Icc L R, (S' * |g₂ c (m₁ ^ 2) (m₂ ^ 2) θ| + |g₂' c (m₁ ^ 2) (m₂ ^ 2) θ|) ^ 2
      * ((m₁ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₁ ^ 2) ^ 2 * θ ^ 2 - m₁ ^ 2 * χb)) ≤ C₂)
    (hN₀ : 0 < ∑ i, a i ^ 2 * Mm i) (hC₁m : 0 ≤ C₁) (hC₂m : 0 ≤ C₂) (N : ℕ) :
    |node c m₁ m₂ L R σ a χ ψ []|
      ≤ ((∑ j ∈ range N, (m₂ ^ 2 * κ₁ * χm + m₁ ^ 2 * κ₂ * χm) ^ j
            * Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc m₁ ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) j j)
          + (m₂ ^ 2 * κ₁ * χm + m₁ ^ 2 * κ₂ * χm) ^ N * ((1 / m₁ + 1 / m₂) / 2)) * ∑ i, a i ^ 2 * Mm i := by
  have hm₁0 : 0 < m₁ := by linarith
  have hm₂0 : 0 < m₂ := by linarith
  have hσc : ContinuousOn σ (Icc L R) := fun θ hθ => (hσ θ hθ).continuousAt.continuousWithinAt
  set N₀ := ∑ i, a i ^ 2 * Mm i with hN₀def
  set D : List Bool → ℝ := fun p => κ₁ ^ ktrue p * κ₂ ^ lfalse p * χm ^ p.length * N₀ with hD
  have hDpos : ∀ p, 0 < D p := fun p => by simp only [hD]; positivity
  set x : List Bool → ℝ := fun p => |node c m₁ m₂ L R σ a χ ψ p| / D p with hx
  have hnorm : ∀ p : List Bool, κ₁ ^ ktrue p * κ₂ ^ lfalse p * χm ^ (ktrue p + lfalse p) * N₀ = D p := fun p => by
    simp only [hD]; rw [ktrue_add_lfalse]
  have hDT : ∀ p : List Bool, D (p ++ [true]) = κ₁ * χm * D p := fun p => by
    simp only [hD]
    rw [ktrue_append_true, lfalse_append_true, List.length_append, List.length_singleton, pow_succ, pow_succ]; ring
  have hDF : ∀ p : List Bool, D (p ++ [false]) = κ₂ * χm * D p := fun p => by
    simp only [hD]
    rw [ktrue_append_false, lfalse_append_false, List.length_append, List.length_singleton, pow_succ, pow_succ]; ring
  have hstep : ∀ p : List Bool, p.length < N →
      x p ≤ Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc m₁ ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) p.length p.length
        + (m₂ ^ 2 * κ₁ * χm) * x (p ++ [true]) + (m₁ ^ 2 * κ₂ * χm) * x (p ++ [false]) := fun p _ => by
    have hs := node_step (a := a) K p hc hm₁ hm₁₂ hL hLR hh hα₁ hχb₁ hχ hχm hM hS hε hε2 hδ hμ₁ hμ₂ hψ hu hψc huc hcross hmass
      hσ hσ'c hσL hσR hσ1 hσ'b hS' hκ₁ hκ₂ hκ₁' hκ₂' hg₁ hg₂ hg₁' hg₂' hA₁ hB₁ hA₂ hB₂ hC₁ hC₂
    have hkl := ktrue_add_lfalse p
    have hmono := Ecost_mono (V₁ := Vc m₁ ε δ A₁ B₁ Sp) (V₂ := Vc m₂ ε δ A₂ B₂ Sp) hm₁0 hm₂0 hμ₁ hμ₂ hS' hκ₁ hκ₂
      hκ₁' hκ₂' hC₁m hC₂m (k := lfalse p) (l := ktrue p) (n := p.length) (by omega) (by omega)
    rw [hnorm p] at hs
    simp only [hx]
    rw [div_le_iff₀ (hDpos p)]
    have hDp := (hDpos p).ne'
    have hDT' := (hDpos (p ++ [true])).ne'
    have hDF' := (hDpos (p ++ [false])).ne'
    have e1 : m₂ ^ 2 * κ₁ * χm * (|node c m₁ m₂ L R σ a χ ψ (p ++ [true])| / D (p ++ [true])) * D p
        = m₂ ^ 2 * |node c m₁ m₂ L R σ a χ ψ (p ++ [true])| := by
      rw [hDT]; field_simp
    have e2 : m₁ ^ 2 * κ₂ * χm * (|node c m₁ m₂ L R σ a χ ψ (p ++ [false])| / D (p ++ [false])) * D p
        = m₁ ^ 2 * |node c m₁ m₂ L R σ a χ ψ (p ++ [false])| := by
      rw [hDF]; field_simp
    calc |node c m₁ m₂ L R σ a χ ψ p| ≤ _ := hs
      _ ≤ Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc m₁ ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) p.length p.length * D p
          + m₂ ^ 2 * |node c m₁ m₂ L R σ a χ ψ (p ++ [true])| + m₁ ^ 2 * |node c m₁ m₂ L R σ a χ ψ (p ++ [false])| := by
          gcongr
      _ = _ := by rw [add_mul, add_mul, e1, e2]
  have hleaf : ∀ p : List Bool, p.length = N → x p ≤ (1 / m₁ + 1 / m₂) / 2 := fun p _ => by
    have h := node_leaf (a := a) K p hc hm₁ hm₁₂ hL hLR hχ hχm hM hψc hcross hmass hσc hσ1 hκ₁ hκ₂ hg₁ hg₂
    rw [hnorm p] at h
    simp only [hx]
    rw [div_le_iff₀ (hDpos p)]
    exact h
  have htree := Cvs.Upstream.BinaryTreeDepthSum.tree_sum_depth (x := x)
    (E := fun j => Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc m₁ ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) j j)
    (ρ₁ := m₂ ^ 2 * κ₁ * χm) (ρ₂ := m₁ ^ 2 * κ₂ * χm) (X := (1 / m₁ + 1 / m₂) / 2) (by positivity) (by positivity) N
    hstep hleaf
  have hD0 : D [] = N₀ := by simp [hD, ktrue, lfalse]
  simp only [hx, hD0] at htree
  rwa [div_le_iff₀ hN₀] at htree

end Cvs.L2a.TreeBoundModePair
