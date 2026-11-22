import Mathlib
import Cvs.L2a.BoundaryFreeNodeCostModes
import Cvs.L2a.HierarchyLevelNorms
import Cvs.L2a.HierarchyModePairFactors
import Cvs.L2a.HierarchyModePairNode
import Cvs.L2a.HierarchyModePairNodeInterval
import Cvs.L2a.HierarchyNodeWeight
import Cvs.L2a.HierarchyPathWeight
import Cvs.L2a.PathWeightDerivative
import Cvs.L2a.PathWeightTwoConstants
import Cvs.L2a.RungChiHierarchy
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The step of the project for a mode pair `≥ 2`

For the pair `(m₁, m₂)`, `2 ≤ m₁`, `m₁ + 1 ≤ m₂`, on `[L, R]` with a cutoff `σ`, the node of a path `p` is
`node p = ∫ σ·pw_p · G_k(m₁·) G_l(m₂·)` (`k`, `l` the false and true steps), and `|node p| ≤ E(k, l) κ₁^l κ₂^k χ^{k+l} N₀
+ m₂² |node (p ++ [true])| + m₁² |node (p ++ [false])|` with an explicit `E`: the node cost (Cvs.L2a.BoundaryFreeNodeCostModes), its norms by the
masses (Cvs.L2a.HierarchyLevelNorms), its `f u` weights by the pointwise bound (Cvs.L2a.HierarchyNodeWeight) through `C_i ≥ (S'|g_i| + |g_i'|)² P`, the `λ`s balanced.
-/

namespace Cvs.L2a.TreeStepModePair

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.L2a.HierarchyPathWeight Cvs.L2a.HierarchyModePairNode Cvs.L2a.PathWeightTwoConstants Cvs.L2a.PathWeightDerivative Cvs.L2a.HierarchyNodeWeight

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ktrue_append_true (p : List Bool) : ktrue (p ++ [true]) = ktrue p + 1 := by simp [ktrue]
theorem ktrue_append_false (p : List Bool) : ktrue (p ++ [false]) = ktrue p := by simp [ktrue]
theorem lfalse_append_true (p : List Bool) : lfalse (p ++ [true]) = lfalse p := by simp [lfalse]
theorem lfalse_append_false (p : List Bool) : lfalse (p ++ [false]) = lfalse p + 1 := by simp [lfalse]

/-- The node of a path for the pair `(m₁, m₂)`: the false steps raise the first level, the true steps the second. -/
noncomputable def node (c m₁ m₂ L R : ℝ) (σ : ℝ → ℝ) (a χ : ι → ℝ) (ψ : ι → ℝ → ℝ) (p : List Bool) : ℝ :=
  ∫ θ in L..R, σ θ * pathWeight (g₁ c (m₁ ^ 2) (m₂ ^ 2)) (g₂ c (m₁ ^ 2) (m₂ ^ 2)) p θ
    * (Gk a χ ψ (lfalse p) (m₁ * θ) * Gk a χ ψ (ktrue p) (m₂ * θ))

/-- The `V`-norm constant of a dilation `m` (Cvs.L2a.HierarchyLevelNorms). -/
noncomputable def Vc (m ε δ A B Sp : ℝ) : ℝ := ((A / (2 * ε) + 1 + δ / 2) / m + B * m ^ 3 * Sp ^ 2 / (2 * δ)) / (1 - ε / 2)

/-- The level cost at depth `(k, l)`: `C₁` is the `f u` constant of `g₁` against the second product, `C₂` that of
`g₂` against the first. -/
noncomputable def Ecost (m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ : ℝ) (k l : ℕ) : ℝ :=
  μ₁ / 2 * (1 + grow0 κ₁ κ₂ κ₁' κ₂' k l / S') ^ 2 * C₁ / m₁ + V₂ / (2 * μ₁)
    + (μ₂ / 2 * (1 + grow0 κ₁ κ₂ κ₁' κ₂' k l / S') ^ 2 * C₂ / m₂ + V₁ / (2 * μ₂))

set_option maxHeartbeats 800000 in
/-- **The step of the project for a mode pair**, un-normalised. -/
theorem node_step {c m₁ m₂ L R χb χm Sp h ε δ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' A₁ B₁ A₂ B₂ C₁ C₂ : ℝ}
    {a χ Mm : ι → ℝ} {ψ u : ι → ℝ → ℝ} (K : ι → ι → ℝ) {σ σ' : ℝ → ℝ} (p : List Bool)
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
      * ((m₁ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₁ ^ 2) ^ 2 * θ ^ 2 - m₁ ^ 2 * χb)) ≤ C₂) :
    |node c m₁ m₂ L R σ a χ ψ p|
      ≤ Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc m₁ ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) (lfalse p) (ktrue p)
          * (κ₁ ^ ktrue p * κ₂ ^ lfalse p * χm ^ (ktrue p + lfalse p) * ∑ i, a i ^ 2 * Mm i)
        + m₂ ^ 2 * |node c m₁ m₂ L R σ a χ ψ (p ++ [true])|
        + m₁ ^ 2 * |node c m₁ m₂ L R σ a χ ψ (p ++ [false])| := by
  -- names
  set k := lfalse p with hk_def
  set l := ktrue p with hl_def
  set N₀ := ∑ i, a i ^ 2 * Mm i with hN₀
  set pw := pathWeight (g₁ c (m₁ ^ 2) (m₂ ^ 2)) (g₂ c (m₁ ^ 2) (m₂ ^ 2)) p with hpw
  set pw' := pathWeight' (g₁ c (m₁ ^ 2) (m₂ ^ 2)) (g₂ c (m₁ ^ 2) (m₂ ^ 2)) (g₁' c (m₁ ^ 2) (m₂ ^ 2)) (g₂' c (m₁ ^ 2) (m₂ ^ 2)) p with hpw'
  set G := 1 + grow0 κ₁ κ₂ κ₁' κ₂' k l / S' with hG
  set Kp := κ₁ ^ l * κ₂ ^ k with hKp
  have hs : 4 ≤ m₁ ^ 2 := by nlinarith
  have hst : m₁ ^ 2 + 5 ≤ m₂ ^ 2 := by nlinarith
  have hm₁0 : 0 < m₁ := by linarith
  have hm₂0 : 0 < m₂ := by linarith
  have hθL : ∀ θ ∈ Icc L R, 19 / 20 ≤ θ := fun θ hθ => hL.trans hθ.1
  have hL0 : 0 < L := by linarith
  have hLh : 0 < L - h := by nlinarith
  have hα₂ : 1 < m₂ * (L - h) := by nlinarith
  have hχb₂ : χb < c ^ 2 * m₂ ^ 2 * (L - h) ^ 2 := by
    have : c ^ 2 * m₁ ^ 2 * (L - h) ^ 2 ≤ c ^ 2 * m₂ ^ 2 * (L - h) ^ 2 := by
      have h1 : m₁ ^ 2 ≤ m₂ ^ 2 := pow_le_pow_left₀ hm₁0.le (by linarith) 2
      have h2 : 0 ≤ c ^ 2 * (L - h) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 h2]
    linarith
  have hN₀ : 0 ≤ N₀ := Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (a i), hM i]
  have hKp0 : 0 < Kp := by positivity
  have hG0 : 0 ≤ G := by rw [hG]; unfold grow0; positivity
  have hχk : 0 < χm ^ (l + k) := by positivity
  -- the systems of the two dilations (Cvs.L2a.RungChiHierarchy), in the form of Cvs.L2a.BoundaryFreeNodeCostModes
  have hsys₁ : ∀ θ ∈ Icc L R,
      HasDerivAt (fun θ => Gk a χ ψ k (m₁ * θ)) (m₁ * Gk a χ u k (m₁ * θ) / (m₁ ^ 2 * θ ^ 2 - 1)) θ ∧
      HasDerivAt (fun θ => m₁ * Gk a χ u k (m₁ * θ))
        (-(c ^ 2 * (m₁ ^ 2) ^ 2 * θ ^ 2 * Gk a χ ψ k (m₁ * θ)) + m₁ ^ 2 * Gk a χ ψ (k + 1) (m₁ * θ)) θ := fun θ hθ => by
    have hmθ : 1 < m₁ * θ := by nlinarith [hθL θ hθ]
    obtain ⟨h1, h2⟩ := hasDerivAt_Gk_dilate (c := c) (a := a) (χ := χ) (ψ := ψ) (u := u) (m := m₁) (θ := θ) k
      (fun i => hψ i (m₁ * θ) hmθ) (fun i => hu i (m₁ * θ))
    exact ⟨h1, h2.congr_deriv (by ring)⟩
  have hsys₂ : ∀ θ ∈ Icc L R,
      HasDerivAt (fun θ => Gk a χ ψ l (m₂ * θ)) (m₂ * Gk a χ u l (m₂ * θ) / (m₂ ^ 2 * θ ^ 2 - 1)) θ ∧
      HasDerivAt (fun θ => m₂ * Gk a χ u l (m₂ * θ))
        (-(c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 * Gk a χ ψ l (m₂ * θ)) + m₂ ^ 2 * Gk a χ ψ (l + 1) (m₂ * θ)) θ := fun θ hθ => by
    have hmθ : 1 < m₂ * θ := by nlinarith [hθL θ hθ]
    obtain ⟨h1, h2⟩ := hasDerivAt_Gk_dilate (c := c) (a := a) (χ := χ) (ψ := ψ) (u := u) (m := m₂) (θ := θ) l
      (fun i => hψ i (m₂ * θ) hmθ) (fun i => hu i (m₂ * θ))
    exact ⟨h1, h2.congr_deriv (by ring)⟩
  have hGc : ∀ j m, Continuous fun θ => Gk a χ ψ j (m * θ) := fun j m => by
    unfold Gk
    exact continuous_finsetSum _ fun i _ => continuous_const.mul ((hψc i).comp (continuous_const.mul continuous_id))
  -- the node weight and its bounds (Cvs.L2a.HierarchyNodeWeight)
  obtain ⟨hg₁c, hg₂c, hg₁'c, hg₂'c⟩ := Cvs.L2a.BoundaryFreeNodeCostModes.continuousOn_factors (R := R) hc hs hst hL
  have hd₁ : ∀ θ ∈ Icc L R, HasDerivAt (g₁ c (m₁ ^ 2) (m₂ ^ 2)) (g₁' c (m₁ ^ 2) (m₂ ^ 2) θ) θ := fun θ hθ => by
    have := Cvs.L2a.HierarchyModePairNodeInterval.hasDerivAt_g₁' hc hs hst (hθL θ hθ)
    exact this
  have hd₂ : ∀ θ ∈ Icc L R, HasDerivAt (g₂ c (m₁ ^ 2) (m₂ ^ 2)) (g₂' c (m₁ ^ 2) (m₂ ^ 2) θ) θ := fun θ hθ =>
    Cvs.L2a.HierarchyModePairNodeInterval.hasDerivAt_g₂' hc hs hst (hθL θ hθ)
  have hσp := hasDerivAt_node_weight (s := Icc L R) hσ hd₁ hd₂ p
  have hσp'c : ContinuousOn (fun θ => σ' θ * pw θ + σ θ * pw' θ) (Icc L R) := by
    have hσc : ContinuousOn σ (Icc L R) := fun θ hθ => (hσ θ hθ).continuousAt.continuousWithinAt
    exact (hσ'c.mul (continuousOn_pathWeight hg₁c hg₂c p)).add
      (hσc.mul (continuousOn_pathWeight' hg₁c hg₂c hg₁'c hg₂'c p))
  obtain ⟨hwα, hwβ⟩ := node_weight_coeff_pointwise (s := Icc L R) hκ₁ hκ₂ hκ₁' hκ₂' hS' hσ1 hσ'b hg₁ hg₂ hg₁' hg₂' p
  -- positivity of the centred products on `[L, R]`
  have hχbL : χb < c ^ 2 * m₁ ^ 2 * L ^ 2 := by
    have : c ^ 2 * m₁ ^ 2 * (L - h) ^ 2 ≤ c ^ 2 * m₁ ^ 2 * L ^ 2 := by
      have : (L - h) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hLh.le (by linarith) 2
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hP₁pos : ∀ θ ∈ Icc L R, 0 < (m₁ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₁ ^ 2) ^ 2 * θ ^ 2 - m₁ ^ 2 * χb) := fun θ hθ => by
    have hθ2 : L ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hL0.le hθ.1 2
    have hθ2' : 361 / 400 ≤ θ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 19 / 20) (hθL θ hθ) 2
      norm_num at this; linarith
    have h1 : 0 < m₁ ^ 2 * θ ^ 2 - 1 := by
      have := mul_le_mul_of_nonneg_left hθ2' (by positivity : (0:ℝ) ≤ m₁ ^ 2)
      linarith
    have h2 : c ^ 2 * m₁ ^ 2 * L ^ 2 ≤ c ^ 2 * m₁ ^ 2 * θ ^ 2 := mul_le_mul_of_nonneg_left hθ2 (by positivity)
    have h3 : 0 < c ^ 2 * m₁ ^ 2 * θ ^ 2 - χb := by linarith
    have : 0 < m₁ ^ 2 * (c ^ 2 * m₁ ^ 2 * θ ^ 2 - χb) := mul_pos (by positivity) h3
    have e : m₁ ^ 2 * (c ^ 2 * m₁ ^ 2 * θ ^ 2 - χb) = c ^ 2 * (m₁ ^ 2) ^ 2 * θ ^ 2 - m₁ ^ 2 * χb := by ring
    exact mul_pos h1 (by linarith)
  have hP₂pos : ∀ θ ∈ Icc L R, 0 < (m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb) := fun θ hθ => by
    have hθ2 : L ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hL0.le hθ.1 2
    have hθ2' : 361 / 400 ≤ θ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 19 / 20) (hθL θ hθ) 2
      norm_num at this; linarith
    have h1 : 0 < m₂ ^ 2 * θ ^ 2 - 1 := by
      have := mul_le_mul_of_nonneg_left hθ2' (by positivity : (0:ℝ) ≤ m₂ ^ 2)
      have h4 : (4:ℝ) ≤ m₂ ^ 2 := by linarith
      linarith
    have hm12 : m₁ ^ 2 ≤ m₂ ^ 2 := pow_le_pow_left₀ hm₁0.le (by linarith) 2
    have h2 : c ^ 2 * m₁ ^ 2 * L ^ 2 ≤ c ^ 2 * m₂ ^ 2 * θ ^ 2 := by
      have hA : c ^ 2 * m₁ ^ 2 * L ^ 2 ≤ c ^ 2 * m₂ ^ 2 * L ^ 2 := by
        have : 0 ≤ c ^ 2 * L ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hm12 this
        linarith
      have hB : c ^ 2 * m₂ ^ 2 * L ^ 2 ≤ c ^ 2 * m₂ ^ 2 * θ ^ 2 := mul_le_mul_of_nonneg_left hθ2 (by positivity)
      linarith
    have h3 : 0 < c ^ 2 * m₂ ^ 2 * θ ^ 2 - χb := by linarith
    have : 0 < m₂ ^ 2 * (c ^ 2 * m₂ ^ 2 * θ ^ 2 - χb) := mul_pos (by positivity) h3
    have e : m₂ ^ 2 * (c ^ 2 * m₂ ^ 2 * θ ^ 2 - χb) = c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb := by ring
    exact mul_pos h1 (by linarith)
  -- the constants of the `f u` terms (Cvs.L2a.HierarchyNodeWeight)
  have hGK : 0 ≤ G * Kp := mul_nonneg hG0 hKp0.le
  have hC₁' : ∀ θ ∈ Icc L R, ((σ' θ * pw θ + σ θ * pw' θ) * g₁ c (m₁ ^ 2) (m₂ ^ 2) θ
        + σ θ * pw θ * g₁' c (m₁ ^ 2) (m₂ ^ 2) θ) ^ 2
      * ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb)) ≤ (G * Kp) ^ 2 * C₁ :=
    fun θ hθ => sq_mul_le_of_abs_le_prod (hwα θ hθ) hGK (hP₂pos θ hθ).le (hC₁ θ hθ)
  have hC₂' : ∀ θ ∈ Icc L R, ((σ' θ * pw θ + σ θ * pw' θ) * g₂ c (m₁ ^ 2) (m₂ ^ 2) θ
        + σ θ * pw θ * g₂' c (m₁ ^ 2) (m₂ ^ 2) θ) ^ 2
      * ((m₁ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₁ ^ 2) ^ 2 * θ ^ 2 - m₁ ^ 2 * χb)) ≤ (G * Kp) ^ 2 * C₂ :=
    fun θ hθ => sq_mul_le_of_abs_le_prod (hwβ θ hθ) hGK (hP₁pos θ hθ).le (hC₂ θ hθ)
  -- the balanced `λ`s
  set lam₁ := μ₁ * χm ^ l / (χm ^ k * Kp) with hlam₁
  set lam₂ := μ₂ * χm ^ k / (χm ^ l * Kp) with hlam₂
  have hl₁ : 0 < lam₁ := by positivity
  have hl₂ : 0 < lam₂ := by positivity
  -- the node cost (Cvs.L2a.BoundaryFreeNodeCostModes)
  have hnode := Cvs.L2a.BoundaryFreeNodeCostModes.node_cost (c := c) (s := m₁ ^ 2) (t := m₂ ^ 2) (L := L) (R := R) (χb := χb)
    (lam₁ := lam₁) (lam₂ := lam₂) (C₁ := (G * Kp) ^ 2 * C₁) (C₂ := (G * Kp) ^ 2 * C₂)
    hc hs hst hL hLR hχbL hl₁ hl₂ (σ := fun θ => σ θ * pw θ) (σ' := fun θ => σ' θ * pw θ + σ θ * pw' θ)
    (f₁ := fun θ => Gk a χ ψ k (m₁ * θ)) (u₁ := fun θ => m₁ * Gk a χ u k (m₁ * θ))
    (f₁p := fun θ => Gk a χ ψ (k + 1) (m₁ * θ))
    (f₂ := fun θ => Gk a χ ψ l (m₂ * θ)) (u₂ := fun θ => m₂ * Gk a χ u l (m₂ * θ))
    (f₂p := fun θ => Gk a χ ψ (l + 1) (m₂ * θ))
    hσp hσp'c (by simp [hσL]) (by simp [hσR])
    (fun θ hθ => (hsys₁ θ hθ).1) (fun θ hθ => (hsys₁ θ hθ).2) (fun θ hθ => (hsys₂ θ hθ).1) (fun θ hθ => (hsys₂ θ hθ).2)
    (hGc (k + 1) m₁).continuousOn (hGc (l + 1) m₂).continuousOn hC₁' hC₂'
  -- the norms (Cvs.L2a.HierarchyLevelNorms)
  have hcont : ∀ i, ContinuousOn (ψ i) (Ici 1) := fun i => (hψc i).continuousOn
  have hL₁ : 1 ≤ m₁ * L := by
    have e : m₁ * (L - h) = m₁ * L - m₁ * h := by ring
    have := mul_nonneg hm₁0.le hh.le
    linarith
  have hL₂ : 1 ≤ m₂ * L := by
    have := mul_le_mul_of_nonneg_right (by linarith : m₁ ≤ m₂) hL0.le
    linarith
  have hRL₁ : m₁ * L ≤ m₁ * R := mul_le_mul_of_nonneg_left hLR hm₁0.le
  have hRL₂ : m₂ * L ≤ m₂ * R := mul_le_mul_of_nonneg_left hLR hm₂0.le
  have hRh₁ : m₁ * R ≤ m₁ * (R + h) := mul_le_mul_of_nonneg_left (by linarith) hm₁0.le
  have hRh₂ : m₂ * R ≤ m₂ * (R + h) := mul_le_mul_of_nonneg_left (by linarith) hm₂0.le
  have hn₁ : ∫ θ in L..R, Gk a χ ψ k (m₁ * θ) ^ 2 ≤ 1 / m₁ * (χm ^ (2 * k) * N₀) :=
    Cvs.L2a.HierarchyLevelNorms.level_norm_le K k hm₁0 hL₁ hLR hχ hM hcont (fun i j hij t ht => hcross i j hij t (by linarith))
      (fun i t ht => hmass i t (by linarith))
  have hn₂ : ∫ θ in L..R, Gk a χ ψ l (m₂ * θ) ^ 2 ≤ 1 / m₂ * (χm ^ (2 * l) * N₀) :=
    Cvs.L2a.HierarchyLevelNorms.level_norm_le K l hm₂0 hL₂ hLR hχ hM hcont (fun i j hij t ht => hcross i j hij t (by linarith))
      (fun i t ht => hmass i t (by linarith))
  have hV₁raw := Cvs.L2a.HierarchyLevelNorms.level_V_norm_le (c := c) (m := m₁) (χb := χb) (L := L) (R := R) (h := h)
    (ε := ε) (δ := δ) (A := A₁) (B := B₁) (a := a) (χ := χ) (Mm := Mm) (χm := χm) (S := Sp) (ψ := ψ) (u := u) K k
    hm₁0 hh hα₁ hχb₁ hLR hε hε2 hδ hχ hM hS hψ hu hψc huc
    (fun i j hij t ht => hcross i j hij t (by linarith)) (fun i t ht => hmass i t (by linarith)) hA₁ hB₁
  have hV₂raw := Cvs.L2a.HierarchyLevelNorms.level_V_norm_le (c := c) (m := m₂) (χb := χb) (L := L) (R := R) (h := h)
    (ε := ε) (δ := δ) (A := A₂) (B := B₂) (a := a) (χ := χ) (Mm := Mm) (χm := χm) (S := Sp) (ψ := ψ) (u := u) K l
    hm₂0 hh hα₂ hχb₂ hLR hε hε2 hδ hχ hM hS hψ hu hψc huc
    (fun i j hij t ht => hcross i j hij t (by linarith)) (fun i t ht => hmass i t (by linarith)) hA₂ hB₂
  have hε' : 0 < 1 - ε / 2 := by linarith
  have eV₁ : (fun θ => (m₁ * Gk a χ u k (m₁ * θ)) ^ 2 / ((m₁ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₁ ^ 2) ^ 2 * θ ^ 2 - m₁ ^ 2 * χb)))
      = fun θ => (m₁ * Gk a χ u k (m₁ * θ)) ^ 2 / ((m₁ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * m₁ ^ 4 * θ ^ 2 - m₁ ^ 2 * χb)) := by
    funext θ; ring_nf
  have eV₂ : (fun θ => (m₂ * Gk a χ u l (m₂ * θ)) ^ 2 / ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb)))
      = fun θ => (m₂ * Gk a χ u l (m₂ * θ)) ^ 2 / ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb)) := by
    funext θ; ring_nf
  have hV₁ : ∫ θ in L..R, (m₁ * Gk a χ u k (m₁ * θ)) ^ 2
      / ((m₁ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₁ ^ 2) ^ 2 * θ ^ 2 - m₁ ^ 2 * χb))
      ≤ Vc m₁ ε δ A₁ B₁ Sp * (χm ^ (2 * k) * N₀) := by
    rw [eV₁]; unfold Vc; rw [div_mul_eq_mul_div, le_div_iff₀ hε']; linarith [hV₁raw]
  have hV₂ : ∫ θ in L..R, (m₂ * Gk a χ u l (m₂ * θ)) ^ 2
      / ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb))
      ≤ Vc m₂ ε δ A₂ B₂ Sp * (χm ^ (2 * l) * N₀) := by
    rw [eV₂]; unfold Vc; rw [div_mul_eq_mul_div, le_div_iff₀ hε']; linarith [hV₂raw]
  -- the children are the nodes of the extended paths
  have hchild₁ : ∫ θ in L..R, σ θ * pw θ * g₁ c (m₁ ^ 2) (m₂ ^ 2) θ * (Gk a χ ψ k (m₁ * θ) * Gk a χ ψ (l + 1) (m₂ * θ))
      = node c m₁ m₂ L R σ a χ ψ (p ++ [true]) := by
    unfold node
    rw [lfalse_append_true, ktrue_append_true]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ _ => ?_)
    rw [pathWeight_append]; simp only [hpw, ite_true]; ring
  have hchild₂ : ∫ θ in L..R, σ θ * pw θ * g₂ c (m₁ ^ 2) (m₂ ^ 2) θ * (Gk a χ ψ (k + 1) (m₁ * θ) * Gk a χ ψ l (m₂ * θ))
      = node c m₁ m₂ L R σ a χ ψ (p ++ [false]) := by
    unfold node
    rw [lfalse_append_false, ktrue_append_false]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ _ => ?_)
    rw [pathWeight_append]; simp only [hpw, Bool.false_eq_true, ite_false]; ring
  have e0 : node c m₁ m₂ L R σ a χ ψ p = ∫ θ in L..R, σ θ * pw θ * (Gk a χ ψ k (m₁ * θ) * Gk a χ ψ l (m₂ * θ)) := rfl
  rw [e0]
  rw [hchild₁, hchild₂] at hnode
  -- the algebra of the four cost terms
  have hC₁0 : 0 ≤ (G * Kp) ^ 2 * C₁ := by
    have := hC₁ L ⟨le_rfl, hLR⟩
    exact mul_nonneg (sq_nonneg _) (le_trans (mul_nonneg (sq_nonneg _) (hP₂pos L ⟨le_rfl, hLR⟩).le) this)
  have hC₂0 : 0 ≤ (G * Kp) ^ 2 * C₂ := by
    have := hC₂ L ⟨le_rfl, hLR⟩
    exact mul_nonneg (sq_nonneg _) (le_trans (mul_nonneg (sq_nonneg _) (hP₁pos L ⟨le_rfl, hLR⟩).le) this)
  have hT₁ : lam₁ * ((G * Kp) ^ 2 * C₁) / 2 * (∫ θ in L..R, Gk a χ ψ k (m₁ * θ) ^ 2)
      ≤ μ₁ / 2 * G ^ 2 * C₁ / m₁ * (Kp * χm ^ (l + k) * N₀) := by
    calc _ ≤ lam₁ * ((G * Kp) ^ 2 * C₁) / 2 * (1 / m₁ * (χm ^ (2 * k) * N₀)) := by gcongr
      _ = _ := by rw [hlam₁]; field_simp; ring
  have hT₂ : 1 / (2 * lam₁) * (∫ θ in L..R, (m₂ * Gk a χ u l (m₂ * θ)) ^ 2
        / ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb)))
      ≤ Vc m₂ ε δ A₂ B₂ Sp / (2 * μ₁) * (Kp * χm ^ (l + k) * N₀) := by
    calc _ ≤ 1 / (2 * lam₁) * (Vc m₂ ε δ A₂ B₂ Sp * (χm ^ (2 * l) * N₀)) := by gcongr
      _ = _ := by rw [hlam₁]; field_simp; ring
  have hT₃ : lam₂ * ((G * Kp) ^ 2 * C₂) / 2 * (∫ θ in L..R, Gk a χ ψ l (m₂ * θ) ^ 2)
      ≤ μ₂ / 2 * G ^ 2 * C₂ / m₂ * (Kp * χm ^ (l + k) * N₀) := by
    calc _ ≤ lam₂ * ((G * Kp) ^ 2 * C₂) / 2 * (1 / m₂ * (χm ^ (2 * l) * N₀)) := by gcongr
      _ = _ := by rw [hlam₂]; field_simp; ring
  have hT₄ : 1 / (2 * lam₂) * (∫ θ in L..R, (m₁ * Gk a χ u k (m₁ * θ)) ^ 2
        / ((m₁ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₁ ^ 2) ^ 2 * θ ^ 2 - m₁ ^ 2 * χb)))
      ≤ Vc m₁ ε δ A₁ B₁ Sp / (2 * μ₂) * (Kp * χm ^ (l + k) * N₀) := by
    calc _ ≤ 1 / (2 * lam₂) * (Vc m₁ ε δ A₁ B₁ Sp * (χm ^ (2 * k) * N₀)) := by gcongr
      _ = _ := by rw [hlam₂]; field_simp; ring
  have eE : Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc m₁ ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) k l
        * (κ₁ ^ l * κ₂ ^ k * χm ^ (l + k) * N₀)
      = μ₁ / 2 * G ^ 2 * C₁ / m₁ * (Kp * χm ^ (l + k) * N₀)
        + Vc m₂ ε δ A₂ B₂ Sp / (2 * μ₁) * (Kp * χm ^ (l + k) * N₀)
        + (μ₂ / 2 * G ^ 2 * C₂ / m₂ * (Kp * χm ^ (l + k) * N₀)
          + Vc m₁ ε δ A₁ B₁ Sp / (2 * μ₂) * (Kp * χm ^ (l + k) * N₀)) := by
    unfold Ecost; rw [hKp, hG]; ring
  rw [eE]
  linarith [hnode, hT₁, hT₂, hT₃, hT₄]

end Cvs.L2a.TreeStepModePair
