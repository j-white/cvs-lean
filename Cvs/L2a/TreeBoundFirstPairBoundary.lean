import Mathlib
import Cvs.L2a.BoundaryFreeNodeCostFirst
import Cvs.L2a.BoundaryNodeCostFirst
import Cvs.L2a.HierarchyFirstPairNodeInterval
import Cvs.L2a.HierarchyLevelNorms
import Cvs.L2a.HierarchyModePairFactors
import Cvs.L2a.HierarchyModePairNode
import Cvs.L2a.HierarchyNodeWeight
import Cvs.L2a.HierarchyPathWeight
import Cvs.L2a.PathWeightDerivative
import Cvs.L2a.PathWeightTwoConstants
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.TreeBoundFirstPair
import Cvs.L2a.TreeBoundModePair
import Cvs.L2a.TreeStepFirstPair
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
# The step and the project bound of a pair `(1, k)` with the boundary at `b`

The ramp of the `(1, k)` pairs is `1` at `b`, so their nodes keep a boundary term there (Cvs.L2a.BoundaryNodeCostFirst), bounded by
`κ₁^l κ₂^k χ^{k+l} B_c` with `B_c = κ₁ᴿ P_ψ(R)·m₂P_u(m₂R) + κ₂ᴿ P_u(R)·P_ψ(m₂R)`, `κ_iᴿ ≥ |g_i(R)|`, `P_f(ξ) = Σ |a_i||f_i(ξ)|`
(`|G_k(ξ)| ≤ χ^k P_ψ(ξ)`); the step is that of Cvs.L2a.TreeStepFirstPair plus this term, and the project sum gives
`|∫ σ G G(m₂·)| ≤ (Σ_{j<N} ρ^j (E(j) + B_c/N₀) + ρ^N X) N₀`.
-/

namespace Cvs.L2a.TreeBoundFirstPairBoundary

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.L2a.HierarchyPathWeight Cvs.L2a.HierarchyModePairNode Cvs.L2a.PathWeightTwoConstants Cvs.L2a.PathWeightDerivative Cvs.L2a.HierarchyNodeWeight Cvs.L2a.TreeStepModePair Cvs.L2a.TreeBoundModePair Cvs.L2a.TreeStepFirstPair Cvs.L2a.TreeBoundFirstPair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `Σ |a_i| |f_i(ξ)|`. -/
noncomputable def Pabs (a : ι → ℝ) (f : ι → ℝ → ℝ) (ξ : ℝ) : ℝ := ∑ i, |a i| * |f i ξ|

theorem Pabs_nonneg (a : ι → ℝ) (f : ι → ℝ → ℝ) (ξ : ℝ) : 0 ≤ Pabs a f ξ :=
  Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- `|G_k(ξ)| ≤ χ^k P_ψ(ξ)` for `0 ≤ χ_i ≤ χ`. -/
theorem abs_Gk_le {a χ : ι → ℝ} {f : ι → ℝ → ℝ} {χm ξ : ℝ} (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (k : ℕ) :
    |Gk a χ f k ξ| ≤ χm ^ k * Pabs a f ξ := by
  unfold Gk Pabs
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (hχ i).1 k)]
  have : χ i ^ k ≤ χm ^ k := pow_le_pow_left₀ (hχ i).1 (hχ i).2 k
  calc |a i| * χ i ^ k * |f i ξ| ≤ |a i| * χm ^ k * |f i ξ| := by gcongr
    _ = χm ^ k * (|a i| * |f i ξ|) := by ring

/-- The boundary constant of the pair `(1, m₂)` at `R`, with the values of the factors at `R`. -/
noncomputable def Bc (a : ι → ℝ) (ψ u : ι → ℝ → ℝ) (m₂ R κ₁R κ₂R : ℝ) : ℝ :=
  κ₁R * Pabs a ψ R * (m₂ * Pabs a u (m₂ * R)) + κ₂R * Pabs a u R * Pabs a ψ (m₂ * R)

set_option maxHeartbeats 800000 in
/-- **The step of the project for a pair `(1, k)` with its boundary at `R`**, un-normalised. -/
theorem node_step_first_bd {c m₂ L R χb χm Sp h ε δ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' A₁ B₁ A₂ B₂ C₁ C₂ : ℝ}
    {a χ Mm : ι → ℝ} {ψ u : ι → ℝ → ℝ} (K : ι → ι → ℝ) {σ σ' : ℝ → ℝ} (p : List Bool)
    (hc : 0 < c) (hm₂ : 2 ≤ m₂) (hL : 4 / 3 ≤ L) (hLR : L ≤ R) (hh : 0 < h)
    (hα₁ : 1 < 1 * (L - h)) (hχb₁ : χb < c ^ 2 * 1 ^ 2 * (L - h) ^ 2)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hχm : 0 < χm) (hM : ∀ i, 0 ≤ Mm i) (hS : ∀ i, |χ i - χb| ≤ Sp)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hψ : ∀ i, ∀ ξ, 1 < ξ → HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hψc : ∀ i, Continuous (ψ i)) (huc : ∀ i, Continuous (u i))
    (hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hσ : ∀ θ ∈ Icc L R, HasDerivAt σ (σ' θ) θ) (hσ'c : ContinuousOn σ' (Icc L R)) (hσL : σ L = 0)
    (hσ1 : ∀ θ ∈ Icc L R, |σ θ| ≤ 1) (hσ'b : ∀ θ ∈ Icc L R, |σ' θ| ≤ S') (hS' : 0 < S')
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hκ₁' : 0 ≤ κ₁') (hκ₂' : 0 ≤ κ₂')
    (hg₁ : ∀ θ ∈ Icc L R, |g₁ c 1 (m₂ ^ 2) θ| ≤ κ₁) (hg₂ : ∀ θ ∈ Icc L R, |g₂ c 1 (m₂ ^ 2) θ| ≤ κ₂)
    (hg₁' : ∀ θ ∈ Icc L R, |g₁' c 1 (m₂ ^ 2) θ| ≤ κ₁') (hg₂' : ∀ θ ∈ Icc L R, |g₂' c 1 (m₂ ^ 2) θ| ≤ κ₂')
    {κ₁R κ₂R : ℝ} (hg₁R : |g₁ c 1 (m₂ ^ 2) R| ≤ κ₁R) (hg₂R : |g₂ c 1 (m₂ ^ 2) R| ≤ κ₂R)
    (hA₁ : ∀ θ ∈ Icc (L - h) (R + h), 2 * (1 ^ 2 * θ ^ 2 - 1)
      * ((Real.pi / h) ^ 2 / (c ^ 2 * 1 ^ 4 * θ ^ 2 - 1 ^ 2 * χb)
        + (2 * c ^ 2 * 1 ^ 4 * θ) ^ 2 / (c ^ 2 * 1 ^ 4 * θ ^ 2 - 1 ^ 2 * χb) ^ 3) ≤ A₁)
    (hB₁ : ∀ θ ∈ Icc (L - h) (R + h), 1 / (c ^ 2 * 1 ^ 4 * θ ^ 2 - 1 ^ 2 * χb) ^ 2 ≤ B₁)
    (hA₂ : ∀ θ ∈ Icc (L - h) (R + h), 2 * (m₂ ^ 2 * θ ^ 2 - 1)
      * ((Real.pi / h) ^ 2 / (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb)
        + (2 * c ^ 2 * m₂ ^ 4 * θ) ^ 2 / (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb) ^ 3) ≤ A₂)
    (hB₂ : ∀ θ ∈ Icc (L - h) (R + h), 1 / (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb) ^ 2 ≤ B₂)
    (hC₁ : ∀ θ ∈ Icc L R, (S' * |g₁ c 1 (m₂ ^ 2) θ| + |g₁' c 1 (m₂ ^ 2) θ|) ^ 2
      * ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb)) ≤ C₁)
    (hC₂ : ∀ θ ∈ Icc L R, (S' * |g₂ c 1 (m₂ ^ 2) θ| + |g₂' c 1 (m₂ ^ 2) θ|) ^ 2
      * ((1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb)) ≤ C₂) :
    |nodeFirst c m₂ L R σ a χ ψ p|
      ≤ Ecost 1 m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc 1 ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) (lfalse p) (ktrue p)
          * (κ₁ ^ ktrue p * κ₂ ^ lfalse p * χm ^ (ktrue p + lfalse p) * ∑ i, a i ^ 2 * Mm i)
        + κ₁ ^ ktrue p * κ₂ ^ lfalse p * χm ^ (ktrue p + lfalse p) * Bc a ψ u m₂ R κ₁R κ₂R
        + m₂ ^ 2 * |nodeFirst c m₂ L R σ a χ ψ (p ++ [true])|
        + 1 * |nodeFirst c m₂ L R σ a χ ψ (p ++ [false])| := by
  -- names
  set k := lfalse p with hk_def
  set l := ktrue p with hl_def
  set N₀ := ∑ i, a i ^ 2 * Mm i with hN₀
  set pw := pathWeight (g₁ c 1 (m₂ ^ 2)) (g₂ c 1 (m₂ ^ 2)) p with hpw
  set pw' := pathWeight' (g₁ c 1 (m₂ ^ 2)) (g₂ c 1 (m₂ ^ 2)) (g₁' c 1 (m₂ ^ 2)) (g₂' c 1 (m₂ ^ 2)) p with hpw'
  set G := 1 + grow0 κ₁ κ₂ κ₁' κ₂' k l / S' with hG
  have hG0 : 0 ≤ G := by rw [hG]; unfold grow0; positivity
  set Kp := κ₁ ^ l * κ₂ ^ k with hKp
  have ht : 4 ≤ m₂ ^ 2 := by nlinarith
  have hm₂0 : 0 < m₂ := by linarith
  have hθL : ∀ θ ∈ Icc L R, 4 / 3 ≤ θ := fun θ hθ => hL.trans hθ.1
  have hL0 : 0 < L := by linarith
  have hLh : 0 < L - h := by linarith
  have hα₂ : 1 < m₂ * (L - h) := by
    have := mul_le_mul_of_nonneg_right hm₂ hLh.le
    linarith
  have hχb₂ : χb < c ^ 2 * m₂ ^ 2 * (L - h) ^ 2 := by
    have h1 : (1:ℝ) ≤ m₂ ^ 2 := by linarith
    have h2 : 0 ≤ c ^ 2 * (L - h) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    linarith
  have hN₀ : 0 ≤ N₀ := Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (a i), hM i]
  have hKp0 : 0 < Kp := by positivity
  have hχk : 0 < χm ^ (l + k) := by positivity
  -- the systems: the first undilated (Cvs.L2a.RungChiHierarchy), the second dilated by `m₂`, in the form of Cvs.L2a.BoundaryFreeNodeCostFirst
  have hsys₁ : ∀ θ ∈ Icc L R,
      HasDerivAt (Gk a χ ψ k) (Gk a χ u k θ / (1 * θ ^ 2 - 1)) θ ∧
      HasDerivAt (Gk a χ u k) (-(c ^ 2 * 1 ^ 2 * θ ^ 2 * Gk a χ ψ k θ) + 1 * Gk a χ ψ (k + 1) θ) θ := fun θ hθ => by
    have hθ1 : 1 < θ := by linarith [hθL θ hθ]
    obtain ⟨h1, h2⟩ := hasDerivAt_Gk (c := c) (a := a) (χ := χ) (ψ := ψ) (u := u) (ξ := θ) k
      (fun i => hψ i θ hθ1) (fun i => hu i θ)
    refine ⟨h1.congr_deriv ?_, h2.congr_deriv (by ring)⟩
    unfold pP; ring
  have hsys₂ : ∀ θ ∈ Icc L R,
      HasDerivAt (fun θ => Gk a χ ψ l (m₂ * θ)) (m₂ * Gk a χ u l (m₂ * θ) / (m₂ ^ 2 * θ ^ 2 - 1)) θ ∧
      HasDerivAt (fun θ => m₂ * Gk a χ u l (m₂ * θ))
        (-(c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 * Gk a χ ψ l (m₂ * θ)) + m₂ ^ 2 * Gk a χ ψ (l + 1) (m₂ * θ)) θ := fun θ hθ => by
    have hmθ : 1 < m₂ * θ := by
      have := mul_le_mul hm₂ (hθL θ hθ) (by norm_num) hm₂0.le
      linarith
    obtain ⟨h1, h2⟩ := hasDerivAt_Gk_dilate (c := c) (a := a) (χ := χ) (ψ := ψ) (u := u) (m := m₂) (θ := θ) l
      (fun i => hψ i (m₂ * θ) hmθ) (fun i => hu i (m₂ * θ))
    exact ⟨h1, h2.congr_deriv (by ring)⟩
  have hGc : ∀ j m, Continuous fun θ => Gk a χ ψ j (m * θ) := fun j m => by
    unfold Gk
    exact continuous_finsetSum _ fun i _ => continuous_const.mul ((hψc i).comp (continuous_const.mul continuous_id))
  have hGc0 : ∀ j, Continuous (Gk a χ ψ j) := fun j => by
    unfold Gk
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  -- the node weight and its bounds (Cvs.L2a.HierarchyNodeWeight)
  obtain ⟨hg₁c, hg₂c, hg₁'c, hg₂'c⟩ := Cvs.L2a.BoundaryFreeNodeCostFirst.continuousOn_factors_first (R := R) hc ht hL
  have hd₁ : ∀ θ ∈ Icc L R, HasDerivAt (g₁ c 1 (m₂ ^ 2)) (g₁' c 1 (m₂ ^ 2) θ) θ := fun θ hθ => by
    have := Cvs.L2a.HierarchyFirstPairNodeInterval.hasDerivAt_g₁_first' hc ht (hθL θ hθ)
    exact this
  have hd₂ : ∀ θ ∈ Icc L R, HasDerivAt (g₂ c 1 (m₂ ^ 2)) (g₂' c 1 (m₂ ^ 2) θ) θ := fun θ hθ =>
    Cvs.L2a.HierarchyFirstPairNodeInterval.hasDerivAt_g₂_first' hc ht (hθL θ hθ)
  have hσp := hasDerivAt_node_weight (s := Icc L R) hσ hd₁ hd₂ p
  have hσp'c : ContinuousOn (fun θ => σ' θ * pw θ + σ θ * pw' θ) (Icc L R) := by
    have hσc : ContinuousOn σ (Icc L R) := fun θ hθ => (hσ θ hθ).continuousAt.continuousWithinAt
    exact (hσ'c.mul (continuousOn_pathWeight hg₁c hg₂c p)).add
      (hσc.mul (continuousOn_pathWeight' hg₁c hg₂c hg₁'c hg₂'c p))
  obtain ⟨hw0, -, -, -⟩ := node_weight_bounds (s := Icc L R) hκ₁ hκ₂ hκ₁' hκ₂' hS'.le hσ1 hσ'b hg₁ hg₂ hg₁' hg₂' p
  obtain ⟨hwα, hwβ⟩ := node_weight_coeff_pointwise (s := Icc L R) hκ₁ hκ₂ hκ₁' hκ₂' hS' hσ1 hσ'b hg₁ hg₂ hg₁' hg₂' p
  -- positivity of the centred products on `[L, R]`
  have hχbL : χb < c ^ 2 * 1 * L ^ 2 := by
    have : c ^ 2 * 1 ^ 2 * (L - h) ^ 2 ≤ c ^ 2 * 1 * L ^ 2 := by
      have : (L - h) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hLh.le (by linarith) 2
      have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ c ^ 2)
      linarith
    linarith
  have hP₁pos : ∀ θ ∈ Icc L R, 0 < (1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb) := fun θ hθ => by
    have hθ2 : L ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hL0.le hθ.1 2
    have hθ2' : 16 / 9 ≤ θ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4 / 3) (hθL θ hθ) 2
      norm_num at this; linarith
    have h1 : 0 < 1 * θ ^ 2 - 1 := by linarith
    have h2 : c ^ 2 * 1 * L ^ 2 ≤ c ^ 2 * 1 * θ ^ 2 := mul_le_mul_of_nonneg_left hθ2 (by positivity)
    have h3 : 0 < c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb := by linarith
    exact mul_pos h1 h3
  have hP₂pos : ∀ θ ∈ Icc L R, 0 < (m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb) := fun θ hθ => by
    have hθ2 : L ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hL0.le hθ.1 2
    have hθ2' : 16 / 9 ≤ θ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4 / 3) (hθL θ hθ) 2
      norm_num at this; linarith
    have h1 : 0 < m₂ ^ 2 * θ ^ 2 - 1 := by
      have := mul_le_mul_of_nonneg_left hθ2' (by positivity : (0:ℝ) ≤ m₂ ^ 2)
      linarith
    have h2 : c ^ 2 * 1 * L ^ 2 ≤ c ^ 2 * m₂ ^ 2 * θ ^ 2 := by
      have hA : c ^ 2 * 1 * L ^ 2 ≤ c ^ 2 * m₂ ^ 2 * L ^ 2 := by
        have h1' : (1:ℝ) ≤ m₂ ^ 2 := by linarith
        have : 0 ≤ c ^ 2 * L ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left h1' this
        linarith
      have hB : c ^ 2 * m₂ ^ 2 * L ^ 2 ≤ c ^ 2 * m₂ ^ 2 * θ ^ 2 := mul_le_mul_of_nonneg_left hθ2 (by positivity)
      linarith
    have h3 : 0 < c ^ 2 * m₂ ^ 2 * θ ^ 2 - χb := by linarith
    have : 0 < m₂ ^ 2 * (c ^ 2 * m₂ ^ 2 * θ ^ 2 - χb) := mul_pos (by positivity) h3
    have e : m₂ ^ 2 * (c ^ 2 * m₂ ^ 2 * θ ^ 2 - χb) = c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb := by ring
    exact mul_pos h1 (by linarith)
  -- the constants `C₁`, `C₂` (Cvs.L2a.HierarchyNodeWeight)
  have hGK : 0 ≤ G * Kp := mul_nonneg hG0 (by positivity)
  have hC₁' : ∀ θ ∈ Icc L R, ((σ' θ * pw θ + σ θ * pw' θ) * g₁ c 1 (m₂ ^ 2) θ
        + σ θ * pw θ * g₁' c 1 (m₂ ^ 2) θ) ^ 2
      * ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb)) ≤ (G * Kp) ^ 2 * C₁ :=
    fun θ hθ => sq_mul_le_of_abs_le_prod (hwα θ hθ) hGK (hP₂pos θ hθ).le (hC₁ θ hθ)
  have hC₂' : ∀ θ ∈ Icc L R, ((σ' θ * pw θ + σ θ * pw' θ) * g₂ c 1 (m₂ ^ 2) θ
        + σ θ * pw θ * g₂' c 1 (m₂ ^ 2) θ) ^ 2
      * ((1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb)) ≤ (G * Kp) ^ 2 * C₂ :=
    fun θ hθ => sq_mul_le_of_abs_le_prod (hwβ θ hθ) hGK (hP₁pos θ hθ).le (hC₂ θ hθ)
  -- the balanced `λ`s
  set lam₁ := μ₁ * χm ^ l / (χm ^ k * Kp) with hlam₁
  set lam₂ := μ₂ * χm ^ k / (χm ^ l * Kp) with hlam₂
  have hl₁ : 0 < lam₁ := by positivity
  have hl₂ : 0 < lam₂ := by positivity
  -- the node cost (Cvs.L2a.BoundaryFreeNodeCostFirst)
  have hnode := Cvs.L2a.BoundaryNodeCostFirst.node_cost_first_bd (c := c) (t := m₂ ^ 2) (L := L) (R := R) (χb := χb)
    (lam₁ := lam₁) (lam₂ := lam₂) (C₁ := (G * Kp) ^ 2 * C₁) (C₂ := (G * Kp) ^ 2 * C₂)
    hc ht hL hLR hχbL hl₁ hl₂ (σ := fun θ => σ θ * pw θ) (σ' := fun θ => σ' θ * pw θ + σ θ * pw' θ)
    (f₁ := Gk a χ ψ k) (u₁ := Gk a χ u k) (f₁p := Gk a χ ψ (k + 1))
    (f₂ := fun θ => Gk a χ ψ l (m₂ * θ)) (u₂ := fun θ => m₂ * Gk a χ u l (m₂ * θ))
    (f₂p := fun θ => Gk a χ ψ (l + 1) (m₂ * θ))
    hσp hσp'c (by simp [hσL])
    (fun θ hθ => (hsys₁ θ hθ).1) (fun θ hθ => (hsys₁ θ hθ).2) (fun θ hθ => (hsys₂ θ hθ).1) (fun θ hθ => (hsys₂ θ hθ).2)
    (hGc0 (k + 1)).continuousOn (hGc (l + 1) m₂).continuousOn hC₁' hC₂'
  -- the norms (Cvs.L2a.HierarchyLevelNorms)
  have hcont : ∀ i, ContinuousOn (ψ i) (Ici 1) := fun i => (hψc i).continuousOn
  have hL₁ : 1 ≤ 1 * L := by linarith
  have hL₂ : 1 ≤ m₂ * L := by
    have := mul_le_mul_of_nonneg_right hm₂ hL0.le
    linarith
  have hRL₂ : m₂ * L ≤ m₂ * R := mul_le_mul_of_nonneg_left hLR hm₂0.le
  have hRh₂ : m₂ * R ≤ m₂ * (R + h) := mul_le_mul_of_nonneg_left (by linarith) hm₂0.le
  have hn₁ : ∫ θ in L..R, Gk a χ ψ k θ ^ 2 ≤ 1 / 1 * (χm ^ (2 * k) * N₀) := by
    have := Cvs.L2a.HierarchyLevelNorms.level_norm_le (a := a) (m := 1) K k one_pos hL₁ hLR hχ hM hcont
      (fun i j hij t ht => hcross i j hij t (by linarith)) (fun i t ht => hmass i t (by linarith))
    simpa only [one_mul] using this
  have hn₂ : ∫ θ in L..R, Gk a χ ψ l (m₂ * θ) ^ 2 ≤ 1 / m₂ * (χm ^ (2 * l) * N₀) :=
    Cvs.L2a.HierarchyLevelNorms.level_norm_le K l hm₂0 hL₂ hLR hχ hM hcont (fun i j hij t ht => hcross i j hij t (by linarith))
      (fun i t ht => hmass i t (by linarith))
  have hV₁raw := Cvs.L2a.HierarchyLevelNorms.level_V_norm_le (c := c) (m := 1) (χb := χb) (L := L) (R := R) (h := h)
    (ε := ε) (δ := δ) (A := A₁) (B := B₁) (a := a) (χ := χ) (Mm := Mm) (χm := χm) (S := Sp) (ψ := ψ) (u := u) K k
    one_pos hh hα₁ hχb₁ hLR hε hε2 hδ hχ hM hS hψ hu hψc huc
    (fun i j hij t ht => hcross i j hij t (by linarith)) (fun i t ht => hmass i t (by linarith)) hA₁ hB₁
  have hV₂raw := Cvs.L2a.HierarchyLevelNorms.level_V_norm_le (c := c) (m := m₂) (χb := χb) (L := L) (R := R) (h := h)
    (ε := ε) (δ := δ) (A := A₂) (B := B₂) (a := a) (χ := χ) (Mm := Mm) (χm := χm) (S := Sp) (ψ := ψ) (u := u) K l
    hm₂0 hh hα₂ hχb₂ hLR hε hε2 hδ hχ hM hS hψ hu hψc huc
    (fun i j hij t ht => hcross i j hij t (by linarith)) (fun i t ht => hmass i t (by linarith)) hA₂ hB₂
  have hε' : 0 < 1 - ε / 2 := by linarith
  have eV₁ : (fun θ => Gk a χ u k θ ^ 2 / ((1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb)))
      = fun θ => (1 * Gk a χ u k (1 * θ)) ^ 2 / ((1 ^ 2 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 4 * θ ^ 2 - 1 ^ 2 * χb)) := by
    funext θ; simp only [one_mul, one_pow]
  have eV₂ : (fun θ => (m₂ * Gk a χ u l (m₂ * θ)) ^ 2 / ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb)))
      = fun θ => (m₂ * Gk a χ u l (m₂ * θ)) ^ 2 / ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb)) := by
    funext θ; ring_nf
  have hV₁ : ∫ θ in L..R, Gk a χ u k θ ^ 2 / ((1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb))
      ≤ Vc 1 ε δ A₁ B₁ Sp * (χm ^ (2 * k) * N₀) := by
    rw [eV₁]; unfold Vc; rw [div_mul_eq_mul_div, le_div_iff₀ hε']; linarith [hV₁raw]
  have hV₂ : ∫ θ in L..R, (m₂ * Gk a χ u l (m₂ * θ)) ^ 2
      / ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb))
      ≤ Vc m₂ ε δ A₂ B₂ Sp * (χm ^ (2 * l) * N₀) := by
    rw [eV₂]; unfold Vc; rw [div_mul_eq_mul_div, le_div_iff₀ hε']; linarith [hV₂raw]
  -- the children are the nodes of the extended paths
  have hchild₁ : ∫ θ in L..R, σ θ * pw θ * g₁ c 1 (m₂ ^ 2) θ * (Gk a χ ψ k θ * Gk a χ ψ (l + 1) (m₂ * θ))
      = nodeFirst c m₂ L R σ a χ ψ (p ++ [true]) := by
    unfold nodeFirst
    rw [lfalse_append_true, ktrue_append_true]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ _ => ?_)
    rw [pathWeight_append]; simp only [hpw, ite_true]; ring
  have hchild₂ : ∫ θ in L..R, σ θ * pw θ * g₂ c 1 (m₂ ^ 2) θ * (Gk a χ ψ (k + 1) θ * Gk a χ ψ l (m₂ * θ))
      = nodeFirst c m₂ L R σ a χ ψ (p ++ [false]) := by
    unfold nodeFirst
    rw [lfalse_append_false, ktrue_append_false]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ _ => ?_)
    rw [pathWeight_append]; simp only [hpw, Bool.false_eq_true, ite_false]; ring
  have e0 : nodeFirst c m₂ L R σ a χ ψ p = ∫ θ in L..R, σ θ * pw θ * (Gk a χ ψ k θ * Gk a χ ψ l (m₂ * θ)) := rfl
  rw [e0]
  rw [hchild₁, hchild₂] at hnode
  -- the algebra of the four cost terms
  have hT₁ : lam₁ * ((G * Kp) ^ 2 * C₁) / 2 * (∫ θ in L..R, Gk a χ ψ k θ ^ 2)
      ≤ μ₁ / 2 * G ^ 2 * C₁ / 1 * (Kp * χm ^ (l + k) * N₀) := by
    have hC₁0 : 0 ≤ (G * Kp) ^ 2 * C₁ := by
      have := hC₁ L ⟨le_rfl, hLR⟩
      exact mul_nonneg (sq_nonneg _) (le_trans (mul_nonneg (sq_nonneg _) (hP₂pos L ⟨le_rfl, hLR⟩).le) this)
    calc _ ≤ lam₁ * ((G * Kp) ^ 2 * C₁) / 2 * (1 / 1 * (χm ^ (2 * k) * N₀)) := by gcongr
      _ = _ := by rw [hlam₁]; field_simp; ring
  have hT₂ : 1 / (2 * lam₁) * (∫ θ in L..R, (m₂ * Gk a χ u l (m₂ * θ)) ^ 2
        / ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb)))
      ≤ Vc m₂ ε δ A₂ B₂ Sp / (2 * μ₁) * (Kp * χm ^ (l + k) * N₀) := by
    calc _ ≤ 1 / (2 * lam₁) * (Vc m₂ ε δ A₂ B₂ Sp * (χm ^ (2 * l) * N₀)) := by gcongr
      _ = _ := by rw [hlam₁]; field_simp; ring
  have hT₃ : lam₂ * ((G * Kp) ^ 2 * C₂) / 2 * (∫ θ in L..R, Gk a χ ψ l (m₂ * θ) ^ 2)
      ≤ μ₂ / 2 * G ^ 2 * C₂ / m₂ * (Kp * χm ^ (l + k) * N₀) := by
    have hC₂0 : 0 ≤ (G * Kp) ^ 2 * C₂ := by
      have := hC₂ L ⟨le_rfl, hLR⟩
      exact mul_nonneg (sq_nonneg _) (le_trans (mul_nonneg (sq_nonneg _) (hP₁pos L ⟨le_rfl, hLR⟩).le) this)
    calc _ ≤ lam₂ * ((G * Kp) ^ 2 * C₂) / 2 * (1 / m₂ * (χm ^ (2 * l) * N₀)) := by gcongr
      _ = _ := by rw [hlam₂]; field_simp; ring
  have hT₄ : 1 / (2 * lam₂) * (∫ θ in L..R, Gk a χ u k θ ^ 2 / ((1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb)))
      ≤ Vc 1 ε δ A₁ B₁ Sp / (2 * μ₂) * (Kp * χm ^ (l + k) * N₀) := by
    calc _ ≤ 1 / (2 * lam₂) * (Vc 1 ε δ A₁ B₁ Sp * (χm ^ (2 * k) * N₀)) := by gcongr
      _ = _ := by rw [hlam₂]; field_simp; ring
  have eE : Ecost 1 m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc 1 ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) k l
        * (κ₁ ^ l * κ₂ ^ k * χm ^ (l + k) * N₀)
      = μ₁ / 2 * G ^ 2 * C₁ / 1 * (Kp * χm ^ (l + k) * N₀)
        + Vc m₂ ε δ A₂ B₂ Sp / (2 * μ₁) * (Kp * χm ^ (l + k) * N₀)
        + (μ₂ / 2 * G ^ 2 * C₂ / m₂ * (Kp * χm ^ (l + k) * N₀)
          + Vc 1 ε δ A₁ B₁ Sp / (2 * μ₂) * (Kp * χm ^ (l + k) * N₀)) := by
    unfold Ecost; rw [hKp, hG]; ring
  -- the boundary term at `R`
  have hbd : |σ R * pw R * g₁ c 1 (m₂ ^ 2) R * (Gk a χ ψ k R * (m₂ * Gk a χ u l (m₂ * R)))
      - σ R * pw R * g₂ c 1 (m₂ ^ 2) R * (Gk a χ u k R * Gk a χ ψ l (m₂ * R))|
      ≤ Kp * χm ^ (l + k) * Bc a ψ u m₂ R κ₁R κ₂R := by
    have hR : R ∈ Icc L R := ⟨hLR, le_rfl⟩
    have h0 : |σ R| * |pw R| ≤ Kp := by rw [← abs_mul]; exact hw0 R hR
    have hGk := abs_Gk_le (a := a) (f := ψ) (ξ := R) hχ k
    have hGl := abs_Gk_le (a := a) (f := ψ) (ξ := m₂ * R) hχ l
    have hUk := abs_Gk_le (a := a) (f := u) (ξ := R) hχ k
    have hUl := abs_Gk_le (a := a) (f := u) (ξ := m₂ * R) hχ l
    have hg1 := hg₁R
    have hg2 := hg₂R
    have hκ₁R : 0 ≤ κ₁R := (abs_nonneg _).trans hg₁R
    have hκ₂R : 0 ≤ κ₂R := (abs_nonneg _).trans hg₂R
    have hP1 := Pabs_nonneg a ψ R; have hP2 := Pabs_nonneg a u (m₂ * R)
    have hP3 := Pabs_nonneg a u R; have hP4 := Pabs_nonneg a ψ (m₂ * R)
    have h1 : |σ R * pw R * g₁ c 1 (m₂ ^ 2) R * (Gk a χ ψ k R * (m₂ * Gk a χ u l (m₂ * R)))|
        ≤ Kp * κ₁R * (χm ^ k * Pabs a ψ R * (m₂ * (χm ^ l * Pabs a u (m₂ * R)))) := by
      simp only [abs_mul, abs_of_pos hm₂0]
      gcongr
    have h2 : |σ R * pw R * g₂ c 1 (m₂ ^ 2) R * (Gk a χ u k R * Gk a χ ψ l (m₂ * R))|
        ≤ Kp * κ₂R * (χm ^ k * Pabs a u R * (χm ^ l * Pabs a ψ (m₂ * R))) := by
      simp only [abs_mul]
      gcongr
    refine (abs_sub _ _).trans (le_trans (add_le_add h1 h2) (le_of_eq ?_))
    unfold Bc; rw [pow_add]; ring
  rw [eE]
  have eK : κ₁ ^ l * κ₂ ^ k * χm ^ (l + k) * Bc a ψ u m₂ R κ₁R κ₂R = Kp * χm ^ (l + k) * Bc a ψ u m₂ R κ₁R κ₂R := by
    rw [hKp]
  rw [eK]
  linarith [hnode, hT₁, hT₂, hT₃, hT₄, hbd]

set_option maxHeartbeats 800000 in
/-- **The tree bound of a pair `(1, k)` with its boundary at `R`**: for every depth `N`,
`|∫ σ G(θ) G(m₂θ)| ≤ (Σ_{j<N} ρ^j (E(j) + B_c/N₀) + ρ^N (1 + 1/m₂)/2) N₀`, `ρ = m₂²κ₁χ + κ₂χ`. -/
theorem pair_tree_bound_first_bd {c m₂ L R χb χm Sp h ε δ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' A₁ B₁ A₂ B₂ C₁ C₂ : ℝ}
    {a χ Mm : ι → ℝ} {ψ u : ι → ℝ → ℝ} (K : ι → ι → ℝ) {σ σ' : ℝ → ℝ}
    (hc : 0 < c) (hm₂ : 2 ≤ m₂) (hL : 4 / 3 ≤ L) (hLR : L ≤ R) (hh : 0 < h)
    (hα₁ : 1 < 1 * (L - h)) (hχb₁ : χb < c ^ 2 * 1 ^ 2 * (L - h) ^ 2)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hχm : 0 < χm) (hM : ∀ i, 0 ≤ Mm i) (hS : ∀ i, |χ i - χb| ≤ Sp)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hψ : ∀ i, ∀ ξ, 1 < ξ → HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hψc : ∀ i, Continuous (ψ i)) (huc : ∀ i, Continuous (u i))
    (hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hσ : ∀ θ ∈ Icc L R, HasDerivAt σ (σ' θ) θ) (hσ'c : ContinuousOn σ' (Icc L R)) (hσL : σ L = 0)
    (hσ1 : ∀ θ ∈ Icc L R, |σ θ| ≤ 1) (hσ'b : ∀ θ ∈ Icc L R, |σ' θ| ≤ S') (hS' : 0 < S')
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hκ₁' : 0 ≤ κ₁') (hκ₂' : 0 ≤ κ₂')
    (hg₁ : ∀ θ ∈ Icc L R, |g₁ c 1 (m₂ ^ 2) θ| ≤ κ₁) (hg₂ : ∀ θ ∈ Icc L R, |g₂ c 1 (m₂ ^ 2) θ| ≤ κ₂)
    (hg₁' : ∀ θ ∈ Icc L R, |g₁' c 1 (m₂ ^ 2) θ| ≤ κ₁') (hg₂' : ∀ θ ∈ Icc L R, |g₂' c 1 (m₂ ^ 2) θ| ≤ κ₂')
    {κ₁R κ₂R : ℝ} (hg₁R : |g₁ c 1 (m₂ ^ 2) R| ≤ κ₁R) (hg₂R : |g₂ c 1 (m₂ ^ 2) R| ≤ κ₂R)
    (hA₁ : ∀ θ ∈ Icc (L - h) (R + h), 2 * (1 ^ 2 * θ ^ 2 - 1)
      * ((Real.pi / h) ^ 2 / (c ^ 2 * 1 ^ 4 * θ ^ 2 - 1 ^ 2 * χb)
        + (2 * c ^ 2 * 1 ^ 4 * θ) ^ 2 / (c ^ 2 * 1 ^ 4 * θ ^ 2 - 1 ^ 2 * χb) ^ 3) ≤ A₁)
    (hB₁ : ∀ θ ∈ Icc (L - h) (R + h), 1 / (c ^ 2 * 1 ^ 4 * θ ^ 2 - 1 ^ 2 * χb) ^ 2 ≤ B₁)
    (hA₂ : ∀ θ ∈ Icc (L - h) (R + h), 2 * (m₂ ^ 2 * θ ^ 2 - 1)
      * ((Real.pi / h) ^ 2 / (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb)
        + (2 * c ^ 2 * m₂ ^ 4 * θ) ^ 2 / (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb) ^ 3) ≤ A₂)
    (hB₂ : ∀ θ ∈ Icc (L - h) (R + h), 1 / (c ^ 2 * m₂ ^ 4 * θ ^ 2 - m₂ ^ 2 * χb) ^ 2 ≤ B₂)
    (hC₁ : ∀ θ ∈ Icc L R, (S' * |g₁ c 1 (m₂ ^ 2) θ| + |g₁' c 1 (m₂ ^ 2) θ|) ^ 2
      * ((m₂ ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m₂ ^ 2) ^ 2 * θ ^ 2 - m₂ ^ 2 * χb)) ≤ C₁)
    (hC₂ : ∀ θ ∈ Icc L R, (S' * |g₂ c 1 (m₂ ^ 2) θ| + |g₂' c 1 (m₂ ^ 2) θ|) ^ 2
      * ((1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb)) ≤ C₂)
    (hN₀ : 0 < ∑ i, a i ^ 2 * Mm i) (hC₁m : 0 ≤ C₁) (hC₂m : 0 ≤ C₂) (N : ℕ) :
    |nodeFirst c m₂ L R σ a χ ψ []|
      ≤ ((∑ j ∈ range N, (m₂ ^ 2 * κ₁ * χm + 1 * κ₂ * χm) ^ j
            * (Ecost 1 m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc 1 ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) j j
              + Bc a ψ u m₂ R κ₁R κ₂R / ∑ i, a i ^ 2 * Mm i))
          + (m₂ ^ 2 * κ₁ * χm + 1 * κ₂ * χm) ^ N * ((1 / 1 + 1 / m₂) / 2)) * ∑ i, a i ^ 2 * Mm i := by
  have hm₂0 : 0 < m₂ := by linarith
  have hσc : ContinuousOn σ (Icc L R) := fun θ hθ => (hσ θ hθ).continuousAt.continuousWithinAt
  set N₀ := ∑ i, a i ^ 2 * Mm i with hN₀def
  set D : List Bool → ℝ := fun p => κ₁ ^ ktrue p * κ₂ ^ lfalse p * χm ^ p.length * N₀ with hD
  have hDpos : ∀ p, 0 < D p := fun p => by simp only [hD]; positivity
  set x : List Bool → ℝ := fun p => |nodeFirst c m₂ L R σ a χ ψ p| / D p with hx
  have hnorm : ∀ p : List Bool, κ₁ ^ ktrue p * κ₂ ^ lfalse p * χm ^ (ktrue p + lfalse p) * N₀ = D p := fun p => by
    simp only [hD]; rw [ktrue_add_lfalse]
  have hDT : ∀ p : List Bool, D (p ++ [true]) = κ₁ * χm * D p := fun p => by
    simp only [hD]
    rw [ktrue_append_true, lfalse_append_true, List.length_append, List.length_singleton, pow_succ, pow_succ]; ring
  have hDF : ∀ p : List Bool, D (p ++ [false]) = κ₂ * χm * D p := fun p => by
    simp only [hD]
    rw [ktrue_append_false, lfalse_append_false, List.length_append, List.length_singleton, pow_succ, pow_succ]; ring
  have hstep : ∀ p : List Bool, p.length < N →
      x p ≤ (Ecost 1 m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc 1 ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) p.length p.length
          + Bc a ψ u m₂ R κ₁R κ₂R / N₀)
        + (m₂ ^ 2 * κ₁ * χm) * x (p ++ [true]) + (1 * κ₂ * χm) * x (p ++ [false]) := fun p _ => by
    have hs := node_step_first_bd (a := a) K p hc hm₂ hL hLR hh hα₁ hχb₁ hχ hχm hM hS hε hε2 hδ hμ₁ hμ₂ hψ hu hψc huc
      hcross hmass hσ hσ'c hσL hσ1 hσ'b hS' hκ₁ hκ₂ hκ₁' hκ₂' hg₁ hg₂ hg₁' hg₂' hg₁R hg₂R hA₁ hB₁ hA₂ hB₂ hC₁ hC₂
    have hkl := ktrue_add_lfalse p
    have hmono := Ecost_mono (m₁ := 1) (V₁ := Vc 1 ε δ A₁ B₁ Sp) (V₂ := Vc m₂ ε δ A₂ B₂ Sp) one_pos hm₂0 hμ₁ hμ₂ hS'
      hκ₁ hκ₂ hκ₁' hκ₂' hC₁m hC₂m (k := lfalse p) (l := ktrue p) (n := p.length) (by omega) (by omega)
    rw [hnorm p] at hs
    have e3 : κ₁ ^ ktrue p * κ₂ ^ lfalse p * χm ^ (ktrue p + lfalse p) * Bc a ψ u m₂ R κ₁R κ₂R
        = Bc a ψ u m₂ R κ₁R κ₂R / N₀ * D p := by
      rw [← hnorm p]; field_simp
    rw [e3] at hs
    simp only [hx]
    rw [div_le_iff₀ (hDpos p)]
    have hDp := (hDpos p).ne'
    have hDT' := (hDpos (p ++ [true])).ne'
    have hDF' := (hDpos (p ++ [false])).ne'
    have e1 : m₂ ^ 2 * κ₁ * χm * (|nodeFirst c m₂ L R σ a χ ψ (p ++ [true])| / D (p ++ [true])) * D p
        = m₂ ^ 2 * |nodeFirst c m₂ L R σ a χ ψ (p ++ [true])| := by
      rw [hDT]; field_simp
    have e2 : 1 * κ₂ * χm * (|nodeFirst c m₂ L R σ a χ ψ (p ++ [false])| / D (p ++ [false])) * D p
        = 1 * |nodeFirst c m₂ L R σ a χ ψ (p ++ [false])| := by
      rw [hDF]; field_simp
    calc |nodeFirst c m₂ L R σ a χ ψ p| ≤ _ := hs
      _ ≤ Ecost 1 m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc 1 ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) p.length p.length * D p
          + Bc a ψ u m₂ R κ₁R κ₂R / N₀ * D p
          + m₂ ^ 2 * |nodeFirst c m₂ L R σ a χ ψ (p ++ [true])| + 1 * |nodeFirst c m₂ L R σ a χ ψ (p ++ [false])| := by
          gcongr
      _ = _ := by rw [add_mul, add_mul, add_mul, e1, e2]
  have hleaf : ∀ p : List Bool, p.length = N → x p ≤ (1 / 1 + 1 / m₂) / 2 := fun p _ => by
    have h := node_leaf_first (a := a) K p hc hm₂ hL hLR hχ hχm hM hψc hcross hmass hσc hσ1 hκ₁ hκ₂ hg₁ hg₂
    rw [hnorm p] at h
    simp only [hx]
    rw [div_le_iff₀ (hDpos p)]
    exact h
  have htree := Cvs.Upstream.BinaryTreeDepthSum.tree_sum_depth (x := x)
    (E := fun j => Ecost 1 m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ (Vc 1 ε δ A₁ B₁ Sp) (Vc m₂ ε δ A₂ B₂ Sp) j j
      + Bc a ψ u m₂ R κ₁R κ₂R / N₀)
    (ρ₁ := m₂ ^ 2 * κ₁ * χm) (ρ₂ := 1 * κ₂ * χm) (X := (1 / 1 + 1 / m₂) / 2) (by positivity) (by positivity) N
    hstep hleaf
  have hD0 : D [] = N₀ := by simp [hD, ktrue, lfalse]
  simp only [hx, hD0] at htree
  rwa [div_le_iff₀ hN₀] at htree

end Cvs.L2a.TreeBoundFirstPairBoundary
