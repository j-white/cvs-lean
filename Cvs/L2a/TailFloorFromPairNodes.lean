import Mathlib
import Cvs.L2a.CutoffCrossTermsAsNodes
import Cvs.L2a.CutoffTailFloor
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
# The tail floor from bounds on the pair nodes

Given `|node c m m' (19/20) (3/2) σ []| ≤ N₀ T(m, m')` for `2 ≤ m < m' ≤ M` and
`|nodeFirst c m (4/3) b η []| ≤ N₀ T₁(m)` for `2 ≤ m ≤ M`, the floor of Cvs.L2a.CutoffTailFloor for `G = G_0` reads
`∫₁ᵇ (G + T₂)² ≥ ∫₁ᵇ G² − s∫ (1 − η)²G² − (1/s)[(5/6)∫_{19/10}^{3M/2} G² + N₀ Σ_{m≠m'} T(m, m')] − 2N₀ Σ_m T₁(m)`,
the nodes of the swapped pairs being equal (`node_nil_symm`).
-/

namespace Cvs.L2a.TailFloorFromPairNodes

open Real Set Finset intervalIntegral Cvs.L2a.RungChiHierarchy Cvs.L2a.TreeStepModePair Cvs.L2a.TreeStepFirstPair Cvs.L2a.CutoffCrossTermsAsNodes

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The node of the empty path is symmetric in the pair. -/
theorem node_nil_symm (c m₁ m₂ L R : ℝ) (σ : ℝ → ℝ) (a χ : ι → ℝ) (ψ : ι → ℝ → ℝ) :
    node c m₁ m₂ L R σ a χ ψ [] = node c m₂ m₁ L R σ a χ ψ [] := by
  rw [node_nil, node_nil]
  congr 1; funext θ; ring

/-- The symmetric extension of a bound on the pairs `m < m'`. -/
noncomputable def Tsym (T : ℕ → ℕ → ℝ) (m m' : ℕ) : ℝ := if m < m' then T m m' else T m' m

/-- **The tail floor from bounds on the pair nodes.** -/
theorem floor_of_pair_bounds {c θ₀ b s : ℝ} {M : ℕ} {a χ : ι → ℝ} {ψ : ι → ℝ → ℝ} {η σ : ℝ → ℝ} {N₀ : ℝ}
    {T : ℕ → ℕ → ℝ} {T₁ : ℕ → ℝ}
    (hM : 2 ≤ M) (h1 : 4 / 3 ≤ θ₀) (hθ₀ : θ₀ ≤ 3 / 2) (hb : θ₀ ≤ b) (hs : 0 < s) (hN₀ : 0 ≤ N₀)
    (hψc : ∀ i, Continuous (ψ i))
    (hηc : Continuous η) (hη0 : ∀ θ ∈ Icc (1 : ℝ) (4 / 3), η θ = 0) (hη1 : ∀ θ ∈ Icc θ₀ b, η θ = 1)
    (hσc : Continuous σ) (hσnn : ∀ θ, 0 ≤ σ θ) (hσ1 : ∀ θ, σ θ ≤ 1) (hσp : ∀ θ ∈ Icc 1 θ₀, σ θ = 1)
    (hσ0 : ∀ θ, θ ≤ 19 / 20 ∨ 3 / 2 ≤ θ → σ θ = 0)
    (hT : ∀ m m' : ℕ, 2 ≤ m → m < m' → m' ≤ M →
      |node c (m : ℝ) (m' : ℝ) (19 / 20) (3 / 2) σ a χ ψ []| ≤ N₀ * T m m')
    (hT₁ : ∀ m : ℕ, 2 ≤ m → m ≤ M → |nodeFirst c (m : ℝ) (4 / 3) b η a χ ψ []| ≤ N₀ * T₁ m) :
    (∫ θ in (1 : ℝ)..b, Gk a χ ψ 0 θ ^ 2) - s * (∫ θ in (1 : ℝ)..b, (1 - η θ) ^ 2 * Gk a χ ψ 0 θ ^ 2)
        - 1 / s * (5 / 6 * (∫ u in (19 / 10 : ℝ)..(3 * M / 2), Gk a χ ψ 0 u ^ 2)
            + N₀ * ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M, (if m = m' then 0 else Tsym T m m'))
        - 2 * (N₀ * ∑ m ∈ Finset.Icc 2 M, T₁ m)
      ≤ ∫ θ in (1 : ℝ)..b, (Gk a χ ψ 0 θ + ∑ m ∈ Finset.Icc 2 M, Gk a χ ψ 0 (m * θ)) ^ 2 := by
  have hGc : Continuous (Gk a χ ψ 0) := by
    unfold Gk; exact continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have h1' : 1 ≤ θ₀ := by linarith
  have hfloor := Cvs.L2a.CutoffTailFloor.tail_floor_cutoff (G := Gk a χ ψ 0) (η := η) (σ := σ) hM h1' hθ₀ hb hs hGc hηc
    hη1 hσc hσnn hσ1 hσp hσ0
  -- the mode pairs, from above
  have hpairs : ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
          (if m = m' then 0 else ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (Gk a χ ψ 0 (m * θ) * Gk a χ ψ 0 (m' * θ)))
      ≤ N₀ * ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M, (if m = m' then 0 else Tsym T m m') := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro m' hm'
    rw [Finset.mem_Icc] at hm hm'
    split_ifs with hmm
    · simp
    · rw [cross_eq_node c m m']
      have hb' : |node c (m : ℝ) (m' : ℝ) (19 / 20) (3 / 2) σ a χ ψ []| ≤ N₀ * Tsym T m m' := by
        unfold Tsym
        rcases lt_or_gt_of_ne hmm with hlt | hgt
        · rw [if_pos hlt]; exact hT m m' hm.1 hlt hm'.2
        · rw [if_neg (not_lt.mpr hgt.le), node_nil_symm]; exact hT m' m hm'.1 hgt hm.2
      exact (le_abs_self _).trans hb'
  -- the first-mode pairs
  have hfirst : -(N₀ * ∑ m ∈ Finset.Icc 2 M, T₁ m)
      ≤ ∑ m ∈ Finset.Icc 2 M, ∫ θ in (1 : ℝ)..b, η θ * (Gk a χ ψ 0 θ * Gk a χ ψ 0 (m * θ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum; intro m hm
    rw [Finset.mem_Icc] at hm
    rw [first_eq_nodeFirst c m (by linarith) hηc hη0 a χ ψ hψc]
    linarith [neg_abs_le (nodeFirst c (m : ℝ) (4 / 3) b η a χ ψ []), hT₁ m hm.1 hm.2]
  have hs' : 0 < 1 / s := by positivity
  have h3 := mul_le_mul_of_nonneg_left hpairs hs'.le
  linarith [hfloor, hfirst, h3]

end Cvs.L2a.TailFloorFromPairNodes
