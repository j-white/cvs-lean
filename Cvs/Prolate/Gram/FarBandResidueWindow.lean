import Mathlib
import Cvs.Prolate.Gram.FarTwistResidue
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.TwoCutFromTwistedPair
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.PencilLayerBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The far out-of-band residue is the window remainder

If `Cv` vanishes below `k₀` then `vᵀCv ≤ |v_A|²`, and `1 − λ_j ≤ μ_j` since `1 − λ_t ≤ ½`. Theorem A with `μ`
frozen at `k₀ − 1` bounds `Σ_{j<k₀}(1 − λ_j)v_j²` by `R(k₀)·|v_A|²`, `R(k₀) = Σ_{k<k₀} δ_k/F_k` (EF′'s remainder).
So (EF′) at `T₀`, which the deep and band cell floors give at every `T₀ < 1`, makes `FarBandRes x k₀ ρ` hold
eventually at the first rung of `{T ≥ T₀}` for every `ρ > 0`.
-/

noncomputable section

open Real Filter Matrix Finset Topology

namespace Cvs.Prolate.Gram.FarBandResidueWindow
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram lam lamTop levT mu muInc)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (floorC)

/-- A symmetric positive semidefinite form does not grow under restriction to `{j ≥ k}` when `Mv` vanishes
below `k`: `vᵀMv ≤ uᵀMu` with `u = v·1_{j ≥ k}`. -/
theorem quad_le_quad_restrict {ι : Type*} [Fintype ι] [LinearOrder ι] {M : Matrix ι ι ℝ} (hM : M.PosSemidef)
    {k : ι} {v : ι → ℝ} (hv : ∀ j, ¬ k ≤ j → (M *ᵥ v) j = 0) :
    v ⬝ᵥ (M *ᵥ v) ≤ (fun j => if k ≤ j then v j else 0) ⬝ᵥ (M *ᵥ fun j => if k ≤ j then v j else 0) := by
  set u : ι → ℝ := fun j => if k ≤ j then v j else 0
  set w : ι → ℝ := fun j => if k ≤ j then 0 else v j
  have hvw : v = u + w := by ext j; simp only [u, w, Pi.add_apply]; split_ifs <;> simp
  have hw0 : w ⬝ᵥ (M *ᵥ v) = 0 := Finset.sum_eq_zero fun j _ => by
    simp only [w]; split_ifs with h
    · simp
    · simp [hv j h]
  have hsym : u ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ u) := by
    have hT : Mᵀ = M := by
      have h := hM.isHermitian
      rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have hww : 0 ≤ w ⬝ᵥ (M *ᵥ w) := by simpa using hM.dotProduct_mulVec_nonneg w
  have e1 : v ⬝ᵥ (M *ᵥ v) = u ⬝ᵥ (M *ᵥ u) + u ⬝ᵥ (M *ᵥ w) := by
    have : v ⬝ᵥ (M *ᵥ v) = u ⬝ᵥ (M *ᵥ v) + w ⬝ᵥ (M *ᵥ v) := by rw [hvw, add_dotProduct]
    rw [this, hw0, add_zero, hvw, mulVec_add, dotProduct_add]
  have e2 : w ⬝ᵥ (M *ᵥ u) + w ⬝ᵥ (M *ᵥ w) = 0 := by rw [← dotProduct_add, ← mulVec_add, ← hvw, hw0]
  linarith

/-- The out-of-band weight of a rung is at most its window weight: `1 − λ_j ≤ μ_j`. -/
theorem one_sub_lam_le_mu {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : 1 - lam x j ≤ mu x j := by
  have hl0 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_nonneg x j
  have hl1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx j.2
  have ht1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop_lt_one hx
  have ht2 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx
  have hs0 := Real.sqrt_nonneg (lam x j)
  have hs1 : √(lam x j) ≤ 1 := Real.sqrt_le_one.2 hl1
  have hd0 : 0 < (1 - lamTop x) * (1 + √(lam x j)) ^ 2 := by
    have : 0 < 1 - lamTop x := by linarith
    positivity
  have hd2 : (1 - lamTop x) * (1 + √(lam x j)) ^ 2 ≤ 2 := by
    have h4 : (1 + √(lam x j)) ^ 2 ≤ 4 := by nlinarith
    nlinarith
  unfold mu
  rw [le_div_iff₀ hd0]
  nlinarith

/-- `FarBandRes` is monotone in the residue. -/
theorem FarBandRes.mono {x : ℕ} {k : Fin x} {ρ ρ' : ℝ} (h : Cvs.Prolate.Gram.FarTwistResidue.FarBandRes x k ρ) (hρ : ρ ≤ ρ') :
    Cvs.Prolate.Gram.FarTwistResidue.FarBandRes x k ρ' := fun v hv =>
  (h v hv).trans (mul_le_mul_of_nonneg_right hρ (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- **The far out-of-band residue is the window remainder**: at `80 ≤ 2πx`, every cut `k₀` has
`FarBandRes x k₀ (Σ_{k<k₀} δ_k/F_k)`. -/
theorem farBandRes_window {x : ℕ} (hx : 80 ≤ 2 * π * x) (k₀ : Fin x) :
    Cvs.Prolate.Gram.FarTwistResidue.FarBandRes x k₀ (∑ k ∈ univ.filter (· < k₀), muInc x k / floorC x k) := by
  intro v hv
  have hC := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_posDef hx
  set δ : Fin x → ℝ := fun k => if k < k₀ then muInc x k else 0
  have hδ : ∀ k, 0 ≤ δ k := fun k => by
    simp only [δ]; split_ifs
    · exact Cvs.Prolate.Gram.ProlateCellGramHalfUnit.muInc_nonneg hx k.2
    · exact le_rfl
  have hA := Cvs.Upstream.PencilLayerBound.sum_le_layer hC hδ (μ := fun j => ∑ k ∈ univ.filter (· ≤ j), δ k) (fun _ => rfl)
    (Cvs.Upstream.PencilLayerBound.layerFloor_pos hC) (Cvs.Upstream.PencilLayerBound.isFloor_layerFloor hC) v
  have hR : ∑ k, δ k / Cvs.Upstream.PencilLayerBound.layerFloor hC k = ∑ k ∈ univ.filter (· < k₀), muInc x k / floorC x k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [δ, Cvs.Route.Visibility.LayerFloorDeepRemainderB.floorC_eq hx]; split_ifs <;> simp
  rw [hR] at hA
  have hR0 : 0 ≤ ∑ k ∈ univ.filter (· < k₀), muInc x k / floorC x k :=
    Finset.sum_nonneg fun k _ => div_nonneg (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.muInc_nonneg hx k.2) (Cvs.Route.Visibility.LayerFloorDeepRemainderB.floorC_nonneg x k)
  have hF : ∀ j : Fin x, ¬ k₀ ≤ j → ∑ k ∈ univ.filter (· ≤ j), δ k = mu x j := fun j hj => by
    rw [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_eq_sum x j]
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k < k₀ := lt_of_le_of_lt (Finset.mem_filter.1 hk).2 (not_le.1 hj)
    simp [δ, this]
  have hq : v ⬝ᵥ (cellGram x *ᵥ v) ≤ ∑ j ∈ univ.filter (k₀ ≤ ·), v j ^ 2 := by
    refine (quad_le_quad_restrict hC.posSemidef hv).trans ((Cvs.Prolate.Gram.TwoCutFromTwistedPair.quad_cellGram_le hx _).trans_eq ?_)
    simp only [dotProduct, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  calc ∑ j ∈ univ.filter (fun j => ¬ k₀ ≤ j), (1 - lam x j) * v j ^ 2
      ≤ ∑ j ∈ univ.filter (fun j => ¬ k₀ ≤ j), (∑ k ∈ univ.filter (· ≤ j), δ k) * v j ^ 2 :=
        Finset.sum_le_sum fun j hj => by
          rw [hF j (Finset.mem_filter.1 hj).2]
          exact mul_le_mul_of_nonneg_right (one_sub_lam_le_mu hx j) (sq_nonneg _)
    _ ≤ ∑ j, (∑ k ∈ univ.filter (· ≤ j), δ k) * v j ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
          mul_nonneg (Finset.sum_nonneg fun k _ => hδ k) (sq_nonneg _)
    _ ≤ _ := hA
    _ ≤ _ := mul_le_mul_of_nonneg_left hq hR0

/-- **The far residue from (EF′)**: (EF′) at `T₀` and `ρ > 0` give, eventually, `FarBandRes x k₀ ρ` at every
first rung `k₀` of `{T ≥ T₀}`. -/
theorem farBandRes_of_efprime {T₀ ρ : ℝ} (hE : Cvs.Route.Visibility.LayerFloorDeepRemainderB.EFprime T₀) (hρ : 0 < ρ) :
    ∀ᶠ x : ℕ in atTop, ∀ k₀ : Fin x, T₀ ≤ levT x k₀ → (∀ j < k₀, levT x j < T₀) → Cvs.Prolate.Gram.FarTwistResidue.FarBandRes x k₀ ρ := by
  filter_upwards [hE.eventually (gt_mem_nhds hρ), Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hlt hx k₀ h1 h2
  refine FarBandRes.mono (farBandRes_window hx k₀) ?_
  rw [Cvs.Route.Visibility.LayerFloorDeepRemainderB.filter_lt_eq hx h1 h2]
  exact hlt.le

end Cvs.Prolate.Gram.FarBandResidueWindow
