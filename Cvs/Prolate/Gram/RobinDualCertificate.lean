import Mathlib
import Cvs.Prolate.Gram.WindowFloorMinNormInterp
import Cvs.Upstream.CellFloorSandwichPosDef

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Robin dual certificate: `σ'_j ≥ a² (r_*/g_*)² / Σ_S (r_k/g_k)²`

A vector `v ⊥ u_b` (`b ≠ j`) gives `⟨v, u_j⟩² ≤ ‖v‖² σ'_j`. With orthonormal `ψ_k` (`k ∈ S`) pairing as
`⟨ψ_k, u_b⟩ = n_b g_k/(χ_b − σ_k)` off the reference node `k_*` (where `σ_{k_*} = χ_j` and `⟨ψ_{k_*}, u_j⟩ = a`),
any `Q` of degree `< |S|` vanishing at `χ_b`, `b ≠ j`, gives the row `v = Σ_S (r_k/g_k)ψ_k`, `r_k = Q(σ_k)w_k`
(`w_k` the nodal weight), hence `σ'_j ≥ a²/Σ_S ρ_k` with `ρ_k = ((r_k g_*)/(r_* g_k))²`.
-/

noncomputable section

open Matrix Polynomial Finset

namespace Cvs.Prolate.Gram.RobinDualCertificate
open Cvs.ZeroCounting

open Cvs.Upstream.CellFloorSandwichPosDef (sigmaP)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Distance from a dual vector**: if `v ⊥ u_b` for every `b ≠ j`, then `⟨v, u_j⟩² ≤ ‖v‖² σ'_j`. -/
theorem sq_inner_le_sigmaP (u : ι → E) (hM : (gram ℝ u).PosDef) (j : ι) (v : E)
    (hv : ∀ b, b ≠ j → inner ℝ v (u b) = 0) :
    inner ℝ v (u j) ^ 2 ≤ ‖v‖ ^ 2 * sigmaP (gram ℝ u) j := by
  obtain ⟨⟨b, hbj, hq⟩, -⟩ := Cvs.Upstream.CellFloorSandwichPosDef.isLeast_sigmaP hM j
  rw [← hq, Cvs.Upstream.CellFloorSandwichPosDef.quad_gram]
  have hin : inner ℝ v (∑ i, b i • u i) = inner ℝ v (u j) := by
    rw [inner_sum, Finset.sum_eq_single j (fun i _ hi => by rw [inner_smul_right, hv i hi, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), inner_smul_right, hbj, one_mul]
  rw [← hin, ← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2 |>.trans' (by rw [sq_abs])

/-- The residue `r_k = Q(σ_k) ∏_{l ∈ S, l ≠ k}(σ_k − σ_l)⁻¹` of `Q/∏_S(z − σ_l)` at `σ_k`. -/
def resid {κ : Type*} [DecidableEq κ] (S : Finset κ) (σ : κ → ℝ) (Q : ℝ[X]) (k : κ) : ℝ :=
  Q.eval (σ k) * Lagrange.nodalWeight S σ k

/-- **Residue sum**: for `deg Q < |S|` and `z` off the nodes, `Σ_S r_k/(z − σ_k) = Q(z)/∏_S(z − σ_k)`. -/
theorem sum_resid_div {κ : Type*} [DecidableEq κ] {S : Finset κ} {σ : κ → ℝ} (hσ : Set.InjOn σ S) {Q : ℝ[X]}
    (hQ : Q.degree < S.card) {z : ℝ} (hz : ∀ k ∈ S, z ≠ σ k) :
    ∑ k ∈ S, resid S σ Q k / (z - σ k) = Q.eval z / ∏ k ∈ S, (z - σ k) :=
  (Cvs.Prolate.Gram.WindowFloorMinNormInterp.eval_div_prod_eq_sum hσ hQ hz).symm

/-- The Robin weight `ρ_k = ((r_k g_*)/(r_* g_k))²` of node `k` against the reference node `k_*`. -/
def robinWeight {κ : Type*} [DecidableEq κ] (S : Finset κ) (σ : κ → ℝ) (g : κ → ℝ) (Q : ℝ[X]) (k₀ k : κ) : ℝ :=
  (resid S σ Q k * g k₀ / (resid S σ Q k₀ * g k)) ^ 2

/-- **The Robin dual certificate** (cpa-loc P2, eq-cpb Lemma 1): orthonormal `ψ_k` on `S` with
`⟨ψ_k, u_b⟩ = n_b g_k/(χ_b − σ_k)` off `k_*`, `σ_{k_*} = χ_j`, `⟨ψ_k, u_j⟩ = 0` off `k_*`, `⟨ψ_{k_*}, u_j⟩ = a`,
and `Q` of degree `< |S|` vanishing at `χ_b` (`b ≠ j`) with `Q(χ_j) ≠ 0` give `a²/Σ_S ρ_k ≤ σ'_j`. -/
theorem div_sum_robinWeight_le {κ : Type*} [DecidableEq κ] (u : ι → E) (hM : (gram ℝ u).PosDef) (j : ι)
    (ψ : κ → E) (S : Finset κ) (hψ : ∀ k ∈ S, ∀ l ∈ S, inner ℝ (ψ k) (ψ l) = if k = l then 1 else 0)
    (σ : κ → ℝ) (hσ : Set.InjOn σ S) (χ n : ι → ℝ) (g : κ → ℝ) (hg : ∀ k ∈ S, g k ≠ 0)
    {k₀ : κ} (hk₀ : k₀ ∈ S) (hσ₀ : σ k₀ = χ j) (hz : ∀ b, b ≠ j → ∀ k ∈ S, χ b ≠ σ k)
    (hpair : ∀ b, b ≠ j → ∀ k ∈ S, inner ℝ (ψ k) (u b) = n b * g k / (χ b - σ k))
    (hjk : ∀ k ∈ S, k ≠ k₀ → inner ℝ (ψ k) (u j) = 0) {a : ℝ} (ha : inner ℝ (ψ k₀) (u j) = a)
    {Q : ℝ[X]} (hQ : Q.degree < S.card) (hQz : ∀ b, b ≠ j → Q.eval (χ b) = 0) (hQj : Q.eval (χ j) ≠ 0) :
    a ^ 2 / ∑ k ∈ S, robinWeight S σ g Q k₀ k ≤ sigmaP (gram ℝ u) j := by
  set β : κ → ℝ := fun k => resid S σ Q k / g k with hβ
  set v : E := ∑ k ∈ S, β k • ψ k with hvdef
  have hv : ∀ b, b ≠ j → inner ℝ v (u b) = 0 := by
    intro b hb
    rw [hvdef, sum_inner]
    have : ∀ k ∈ S, inner ℝ (β k • ψ k) (u b) = n b * (resid S σ Q k / (χ b - σ k)) := by
      intro k hk
      rw [inner_smul_left, conj_trivial, hpair b hb k hk, hβ]
      have := hg k hk
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_resid_div hσ hQ (hz b hb), hQz b hb, zero_div, mul_zero]
  have hvj : inner ℝ v (u j) = β k₀ * a := by
    rw [hvdef, sum_inner, Finset.sum_eq_single k₀ (fun k hk hne => by
      rw [inner_smul_left, hjk k hk hne, mul_zero]) (fun h => absurd hk₀ h), inner_smul_left, conj_trivial, ha]
  have hnorm : ‖v‖ ^ 2 = ∑ k ∈ S, β k ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hvdef, sum_inner]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [inner_sum, Finset.sum_eq_single k (fun l hl hne => by
      rw [inner_smul_left, inner_smul_right, hψ k hk l hl, if_neg (Ne.symm hne)]; simp)
      (fun h => absurd hk h), inner_smul_left, inner_smul_right, hψ k hk k hk, if_pos rfl]
    simp; ring
  have hkey := sq_inner_le_sigmaP u hM j v hv
  rw [hvj, hnorm] at hkey
  have hr₀ : resid S σ Q k₀ ≠ 0 := by
    unfold resid
    refine mul_ne_zero (by rw [hσ₀]; exact hQj) ?_
    unfold Lagrange.nodalWeight
    refine Finset.prod_ne_zero_iff.mpr fun l hl => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
    exact (Finset.mem_erase.mp hl).1 (hσ (Finset.mem_erase.mp hl).2 hk₀ h.symm)
  have hβ₀ : β k₀ ≠ 0 := div_ne_zero hr₀ (hg k₀ hk₀)
  have hsum : ∑ k ∈ S, robinWeight S σ g Q k₀ k = (∑ k ∈ S, β k ^ 2) / β k₀ ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [robinWeight, hβ]
    have := hg k hk
    have := hg k₀ hk₀
    field_simp
  have hpos : 0 < β k₀ ^ 2 := by positivity
  rw [hsum]
  by_cases hS : ∑ k ∈ S, β k ^ 2 = 0
  · rw [hS, zero_div, div_zero]; exact (Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos hM j).le
  have hS' : 0 < ∑ k ∈ S, β k ^ 2 := lt_of_le_of_ne (Finset.sum_nonneg fun k _ => sq_nonneg _) (Ne.symm hS)
  rw [div_div_eq_mul_div, div_le_iff₀ hS']
  nlinarith [hkey]

end Cvs.Prolate.Gram.RobinDualCertificate

end
