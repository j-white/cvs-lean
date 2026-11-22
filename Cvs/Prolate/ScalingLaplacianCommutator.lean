import Mathlib
import Cvs.Finite.ParityDisplacementEigenspaces
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ScalingLaplacianCauchyLaw
import Cvs.Prolate.SincOperatorEigenCount

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rank-two commutator of the scaling Laplacian in the rung basis

For rungs `rung c (n i)` with `W_ij = ∫(−(θ + ½)²h_{n(j)})h_{n(i)}` and `M_ij = ∫(H_c h_{n(j)})h_{n(i)}`:
`W = M − diag(χ + ¼)` and `[diag μ, W] = [diag μ, M] = U Vᵀ`, of rank two for `c > 0` and two distinct rungs; for
`c > 0`, `diag(μ)⁻¹M` is symmetric with `Displacement μ (diag(μ)⁻¹M) (2q) p`, and for `c ≠ 0` the `θ + ½` matrix has
`diag(μ)A + A diag(μ) = 2 diag(μ) p pᵀ`.
-/

noncomputable section

open Real Matrix Module

namespace Cvs.Prolate.ScalingLaplacianCommutator
open Cvs.ZeroCounting

open Cvs.Finite.ParityDisplacementEigenspaces (Displacement)
open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev muR IsLevelIdx)
open Cvs.Prolate.ScalingLaplacianCauchyLaw (hamC scalingLap cauchy_rung integral_scalingLap_rung cauchy_entry cross_edge muR_ne_zero theta_rung rungSpace_level)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Cauchy matrix `M_ij = ∫_{−1}^{1} (H_c h_{n(j)}) h_{n(i)}`. -/
def cauchyM (c : ℝ) (n : ι → ℕ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∫ v in (-1 : ℝ)..1, hamC c (rung c (n j)) (rung₂ c (n j)) v * rung c (n i) v

/-- The scaling-Laplacian matrix `W_ij = ∫_{−1}^{1} (−(θ + ½)²h_{n(j)}) h_{n(i)}`. -/
def scalingGram (c : ℝ) (n : ι → ℕ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    ∫ v in (-1 : ℝ)..1, scalingLap (rung c (n j)) (rung₁ c (n j)) (rung₂ c (n j)) v * rung c (n i) v

/-- The `θ + ½` matrix `A_ij = ∫_{−1}^{1} (v h_{n(j)}′ + h_{n(j)}/2) h_{n(i)}`. -/
def thetaGram (c : ℝ) (n : ι → ℕ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∫ v in (-1 : ℝ)..1, (v * rung₁ c (n j) v + rung c (n j) v / 2) * rung c (n i) v

/-- The edge values `p_i = h_{n(i)}(1)`. -/
def edgeVal (c : ℝ) (n : ι → ℕ) (i : ι) : ℝ := rung c (n i) 1

/-- The edge slopes `q_i = h_{n(i)}′(1)`. -/
def edgeSlope (c : ℝ) (n : ι → ℕ) (i : ι) : ℝ := rung₁ c (n i) 1

/-- The cosine-transform eigenvalues `μ_i = muR c (n i)`. -/
def eigs (c : ℝ) (n : ι → ℕ) (i : ι) : ℝ := muR c (n i)

/-- The levels `χ_i = lev c (n i)`. -/
def levs (c : ℝ) (n : ι → ℕ) (i : ι) : ℝ := lev c (n i)

/-- The left generator `U = (2μq, −2μp)`. -/
def genU (c : ℝ) (n : ι → ℕ) : Matrix ι (Fin 2) ℝ :=
  Matrix.of fun i a => ![2 * eigs c n i * edgeSlope c n i, -(2 * eigs c n i * edgeVal c n i)] a

/-- The right generator `V = (p, q)`, used as `Vᵀ`. -/
def genVt (c : ℝ) (n : ι → ℕ) : Matrix (Fin 2) ι ℝ :=
  Matrix.of fun a j => ![edgeVal c n j, edgeSlope c n j] a

/-- The symmetrised Cauchy matrix `diag(μ)⁻¹M`, entries `M_ij/μ_i`. -/
def loewnerM (c : ℝ) (n : ι → ℕ) : Matrix ι ι ℝ := diagonal (fun i => (eigs c n i)⁻¹) * cauchyM c n

/-! ### A rank criterion -/

omit [DecidableEq ι] in
/-- A matrix with a nonsingular off-diagonal `2 × 2` minor `[[0, a], [b, 0]]` has rank at least two. -/
theorem two_le_rank_of_minor {A : Matrix ι ι ℝ} {i j : ι} (hii : A i i = 0) (hjj : A j j = 0)
    (hij' : A i j ≠ 0) (hji : A j i ≠ 0) : 2 ≤ A.rank := by
  rw [rank_eq_finrank_span_cols]
  have hli : LinearIndependent ℝ ![A.col i, A.col j] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hi := congrFun h i
    have hj := congrFun h j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, col_apply, hii, hjj, mul_zero,
      zero_add, add_zero] at hi hj
    exact ⟨(mul_eq_zero.1 hj).resolve_right hji, (mul_eq_zero.1 hi).resolve_right hij'⟩
  have h2 := finrank_span_eq_card hli
  rw [Fintype.card_fin] at h2
  refine h2.symm.le.trans (Submodule.finrank_mono (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact ⟨i, rfl⟩
  · exact ⟨j, rfl⟩

/-! ### The second-order law -/

omit [Fintype ι] in
/-- **The split `W = M − diag(χ + ¼)`** for injective `n`. -/
theorem scalingGram_eq {c : ℝ} {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) (hinj : Function.Injective n) :
    scalingGram c n = cauchyM c n - diagonal fun i => lev c (n i) + 1 / 4 := by
  ext i j
  simp only [scalingGram, cauchyM, of_apply, Matrix.sub_apply, diagonal_apply]
  rw [integral_scalingLap_rung (hn i) (hn j)]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, if_pos rfl]; ring
  · rw [if_neg (fun h => hij (hinj h).symm), if_neg hij]; ring

/-- **The commutator of the Cauchy matrix, entrywise**: `μ_i M_ij − M_ij μ_j = 2μ_i(q_i p_j − p_i q_j)`. -/
theorem commutator_cauchyM_apply {c : ℝ} {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) (i j : ι) :
    (diagonal (eigs c n) * cauchyM c n - cauchyM c n * diagonal (eigs c n)) i j
      = 2 * eigs c n i * (edgeSlope c n i * edgeVal c n j - edgeVal c n i * edgeSlope c n j) := by
  simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal, cauchyM, of_apply, eigs, edgeSlope, edgeVal]
  have := cauchy_rung (hn i) (hn j)
  linear_combination this

/-- **The commutator in closed form**: `μ_i M_ij − M_ij μ_j = μ_i p_i p_j(χ_i − χ_j)`. -/
theorem commutator_cauchyM_apply_edge {c : ℝ} {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) (i j : ι) :
    (diagonal (eigs c n) * cauchyM c n - cauchyM c n * diagonal (eigs c n)) i j
      = eigs c n i * edgeVal c n i * edgeVal c n j * (levs c n i - levs c n j) := by
  rw [commutator_cauchyM_apply hn]
  have := cross_edge (hn i) (hn j)
  simp only [eigs, edgeSlope, edgeVal, levs]
  linear_combination (2 * muR c (n i)) * this

/-- **The displacement form**: `[diag μ, M] = 2 diag μ (q pᵀ − p qᵀ)`. -/
theorem commutator_cauchyM {c : ℝ} {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) :
    diagonal (eigs c n) * cauchyM c n - cauchyM c n * diagonal (eigs c n)
      = (2 : ℝ) • (diagonal (eigs c n) *
          (vecMulVec (edgeSlope c n) (edgeVal c n) - vecMulVec (edgeVal c n) (edgeSlope c n))) := by
  ext i j
  rw [commutator_cauchyM_apply hn]
  simp only [Matrix.smul_apply, diagonal_mul, Matrix.sub_apply, vecMulVec_apply, smul_eq_mul]
  ring

/-- **The commutator factors through `Fin 2`**: `[diag μ, M] = U Vᵀ`. -/
theorem commutator_cauchyM_eq_mul {c : ℝ} {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) :
    diagonal (eigs c n) * cauchyM c n - cauchyM c n * diagonal (eigs c n) = genU c n * genVt c n := by
  ext i j
  rw [commutator_cauchyM_apply hn]
  simp only [genU, genVt, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Rank at most two**: `rank [diag μ, M] ≤ 2`. -/
theorem rank_commutator_cauchyM_le {c : ℝ} {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) :
    (diagonal (eigs c n) * cauchyM c n - cauchyM c n * diagonal (eigs c n)).rank ≤ 2 := by
  rw [commutator_cauchyM_eq_mul hn]
  exact (rank_mul_le_left _ _).trans ((rank_le_card_width _).trans_eq (Fintype.card_fin 2))

/-- **Rank exactly two**: for `c > 0`, injective `n` and at least two rungs, `rank [diag μ, M] = 2`. -/
theorem rank_commutator_cauchyM_eq_two {c : ℝ} (hc : 0 < c) {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ)
    (hinj : Function.Injective n) (h2 : 2 ≤ Fintype.card ι) :
    (diagonal (eigs c n) * cauchyM c n - cauchyM c n * diagonal (eigs c n)).rank = 2 := by
  refine le_antisymm (rank_commutator_cauchyM_le hn) ?_
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (α := ι) (by omega)
  have hχ : levs c n i - levs c n j ≠ 0 := by
    have hne : n i ≠ n j := fun h => hij (hinj h)
    simp only [levs]
    rcases lt_or_gt_of_ne hne with h | h
    · exact sub_ne_zero.2 (Cvs.Prolate.EvenRungsByIndex.lev_lt (hn j) h).ne
    · exact sub_ne_zero.2 (Cvs.Prolate.EvenRungsByIndex.lev_lt (hn i) h).ne'
  have hp : ∀ k, edgeVal c n k ≠ 0 := fun k => Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero (hn k)
  have hμ : ∀ k, eigs c n k ≠ 0 := fun k => muR_ne_zero hc (hn k)
  refine two_le_rank_of_minor (i := i) (j := j) ?_ ?_ ?_ ?_ <;> rw [commutator_cauchyM_apply_edge hn]
  · ring
  · ring
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hμ i) (hp i)) (hp j)) hχ
  · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (hμ j) (hp j)) (hp i)) ?_
    rw [← neg_sub]; exact neg_ne_zero.2 hχ

/-- `W − M` commutes with `diag μ`: its entries vanish off `n i = n j`. -/
theorem commutator_scalingGram {c : ℝ} {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) :
    diagonal (eigs c n) * scalingGram c n - scalingGram c n * diagonal (eigs c n)
      = diagonal (eigs c n) * cauchyM c n - cauchyM c n * diagonal (eigs c n) := by
  ext i j
  simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal, scalingGram, cauchyM, of_apply]
  rw [integral_scalingLap_rung (hn i) (hn j)]
  by_cases hij : n j = n i
  · simp only [eigs, hij]; ring
  · rw [if_neg hij]; ring

/-- **The commutator of the scaling Laplacian factors**: `[diag μ, W] = U Vᵀ`. -/
theorem commutator_scalingGram_eq_mul {c : ℝ} {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) :
    diagonal (eigs c n) * scalingGram c n - scalingGram c n * diagonal (eigs c n) = genU c n * genVt c n := by
  rw [commutator_scalingGram hn]
  exact commutator_cauchyM_eq_mul hn

/-- **The rank-two law for the scaling Laplacian**: `rank [diag μ, W] ≤ 2`. -/
theorem rank_commutator_scalingGram_le {c : ℝ} {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) :
    (diagonal (eigs c n) * scalingGram c n - scalingGram c n * diagonal (eigs c n)).rank ≤ 2 := by
  rw [commutator_scalingGram hn]
  exact rank_commutator_cauchyM_le hn

/-- **Rank exactly two**: for `c > 0`, injective `n` and at least two rungs, `rank [diag μ, W] = 2`. -/
theorem rank_commutator_scalingGram_eq_two {c : ℝ} (hc : 0 < c) {n : ι → ℕ}
    (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) (hinj : Function.Injective n) (h2 : 2 ≤ Fintype.card ι) :
    (diagonal (eigs c n) * scalingGram c n - scalingGram c n * diagonal (eigs c n)).rank = 2 := by
  rw [commutator_scalingGram hn]
  exact rank_commutator_cauchyM_eq_two hc hn hinj h2

/-! ### The symmetric Loewner form -/

/-- **Loewner entries**: for `c > 0` and `n i ≠ n j`, `M_ij/μ_i = p_i p_j(χ_i − χ_j)/(μ_i − μ_j) = M_ji/μ_j`. -/
theorem loewnerM_apply {c : ℝ} (hc : 0 < c) {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) {i j : ι}
    (hij : n i ≠ n j) :
    loewnerM c n i j = edgeVal c n i * edgeVal c n j * (levs c n i - levs c n j) / (eigs c n i - eigs c n j) ∧
      loewnerM c n i j = loewnerM c n j i := by
  have hl : ∀ a b : ι, n a ≠ n b →
      loewnerM c n a b = edgeVal c n a * edgeVal c n b * (levs c n a - levs c n b) / (eigs c n a - eigs c n b) := by
    intro a b hab
    simp only [loewnerM, diagonal_mul, cauchyM, of_apply, eigs, edgeVal, levs]
    rw [(cauchy_entry hc (hn a) (hn b) hab).2.2]
    have := muR_ne_zero hc (hn a)
    field_simp
  refine ⟨hl i j hij, ?_⟩
  rw [hl i j hij, hl j i (Ne.symm hij)]
  have h1 : eigs c n i - eigs c n j ≠ 0 :=
    sub_ne_zero.2 (Cvs.Prolate.ScalingLaplacianCauchyLaw.muR_ne hc (hn i) (hn j) hij)
  have h2 : eigs c n j - eigs c n i ≠ 0 := fun h => h1 (by linarith)
  field_simp
  ring

/-- **`diag(μ)⁻¹M` is symmetric** for `c > 0`. -/
theorem loewnerM_transpose {c : ℝ} (hc : 0 < c) {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) :
    (loewnerM c n)ᵀ = loewnerM c n := by
  ext i j
  rw [transpose_apply]
  by_cases hij : n j = n i
  · simp only [loewnerM, diagonal_mul, cauchyM, of_apply, eigs, hij]
  · exact (loewnerM_apply hc hn hij).2

/-- **The displacement predicate**: for `c > 0`, `Displacement μ (diag(μ)⁻¹M) (2q) p`, i.e.
`(μ_i − μ_j)M_ij/μ_i = 2q_i p_j − 2p_i q_j`. -/
theorem displacement_loewnerM {c : ℝ} (hc : 0 < c) {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) :
    Displacement (eigs c n) (loewnerM c n) (2 • edgeSlope c n) (edgeVal c n) := by
  intro i j
  have h := cauchy_rung (hn i) (hn j)
  have hμ := muR_ne_zero hc (hn i)
  simp only [loewnerM, diagonal_mul, cauchyM, of_apply, eigs, edgeSlope, edgeVal, Pi.smul_apply]
  field_simp
  linear_combination h

/-! ### The first-order law -/

/-- **The anti-displacement of `θ + ½`**: for `c ≠ 0`, `diag(μ)A + A diag(μ) = 2 diag(μ) p pᵀ`. -/
theorem antiCommutator_thetaGram {c : ℝ} (hc : c ≠ 0) {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) :
    diagonal (eigs c n) * thetaGram c n + thetaGram c n * diagonal (eigs c n)
      = (2 : ℝ) • (diagonal (eigs c n) * vecMulVec (edgeVal c n) (edgeVal c n)) := by
  ext i j
  simp only [Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    thetaGram, of_apply, eigs, edgeVal]
  have hli : ContinuousOn (fun v => rung c (n j) v * rung c (n i) v) (Set.Icc (-1) 1) :=
    (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung (hn j)).mul (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung (hn i))
  rw [← Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hli
  have hθ : ContinuousOn (fun v => v * rung₁ c (n j) v * rung c (n i) v) (Set.uIcc (-1) 1) := by
    obtain ⟨-, hg₁, -, -, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec (hn j)
    have hg₁c : ContinuousOn (rung₁ c (n j)) (Set.uIcc (-1) 1) := fun s hs =>
      (hg₁ s hs).continuousAt.continuousWithinAt
    have hic := Cvs.Prolate.EvenRungsByIndex.continuousOn_rung (hn i)
    rw [← Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hic
    exact (continuousOn_id.mul hg₁c).mul hic
  have e : ∫ v in (-1 : ℝ)..1, (v * rung₁ c (n j) v + rung c (n j) v / 2) * rung c (n i) v
      = (∫ v in (-1 : ℝ)..1, v * rung₁ c (n j) v * rung c (n i) v)
        + (1 / 2) * ∫ v in (-1 : ℝ)..1, rung c (n j) v * rung c (n i) v := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hθ.intervalIntegrable
      (hli.intervalIntegrable.const_mul _)]
    exact intervalIntegral.integral_congr fun v _ => by ring
  rw [e, Cvs.Prolate.SincOperatorEigenCount.integral_rung_mul_rung_eq (hn j) (hn i)]
  have ht := theta_rung hc (hn i) (hn j)
  by_cases hij : n j = n i
  · rw [if_pos hij] at ht ⊢
    rw [hij] at ht ⊢
    linear_combination ht
  · rw [if_neg hij] at ht ⊢
    linear_combination ht

/-- **Rank one**: `rank (diag(μ)A + A diag(μ)) ≤ 1` for `c ≠ 0`. -/
theorem rank_antiCommutator_thetaGram_le {c : ℝ} (hc : c ≠ 0) {n : ι → ℕ} (hn : ∀ i, ∃ χ, IsLevelIdx c (n i) χ) :
    (diagonal (eigs c n) * thetaGram c n + thetaGram c n * diagonal (eigs c n)).rank ≤ 1 := by
  have e : (2 : ℝ) • (diagonal (eigs c n) * vecMulVec (edgeVal c n) (edgeVal c n))
      = vecMulVec (fun i => 2 * eigs c n i * edgeVal c n i) (edgeVal c n) := by
    ext i j
    simp only [Matrix.smul_apply, diagonal_mul, vecMulVec_apply, smul_eq_mul]
    ring
  rw [antiCommutator_thetaGram hc hn, e]
  exact rank_vecMulVec_le _ _

/-! ### On the rung space at `c = 2πx` -/

/-- **The law on the rungs `rung (2πx) (2j)`, `j < x`**: `[diag μ, W] = U Vᵀ`, `rank [diag μ, W] ≤ 2` and
`W = M − diag(χ + ¼)`. -/
theorem rungSpace_law (x : ℕ) :
    diagonal (eigs (2 * π * x) fun j : Fin x => 2 * (j : ℕ)) * scalingGram (2 * π * x) (fun j : Fin x => 2 * (j : ℕ))
        - scalingGram (2 * π * x) (fun j : Fin x => 2 * (j : ℕ))
          * diagonal (eigs (2 * π * x) fun j : Fin x => 2 * (j : ℕ))
        = genU (2 * π * x) (fun j : Fin x => 2 * (j : ℕ)) * genVt (2 * π * x) (fun j : Fin x => 2 * (j : ℕ)) ∧
      (diagonal (eigs (2 * π * x) fun j : Fin x => 2 * (j : ℕ)) * scalingGram (2 * π * x) (fun j : Fin x => 2 * (j : ℕ))
        - scalingGram (2 * π * x) (fun j : Fin x => 2 * (j : ℕ))
          * diagonal (eigs (2 * π * x) fun j : Fin x => 2 * (j : ℕ))).rank ≤ 2 ∧
      scalingGram (2 * π * x) (fun j : Fin x => 2 * (j : ℕ))
        = cauchyM (2 * π * x) (fun j : Fin x => 2 * (j : ℕ))
          - diagonal fun j : Fin x => lev (2 * π * x) (2 * (j : ℕ)) + 1 / 4 := by
  have hn : ∀ j : Fin x, ∃ χ, IsLevelIdx (2 * π * x) (2 * (j : ℕ)) χ := fun j => rungSpace_level j.2
  have hinj : Function.Injective fun j : Fin x => 2 * (j : ℕ) := fun a b h => Fin.ext (by simpa using h)
  exact ⟨commutator_scalingGram_eq_mul hn, rank_commutator_scalingGram_le hn, scalingGram_eq hn hinj⟩

/-- **Rank exactly two on the rung space**: for `x ≥ 2`, `rank [diag μ, W] = 2` on `rung (2πx) (2j)`, `j < x`. -/
theorem rungSpace_rank_eq_two {x : ℕ} (hx : 2 ≤ x) :
    (diagonal (eigs (2 * π * x) fun j : Fin x => 2 * (j : ℕ)) * scalingGram (2 * π * x) (fun j : Fin x => 2 * (j : ℕ))
        - scalingGram (2 * π * x) (fun j : Fin x => 2 * (j : ℕ))
          * diagonal (eigs (2 * π * x) fun j : Fin x => 2 * (j : ℕ))).rank = 2 := by
  have hn : ∀ j : Fin x, ∃ χ, IsLevelIdx (2 * π * x) (2 * (j : ℕ)) χ := fun j => rungSpace_level j.2
  have hinj : Function.Injective fun j : Fin x => 2 * (j : ℕ) := fun a b h => Fin.ext (by simpa using h)
  have hc : 0 < 2 * π * x := by
    have : (2 : ℝ) ≤ x := by exact_mod_cast hx
    positivity
  exact rank_commutator_scalingGram_eq_two hc hn hinj (by rw [Fintype.card_fin]; exact hx)

/-- **The displacement predicate on the rung space**: `Displacement μ (diag(μ)⁻¹M) (2q) p` on `rung (2πx) (2j)`,
`j < x`. -/
theorem rungSpace_displacement (x : ℕ) :
    Displacement (eigs (2 * π * x) fun j : Fin x => 2 * (j : ℕ)) (loewnerM (2 * π * x) fun j : Fin x => 2 * (j : ℕ))
      (2 • edgeSlope (2 * π * x) fun j : Fin x => 2 * (j : ℕ)) (edgeVal (2 * π * x) fun j : Fin x => 2 * (j : ℕ)) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · intro i; exact i.elim0
  have hc : 0 < 2 * π * x := by
    have : (0 : ℝ) < x := by exact_mod_cast hx
    positivity
  exact displacement_loewnerM hc fun j => rungSpace_level j.2

end Cvs.Prolate.ScalingLaplacianCommutator
