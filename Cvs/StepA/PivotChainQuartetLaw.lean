import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Route.EigenvectorCoordinateCompression
import Cvs.StepA.OddBottomGapCriterion
import Cvs.StepA.OneZeroParitySectors
import Cvs.Upstream.BorderedDeterminantPivot
import Cvs.Upstream.ConstrainedFormPivotChain
import Cvs.Upstream.PivotChainInertia
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The quartet law for the pivot chain

For `Q = A + BCBᵀ`, `det K_M(Q) = det K_M(A) · det C · det(C⁻¹ + Γ_M)` with `Γ_M = U_Mᵀ K_M(A)⁻¹ U_M` the maximum of
`2yᵀBᵀv − vᵀAv` over `V_M`, growing by `κ'_{M+1}(A)⁻¹ββᵀ` per step. For symmetric `2 × 2` `C` with `det C < 0`,
`A + BCBᵀ ≥ 0` on `V_M` iff `det(C⁻¹ + Γ_M) ≤ 0`, with negative index `1` or `0` accordingly. On the window form,
`log x · Cvs.Upstream.ConstrainedFormPivotChain.cosQ x` is the zero sum of Cvs.StepA.OneZeroParitySectors, one `Cq(1/2)` block per zero and a square per on-line zero.
-/

noncomputable section

open Matrix

namespace Cvs.StepA.PivotChainQuartetLaw
open Cvs.ZeroCounting

/-! ### The matrix determinant lemma with a symmetric middle factor -/

section Woodbury

variable {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

/-- **Determinant lemma**: `det(K + U C Uᵀ) = det K · det C · det(C⁻¹ + UᵀK⁻¹U)` for invertible `K`, `C`. -/
theorem det_add_mul_mul {Kmat : Matrix m m ℝ} (hK : IsUnit Kmat.det) (U : Matrix m p ℝ) {C : Matrix p p ℝ}
    (hC : IsUnit C.det) :
    (Kmat + U * C * Uᵀ).det = Kmat.det * C.det * (C⁻¹ + Uᵀ * Kmat⁻¹ * U).det := by
  rw [Matrix.mul_assoc, det_add_mul U (C * Uᵀ) hK, mul_assoc]
  congr 1
  rw [← det_mul, Matrix.mul_add, mul_nonsing_inv _ hC, Matrix.mul_assoc C, Matrix.mul_assoc C,
    Matrix.mul_assoc]

/-- The ratio of two determinant-lemma factorisations with the same `C`. -/
theorem ratio_eq {a1 a0 c g1 g0 : ℝ} (hc : c ≠ 0) :
    (a1 * c * g1) / (a0 * c * g0) = (a1 / a0) * (g1 / g0) := by
  rw [show a1 * c * g1 = (a1 * g1) * c by ring, show a0 * c * g0 = (a0 * g0) * c by ring,
    mul_div_mul_right _ _ hc, mul_div_mul_comm]

end Woodbury

/-! ### The single quartet -/

/-- The quartet block `C = 2[[α, −β], [−β, −α]]` of `c = α + iβ`. -/
def Cq (c : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * c.re, -2 * c.im; -2 * c.im, -2 * c.re]

/-- **The quartet block represents `2 Re(c (p + iq)²)`.** -/
theorem quad_Cq (c : ℂ) (p q : ℝ) :
    ![p, q] ⬝ᵥ (Cq c *ᵥ ![p, q]) = 2 * (c * (p + q * Complex.I) ^ 2).re := by
  simp [Cq, dotProduct, mulVec, Fin.sum_univ_two, sq, Complex.mul_re, Complex.mul_im]
  ring

/-- `C² = 4|c|²`. -/
theorem Cq_mul_self (c : ℂ) : Cq c * Cq c = (4 * Complex.normSq c) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Cq, Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_apply] <;> ring

/-- `det C = −4|c|²`. -/
theorem det_Cq (c : ℂ) : (Cq c).det = -4 * Complex.normSq c := by
  simp [Cq, det_fin_two, Complex.normSq_apply]; ring

/-- `C⁻¹ = C / (4|c|²)` for `c ≠ 0`. -/
theorem inv_Cq {c : ℂ} (hc : c ≠ 0) : (Cq c)⁻¹ = (4 * Complex.normSq c)⁻¹ • Cq c := by
  have hn : (4 * Complex.normSq c) ≠ 0 := mul_ne_zero (by norm_num) (Complex.normSq_pos.mpr hc).ne'
  refine inv_eq_left_inv ?_
  rw [smul_mul_assoc, Cq_mul_self, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- **The single-quartet determinant**: for a symmetric `Γ = [[a, b], [b, d]]`,
`det(C/2 + 2|c|²Γ) = |c|²(|c|²k₁² − |1 + c k₂|²)` with `k₁ = a + d`, `k₂ = a − d + 2ib`. -/
theorem det_quartet (c : ℂ) (a b d : ℝ) :
    ((1 / 2 : ℝ) • Cq c + (2 * Complex.normSq c) • !![a, b; b, d]).det
      = Complex.normSq c * (Complex.normSq c * (a + d) ^ 2
          - Complex.normSq (1 + c * ((a - d : ℝ) + (2 * b : ℝ) * Complex.I))) := by
  simp [Cq, det_fin_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- **The single-quartet test in the report's normalisation**: for `c ≠ 0`,
`det(2|c|²(C⁻¹ + Γ)) / |c|² = |c|²k₁² − |1 + c k₂|²`. -/
theorem det_quartet_inv {c : ℂ} (hc : c ≠ 0) (a b d : ℝ) :
    ((2 * Complex.normSq c) • ((Cq c)⁻¹ + !![a, b; b, d])).det / Complex.normSq c
      = Complex.normSq c * (a + d) ^ 2
          - Complex.normSq (1 + c * ((a - d : ℝ) + (2 * b : ℝ) * Complex.I)) := by
  have hn : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  have h : (2 * Complex.normSq c) • ((Cq c)⁻¹ + !![a, b; b, d])
      = (1 / 2 : ℝ) • Cq c + (2 * Complex.normSq c) • !![a, b; b, d] := by
    rw [smul_add, inv_Cq hc, smul_smul]
    congr 2
    field_simp
    ring
  rw [h, det_quartet, mul_div_cancel_left₀ _ hn]

/-- **The quartet kernels from extremal functions**: for `Γ = Σ_j w_j (p_j, q_j)(p_j, q_j)ᵀ` and `F_j = p_j + i q_j`,
`tr Γ = Σ w_j |F_j|²` and `Γ₁₁ − Γ₂₂ + 2iΓ₁₂ = Σ w_j F_j²`. -/
theorem kernels_of_sum {J : Type*} (s : Finset J) (w p q : J → ℝ) :
    (∑ j ∈ s, w j * p j ^ 2) + (∑ j ∈ s, w j * q j ^ 2) = ∑ j ∈ s, w j * Complex.normSq (p j + q j * Complex.I) ∧
    (((∑ j ∈ s, w j * p j ^ 2) - (∑ j ∈ s, w j * q j ^ 2) : ℝ) : ℂ)
        + ((2 * ∑ j ∈ s, w j * (p j * q j) : ℝ) : ℂ) * Complex.I
      = ∑ j ∈ s, (w j : ℂ) * (p j + q j * Complex.I) ^ 2 := by
  constructor
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.normSq_apply]; ring
  · push_cast
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring_nf
    rw [Complex.I_sq]
    ring

/-! ### Symmetric `2 × 2` forms -/

section TwoByTwo

theorem symm_10 {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : Sᵀ = S) : S 1 0 = S 0 1 := by
  have := congrFun (congrFun hS 0) 1
  simpa using this

theorem quad_two (S : Matrix (Fin 2) (Fin 2) ℝ) (z : Fin 2 → ℝ) :
    z ⬝ᵥ (S *ᵥ z) = S 0 0 * z 0 ^ 2 + (S 0 1 + S 1 0) * (z 0 * z 1) + S 1 1 * z 1 ^ 2 := by
  simp only [dotProduct, mulVec, Fin.sum_univ_two]; ring

theorem bil_two (S : Matrix (Fin 2) (Fin 2) ℝ) (z s : Fin 2 → ℝ) :
    z ⬝ᵥ (S *ᵥ s) = S 0 0 * z 0 * s 0 + S 0 1 * z 0 * s 1 + S 1 0 * z 1 * s 0 + S 1 1 * z 1 * s 1 := by
  simp only [dotProduct, mulVec, Fin.sum_univ_two]; ring

theorem ne_zero_two {z : Fin 2 → ℝ} (hz : z ≠ 0) : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
  by_contra h
  push Not at h
  exact hz (funext fun i => by fin_cases i <;> simp [h.1, h.2])

/-- **A symmetric `2 × 2` form with negative determinant takes a negative value.** -/
theorem exists_neg_of_det_neg {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : Sᵀ = S) (hd : S.det < 0) :
    ∃ z : Fin 2 → ℝ, z ⬝ᵥ (S *ᵥ z) < 0 := by
  have h10 := symm_10 hS
  rw [det_fin_two, h10] at hd
  rcases lt_trichotomy (S 0 0) 0 with h | h | h
  · refine ⟨![1, 0], ?_⟩
    rw [quad_two]; simp; linarith
  · refine ⟨![-(S 1 1 + 1), 2 * S 0 1], ?_⟩
    rw [h] at hd
    rw [quad_two, h10, h]; simp
    nlinarith
  · refine ⟨![-S 0 1, S 0 0], ?_⟩
    rw [quad_two, h10]; simp
    nlinarith

/-- **A symmetric `2 × 2` form with negative determinant takes a positive value.** -/
theorem exists_pos_of_det_neg {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : Sᵀ = S) (hd : S.det < 0) :
    ∃ z : Fin 2 → ℝ, 0 < z ⬝ᵥ (S *ᵥ z) := by
  have hS' : (-S)ᵀ = -S := by rw [transpose_neg, hS]
  have hd' : (-S).det < 0 := by rw [det_neg]; simpa using hd
  obtain ⟨z, hz⟩ := exists_neg_of_det_neg hS' hd'
  refine ⟨z, ?_⟩
  rw [neg_mulVec, dotProduct_neg] at hz
  linarith

/-- **Positive determinant and one positive value make a symmetric `2 × 2` form positive definite.** -/
theorem pos_of_det_pos {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : Sᵀ = S) (hd : 0 < S.det) {e : Fin 2 → ℝ}
    (he : 0 < e ⬝ᵥ (S *ᵥ e)) {z : Fin 2 → ℝ} (hz : z ≠ 0) : 0 < z ⬝ᵥ (S *ᵥ z) := by
  have h10 := symm_10 hS
  rw [det_fin_two, h10] at hd
  rw [quad_two, h10] at he ⊢
  have key : ∀ w : Fin 2 → ℝ, S 0 0 * (S 0 0 * w 0 ^ 2 + (S 0 1 + S 0 1) * (w 0 * w 1) + S 1 1 * w 1 ^ 2)
      = (S 0 0 * w 0 + S 0 1 * w 1) ^ 2 + (S 0 0 * S 1 1 - S 0 1 * S 0 1) * w 1 ^ 2 := fun w => by ring
  have h00 : 0 < S 0 0 := by
    rcases lt_trichotomy (S 0 0) 0 with h | h | h
    · have := key e
      nlinarith [sq_nonneg (S 0 0 * e 0 + S 0 1 * e 1), sq_nonneg (e 1)]
    · rw [h] at hd; nlinarith [sq_nonneg (S 0 1)]
    · exact h
  have hk := key z
  have hpos : 0 < (S 0 0 * z 0 + S 0 1 * z 1) ^ 2 + (S 0 0 * S 1 1 - S 0 1 * S 0 1) * z 1 ^ 2 := by
    rcases ne_zero_two hz with h | h
    · by_cases h1 : z 1 = 0
      · rw [h1]; simp
        exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (mul_ne_zero h00.ne' h)))
      · have := pow_pos (abs_pos.mpr h1) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg (S 0 0 * z 0 + S 0 1 * z 1)]
    · have := pow_pos (abs_pos.mpr h) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg (S 0 0 * z 0 + S 0 1 * z 1)]
  rw [← hk] at hpos
  exact pos_of_mul_pos_right hpos h00.le

/-- **A positive definite symmetric `2 × 2` form has positive determinant.** -/
theorem det_pos_of_pos {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : Sᵀ = S)
    (hpd : ∀ z : Fin 2 → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (S *ᵥ z)) : 0 < S.det := by
  have h10 := symm_10 hS
  have h00 : 0 < S 0 0 := by
    have := hpd ![1, 0] (by intro h; simpa using congrFun h 0)
    rw [quad_two] at this; simpa using this
  have := hpd ![-S 0 1, S 0 0] (by intro h; have := congrFun h 1; simp at this; linarith)
  rw [quad_two, h10] at this
  simp at this
  rw [det_fin_two, h10]
  nlinarith

/-- **The reverse Cauchy–Schwarz identity** for a symmetric `2 × 2` form:
`(zᵀSs)² − (zᵀSz)(sᵀSs) = −det S · (z₀s₁ − z₁s₀)²`. -/
theorem rev_cs {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : Sᵀ = S) (z s : Fin 2 → ℝ) :
    (z ⬝ᵥ (S *ᵥ s)) ^ 2 - (z ⬝ᵥ (S *ᵥ z)) * (s ⬝ᵥ (S *ᵥ s)) = -S.det * (z 0 * s 1 - z 1 * s 0) ^ 2 := by
  have h10 := symm_10 hS
  rw [bil_two, quad_two, quad_two, det_fin_two, h10]
  ring

end TwoByTwo

/-! ### The quartet law on the chain -/

section Chain

open Cvs.Upstream.ConstrainedFormPivotChain (qf rows V mem_V)
open Cvs.Upstream.BorderedDeterminantPivot (bord solW solL bord_solve lagrange K blk schur schur_eq_det_div qf_succ rows_succ blk_transpose amin amin_mem amin_orth qf_amin wmin wmin_solve)

variable {κ p : Type*} [Fintype κ] [DecidableEq κ] [Fintype p] [DecidableEq p]

/-- The low-rank part `B C Bᵀ` on `ℕ`-indexed entries. -/
def lowRank (B : ℕ → p → ℝ) (C : Matrix p p ℝ) : Matrix ℕ ℕ ℝ :=
  Matrix.of fun i j => ∑ b, (∑ a, B i a * C a b) * B j b

/-- The low-rank columns bordered by zeros: `U_M = [B_{[0,M]}; 0]`. -/
def Ucol (B : ℕ → p → ℝ) (M : ℕ) : Matrix (Fin (M + 1) ⊕ κ) p ℝ :=
  Matrix.of (Sum.elim (fun i a => B i a) fun _ _ => 0)

/-- **The reproducing kernel at the low-rank directions**: `Γ_M = U_Mᵀ K_M(A)⁻¹ U_M`. -/
def Gam (A : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) (M : ℕ) : Matrix p p ℝ :=
  (Ucol (κ := κ) B M)ᵀ * (K A r M)⁻¹ * Ucol B M

omit [Fintype κ] [DecidableEq κ] [DecidableEq p] in
theorem K_add_lowRank (A : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) (C : Matrix p p ℝ) (M : ℕ) :
    K (A + lowRank B C) r M = K A r M + Ucol B M * C * (Ucol B M)ᵀ := by
  ext x y
  rcases x with i | k <;> rcases y with j | l <;>
    simp [K, bord, blk, lowRank, Ucol, Matrix.mul_apply, Function.swap]

omit [DecidableEq p] in
theorem lowRank_symm (B : ℕ → p → ℝ) {C : Matrix p p ℝ} (hC : Cᵀ = C) (i j : ℕ) :
    lowRank B C j i = lowRank B C i j := by
  have hc : ∀ a b, C b a = C a b := fun a b => by
    have := congrFun (congrFun hC a) b; simpa using this
  simp only [lowRank, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hc]; ring

/-- **The determinant lemma on the chain**: `det K_M(A + BCBᵀ) = det K_M(A) · det C · det(C⁻¹ + Γ_M)`. -/
theorem det_K_add_lowRank (A : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) {C : Matrix p p ℝ} {M : ℕ}
    (hK : IsUnit (K A r M).det) (hC : IsUnit C.det) :
    (K (A + lowRank B C) r M).det = (K A r M).det * C.det * (C⁻¹ + Gam A r B M).det := by
  rw [K_add_lowRank, det_add_mul_mul hK _ hC]
  rfl

/-- **The quartet law**: `κ'_{M+1}(A + BCBᵀ) = κ'_{M+1}(A) · det(C⁻¹ + Γ_{M+1}) / det(C⁻¹ + Γ_M)` for symmetric
`A`, `C`, invertible `C`, `K_M(A)`, `K_{M+1}(A)` and `C⁻¹ + Γ_M`. -/
theorem schur_add_lowRank (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ)
    {C : Matrix p p ℝ} (hCs : Cᵀ = C) (hC : IsUnit C.det) {M : ℕ} (hK0 : IsUnit (K A r M).det)
    (hK1 : IsUnit (K A r (M + 1)).det) (hG0 : IsUnit (C⁻¹ + Gam A r B M).det) :
    schur (A + lowRank B C) r M
      = schur A r M * ((C⁻¹ + Gam A r B (M + 1)).det / (C⁻¹ + Gam A r B M).det) := by
  have hQ : ∀ i j, (A + lowRank B C) j i = (A + lowRank B C) i j := fun i j => by
    simp only [Matrix.add_apply, hA i j, lowRank_symm B hCs i j]
  have hKQ : IsUnit (K (A + lowRank B C) r M).det := by
    rw [det_K_add_lowRank A r B hK0 hC]
    exact ((hK0.mul hC).mul hG0)
  rw [schur_eq_det_div _ hQ r hKQ, schur_eq_det_div A hA r hK0, det_K_add_lowRank A r B hK1 hC,
    det_K_add_lowRank A r B hK0 hC, ratio_eq hC.ne_zero]

omit [Fintype κ] [DecidableEq κ] [DecidableEq p] in
theorem Ucol_mulVec (B : ℕ → p → ℝ) (M : ℕ) (y : p → ℝ) :
    Ucol (κ := κ) B M *ᵥ y = Sum.elim (fun i : Fin (M + 1) => ∑ a, B i a * y a) 0 := by
  funext x; rcases x with i | k <;> simp [Ucol, mulVec, dotProduct]

omit [DecidableEq p] in
theorem quad_Gam (A : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) (M : ℕ) (y : p → ℝ) :
    y ⬝ᵥ (Gam A r B M *ᵥ y) = (Ucol (κ := κ) B M *ᵥ y) ⬝ᵥ ((K A r M)⁻¹ *ᵥ (Ucol B M *ᵥ y)) := by
  have h : Gam A r B M *ᵥ y = (Ucol (κ := κ) B M)ᵀ *ᵥ ((K A r M)⁻¹ *ᵥ (Ucol B M *ᵥ y)) := by
    rw [mulVec_mulVec, mulVec_mulVec]
    rfl
  rw [h, dotProduct_mulVec, vecMul_transpose]

/-- The low-rank direction `b = B_{[0,M]} y` on the modes. -/
def bvec (B : ℕ → p → ℝ) (M : ℕ) (y : p → ℝ) : Fin (M + 1) → ℝ := fun i => ∑ a, B i a * y a

omit [DecidableEq p] in
/-- **`Γ_M` as a constrained maximum**: for every `v ∈ V_M`, `yᵀΓ_M y = 2bᵀv − vᵀA_M v + (v − w)ᵀA_M(v − w)` with
`b = B_{[0,M]} y` and `w` the mode part of `K_M(A)⁻¹(b, 0)`. -/
theorem quad_Gam_eq (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) {M : ℕ}
    (hK : IsUnit (K A r M).det) (y : p → ℝ) {v : Fin (M + 1) → ℝ} (hv : v ∈ V r M) :
    y ⬝ᵥ (Gam A r B M *ᵥ y) = 2 * (bvec B M y ⬝ᵥ v) - qf A M v
      + qf A M (v - solW (blk A M) (rows r M)ᵀ (bvec B M y) 0) := by
  have hv' : ((rows r M)ᵀ)ᵀ *ᵥ v = 0 := by rw [transpose_transpose]; exact mem_V.mp hv
  have hl := lagrange (blk_transpose A hA M) hK (bvec B M y) 0 hv'
  rw [quad_Gam, Ucol_mulVec]
  have : Sum.elim (fun i : Fin (M + 1) => ∑ a, B i a * y a) (0 : κ → ℝ) = Sum.elim (bvec B M y) 0 := rfl
  rw [this]
  simp only [qf]
  change v ⬝ᵥ (blk A M *ᵥ v) - _ = _ at hl
  unfold K
  linarith

omit [DecidableEq p] in
/-- **`Γ_M` is Loewner-nondecreasing**: `yᵀΓ_M y ≤ yᵀΓ_{M+1} y` when `K_M(A)`, `K_{M+1}(A)` are invertible and
`A_{M+1} ≥ 0` on `V_{M+1}`. -/
theorem Gam_mono (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) {M : ℕ}
    (hK0 : IsUnit (K A r M).det) (hK1 : IsUnit (K A r (M + 1)).det)
    (hpsd : ∀ u ∈ V r (M + 1), 0 ≤ qf A (M + 1) u) (y : p → ℝ) :
    y ⬝ᵥ (Gam A r B M *ᵥ y) ≤ y ⬝ᵥ (Gam A r B (M + 1) *ᵥ y) := by
  set w := solW (blk A M) (rows r M)ᵀ (bvec B M y) 0
  have hw : w ∈ V r M := by
    have := (bord_solve hK0 (bvec B M y) 0).2
    rw [transpose_transpose] at this; exact mem_V.mpr this
  have h0 := quad_Gam_eq A hA r B hK0 y hw
  have hz : qf A M 0 = 0 := by simp [qf]
  rw [sub_self, hz, add_zero] at h0
  set v : Fin (M + 1 + 1) → ℝ := Fin.snoc w 0
  have hv : v ∈ V r (M + 1) := by
    rw [mem_V, rows_succ]; simp [v, Fin.init_snoc, mem_V.mp hw]
  have h1 := quad_Gam_eq A hA r B hK1 y hv
  have hdiff : v - solW (blk A (M + 1)) (rows r (M + 1))ᵀ (bvec B (M + 1) y) 0 ∈ V r (M + 1) := by
    have := (bord_solve hK1 (bvec B (M + 1) y) 0).2
    rw [transpose_transpose] at this
    refine Submodule.sub_mem _ hv (mem_V.mpr this)
  have hq : qf A (M + 1) v = qf A M w := by
    rw [qf_succ A hA]; simp [v]
  have hb : bvec B (M + 1) y ⬝ᵥ v = bvec B M y ⬝ᵥ w := by
    simp [v, dotProduct, Fin.sum_univ_castSucc, bvec]
  have := hpsd _ hdiff
  rw [h0, h1, hq, hb]
  linarith

/-! ### `Γ_M` as a maximum, its maximiser, and its rank-one growth -/

/-- The low-rank samples `B_{[0,M]}ᵀ v` of a mode vector. -/
def sv (B : ℕ → p → ℝ) (M : ℕ) (v : Fin (M + 1) → ℝ) : p → ℝ := fun a => ∑ i : Fin (M + 1), B i a * v i

omit [DecidableEq p] in
theorem bvec_dot (B : ℕ → p → ℝ) (M : ℕ) (y : p → ℝ) (v : Fin (M + 1) → ℝ) :
    bvec B M y ⬝ᵥ v = y ⬝ᵥ sv B M v := by
  simp only [bvec, sv, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

omit [Fintype p] [DecidableEq p] in
theorem sv_add_smul (B : ℕ → p → ℝ) (M : ℕ) (v w : Fin (M + 1) → ℝ) (t : ℝ) :
    sv B M (v + t • w) = sv B M v + t • sv B M w := by
  funext a
  simp only [sv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

omit [Fintype p] [DecidableEq p] in
theorem sv_snoc_zero (B : ℕ → p → ℝ) (M : ℕ) (u : Fin (M + 1) → ℝ) :
    sv B (M + 1) (Fin.snoc u 0) = sv B M u := by
  funext a
  simp [sv, Fin.sum_univ_castSucc]

omit [Fintype p] [DecidableEq p] in
theorem sv_zero (B : ℕ → p → ℝ) (M : ℕ) : sv B M 0 = 0 := by
  funext a; simp [sv]

/-- **The maximiser** `w(y)`: the mode part of `K_M(A)⁻¹(B_{[0,M]}y, 0)`. -/
def gmin (A : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) (M : ℕ) (y : p → ℝ) : Fin (M + 1) → ℝ :=
  solW (blk A M) (rows r M)ᵀ (bvec B M y) 0

omit [DecidableEq p] in
theorem gmin_mem {A : Matrix ℕ ℕ ℝ} {r : κ → ℕ → ℝ} (B : ℕ → p → ℝ) {M : ℕ} (hK : IsUnit (K A r M).det)
    (y : p → ℝ) : gmin A r B M y ∈ V r M := by
  have := (bord_solve hK (bvec B M y) 0).2
  rw [transpose_transpose] at this
  exact mem_V.mpr this

omit [DecidableEq p] in
/-- **`Γ_M y` is the sample vector of the maximiser**: `Γ_M y = B_{[0,M]}ᵀ w(y)`. -/
theorem Gam_mulVec (A : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) (M : ℕ) (y : p → ℝ) :
    Gam A r B M *ᵥ y = sv B M (gmin A r B M y) := by
  have h : Gam A r B M *ᵥ y = (Ucol (κ := κ) B M)ᵀ *ᵥ ((K A r M)⁻¹ *ᵥ (Ucol B M *ᵥ y)) := by
    rw [mulVec_mulVec, mulVec_mulVec]
    rfl
  rw [h, Ucol_mulVec]
  funext a
  simp only [mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type, Ucol, of_apply, Sum.elim_inl,
    Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero, sv, gmin, solW]
  rfl

omit [DecidableEq p] in
/-- **The value at the maximiser**: `w(y)ᵀ A_M w(y) = yᵀΓ_M y`. -/
theorem qf_gmin (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) {M : ℕ}
    (hK : IsUnit (K A r M).det) (y : p → ℝ) : qf A M (gmin A r B M y) = y ⬝ᵥ (Gam A r B M *ᵥ y) := by
  have h := quad_Gam_eq A hA r B hK y (gmin_mem B hK y)
  have hz : gmin A r B M y - solW (blk A M) (rows r M)ᵀ (bvec B M y) 0 = 0 := sub_self _
  have hq0 : qf A M 0 = 0 := by simp [qf]
  rw [hz, hq0, add_zero, bvec_dot, ← Gam_mulVec] at h
  linarith

omit [DecidableEq p] in
/-- **`Γ_M` is the maximum of `2yᵀBᵀv − vᵀA_M v` over `V_M`** when `A_M ≥ 0` on `V_M`, attained at `w(y)`. -/
theorem quad_Gam_isGreatest (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ)
    {M : ℕ} (hK : IsUnit (K A r M).det) (hpsd : ∀ v ∈ V r M, 0 ≤ qf A M v) (y : p → ℝ) :
    IsGreatest {z | ∃ v ∈ V r M, z = 2 * (y ⬝ᵥ sv B M v) - qf A M v} (y ⬝ᵥ (Gam A r B M *ᵥ y)) := by
  refine ⟨⟨gmin A r B M y, gmin_mem B hK y, ?_⟩, ?_⟩
  · rw [qf_gmin A hA r B hK, ← Gam_mulVec]; ring
  · rintro z ⟨v, hv, rfl⟩
    have h := quad_Gam_eq A hA r B hK y hv
    have hd : v - solW (blk A M) (rows r M)ᵀ (bvec B M y) 0 ∈ V r M :=
      Submodule.sub_mem _ hv (gmin_mem B hK y)
    have := hpsd _ hd
    rw [bvec_dot] at h
    linarith

omit [DecidableEq p] in
/-- `Γ_M` is positive semidefinite when `A_M ≥ 0` on `V_M`. -/
theorem Gam_psd (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) {M : ℕ}
    (hK : IsUnit (K A r M).det) (hpsd : ∀ v ∈ V r M, 0 ≤ qf A M v) (y : p → ℝ) :
    0 ≤ y ⬝ᵥ (Gam A r B M *ᵥ y) := by
  have := (quad_Gam_isGreatest A hA r B hK hpsd y).2 ⟨0, (V r M).zero_mem, rfl⟩
  simpa [sv_zero, qf] using this

omit [Fintype κ] [DecidableEq κ] in
theorem K_transpose (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (M : ℕ) :
    (K A r M)ᵀ = K A r M := by
  rw [K, bord, fromBlocks_transpose, transpose_transpose, transpose_zero, blk_transpose A hA M]

omit [Fintype p] [DecidableEq p] in
theorem Gam_apply (A : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) (M : ℕ) (a b : p) :
    Gam A r B M a b = ∑ z, (∑ x, Ucol (κ := κ) B M x a * (K A r M)⁻¹ x z) * Ucol (κ := κ) B M z b := rfl

omit [Fintype p] [DecidableEq p] in
/-- `Γ_M` is symmetric. -/
theorem Gam_symm (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) (M : ℕ) :
    (Gam A r B M)ᵀ = Gam A r B M := by
  have hK : ∀ x z, (K A r M)⁻¹ z x = (K A r M)⁻¹ x z := fun x z => by
    have := congrFun (congrFun (transpose_nonsing_inv (K A r M)) x) z
    rw [K_transpose A hA r M] at this
    simpa using this
  ext a b
  rw [transpose_apply, Gam_apply, Gam_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => by rw [hK]; ring

omit [DecidableEq p] in
theorem amin_samples_mem (A : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) {M : ℕ} {u : Fin (M + 1) → ℝ} (hu : u ∈ V r M)
    (hK : IsUnit (K A r M).det) (t : ℝ) : (Fin.snoc u 0 + t • amin A r M : Fin (M + 1 + 1) → ℝ) ∈ V r (M + 1) := by
  have hs : (Fin.snoc u 0 : Fin (M + 1 + 1) → ℝ) ∈ V r (M + 1) := by
    rw [mem_V, rows_succ]; simp [Fin.init_snoc, mem_V.mp hu]
  exact (V r (M + 1)).add_mem hs ((V r (M + 1)).smul_mem t (amin_mem A r hK).1)

omit [DecidableEq p] in
/-- **Every `v ∈ V_{M+1}` splits as `(u, 0) + t a*`** with `u ∈ V_M` and `a*` the minimiser of Cvs.Upstream.BorderedDeterminantPivot. -/
theorem decomp_succ (A : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) {M : ℕ} (hK : IsUnit (K A r M).det)
    {v : Fin (M + 1 + 1) → ℝ} (hv : v ∈ V r (M + 1)) :
    ∃ u ∈ V r M, ∃ t : ℝ, v = Fin.snoc u 0 + t • amin A r M := by
  set t := v (Fin.last _)
  refine ⟨Fin.init v + t • wmin A r M, ?_, t, ?_⟩
  · have hc := mem_V.mp hv
    rw [rows_succ] at hc
    rw [mem_V, mulVec_add, mulVec_smul, (wmin_solve A r hK).2]
    exact hc
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [amin, t]
    · simp [amin, Fin.init]

omit [DecidableEq p] in
/-- Along the split, `A_{M+1}((u, 0) + t a*) = A_M(u) + κ'_{M+1} t²`. -/
theorem qf_split (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) {M : ℕ}
    (hK : IsUnit (K A r M).det) {u : Fin (M + 1) → ℝ} (hu : u ∈ V r M) (t : ℝ) :
    qf A (M + 1) (Fin.snoc u 0 + t • amin A r M) = qf A M u + schur A r M * t ^ 2 := by
  rw [Cvs.Upstream.BorderedDeterminantPivot.qf_add_smul, qf_amin A hA r hK]
  have h1 := amin_orth A r hK hu
  have h2 : amin A r M ⬝ᵥ (blk A (M + 1) *ᵥ Fin.snoc u 0) = 0 := by
    rw [Cvs.Upstream.BorderedDeterminantPivot.dot_mulVec_symm (blk_transpose A hA (M + 1))]; exact h1
  have h3 : qf A (M + 1) (Fin.snoc u 0) = qf A M u := by
    rw [qf_succ A hA]; simp
  rw [h1, h2, h3]; ring

omit [DecidableEq p] in
/-- **The rank-one growth of `Γ`**: with `K_M(A)`, `K_{M+1}(A)` invertible and `A_{M+1} ≥ 0` on `V_{M+1}`,
`yᵀΓ_{M+1}y = yᵀΓ_M y + (yᵀβ)²/κ'_{M+1}`, where `β = B_{[0,M+1]}ᵀ a*` samples the minimiser. -/
theorem Gam_succ_quad (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ)
    {M : ℕ} (hK0 : IsUnit (K A r M).det) (hK1 : IsUnit (K A r (M + 1)).det)
    (hpsd1 : ∀ u ∈ V r (M + 1), 0 ≤ qf A (M + 1) u) (y : p → ℝ) :
    y ⬝ᵥ (Gam A r B (M + 1) *ᵥ y)
      = y ⬝ᵥ (Gam A r B M *ᵥ y) + (y ⬝ᵥ sv B (M + 1) (amin A r M)) ^ 2 / schur A r M := by
  set κ' := schur A r M
  set c := y ⬝ᵥ sv B (M + 1) (amin A r M)
  have hpos : 0 < κ' := by
    have h0 : 0 ≤ κ' := by
      have := hpsd1 _ (amin_mem A r hK0).1
      rwa [qf_amin A hA r hK0] at this
    have hne : κ' ≠ 0 := by
      intro h
      have := Cvs.Upstream.BorderedDeterminantPivot.det_K_succ A hA r hK0
      have h' : schur A r M = 0 := h
      rw [h', mul_zero] at this
      exact hK1.ne_zero this
    exact lt_of_le_of_ne h0 (Ne.symm hne)
  have hpsd0 : ∀ u ∈ V r M, 0 ≤ qf A M u := fun u hu => by
    have := hpsd1 _ (amin_samples_mem A r hu hK0 0)
    rwa [qf_split A hA r hK0 hu, zero_pow two_ne_zero, mul_zero, add_zero] at this
  refine (quad_Gam_isGreatest A hA r B hK1 hpsd1 y).unique ⟨?_, ?_⟩
  · refine ⟨Fin.snoc (gmin A r B M y) 0 + (c / κ') • amin A r M,
      amin_samples_mem A r (gmin_mem B hK0 y) hK0 _, ?_⟩
    rw [sv_add_smul, sv_snoc_zero, qf_split A hA r hK0 (gmin_mem B hK0 y), qf_gmin A hA r B hK0,
      dotProduct_add, dotProduct_smul, smul_eq_mul, ← Gam_mulVec]
    field_simp
    ring
  · rintro z ⟨v, hv, rfl⟩
    obtain ⟨u, hu, t, rfl⟩ := decomp_succ A r hK0 hv
    rw [sv_add_smul, sv_snoc_zero, qf_split A hA r hK0 hu, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hG := (quad_Gam_isGreatest A hA r B hK0 hpsd0 y).2 ⟨u, hu, rfl⟩
    have h2 : 2 * (t * c) - κ' * t ^ 2 ≤ c ^ 2 / κ' := by
      rw [le_div_iff₀ hpos]; nlinarith [sq_nonneg (c - κ' * t)]
    linarith

theorem eq_of_quad_eq {S T : Matrix p p ℝ} (hS : Sᵀ = S) (hT : Tᵀ = T)
    (h : ∀ y, y ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (T *ᵥ y)) : S = T := by
  set D := S - T
  have hD : ∀ y, y ⬝ᵥ (D *ᵥ y) = 0 := fun y => by rw [sub_mulVec, dotProduct_sub, h, sub_self]
  have hDs : ∀ i j, D j i = D i j := fun i j => by
    have := congrFun (congrFun (show Dᵀ = D by rw [transpose_sub, hS, hT]) i) j
    simpa using this
  have he : ∀ (y : p → ℝ) i j, (Pi.single i (1 : ℝ) + Pi.single j 1) ⬝ᵥ (D *ᵥ (Pi.single i 1 + Pi.single j 1))
      = D i i + D i j + D j i + D j j := fun y i j => by
    simp only [mulVec_add, dotProduct_add, add_dotProduct, single_dotProduct, one_mul]
    simp only [mulVec, dotProduct_single, mul_one]
    ring
  rw [← sub_eq_zero]
  ext i j
  have h1 := hD (Pi.single i 1 + Pi.single j 1)
  have h2 := hD (Pi.single i 1)
  have h3 := hD (Pi.single j 1)
  rw [he 0 i j] at h1
  simp only [single_dotProduct, one_mul, mulVec, dotProduct_single, mul_one] at h2 h3
  simp only [Matrix.zero_apply]
  change D i j = 0
  rw [hDs i j] at h1
  linarith

omit [DecidableEq p] in
theorem vecMulVec_quad (β y : p → ℝ) : y ⬝ᵥ (vecMulVec β β *ᵥ y) = (y ⬝ᵥ β) ^ 2 := by
  simp only [dotProduct, mulVec, vecMulVec_apply, sq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The rank-one growth of `Γ` as matrices**: `Γ_{M+1} = Γ_M + κ'_{M+1}⁻¹ ββᵀ`, `β = B_{[0,M+1]}ᵀ a*`. -/
theorem Gam_succ (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ)
    {M : ℕ} (hK0 : IsUnit (K A r M).det) (hK1 : IsUnit (K A r (M + 1)).det)
    (hpsd1 : ∀ u ∈ V r (M + 1), 0 ≤ qf A (M + 1) u) :
    Gam A r B (M + 1) = Gam A r B M
      + (schur A r M)⁻¹ • vecMulVec (sv B (M + 1) (amin A r M)) (sv B (M + 1) (amin A r M)) := by
  refine eq_of_quad_eq (Gam_symm A hA r B _) ?_ fun y => ?_
  · rw [transpose_add, transpose_smul, transpose_vecMulVec, Gam_symm A hA r B]
  · rw [Gam_succ_quad A hA r B hK0 hK1 hpsd1, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      vecMulVec_quad, smul_eq_mul, dotProduct_comm y]
    ring

/-- **`Γ` accumulates the minimisers**: from `m₀` on, with every `K_{m₀+k}(A)`, `k ≤ n`, invertible and
`A ≥ 0` on every `V_{m₀+k}`, `Γ_{m₀+n} = Γ_{m₀} + Σ_{k<n} κ'_{m₀+k+1}⁻¹ β_k β_kᵀ`. -/
theorem Gam_eq_sum (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → p → ℝ) (m₀ : ℕ) :
    ∀ n, (∀ k ≤ n, IsUnit (K A r (m₀ + k)).det) → (∀ k ≤ n, ∀ u ∈ V r (m₀ + k), 0 ≤ qf A (m₀ + k) u) →
      Gam A r B (m₀ + n) = Gam A r B m₀ + ∑ k ∈ Finset.range n,
        (schur A r (m₀ + k))⁻¹ • vecMulVec (sv B (m₀ + k + 1) (amin A r (m₀ + k)))
          (sv B (m₀ + k + 1) (amin A r (m₀ + k))) := by
  intro n
  induction n with
  | zero => intro _ _; simp
  | succ n ih =>
    intro hK hpsd
    rw [Finset.sum_range_succ, ← add_assoc (Gam A r B m₀), ← ih (fun k hk => hK k (by omega)) (fun k hk => hpsd k (by omega))]
    exact Gam_succ A hA r B (hK n (by omega)) (hK (n + 1) le_rfl) (hpsd (n + 1) le_rfl)
/-- **The quartet kernels accumulate the minimisers**: with `F_k = β_k(0) + iβ_k(1)`, `β_k` the samples of the
minimiser at step `m₀ + k + 1`, `k₁ = Γ₀₀ + Γ₁₁` gains `Σ_k κ'⁻¹|F_k|²` and `k₂ = Γ₀₀ − Γ₁₁ + 2iΓ₀₁` gains
`Σ_k κ'⁻¹F_k²` from `Γ_{m₀}` to `Γ_{m₀+n}`. -/
theorem kernels_Gam (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ) (B : ℕ → Fin 2 → ℝ)
    (m₀ n : ℕ) (hK : ∀ k ≤ n, IsUnit (K A r (m₀ + k)).det)
    (hpsd : ∀ k ≤ n, ∀ u ∈ V r (m₀ + k), 0 ≤ qf A (m₀ + k) u) :
    Gam A r B (m₀ + n) 0 0 + Gam A r B (m₀ + n) 1 1 = Gam A r B m₀ 0 0 + Gam A r B m₀ 1 1
        + ∑ k ∈ Finset.range n, (schur A r (m₀ + k))⁻¹ * Complex.normSq
            (sv B (m₀ + k + 1) (amin A r (m₀ + k)) 0 + sv B (m₀ + k + 1) (amin A r (m₀ + k)) 1 * Complex.I) ∧
      ((Gam A r B (m₀ + n) 0 0 - Gam A r B (m₀ + n) 1 1 : ℝ) : ℂ)
          + ((2 * Gam A r B (m₀ + n) 0 1 : ℝ) : ℂ) * Complex.I
        = ((Gam A r B m₀ 0 0 - Gam A r B m₀ 1 1 : ℝ) : ℂ) + ((2 * Gam A r B m₀ 0 1 : ℝ) : ℂ) * Complex.I
          + ∑ k ∈ Finset.range n, (((schur A r (m₀ + k))⁻¹ : ℝ) : ℂ)
            * ((sv B (m₀ + k + 1) (amin A r (m₀ + k)) 0 : ℂ)
              + (sv B (m₀ + k + 1) (amin A r (m₀ + k)) 1 : ℂ) * Complex.I) ^ 2 := by
  obtain ⟨h1, h2⟩ := kernels_of_sum (Finset.range n) (fun k => (schur A r (m₀ + k))⁻¹)
    (fun k => sv B (m₀ + k + 1) (amin A r (m₀ + k)) 0) (fun k => sv B (m₀ + k + 1) (amin A r (m₀ + k)) 1)
  rw [Gam_eq_sum A hA r B m₀ n hK hpsd]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] at h1 h2 ⊢
  simp only [sq] at h1 h2 ⊢
  constructor
  · rw [← h1]; ring
  · rw [← h2]; push_cast; ring

/-! ### The single-quartet sign law -/

omit [Fintype p] [DecidableEq p] in
theorem sv_smul (B : ℕ → p → ℝ) (M : ℕ) (v : Fin (M + 1) → ℝ) (t : ℝ) : sv B M (t • v) = t • sv B M v := by
  funext a
  simp only [sv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem qf_smul (A : Matrix ℕ ℕ ℝ) (M : ℕ) (v : Fin (M + 1) → ℝ) (t : ℝ) :
    qf A M (t • v) = t ^ 2 * qf A M v := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

omit [DecidableEq p] in
/-- `Q = A + BCBᵀ` on the modes: `Q_M(v) = A_M(v) + (Bᵀv)ᵀ C (Bᵀv)`. -/
theorem qf_add_lowRank (A : Matrix ℕ ℕ ℝ) (B : ℕ → p → ℝ) (C : Matrix p p ℝ) (M : ℕ) (v : Fin (M + 1) → ℝ) :
    qf (A + lowRank B C) M v = qf A M v + sv B M v ⬝ᵥ (C *ᵥ sv B M v) := by
  set Bm : Matrix (Fin (M + 1)) p ℝ := Matrix.of fun i a => B i a
  have hL : (lowRank B C).submatrix Fin.val Fin.val = Bm * C * Bmᵀ := rfl
  have hsv : sv B M v = Bmᵀ *ᵥ v := by funext a; simp [sv, Bm, mulVec, dotProduct]
  have hmv : (Bm * C * Bmᵀ) *ᵥ v = Bm *ᵥ (C *ᵥ (Bmᵀ *ᵥ v)) := by
    rw [mulVec_mulVec, mulVec_mulVec]
  have h : qf (A + lowRank B C) M v = qf A M v + v ⬝ᵥ ((lowRank B C).submatrix Fin.val Fin.val *ᵥ v) := by
    simp only [qf]
    rw [show (A + lowRank B C).submatrix Fin.val Fin.val
      = A.submatrix Fin.val Fin.val + (lowRank B C).submatrix Fin.val Fin.val from rfl, add_mulVec, dotProduct_add]
  rw [h, hL, hmv, dotProduct_mulVec, ← mulVec_transpose, hsv]

theorem Cq_transpose (c : ℂ) : (Cq c)ᵀ = Cq c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Cq]

theorem det_Cq_neg {c : ℂ} (hc : c ≠ 0) : (Cq c).det < 0 := by
  rw [det_Cq]; have := Complex.normSq_pos.mpr hc; linarith

omit [Fintype κ] [DecidableEq κ] [Fintype p] [DecidableEq p] in
theorem mem_V_smul {r : κ → ℕ → ℝ} {M : ℕ} {v : Fin (M + 1) → ℝ} (hv : v ∈ V r M) (t : ℝ) : t • v ∈ V r M :=
  (V r M).smul_mem t hv

/-- **The single-quartet sign law**: for symmetric `A` with `A_M ≥ 0` on `V_M` and `K_M(A)` invertible, and a
symmetric `2 × 2` block `C` with `det C < 0`, `A + BCBᵀ ≥ 0` on `V_M` iff `det(C⁻¹ + Γ_M) ≤ 0`. -/
theorem quartet_nonneg_iff (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ)
    (B : ℕ → Fin 2 → ℝ) {C : Matrix (Fin 2) (Fin 2) ℝ} (hCs : Cᵀ = C) (hC : C.det < 0) {M : ℕ}
    (hK : IsUnit (K A r M).det) (hpsd : ∀ v ∈ V r M, 0 ≤ qf A M v) :
    (∀ v ∈ V r M, 0 ≤ qf (A + lowRank B C) M v) ↔ (C⁻¹ + Gam A r B M).det ≤ 0 := by
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC.ne
  have hCi : C⁻¹ᵀ = C⁻¹ := by rw [transpose_nonsing_inv, hCs]
  have hΓs : (Gam A r B M)ᵀ = Gam A r B M := Gam_symm A hA r B M
  have hGs : (C⁻¹ + Gam A r B M)ᵀ = C⁻¹ + Gam A r B M := by rw [transpose_add, hCi, hΓs]
  have hCC : ∀ y, C *ᵥ (C⁻¹ *ᵥ y) = y := fun y => by rw [mulVec_mulVec, mul_nonsing_inv _ hCu, one_mulVec]
  have symmC : ∀ x y : Fin 2 → ℝ, x ⬝ᵥ (C *ᵥ y) = y ⬝ᵥ (C *ᵥ x) := fun x y => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hCs, dotProduct_comm]
  constructor
  · intro hQ
    by_contra hd
    push Not at hd
    have hdetCi : (C⁻¹).det < 0 := by
      rw [det_nonsing_inv, Ring.inverse_eq_inv']
      exact inv_lt_zero.mpr hC
    obtain ⟨e, he⟩ := exists_pos_of_det_neg hCi hdetCi
    have hGe : 0 < e ⬝ᵥ ((C⁻¹ + Gam A r B M) *ᵥ e) := by
      rw [add_mulVec, dotProduct_add]; linarith [Gam_psd A hA r B hK hpsd e]
    have hGu : IsUnit (C⁻¹ + Gam A r B M).det := isUnit_iff_ne_zero.mpr hd.ne'
    obtain ⟨z, hz⟩ := exists_neg_of_det_neg hCs hC
    have hGy : (C⁻¹ + Gam A r B M) *ᵥ ((C⁻¹ + Gam A r B M)⁻¹ *ᵥ z) = z := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hGu, one_mulVec]
    set y := (C⁻¹ + Gam A r B M)⁻¹ *ᵥ z with hydef
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, mulVec_zero] at hGy
      rw [← hGy] at hz
      simp at hz
    have hpos := pos_of_det_pos hGs hd hGe hy0
    rw [hGy] at hpos
    have hg : Gam A r B M *ᵥ y = z - C⁻¹ *ᵥ y := by
      rw [← hGy, add_mulVec]; abel
    have hCg : C *ᵥ (Gam A r B M *ᵥ y) = C *ᵥ z - y := by rw [hg, mulVec_sub, hCC]
    have e1 : (C⁻¹ *ᵥ y) ⬝ᵥ (C *ᵥ z) = z ⬝ᵥ y := by rw [symmC, hCC]
    have p1 : y ⬝ᵥ (Gam A r B M *ᵥ y) = y ⬝ᵥ z - y ⬝ᵥ (C⁻¹ *ᵥ y) := by rw [hg, dotProduct_sub]
    have p2 : (Gam A r B M *ᵥ y) ⬝ᵥ (C *ᵥ (Gam A r B M *ᵥ y))
        = z ⬝ᵥ (C *ᵥ z) - z ⬝ᵥ y - (z ⬝ᵥ y - (C⁻¹ *ᵥ y) ⬝ᵥ y) := by
      rw [hCg, dotProduct_sub, hg, sub_dotProduct, sub_dotProduct, e1]
    have c1 : y ⬝ᵥ z = z ⬝ᵥ y := dotProduct_comm _ _
    have c2 : y ⬝ᵥ (C⁻¹ *ᵥ y) = (C⁻¹ *ᵥ y) ⬝ᵥ y := dotProduct_comm _ _
    have hval := hQ _ (gmin_mem B hK y)
    rw [qf_add_lowRank, qf_gmin A hA r B hK, ← Gam_mulVec] at hval
    linarith
  · intro hd v hv
    by_contra hneg
    push Not at hneg
    rw [qf_add_lowRank] at hneg
    have ha := hpsd v hv
    have hσ : sv B M v ⬝ᵥ (C *ᵥ sv B M v) < -qf A M v := by linarith
    have hσ0 : sv B M v ⬝ᵥ (C *ᵥ sv B M v) < 0 := by linarith
    have hGpd : ∀ u : Fin 2 → ℝ, u ≠ 0 → 0 < u ⬝ᵥ ((C⁻¹ + Gam A r B M) *ᵥ u) := by
      intro u hu
      have hCz : C *ᵥ (C⁻¹ *ᵥ u) = u := hCC u
      set z := C⁻¹ *ᵥ u with hzdef
      have hz0 : z ≠ 0 := by
        intro h; rw [h, mulVec_zero] at hCz; exact hu hCz.symm
      have hβ : u ⬝ᵥ sv B M v = z ⬝ᵥ (C *ᵥ sv B M v) := by
        rw [symmC, ← hCz, dotProduct_comm]
      have hc : u ⬝ᵥ (C⁻¹ *ᵥ u) = z ⬝ᵥ (C *ᵥ z) := by rw [hCz, dotProduct_comm]
      have hrev := rev_cs hCs z (sv B M v)
      have hΓt : ∀ t : ℝ, 2 * t * (u ⬝ᵥ sv B M v) - t ^ 2 * qf A M v ≤ u ⬝ᵥ (Gam A r B M *ᵥ u) := by
        intro t
        have := (quad_Gam_isGreatest A hA r B hK hpsd u).2 ⟨t • v, mem_V_smul hv t, rfl⟩
        rw [sv_smul, qf_smul, dotProduct_smul, smul_eq_mul] at this
        linarith
      rw [add_mulVec, dotProduct_add, hc]
      have hdC : 0 < -C.det := by linarith
      by_cases hβ0 : u ⬝ᵥ sv B M v = 0
      · have hgg : 0 ≤ u ⬝ᵥ (Gam A r B M *ᵥ u) := Gam_psd A hA r B hK hpsd u
        rw [hβ0] at hβ
        rw [← hβ] at hrev
        have hc0 : 0 ≤ z ⬝ᵥ (C *ᵥ z) := by
          by_contra hn
          push Not at hn
          nlinarith [sq_nonneg (z 0 * sv B M v 1 - z 1 * sv B M v 0), mul_pos_of_neg_of_neg hn hσ0]
        have hc1 : z ⬝ᵥ (C *ᵥ z) ≠ 0 := by
          intro h0
          rw [h0] at hrev
          have hx : z 0 * sv B M v 1 - z 1 * sv B M v 0 = 0 := by
            have : -C.det * (z 0 * sv B M v 1 - z 1 * sv B M v 0) ^ 2 = 0 := by linarith
            rcases mul_eq_zero.mp this with h | h
            · exact absurd h hdC.ne'
            · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
          have hw : z ⬝ᵥ (C *ᵥ sv B M v) = z 0 * (C *ᵥ sv B M v) 0 + z 1 * (C *ᵥ sv B M v) 1 := by
            simp [dotProduct, Fin.sum_univ_two]
          have hs : sv B M v ⬝ᵥ (C *ᵥ sv B M v)
              = sv B M v 0 * (C *ᵥ sv B M v) 0 + sv B M v 1 * (C *ᵥ sv B M v) 1 := by
            simp [dotProduct, Fin.sum_univ_two]
          have hzw : z 0 * (C *ᵥ sv B M v) 0 + z 1 * (C *ᵥ sv B M v) 1 = 0 := by rw [← hw, ← hβ]
          have h0' : z 0 = 0 := by
            have : z 0 * (sv B M v ⬝ᵥ (C *ᵥ sv B M v)) = 0 := by
              rw [hs]
              linear_combination (sv B M v 0) * hzw + (C *ᵥ sv B M v) 1 * hx
            rcases mul_eq_zero.mp this with h | h
            · exact h
            · exact absurd h hσ0.ne
          have h1' : z 1 = 0 := by
            have : z 1 * (sv B M v ⬝ᵥ (C *ᵥ sv B M v)) = 0 := by
              rw [hs]
              linear_combination (sv B M v 1) * hzw - (C *ᵥ sv B M v) 0 * hx
            rcases mul_eq_zero.mp this with h | h
            · exact h
            · exact absurd h hσ0.ne
          exact hz0 (funext fun i => by fin_cases i <;> simp [h0', h1'])
        have := lt_of_le_of_ne hc0 (Ne.symm hc1)
        linarith
      · set β := u ⬝ᵥ sv B M v
        set σ := sv B M v ⬝ᵥ (C *ᵥ sv B M v)
        set a := qf A M v
        set c := z ⬝ᵥ (C *ᵥ z)
        set g := u ⬝ᵥ (Gam A r B M *ᵥ u)
        have h1 := hΓt (-β / σ)
        have hσne : σ ≠ 0 := hσ0.ne
        have e : (2 * (-β / σ) * β - (-β / σ) ^ 2 * a) * σ ^ 2 = β ^ 2 * (-2 * σ - a) := by
          field_simp
        have h1' := mul_le_mul_of_nonneg_right h1 (sq_nonneg σ)
        rw [e] at h1'
        have hcσ : c * σ ≤ β ^ 2 := by
          rw [← hβ] at hrev
          nlinarith [sq_nonneg (z 0 * sv B M v 1 - z 1 * sv B M v 0)]
        have hβ2 : 0 < β ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hβ0))
        have hσ2 : 0 < σ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hσne))
        have k1 : c * σ ^ 2 ≥ β ^ 2 * σ := by nlinarith
        have k2 : g * σ ^ 2 > -σ * β ^ 2 := by nlinarith [mul_pos hβ2 (show 0 < -σ - a by linarith)]
        have : 0 < (c + g) * σ ^ 2 := by nlinarith
        exact pos_of_mul_pos_left this hσ2.le
    exact absurd hd (not_le.mpr (det_pos_of_pos hGs hGpd))

/-- **A form that is nonnegative off one linear condition has negative index at most one.** -/
theorem sigNeg_le_one {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (q : QuadraticForm ℝ E) (φ : E →ₗ[ℝ] ℝ) (h : ∀ v, φ v = 0 → 0 ≤ q v) : sigNeg q ≤ 1 := by
  have h1 := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -q) (V := LinearMap.ker φ)
    fun x hx => by
      rw [_root_.neg_apply]; linarith [h x (LinearMap.mem_ker.mp hx)]
  rw [sigPos_neg] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  have h3 : Module.finrank ℝ (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  omega

theorem exists_kernel_nonneg {C : Matrix (Fin 2) (Fin 2) ℝ} (hCs : Cᵀ = C) (hC : C.det < 0) :
    ∃ ψ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ, ∀ s, ψ s = 0 → 0 ≤ s ⬝ᵥ (C *ᵥ s) := by
  have h10 := symm_10 hCs
  rw [det_fin_two, h10] at hC
  by_cases h00 : 0 ≤ C 0 0
  · refine ⟨LinearMap.proj 1, fun s hs => ?_⟩
    simp only [LinearMap.coe_proj, Function.eval] at hs
    rw [quad_two, hs]; nlinarith [sq_nonneg (s 0)]
  · push Not at h00
    refine ⟨C 0 0 • LinearMap.proj 0 + C 0 1 • LinearMap.proj 1, fun s hs => ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, smul_eq_mul] at hs
    rw [quad_two, h10]
    have key : C 0 0 * (C 0 0 * s 0 ^ 2 + (C 0 1 + C 0 1) * (s 0 * s 1) + C 1 1 * s 1 ^ 2)
        = (C 0 0 * s 0 + C 0 1 * s 1) ^ 2 + (C 0 0 * C 1 1 - C 0 1 * C 0 1) * s 1 ^ 2 := by ring
    rw [hs] at key
    nlinarith [sq_nonneg (s 1)]

/-- The low-rank samples as a linear map. -/
def svLin (B : ℕ → p → ℝ) (M : ℕ) : (Fin (M + 1) → ℝ) →ₗ[ℝ] (p → ℝ) where
  toFun := sv B M
  map_add' v w := by simpa using sv_add_smul B M v w 1
  map_smul' t v := sv_smul B M v t

/-- **The single-quartet inertia law**: under the hypotheses of `quartet_nonneg_iff`, the negative index of
`A + BCBᵀ` on `V_M` is `1` if `det(C⁻¹ + Γ_M) > 0` and `0` otherwise. -/
theorem quartet_sigNeg (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ)
    (B : ℕ → Fin 2 → ℝ) {C : Matrix (Fin 2) (Fin 2) ℝ} (hCs : Cᵀ = C) (hC : C.det < 0) {M : ℕ}
    (hK : IsUnit (K A r M).det) (hpsd : ∀ v ∈ V r M, 0 ≤ qf A M v) :
    sigNeg ((Cvs.Upstream.PivotChainInertia.qform (blk (A + lowRank B C) M)).restrict (V r M))
      = if 0 < (C⁻¹ + Gam A r B M).det then 1 else 0 := by
  have hiff := quartet_nonneg_iff A hA r B hCs hC hK hpsd
  split_ifs with hd
  · refine le_antisymm ?_ ?_
    · obtain ⟨ψ, hψ⟩ := exists_kernel_nonneg hCs hC
      refine sigNeg_le_one _ (ψ ∘ₗ svLin B M ∘ₗ (V r M).subtype) fun v hv => ?_
      rw [Cvs.Upstream.PivotChainInertia.qform_restrict_apply, qf_add_lowRank]
      have := hψ (sv B M v) hv
      linarith [hpsd v v.2]
    · have hn : ¬ ∀ v ∈ V r M, 0 ≤ qf (A + lowRank B C) M v := fun h => absurd (hiff.mp h) (not_le.mpr hd)
      have hne : sigNeg ((Cvs.Upstream.PivotChainInertia.qform (blk (A + lowRank B C) M)).restrict (V r M)) ≠ 0 := by
        rw [Ne, ← Cvs.Upstream.PivotChainInertia.nonneg_iff_sigNeg]; exact hn
      omega
  · push Not at hd
    exact (Cvs.Upstream.PivotChainInertia.nonneg_iff_sigNeg _ r M).mp (hiff.mpr hd)

/-- **The single-quartet test for `C = Cq c`**: with `k₁ = tr Γ_M` and `k₂ = Γ₁₁ − Γ₂₂ + 2iΓ₁₂`,
`A + B (Cq c) Bᵀ ≥ 0` on `V_M` iff `|c|²k₁² ≤ |1 + c k₂|²`. -/
theorem quartet_Cq_nonneg_iff (A : Matrix ℕ ℕ ℝ) (hA : ∀ i j, A j i = A i j) (r : κ → ℕ → ℝ)
    (B : ℕ → Fin 2 → ℝ) {c : ℂ} (hc : c ≠ 0) {M : ℕ} (hK : IsUnit (K A r M).det)
    (hpsd : ∀ v ∈ V r M, 0 ≤ qf A M v) :
    (∀ v ∈ V r M, 0 ≤ qf (A + lowRank B (Cq c)) M v) ↔
      Complex.normSq c * (Gam A r B M 0 0 + Gam A r B M 1 1) ^ 2
        ≤ Complex.normSq (1 + c * (((Gam A r B M 0 0 - Gam A r B M 1 1 : ℝ) : ℂ)
            + ((2 * Gam A r B M 0 1 : ℝ) : ℂ) * Complex.I)) := by
  rw [quartet_nonneg_iff A hA r B (Cq_transpose c) (det_Cq_neg hc) hK hpsd]
  have h10 : Gam A r B M 1 0 = Gam A r B M 0 1 := symm_10 (Gam_symm A hA r B M)
  have hG : Gam A r B M = !![Gam A r B M 0 0, Gam A r B M 0 1; Gam A r B M 0 1, Gam A r B M 1 1] := by
    exact (eta_fin_two _).trans (by rw [h10])
  have hq := det_quartet_inv hc (Gam A r B M 0 0) (Gam A r B M 0 1) (Gam A r B M 1 1)
  rw [← hG, det_smul, Fintype.card_fin] at hq
  have hn : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
  constructor
  · intro hd
    have : (2 * Complex.normSq c) ^ 2 * ((Cq c)⁻¹ + Gam A r B M).det / Complex.normSq c ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hd) hn.le
    linarith
  · intro h
    have h2 : (2 * Complex.normSq c) ^ 2 * ((Cq c)⁻¹ + Gam A r B M).det / Complex.normSq c ≤ 0 := by linarith
    rw [div_nonpos_iff] at h2
    rcases h2 with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact absurd h2 (not_le.mpr hn)
    · by_contra hpos
      push Not at hpos
      have : 0 < (2 * Complex.normSq c) ^ 2 * ((Cq c)⁻¹ + Gam A r B M).det :=
        mul_pos (by positivity) hpos
      linarith

/-! ### Witnesses: the hypotheses hold, on both sides of the test -/

/-- The empty constraint family. -/
def noRows : Empty → ℕ → ℝ := fun e => e.elim

theorem K_one_noRows (M : ℕ) : K (1 : Matrix ℕ ℕ ℝ) noRows M = 1 := by
  ext x y
  rcases x with i | e
  · rcases y with j | e
    · simp [K, bord, blk, Matrix.one_apply, Fin.val_inj]
    · exact e.elim
  · exact e.elim

theorem isUnit_K_one_noRows (M : ℕ) : IsUnit (K (1 : Matrix ℕ ℕ ℝ) noRows M).det := by
  rw [K_one_noRows, det_one]; exact isUnit_one

theorem qf_one_nonneg (M : ℕ) (v : Fin (M + 1) → ℝ) : 0 ≤ qf (1 : Matrix ℕ ℕ ℝ) M v := by
  have h : (1 : Matrix ℕ ℕ ℝ).submatrix (Fin.val : Fin (M + 1) → ℕ) Fin.val = 1 :=
    submatrix_one _ Fin.val_injective
  simp only [qf, h, one_mulVec, dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem mem_V_noRows (M : ℕ) (v : Fin (M + 1) → ℝ) : v ∈ V noRows M := by
  rw [mem_V]; funext e; exact e.elim

/-- The quartet columns of the negative witness: `B_m = (0, 2)` for every mode `m`. -/
def Bneg : ℕ → Fin 2 → ℝ := fun _ => ![0, 2]

/-- **The quartet test is not vacuous**: with no constraints, `A = 1` and `C = Cq 1 = diag(2, −2)`, every
hypothesis of `quartet_nonneg_iff` holds, `B = 0` gives `det(C⁻¹ + Γ_0) ≤ 0` and a nonnegative form, and
`B_m = (0, 2)` gives `det(C⁻¹ + Γ_0) > 0` and a negative value. -/
theorem quartet_witness :
    IsUnit (K (1 : Matrix ℕ ℕ ℝ) noRows 0).det ∧ (∀ v ∈ V noRows 0, 0 ≤ qf (1 : Matrix ℕ ℕ ℝ) 0 v) ∧
      (Cq 1)ᵀ = Cq 1 ∧ (Cq 1).det < 0 ∧
      ((Cq 1)⁻¹ + Gam (1 : Matrix ℕ ℕ ℝ) noRows (fun _ _ => (0 : ℝ)) 0).det ≤ 0 ∧
      0 < ((Cq 1)⁻¹ + Gam (1 : Matrix ℕ ℕ ℝ) noRows Bneg 0).det := by
  have hA : ∀ i j, (1 : Matrix ℕ ℕ ℝ) j i = (1 : Matrix ℕ ℕ ℝ) i j := fun i j => by
    simp [Matrix.one_apply, eq_comm]
  have hc : (1 : ℂ) ≠ 0 := by norm_num
  have hK := isUnit_K_one_noRows 0
  have hpsd : ∀ v ∈ V noRows 0, 0 ≤ qf (1 : Matrix ℕ ℕ ℝ) 0 v := fun v _ => qf_one_nonneg 0 v
  refine ⟨hK, hpsd, Cq_transpose _, det_Cq_neg hc, ?_, ?_⟩
  · refine (quartet_nonneg_iff 1 hA noRows _ (Cq_transpose _) (det_Cq_neg hc) hK hpsd).mp fun v _ => ?_
    rw [qf_add_lowRank]
    have : sv (fun (_ : ℕ) (_ : Fin 2) => (0 : ℝ)) 0 v = 0 := by funext a; simp [sv]
    rw [this, mulVec_zero, dotProduct_zero, add_zero]
    exact qf_one_nonneg 0 v
  · by_contra h
    push Not at h
    have := (quartet_nonneg_iff 1 hA noRows Bneg (Cq_transpose _) (det_Cq_neg hc) hK hpsd).mpr h
      (fun _ => 1) (mem_V_noRows 0 _)
    rw [qf_add_lowRank] at this
    have h1 : qf (1 : Matrix ℕ ℕ ℝ) 0 (fun _ => 1) = 1 := by
      simp [qf, dotProduct, mulVec, Matrix.one_apply]
    have h2 : sv Bneg 0 (fun _ => 1) = ![0, 2] := by
      funext a; fin_cases a <;> simp [sv, Bneg]
    rw [h1, h2] at this
    norm_num [Cq, dotProduct, mulVec, Fin.sum_univ_two] at this

/-- **The hypotheses of the quartet law hold together**: at `A = 1`, no constraints, `C = Cq 1` and
`B_m = (0, 2)`, the matrices `C`, `K_0(A)`, `K_1(A)` and `C⁻¹ + Γ_0` are all invertible. -/
theorem lowRank_witness :
    IsUnit (Cq 1).det ∧ IsUnit (K (1 : Matrix ℕ ℕ ℝ) noRows 0).det ∧ IsUnit (K (1 : Matrix ℕ ℕ ℝ) noRows 1).det ∧
      IsUnit ((Cq 1)⁻¹ + Gam (1 : Matrix ℕ ℕ ℝ) noRows Bneg 0).det :=
  ⟨isUnit_iff_ne_zero.mpr (det_Cq_neg one_ne_zero).ne, isUnit_K_one_noRows 0, isUnit_K_one_noRows 1,
    isUnit_iff_ne_zero.mpr quartet_witness.2.2.2.2.2.ne'⟩

end Chain

/-! ### The zero side of the cosine-mode window form -/

section ZeroSide

open Cvs.Upstream.ConstrainedFormPivotChain (cosQ ofCos qf_cosQ ofCos_even qf)

/-- **The cosine-mode window form as a zero sum**: at `1 < x`,
`log x · Q_N(a) = Σ_ρ m_ρ ((∫ g ue_ρ)² − (∫ g ve_ρ)²)` with `g` the cosine polynomial of `ofCos a` centred at
`log x / 2` and `Q = cosQ x`. -/
theorem log_mul_qf_cosQ {x : ℕ} (hx1 : (1 : ℝ) < x) (N : ℕ) (a : Fin (N + 1) → ℝ) :
    Real.log x * qf (cosQ x) N a = ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
      (Cvs.Criterion.divisorWeight rho : ℝ) *
        ((∫ t in -(Real.log x / 2)..Real.log x / 2,
            Cvs.Finite.EvenSectorZeroSide.cosPoly (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) (ofCos N a) (t + Real.log x / 2)
              * Cvs.StepA.OneZeroParitySectors.ue (Cvs.ZeroCounting.zPoint rho) t) ^ 2
          - (∫ t in -(Real.log x / 2)..Real.log x / 2,
            Cvs.Finite.EvenSectorZeroSide.cosPoly (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) (ofCos N a) (t + Real.log x / 2)
              * Cvs.StepA.OneZeroParitySectors.ve (Cvs.ZeroCounting.zPoint rho) t) ^ 2) := by
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hx0 : 0 < x := by exact_mod_cast (zero_lt_one.trans hx1)
  rw [← qf_cosQ hx1]
  have h := Cvs.StepA.OneZeroParitySectors.quadForm_even_eq_pairings hL (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.SymmetricModeSet.mode_negI N) (ofCos_even N a)
  rw [Cvs.StepA.OddBottomGapCriterion.ceil_exp_log_natCast hx0, Cvs.Route.EigenvectorCoordinateCompression.natCeil_log_div_log_two_eq_clog] at h
  exact h

/-- **An on-line zero contributes a square**: if `Re ρ = 1/2`, its term is `m_ρ (∫ g ue_ρ)² ≥ 0`. -/
theorem zeroTerm_onLine {rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet} (h : (rho : ℂ).re = 1 / 2) (L : ℝ)
    (g : ℝ → ℝ) :
    (∫ t in -(L / 2)..L / 2, g t * Cvs.StepA.OneZeroParitySectors.ve (Cvs.ZeroCounting.zPoint rho) t) = 0 := by
  have : ∀ t, g t * Cvs.StepA.OneZeroParitySectors.ve (Cvs.ZeroCounting.zPoint rho) t = 0 := fun t => by
    rw [Cvs.StepA.OneZeroParitySectors.ve_eq_zero (Or.inr (Cvs.StepA.OneZeroParitySectors.zPoint_im_eq_zero h)), mul_zero]
  simp [this]

/-- **Each zero's term is a quartet block**: `P² − Q² = (P, Q) Cq(1/2) (P, Q)ᵀ = Re (P + iQ)²`. -/
theorem sq_sub_sq_eq_Cq (P Q : ℝ) : P ^ 2 - Q ^ 2 = ![P, Q] ⬝ᵥ (Cq (1 / 2) *ᵥ ![P, Q]) := by
  rw [quad_Cq]
  simp [Complex.mul_re, sq]

end ZeroSide

end Cvs.StepA.PivotChainQuartetLaw
