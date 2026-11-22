import Mathlib
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.StepA.OddAboveDisplacement
import Cvs.Upstream.SchurSylvesterDisplacement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The bordered displacement and the compressed displacement rank

For `K = [[Q, U], [Uᵀ, 0]]` with `AQ − QAᵀ = GJGᵀ`, `AU − UBᵀ = YZᵀ`: `ΩK − KΩᵀ = ĜĴĜᵀ`, `Ĝ = [[G, Y, 0], [0, 0, Z]]`.
A symmetric idempotent `P` with `PD(1 − P) = YZᵀ` (`m` columns) compresses `P(DM − MD)P = P GJGᵀ P` to a commutator
of rank `≤ |G| + 2m`. On `Cvs.Finite.TruncationQuadraticForm.M`, `diag(ω²)M − M diag(ω²)` has rank two on the even sector, so `P = E_ev − UUᵀ`
gives rank `≤ 2 + 2r`, and `≤ 2r` when `P𝟙 ∈ span(PDU)`, as when `P` kills `v_F`, `v_{F″}` and `F′(L) ≠ F′(0)`.
-/

noncomputable section

open Matrix

namespace Cvs.Upstream.BorderedDisplacementRank
open Cvs.ZeroCounting

/-! ### The bordered displacement -/

section Bordered

variable {R : Type*} [CommRing R] {n r p m : Type*} [Fintype n] [Fintype r] [Fintype p] [Fintype m]
  [DecidableEq m]

/-- The symplectic block `[[0, 1], [−1, 0]]` on `m ⊕ m`. -/
def sympBlock (R : Type*) [CommRing R] (m : Type*) [DecidableEq m] : Matrix (m ⊕ m) (m ⊕ m) R :=
  fromBlocks 0 1 (-1) 0

/-- The bordered generator `Ĝ = [[G, Y, 0], [0, 0, Z]]`. -/
def borderGen (G : Matrix n p R) (Y : Matrix n m R) (Z : Matrix r m R) : Matrix (n ⊕ r) (p ⊕ (m ⊕ m)) R :=
  fromBlocks G (fromCols Y 0) 0 (fromCols 0 Z)

/-- The bordered form `Ĵ = J ⊕ [[0, 1], [−1, 0]]`. -/
def borderJ (m : Type*) [DecidableEq m] (J : Matrix p p R) : Matrix (p ⊕ (m ⊕ m)) (p ⊕ (m ⊕ m)) R :=
  fromBlocks J 0 0 (sympBlock R m)

omit [Fintype n] [Fintype r] [Fintype p] [Fintype m] in
/-- The bordered form is antisymmetric when `J` is. -/
theorem borderJ_transpose {J : Matrix p p R} (hJ : Jᵀ = -J) : (borderJ m J)ᵀ = -borderJ m J := by
  rw [borderJ, sympBlock, fromBlocks_transpose, fromBlocks_transpose, fromBlocks_neg, fromBlocks_neg, hJ]
  simp

omit [Fintype n] [Fintype r] in
/-- `ĜĴĜᵀ = [[GJGᵀ, YZᵀ], [−ZYᵀ, 0]]`. -/
theorem borderGen_mul_borderJ_mul (G : Matrix n p R) (J : Matrix p p R) (Y : Matrix n m R) (Z : Matrix r m R) :
    borderGen G Y Z * borderJ m J * (borderGen G Y Z)ᵀ
      = fromBlocks (G * J * Gᵀ) (Y * Zᵀ) (-(Z * Yᵀ)) 0 := by
  simp [borderGen, borderJ, sympBlock, fromBlocks_transpose, fromBlocks_multiply, transpose_fromCols,
    fromCols_mul_fromBlocks, fromCols_mul_fromRows]

/-- **The bordered displacement**: `Ω = A ⊕ B`, `K = [[Q, U], [Uᵀ, 0]]`, `AQ − QAᵀ = GJGᵀ` and `AU − UBᵀ = YZᵀ`
give `ΩK − KΩᵀ = ĜĴĜᵀ`. -/
theorem bordered_displacement {A Q : Matrix n n R} {B : Matrix r r R} {U : Matrix n r R} {G : Matrix n p R}
    {J : Matrix p p R} {Y : Matrix n m R} {Z : Matrix r m R}
    (hQ : A * Q - Q * Aᵀ = G * J * Gᵀ) (hU : A * U - U * Bᵀ = Y * Zᵀ) :
    fromBlocks A 0 0 B * fromBlocks Q U Uᵀ 0 - fromBlocks Q U Uᵀ 0 * (fromBlocks A 0 0 B)ᵀ
      = borderGen G Y Z * borderJ m J * (borderGen G Y Z)ᵀ := by
  rw [borderGen_mul_borderJ_mul, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    Cvs.Upstream.SchurSylvesterDisplacement.fromBlocks_sub_fromBlocks]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, transpose_zero, sub_self]
  have hU' : B * Uᵀ - Uᵀ * Aᵀ = -(Z * Yᵀ) := by
    have := congrArg transpose hU
    simp only [transpose_sub, transpose_mul, transpose_transpose] at this
    rw [← this]; abel
  rw [hQ, hU, hU']

omit [Fintype n] [Fintype r] [Fintype p] [Fintype m] [DecidableEq m] in
/-- With `A = diag u`, the block-diagonal `Ω = diag u ⊕ B` has no blocks between a composite index set `T`
containing every constraint index and its complement. -/
theorem blockDiag_border [DecidableEq n] (u : n → R) (B : Matrix r r R) (p : n ⊕ r → Prop) [DecidablePred p]
    (hp : ∀ c, p (Sum.inr c)) : Cvs.Upstream.SchurSylvesterDisplacement.BlockDiag p (fromBlocks (diagonal u) 0 0 B) := by
  constructor
  · ext ⟨i, hi⟩ ⟨j, hj⟩
    rcases i with a | c <;> rcases j with b | d
    · have hab : a ≠ b := fun h => hj (h ▸ hi)
      simp [Matrix.toBlock, hab]
    · exact absurd (hp d) hj
    · simp [Matrix.toBlock]
    · exact absurd (hp d) hj
  · ext ⟨i, hi⟩ ⟨j, hj⟩
    rcases i with a | c <;> rcases j with b | d
    · have hab : a ≠ b := fun h => hi (h ▸ hj)
      simp [Matrix.toBlock, hab]
    · simp [Matrix.toBlock]
    · exact absurd (hp c) hi
    · exact absurd (hp c) hi

omit [Fintype n] [Fintype r] [Fintype p] [Fintype m] [DecidableEq m] in
/-- On the kept modes `F = {¬ T}`, `T ⊇` every constraint index, the block `Ω_FF` of `diag u ⊕ B` is the diagonal
of `u`. -/
theorem toBlock_border_diagonal [DecidableEq n] [DecidableEq r] (u : n → R) (B : Matrix r r R)
    (T : n ⊕ r → Prop) [DecidablePred T] (hT : ∀ c, T (Sum.inr c)) :
    (fromBlocks (diagonal u) 0 0 B).toBlock (¬ T ·) (¬ T ·)
      = diagonal fun j : {j // ¬ T j} => Sum.elim u (fun _ => 0) j.1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rcases i with a | c
  · rcases j with b | d
    · by_cases hab : a = b
      · subst hab; simp [Matrix.toBlock]
      · simp [Matrix.toBlock, hab]
    · exact absurd (hT d) hj
  · exact absurd (hT c) hi

/-- **The composite first step of the bordered recursion**: eliminating a block `T` containing every constraint index
from `K = [[Q, U], [Uᵀ, 0]]` (symmetric `Q`, `diag(u)Q − Q diag(u) = GJGᵀ`, `diag(u)U − UBᵀ = YZᵀ`) leaves a Schur
complement with `diag(u_F) S − S diag(u_F) = G̃ĴG̃ᵀ`, `G̃ = Ĝ_F − K_FT K_TT⁻¹ Ĝ_T`. -/
theorem bordered_elim [DecidableEq n] [DecidableEq r] {u : n → R} {Q : Matrix n n R} {B : Matrix r r R}
    {U : Matrix n r R} {G : Matrix n p R} {J : Matrix p p R} {Y : Matrix n m R} {Z : Matrix r m R} (hQs : Qᵀ = Q)
    (hQ : diagonal u * Q - Q * diagonal u = G * J * Gᵀ) (hU : diagonal u * U - U * Bᵀ = Y * Zᵀ)
    (T : n ⊕ r → Prop) [DecidablePred T] (hT : ∀ c, T (Sum.inr c)) :
    diagonal (fun j : {j // ¬ T j} => Sum.elim u (fun _ => 0) j.1) * Cvs.Upstream.SchurSylvesterDisplacement.elim T (fromBlocks Q U Uᵀ 0)
        - Cvs.Upstream.SchurSylvesterDisplacement.elim T (fromBlocks Q U Uᵀ 0) * diagonal (fun j : {j // ¬ T j} => Sum.elim u (fun _ => 0) j.1)
      = Cvs.Upstream.SchurSylvesterDisplacement.elimGen T (fromBlocks Q U Uᵀ 0) (borderGen G Y Z) * borderJ m J
          * (Cvs.Upstream.SchurSylvesterDisplacement.elimGen T (fromBlocks Q U Uᵀ 0) (borderGen G Y Z))ᵀ := by
  have hKs : (fromBlocks Q U Uᵀ 0)ᵀ = fromBlocks Q U Uᵀ 0 := by
    rw [fromBlocks_transpose, hQs, transpose_transpose, transpose_zero]
  have hQ' : diagonal u * Q - Q * (diagonal u)ᵀ = G * J * Gᵀ := by rw [diagonal_transpose, hQ]
  have h := Cvs.Upstream.SchurSylvesterDisplacement.elim_displacement (blockDiag_border u B T hT) hKs (bordered_displacement hQ' hU)
  rw [toBlock_border_diagonal u B T hT, diagonal_transpose] at h
  exact h

end Bordered

/-! ### The constraint equation: Krylov and orthonormal bases -/

section Constraint

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- The Krylov basis `U_j = (D − σ)^{r−j} ξ`, `j ≤ r`. -/
def krylov (D : Matrix n n R) (σ : R) (ξ : n → R) (r : ℕ) : Matrix n (Fin (r + 1)) R :=
  Matrix.of fun i j => ((D - σ • (1 : Matrix n n R)) ^ (r - (j : ℕ)) *ᵥ ξ) i

/-- The shifted lower shift `B = σ + N`, `N_{j, j−1} = 1`. -/
def shiftB (σ : R) (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  σ • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    + Matrix.of fun (i j : Fin (r + 1)) => if (i : ℕ) = (j : ℕ) + 1 then (1 : R) else 0

/-- **The Krylov constraint equation**: `DU − UBᵀ = ((D − σ)^{r+1}ξ) e₀ᵀ`. -/
theorem krylov_constraint (D : Matrix n n R) (σ : R) (ξ : n → R) (r : ℕ) :
    D * krylov D σ ξ r - krylov D σ ξ r * (shiftB σ r)ᵀ
      = (Matrix.of (fun i (_ : Unit) => ((D - σ • (1 : Matrix n n R)) ^ (r + 1) *ᵥ ξ) i) : Matrix n Unit R)
        * (Matrix.of fun (j : Fin (r + 1)) (_ : Unit) => if (j : ℕ) = 0 then (1 : R) else 0 : Matrix (Fin (r + 1)) Unit R)ᵀ := by
  set v : ℕ → n → R := fun k => (D - σ • (1 : Matrix n n R)) ^ k *ᵥ ξ
  have hcol : ∀ k : ℕ, D *ᵥ v k = v (k + 1) + σ • v k := by
    intro k
    simp only [v]
    rw [pow_succ', ← mulVec_mulVec, sub_mulVec, smul_mulVec, one_mulVec, sub_add_cancel]
  ext i j
  have h1 : (D * krylov D σ ξ r) i j = (D *ᵥ v (r - (j : ℕ))) i := by
    simp only [Matrix.mul_apply, krylov, of_apply, v, mulVec, dotProduct]
  have h2 : (krylov D σ ξ r * (shiftB σ r)ᵀ) i j
      = σ * v (r - (j : ℕ)) i + ∑ l : Fin (r + 1), if (j : ℕ) = (l : ℕ) + 1 then v (r - (l : ℕ)) i else 0 := by
    simp only [Matrix.mul_apply, krylov, shiftB, transpose_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, of_apply,
      smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, v]
    congr 1
    rw [Finset.sum_ite_eq]; simp [mul_comm]
  have h3 : ((Matrix.of (fun i (_ : Unit) => ((D - σ • (1 : Matrix n n R)) ^ (r + 1) *ᵥ ξ) i) : Matrix n Unit R)
        * (Matrix.of fun (j : Fin (r + 1)) (_ : Unit) => if (j : ℕ) = 0 then (1 : R) else 0 :
          Matrix (Fin (r + 1)) Unit R)ᵀ) i j
      = if (j : ℕ) = 0 then v (r + 1) i else 0 := by
    simp [Matrix.mul_apply, v]
  rw [Matrix.sub_apply, h1, h2, h3, hcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : (j : ℕ) = 0
  · have : ∀ x : Fin (r + 1), ¬ ((j : ℕ) = (x : ℕ) + 1) := fun x => by omega
    rw [Finset.sum_eq_zero (fun x _ => ite_eq_right (this x)), ite_eq_left hj, hj, Nat.sub_zero]
    ring
  · obtain ⟨j', hj'⟩ : ∃ j' : Fin (r + 1), (j : ℕ) = (j' : ℕ) + 1 := ⟨⟨(j : ℕ) - 1, by omega⟩, by simp; omega⟩
    rw [Finset.sum_eq_single j' (fun b _ hb => ite_eq_right fun h => hb (Fin.ext (by omega)))
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left hj', ite_eq_right hj]
    have : r - (j' : ℕ) = r - (j : ℕ) + 1 := by have := j.2; omega
    rw [this]; ring

/-- **The compressed constraint equation**: `DU − U(UᵀDU)ᵀ = ((1 − UUᵀ)DU) · 1ᵀ` for symmetric `D`. -/
theorem compressed_constraint {k : Type*} [Fintype k] [DecidableEq k] {D : Matrix n n R} (hD : Dᵀ = D)
    (U : Matrix n k R) :
    D * U - U * (Uᵀ * D * U)ᵀ = ((1 - U * Uᵀ) * D * U) * (1 : Matrix k k R)ᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hD, transpose_one, Matrix.mul_one]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

/-- **The compressed constraint equation, factored**: if `(1 − UUᵀ)DU = Y Zhᵀ` (`m` columns) and `D` is symmetric,
then `DU − U(UᵀDU)ᵀ = Y Zhᵀ`. -/
theorem compressed_constraint_factor {k m : Type*} [Fintype k] [DecidableEq k] [Fintype m] {D : Matrix n n R} (hD : Dᵀ = D)
    {U : Matrix n k R} {Y : Matrix n m R} {Zh : Matrix k m R} (h : (1 - U * Uᵀ) * D * U = Y * Zhᵀ) :
    D * U - U * (Uᵀ * D * U)ᵀ = Y * Zhᵀ := by
  rw [compressed_constraint hD U, transpose_one, Matrix.mul_one, h]

end Constraint

/-! ### The compression identity -/

section Compression

variable {R : Type*} [CommRing R] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

/-- **The compression identity**: for symmetric `D, P`, `P² = P` and `PD(1 − P) = YZᵀ`,
`(PDP)(PMP) − (PMP)(PDP) = P(DM − MD)P + (PMZ)Yᵀ − Y(ZᵀMP)`. -/
theorem compress_commutator {D M P : Matrix n n R} {Y Z : Matrix n m R} (hD : Dᵀ = D) (hP : Pᵀ = P)
    (hPP : P * P = P) (hdef : P * D * (1 - P) = Y * Zᵀ) :
    (P * D * P) * (P * M * P) - (P * M * P) * (P * D * P)
      = P * (D * M - M * D) * P + (P * M * Z) * Yᵀ - Y * (Zᵀ * M * P) := by
  have h1 : P * D * P = P * D - Y * Zᵀ := by rw [← hdef]; simp only [Matrix.mul_sub, Matrix.mul_one]; abel
  have h2 : P * D * P = D * P - Z * Yᵀ := by
    have := congrArg transpose h1
    simp only [transpose_mul, transpose_sub, transpose_transpose, hP, hD, Matrix.mul_assoc] at this
    rw [Matrix.mul_assoc]; exact this
  have hl : (P * D * P) * (P * M * P) = (P * D * P) * M * P := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc P P, hPP]
  have hr : (P * M * P) * (P * D * P) = P * M * (P * D * P) := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc P P, hPP]
  rw [hl, hr]
  nth_rewrite 1 [h1]
  rw [h2]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **The compressed generators**: for symmetric `M` with `P(DM − MD)P = P GJGᵀ P`, the commutator of `PDP` and
`PMP` is `ĜĴĜᵀ` with `Ĝ = [PG, PMZ, Y]` and `Ĵ = J ⊕ [[0, 1], [−1, 0]]`. -/
theorem compress_displacement {p : Type*} [Fintype p] [DecidableEq m] {D M P : Matrix n n R}
    {Y Z : Matrix n m R} {G : Matrix n p R} {J : Matrix p p R} (hD : Dᵀ = D) (hM : Mᵀ = M) (hP : Pᵀ = P)
    (hPP : P * P = P) (hdef : P * D * (1 - P) = Y * Zᵀ) (hG : P * (D * M - M * D) * P = P * (G * J * Gᵀ) * P) :
    (P * D * P) * (P * M * P) - (P * M * P) * (P * D * P)
      = fromCols (P * G) (fromCols (P * M * Z) Y) * borderJ m J
          * (fromCols (P * G) (fromCols (P * M * Z) Y))ᵀ := by
  rw [compress_commutator hD hP hPP hdef, hG]
  simp only [borderJ, sympBlock, transpose_fromCols, fromCols_mul_fromBlocks, fromCols_mul_fromRows,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    transpose_mul, hP, hM, Matrix.mul_assoc]
  abel

end Compression

section CompRank

/-- **The compressed displacement rank** is at most `|p| + 2m` when `P(DM − MD)P = P GJGᵀ P`. -/
theorem rank_compress_le {K : Type*} [Field K] {n m p : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] [Fintype p] [DecidableEq p] {D M P : Matrix n n K} {Y Z : Matrix n m K} {G : Matrix n p K}
    {J : Matrix p p K} (hD : Dᵀ = D) (hM : Mᵀ = M) (hP : Pᵀ = P) (hPP : P * P = P)
    (hdef : P * D * (1 - P) = Y * Zᵀ) (hG : P * (D * M - M * D) * P = P * (G * J * Gᵀ) * P) :
    ((P * D * P) * (P * M * P) - (P * M * P) * (P * D * P)).rank ≤ Fintype.card p + 2 * Fintype.card m := by
  rw [compress_displacement hD hM hP hPP hdef hG]
  refine (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans ?_)
  refine (rank_le_card_width _).trans ?_
  simp only [Fintype.card_sum]; omega

end CompRank

/-! ### The edge law -/

section Edge

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
/-- For symmetric `P`, `P (abᵀ) P = (Pa)(Pb)ᵀ`. -/
theorem mul_vecMulVec_mul {P : Matrix n n ℝ} (hP : Pᵀ = P) (a b : n → ℝ) :
    P * vecMulVec a b * P = vecMulVec (P *ᵥ a) (P *ᵥ b) := by
  rw [mul_vecMulVec, vecMulVec_mul, ← mulVec_transpose, hP]

omit [DecidableEq m] in
/-- **Edge law**: if the edge generator `e` of `P(DM − MD)P = P(feᵀ − efᵀ)P` has `Pe = Yc`, the compressed
commutator is `XYᵀ − YXᵀ` with `X = PMZ + (Pf)cᵀ`. -/
theorem compress_commutator_edge {D M P : Matrix n n ℝ} {Y Z : Matrix n m ℝ} {f e : n → ℝ} {c : m → ℝ}
    (hD : Dᵀ = D) (hM : Mᵀ = M) (hP : Pᵀ = P) (hPP : P * P = P) (hdef : P * D * (1 - P) = Y * Zᵀ)
    (hG : P * (D * M - M * D) * P = P * (vecMulVec f e - vecMulVec e f) * P) (hc : P *ᵥ e = Y *ᵥ c) :
    (P * D * P) * (P * M * P) - (P * M * P) * (P * D * P)
      = (P * M * Z + vecMulVec (P *ᵥ f) c) * Yᵀ - Y * (P * M * Z + vecMulVec (P *ᵥ f) c)ᵀ := by
  rw [compress_commutator hD hP hPP hdef, hG]
  have hZ : Zᵀ * M * P = (P * M * Z)ᵀ := by
    rw [transpose_mul, transpose_mul, hP, hM, Matrix.mul_assoc]
  have hPv : ∀ a b : n → ℝ, P * vecMulVec a b * P = vecMulVec (P *ᵥ a) (P *ᵥ b) := mul_vecMulVec_mul hP
  have h1 : vecMulVec (P *ᵥ f) (P *ᵥ e) = vecMulVec (P *ᵥ f) c * Yᵀ := by
    rw [hc, vecMulVec_mul, vecMul_transpose]
  have h2 : vecMulVec (P *ᵥ e) (P *ᵥ f) = Y * (vecMulVec (P *ᵥ f) c)ᵀ := by
    rw [hc, transpose_vecMulVec, mul_vecMulVec]
  rw [hZ, Matrix.mul_sub, Matrix.sub_mul, hPv, hPv, h1, h2]
  simp only [Matrix.add_mul, Matrix.mul_add, transpose_add]
  abel

/-- **Edge law, rank**: under the edge condition the compressed displacement rank is at most `2m`,
i.e. `2 + 2(m − 1)`. -/
theorem rank_compress_edge_le {D M P : Matrix n n ℝ} {Y Z : Matrix n m ℝ} {f e : n → ℝ} {c : m → ℝ}
    (hD : Dᵀ = D) (hM : Mᵀ = M) (hP : Pᵀ = P) (hPP : P * P = P) (hdef : P * D * (1 - P) = Y * Zᵀ)
    (hG : P * (D * M - M * D) * P = P * (vecMulVec f e - vecMulVec e f) * P) (hc : P *ᵥ e = Y *ᵥ c) :
    ((P * D * P) * (P * M * P) - (P * M * P) * (P * D * P)).rank ≤ 2 * Fintype.card m := by
  rw [compress_commutator_edge hD hM hP hPP hdef hG hc]
  set X := P * M * Z + vecMulVec (P *ᵥ f) c
  have : X * Yᵀ - Y * Xᵀ = fromCols X Y * sympBlock ℝ m * (fromCols X Y)ᵀ := by
    simp only [sympBlock, transpose_fromCols, fromCols_mul_fromBlocks, fromCols_mul_fromRows, Matrix.mul_zero,
      add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul]
    abel
  rw [this]
  refine (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans ?_)
  refine (rank_le_card_width _).trans ?_
  simp only [Fintype.card_sum]; omega

omit [DecidableEq m] in
/-- **The edge condition from the defect span**: if `e = Dw₀ + w₁` with `Pw₀ = Pw₁ = 0` (both in the constraint
space), then `Pe = Y(Zᵀw₀)`. -/
theorem edge_of_mem {D P : Matrix n n ℝ} {Y Z : Matrix n m ℝ} (hdef : P * D * (1 - P) = Y * Zᵀ)
    {e w₀ w₁ : n → ℝ} (he : e = D *ᵥ w₀ + w₁) (h₀ : P *ᵥ w₀ = 0) (h₁ : P *ᵥ w₁ = 0) :
    P *ᵥ e = Y *ᵥ (Zᵀ *ᵥ w₀) := by
  have : (1 - P) *ᵥ w₀ = w₀ := by rw [sub_mulVec, one_mulVec, h₀, sub_zero]
  calc P *ᵥ e = (P * D) *ᵥ w₀ := by rw [he, mulVec_add, h₁, add_zero, mulVec_mulVec]
    _ = (P * D * (1 - P)) *ᵥ w₀ := by conv_rhs => rw [← mulVec_mulVec, this]
    _ = Y *ᵥ (Zᵀ *ᵥ w₀) := by rw [hdef, mulVec_mulVec]

end Edge

/-! ### Projectors built from an orthonormal basis -/

section Projector

variable {R : Type*} [CommRing R] {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- **The defect of `P = E − UUᵀ`**: for a symmetric idempotent `E` commuting with `D` and `U` with orthonormal
columns in the range of `E` (`UᵀU = 1`, `EU = U`), `P` is a symmetric idempotent and `PD(1 − P) = (PDU)Uᵀ`. -/
theorem defect_of_sub {E D : Matrix n n R} {U : Matrix n k R} (hE : Eᵀ = E) (hEE : E * E = E)
    (hED : E * D = D * E) (hU : Uᵀ * U = 1) (hEU : E * U = U) :
    (E - U * Uᵀ)ᵀ = E - U * Uᵀ ∧ (E - U * Uᵀ) * (E - U * Uᵀ) = E - U * Uᵀ
      ∧ (E - U * Uᵀ) * D * (1 - (E - U * Uᵀ)) = ((E - U * Uᵀ) * D * U) * Uᵀ := by
  have hUE : Uᵀ * E = Uᵀ := by
    have := congrArg transpose hEU; rwa [transpose_mul, hE] at this
  have hUU : U * Uᵀ * (U * Uᵀ) = U * Uᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
  have hPE : (E - U * Uᵀ) * E = E - U * Uᵀ := by
    rw [Matrix.sub_mul, hEE, Matrix.mul_assoc, hUE]
  refine ⟨by rw [transpose_sub, hE, transpose_mul, transpose_transpose], ?_, ?_⟩
  · rw [Matrix.mul_sub, hPE, Matrix.sub_mul, ← Matrix.mul_assoc E U, hEU, hUU, sub_self, sub_zero]
  · have hD1 : D * (1 - E) = (1 - E) * D := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hED]
    have h1 : (E - U * Uᵀ) * D * (1 - E) = 0 := by
      rw [Matrix.mul_assoc, hD1, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hPE, sub_self,
        Matrix.zero_mul]
    have : (1 : Matrix n n R) - (E - U * Uᵀ) = (1 - E) + U * Uᵀ := by abel
    rw [this, Matrix.mul_add, h1, zero_add, Matrix.mul_assoc _ U]

/-- **The defect of the projector onto `W⊥`**: for `UᵀU = 1`, `P = 1 − UUᵀ` is a symmetric idempotent with
`PD(1 − P) = (PDU)Uᵀ`. -/
theorem defect_of_orthonormal {D : Matrix n n R} {U : Matrix n k R} (hU : Uᵀ * U = 1) :
    (1 - U * Uᵀ)ᵀ = 1 - U * Uᵀ ∧ (1 - U * Uᵀ) * (1 - U * Uᵀ) = 1 - U * Uᵀ
      ∧ (1 - U * Uᵀ) * D * (1 - (1 - U * Uᵀ)) = ((1 - U * Uᵀ) * D * U) * Uᵀ :=
  defect_of_sub transpose_one (Matrix.one_mul 1) (by rw [Matrix.one_mul, Matrix.mul_one]) hU (Matrix.one_mul U)

/-- **The defect factorization always exists**: `Y = PD(1 − P)`, `Z = 1`. -/
theorem defect_factor (D P : Matrix n n R) :
    P * D * (1 - P) = (P * D * (1 - P)) * (1 : Matrix n n R)ᵀ := by
  rw [transpose_one, Matrix.mul_one]

end Projector

/-! ### The even sector of an involution -/

section Even

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {neg : ι → ι}

/-- `P` has even rows: `P_{−i, j} = P_{ij}`, i.e. its range lies in the even vectors. -/
def EvenRows (neg : ι → ι) (P : Matrix ι ι ℝ) : Prop := ∀ i j, P (neg i) j = P i j

omit [Fintype ι] [DecidableEq ι] in
/-- A symmetric matrix with even rows has even columns. -/
theorem evenRows_col {P : Matrix ι ι ℝ} (hP : Pᵀ = P) (hE : EvenRows neg P) (i j : ι) : P i (neg j) = P i j := by
  have hs : ∀ a b, P a b = P b a := fun a b => congrFun (congrFun hP b) a
  rw [hs, hE, hs]

omit [DecidableEq ι] in
/-- A sum is unchanged by reindexing along an involution. -/
theorem sum_comp_involutive (hinv : Function.Involutive neg) (f : ι → ℝ) : ∑ i, f (neg i) = ∑ i, f i :=
  Equiv.sum_comp (hinv.toPerm neg) f

omit [DecidableEq ι] in
/-- **The even sector kills odd vectors**: a symmetric `P` with even rows has `Pv = 0` for odd `v`. -/
theorem mulVec_odd_eq_zero (hinv : Function.Involutive neg) {P : Matrix ι ι ℝ} (hP : Pᵀ = P)
    (hE : EvenRows neg P) {v : ι → ℝ} (hv : ∀ i, v (neg i) = -v i) : P *ᵥ v = 0 := by
  ext i
  have h := sum_comp_involutive hinv fun j => P i j * v j
  simp only [evenRows_col hP hE, hv, mul_neg, Finset.sum_neg_distrib] at h
  simp only [mulVec, dotProduct, Pi.zero_apply]
  linarith

/-- **An odd diagonal compresses to zero on the even sector**: for symmetric `P` with even rows and odd `w`,
`P diag(w) P = 0`. -/
theorem mul_diagonal_odd_mul (hinv : Function.Involutive neg) {P : Matrix ι ι ℝ} (hP : Pᵀ = P)
    (hE : EvenRows neg P) {w : ι → ℝ} (hw : ∀ i, w (neg i) = -w i) : P * diagonal w * P = 0 := by
  ext i j
  have h := sum_comp_involutive hinv fun l => P i l * w l * P l j
  simp only [evenRows_col hP hE, show ∀ x, P (neg x) j = P x j from fun x => hE x j, hw, mul_neg, neg_mul,
    Finset.sum_neg_distrib] at h
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, Matrix.zero_apply]
  linarith

/-- The even projector `E = (1 + Π)/2` of the involution. -/
def evenProj (neg : ι → ι) : Matrix ι ι ℝ :=
  fun i j => ((if i = j then 1 else 0) + (if i = neg j then 1 else 0)) / 2

omit [Fintype ι] in
theorem evenProj_transpose (hinv : Function.Involutive neg) : (evenProj neg)ᵀ = evenProj neg := by
  ext i j
  have : (j = neg i) ↔ (i = neg j) := ⟨fun h => by rw [h, hinv], fun h => by rw [h, hinv]⟩
  simp only [transpose_apply, evenProj, eq_comm (a := j) (b := i), this]

omit [Fintype ι] in
theorem evenProj_evenRows (hinv : Function.Involutive neg) : EvenRows neg (evenProj neg) := by
  intro i j
  have h1 : (neg i = j) ↔ (i = neg j) := ⟨fun h => by rw [← h, hinv], fun h => by rw [h, hinv]⟩
  have h2 : (neg i = neg j) ↔ (i = j) := hinv.injective.eq_iff
  simp only [evenProj, h1, h2]
  ring

theorem evenProj_mul_self (hinv : Function.Involutive neg) : evenProj neg * evenProj neg = evenProj neg := by
  ext i j
  have hc : ∀ l, (i = neg l) ↔ (l = neg i) := fun l => ⟨fun h => by rw [h, hinv], fun h => by rw [h, hinv]⟩
  simp only [Matrix.mul_apply, evenProj, hc]
  simp only [add_div, add_mul, mul_add, div_mul_div_comm, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
  simp only [ite_div, zero_div, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h5 : (i = neg j) ↔ (j = neg i) := ⟨fun h => by rw [h, hinv], fun h => by rw [h, hinv]⟩
  have h6 : (neg j = neg i) ↔ (i = j) := hinv.injective.eq_iff.trans eq_comm
  simp only [← h5, h6]
  split_ifs <;> norm_num

/-- The even projector commutes with an even diagonal. -/
theorem evenProj_mul_diagonal {d : ι → ℝ} (hd : ∀ i, d (neg i) = d i) :
    evenProj neg * diagonal d = diagonal d * evenProj neg := by
  ext i j
  simp only [mul_diagonal, diagonal_mul, evenProj]
  by_cases h1 : i = j
  · subst h1; ring
  · by_cases h2 : i = neg j
    · subst h2; rw [hd]; ring
    · simp [h1, h2]

/-- The even projector fixes a matrix with even columns. -/
theorem evenProj_mul_of_even (hinv : Function.Involutive neg) {k : Type*} {U : Matrix ι k ℝ}
    (hU : ∀ i a, U (neg i) a = U i a) : evenProj neg * U = U := by
  ext i a
  have hc : ∀ l, (i = neg l) ↔ (l = neg i) := fun l => ⟨fun h => by rw [h, hinv], fun h => by rw [h, hinv]⟩
  simp only [Matrix.mul_apply, evenProj, hc, add_div, add_mul, Finset.sum_add_distrib, ite_div, ite_mul, zero_div,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hU]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- `E − UUᵀ` has even rows when `E` does and `U` has even columns. -/
theorem evenRows_sub {k : Type*} [Fintype k] {E : Matrix ι ι ℝ} (hE : EvenRows neg E)
    {U : Matrix ι k ℝ} (hU : ∀ i a, U (neg i) a = U i a) : EvenRows neg (E - U * Uᵀ) := by
  intro i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, transpose_apply, hU]
  rw [hE]

end Even

/-! ### The edge vector from integration by parts -/

section IBP

open Real intervalIntegral

/-- **Twice integrating by parts against a cosine whose period divides `L`**: if `sin(ωL) = 0` and `cos(ωL) = 1`,
`ω² ∫₀ᴸ F cos(ωt) dt = −∫₀ᴸ F″ cos(ωt) dt + (F′(L) − F′(0))`. -/
theorem sq_mul_integral_cos {F F' F'' : ℝ → ℝ} {L ω : ℝ} (hF : ∀ t ∈ Set.uIcc 0 L, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc 0 L, HasDerivAt F' (F'' t) t) (hF'' : IntervalIntegrable F'' MeasureTheory.volume 0 L)
    (hs : Real.sin (ω * L) = 0) (hc : Real.cos (ω * L) = 1) :
    ω ^ 2 * ∫ t in (0 : ℝ)..L, F t * Real.cos (ω * t)
      = -(∫ t in (0 : ℝ)..L, F'' t * Real.cos (ω * t)) + (F' L - F' 0) := by
  by_cases hω : ω = 0
  · subst hω
    simp only [zero_mul, Real.cos_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul]
    rw [integral_eq_sub_of_hasDerivAt hF' hF'']
    ring
  have hF'c : ContinuousOn F' (Set.uIcc 0 L) := fun t ht => (hF' t ht).continuousAt.continuousWithinAt
  have hF'i : IntervalIntegrable F' MeasureTheory.volume 0 L := hF'c.intervalIntegrable
  have hv : ∀ t ∈ Set.uIcc 0 L, HasDerivAt (fun t => Real.sin (ω * t) / ω) (Real.cos (ω * t)) t := by
    intro t _
    exact ((((hasDerivAt_id' t).const_mul ω).sin).div_const ω).congr_deriv
      (by rw [mul_one, mul_div_assoc, div_self hω, mul_one])
  have hw : ∀ t ∈ Set.uIcc 0 L, HasDerivAt (fun t => -Real.cos (ω * t) / ω ^ 2) (Real.sin (ω * t) / ω) t := by
    intro t _
    exact (((((hasDerivAt_id' t).const_mul ω).cos).neg).div_const (ω ^ 2)).congr_deriv
      (by rw [mul_one, neg_mul, neg_neg, pow_two, ← div_div, mul_div_assoc, div_self hω, mul_one])
  have I1 := integral_mul_deriv_eq_deriv_mul hF hv hF'i
    (Continuous.intervalIntegrable (by fun_prop) 0 L)
  have I2 := integral_mul_deriv_eq_deriv_mul hF' hw hF''
    (Continuous.intervalIntegrable (by fun_prop) 0 L)
  have hI : (∫ t in (0 : ℝ)..L, F'' t * (-Real.cos (ω * t) / ω ^ 2))
      = (-1 / ω ^ 2) * ∫ t in (0 : ℝ)..L, F'' t * Real.cos (ω * t) := by
    rw [← integral_const_mul]
    congr 1; funext t; ring
  rw [hI] at I2
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_div, mul_zero, sub_zero] at I1 I2
  rw [I1, I2, hs, hc]
  field_simp
  ring

end IBP

/-! ### On the project's window matrix, in the node variable `u = ω²` -/

section Window

open Cvs.Finite.SymmetricModeSet (Idx negI mode)
open Cvs.Finite.OddEigenvectorResolvent (om)

/-- `b_i = bval (mode i)` is odd under `negI`. -/
theorem bval_odd (Pt R : ℕ) (L : ℝ) (N : ℕ) (i : Idx N) :
    Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N (negI N i)) = -Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i) := by
  rw [Cvs.Finite.SymmetricModeSet.mode_negI, Cvs.Finite.PairFormDividedDifference.bval_neg]

/-- **The `u = ω²` displacement of the CvS window matrix**:
`diag(ω²)M − M diag(ω²) = (ωb)𝟙ᵀ − 𝟙(ωb)ᵀ + bωᵀ − ωbᵀ`. -/
theorem window_sq_displacement {L : ℝ} (hL : 0 < L) (Pt R N : ℕ) :
    diagonal (fun i => om L N i ^ 2) * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N)
        - Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * diagonal (fun i => om L N i ^ 2)
      = vecMulVec (fun i => om L N i * Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i)) 1
        - vecMulVec 1 (fun i => om L N i * Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i))
        + vecMulVec (fun i => Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i)) (om L N)
        - vecMulVec (om L N) (fun i => Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i)) := by
  ext i j
  have h := Cvs.StepA.OddAboveDisplacement.displacement_M hL Pt R N i j
  simp only [Pi.one_apply] at h
  simp only [Matrix.sub_apply, Matrix.add_apply, diagonal_mul, mul_diagonal, vecMulVec_apply, Pi.one_apply]
  linear_combination (om L N i + om L N j) * h

/-- The window generator: `[ωb, 𝟙]`. -/
def windowGen (Pt R : ℕ) (L : ℝ) (N : ℕ) : Matrix (Idx N) (Fin 2) ℝ :=
  Cvs.Upstream.SchurSylvesterDisplacement.gen2 (fun i => om L N i * Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i)) 1

/-- **On the even sector the `u = ω²` displacement has rank two**: for symmetric `P` with even rows,
`P(diag(ω²)M − M diag(ω²))P = P((ωb)𝟙ᵀ − 𝟙(ωb)ᵀ)P`. -/
theorem window_sq_displacement_even {L : ℝ} (hL : 0 < L) (Pt R N : ℕ) {P : Matrix (Idx N) (Idx N) ℝ}
    (hP : Pᵀ = P) (hE : EvenRows (negI N) P) :
    P * (diagonal (fun i => om L N i ^ 2) * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N)
        - Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * diagonal (fun i => om L N i ^ 2)) * P
      = P * (vecMulVec (fun i => om L N i * Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i)) 1
        - vecMulVec 1 (fun i => om L N i * Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i))) * P := by
  have hinv := Cvs.Finite.SymmetricModeSet.negI_involutive N
  have hb : P *ᵥ (fun i => Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i)) = 0 :=
    mulVec_odd_eq_zero hinv hP hE (bval_odd Pt R L N)
  have hw : P *ᵥ om L N = 0 := mulVec_odd_eq_zero hinv hP hE (Cvs.StepA.OddAboveDisplacement.om_odd L N)
  rw [window_sq_displacement hL Pt R N, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    mul_vecMulVec_mul hP, mul_vecMulVec_mul hP (om L N) _, hb, hw, Matrix.mul_sub, Matrix.sub_mul]
  simp

/-- **The window `ω`-diagonal compresses to zero on the even sector**: `P diag(ω) P = 0` for symmetric `P` with
even rows. -/
theorem window_om_compress_eq_zero (L : ℝ) (N : ℕ) {P : Matrix (Idx N) (Idx N) ℝ} (hP : Pᵀ = P)
    (hE : EvenRows (negI N) P) : P * diagonal (om L N) * P = 0 :=
  mul_diagonal_odd_mul (Cvs.Finite.SymmetricModeSet.negI_involutive N) hP hE (Cvs.StepA.OddAboveDisplacement.om_odd L N)

/-- **Compressed displacement rank of the CvS window matrix on the even sector**: for `D = diag(ω²)`, a symmetric
idempotent `P` with even rows and `PD(1 − P) = YZᵀ`, the commutator of `PDP` and `PMP` has rank at most
`2 + 2m`. -/
theorem rank_compress_window {L : ℝ} (hL : 0 < L) (Pt R N : ℕ) {m : Type*} [Fintype m] [DecidableEq m]
    {P : Matrix (Idx N) (Idx N) ℝ} {Y Z : Matrix (Idx N) m ℝ} (hP : Pᵀ = P) (hPP : P * P = P)
    (hE : EvenRows (negI N) P) (hdef : P * diagonal (fun i => om L N i ^ 2) * (1 - P) = Y * Zᵀ) :
    ((P * diagonal (fun i => om L N i ^ 2) * P) * (P * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * P)
      - (P * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * P)
        * (P * diagonal (fun i => om L N i ^ 2) * P)).rank ≤ 2 + 2 * Fintype.card m := by
  have hG : P * (diagonal (fun i => om L N i ^ 2) * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N)
        - Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * diagonal (fun i => om L N i ^ 2)) * P
      = P * (windowGen Pt R L N * Cvs.Upstream.SchurSylvesterDisplacement.J2 ℝ * (windowGen Pt R L N)ᵀ) * P := by
    rw [window_sq_displacement_even hL Pt R N hP hE, windowGen, Cvs.Upstream.SchurSylvesterDisplacement.gen2_mul_J2_mul]
  have := rank_compress_le (diagonal_transpose _) (Cvs.StepA.OddAboveDisplacement.M_isSymm hL Pt R N).eq hP hPP hdef hG
  simpa using this

/-- **Edge law on the CvS window matrix**: on the even sector, with `D = diag(ω²)`, if `P𝟙 = Yc` the commutator of
`PDP` and `PMP` has rank at most `2m`. -/
theorem rank_compress_edge_window {L : ℝ} (hL : 0 < L) (Pt R N : ℕ) {m : Type*} [Fintype m] [DecidableEq m]
    {P : Matrix (Idx N) (Idx N) ℝ} {Y Z : Matrix (Idx N) m ℝ} {c : m → ℝ} (hP : Pᵀ = P) (hPP : P * P = P)
    (hE : EvenRows (negI N) P) (hdef : P * diagonal (fun i => om L N i ^ 2) * (1 - P) = Y * Zᵀ)
    (hc : P *ᵥ 1 = Y *ᵥ c) :
    ((P * diagonal (fun i => om L N i ^ 2) * P) * (P * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * P)
      - (P * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * P)
        * (P * diagonal (fun i => om L N i ^ 2) * P)).rank ≤ 2 * Fintype.card m :=
  rank_compress_edge_le (diagonal_transpose _) (Cvs.StepA.OddAboveDisplacement.M_isSymm hL Pt R N).eq hP hPP hdef
    (window_sq_displacement_even hL Pt R N hP hE) hc

/-- The cosine coefficients `v_F(i) = ∫₀ᴸ F(t) cos(ω_i t) dt` at the window nodes. -/
def cosVec (L : ℝ) (N : ℕ) (F : ℝ → ℝ) : Idx N → ℝ := fun i => ∫ t in (0 : ℝ)..L, F t * Real.cos (om L N i * t)

/-- **The window edge identity**: `diag(ω²) v_F = −v_{F″} + (F′(L) − F′(0)) 𝟙` for `F` twice differentiable on
`[0, L]` with `F″` integrable. -/
theorem window_cosVec_edge {L : ℝ} (hL : 0 < L) (N : ℕ) {F F' F'' : ℝ → ℝ}
    (hF : ∀ t ∈ Set.uIcc 0 L, HasDerivAt F (F' t) t) (hF' : ∀ t ∈ Set.uIcc 0 L, HasDerivAt F' (F'' t) t)
    (hF'' : IntervalIntegrable F'' MeasureTheory.volume 0 L) :
    diagonal (fun i => om L N i ^ 2) *ᵥ cosVec L N F = -cosVec L N F'' + (F' L - F' 0) • (1 : Idx N → ℝ) := by
  ext i
  have hωL : om L N i * L = ((2 * mode N i : ℤ) : ℝ) * Real.pi := by
    simp only [om, Cvs.Finite.TruncationZeroFreeOffAxes.omega]; push_cast; field_simp
  have hs : Real.sin (om L N i * L) = 0 := by rw [hωL]; exact Real.sin_int_mul_pi _
  have hc : Real.cos (om L N i * L) = 1 := by
    rw [show om L N i * L = ((mode N i : ℤ) : ℝ) * (2 * Real.pi) by rw [hωL]; push_cast; ring]
    exact Real.cos_int_mul_two_pi _
  rw [mulVec_diagonal, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  exact sq_mul_integral_cos hF hF' hF'' hs hc

/-- **The edge condition from a profile**: on the window with `D = diag(ω²)` and `PD(1 − P) = YZᵀ`, if `P` kills
`v_F` and `v_{F″}` and `F′(L) ≠ F′(0)`, then `P𝟙 = Y(Zᵀ v_F)/(F′(L) − F′(0))`. -/
theorem window_edge_of_profile {L : ℝ} (hL : 0 < L) (N : ℕ) {m : Type*} [Fintype m]
    {P : Matrix (Idx N) (Idx N) ℝ} {Y Z : Matrix (Idx N) m ℝ}
    (hdef : P * diagonal (fun i => om L N i ^ 2) * (1 - P) = Y * Zᵀ) {F F' F'' : ℝ → ℝ}
    (hF : ∀ t ∈ Set.uIcc 0 L, HasDerivAt F (F' t) t) (hF' : ∀ t ∈ Set.uIcc 0 L, HasDerivAt F' (F'' t) t)
    (hF'' : IntervalIntegrable F'' MeasureTheory.volume 0 L) (h0 : P *ᵥ cosVec L N F = 0)
    (h1 : P *ᵥ cosVec L N F'' = 0) (hne : F' L ≠ F' 0) :
    P *ᵥ 1 = Y *ᵥ (Zᵀ *ᵥ ((F' L - F' 0)⁻¹ • cosVec L N F)) := by
  have hc : F' L - F' 0 ≠ 0 := sub_ne_zero.mpr hne
  have he : (1 : Idx N → ℝ) = diagonal (fun i => om L N i ^ 2) *ᵥ ((F' L - F' 0)⁻¹ • cosVec L N F)
      + (F' L - F' 0)⁻¹ • cosVec L N F'' := by
    rw [mulVec_smul, window_cosVec_edge hL N hF hF' hF'', smul_add, smul_neg, smul_smul, inv_mul_cancel₀ hc,
      one_smul]
    abel
  exact edge_of_mem hdef he (by rw [mulVec_smul, h0, smul_zero]) (by rw [mulVec_smul, h1, smul_zero])

/-- **The window compression onto `Ev ∩ W⊥`**: for `U` with orthonormal even columns (`UᵀU = 1`), the projector
`P = E_ev − UUᵀ` meets every hypothesis of `rank_compress_window` with `Y = PDU`, `Z = U`, so the compressed
displacement rank is at most `2 + 2r`, and at most `2r` when `P𝟙 = PDU c`. -/
theorem rank_compress_window_basis {L : ℝ} (hL : 0 < L) (Pt R N : ℕ) {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix (Idx N) r ℝ} (hU : Uᵀ * U = 1) (hUe : ∀ i a, U (negI N i) a = U i a) :
    let P := evenProj (negI N) - U * Uᵀ
    let D := diagonal fun i => om L N i ^ 2
    ((P * D * P) * (P * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * P)
        - (P * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * P) * (P * D * P)).rank ≤ 2 + 2 * Fintype.card r
      ∧ ∀ c : r → ℝ, P *ᵥ 1 = (P * D * U) *ᵥ c →
        ((P * D * P) * (P * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * P)
          - (P * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * P) * (P * D * P)).rank ≤ 2 * Fintype.card r := by
  intro P D
  have hinv := Cvs.Finite.SymmetricModeSet.negI_involutive N
  have hd : ∀ i, om L N (negI N i) ^ 2 = om L N i ^ 2 := fun i => by
    rw [Cvs.StepA.OddAboveDisplacement.om_odd, neg_sq]
  obtain ⟨hP, hPP, hdef⟩ := defect_of_sub (evenProj_transpose hinv) (evenProj_mul_self hinv)
    (evenProj_mul_diagonal (d := fun i => om L N i ^ 2) hd) hU (evenProj_mul_of_even hinv hUe)
  have hE : EvenRows (negI N) P := evenRows_sub (evenProj_evenRows hinv) hUe
  exact ⟨rank_compress_window hL Pt R N hP hPP hE hdef,
    fun c hc => rank_compress_edge_window hL Pt R N hP hPP hE hdef hc⟩

/-- **The window edge law from a profile**: for `U` with orthonormal even columns and `P = E_ev − UUᵀ`, if `P` kills
the cosine coefficients `v_F` and `v_{F″}` of a twice differentiable `F` with `F′(L) ≠ F′(0)`, the compressed
displacement rank of the window matrix on `Ev ∩ span(U)⊥` is at most `2r`. -/
theorem rank_compress_window_of_profile {L : ℝ} (hL : 0 < L) (Pt R N : ℕ) {r : Type*} [Fintype r]
    [DecidableEq r] {U : Matrix (Idx N) r ℝ} (hU : Uᵀ * U = 1) (hUe : ∀ i a, U (negI N i) a = U i a)
    {F F' F'' : ℝ → ℝ} (hF : ∀ t ∈ Set.uIcc 0 L, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc 0 L, HasDerivAt F' (F'' t) t) (hF'' : IntervalIntegrable F'' MeasureTheory.volume 0 L)
    (h0 : (evenProj (negI N) - U * Uᵀ) *ᵥ cosVec L N F = 0)
    (h1 : (evenProj (negI N) - U * Uᵀ) *ᵥ cosVec L N F'' = 0) (hne : F' L ≠ F' 0) :
    let P := evenProj (negI N) - U * Uᵀ
    let D := diagonal fun i => om L N i ^ 2
    ((P * D * P) * (P * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * P)
        - (P * Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) * P) * (P * D * P)).rank ≤ 2 * Fintype.card r := by
  intro P D
  have hinv := Cvs.Finite.SymmetricModeSet.negI_involutive N
  have hd : ∀ i, om L N (negI N i) ^ 2 = om L N i ^ 2 := fun i => by
    rw [Cvs.StepA.OddAboveDisplacement.om_odd, neg_sq]
  obtain ⟨-, -, hdef⟩ := defect_of_sub (evenProj_transpose hinv) (evenProj_mul_self hinv)
    (evenProj_mul_diagonal (d := fun i => om L N i ^ 2) hd) hU (evenProj_mul_of_even hinv hUe)
  exact (rank_compress_window_basis hL Pt R N hU hUe).2 _
    (window_edge_of_profile hL N hdef hF hF' hF'' h0 h1 hne)

/-- **The even compression of `diag(ω²)` is not zero**: for `N ≥ 1` the even projector gives
`(E D E)_{ii} = ω_i²/2 ≠ 0` at the first positive mode. -/
theorem evenProj_D_evenProj_ne_zero {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 0 < N) :
    evenProj (negI N) * diagonal (fun i => om L N i ^ 2) * evenProj (negI N) ≠ 0 := by
  have hinv := Cvs.Finite.SymmetricModeSet.negI_involutive N
  have hd : ∀ i, om L N (negI N i) ^ 2 = om L N i ^ 2 := fun i => by
    rw [Cvs.StepA.OddAboveDisplacement.om_odd, neg_sq]
  rw [evenProj_mul_diagonal (d := fun i => om L N i ^ 2) hd, Matrix.mul_assoc, evenProj_mul_self hinv]
  intro h
  set i : Idx N := some (⟨0, hN⟩, true)
  have hi := congrFun (congrFun h i) i
  have hne : i ≠ negI N i := by simp [i, Cvs.Finite.SymmetricModeSet.negI]
  simp only [diagonal_mul, evenProj, ite_true, ite_eq_right hne, Matrix.zero_apply] at hi
  have := Cvs.Finite.OddEigenvectorResolvent.om_some_ne hL N (⟨0, hN⟩, true)
  have : om L N i ^ 2 ≠ 0 := pow_ne_zero 2 this
  apply this; linarith

end Window

end Cvs.Upstream.BorderedDisplacementRank
