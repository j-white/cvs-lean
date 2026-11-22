import Mathlib
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.ParityDisplacementEigenspaces
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.StepA.OddAboveDisplacement
import Cvs.Upstream.PencilLayerBound
import Cvs.Upstream.SchurFloorIndexSet

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Schur complements inherit a Sylvester displacement

If `Ω = Ω₁ ⊕ Ω₂`, `Ω' = Ω₁' ⊕ Ω₂'` and `ΩK − KΩ' = GH`, the Schur complement `S = K₂₂ − K₂₁K₁₁⁻¹K₁₂` obeys
`Ω₂S − SΩ₂' = (G₂ − K₂₁K₁₁⁻¹G₁)(H₂ − H₁K₁₁⁻¹K₁₂)`, with no invertibility used. On an index set split by `T` this
gives the generators `e_F − M_FT M_TT⁻¹ e_T` of `ParityDisplacementEigenspaces`'s `Displacement`, and `det K = det K_TT · det S`. The
inverse-block forms of Cvs.Prolate.Gram.RungCellGramDisplacement and Cvs.Upstream.SchurLayerFloors hold for every symmetric matrix.
-/

noncomputable section

open Matrix

namespace Cvs.Upstream.SchurSylvesterDisplacement
open Cvs.ZeroCounting

open Cvs.Finite.ParityDisplacementEigenspaces (Displacement)
open Cvs.Upstream.SchurFloorIndexSet (schurOn)

/-! ### The block identity -/

section Blocks

variable {R : Type*} [CommRing R] {n o m : Type*} [Fintype n] [DecidableEq n] [Fintype o] [Fintype m]

/-- **Schur inheritance, block equations**: the four block equations of `ΩK − KΩ' = GH` with block-diagonal
`Ω, Ω'` give `Ω₂S − SΩ₂' = (G₂ − K₂₁K₁₁⁻¹G₁)(H₂ − H₁K₁₁⁻¹K₁₂)`. -/
theorem schur_sylvester_of_blocks {Ω₁ Ω₁' : Matrix n n R} {Ω₂ Ω₂' : Matrix o o R}
    {K₁₁ : Matrix n n R} {K₁₂ : Matrix n o R} {K₂₁ : Matrix o n R} {K₂₂ : Matrix o o R}
    {G₁ : Matrix n m R} {G₂ : Matrix o m R} {H₁ : Matrix m n R} {H₂ : Matrix m o R}
    (h11 : Ω₁ * K₁₁ - K₁₁ * Ω₁' = G₁ * H₁) (h12 : Ω₁ * K₁₂ - K₁₂ * Ω₂' = G₁ * H₂)
    (h21 : Ω₂ * K₂₁ - K₂₁ * Ω₁' = G₂ * H₁) (h22 : Ω₂ * K₂₂ - K₂₂ * Ω₂' = G₂ * H₂) :
    Ω₂ * (K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂) - (K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂) * Ω₂'
      = (G₂ - K₂₁ * K₁₁⁻¹ * G₁) * (H₂ - H₁ * K₁₁⁻¹ * K₁₂) := by
  by_cases hK : IsUnit K₁₁.det
  swap
  · simp only [nonsing_inv_apply_not_isUnit _ hK, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    exact h22
  set X := K₁₁⁻¹
  have e21 : Ω₂ * K₂₁ = G₂ * H₁ + K₂₁ * Ω₁' := sub_eq_iff_eq_add.mp h21
  have e12 : K₁₂ * Ω₂' = Ω₁ * K₁₂ - G₁ * H₂ := by rw [← h12]; abel
  have e22 : Ω₂ * K₂₂ = G₂ * H₂ + K₂₂ * Ω₂' := sub_eq_iff_eq_add.mp h22
  have eX : X * Ω₁ = Ω₁' * X + X * G₁ * H₁ * X := by
    have a1 : X * (Ω₁ * K₁₁) * X = X * Ω₁ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hK, Matrix.mul_one]
    have a2 : X * (K₁₁ * Ω₁') * X = Ω₁' * X := by
      rw [← Matrix.mul_assoc X K₁₁, nonsing_inv_mul _ hK, Matrix.one_mul]
    have : X * (Ω₁ * K₁₁ - K₁₁ * Ω₁') * X = X * (G₁ * H₁) * X := by rw [h11]
    rw [Matrix.mul_sub, Matrix.sub_mul, a1, a2] at this
    rw [← sub_eq_iff_eq_add', this, Matrix.mul_assoc X G₁]
  have eX' : X * (Ω₁ * K₁₂) = Ω₁' * (X * K₁₂) + X * (G₁ * (H₁ * (X * K₁₂))) := by
    rw [← Matrix.mul_assoc, eX]; simp only [Matrix.add_mul, Matrix.mul_assoc]
  calc Ω₂ * (K₂₂ - K₂₁ * X * K₁₂) - (K₂₂ - K₂₁ * X * K₁₂) * Ω₂'
      = Ω₂ * K₂₂ - K₂₂ * Ω₂' - (Ω₂ * K₂₁) * (X * K₁₂) + K₂₁ * (X * (K₁₂ * Ω₂')) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]; abel
    _ = (G₂ - K₂₁ * X * G₁) * (H₂ - H₁ * X * K₁₂) := by
        rw [e21, e12, e22, Matrix.mul_sub, eX']
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
        abel

omit [Fintype n] [DecidableEq n] [Fintype o] [Fintype m] in
/-- Block matrices subtract blockwise. -/
theorem fromBlocks_sub_fromBlocks {l q : Type*} (A A' : Matrix n l R) (B B' : Matrix n q R) (C C' : Matrix o l R)
    (D D' : Matrix o q R) :
    fromBlocks A B C D - fromBlocks A' B' C' D' = fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

/-- **Schur inheritance, block form**: `ΩK − KΩ' = GH` with `Ω = Ω₁ ⊕ Ω₂`, `Ω' = Ω₁' ⊕ Ω₂'`, `G = [G₁; G₂]` and
`H = [H₁ H₂]` gives `Ω₂S − SΩ₂' = (G₂ − K₂₁K₁₁⁻¹G₁)(H₂ − H₁K₁₁⁻¹K₁₂)`. -/
theorem schur_sylvester {Ω₁ Ω₁' : Matrix n n R} {Ω₂ Ω₂' : Matrix o o R}
    {K₁₁ : Matrix n n R} {K₁₂ : Matrix n o R} {K₂₁ : Matrix o n R} {K₂₂ : Matrix o o R}
    {G₁ : Matrix n m R} {G₂ : Matrix o m R} {H₁ : Matrix m n R} {H₂ : Matrix m o R}
    (h : fromBlocks Ω₁ 0 0 Ω₂ * fromBlocks K₁₁ K₁₂ K₂₁ K₂₂ - fromBlocks K₁₁ K₁₂ K₂₁ K₂₂ * fromBlocks Ω₁' 0 0 Ω₂'
      = fromRows G₁ G₂ * fromCols H₁ H₂) :
    Ω₂ * (K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂) - (K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂) * Ω₂'
      = (G₂ - K₂₁ * K₁₁⁻¹ * G₁) * (H₂ - H₁ * K₁₁⁻¹ * K₁₂) := by
  rw [fromBlocks_multiply, fromBlocks_multiply, fromRows_mul_fromCols, ← sub_eq_zero] at h
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] at h
  rw [fromBlocks_sub_fromBlocks, fromBlocks_sub_fromBlocks, ← fromBlocks_zero, fromBlocks_inj] at h
  obtain ⟨h11, h12, h21, h22⟩ := h
  exact schur_sylvester_of_blocks (sub_eq_zero.mp h11) (sub_eq_zero.mp h12) (sub_eq_zero.mp h21)
    (sub_eq_zero.mp h22)

/-- **Schur inheritance, symmetric form**: for `K = [[K₁₁, K₁₂], [K₁₂ᵀ, K₂₂]]` with `K₁₁ᵀ = K₁₁`,
`Ω = Ω₁ ⊕ Ω₂` and `ΩK − KΩᵀ = GJGᵀ`, the Schur complement obeys `Ω₂S − SΩ₂ᵀ = G̃JG̃ᵀ`,
`G̃ = G₂ − K₁₂ᵀK₁₁⁻¹G₁`. -/
theorem schur_displacement {p : Type*} [Fintype p] {Ω₁ : Matrix n n R} {Ω₂ : Matrix o o R}
    {K₁₁ : Matrix n n R} {K₁₂ : Matrix n o R} {K₂₂ : Matrix o o R}
    {G₁ : Matrix n p R} {G₂ : Matrix o p R} {J : Matrix p p R} (hs : K₁₁ᵀ = K₁₁)
    (h : fromBlocks Ω₁ 0 0 Ω₂ * fromBlocks K₁₁ K₁₂ K₁₂ᵀ K₂₂ - fromBlocks K₁₁ K₁₂ K₁₂ᵀ K₂₂ * (fromBlocks Ω₁ 0 0 Ω₂)ᵀ
      = fromRows G₁ G₂ * J * (fromRows G₁ G₂)ᵀ) :
    Ω₂ * (K₂₂ - K₁₂ᵀ * K₁₁⁻¹ * K₁₂) - (K₂₂ - K₁₂ᵀ * K₁₁⁻¹ * K₁₂) * Ω₂ᵀ
      = (G₂ - K₁₂ᵀ * K₁₁⁻¹ * G₁) * J * (G₂ - K₁₂ᵀ * K₁₁⁻¹ * G₁)ᵀ := by
  rw [fromBlocks_transpose, transpose_zero, transpose_zero, fromRows_mul, transpose_fromRows] at h
  have := schur_sylvester h
  have hX : (K₁₁⁻¹)ᵀ = K₁₁⁻¹ := by rw [transpose_nonsing_inv, hs]
  rw [this, Matrix.mul_assoc, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hX,
    transpose_transpose]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]

end Blocks

/-! ### On an index set split by a predicate -/

section Split

variable {R : Type*} [CommRing R] {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]
variable (p : ι → Prop) [DecidablePred p]

/-- The Schur complement onto `{¬ p}` after eliminating the block `{p}`: `K_FF − K_FT K_TT⁻¹ K_TF`. -/
def elim (K : Matrix ι ι R) : Matrix {j // ¬ p j} {j // ¬ p j} R :=
  K.toBlock (¬ p ·) (¬ p ·) - (K.toBlock (¬ p ·) p : Matrix {j // ¬ p j} {j // p j} R) *
    ((K.toBlock p p)⁻¹ : Matrix {j // p j} {j // p j} R) * (K.toBlock p (¬ p ·) : Matrix {j // p j} {j // ¬ p j} R)

/-- The eliminated generator rows `G_F − K_FT K_TT⁻¹ G_T`. -/
def elimGen {m : Type*} (K : Matrix ι ι R) (G : Matrix ι m R) : Matrix {j // ¬ p j} m R :=
  G.submatrix Subtype.val id - (K.toBlock (¬ p ·) p : Matrix {j // ¬ p j} {j // p j} R) *
    ((K.toBlock p p)⁻¹ : Matrix {j // p j} {j // p j} R) * (G.submatrix Subtype.val id : Matrix {j // p j} m R)

/-- `Ω` has no blocks between `{p}` and `{¬ p}`. -/
def BlockDiag (Ω : Matrix ι ι R) : Prop := Ω.toBlock p (¬ p ·) = 0 ∧ Ω.toBlock (¬ p ·) p = 0

variable {p}

omit [CommRing R] [Fintype ι] [DecidableEq ι] in
/-- The transpose of a block is the transposed block: `(M_ab)ᵀ = (Mᵀ)_ba`. -/
theorem transpose_toBlock' [CommRing R] (M : Matrix ι ι R) (a b : ι → Prop) : (M.toBlock a b)ᵀ = Mᵀ.toBlock b a := by
  ext i j; rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Blocks of a difference are differences of blocks. -/
theorem toBlock_sub' (A B : Matrix ι ι R) (a b : ι → Prop) : (A - B).toBlock a b = A.toBlock a b - B.toBlock a b := by
  ext i j; rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The `(a, b)` block of `GH` is `G_a H_b`. -/
theorem toBlock_mul_gen (G : Matrix ι m R) (H : Matrix m ι R) (a b : ι → Prop) :
    (G * H).toBlock a b = G.submatrix (Subtype.val : {j // a j} → ι) id * H.submatrix id Subtype.val := by
  ext i j; simp [toBlock, Matrix.mul_apply]

omit [DecidableEq ι] in
/-- One block of `ΩK − KΩ' = GH`, given the two product splittings through the diagonal blocks. -/
theorem block_eq {Ω Ω' K : Matrix ι ι R} {G : Matrix ι m R} {H : Matrix m ι R} (h : Ω * K - K * Ω' = G * H)
    (a b : ι → Prop) [DecidablePred a] [DecidablePred b]
    (hL : (Ω * K).toBlock a b = Ω.toBlock a a * K.toBlock a b)
    (hR : (K * Ω').toBlock a b = K.toBlock a b * Ω'.toBlock b b) :
    Ω.toBlock a a * K.toBlock a b - K.toBlock a b * Ω'.toBlock b b
      = G.submatrix (Subtype.val : {j // a j} → ι) id * H.submatrix id Subtype.val := by
  rw [← hL, ← hR, ← toBlock_mul_gen, ← toBlock_sub', h]

/-- **Schur inheritance on a split index set**: block-diagonal `Ω, Ω'` with `ΩK − KΩ' = GH` give `Ω_FF S − S Ω'_FF = (G_F − K_FT K_TT⁻¹ G_T)(H_F − H_T K_TT⁻¹ K_TF)`. -/
theorem elim_sylvester {Ω Ω' K : Matrix ι ι R} (hΩ : BlockDiag p Ω) (hΩ' : BlockDiag p Ω')
    {G : Matrix ι m R} {H : Matrix m ι R} (h : Ω * K - K * Ω' = G * H) :
    Ω.toBlock (¬ p ·) (¬ p ·) * elim p K - elim p K * Ω'.toBlock (¬ p ·) (¬ p ·)
      = elimGen p K G * (H.submatrix id Subtype.val - H.submatrix id (Subtype.val : {j // p j} → ι)
          * (K.toBlock p p)⁻¹ * K.toBlock p (¬ p ·)) := by
  have Lp : ∀ b : ι → Prop, (Ω * K).toBlock p b = Ω.toBlock p p * K.toBlock p b := fun b => by
    rw [toBlock_mul_eq_add p p b Ω K, hΩ.1, Matrix.zero_mul, add_zero]
  have Ln : ∀ b : ι → Prop, (Ω * K).toBlock (¬ p ·) b = Ω.toBlock (¬ p ·) (¬ p ·) * K.toBlock (¬ p ·) b :=
    fun b => by rw [toBlock_mul_eq_add (¬ p ·) p b Ω K, hΩ.2, Matrix.zero_mul, zero_add]
  have Rp : ∀ a : ι → Prop, (K * Ω').toBlock a p = K.toBlock a p * Ω'.toBlock p p := fun a => by
    rw [toBlock_mul_eq_add a p p K Ω', hΩ'.2, Matrix.mul_zero, add_zero]
  have Rn : ∀ a : ι → Prop, (K * Ω').toBlock a (¬ p ·) = K.toBlock a (¬ p ·) * Ω'.toBlock (¬ p ·) (¬ p ·) :=
    fun a => by rw [toBlock_mul_eq_add a p (¬ p ·) K Ω', hΩ'.1, Matrix.mul_zero, zero_add]
  exact schur_sylvester_of_blocks (block_eq h p p (Lp p) (Rp p)) (block_eq h p (¬ p ·) (Lp _) (Rn p))
    (block_eq h (¬ p ·) p (Ln p) (Rp _)) (block_eq h (¬ p ·) (¬ p ·) (Ln _) (Rn _))

/-- **Schur inheritance on a split index set, symmetric form**: for `Kᵀ = K`, block-diagonal `Ω` and
`ΩK − KΩᵀ = GJGᵀ`, `Ω_FF S − S Ω_FFᵀ = G̃JG̃ᵀ` with `G̃ = G_F − K_FT K_TT⁻¹ G_T`. -/
theorem elim_displacement {Ω K : Matrix ι ι R} (hΩ : BlockDiag p Ω) (hs : Kᵀ = K) {G : Matrix ι m R}
    {J : Matrix m m R} (h : Ω * K - K * Ωᵀ = G * J * Gᵀ) :
    Ω.toBlock (¬ p ·) (¬ p ·) * elim p K - elim p K * (Ω.toBlock (¬ p ·) (¬ p ·))ᵀ
      = elimGen p K G * J * (elimGen p K G)ᵀ := by
  have hΩt : BlockDiag p Ωᵀ := ⟨by rw [← transpose_toBlock', hΩ.2, transpose_zero],
    by rw [← transpose_toBlock', hΩ.1, transpose_zero]⟩
  have h' : Ω * K - K * Ωᵀ = (G * J) * Gᵀ := by rw [h]
  have := elim_sylvester hΩ hΩt h'
  have hFF : Ωᵀ.toBlock (¬ p ·) (¬ p ·) = (Ω.toBlock (¬ p ·) (¬ p ·))ᵀ := (transpose_toBlock' _ _ _).symm
  have hTT : (K.toBlock p p)ᵀ = K.toBlock p p := by rw [transpose_toBlock', hs]
  have hX : ((K.toBlock p p)⁻¹)ᵀ = (K.toBlock p p)⁻¹ := by rw [transpose_nonsing_inv, hTT]
  have hTF : (K.toBlock (¬ p ·) p)ᵀ = K.toBlock p (¬ p ·) := by rw [transpose_toBlock', hs]
  have hsub : ∀ q : ι → Prop, (G * J).submatrix (Subtype.val : {j // q j} → ι) id
      = G.submatrix Subtype.val id * J := fun q => by ext i j; simp [Matrix.mul_apply]
  have hA : elimGen p K (G * J) = elimGen p K G * J := by
    simp only [elimGen, hsub, Matrix.sub_mul, Matrix.mul_assoc]
  have hB : (elimGen p K G)ᵀ = Gᵀ.submatrix id Subtype.val
      - Gᵀ.submatrix id (Subtype.val : {j // p j} → ι) * (K.toBlock p p)⁻¹ * K.toBlock p (¬ p ·) := by
    simp only [elimGen, Matrix.transpose_sub, Matrix.transpose_mul, hX, hTF, Matrix.transpose_submatrix,
      Matrix.mul_assoc]
  rw [hFF] at this
  rw [this, hA, hB]

end Split

/-! ### The determinant of a split matrix -/

section Det

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → Prop} [DecidablePred p]

/-- **The Schur determinant formula on a split index set**: for `K_TT` invertible,
`det K = det K_TT · det (K_FF − K_FT K_TT⁻¹ K_TF)`. -/
theorem det_eq_det_mul_det_elim (K : Matrix ι ι R) (hK : IsUnit (K.toBlock p p).det) :
    K.det = (K.toBlock p p).det * (elim p K).det := by
  let _ := invertibleOfIsUnitDet _ hK
  rw [det_toBlock K p, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  rfl

/-- **A one-index Schur complement is a determinant ratio**: if `{¬ p} = {k}` and `K_TT` is invertible, the
remaining entry of `K_FF − K_FT K_TT⁻¹ K_TF` is `det K / det K_TT`. -/
theorem elim_apply_eq_det_div {K' : Type*} [Field K'] {K : Matrix ι ι K'} {k : ι} (hk : ∀ j, ¬ p j ↔ j = k)
    (hK : (K.toBlock p p).det ≠ 0) :
    elim p K ⟨k, (hk k).mpr rfl⟩ ⟨k, (hk k).mpr rfl⟩ = K.det / (K.toBlock p p).det := by
  let _ : Unique {j // ¬ p j} := ⟨⟨⟨k, (hk k).mpr rfl⟩⟩, fun j => Subtype.ext ((hk j).mp j.2)⟩
  have h := det_eq_det_mul_det_elim K (isUnit_iff_ne_zero.mpr hK)
  have hu : (elim p K).det = elim p K ⟨k, (hk k).mpr rfl⟩ ⟨k, (hk k).mpr rfl⟩ := Matrix.det_unique _
  rw [h, hu, mul_div_cancel_left₀ _ hK]

/-- **Eliminating one index**: `(K_FF − K_Fk K_kk⁻¹ K_kF)_ij = K_ij − K_ik K_kj / K_kk` over a field. -/
theorem elim_single_apply {K' : Type*} [Field K'] (K : Matrix ι ι K') (k : ι) (i j : {j // ¬ j = k}) :
    elim (· = k) K i j = K i j - K i k * K k j / K k k := by
  simp only [elim, Matrix.sub_apply, Matrix.mul_apply, toBlock_apply, inv_subsingleton, Fintype.sum_unique,
    diagonal_apply_eq, Ring.inverse_eq_inv']
  change K i j - K i k * (K k k)⁻¹ * K k j = _
  ring

end Det

/-! ### The rank-two `Displacement` form -/

section RankTwo

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → Prop} [DecidablePred p]

/-- The generator `[e u]` of a rank-two displacement. -/
def gen2 {R : Type*} (e u : ι → R) : Matrix ι (Fin 2) R := Matrix.of fun i k => ![e i, u i] k

/-- The symplectic form `J = [[0, 1], [−1, 0]]`. -/
def J2 (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

/-- `J2` is antisymmetric. -/
theorem J2_transpose (R : Type*) [CommRing R] : (J2 R)ᵀ = -J2 R := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J2]

omit [Fintype ι] [DecidableEq ι] in
/-- `[e u] J [e u]ᵀ = euᵀ − ueᵀ`. -/
theorem gen2_mul_J2_mul {R : Type*} [CommRing R] (e u : ι → R) :
    gen2 e u * J2 R * (gen2 e u)ᵀ = vecMulVec e u - vecMulVec u e := by
  ext i j; simp [gen2, J2, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec_apply, Function.swap]; ring

/-- `Displacement ω M e u` is `diag ω · M − M · diag ω = [e u] J [e u]ᵀ`. -/
theorem displacement_iff_gen2 {om : ι → ℝ} {M : Matrix ι ι ℝ} {e u : ι → ℝ} :
    Displacement om M e u ↔ diagonal om * M - M * (diagonal om)ᵀ = gen2 e u * J2 ℝ * (gen2 e u)ᵀ := by
  rw [diagonal_transpose, Cvs.Prolate.Gram.RungCellGramDisplacement.displacement_iff, gen2_mul_J2_mul]

omit [Fintype ι] [DecidablePred p] in
/-- A diagonal matrix has no blocks between `{p}` and `{¬ p}`. -/
theorem blockDiag_diagonal {R : Type*} [CommRing R] (om : ι → R) : BlockDiag p (diagonal om) :=
  ⟨toBlock_diagonal_disjoint om fun _ h₁ h₂ i hi => h₂ i hi (h₁ i hi),
    toBlock_diagonal_disjoint om fun _ h₁ h₂ i hi => h₁ i hi (h₂ i hi)⟩

/-- **Residual Schur inheritance on the kept set**: `[diag ω, M] = euᵀ − ueᵀ` for symmetric `M` gives
`[diag ω_F, S] = ẽũᵀ − ũẽᵀ` on `S = M_FF − M_FT M_TT⁻¹ M_TF`, with `ẽ = e_F − M_FT M_TT⁻¹ e_T` and
`ũ = u_F − M_FT M_TT⁻¹ u_T`. -/
theorem displacement_elim {om : ι → ℝ} {M : Matrix ι ι ℝ} {e u : ι → ℝ} (hs : Mᵀ = M)
    (hd : Displacement om M e u) :
    Displacement (fun j : {j // ¬ p j} => om j) (elim p M)
      ((fun j : {j // ¬ p j} => e j) - M.toBlock (¬ p ·) p *ᵥ ((M.toBlock p p)⁻¹ *ᵥ fun j : {j // p j} => e j))
      ((fun j : {j // ¬ p j} => u j) - M.toBlock (¬ p ·) p *ᵥ ((M.toBlock p p)⁻¹ *ᵥ fun j : {j // p j} => u j)) := by
  rw [displacement_iff_gen2] at hd ⊢
  have := elim_displacement (p := p) (blockDiag_diagonal om) hs hd
  rw [toBlock_diagonal_self] at this
  rw [this]
  have hg : elimGen p M (gen2 e u) = gen2
      ((fun j : {j // ¬ p j} => e j) - M.toBlock (¬ p ·) p *ᵥ ((M.toBlock p p)⁻¹ *ᵥ fun j : {j // p j} => e j))
      ((fun j : {j // ¬ p j} => u j) - M.toBlock (¬ p ·) p *ᵥ ((M.toBlock p p)⁻¹ *ᵥ fun j : {j // p j} => u j)) := by
    ext i k
    fin_cases k <;> simp [elimGen, gen2, mulVec, dotProduct, Matrix.mul_assoc, Matrix.mul_apply] <;>
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc] <;> exact Finset.sum_comm
  rw [hg]

end RankTwo

/-! ### The inverse-block forms for every symmetric matrix -/

section InverseBlock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → Prop} [DecidablePred p]

/-- **`Cvs.Prolate.Gram.RungCellGramDisplacement.displacement_schurOn` for every symmetric matrix**: symmetric `M` with `[diag ω, M] = euᵀ − ueᵀ`
gives `[diag ω_T, S_T] = ẽũᵀ − ũẽᵀ` for `S_T = (M⁻¹_TT)⁻¹`, `ẽ = S_T(M⁻¹e)_T`, `ũ = S_T(M⁻¹u)_T`. -/
theorem displacement_schurOn_of_symm {om : ι → ℝ} {M : Matrix ι ι ℝ} {e u : ι → ℝ} (hs : Mᵀ = M)
    (hd : Displacement om M e u) :
    Displacement (fun j : {j // p j} => om j) (schurOn p M)
      (schurOn p M *ᵥ fun j : {j // p j} => (M⁻¹ *ᵥ e) j)
      (schurOn p M *ᵥ fun j : {j // p j} => (M⁻¹ *ᵥ u) j) := by
  have hzero : schurOn p M = 0 → Displacement (fun j : {j // p j} => om j) (schurOn p M)
      (schurOn p M *ᵥ fun j : {j // p j} => (M⁻¹ *ᵥ e) j)
      (schurOn p M *ᵥ fun j : {j // p j} => (M⁻¹ *ᵥ u) j) := fun h0 i j => by
    rw [h0]; simp
  by_cases hu : IsUnit M.det
  swap
  · exact hzero (by rw [schurOn, nonsing_inv_apply_not_isUnit _ hu]; exact (congrArg _ (by ext; rfl)).trans inv_zero)
  by_cases hN : IsUnit (M⁻¹.toBlock p p).det
  swap
  · exact hzero (nonsing_inv_apply_not_isUnit _ hN)
  have hsi : M⁻¹ᵀ = M⁻¹ := by rw [transpose_nonsing_inv, hs]
  have hNs : (M⁻¹.toBlock p p)ᵀ = M⁻¹.toBlock p p := by rw [transpose_toBlock', hsi]
  have h1 := Cvs.Prolate.Gram.RungCellGramDisplacement.displacement_toBlock (Cvs.Prolate.Gram.RungCellGramDisplacement.displacement_inv hs hu hd) p
  exact Cvs.Prolate.Gram.RungCellGramDisplacement.displacement_inv hNs hN h1

/-- **`Cvs.Upstream.SchurLayerFloors.layer_displacement_lowRank` for every symmetric matrix**: symmetric `M` with
`ΛM − MΛ = GJGᵀ` gives `Λ_A S_A − S_A Λ_A = S_A X J Xᵀ S_A`, `X = (M⁻¹G)_A`, on `A = {j ≥ k}`. -/
theorem layer_displacement_lowRank_of_symm {κ : Type*} [Fintype κ] [LinearOrder κ] {m : Type*} [Fintype m]
    {M : Matrix κ κ ℝ} (hs : Mᵀ = M) (k : κ) (d : κ → ℝ)
    (G : Matrix κ m ℝ) (J : Matrix m m ℝ) (hK : diagonal d * M - M * diagonal d = G * J * Gᵀ) :
    diagonal (fun j : {j // k ≤ j} => d j) * Cvs.Upstream.PencilLayerBound.layer M k - Cvs.Upstream.PencilLayerBound.layer M k * diagonal (fun j : {j // k ≤ j} => d j)
      = Cvs.Upstream.PencilLayerBound.layer M k * (M⁻¹ * G).submatrix (Subtype.val : {j // k ≤ j} → κ) (id : m → m) * J
          * ((M⁻¹ * G).submatrix (Subtype.val : {j // k ≤ j} → κ) (id : m → m))ᵀ * Cvs.Upstream.PencilLayerBound.layer M k := by
  set Pa := M⁻¹.submatrix (Subtype.val : {j // k ≤ j} → κ) Subtype.val
  set La := diagonal (fun j : {j // k ≤ j} => d j)
  rw [show Cvs.Upstream.PencilLayerBound.layer M k = Pa⁻¹ from rfl]
  by_cases hN : IsUnit Pa.det
  swap
  · rw [nonsing_inv_apply_not_isUnit _ hN]; simp
  by_cases hu : IsUnit M.det
  swap
  · exfalso
    have hP0 : Pa = 0 := by
      simp only [Pa, nonsing_inv_apply_not_isUnit _ hu]; rfl
    have : Nonempty {j // k ≤ j} := ⟨⟨k, le_refl k⟩⟩
    rw [hP0, det_zero] at hN
    exact not_isUnit_zero hN
  have hsi : M⁻¹ᵀ = M⁻¹ := by rw [transpose_nonsing_inv, hs]
  have hfull : M⁻¹ * (G * J * Gᵀ) * M⁻¹ = -(diagonal d * M⁻¹ - M⁻¹ * diagonal d) := by
    have a1 : M⁻¹ * (diagonal d * M) * M⁻¹ = M⁻¹ * diagonal d := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    have a2 : M⁻¹ * (M * diagonal d) * M⁻¹ = diagonal d * M⁻¹ := by
      rw [← Matrix.mul_assoc M⁻¹ M, nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [← hK, Matrix.mul_sub, Matrix.sub_mul, a1, a2, neg_sub]
  have hres : (M⁻¹ * (G * J * Gᵀ) * M⁻¹).submatrix (Subtype.val : {j // k ≤ j} → κ) Subtype.val
      = -(La * Pa - Pa * La) := by
    rw [hfull]; ext a b; simp [La, Pa, diagonal_mul, mul_diagonal]
  have hsub : (M⁻¹ * (G * J * Gᵀ) * M⁻¹).submatrix (Subtype.val : {j // k ≤ j} → κ) Subtype.val
      = (M⁻¹ * G).submatrix (Subtype.val : {j // k ≤ j} → κ) (id : m → m) * J
          * ((M⁻¹ * G).submatrix (Subtype.val : {j // k ≤ j} → κ) (id : m → m))ᵀ := by
    have hX : M⁻¹ * (G * J * Gᵀ) * M⁻¹ = (M⁻¹ * G) * J * (M⁻¹ * G)ᵀ := by
      rw [Matrix.transpose_mul, hsi]; simp only [Matrix.mul_assoc]
    rw [hX]; ext a b; simp [Matrix.mul_apply]
  have e1 : Pa⁻¹ * (La * Pa) * Pa⁻¹ = Pa⁻¹ * La := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hN, Matrix.mul_one]
  have e2 : Pa⁻¹ * (Pa * La) * Pa⁻¹ = La * Pa⁻¹ := by
    rw [← Matrix.mul_assoc Pa⁻¹ Pa La, nonsing_inv_mul _ hN, Matrix.one_mul]
  have key : Pa⁻¹ * (-(La * Pa - Pa * La)) * Pa⁻¹ = La * Pa⁻¹ - Pa⁻¹ * La := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, e1, e2, neg_sub]
  rw [← key, ← hres, hsub]
  simp only [Matrix.mul_assoc]

end InverseBlock

/-! ### On the project's window matrix -/

/-- **Residual Schur inheritance on the CvS window matrix**: for every index set `T`, the Schur complement of
`M = Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)` onto the complement of `T` keeps the displacement with generators
`𝟙 − M_FT M_TT⁻¹ 𝟙` and `−(b_F − M_FT M_TT⁻¹ b_T)`. -/
theorem displacement_elim_windowM {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (p : Cvs.Finite.SymmetricModeSet.Idx N → Prop) [DecidablePred p] :
    Displacement (fun j : {j // ¬ p j} => Cvs.Finite.OddEigenvectorResolvent.om L N j)
      (elim p (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N)))
      ((fun j : {j // ¬ p j} => (1 : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) j)
        - (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N)).toBlock (¬ p ·) p *ᵥ
          (((Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N)).toBlock p p)⁻¹ *ᵥ
            fun j : {j // p j} => (1 : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) j))
      ((fun j : {j // ¬ p j} => -Cvs.Finite.PairFormDividedDifference.bval P R L (Cvs.Finite.SymmetricModeSet.mode N j))
        - (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N)).toBlock (¬ p ·) p *ᵥ
          (((Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N)).toBlock p p)⁻¹ *ᵥ
            fun j : {j // p j} => -Cvs.Finite.PairFormDividedDifference.bval P R L (Cvs.Finite.SymmetricModeSet.mode N j))) :=
  displacement_elim (p := p) (om := Cvs.Finite.OddEigenvectorResolvent.om L N)
    (M := Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N)) (e := 1)
    (u := fun i => -Cvs.Finite.PairFormDividedDifference.bval P R L (Cvs.Finite.SymmetricModeSet.mode N i))
    (Cvs.StepA.OddAboveDisplacement.M_isSymm hL P R N).eq
    (Cvs.StepA.OddAboveDisplacement.displacement_M hL P R N)

end Cvs.Upstream.SchurSylvesterDisplacement
