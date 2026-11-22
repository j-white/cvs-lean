import Mathlib
import Cvs.StepA.Edge.CauchyPairingIdentity
import Cvs.StepA.Edge.ComplexWeightDiscriminant
import Cvs.StepA.Edge.DampedEdgeGram
import Cvs.StepA.Edge.EdgePencil
import Cvs.StepA.Edge.EdgeSpace
import Cvs.StepA.Edge.ExtremeEigenvalueSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The operator identities of the edge pencil

On the edge space, `D = −d/du` satisfies `D + D* = κκ*`, the pencil satisfies `DA = AD*`, hence
`AD + DA = (Aκ)κ*`; an eigenvector vanishing at `0` is reflected by `D` to the opposite eigenvalue,
eigenvectors pair as `(λ + ν)⟪Dx, y⟫ = ν x(0) y(0)`, and the orbit and heat derivatives of the
pencil are `(D − δ)A` and `(D − δ)A(D* − δ)`, with a second-order Taylor bound along the flow.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : EdgeData ι)

/-- `κκ*`, the rank-one operator `x ↦ ⟪κ, x⟫ κ`. -/
def rk : EdgeV P →L[ℝ] EdgeV P := InnerProductSpace.rankOne ℝ (kap P) (kap P)

omit [DecidableEq ι] in
@[simp] theorem rk_apply (x : EdgeV P) : rk P x = ⟪kap P, x⟫ • kap P := rfl

/-- `D − δ`. -/
def opDδ : EdgeV P →L[ℝ] EdgeV P := opD P - P.δ • ContinuousLinearMap.id ℝ (EdgeV P)

/-- The orbit derivative of the pencil, `A_ξ = (D − δ)A`. -/
def opAxi (z : ι → ℂ) : EdgeV P →L[ℝ] EdgeV P := opDδ P ∘L opA P z

/-- The heat derivative of the pencil, `A_ζ = (D − δ)A(D* − δ)`. -/
def opAzeta (z : ι → ℂ) : EdgeV P →L[ℝ] EdgeV P :=
  opDδ P ∘L opA P z ∘L ContinuousLinearMap.adjoint (opDδ P)

/-! ### Coefficient matrices -/

/-- The block-diagonal matrix `diag([[d, −gᵢ], [gᵢ, d]])`: at `d = δ` the matrix of `D`, at `d = 0`
that of `D − δ`. -/
private def derMat (d : ℝ) (g : ι → ℝ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ :=
  Matrix.blockDiagonal fun i => !![d, -g i; g i, d]

open Matrix Cvs.StepA.Edge.CauchyPairingIdentity in
/-- `edgeDer` is multiplication by `derMat δ g`. -/
private theorem edgeDer_eq_mulVec (δ : ℝ) (g : ι → ℝ) (v : Fin 2 × ι → ℝ) :
    edgeDer δ g v = derMat δ g *ᵥ v := by
  funext ⟨e, i⟩
  fin_cases e
  · simp [edgeDer, derMat, mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    ring
  · simp [edgeDer, derMat, mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two]

open Matrix Cvs.StepA.Edge.CauchyPairingIdentity in
/-- `edgeDer δ g v − δ v` is multiplication by `derMat 0 g`. -/
private theorem edgeDer_sub_smul (δ : ℝ) (g : ι → ℝ) (v : Fin 2 × ι → ℝ) :
    edgeDer δ g v - δ • v = derMat 0 g *ᵥ v := by
  funext ⟨e, i⟩
  fin_cases e <;>
    simp [edgeDer, derMat, mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two]

open Matrix in
/-- `derMat d g · B(z) = B(z) · derMat d gᵀ`, blockwise. -/
private theorem derMat_mul_edgeBZ (d : ℝ) (g : ι → ℝ) (z : ι → ℂ) :
    derMat d g * edgeBZ z = edgeBZ z * (derMat d g)ᵀ := by
  rw [derMat, edgeBZ, blockDiagonal_transpose, ← blockDiagonal_mul, ← blockDiagonal_mul]
  congr 1
  funext i
  ext e f
  fin_cases e <;> fin_cases f <;> simp [edgeBlockZ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

open Matrix in
/-- `derMat 0 g · B(z) = B((i gᵢ zᵢ)ᵢ)`, blockwise. -/
private theorem derMat_zero_mul_edgeBZ (g : ι → ℝ) (z : ι → ℂ) :
    derMat 0 g * edgeBZ z = edgeBZ (fun i => (g i : ℂ) * Complex.I * z i) := by
  rw [derMat, edgeBZ, edgeBZ, ← blockDiagonal_mul]
  congr 1
  funext i
  ext e f
  fin_cases e <;> fin_cases f <;> simp [edgeBlockZ, Matrix.mul_apply, Fin.sum_univ_two]

omit [Fintype ι] in
open Matrix in
/-- `B(z)` is symmetric. -/
private theorem edgeBZ_transpose (z : ι → ℂ) : (edgeBZ z)ᵀ = edgeBZ z := by
  rw [edgeBZ, blockDiagonal_transpose]
  congr 1
  funext i
  ext e f
  fin_cases e <;> fin_cases f <;> simp [edgeBlockZ]

omit [DecidableEq ι] in
open Matrix in
/-- `(Av) ⬝ w = v ⬝ (Aᵀw)`. -/
private theorem dot_mulVec_left (A : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ) (v w : Fin 2 × ι → ℝ) :
    (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [dotProduct_transpose_mulVec, dotProduct_comm]

/-- The indicator of the cosine coordinates, the coefficient vector of evaluation at `0`. -/
private def cosInd : Fin 2 × ι → ℝ := fun k => if k.1 = 0 then 1 else 0

open Matrix Cvs.StepA.Edge.DampedEdgeGram in
/-- **`G D + Dᵀ G = k kᵀ`** with `k` the cosine indicator, for `δ ≠ 0`. -/
private theorem gram_derMat {δ : ℝ} (hδ : δ ≠ 0) (g : ι → ℝ) :
    gram δ g * derMat δ g + (derMat δ g)ᵀ * gram δ g = vecMulVec cosInd cosInd := by
  ext ⟨e, i⟩ ⟨f, j⟩
  have hA : 4 * δ ^ 2 + (g i + g j) ^ 2 ≠ 0 := by positivity
  have hB : 4 * δ ^ 2 + (g i - g j) ^ 2 ≠ 0 := by positivity
  simp only [derMat, Matrix.add_apply, Matrix.mul_apply, transpose_apply, blockDiagonal_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Fin.sum_univ_two, vecMulVec_apply, cosInd]
  fin_cases e <;> fin_cases f <;>
    simp [gram_cos_cos, gram_sin_sin, gram_cos_sin, gram_sin_cos] <;> field_simp <;> ring

omit [DecidableEq ι] in
open Matrix Cvs.StepA.Edge.CauchyPairingIdentity in
/-- `v ⬝ (k kᵀ w) = κ(v) κ(w)`. -/
private theorem dot_vecMulVec_cosInd (v w : Fin 2 × ι → ℝ) :
    v ⬝ᵥ (vecMulVec cosInd cosInd *ᵥ w) = edgeVal v * edgeVal w := by
  simp [dotProduct, mulVec, vecMulVec_apply, cosInd, Fintype.sum_prod_type, Fin.sum_univ_two,
    edgeVal, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

open Matrix Cvs.StepA.Edge.DampedEdgeGram in
/-- `(D M)ᵀ G = G (D M)` for `M = B(z) G`: `D A(z)` is symmetric for the inner product. -/
private theorem derMat_edgeMZ_transpose (δ : ℝ) (g : ι → ℝ) (z : ι → ℂ) :
    (derMat δ g * edgeMZ δ g z)ᵀ * gram δ g = gram δ g * (derMat δ g * edgeMZ δ g z) := by
  rw [edgeMZ, transpose_mul, transpose_mul, Cvs.StepA.Edge.ExtremeEigenvalueSum.gram_transpose,
    edgeBZ_transpose, ← Matrix.mul_assoc (derMat δ g), derMat_mul_edgeBZ]
  simp only [Matrix.mul_assoc]

omit [DecidableEq ι] in
open Matrix in
/-- `Mᵀ G = G M` for `M = B G` with `B`, `G` symmetric. -/
private theorem transpose_mul_gram_sym {G B : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ} (hG : Gᵀ = G)
    (hB : Bᵀ = B) : (B * G)ᵀ * G = G * (B * G) := by
  rw [transpose_mul, hG, hB, Matrix.mul_assoc]

/-- `A(z)` is its own adjoint, from `B(z)ᵀ = B(z)` and `Gᵀ = G`. -/
private theorem adjoint_opA (z : ι → ℂ) : ContinuousLinearMap.adjoint (opA P z) = opA P z := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_).symm
  rw [inner_def, inner_def]
  open Matrix Cvs.StepA.Edge.DampedEdgeGram in
  · show (edgeMZ P.δ P.g z *ᵥ x.vec) ⬝ᵥ (gram P.δ P.g *ᵥ y.vec)
        = x.vec ⬝ᵥ (gram P.δ P.g *ᵥ (edgeMZ P.δ P.g z *ᵥ y.vec))
    rw [dot_mulVec_left, mulVec_mulVec, mulVec_mulVec, edgeMZ,
      transpose_mul_gram_sym (Cvs.StepA.Edge.ExtremeEigenvalueSum.gram_transpose _ _) (edgeBZ_transpose z)]

/-! ### P1 -/

-- merged §1 (P1): `D + D* = κκ*` (R1 l.604, l.639; an earlier result frame_gram, Cvs.StepA.Edge.CauchyPairingIdentity cauchyDisp_edgeCauchy)
/-- **`D + D* = κκ*`**: `⟪Dx, y⟫ + ⟪x, Dy⟫ = x(0) y(0)`. -/
theorem inner_opD_add (x y : EdgeV P) :
    ⟪opD P x, y⟫ + ⟪x, opD P y⟫ = ⟪kap P, x⟫ * ⟪kap P, y⟫ := by
  open Matrix Cvs.StepA.Edge.DampedEdgeGram Cvs.StepA.Edge.CauchyPairingIdentity in
  · rw [inner_kap, inner_kap, inner_def, inner_def]
    show edgeDer P.δ P.g x.vec ⬝ᵥ (gram P.δ P.g *ᵥ y.vec)
        + x.vec ⬝ᵥ (gram P.δ P.g *ᵥ edgeDer P.δ P.g y.vec) = edgeVal x.vec * edgeVal y.vec
    rw [edgeDer_eq_mulVec, edgeDer_eq_mulVec, dot_mulVec_left, mulVec_mulVec, mulVec_mulVec,
      ← dotProduct_add, ← add_mulVec, add_comm, gram_derMat P.hδ.ne', dot_vecMulVec_cosInd]

/-- `⟪Dx, x⟫ = x(0)²/2`. -/
theorem inner_opD_self (x : EdgeV P) : ⟪opD P x, x⟫ = ⟪kap P, x⟫ ^ 2 / 2 := by
  have h := inner_opD_add P x x
  rw [real_inner_comm (opD P x) x] at h
  linarith

/-- **The adjoint of `D`** is `κκ* − D`. -/
theorem adjoint_opD : ContinuousLinearMap.adjoint (opD P) = rk P - opD P := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (rk P - opD P) (opD P)).mpr fun x y => ?_).symm
  rw [sub_apply, inner_sub_left, rk_apply, real_inner_smul_left]
  linarith [inner_opD_add P x y]

omit [DecidableEq ι] in
/-- The adjoint of `D − δ` is `D* − δ`. -/
theorem adjoint_opDδ : ContinuousLinearMap.adjoint (opDδ P)
    = ContinuousLinearMap.adjoint (opD P) - P.δ • ContinuousLinearMap.id ℝ (EdgeV P) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ (opDδ P)).mpr fun x y => ?_).symm
  simp only [opDδ, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left]

-- merged §1 (P1): `DA = AD*`, the blockwise identity `D B(z) = B(z) Dᵀ` (R2 l.201)
/-- **`DA = AD*`** at every complex weight. -/
theorem opD_comp_opA (z : ι → ℂ) :
    opD P ∘L opA P z = opA P z ∘L ContinuousLinearMap.adjoint (opD P) := by
  have hsa : opD P ∘L opA P z = ContinuousLinearMap.adjoint (opD P ∘L opA P z) := by
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, inner_def, inner_def]
    open Matrix Cvs.StepA.Edge.DampedEdgeGram Cvs.StepA.Edge.CauchyPairingIdentity in
    · show edgeDer P.δ P.g (edgeMZ P.δ P.g z *ᵥ x.vec) ⬝ᵥ (gram P.δ P.g *ᵥ y.vec)
          = x.vec ⬝ᵥ (gram P.δ P.g *ᵥ edgeDer P.δ P.g (edgeMZ P.δ P.g z *ᵥ y.vec))
      rw [edgeDer_eq_mulVec, edgeDer_eq_mulVec, mulVec_mulVec, mulVec_mulVec, dot_mulVec_left,
        mulVec_mulVec, mulVec_mulVec, derMat_edgeMZ_transpose, Matrix.mul_assoc]
  rw [hsa, ContinuousLinearMap.adjoint_comp, adjoint_opA]

/-- **`AD + DA = (Aκ)κ*`**: `A(Dx) + D(Ax) = ⟪κ, x⟫ Aκ`. -/
theorem opA_opD_add (z : ι → ℂ) (x : EdgeV P) :
    opA P z (opD P x) + opD P (opA P z x) = ⟪kap P, x⟫ • opA P z (kap P) := by
  have h := congrArg (fun T => T x) (opD_comp_opA P z)
  simp only [ContinuousLinearMap.comp_apply, adjoint_opD, sub_apply,
    rk_apply, map_sub, map_smul] at h
  rw [h]
  abel

/-- **The reflection (1b)**: `Ax = μx` with `x(0) = 0` gives `A(Dx) = −μ Dx`. -/
theorem opA_opD_of_eig {z : ι → ℂ} {x : EdgeV P} {μ : ℝ} (hx : opA P z x = μ • x)
    (h0 : ⟪kap P, x⟫ = 0) : opA P z (opD P x) = (-μ) • opD P x := by
  have h := opA_opD_add P z x
  rw [hx, map_smul, h0, zero_smul] at h
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h

/-- **The pairing (P2)**: `Ax = λx`, `Ay = νy` give `(λ + ν)⟪Dx, y⟫ = ν x(0) y(0)`. -/
theorem pairing {z : ι → ℂ} {x y : EdgeV P} {lam nu : ℝ} (hx : opA P z x = lam • x)
    (hy : opA P z y = nu • y) :
    (lam + nu) * ⟪opD P x, y⟫ = nu * ⟪kap P, x⟫ * ⟪kap P, y⟫ := by
  have h := congrArg (fun v => ⟪v, y⟫) (opA_opD_add P z x)
  simp only [inner_add_left, real_inner_smul_left] at h
  rw [inner_opA_comm P z (opD P x) y, inner_opA_comm P z (kap P) y, hy, hx, map_smul,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_right] at h
  linear_combination h

/-! ### The flow derivatives -/

-- merged §1 (P1): `∂_ξ A = (D − δ)A` (R1 l.636: the residue multipliers)
/-- **The orbit derivative**: `A((i gᵢ zᵢ)ᵢ) = (D − δ) A(z)`. -/
theorem opA_mul_I_g (z : ι → ℂ) :
    opA P (fun i => (P.g i : ℂ) * Complex.I * z i) = opAxi P z := by
  ext x
  rw [opAxi, opDδ, ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply]
  open Matrix Cvs.StepA.Edge.CauchyPairingIdentity in
  · show edgeMZ P.δ P.g (fun i => (P.g i : ℂ) * Complex.I * z i) *ᵥ x.vec
        = edgeDer P.δ P.g (edgeMZ P.δ P.g z *ᵥ x.vec) - P.δ • (edgeMZ P.δ P.g z *ᵥ x.vec)
    rw [edgeDer_sub_smul, edgeMZ, edgeMZ, ← derMat_zero_mul_edgeBZ, Matrix.mul_assoc,
      mulVec_mulVec]

/-- `(D − δ)A = A(D* − δ)`. -/
theorem opDδ_comp_opA (z : ι → ℂ) :
    opDδ P ∘L opA P z = opA P z ∘L ContinuousLinearMap.adjoint (opDδ P) := by
  rw [adjoint_opDδ, opDδ, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    opD_comp_opA, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

/-- **The heat derivative**: `A((−gᵢ² zᵢ)ᵢ) = (D − δ) A(z) (D* − δ)`. -/
theorem opA_neg_g_sq (z : ι → ℂ) :
    opA P (fun i => -((P.g i : ℂ) ^ 2) * z i) = opAzeta P z := by
  have h1 := opA_mul_I_g P (fun i => (P.g i : ℂ) * Complex.I * z i)
  have e : (fun i => (P.g i : ℂ) * Complex.I * ((P.g i : ℂ) * Complex.I * z i))
      = fun i => -((P.g i : ℂ) ^ 2) * z i := by
    funext i
    linear_combination ((P.g i : ℂ) ^ 2 * z i) * Complex.I_sq
  rw [e, opAxi, opA_mul_I_g] at h1
  rw [h1, opAxi, opAzeta, opDδ_comp_opA]

/-- `‖e^c − 1 − c‖ ≤ (e^R + 1 + R) ‖c‖²` whenever `‖c‖ ≤ R`. -/
private theorem norm_exp_sub_one_sub_le {c : ℂ} {R : ℝ} (hcR : ‖c‖ ≤ R) :
    ‖Complex.exp c - 1 - c‖ ≤ (Real.exp R + 1 + R) * ‖c‖ ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg c).trans hcR
  have hK : 1 ≤ Real.exp R + 1 + R := by have := Real.exp_pos R; linarith
  by_cases hc : ‖c‖ ≤ 1
  · calc ‖Complex.exp c - 1 - c‖ ≤ ‖c‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hc
      _ ≤ (Real.exp R + 1 + R) * ‖c‖ ^ 2 := le_mul_of_one_le_left (by positivity) hK
  · push Not at hc
    have h1 : 1 ≤ ‖c‖ ^ 2 := by nlinarith
    have hexp : ‖Complex.exp c‖ ≤ Real.exp R := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm c).trans hcR)
    calc ‖Complex.exp c - 1 - c‖ ≤ ‖Complex.exp c‖ + ‖(1 : ℂ)‖ + ‖c‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ Real.exp R + 1 + R := by rw [norm_one]; linarith
      _ ≤ (Real.exp R + 1 + R) * ‖c‖ ^ 2 := le_mul_of_one_le_right (by positivity) h1

/-- The flow exponent `c = i g ξ − g² ζ` has `‖c‖² = (gξ)² + (g²ζ)²`. -/
private theorem sq_norm_flowExp (g ξ ζ : ℝ) :
    ‖((g * ξ : ℝ) : ℂ) * Complex.I - ((g ^ 2 * ζ : ℝ) : ℂ)‖ ^ 2
      = (g * ξ) ^ 2 + (g ^ 2 * ζ) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- On `|ξ|, |ζ| ≤ 1` the flow exponent has `‖i g ξ − g² ζ‖ ≤ |g| + g²`. -/
private theorem norm_flowExp_le (g : ℝ) {ξ ζ : ℝ} (hξ : |ξ| ≤ 1) (hζ : |ζ| ≤ 1) :
    ‖((g * ξ : ℝ) : ℂ) * Complex.I - ((g ^ 2 * ζ : ℝ) : ℂ)‖ ≤ |g| + g ^ 2 := by
  calc _ ≤ ‖((g * ξ : ℝ) : ℂ) * Complex.I‖ + ‖((g ^ 2 * ζ : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ = |g| * |ξ| + g ^ 2 * |ζ| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg g)]
    _ ≤ |g| + g ^ 2 :=
        add_le_add (mul_le_of_le_one_right (abs_nonneg g) hξ)
          (mul_le_of_le_one_right (sq_nonneg g) hζ)

-- merged §2(a): Taylor's theorem for the entire family `A(ξ, ζ) = A(flow ξ ζ z)`
/-- **Second-order Taylor bound along the flow**: on `|ξ|, |ζ| ≤ 1`,
`‖A(flow ξ ζ z) − A(z) − ξ A_ξ − ζ A_ζ‖ ≤ C (ξ² + ζ²)`. -/
theorem taylor_flow (z : ι → ℂ) :
    ∃ C : ℝ, ∀ ξ ζ : ℝ, |ξ| ≤ 1 → |ζ| ≤ 1 → ∀ x : EdgeV P,
      ‖(opA P (flow P.g ξ ζ z) - opA P z - ξ • opAxi P z - ζ • opAzeta P z) x‖
        ≤ C * (ξ ^ 2 + ζ ^ 2) * ‖x‖ := by
  set K : ι → ℝ := fun i => Real.exp (|P.g i| + P.g i ^ 2) + 1 + (|P.g i| + P.g i ^ 2) with hK
  refine ⟨(∑ i, ‖z i‖ * K i * (P.g i ^ 2 + P.g i ^ 4)) / (2 * P.δ),
    fun ξ ζ hξ hζ x => ?_⟩
  set c : ι → ℂ := fun i => ((P.g i * ξ : ℝ) : ℂ) * Complex.I - ((P.g i ^ 2 * ζ : ℝ) : ℂ)
    with hc
  set w : ι → ℂ := fun i => z i * (Complex.exp (c i) - 1 - c i) with hw
  have hsplit : flow P.g ξ ζ z = w + z + (fun i => (ξ : ℂ) * ((P.g i : ℂ) * Complex.I * z i))
      + (fun i => (ζ : ℂ) * (-((P.g i : ℂ) ^ 2) * z i)) := by
    funext i
    simp only [flow, hw, hc, Pi.add_apply]
    push_cast
    ring
  have hop : opA P (flow P.g ξ ζ z) - opA P z - ξ • opAxi P z - ζ • opAzeta P z = opA P w := by
    rw [hsplit, opA_add, opA_add, opA_add, opA_real_smul, opA_real_smul, opA_mul_I_g,
      opA_neg_g_sq]
    abel
  rw [hop]
  refine (norm_opA_apply_le P w x).trans ?_
  have hδ := P.hδ
  have hsum : ∑ i, ‖w i‖ ≤ (∑ i, ‖z i‖ * K i * (P.g i ^ 2 + P.g i ^ 4)) * (ξ ^ 2 + ζ ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have he := norm_exp_sub_one_sub_le (norm_flowExp_le (P.g i) hξ hζ)
    have hsq : ‖c i‖ ^ 2 ≤ (P.g i ^ 2 + P.g i ^ 4) * (ξ ^ 2 + ζ ^ 2) := by
      rw [hc, sq_norm_flowExp]
      nlinarith [mul_nonneg (pow_nonneg (sq_nonneg (P.g i)) 2) (sq_nonneg ξ),
        mul_nonneg (sq_nonneg (P.g i)) (sq_nonneg ζ)]
    have hK0 : 0 ≤ K i := by
      have := Real.exp_pos (|P.g i| + P.g i ^ 2)
      simp only [hK]
      positivity
    rw [hw, norm_mul]
    calc ‖z i‖ * ‖Complex.exp (c i) - 1 - c i‖ ≤ ‖z i‖ * (K i * ‖c i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ ‖z i‖ * (K i * ((P.g i ^ 2 + P.g i ^ 4) * (ξ ^ 2 + ζ ^ 2))) := by gcongr
      _ = ‖z i‖ * K i * (P.g i ^ 2 + P.g i ^ 4) * (ξ ^ 2 + ζ ^ 2) := by ring
  calc (∑ i, ‖w i‖) / (2 * P.δ) * ‖x‖
      ≤ (∑ i, ‖z i‖ * K i * (P.g i ^ 2 + P.g i ^ 4)) * (ξ ^ 2 + ζ ^ 2) / (2 * P.δ) * ‖x‖ := by
        gcongr
    _ = _ := by ring

/-! ### First-order compressions at an eigenvector -/

-- merged §2(e)
/-- **The orbit compression**: `Af = μf` gives `⟪A_ξ f, f⟫ = μ(f(0)²/2 − δ‖f‖²)`. -/
theorem inner_opAxi_of_eig {z : ι → ℂ} {f : EdgeV P} {μ : ℝ} (hf : opA P z f = μ • f) :
    ⟪opAxi P z f, f⟫ = μ * (⟪kap P, f⟫ ^ 2 / 2 - P.δ * ‖f‖ ^ 2) := by
  simp only [opAxi, opDδ, ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, hf, map_smul, inner_sub_left,
    real_inner_smul_left, inner_opD_self, real_inner_self_eq_norm_sq]

-- merged §2(e), Theorem A Step 4
/-- **The heat compression**: `Af = μf` with `f(0) = 0` gives
`⟪A_ζ f, f⟫ = −μ(‖Df‖² − δ²‖f‖²)`. -/
theorem inner_opAzeta_of_eig {z : ι → ℂ} {f : EdgeV P} {μ : ℝ} (hf : opA P z f = μ • f)
    (h0 : ⟪kap P, f⟫ = 0) :
    ⟪opAzeta P z f, f⟫ = -μ * (‖opD P f‖ ^ 2 - P.δ ^ 2 * ‖f‖ ^ 2) := by
  have hadj : ContinuousLinearMap.adjoint (opDδ P) f = -(opD P f + P.δ • f) := by
    rw [adjoint_opDδ, adjoint_opD]
    simp only [sub_apply, rk_apply, h0, zero_smul,
      smul_apply, ContinuousLinearMap.id_apply]
    abel
  have hDf := opA_opD_of_eig P hf h0
  have e1 : ⟪opAzeta P z f, f⟫ = ⟪opA P z (ContinuousLinearMap.adjoint (opDδ P) f),
      ContinuousLinearMap.adjoint (opDδ P) f⟫ := by
    rw [opAzeta, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_right]
  rw [e1, hadj, map_neg, map_add, map_smul, hDf, hf]
  have hc : ⟪opD P f, f⟫ = 0 := by rw [inner_opD_self, h0]; ring
  have hc' : ⟪f, opD P f⟫ = 0 := by rw [real_inner_comm]; exact hc
  simp only [inner_neg_left, inner_neg_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hc, hc', real_inner_self_eq_norm_sq]
  ring

/-! ### `D²` and strict Cauchy–Schwarz -/

-- merged §2(g), odd-chains Theorem A Step 5: `spec D² = {(δ ± igᵢ)²}` is non-real
/-- `D²` has no real eigenvalue: `D(Dx) = a x` with `a` real forces `x = 0`. -/
theorem eq_zero_of_opD_opD {x : EdgeV P} {a : ℝ} (h : opD P (opD P x) = a • x) : x = 0 := by
  open Cvs.StepA.Edge.CauchyPairingIdentity in
  · have h' : edgeDer P.δ P.g (edgeDer P.δ P.g x.vec) = a • x.vec := h
    show x.vec = 0
    funext ⟨e, i⟩
    have h0 := congrFun h' (0, i)
    have h1 := congrFun h' (1, i)
    simp [edgeDer] at h0 h1
    have hb : 0 < (P.δ ^ 2 - P.g i ^ 2 - a) ^ 2 + (2 * P.δ * P.g i) ^ 2 := by
      have := P.hδ
      have := P.hg0 i
      positivity
    have hu : ((P.δ ^ 2 - P.g i ^ 2 - a) ^ 2 + (2 * P.δ * P.g i) ^ 2) * x.vec (0, i) = 0 := by
      linear_combination (P.δ ^ 2 - P.g i ^ 2 - a) * h0 + (2 * P.δ * P.g i) * h1
    have hv : ((P.δ ^ 2 - P.g i ^ 2 - a) ^ 2 + (2 * P.δ * P.g i) ^ 2) * x.vec (1, i) = 0 := by
      linear_combination (-(2 * P.δ * P.g i)) * h0 + (P.δ ^ 2 - P.g i ^ 2 - a) * h1
    fin_cases e
    · exact (mul_eq_zero.mp hu).resolve_left hb.ne'
    · exact (mul_eq_zero.mp hv).resolve_left hb.ne'

-- Step 5
/-- **Strict Cauchy–Schwarz**: `w ≠ 0` with `w(0) (D⁻¹w)(0) = 0` gives
`‖w‖² < ‖D⁻¹w‖ ‖Dw‖`. -/
theorem sq_norm_lt_opDinv_mul_opD {w : EdgeV P} (hw : w ≠ 0)
    (h0 : ⟪kap P, w⟫ * ⟪kap P, opDinv P w⟫ = 0) : ‖w‖ ^ 2 < ‖opDinv P w‖ * ‖opD P w‖ := by
  set a := opDinv P w
  have hDa : opD P a = w := opD_opDinv P w
  have hp := inner_opD_add P a w
  rw [hDa, real_inner_self_eq_norm_sq, mul_comm, h0] at hp
  have hneg : ⟪a, -opD P w⟫ = ‖w‖ ^ 2 := by rw [inner_neg_right]; linarith
  have hle : ‖w‖ ^ 2 ≤ ‖a‖ * ‖opD P w‖ := by
    rw [← hneg, ← norm_neg (opD P w)]
    exact real_inner_le_norm _ _
  refine lt_of_le_of_ne hle fun heq => ?_
  have h1 : ⟪a, -opD P w⟫ = ‖a‖ * ‖-opD P w‖ := by rw [hneg, norm_neg, heq]
  rw [inner_eq_norm_mul_iff_real] at h1
  have ha0 : a ≠ 0 := by
    rintro ha
    rw [ha, map_zero] at hDa
    exact hw hDa.symm
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set c := ‖-opD P w‖
  have h3 : ‖a‖⁻¹ • (c • a) = -(opD P w) := by
    rw [h1, smul_smul, inv_mul_cancel₀ hna.ne', one_smul]
  have h2 : opD P (opD P a) = (-(‖a‖⁻¹ * c)) • a := by
    rw [hDa, neg_smul, ← smul_smul, h3, neg_neg]
  exact ha0 (eq_zero_of_opD_opD P h2)

omit [DecidableEq ι] in
/-- `‖D⁻¹w‖²` is bounded below on the unit sphere. -/
theorem exists_opDinv_lower : ∃ c₁ > 0, ∀ w : EdgeV P, ‖w‖ = 1 → c₁ ≤ ‖opDinv P w‖ ^ 2 := by
  refine ⟨1 / (‖opD P‖ + 1) ^ 2, by positivity, fun w hw => ?_⟩
  have h := (opD P).le_opNorm (opDinv P w)
  rw [opD_opDinv, hw] at h
  have h0 : 0 ≤ ‖opDinv P w‖ := norm_nonneg _
  have hD : 0 ≤ ‖opD P‖ := norm_nonneg _
  have h1 : 1 ≤ (‖opD P‖ + 1) * ‖opDinv P w‖ := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end Cvs.StepA.Edge.PlanarBoxLemma
