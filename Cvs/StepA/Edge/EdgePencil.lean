import Mathlib
import Cvs.StepA.Edge.ComplexWeightDiscriminant
import Cvs.StepA.Edge.DampedEdgeGram
import Cvs.StepA.Edge.EdgeDiscriminant
import Cvs.StepA.Edge.EdgeSpace
import Cvs.StepA.Edge.ExtremeEigenvalueSum
import Cvs.StepA.Edge.TwoEdgeSplit
import Cvs.Upstream.RayleighQuotientExtremes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge pencil at complex weights

At complex weights `z` the edge form of a combination `comb x` is `(Gx)ᵀ B(z) (Gx)` with
`B(z) = diag([[Re zᵢ, Im zᵢ], [Im zᵢ, −Re zᵢ]])`, so on the edge space it is the quadratic form of
the self-adjoint operator `A(z) = B(z)G`. The edge supremum and infimum at `z` are the extreme
eigenvalues of `A(z)`, and with every weight nonzero `A(z)` has a positive and a negative one.
-/

noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
open Cvs.StepA.Edge.DampedEdgeGram (gram)
open Cvs.StepA.Edge.EdgeDiscriminant (edgeRay)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The edge block of a complex weight, `[[Re z, Im z], [Im z, −Re z]]`. -/
def edgeBlockZ (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![z.re, z.im; z.im, -z.re]

/-- The edge matrix at complex weights, `B(z) = diag(edgeBlockZ zᵢ)`. -/
def edgeBZ (z : ι → ℂ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ :=
  blockDiagonal fun i => edgeBlockZ (z i)

/-- The edge pencil at complex weights, `M(z) = B(z)G`. -/
def edgeMZ (δ : ℝ) (g : ι → ℝ) (z : ι → ℂ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ :=
  edgeBZ z * gram δ g

variable (P : EdgeData ι)

omit [Fintype ι] in
/-- `B(z)` is symmetric. -/
private theorem edgeBZ_transpose (z : ι → ℂ) : (edgeBZ z)ᵀ = edgeBZ z := by
  rw [edgeBZ, blockDiagonal_transpose]
  congr 1
  funext i
  ext e f
  fin_cases e <;> fin_cases f <;> simp [edgeBlockZ]

omit [Fintype ι] in
/-- `B(z)` is additive in the weights. -/
private theorem edgeBZ_add (z z' : ι → ℂ) : edgeBZ (z + z') = edgeBZ z + edgeBZ z' := by
  rw [edgeBZ, edgeBZ, edgeBZ, ← blockDiagonal_add]
  congr 1
  funext i
  ext e f
  fin_cases e <;> fin_cases f <;> simp [edgeBlockZ, add_comm]

omit [Fintype ι] in
/-- `B(z)` is real-homogeneous in the weights. -/
private theorem edgeBZ_real_smul (r : ℝ) (z : ι → ℂ) :
    edgeBZ (fun i => (r : ℂ) * z i) = r • edgeBZ z := by
  rw [edgeBZ, edgeBZ, ← blockDiagonal_smul]
  congr 1
  funext i
  ext e f
  fin_cases e <;> fin_cases f <;> simp [edgeBlockZ]

/-- The edge operator `A(z) = M(z)` on the edge space. -/
def opA (z : ι → ℂ) : EdgeV P →L[ℝ] EdgeV P := ofLin P (mulVecLin (edgeMZ P.δ P.g z))

-- merged §0.2; Cvs.StepA.Edge.ExtremeEigenvalueSum edgeForm_eq_pairVec pattern
/-- The quadratic form of `A(z)`: `⟪A(z)x, y⟫ = (Gx)ᵀ B(z) (Gy)`. -/
theorem inner_opA (z : ι → ℂ) (x y : EdgeV P) :
    ⟪opA P z x, y⟫ = (gram P.δ P.g *ᵥ x.vec) ⬝ᵥ (edgeBZ z *ᵥ (gram P.δ P.g *ᵥ y.vec)) := by
  rw [inner_def]
  change (edgeMZ P.δ P.g z *ᵥ x.vec) ⬝ᵥ (gram P.δ P.g *ᵥ y.vec) = _
  rw [edgeMZ, ← mulVec_mulVec, dotProduct_mulVec (gram P.δ P.g *ᵥ x.vec), ← mulVec_transpose,
    edgeBZ_transpose]

-- merged §0.2
/-- `A(z)` is self-adjoint. -/
theorem opA_isSelfAdjoint (z : ι → ℂ) : IsSelfAdjoint (opA P z) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change ⟪opA P z x, y⟫ = ⟪x, opA P z y⟫
  rw [real_inner_comm (opA P z y) x, inner_opA, inner_opA, dotProduct_mulVec, ← mulVec_transpose,
    edgeBZ_transpose, dotProduct_comm]

/-- `A(z)` is symmetric: `⟪A(z)x, y⟫ = ⟪x, A(z)y⟫`. -/
theorem inner_opA_comm (z : ι → ℂ) (x y : EdgeV P) : ⟪opA P z x, y⟫ = ⟪x, opA P z y⟫ :=
  (opA_isSelfAdjoint P z).isSymmetric x y

/-! ### Linearity in the weights -/

-- `B(z)` is real-linear in `z`
/-- `A` is additive in the weights. -/
theorem opA_add (z z' : ι → ℂ) : opA P (z + z') = opA P z + opA P z' := by
  ext x
  change edgeMZ P.δ P.g (z + z') *ᵥ x.vec = edgeMZ P.δ P.g z *ᵥ x.vec + edgeMZ P.δ P.g z' *ᵥ x.vec
  rw [edgeMZ, edgeMZ, edgeMZ, edgeBZ_add, Matrix.add_mul, Matrix.add_mulVec]

-- `B(z)` is real-linear in `z`
/-- `A` is real-homogeneous in the weights. -/
theorem opA_real_smul (r : ℝ) (z : ι → ℂ) :
    opA P (fun i => (r : ℂ) * z i) = r • opA P z := by
  ext x
  change edgeMZ P.δ P.g (fun i => (r : ℂ) * z i) *ᵥ x.vec = r • (edgeMZ P.δ P.g z *ᵥ x.vec)
  rw [edgeMZ, edgeMZ, edgeBZ_real_smul, Matrix.smul_mul, Matrix.smul_mulVec]

/-- `A` is odd in the weights. -/
theorem opA_neg (z : ι → ℂ) : opA P (-z) = -opA P z := by
  have h := opA_real_smul P (-1) z
  rw [show (fun i => (((-1 : ℝ)) : ℂ) * z i) = -z from by funext i; simp] at h
  rw [h]
  exact neg_one_smul ℝ (opA P z)

/-- A block-diagonal bilinear form: `uᵀ diag(dᵢ) w = ∑ᵢ ∑ₑ ∑_f u_{(e,i)} dᵢ(e,f) w_{(f,i)}`. -/
private theorem dotProduct_blockDiagonal_mulVec₂ (d : ι → Matrix (Fin 2) (Fin 2) ℝ)
    (u w : Fin 2 × ι → ℝ) :
    u ⬝ᵥ (blockDiagonal d *ᵥ w) = ∑ i, ∑ e, ∑ f, u (e, i) * d i e f * w (f, i) := by
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun f _ => ?_
  ring

/-- The bilinear form of `B(z)`, blockwise:
`uᵀB(z)w = ∑ᵢ Re zᵢ (u₀w₀ − u₁w₁) + Im zᵢ (u₀w₁ + u₁w₀)`. -/
private theorem dotProduct_edgeBZ_mulVec (z : ι → ℂ) (u w : Fin 2 × ι → ℝ) :
    u ⬝ᵥ (edgeBZ z *ᵥ w) = ∑ i, ((z i).re * (u (0, i) * w (0, i) - u (1, i) * w (1, i))
      + (z i).im * (u (0, i) * w (1, i) + u (1, i) * w (0, i))) := by
  rw [edgeBZ, dotProduct_blockDiagonal_mulVec₂]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.sum_univ_two, edgeBlockZ, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one]
  ring

/-- One block of `B(z)` is bounded by `|c|`:
`(Re c (pr − qs) + Im c (ps + qr))² ≤ |c|² (p² + q²)(r² + s²)`. -/
private theorem sq_block_le (c : ℂ) (p q r s : ℝ) :
    (c.re * (p * r - q * s) + c.im * (p * s + q * r)) ^ 2
      ≤ ‖c‖ ^ 2 * ((p ^ 2 + q ^ 2) * (r ^ 2 + s ^ 2)) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have e : (c.re * c.re + c.im * c.im) * ((p ^ 2 + q ^ 2) * (r ^ 2 + s ^ 2))
      - (c.re * (p * r - q * s) + c.im * (p * s + q * r)) ^ 2
      = (c.re * (p * s + q * r) - c.im * (p * r - q * s)) ^ 2 := by ring
  linarith [sq_nonneg (c.re * (p * s + q * r) - c.im * (p * r - q * s))]

omit [Fintype ι] [DecidableEq ι] in
/-- The two diagonal Gram entries of one ordinate sum to `1/(2δ)`. -/
private theorem gram_diag_add (i : ι) :
    gram P.δ P.g (0, i) (0, i) + gram P.δ P.g (1, i) (1, i) = 1 / (2 * P.δ) := by
  rw [Cvs.StepA.Edge.DampedEdgeGram.gram_cos_cos, Cvs.StepA.Edge.DampedEdgeGram.gram_sin_sin]
  have hδ := P.hδ
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  field_simp
  ring

/-- The coordinate `(Gx)_{(e,i)}` is the inner product of `x` with the coordinate vector. -/
private theorem inner_single_left (x : EdgeV P) (k : Fin 2 × ι) :
    ⟪(show EdgeV P from Pi.single k (1 : ℝ)), x⟫ = (gram P.δ P.g *ᵥ x.vec) k := by
  rw [inner_def]
  change Pi.single k (1 : ℝ) ⬝ᵥ (gram P.δ P.g *ᵥ x.vec) = _
  rw [single_dotProduct, one_mul]

/-- The squared norm of a coordinate vector is the diagonal Gram entry. -/
private theorem inner_single_single (k : Fin 2 × ι) :
    ⟪(show EdgeV P from Pi.single k (1 : ℝ)), (show EdgeV P from Pi.single k (1 : ℝ))⟫
      = gram P.δ P.g k k := by
  rw [inner_single_left]
  change (gram P.δ P.g *ᵥ Pi.single k (1 : ℝ)) k = _
  simp [mulVec_single]

/-- **The pairing bound**: `(Gx)²_{(0,i)} + (Gx)²_{(1,i)} ≤ ‖x‖²/(2δ)`. -/
private theorem gram_pair_sq_le (x : EdgeV P) (i : ι) :
    (gram P.δ P.g *ᵥ x.vec) (0, i) ^ 2 + (gram P.δ P.g *ᵥ x.vec) (1, i) ^ 2
      ≤ ‖x‖ ^ 2 / (2 * P.δ) := by
  have hcs : ∀ k : Fin 2 × ι, (gram P.δ P.g *ᵥ x.vec) k ^ 2 ≤ gram P.δ P.g k k * ‖x‖ ^ 2 := by
    intro k
    have h := real_inner_mul_inner_self_le (show EdgeV P from Pi.single k (1 : ℝ)) x
    rw [inner_single_left, inner_single_single, real_inner_self_eq_norm_sq] at h
    rw [sq]
    exact h
  have h0 := hcs (0, i)
  have h1 := hcs (1, i)
  have hd := gram_diag_add P i
  calc _ ≤ gram P.δ P.g (0, i) (0, i) * ‖x‖ ^ 2 + gram P.δ P.g (1, i) (1, i) * ‖x‖ ^ 2 :=
        add_le_add h0 h1
    _ = ‖x‖ ^ 2 / (2 * P.δ) := by rw [← add_mul, hd]; ring

/-- **The bilinear bound**: `⟪A(v)x, y⟫ ≤ (∑ᵢ ‖vᵢ‖/(2δ)) ‖x‖ ‖y‖`. -/
private theorem inner_opA_le (v : ι → ℂ) (x y : EdgeV P) :
    ⟪opA P v x, y⟫ ≤ (∑ i, ‖v i‖) / (2 * P.δ) * ‖x‖ * ‖y‖ := by
  rw [inner_opA, dotProduct_edgeBZ_mulVec]
  have hδ := P.hδ
  calc _ ≤ ∑ i, ‖v i‖ * (‖x‖ * ‖y‖ / (2 * P.δ)) := by
        refine Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_
        refine abs_le_of_sq_le_sq ?_ (by positivity)
        refine (sq_block_le (v i) _ _ _ _).trans ?_
        have hx := gram_pair_sq_le P x i
        have hy := gram_pair_sq_le P y i
        have e : (‖v i‖ * (‖x‖ * ‖y‖ / (2 * P.δ))) ^ 2
            = ‖v i‖ ^ 2 * ((‖x‖ ^ 2 / (2 * P.δ)) * (‖y‖ ^ 2 / (2 * P.δ))) := by ring
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hx hy (by positivity) (by positivity)
    _ = (∑ i, ‖v i‖) / (2 * P.δ) * ‖x‖ * ‖y‖ := by rw [← Finset.sum_mul]; ring

/-- Every coefficient vector is `G x` for some `x` in the edge space (`G` is invertible). -/
private theorem exists_gram_mulVec_eq (p : Fin 2 × ι → ℝ) :
    ∃ x : EdgeV P, gram P.δ P.g *ᵥ x.vec = p :=
  ⟨(show EdgeV P from (gram P.δ P.g)⁻¹ *ᵥ p), by
    change gram P.δ P.g *ᵥ ((gram P.δ P.g)⁻¹ *ᵥ p) = p
    rw [mulVec_mulVec, Cvs.StepA.Edge.ExtremeEigenvalueSum.mul_inv_of_posDef
      (Cvs.StepA.Edge.DampedEdgeGram.gram_posDef P.hδ P.hg0 P.hg), one_mulVec]⟩

omit [DecidableEq ι] in
/-- `x ↦ G x` is injective on the edge space. -/
private theorem ne_zero_of_gram_mulVec_ne_zero {x : EdgeV P} (h : gram P.δ P.g *ᵥ x.vec ≠ 0) :
    x ≠ 0 := by
  rintro rfl
  exact h (mulVec_zero _)

-- merged §0 (F2), Cauchy–Schwarz Cvs.StepA.Edge.TwoEdgeSplit norm_sq_edgePair_le
/-- `‖A(v)x‖ ≤ (∑ᵢ ‖vᵢ‖ / (2δ)) ‖x‖`. -/
theorem norm_opA_apply_le (v : ι → ℂ) (x : EdgeV P) :
    ‖opA P v x‖ ≤ (∑ i, ‖v i‖) / (2 * P.δ) * ‖x‖ := by
  have h := inner_opA_le P v x (opA P v x)
  rw [real_inner_self_eq_norm_sq] at h
  rcases (norm_nonneg (opA P v x)).eq_or_lt with h0 | hpos
  · rw [← h0]
    have := P.hδ
    positivity
  · refine le_of_mul_le_mul_right ?_ hpos
    nlinarith

/-! ### The edge discriminant as the sum of the extreme eigenvalues -/

omit [DecidableEq ι] in
/-- The squared norm of the edge space is `xᵀ G x`. -/
private theorem norm_sq_eq (x : EdgeV P) : ‖x‖ ^ 2 = x.vec ⬝ᵥ (gram P.δ P.g *ᵥ x.vec) := by
  rw [← real_inner_self_eq_norm_sq, inner_def]

open Cvs.StepA.Edge.DampedEdgeGram in
/-- **The edge form in the pairing coordinates**: `edgeFormZ(F, a) = pᵀB(z)p` with `p = p(F, a)`,
for continuous `F`. -/
private theorem edgeFormZ_eq_pairVec (z : ι → ℂ) {F : ℝ → ℝ} (hF : Continuous F) (a : ℝ) :
    edgeFormZ P.δ P.g z F a
      = pairVec P.δ P.g F a ⬝ᵥ (edgeBZ z *ᵥ pairVec P.δ P.g F a) := by
  rw [dotProduct_edgeBZ_mulVec]
  unfold edgeFormZ
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pairVec_eq P.δ P.g hF, edgeUnit, cons_val_zero, cons_val_one, one_mul, sq,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- **The top of `A(z)` is nonnegative**: the diagonal blocks of `B(z)` are traceless. -/
private theorem lamMax_nonneg [Nonempty ι] (z : ι → ℂ) : 0 ≤ lamMax (opA P z) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have key : ∀ e : Fin 2, ∃ y : EdgeV P, y ≠ 0 ∧ ⟪opA P z y, y⟫ = edgeBZ z (e, i) (e, i) := by
    intro e
    obtain ⟨y, hy⟩ := exists_gram_mulVec_eq P (Pi.single (e, i) 1)
    refine ⟨y, ne_zero_of_gram_mulVec_ne_zero P (by rw [hy]; simp), ?_⟩
    rw [inner_opA, hy, mulVec_single, single_dotProduct]
    simp
  obtain ⟨y₀, hy₀, e₀⟩ := key 0
  obtain ⟨y₁, hy₁, e₁⟩ := key 1
  have hsum : edgeBZ z (0, i) (0, i) + edgeBZ z (1, i) (1, i) = 0 := by
    simp [edgeBZ, edgeBlockZ]
  by_cases h : 0 ≤ edgeBZ z (0, i) (0, i)
  · exact le_lamMax_of hy₀ (by rw [e₀, zero_mul]; exact h)
  · exact le_lamMax_of hy₁ (by rw [e₁, zero_mul]; linarith)

open Cvs.StepA.Edge.DampedEdgeGram in
/-- **The edge form lies below the top of `A(z)`**: `edgeFormZ(F, a) ≤ lamMax A(z) ∫₀^a F²` for
continuous `F` and `a ≥ 0`. -/
private theorem edgeFormZ_le [Nonempty ι] (z : ι → ℂ) {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ}
    (ha : 0 ≤ a) : edgeFormZ P.δ P.g z F a ≤ lamMax (opA P z) * ∫ u in (0 : ℝ)..a, F u ^ 2 := by
  obtain ⟨y, hy⟩ := exists_gram_mulVec_eq P (pairVec P.δ P.g F a)
  have h1 : edgeFormZ P.δ P.g z F a ≤ lamMax (opA P z) * ‖y‖ ^ 2 := by
    rw [edgeFormZ_eq_pairVec P z hF, ← hy, ← inner_opA]
    exact inner_le_lamMax _ _
  have h2 := bessel P.δ P.g hF y.vec ha
  have h3 := quad_gramOn_le P.hδ P.g y.vec ha
  rw [← hy] at h2
  have h4 : ‖y‖ ^ 2 ≤ ∫ u in (0 : ℝ)..a, F u ^ 2 := by
    rw [norm_sq_eq]
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_left h4 (lamMax_nonneg P z))

/-- The edge Rayleigh quotients at complex weights lie below `lamMax A(z)`. -/
private theorem le_lamMax_of_mem_edgeRayZ [Nonempty ι] (z : ι → ℂ) :
    ∀ r ∈ edgeRayZ P.δ P.g z, r ≤ lamMax (opA P z) := by
  rintro r ⟨F, a, hF, hpos, rfl⟩
  rw [div_le_iff₀ hpos]
  exact edgeFormZ_le P z hF (Cvs.StepA.Edge.EdgeDiscriminant.pos_of_integral_sq_pos hpos).le

omit [DecidableEq ι] in
/-- The edge Rayleigh quotients at complex weights form a nonempty set. -/
private theorem edgeRayZ_nonempty (z : ι → ℂ) : (edgeRayZ P.δ P.g z).Nonempty :=
  ⟨_, fun _ => 1, 1, continuous_const, by simp, rfl⟩

open Filter Topology Cvs.StepA.Edge.DampedEdgeGram in
/-- **Edge combinations approach every Rayleigh quotient of `A(z)`**: for `x ≠ 0` and bounded edge
Rayleigh quotients, `⟪A(z)x, x⟫/‖x‖² ≤ sSup edgeRayZ`. -/
private theorem inner_div_le_sSup (z : ι → ℂ) {x : EdgeV P} (hx : x ≠ 0)
    (hbdd : BddAbove (edgeRayZ P.δ P.g z)) :
    ⟪opA P z x, x⟫ / ‖x‖ ^ 2 ≤ sSup (edgeRayZ P.δ P.g z) := by
  have hGx : 0 < x.vec ⬝ᵥ (gram P.δ P.g *ᵥ x.vec) := by
    rw [← norm_sq_eq]
    exact pow_pos (norm_pos_iff.mpr hx) 2
  have hnum : Tendsto (fun b => (gramOn P.δ P.g b *ᵥ x.vec) ⬝ᵥ
      (edgeBZ z *ᵥ (gramOn P.δ P.g b *ᵥ x.vec))) atTop
      (𝓝 ((gram P.δ P.g *ᵥ x.vec) ⬝ᵥ (edgeBZ z *ᵥ (gram P.δ P.g *ᵥ x.vec)))) := by
    have hc : Continuous fun M : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ =>
        (M *ᵥ x.vec) ⬝ᵥ (edgeBZ z *ᵥ (M *ᵥ x.vec)) :=
      (continuous_id.matrix_mulVec continuous_const).dotProduct
        (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))
    exact (hc.tendsto _).comp (tendsto_gramOn P.hδ P.g)
  have hq := hnum.div (tendsto_quad_gramOn P.hδ P.g x.vec) hGx.ne'
  rw [← inner_opA, ← norm_sq_eq] at hq
  refine le_of_tendsto hq ?_
  filter_upwards [(tendsto_quad_gramOn P.hδ P.g x.vec).eventually (lt_mem_nhds hGx)] with b hb
  have hmem : edgeFormZ P.δ P.g z (comb P.δ P.g x.vec) b
      / ∫ u in (0 : ℝ)..b, comb P.δ P.g x.vec u ^ 2 ∈ edgeRayZ P.δ P.g z := by
    refine ⟨comb P.δ P.g x.vec, b, continuous_comb P.δ P.g x.vec, ?_, rfl⟩
    rwa [← quad_gramOn]
  rw [edgeFormZ_eq_pairVec P z (continuous_comb P.δ P.g x.vec), pairVec_comb, ← quad_gramOn]
    at hmem
  exact le_csSup hbdd hmem

-- merged §0.3, lean gap 4(a); copy of Cvs.StepA.Edge.ExtremeEigenvalueSum l.213-397 at complex weights
/-- **The edge supremum is `lamMax A(z)`**, at every complex weight. -/
theorem sSup_edgeRayZ [Nonempty ι] (z : ι → ℂ) :
    sSup (edgeRayZ P.δ P.g z) = lamMax (opA P z) := by
  have hub := le_lamMax_of_mem_edgeRayZ P z
  refine le_antisymm (csSup_le (edgeRayZ_nonempty P z) hub) ?_
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : EdgeV P)
  have : Nonempty {x : EdgeV P // x ≠ 0} := ⟨⟨x₀, hx₀⟩⟩
  refine ciSup_le fun x => ?_
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real]
  exact inner_div_le_sSup P z x.2 ⟨_, hub⟩

/-- **The edge infimum is `lamMin A(z)`**, at every complex weight. -/
theorem sInf_edgeRayZ [Nonempty ι] (z : ι → ℂ) :
    sInf (edgeRayZ P.δ P.g z) = lamMin (opA P z) := by
  have h := sSup_edgeRayZ P (-z)
  rw [edgeRayZ_neg, Real.sSup_neg, opA_neg] at h
  rw [lamMin_eq_neg_lamMax_neg, ← h, neg_neg]

/-- **The edge discriminant is `lamMax A(z) + lamMin A(z)`**, at every complex weight. -/
theorem edgeDiscZ_eq [Nonempty ι] (z : ι → ℂ) :
    edgeDiscZ P.δ P.g z = lamMax (opA P z) + lamMin (opA P z) := by
  rw [edgeDiscZ, sSup_edgeRayZ, sInf_edgeRayZ]

/-! ### The signature -/

-- merged §0 (F1), lean gap 4(b): the map `x ↦ (P_q x)_q` is a real bijection onto `ℂ^k`
-- (an earlier result principalNonsing_cauchy), so prescribing `P_q = e^{−i arg zᵢ/2}` gives `⟪A x, x⟫ > 0`
/-- **A positive direction**: with some weight nonzero, `⟪A(z)x, x⟫ > 0` for some `x`. -/
theorem exists_inner_opA_pos {z : ι → ℂ} (hz : ∃ i, z i ≠ 0) :
    ∃ x : EdgeV P, 0 < ⟪opA P z x, x⟫ := by
  obtain ⟨i, hi⟩ := hz
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_eq_mul_self (z i)
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hi (by rw [hw, zero_mul])
  have hn : 0 < w.re * w.re + w.im * w.im := by
    rw [← Complex.normSq_apply]
    exact Complex.normSq_pos.mpr hw0
  obtain ⟨x, hx⟩ := exists_gram_mulVec_eq P
    (fun k => if k.2 = i then ![w.re, w.im] k.1 else 0)
  refine ⟨x, ?_⟩
  rw [inner_opA, hx, dotProduct_edgeBZ_mulVec, Finset.sum_eq_single i]
  · simp only [if_true, cons_val_zero, cons_val_one, hw, Complex.mul_re, Complex.mul_im]
    have e : (w.re * w.re - w.im * w.im) * (w.re * w.re - w.im * w.im)
        + (w.re * w.im + w.im * w.re) * (w.re * w.im + w.im * w.re)
        = (w.re * w.re + w.im * w.im) ^ 2 := by ring
    rw [e]
    exact pow_pos hn 2
  · intro j _ hj
    simp [hj]
  · simp

/-- **The signature**: with some weight nonzero, `lamMin A(z) < 0 < lamMax A(z)`. -/
theorem lamMin_neg_lamMax_pos {z : ι → ℂ} (hz : ∃ i, z i ≠ 0) :
    lamMin (opA P z) < 0 ∧ 0 < lamMax (opA P z) := by
  obtain ⟨x, hx⟩ := exists_inner_opA_pos P hz
  obtain ⟨y, hy⟩ := exists_inner_opA_pos P (z := -z) (by
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, neg_ne_zero.mpr hi⟩)
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  rw [opA_neg, _root_.neg_apply, inner_neg_left] at hy
  have hxn : 0 < ‖x‖ ^ 2 := by positivity
  have hyn : 0 < ‖y‖ ^ 2 := by positivity
  constructor
  · refine lt_of_le_of_lt (lamMin_le_of hy0 (c := ⟪opA P z y, y⟫ / ‖y‖ ^ 2) ?_) ?_
    · rw [div_mul_cancel₀ _ hyn.ne']
    · exact div_neg_of_neg_of_pos (by linarith) hyn
  · refine lt_of_lt_of_le ?_ (le_lamMax_of hx0 (c := ⟪opA P z x, x⟫ / ‖x‖ ^ 2) ?_)
    · exact div_pos hx hxn
    · rw [div_mul_cancel₀ _ hxn.ne']

end Cvs.StepA.Edge.PlanarBoxLemma
