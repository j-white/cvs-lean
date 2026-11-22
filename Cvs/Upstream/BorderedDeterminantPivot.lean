import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.SymmetricModeSet
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Upstream.ConstrainedFormPivotChain

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pivot as a bordered-determinant ratio

For `K = [[A, R], [Rᵀ, 0]]` invertible, `A` symmetric, `vᵀAv − 2qᵀv = −gᵀK⁻¹g + (v − w)ᵀA(v − w)` on `Rᵀv = r`.
On the chain of Cvs.Upstream.ConstrainedFormPivotChain this gives `det K_{M+1} = det K_M · κ'_{M+1}`, and the pivot value `κ_{M+1}` is the Schur
pivot `κ'_{M+1}` when `Q_M ≥ 0` on `V_M` and `⊥` otherwise. `K_M` is invertible when `Q_M` is positive definite on
`V_M` and the truncated rows are independent, and invertibility forces independent rows.
-/

noncomputable section

open Matrix

namespace Cvs.Upstream.BorderedDeterminantPivot
open Cvs.ZeroCounting

open Cvs.Upstream.ConstrainedFormPivotChain (qf rows V mem_V kappa kappa_le le_kappa_iff zext zext_top restr_zext qf_restr rows_mulVec_restr)

/-! ### The Lagrange identity for a bordered matrix -/

section Bordered

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]

/-- The bordered matrix `[[A, R], [Rᵀ, 0]]`. -/
def bord (A : Matrix n n ℝ) (R : Matrix n κ ℝ) : Matrix (n ⊕ κ) (n ⊕ κ) ℝ :=
  fromBlocks A R Rᵀ 0

/-- The mode part `w` of `K⁻¹g`. -/
def solW (A : Matrix n n ℝ) (R : Matrix n κ ℝ) (q : n → ℝ) (r : κ → ℝ) : n → ℝ :=
  fun i => ((bord A R)⁻¹ *ᵥ Sum.elim q r) (Sum.inl i)

/-- The multiplier part `λ` of `K⁻¹g`. -/
def solL (A : Matrix n n ℝ) (R : Matrix n κ ℝ) (q : n → ℝ) (r : κ → ℝ) : κ → ℝ :=
  fun k => ((bord A R)⁻¹ *ᵥ Sum.elim q r) (Sum.inr k)

/-- **The stationarity equations**: `(w, λ) = K⁻¹(q, r)` solves `Aw + Rλ = q`, `Rᵀw = r`. -/
theorem bord_solve {A : Matrix n n ℝ} {R : Matrix n κ ℝ} (hK : IsUnit (bord A R).det) (q : n → ℝ)
    (r : κ → ℝ) :
    A *ᵥ solW A R q r + R *ᵥ solL A R q r = q ∧ Rᵀ *ᵥ solW A R q r = r := by
  have hz : bord A R *ᵥ ((bord A R)⁻¹ *ᵥ Sum.elim q r) = Sum.elim q r := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hK, one_mulVec]
  have hsplit : (bord A R)⁻¹ *ᵥ Sum.elim q r = Sum.elim (solW A R q r) (solL A R q r) := by
    funext x; cases x <;> rfl
  rw [hsplit, bord, fromBlocks_mulVec, zero_mulVec, add_zero] at hz
  exact ⟨congrArg (fun f => fun i => f (Sum.inl i)) hz, congrArg (fun f => fun k => f (Sum.inr k)) hz⟩

theorem dot_bord_inv {A : Matrix n n ℝ} {R : Matrix n κ ℝ} (q : n → ℝ) (r : κ → ℝ) :
    Sum.elim q r ⬝ᵥ ((bord A R)⁻¹ *ᵥ Sum.elim q r) = q ⬝ᵥ solW A R q r + r ⬝ᵥ solL A R q r := by
  have hsplit : (bord A R)⁻¹ *ᵥ Sum.elim q r = Sum.elim (solW A R q r) (solL A R q r) := by
    funext x; cases x <;> rfl
  rw [hsplit, sumElim_dotProduct_sumElim]

omit [DecidableEq n] in
theorem dot_mulVec_symm {A : Matrix n n ℝ} (hA : Aᵀ = A) (x y : n → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

omit [DecidableEq n] [DecidableEq κ] in
theorem dot_mulVec_transpose (R : Matrix n κ ℝ) (x : n → ℝ) (l : κ → ℝ) :
    x ⬝ᵥ (R *ᵥ l) = (Rᵀ *ᵥ x) ⬝ᵥ l := by
  rw [dotProduct_mulVec, mulVec_transpose]

/-- **The Lagrange identity**: for `A` symmetric, `K = [[A, R], [Rᵀ, 0]]` invertible and `Rᵀv = r`,
`vᵀAv − 2qᵀv = −(q, r)ᵀK⁻¹(q, r) + (v − w)ᵀA(v − w)`. -/
theorem lagrange {A : Matrix n n ℝ} (hA : Aᵀ = A) {R : Matrix n κ ℝ} (hK : IsUnit (bord A R).det)
    (q : n → ℝ) (r : κ → ℝ) {v : n → ℝ} (hv : Rᵀ *ᵥ v = r) :
    v ⬝ᵥ (A *ᵥ v) - 2 * (q ⬝ᵥ v)
      = -(Sum.elim q r ⬝ᵥ ((bord A R)⁻¹ *ᵥ Sum.elim q r))
        + (v - solW A R q r) ⬝ᵥ (A *ᵥ (v - solW A R q r)) := by
  rw [dot_bord_inv]
  obtain ⟨h1, h2⟩ := bord_solve hK q r
  set w := solW A R q r
  set l := solL A R q r
  set u := v - w with hu
  have hv' : v = w + u := by rw [hu]; abel
  have hRu : Rᵀ *ᵥ u = 0 := by rw [hu, mulVec_sub, hv, h2, sub_self]
  have hqu : q ⬝ᵥ u = u ⬝ᵥ (A *ᵥ w) := by
    rw [← h1, add_dotProduct, dotProduct_comm (A *ᵥ w), dotProduct_comm (R *ᵥ l), dot_mulVec_transpose R u l, hRu,
      zero_dotProduct, add_zero]
  have hqw : q ⬝ᵥ w = w ⬝ᵥ (A *ᵥ w) + r ⬝ᵥ l := by
    rw [← h1, add_dotProduct, dotProduct_comm (A *ᵥ w), dotProduct_comm (R *ᵥ l), dot_mulVec_transpose R w l, h2]
  have hvv : v ⬝ᵥ (A *ᵥ v) = w ⬝ᵥ (A *ᵥ w) + 2 * (u ⬝ᵥ (A *ᵥ w)) + u ⬝ᵥ (A *ᵥ u) := by
    rw [hv', mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, dot_mulVec_symm hA w u]
    ring
  have hqv : q ⬝ᵥ v = q ⬝ᵥ w + q ⬝ᵥ u := by rw [hv', dotProduct_add]
  rw [hqv, hvv, hqu, hqw]
  ring

end Bordered

/-! ### The chain step -/

section Chain

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The leading block `Q_{[0,M]}`. -/
abbrev blk (Q : Matrix ℕ ℕ ℝ) (M : ℕ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  Q.submatrix Fin.val Fin.val

/-- **The bordered matrix of the chain** `K_M = [[Q_{[0,M]}, R_M], [R_Mᵀ, 0]]`. -/
def K (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (M : ℕ) : Matrix (Fin (M + 1) ⊕ κ) (Fin (M + 1) ⊕ κ) ℝ :=
  bord (blk Q M) (rows r M)ᵀ

/-- The new column of `Q` at step `M+1`. -/
def qcol (Q : Matrix ℕ ℕ ℝ) (M : ℕ) : Fin (M + 1) → ℝ := fun i => Q i (M + 1)

/-- The new constraint coordinates at step `M+1`. -/
def rcol (r : κ → ℕ → ℝ) (M : ℕ) : κ → ℝ := fun k => r k (M + 1)

/-- The border vector `g = (q, r)` of step `M+1`. -/
def gvec (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (M : ℕ) : Fin (M + 1) ⊕ κ → ℝ :=
  Sum.elim (qcol Q M) (rcol r M)

/-- **The Schur pivot** `κ'_{M+1} = Q_{M+1,M+1} − gᵀK_M⁻¹g`. -/
def schur (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (M : ℕ) : ℝ :=
  Q (M + 1) (M + 1) - gvec Q r M ⬝ᵥ ((K Q r M)⁻¹ *ᵥ gvec Q r M)

/-- The minimiser's mode part `w = (K_M⁻¹g)_modes`. -/
def wmin (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (M : ℕ) : Fin (M + 1) → ℝ :=
  solW (blk Q M) (rows r M)ᵀ (qcol Q M) (rcol r M)

/-- **The minimiser** `a* = (−w, 1)`. -/
def amin (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (M : ℕ) : Fin (M + 2) → ℝ :=
  Fin.snoc (-wmin Q r M) 1

theorem qf_succ (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (M : ℕ) (a : Fin (M + 1 + 1) → ℝ) :
    qf Q (M + 1) a = qf Q M (Fin.init a)
      + 2 * a (Fin.last _) * (qcol Q M ⬝ᵥ Fin.init a) + a (Fin.last _) ^ 2 * Q (M + 1) (M + 1) := by
  have e1 : ∑ i : Fin (M + 1), a i.castSucc * (Q i (M + 1) * a (Fin.last _))
      = a (Fin.last _) * ∑ i : Fin (M + 1), Q i (M + 1) * a i.castSucc := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j : Fin (M + 1), Q (M + 1) j * a j.castSucc = ∑ j : Fin (M + 1), Q j (M + 1) * a j.castSucc :=
    Finset.sum_congr rfl fun j _ => by rw [hQ]
  simp only [qf, dotProduct, mulVec, submatrix_apply]
  simp only [Fin.sum_univ_castSucc (n := M + 1), Fin.val_castSucc, Fin.val_last, qcol, Fin.init, mul_add,
    Finset.sum_add_distrib]
  rw [e1, e2]
  ring

omit [Fintype κ] [DecidableEq κ] in
theorem rows_succ (r : κ → ℕ → ℝ) (M : ℕ) (a : Fin (M + 1 + 1) → ℝ) :
    rows r (M + 1) *ᵥ a = rows r M *ᵥ Fin.init a + a (Fin.last _) • rcol r M := by
  funext k
  simp only [rows, mulVec, dotProduct, of_apply, Fin.sum_univ_castSucc (n := M + 1), Fin.val_castSucc,
    Fin.val_last, Fin.init, Pi.add_apply, Pi.smul_apply, smul_eq_mul, rcol]
  ring

theorem blk_transpose (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (M : ℕ) : (blk Q M)ᵀ = blk Q M := by
  ext i j; simp [hQ]

/-- The stationarity equations of the minimiser: `Q_M w + R_M λ = q`, `R_Mᵀ w = r`. -/
theorem wmin_solve (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) {M : ℕ} (hK : IsUnit (K Q r M).det) :
    blk Q M *ᵥ wmin Q r M + (rows r M)ᵀ *ᵥ solL (blk Q M) (rows r M)ᵀ (qcol Q M) (rcol r M) = qcol Q M ∧
      rows r M *ᵥ wmin Q r M = rcol r M := by
  have := bord_solve hK (qcol Q M) (rcol r M)
  rwa [transpose_transpose] at this

/-- **The pivot identity**: for `a ∈ V_{M+1}` with `a_{M+1} = 1`,
`Q_{M+1}(a) = κ'_{M+1} + uᵀQ_M u` with `u = a_{[0,M]} + w`. -/
theorem qf_eq_schur (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (r : κ → ℕ → ℝ) {M : ℕ}
    (hK : IsUnit (K Q r M).det) {a : Fin (M + 1 + 1) → ℝ} (ha : a ∈ V r (M + 1)) (h1 : a (Fin.last _) = 1) :
    qf Q (M + 1) a = schur Q r M
      + (Fin.init a + wmin Q r M) ⬝ᵥ (blk Q M *ᵥ (Fin.init a + wmin Q r M)) := by
  have hc := mem_V.mp ha
  rw [rows_succ, h1, one_smul] at hc
  have hv : ((rows r M)ᵀ)ᵀ *ᵥ (-Fin.init a) = rcol r M := by
    rw [transpose_transpose, mulVec_neg, eq_neg_of_add_eq_zero_left hc, neg_neg]
  have hl := lagrange (blk_transpose Q hQ M) hK (qcol Q M) (rcol r M) hv
  rw [show solW (blk Q M) (rows r M)ᵀ (qcol Q M) (rcol r M) = wmin Q r M from rfl,
    show -Fin.init a - wmin Q r M = -(Fin.init a + wmin Q r M) by abel] at hl
  simp only [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg] at hl
  have hs : schur Q r M = Q (M + 1) (M + 1)
      - Sum.elim (qcol Q M) (rcol r M) ⬝ᵥ ((bord (blk Q M) (rows r M)ᵀ)⁻¹ *ᵥ Sum.elim (qcol Q M) (rcol r M)) := rfl
  have hq0 : qf Q M (Fin.init a) = Fin.init a ⬝ᵥ (blk Q M *ᵥ Fin.init a) := rfl
  rw [qf_succ Q hQ, h1, hs, hq0]
  linarith

/-- The step reindexing `(Fin (M+1) ⊕ κ) ⊕ Unit ≃ Fin (M+2) ⊕ κ` that moves the new mode last. -/
def stepEquiv (M : ℕ) : (Fin (M + 1) ⊕ κ) ⊕ Unit ≃ Fin (M + 1 + 1) ⊕ κ where
  toFun
    | .inl (.inl i) => .inl i.castSucc
    | .inl (.inr k) => .inr k
    | .inr _ => .inl (Fin.last _)
  invFun
    | .inl i => Fin.lastCases (.inr ()) (fun j => .inl (.inl j)) i
    | .inr k => .inl (.inr k)
  left_inv := by rintro ((i | k) | u) <;> simp
  right_inv := by
    rintro (i | k)
    · refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    · rfl

/-- **The determinant form of the pivot**: `det K_{M+1} = det K_M · κ'_{M+1}`. -/
theorem det_K_succ (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (r : κ → ℕ → ℝ) {M : ℕ}
    (hK : IsUnit (K Q r M).det) : (K Q r (M + 1)).det = (K Q r M).det * schur Q r M := by
  have hsub : (K Q r (M + 1)).submatrix (stepEquiv M) (stepEquiv M)
      = fromBlocks (K Q r M) (replicateCol Unit (gvec Q r M)) (replicateRow Unit (gvec Q r M))
          (Matrix.of fun _ _ => Q (M + 1) (M + 1)) := by
    ext x y
    rcases x with ((i | k) | u) <;> rcases y with ((j | l) | w) <;>
      simp [stepEquiv, K, bord, blk, rows, gvec, qcol, rcol, hQ, Function.swap, Fin.coe_castSucc]
  have := (K Q r M).invertibleOfIsUnitDet hK
  rw [← det_submatrix_equiv_self (stepEquiv M), hsub, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  congr 1
  rw [det_unique]
  simp only [schur, Matrix.sub_apply, of_apply, Matrix.mul_apply, replicateRow_apply, replicateCol_apply,
    dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The pivot as a determinant ratio**: `κ'_{M+1} = det K_{M+1} / det K_M`. -/
theorem schur_eq_det_div (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (r : κ → ℕ → ℝ) {M : ℕ}
    (hK : IsUnit (K Q r M).det) : schur Q r M = (K Q r (M + 1)).det / (K Q r M).det := by
  rw [det_K_succ Q hQ r hK, mul_div_cancel_left₀ _ hK.ne_zero]

/-- The minimiser lies in `V_{M+1}` with top coordinate `1`. -/
theorem amin_mem (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) {M : ℕ} (hK : IsUnit (K Q r M).det) :
    amin Q r M ∈ V r (M + 1) ∧ amin Q r M (Fin.last _) = 1 := by
  refine ⟨mem_V.mpr ?_, by simp [amin]⟩
  rw [rows_succ]
  simp only [amin, Fin.init_snoc, Fin.snoc_last, one_smul, mulVec_neg, (wmin_solve Q r hK).2, neg_add_cancel]

/-- The minimiser attains the Schur pivot: `Q_{M+1}(a*) = κ'_{M+1}`. -/
theorem qf_amin (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (r : κ → ℕ → ℝ) {M : ℕ}
    (hK : IsUnit (K Q r M).det) : qf Q (M + 1) (amin Q r M) = schur Q r M := by
  obtain ⟨hmem, h1⟩ := amin_mem Q r hK
  rw [qf_eq_schur Q hQ r hK hmem h1, amin, Fin.init_snoc, neg_add_cancel, mulVec_zero, dotProduct_zero, add_zero]

/-- **The pivot value is the Schur pivot**: `κ_{M+1} = κ'_{M+1}` when `K_M` is invertible and `Q_M ≥ 0` on `V_M`. -/
theorem kappa_succ_eq (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (r : κ → ℕ → ℝ) {M : ℕ}
    (hK : IsUnit (K Q r M).det) (hpsd : ∀ u ∈ V r M, 0 ≤ qf Q M u) :
    kappa Q r (M + 1) = (schur Q r M : EReal) := by
  obtain ⟨hmem, h1⟩ := amin_mem Q r hK
  apply le_antisymm
  · have := kappa_le (Q := Q) hmem h1
    rwa [qf_amin Q hQ r hK] at this
  · refine le_kappa_iff.mpr fun a ha ha1 => ?_
    rw [qf_eq_schur Q hQ r hK ha ha1]
    have hc := mem_V.mp ha
    rw [rows_succ, ha1, one_smul] at hc
    have hu : Fin.init a + wmin Q r M ∈ V r M := by
      rw [mem_V, mulVec_add, (wmin_solve Q r hK).2, ← hc]
    have := hpsd _ hu
    simp only [qf] at this
    linarith

/-- **The minimiser is `Q`-orthogonal to `V_M`**: `(u, 0)ᵀ Q_{M+1} (−w, 1) = 0` for `u ∈ V_M`. -/
theorem amin_orth (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) {M : ℕ}
    (hK : IsUnit (K Q r M).det) {u : Fin (M + 1) → ℝ} (hu : u ∈ V r M) :
    (Fin.snoc u 0 : Fin (M + 1 + 1) → ℝ) ⬝ᵥ (blk Q (M + 1) *ᵥ amin Q r M) = 0 := by
  obtain ⟨h1, -⟩ := wmin_solve Q r hK
  have hR : u ⬝ᵥ ((rows r M)ᵀ *ᵥ solL (blk Q M) (rows r M)ᵀ (qcol Q M) (rcol r M)) = 0 := by
    rw [dot_mulVec_transpose, transpose_transpose, mem_V.mp hu, zero_dotProduct]
  have hq : u ⬝ᵥ qcol Q M = u ⬝ᵥ (blk Q M *ᵥ wmin Q r M) := by
    rw [← h1, dotProduct_add, hR, add_zero]
  have hexp : (Fin.snoc u 0 : Fin (M + 1 + 1) → ℝ) ⬝ᵥ (blk Q (M + 1) *ᵥ amin Q r M)
      = -(u ⬝ᵥ (blk Q M *ᵥ wmin Q r M)) + u ⬝ᵥ qcol Q M := by
    simp only [dotProduct, mulVec, submatrix_apply, Fin.sum_univ_castSucc (n := M + 1), Fin.snoc_castSucc,
      Fin.snoc_last, Fin.val_castSucc, Fin.val_last, amin, zero_mul, add_zero, Pi.neg_apply, qcol, mul_add, mul_one,
      Finset.sum_add_distrib, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_const_zero]
    ring
  rw [hexp, hq]; ring

/-- A concave quadratic in `t` is unbounded below. -/
theorem exists_quad_lt {α β γ : ℝ} (hγ : γ < 0) (y : ℝ) : ∃ t : ℝ, α + β * t + γ * t ^ 2 < y := by
  refine ⟨max 1 ((|α| + |β| + |y| + 1) / -γ), ?_⟩
  set t := max 1 ((|α| + |β| + |y| + 1) / -γ)
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht2 : (|α| + |β| + |y| + 1) / -γ ≤ t := le_max_right _ _
  have h3 : |α| + |β| + |y| + 1 ≤ t * -γ := by rwa [div_le_iff₀ (by linarith)] at ht2
  have h4 : t * (|α| + |β| + |y| + 1) ≤ t * (t * -γ) := mul_le_mul_of_nonneg_left h3 (by linarith)
  have hα : α ≤ |α| * t := by nlinarith [le_abs_self α, abs_nonneg α]
  have hβ : β * t ≤ |β| * t := by nlinarith [le_abs_self β]
  have hy : -|y| ≤ y := neg_abs_le y
  have hy0 : 0 ≤ |y| := abs_nonneg y
  nlinarith

/-- The block form along a line: `Q(a + t e) = Q(a) + t (aᵀQe + eᵀQa) + t² Q(e)`. -/
theorem qf_add_smul (Q : Matrix ℕ ℕ ℝ) (M : ℕ) (a e : Fin (M + 1) → ℝ) (t : ℝ) :
    qf Q M (a + t • e) = qf Q M a + (a ⬝ᵥ (blk Q M *ᵥ e) + e ⬝ᵥ (blk Q M *ᵥ a)) * t + qf Q M e * t ^ 2 := by
  simp only [qf, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

omit [Fintype κ] [DecidableEq κ] in
/-- **Past a negative direction the pivot value is `⊥`**: if `M < M'`, some `a ∈ V_{M'}` has `a_{M'} = 1` and some
`u ∈ V_M` has `Q_M(u) < 0`, then `κ_{M'} = ⊥`. -/
theorem kappa_eq_bot_of_neg (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) {M M' : ℕ} (hMM : M < M')
    {a : Fin (M' + 1) → ℝ} (ha : a ∈ V r M') (ha1 : a (Fin.last M') = 1)
    {u : Fin (M + 1) → ℝ} (hu : u ∈ V r M) (hneg : qf Q M u < 0) : kappa Q r M' = ⊥ := by
  have hle : M + 1 ≤ M' + 1 := by omega
  set e : Fin (M' + 1) → ℝ := zext u
  have htop : ∀ i : Fin (M' + 1), M < (i : ℕ) → e i = 0 := zext_top u
  have he : e ∈ V r M' := by rw [mem_V, ← rows_mulVec_restr r hle htop, restr_zext]; exact mem_V.mp hu
  have he1 : e (Fin.last M') = 0 := htop _ (by simp [hMM])
  have hqe : qf Q M' e = qf Q M u := by rw [← qf_restr Q hle htop, restr_zext]
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  obtain ⟨t, ht⟩ := exists_quad_lt (α := qf Q M' a)
    (β := a ⬝ᵥ (blk Q M' *ᵥ e) + e ⬝ᵥ (blk Q M' *ᵥ a)) hneg y
  have hmem : a + t • e ∈ V r M' := (V r M').add_mem ha ((V r M').smul_mem t he)
  have h1 : (a + t • e) (Fin.last M') = 1 := by simp [ha1, he1]
  refine lt_of_le_of_lt (kappa_le hmem h1) ?_
  rw [EReal.coe_lt_coe_iff, qf_add_smul, hqe]
  exact ht

open Classical in
/-- **The pivot value in both regimes**: with `K_M` invertible, `κ_{M+1}` is the Schur pivot `κ'_{M+1}` if
`Q_M ≥ 0` on `V_M` and `⊥` otherwise. -/
theorem kappa_succ_eq_ite (Q : Matrix ℕ ℕ ℝ) (hQ : ∀ i j, Q j i = Q i j) (r : κ → ℕ → ℝ) {M : ℕ}
    (hK : IsUnit (K Q r M).det) :
    kappa Q r (M + 1) = if ∀ u ∈ V r M, 0 ≤ qf Q M u then (schur Q r M : EReal) else ⊥ := by
  split_ifs with h
  · exact kappa_succ_eq Q hQ r hK h
  · push Not at h
    obtain ⟨u, hu, hneg⟩ := h
    obtain ⟨hmem, h1⟩ := amin_mem Q r hK
    exact kappa_eq_bot_of_neg Q r (Nat.lt_succ_self M) hmem h1 hu hneg

/-- **The bordered matrix is invertible (KKT)** when `Q_M` is positive definite on `V_M` and the truncated
constraint rows are linearly independent. -/
theorem isUnit_det_K_of_posDef (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) {M : ℕ}
    (hpd : ∀ u ∈ V r M, u ≠ 0 → 0 < qf Q M u) (hli : LinearIndependent ℝ (rows r M)) :
    IsUnit (K Q r M).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨z, hz0, hz⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  set v : Fin (M + 1) → ℝ := fun i => z (Sum.inl i)
  set l : κ → ℝ := fun k => z (Sum.inr k)
  have hzs : z = Sum.elim v l := by funext x; cases x <;> rfl
  rw [hzs, K, bord, fromBlocks_mulVec, zero_mulVec, add_zero, transpose_transpose] at hz
  have h1 : blk Q M *ᵥ v + (rows r M)ᵀ *ᵥ l = 0 := funext fun i => congrFun hz (Sum.inl i)
  have h2 : rows r M *ᵥ v = 0 := funext fun k => congrFun hz (Sum.inr k)
  have hv : v = 0 := by
    by_contra hv0
    have hp := hpd v (mem_V.mpr h2) hv0
    have hq : qf Q M v = 0 := by
      have e1 : v ⬝ᵥ (blk Q M *ᵥ v) = -(v ⬝ᵥ ((rows r M)ᵀ *ᵥ l)) := by
        rw [eq_neg_of_add_eq_zero_left h1, dotProduct_neg]
      rw [dot_mulVec_transpose (rows r M)ᵀ v l, transpose_transpose, h2, zero_dotProduct, neg_zero] at e1
      exact e1
    linarith
  have hl : l = 0 := by
    rw [hv, mulVec_zero, zero_add, mulVec_transpose, vecMul_eq_sum] at h1
    funext k
    exact Fintype.linearIndependent_iff.mp hli l h1 k
  apply hz0
  rw [hzs, hv, hl]
  funext x; cases x <;> rfl

/-- **An invertible bordered matrix has independent constraint rows**: `IsUnit (det K_M)` forces the truncated
rows `r_k|_{[0,M]}` to be linearly independent. -/
theorem linearIndependent_rows_of_isUnit (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) {M : ℕ}
    (hK : IsUnit (K Q r M).det) : LinearIndependent ℝ (rows r M) := by
  refine Fintype.linearIndependent_iff.mpr fun l hl => ?_
  have hinj : Function.Injective (K Q r M).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hK)
  have hRl : (rows r M)ᵀ *ᵥ l = 0 := by rw [mulVec_transpose, vecMul_eq_sum, hl]
  have hz : K Q r M *ᵥ Sum.elim 0 l = K Q r M *ᵥ 0 := by
    rw [mulVec_zero]
    funext x
    cases x with
    | inl i => simp [K, bord, fromBlocks_mulVec, hRl]
    | inr k => simp [K, bord, fromBlocks_mulVec]
  intro k
  exact congrFun (hinj hz) (Sum.inr k)

/-- **At most `M + 1` constraint rows** can sit in front of an invertible bordered matrix `K_M`. -/
theorem card_le_of_isUnit (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) {M : ℕ} (hK : IsUnit (K Q r M).det) :
    Fintype.card κ ≤ M + 1 := by
  have := (linearIndependent_rows_of_isUnit Q r hK).fintype_card_le_finrank
  simpa using this

open Cvs.Upstream.ConstrainedFormPivotChain (cosQ cosR cosQ_symm) in
/-- **The pivots of the even bulk form**: at `1 < x`, if `K_M` of `cosQ x` against the `R₁` rows `cosR x` is
invertible and the form is `≥ 0` on `V_M`, then `κ_{M+1} = det K_{M+1} / det K_M`. -/
theorem kappa_cosQ_succ {x : ℕ} (hx1 : (1 : ℝ) < x) {M : ℕ} (hK : IsUnit (K (cosQ x) (cosR x) M).det)
    (hpsd : ∀ u ∈ V (cosR x) M, 0 ≤ qf (cosQ x) M u) :
    kappa (cosQ x) (cosR x) (M + 1)
      = (((K (cosQ x) (cosR x) (M + 1)).det / (K (cosQ x) (cosR x) M).det : ℝ) : EReal) := by
  rw [kappa_succ_eq _ (fun i j => cosQ_symm hx1 i j) _ hK hpsd,
    schur_eq_det_div _ (fun i j => cosQ_symm hx1 i j) _ hK]

open Cvs.Upstream.ConstrainedFormPivotChain (cosQ cosR cosW evenBulkFloor_iff_kappa nonneg_iff_kappa qf_sub_smul qf_cosW dot_ofCos) in
/-- **At a strict floor the bordered matrices of the even bulk form are invertible exactly where the rows are
independent**: if `1 < x`, `0 < b` and `EvenBulkFloor x b`, then `K_M(cosQ x, cosR x)` is invertible iff the
truncated rung-cosine rows `cosR x|_{[0,M]}` are linearly independent. -/
theorem isUnit_det_K_cosQ_iff_of_floor {x : ℕ} (hx1 : (1 : ℝ) < x) {b : ℝ} (hb : 0 < b)
    (hF : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b) (M : ℕ) :
    IsUnit (K (cosQ x) (cosR x) M).det ↔ LinearIndependent ℝ (rows (cosR x) M) := by
  refine ⟨linearIndependent_rows_of_isUnit _ _, fun hli => ?_⟩
  have hnn := (nonneg_iff_kappa _ _).mpr ((evenBulkFloor_iff_kappa hx1 b).mp hF) M
  refine isUnit_det_K_of_posDef _ _ (fun u hu hu0 => ?_) hli
  have h1 := hnn u hu
  rw [qf_sub_smul] at h1
  have h2 : 0 < qf cosW M u := by
    rw [qf_cosW, dot_ofCos]
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact hu0 (funext h)
    refine Finset.sum_pos' (fun m _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · split_ifs <;> nlinarith [sq_nonneg (u m)]
    · split_ifs <;> nlinarith [mul_self_pos.mpr hi]
  nlinarith

end Chain

end Cvs.Upstream.BorderedDeterminantPivot
