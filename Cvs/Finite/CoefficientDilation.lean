import Mathlib

/-!
# The dilation map on coefficient vectors: roots scale, exactly
Over any field, on distinct nodes `q_k` the secular polynomial `P_y(w) = ∑_k y_k ∏_{l≠k}(q_l − w)` has degree
`< K`, evaluates at a node to `y_m ∏_{l≠m}(q_l − q_m)`, and is determined by its node values.
The dilated vector `dil t y := (P_y(q_k/t)/∏_{l≠k}(q_l − q_k))_k` therefore has secular polynomial
`P_y(w/t)`: its roots are the roots of `P_y` scaled by `t`, and its rational factor is
`P_y(u²/t)/∏(q_l − u²)`. This is the exact form of "dilate the resolved zeros to the next scale".
-/

noncomputable section

open Polynomial

namespace Cvs.Finite.CoefficientDilation

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {F : Type*} [Field F]

/-- The secular polynomial on distinct nodes. -/
def Psec (q : κ → F) (y : κ → F) : F[X] :=
  ∑ k, C (y k) * ∏ l ∈ Finset.univ.erase k, (C (q l) - X)

theorem eval_Psec (q : κ → F) (y : κ → F) (w : F) :
    (Psec q y).eval w = ∑ k, y k * ∏ l ∈ Finset.univ.erase k, (q l - w) := by
  simp [Psec, eval_finsetSum, eval_prod]

/-- At a node only one term survives. -/
theorem eval_Psec_node (q : κ → F) (y : κ → F) (m : κ) :
    (Psec q y).eval (q m) = y m * ∏ l ∈ Finset.univ.erase m, (q l - q m) := by
  rw [eval_Psec, Finset.sum_eq_single m]
  · intro k _ hk
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hk, Finset.mem_univ m⟩) (sub_self _),
      mul_zero]
  · intro h; exact absurd (Finset.mem_univ m) h

theorem natDegree_Psec_le (q : κ → F) (y : κ → F) :
    (Psec q y).natDegree ≤ Fintype.card κ - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  refine le_trans (natDegree_prod_le _ _) ?_
  refine (Finset.sum_le_sum fun l _ => (show (C (q l) - X : F[X]).natDegree ≤ 1 from
    (natDegree_sub_le _ _).trans (by simp))).trans ?_
  simp [Finset.card_erase_of_mem, Finset.card_univ]

theorem degree_Psec_lt (q : κ → F) (y : κ → F) :
    (Psec q y).degree < (Fintype.card κ : WithBot ℕ) := by
  rcases isEmpty_or_nonempty κ with h | h
  · have : Psec q y = 0 := by simp [Psec]
    rw [this, degree_zero]; exact WithBot.bot_lt_coe _
  · have hcard : 1 ≤ Fintype.card κ := Fintype.card_pos
    rcases eq_or_ne (Psec q y) 0 with h0 | h0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · exact (natDegree_lt_iff_degree_lt h0).mp (by have := natDegree_Psec_le q y; omega)

/-- **The dilated coefficient vector.** -/
def dil (q : κ → F) (t : F) (y : κ → F) : κ → F :=
  fun k => (Psec q y).eval (q k / t) / ∏ l ∈ Finset.univ.erase k, (q l - q k)

/-- **The dilated vector's secular polynomial is `P_y(w/t)`.** -/
theorem Psec_dil {q : κ → F} (hq : Function.Injective q) (t : F) (y : κ → F) :
    Psec q (dil q t y) = (Psec q y).comp (C t⁻¹ * X) := by
  refine eq_of_degrees_lt_of_eval_index_eq Finset.univ hq.injOn ?_ ?_ ?_
  · rw [Finset.card_univ]; exact degree_Psec_lt _ _
  · rw [Finset.card_univ]
    rcases isEmpty_or_nonempty κ with h | h
    · have : Psec q y = 0 := by simp [Psec]
      rw [this, zero_comp, degree_zero]; exact WithBot.bot_lt_coe _
    · have hcard : 1 ≤ Fintype.card κ := Fintype.card_pos
      rcases eq_or_ne ((Psec q y).comp (C t⁻¹ * X)) 0 with h0 | h0
      · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
      refine (natDegree_lt_iff_degree_lt h0).mp ?_
      have h1 := natDegree_comp_le (p := Psec q y) (q := C t⁻¹ * X)
      have h2 : (C t⁻¹ * X : F[X]).natDegree ≤ 1 :=
        (natDegree_C_mul_le _ _).trans (by simp)
      have h3 := natDegree_Psec_le q y
      have h4 : (Psec q y).natDegree * (C t⁻¹ * X : F[X]).natDegree ≤ (Psec q y).natDegree :=
        (Nat.mul_le_mul_left _ h2).trans (by simp)
      omega
  · intro m _
    rw [eval_Psec_node, eval_comp, eval_mul, eval_C, eval_X]
    unfold dil
    have hne : ∏ l ∈ Finset.univ.erase m, (q l - q m) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun l hl => sub_ne_zero.mpr (hq.ne (Finset.ne_of_mem_erase hl))
    rw [div_mul_cancel₀ _ hne, div_eq_inv_mul]

/-- The rational factor on the nodes. -/
def Rq (q : κ → F) (y : κ → F) (u : F) : F := ∑ k, y k / (q k - u ^ 2)

/-- Partial fractions: `Rq y u = P_y(u²)/∏_l(q_l − u²)`. -/
theorem Rq_eq_Psec (q : κ → F) (y : κ → F) {u : F} (hu : ∀ k, q k - u ^ 2 ≠ 0) :
    Rq q y u = (Psec q y).eval (u ^ 2) / ∏ l, (q l - u ^ 2) := by
  unfold Rq
  rw [eval_Psec, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hprod : ∏ l, (q l - u ^ 2) = (q k - u ^ 2) * ∏ l ∈ Finset.univ.erase k, (q l - u ^ 2) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)).symm
  have hne : ∏ l ∈ Finset.univ.erase k, (q l - u ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun l _ => hu l
  rw [hprod]
  field_simp

/-- **The dilated vector's rational factor is `P_y(u²/t)/∏_l(q_l − u²)`.** -/
theorem Rq_dil {q : κ → F} (hq : Function.Injective q) (t : F) (y : κ → F) {u : F}
    (hu : ∀ k, q k - u ^ 2 ≠ 0) :
    Rq q (dil q t y) u = (Psec q y).eval (u ^ 2 / t) / ∏ l, (q l - u ^ 2) := by
  rw [Rq_eq_Psec q _ hu, Psec_dil hq, eval_comp, eval_mul, eval_C, eval_X, div_eq_inv_mul (u ^ 2) t]

/-- **Transfer between scales**: with `t = (L'/L)²` and `u' = (L'/L)·u`, the dilated vector's
rational factor at `u'` is the original's at `u`, times the explicit node factor. -/
theorem Rq_dil_transfer {q : κ → F} (hq : Function.Injective q) {s : F} (hs : s ≠ 0) (y : κ → F)
    {u : F} (hu : ∀ k, q k - u ^ 2 ≠ 0) (hu' : ∀ k, q k - (s * u) ^ 2 ≠ 0) :
    Rq q (dil q (s ^ 2) y) (s * u)
      = Rq q y u * (∏ l, (q l - u ^ 2)) / ∏ l, (q l - (s * u) ^ 2) := by
  rw [Rq_dil hq _ _ hu', Rq_eq_Psec q y hu]
  have hne : ∏ l, (q l - u ^ 2) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun l _ => hu l
  rw [show (s * u) ^ 2 / s ^ 2 = u ^ 2 by field_simp]
  field_simp

end Cvs.Finite.CoefficientDilation
