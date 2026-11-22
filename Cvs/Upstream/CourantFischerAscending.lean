import Mathlib
import Cvs.L2a.LowEigenCountPointVanishing
import Cvs.Upstream.NegativeIndexEigenCount
import Cvs.Upstream.OnsetSchurCriterion

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Courant–Fischer for a real symmetric matrix, ascending eigenvalues

`eigAsc hA k = λ_k` lists the eigenvalues in ascending order. `n₋(A − d·1) = #{i | λᵢ < d}`, so a floor
`d|v|² ≤ vᵀAv` on codimension `r` gives `d ≤ λ_r`. Max-min: `λ_k` is the greatest `d` with such a floor on
codimension `≤ k`; min-max: the least `d` with `vᵀAv ≤ d|v|²` on dimension `≥ k + 1`. Pencil: a floor
`d·vᵀGv ≤ vᵀAv` on codimension `r` gives `n₋(A − dG) ≤ r`, and `d ≤ λ_r(PᵀAP)` when `PᵀGP = 1`.
-/

noncomputable section

open Matrix Module

namespace Cvs.Upstream.CourantFischerAscending

open Cvs.Upstream.OnsetSchurCriterion (NegDefOn negIndex)
open Cvs.Upstream.NegativeIndexEigenCount (U)

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-! ### Ascending eigenvalues -/

/-- The eigenvalues of `A` in ascending order, `λ_0 ≤ λ_1 ≤ ⋯ ≤ λ_{N−1}`. -/
def eigAsc (hA : A.IsHermitian) (k : Fin (Fintype.card n)) : ℝ := hA.eigenvalues₀ k.rev

theorem eigAsc_monotone (hA : A.IsHermitian) : Monotone (eigAsc hA) :=
  fun _ _ h => hA.eigenvalues₀_antitone (Fin.rev_le_rev.2 h)

/-- The eigenvalue list `hA.eigenvalues` is a relabelling of `eigAsc hA`. -/
def ascEquiv : n ≃ Fin (Fintype.card n) :=
  (Fintype.equivOfCardEq (Fintype.card_fin _)).symm.trans Fin.revPerm

theorem eigAsc_ascEquiv (hA : A.IsHermitian) (i : n) : eigAsc hA (ascEquiv i) = hA.eigenvalues i := by
  simp [eigAsc, ascEquiv, Matrix.IsHermitian.eigenvalues]

/-- Counting eigenvalues with a property is counting ascending eigenvalues with it. -/
theorem card_eigenvalues (hA : A.IsHermitian) (p : ℝ → Prop) [DecidablePred p] :
    Fintype.card {i // p (hA.eigenvalues i)} = Fintype.card {k // p (eigAsc hA k)} :=
  Fintype.card_congr (Equiv.subtypeEquiv ascEquiv fun i => by rw [eigAsc_ascEquiv])

/-! ### Counting a monotone list -/

section Monotone

variable {N : ℕ} {f : Fin N → ℝ}

/-- **At most `r` values of a monotone list lie below `d` iff `d ≤ f_r`.** -/
theorem card_lt_le_iff (hf : Monotone f) (d : ℝ) {r : ℕ} (hr : r < N) :
    Fintype.card {k // f k < d} ≤ r ↔ d ≤ f ⟨r, hr⟩ := by
  rw [Fintype.card_subtype]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hsub : Finset.Iic (⟨r, hr⟩ : Fin N) ⊆ Finset.univ.filter fun k => f k < d := fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hf (Finset.mem_Iic.1 hk)).trans_lt hlt
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    simp at this
    omega
  · intro h
    have hsub : (Finset.univ.filter fun k => f k < d) ⊆ Finset.Iio (⟨r, hr⟩ : Fin N) := fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [Finset.mem_Iio]
      by_contra hle
      push Not at hle
      exact absurd (h.trans (hf hle)) (not_le.2 hk)
    have := Finset.card_le_card hsub
    rwa [Fin.card_Iio] at this

/-- `f_k ≤ f_j` for at least `N − k` indices `j`. -/
theorem sub_le_card_le (hf : Monotone f) (k : Fin N) :
    N - k ≤ Fintype.card {j // f k ≤ f j} := by
  rw [Fintype.card_subtype, ← Fin.card_Ici]
  exact Finset.card_le_card fun j hj => by simpa using hf (Finset.mem_Ici.1 hj)

/-- `f_j ≤ f_k` for at least `k + 1` indices `j`. -/
theorem succ_le_card_le (hf : Monotone f) (k : Fin N) :
    (k : ℕ) + 1 ≤ Fintype.card {j // f j ≤ f k} := by
  rw [Fintype.card_subtype, ← Fin.card_Iic]
  exact Finset.card_le_card fun j hj => by simpa using hf (Finset.mem_Iic.1 hj)

/-- `d < f_j` for at least `N − k` indices `j` when `d < f_k`. -/
theorem sub_le_card_lt (hf : Monotone f) {d : ℝ} {k : Fin N} (hd : d < f k) :
    N - k ≤ Fintype.card {j // d < f j} := by
  rw [Fintype.card_subtype, ← Fin.card_Ici]
  exact Finset.card_le_card fun j hj => by simpa using hd.trans_le (hf (Finset.mem_Ici.1 hj))

end Monotone

/-! ### Spectral subspaces -/

/-- Extension by zero from the coordinates satisfying `p`. -/
def extP (p : n → Prop) [DecidablePred p] (a : {i // p i} → ℝ) : n → ℝ :=
  fun j => if h : p j then a ⟨j, h⟩ else 0

/-- The span of the eigenvectors with index in `p`, as the image of `a ↦ U (extP a)`. -/
def upP (hA : A.IsHermitian) (p : n → Prop) [DecidablePred p] : ({i // p i} → ℝ) →ₗ[ℝ] (n → ℝ) where
  toFun a := U hA *ᵥ extP p a
  map_add' a b := by
    rw [← mulVec_add]; congr 1; ext j; simp only [extP, Pi.add_apply]; split_ifs <;> simp
  map_smul' r a := by
    rw [RingHom.id_apply, ← mulVec_smul]; congr 1; ext j
    simp only [extP, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem coord_upP (hA : A.IsHermitian) (p : n → Prop) [DecidablePred p] (a : {i // p i} → ℝ) :
    (U hA)ᵀ *ᵥ upP hA p a = extP p a := by
  show (U hA)ᵀ *ᵥ (U hA *ᵥ extP p a) = _
  rw [mulVec_mulVec, Cvs.Upstream.NegativeIndexEigenCount.transpose_mul_U, one_mulVec]

theorem upP_injective (hA : A.IsHermitian) (p : n → Prop) [DecidablePred p] :
    Function.Injective (upP hA p) := by
  intro a b h
  have := congrArg ((U hA)ᵀ *ᵥ ·) h
  simp only [coord_upP] at this
  funext i
  simpa [extP, i.2] using congrFun this i

theorem finrank_range_upP (hA : A.IsHermitian) (p : n → Prop) [DecidablePred p] :
    finrank ℝ (LinearMap.range (upP hA p)) = Fintype.card {i // p i} := by
  rw [LinearMap.finrank_range_of_inj (upP_injective hA p), Module.finrank_fintype_fun_eq_card]

/-- `yᵀ(A − d·1)y = ∑ᵢ (λᵢ − d) zᵢ²`, `z = Uᵀy`. -/
theorem quad_sub_smul (hA : A.IsHermitian) (d : ℝ) (y : n → ℝ) :
    y ⬝ᵥ ((A - d • 1) *ᵥ y) = ∑ i, (hA.eigenvalues i - d) * ((U hA)ᵀ *ᵥ y) i ^ 2 := by
  have h := Cvs.Upstream.NegativeIndexEigenCount.quad_shift hA d y
  have e : A - d • 1 = -(d • 1 - A) := by abel
  rw [e, neg_mulVec, dotProduct_neg, h, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- On the span of the eigenvectors with `q λᵢ`, `yᵀ(A − d·1)y = ∑_{q λᵢ} (λᵢ − d) aᵢ²`. -/
theorem quad_upP (hA : A.IsHermitian) (q : ℝ → Prop) [DecidablePred q] (d : ℝ)
    (a : {i // q (hA.eigenvalues i)} → ℝ) :
    upP hA _ a ⬝ᵥ ((A - d • 1) *ᵥ upP hA _ a)
      = ∑ i, (hA.eigenvalues i - d) * extP (fun i => q (hA.eigenvalues i)) a i ^ 2 := by
  rw [quad_sub_smul hA, coord_upP]

/-- The eigenvectors below `d` span a negative definite subspace of `A − d·1`. -/
theorem negDefOn_lt (hA : A.IsHermitian) (d : ℝ) :
    NegDefOn (A - d • 1) (LinearMap.range (upP hA fun i => hA.eigenvalues i < d)) := by
  rintro y ⟨a, rfl⟩ hy
  rw [quad_upP hA (· < d)]
  have ha : a ≠ 0 := fun h => hy (by rw [h, map_zero])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hterm : ∀ j, (hA.eigenvalues j - d) * extP (fun i => hA.eigenvalues i < d) a j ^ 2 ≤ 0 :=
    fun j => by
      unfold extP
      split_ifs with h
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
      · simp
  have hlt : (hA.eigenvalues i - d) * extP (fun i => hA.eigenvalues i < d) a i ^ 2 < 0 := by
    simp only [extP, i.2, dite_true]
    exact mul_neg_of_neg_of_pos (by linarith [i.2]) (sq_pos_of_ne_zero hi)
  calc _ < ∑ j : n, (0 : ℝ) := Finset.sum_lt_sum (fun j _ => hterm j) ⟨i, Finset.mem_univ _, hlt⟩
    _ = 0 := by simp

/-- On the eigenvectors at or above `d`, `yᵀ(A − d·1)y ≥ 0`. -/
theorem quad_nonneg_ge (hA : A.IsHermitian) (d : ℝ) :
    ∀ y ∈ LinearMap.range (upP hA fun i => d ≤ hA.eigenvalues i), 0 ≤ y ⬝ᵥ ((A - d • 1) *ᵥ y) := by
  rintro y ⟨a, rfl⟩
  rw [quad_upP hA (d ≤ ·)]
  refine Finset.sum_nonneg fun j _ => ?_
  unfold extP
  split_ifs with h
  · exact mul_nonneg (by linarith) (sq_nonneg _)
  · simp

/-- On the eigenvectors at or below `d`, `yᵀ(A − d·1)y ≤ 0`. -/
theorem quad_nonpos_le (hA : A.IsHermitian) (d : ℝ) :
    ∀ y ∈ LinearMap.range (upP hA fun i => hA.eigenvalues i ≤ d), y ⬝ᵥ ((A - d • 1) *ᵥ y) ≤ 0 := by
  rintro y ⟨a, rfl⟩
  rw [quad_upP hA (· ≤ d)]
  refine Finset.sum_nonpos fun j _ => ?_
  unfold extP
  split_ifs with h
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  · simp

theorem quad_sub_smul_one (A : Matrix n n ℝ) (d : ℝ) (y : n → ℝ) :
    y ⬝ᵥ ((A - d • 1) *ᵥ y) = y ⬝ᵥ (A *ᵥ y) - d * (y ⬝ᵥ y) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

/-! ### The counting form -/

/-- **The negative index counts eigenvalues below `d`**: `n₋(A − d·1) = #{i | λᵢ < d}`. -/
theorem negIndex_sub_smul_one (hA : A.IsHermitian) (d : ℝ) :
    negIndex (A - d • 1) = Fintype.card {i // hA.eigenvalues i < d} := by
  apply le_antisymm
  · have h := Cvs.L2a.LowEigenCountPointVanishing.finrank_add_negIndex_le _ (quad_nonneg_ge hA d)
    rw [finrank_range_upP] at h
    have hc := Fintype.card_subtype_compl (fun i => hA.eigenvalues i < d)
    have e : Fintype.card {i // ¬ hA.eigenvalues i < d} = Fintype.card {i // d ≤ hA.eigenvalues i} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun i => not_lt)
    have hle : Fintype.card {i // hA.eigenvalues i < d} ≤ Fintype.card n := Fintype.card_subtype_le _
    omega
  · refine le_csSup ⟨Fintype.card n, ?_⟩ ⟨_, negDefOn_lt hA d, finrank_range_upP hA _⟩
    rintro m ⟨V, -, rfl⟩
    simpa using Submodule.finrank_le V

/-- **Floor ⇒ count.** A floor `d|v|² ≤ vᵀAv` on a subspace of codimension `≤ r` leaves at most `r`
eigenvalues below `d`. -/
theorem card_lt_le_of_floor (hA : A.IsHermitian) {V : Submodule ℝ (n → ℝ)} {d : ℝ} {r : ℕ}
    (hcodim : Fintype.card n ≤ finrank ℝ V + r) (hV : ∀ v ∈ V, d * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) :
    Fintype.card {i // hA.eigenvalues i < d} ≤ r := by
  have h := Cvs.L2a.LowEigenCountPointVanishing.finrank_add_negIndex_le (A - d • 1) (U := V) fun v hv => by
    rw [quad_sub_smul_one]; linarith [hV v hv]
  rw [negIndex_sub_smul_one hA] at h
  omega

/-- **Floor ⇒ `d ≤ λ_r`.** -/
theorem le_eigAsc_of_floor (hA : A.IsHermitian) {V : Submodule ℝ (n → ℝ)} {d : ℝ} {r : ℕ}
    (hcodim : Fintype.card n ≤ finrank ℝ V + r) (hV : ∀ v ∈ V, d * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hr : r < Fintype.card n) : d ≤ eigAsc hA ⟨r, hr⟩ := by
  have h := card_lt_le_of_floor hA hcodim hV
  rw [card_eigenvalues hA (· < d)] at h
  exact (card_lt_le_iff (eigAsc_monotone hA) d hr).1 h

/-! ### Courant–Fischer -/

/-- **Courant–Fischer, max-min.** `λ_k` is the greatest `d` admitting a subspace `V` of codimension `≤ k`
with `d|v|² ≤ vᵀAv` on `V`. -/
theorem isGreatest_eigAsc (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    IsGreatest {d | ∃ V : Submodule ℝ (n → ℝ), Fintype.card n ≤ finrank ℝ V + k ∧
      ∀ v ∈ V, d * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)} (eigAsc hA k) := by
  refine ⟨⟨LinearMap.range (upP hA fun i => eigAsc hA k ≤ hA.eigenvalues i), ?_, fun v hv => ?_⟩, ?_⟩
  · rw [finrank_range_upP, card_eigenvalues hA (eigAsc hA k ≤ ·)]
    have := sub_le_card_le (eigAsc_monotone hA) k
    omega
  · have := quad_nonneg_ge hA (eigAsc hA k) v hv
    rw [quad_sub_smul_one] at this
    linarith
  · rintro d ⟨V, hcodim, hV⟩
    exact le_eigAsc_of_floor hA hcodim hV k.2

/-- **Courant–Fischer, min-max.** `λ_k` is the least `d` admitting a subspace `V` of dimension `≥ k + 1`
with `vᵀAv ≤ d|v|²` on `V`. -/
theorem isLeast_eigAsc (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    IsLeast {d | ∃ V : Submodule ℝ (n → ℝ), (k : ℕ) + 1 ≤ finrank ℝ V ∧
      ∀ v ∈ V, v ⬝ᵥ (A *ᵥ v) ≤ d * (v ⬝ᵥ v)} (eigAsc hA k) := by
  refine ⟨⟨LinearMap.range (upP hA fun i => hA.eigenvalues i ≤ eigAsc hA k), ?_, fun v hv => ?_⟩, ?_⟩
  · rw [finrank_range_upP, card_eigenvalues hA (· ≤ eigAsc hA k)]
    exact succ_le_card_le (eigAsc_monotone hA) k
  · have := quad_nonpos_le hA (eigAsc hA k) v hv
    rw [quad_sub_smul_one] at this
    linarith
  · rintro d ⟨V, hdim, hV⟩
    by_contra hlt
    push Not at hlt
    have h := Cvs.L2a.LowEigenCountPointVanishing.finrank_add_negIndex_le (d • 1 - A) (U := V) fun v hv => by
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      linarith [hV v hv]
    rw [Cvs.Upstream.NegativeIndexEigenCount.negIndex_smul_one_sub hA, card_eigenvalues hA (d < ·)] at h
    have := sub_le_card_lt (eigAsc_monotone hA) hlt
    have := k.2
    omega

/-! ### Pencils `(A, G)` -/

omit [DecidableEq n] in
theorem quad_congr (P S : Matrix n n ℝ) (y : n → ℝ) :
    y ⬝ᵥ ((Pᵀ * S * P) *ᵥ y) = (P *ᵥ y) ⬝ᵥ (S *ᵥ (P *ᵥ y)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, Cvs.Upstream.OnsetSchurCriterion.dot_mulVec_left, transpose_transpose]

/-- **Floor ⇒ `d ≤ λ_r(PᵀAP)`**, for `P` with `PᵀGP = 1`: the generalised eigenvalues of `(A, G)` in
ascending order are those of `PᵀAP`. -/
theorem le_eigAsc_of_floor_gram {A G P : Matrix n n ℝ} (hGP : Pᵀ * G * P = 1)
    (hAP : (Pᵀ * A * P).IsHermitian) {V : Submodule ℝ (n → ℝ)} {d : ℝ} {r : ℕ}
    (hcodim : Fintype.card n ≤ finrank ℝ V + r) (hV : ∀ v ∈ V, d * (v ⬝ᵥ (G *ᵥ v)) ≤ v ⬝ᵥ (A *ᵥ v))
    (hr : r < Fintype.card n) : d ≤ eigAsc hAP ⟨r, hr⟩ := by
  have hright : P * (Pᵀ * G) = 1 := mul_eq_one_comm.1 hGP
  have hsurj : Function.Surjective (toLin' P) := fun v =>
    ⟨(Pᵀ * G) *ᵥ v, by rw [toLin'_apply, mulVec_mulVec, hright, one_mulVec]⟩
  set V' := V.comap (toLin' P)
  have hmap : V'.map (toLin' P) = V := Submodule.map_comap_eq_of_surjective hsurj V
  have hdim : finrank ℝ V ≤ finrank ℝ V' := by
    rw [← hmap]; exact Submodule.finrank_map_le _ _
  refine le_eigAsc_of_floor hAP (V := V') (by omega) (fun y hy => ?_) hr
  have h := hV (P *ᵥ y) hy
  rw [quad_congr]
  have e : y ⬝ᵥ y = (P *ᵥ y) ⬝ᵥ (G *ᵥ (P *ᵥ y)) := by
    rw [← quad_congr, hGP, one_mulVec]
  rw [e]; exact h

end Cvs.Upstream.CourantFischerAscending
