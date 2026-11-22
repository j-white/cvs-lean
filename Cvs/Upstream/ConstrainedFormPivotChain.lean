import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.EvenBulkModeMatrices
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Route.EvenHyperplaneFloorCompress
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pivot chain of a constrained form

`Q ≥ 0` on a subspace `V` of a finite ordered index set iff `Q(v) ≥ 0` for every `v ∈ V` with last nonzero entry `1`.
The pivot value `κ_M = inf {Q(v) : v ∈ V_M, v_M = 1}` uses only the entries `≤ M`, and `Q ≥ 0` on every truncation
iff every `κ_M ≥ 0`. In cosine coordinates `Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b` holds iff every pivot value of `cosQ x − b·cosW`
against `cosR x` is nonnegative; rescaling coordinate `M` by `s_M` divides `κ_M` by `s_M² > 0`.
-/

noncomputable section

open Matrix Real

namespace Cvs.Upstream.ConstrainedFormPivotChain
open Cvs.ZeroCounting

/-! ### Positivity from the top-normalised vectors -/

section General

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Positivity on `V` is positivity on its top-normalised vectors**: `Q ≥ 0` on `V` iff `Q(v) ≥ 0` for every
`v ∈ V` vanishing above some `M` with `v_M = 1`. -/
theorem nonneg_iff_top_normalised (Q : Matrix ι ι ℝ) (V : Submodule ℝ (ι → ℝ)) :
    (∀ v ∈ V, 0 ≤ v ⬝ᵥ (Q *ᵥ v)) ↔
      ∀ M : ι, ∀ v ∈ V, (∀ i, M < i → v i = 0) → v M = 1 → 0 ≤ v ⬝ᵥ (Q *ᵥ v) := by
  classical
  refine ⟨fun h M v hv _ _ => h v hv, fun h v hv => ?_⟩
  by_cases h0 : v = 0
  · simp [h0]
  have hS : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra hne
    apply h0
    funext i
    by_contra hi
    exact hne ⟨i, by simpa using hi⟩
  set M := (Finset.univ.filter fun i => v i ≠ 0).max' hS
  have hM : v M ≠ 0 := by
    have := Finset.max'_mem _ hS
    simpa using this
  have htop : ∀ i, M < i → v i = 0 := by
    intro i hi
    by_contra hvi
    have : i ≤ M := Finset.le_max' _ i (by simp [hvi])
    exact absurd hi (not_lt.mpr this)
  have key := h M ((v M)⁻¹ • v) (V.smul_mem _ hv) (fun i hi => by simp [htop i hi])
    (by simp [inv_mul_cancel₀ hM])
  rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc] at key
  have hpos : 0 < (v M)⁻¹ * (v M)⁻¹ := mul_self_pos.mpr (inv_ne_zero hM)
  exact nonneg_of_mul_nonneg_right key hpos

end General

/-! ### The chain on `ℕ`-indexed entries -/

section Chain

variable {κ : Type*}

/-- The leading `(M+1)`-block form: `Q_M(a) = a ⬝ Q_{[0,M]} a`. -/
def qf (Q : Matrix ℕ ℕ ℝ) (M : ℕ) (a : Fin (M + 1) → ℝ) : ℝ :=
  a ⬝ᵥ (Q.submatrix Fin.val Fin.val *ᵥ a)

/-- The constraint rows restricted to the coordinates `≤ M`. -/
def rows (r : κ → ℕ → ℝ) (M : ℕ) : Matrix κ (Fin (M + 1)) ℝ :=
  Matrix.of fun k i => r k i

/-- The truncated constraint space `V_M = {a : Σ_{i ≤ M} r_k(i) a_i = 0 ∀ k}`. -/
def V (r : κ → ℕ → ℝ) (M : ℕ) : Submodule ℝ (Fin (M + 1) → ℝ) :=
  LinearMap.ker (rows r M).mulVecLin

theorem mem_V {r : κ → ℕ → ℝ} {M : ℕ} {a : Fin (M + 1) → ℝ} : a ∈ V r M ↔ rows r M *ᵥ a = 0 := by
  simp [V]

/-- **The pivot value** `κ_M = inf {Q_M(a) : a ∈ V_M, a_M = 1}` in `EReal` (`⊤` when no such `a` exists). -/
def kappa (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (M : ℕ) : EReal :=
  ⨅ (a : Fin (M + 1) → ℝ) (_ : a ∈ V r M) (_ : a (Fin.last M) = 1), ((qf Q M a : ℝ) : EReal)

theorem kappa_le {Q : Matrix ℕ ℕ ℝ} {r : κ → ℕ → ℝ} {M : ℕ} {a : Fin (M + 1) → ℝ} (ha : a ∈ V r M)
    (h1 : a (Fin.last M) = 1) : kappa Q r M ≤ (qf Q M a : EReal) :=
  iInf₂_le_of_le a ha (iInf_le _ h1)

theorem le_kappa_iff {Q : Matrix ℕ ℕ ℝ} {r : κ → ℕ → ℝ} {M : ℕ} {c : ℝ} :
    (c : EReal) ≤ kappa Q r M ↔ ∀ a ∈ V r M, a (Fin.last M) = 1 → c ≤ qf Q M a := by
  simp only [kappa, le_iInf_iff, EReal.coe_le_coe_iff]

theorem zero_le_kappa_iff {Q : Matrix ℕ ℕ ℝ} {r : κ → ℕ → ℝ} {M : ℕ} :
    0 ≤ kappa Q r M ↔ ∀ a ∈ V r M, a (Fin.last M) = 1 → 0 ≤ qf Q M a := by
  rw [← EReal.coe_zero]; exact le_kappa_iff

/-- **`κ_M` depends only on the entries and constraint coordinates `≤ M`.** -/
theorem kappa_congr {Q Q' : Matrix ℕ ℕ ℝ} {r r' : κ → ℕ → ℝ} {M : ℕ}
    (hQ : ∀ i j, i ≤ M → j ≤ M → Q i j = Q' i j) (hr : ∀ k i, i ≤ M → r k i = r' k i) :
    kappa Q r M = kappa Q' r' M := by
  have h1 : (Q.submatrix (Fin.val : Fin (M + 1) → ℕ) (Fin.val : Fin (M + 1) → ℕ))
      = Q'.submatrix (Fin.val : Fin (M + 1) → ℕ) (Fin.val : Fin (M + 1) → ℕ) := by
    ext i j; exact hQ i j (Nat.lt_succ_iff.mp i.2) (Nat.lt_succ_iff.mp j.2)
  have h2 : rows r M = rows r' M := by
    ext k i; exact hr k i (Nat.lt_succ_iff.mp i.2)
  simp only [kappa, qf, V, h1, h2]

/-! ### Truncation -/

/-- A sum over `Fin (N+1)` of a function vanishing above `M ≤ N` is its sum over `Fin (M+1)`. -/
theorem sum_castLE {M N : ℕ} (h : M + 1 ≤ N + 1) (f : Fin (N + 1) → ℝ)
    (hf : ∀ i : Fin (N + 1), M < (i : ℕ) → f i = 0) :
    ∑ i : Fin (M + 1), f (Fin.castLE h i) = ∑ i, f i := by
  rw [show (∑ i : Fin (M + 1), f (Fin.castLE h i)) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb h), f i from
    (Finset.sum_map Finset.univ (Fin.castLEEmb h) f).symm]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_
  by_contra hle
  exact hi (Finset.mem_map.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/-- The restriction of a vector on `Fin (N+1)` to its first `M+1` coordinates. -/
def restr {M N : ℕ} (h : M + 1 ≤ N + 1) (a : Fin (N + 1) → ℝ) : Fin (M + 1) → ℝ :=
  fun i => a (Fin.castLE h i)

theorem qf_restr (Q : Matrix ℕ ℕ ℝ) {M N : ℕ} (h : M + 1 ≤ N + 1) {a : Fin (N + 1) → ℝ}
    (ha : ∀ i : Fin (N + 1), M < (i : ℕ) → a i = 0) : qf Q M (restr h a) = qf Q N a := by
  have hin : ∀ i : Fin (N + 1), ∑ j : Fin (M + 1), Q.submatrix Fin.val Fin.val i (Fin.castLE h j) * a (Fin.castLE h j)
      = ∑ j : Fin (N + 1), Q.submatrix Fin.val Fin.val i j * a j := fun i =>
    sum_castLE h (fun j => Q.submatrix Fin.val Fin.val i j * a j) fun j hj => by rw [ha j hj, mul_zero]
  calc qf Q M (restr h a)
      = ∑ i : Fin (M + 1), a (Fin.castLE h i) * ∑ j : Fin (M + 1),
          Q.submatrix Fin.val Fin.val (Fin.castLE h i) (Fin.castLE h j) * a (Fin.castLE h j) := rfl
    _ = ∑ i : Fin (M + 1), a (Fin.castLE h i) * ∑ j : Fin (N + 1),
          Q.submatrix Fin.val Fin.val (Fin.castLE h i) j * a j := by simp only [hin]
    _ = qf Q N a := sum_castLE h (fun i => a i * ∑ j : Fin (N + 1), Q.submatrix Fin.val Fin.val i j * a j)
          fun i hi => by rw [ha i hi, zero_mul]

theorem bil_restr (Q : Matrix ℕ ℕ ℝ) {M N : ℕ} (h : M + 1 ≤ N + 1) (x : Fin (N + 1) → ℝ) {a : Fin (N + 1) → ℝ}
    (hx : ∀ i : Fin (N + 1), M < (i : ℕ) → x i = 0) (ha : ∀ i : Fin (N + 1), M < (i : ℕ) → a i = 0) :
    restr h x ⬝ᵥ (Q.submatrix Fin.val Fin.val *ᵥ restr h a) = x ⬝ᵥ (Q.submatrix Fin.val Fin.val *ᵥ a) := by
  have hin : ∀ i : Fin (N + 1), ∑ j : Fin (M + 1), Q.submatrix Fin.val Fin.val i (Fin.castLE h j) * a (Fin.castLE h j)
      = ∑ j : Fin (N + 1), Q.submatrix Fin.val Fin.val i j * a j := fun i =>
    sum_castLE h (fun j => Q.submatrix Fin.val Fin.val i j * a j) fun j hj => by rw [ha j hj, mul_zero]
  calc restr h x ⬝ᵥ (Q.submatrix Fin.val Fin.val *ᵥ restr h a)
      = ∑ i : Fin (M + 1), x (Fin.castLE h i) * ∑ j : Fin (M + 1),
          Q.submatrix Fin.val Fin.val (Fin.castLE h i) (Fin.castLE h j) * a (Fin.castLE h j) := rfl
    _ = ∑ i : Fin (M + 1), x (Fin.castLE h i) * ∑ j : Fin (N + 1),
          Q.submatrix Fin.val Fin.val (Fin.castLE h i) j * a j := by simp only [hin]
    _ = x ⬝ᵥ (Q.submatrix Fin.val Fin.val *ᵥ a) :=
          sum_castLE h (fun i => x i * ∑ j : Fin (N + 1), Q.submatrix Fin.val Fin.val i j * a j)
          fun i hi => by rw [hx i hi, zero_mul]

theorem rows_mulVec_restr (r : κ → ℕ → ℝ) {M N : ℕ} (h : M + 1 ≤ N + 1) {a : Fin (N + 1) → ℝ}
    (ha : ∀ i : Fin (N + 1), M < (i : ℕ) → a i = 0) : rows r M *ᵥ restr h a = rows r N *ᵥ a := by
  funext k
  simp only [rows, mulVec, dotProduct, of_apply, restr]
  exact sum_castLE h (fun i => r k i * a i) fun i hi => by simp [ha i hi]

/-- The extension by zero of a vector on `Fin (M+1)` to `Fin (N+1)`. -/
def zext {M N : ℕ} (a : Fin (M + 1) → ℝ) : Fin (N + 1) → ℝ :=
  fun i => if h : (i : ℕ) < M + 1 then a ⟨i, h⟩ else 0

theorem zext_apply_lt {M N : ℕ} (a : Fin (M + 1) → ℝ) (i : Fin (N + 1)) (hi : (i : ℕ) < M + 1) :
    (zext a : Fin (N + 1) → ℝ) i = a ⟨i, hi⟩ := by
  simp [zext, hi]

theorem zext_top {M N : ℕ} (a : Fin (M + 1) → ℝ) (i : Fin (N + 1)) (hi : M < (i : ℕ)) :
    (zext a : Fin (N + 1) → ℝ) i = 0 := by
  simp [zext, show ¬ (i : ℕ) < M + 1 by omega]

theorem restr_zext {M N : ℕ} (h : M + 1 ≤ N + 1) (a : Fin (M + 1) → ℝ) : restr h (zext a) = a := by
  funext i; simp [restr, zext, i.2]

/-- **N-independence**: `κ_M` is the infimum of `Q_N` over `a ∈ V_N` vanishing above `M` with `a_M = 1`, for
every truncation `N ≥ M`. -/
theorem kappa_eq_trunc (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    kappa Q r M = ⨅ (a : Fin (N + 1) → ℝ) (_ : a ∈ V r N) (_ : ∀ i : Fin (N + 1), M < (i : ℕ) → a i = 0)
      (_ : a ⟨M, by omega⟩ = 1), ((qf Q N a : ℝ) : EReal) := by
  have h : M + 1 ≤ N + 1 := by omega
  apply le_antisymm
  · refine le_iInf fun a => le_iInf fun ha => le_iInf fun htop => le_iInf fun h1 => ?_
    rw [← qf_restr Q h htop]
    refine kappa_le ?_ ?_
    · rw [mem_V, rows_mulVec_restr r h htop]; exact mem_V.mp ha
    · exact (congrArg a (Fin.ext rfl)).trans h1
  · refine le_iInf fun a => le_iInf fun ha => le_iInf fun h1 => ?_
    have htop : ∀ i : Fin (N + 1), M < (i : ℕ) → (zext a : Fin (N + 1) → ℝ) i = 0 := zext_top a
    refine iInf_le_of_le (zext a) (iInf_le_of_le ?_ (iInf_le_of_le htop (iInf_le_of_le ?_ ?_)))
    · rw [mem_V, ← rows_mulVec_restr r h htop, restr_zext]; exact mem_V.mp ha
    · rw [zext_apply_lt a _ (Nat.lt_succ_self M)]; exact (congrArg a (Fin.ext rfl)).trans h1
    · rw [← qf_restr Q h htop, restr_zext]

/-- **The chain at one truncation**: `Q_N ≥ 0` on `V_N` iff `κ_M ≥ 0` for every `M ≤ N`. -/
theorem nonneg_trunc_iff (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (N : ℕ) :
    (∀ a ∈ V r N, 0 ≤ qf Q N a) ↔ ∀ M ≤ N, 0 ≤ kappa Q r M := by
  refine (nonneg_iff_top_normalised _ (V r N)).trans ⟨fun h M hMN => ?_, fun h M a ha htop h1 => ?_⟩
  · have hle : M + 1 ≤ N + 1 := by omega
    rw [zero_le_kappa_iff]
    intro a ha h1
    have htop : ∀ i : Fin (N + 1), M < (i : ℕ) → (zext a : Fin (N + 1) → ℝ) i = 0 := zext_top a
    have := h ⟨M, by omega⟩ (zext a) (by rw [mem_V, ← rows_mulVec_restr r hle htop, restr_zext]; exact mem_V.mp ha)
      (fun i hi => zext_top a i hi)
      (by rw [zext_apply_lt a _ (Nat.lt_succ_self M)]; exact (congrArg a (Fin.ext rfl)).trans h1)
    change 0 ≤ qf Q N (zext a) at this
    rwa [← qf_restr Q hle htop, restr_zext] at this
  · have hle : (M : ℕ) + 1 ≤ N + 1 := by omega
    have htop' : ∀ i : Fin (N + 1), (M : ℕ) < (i : ℕ) → a i = 0 := fun i hi => htop i hi
    have hk := zero_le_kappa_iff.mp (h M (Nat.lt_succ_iff.mp M.2)) (restr hle a)
      (by rw [mem_V, rows_mulVec_restr r hle htop']; exact mem_V.mp ha)
      ((congrArg a (Fin.ext rfl)).trans h1)
    rw [qf_restr Q hle htop'] at hk
    exact hk

/-- **The pivot chain**: `Q_N ≥ 0` on `V_N` at every truncation `N` iff every pivot value `κ_M ≥ 0`. -/
theorem nonneg_iff_kappa (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) :
    (∀ N, ∀ a ∈ V r N, 0 ≤ qf Q N a) ↔ ∀ M, 0 ≤ kappa Q r M :=
  ⟨fun h M => (nonneg_trunc_iff Q r M).mp (h M) M le_rfl,
    fun h N => (nonneg_trunc_iff Q r N).mpr fun M _ => h M⟩

/-! ### Changing the coordinate scale -/

/-- The form in rescaled coordinates `c_i = s_i a_i`. -/
def rescaleQ (s : ℕ → ℝ) (Q : Matrix ℕ ℕ ℝ) : Matrix ℕ ℕ ℝ := fun i j => Q i j / (s i * s j)

/-- The constraint rows in rescaled coordinates `c_i = s_i a_i`. -/
def rescaleR (s : ℕ → ℝ) (r : κ → ℕ → ℝ) : κ → ℕ → ℝ := fun k i => r k i / s i

theorem qf_smul' (Q : Matrix ℕ ℕ ℝ) (M : ℕ) (a : Fin (M + 1) → ℝ) (t : ℝ) :
    qf Q M (t • a) = t ^ 2 * qf Q M a := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

theorem qf_rescale {s : ℕ → ℝ} (hs : ∀ i, s i ≠ 0) (Q : Matrix ℕ ℕ ℝ) (M : ℕ) (a : Fin (M + 1) → ℝ) :
    qf (rescaleQ s Q) M (fun i => s i * a i) = qf Q M a := by
  simp only [qf, rescaleQ, dotProduct, mulVec, submatrix_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hi := hs i
  have hj := hs j
  field_simp

theorem rows_rescale {s : ℕ → ℝ} (hs : ∀ i, s i ≠ 0) (r : κ → ℕ → ℝ) (M : ℕ) (a : Fin (M + 1) → ℝ) :
    rows (rescaleR s r) M *ᵥ (fun i => s i * a i) = rows r M *ᵥ a := by
  funext k
  simp only [rows, rescaleR, mulVec, dotProduct, of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := hs i
  field_simp

/-- **A change of coordinate scale divides each pivot value by `s_M²`**: in coordinates `c_i = s_i a_i`,
`c ≤ κ_M` iff `c / s_M² ≤ κ_M` of the rescaled form against the rescaled rows. -/
theorem le_kappa_rescale {s : ℕ → ℝ} (hs : ∀ i, s i ≠ 0) (Q : Matrix ℕ ℕ ℝ) (r : κ → ℕ → ℝ) (M : ℕ) (c : ℝ) :
    (c : EReal) ≤ kappa Q r M ↔ ((c / s M ^ 2 : ℝ) : EReal) ≤ kappa (rescaleQ s Q) (rescaleR s r) M := by
  have hM := hs M
  have hM2 : 0 < s M ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hM))
  rw [le_kappa_iff, le_kappa_iff]
  constructor
  · intro h b hb hb1
    set a : Fin (M + 1) → ℝ := fun i => s M * b i / s i
    have hsa : (fun i : Fin (M + 1) => s i * a i) = s M • b := by
      funext i; have := hs i; simp only [a, Pi.smul_apply, smul_eq_mul]; field_simp
    have ha : a ∈ V r M := by
      rw [mem_V, ← rows_rescale hs, hsa, mulVec_smul, mem_V.mp hb, smul_zero]
    have ha1 : a (Fin.last M) = 1 := by
      simp only [a, Fin.val_last, hb1, mul_one]; exact div_self hM
    have hq := h a ha ha1
    rw [← qf_rescale hs, hsa, qf_smul'] at hq
    rw [div_le_iff₀ hM2]; linarith
  · intro h a ha ha1
    set b : Fin (M + 1) → ℝ := (s M)⁻¹ • fun i : Fin (M + 1) => s i * a i with hbdef
    have hb : b ∈ V (rescaleR s r) M := by
      rw [mem_V, hbdef, mulVec_smul, rows_rescale hs, mem_V.mp ha, smul_zero]
    have hb1 : b (Fin.last M) = 1 := by
      rw [hbdef]
      simp only [Pi.smul_apply, smul_eq_mul, Fin.val_last, ha1, mul_one]; exact inv_mul_cancel₀ hM
    have hq := h b hb hb1
    rw [hbdef, qf_smul', qf_rescale hs, inv_pow, ← div_eq_inv_mul, div_le_div_iff_of_pos_right hM2] at hq
    exact hq

end Chain

section EvenBulkFloor

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Route.L1FloorFromBulkD0 (Dom rung)

/-! ### The even bulk floor in cosine coordinates -/

/-- The fold of an integer-mode function onto the cosine index `m`: `g(0)` at `m = 0`, `g(m) + g(−m)` otherwise. -/
def cfold (g : ℤ → ℝ) (m : ℕ) : ℝ := if m = 0 then g 0 else g m + g (-(m : ℤ))

theorem cfold_sum {J : Type*} (s : Finset J) (c : J → ℝ) (h : J → ℤ → ℝ) (m : ℕ) :
    cfold (fun t => ∑ n ∈ s, c n * h n t) m = ∑ n ∈ s, c n * cfold (h n) m := by
  unfold cfold; split_ifs <;> simp [Finset.sum_add_distrib, mul_add]

/-- The even mode vector with cosine coordinates `a`: `f(0) = a₀`, `f(±(k+1)) = a_{k+1}`. -/
def ofCos (N : ℕ) (a : Fin (N + 1) → ℝ) : Idx N → ℝ
  | none => a 0
  | some (k, _) => a k.succ

/-- The cosine coordinates of a mode vector. -/
def toCos (N : ℕ) (f : Idx N → ℝ) : Fin (N + 1) → ℝ :=
  Fin.cases (f none) fun k => f (some (k, true))

theorem ofCos_even (N : ℕ) (a : Fin (N + 1) → ℝ) (i : Idx N) : ofCos N a (negI N i) = ofCos N a i := by
  rcases i with _ | ⟨k, b⟩ <;> rfl

theorem ofCos_toCos {N : ℕ} {f : Idx N → ℝ} (hf : ∀ i, f (negI N i) = f i) : ofCos N (toCos N f) = f := by
  funext i
  rcases i with _ | ⟨k, b⟩
  · rfl
  · cases b
    · have := hf (some (k, true)); simp only [negI, Bool.not_true] at this; simpa [ofCos, toCos] using this.symm
    · simp [ofCos, toCos]

/-- **Folding a mode sum**: `Σ_i f_i g(mode i) = Σ_m a_m cfold g m` for `f = ofCos a`. -/
theorem sum_ofCos_mul (N : ℕ) (a : Fin (N + 1) → ℝ) (g : ℤ → ℝ) :
    ∑ i, ofCos N a i * g (mode N i) = ∑ m : Fin (N + 1), a m * cfold g m := by
  rw [Fintype.sum_option, Fin.sum_univ_succ, Fintype.sum_prod_type]
  simp only [ofCos, mode, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, cfold, Fin.val_zero,
    if_true, Fin.val_succ, Nat.add_one_ne_zero, if_false, Nat.cast_add, Nat.cast_one]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dot_ofCos (N : ℕ) (a : Fin (N + 1) → ℝ) :
    ofCos N a ⬝ᵥ ofCos N a = ∑ m : Fin (N + 1), a m * ((if (m : ℕ) = 0 then 1 else 2) * a m) := by
  rw [dotProduct, Fintype.sum_option, Fin.sum_univ_succ, Fintype.sum_prod_type]
  simp only [ofCos, Fintype.sum_bool, Fin.val_zero, if_true, Fin.val_succ, Nat.add_one_ne_zero, if_false]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- The cosine-mode window matrix at `x`: the CvS pair values folded over `±m`, `±n`. -/
def cosQ (x : ℕ) : Matrix ℕ ℕ ℝ := fun m n =>
  cfold (fun s => cfold (fun t => Cvs.Finite.ModeSumPairValues.pairQ x (Nat.clog 2 x) (Real.log x) s t / 2) n) m

/-- The cosine coordinate weights `1, 2, 2, …` of the `L²` norm. -/
def cosW : Matrix ℕ ℕ ℝ := diagonal fun m => if m = 0 then 1 else 2

/-- The pairing of a window class with the cosine of mode `s`. -/
def cosCoeff (x : ℕ) (η : Dom x) (s : ℤ) : ℝ :=
  ∫ y, Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) y *
    (if y ∈ Set.Ioc (0 : ℝ) (Real.log x) then Real.cos (2 * π * (s : ℝ) / Real.log x * y) else 0)

/-- The `R₁` constraint rows in cosine coordinates: the rung pairings folded over `±m`. -/
def cosR (x : ℕ) : Cvs.Approximant.SpineSubspace.SF x → ℕ → ℝ := fun j m => cfold (cosCoeff x (rung x j)) m

theorem normalCoeff_eq (x N : ℕ) (η : Dom x) (i : Idx N) :
    Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) η (mode N) i = cosCoeff x η (mode N i) := by
  simp only [Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff, Cvs.Finite.DiscreteTwoGap.ell, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, Cvs.Finite.TruncationZeroFreeOffAxes.omega, cosCoeff]
  congr 1
  funext y
  congr 1
  split_ifs
  · simp [Pi.single_apply]
  · rfl

theorem qf_cosQ {x : ℕ} (hx1 : (1 : ℝ) < x) (N : ℕ) (a : Fin (N + 1) → ℝ) :
    ofCos N a ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ ofCos N a) = qf (cosQ x) N a := by
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hin : ∀ i, (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ ofCos N a) i
      = ∑ n : Fin (N + 1), a n * cfold (fun t => Cvs.Finite.ModeSumPairValues.pairQ x (Nat.clog 2 x) (Real.log x) (mode N i) t / 2) n := by
    intro i
    rw [← sum_ofCos_mul]
    simp only [mulVec, dotProduct, Cvs.Finite.TruncationQuadraticForm.M_apply hL _ _ (Cvs.Finite.SymmetricModeSet.mode_injective N)]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [dotProduct, hin]
  refine (sum_ofCos_mul N a (fun s => ∑ n : Fin (N + 1), a n *
    cfold (fun t => Cvs.Finite.ModeSumPairValues.pairQ x (Nat.clog 2 x) (Real.log x) s t / 2) n)).trans ?_
  simp only [qf, dotProduct, mulVec, submatrix_apply, cosQ]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [cfold_sum]
  congr 1
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

theorem qf_cosW (N : ℕ) (a : Fin (N + 1) → ℝ) : qf cosW N a = ofCos N a ⬝ᵥ ofCos N a := by
  rw [dot_ofCos]
  simp only [qf, dotProduct, mulVec, submatrix_apply, cosW, diagonal_apply, Fin.val_inj]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  simp

theorem qf_sub_smul (Q W : Matrix ℕ ℕ ℝ) (b : ℝ) (N : ℕ) (a : Fin (N + 1) → ℝ) :
    qf (Q - b • W) N a = qf Q N a - b * qf W N a := by
  simp only [qf]
  rw [show (Q - b • W).submatrix Fin.val Fin.val = Q.submatrix Fin.val Fin.val - b • W.submatrix Fin.val Fin.val
    from rfl, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem rows_cosR {x : ℕ} (N : ℕ) (a : Fin (N + 1) → ℝ) (j : Cvs.Approximant.SpineSubspace.SF x) :
    Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (rung x j) (mode N) ⬝ᵥ ofCos N a
      = (rows (cosR x) N *ᵥ a) j := by
  rw [dotProduct_comm, dotProduct]
  simp only [normalCoeff_eq]
  rw [sum_ofCos_mul]
  simp only [rows, mulVec, dotProduct, of_apply, cosR]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem cfold_comm (f : ℤ → ℤ → ℝ) (m n : ℕ) :
    cfold (fun s => cfold (fun t => f s t) n) m = cfold (fun t => cfold (fun s => f s t) m) n := by
  unfold cfold; split_ifs <;> ring

/-- The cosine-mode window matrix is symmetric. -/
theorem cosQ_symm {x : ℕ} (hx1 : (1 : ℝ) < x) (m n : ℕ) : cosQ x n m = cosQ x m n := by
  have hL : 0 < Real.log x := Real.log_pos hx1
  simp only [cosQ]
  rw [cfold_comm]
  congr 1
  funext t
  congr 1
  funext s
  rw [Cvs.Finite.TruncationQuadraticForm.pairQ_symm hL x (Nat.clog 2 x)]

/-- **The even bulk floor is the pivot chain**: at `1 < x`, `EvenBulkFloor x b` holds iff every pivot value of
`cosQ x − b·cosW` against the cosine rows `cosR x` of `R₁` is nonnegative. -/
theorem evenBulkFloor_iff_kappa {x : ℕ} (hx1 : (1 : ℝ) < x) (b : ℝ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b ↔ ∀ M, 0 ≤ kappa (cosQ x - b • cosW) (cosR x) M := by
  rw [Cvs.Finite.EvenBulkModeMatrices.evenBulkFloor_iff_matrix hx1, ← nonneg_iff_kappa]
  refine forall_congr' fun N => ⟨fun h a ha => ?_, fun h f hf hc => ?_⟩
  · have := h (ofCos N a) (ofCos_even N a) fun j => by rw [rows_cosR, mem_V.mp ha]; rfl
    rw [qf_cosQ hx1, ← qf_cosW] at this
    rw [qf_sub_smul]; linarith
  · rw [← ofCos_toCos hf] at hc ⊢
    have ha : toCos N f ∈ V (cosR x) N := mem_V.mpr (funext fun j => by rw [← rows_cosR]; exact hc j)
    have := h _ ha
    rw [qf_sub_smul] at this
    rw [qf_cosQ hx1, ← qf_cosW]; linarith

/-- **hF is the pivot chain**: at `1 < x`, `EvenBulkFloor x 0` iff every pivot value `κ_M` of `cosQ x` against
`cosR x` is nonnegative. -/
theorem evenBulkFloor_zero_iff_kappa {x : ℕ} (hx1 : (1 : ℝ) < x) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 ↔ ∀ M, 0 ≤ kappa (cosQ x) (cosR x) M := by
  rw [evenBulkFloor_iff_kappa hx1, zero_smul, sub_zero]

end EvenBulkFloor

end Cvs.Upstream.ConstrainedFormPivotChain
