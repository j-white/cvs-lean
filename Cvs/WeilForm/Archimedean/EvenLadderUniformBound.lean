import Mathlib
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Upstream.HilbertInequalityUniformGap
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.WeilForm.Archimedean.SymbolImaginaryTrapped

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A uniform bound for the positive-mode even archimedean ladder

The ladder, excluding the pole term and the zero mode, is dominated by a Hilbert
matrix. Its finite quadratic forms are bounded uniformly in the window length and
the number of modes.
-/

noncomputable section

open Real Finset Matrix

namespace Cvs.WeilForm.Archimedean.EvenLadderUniformBound

open Cvs.Finite.WindowMatrixSymbolKernel (bk uu)

/-- The positive rank-one part of the digamma ladder, without the pole term. -/
def ladder (L A B : ℝ) : ℝ :=
  ∑' k : ℕ, 2 * (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L k) * uu (bk k) A * uu (bk k) B

/-- The imaginary digamma series bounds the reciprocal Cauchy ladder. -/
theorem reciprocal_ladder_bound {C : ℝ} (hC : 0 < C) :
    (∑' k : ℕ, 2 / (bk k ^ 2 + C ^ 2)) ≤ (2 + π / 2) / C := by
  have heq : ∀ k : ℕ,
      2 / (bk k ^ 2 + C ^ 2) = Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm C k / C := by
    intro k
    unfold Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm bk
    have hd : (0 : ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (C / 2) ^ 2 := by positivity
    have hd' : (0 : ℝ) < (2 * (k : ℝ) + 1 / 2) ^ 2 + C ^ 2 := by positivity
    field_simp
    ring
  rw [tsum_congr heq, tsum_div_const, (Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.hasSum_imTerm C).tsum_eq]
  have hb := (Cvs.WeilForm.Archimedean.SymbolImaginaryTrapped.archSymbolIm_bounds hC).2
  have ha : 0 ≤ Real.arctan (1 / (4 * (C / 2))) := Real.arctan_nonneg.mpr (by positivity)
  have hc : (C / 2) / (1 / 16 + (C / 2) ^ 2) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (C / 2 - 1 / 4)]
  exact div_le_div_of_nonneg_right (by linarith) hC.le

/-- Each positive ladder summand is bounded by the reciprocal kernel at the larger frequency. -/
theorem ladder_term_le {L A B : ℝ} (k : ℕ) :
    2 * (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L k) * uu (bk k) A * uu (bk k) B
      ≤ 2 / (bk k ^ 2 + (max A B) ^ 2) := by
  have hb := Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k
  have htf0 : 0 ≤ Cvs.Finite.DiagonalLevySymbol.tailFactor L k := (Real.exp_pos _).le
  have hdA : 0 < bk k ^ 2 + A ^ 2 := by positivity
  have hdB : 0 < bk k ^ 2 + B ^ 2 := by positivity
  have huA : 0 ≤ uu (bk k) A := by unfold uu; positivity
  have huB : 0 ≤ uu (bk k) B := by unfold uu; positivity
  have hprod : uu (bk k) A * uu (bk k) B ≤ 1 / (bk k ^ 2 + (max A B) ^ 2) := by
    rcases le_total A B with h | h
    · rw [max_eq_right h]
      unfold uu
      rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hdA hdB) hdB]
      nlinarith [mul_nonneg (sq_nonneg A) (le_of_lt hdB)]
    · rw [max_eq_left h]
      unfold uu
      rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hdA hdB) hdA]
      nlinarith [mul_nonneg (sq_nonneg B) (le_of_lt hdA)]
  calc
    2 * (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L k) * uu (bk k) A * uu (bk k) B
        = 2 * (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L k) * (uu (bk k) A * uu (bk k) B) := by ring
    _ ≤ 2 * (uu (bk k) A * uu (bk k) B) := by
      exact mul_le_mul_of_nonneg_right (by linarith : 2 * (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L k) ≤ 2)
        (mul_nonneg huA huB)
    _ ≤ 2 / (bk k ^ 2 + (max A B) ^ 2) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)

/-- The ladder is dominated by a Cauchy kernel in the sum of its positive frequencies. -/
theorem ladder_le {L A B : ℝ} (hL : 0 < L) (hA : 0 < A) (hB : 0 < B) :
    ladder L A B ≤ (4 + π) / (A + B) := by
  have hC : 0 < max A B := lt_max_of_lt_left hA
  have hs : Summable (fun k : ℕ => 2 / (bk k ^ 2 + (max A B) ^ 2)) := by
    have heq : ∀ k : ℕ,
        2 / (bk k ^ 2 + (max A B) ^ 2) = Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (max A B) k / max A B := by
      intro k
      unfold Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm bk
      have hd : (0 : ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (max A B / 2) ^ 2 := by positivity
      have hd' : (0 : ℝ) < (2 * (k : ℝ) + 1 / 2) ^ 2 + (max A B) ^ 2 := by positivity
      field_simp
      ring
    exact ((Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.summable_imTerm _).div_const _).congr (fun k => (heq k).symm)
  have hn : ∀ k : ℕ,
      0 ≤ 2 * (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L k) * uu (bk k) A * uu (bk k) B := by
    intro k
    have htf1 : Cvs.Finite.DiagonalLevySymbol.tailFactor L k ≤ 1 := by
      rw [Cvs.Finite.WindowMatrixSymbolKernel.tailFactor_eq_rpow]
      exact Real.exp_le_one_iff.mpr (by nlinarith [Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k])
    have hb := Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k
    unfold uu
    positivity
  have hl := Summable.of_nonneg_of_le hn (ladder_term_le (L := L) (A := A) (B := B)) hs
  calc
    ladder L A B ≤ ∑' k : ℕ, 2 / (bk k ^ 2 + (max A B) ^ 2) :=
      hl.tsum_le_tsum (ladder_term_le (L := L) (A := A) (B := B)) hs
    _ ≤ (2 + π / 2) / max A B := reciprocal_ladder_bound hC
    _ ≤ (4 + π) / (A + B) := by
      rw [div_le_div_iff₀ hC (by positivity)]
      have hsum : A + B ≤ 2 * max A B := by linarith [le_max_left A B, le_max_right A B]
      nlinarith [Real.pi_pos]

/-- The normalized positive-mode ladder has an entrywise Hilbert-matrix bound. -/
theorem ladder_mode_le {L : ℝ} (hL : 0 < L) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ladder L (2 * π * m / L) (2 * π * n / L) / L
      ≤ (4 + π) / (2 * π) / ((m : ℝ) + n) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := div_le_div_of_nonneg_right
    (ladder_le hL (by positivity : 0 < 2 * π * m / L) (by positivity : 0 < 2 * π * n / L)) hL.le
  refine h.trans_eq ?_
  field_simp

section Hilbert

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Hilbert inequality on positive integer nodes, written as a Hankel kernel. -/
theorem hankel_bilinear (mode : ι → ℕ) (hinj : Function.Injective mode)
    (hpos : ∀ i, 0 < mode i) (u v : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    |∑ i, ∑ j, u i * v j / ((mode i : ℝ) + mode j)|
      ≤ π / 2 * (s ^ 2 * ∑ i, u i ^ 2 + (∑ i, v i ^ 2) / s ^ 2) := by
  let freq : ι ⊕ ι → ℝ := Sum.elim (fun i => (mode i : ℝ)) (fun i => -(mode i : ℝ))
  let U : ι ⊕ ι → ℝ := Sum.elim u (fun _ => 0)
  let V : ι ⊕ ι → ℝ := Sum.elim (fun _ => 0) v
  have hp : ∀ i, (1 : ℝ) ≤ mode i := fun i => by exact_mod_cast hpos i
  have hg : ∀ r t : ι ⊕ ι, r ≠ t → (1 : ℝ) ≤ |freq r - freq t| := by
    intro r t hrt
    cases r with
    | inl i =>
      cases t with
      | inl j =>
        have hm : mode i ≠ mode j := fun h => hrt (congrArg Sum.inl (hinj h))
        dsimp [freq]
        rcases lt_or_gt_of_ne hm with h | h
        · have hc : (mode i : ℝ) + 1 ≤ mode j := by exact_mod_cast (show mode i + 1 ≤ mode j by omega)
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have hc : (mode j : ℝ) + 1 ≤ mode i := by exact_mod_cast (show mode j + 1 ≤ mode i by omega)
          rw [abs_of_nonneg (by linarith)]
          linarith
      | inr j =>
        dsimp [freq]
        rw [abs_of_nonneg (by linarith [hp i, hp j])]
        linarith [hp i, hp j]
    | inr i =>
      cases t with
      | inl j =>
        dsimp [freq]
        rw [abs_of_nonpos (by linarith [hp i, hp j])]
        linarith [hp i, hp j]
      | inr j =>
        have hm : mode i ≠ mode j := fun h => hrt (congrArg Sum.inr (hinj h))
        dsimp [freq]
        rcases lt_or_gt_of_ne hm with h | h
        · have hc : (mode i : ℝ) + 1 ≤ mode j := by exact_mod_cast (show mode i + 1 ≤ mode j by omega)
          rw [abs_of_nonneg (by linarith)]
          linarith
        · have hc : (mode j : ℝ) + 1 ≤ mode i := by exact_mod_cast (show mode j + 1 ≤ mode i by omega)
          rw [abs_of_nonpos (by linarith)]
          linarith
  have h := Cvs.Upstream.HilbertInequalityUniformGap.hilbert_real_bilinear (freq := freq) (D := 1) (by norm_num) hg U V hs
  simpa [freq, U, V, Fintype.sum_sum_type, sub_neg_eq_add] using h

/-- The normalized ladder matrix on an injective family of positive modes. -/
def positiveMatrix (L : ℝ) (mode : ι → ℕ) : Matrix ι ι ℝ :=
  fun i j => ladder L (2 * π * mode i / L) (2 * π * mode j / L) / L

omit [Fintype ι] [DecidableEq ι] in
/-- The ladder entries are nonnegative when the window length is positive. -/
theorem positiveMatrix_nonneg {L : ℝ} (hL : 0 < L) (mode : ι → ℕ) (i j : ι) :
    0 ≤ positiveMatrix L mode i j := by
  unfold positiveMatrix ladder
  apply div_nonneg (tsum_nonneg fun k => ?_) hL.le
  have hb := Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k
  have htf : Cvs.Finite.DiagonalLevySymbol.tailFactor L k ≤ 1 := by
    rw [Cvs.Finite.WindowMatrixSymbolKernel.tailFactor_eq_rpow]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  unfold uu
  positivity

/-- A finite bilinear estimate for the positive-mode block, uniform in length and order. -/
theorem positiveMatrix_bilinear_le {L : ℝ} (hL : 0 < L) (mode : ι → ℕ)
    (hinj : Function.Injective mode) (hpos : ∀ i, 0 < mode i)
    (u v : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    |u ⬝ᵥ (positiveMatrix L mode *ᵥ v)|
      ≤ (4 + π) / 4 * (s ^ 2 * ∑ i, u i ^ 2 + (∑ i, v i ^ 2) / s ^ 2) := by
  let c : ℝ := (4 + π) / (2 * π)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hn : 0 ≤ ∑ i, ∑ j, |u i| * |v j| / ((mode i : ℝ) + mode j) := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    have hi : (0 : ℝ) < mode i := by exact_mod_cast hpos i
    have hj : (0 : ℝ) < mode j := by exact_mod_cast hpos j
    positivity
  have hh := hankel_bilinear mode hinj hpos (fun i => |u i|) (fun i => |v i|) hs
  rw [abs_of_nonneg hn] at hh
  simp only [sq_abs] at hh
  have habs : |u ⬝ᵥ (positiveMatrix L mode *ᵥ v)|
      ≤ ∑ i, ∑ j, |u i| * |v j| * positiveMatrix L mode i j := by
    change |∑ i, u i * ∑ j, positiveMatrix L mode i j * v j| ≤ _
    simp_rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (positiveMatrix_nonneg hL mode i j)]
    ring
  calc
    |u ⬝ᵥ (positiveMatrix L mode *ᵥ v)|
        ≤ ∑ i, ∑ j, |u i| * |v j| * positiveMatrix L mode i j := habs
    _ ≤ c * ∑ i, ∑ j, |u i| * |v j| / ((mode i : ℝ) + mode j) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      have h := mul_le_mul_of_nonneg_left (ladder_mode_le hL (hpos i) (hpos j))
        (mul_nonneg (abs_nonneg (u i)) (abs_nonneg (v j)))
      change |u i| * |v j| * (ladder L (2 * π * mode i / L) (2 * π * mode j / L) / L) ≤ _
      exact h.trans_eq (by dsimp [c]; ring)
    _ ≤ c * (π / 2 * (s ^ 2 * ∑ i, u i ^ 2 + (∑ i, v i ^ 2) / s ^ 2)) :=
      mul_le_mul_of_nonneg_left hh hc
    _ = (4 + π) / 4 * (s ^ 2 * ∑ i, u i ^ 2 + (∑ i, v i ^ 2) / s ^ 2) := by
      dsimp [c]
      field_simp
      ring

/-- The positive-mode quadratic form has bound `(4 + π)/2` in the ordinary coefficient norm. -/
theorem positiveMatrix_quad_le {L : ℝ} (hL : 0 < L) (mode : ι → ℕ)
    (hinj : Function.Injective mode) (hpos : ∀ i, 0 < mode i) (u : ι → ℝ) :
    u ⬝ᵥ (positiveMatrix L mode *ᵥ u) ≤ (4 + π) / 2 * ∑ i, u i ^ 2 := by
  have h := positiveMatrix_bilinear_le hL mode hinj hpos u u (s := 1) (by norm_num)
  simp only [one_pow, one_mul, div_one] at h
  calc
    u ⬝ᵥ (positiveMatrix L mode *ᵥ u) ≤ |u ⬝ᵥ (positiveMatrix L mode *ᵥ u)| := le_abs_self _
    _ ≤ (4 + π) / 4 * ((∑ i, u i ^ 2) + ∑ i, u i ^ 2) := h
    _ = (4 + π) / 2 * ∑ i, u i ^ 2 := by ring

end Hilbert

end Cvs.WeilForm.Archimedean.EvenLadderUniformBound
