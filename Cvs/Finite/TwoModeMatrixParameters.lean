import Mathlib
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm

/-!
# The two-mode CvS matrix in five parameters
On `Idx 2 = {0, ±1, ±2}` every entry of `Cvs.Finite.TruncationQuadraticForm.M` is one of `a₀, a₁, a₂` (the diagonal) or a divided
difference of the odd `bval`, fixed by `p = pairQ(0,1)/2` and `q = pairQ(0,2)/2`: `M(1,−1) = p`,
`M(2,−2) = q`, `M(1,2) = 2q − p`, `M(1,−2) = (p + 2q)/3` (`pairQ_two_entries`). `quad_two` writes the
quadratic form in these five numbers, the input to any two-mode certificate.
-/

noncomputable section

open Real Matrix

namespace Cvs.Finite.TwoModeMatrixParameters

/-- The five parameters of the two-mode matrix. -/
def a0 (P R : ℕ) (L : ℝ) : ℝ := Cvs.Finite.ModeSumPairValues.pairQ P R L 0 0 / 2
def a1 (P R : ℕ) (L : ℝ) : ℝ := Cvs.Finite.ModeSumPairValues.pairQ P R L 1 1 / 2
def a2 (P R : ℕ) (L : ℝ) : ℝ := Cvs.Finite.ModeSumPairValues.pairQ P R L 2 2 / 2
def pp (P R : ℕ) (L : ℝ) : ℝ := Cvs.Finite.ModeSumPairValues.pairQ P R L 0 1 / 2
def qq (P R : ℕ) (L : ℝ) : ℝ := Cvs.Finite.ModeSumPairValues.pairQ P R L 0 2 / 2

/-- Every off-diagonal pair value is a divided difference of `bval` over the frequencies. -/
theorem half_pairQ_off {L : ℝ} (hL : 0 < L) (P R : ℕ) {m n : ℤ} (hmn : m ≠ n) :
    Cvs.Finite.ModeSumPairValues.pairQ P R L m n / 2
      = L * (Cvs.Finite.PairFormDividedDifference.bval P R L m - Cvs.Finite.PairFormDividedDifference.bval P R L n)
        / (2 * π * ((m : ℝ) - n)) := by
  rw [Cvs.Finite.PairFormDividedDifference.pairQ_off hL P R hmn]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hL0 : L ≠ 0 := hL.ne'
  have hmn' : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  rw [show 2 * π * (m : ℝ) / L - 2 * π * n / L = 2 * π * ((m : ℝ) - n) / L by ring]
  field_simp

theorem bval_zero (P R : ℕ) (L : ℝ) : Cvs.Finite.PairFormDividedDifference.bval P R L 0 = 0 := by
  have := Cvs.Finite.PairFormDividedDifference.bval_neg P R L 0
  simp only [neg_zero] at this
  linarith

/-- **The off-diagonal entries of the two-mode matrix in `p` and `q`.** -/
theorem pairQ_two_entries {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    Cvs.Finite.ModeSumPairValues.pairQ P R L 1 (-1) / 2 = pp P R L
    ∧ Cvs.Finite.ModeSumPairValues.pairQ P R L 2 (-2) / 2 = qq P R L
    ∧ Cvs.Finite.ModeSumPairValues.pairQ P R L 1 2 / 2 = 2 * qq P R L - pp P R L
    ∧ Cvs.Finite.ModeSumPairValues.pairQ P R L 1 (-2) / 2 = (pp P R L + 2 * qq P R L) / 3 := by
  have hb0 := bval_zero P R L
  have hb1 := Cvs.Finite.PairFormDividedDifference.bval_neg P R L 1
  have hb2 := Cvs.Finite.PairFormDividedDifference.bval_neg P R L 2
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hL0 : L ≠ 0 := hL.ne'
  have e01 := half_pairQ_off hL P R (m := 0) (n := 1) (by norm_num)
  have e02 := half_pairQ_off hL P R (m := 0) (n := 2) (by norm_num)
  have e1m1 := half_pairQ_off hL P R (m := 1) (n := -1) (by norm_num)
  have e2m2 := half_pairQ_off hL P R (m := 2) (n := -2) (by norm_num)
  have e12 := half_pairQ_off hL P R (m := 1) (n := 2) (by norm_num)
  have e1m2 := half_pairQ_off hL P R (m := 1) (n := -2) (by norm_num)
  unfold pp qq
  rw [e01, e02, e1m1, e2m2, e12, e1m2, hb0, hb1, hb2]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> · field_simp; ring

/-- **The two-mode quadratic form in its five parameters.** -/
theorem quad_two {L : ℝ} (hL : 0 < L) (P R : ℕ) (v : Cvs.Finite.SymmetricModeSet.Idx 2 → ℝ) :
    v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode 2) *ᵥ v)
      = a0 P R L * v none ^ 2
        + a1 P R L * (v (some (0, true)) ^ 2 + v (some (0, false)) ^ 2)
        + a2 P R L * (v (some (1, true)) ^ 2 + v (some (1, false)) ^ 2)
        + 2 * pp P R L * (v none * v (some (0, true)) + v none * v (some (0, false))
            + v (some (0, true)) * v (some (0, false)))
        + 2 * qq P R L * (v none * v (some (1, true)) + v none * v (some (1, false))
            + v (some (1, true)) * v (some (1, false)))
        + 2 * (2 * qq P R L - pp P R L) * (v (some (0, true)) * v (some (1, true))
            + v (some (0, false)) * v (some (1, false)))
        + 2 * ((pp P R L + 2 * qq P R L) / 3) * (v (some (0, true)) * v (some (1, false))
            + v (some (0, false)) * v (some (1, true))) := by
  obtain ⟨h1m1, h2m2, h12, h1m2⟩ := pairQ_two_entries hL P R
  have hinj := Cvs.Finite.SymmetricModeSet.mode_injective 2
  have hM : ∀ i j, Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode 2) i j
      = Cvs.Finite.ModeSumPairValues.pairQ P R L (Cvs.Finite.SymmetricModeSet.mode 2 i)
          (Cvs.Finite.SymmetricModeSet.mode 2 j) / 2 :=
    Cvs.Finite.TruncationQuadraticForm.M_apply hL P R hinj
  have hs := fun m n => Cvs.Finite.TruncationQuadraticForm.pairQ_symm hL P R m n
  have hnn := fun m n => Cvs.Finite.TruncationQuadraticForm.pairQ_neg_neg P R L m n
  -- every pair value that occurs, in the five parameters
  have v00 : Cvs.Finite.ModeSumPairValues.pairQ P R L 0 0 / 2 = a0 P R L := rfl
  have v11 : Cvs.Finite.ModeSumPairValues.pairQ P R L 1 1 / 2 = a1 P R L := rfl
  have v22 : Cvs.Finite.ModeSumPairValues.pairQ P R L 2 2 / 2 = a2 P R L := rfl
  have vm1m1 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-1) (-1) / 2 = a1 P R L := by rw [hnn]; rfl
  have vm2m2 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-2) (-2) / 2 = a2 P R L := by rw [hnn]; rfl
  have v01 : Cvs.Finite.ModeSumPairValues.pairQ P R L 0 1 / 2 = pp P R L := rfl
  have v10 : Cvs.Finite.ModeSumPairValues.pairQ P R L 1 0 / 2 = pp P R L := by rw [hs]; rfl
  have v0m1 : Cvs.Finite.ModeSumPairValues.pairQ P R L 0 (-1) / 2 = pp P R L := by
    have := hnn 0 1; simp only [neg_zero] at this; rw [this]; rfl
  have vm10 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-1) 0 / 2 = pp P R L := by rw [hs]; exact v0m1
  have v02 : Cvs.Finite.ModeSumPairValues.pairQ P R L 0 2 / 2 = qq P R L := rfl
  have v20 : Cvs.Finite.ModeSumPairValues.pairQ P R L 2 0 / 2 = qq P R L := by rw [hs]; rfl
  have v0m2 : Cvs.Finite.ModeSumPairValues.pairQ P R L 0 (-2) / 2 = qq P R L := by
    have := hnn 0 2; simp only [neg_zero] at this; rw [this]; rfl
  have vm20 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-2) 0 / 2 = qq P R L := by rw [hs]; exact v0m2
  have vm11 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-1) 1 / 2 = pp P R L := by rw [hs]; exact h1m1
  have vm22 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-2) 2 / 2 = qq P R L := by rw [hs]; exact h2m2
  have v21 : Cvs.Finite.ModeSumPairValues.pairQ P R L 2 1 / 2 = 2 * qq P R L - pp P R L := by rw [hs]; exact h12
  have vm1m2 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-1) (-2) / 2 = 2 * qq P R L - pp P R L := by
    rw [hnn]; exact h12
  have vm2m1 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-2) (-1) / 2 = 2 * qq P R L - pp P R L := by
    rw [hs]; exact vm1m2
  have vm12 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-1) 2 / 2 = (pp P R L + 2 * qq P R L) / 3 := by
    have := hnn 1 (-2); simp only [neg_neg] at this; rw [this]; exact h1m2
  have vm21 : Cvs.Finite.ModeSumPairValues.pairQ P R L 2 (-1) / 2 = (pp P R L + 2 * qq P R L) / 3 := by
    rw [hs]; exact vm12
  have v2m1 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-2) 1 / 2 = (pp P R L + 2 * qq P R L) / 3 := by
    rw [hs]; exact h1m2
  simp only [dotProduct, mulVec, Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fintype.sum_bool, hM]
  simp only [Cvs.Finite.SymmetricModeSet.mode, if_true, Bool.false_eq_true, if_false, Fin.val_zero,
    Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_add]
  norm_num only [v00, v11, v22, vm1m1, vm2m2, v01, v10, v0m1, vm10, v02, v20, v0m2, vm20, vm11, vm22,
    h1m1, h2m2, h12, v21, vm1m2, vm2m1, vm21, v2m1, vm12, h1m2]
  ring

end Cvs.Finite.TwoModeMatrixParameters
