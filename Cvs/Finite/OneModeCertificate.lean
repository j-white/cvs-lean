import Mathlib
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Limit.DiscreteSpine
import Cvs.WeilForm.Archimedean.ArchConstantRationalBounds
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.Zeta.Digamma.DigammaQuarterConstant

/-!
# The one-mode certificate reduces to four inequalities in three entries
On `Idx 1 = {0, +1, −1}` the CvS matrix has three distinct entries, `A = M(0,0)`, `B = M(1,1)` and
`C = M(0,1) = M(1,−1)` (the divided differences coincide because `bval` is odd). With the trial
`w = (1, s, s)` and a level `t`, `Cert P R L 1` follows from `A + 2Bs² + 2C(2s + s²) < t(1 + 2s²)`,
`t ≤ B − C`, `t(4s² + 2) ≤ 4s²A + 2B + 2C − 8sC` and `t ≤ A` (`cert_one`). Also: the archimedean
constant to `10⁻⁴`, from `γ`, `log 2`, `π` and `log π`.
-/

noncomputable section

open Real Matrix

namespace Cvs.Finite.OneModeCertificate

/-- **The archimedean constant between two rationals, `10⁻⁴` apart.** -/
theorem archSymbol_zero_bounds :
    (-5.37228 : ℝ) ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      ∧ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ (-5.37208 : ℝ) := by
  rw [Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.archSymbol_zero_eq]
  obtain ⟨hlp, hlp'⟩ := Cvs.Moments.log_pi_bounds
  have hg1 := Cvs.WeilForm.Archimedean.ArchConstantRationalBounds.gamma_upper
  have hg2 := Cvs.WeilForm.Archimedean.ArchConstantRationalBounds.gamma_lower
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  constructor <;> linarith

/-- The three entries of the one-mode matrix. -/
def eA (P R : ℕ) (L : ℝ) : ℝ := Cvs.Finite.ModeSumPairValues.pairQ P R L 0 0 / 2
def eB (P R : ℕ) (L : ℝ) : ℝ := Cvs.Finite.ModeSumPairValues.pairQ P R L 1 1 / 2
def eC (P R : ℕ) (L : ℝ) : ℝ := Cvs.Finite.ModeSumPairValues.pairQ P R L 0 1 / 2

/-- **The divided differences coincide**: `pairQ(1,−1) = pairQ(0,1)`. -/
theorem pairQ_one_neg_one {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    Cvs.Finite.ModeSumPairValues.pairQ P R L 1 (-1) = Cvs.Finite.ModeSumPairValues.pairQ P R L 0 1 := by
  have h1 := Cvs.Finite.PairFormDividedDifference.pairQ_off hL P R (m := 1) (n := -1) (by norm_num)
  have h2 := Cvs.Finite.PairFormDividedDifference.pairQ_off hL P R (m := 0) (n := 1) (by norm_num)
  have hb0 : Cvs.Finite.PairFormDividedDifference.bval P R L 0 = 0 := by
    have := Cvs.Finite.PairFormDividedDifference.bval_neg P R L 0
    simp only [neg_zero] at this
    linarith
  have hbm : Cvs.Finite.PairFormDividedDifference.bval P R L (-1) = -Cvs.Finite.PairFormDividedDifference.bval P R L 1 :=
    Cvs.Finite.PairFormDividedDifference.bval_neg P R L 1
  rw [hbm] at h1
  rw [hb0] at h2
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hL0 : L ≠ 0 := hL.ne'
  push_cast at h1 h2
  have e1 : Cvs.Finite.ModeSumPairValues.pairQ P R L 1 (-1)
      = 2 * ((Cvs.Finite.PairFormDividedDifference.bval P R L 1 - -Cvs.Finite.PairFormDividedDifference.bval P R L 1)
        / (2 * π * 1 / L - 2 * π * -1 / L)) := by linarith
  have e2 : Cvs.Finite.ModeSumPairValues.pairQ P R L 0 1
      = 2 * ((0 - Cvs.Finite.PairFormDividedDifference.bval P R L 1) / (2 * π * 0 / L - 2 * π * 1 / L)) := by
    linarith
  rw [e1, e2]
  field_simp
  ring

/-- **The one-mode matrix in its three entries.** -/
theorem quad_one {L : ℝ} (hL : 0 < L) (P R : ℕ) (v : Cvs.Finite.SymmetricModeSet.Idx 1 → ℝ) :
    v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode 1) *ᵥ v)
      = eA P R L * v none ^ 2 + eB P R L * (v (some (0, true)) ^ 2 + v (some (0, false)) ^ 2)
        + 2 * eC P R L * (v none * v (some (0, true)) + v none * v (some (0, false))
          + v (some (0, true)) * v (some (0, false))) := by
  have hinj := Cvs.Finite.SymmetricModeSet.mode_injective 1
  have hM : ∀ i j, Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode 1) i j
      = Cvs.Finite.ModeSumPairValues.pairQ P R L (Cvs.Finite.SymmetricModeSet.mode 1 i)
          (Cvs.Finite.SymmetricModeSet.mode 1 j) / 2 :=
    Cvs.Finite.TruncationQuadraticForm.M_apply hL P R hinj
  have hs10 : Cvs.Finite.ModeSumPairValues.pairQ P R L 1 0 = Cvs.Finite.ModeSumPairValues.pairQ P R L 0 1 :=
    Cvs.Finite.TruncationQuadraticForm.pairQ_symm hL P R 1 0
  have hsm0 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-1) 0 = Cvs.Finite.ModeSumPairValues.pairQ P R L 0 1 := by
    have := Cvs.Finite.TruncationQuadraticForm.pairQ_neg_neg P R L 1 0
    simp only [neg_zero] at this
    rw [this, hs10]
  have hs0m : Cvs.Finite.ModeSumPairValues.pairQ P R L 0 (-1) = Cvs.Finite.ModeSumPairValues.pairQ P R L 0 1 := by
    rw [Cvs.Finite.TruncationQuadraticForm.pairQ_symm hL P R 0 (-1), hsm0]
  have hmm : Cvs.Finite.ModeSumPairValues.pairQ P R L (-1) (-1) = Cvs.Finite.ModeSumPairValues.pairQ P R L 1 1 :=
    Cvs.Finite.TruncationQuadraticForm.pairQ_neg_neg P R L 1 1
  have hsm1 : Cvs.Finite.ModeSumPairValues.pairQ P R L (-1) 1 = Cvs.Finite.ModeSumPairValues.pairQ P R L 0 1 := by
    rw [Cvs.Finite.TruncationQuadraticForm.pairQ_symm hL P R (-1) 1, pairQ_one_neg_one hL]
  simp only [dotProduct, mulVec, Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_one,
    Fintype.sum_bool, hM]
  simp only [Cvs.Finite.SymmetricModeSet.mode, if_true, Bool.false_eq_true, if_false, Fin.val_zero,
    Nat.cast_zero, zero_add]
  norm_num only [hs10, hsm0, hs0m, hmm, hsm1, pairQ_one_neg_one hL]
  unfold eA eB eC
  ring

open Cvs.Finite.SymmetricModeSet in
/-- **The one-mode certificate from four inequalities in the three entries.** -/
theorem cert_one {L : ℝ} (hL : 0 < L) (P R : ℕ) {s t : ℝ}
    (h1 : eA P R L + 2 * eB P R L * s ^ 2 + 2 * eC P R L * (2 * s + s ^ 2) < t * (1 + 2 * s ^ 2))
    (h2 : t ≤ eB P R L - eC P R L)
    (h3 : t * (4 * s ^ 2 + 2) ≤ 4 * s ^ 2 * eA P R L + 2 * eB P R L + 2 * eC P R L - 8 * s * eC P R L)
    (h4 : t ≤ eA P R L) :
    Cvs.Limit.DiscreteSpine.Cert P R L 1 := by
  set w : Idx 1 → ℝ := fun i => match i with
    | none => 1
    | some _ => s with hw
  refine ⟨w, t, ?_, ?_, ?_, ?_⟩
  · rw [quad_one hL]
    have hww : w ⬝ᵥ w = 1 + 2 * s ^ 2 := by
      simp only [dotProduct, Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_one,
        Fintype.sum_bool, hw]
      ring
    rw [hww]
    simp only [hw]
    linarith
  · intro o ho
    have h0 : o none = 0 := by
      have := ho none; simp only [negI] at this; linarith
    have hm : o (some (0, false)) = -o (some (0, true)) := by
      have := ho (some (0, true)); simpa [negI] using this
    rw [quad_one hL]
    have hoo : o ⬝ᵥ o = o none ^ 2 + (o (some (0, true)) ^ 2 + o (some (0, false)) ^ 2) := by
      simp only [dotProduct, Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_one,
        Fintype.sum_bool]
      ring
    rw [hoo, h0, hm]
    nlinarith [sq_nonneg (o (some (0, true)))]
  · intro v hv hperp
    have hm : v (some (0, false)) = v (some (0, true)) := by
      have := hv (some (0, true)); simpa [negI] using this
    have hdot : v none + s * v (some (0, true)) + s * v (some (0, false)) = 0 := by
      have := hperp
      simp only [dotProduct, Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_one,
        Fintype.sum_bool, hw] at this
      linarith
    rw [hm] at hdot
    have hx : v none = -2 * s * v (some (0, true)) := by linarith
    rw [quad_one hL]
    have hvv : v ⬝ᵥ v = v none ^ 2 + (v (some (0, true)) ^ 2 + v (some (0, false)) ^ 2) := by
      simp only [dotProduct, Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_one,
        Fintype.sum_bool]
      ring
    rw [hvv, hm, hx]
    nlinarith [sq_nonneg (v (some (0, true)))]
  · have : Cvs.Finite.TruncationQuadraticForm.M P R L (mode 1) none none = eA P R L := by
      rw [Cvs.Finite.TruncationQuadraticForm.M_apply hL P R (mode_injective 1)]; rfl
    rw [this]; exact h4

end Cvs.Finite.OneModeCertificate
