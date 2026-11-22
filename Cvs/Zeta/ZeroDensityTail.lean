import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.LocalCountTransfer
import Cvs.Zeta.LocalZeroCount
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.WeightExponentialChord
import Cvs.Zeta.ZetaRightHalfPlaneBounds
import Cvs.Zeta.ZetaSeamStatement
import Cvs.Zeta.ZetaZeroWindows

/-!
# The density tail, as a number at the best rate

Every constant in the chain is now explicit: `zeta_growth_right` carries `A = 1, C = 20/3`,
`Cvs.Zeta.WeightExponentialChord` empties the low window, and what comes out is a tail with no existential in it.
RH.md §3.20 carries the arithmetic.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Finset Cvs.Zeta.Explicit.Venue

namespace Cvs.Zeta.ZeroDensityTail

/-- **The low window is empty.**  `Cvs.Zeta.WeightExponentialChord` puts every `ξ`-zero above height `6.24`, and
`(-4, 5]` is inside that. -/
theorem zerosIn_low_eq_empty : Cvs.Zeta.Base.zerosIn (-4) 5 = ∅ := by
  ext rho
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hz, hre0, hre1⟩, hlo, hhi⟩
  have hne1 : rho ≠ 1 := by
    intro h
    rw [h] at hre1
    simp at hre1
  have hxi : Cvs.Zeta.riemannXi rho = 0 :=
    (Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta hre0 hne1).mpr hz
  have h624 := Cvs.Zeta.WeightExponentialChord.abs_im_gt_of_riemannXi_eq_zero hxi
  rcases abs_cases rho.im with ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq] at h624 <;> linarith

/-- Hence the count there is zero. -/
theorem Ncount_low_eq_zero : Cvs.Zeta.Base.Ncount (-4) 5 = 0 := by
  rw [Cvs.Zeta.Base.Ncount, zerosIn_low_eq_empty, finsum_mem_empty]

/-- `log(0.95/0.84) ≥ 0.1157`, from `log x ≥ 1 − 1/x`. -/
theorem log_ratio_ge : (0.1157 : ℝ) ≤ Real.log (0.95 / 0.84) := by
  have h := Real.log_le_sub_one_of_pos (x := (0.84 : ℝ) / 0.95) (by norm_num)
  rw [show (0.84 : ℝ) / 0.95 = ((0.95 : ℝ) / 0.84)⁻¹ by norm_num, Real.log_inv] at h
  norm_num at h
  linarith

/-- `log 20 < 3`, since `e³ > 20.08`. -/
theorem log_twenty_lt : Real.log 20 < 3 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hcube : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h20 : (20 : ℝ) < Real.exp 3 := by
    rw [hcube]
    have hb : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) he.le 3
    have : (20 : ℝ) < (2.7182818283 : ℝ) ^ 3 := by norm_num
    linarith
  calc Real.log 20 < Real.log (Real.exp 3) := Real.log_lt_log (by norm_num) h20
    _ = 3 := Real.log_exp 3

/-- **The half-window constant is below `44`.** -/
theorem halfConst_le : ∀ t : ℝ, 4 ≤ |t| →
    Cvs.Zeta.Base.RvM.NhalfR t ≤ 44 * Real.log (|t| + 3) := by
  have hbase := Cvs.Zeta.Base.RvM.half_count_large_of (A := 1) (C := 20/3) (by norm_num)
    (fun s h1 h2 => Cvs.Zeta.Base.RvM.zeta_growth_right_at s h1 h2)
  intro t ht
  refine (hbase t ht).trans ?_
  have hlogt : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlr := log_ratio_ge
  have h20 : |Real.log (3 * (20/3 : ℝ))| = Real.log 20 := by
    rw [show (3 : ℝ) * (20/3) = 20 by norm_num]
    exact abs_of_nonneg (Real.log_nonneg (by norm_num))
  have hmax : max (1 : ℝ) 0 = 1 := by norm_num
  rw [h20, hmax]
  have hcoef : 1 / Real.log (0.95 / 0.84) * (Real.log 20 + 2 * 1) ≤ 44 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
    nlinarith [log_twenty_lt, hlr]
  exact mul_le_mul_of_nonneg_right hcoef hlogt

/-- **The local count constant is below `88`.** -/
theorem localCount_le : ∀ t : ℝ,
    (Cvs.Zeta.Base.Ncount t (t + 1) : ℝ) ≤ 88 * Real.log (|t| + 3) := by
  intro t
  refine (Cvs.Zeta.Base.RvM.zeta_local_zero_count_of halfConst_le t).trans ?_
  have hlogt : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hK : ((Cvs.Zeta.Base.Ncount (-4) 5 : ℕ) : ℝ) = 0 := by rw [Ncount_low_eq_zero]; norm_num
  rw [hK]
  refine mul_le_mul_of_nonneg_right ?_ hlogt
  rw [show (2 : ℝ) * 44 = 88 by norm_num]
  exact max_le (by norm_num) (max_le le_rfl (by norm_num))

/-- **The per-bucket count, as a number.** -/
theorem bucketCard_le_num (n : ℕ) (hn : 1 ≤ n) :
    ((completedZetaZeroBucketFinset n).card : ℝ) ≤ 352 * Real.log ((n : ℝ) + 3) := by
  have h := Cvs.Zeta.LocalCountTransfer.bucketCard_le_log_of (A₀ := 88) (by norm_num) localCount_le n hn
  rw [show (4 : ℝ) * 88 = 352 by norm_num] at h
  exact h

end Cvs.Zeta.ZeroDensityTail
