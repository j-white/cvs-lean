import Mathlib
import Cvs.Prolate.GevreyTailCircle
import Cvs.Route.OneCellChebyshevInequality
import Cvs.Route.OneCellCriterion
import Cvs.Route.OneCellLaplaceTransform
import Cvs.Upstream.LandauLaplaceNonneg
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.DivisorHyperbolaFactorisation
import Cvs.WeilForm.MaskedShift.AtomNormLaw
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.WeilForm.MaskedShift.PrimePowerRotationNumber
import Cvs.WeilForm.PrimeOperatorPathLawDeficit
import Cvs.WeilForm.ShiftedDirichletSchurVacuum
import Cvs.WeilForm.WholeDomainUnification
import Cvs.WeilForm.WindowVacuumRieszMean
import Cvs.Zeta.AllZerosOnLine
import Cvs.Zeta.DivisorDiscrepancyAdjointZeta
import Cvs.Zeta.DivisorDiscrepancyHyperbola
import Cvs.Zeta.EulerMascheroniSqueeze
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.PartialSumHalfEulerMaclaurin
import Cvs.Zeta.PsihalfIntegerInterpolation
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiVertical
import Cvs.Zeta.ZeroFreeHeightFive

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Exact Wing Cancellation of `log k` in `partialSumHalf log` and Uniform `O(1)` Norm Bound on `Op c d_{-2γ} vac`

Rewrites `partialSumHalf log k = ∑_{j=1}^{k-1} logStep j * (partialSumHalf ζ k - partialSumHalf ζ j)` to cancel the
`log k` error identically, proving `|partialSumHalf (divisorDiscrepancy (-2 * γ)) k| ≤ 23` and `‖Op c d_{-2γ} vac‖ ≤ 23`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.Zeta.WingCancellationLog
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
open Cvs.Route.OneCellChebyshevInequality (Psihalf S0 trivTail M)
open Cvs.WeilForm.WindowVacuumRieszMean (vac)
open Cvs.WeilForm.DirichletSchurFactorisation
open Cvs.WeilForm.ShiftedDirichletSchurVacuum
open Cvs.WeilForm.DivisorHyperbolaFactorisation
open Cvs.WeilForm.WholeDomainUnification
open Cvs.Zeta.PartialSumHalfEulerMaclaurin
open Cvs.Zeta.DivisorDiscrepancyHyperbola
open Cvs.Zeta.DivisorDiscrepancyAdjointZeta
open Cvs.Zeta.PsihalfIntegerInterpolation
open Cvs.Zeta.EulerMascheroniSqueeze

/-! ### 1. Exact Pre-Cauchy-Schwarz Floor-Convolution Formula for `M c - Psihalf c` -/

/-! ### 2. Exact Wing Cancellation of `log k` in `partialSumHalf log k` -/

/-- **Wing-Difference Identity for `partialSumHalf log k`**: for `1 < k`,
`partialSumHalf log k = ∑_{j=1}^{k-1} logStep j * (partialSumHalf ζ k - partialSumHalf ζ j)`.
This cancels any constant offset in `partialSumHalf ζ` identically. -/
theorem partialSumHalf_log_eq_sum_logStep_mul_sub {k : ℕ} (hk : 1 < k) :
    partialSumHalf ArithmeticFunction.log k
      = ∑ j ∈ Finset.Ico 1 k,
          logStep j *
            (partialSumHalf (ζ : ArithmeticFunction ℝ) k
              - partialSumHalf (ζ : ArithmeticFunction ℝ) j) := by
  rw [partialSumHalf_log_eq_log_mul_zeta_sub_discretePoleRiesz hk,
    discretePoleRiesz_eq_sum_partialSumHalf_zeta hk,
    ← sum_Ico_one_logStep hk.le, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- Difference of `partialSumHalf ζ k - partialSumHalf ζ j` as the wing sum over `Icc (j + 1) k`. -/
theorem partialSumHalf_zeta_sub_eq_wing_sum {j k : ℕ} (hjk : j ≤ k) :
    partialSumHalf (ζ : ArithmeticFunction ℝ) k
        - partialSumHalf (ζ : ArithmeticFunction ℝ) j
      = ∑ n ∈ Finset.Icc (j + 1) k, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [partialSumHalf_zeta_eq_sum, partialSumHalf_zeta_eq_sum]
  have hdisj : Disjoint (Finset.Icc 1 j) (Finset.Icc (j + 1) k) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2
    omega
  have hunion : Finset.Icc 1 k = Finset.Icc 1 j ∪ Finset.Icc (j + 1) k := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [hunion, Finset.sum_union hdisj, add_sub_cancel_left]

/-- For `1 ≤ j`, `2 * (√(j + 1) - √j) * logStep j ≤ 4 * ((√j)⁻¹ - (√(j + 1))⁻¹)`. -/
theorem two_mul_sqrt_succ_sub_sqrt_mul_logStep_le {j : ℕ} (hj : 1 ≤ j) :
    2 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) * logStep j
      ≤ 4 * ((Real.sqrt (j : ℝ))⁻¹ - (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (0 : ℝ) < (j + 1 : ℕ) := by exact_mod_cast Nat.succ_pos j
  have hsq_j : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
  have hsq_j1 : 0 < Real.sqrt ((j + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hj1
  have hdiff : 0 ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ j))
  have hstep : logStep j ≤ (j : ℝ)⁻¹ := logStep_le_inv hj
  have h1 :
      2 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) * logStep j
        ≤ 2 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) * (j : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  have hsq_le : Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (j : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    rw [Nat.cast_add, Nat.cast_one]
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hinv_le : (j : ℝ)⁻¹ ≤ 2 / (Real.sqrt (j : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ)) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hj0 (by positivity)]
    have hmul : Real.sqrt (j : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ 2 * (j : ℝ) := by
      calc Real.sqrt (j : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ)
          ≤ Real.sqrt (j : ℝ) * (2 * Real.sqrt (j : ℝ)) :=
            mul_le_mul_of_nonneg_left hsq_le hsq_j.le
        _ = 2 * (Real.sqrt (j : ℝ) * Real.sqrt (j : ℝ)) := by ring
        _ = 2 * (j : ℝ) := by rw [Real.mul_self_sqrt hj0.le]
    linarith
  have h2 :
      2 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) * (j : ℝ)⁻¹
        ≤ 2 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ))
            * (2 / (Real.sqrt (j : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left hinv_le (by positivity)
  have h3 :
      2 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ))
          * (2 / (Real.sqrt (j : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ)))
        = 4 * ((Real.sqrt (j : ℝ))⁻¹ - (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹) := by
    have hne1 : Real.sqrt (j : ℝ) ≠ 0 := hsq_j.ne'
    have hne2 : Real.sqrt ((j + 1 : ℕ) : ℝ) ≠ 0 := hsq_j1.ne'
    field_simp
    ring
  linarith

/-- Telescoping sum of `4 * ((√j)⁻¹ - (√(j + 1))⁻¹)` over `j ∈ Finset.Ico 1 k` is at most `4`. -/
theorem sum_Ico_four_mul_inv_sqrt_sub_le_four {k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ Finset.Ico 1 k,
        4 * ((Real.sqrt (j : ℝ))⁻¹ - (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹)
      ≤ 4 := by
  have htel :
      ∑ j ∈ Finset.Ico 1 k,
          4 * ((Real.sqrt (j : ℝ))⁻¹ - (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹)
        = -4 * ∑ j ∈ Finset.Ico 1 k,
            ((Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (j : ℝ))⁻¹) := by
    rw [Finset.mul_sum, ← Finset.sum_congr rfl]
    intro j _
    ring
  rw [htel, Finset.sum_Ico_sub (fun j : ℕ => (Real.sqrt (j : ℝ))⁻¹) hk]
  simp only [Nat.cast_one, Real.sqrt_one, inv_one]
  have hpos : 0 ≤ (Real.sqrt (k : ℝ))⁻¹ := by positivity
  linarith

/-- Sum of `2 * √(j + 1) * logStep j` over `j ∈ Finset.Ico 1 k` is at most `4 * √k` (`1 ≤ k`). -/
theorem sum_Ico_two_mul_sqrt_succ_mul_logStep_le {k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ Finset.Ico 1 k, 2 * Real.sqrt ((j + 1 : ℕ) : ℝ) * logStep j
      ≤ 4 * Real.sqrt (k : ℝ) := by
  have hle :
      ∑ j ∈ Finset.Ico 1 k, 2 * Real.sqrt ((j + 1 : ℕ) : ℝ) * logStep j
        ≤ ∑ j ∈ Finset.Ico 1 k,
            (4 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ))
              + 4 * ((Real.sqrt (j : ℝ))⁻¹ - (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have h1 := two_mul_sqrt_mul_logStep_le hj1
    have h2 := two_mul_sqrt_succ_sub_sqrt_mul_logStep_le hj1
    linarith
  rw [Finset.sum_add_distrib, sum_Ico_four_mul_sqrt_succ_sub_sqrt hk] at hle
  linarith [sum_Ico_four_mul_inv_sqrt_sub_le_four hk]

/-- Sum of `2 * √j * logStep j` over `j ∈ Finset.Ico 1 k` is at least `4 * √k - 8` (`1 ≤ k`). -/
theorem four_mul_sqrt_sub_eight_le_sum_Ico_two_mul_sqrt_mul_logStep {k : ℕ} (hk : 1 ≤ k) :
    4 * Real.sqrt (k : ℝ) - 8
      ≤ ∑ j ∈ Finset.Ico 1 k, 2 * Real.sqrt (j : ℝ) * logStep j := by
  have hle :
      ∑ j ∈ Finset.Ico 1 k,
          (4 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ))
            - 4 * ((Real.sqrt (j : ℝ))⁻¹ - (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹))
        ≤ ∑ j ∈ Finset.Ico 1 k, 2 * Real.sqrt (j : ℝ) * logStep j := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have h1 := four_mul_sqrt_succ_sub_sqrt_le_two_mul_sqrt_succ_mul_logStep hj1
    have h2 := two_mul_sqrt_succ_sub_sqrt_mul_logStep_le hj1
    linarith
  rw [Finset.sum_sub_distrib, sum_Ico_four_mul_sqrt_succ_sub_sqrt hk] at hle
  linarith [sum_Ico_four_mul_inv_sqrt_sub_le_four hk]

/-- **`O(1)`-Accurate Lower Bound on `partialSumHalf log k`** (with NO `-log k` error!):
for every `1 ≤ k`, `2 * √k * log k - 4 * √k ≤ partialSumHalf log k`. -/
theorem two_mul_sqrt_mul_log_sub_four_sqrt_le_partialSumHalf_log {k : ℕ} (hk : 1 ≤ k) :
    2 * Real.sqrt (k : ℝ) * Real.log (k : ℝ) - 4 * Real.sqrt (k : ℝ)
      ≤ partialSumHalf ArithmeticFunction.log k := by
  rcases eq_or_lt_of_le hk with rfl | hk1
  · simp [partialSumHalf_log_one]
  · rw [partialSumHalf_log_eq_sum_logStep_mul_sub hk1]
    have hwing :
        ∑ j ∈ Finset.Ico 1 k,
            logStep j * (2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt ((j + 1 : ℕ) : ℝ))
          ≤ ∑ j ∈ Finset.Ico 1 k,
              logStep j *
                (partialSumHalf (ζ : ArithmeticFunction ℝ) k
                  - partialSumHalf (ζ : ArithmeticFunction ℝ) j) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
      have hjk : j ≤ k := (Finset.mem_Ico.mp hj).2.le
      rw [partialSumHalf_zeta_sub_eq_wing_sum hjk]
      exact mul_le_mul_of_nonneg_left (two_mul_sqrt_succ_sub_le_wing_sum hjk) (logStep_nonneg hj1)
    have hsplit :
        ∑ j ∈ Finset.Ico 1 k,
            logStep j * (2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt ((j + 1 : ℕ) : ℝ))
          = 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.log (k : ℝ)
            - ∑ j ∈ Finset.Ico 1 k, 2 * Real.sqrt ((j + 1 : ℕ) : ℝ) * logStep j := by
      calc
        ∑ j ∈ Finset.Ico 1 k,
            logStep j * (2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt ((j + 1 : ℕ) : ℝ))
          = (∑ j ∈ Finset.Ico 1 k, logStep j) * (2 * Real.sqrt ((k + 1 : ℕ) : ℝ))
              - ∑ j ∈ Finset.Ico 1 k, 2 * Real.sqrt ((j + 1 : ℕ) : ℝ) * logStep j := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => by ring
        _ = 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.log (k : ℝ)
              - ∑ j ∈ Finset.Ico 1 k, 2 * Real.sqrt ((j + 1 : ℕ) : ℝ) * logStep j := by
            rw [sum_Ico_one_logStep hk, mul_comm]
    have hL : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
    have hsq : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
    have hmul : 2 * Real.sqrt (k : ℝ) * Real.log (k : ℝ)
        ≤ 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.log (k : ℝ) := by nlinarith
    have hsum := sum_Ico_two_mul_sqrt_succ_mul_logStep_le hk
    linarith

/-- **`O(1)`-Accurate Upper Bound on `partialSumHalf log k`** (with NO `+log k` error!):
for every `1 ≤ k`, `partialSumHalf log k ≤ 2 * √k * log k - 4 * √k + 8`. -/
theorem partialSumHalf_log_le_two_mul_sqrt_mul_log_sub_four_sqrt_add_eight {k : ℕ} (hk : 1 ≤ k) :
    partialSumHalf ArithmeticFunction.log k
      ≤ 2 * Real.sqrt (k : ℝ) * Real.log (k : ℝ) - 4 * Real.sqrt (k : ℝ) + 8 := by
  rcases eq_or_lt_of_le hk with rfl | hk1
  · simp [partialSumHalf_log_one]
    norm_num
  · rw [partialSumHalf_log_eq_sum_logStep_mul_sub hk1]
    have hwing :
        ∑ j ∈ Finset.Ico 1 k,
            logStep j *
              (partialSumHalf (ζ : ArithmeticFunction ℝ) k
                - partialSumHalf (ζ : ArithmeticFunction ℝ) j)
          ≤ ∑ j ∈ Finset.Ico 1 k,
              logStep j * (2 * Real.sqrt (k : ℝ) - 2 * Real.sqrt (j : ℝ)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
      have hjk : j ≤ k := (Finset.mem_Ico.mp hj).2.le
      rw [partialSumHalf_zeta_sub_eq_wing_sum hjk]
      exact mul_le_mul_of_nonneg_left (wing_sum_le_two_mul_sqrt_sub hjk) (logStep_nonneg hj1)
    have hsplit :
        ∑ j ∈ Finset.Ico 1 k,
            logStep j * (2 * Real.sqrt (k : ℝ) - 2 * Real.sqrt (j : ℝ))
          = 2 * Real.sqrt (k : ℝ) * Real.log (k : ℝ)
            - ∑ j ∈ Finset.Ico 1 k, 2 * Real.sqrt (j : ℝ) * logStep j := by
      calc
        ∑ j ∈ Finset.Ico 1 k,
            logStep j * (2 * Real.sqrt (k : ℝ) - 2 * Real.sqrt (j : ℝ))
          = (∑ j ∈ Finset.Ico 1 k, logStep j) * (2 * Real.sqrt (k : ℝ))
              - ∑ j ∈ Finset.Ico 1 k, 2 * Real.sqrt (j : ℝ) * logStep j := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => by ring
        _ = 2 * Real.sqrt (k : ℝ) * Real.log (k : ℝ)
              - ∑ j ∈ Finset.Ico 1 k, 2 * Real.sqrt (j : ℝ) * logStep j := by
            rw [sum_Ico_one_logStep hk, mul_comm]
    have hsum := four_mul_sqrt_sub_eight_le_sum_Ico_two_mul_sqrt_mul_logStep hk
    linarith

/-! ### 3. Complete `O(1)` Bound on `partialSumHalf (divisorDiscrepancy (-2 * γ)) k` and `‖Op c d_{-2γ} vac‖` -/

/-- **Uniform `O(1)` Upper Bound on `partialSumHalf (divisorDiscrepancy (-2 * eulerMascheroni)) k`**:
for every `1 ≤ k`, `partialSumHalf (divisorDiscrepancy (-2 * eulerMascheroni)) k ≤ 20`. -/
theorem partialSumHalf_divisorDiscrepancy_neg_two_eulerMascheroni_le_twenty {k : ℕ} (hk : 1 ≤ k) :
    partialSumHalf (divisorDiscrepancy (-2 * eulerMascheroni)) k ≤ 20 := by
  rw [partialSumHalf_divisorDiscrepancy]
  have htau := partialSumHalf_zeta_mul_zeta_le_harmonic hk
  have hlog := two_mul_sqrt_mul_log_sub_four_sqrt_le_partialSumHalf_log hk
  have hharm := four_sqrt_mul_harmonicSum_sub_half_log_le hk
  have hzeta := two_mul_sqrt_succ_sub_two_le_partialSumHalf_zeta hk
  have hsq_le : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
  have hnat := sqrt_sub_nat_sqrt_le_one k
  have hγ0 := eulerMascheroni_nonneg
  have hγ1 := eulerMascheroni_le_one
  nlinarith

/-- **Uniform `O(1)` Lower Bound on `partialSumHalf (divisorDiscrepancy (-2 * eulerMascheroni)) k`**:
for every `1 ≤ k`, `-19 ≤ partialSumHalf (divisorDiscrepancy (-2 * eulerMascheroni)) k`. -/
theorem neg_nineteen_le_partialSumHalf_divisorDiscrepancy_neg_two_eulerMascheroni
    {k : ℕ} (hk : 1 ≤ k) :
    -19 ≤ partialSumHalf (divisorDiscrepancy (-2 * eulerMascheroni)) k := by
  rw [partialSumHalf_divisorDiscrepancy]
  have htau := harmonic_le_partialSumHalf_zeta_mul_zeta hk
  have hlog := partialSumHalf_log_le_two_mul_sqrt_mul_log_sub_four_sqrt_add_eight hk
  have hharm := four_eulerMascheroni_mul_sqrt_sub_eight_le hk
  have hzeta := partialSumHalf_zeta_le_two_mul_sqrt_sub_one hk
  have hnat := zero_le_sqrt_sub_nat_sqrt k
  have hγ0 := eulerMascheroni_nonneg
  nlinarith

/-- **Uniform `O(1)` Absolute Bound on `partialSumHalf (divisorDiscrepancy (-2 * eulerMascheroni)) k`**:
for every `1 ≤ k`, `|partialSumHalf (divisorDiscrepancy (-2 * eulerMascheroni)) k| ≤ 20`. -/
theorem abs_partialSumHalf_divisorDiscrepancy_neg_two_eulerMascheroni_le_twenty
    {k : ℕ} (hk : 1 ≤ k) :
    |partialSumHalf (divisorDiscrepancy (-2 * eulerMascheroni)) k| ≤ 20 := by
  have hlow := neg_nineteen_le_partialSumHalf_divisorDiscrepancy_neg_two_eulerMascheroni hk
  have hup := partialSumHalf_divisorDiscrepancy_neg_two_eulerMascheroni_le_twenty hk
  exact abs_le.mpr ⟨by linarith, hup⟩

/-- **Uniform `O(1)` Norm Bound on `Op c (divisorDiscrepancy (-2 * eulerMascheroni)) vac`**:
for every `1 < c`, `‖Op c (divisorDiscrepancy (-2 * eulerMascheroni)) vac‖ ≤ 20` (independent of `c`!). -/
theorem norm_Op_divisorDiscrepancy_neg_two_eulerMascheroni_vac_le_twenty {c : ℕ} (hc : 1 < c) :
    ‖Op c (divisorDiscrepancy (-2 * eulerMascheroni)) vac‖ ≤ 20 := by
  refine norm_Op_vac_le_of_partialSumHalf_le hc
    (divisorDiscrepancy (-2 * eulerMascheroni)) (by norm_num) fun k hk => ?_
  exact abs_partialSumHalf_divisorDiscrepancy_neg_two_eulerMascheroni_le_twenty
    (Finset.mem_Ico.mp hk).1

/-! ### 4. Truncated-Möbius Sieve Eliminator `b_M = a * truncMoebius M` on `L²(𝕋)` -/

/-- The truncated Möbius arithmetic function `μ_{≤ M}(n) = μ(n)` for `n ≤ M`, `0` for `n > M`. -/
def truncMoebius (M : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ M then (μ n : ℝ) else 0, by simp⟩

/-- Pointwise evaluation of `truncMoebius M n`. -/
theorem truncMoebius_apply (M n : ℕ) :
    truncMoebius M n = if n ≤ M then (μ n : ℝ) else 0 := rfl

/-- **Exact Sieve Identity for `truncMoebius M * ζ`**: for all `n ≤ M`,
`(truncMoebius M * ζ) n = 1 n`. -/
theorem truncMoebius_mul_zeta_apply_of_le {M n : ℕ} (hn : n ≤ M) :
    (truncMoebius M * (ζ : ArithmeticFunction ℝ)) n = (1 : ArithmeticFunction ℝ) n := by
  rw [← ArithmeticFunction.coe_moebius_mul_coe_zeta,
    ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp_eq := Nat.mem_divisorsAntidiagonal.mp hp
  have hd_le : p.1 ≤ M := by
    have hd_n : p.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hp_eq.2) ⟨p.2, hp_eq.1.symm⟩
    exact hd_n.trans hn
  simp [truncMoebius_apply, hd_le]

/-! ### 5. The `O(k^{-1/2})` Squeeze for `zetaHalfConst` (`ζ(1/2)`) and Exact `log c` Coefficient of `smoothPoleRem` -/

/-- The monotone lower sequence `partialSumHalf ζ k - 2 * √(k + 1)` converging to `ζ(1/2)`. -/
def lowerZetaConstSeq (k : ℕ) : ℝ :=
  partialSumHalf (ζ : ArithmeticFunction ℝ) k - 2 * Real.sqrt ((k + 1 : ℕ) : ℝ)

/-- The antitone upper sequence `partialSumHalf ζ k - 2 * √k` converging to `ζ(1/2)`. -/
def upperZetaConstSeq (k : ℕ) : ℝ :=
  partialSumHalf (ζ : ArithmeticFunction ℝ) k - 2 * Real.sqrt (k : ℝ)

/-- Exact gap `upperZetaConstSeq k - lowerZetaConstSeq k = 2 * (√(k + 1) - √k)`. -/
theorem upperZetaConstSeq_sub_lower (k : ℕ) :
    upperZetaConstSeq k - lowerZetaConstSeq k
      = 2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) := by
  unfold upperZetaConstSeq lowerZetaConstSeq
  ring

/-- Step identity for `partialSumHalf ζ (k + 1)`. -/
theorem partialSumHalf_zeta_succ (k : ℕ) :
    partialSumHalf (ζ : ArithmeticFunction ℝ) (k + 1)
      = partialSumHalf (ζ : ArithmeticFunction ℝ) k + ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [partialSumHalf_zeta_eq_sum, partialSumHalf_zeta_eq_sum]
  have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp), add_comm]

/-- `lowerZetaConstSeq` is monotonically increasing on `ℕ`. -/
theorem lowerZetaConstSeq_mono : Monotone lowerZetaConstSeq := by
  refine monotone_nat_of_le_succ fun k => ?_
  unfold lowerZetaConstSeq
  rw [partialSumHalf_zeta_succ]
  have h := two_mul_sqrt_succ_sub_sqrt_le_rpow_neg_half (Nat.succ_pos k)
  linarith

/-- `upperZetaConstSeq` is antitone on `ℕ`. -/
theorem upperZetaConstSeq_anti : Antitone upperZetaConstSeq := by
  refine antitone_nat_of_succ_le fun k => ?_
  unfold upperZetaConstSeq
  rw [partialSumHalf_zeta_succ]
  have h := rpow_neg_half_le_two_mul_sqrt_sub_sqrt_pred (Nat.le_add_left 1 k)
  simp only [Nat.add_sub_cancel] at h
  linarith

/-- Every term of `lowerZetaConstSeq` is bounded above by every term of `upperZetaConstSeq`. -/
theorem lowerZetaConstSeq_le_upperZetaConstSeq (j k : ℕ) :
    lowerZetaConstSeq j ≤ upperZetaConstSeq k := by
  have h1 : lowerZetaConstSeq j ≤ lowerZetaConstSeq (max j k) :=
    lowerZetaConstSeq_mono (le_max_left j k)
  have h2 : lowerZetaConstSeq (max j k) ≤ upperZetaConstSeq (max j k) := by
    have hgap := upperZetaConstSeq_sub_lower (max j k)
    have hsq : Real.sqrt ((max j k : ℕ) : ℝ) ≤ Real.sqrt ((max j k + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (max j k))
    linarith
  have h3 : upperZetaConstSeq (max j k) ≤ upperZetaConstSeq k :=
    upperZetaConstSeq_anti (le_max_right j k)
  exact h1.trans (h2.trans h3)

/-- `lowerZetaConstSeq` is bounded above. -/
theorem bddAbove_lowerZetaConstSeq : BddAbove (Set.range lowerZetaConstSeq) := by
  refine ⟨upperZetaConstSeq 1, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact lowerZetaConstSeq_le_upperZetaConstSeq j 1

/-- The Dirichlet zeta constant `ζ(1/2) = sup_k (partialSumHalf ζ k - 2 * √(k + 1))`. -/
def zetaHalfConst : ℝ :=
  ⨆ k : ℕ, lowerZetaConstSeq k

/-- For every `k : ℕ`, `lowerZetaConstSeq k ≤ zetaHalfConst`. -/
theorem lowerZetaConstSeq_le_zetaHalfConst (k : ℕ) :
    lowerZetaConstSeq k ≤ zetaHalfConst :=
  le_ciSup bddAbove_lowerZetaConstSeq k

/-- For every `k : ℕ`, `zetaHalfConst ≤ upperZetaConstSeq k`. -/
theorem zetaHalfConst_le_upperZetaConstSeq (k : ℕ) :
    zetaHalfConst ≤ upperZetaConstSeq k :=
  ciSup_le fun j => lowerZetaConstSeq_le_upperZetaConstSeq j k

/-- **Two-Sided `O(k^{-1/2})` Approximation of `partialSumHalf ζ k` by `2 * √k + zetaHalfConst`**:
for every `k : ℕ`, `2 * √k + zetaHalfConst ≤ partialSumHalf ζ k ≤ 2 * √(k + 1) + zetaHalfConst`. -/
theorem two_mul_sqrt_add_zetaHalfConst_le_partialSumHalf_zeta (k : ℕ) :
    2 * Real.sqrt (k : ℝ) + zetaHalfConst ≤ partialSumHalf (ζ : ArithmeticFunction ℝ) k := by
  have h := zetaHalfConst_le_upperZetaConstSeq k
  unfold upperZetaConstSeq at h
  linarith

theorem partialSumHalf_zeta_le_two_mul_sqrt_succ_add_zetaHalfConst (k : ℕ) :
    partialSumHalf (ζ : ArithmeticFunction ℝ) k
      ≤ 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) + zetaHalfConst := by
  have h := lowerZetaConstSeq_le_zetaHalfConst k
  unfold lowerZetaConstSeq at h
  linarith

/-- **`O(1)`-Accurate Upper Bound on `discretePoleRiesz c` with Exact `zetaHalfConst * log c` Term**:
for `1 < c`, `discretePoleRiesz c ≤ 4 * √c + zetaHalfConst * log c`. -/
theorem discretePoleRiesz_le_four_mul_sqrt_add_zetaHalfConst_mul_log {c : ℕ} (hc : 1 < c) :
    discretePoleRiesz c ≤ 4 * Real.sqrt (c : ℝ) + zetaHalfConst * Real.log (c : ℝ) := by
  rw [discretePoleRiesz_eq_sum_partialSumHalf_zeta hc]
  have hle :
      ∑ k ∈ Finset.Ico 1 c, logStep k * partialSumHalf (ζ : ArithmeticFunction ℝ) k
        ≤ ∑ k ∈ Finset.Ico 1 c,
            (2 * Real.sqrt ((k + 1 : ℕ) : ℝ) * logStep k + zetaHalfConst * logStep k) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hstep : 0 ≤ logStep k := logStep_nonneg hk1
    have hz := partialSumHalf_zeta_le_two_mul_sqrt_succ_add_zetaHalfConst k
    nlinarith
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_Ico_one_logStep hc.le] at hle
  linarith [sum_Ico_two_mul_sqrt_succ_mul_logStep_le hc.le]

/-! ### 6. Universal Real-to-Integer Smooth Pole Lower Bound and Master Real-Variable Inequality -/

/-- `archSymbol 0 ≤ 0` (`archSymbol 0 ≤ -5.2948` by `Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.archSymbol_zero_bounds`). -/
theorem archSymbol_zero_nonpos : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ 0 := by
  linarith [Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.archSymbol_zero_bounds.2]

/-- For every real `1 < x`, `4 * (√⌈x⌉₊ - √x) ≤ 2`. -/
theorem four_mul_sqrt_ceil_sub_sqrt_le_two {x : ℝ} (hx : 1 < x) :
    4 * (Real.sqrt (⌈x⌉₊ : ℝ) - Real.sqrt x) ≤ 2 := by
  have hx0 : 0 < x := by linarith
  have hxc : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceil_lt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have h1 := sqrt_sub_sqrt_le_div_two_sqrt hx0 hxc
  have hsx : 1 ≤ Real.sqrt x := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hx.le
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith

/-- **Universal Real-to-Integer Smooth Pole Lower Bound (`x > 1`)**:
since `archSymbol 0 ≤ 0`, `trivTail x ≤ S0 - 4`, and `4 * (√⌈x⌉₊ - √x) ≤ 2`,
`smoothPoleRem ⌈x⌉₊ α - (M ⌈x⌉₊ - M x) ≥ (archSymbol 0 / 2 - zetaHalfConst - α) * log ⌈x⌉₊ - 6`. -/
theorem smoothPoleRem_ceil_sub_M_step_ge {x : ℝ} (hx : 1 < x) (α : ℝ) :
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst - α) * Real.log (⌈x⌉₊ : ℝ) - 6
      ≤ smoothPoleRem ⌈x⌉₊ α - (M (⌈x⌉₊ : ℝ) - M x) := by
  have hx0 : 0 < x := by linarith
  have hc : 1 < ⌈x⌉₊ := one_lt_ceil_of_one_lt hx
  have htriv := trivTail_le_S0_sub_four hx.le
  have hdisc := discretePoleRiesz_le_four_mul_sqrt_add_zetaHalfConst_mul_log hc
  have hsq := four_mul_sqrt_ceil_sub_sqrt_le_two hx
  have hlog : Real.log x ≤ Real.log (⌈x⌉₊ : ℝ) := Real.log_le_log hx0 (Nat.le_ceil x)
  have harch : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * Real.log (⌈x⌉₊ : ℝ) ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * Real.log x := by
    have := archSymbol_zero_nonpos
    nlinarith
  unfold smoothPoleRem M
  linarith

/-- **Real-Variable Master Smooth Arithmetic Projection Lower Bound on `M x - Psihalf x`**:
for every real `1 < x`, `α : ℝ`, and `b : ArithmeticFunction ℝ`. -/
theorem M_sub_Psihalf_real_ge_master {x : ℝ} (hx : 1 < x)
    (α : ℝ) (b : ArithmeticFunction ℝ) :
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst - α) * Real.log (⌈x⌉₊ : ℝ) - 6
        + (∑ k ∈ Finset.Ico 1 ⌈x⌉₊, logStep k * partialSumHalf b k)
        - Real.log (⌈x⌉₊ : ℝ)
          * ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖
          * ‖Op ⌈x⌉₊ (divisorDiscrepancy α - b * (ζ : ArithmeticFunction ℝ)) vac‖
      ≤ M x - Psihalf x := by
  have hc : 1 < ⌈x⌉₊ := one_lt_ceil_of_one_lt hx
  have hL : 0 ≤ Real.log (⌈x⌉₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hc.le)
  have hid := M_sub_Psihalf_eq_smoothPoleRem_add_divisor_pairing hc α
  rw [inner_Op_moebius_eq_inner_add_rem hc vac
    (ContinuousLinearMap.adjoint (Op ⌈x⌉₊ (divisorDiscrepancy α)) vac)
    (ContinuousLinearMap.adjoint (Op ⌈x⌉₊ b) vac),
    adj_Op_sub_adj_Op_zeta_apply_adj_Op hc] at hid
  have hvac :
      ⟪vac, ContinuousLinearMap.adjoint (Op ⌈x⌉₊ b) vac⟫_ℝ * Real.log (⌈x⌉₊ : ℝ)
        = ∑ k ∈ Finset.Ico 1 ⌈x⌉₊, logStep k * partialSumHalf b k := by
    rw [ContinuousLinearMap.adjoint_inner_right, mul_comm,
      log_mul_inner_Op_vac_vac_eq_sum_partialSumHalf hc b]
  have hcs :
      -⟪Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac,
          ContinuousLinearMap.adjoint
            (Op ⌈x⌉₊ (divisorDiscrepancy α - b * (ζ : ArithmeticFunction ℝ))) vac⟫_ℝ
        ≤ ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖
          * ‖Op ⌈x⌉₊ (divisorDiscrepancy α - b * (ζ : ArithmeticFunction ℝ)) vac‖ := by
    rw [← inner_neg_left, ← norm_adj_Op_vac_eq hc (divisorDiscrepancy α - b * (ζ : ArithmeticFunction ℝ))]
    exact (real_inner_le_norm _ _).trans (by rw [norm_neg])
  have hmul := mul_le_mul_of_nonneg_left hcs hL
  have hstep := smoothPoleRem_ceil_sub_M_step_ge hx α
  have hinterp := M_sub_Psihalf_ge_ceil_sub_interp hx
  linarith

/-! ### 7. Exact `√c` Hyperbola Reflection via `truncMoebius (Nat.sqrt c)` -/

/-! ### 8. Landau Shift Criterion: Absorbing All `O(log x) + O(1)` Remainder Terms -/

/-- The linearly shifted one-cell function `G(L) + A * L + B`, whose Laplace transform adds
only `A / z² + B / z` (holomorphic on `{Re z > 0}`). -/
def GShift (A B L : ℝ) : ℝ :=
  Cvs.Route.OneCellLaplaceTransform.G L + A * L + B

/-- `(G L + A * L + B) * exp (-(s * L))` is integrable on `(0, ∞)` for every `s > 1 / 2`. -/
theorem integrableOn_GShift_mul_exp (A B : ℝ) {s : ℝ} (hs : 1 / 2 < s) :
    IntegrableOn (fun L => GShift A B L * Real.exp (-(s * L))) (Ioi 0) := by
  have hs0 : 0 < s := by linarith
  have hG := Cvs.Route.OneCellCriterion.integrableOn_G_mul_exp hs
  have hA : IntegrableOn (fun L => A * ((L - 0) * Real.exp (-(s * L)))) (Ioi 0) :=
    (Cvs.Route.OneCellLaplaceTransform.integrableOn_ramp (c := 0) hs0).const_mul A
  have hB : IntegrableOn (fun L => B * Real.exp (-s * L)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0).const_mul B
  have hfun :
      (fun L => GShift A B L * Real.exp (-(s * L)))
        = fun L =>
            Cvs.Route.OneCellLaplaceTransform.G L * Real.exp (-(s * L))
              + A * ((L - 0) * Real.exp (-(s * L)))
              + B * Real.exp (-s * L) := by
    funext L
    unfold GShift
    rw [show -s * L = -(s * L) by ring]
    ring
  rw [hfun]
  exact (hG.add hA).add hB

/-- `GShift A B` is a.e. strongly measurable on `(0, ∞)`. -/
theorem aestronglyMeasurable_GShift (A B : ℝ) :
    AEStronglyMeasurable (GShift A B) (volume.restrict (Ioi 0)) := by
  have h := (integrableOn_GShift_mul_exp A B (s := 1) (by norm_num)).aestronglyMeasurable
  have h2 := h.mul
    (Continuous.aestronglyMeasurable (f := fun L : ℝ => Real.exp (1 * L)) (by fun_prop))
  refine h2.congr (ae_of_all _ fun L => ?_)
  show GShift A B L * Real.exp (-(1 * L)) * Real.exp (1 * L) = GShift A B L
  rw [mul_assoc, ← Real.exp_add]
  simp

/-- The Laplace transform of `GShift A B` converges above `1 / 2`. -/
theorem convAbove_GShift_half (A B : ℝ) : Cvs.Upstream.LandauLaplaceNonneg.ConvAbove (GShift A B) (1 / 2) :=
  fun _ hτ => integrableOn_GShift_mul_exp A B hτ

/-- On the real ray `s > 1 / 2`, `lap (GShift A B) s = lap G s + A / s² + B / s`. -/
theorem lap_GShift_real (A B : ℝ) {s : ℝ} (hs : 1 / 2 < s) :
    Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B) (s : ℂ)
      = Cvs.Upstream.LandauLaplaceNonneg.lap Cvs.Route.OneCellLaplaceTransform.G (s : ℂ) + (A : ℂ) / (s : ℂ) ^ 2 + (B : ℂ) / (s : ℂ) := by
  have hs0 : 0 < s := by linarith
  have hG := Cvs.Route.OneCellCriterion.integrableOn_G_mul_exp hs
  have hA : IntegrableOn (fun L => A * ((L - 0) * Real.exp (-(s * L)))) (Ioi 0) :=
    (Cvs.Route.OneCellLaplaceTransform.integrableOn_ramp (c := 0) hs0).const_mul A
  have hB : IntegrableOn (fun L => B * Real.exp (-s * L)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0).const_mul B
  have h1 :
      Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B) (s : ℂ)
        = ((∫ L in Ioi (0 : ℝ), GShift A B L * Real.exp (-(s * L)) : ℝ) : ℂ) := by
    unfold Cvs.Upstream.LandauLaplaceNonneg.lap
    have hfun :
        (fun L : ℝ => (GShift A B L : ℂ) * Complex.exp (-((s : ℂ) * L)))
          = fun L => ((GShift A B L * Real.exp (-(s * L)) : ℝ) : ℂ) := by
      funext L; push_cast; ring_nf
    rw [hfun, integral_complex_ofReal]
  have h2 :
      Cvs.Upstream.LandauLaplaceNonneg.lap Cvs.Route.OneCellLaplaceTransform.G (s : ℂ)
        = ((∫ L in Ioi (0 : ℝ), Cvs.Route.OneCellLaplaceTransform.G L * Real.exp (-(s * L)) : ℝ) : ℂ) := by
    unfold Cvs.Upstream.LandauLaplaceNonneg.lap
    have hfun :
        (fun L : ℝ => (Cvs.Route.OneCellLaplaceTransform.G L : ℂ) * Complex.exp (-((s : ℂ) * L)))
          = fun L => ((Cvs.Route.OneCellLaplaceTransform.G L * Real.exp (-(s * L)) : ℝ) : ℂ) := by
      funext L; push_cast; ring_nf
    rw [hfun, integral_complex_ofReal]
  have hsplit :
      (fun L => GShift A B L * Real.exp (-(s * L)))
        = fun L =>
            (Cvs.Route.OneCellLaplaceTransform.G L * Real.exp (-(s * L))
              + A * ((L - 0) * Real.exp (-(s * L))))
              + B * Real.exp (-s * L) := by
    funext L
    unfold GShift
    rw [show -s * L = -(s * L) by ring]
    ring
  have hGA :
      IntegrableOn
        (fun L => Cvs.Route.OneCellLaplaceTransform.G L * Real.exp (-(s * L)) + A * ((L - 0) * Real.exp (-(s * L))))
        (Ioi 0) :=
    hG.add hA
  have hint_eq :
      (∫ L in Ioi (0 : ℝ), GShift A B L * Real.exp (-(s * L)))
        = (∫ L in Ioi (0 : ℝ), Cvs.Route.OneCellLaplaceTransform.G L * Real.exp (-(s * L)))
          + A / s ^ 2 + B / s := by
    rw [hsplit, integral_add hGA hB, integral_add hG hA,
      integral_const_mul, integral_const_mul,
      Cvs.Route.OneCellLaplaceTransform.laplace_ramp hs0, Cvs.Route.OneCellLaplaceTransform.laplace_exp (by linarith : -s < 0)]
    simp only [mul_zero, neg_zero, Real.exp_zero]
    field_simp
  rw [h1, h2, hint_eq]
  push_cast
  ring

/-- Real-ray identity for `GShift A B`: `deriv φ s = φ s * ((lap (GShift A B) s * s² - A - B * s) / 2)`. -/
theorem real_identity_GShift (A B : ℝ) {s : ℝ} (hs : 1 / 2 < s) :
    deriv Cvs.Route.OneCellCriterion.φ (s : ℂ)
      = Cvs.Route.OneCellCriterion.φ (s : ℂ)
        * ((Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B) (s : ℂ) * (s : ℂ) ^ 2 - (A : ℂ) - (B : ℂ) * (s : ℂ)) / 2) := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by linarith)
  rw [Cvs.Route.OneCellCriterion.real_identity hs, lap_GShift_real A B hs]
  congr 1
  field_simp
  ring

/-- Analytic continuation of the `GShift` differential identity to any half-plane `{Re z > σ}` of convergence. -/
theorem deriv_φ_eq_GShift {A B : ℝ} (hG : ∀ L, 0 < L → 0 ≤ GShift A B L)
    {σ : ℝ} (hσ : Cvs.Upstream.LandauLaplaceNonneg.ConvAbove (GShift A B) σ) {z : ℂ} (hz : σ < z.re) :
    deriv Cvs.Route.OneCellCriterion.φ z
      = Cvs.Route.OneCellCriterion.φ z * ((Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B) z * z ^ 2 - (A : ℂ) - (B : ℂ) * z) / 2) := by
  set U : Set ℂ := {z | σ < z.re}
  have hUo : IsOpen U := Cvs.Upstream.LandauLaplaceNonneg.isOpen_halfPlane σ
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt σ).isPreconnected
  have hlap : AnalyticOnNhd ℂ (Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B)) U :=
    (Cvs.Upstream.LandauLaplaceNonneg.differentiableOn_lap hG (aestronglyMeasurable_GShift A B) hσ).analyticOnNhd hUo
  have hf : AnalyticOnNhd ℂ (deriv Cvs.Route.OneCellCriterion.φ) U :=
    ((Cvs.Route.OneCellCriterion.analyticOnNhd_φ univ).deriv).mono (subset_univ _)
  have hh : AnalyticOnNhd ℂ
      (fun z => Cvs.Route.OneCellCriterion.φ z * ((Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B) z * z ^ 2 - (A : ℂ) - (B : ℂ) * z) / 2)) U :=
    (Cvs.Route.OneCellCriterion.analyticOnNhd_φ U).mul
      ((((hlap.mul (analyticOnNhd_id.pow 2)).sub analyticOnNhd_const).sub
        (analyticOnNhd_const.mul analyticOnNhd_id)).div analyticOnNhd_const fun _ _ => two_ne_zero)
  set b : ℝ := max σ (1 / 2) + 1 with hb
  have hbU : (b : ℂ) ∈ U := by
    show σ < (b : ℂ).re
    rw [Complex.ofReal_re, hb]
    linarith [le_max_left σ (1 / 2)]
  have hten : Tendsto (fun j : ℕ => (((b + 1 / ((j : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] (b : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hr : Tendsto (fun j : ℕ => b + 1 / ((j : ℝ) + 1)) atTop (𝓝 (b + 0)) :=
        tendsto_const_nhds.add h0
      have hc := (Complex.continuous_ofReal.tendsto (b + 0)).comp hr
      have hc' : Tendsto (fun j : ℕ => (((b + 1 / ((j : ℝ) + 1)) : ℝ) : ℂ)) atTop
          (𝓝 (((b + 0 : ℝ)) : ℂ)) := hc
      simpa using hc'
    · filter_upwards with j
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      have : b + 1 / ((j : ℝ) + 1) = b := by exact_mod_cast congrArg Complex.re hc
      have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ w in 𝓝[≠] (b : ℂ),
      deriv Cvs.Route.OneCellCriterion.φ w
        = Cvs.Route.OneCellCriterion.φ w * ((Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B) w * w ^ 2 - (A : ℂ) - (B : ℂ) * w) / 2) := by
    refine hten.frequently (Filter.Eventually.frequently ?_)
    filter_upwards with j
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    exact real_identity_GShift A B (by rw [hb]; linarith [le_max_right σ (1 / 2)])
  exact hf.eqOn_of_preconnected_of_frequently_eq hh hUc hbU hfreq hz

/-- No zero of `riemannXi` lies to the right of `1 / 2 + σ` when `GShift A B ≥ 0` and `ConvAbove (GShift A B) σ`. -/
theorem re_le_of_convAbove_GShift {A B : ℝ} (hG : ∀ L, 0 < L → 0 ≤ GShift A B L)
    {σ : ℝ} (hσ : Cvs.Upstream.LandauLaplaceNonneg.ConvAbove (GShift A B) σ) {ρ : ℂ} (hρ : Cvs.Zeta.riemannXi ρ = 0) :
    ρ.re ≤ 1 / 2 + σ := by
  by_contra hlt
  rw [not_le] at hlt
  set z₀ : ℂ := ρ - 1 / 2 with hz₀def
  have hz₀ : σ < z₀.re := by rw [hz₀def]; simp; linarith
  have hφ0 : Cvs.Route.OneCellCriterion.φ z₀ = 0 := by
    unfold Cvs.Route.OneCellCriterion.φ
    rw [hz₀def, show (1 / 2 : ℂ) + (ρ - 1 / 2) = ρ by ring]
    exact hρ
  set U : Set ℂ := {z | σ < z.re}
  have hUo : IsOpen U := Cvs.Upstream.LandauLaplaceNonneg.isOpen_halfPlane σ
  set Ψ : ℂ → ℂ := fun z => (Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B) z * z ^ 2 - (A : ℂ) - (B : ℂ) * z) / 2 with hΨdef
  have hΨ : DifferentiableOn ℂ Ψ U :=
    ((((Cvs.Upstream.LandauLaplaceNonneg.differentiableOn_lap hG (aestronglyMeasurable_GShift A B) hσ).mul
      (differentiableOn_id.pow 2)).sub (differentiableOn_const _)).sub
      ((differentiableOn_const _).mul differentiableOn_id)).div_const 2
  have key : ∀ n : ℕ, ∃ Ψn : ℂ → ℂ, DifferentiableOn ℂ Ψn U ∧ ∀ z ∈ U, iteratedDeriv n Cvs.Route.OneCellCriterion.φ z = Cvs.Route.OneCellCriterion.φ z * Ψn z := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => 1, differentiableOn_const _, fun z _ => by simp⟩
    | succ n ih =>
      obtain ⟨Ψn, hΨn, hn⟩ := ih
      refine ⟨fun z => Ψ z * Ψn z + deriv Ψn z, ?_, fun z hz => ?_⟩
      · exact (hΨ.mul hΨn).add ((hΨn.analyticOnNhd hUo).deriv.differentiableOn)
      · have hz' : σ < z.re := hz
        rw [iteratedDeriv_succ]
        have hev : iteratedDeriv n Cvs.Route.OneCellCriterion.φ =ᶠ[𝓝 z] fun w => Cvs.Route.OneCellCriterion.φ w * Ψn w :=
          Filter.eventually_of_mem (hUo.mem_nhds hz) hn
        rw [hev.deriv_eq, show (fun w => Cvs.Route.OneCellCriterion.φ w * Ψn w) = Cvs.Route.OneCellCriterion.φ * Ψn from rfl,
          deriv_mul (Cvs.Route.OneCellCriterion.differentiable_φ z) (hΨn.differentiableAt (hUo.mem_nhds hz)),
          deriv_φ_eq_GShift hG hσ hz']
        simp only [hΨdef]
        ring
  have hall : ∀ n, iteratedDeriv n Cvs.Route.OneCellCriterion.φ z₀ = 0 := fun n => by
    obtain ⟨Ψn, -, hn⟩ := key n
    rw [hn z₀ hz₀, hφ0, zero_mul]
  have hzero : ∀ z, Cvs.Route.OneCellCriterion.φ z = 0 := fun z => by
    rw [← Complex.taylorSeries_eq_of_entire' (c := z₀) (z := z) Cvs.Route.OneCellCriterion.differentiable_φ]
    simp [hall]
  have h := hzero (-(1 / 2))
  unfold Cvs.Route.OneCellCriterion.φ at h
  rw [show (1 / 2 : ℂ) + -(1 / 2) = 0 by ring] at h
  exact Cvs.Zeta.riemannXi_zero_ne_zero h

/-- **Landau Shift Criterion for `RiemannHypothesis`**: if `0 ≤ G L + A * L + B` for all `L > 0`
(for ANY real constants `A, B`), then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_GShift_nonneg {A B : ℝ}
    (hG : ∀ L : ℝ, 0 < L → 0 ≤ GShift A B L) : RiemannHypothesis := by
  rw [← Cvs.Operator.allZerosOnLine_iff_rh]
  by_contra hnot
  obtain ⟨ρ, hre⟩ := Cvs.Zeta.GaussKernel.AdmissibleKernel.exists_offLine_of_not_allZerosOnLine hnot
  obtain ⟨hz, h0, h1⟩ := ρ.2
  have hρ1 : (ρ : ℂ) ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hξ : Cvs.Zeta.riemannXi ρ = 0 := (Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta h0 hρ1).2 hz
  obtain ⟨ρ', hξ', hre'⟩ : ∃ ρ' : ℂ, Cvs.Zeta.riemannXi ρ' = 0 ∧ 1 / 2 < ρ'.re := by
    rcases lt_or_gt_of_ne hre with h | h
    · exact ⟨1 - ρ, by rw [Cvs.Zeta.riemannXi_one_sub]; exact hξ, by simp; linarith⟩
    · exact ⟨ρ, hξ, h⟩
  set δ : ℝ := ρ'.re - 1 / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set S : Set ℝ := {σ | Cvs.Upstream.LandauLaplaceNonneg.ConvAbove (GShift A B) σ}
  have hhalf : (1 / 2 : ℝ) ∈ S := convAbove_GShift_half A B
  have hlow : ∀ σ ∈ S, δ ≤ σ := fun σ hσ => by
    have := re_le_of_convAbove_GShift hG hσ hξ'
    rw [hδ]; linarith
  have hbdd : BddBelow S := ⟨δ, hlow⟩
  have hne : S.Nonempty := ⟨_, hhalf⟩
  set σ₁ : ℝ := sInf S
  have hσ₁δ : δ ≤ σ₁ := le_csInf hne hlow
  have hσ₁pos : 0 < σ₁ := lt_of_lt_of_le hδ0 hσ₁δ
  have hconv : Cvs.Upstream.LandauLaplaceNonneg.ConvAbove (GShift A B) σ₁ := by
    intro τ hτ
    obtain ⟨σ, hσS, hστ⟩ := exists_lt_of_csInf_lt hne hτ
    exact hσS τ hστ
  have hφσ : Cvs.Route.OneCellCriterion.φ (σ₁ : ℂ) ≠ 0 := by
    intro h
    have := Cvs.ZeroFree.abs_im_gt_five_of_riemannXi_eq_zero h
    simp at this
    linarith
  obtain ⟨r₁, hr₁, hball⟩ :=
    Metric.eventually_nhds_iff.1 (Cvs.Route.OneCellCriterion.differentiable_φ.continuous.continuousAt.eventually_ne hφσ)
  set r : ℝ := min r₁ σ₁
  have hr0 : 0 < r := lt_min hr₁ hσ₁pos
  have hrσ : r ≤ σ₁ := min_le_right _ _
  have hrr : r ≤ r₁ := min_le_left _ _
  set Ft : ℂ → ℂ := fun z =>
    2 / z ^ 2 * (deriv Cvs.Route.OneCellCriterion.φ z / Cvs.Route.OneCellCriterion.φ z) + (A : ℂ) / z ^ 2 + (B : ℂ) / z with hFt
  have hFd : DifferentiableOn ℂ Ft (Metric.ball (σ₁ : ℂ) r) := by
    intro z hz
    have hz0 : z ≠ 0 := Cvs.Route.OneCellCriterion.ne_zero_of_mem_ball hσ₁pos hrσ hz
    have hφz : Cvs.Route.OneCellCriterion.φ z ≠ 0 := hball (lt_of_lt_of_le (Metric.mem_ball.1 hz) hrr)
    have h1 : DifferentiableAt ℂ (fun z : ℂ => 2 / z ^ 2) z :=
      (differentiableAt_const _).fun_div (differentiableAt_pow 2) (pow_ne_zero 2 hz0)
    have h2 : DifferentiableAt ℂ (fun z => deriv Cvs.Route.OneCellCriterion.φ z / Cvs.Route.OneCellCriterion.φ z) z :=
      (((Cvs.Route.OneCellCriterion.analyticOnNhd_φ univ).deriv z trivial).differentiableAt).fun_div (Cvs.Route.OneCellCriterion.differentiable_φ z) hφz
    have h3 : DifferentiableAt ℂ (fun z : ℂ => (A : ℂ) / z ^ 2) z :=
      (differentiableAt_const _).fun_div (differentiableAt_pow 2) (pow_ne_zero 2 hz0)
    have h4 : DifferentiableAt ℂ (fun z : ℂ => (B : ℂ) / z) z :=
      (differentiableAt_const _).fun_div differentiableAt_id hz0
    exact (((h1.mul h2).add h3).add h4).differentiableWithinAt
  have hFeq : ∀ z ∈ Metric.ball (σ₁ : ℂ) r, σ₁ < z.re → Ft z = Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B) z := by
    intro z hz hzre
    have hz0 : z ≠ 0 := Cvs.Route.OneCellCriterion.ne_zero_of_mem_ball hσ₁pos hrσ hz
    have hφz : Cvs.Route.OneCellCriterion.φ z ≠ 0 := hball (lt_of_lt_of_le (Metric.mem_ball.1 hz) hrr)
    simp only [hFt]
    rw [deriv_φ_eq_GShift hG hconv hzre]
    field_simp
    ring
  have hnew : Cvs.Upstream.LandauLaplaceNonneg.Conv (GShift A B) (σ₁ - r / 4) :=
    Cvs.Upstream.LandauLaplaceNonneg.conv_of_analytic hG (aestronglyMeasurable_GShift A B) hconv hr0 hFd hFeq
  have hmem : σ₁ - r / 4 ∈ S := hnew.convAbove hG (aestronglyMeasurable_GShift A B)
  have := csInf_le hbdd hmem
  linarith

/-- **Shifted Chebyshev Criterion for `RiemannHypothesis`**: if there exist real constants `A, B`
such that `-A * log x - B ≤ M x - Psihalf x` for all `1 < x`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_M_sub_Psihalf_ge_neg_linear {A B : ℝ}
    (h : ∀ x : ℝ, 1 < x → -A * Real.log x - B ≤ M x - Psihalf x) : RiemannHypothesis := by
  refine riemannHypothesis_of_GShift_nonneg (A := 2 * A) (B := 2 * B) fun L hL => ?_
  have hx : 1 < Real.exp L := by rw [Real.one_lt_exp_iff]; exact hL
  have hM := h (Real.exp L) hx
  unfold GShift
  rw [← Real.log_exp L, Cvs.Route.OneCellChebyshevInequality.G_log_eq hx.le, Real.log_exp]
  rw [Real.log_exp] at hM
  linarith

/-- For every real `1 < x`, `log ⌈x⌉₊ ≤ log x + 1`. -/
theorem log_ceil_le_log_add_one {x : ℝ} (hx : 1 < x) :
    Real.log (⌈x⌉₊ : ℝ) ≤ Real.log x + 1 := by
  have hx0 : 0 < x := by linarith
  have hceil_lt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hle : (⌈x⌉₊ : ℝ) ≤ x * Real.exp 1 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith
  calc
    Real.log (⌈x⌉₊ : ℝ) ≤ Real.log (x * Real.exp 1) :=
      Real.log_le_log (by positivity) hle
    _ = Real.log x + 1 := by
      rw [Real.log_mul hx0.ne' (Real.exp_pos 1).ne', Real.log_exp]

/-- `partialSumHalf 0 k = 0` for every `k : ℕ`. -/
theorem partialSumHalf_zero (k : ℕ) : partialSumHalf 0 k = 0 := by
  unfold partialSumHalf
  simp

/-- **Unconditional Real-Variable Lower Bound on `M x - Psihalf x` in Terms of `Op ⌈x⌉₊ μ vac` Alone**:
combines `M_sub_Psihalf_real_ge_master` (at `b = 0`, `α = -2 * eulerMascheroni`) with
`norm_Op_divisorDiscrepancy_neg_two_eulerMascheroni_vac_le_twenty` (`‖Op ⌈x⌉₊ d_{-2γ} vac‖ ≤ 20`). -/
theorem M_sub_Psihalf_real_ge_neg_moebius_norm_sq {x : ℝ} (hx : 1 < x) :
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst - -2 * eulerMascheroni - 200) * Real.log (⌈x⌉₊ : ℝ) - 6
        - (1 / 2) * ∑ k ∈ Finset.Ico 1 ⌈x⌉₊,
            logStep k * partialSumHalf (μ : ArithmeticFunction ℝ) k ^ 2
      ≤ M x - Psihalf x := by
  have hc : 1 < ⌈x⌉₊ := one_lt_ceil_of_one_lt hx
  have hL : 0 ≤ Real.log (⌈x⌉₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hc.le)
  have hmaster := M_sub_Psihalf_real_ge_master hx (-2 * eulerMascheroni) 0
  simp only [zero_mul, sub_zero, partialSumHalf_zero, mul_zero, Finset.sum_const_zero, add_zero] at hmaster
  have hd := norm_Op_divisorDiscrepancy_neg_two_eulerMascheroni_vac_le_twenty hc
  have hμ0 : 0 ≤ ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖ := norm_nonneg _
  have hprod :
      ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖
          * ‖Op ⌈x⌉₊ (divisorDiscrepancy (-2 * eulerMascheroni)) vac‖
        ≤ (1 / 2) * ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖ ^ 2 + 200 := by
    have hsq : 0 ≤ (‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖ - 20) ^ 2 := sq_nonneg _
    nlinarith
  have hmul :
      Real.log (⌈x⌉₊ : ℝ)
          * ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖
          * ‖Op ⌈x⌉₊ (divisorDiscrepancy (-2 * eulerMascheroni)) vac‖
        ≤ Real.log (⌈x⌉₊ : ℝ)
            * ((1 / 2) * ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖ ^ 2 + 200) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hprod hL
  have hnorm_eq :
      Real.log (⌈x⌉₊ : ℝ) * ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖ ^ 2
        = ∑ k ∈ Finset.Ico 1 ⌈x⌉₊,
            logStep k * partialSumHalf (μ : ArithmeticFunction ℝ) k ^ 2 := by
    rw [norm_sq_Op_vac_eq_rieszCorrelation hc (μ : ArithmeticFunction ℝ),
      log_mul_rieszCorrelation_eq_sum_partialSumHalf hc]
    refine Finset.sum_congr rfl fun k _ => by ring
  linarith

/-- **Pure Möbius-Energy Criterion for `RiemannHypothesis`** (all `divisorDiscrepancy`, `archSymbol 0`,
`zetaHalfConst`, `eulerMascheroni`, and `-6` constants eliminated unconditionally):
if the Riesz-weighted mean of `partialSumHalf μ k ^ 2` is bounded by `A * log ⌈x⌉₊ + B`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_sum_moebius_sq_le_linear {A B : ℝ} (hA : 0 ≤ A)
    (h : ∀ x : ℝ, 1 < x →
      ∑ k ∈ Finset.Ico 1 ⌈x⌉₊,
          logStep k * partialSumHalf (μ : ArithmeticFunction ℝ) k ^ 2
        ≤ A * Real.log (⌈x⌉₊ : ℝ) + B) :
    RiemannHypothesis := by
  set C₀ : ℝ := |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst - -2 * eulerMascheroni - 200| + (1 / 2) * A
  have hC₀ : 0 ≤ C₀ := by positivity
  refine riemannHypothesis_of_M_sub_Psihalf_ge_neg_linear
    (A := C₀) (B := C₀ + (1 / 2) * B + 6) fun x hx => ?_
  have hlow := M_sub_Psihalf_real_ge_neg_moebius_norm_sq hx
  have hup := h x hx
  have hL_nonneg : 0 ≤ Real.log (⌈x⌉₊ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (one_lt_ceil_of_one_lt hx).le)
  have habs :
      -(|Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst - -2 * eulerMascheroni - 200|)
        ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst - -2 * eulerMascheroni - 200 :=
    neg_abs_le _
  have hcoef :
      -C₀ * Real.log (⌈x⌉₊ : ℝ)
        ≤ (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst - -2 * eulerMascheroni - 200) * Real.log (⌈x⌉₊ : ℝ)
          - (1 / 2) * A * Real.log (⌈x⌉₊ : ℝ) := by
    unfold C₀
    nlinarith
  have hceil := log_ceil_le_log_add_one hx
  have hlog_bound : -C₀ * (Real.log x + 1) ≤ -C₀ * Real.log (⌈x⌉₊ : ℝ) := by
    nlinarith
  linarith

/-! ### 9. Sub-Power Landau Criterion (`GExpShift`): Absorbing `O_ε(x^ε)` Remainder Terms -/

/-- The exponentially + linearly shifted one-cell function `G(L) + C * exp(ε * L) + A * L + B`. -/
def GExpShift (C ε A B L : ℝ) : ℝ :=
  GShift A B L + C * Real.exp (ε * L)

/-- For `ε < 1 / 2 < s`, `GExpShift C ε A B L * exp(-(s * L))` is integrable on `(0, ∞)`. -/
theorem integrableOn_GExpShift_mul_exp (C : ℝ) {ε : ℝ} (hε : ε < 1 / 2) (A B : ℝ)
    {s : ℝ} (hs : 1 / 2 < s) :
    IntegrableOn (fun L => GExpShift C ε A B L * Real.exp (-(s * L))) (Ioi 0) := by
  have hGS := integrableOn_GShift_mul_exp A B hs
  have hC : IntegrableOn (fun L => C * Real.exp ((ε - s) * L)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : ε - s < 0) 0).const_mul C
  have hfun :
      (fun L => GExpShift C ε A B L * Real.exp (-(s * L)))
        = fun L => GShift A B L * Real.exp (-(s * L)) + C * Real.exp ((ε - s) * L) := by
    funext L
    unfold GExpShift
    rw [add_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hfun]
  exact hGS.add hC

/-- `GExpShift C ε A B` is a.e. strongly measurable on `(0, ∞)` when `ε < 1 / 2`. -/
theorem aestronglyMeasurable_GExpShift (C : ℝ) {ε : ℝ} (hε : ε < 1 / 2) (A B : ℝ) :
    AEStronglyMeasurable (GExpShift C ε A B) (volume.restrict (Ioi 0)) := by
  have h := (integrableOn_GExpShift_mul_exp C hε A B (s := 1) (by norm_num)).aestronglyMeasurable
  have h2 := h.mul
    (Continuous.aestronglyMeasurable (f := fun L : ℝ => Real.exp (1 * L)) (by fun_prop))
  refine h2.congr (ae_of_all _ fun L => ?_)
  show GExpShift C ε A B L * Real.exp (-(1 * L)) * Real.exp (1 * L) = GExpShift C ε A B L
  rw [mul_assoc, ← Real.exp_add]
  simp

/-- The Laplace transform of `GExpShift C ε A B` converges above `1 / 2` when `ε < 1 / 2`. -/
theorem convAbove_GExpShift_half (C : ℝ) {ε : ℝ} (hε : ε < 1 / 2) (A B : ℝ) :
    Cvs.Upstream.LandauLaplaceNonneg.ConvAbove (GExpShift C ε A B) (1 / 2) :=
  fun _ hτ => integrableOn_GExpShift_mul_exp C hε A B hτ

/-- On the real ray `s > 1 / 2` (`ε < 1 / 2`), `lap (GExpShift C ε A B) s = lap (GShift A B) s + C / (s - ε)`. -/
theorem lap_GExpShift_real (C : ℝ) {ε : ℝ} (hε : ε < 1 / 2) (A B : ℝ)
    {s : ℝ} (hs : 1 / 2 < s) :
    Cvs.Upstream.LandauLaplaceNonneg.lap (GExpShift C ε A B) (s : ℂ)
      = Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B) (s : ℂ) + (C : ℂ) / ((s : ℂ) - (ε : ℂ)) := by
  have hGS := integrableOn_GShift_mul_exp A B hs
  have hC : IntegrableOn (fun L => C * Real.exp ((ε - s) * L)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : ε - s < 0) 0).const_mul C
  have h1 :
      Cvs.Upstream.LandauLaplaceNonneg.lap (GExpShift C ε A B) (s : ℂ)
        = ((∫ L in Ioi (0 : ℝ), GExpShift C ε A B L * Real.exp (-(s * L)) : ℝ) : ℂ) := by
    unfold Cvs.Upstream.LandauLaplaceNonneg.lap
    have hfun :
        (fun L : ℝ => (GExpShift C ε A B L : ℂ) * Complex.exp (-((s : ℂ) * L)))
          = fun L => ((GExpShift C ε A B L * Real.exp (-(s * L)) : ℝ) : ℂ) := by
      funext L; push_cast; ring_nf
    rw [hfun, integral_complex_ofReal]
  have h2 :
      Cvs.Upstream.LandauLaplaceNonneg.lap (GShift A B) (s : ℂ)
        = ((∫ L in Ioi (0 : ℝ), GShift A B L * Real.exp (-(s * L)) : ℝ) : ℂ) := by
    unfold Cvs.Upstream.LandauLaplaceNonneg.lap
    have hfun :
        (fun L : ℝ => (GShift A B L : ℂ) * Complex.exp (-((s : ℂ) * L)))
          = fun L => ((GShift A B L * Real.exp (-(s * L)) : ℝ) : ℂ) := by
      funext L; push_cast; ring_nf
    rw [hfun, integral_complex_ofReal]
  have hsplit :
      (fun L => GExpShift C ε A B L * Real.exp (-(s * L)))
        = fun L => GShift A B L * Real.exp (-(s * L)) + C * Real.exp ((ε - s) * L) := by
    funext L
    unfold GExpShift
    rw [add_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hne : ε - s ≠ 0 := by linarith
  have hne' : s - ε ≠ 0 := by linarith
  have hint_eq :
      (∫ L in Ioi (0 : ℝ), GExpShift C ε A B L * Real.exp (-(s * L)))
        = (∫ L in Ioi (0 : ℝ), GShift A B L * Real.exp (-(s * L)))
          + C / (s - ε) := by
    rw [hsplit, integral_add hGS hC, integral_const_mul,
      Cvs.Route.OneCellLaplaceTransform.laplace_exp (by linarith : ε - s < 0)]
    field_simp
    ring
  rw [h1, h2, hint_eq]
  push_cast
  ring

/-- Real-ray identity for `GExpShift C ε A B` (`ε < 1 / 2 < s`). -/
theorem real_identity_GExpShift (C : ℝ) {ε : ℝ} (hε : ε < 1 / 2) (A B : ℝ)
    {s : ℝ} (hs : 1 / 2 < s) :
    deriv Cvs.Route.OneCellCriterion.φ (s : ℂ)
      = Cvs.Route.OneCellCriterion.φ (s : ℂ)
        * (((Cvs.Upstream.LandauLaplaceNonneg.lap (GExpShift C ε A B) (s : ℂ) - (C : ℂ) / ((s : ℂ) - (ε : ℂ))) * (s : ℂ) ^ 2
            - (A : ℂ) - (B : ℂ) * (s : ℂ)) / 2) := by
  rw [real_identity_GShift A B hs, lap_GExpShift_real C hε A B hs]
  ring

/-- Analytic continuation of the `GExpShift` differential identity to `{Re z > σ}` when `ε ≤ σ`. -/
theorem deriv_φ_eq_GExpShift {C ε A B : ℝ} (hε : ε < 1 / 2)
    (hG : ∀ L, 0 < L → 0 ≤ GExpShift C ε A B L)
    {σ : ℝ} (hεσ : ε ≤ σ) (hσ : Cvs.Upstream.LandauLaplaceNonneg.ConvAbove (GExpShift C ε A B) σ)
    {z : ℂ} (hz : σ < z.re) :
    deriv Cvs.Route.OneCellCriterion.φ z
      = Cvs.Route.OneCellCriterion.φ z
        * (((Cvs.Upstream.LandauLaplaceNonneg.lap (GExpShift C ε A B) z - (C : ℂ) / (z - (ε : ℂ))) * z ^ 2
            - (A : ℂ) - (B : ℂ) * z) / 2) := by
  set U : Set ℂ := {z | σ < z.re}
  have hUo : IsOpen U := Cvs.Upstream.LandauLaplaceNonneg.isOpen_halfPlane σ
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt σ).isPreconnected
  have hlap : AnalyticOnNhd ℂ (Cvs.Upstream.LandauLaplaceNonneg.lap (GExpShift C ε A B)) U :=
    (Cvs.Upstream.LandauLaplaceNonneg.differentiableOn_lap hG (aestronglyMeasurable_GExpShift C hε A B) hσ).analyticOnNhd hUo
  have hne_ε : ∀ w ∈ U, w - (ε : ℂ) ≠ 0 := by
    intro w hw h0
    have hre : σ < w.re := hw
    have := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at this
    linarith
  have hdiv_ε : AnalyticOnNhd ℂ (fun w => (C : ℂ) / (w - (ε : ℂ))) U :=
    analyticOnNhd_const.div (analyticOnNhd_id.sub analyticOnNhd_const) hne_ε
  have hf : AnalyticOnNhd ℂ (deriv Cvs.Route.OneCellCriterion.φ) U :=
    ((Cvs.Route.OneCellCriterion.analyticOnNhd_φ univ).deriv).mono (subset_univ _)
  have hh : AnalyticOnNhd ℂ
      (fun z => Cvs.Route.OneCellCriterion.φ z
        * (((Cvs.Upstream.LandauLaplaceNonneg.lap (GExpShift C ε A B) z - (C : ℂ) / (z - (ε : ℂ))) * z ^ 2
            - (A : ℂ) - (B : ℂ) * z) / 2)) U :=
    (Cvs.Route.OneCellCriterion.analyticOnNhd_φ U).mul
      (((((hlap.sub hdiv_ε).mul (analyticOnNhd_id.pow 2)).sub analyticOnNhd_const).sub
        (analyticOnNhd_const.mul analyticOnNhd_id)).div analyticOnNhd_const fun _ _ => two_ne_zero)
  set b : ℝ := max σ (1 / 2) + 1 with hb
  have hbU : (b : ℂ) ∈ U := by
    show σ < (b : ℂ).re
    rw [Complex.ofReal_re, hb]
    linarith [le_max_left σ (1 / 2)]
  have hten : Tendsto (fun j : ℕ => (((b + 1 / ((j : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] (b : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hr : Tendsto (fun j : ℕ => b + 1 / ((j : ℝ) + 1)) atTop (𝓝 (b + 0)) :=
        tendsto_const_nhds.add h0
      have hc := (Complex.continuous_ofReal.tendsto (b + 0)).comp hr
      have hc' : Tendsto (fun j : ℕ => (((b + 1 / ((j : ℝ) + 1)) : ℝ) : ℂ)) atTop
          (𝓝 (((b + 0 : ℝ)) : ℂ)) := hc
      simpa using hc'
    · filter_upwards with j
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      have : b + 1 / ((j : ℝ) + 1) = b := by exact_mod_cast congrArg Complex.re hc
      have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ w in 𝓝[≠] (b : ℂ),
      deriv Cvs.Route.OneCellCriterion.φ w
        = Cvs.Route.OneCellCriterion.φ w
          * (((Cvs.Upstream.LandauLaplaceNonneg.lap (GExpShift C ε A B) w - (C : ℂ) / (w - (ε : ℂ))) * w ^ 2
              - (A : ℂ) - (B : ℂ) * w) / 2) := by
    refine hten.frequently (Filter.Eventually.frequently ?_)
    filter_upwards with j
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    exact real_identity_GExpShift C hε A B (by rw [hb]; linarith [le_max_right σ (1 / 2)])
  exact hf.eqOn_of_preconnected_of_frequently_eq hh hUc hbU hfreq hz

/-- No zero of `riemannXi` lies to the right of `1 / 2 + σ` when `ε ≤ σ`, `GExpShift C ε A B ≥ 0`,
and `ConvAbove (GExpShift C ε A B) σ`. -/
theorem re_le_of_convAbove_GExpShift {C ε A B : ℝ} (hε : ε < 1 / 2)
    (hG : ∀ L, 0 < L → 0 ≤ GExpShift C ε A B L)
    {σ : ℝ} (hεσ : ε ≤ σ) (hσ : Cvs.Upstream.LandauLaplaceNonneg.ConvAbove (GExpShift C ε A B) σ)
    {ρ : ℂ} (hρ : Cvs.Zeta.riemannXi ρ = 0) :
    ρ.re ≤ 1 / 2 + σ := by
  by_contra hlt
  rw [not_le] at hlt
  set z₀ : ℂ := ρ - 1 / 2 with hz₀def
  have hz₀ : σ < z₀.re := by rw [hz₀def]; simp; linarith
  have hφ0 : Cvs.Route.OneCellCriterion.φ z₀ = 0 := by
    unfold Cvs.Route.OneCellCriterion.φ
    rw [hz₀def, show (1 / 2 : ℂ) + (ρ - 1 / 2) = ρ by ring]
    exact hρ
  set U : Set ℂ := {z | σ < z.re}
  have hUo : IsOpen U := Cvs.Upstream.LandauLaplaceNonneg.isOpen_halfPlane σ
  have hne_ε : ∀ w ∈ U, w - (ε : ℂ) ≠ 0 := by
    intro w hw h0
    have hre : σ < w.re := hw
    have := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at this
    linarith
  have hdiv_ε : DifferentiableOn ℂ (fun w => (C : ℂ) / (w - (ε : ℂ))) U :=
    (differentiableOn_const _).fun_div (differentiableOn_id.sub (differentiableOn_const _)) hne_ε
  set Ψ : ℂ → ℂ := fun z =>
    (((Cvs.Upstream.LandauLaplaceNonneg.lap (GExpShift C ε A B) z - (C : ℂ) / (z - (ε : ℂ))) * z ^ 2
      - (A : ℂ) - (B : ℂ) * z) / 2) with hΨdef
  have hΨ : DifferentiableOn ℂ Ψ U :=
    (((((Cvs.Upstream.LandauLaplaceNonneg.differentiableOn_lap hG (aestronglyMeasurable_GExpShift C hε A B) hσ).sub hdiv_ε).mul
      (differentiableOn_id.pow 2)).sub (differentiableOn_const _)).sub
      ((differentiableOn_const _).mul differentiableOn_id)).div_const 2
  have key : ∀ n : ℕ, ∃ Ψn : ℂ → ℂ, DifferentiableOn ℂ Ψn U ∧ ∀ z ∈ U, iteratedDeriv n Cvs.Route.OneCellCriterion.φ z = Cvs.Route.OneCellCriterion.φ z * Ψn z := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => 1, differentiableOn_const _, fun z _ => by simp⟩
    | succ n ih =>
      obtain ⟨Ψn, hΨn, hn⟩ := ih
      refine ⟨fun z => Ψ z * Ψn z + deriv Ψn z, ?_, fun z hz => ?_⟩
      · exact (hΨ.mul hΨn).add ((hΨn.analyticOnNhd hUo).deriv.differentiableOn)
      · have hz' : σ < z.re := hz
        rw [iteratedDeriv_succ]
        have hev : iteratedDeriv n Cvs.Route.OneCellCriterion.φ =ᶠ[𝓝 z] fun w => Cvs.Route.OneCellCriterion.φ w * Ψn w :=
          Filter.eventually_of_mem (hUo.mem_nhds hz) hn
        rw [hev.deriv_eq, show (fun w => Cvs.Route.OneCellCriterion.φ w * Ψn w) = Cvs.Route.OneCellCriterion.φ * Ψn from rfl,
          deriv_mul (Cvs.Route.OneCellCriterion.differentiable_φ z) (hΨn.differentiableAt (hUo.mem_nhds hz)),
          deriv_φ_eq_GExpShift hε hG hεσ hσ hz']
        simp only [hΨdef]
        ring
  have hall : ∀ n, iteratedDeriv n Cvs.Route.OneCellCriterion.φ z₀ = 0 := fun n => by
    obtain ⟨Ψn, -, hn⟩ := key n
    rw [hn z₀ hz₀, hφ0, zero_mul]
  have hzero : ∀ z, Cvs.Route.OneCellCriterion.φ z = 0 := fun z => by
    rw [← Complex.taylorSeries_eq_of_entire' (c := z₀) (z := z) Cvs.Route.OneCellCriterion.differentiable_φ]
    simp [hall]
  have h := hzero (-(1 / 2))
  unfold Cvs.Route.OneCellCriterion.φ at h
  rw [show (1 / 2 : ℂ) + -(1 / 2) = 0 by ring] at h
  exact Cvs.Zeta.riemannXi_zero_ne_zero h

/-- **Zero-Free Strip Theorem via `GExpShift`**: if `0 < ε < 1 / 2` and `0 ≤ GExpShift C ε A B L`
for all `L > 0`, then every zero `ρ` of `riemannXi` satisfies `ρ.re ≤ 1 / 2 + ε`! -/
theorem re_le_half_add_of_GExpShift_nonneg {C ε A B : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2)
    (hG : ∀ L : ℝ, 0 < L → 0 ≤ GExpShift C ε A B L)
    {ρ : ℂ} (hρ : Cvs.Zeta.riemannXi ρ = 0) :
    ρ.re ≤ 1 / 2 + ε := by
  by_contra hlt
  rw [not_le] at hlt
  set δ : ℝ := ρ.re - 1 / 2 with hδ
  have hεδ : ε < δ := by rw [hδ]; linarith
  set S : Set ℝ := {σ | ε ≤ σ ∧ Cvs.Upstream.LandauLaplaceNonneg.ConvAbove (GExpShift C ε A B) σ}
  have hhalf : (1 / 2 : ℝ) ∈ S := ⟨hε.le, convAbove_GExpShift_half C hε A B⟩
  have hlow : ∀ σ ∈ S, δ ≤ σ := fun σ hσ => by
    have := re_le_of_convAbove_GExpShift hε hG hσ.1 hσ.2 hρ
    rw [hδ]; linarith
  have hbdd : BddBelow S := ⟨δ, hlow⟩
  have hne : S.Nonempty := ⟨_, hhalf⟩
  set σ₁ : ℝ := sInf S
  have hσ₁δ : δ ≤ σ₁ := le_csInf hne hlow
  have hεσ₁ : ε < σ₁ := lt_of_lt_of_le hεδ hσ₁δ
  have hσ₁pos : 0 < σ₁ := lt_trans hε0 hεσ₁
  have hconv : Cvs.Upstream.LandauLaplaceNonneg.ConvAbove (GExpShift C ε A B) σ₁ := by
    intro τ hτ
    obtain ⟨σ, hσS, hστ⟩ := exists_lt_of_csInf_lt hne hτ
    exact hσS.2 τ hστ
  have hφσ : Cvs.Route.OneCellCriterion.φ (σ₁ : ℂ) ≠ 0 := by
    intro h
    have := Cvs.ZeroFree.abs_im_gt_five_of_riemannXi_eq_zero h
    simp at this
    linarith
  obtain ⟨r₁, hr₁, hball⟩ :=
    Metric.eventually_nhds_iff.1 (Cvs.Route.OneCellCriterion.differentiable_φ.continuous.continuousAt.eventually_ne hφσ)
  set r : ℝ := min r₁ (σ₁ - ε)
  have hr0 : 0 < r := lt_min hr₁ (sub_pos.mpr hεσ₁)
  have hr_sub : r ≤ σ₁ - ε := min_le_right _ _
  have hrr : r ≤ r₁ := min_le_left _ _
  have hre_gt_ε : ∀ z ∈ Metric.ball (σ₁ : ℂ) r, ε < z.re := by
    intro z hz
    have h1 := Complex.abs_re_le_norm (z - (σ₁ : ℂ))
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have h2 := abs_lt.mp (h1.trans_lt hz)
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    linarith
  set Ft : ℂ → ℂ := fun z =>
    2 / z ^ 2 * (deriv Cvs.Route.OneCellCriterion.φ z / Cvs.Route.OneCellCriterion.φ z)
      + (C : ℂ) / (z - (ε : ℂ)) + (A : ℂ) / z ^ 2 + (B : ℂ) / z with hFt
  have hFd : DifferentiableOn ℂ Ft (Metric.ball (σ₁ : ℂ) r) := by
    intro z hz
    have hzre : ε < z.re := hre_gt_ε z hz
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at hzre
      linarith
    have hzε : z - (ε : ℂ) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at this
      linarith
    have hφz : Cvs.Route.OneCellCriterion.φ z ≠ 0 := hball (lt_of_lt_of_le (Metric.mem_ball.1 hz) hrr)
    have h1 : DifferentiableAt ℂ (fun z : ℂ => 2 / z ^ 2) z :=
      (differentiableAt_const _).fun_div (differentiableAt_pow 2) (pow_ne_zero 2 hz0)
    have h2 : DifferentiableAt ℂ (fun z => deriv Cvs.Route.OneCellCriterion.φ z / Cvs.Route.OneCellCriterion.φ z) z :=
      (((Cvs.Route.OneCellCriterion.analyticOnNhd_φ univ).deriv z trivial).differentiableAt).fun_div (Cvs.Route.OneCellCriterion.differentiable_φ z) hφz
    have h3 : DifferentiableAt ℂ (fun z : ℂ => (C : ℂ) / (z - (ε : ℂ))) z :=
      (differentiableAt_const _).fun_div (differentiableAt_id.sub (differentiableAt_const _)) hzε
    have h4 : DifferentiableAt ℂ (fun z : ℂ => (A : ℂ) / z ^ 2) z :=
      (differentiableAt_const _).fun_div (differentiableAt_pow 2) (pow_ne_zero 2 hz0)
    have h5 : DifferentiableAt ℂ (fun z : ℂ => (B : ℂ) / z) z :=
      (differentiableAt_const _).fun_div differentiableAt_id hz0
    exact ((((h1.mul h2).add h3).add h4).add h5).differentiableWithinAt
  have hFeq : ∀ z ∈ Metric.ball (σ₁ : ℂ) r, σ₁ < z.re → Ft z = Cvs.Upstream.LandauLaplaceNonneg.lap (GExpShift C ε A B) z := by
    intro z hz hzre
    have hz_ε : ε < z.re := hre_gt_ε z hz
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at hz_ε
      linarith
    have hzε : z - (ε : ℂ) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at this
      linarith
    have hφz : Cvs.Route.OneCellCriterion.φ z ≠ 0 := hball (lt_of_lt_of_le (Metric.mem_ball.1 hz) hrr)
    simp only [hFt]
    rw [deriv_φ_eq_GExpShift hε hG hεσ₁.le hconv hzre]
    field_simp
    ring
  have hnew : Cvs.Upstream.LandauLaplaceNonneg.Conv (GExpShift C ε A B) (σ₁ - r / 4) :=
    Cvs.Upstream.LandauLaplaceNonneg.conv_of_analytic hG (aestronglyMeasurable_GExpShift C hε A B) hconv hr0 hFd hFeq
  have hmem : σ₁ - r / 4 ∈ S := ⟨by linarith, hnew.convAbove hG (aestronglyMeasurable_GExpShift C hε A B)⟩
  have := csInf_le hbdd hmem
  linarith

/-- **Sub-Power Landau Criterion for `RiemannHypothesis`**: if for every `ε ∈ (0, 1 / 2)` there exist
`C, A, B : ℝ` such that `0 ≤ GExpShift C ε A B L` for all `L > 0`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_forall_GExpShift_nonneg
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C A B : ℝ, ∀ L : ℝ, 0 < L → 0 ≤ GExpShift C ε A B L) :
    RiemannHypothesis := by
  rw [← Cvs.Operator.allZerosOnLine_iff_rh]
  by_contra hnot
  obtain ⟨ρ, hre⟩ := Cvs.Zeta.GaussKernel.AdmissibleKernel.exists_offLine_of_not_allZerosOnLine hnot
  obtain ⟨hz, h0, h1⟩ := ρ.2
  have hρ1 : (ρ : ℂ) ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hξ : Cvs.Zeta.riemannXi ρ = 0 := (Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta h0 hρ1).2 hz
  obtain ⟨ρ', hξ', hre'⟩ : ∃ ρ' : ℂ, Cvs.Zeta.riemannXi ρ' = 0 ∧ 1 / 2 < ρ'.re := by
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · exact ⟨1 - ρ, by rw [Cvs.Zeta.riemannXi_one_sub]; exact hξ, by simp; linarith⟩
    · exact ⟨ρ, hξ, hgt⟩
  set ε : ℝ := min ((ρ'.re - 1 / 2) / 2) (1 / 4)
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε_half : ε < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε_re : 1 / 2 + ε < ρ'.re := by
    have : ε ≤ (ρ'.re - 1 / 2) / 2 := min_le_left _ _
    linarith
  obtain ⟨C, A, B, hG⟩ := h ε hε0 hε_half
  have hle := re_le_half_add_of_GExpShift_nonneg hε0 hε_half hG hξ'
  linarith

/-- **Sub-Power Chebyshev Criterion for `RiemannHypothesis`**: if for every `ε ∈ (0, 1 / 2)`
there exist `C, A, B : ℝ` such that `-C * x ^ ε - A * log x - B ≤ M x - Psihalf x` for all `1 < x`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_M_sub_Psihalf_ge_neg_rpow
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ C A B : ℝ, ∀ x : ℝ, 1 < x → -C * x ^ ε - A * Real.log x - B ≤ M x - Psihalf x) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_GExpShift_nonneg fun ε hε0 hε_half => ?_
  obtain ⟨C, A, B, hM⟩ := h ε hε0 hε_half
  refine ⟨2 * C, 2 * A, 2 * B, fun L hL => ?_⟩
  have hx : 1 < Real.exp L := by rw [Real.one_lt_exp_iff]; exact hL
  have hML := hM (Real.exp L) hx
  have hexp_rpow : (Real.exp L) ^ ε = Real.exp (ε * L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp, mul_comm]
  unfold GExpShift GShift
  rw [← Real.log_exp L, Cvs.Route.OneCellChebyshevInequality.G_log_eq hx.le, Real.log_exp]
  rw [Real.log_exp, hexp_rpow] at hML
  linarith

/-- For `1 < x` and `0 ≤ ε`, `(⌈x⌉₊ : ℝ) ^ ε ≤ (2 : ℝ) ^ ε * x ^ ε`. -/
theorem ceil_rpow_le_two_rpow_mul_rpow {x ε : ℝ} (hx : 1 < x) (hε : 0 ≤ ε) :
    (⌈x⌉₊ : ℝ) ^ ε ≤ (2 : ℝ) ^ ε * x ^ ε := by
  have hx0 : 0 < x := by linarith
  have hceil_lt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hle : (⌈x⌉₊ : ℝ) ≤ 2 * x := by linarith
  calc
    (⌈x⌉₊ : ℝ) ^ ε ≤ (2 * x) ^ ε := Real.rpow_le_rpow (Nat.cast_nonneg _) hle hε
    _ = (2 : ℝ) ^ ε * x ^ ε := Real.mul_rpow (by norm_num) hx0.le

/-- For every `0 < y` and `0 < δ`, `log y ≤ y ^ δ / δ`. -/
theorem log_le_rpow_div {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ) :
    Real.log y ≤ y ^ δ / δ := by
  have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy δ)
  rw [Real.log_rpow hy] at h1
  rw [le_div_iff₀ hδ]
  linarith

/-- **Linear-in-`‖Op ⌈x⌉₊ μ vac‖` Lower Bound on `M x - Psihalf x`**:
combining `M_sub_Psihalf_real_ge_master` with `norm_Op_divisorDiscrepancy_neg_two_eulerMascheroni_vac_le_twenty`
without squaring `‖Op ⌈x⌉₊ μ vac‖` bounds the pairing by `20 * log ⌈x⌉₊ * ‖Op ⌈x⌉₊ μ vac‖`. -/
theorem M_sub_Psihalf_real_ge_neg_twenty_mul_norm_Op_moebius {x : ℝ} (hx : 1 < x) :
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst + 2 * eulerMascheroni) * Real.log (⌈x⌉₊ : ℝ) - 6
        - 20 * Real.log (⌈x⌉₊ : ℝ) * ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖
      ≤ M x - Psihalf x := by
  have hc : 1 < ⌈x⌉₊ := one_lt_ceil_of_one_lt hx
  have hL : 0 ≤ Real.log (⌈x⌉₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hc.le)
  have hmas := M_sub_Psihalf_real_ge_master hx (-2 * eulerMascheroni) 0
  simp only [zero_mul, sub_zero, partialSumHalf_zero, mul_zero, Finset.sum_const_zero, add_zero] at hmas
  have h20 := norm_Op_divisorDiscrepancy_neg_two_eulerMascheroni_vac_le_twenty hc
  have hmul :
      Real.log (⌈x⌉₊ : ℝ)
          * ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖
          * ‖Op ⌈x⌉₊ (divisorDiscrepancy (-2 * eulerMascheroni)) vac‖
        ≤ 20 * Real.log (⌈x⌉₊ : ℝ) * ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖ := by
    have h1 :
        ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖
            * ‖Op ⌈x⌉₊ (divisorDiscrepancy (-2 * eulerMascheroni)) vac‖
          ≤ 20 * ‖Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac‖ := by
      nlinarith [norm_nonneg (Op ⌈x⌉₊ (μ : ArithmeticFunction ℝ) vac)]
    have h2 := mul_le_mul_of_nonneg_left h1 hL
    linarith
  linarith

/-- **Zero-Free Strip Theorem from a Fixed Sub-Power Bound on `partialSumHalf μ`**:
if `0 ≤ ε₀ < 1 / 2` and `|partialSumHalf μ k| ≤ C * k ^ ε₀` for all `1 ≤ k`, then every zero `ρ`
of `riemannXi` satisfies `ρ.re ≤ 1 / 2 + ε` for every `ε ∈ (ε₀, 1 / 2)`. -/
theorem re_le_half_add_of_abs_partialSumHalf_moebius_le_rpow
    {ε₀ C : ℝ} (hε₀ : 0 ≤ ε₀) (hC : 0 ≤ C)
    (hbound : ∀ k : ℕ, 1 ≤ k →
      |partialSumHalf (μ : ArithmeticFunction ℝ) k| ≤ C * (k : ℝ) ^ ε₀)
    {ε : ℝ} (hε_gt : ε₀ < ε) (hε_half : ε < 1 / 2)
    {ρ : ℂ} (hρ : Cvs.Zeta.riemannXi ρ = 0) :
    ρ.re ≤ 1 / 2 + ε := by
  set δ := ε - ε₀
  have hδ : 0 < δ := by linarith
  have hε0 : 0 < ε := by linarith
  set A₀ := |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst + 2 * eulerMascheroni|
  set C' := 20 * C / δ * (2 : ℝ) ^ ε
  set B' := A₀ + 6
  refine re_le_half_add_of_GExpShift_nonneg (C := 2 * C') (ε := ε) (A := 2 * A₀) (B := 2 * B')
    hε0 hε_half (fun L hL => ?_) hρ
  have hx : 1 < Real.exp L := Real.one_lt_exp_iff.mpr hL
  have hc : 1 < ⌈Real.exp L⌉₊ := one_lt_ceil_of_one_lt hx
  have hc_pos : (0 : ℝ) < ⌈Real.exp L⌉₊ := by exact_mod_cast (zero_lt_one.trans hc)
  have hlog_le : Real.log (⌈Real.exp L⌉₊ : ℝ) ≤ L + 1 := by
    have h := log_ceil_le_log_add_one hx
    rwa [Real.log_exp] at h
  have hL_nonneg : 0 ≤ Real.log (⌈Real.exp L⌉₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hc.le)
  have hOp :
      ‖Op ⌈Real.exp L⌉₊ (μ : ArithmeticFunction ℝ) vac‖
        ≤ C * (⌈Real.exp L⌉₊ : ℝ) ^ ε₀ := by
    refine norm_Op_vac_le_of_partialSumHalf_le hc (μ : ArithmeticFunction ℝ) (by positivity) fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkc : (k : ℝ) ≤ ⌈Real.exp L⌉₊ := by exact_mod_cast (Finset.mem_Ico.mp hk).2.le
    exact (hbound k hk1).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg k) hkc hε₀) hC)
  have hlog_rpow := log_le_rpow_div hc_pos hδ
  have hprod :
      20 * Real.log (⌈Real.exp L⌉₊ : ℝ) * ‖Op ⌈Real.exp L⌉₊ (μ : ArithmeticFunction ℝ) vac‖
        ≤ 20 * C / δ * (⌈Real.exp L⌉₊ : ℝ) ^ ε := by
    have h1 :
        20 * Real.log (⌈Real.exp L⌉₊ : ℝ) * ‖Op ⌈Real.exp L⌉₊ (μ : ArithmeticFunction ℝ) vac‖
          ≤ 20 * ((⌈Real.exp L⌉₊ : ℝ) ^ δ / δ) * (C * (⌈Real.exp L⌉₊ : ℝ) ^ ε₀) := by
      have ha : 20 * Real.log (⌈Real.exp L⌉₊ : ℝ) ≤ 20 * ((⌈Real.exp L⌉₊ : ℝ) ^ δ / δ) := by linarith
      exact mul_le_mul ha hOp (norm_nonneg _) (by positivity)
    have hrpow_add :
        (⌈Real.exp L⌉₊ : ℝ) ^ δ * (⌈Real.exp L⌉₊ : ℝ) ^ ε₀ = (⌈Real.exp L⌉₊ : ℝ) ^ ε := by
      rw [← Real.rpow_add hc_pos]
      congr 1
      linarith
    have h2 :
        20 * ((⌈Real.exp L⌉₊ : ℝ) ^ δ / δ) * (C * (⌈Real.exp L⌉₊ : ℝ) ^ ε₀)
          = 20 * C / δ * ((⌈Real.exp L⌉₊ : ℝ) ^ δ * (⌈Real.exp L⌉₊ : ℝ) ^ ε₀) := by ring
    rw [h2, hrpow_add] at h1
    exact h1
  have hrpow_ceil :
      (⌈Real.exp L⌉₊ : ℝ) ^ ε ≤ (2 : ℝ) ^ ε * Real.exp (ε * L) := by
    calc
      (⌈Real.exp L⌉₊ : ℝ) ^ ε ≤ (2 : ℝ) ^ ε * (Real.exp L) ^ ε :=
        ceil_rpow_le_two_rpow_mul_rpow hx hε0.le
      _ = (2 : ℝ) ^ ε * Real.exp (ε * L) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp, mul_comm L ε]
  have hmas := M_sub_Psihalf_real_ge_neg_twenty_mul_norm_Op_moebius hx
  have harch :
      -A₀ * Real.log (⌈Real.exp L⌉₊ : ℝ)
        ≤ (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst + 2 * eulerMascheroni)
            * Real.log (⌈Real.exp L⌉₊ : ℝ) := by
    have habs := neg_abs_le (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst + 2 * eulerMascheroni)
    exact mul_le_mul_of_nonneg_right habs hL_nonneg
  have hA_bound : A₀ * Real.log (⌈Real.exp L⌉₊ : ℝ) ≤ A₀ * L + A₀ := by
    have hA0 : 0 ≤ A₀ := abs_nonneg _
    nlinarith
  have hC_bound :
      20 * C / δ * (⌈Real.exp L⌉₊ : ℝ) ^ ε ≤ C' * Real.exp (ε * L) := by
    unfold C'
    have h0 : 0 ≤ 20 * C / δ := by positivity
    nlinarith
  have hG := Cvs.Route.OneCellChebyshevInequality.G_log_eq hx.le
  rw [Real.log_exp] at hG
  unfold GExpShift GShift
  linarith

/-- **Pointwise Sub-Power `partialSumHalf μ` Criterion for `RiemannHypothesis`**:
if for every `0 < ε < 1 / 2`, there exists `C ≥ 0` such that `|partialSumHalf μ k| ≤ C * k ^ ε`
for all `1 ≤ k`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_abs_partialSumHalf_moebius_le_rpow
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
        |partialSumHalf (μ : ArithmeticFunction ℝ) k| ≤ C * (k : ℝ) ^ ε) :
    RiemannHypothesis := by
  rw [← Cvs.Operator.allZerosOnLine_iff_rh]
  by_contra hnot
  obtain ⟨ρ, hre⟩ := Cvs.Zeta.GaussKernel.AdmissibleKernel.exists_offLine_of_not_allZerosOnLine hnot
  obtain ⟨hz, h0, h1⟩ := ρ.2
  have hρ1 : (ρ : ℂ) ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hξ : Cvs.Zeta.riemannXi ρ = 0 := (Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta h0 hρ1).2 hz
  obtain ⟨ρ', hξ', hre'⟩ : ∃ ρ' : ℂ, Cvs.Zeta.riemannXi ρ' = 0 ∧ 1 / 2 < ρ'.re := by
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · exact ⟨1 - ρ, by rw [Cvs.Zeta.riemannXi_one_sub]; exact hξ, by simp; linarith⟩
    · exact ⟨ρ, hξ, hgt⟩
  set ε : ℝ := min ((ρ'.re - 1 / 2) / 2) (1 / 4)
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε_half : ε < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε_le : ε ≤ (ρ'.re - 1 / 2) / 2 := min_le_left _ _
  obtain ⟨C, hC, hbound⟩ := h (ε / 2) (by linarith) (by linarith)
  have hle := re_le_half_add_of_abs_partialSumHalf_moebius_le_rpow
    (by linarith) hC hbound (by linarith) hε_half hξ'
  linarith

/-! ### 10. Exact `zetaHalfConst` Extraction from the Smooth Inverse Equation for `partialSumHalf μ` -/

/-! ### 11. Continuous Riesz Mean `rieszMean` and the Exact Real-Quotient Convolution Identity -/

/-- The continuous `1/2`-weighted logarithmic Riesz mean
`∑_{1 ≤ n ≤ ⌊y⌋₊} a(n) n^{-1/2} (log y - log n)` of an arithmetic function `a` at real scale `y`. -/
def rieszMean (a : ArithmeticFunction ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log y - Real.log (n : ℝ))

/-- `rieszMean` preserves subtraction of arithmetic functions. -/
theorem rieszMean_sub (a b : ArithmeticFunction ℝ) (y : ℝ) :
    rieszMean (a - b) y = rieszMean a y - rieszMean b y := by
  unfold rieszMean
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  change (a n - b n) * _ * _ = _
  ring

/-- `rieszMean` preserves scalar multiplication of arithmetic functions. -/
theorem rieszMean_smul (α : ℝ) (a : ArithmeticFunction ℝ) (y : ℝ) :
    rieszMean (α • a) y = α * rieszMean a y := by
  unfold rieszMean
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  change (α * a n) * _ * _ = _
  ring

/-- For `y ≤ 1`, `rieszMean a y = 0`. -/
theorem rieszMean_eq_zero_of_le_one {y : ℝ} (hy : y ≤ 1) (a : ArithmeticFunction ℝ) :
    rieszMean a y = 0 := by
  unfold rieszMean
  rcases lt_or_eq_of_le hy with hlt | rfl
  · have hfl : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hlt
    rw [hfl]
    simp
  · simp

/-- At an integer `1 < c`, `rieszMean a c = log c * ⟪Op c a vac, vac⟫`. -/
theorem rieszMean_natCast_eq_log_mul_inner_Op_vac {c : ℕ} (hc : 1 < c)
    (a : ArithmeticFunction ℝ) :
    rieszMean a (c : ℝ) = Real.log (c : ℝ) * ⟪Op c a vac, vac⟫_ℝ := by
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast hc)
  unfold rieszMean
  rw [Nat.floor_natCast, real_inner_comm, Cvs.WeilForm.WindowVacuumRieszMean.inner_vac_Op hc,
    sum_range_eq_sum_Ico_one (by simp), Finset.mul_sum]
  have hins : Finset.Icc 1 c = insert c (Finset.Ico 1 c) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hins, Finset.sum_insert (by simp), sub_self, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hne : Real.log (c : ℝ) ≠ 0 := hL.ne'
  field_simp

/-- At an integer `1 < c`, `rieszMean a c = ∑_{k=1}^{c-1} logStep k * partialSumHalf a k`. -/
theorem rieszMean_natCast_eq_sum_logStep_mul_partialSumHalf {c : ℕ} (hc : 1 < c)
    (a : ArithmeticFunction ℝ) :
    rieszMean a (c : ℝ) = ∑ k ∈ Finset.Ico 1 c, logStep k * partialSumHalf a k := by
  rw [rieszMean_natCast_eq_log_mul_inner_Op_vac hc,
    log_mul_inner_Op_vac_vac_eq_sum_partialSumHalf hc]

/-- **Continuous Piecewise-Log-Linear Decomposition of `rieszMean a y`**:
for any real `y`, `rieszMean a y = rieszMean a ⌊y⌋₊ + partialSumHalf a ⌊y⌋₊ * (log y - log ⌊y⌋₊)`. -/
theorem rieszMean_eq_rieszMean_floor_add_partialSumHalf_mul_log_sub
    (a : ArithmeticFunction ℝ) (y : ℝ) :
    rieszMean a y
      = rieszMean a (⌊y⌋₊ : ℝ)
        + partialSumHalf a ⌊y⌋₊ * (Real.log y - Real.log (⌊y⌋₊ : ℝ)) := by
  unfold rieszMean partialSumHalf
  rw [Nat.floor_natCast, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- Exact floor-quotient identity `⌊x / n⌋₊ = ⌊x⌋₊ / n` for all real `x` and `n : ℕ`. -/
theorem nat_floor_div_eq_div (x : ℝ) (n : ℕ) :
    ⌊x / (n : ℝ)⌋₊ = ⌊x⌋₊ / n := by
  rcases le_or_gt 0 x with hx | hx
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Nat.floor_eq_iff (div_nonneg hx hn0.le)]
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hn0]
        calc
          ((⌊x⌋₊ / n : ℕ) : ℝ) * (n : ℝ) = (((⌊x⌋₊ / n) * n : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.div_mul_le_self ⌊x⌋₊ n
          _ ≤ x := Nat.floor_le hx
      · rw [div_lt_iff₀ hn0]
        have hlt : ⌊x⌋₊ + 1 ≤ n * (⌊x⌋₊ / n + 1) :=
          Nat.succ_le_of_lt (Nat.lt_mul_div_succ ⌊x⌋₊ hn)
        calc
          x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
          _ = ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ ((n * (⌊x⌋₊ / n + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
          _ = ((⌊x⌋₊ / n : ℕ) + 1 : ℝ) * (n : ℝ) := by push_cast; ring
  · have h1 : x / (n : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx.le (Nat.cast_nonneg n)
    rw [Nat.floor_of_nonpos h1, Nat.floor_of_nonpos hx.le, Nat.zero_div]

/-- **Exact Real-Quotient Dirichlet Convolution Formula for `rieszMean`**:
for any `a, b : ArithmeticFunction ℝ` and `x : ℝ`,
`rieszMean (a * b) x = ∑_{n=1}^{⌊x⌋₊} b(n) n^{-1/2} * rieszMean a (x / n)` with no floor on `x / n`! -/
theorem rieszMean_mul_eq_sum_div (a b : ArithmeticFunction ℝ) (x : ℝ) :
    rieszMean (a * b) x
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          b n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * rieszMean a (x / (n : ℝ)) := by
  rcases le_or_gt x 0 with hx0 | hx0
  · have hfl : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos hx0
    unfold rieszMean
    rw [hfl]
    simp
  · unfold rieszMean
    simp_rw [nat_floor_div_eq_div x, ArithmeticFunction.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij'
      (fun p => ⟨p.2.2, p.2.1⟩)
      (fun q => ⟨q.2 * q.1, (q.2, q.1)⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨j, m, n⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hp ⊢
      obtain ⟨⟨hj1, hjk⟩, hmn, hj0⟩ := hp
      subst hmn
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h => by simp [h] at hj0
      have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h => by simp [h] at hj0
      exact ⟨⟨hn1, le_trans (Nat.le_mul_of_pos_left n hm1) hjk⟩,
        hm1, (Nat.le_div_iff_mul_le hn1).mpr hjk⟩
    · rintro ⟨n, m⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hq ⊢
      obtain ⟨⟨hn1, hnk⟩, hm1, hmk⟩ := hq
      have hmn : m * n ≤ ⌊x⌋₊ := (Nat.le_div_iff_mul_le hn1).mp hmk
      exact ⟨⟨by nlinarith, hmn⟩, trivial, by positivity⟩
    · rintro ⟨j, m, n⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hp
      obtain ⟨_, hmn, _⟩ := hp
      ext <;> simp [hmn]
    · rintro ⟨n, m⟩ _
      rfl
    · rintro ⟨j, m, n⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hp
      obtain ⟨_, rfl, hj0⟩ := hp
      have hm0 : (0 : ℝ) < m := by
        exact_mod_cast Nat.pos_of_ne_zero fun h => by simp [h] at hj0
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero fun h => by simp [h] at hj0
      rw [Nat.cast_mul, Real.mul_rpow hm0.le hn0.le,
        Real.log_mul hm0.ne' hn0.ne', Real.log_div hx0.ne' hn0.ne']
      ring

/-- Commuted real-quotient convolution formula for `rieszMean`:
`rieszMean (a * b) x = ∑_{m=1}^{⌊x⌋₊} a(m) m^{-1/2} * rieszMean b (x / m)`. -/
theorem rieszMean_mul_eq_sum_div_left (a b : ArithmeticFunction ℝ) (x : ℝ) :
    rieszMean (a * b) x
      = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          a m * (m : ℝ) ^ (-(1 / 2 : ℝ)) * rieszMean b (x / (m : ℝ)) := by
  rw [mul_comm, rieszMean_mul_eq_sum_div]

/-- Continuous fractional-step lower bound: for `0 < u ≤ v`,
`2 * √u * (log v - log u) ≤ 4 * (√v - √u)`. -/
theorem two_mul_sqrt_mul_log_sub_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    2 * Real.sqrt u * (Real.log v - Real.log u)
      ≤ 4 * (Real.sqrt v - Real.sqrt u) := by
  have hv : 0 < v := hu.trans_le huv
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsv hsu)
  have hlog_eq :
      Real.log v - Real.log u = 2 * Real.log (Real.sqrt v / Real.sqrt u) := by
    rw [Real.log_div hsv.ne' hsu.ne', Real.log_sqrt hv.le, Real.log_sqrt hu.le]
    ring
  rw [hlog_eq]
  have hmul :
      2 * Real.sqrt u * (2 * Real.log (Real.sqrt v / Real.sqrt u))
        ≤ 4 * Real.sqrt u * (Real.sqrt v / Real.sqrt u - 1) := by
    nlinarith [hsu.le]
  have hsimpl :
      4 * Real.sqrt u * (Real.sqrt v / Real.sqrt u - 1)
        = 4 * (Real.sqrt v - Real.sqrt u) := by
    have hne : Real.sqrt u ≠ 0 := hsu.ne'
    field_simp
  linarith

/-- Continuous fractional-step upper bound: for `0 < u ≤ v`,
`4 * (√v - √u) ≤ 2 * √v * (log v - log u)`. -/
theorem four_mul_sqrt_sub_le_two_mul_sqrt_mul_log_sub {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    4 * (Real.sqrt v - Real.sqrt u)
      ≤ 2 * Real.sqrt v * (Real.log v - Real.log u) := by
  have hv : 0 < v := hu.trans_le huv
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsu hsv)
  have hlog_eq :
      Real.log v - Real.log u = -2 * Real.log (Real.sqrt u / Real.sqrt v) := by
    rw [Real.log_div hsu.ne' hsv.ne', Real.log_sqrt hu.le, Real.log_sqrt hv.le]
    ring
  rw [hlog_eq]
  have hmul :
      4 * Real.sqrt v * (1 - Real.sqrt u / Real.sqrt v)
        ≤ 2 * Real.sqrt v * (-2 * Real.log (Real.sqrt u / Real.sqrt v)) := by
    nlinarith [hsv.le]
  have hsimpl :
      4 * Real.sqrt v * (1 - Real.sqrt u / Real.sqrt v)
        = 4 * (Real.sqrt v - Real.sqrt u) := by
    have hne : Real.sqrt v ≠ 0 := hsv.ne'
    field_simp
  linarith

/-! ### 12. The `O(y^{-1/2})` Continuous Expansion of `rieszMean ζ y` and Exact `√x` Factorization -/

/-- The unshifted integer Rieszzeta approximation `rieszMean ζ k - 4 * √k - zetaHalfConst * log k`. -/
def rieszZetaBase (k : ℕ) : ℝ :=
  rieszMean (ζ : ArithmeticFunction ℝ) (k : ℝ)
    - 4 * Real.sqrt (k : ℝ)
    - zetaHalfConst * Real.log (k : ℝ)

/-- The integer step discrepancy of `rieszZetaBase`:
`(partialSumHalf ζ k - zetaHalfConst) * logStep k - 4 * (√(k + 1) - √k)`. -/
def rieszZetaStep (k : ℕ) : ℝ :=
  (partialSumHalf (ζ : ArithmeticFunction ℝ) k - zetaHalfConst) * logStep k
    - 4 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ))

/-- For `1 ≤ k`, `rieszMean ζ (k + 1) - rieszMean ζ k = logStep k * partialSumHalf ζ k`. -/
theorem rieszMean_natCast_succ_sub {k : ℕ} (hk : 1 ≤ k) :
    rieszMean (ζ : ArithmeticFunction ℝ) ((k + 1 : ℕ) : ℝ)
        - rieszMean (ζ : ArithmeticFunction ℝ) (k : ℝ)
      = logStep k * partialSumHalf (ζ : ArithmeticFunction ℝ) k := by
  have hk1 : 1 < k + 1 := by omega
  rw [rieszMean_natCast_eq_sum_logStep_mul_partialSumHalf hk1]
  rcases eq_or_lt_of_le hk with rfl | hgt
  · rw [Nat.cast_one, rieszMean_eq_zero_of_le_one le_rfl, sub_zero]
    simp
  · rw [rieszMean_natCast_eq_sum_logStep_mul_partialSumHalf hgt,
      Finset.sum_Ico_succ_top hk]
    ring

/-- Exact step identity `rieszZetaBase (k + 1) - rieszZetaBase k = rieszZetaStep k` (`1 ≤ k`). -/
theorem rieszZetaBase_succ_sub {k : ℕ} (hk : 1 ≤ k) :
    rieszZetaBase (k + 1) - rieszZetaBase k = rieszZetaStep k := by
  have hstep := rieszMean_natCast_succ_sub hk
  unfold rieszZetaBase rieszZetaStep
  unfold logStep at hstep ⊢
  linarith

/-- Lower bound on `rieszZetaStep k` (`1 ≤ k`):
`-2 * (√(k + 1) - √k) * logStep k ≤ rieszZetaStep k`. -/
theorem neg_two_mul_sqrt_sub_mul_logStep_le_rieszZetaStep {k : ℕ} (hk : 1 ≤ k) :
    -2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) * logStep k
      ≤ rieszZetaStep k := by
  have hls : 0 ≤ logStep k := logStep_nonneg hk
  have hz := two_mul_sqrt_add_zetaHalfConst_le_partialSumHalf_zeta k
  have h1 :
      2 * Real.sqrt (k : ℝ) * logStep k
        ≤ (partialSumHalf (ζ : ArithmeticFunction ℝ) k - zetaHalfConst) * logStep k :=
    mul_le_mul_of_nonneg_right (by linarith) hls
  have h2 := four_mul_sqrt_succ_sub_sqrt_le_two_mul_sqrt_succ_mul_logStep hk
  unfold rieszZetaStep
  linarith

/-- Upper bound on `rieszZetaStep k` (`1 ≤ k`):
`rieszZetaStep k ≤ 2 * (√(k + 1) - √k) * logStep k`. -/
theorem rieszZetaStep_le_two_mul_sqrt_sub_mul_logStep {k : ℕ} (hk : 1 ≤ k) :
    rieszZetaStep k
      ≤ 2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) * logStep k := by
  have hls : 0 ≤ logStep k := logStep_nonneg hk
  have hz := partialSumHalf_zeta_le_two_mul_sqrt_succ_add_zetaHalfConst k
  have h1 :
      (partialSumHalf (ζ : ArithmeticFunction ℝ) k - zetaHalfConst) * logStep k
        ≤ 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) * logStep k :=
    mul_le_mul_of_nonneg_right (by linarith) hls
  have h2 := two_mul_sqrt_mul_logStep_le hk
  unfold rieszZetaStep
  linarith

/-- For `1 ≤ k`, `√(k + 1) ≤ 2 * √k`. -/
theorem sqrt_succ_le_two_mul_sqrt {k : ℕ} (hk : 1 ≤ k) :
    Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (k : ℝ) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h4 : ((k + 1 : ℕ) : ℝ) ≤ (2 * Real.sqrt (k : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hk0]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    linarith
  rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.sqrt (k : ℝ))]
  exact Real.sqrt_le_sqrt h4

/-- Telescoping reciprocal-square-root identity: for `0 < u` and `0 < v`,
`1 / u - 1 / v = (v - u) / (u * v)`. -/
theorem one_div_sub_one_div {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    1 / u - 1 / v = (v - u) / (u * v) := by
  field_simp

/-- **Exact Telescoping Majorant for `2 * (√(k + 1) - √k) * logStep k`**:
for every `1 ≤ k`, `2 * (√(k + 1) - √k) * logStep k ≤ 4 * (1 / √k - 1 / √(k + 1))`. -/
theorem two_mul_sqrt_sub_mul_logStep_le_four_mul_inv_sqrt_sub {k : ℕ} (hk : 1 ≤ k) :
    2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) * logStep k
      ≤ 4 * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  have hsq0 : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hsq1 : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hk1
  have hle : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
  have hprod : Real.sqrt (k : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
    calc
      Real.sqrt (k : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ)
        ≤ Real.sqrt (k : ℝ) * (2 * Real.sqrt (k : ℝ)) :=
        mul_le_mul_of_nonneg_left (sqrt_succ_le_two_mul_sqrt hk) hsq0.le
      _ = 2 * Real.sqrt (k : ℝ) ^ 2 := by ring
      _ = 2 * (k : ℝ) := by rw [Real.sq_sqrt hk0.le]
  have hinv :
      (k : ℝ)⁻¹ ≤ 2 / (Real.sqrt (k : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hk0 (mul_pos hsq0 hsq1)]
    linarith
  have hls : logStep k ≤ 2 / (Real.sqrt (k : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ)) :=
    (logStep_le_inv hk).trans hinv
  have hmul :=
    mul_le_mul_of_nonneg_left hls (by linarith : 0 ≤ 2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)))
  rw [one_div_sub_one_div hsq0.ne' hsq1.ne']
  have hring :
      2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ))
          * (2 / (Real.sqrt (k : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ)))
        = 4 * ((Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ))
            / (Real.sqrt (k : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ))) := by ring
  linarith

/-- Monotone lower sequence for `rieszZetaConst`: `rieszZetaBase (n + 1) - 4 / √(n + 1)`. -/
def lowerRieszZetaConstSeq (n : ℕ) : ℝ :=
  rieszZetaBase (n + 1) - 4 * (1 / Real.sqrt ((n + 1 : ℕ) : ℝ))

/-- Antitone upper sequence for `rieszZetaConst`: `rieszZetaBase (n + 1) + 4 / √(n + 1)`. -/
def upperRieszZetaConstSeq (n : ℕ) : ℝ :=
  rieszZetaBase (n + 1) + 4 * (1 / Real.sqrt ((n + 1 : ℕ) : ℝ))

/-- `lowerRieszZetaConstSeq` is monotonically increasing on `ℕ`. -/
theorem lowerRieszZetaConstSeq_le_succ (n : ℕ) :
    lowerRieszZetaConstSeq n ≤ lowerRieszZetaConstSeq (n + 1) := by
  have hn1 : 1 ≤ n + 1 := Nat.succ_pos n
  have hsub := rieszZetaBase_succ_sub hn1
  have hlow := neg_two_mul_sqrt_sub_mul_logStep_le_rieszZetaStep hn1
  have hmaj := two_mul_sqrt_sub_mul_logStep_le_four_mul_inv_sqrt_sub hn1
  unfold lowerRieszZetaConstSeq
  linarith

theorem lowerRieszZetaConstSeq_mono : Monotone lowerRieszZetaConstSeq :=
  monotone_nat_of_le_succ lowerRieszZetaConstSeq_le_succ

/-- `upperRieszZetaConstSeq` is antitone on `ℕ`. -/
theorem upperRieszZetaConstSeq_succ_le (n : ℕ) :
    upperRieszZetaConstSeq (n + 1) ≤ upperRieszZetaConstSeq n := by
  have hn1 : 1 ≤ n + 1 := Nat.succ_pos n
  have hsub := rieszZetaBase_succ_sub hn1
  have hup := rieszZetaStep_le_two_mul_sqrt_sub_mul_logStep hn1
  have hmaj := two_mul_sqrt_sub_mul_logStep_le_four_mul_inv_sqrt_sub hn1
  unfold upperRieszZetaConstSeq
  linarith

theorem upperRieszZetaConstSeq_anti : Antitone upperRieszZetaConstSeq :=
  antitone_nat_of_succ_le upperRieszZetaConstSeq_succ_le

/-- Every term of `lowerRieszZetaConstSeq` is bounded above by every term of `upperRieszZetaConstSeq`. -/
theorem lowerRieszZetaConstSeq_le_upperRieszZetaConstSeq (m n : ℕ) :
    lowerRieszZetaConstSeq m ≤ upperRieszZetaConstSeq n := by
  have h1 : lowerRieszZetaConstSeq m ≤ lowerRieszZetaConstSeq (max m n) :=
    lowerRieszZetaConstSeq_mono (le_max_left m n)
  have h2 : lowerRieszZetaConstSeq (max m n) ≤ upperRieszZetaConstSeq (max m n) := by
    unfold lowerRieszZetaConstSeq upperRieszZetaConstSeq
    have hpos : 0 ≤ 4 * (1 / Real.sqrt ((max m n + 1 : ℕ) : ℝ)) := by positivity
    linarith
  have h3 : upperRieszZetaConstSeq (max m n) ≤ upperRieszZetaConstSeq n :=
    upperRieszZetaConstSeq_anti (le_max_right m n)
  exact h1.trans (h2.trans h3)

/-- `lowerRieszZetaConstSeq` is bounded above. -/
theorem bddAbove_lowerRieszZetaConstSeq : BddAbove (Set.range lowerRieszZetaConstSeq) := by
  refine ⟨upperRieszZetaConstSeq 0, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact lowerRieszZetaConstSeq_le_upperRieszZetaConstSeq m 0

/-- The constant term `C_ζ = sup_n (rieszZetaBase (n + 1) - 4 / √(n + 1))` in the continuous Riesz
expansion `rieszMean ζ y = 4 * √y + zetaHalfConst * log y + rieszZetaConst + O(y^{-1/2})`. -/
def rieszZetaConst : ℝ :=
  ⨆ n : ℕ, lowerRieszZetaConstSeq n

/-- For every `n : ℕ`, `lowerRieszZetaConstSeq n ≤ rieszZetaConst ≤ upperRieszZetaConstSeq n`. -/
theorem lowerRieszZetaConstSeq_le_rieszZetaConst (n : ℕ) :
    lowerRieszZetaConstSeq n ≤ rieszZetaConst :=
  le_ciSup bddAbove_lowerRieszZetaConstSeq n

theorem rieszZetaConst_le_upperRieszZetaConstSeq (n : ℕ) :
    rieszZetaConst ≤ upperRieszZetaConstSeq n :=
  ciSup_le fun m => lowerRieszZetaConstSeq_le_upperRieszZetaConstSeq m n

/-- **Two-Sided `4 / √k` Approximation of `rieszMean ζ k` at Every Integer `1 ≤ k`**:
`|rieszMean ζ k - (4 * √k + zetaHalfConst * log k + rieszZetaConst)| ≤ 4 / √k`. -/
theorem abs_rieszZetaBase_sub_rieszZetaConst_le {k : ℕ} (hk : 1 ≤ k) :
    |rieszZetaBase k - rieszZetaConst| ≤ 4 / Real.sqrt (k : ℝ) := by
  have hk_eq : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  have hlow := lowerRieszZetaConstSeq_le_rieszZetaConst (k - 1)
  have hup := rieszZetaConst_le_upperRieszZetaConstSeq (k - 1)
  unfold lowerRieszZetaConstSeq at hlow
  unfold upperRieszZetaConstSeq at hup
  rw [← hk_eq] at hlow hup
  have hdiv : 4 * (1 / Real.sqrt (k : ℝ)) = 4 / Real.sqrt (k : ℝ) := by ring
  rw [abs_le]
  constructor <;> linarith

/-- The continuous Riesz remainder `rieszMean ζ y - (4 * √y + zetaHalfConst * log y + rieszZetaConst)`. -/
def rieszZetaRem (y : ℝ) : ℝ :=
  rieszMean (ζ : ArithmeticFunction ℝ) y
    - (4 * Real.sqrt y + zetaHalfConst * Real.log y + rieszZetaConst)

/-- Fractional-step identity for `rieszZetaRem y` (`1 ≤ y`):
`rieszZetaRem y = (rieszZetaBase ⌊y⌋₊ - rieszZetaConst) + ((partialSumHalf ζ ⌊y⌋₊ - zetaHalfConst) * (log y - log ⌊y⌋₊) - 4 * (√y - √⌊y⌋₊))`. -/
theorem rieszZetaRem_eq_floor_add_frac (y : ℝ) :
    rieszZetaRem y
      = (rieszZetaBase ⌊y⌋₊ - rieszZetaConst)
        + ((partialSumHalf (ζ : ArithmeticFunction ℝ) ⌊y⌋₊ - zetaHalfConst)
            * (Real.log y - Real.log (⌊y⌋₊ : ℝ))
          - 4 * (Real.sqrt y - Real.sqrt (⌊y⌋₊ : ℝ))) := by
  unfold rieszZetaRem rieszZetaBase
  rw [rieszMean_eq_rieszMean_floor_add_partialSumHalf_mul_log_sub]
  ring

/-- **All-Scale `O(y^{-1/2})` Bound on `rieszZetaRem y` for Every Real `1 ≤ y`**:
`|rieszZetaRem y| ≤ 5 / √⌊y⌋₊ ≤ 10 / √y`. -/
theorem abs_rieszZetaRem_le_five_div_sqrt_floor {y : ℝ} (hy : 1 ≤ y) :
    |rieszZetaRem y| ≤ 5 / Real.sqrt (⌊y⌋₊ : ℝ) := by
  set N := ⌊y⌋₊
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff y).mpr hy
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hy_lt : y < ((N + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one y
  have hlog_nonneg : 0 ≤ Real.log y - Real.log (N : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hN0 hNy)
  have hlog_le : Real.log y - Real.log (N : ℝ) ≤ logStep N := by
    unfold logStep
    linarith [Real.log_le_log (by linarith : 0 < y) hy_lt.le]
  have hz_low := two_mul_sqrt_add_zetaHalfConst_le_partialSumHalf_zeta N
  have hz_up := partialSumHalf_zeta_le_two_mul_sqrt_succ_add_zetaHalfConst N
  have hp_low :
      2 * Real.sqrt (N : ℝ) * (Real.log y - Real.log (N : ℝ))
        ≤ (partialSumHalf (ζ : ArithmeticFunction ℝ) N - zetaHalfConst)
            * (Real.log y - Real.log (N : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hlog_nonneg
  have hp_up :
      (partialSumHalf (ζ : ArithmeticFunction ℝ) N - zetaHalfConst)
          * (Real.log y - Real.log (N : ℝ))
        ≤ 2 * Real.sqrt ((N + 1 : ℕ) : ℝ) * (Real.log y - Real.log (N : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hlog_nonneg
  have hs_low := two_mul_sqrt_mul_log_sub_le hN0 hNy
  have hs_up :
      4 * (Real.sqrt y - Real.sqrt (N : ℝ))
        ≤ 2 * Real.sqrt ((N + 1 : ℕ) : ℝ) * (Real.log y - Real.log (N : ℝ)) := by
    have h1 := four_mul_sqrt_sub_le_two_mul_sqrt_mul_log_sub hN0 hNy
    have h2 : Real.sqrt y ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt hy_lt.le
    nlinarith
  have hfrac_abs :
      |(partialSumHalf (ζ : ArithmeticFunction ℝ) N - zetaHalfConst)
          * (Real.log y - Real.log (N : ℝ))
        - 4 * (Real.sqrt y - Real.sqrt (N : ℝ))|
        ≤ 1 / Real.sqrt (N : ℝ) := by
    have hdiff_nonneg : 0 ≤ 2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) := by
      have := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ N : (N : ℝ) ≤ (N + 1 : ℕ))
      linarith
    have hstep_le :
        2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) * (Real.log y - Real.log (N : ℝ))
          ≤ 2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) * logStep N :=
      mul_le_mul_of_nonneg_left hlog_le hdiff_nonneg
    have hsub_sqrt := sqrt_sub_sqrt_le_div_two_sqrt hN0
      (by exact_mod_cast Nat.le_succ N : (N : ℝ) ≤ (N + 1 : ℕ))
    have hcast : ((N + 1 : ℕ) : ℝ) - (N : ℝ) = 1 := by push_cast; ring
    rw [hcast] at hsub_sqrt
    have hls_le : logStep N ≤ 1 := (logStep_le_inv hN1).trans (inv_le_one_of_one_le₀ (by exact_mod_cast hN1))
    have hls0 : 0 ≤ logStep N := logStep_nonneg hN1
    have hdiv_eq : 2 * (1 / (2 * Real.sqrt (N : ℝ))) = 1 / Real.sqrt (N : ℝ) := by ring
    have hprod_le :
        2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) * logStep N
          ≤ 1 / Real.sqrt (N : ℝ) := by
      nlinarith
    rw [abs_le]
    constructor <;> linarith
  have hbase := abs_rieszZetaBase_sub_rieszZetaConst_le hN1
  rw [rieszZetaRem_eq_floor_add_frac y]
  have htri := abs_add_le (rieszZetaBase N - rieszZetaConst)
    ((partialSumHalf (ζ : ArithmeticFunction ℝ) N - zetaHalfConst)
        * (Real.log y - Real.log (N : ℝ))
      - 4 * (Real.sqrt y - Real.sqrt (N : ℝ)))
  have hsum : 4 / Real.sqrt (N : ℝ) + 1 / Real.sqrt (N : ℝ) = 5 / Real.sqrt (N : ℝ) := by ring
  linarith

/-- For every real `1 ≤ y`, `|rieszZetaRem y| ≤ 10 / √y`. -/
theorem abs_rieszZetaRem_le_ten_div_sqrt {y : ℝ} (hy : 1 ≤ y) :
    |rieszZetaRem y| ≤ 10 / Real.sqrt y := by
  have hN1 : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff y).mpr hy
  have hN0 : (0 : ℝ) < ⌊y⌋₊ := by exact_mod_cast hN1
  have hy_le : y ≤ 2 * (⌊y⌋₊ : ℝ) := by
    have hlt := Nat.lt_floor_add_one y
    have h1 : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hN1
    linarith
  have hsq : Real.sqrt y ≤ 2 * Real.sqrt (⌊y⌋₊ : ℝ) := by
    have h4 : y ≤ (2 * Real.sqrt (⌊y⌋₊ : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hN0.le]
      linarith
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.sqrt (⌊y⌋₊ : ℝ))]
    exact Real.sqrt_le_sqrt h4
  have hdiv : 5 / Real.sqrt (⌊y⌋₊ : ℝ) ≤ 10 / Real.sqrt y := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hN0) (Real.sqrt_pos.mpr (by linarith))]
    linarith
  exact (abs_rieszZetaRem_le_five_div_sqrt_floor hy).trans hdiv

/-- For every `m : ℕ`, `|(μ m : ℝ)| ≤ 1`. -/
theorem abs_moebius_le_one (m : ℕ) : |(μ m : ℝ)| ≤ 1 := by
  by_cases hm : Squarefree m
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hm]
    push_cast
    rw [abs_pow, abs_neg, abs_one, one_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hm, Int.cast_zero, abs_zero]
    norm_num

/-! ### 13. Real-Quotient Zeta Remainder `zetaRealRem` and Exact Pole-Cancelled Riesz–Zeta Identity -/

/-- The real-variable Euler–Maclaurin remainder `partialSumHalf ζ ⌊y⌋₊ - 2 * √y - zetaHalfConst`,
which replaces `2 * √⌊y⌋₊` by the unfloored `2 * √y` so `√x` factors out at `y = x / m`. -/
def zetaRealRem (y : ℝ) : ℝ :=
  partialSumHalf (ζ : ArithmeticFunction ℝ) ⌊y⌋₊ - 2 * Real.sqrt y - zetaHalfConst

/-! ### 14. Universal Kernel Riesz Transform `kernelRiesz` and Pole-Cancelled Quadratic Riesz Kernel -/

/-! ### 15. Vacuum Riesz–Inner-Product Bridge & Zeta–Möbius Resolvent Norm Identities on `L²(𝕋)` -/

/-- For every `a : ArithmeticFunction ℝ` and `1 < c`, the continuous Riesz mean `rieszMean a c`
at integer scale `c` equals `log c * ⟪Op c a vac, vac⟫` on `L²(𝕋)`. -/
theorem rieszMean_nat_eq_log_mul_inner_Op_vac {c : ℕ} (hc : 1 < c)
    (a : ArithmeticFunction ℝ) :
    rieszMean a (c : ℝ) = Real.log c * ⟪Op c a vac, vac⟫_ℝ := by
  have hL : (0 : ℝ) < Real.log c := Real.log_pos (by exact_mod_cast hc)
  have hLne : Real.log (c : ℝ) ≠ 0 := hL.ne'
  rw [real_inner_comm, Cvs.WeilForm.WindowVacuumRieszMean.inner_vac_Op hc, Finset.mul_sum]
  unfold rieszMean
  rw [Nat.floor_natCast]
  have hsub : Finset.Icc 1 c ⊆ Finset.range (c + 1) := fun n hn =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
  have h1 :
      ∑ n ∈ Finset.Icc 1 c,
          a n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (c : ℝ) - Real.log (n : ℝ))
        = ∑ n ∈ Finset.range (c + 1),
            a n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (c : ℝ) - Real.log (n : ℝ)) := by
    refine Finset.sum_subset hsub fun n hn hnI => ?_
    have hn0 : n = 0 := by
      have hlt := Finset.mem_range.mp hn
      by_contra hne
      exact hnI (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    subst hn0
    simp
  rw [h1, Finset.sum_range_succ, sub_self, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hlog : (1 - Real.log (n : ℝ) / Real.log (c : ℝ)) * Real.log (c : ℝ)
      = Real.log (c : ℝ) - Real.log (n : ℝ) := by
    field_simp
  calc a n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (c : ℝ) - Real.log (n : ℝ))
      = a n * (n : ℝ) ^ (-(1 / 2 : ℝ))
          * ((1 - Real.log (n : ℝ) / Real.log (c : ℝ)) * Real.log (c : ℝ)) := by
        rw [hlog]
    _ = Real.log (c : ℝ)
          * (a n * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.log (n : ℝ) / Real.log (c : ℝ)))) := by
        ring

/-! ### 16. The Spectrum of the Primes & The 3-Cut (Three-Distance) Capacity Partition on `L²(𝕋)` -/

/-- Single-shift Path-Law Three-Distance difference form for `rho c n` on `L²(𝕋)`. -/
def shiftSchurDiff (c n : ℕ) (f : L2) : ℝ :=
  (n : ℝ) ^ (-(1 / 2 : ℝ))
    * ((∫ x, Cvs.WeilForm.PrimeOperatorPathLawDeficit.schurDiffSq ((rot c n : ℝ≥0) : ℝ) f x)
      + ∫ x, Cvs.WeilForm.PrimeOperatorPathLawDeficit.shortChainDefect ((rot c n : ℝ≥0) : ℝ) f x)

/-- Single-shift Path-Law Three-Distance companion (plus) form for `rho c n` on `L²(𝕋)`. -/
def shiftSchurPlus (c n : ℕ) (f : L2) : ℝ :=
  (n : ℝ) ^ (-(1 / 2 : ℝ))
    * ((∫ x, Cvs.WeilForm.PrimeOperatorPathLawDeficit.schurPlusSq ((rot c n : ℝ≥0) : ℝ) f x)
      + ∫ x, Cvs.WeilForm.PrimeOperatorPathLawDeficit.shortChainDefect ((rot c n : ℝ≥0) : ℝ) f x)

/-- `shiftSchurDiff c n f` is nonnegative for `1 < c` and `1 < n`. -/
theorem shiftSchurDiff_nonneg {c n : ℕ} (hc : 1 < c) (hn : 1 < n) (f : L2) :
    0 ≤ shiftSchurDiff c n f := by
  unfold shiftSchurDiff
  refine mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (add_nonneg (integral_nonneg (Cvs.WeilForm.PrimeOperatorPathLawDeficit.schurDiffSq_nonneg _ f))
      (integral_nonneg (Cvs.WeilForm.PrimeOperatorPathLawDeficit.shortChainDefect_nonneg
        (Cvs.WeilForm.PrimeOperatorPathLawDeficit.coe_rot_pos hc hn) f)))

/-- `shiftSchurPlus c n f` is nonnegative for `1 < c` and `1 < n`. -/
theorem shiftSchurPlus_nonneg {c n : ℕ} (hc : 1 < c) (hn : 1 < n) (f : L2) :
    0 ≤ shiftSchurPlus c n f := by
  unfold shiftSchurPlus
  refine mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (add_nonneg (integral_nonneg (Cvs.WeilForm.PrimeOperatorPathLawDeficit.schurPlusSq_nonneg _ f))
      (integral_nonneg (Cvs.WeilForm.PrimeOperatorPathLawDeficit.shortChainDefect_nonneg
        (Cvs.WeilForm.PrimeOperatorPathLawDeficit.coe_rot_pos hc hn) f)))

/-- For any `c, n : ℕ` and `f : L²(𝕋)`,
`2 * ⟪rho c n f, f⟫ = (n : ℝ)^(-1/2) * ⟪(S (rot c n) + (S (rot c n))*) f, f⟫`. -/
theorem two_inner_rho_eq_inner_W (c n : ℕ) (f : L2) :
    2 * ⟪rho c n f, f⟫_ℝ
      = (n : ℝ) ^ (-(1 / 2 : ℝ))
        * ⟪(S ((rot c n : ℝ≥0) : ℝ)
            + ContinuousLinearMap.adjoint (S ((rot c n : ℝ≥0) : ℝ))) f, f⟫_ℝ := by
  simp only [rho, Snn, _root_.smul_apply, _root_.add_apply,
    inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm (S ((rot c n : ℝ≥0) : ℝ) f) f]
  ring

/-- **Single-Shift Three-Distance Path-Law Deficit Identity**: for `1 < c`, `1 < n`, and `f : L²(𝕋)`,
`2 * ⟪rho c n f, f⟫ = n^(-1/2) * chebFactor (cap (log c) (log n)) * ‖f‖² - shiftSchurDiff c n f`. -/
theorem two_inner_rho_eq_chebFactor_sub_shiftSchurDiff {c n : ℕ} (hc : 1 < c) (hn : 1 < n)
    (f : L2) :
    2 * ⟪rho c n f, f⟫_ℝ
      = (n : ℝ) ^ (-(1 / 2 : ℝ))
          * Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n)) * ‖f‖ ^ 2
        - shiftSchurDiff c n f := by
  have hβ := Cvs.WeilForm.PrimeOperatorPathLawDeficit.coe_rot_pos hc hn
  have hdef := Cvs.WeilForm.PrimeOperatorPathLawDeficit.chebFactor_norm_sq_sub_inner_W hβ f
  rw [Cvs.WeilForm.PrimeOperatorPathLawDeficit.cap_one_rot_eq hc hn] at hdef
  rw [two_inner_rho_eq_inner_W]
  unfold shiftSchurDiff
  linear_combination -(n : ℝ) ^ (-(1 / 2 : ℝ)) * hdef

/-- **Single-Shift Three-Distance Path-Law Companion Identity**: for `1 < c`, `1 < n`, and `f : L²(𝕋)`,
`2 * ⟪rho c n f, f⟫ = shiftSchurPlus c n f - n^(-1/2) * chebFactor (cap (log c) (log n)) * ‖f‖²`. -/
theorem two_inner_rho_eq_shiftSchurPlus_sub_chebFactor {c n : ℕ} (hc : 1 < c) (hn : 1 < n)
    (f : L2) :
    2 * ⟪rho c n f, f⟫_ℝ
      = shiftSchurPlus c n f
        - (n : ℝ) ^ (-(1 / 2 : ℝ))
          * Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n)) * ‖f‖ ^ 2 := by
  have hβ := Cvs.WeilForm.PrimeOperatorPathLawDeficit.coe_rot_pos hc hn
  have hdef := Cvs.WeilForm.PrimeOperatorPathLawDeficit.chebFactor_norm_sq_add_inner_W hβ f
  rw [Cvs.WeilForm.PrimeOperatorPathLawDeficit.cap_one_rot_eq hc hn] at hdef
  rw [two_inner_rho_eq_inner_W]
  unfold shiftSchurPlus
  linear_combination (n : ℝ) ^ (-(1 / 2 : ℝ)) * hdef

/-- **Two-Sided Single-Shift Chebyshev Bound**: for `1 < c`, `1 < n`, and `f : L²(𝕋)`,
`|2 * ⟪rho c n f, f⟫| ≤ n^(-1/2) * chebFactor (cap (log c) (log n)) * ‖f‖²`. -/
theorem abs_two_inner_rho_le_chebFactor {c n : ℕ} (hc : 1 < c) (hn : 1 < n) (f : L2) :
    |2 * ⟪rho c n f, f⟫_ℝ|
      ≤ (n : ℝ) ^ (-(1 / 2 : ℝ))
        * Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n)) * ‖f‖ ^ 2 := by
  rw [abs_le]
  constructor
  · linarith [two_inner_rho_eq_shiftSchurPlus_sub_chebFactor hc hn f,
      shiftSchurPlus_nonneg hc hn f]
  · linarith [two_inner_rho_eq_chebFactor_sub_shiftSchurDiff hc hn f,
      shiftSchurDiff_nonneg hc hn f]

/-- **The Dimer Cut (`√c ≤ n < c`)**: for `1 < c`, `n < c`, and `c ≤ n²`, the Steinhaus capacity
`cap (log c) (log n)` equals `2`. -/
theorem cap_log_eq_two_of_dimer {c n : ℕ} (hc : 1 < c) (hnc : n < c) (hcn2 : c ≤ n ^ 2) :
    cap (Real.log c) (Real.log n) = 2 := by
  have hn1 : 1 < n := by
    by_contra hle
    have hn01 : n ≤ 1 := not_lt.mp hle
    have hsq : n ^ 2 ≤ 1 := by nlinarith
    omega
  have hlc : 0 < Real.log c := Cvs.PrimeOperator.log_pos_of_one_lt hc
  have hln : 0 < Real.log n := Cvs.Operator.log_pos_of_one_lt hn1
  have hlt : Real.log n < Real.log c :=
    Real.log_lt_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnc)
  have hle2 : Real.log c ≤ 2 * Real.log n := by
    have hlog : Real.log (c : ℝ) ≤ Real.log ((n ^ 2 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < c)) (by exact_mod_cast hcn2)
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hlog
    exact hlog
  unfold cap
  rw [Nat.ceil_eq_iff (by norm_num)]
  push_cast
  exact ⟨(one_lt_div hln).mpr hlt, (div_le_iff₀ hln).mpr hle2⟩

/-- On the dimer cut (`1 < c`, `n < c`, `c ≤ n²`), the Chebyshev factor is `1` (halving the trivial bound `2`). -/
theorem chebFactor_cap_eq_one_of_dimer {c n : ℕ} (hc : 1 < c) (hnc : n < c) (hcn2 : c ≤ n ^ 2) :
    Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n)) = 1 := by
  rw [cap_log_eq_two_of_dimer hc hnc hcn2, Cvs.Operator.chebFactor_two]

/-- **Dimer-Cut Shift Bound on `L²(𝕋)`**: for every `n` in the dimer shell `c ≤ n²`, `n < c`,
`|2 * ⟪rho c n f, f⟫| ≤ n^(-1/2) * ‖f‖²`. -/
theorem abs_two_inner_rho_le_one_of_dimer {c n : ℕ} (hc : 1 < c) (hnc : n < c)
    (hcn2 : c ≤ n ^ 2) (f : L2) :
    |2 * ⟪rho c n f, f⟫_ℝ| ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * ‖f‖ ^ 2 := by
  have hn1 : 1 < n := by
    by_contra hle
    have hn01 : n ≤ 1 := not_lt.mp hle
    have hsq : n ^ 2 ≤ 1 := by nlinarith
    omega
  have h := abs_two_inner_rho_le_chebFactor hc hn1 f
  rwa [chebFactor_cap_eq_one_of_dimer hc hnc hcn2, mul_one] at h

/-! ### 17. Concentric-Disc Three-Circles Theorem via Iterated `dslope` -/

end Cvs.Zeta.WingCancellationLog
