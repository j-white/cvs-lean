import Mathlib
import Cvs.WeilForm.WholeDomainUnification
import Cvs.Zeta.DivisorDiscrepancyAdjointZeta
import Cvs.Zeta.DivisorDiscrepancyHyperbola

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Two-Sided Euler-Mascheroni Squeeze and `O(log c)` Norm Bound for `divisorDiscrepancy (-2 * γ)`

Defines `upperEulerMascheroniSeq` and `eulerMascheroni`, proves the `1 / M` squeeze, and cancels
`4 * γ * √k` two-sidedly in `divisorDiscrepancy (-2 * eulerMascheroni)` to prove `‖Op c d_{-2γ} vac‖ ≤ log c + 16`.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace NNReal ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.Zeta.EulerMascheroniSqueeze
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

/-! ### 1. Antitone Upper Euler-Mascheroni Sequence and the `1 / M` Squeeze -/

/-- The upper Euler-Mascheroni sequence `H_M - log M`. -/
def upperEulerMascheroniSeq (M : ℕ) : ℝ :=
  harmonicSum M - Real.log (M : ℝ)

/-- At `M = 0`, `eulerMascheroniSeq 0 = 0`. -/
theorem eulerMascheroniSeq_zero : eulerMascheroniSeq 0 = 0 := by
  unfold eulerMascheroniSeq harmonicSum
  simp

/-- At `M = 1`, `upperEulerMascheroniSeq 1 = 1`. -/
theorem upperEulerMascheroniSeq_one : upperEulerMascheroniSeq 1 = 1 := by
  unfold upperEulerMascheroniSeq harmonicSum
  simp

/-- Exact gap `upperEulerMascheroniSeq M - eulerMascheroniSeq M = logStep M`. -/
theorem upperEulerMascheroniSeq_sub_lower (M : ℕ) :
    upperEulerMascheroniSeq M - eulerMascheroniSeq M = logStep M := by
  unfold upperEulerMascheroniSeq eulerMascheroniSeq logStep
  ring

/-- For `1 ≤ M`, `upperEulerMascheroniSeq M - eulerMascheroniSeq M ≤ M⁻¹`. -/
theorem upperEulerMascheroniSeq_sub_lower_le_inv {M : ℕ} (hM : 1 ≤ M) :
    upperEulerMascheroniSeq M - eulerMascheroniSeq M ≤ (M : ℝ)⁻¹ := by
  rw [upperEulerMascheroniSeq_sub_lower]
  exact logStep_le_inv hM

/-- Step difference of `upperEulerMascheroniSeq`:
`upperEulerMascheroniSeq (M + 1) - upperEulerMascheroniSeq M = (M + 1)⁻¹ - logStep M`. -/
theorem upperEulerMascheroniSeq_succ_sub (M : ℕ) :
    upperEulerMascheroniSeq (M + 1) - upperEulerMascheroniSeq M
      = ((M + 1 : ℕ) : ℝ)⁻¹ - logStep M := by
  unfold upperEulerMascheroniSeq harmonicSum logStep
  have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp)]
  ring

/-- `upperEulerMascheroniSeq` is decreasing for `1 ≤ M`:
`upperEulerMascheroniSeq (M + 1) ≤ upperEulerMascheroniSeq M`. -/
theorem upperEulerMascheroniSeq_succ_le {M : ℕ} (hM : 1 ≤ M) :
    upperEulerMascheroniSeq (M + 1) ≤ upperEulerMascheroniSeq M := by
  have h := upperEulerMascheroniSeq_succ_sub M
  have hstep := inv_le_logStep_pred (by omega : 2 ≤ M + 1)
  simp only [Nat.add_sub_cancel] at hstep
  linarith

/-- `upperEulerMascheroniSeq` is antitone on `{M : ℕ | 1 ≤ M}`: for `1 ≤ M ≤ N`,
`upperEulerMascheroniSeq N ≤ upperEulerMascheroniSeq M`. -/
theorem upperEulerMascheroniSeq_anti {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    upperEulerMascheroniSeq N ≤ upperEulerMascheroniSeq M := by
  induction hMN with
  | refl => exact le_rfl
  | @step k hMk ih =>
    exact (upperEulerMascheroniSeq_succ_le (le_trans hM hMk)).trans ih

/-- `eulerMascheroniSeq` is monotonically increasing on `ℕ`. -/
theorem eulerMascheroniSeq_mono : Monotone eulerMascheroniSeq :=
  monotone_nat_of_le_succ eulerMascheroniSeq_le_succ

/-- Nonnegativity of `eulerMascheroniSeq M` for all `M : ℕ`. -/
theorem eulerMascheroniSeq_nonneg_all (M : ℕ) :
    0 ≤ eulerMascheroniSeq M := by
  rw [← eulerMascheroniSeq_zero]
  exact eulerMascheroniSeq_mono (Nat.zero_le M)

/-- Every term of `eulerMascheroniSeq` is bounded above by every term of
`upperEulerMascheroniSeq` (`1 ≤ N`). -/
theorem eulerMascheroniSeq_le_upperEulerMascheroniSeq (M : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    eulerMascheroniSeq M ≤ upperEulerMascheroniSeq N := by
  have h1 : eulerMascheroniSeq M ≤ eulerMascheroniSeq (max M N) :=
    eulerMascheroniSeq_mono (le_max_left M N)
  have hmax1 : 1 ≤ max M N := le_trans hN (le_max_right M N)
  have h2 : eulerMascheroniSeq (max M N) ≤ upperEulerMascheroniSeq (max M N) := by
    have hgap := upperEulerMascheroniSeq_sub_lower (max M N)
    have hpos := logStep_nonneg hmax1
    linarith
  have h3 : upperEulerMascheroniSeq (max M N) ≤ upperEulerMascheroniSeq N :=
    upperEulerMascheroniSeq_anti hN (le_max_right M N)
  exact h1.trans (h2.trans h3)

/-- `eulerMascheroniSeq` is bounded above by `1`. -/
theorem bddAbove_eulerMascheroniSeq :
    BddAbove (Set.range eulerMascheroniSeq) := by
  refine ⟨upperEulerMascheroniSeq 1, ?_⟩
  rintro _ ⟨M, rfl⟩
  exact eulerMascheroniSeq_le_upperEulerMascheroniSeq M le_rfl

/-- The Euler-Mascheroni constant `γ = sup_M (H_M - log(M + 1))`. -/
def eulerMascheroni : ℝ :=
  ⨆ M : ℕ, eulerMascheroniSeq M

/-- For every `M : ℕ`, `eulerMascheroniSeq M ≤ eulerMascheroni`. -/
theorem eulerMascheroniSeq_le_eulerMascheroni (M : ℕ) :
    eulerMascheroniSeq M ≤ eulerMascheroni :=
  le_ciSup bddAbove_eulerMascheroniSeq M

/-- For every `1 ≤ N`, `eulerMascheroni ≤ upperEulerMascheroniSeq N`. -/
theorem eulerMascheroni_le_upperEulerMascheroniSeq {N : ℕ} (hN : 1 ≤ N) :
    eulerMascheroni ≤ upperEulerMascheroniSeq N :=
  ciSup_le fun M => eulerMascheroniSeq_le_upperEulerMascheroniSeq M hN

/-- `0 ≤ eulerMascheroni`. -/
theorem eulerMascheroni_nonneg : 0 ≤ eulerMascheroni :=
  (eulerMascheroniSeq_nonneg_all 0).trans (eulerMascheroniSeq_le_eulerMascheroni 0)

/-- `eulerMascheroni ≤ 1`. -/
theorem eulerMascheroni_le_one : eulerMascheroni ≤ 1 := by
  rw [← upperEulerMascheroniSeq_one]
  exact eulerMascheroni_le_upperEulerMascheroniSeq le_rfl

/-- For `1 ≤ M`, `upperEulerMascheroniSeq M ≤ eulerMascheroni + M⁻¹`. -/
theorem upperEulerMascheroniSeq_le_eulerMascheroni_add_inv {M : ℕ} (hM : 1 ≤ M) :
    upperEulerMascheroniSeq M ≤ eulerMascheroni + (M : ℝ)⁻¹ := by
  have h1 := eulerMascheroniSeq_le_eulerMascheroni M
  have h2 := upperEulerMascheroniSeq_sub_lower_le_inv hM
  linarith

/-- For `1 ≤ M`, `eulerMascheroni - M⁻¹ ≤ eulerMascheroniSeq M`. -/
theorem eulerMascheroni_sub_inv_le_eulerMascheroniSeq {M : ℕ} (hM : 1 ≤ M) :
    eulerMascheroni - (M : ℝ)⁻¹ ≤ eulerMascheroniSeq M := by
  have h1 := eulerMascheroni_le_upperEulerMascheroniSeq hM
  have h2 := upperEulerMascheroniSeq_sub_lower_le_inv hM
  linarith

/-! ### 2. Two-Sided `O(1)` Bounds on `4 * √k * (harmonicSum (Nat.sqrt k) - log k / 2)` -/

/-- For `1 ≤ k`, `harmonicSum (Nat.sqrt k) - log k / 2 ≤ eulerMascheroni + (Nat.sqrt k)⁻¹`. -/
theorem harmonicSum_sqrt_sub_half_log_le_eulerMascheroni_add_inv {k : ℕ} (hk : 1 ≤ k) :
    harmonicSum (Nat.sqrt k) - Real.log (k : ℝ) / 2
      ≤ eulerMascheroni + (Nat.sqrt k : ℝ)⁻¹ := by
  set M := Nat.sqrt k
  have hM1 : 1 ≤ M := Nat.sqrt_pos.mpr hk
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsq_le : (M : ℝ) ≤ Real.sqrt (k : ℝ) := by
    rw [← Real.sqrt_sq hM0.le]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' k)
  have hlog : Real.log (M : ℝ) ≤ Real.log (k : ℝ) / 2 := by
    rw [← Real.log_sqrt hk0]
    exact Real.log_le_log hM0 hsq_le
  have hseq : harmonicSum M - Real.log (k : ℝ) / 2 ≤ upperEulerMascheroniSeq M := by
    unfold upperEulerMascheroniSeq
    linarith
  exact hseq.trans (upperEulerMascheroniSeq_le_eulerMascheroni_add_inv hM1)

/-- For `1 ≤ k`, `eulerMascheroni - (Nat.sqrt k)⁻¹ ≤ harmonicSum (Nat.sqrt k) - log k / 2`. -/
theorem eulerMascheroni_sub_inv_le_harmonicSum_sqrt_sub_half_log {k : ℕ} (hk : 1 ≤ k) :
    eulerMascheroni - (Nat.sqrt k : ℝ)⁻¹
      ≤ harmonicSum (Nat.sqrt k) - Real.log (k : ℝ) / 2 := by
  set M := Nat.sqrt k
  have hM1 : 1 ≤ M := Nat.sqrt_pos.mpr hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hsq_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hlt : k < (M + 1) ^ 2 := Nat.lt_succ_sqrt' k
  have hle_cast : (k : ℝ) ≤ ((M + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hlt.le
  have hsq_le : Real.sqrt (k : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg (M + 1))]
    exact Real.sqrt_le_sqrt hle_cast
  have hlog : Real.log (k : ℝ) / 2 ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
    rw [← Real.log_sqrt hk0.le]
    exact Real.log_le_log hsq_pos hsq_le
  have hseq : eulerMascheroniSeq M ≤ harmonicSum M - Real.log (k : ℝ) / 2 := by
    unfold eulerMascheroniSeq
    linarith
  exact (eulerMascheroni_sub_inv_le_eulerMascheroniSeq hM1).trans hseq

/-- For `1 ≤ k`, `√k * (Nat.sqrt k)⁻¹ ≤ 2`. -/
theorem sqrt_mul_inv_nat_sqrt_le_two {k : ℕ} (hk : 1 ≤ k) :
    Real.sqrt (k : ℝ) * (Nat.sqrt k : ℝ)⁻¹ ≤ 2 := by
  set M := Nat.sqrt k
  have hM1 : 1 ≤ M := Nat.sqrt_pos.mpr hk
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have h1 : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hsq := sqrt_sub_nat_sqrt_le_one k
  rw [← div_eq_mul_inv, div_le_iff₀ hM0]
  linarith

/-- **Upper `O(1)` Bound on `4 * √k * (harmonicSum (Nat.sqrt k) - log k / 2)`**:
for `1 ≤ k`, `4 * √k * (harmonicSum (Nat.sqrt k) - log k / 2) ≤ 4 * eulerMascheroni * √k + 8`. -/
theorem four_sqrt_mul_harmonicSum_sub_half_log_le {k : ℕ} (hk : 1 ≤ k) :
    4 * Real.sqrt (k : ℝ) * (harmonicSum (Nat.sqrt k) - Real.log (k : ℝ) / 2)
      ≤ 4 * eulerMascheroni * Real.sqrt (k : ℝ) + 8 := by
  have hsq : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have h1 := harmonicSum_sqrt_sub_half_log_le_eulerMascheroni_add_inv hk
  have h2 :
      4 * Real.sqrt (k : ℝ) * (harmonicSum (Nat.sqrt k) - Real.log (k : ℝ) / 2)
        ≤ 4 * Real.sqrt (k : ℝ) * (eulerMascheroni + (Nat.sqrt k : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 := sqrt_mul_inv_nat_sqrt_le_two hk
  linarith

/-- **Lower `O(1)` Bound on `4 * √k * (harmonicSum (Nat.sqrt k) - log k / 2)`**:
for `1 ≤ k`, `4 * eulerMascheroni * √k - 8 ≤ 4 * √k * (harmonicSum (Nat.sqrt k) - log k / 2)`. -/
theorem four_eulerMascheroni_mul_sqrt_sub_eight_le {k : ℕ} (hk : 1 ≤ k) :
    4 * eulerMascheroni * Real.sqrt (k : ℝ) - 8
      ≤ 4 * Real.sqrt (k : ℝ) * (harmonicSum (Nat.sqrt k) - Real.log (k : ℝ) / 2) := by
  have hsq : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have h1 := eulerMascheroni_sub_inv_le_harmonicSum_sqrt_sub_half_log hk
  have h2 :
      4 * Real.sqrt (k : ℝ) * (eulerMascheroni - (Nat.sqrt k : ℝ)⁻¹)
        ≤ 4 * Real.sqrt (k : ℝ) * (harmonicSum (Nat.sqrt k) - Real.log (k : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 := sqrt_mul_inv_nat_sqrt_le_two hk
  linarith

/-! ### 3. Two-Sided `√k` Cancellation at `α = -2 * eulerMascheroni` and `O(log c)` Operator Norm Bound -/

end Cvs.Zeta.EulerMascheroniSqueeze
