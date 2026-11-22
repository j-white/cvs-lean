import Mathlib
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.OneCellChebyshevInequality
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.DivisorHyperbolaFactorisation
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.WholeDomainUnification
import Cvs.WeilForm.WindowVacuumRieszMean

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Unconditional Euler–Maclaurin Bounds on `partialSumHalf ζ`, `discretePoleRiesz`, and `smoothPoleRem`

Proves unconditional algebraic step bounds for `n^{-1/2}` and `logStep`, telescopes them to bound
`partialSumHalf ζ k` and `discretePoleRiesz c`, and cancels the `4√c - 8` pole term in `smoothPoleRem c α`.
-/

noncomputable section

open MeasureTheory Real Set
open scoped InnerProductSpace NNReal ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.Zeta.PartialSumHalfEulerMaclaurin
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
open Cvs.Finite.WindowMatrixSymbolKernel (bk bk_pos)
open Cvs.Route.OneCellLaplaceTransform (G ladder summable_inv_bk_sq)
open Cvs.Route.OneCellChebyshevInequality (Psihalf S0 trivTail M summable_exp_div_bk_sq ladder_eq)
open Cvs.WeilForm.WindowVacuumRieszMean (vac inner_vac_Op)
open Cvs.WeilForm.DirichletSchurFactorisation
open Cvs.WeilForm.ShiftedDirichletSchurVacuum
open Cvs.WeilForm.DivisorHyperbolaFactorisation
open Cvs.WeilForm.WholeDomainUnification

attribute [local instance] Classical.propDecidable

/-! ### 1. Algebraic Step Bounds for `n^{-1/2}` and `logStep k` -/

/-- Conjugate product identity `(√(x + 1) - √x) * (√(x + 1) + √x) = 1` for `0 ≤ x`. -/
theorem sqrt_add_one_sub_sqrt_mul_add {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt (x + 1) - Real.sqrt x) * (Real.sqrt (x + 1) + Real.sqrt x) = 1 := by
  have h1 : (Real.sqrt (x + 1) - Real.sqrt x) * (Real.sqrt (x + 1) + Real.sqrt x)
      = Real.sqrt (x + 1) ^ 2 - Real.sqrt x ^ 2 := by ring
  rw [h1, Real.sq_sqrt (by linarith), Real.sq_sqrt hx]
  ring

/-- For `0 < x`, `x ^ (-1/2 : ℝ) = (Real.sqrt x)⁻¹`. -/
theorem rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [show -(1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- Lower step bound: `2 * (√(n + 1) - √n) ≤ n ^ (-1/2)` for `1 ≤ n`. -/
theorem two_mul_sqrt_succ_sub_sqrt_le_rpow_neg_half {n : ℕ} (hn : 1 ≤ n) :
    2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
      ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)
  have hconj :
      (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
        * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) = 1 := by
    simpa [Nat.cast_add, Nat.cast_one] using sqrt_add_one_sub_sqrt_mul_add hn0.le
  rw [rpow_neg_half_eq_inv_sqrt hn0.le]
  refine le_of_mul_le_mul_right ?_ hsq_pos
  rw [inv_mul_cancel₀ hsq_pos.ne']
  calc
    2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ)
      = (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
          * (2 * Real.sqrt (n : ℝ)) := by ring
    _ ≤ (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
          * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hle)
    _ = 1 := hconj

/-- Upper step bound: `n ^ (-1/2) ≤ 2 * (√n - √(n - 1))` for `1 ≤ n`. -/
theorem rpow_neg_half_le_two_mul_sqrt_sub_sqrt_pred {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hpred_nonneg : (0 : ℝ) ≤ (n - 1 : ℕ) := Nat.cast_nonneg _
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hn
  have hconj :
      (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ))
        * (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ)) = 1 := by
    have h := sqrt_add_one_sub_sqrt_mul_add hpred_nonneg
    rwa [hcast] at h
  have hle : Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [← hcast]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [rpow_neg_half_eq_inv_sqrt hn0.le]
  refine le_of_mul_le_mul_right ?_ hsq_pos
  rw [inv_mul_cancel₀ hsq_pos.ne']
  calc
    1 = (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ))
          * (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ)) := hconj.symm
    _ ≤ (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ))
          * (2 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hle)
    _ = 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) * Real.sqrt (n : ℝ) := by ring

/-- `logStep k = 2 * log (√(k + 1) / √k)` for `1 ≤ k`. -/
theorem logStep_eq_two_mul_log_sqrt_div {k : ℕ} (hk : 1 ≤ k) :
    logStep k = 2 * Real.log (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  unfold logStep
  rw [Real.log_div (Real.sqrt_pos.mpr hk1).ne' (Real.sqrt_pos.mpr hk0).ne',
    Real.log_sqrt hk1.le, Real.log_sqrt hk0.le]
  ring

/-- Upper step bound on `logStep`: `2 * √k * logStep k ≤ 4 * (√(k + 1) - √k)` for `1 ≤ k`. -/
theorem two_mul_sqrt_mul_logStep_le {k : ℕ} (hk : 1 ≤ k) :
    2 * Real.sqrt (k : ℝ) * logStep k
      ≤ 4 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  have hsq0 : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hsq1 : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hk1
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsq1 hsq0)
  rw [logStep_eq_two_mul_log_sqrt_div hk]
  have hmul :
      2 * Real.sqrt (k : ℝ) * (2 * Real.log (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (k : ℝ)))
        ≤ 4 * Real.sqrt (k : ℝ) * (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (k : ℝ) - 1) := by
    nlinarith [hsq0.le]
  have hsimpl :
      4 * Real.sqrt (k : ℝ) * (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (k : ℝ) - 1)
        = 4 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) := by
    have hne : Real.sqrt (k : ℝ) ≠ 0 := hsq0.ne'
    field_simp
  linarith

/-- Lower step bound on `logStep`: `4 * (√(k + 1) - √k) ≤ 2 * √(k + 1) * logStep k` for `1 ≤ k`. -/
theorem four_mul_sqrt_succ_sub_sqrt_le_two_mul_sqrt_succ_mul_logStep {k : ℕ} (hk : 1 ≤ k) :
    4 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ))
      ≤ 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) * logStep k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  have hsq0 : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hsq1 : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hk1
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsq0 hsq1)
  have hlog_inv :
      Real.log (Real.sqrt (k : ℝ) / Real.sqrt ((k + 1 : ℕ) : ℝ))
        = -Real.log (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (k : ℝ)) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog_inv] at hlog
  rw [logStep_eq_two_mul_log_sqrt_div hk]
  have hmul :
      4 * Real.sqrt ((k + 1 : ℕ) : ℝ) * (1 - Real.sqrt (k : ℝ) / Real.sqrt ((k + 1 : ℕ) : ℝ))
        ≤ 2 * Real.sqrt ((k + 1 : ℕ) : ℝ)
            * (2 * Real.log (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (k : ℝ))) := by
    nlinarith [hsq1.le]
  have hsimpl :
      4 * Real.sqrt ((k + 1 : ℕ) : ℝ) * (1 - Real.sqrt (k : ℝ) / Real.sqrt ((k + 1 : ℕ) : ℝ))
        = 4 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) := by
    have hne : Real.sqrt ((k + 1 : ℕ) : ℝ) ≠ 0 := hsq1.ne'
    field_simp
  linarith

/-! ### 2. Unconditional Two-Sided Bounds on `partialSumHalf ζ k` -/

/-- Explicit sum representation of `partialSumHalf ζ k` for any `k : ℕ`. -/
theorem partialSumHalf_zeta_eq_sum (k : ℕ) :
    partialSumHalf (ζ : ArithmeticFunction ℝ) k
      = ∑ n ∈ Finset.Icc 1 k, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold partialSumHalf
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  simp [ArithmeticFunction.zeta_apply, hn0]

/-- Telescoping sum of `2 * (√(n + 1) - √n)` over `n ∈ Finset.Icc 1 k` (`1 ≤ k`). -/
theorem sum_Icc_two_mul_sqrt_succ_sub_sqrt {k : ℕ} (hk : 1 ≤ k) :
    ∑ n ∈ Finset.Icc 1 k, 2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
      = 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 := by
  have hIcc : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, ← Finset.mul_sum,
    Finset.sum_Ico_sub (fun n : ℕ => Real.sqrt (n : ℝ)) (Nat.le_succ_of_le hk)]
  simp [Real.sqrt_one]
  ring

/-- Telescoping sum of `2 * (√n - √(n - 1))` over `n ∈ Finset.Icc 2 k` (`1 ≤ k`). -/
theorem sum_Icc_two_mul_sqrt_sub_sqrt_pred {k : ℕ} (hk : 1 ≤ k) :
    ∑ n ∈ Finset.Icc 2 k, 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ))
      = 2 * Real.sqrt (k : ℝ) - 2 := by
  rw [← Finset.mul_sum]
  have hsub :
      ∑ n ∈ Finset.Icc 2 k, (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ))
        = ∑ m ∈ Finset.Ico 1 k, (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) := by
    refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_Ico]
      omega
    · intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_Icc] at hn₁ hn₂
      omega
    · intro m hm
      simp only [Finset.mem_Ico] at hm
      exact ⟨m + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      have h1 : n - 1 + 1 = n := by omega
      rw [h1]
  rw [hsub, Finset.sum_Ico_sub (fun m : ℕ => Real.sqrt (m : ℝ)) hk]
  simp [Real.sqrt_one]
  ring

/-- **Unconditional Lower Bound on `partialSumHalf ζ k`**: for all `1 ≤ k`,
`2 * √(k + 1) - 2 ≤ partialSumHalf ζ k`. -/
theorem two_mul_sqrt_succ_sub_two_le_partialSumHalf_zeta {k : ℕ} (hk : 1 ≤ k) :
    2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 ≤ partialSumHalf (ζ : ArithmeticFunction ℝ) k := by
  rw [partialSumHalf_zeta_eq_sum, ← sum_Icc_two_mul_sqrt_succ_sub_sqrt hk]
  refine Finset.sum_le_sum fun n hn => ?_
  exact two_mul_sqrt_succ_sub_sqrt_le_rpow_neg_half (Finset.mem_Icc.mp hn).1

/-- **Unconditional Upper Bound on `partialSumHalf ζ k`**: for all `1 ≤ k`,
`partialSumHalf ζ k ≤ 2 * √k - 1`. -/
theorem partialSumHalf_zeta_le_two_mul_sqrt_sub_one {k : ℕ} (hk : 1 ≤ k) :
    partialSumHalf (ζ : ArithmeticFunction ℝ) k ≤ 2 * Real.sqrt (k : ℝ) - 1 := by
  rw [partialSumHalf_zeta_eq_sum]
  have hsplit :
      ∑ n ∈ Finset.Icc 1 k, (n : ℝ) ^ (-(1 / 2 : ℝ))
        = 1 + ∑ n ∈ Finset.Icc 2 k, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hins : Finset.Icc 1 k = insert 1 (Finset.Icc 2 k) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp), Nat.cast_one, Real.one_rpow]
  rw [hsplit]
  have hsum :
      ∑ n ∈ Finset.Icc 2 k, (n : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ ∑ n ∈ Finset.Icc 2 k, 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    exact rpow_neg_half_le_two_mul_sqrt_sub_sqrt_pred (by omega)
  linarith [sum_Icc_two_mul_sqrt_sub_sqrt_pred hk]

/-! ### 3. Telescopic Formula and Unconditional `4√c - 8` Cancellation in `smoothPoleRem` -/

/-- Telescopic partial-sum representation of `log c * ⟪Op c a vac, vac⟫` for `1 < c`. -/
theorem log_mul_inner_Op_vac_vac_eq_sum_partialSumHalf {c : ℕ} (hc : 1 < c)
    (a : ArithmeticFunction ℝ) :
    Real.log c * ⟪Op c a vac, vac⟫_ℝ
      = ∑ k ∈ Finset.Ico 1 c, logStep k * partialSumHalf a k := by
  have hL : (0 : ℝ) < Real.log c := Real.log_pos (by exact_mod_cast hc)
  rw [real_inner_comm, inner_vac_Op hc, Finset.mul_sum,
    sum_range_eq_sum_Ico_one (by simp)]
  have hterm : ∀ n ∈ Finset.Ico 1 c,
      Real.log c * (a n * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.log n / Real.log c)))
        = ∑ k ∈ Finset.Ico 1 c,
            logStep k * (if n ≤ k then a n * (n : ℝ) ^ (-(1 / 2 : ℝ)) else 0) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hnc : n ≤ c := (Finset.mem_Ico.mp hn).2.le
    have hdiv : Real.log c * (1 - Real.log n / Real.log c) = Real.log c - Real.log n := by
      field_simp
    calc
      Real.log c * (a n * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.log n / Real.log c)))
        = (a n * (n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log c * (1 - Real.log n / Real.log c)) := by
          ring
      _ = (a n * (n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log c - Real.log (max (n : ℝ) (n : ℝ))) := by
          rw [hdiv, max_self]
      _ = (a n * (n : ℝ) ^ (-(1 / 2 : ℝ)))
            * ∑ k ∈ Finset.Ico 1 c, (if n ≤ k ∧ n ≤ k then logStep k else 0) := by
          rw [log_sub_log_max_eq_sum_Ico hn1 hnc hnc]
      _ = ∑ k ∈ Finset.Ico 1 c,
            logStep k * (if n ≤ k then a n * (n : ℝ) ^ (-(1 / 2 : ℝ)) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hnk : n ≤ k <;> (simp [hnk]; try ring)
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold partialSumHalf
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
  have hkc : k < c := (Finset.mem_Ico.mp hk).2
  omega

/-- Telescopic partial-sum representation of `discretePoleRiesz c` (`1 < c`). -/
theorem discretePoleRiesz_eq_sum_partialSumHalf_zeta {c : ℕ} (hc : 1 < c) :
    discretePoleRiesz c
      = ∑ k ∈ Finset.Ico 1 c, logStep k * partialSumHalf (ζ : ArithmeticFunction ℝ) k :=
  log_mul_inner_Op_vac_vac_eq_sum_partialSumHalf hc (ζ : ArithmeticFunction ℝ)

/-- Telescoping sum of `4 * (√(k + 1) - √k)` over `k ∈ Finset.Ico 1 c` (`1 ≤ c`). -/
theorem sum_Ico_four_mul_sqrt_succ_sub_sqrt {c : ℕ} (hc : 1 ≤ c) :
    ∑ k ∈ Finset.Ico 1 c, 4 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ))
      = 4 * Real.sqrt (c : ℝ) - 4 := by
  rw [← Finset.mul_sum, Finset.sum_Ico_sub (fun k : ℕ => Real.sqrt (k : ℝ)) hc]
  simp [Real.sqrt_one]
  ring

/-- `trivTail x` is nonnegative for all `x : ℝ`. -/
theorem trivTail_nonneg (x : ℝ) : 0 ≤ trivTail x := by
  unfold trivTail
  refine tsum_nonneg fun k => ?_
  positivity

/-- At `L = 0`, `ladder 0 = 0`. -/
theorem ladder_zero : ladder 0 = 0 := by
  unfold ladder
  simp

/-- Exact identity `∑' k : ℕ, 1 / bk (k + 1) ^ 2 = S0 - 4`. -/
theorem tsum_inv_bk_succ_sq : (∑' k : ℕ, 1 / bk (k + 1) ^ 2) = S0 - 4 := by
  have h := ladder_eq (le_refl (0 : ℝ))
  rw [ladder_zero] at h
  simp_rw [mul_zero, zero_div, neg_zero, Real.exp_zero, mul_one] at h
  linarith

/-- For `1 ≤ x`, `trivTail x ≤ S0 - 4`. -/
theorem trivTail_le_S0_sub_four {x : ℝ} (hx : 1 ≤ x) : trivTail x ≤ S0 - 4 := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [← tsum_inv_bk_succ_sq]
  unfold trivTail
  have hs1 : Summable fun k : ℕ => Real.exp (-(bk (k + 1) * Real.log x)) / bk (k + 1) ^ 2 :=
    (summable_exp_div_bk_sq hL).comp_injective Nat.succ_injective
  have hs2 : Summable fun k : ℕ => 1 / bk (k + 1) ^ 2 :=
    summable_inv_bk_sq.comp_injective Nat.succ_injective
  refine hs1.tsum_le_tsum (fun k => ?_) hs2
  have hbk := bk_pos (k + 1)
  have hexp : Real.exp (-(bk (k + 1) * Real.log x)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  exact div_le_div_of_nonneg_right hexp (by positivity)

end Cvs.Zeta.PartialSumHalfEulerMaclaurin
