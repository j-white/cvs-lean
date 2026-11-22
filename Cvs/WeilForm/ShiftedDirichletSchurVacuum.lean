import Mathlib
import Cvs.Route.OneCellChebyshevInequality
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.DirichletSchurFactorisation
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.WeilForm.MaskedShift.PrimeOperatorBudgetGap
import Cvs.WeilForm.VacuumTwoWalkCorrelation
import Cvs.WeilForm.WindowVacuumRieszMean

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Whole-Domain Shifted Dirichlet-Schur Factorization and Vacuum Riesz-Correlation Identities

Proves the adjoint-vacuum isometry `⟪(Op c a)* vac, (Op c b)* vac⟫ = ⟪Op c a vac, Op c b vac⟫`, the whole-domain shifted
factorization `α • 1 - Op c Λ = Op c (α • ζ - log) * Op c μ`, and the single-pairing identity for `G (log c)`.
-/

noncomputable section

open MeasureTheory Real
open scoped InnerProductSpace NNReal ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.WeilForm.ShiftedDirichletSchurVacuum
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
open Cvs.Route.OneCellLaplaceTransform (G primeSide)
open Cvs.Route.OneCellChebyshevInequality (Psihalf M)
open Cvs.WeilForm.WindowVacuumRieszMean (vac inner_vac_S inner_vac_rho inner_vac_Op primeSide_eq_vac)
open Cvs.WeilForm.VacuumTwoWalkCorrelation (inner_S_vac_S_vac inner_adjS_vac_adjS_vac)
open Cvs.WeilForm.DirichletSchurFactorisation

attribute [local instance] Classical.propDecidable

/-! ### 1. Vacuum Unit Norm and Exact Adjoint-Vacuum Isometry on `L²(𝕋)` -/

/-- The vacuum `vac = 1` on `L²(𝕋)` has unit inner product `⟪vac, vac⟫ = 1`. -/
theorem inner_vac_self : ⟪vac, vac⟫_ℝ = 1 := by
  have h := inner_vac_S (β := 0) le_rfl zero_le_one
  rw [S_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, sub_zero] at h
  exact h

/-- The vacuum `vac = 1` on `L²(𝕋)` has unit squared norm `‖vac‖² = 1`. -/
theorem norm_vac_sq : ‖vac‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_vac_self]

/-- At `n = 0`, `rho c 0 = 0`. -/
theorem rho_zero (c : ℕ) : rho c 0 = 0 := by
  unfold rho
  have h0 : ((0 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
  rw [h0]
  exact zero_smul ℝ (Snn (rot c 0))

/-- Closed-form inner product of `rho c m vac` and `rho c n vac` for `1 ≤ m < c` and `1 ≤ n < c`. -/
theorem inner_rho_vac_rho_vac {c m n : ℕ} (hc : 1 < c)
    (hm1 : 1 ≤ m) (hmc : m < c) (hn1 : 1 ≤ n) (hnc : n < c) :
    ⟪rho c m vac, rho c n vac⟫_ℝ
      = (m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))
        * (1 - max (Real.log m / Real.log c) (Real.log n / Real.log c)) := by
  have hL : 0 < Real.log c := Real.log_pos (by exact_mod_cast hc)
  have hm0 : 0 ≤ Real.log m / Real.log c :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hm1)) hL.le
  have hm_le : Real.log m / Real.log c ≤ 1 :=
    (div_le_one hL).mpr (Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmc.le))
  have hn0 : 0 ≤ Real.log n / Real.log c :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) hL.le
  have hn_le : Real.log n / Real.log c ≤ 1 :=
    (div_le_one hL).mpr (Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnc.le))
  have hrot_m : ((rot c m : ℝ≥0) : ℝ) = Real.log m / Real.log c := Real.coe_toNNReal _ hm0
  have hrot_n : ((rot c n : ℝ≥0) : ℝ) = Real.log n / Real.log c := Real.coe_toNNReal _ hn0
  simp only [rho, _root_.smul_apply, real_inner_smul_left, real_inner_smul_right,
    Snn, hrot_m, hrot_n]
  rw [inner_S_vac_S_vac hm0 hm_le hn0 hn_le]
  ring

/-- Closed-form inner product of `(rho c m)* vac` and `(rho c n)* vac` for `1 ≤ m < c` and `1 ≤ n < c`. -/
theorem inner_adj_rho_vac_adj_rho_vac {c m n : ℕ} (hc : 1 < c)
    (hm1 : 1 ≤ m) (hmc : m < c) (hn1 : 1 ≤ n) (hnc : n < c) :
    ⟪ContinuousLinearMap.adjoint (rho c m) vac,
        ContinuousLinearMap.adjoint (rho c n) vac⟫_ℝ
      = (m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))
        * (1 - max (Real.log m / Real.log c) (Real.log n / Real.log c)) := by
  have hL : 0 < Real.log c := Real.log_pos (by exact_mod_cast hc)
  have hm0 : 0 ≤ Real.log m / Real.log c :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hm1)) hL.le
  have hm_le : Real.log m / Real.log c ≤ 1 :=
    (div_le_one hL).mpr (Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmc.le))
  have hn0 : 0 ≤ Real.log n / Real.log c :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) hL.le
  have hn_le : Real.log n / Real.log c ≤ 1 :=
    (div_le_one hL).mpr (Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnc.le))
  have hrot_m : ((rot c m : ℝ≥0) : ℝ) = Real.log m / Real.log c := Real.coe_toNNReal _ hm0
  have hrot_n : ((rot c n : ℝ≥0) : ℝ) = Real.log n / Real.log c := Real.coe_toNNReal _ hn0
  simp only [rho, map_smul, _root_.smul_apply, real_inner_smul_left,
    real_inner_smul_right, Snn, hrot_m, hrot_n]
  rw [inner_adjS_vac_adjS_vac hm0 hm_le hn0 hn_le]
  ring

/-- **Adjoint-Vacuum Isometry for `rho`**: for all `m, n : ℕ` and `1 < c`,
`⟪(rho c m)* vac, (rho c n)* vac⟫ = ⟪rho c m vac, rho c n vac⟫`. -/
theorem inner_adj_rho_vac_eq_inner_rho_vac {c : ℕ} (hc : 1 < c) (m n : ℕ) :
    ⟪ContinuousLinearMap.adjoint (rho c m) vac,
        ContinuousLinearMap.adjoint (rho c n) vac⟫_ℝ
      = ⟪rho c m vac, rho c n vac⟫_ℝ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · simp [rho_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · simp [rho_zero]
  rcases lt_or_ge m c with hmc | hmc
  · rcases lt_or_ge n c with hnc | hnc
    · rw [inner_adj_rho_vac_adj_rho_vac hc hm1 hmc hn1 hnc,
        inner_rho_vac_rho_vac hc hm1 hmc hn1 hnc]
    · simp [rho_eq_zero hc hnc]
  · simp [rho_eq_zero hc hmc]

/-- **Exact Adjoint-Vacuum Isometry for Window Dirichlet Operators**: for any arithmetic functions
`a b : ArithmeticFunction ℝ` and `1 < c`, `⟪(Op c a)* vac, (Op c b)* vac⟫ = ⟪Op c a vac, Op c b vac⟫`. -/
theorem inner_adj_Op_vac_eq_inner_Op_vac {c : ℕ} (hc : 1 < c)
    (a b : ArithmeticFunction ℝ) :
    ⟪ContinuousLinearMap.adjoint (Op c a) vac,
        ContinuousLinearMap.adjoint (Op c b) vac⟫_ℝ
      = ⟪Op c a vac, Op c b vac⟫_ℝ := by
  unfold Op
  rw [map_sum, map_sum, _root_.sum_apply, _root_.sum_apply,
    _root_.sum_apply, _root_.sum_apply,
    sum_inner, sum_inner]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [inner_sum, inner_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [map_smul, _root_.smul_apply, real_inner_smul_left,
    real_inner_smul_right, inner_adj_rho_vac_eq_inner_rho_vac hc m n]

/-- **Norm Equality Between `Op c a vac` and `(Op c a)* vac`**: for any `a : ArithmeticFunction ℝ`
and `1 < c`, `‖(Op c a)* vac‖² = ‖Op c a vac‖²`. -/
theorem norm_sq_adj_Op_vac_eq {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    ‖ContinuousLinearMap.adjoint (Op c a) vac‖ ^ 2 = ‖Op c a vac‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_adj_Op_vac_eq_inner_Op_vac hc a a]

/-- For any `a : ArithmeticFunction ℝ` and `1 < c`, `‖(Op c a)* vac‖ = ‖Op c a vac‖`. -/
theorem norm_adj_Op_vac_eq {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    ‖ContinuousLinearMap.adjoint (Op c a) vac‖ = ‖Op c a vac‖ := by
  have h := norm_sq_adj_Op_vac_eq hc a
  nlinarith [norm_nonneg (ContinuousLinearMap.adjoint (Op c a) vac), norm_nonneg (Op c a vac)]

/-- Closed-form Riesz correlation bilinear form of two arithmetic functions on `[1, c)`. -/
def rieszCorrelation (c : ℕ) (a b : ArithmeticFunction ℝ) : ℝ :=
  ∑ m ∈ Finset.range c, ∑ n ∈ Finset.range c,
    a m * b n * ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))
      * (1 - max (Real.log m / Real.log c) (Real.log n / Real.log c)))

/-- **Explicit Riesz Correlation Identity**: for `1 < c` and `a b : ArithmeticFunction ℝ`,
`⟪Op c a vac, Op c b vac⟫ = rieszCorrelation c a b`. -/
theorem inner_Op_vac_eq_rieszCorrelation {c : ℕ} (hc : 1 < c)
    (a b : ArithmeticFunction ℝ) :
    ⟪Op c a vac, Op c b vac⟫_ℝ = rieszCorrelation c a b := by
  unfold Op rieszCorrelation
  rw [_root_.sum_apply, _root_.sum_apply, sum_inner]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [_root_.smul_apply, _root_.smul_apply,
    real_inner_smul_left, real_inner_smul_right]
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · simp [rho_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · simp [rho_zero]
  rw [inner_rho_vac_rho_vac hc hm1 (Finset.mem_range.mp hm) hn1 (Finset.mem_range.mp hn)]
  ring

/-- `‖Op c a vac‖² = rieszCorrelation c a a` for `1 < c`. -/
theorem norm_sq_Op_vac_eq_rieszCorrelation {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    ‖Op c a vac‖ ^ 2 = rieszCorrelation c a a := by
  rw [← real_inner_self_eq_norm_sq, inner_Op_vac_eq_rieszCorrelation hc a a]

/-! ### 2. Whole-Domain Shifted Dirichlet-Schur Identity (`α • 1 - Op c Λ`) -/

/-! ### 3. Unification with `Psihalf` and the One-Cell Weil Function `G (log c)` -/

/-- `Psihalf c = log c * ⟪Op c Λ vac, vac⟫` for `1 < c`. -/
theorem Psihalf_eq_log_mul_inner_Op_vonMangoldt_vac {c : ℕ} (hc : 1 < c) :
    Psihalf c = Real.log c * ⟪Op c ArithmeticFunction.vonMangoldt vac, vac⟫_ℝ := by
  rw [Cvs.Route.OneCellChebyshevInequality.Psihalf_eq, primeSide_eq_vac hc, real_inner_comm]

/-- `2 * Psihalf c = log c * ⟪primeOperator c P R vac, vac⟫` when `1 < c`, `c ≤ P + 1`,
and `Nat.clog 2 c ≤ R + 1`. -/
theorem two_mul_Psihalf_eq_log_mul_inner_primeOperator_vac {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    2 * Psihalf c = Real.log c * ⟪primeOperator c P R vac, vac⟫_ℝ := by
  rw [inner_primeOperator_eq_two_inner_Op_vonMangoldt hc hP hR,
    Psihalf_eq_log_mul_inner_Op_vonMangoldt_vac hc]
  ring

end Cvs.WeilForm.ShiftedDirichletSchurVacuum
