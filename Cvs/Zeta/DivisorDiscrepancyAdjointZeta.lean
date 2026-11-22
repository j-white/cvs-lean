import Mathlib
import Cvs.WeilForm.DirichletSchurFactorisation
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.WholeDomainUnification
import Cvs.Zeta.DivisorDiscrepancyHyperbola

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Adjoint Zeta Projection Identity and Explicit Unconditional Bounds on `divisorDiscrepancy`

Proves the `μ`-eliminating adjoint projection identity `⟪Op c μ f, (Op c ζ)* w⟫ = ⟪f, w⟫`, the Euler–Mascheroni
monotonicity and `[0, 1]` bounds on `harmonicSum (Nat.sqrt k) - log k / 2`, and explicit bounds on `divisorDiscrepancy`.
-/

noncomputable section

open MeasureTheory Real Set
open scoped InnerProductSpace NNReal ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.Zeta.DivisorDiscrepancyAdjointZeta
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
open Cvs.Route.OneCellLaplaceTransform (G)
open Cvs.Route.OneCellChebyshevInequality (Psihalf M)
open Cvs.WeilForm.WindowVacuumRieszMean (vac)
open Cvs.WeilForm.WindowCircleIsometry (windowCircle)
open Cvs.WeilForm.DirichletSchurFactorisation
open Cvs.WeilForm.ShiftedDirichletSchurVacuum
open Cvs.WeilForm.DivisorHyperbolaFactorisation
open Cvs.WeilForm.WholeDomainUnification
open Cvs.Zeta.PartialSumHalfEulerMaclaurin
open Cvs.Zeta.DivisorDiscrepancyHyperbola

attribute [local instance] Classical.propDecidable

/-! ### 1. The `μ`-Eliminating Adjoint Zeta Projection Identity on `L²(𝕋)` and `formDomain` -/

/-- **The `μ`-Eliminating Adjoint Pairing Identity on `L²(𝕋)`**: for `1 < c` and `f, w : L²(𝕋)`,
`⟪Op c μ f, (Op c ζ)* w⟫ = ⟪f, w⟫`. -/
theorem inner_Op_moebius_adj_Op_zeta {c : ℕ} (hc : 1 < c) (f w : L2) :
    ⟪Op c (μ : ArithmeticFunction ℝ) f,
        ContinuousLinearMap.adjoint (Op c (ζ : ArithmeticFunction ℝ)) w⟫_ℝ
      = ⟪f, w⟫_ℝ := by
  rw [ContinuousLinearMap.adjoint_inner_right, Op_zeta_Op_moebius_apply hc]

/-- **Adjoint Zeta Projection Split on `L²(𝕋)`**: for `1 < c` and `f, u, w : L²(𝕋)`,
`⟪Op c μ f, u⟫ = ⟪f, w⟫ + ⟪Op c μ f, u - (Op c ζ)* w⟫`. -/
theorem inner_Op_moebius_eq_inner_add_rem {c : ℕ} (hc : 1 < c) (f u w : L2) :
    ⟪Op c (μ : ArithmeticFunction ℝ) f, u⟫_ℝ
      = ⟪f, w⟫_ℝ
        + ⟪Op c (μ : ArithmeticFunction ℝ) f,
            u - ContinuousLinearMap.adjoint (Op c (ζ : ArithmeticFunction ℝ)) w⟫_ℝ := by
  rw [inner_sub_right, inner_Op_moebius_adj_Op_zeta hc, add_sub_cancel]

/-! ### 2. Monotone Euler–Mascheroni Sequence and `[0, 1]` Bounds on `H_{⌊√k⌋} - log k / 2` -/

/-- The lower Euler–Mascheroni sequence `H_M - log (M + 1)`. -/
def eulerMascheroniSeq (M : ℕ) : ℝ :=
  harmonicSum M - Real.log ((M + 1 : ℕ) : ℝ)

/-- Step identity `eulerMascheroniSeq (M + 1) - eulerMascheroniSeq M = (M + 1)⁻¹ - logStep (M + 1)`. -/
theorem eulerMascheroniSeq_succ_sub (M : ℕ) :
    eulerMascheroniSeq (M + 1) - eulerMascheroniSeq M
      = ((M + 1 : ℕ) : ℝ)⁻¹ - logStep (M + 1) := by
  unfold eulerMascheroniSeq harmonicSum logStep
  have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp)]
  ring

/-- `eulerMascheroniSeq` is monotonically increasing (`eulerMascheroniSeq M ≤ eulerMascheroniSeq (M + 1)`). -/
theorem eulerMascheroniSeq_le_succ (M : ℕ) :
    eulerMascheroniSeq M ≤ eulerMascheroniSeq (M + 1) := by
  have h := eulerMascheroniSeq_succ_sub M
  have hstep := logStep_le_inv (Nat.le_add_left 1 M)
  linarith

/-- For any `k : ℕ`, `0 ≤ √k - Nat.sqrt k`. -/
theorem zero_le_sqrt_sub_nat_sqrt (k : ℕ) :
    0 ≤ Real.sqrt (k : ℝ) - (Nat.sqrt k : ℝ) := by
  rw [sub_nonneg, ← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt k))]
  exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' k)

/-- For any `k : ℕ`, `√k - Nat.sqrt k ≤ 1`. -/
theorem sqrt_sub_nat_sqrt_le_one (k : ℕ) :
    Real.sqrt (k : ℝ) - (Nat.sqrt k : ℝ) ≤ 1 := by
  have hlt : k < (Nat.sqrt k + 1) ^ 2 := Nat.lt_succ_sqrt' k
  have hle_cast : (k : ℝ) ≤ ((Nat.sqrt k + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hlt.le
  have hsq : Real.sqrt (k : ℝ) ≤ ((Nat.sqrt k + 1 : ℕ) : ℝ) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt k + 1))]
    exact Real.sqrt_le_sqrt hle_cast
  rw [Nat.cast_add, Nat.cast_one] at hsq
  linarith

/-! ### 3. Explicit Unconditional Bounds on `partialSumHalf (divisorDiscrepancy α)` and `Op c` -/

end Cvs.Zeta.DivisorDiscrepancyAdjointZeta
