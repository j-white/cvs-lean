import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.ModeBoxDampedReduction
import Cvs.Route.ModeBoxFourChannelLevy
import Cvs.Route.ModeBoxGreenLaplace
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeBoxLogMinorant
import Cvs.Route.ModeBoxLogSlotConnesRung
import Cvs.Route.ModeBoxPureCurvature
import Cvs.Route.ModeBoxRightInverse
import Cvs.Route.ModeBoxShiftedArchGreen
import Cvs.Route.ModeBoxVolterraCurvature
import Cvs.Route.OneCellChebyshevInequality
import Cvs.Route.OneCellLaplaceTransform
import Cvs.Route.ShiftedSymbolPositivity
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.AdmissibleMultiplierMinorants
import Cvs.WeilForm.ArchGreenSecondChannel
import Cvs.WeilForm.Archimedean.ArchSymbolGlobalMinimum
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.Archimedean.TruncationBelowSymbol
import Cvs.WeilForm.ArithmeticFloorAboveBand
import Cvs.WeilForm.BandFreeLogTwoBase
import Cvs.WeilForm.CentredHodgeIndexWindow
import Cvs.WeilForm.ChannelModeSumEnclosure
import Cvs.WeilForm.DirichletSchurFactorisation
import Cvs.WeilForm.DivisorHyperbolaFactorisation
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.GreenRemovesFirstArchChannel
import Cvs.WeilForm.GreenTailCancellation
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.InterPrimePhaseCancellation
import Cvs.WeilForm.LowHeadSignedCorrection
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskGainQuantified
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.WeilForm.MaskedShift.PrimeOperatorBudgetGap
import Cvs.WeilForm.MaskedShift.PrimeSideAtomBudget
import Cvs.WeilForm.MaskedShift.WideHopVanishes
import Cvs.WeilForm.MeanFreeSpectralIdentity
import Cvs.WeilForm.NilpotentResolventEulerSquares
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.PolePrimeCosineMultipliers
import Cvs.WeilForm.PrimeDiagonalBulkSchur
import Cvs.WeilForm.PrimeMomentVolterra
import Cvs.WeilForm.PrimeOperatorPathLawDeficit
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.ShiftedDirichletSchurVacuum
import Cvs.WeilForm.StepQuadratureResidual
import Cvs.WeilForm.TruncSymbolMonotone
import Cvs.WeilForm.VonMangoldtMultiplier
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WholeDomainUnification
import Cvs.WeilForm.WindowCircleIsometry
import Cvs.WeilForm.WindowRepresentative
import Cvs.WeilForm.WindowVacuumRieszMean
import Cvs.Zeta.Digamma
import Cvs.Zeta.DivisorDiscrepancyHyperbola
import Cvs.Zeta.PartialSumHalfEulerMaclaurin
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.PsihalfIntegerInterpolation
import Cvs.Zeta.WeilPositivityStatement
import Cvs.Zeta.WingCancellationLog

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Direct Spectral-to-RH Chain via Connes' Spine and the 3-Cut Decomposition

Unites the Path-Law Chebyshev spectrum of `primeOperator` and `Op c a`, the 3-cut capacity
partition on `L²(𝕋)`, double-pole divisor cancellation, and Connes' rung–bulk spine on `Dom x`.
-/

set_option maxSynthPendingDepth 3

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.Route.SpectralChainThreeCut
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
open Cvs.Route.OneCellLaplaceTransform (G)
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
open Cvs.Zeta.WingCancellationLog

attribute [local instance] Classical.propDecidable

/-! ### 1. Direct Prime-Spectrum & Euler-Resolvent Identities on the Vacuum and `Psihalf c` -/

/-- **Vacuum Path-Law Deficit Identity for `Psihalf c`**: for `1 < c`, `c ≤ P + 1`, and
`Nat.clog 2 c ≤ R + 1`, `2 * Psihalf c` equals `log c` times the Chebyshev staircase budget
`atomBudget c P R` minus the nonnegative Path-Law sum of squares on `vac`. -/
theorem two_mul_Psihalf_eq_log_mul_atomBudget_sub_schur {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    2 * Psihalf c
      = Real.log c
        * (atomBudget c P R
          - (Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm c P R vac
            + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm c P R vac)) := by
  rw [two_mul_Psihalf_eq_log_mul_inner_primeOperator_vac hc hP hR,
    Cvs.WeilForm.PrimeOperatorPathLawDeficit.inner_primeOperator_eq_atomBudget_sub_schur hc P R vac,
    norm_vac_sq, mul_one]

/-- **Vacuum Path-Law Companion Identity for `Psihalf c`**: for `1 < c`, `c ≤ P + 1`, and
`Nat.clog 2 c ≤ R + 1`, `2 * Psihalf c` equals `log c` times the companion sum of squares minus
`atomBudget c P R`. -/
theorem two_mul_Psihalf_eq_log_mul_schurPlus_sub_atomBudget {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    2 * Psihalf c
      = Real.log c
        * (Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurPlusForm c P R vac
          + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm c P R vac
          - atomBudget c P R) := by
  rw [two_mul_Psihalf_eq_log_mul_inner_primeOperator_vac hc hP hR,
    Cvs.WeilForm.PrimeOperatorPathLawDeficit.inner_primeOperator_eq_schurPlus_sub_atomBudget hc P R vac,
    norm_vac_sq, mul_one]

/-- **Unconditional Chebyshev Spectral Upper Bound on `2 * Psihalf c`**: for `1 < c`, `c ≤ P + 1`,
and `Nat.clog 2 c ≤ R + 1`, `2 * Psihalf c ≤ log c * atomBudget c P R`. -/
theorem two_mul_Psihalf_le_log_mul_atomBudget {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    2 * Psihalf c ≤ Real.log c * atomBudget c P R := by
  have hL : 0 ≤ Real.log c := (Real.log_pos (by exact_mod_cast hc)).le
  have hdiff := Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm_nonneg c P R vac
  have hshort := Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm_nonneg hc P R vac
  rw [two_mul_Psihalf_eq_log_mul_atomBudget_sub_schur hc hP hR]
  nlinarith

/-- **Vacuum Euler-Resolvent Identity for `Psihalf c`**: for `1 < c`, `c ≤ P + 1`, and
`Nat.clog 2 c ≤ R + 1`, `log c * (∑_{p ≤ P} log p) + 2 * Psihalf c = log c * primeEulerResolventForm c P R vac`. -/
theorem log_mul_sum_prime_log_add_two_mul_Psihalf_eq_euler_resolvent {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    Real.log c * (∑ p ∈ primeRange P, Real.log p) + 2 * Psihalf c
      = Real.log c * Cvs.WeilForm.NilpotentResolventEulerSquares.primeEulerResolventForm c P R vac := by
  have heuler := Cvs.WeilForm.NilpotentResolventEulerSquares.inner_primeOperator_eq_euler_resolvent (P := P) hc hR vac
  rw [norm_vac_sq, mul_one] at heuler
  rw [two_mul_Psihalf_eq_log_mul_inner_primeOperator_vac hc hP hR, ← mul_add, heuler]

/-- **Direct Path-Law Sum-of-Squares Decomposition of `G (log c)` on `L²(𝕋)`**: for `1 < c`,
`c ≤ P + 1`, and `Nat.clog 2 c ≤ R + 1`,
`G (log c) = 2 * M c - log c * atomBudget c P R + log c * (atomSchurDiffForm + atomShortChainForm)`. -/
theorem G_log_eq_two_M_sub_log_mul_atomBudget_add_schur {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    G (Real.log c)
      = 2 * M c - Real.log c * atomBudget c P R
        + Real.log c
          * (Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm c P R vac
            + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm c P R vac) := by
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc.le
  have hG := Cvs.Route.OneCellChebyshevInequality.G_log_eq hc1
  have hpsi := two_mul_Psihalf_eq_log_mul_atomBudget_sub_schur hc hP hR
  linarith

/-- **Unconditional Chebyshev Spectral Lower Bound on `G (log c)`**: for `1 < c`, `c ≤ P + 1`,
and `Nat.clog 2 c ≤ R + 1`, `2 * M c - log c * atomBudget c P R ≤ G (Real.log c)`. -/
theorem G_log_ge_two_M_sub_log_mul_atomBudget {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    2 * M c - Real.log c * atomBudget c P R ≤ G (Real.log c) := by
  have hL : 0 ≤ Real.log c := (Real.log_pos (by exact_mod_cast hc)).le
  have hdiff := Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm_nonneg c P R vac
  have hshort := Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm_nonneg hc P R vac
  rw [G_log_eq_two_M_sub_log_mul_atomBudget_add_schur hc hP hR]
  nlinarith

/-! ### 2. Direct Chebyshev-Spectrum Decomposition of `Op c a` & 3-Cut Spectral Bounds on `L²(𝕋)` -/

/-- For `1 < c` and any arithmetic function `a`, `Op c a` splits into the diagonal identity term
`a 1 • 1` plus the off-diagonal shift sum over `n ∈ Ico 2 c`. -/
theorem Op_eq_one_add_sum_Ico {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    Op c a = a 1 • (1 : L2 →L[ℝ] L2) + ∑ n ∈ Finset.Ico 2 c, a n • rho c n := by
  unfold Op
  have hsplit : Finset.range c = insert 0 (insert 1 (Finset.Ico 2 c)) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    ArithmeticFunction.map_zero, zero_smul, zero_add, rho_one]

/-- Quadratic-form expansion of `2 * ⟪Op c a f, f⟫` into `2 * a 1 * ‖f‖²` plus the off-diagonal
shift forms `∑_{2 ≤ n < c} a n * (2 * ⟪rho c n f, f⟫)`. -/
theorem two_inner_Op_eq {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) (f : L2) :
    2 * ⟪Op c a f, f⟫_ℝ
      = 2 * a 1 * ‖f‖ ^ 2 + ∑ n ∈ Finset.Ico 2 c, a n * (2 * ⟪rho c n f, f⟫_ℝ) := by
  rw [Op_eq_one_add_sum_Ico hc a, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
    _root_.sum_apply, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, sum_inner, mul_add, Finset.mul_sum]
  rw [← mul_assoc]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [_root_.smul_apply, real_inner_smul_left]
  ring

/-- Off-diagonal Chebyshev spectral budget of an arithmetic function `a` at cutoff `c`. -/
def opChebOffDiag (c : ℕ) (a : ArithmeticFunction ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico 2 c,
    |a n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n))

/-- Upper Chebyshev spectral budget `2 * a 1 + opChebOffDiag c a` for `2 * ⟪Op c a f, f⟫`. -/
def opChebBudget (c : ℕ) (a : ArithmeticFunction ℝ) : ℝ :=
  2 * a 1 + opChebOffDiag c a

/-- Lower Chebyshev spectral floor `2 * a 1 - opChebOffDiag c a` for `2 * ⟪Op c a f, f⟫`. -/
def opChebFloor (c : ℕ) (a : ArithmeticFunction ℝ) : ℝ :=
  2 * a 1 - opChebOffDiag c a

/-- **Off-Diagonal Chebyshev Spectral Bound on `Op c a`**: for `1 < c`, `a : ArithmeticFunction ℝ`,
and `f : L²(𝕋)`, `|2 * ⟪Op c a f, f⟫ - 2 * a 1 * ‖f‖²| ≤ opChebOffDiag c a * ‖f‖²`. -/
theorem abs_two_inner_Op_sub_diag_le {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) (f : L2) :
    |2 * ⟪Op c a f, f⟫_ℝ - 2 * a 1 * ‖f‖ ^ 2| ≤ opChebOffDiag c a * ‖f‖ ^ 2 := by
  rw [two_inner_Op_eq hc a f, add_sub_cancel_left]
  unfold opChebOffDiag
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hn).1
  have hn1 : 1 < n := by omega
  rw [abs_mul, mul_assoc |a n|, mul_assoc |a n|]
  exact mul_le_mul_of_nonneg_left (abs_two_inner_rho_le_chebFactor hc hn1 f) (abs_nonneg (a n))

/-- **Upper Chebyshev Spectral Bound on `2 * ⟪Op c a f, f⟫`**: for `1 < c` and `f : L²(𝕋)`,
`2 * ⟪Op c a f, f⟫ ≤ opChebBudget c a * ‖f‖²`. -/
theorem two_inner_Op_le_opChebBudget {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) (f : L2) :
    2 * ⟪Op c a f, f⟫_ℝ ≤ opChebBudget c a * ‖f‖ ^ 2 := by
  have h := (abs_le.mp (abs_two_inner_Op_sub_diag_le hc a f)).2
  unfold opChebBudget
  linarith

/-- **Lower Chebyshev Spectral Floor on `2 * ⟪Op c a f, f⟫`**: for `1 < c` and `f : L²(𝕋)`,
`opChebFloor c a * ‖f‖² ≤ 2 * ⟪Op c a f, f⟫`. -/
theorem opChebFloor_le_two_inner_Op {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) (f : L2) :
    opChebFloor c a * ‖f‖ ^ 2 ≤ 2 * ⟪Op c a f, f⟫_ℝ := by
  have h := (abs_le.mp (abs_two_inner_Op_sub_diag_le hc a f)).1
  unfold opChebFloor
  linarith

/-- Higher-capacity chain part (`2 ≤ n < √c`, where `cap (log c) (log n) ≥ 3`) of `opChebOffDiag`. -/
def opChainOffDiag (c : ℕ) (a : ArithmeticFunction ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ico 2 c).filter (fun n => n ^ 2 < c),
    |a n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n))

/-- Dimer-cut part (`√c ≤ n < c`, where `cap (log c) (log n) = 2` and `chebFactor 2 = 1`) of `opChebOffDiag`. -/
def opDimerOffDiag (c : ℕ) (a : ArithmeticFunction ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ico 2 c).filter (fun n => c ≤ n ^ 2),
    |a n| * (n : ℝ) ^ (-(1 / 2 : ℝ))

/-- **The 3-Cut Decomposition of `opChebOffDiag`**: for `1 < c` and `a : ArithmeticFunction ℝ`,
`opChebOffDiag c a` splits into the sub-`√c` chain sum `opChainOffDiag c a` plus the dimer-cut sum
`opDimerOffDiag c a` (where the Chebyshev factor `chebFactor 2 = 1` halves the trivial weight `2`). -/
theorem opChebOffDiag_eq_chain_add_dimer {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    opChebOffDiag c a = opChainOffDiag c a + opDimerOffDiag c a := by
  unfold opChebOffDiag opChainOffDiag opDimerOffDiag
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico 2 c) (fun n => n ^ 2 < c)]
  congr 1
  refine Finset.sum_congr ?_ fun n hn => ?_
  · ext m
    simp only [Finset.mem_filter, not_lt]
  · simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    rw [chebFactor_cap_eq_one_of_dimer hc hn.1.2 hn.2, mul_one]

/-- **3-Cut Expansion of `opChebFloor`**: `opChebFloor c a = 2 * a 1 - opChainOffDiag c a - opDimerOffDiag c a`. -/
theorem opChebFloor_eq_three_cut {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    opChebFloor c a = 2 * a 1 - opChainOffDiag c a - opDimerOffDiag c a := by
  unfold opChebFloor
  rw [opChebOffDiag_eq_chain_add_dimer hc a]
  ring

/-- **3-Cut Expansion of `opChebBudget`**: `opChebBudget c a = 2 * a 1 + opChainOffDiag c a + opDimerOffDiag c a`. -/
theorem opChebBudget_eq_three_cut {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    opChebBudget c a = 2 * a 1 + opChainOffDiag c a + opDimerOffDiag c a := by
  unfold opChebBudget
  rw [opChebOffDiag_eq_chain_add_dimer hc a]
  ring

/-- **Direct Chebyshev Spectral Lower Bound on `rieszMean a c`**: for `1 < c` and `a : ArithmeticFunction ℝ`,
`log c * (opChebFloor c a / 2) ≤ rieszMean a c`. -/
theorem rieszMean_nat_ge_log_mul_opChebFloor_div_two {c : ℕ} (hc : 1 < c)
    (a : ArithmeticFunction ℝ) :
    Real.log c * (opChebFloor c a / 2) ≤ rieszMean a (c : ℝ) := by
  have hL : 0 ≤ Real.log c := (Real.log_pos (by exact_mod_cast hc)).le
  have hfloor := opChebFloor_le_two_inner_Op hc a vac
  rw [norm_vac_sq, mul_one] at hfloor
  rw [rieszMean_nat_eq_log_mul_inner_Op_vac hc a]
  nlinarith

/-- **Exact Vacuum Evaluation of `shiftSchurDiff c n vac`**: for `1 < c` and `1 < n < c`,
`shiftSchurDiff c n vac = n^(-1/2) * (chebFactor (cap (log c) (log n)) - 2 * (1 - log n / log c))`. -/
theorem shiftSchurDiff_vac_eq {c n : ℕ} (hc : 1 < c) (hn : 1 < n) (hnc : n < c) :
    shiftSchurDiff c n vac
      = (n : ℝ) ^ (-(1 / 2 : ℝ))
        * (Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n))
          - 2 * (1 - Real.log n / Real.log c)) := by
  have hdef := two_inner_rho_eq_chebFactor_sub_shiftSchurDiff hc hn vac
  have hvac : ⟪rho c n vac, vac⟫_ℝ
      = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.log n / Real.log c) := by
    rw [real_inner_comm, Cvs.WeilForm.WindowVacuumRieszMean.inner_vac_rho hc (by omega) hnc]
  rw [norm_vac_sq, mul_one, hvac] at hdef
  linarith

/-- **Chebyshev Envelope Majorization of the Riesz Weight**: for `1 < c` and `1 < n < c`,
`2 * (1 - log n / log c) ≤ chebFactor (cap (log c) (log n))`. -/
theorem two_mul_one_sub_log_div_le_chebFactor {c n : ℕ} (hc : 1 < c) (hn : 1 < n) (hnc : n < c) :
    2 * (1 - Real.log n / Real.log c)
      ≤ Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n)) := by
  have hpos : (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
  have hnonneg := shiftSchurDiff_nonneg hc hn vac
  rw [shiftSchurDiff_vac_eq hc hn hnc] at hnonneg
  have hsub : 0 ≤ Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n))
      - 2 * (1 - Real.log n / Real.log c) :=
    nonneg_of_mul_nonneg_right hnonneg hpos
  linarith

/-! ### 3. The 3-Cut Operator Decomposition (`OpChain` + `OpDimer`) & Dimer Square-Zero Algebra on `L²(𝕋)` -/

/-- Sub-`√c` higher-capacity chain operator `∑_{2 ≤ n < c, n² < c} a(n) • rho c n` on `L²(𝕋)`. -/
def OpChain (c : ℕ) (a : ArithmeticFunction ℝ) : L2 →L[ℝ] L2 :=
  ∑ n ∈ (Finset.Ico 2 c).filter (fun n => n ^ 2 < c), a n • rho c n

/-- Dimer-cut operator `∑_{2 ≤ n < c, c ≤ n²} a(n) • rho c n` on `L²(𝕋)`. -/
def OpDimer (c : ℕ) (a : ArithmeticFunction ℝ) : L2 →L[ℝ] L2 :=
  ∑ n ∈ (Finset.Ico 2 c).filter (fun n => c ≤ n ^ 2), a n • rho c n

/-- **The 3-Cut Operator Split on `L²(𝕋)`**: for `1 < c` and `a : ArithmeticFunction ℝ`,
`Op c a = a 1 • 1 + OpChain c a + OpDimer c a`. -/
theorem Op_eq_three_cut {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    Op c a = a 1 • (1 : L2 →L[ℝ] L2) + OpChain c a + OpDimer c a := by
  rw [Op_eq_one_add_sum_Ico hc a, add_assoc]
  congr 1
  unfold OpChain OpDimer
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico 2 c) (fun n => n ^ 2 < c)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [Finset.mem_filter, not_lt]

/-- **Quadratic-Form Bound on `OpChain c a`**: for `1 < c` and `f : L²(𝕋)`,
`|2 * ⟪OpChain c a f, f⟫| ≤ opChainOffDiag c a * ‖f‖²`. -/
theorem abs_two_inner_OpChain_le {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) (f : L2) :
    |2 * ⟪OpChain c a f, f⟫_ℝ| ≤ opChainOffDiag c a * ‖f‖ ^ 2 := by
  unfold OpChain opChainOffDiag
  rw [_root_.sum_apply, sum_inner, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  simp only [Finset.mem_filter, Finset.mem_Ico] at hn
  have hn1 : 1 < n := by omega
  rw [_root_.smul_apply, real_inner_smul_left,
    show 2 * (a n * ⟪rho c n f, f⟫_ℝ) = a n * (2 * ⟪rho c n f, f⟫_ℝ) by ring,
    abs_mul, mul_assoc |a n|, mul_assoc |a n|]
  exact mul_le_mul_of_nonneg_left (abs_two_inner_rho_le_chebFactor hc hn1 f) (abs_nonneg (a n))

/-- **Quadratic-Form Bound on `OpDimer c a`**: for `1 < c` and `f : L²(𝕋)`,
`|2 * ⟪OpDimer c a f, f⟫| ≤ opDimerOffDiag c a * ‖f‖²`. -/
theorem abs_two_inner_OpDimer_le {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) (f : L2) :
    |2 * ⟪OpDimer c a f, f⟫_ℝ| ≤ opDimerOffDiag c a * ‖f‖ ^ 2 := by
  unfold OpDimer opDimerOffDiag
  rw [_root_.sum_apply, sum_inner, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  simp only [Finset.mem_filter, Finset.mem_Ico] at hn
  rw [_root_.smul_apply, real_inner_smul_left,
    show 2 * (a n * ⟪rho c n f, f⟫_ℝ) = a n * (2 * ⟪rho c n f, f⟫_ℝ) by ring,
    abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_two_inner_rho_le_one_of_dimer hc hn.1.2 hn.2 f)
    (abs_nonneg (a n))

/-- **Pairwise Dimer Shift Annihilation**: for `1 < c` and `m, n : ℕ` with `c ≤ m²` and `c ≤ n²`,
`rho c m * rho c n = 0` on `L²(𝕋)` because `(m * n)² ≥ c²` implies `c ≤ m * n`. -/
theorem rho_mul_rho_eq_zero_of_dimer {c m n : ℕ} (hc : 1 < c)
    (hm : c ≤ m ^ 2) (hn : c ≤ n ^ 2) :
    rho c m * rho c n = 0 := by
  have hm0 : 1 ≤ m := by
    by_contra hle
    have hm_zero : m = 0 := by omega
    subst hm_zero
    omega
  have hn0 : 1 ≤ n := by
    by_contra hle
    have hn_zero : n = 0 := by omega
    subst hn_zero
    omega
  rw [← rho_mul hc hm0 hn0]
  have hsq : c ^ 2 ≤ (m * n) ^ 2 := by
    calc c ^ 2 = c * c := sq c
      _ ≤ m ^ 2 * n ^ 2 := Nat.mul_le_mul hm hn
      _ = (m * n) ^ 2 := (mul_pow m n 2).symm
  have hcmn : c ≤ m * n := by
    by_contra hlt
    have hlt' : m * n < c := not_le.mp hlt
    have hsq_lt : (m * n) ^ 2 < c ^ 2 := by nlinarith
    omega
  exact rho_eq_zero hc hcmn

/-- **Triple Shift Annihilation with Two Dimer Factors**: for `1 < c`, `c ≤ m²`, `c ≤ k²`, and any
`n : ℕ`, `rho c m * rho c n * rho c k = 0` on `L²(𝕋)`. -/
theorem rho_mul_rho_mul_rho_eq_zero_of_dimer {c m n k : ℕ} (hc : 1 < c)
    (hm : c ≤ m ^ 2) (hk : c ≤ k ^ 2) :
    rho c m * rho c n * rho c k = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [rho_zero, mul_zero, zero_mul]
  · have hm1 : 1 ≤ m := by
      by_contra hle
      have hm_zero : m = 0 := by omega
      subst hm_zero
      omega
    rw [← rho_mul hc hm1 hn1]
    have hmn : c ≤ (m * n) ^ 2 := by
      have hn_sq : 1 ≤ n ^ 2 := by nlinarith
      calc c = c * 1 := (Nat.mul_one c).symm
        _ ≤ m ^ 2 * n ^ 2 := Nat.mul_le_mul hm hn_sq
        _ = (m * n) ^ 2 := (mul_pow m n 2).symm
    exact rho_mul_rho_eq_zero_of_dimer hc hmn hk

/-- **Universal Dimer-Cut Mutual Annihilation**: for `1 < c` and ANY arithmetic functions `a, b`,
`OpDimer c a * OpDimer c b = 0` identically on `L²(𝕋)`. -/
theorem OpDimer_mul_OpDimer_eq_zero {c : ℕ} (hc : 1 < c)
    (a b : ArithmeticFunction ℝ) :
    OpDimer c a * OpDimer c b = 0 := by
  unfold OpDimer
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun n hn => ?_
  simp only [Finset.mem_filter] at hm hn
  rw [smul_mul_smul_comm, rho_mul_rho_eq_zero_of_dimer hc hm.2 hn.2, smul_zero]

/-- **Sandwich Annihilation `OpDimer c a * Op c b * OpDimer c d = 0`**: any operator sandwiched
between two dimer-cut operators vanishes identically on `L²(𝕋)`. -/
theorem OpDimer_mul_Op_mul_OpDimer_eq_zero {c : ℕ} (hc : 1 < c)
    (a b d : ArithmeticFunction ℝ) :
    OpDimer c a * Op c b * OpDimer c d = 0 := by
  unfold OpDimer Op
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun n _ => ?_
  simp only [Finset.mem_filter] at hm hk
  rw [smul_mul_smul_comm, smul_mul_smul_comm,
    rho_mul_rho_mul_rho_eq_zero_of_dimer hc hm.2 hk.2, smul_zero]

/-- **Dimer-Cut Square-Zero Identity**: for `1 < c` and `a : ArithmeticFunction ℝ`,
`OpDimer c a * OpDimer c a = 0`. -/
theorem OpDimer_sq_eq_zero {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    OpDimer c a * OpDimer c a = 0 :=
  OpDimer_mul_OpDimer_eq_zero hc a a

/-- **Exact Two-Term Inverse of `1 + OpDimer c a`**: for `1 < c` and `a : ArithmeticFunction ℝ`,
`(1 + OpDimer c a) * (1 - OpDimer c a) = 1`. -/
theorem one_add_OpDimer_mul_one_sub_OpDimer {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    (1 + OpDimer c a) * (1 - OpDimer c a) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one,
    OpDimer_sq_eq_zero hc a, sub_zero, sub_add_cancel]

/-- **Dimer Reduction of `Op c a * OpDimer c b`**: for `1 < c` and `a, b : ArithmeticFunction ℝ`,
the dimer part of `Op c a` annihilates `OpDimer c b`, leaving `(a 1 • 1 + OpChain c a) * OpDimer c b`. -/
theorem Op_mul_OpDimer_eq {c : ℕ} (hc : 1 < c) (a b : ArithmeticFunction ℝ) :
    Op c a * OpDimer c b = (a 1 • (1 : L2 →L[ℝ] L2) + OpChain c a) * OpDimer c b := by
  rw [Op_eq_three_cut hc a, add_mul, OpDimer_mul_OpDimer_eq_zero hc a b, add_zero]

/-- **Dimer Reduction of `OpDimer c a * Op c b`**: for `1 < c` and `a, b : ArithmeticFunction ℝ`,
`OpDimer c a * Op c b = OpDimer c a * (b 1 • 1 + OpChain c b)`. -/
theorem OpDimer_mul_Op_eq {c : ℕ} (hc : 1 < c) (a b : ArithmeticFunction ℝ) :
    OpDimer c a * Op c b = OpDimer c a * (b 1 • (1 : L2 →L[ℝ] L2) + OpChain c b) := by
  rw [Op_eq_three_cut hc b, mul_add, OpDimer_mul_OpDimer_eq_zero hc a b, add_zero]

/-- **3-Cut Product Expansion of `Op c a * Op c b`**: for `1 < c` and `a, b : ArithmeticFunction ℝ`,
the dimer-dimer interaction vanishes identically. -/
theorem Op_mul_Op_eq_three_cut {c : ℕ} (hc : 1 < c) (a b : ArithmeticFunction ℝ) :
    Op c a * Op c b
      = (a 1 • (1 : L2 →L[ℝ] L2) + OpChain c a) * Op c b
        + OpDimer c a * (b 1 • (1 : L2 →L[ℝ] L2) + OpChain c b) := by
  rw [Op_eq_three_cut hc a, add_mul, OpDimer_mul_Op_eq hc a b]

/-- **Exact 3-Cut Isolation of `OpDimer c μ * (1 + OpChain c ζ)`**: for `1 < c`,
`OpDimer c μ * (1 + OpChain c ζ) = 1 - (1 + OpChain c μ) * Op c ζ`. -/
theorem OpDimer_moebius_mul_one_add_OpChain_zeta_eq {c : ℕ} (hc : 1 < c) :
    OpDimer c (μ : ArithmeticFunction ℝ) * (1 + OpChain c (ζ : ArithmeticFunction ℝ))
      = 1 - (1 + OpChain c (μ : ArithmeticFunction ℝ)) * Op c (ζ : ArithmeticFunction ℝ) := by
  have h1 := Op_mul_Op_eq_three_cut hc (μ : ArithmeticFunction ℝ) (ζ : ArithmeticFunction ℝ)
  have hmul : Op c (μ : ArithmeticFunction ℝ) * Op c (ζ : ArithmeticFunction ℝ) = 1 := by
    rw [Op_mul hc, ArithmeticFunction.coe_moebius_mul_coe_zeta, Op_one hc]
  have hμ1 : (μ : ArithmeticFunction ℝ) 1 = 1 := by simp
  have hζ1 : (ζ : ArithmeticFunction ℝ) 1 = 1 := by simp
  rw [hmul, hμ1, hζ1, one_smul] at h1
  exact eq_sub_of_add_eq' h1.symm

/-- **Exact 3-Cut Formula for `OpDimer c μ` Purely in Terms of `OpChain c μ` and `Op c ζ`**:
since `OpDimer c μ * Op c ζ * OpDimer c μ = 0`, the high-range dimer Möbius operator `OpDimer c μ`
is determined identically by the sub-`√c` chain operator `1 + OpChain c μ` and `Op c ζ`! -/
theorem OpDimer_moebius_eq_one_add_OpChain_mul {c : ℕ} (hc : 1 < c) :
    OpDimer c (μ : ArithmeticFunction ℝ)
      = (1 + OpChain c (μ : ArithmeticFunction ℝ))
        * (1 - Op c (ζ : ArithmeticFunction ℝ) * (1 + OpChain c (μ : ArithmeticFunction ℝ))) := by
  have h3 := Op_eq_three_cut hc (μ : ArithmeticFunction ℝ)
  have hμ1 : (μ : ArithmeticFunction ℝ) 1 = 1 := by simp
  rw [hμ1, one_smul] at h3
  have hsub :
      OpDimer c (μ : ArithmeticFunction ℝ)
        = Op c (μ : ArithmeticFunction ℝ) - (1 + OpChain c (μ : ArithmeticFunction ℝ)) :=
    eq_sub_of_add_eq' h3.symm
  have hmul_left :
      Op c (μ : ArithmeticFunction ℝ) * Op c (ζ : ArithmeticFunction ℝ) = 1 := by
    rw [Op_mul hc, ArithmeticFunction.coe_moebius_mul_coe_zeta, Op_one hc]
  have hmul_right :
      Op c (ζ : ArithmeticFunction ℝ) * Op c (μ : ArithmeticFunction ℝ) = 1 := by
    rw [Op_mul hc, ArithmeticFunction.coe_zeta_mul_coe_moebius, Op_one hc]
  have hzero := OpDimer_mul_Op_mul_OpDimer_eq_zero hc
    (μ : ArithmeticFunction ℝ) (ζ : ArithmeticFunction ℝ) (μ : ArithmeticFunction ℝ)
  have hleft :
      OpDimer c (μ : ArithmeticFunction ℝ) * Op c (ζ : ArithmeticFunction ℝ)
        = 1 - (1 + OpChain c (μ : ArithmeticFunction ℝ)) * Op c (ζ : ArithmeticFunction ℝ) := by
    rw [hsub, sub_mul, hmul_left]
  have hright :
      Op c (ζ : ArithmeticFunction ℝ) * OpDimer c (μ : ArithmeticFunction ℝ)
        = 1 - Op c (ζ : ArithmeticFunction ℝ) * (1 + OpChain c (μ : ArithmeticFunction ℝ)) := by
    rw [hsub, mul_sub, hmul_right]
  rw [hleft, sub_mul, one_mul, mul_assoc, hright] at hzero
  exact sub_eq_zero.mp hzero

/-- **Newton–Schulz 3-Cut Factorization of `Op c μ` on `L²(𝕋)`**: for every `1 < c`,
`Op c μ = (1 + OpChain c μ) * (2 • 1 - Op c ζ * (1 + OpChain c μ))`, eliminating `OpDimer c μ`
completely in favor of the sub-`√c` operator `1 + OpChain c μ` and `Op c ζ`! -/
theorem Op_moebius_eq_newton_schulz_three_cut {c : ℕ} (hc : 1 < c) :
    Op c (μ : ArithmeticFunction ℝ)
      = (1 + OpChain c (μ : ArithmeticFunction ℝ))
        * ((2 : ℝ) • (1 : L2 →L[ℝ] L2)
          - Op c (ζ : ArithmeticFunction ℝ) * (1 + OpChain c (μ : ArithmeticFunction ℝ))) := by
  have h3 := Op_eq_three_cut hc (μ : ArithmeticFunction ℝ)
  have hμ1 : (μ : ArithmeticFunction ℝ) 1 = 1 := by simp
  rw [hμ1, one_smul, OpDimer_moebius_eq_one_add_OpChain_mul hc] at h3
  calc Op c (μ : ArithmeticFunction ℝ)
      = (1 + OpChain c (μ : ArithmeticFunction ℝ)) * 1
          + (1 + OpChain c (μ : ArithmeticFunction ℝ))
            * (1 - Op c (ζ : ArithmeticFunction ℝ) * (1 + OpChain c (μ : ArithmeticFunction ℝ))) := by
        rw [mul_one, ← h3]
    _ = (1 + OpChain c (μ : ArithmeticFunction ℝ))
          * (1 + (1 - Op c (ζ : ArithmeticFunction ℝ) * (1 + OpChain c (μ : ArithmeticFunction ℝ)))) :=
        (mul_add _ _ _).symm
    _ = (1 + OpChain c (μ : ArithmeticFunction ℝ))
          * ((2 : ℝ) • (1 : L2 →L[ℝ] L2)
            - Op c (ζ : ArithmeticFunction ℝ) * (1 + OpChain c (μ : ArithmeticFunction ℝ))) := by
        rw [two_smul, add_sub_assoc]

/-- For `1 < c` and `n : ℕ`, `n² < c ↔ n ≤ Nat.sqrt (c - 1)`. -/
theorem sq_lt_iff_le_sqrt_pred {c n : ℕ} (hc : 1 < c) :
    n ^ 2 < c ↔ n ≤ Nat.sqrt (c - 1) := by
  rw [Nat.le_sqrt, ← sq]
  omega

/-- **Exact Identification of `1 + OpChain c μ` with `Op c (truncMoebius (Nat.sqrt (c - 1)))`**:
for `1 < c`, the sub-`√c` Möbius operator `1 + OpChain c μ` is the window Dirichlet operator of
`truncMoebius (Nat.sqrt (c - 1))`. -/
theorem one_add_OpChain_moebius_eq_Op_truncMoebius {c : ℕ} (hc : 1 < c) :
    (1 : L2 →L[ℝ] L2) + OpChain c (μ : ArithmeticFunction ℝ)
      = Op c (truncMoebius (Nat.sqrt (c - 1))) := by
  rw [Op_eq_one_add_sum_Ico hc (truncMoebius (Nat.sqrt (c - 1)))]
  have h1_le : 1 ≤ Nat.sqrt (c - 1) := Nat.sqrt_pos.mpr (by omega)
  have h1 : truncMoebius (Nat.sqrt (c - 1)) 1 = 1 := by
    simp [truncMoebius_apply, h1_le]
  rw [h1, one_smul]
  congr 1
  unfold OpChain
  have hsub : (Finset.Ico 2 c).filter (fun n => n ^ 2 < c) ⊆ Finset.Ico 2 c :=
    Finset.filter_subset _ _
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_filter, sq_lt_iff_le_sqrt_pred hc] at hn
    simp [truncMoebius_apply, hn.2]
  · intro n hn hnot
    simp only [Finset.mem_filter, hn, true_and, sq_lt_iff_le_sqrt_pred hc] at hnot
    simp [truncMoebius_apply, hnot]

/-- **Dirichlet Convolution Form of the 3-Cut Newton–Schulz Identity for `Op c μ`**:
for `1 < c`, `Op c μ = Op c (truncMoebius M₀ * (2 • 1 - ζ * truncMoebius M₀))` where `M₀ = Nat.sqrt (c - 1)`. -/
theorem Op_moebius_eq_Op_truncMoebius_newton_schulz {c : ℕ} (hc : 1 < c) :
    Op c (μ : ArithmeticFunction ℝ)
      = Op c (truncMoebius (Nat.sqrt (c - 1))
          * ((2 : ℝ) • (1 : ArithmeticFunction ℝ)
            - (ζ : ArithmeticFunction ℝ) * truncMoebius (Nat.sqrt (c - 1)))) := by
  rw [Op_moebius_eq_newton_schulz_three_cut hc,
    one_add_OpChain_moebius_eq_Op_truncMoebius hc,
    ← Op_one hc, ← Op_smul, Op_mul hc (ζ : ArithmeticFunction ℝ), ← Op_sub, Op_mul hc]

/-- For `M₀ ≤ k`, `partialSumHalf (truncMoebius M₀) k = partialSumHalf μ M₀`. -/
theorem partialSumHalf_truncMoebius_eq_of_le {M₀ k : ℕ} (hM : M₀ ≤ k) :
    partialSumHalf (truncMoebius M₀) k = partialSumHalf (μ : ArithmeticFunction ℝ) M₀ := by
  unfold partialSumHalf
  have hsub : Finset.Icc 1 M₀ ⊆ Finset.Icc 1 k := Finset.Icc_subset_Icc_right hM
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hnM : n ≤ M₀ := (Finset.mem_Icc.mp hn).2
    simp [truncMoebius_apply, hnM]
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hnM : ¬ n ≤ M₀ := by omega
    simp [truncMoebius_apply, hnM]

/-- For `n ≤ M₀`, `(1 - truncMoebius M₀ * ζ) n = 0`. -/
theorem one_sub_truncMoebius_mul_zeta_apply_of_le {M₀ n : ℕ} (hn : n ≤ M₀) :
    ((1 : ArithmeticFunction ℝ) - truncMoebius M₀ * (ζ : ArithmeticFunction ℝ)) n = 0 := by
  change (1 : ArithmeticFunction ℝ) n - (truncMoebius M₀ * (ζ : ArithmeticFunction ℝ)) n = 0
  rw [truncMoebius_mul_zeta_apply_of_le hn, sub_self]

/-- **Dimer Square-Zero Vanishing in `ArithmeticFunction ℝ`**: for any `M₀ : ℕ` and `n < (M₀ + 1)²`,
`((1 - truncMoebius M₀ * ζ) * (1 - truncMoebius M₀ * ζ)) n = 0`. -/
theorem one_sub_truncMoebius_mul_zeta_sq_apply_eq_zero {M₀ n : ℕ} (hn : n < (M₀ + 1) ^ 2) :
    (((1 : ArithmeticFunction ℝ) - truncMoebius M₀ * (ζ : ArithmeticFunction ℝ))
      * ((1 : ArithmeticFunction ℝ) - truncMoebius M₀ * (ζ : ArithmeticFunction ℝ))) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp_eq := Nat.mem_divisorsAntidiagonal.mp hp
  have hle : p.1 ≤ M₀ ∨ p.2 ≤ M₀ := by
    by_contra hnot
    rw [not_or, not_le, not_le] at hnot
    have hmul : (M₀ + 1) ^ 2 ≤ p.1 * p.2 := by
      calc (M₀ + 1) ^ 2 = (M₀ + 1) * (M₀ + 1) := sq (M₀ + 1)
        _ ≤ p.1 * p.2 := Nat.mul_le_mul hnot.1 hnot.2
    omega
  rcases hle with h1 | h2
  · rw [one_sub_truncMoebius_mul_zeta_apply_of_le h1, zero_mul]
  · rw [one_sub_truncMoebius_mul_zeta_apply_of_le h2, mul_zero]

/-- **Pointwise 3-Cut Newton–Schulz Identity for `μ(n)`**: for any `M₀ : ℕ` and `n < (M₀ + 1)²`,
`μ(n) = 2 * truncMoebius M₀ n - (truncMoebius M₀ * truncMoebius M₀ * ζ) n`. -/
theorem moebius_apply_eq_newton_schulz_of_lt_sq {M₀ n : ℕ} (hn : n < (M₀ + 1) ^ 2) :
    (μ : ArithmeticFunction ℝ) n
      = (2 • truncMoebius M₀
          - truncMoebius M₀ * truncMoebius M₀ * (ζ : ArithmeticFunction ℝ)) n := by
  have hconv :
      (((1 : ArithmeticFunction ℝ) - truncMoebius M₀ * (ζ : ArithmeticFunction ℝ))
        * ((1 : ArithmeticFunction ℝ) - truncMoebius M₀ * (ζ : ArithmeticFunction ℝ))
        * (μ : ArithmeticFunction ℝ)) n = 0 := by
    rw [ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp_eq := Nat.mem_divisorsAntidiagonal.mp hp
    have hp1_le : p.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hp_eq.2) ⟨p.2, hp_eq.1.symm⟩
    rw [one_sub_truncMoebius_mul_zeta_sq_apply_eq_zero (lt_of_le_of_lt hp1_le hn), zero_mul]
  have halg :
      ((1 : ArithmeticFunction ℝ) - truncMoebius M₀ * (ζ : ArithmeticFunction ℝ))
          * ((1 : ArithmeticFunction ℝ) - truncMoebius M₀ * (ζ : ArithmeticFunction ℝ))
          * (μ : ArithmeticFunction ℝ)
        = (μ : ArithmeticFunction ℝ)
          - (2 • truncMoebius M₀
              - truncMoebius M₀ * truncMoebius M₀ * (ζ : ArithmeticFunction ℝ)) := by
    have hzm : (ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ) = 1 :=
      ArithmeticFunction.coe_zeta_mul_coe_moebius
    rw [two_smul]
    linear_combination
      (-2 * truncMoebius M₀
        + truncMoebius M₀ * truncMoebius M₀ * (ζ : ArithmeticFunction ℝ))
      * hzm
  rw [halg] at hconv
  change (μ : ArithmeticFunction ℝ) n
      - (2 • truncMoebius M₀
          - truncMoebius M₀ * truncMoebius M₀ * (ζ : ArithmeticFunction ℝ)) n = 0 at hconv
  exact sub_eq_zero.mp hconv

/-- **Exact Quadratic-Step (`√k → k`) Newton–Schulz Formula for `partialSumHalf μ k`**:
for every `k : ℕ`, `partialSumHalf μ k = 2 * partialSumHalf μ (Nat.sqrt k) - partialSumHalf (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k) * ζ) k`. -/
theorem partialSumHalf_moebius_eq_two_mul_sqrt_sub {k : ℕ} :
    partialSumHalf (μ : ArithmeticFunction ℝ) k
      = 2 * partialSumHalf (μ : ArithmeticFunction ℝ) (Nat.sqrt k)
        - partialSumHalf
            (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)
              * (ζ : ArithmeticFunction ℝ)) k := by
  have hlt : k < (Nat.sqrt k + 1) ^ 2 := Nat.lt_succ_sqrt' k
  have heq :
      partialSumHalf (μ : ArithmeticFunction ℝ) k
        = partialSumHalf
            ((2 : ℝ) • truncMoebius (Nat.sqrt k)
              - truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)
                * (ζ : ArithmeticFunction ℝ)) k := by
    unfold partialSumHalf
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnk : n ≤ k := (Finset.mem_Icc.mp hn).2
    rw [moebius_apply_eq_newton_schulz_of_lt_sq (lt_of_le_of_lt hnk hlt), two_smul, two_smul]
  rw [heq, partialSumHalf_sub, partialSumHalf_smul,
    partialSumHalf_truncMoebius_eq_of_le (Nat.sqrt_le_self k)]

/-- **Exact 3-Cut Decomposition of `moebiusVac c` on `L²(𝕋)`**: for `1 < c`,
`moebiusVac c = vac + OpChain c μ vac + OpDimer c μ vac`. -/
theorem moebiusVac_eq_three_cut {c : ℕ} (hc : 1 < c) :
    moebiusVac c
      = vac + OpChain c (μ : ArithmeticFunction ℝ) vac
        + OpDimer c (μ : ArithmeticFunction ℝ) vac := by
  unfold moebiusVac
  have hμ1 : (μ : ArithmeticFunction ℝ) 1 = 1 := by simp
  rw [Op_eq_three_cut hc (μ : ArithmeticFunction ℝ), hμ1, one_smul,
    _root_.add_apply, _root_.add_apply,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]

/-! ### 4. Direct Spectral Criteria for `RiemannHypothesis` -/

/-- For every real `1 < x`, the ceiling interpolation step `M ⌈x⌉₊ - M x` is bounded above by `S0 - 2`. -/
theorem M_ceil_sub_M_le {x : ℝ} (hx : 1 < x) :
    M (⌈x⌉₊ : ℝ) - M x ≤ S0 - 2 := by
  have hx0 : 0 < x := by linarith
  have hsq := four_mul_sqrt_ceil_sub_sqrt_le_two hx
  have hlog : Real.log x ≤ Real.log (⌈x⌉₊ : ℝ) := Real.log_le_log hx0 (Nat.le_ceil x)
  have harch :
      Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * (Real.log (⌈x⌉₊ : ℝ) - Real.log x) ≤ 0 := by
    have := archSymbol_zero_nonpos
    nlinarith
  have htriv1 := trivTail_le_S0_sub_four hx.le
  have htriv2 := trivTail_nonneg ⌈x⌉₊
  rw [M_sub_M_eq]
  linarith

/-- **Direct Chebyshev-Budget Criterion for `RiemannHypothesis`**: if the prime staircase budget
`log c * atomBudget c c (Nat.clog 2 c)` is bounded above by `2 * M c + A * log c + B` for all `1 < c`
(`0 ≤ A`), then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_atomBudget_le_two_M_add_linear {A B : ℝ} (hA : 0 ≤ A)
    (hB : ∀ c : ℕ, 1 < c →
      Real.log c * atomBudget c c (Nat.clog 2 c) ≤ 2 * M c + A * Real.log c + B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_M_sub_Psihalf_ge_neg_linear
    (A := A / 2) (B := A / 2 + B / 2 + S0 - 2) fun x hx => ?_
  have hc : 1 < ⌈x⌉₊ := one_lt_ceil_of_one_lt hx
  have hG := G_log_ge_two_M_sub_log_mul_atomBudget hc (Nat.le_succ _) (Nat.le_succ _)
  have hGL := Cvs.Route.OneCellChebyshevInequality.G_log_eq (by exact_mod_cast hc.le : (1 : ℝ) ≤ ⌈x⌉₊)
  have hbc := hB ⌈x⌉₊ hc
  have hinterp := M_sub_Psihalf_ge_ceil_sub_interp hx
  have hstep := M_ceil_sub_M_le hx
  have hceil := log_ceil_le_log_add_one hx
  have hlog : -(A / 2) * (Real.log x + 1) ≤ -(A / 2) * Real.log (⌈x⌉₊ : ℝ) := by
    nlinarith
  linarith

/-- **Direct `moebiusVac` `L²(𝕋)` Norm Criterion for `RiemannHypothesis`**: if
`log c * ‖moebiusVac c‖² ≤ A * log c + B` for all `1 < c` (`0 ≤ A`), then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_log_mul_norm_moebiusVac_sq_le {A B : ℝ} (hA : 0 ≤ A)
    (h : ∀ c : ℕ, 1 < c → Real.log c * ‖moebiusVac c‖ ^ 2 ≤ A * Real.log c + B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_sum_moebius_sq_le_linear (A := A) (B := B) hA fun x hx => ?_
  have hc : 1 < ⌈x⌉₊ := one_lt_ceil_of_one_lt hx
  have hnorm_eq :
      Real.log (⌈x⌉₊ : ℝ) * ‖moebiusVac ⌈x⌉₊‖ ^ 2
        = ∑ k ∈ Finset.Ico 1 ⌈x⌉₊,
            logStep k * partialSumHalf (μ : ArithmeticFunction ℝ) k ^ 2 := by
    unfold moebiusVac
    rw [norm_sq_Op_vac_eq_rieszCorrelation hc (μ : ArithmeticFunction ℝ),
      log_mul_rieszCorrelation_eq_sum_partialSumHalf hc]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [← hnorm_eq]
  exact h ⌈x⌉₊ hc

/-! ### 5. Asymptotic Behavior (`c → ∞`), Finite-Scale Absorption, and 3-Cut Square Factorization -/

/-- **Universal Finite-Scale Absorption**: if `0 ≤ g c` for all `c` and `f c ≤ g c` eventually for
`c₀ ≤ c`, then there exists an explicit nonnegative constant `B₀ ≥ 0` (bounding the finite range
`c < c₀`) such that `f c ≤ g c + B₀` for all `c : ℕ`. -/
theorem exists_nonneg_bound_of_eventually_nat (f g : ℕ → ℝ) (c₀ : ℕ)
    (hg : ∀ c : ℕ, 0 ≤ g c) (h : ∀ c : ℕ, c₀ ≤ c → f c ≤ g c) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ c : ℕ, f c ≤ g c + B₀ := by
  refine ⟨∑ k ∈ Finset.range c₀, max (f k) 0,
    Finset.sum_nonneg (fun k _ => le_max_right _ _), fun c => ?_⟩
  rcases le_or_gt c₀ c with hc | hc
  · have hB₀ : 0 ≤ ∑ k ∈ Finset.range c₀, max (f k) 0 :=
      Finset.sum_nonneg (fun k _ => le_max_right _ _)
    linarith [h c hc]
  · have hmem : c ∈ Finset.range c₀ := Finset.mem_range.mpr hc
    have hle : max (f c) 0 ≤ ∑ k ∈ Finset.range c₀, max (f k) 0 :=
      Finset.single_le_sum (fun k _ => le_max_right (f k) 0) hmem
    linarith [le_max_left (f c) 0, hg c]

/-- **Asymptotic `moebiusVac` Norm Criterion for `RiemannHypothesis`**: if there exist `c₀ : ℕ`
and `A, B : ℝ` (`0 ≤ A`) such that `log c * ‖moebiusVac c‖² ≤ A * log c + B` for all `c ≥ c₀`
with `1 < c`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_eventually_norm_moebiusVac_sq_le {c₀ : ℕ} {A B : ℝ} (hA : 0 ≤ A)
    (h : ∀ c : ℕ, c₀ ≤ c → 1 < c → Real.log c * ‖moebiusVac c‖ ^ 2 ≤ A * Real.log c + B) :
    RiemannHypothesis := by
  let f : ℕ → ℝ := fun c => if 1 < c then Real.log c * ‖moebiusVac c‖ ^ 2 else 0
  let g : ℕ → ℝ := fun c => A * Real.log c + max B 0
  have hg : ∀ c : ℕ, 0 ≤ g c := fun c => by
    dsimp [g]
    rcases le_or_gt c 1 with hc1 | hc1
    · interval_cases c <;> simp
    · have hL : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1.le)
      nlinarith [le_max_right B 0]
  have hev : ∀ c : ℕ, c₀ ≤ c → f c ≤ g c := fun c hc₀ => by
    dsimp [f, g]
    split_ifs with hc1
    · linarith [h c hc₀ hc1, le_max_left B 0]
    · exact hg c
  obtain ⟨B₀, _, hB₀⟩ := exists_nonneg_bound_of_eventually_nat f g c₀ hg hev
  refine riemannHypothesis_of_log_mul_norm_moebiusVac_sq_le (A := A) (B := max B 0 + B₀) hA
    fun c hc => ?_
  have hfc := hB₀ c
  dsimp [f, g] at hfc
  rw [ite_eq_left hc] at hfc
  linarith

/-- **Asymptotic Chebyshev-Budget Criterion for `RiemannHypothesis`**: if there exist `c₀ : ℕ`
and `A, B : ℝ` (`0 ≤ A`) such that `log c * atomBudget c c (Nat.clog 2 c) ≤ 2 * M c + A * log c + B`
for all `c ≥ c₀` with `1 < c`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_eventually_atomBudget_le_two_M_add_linear {c₀ : ℕ} {A B : ℝ}
    (hA : 0 ≤ A)
    (h : ∀ c : ℕ, c₀ ≤ c → 1 < c →
      Real.log c * atomBudget c c (Nat.clog 2 c) ≤ 2 * M c + A * Real.log c + B) :
    RiemannHypothesis := by
  let f : ℕ → ℝ := fun c =>
    if 1 < c then Real.log c * atomBudget c c (Nat.clog 2 c) - 2 * M c else 0
  let g : ℕ → ℝ := fun c => A * Real.log c + max B 0
  have hg : ∀ c : ℕ, 0 ≤ g c := fun c => by
    dsimp [g]
    rcases le_or_gt c 1 with hc1 | hc1
    · interval_cases c <;> simp
    · have hL : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1.le)
      nlinarith [le_max_right B 0]
  have hev : ∀ c : ℕ, c₀ ≤ c → f c ≤ g c := fun c hc₀ => by
    dsimp [f, g]
    split_ifs with hc1
    · linarith [h c hc₀ hc1, le_max_left B 0]
    · exact hg c
  obtain ⟨B₀, _, hB₀⟩ := exists_nonneg_bound_of_eventually_nat f g c₀ hg hev
  refine riemannHypothesis_of_atomBudget_le_two_M_add_linear (A := A) (B := max B 0 + B₀) hA
    fun c hc => ?_
  have hfc := hB₀ c
  dsimp [f, g] at hfc
  rw [ite_eq_left hc] at hfc
  linarith

/-- **Asymptotic Sub-Power `partialSumHalf μ` Criterion for `RiemannHypothesis`**: if for every
`0 < ε < 1 / 2` there exist a threshold `k₀ : ℕ` and `C ≥ 0` such that
`|partialSumHalf μ k| ≤ C * k ^ ε` for all `k ≥ k₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_eventually_abs_partialSumHalf_moebius_le_rpow
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (k₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ k → 1 ≤ k →
        |partialSumHalf (μ : ArithmeticFunction ℝ) k| ≤ C * (k : ℝ) ^ ε) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_abs_partialSumHalf_moebius_le_rpow fun ε hε0 hε_half => ?_
  obtain ⟨k₀, C, hC, hk₀⟩ := h ε hε0 hε_half
  set B₀ : ℝ := ∑ j ∈ Finset.range k₀, |partialSumHalf (μ : ArithmeticFunction ℝ) j|
  have hB₀ : 0 ≤ B₀ := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  refine ⟨C + B₀, add_nonneg hC hB₀, fun k hk1 => ?_⟩
  have hkrpow : (1 : ℝ) ≤ (k : ℝ) ^ ε :=
    Real.one_le_rpow (by exact_mod_cast hk1) hε0.le
  rcases le_or_gt k₀ k with hk | hk
  · calc |partialSumHalf (μ : ArithmeticFunction ℝ) k|
        ≤ C * (k : ℝ) ^ ε := hk₀ k hk hk1
      _ ≤ (C + B₀) * (k : ℝ) ^ ε := by nlinarith
  · have hmem : k ∈ Finset.range k₀ := Finset.mem_range.mpr hk
    have hle : |partialSumHalf (μ : ArithmeticFunction ℝ) k| ≤ B₀ :=
      Finset.single_le_sum (f := fun j => |partialSumHalf (μ : ArithmeticFunction ℝ) j|)
        (fun j _ => abs_nonneg _) hmem
    calc |partialSumHalf (μ : ArithmeticFunction ℝ) k|
        ≤ B₀ * 1 := by linarith
      _ ≤ (C + B₀) * (k : ℝ) ^ ε := by nlinarith

/-- For every `k : ℕ`, `|partialSumHalf μ k| ≤ partialSumHalf ζ k`. -/
theorem abs_partialSumHalf_moebius_le_partialSumHalf_zeta (k : ℕ) :
    |partialSumHalf (μ : ArithmeticFunction ℝ) k|
      ≤ partialSumHalf (ζ : ArithmeticFunction ℝ) k := by
  unfold partialSumHalf
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  have hrp : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [abs_mul, abs_of_nonneg hrp, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hn0, Nat.cast_one, one_mul,
    ArithmeticFunction.intCoe_apply]
  have h1 := mul_le_mul_of_nonneg_right (abs_moebius_le_one n) hrp
  rwa [one_mul] at h1

/-- For every `k : ℕ`, `|partialSumHalf μ k| ≤ 2 * √k`. -/
theorem abs_partialSumHalf_moebius_le_two_sqrt (k : ℕ) :
    |partialSumHalf (μ : ArithmeticFunction ℝ) k| ≤ 2 * Real.sqrt (k : ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · unfold partialSumHalf
    simp
  · have h1 := abs_partialSumHalf_moebius_le_partialSumHalf_zeta k
    have h2 := partialSumHalf_zeta_le_two_mul_sqrt_sub_one hk
    linarith

/-- For every `k : ℕ`, `√(Nat.sqrt k) ≤ (k : ℝ) ^ (1 / 4)`. -/
theorem sqrt_nat_sqrt_le_rpow_one_fourth (k : ℕ) :
    Real.sqrt (Nat.sqrt k : ℝ) ≤ (k : ℝ) ^ (1 / 4 : ℝ) := by
  have hsq : (Nat.sqrt k : ℝ) ≤ Real.sqrt (k : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _), ← Nat.cast_pow, sq]
    exact_mod_cast Nat.sqrt_le k
  calc Real.sqrt (Nat.sqrt k : ℝ)
      ≤ Real.sqrt (Real.sqrt (k : ℝ)) := Real.sqrt_le_sqrt hsq
    _ = (k : ℝ) ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg k)]
      norm_num

/-- **Unconditional `O(k^{1/4})` Bound on the Sub-`√k` Cut `partialSumHalf μ (Nat.sqrt k)`**:
for every `k : ℕ`, `|partialSumHalf μ (Nat.sqrt k)| ≤ 2 * k ^ (1 / 4)` (exponent `1 / 4 < 1 / 2`). -/
theorem abs_partialSumHalf_moebius_sqrt_le_two_mul_rpow_one_fourth (k : ℕ) :
    |partialSumHalf (μ : ArithmeticFunction ℝ) (Nat.sqrt k)|
      ≤ 2 * (k : ℝ) ^ (1 / 4 : ℝ) := by
  calc |partialSumHalf (μ : ArithmeticFunction ℝ) (Nat.sqrt k)|
      ≤ 2 * Real.sqrt (Nat.sqrt k : ℝ) := abs_partialSumHalf_moebius_le_two_sqrt (Nat.sqrt k)
    _ ≤ 2 * (k : ℝ) ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left (sqrt_nat_sqrt_le_rpow_one_fourth k) (by norm_num)

/-- **Exact Multiplicative Square Factorization for `partialSumHalf (truncMoebius M₀ * truncMoebius M₀) k`**:
whenever `M₀ ^ 2 ≤ k` (in particular for `M₀ = Nat.sqrt k`),
`partialSumHalf (truncMoebius M₀ * truncMoebius M₀) k = partialSumHalf μ M₀ ^ 2 ≥ 0`. -/
theorem partialSumHalf_truncMoebius_sq_eq_sq {M₀ k : ℕ} (hk : M₀ ^ 2 ≤ k) :
    partialSumHalf (truncMoebius M₀ * truncMoebius M₀) k
      = partialSumHalf (μ : ArithmeticFunction ℝ) M₀ ^ 2 := by
  rw [partialSumHalf_mul_eq_sum_div_left]
  have h1 :
      ∑ m ∈ Finset.Icc 1 k,
          truncMoebius M₀ m * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * partialSumHalf (truncMoebius M₀) (k / m)
        = ∑ m ∈ Finset.Icc 1 k,
            truncMoebius M₀ m * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * partialSumHalf (μ : ArithmeticFunction ℝ) M₀ := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    rcases le_or_gt m M₀ with hmM | hmM
    · have hdiv : M₀ ≤ k / m := by
        rw [Nat.le_div_iff_mul_le hm1]
        calc M₀ * m ≤ M₀ * M₀ := Nat.mul_le_mul_left M₀ hmM
          _ = M₀ ^ 2 := (sq M₀).symm
          _ ≤ k := hk
      rw [partialSumHalf_truncMoebius_eq_of_le hdiv]
    · have h0 : truncMoebius M₀ m = 0 := by simp [truncMoebius_apply, not_le.mpr hmM]
      rw [h0, zero_mul, zero_mul, zero_mul]
  have hM_le_k : M₀ ≤ k := by
    rcases Nat.eq_zero_or_pos M₀ with rfl | hM0
    · exact Nat.zero_le k
    · calc M₀ = M₀ * 1 := (mul_one M₀).symm
        _ ≤ M₀ * M₀ := Nat.mul_le_mul_left M₀ hM0
        _ = M₀ ^ 2 := (sq M₀).symm
        _ ≤ k := hk
  rw [h1, ← Finset.sum_mul]
  change partialSumHalf (truncMoebius M₀) k * partialSumHalf (μ : ArithmeticFunction ℝ) M₀ = _
  rw [partialSumHalf_truncMoebius_eq_of_le hM_le_k, sq]

/-- General Dirichlet convolution formula for `1 / n`-weighted sums:
`∑_{j=1}^k (a * b)(j) / j = ∑_{m=1}^k (a(m) / m) * (∑_{n=1}^{k/m} b(n) / n)`. -/
theorem sum_div_mul_eq_sum_div_left (a b : ArithmeticFunction ℝ) (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, (a * b) j / (j : ℝ)
      = ∑ m ∈ Finset.Icc 1 k,
          (a m / (m : ℝ)) * (∑ n ∈ Finset.Icc 1 (k / m), b n / (n : ℝ)) := by
  simp_rw [ArithmeticFunction.mul_apply, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun p => ⟨p.2.1, p.2.2⟩)
    (fun q => ⟨q.1 * q.2, (q.1, q.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, m, n⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hp ⊢
    obtain ⟨⟨hj1, hjk⟩, hmn, hj0⟩ := hp
    subst hmn
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h => by simp [h] at hj0
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h => by simp [h] at hj0
    exact ⟨⟨hm1, le_trans (Nat.le_mul_of_pos_right m hn1) hjk⟩,
      hn1, (Nat.le_div_iff_mul_le hm1).mpr (by rw [mul_comm]; exact hjk)⟩
  · rintro ⟨m, n⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hq ⊢
    obtain ⟨⟨hm1, _⟩, hn1, hnk⟩ := hq
    have hmn : n * m ≤ k := (Nat.le_div_iff_mul_le hm1).mp hnk
    exact ⟨⟨by nlinarith, by rw [mul_comm]; exact hmn⟩, trivial, by positivity⟩
  · rintro ⟨j, m, n⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨_, hmn, _⟩ := hp
    ext <;> simp [hmn]
  · rintro ⟨m, n⟩ _
    rfl
  · rintro ⟨j, m, n⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨_, rfl, _⟩ := hp
    push_cast
    ring

/-- For `M₀ ≤ k`, `∑_{n=1}^k truncMoebius M₀ n / n = ∑_{n=1}^{M₀} μ(n) / n`. -/
theorem sum_truncMoebius_div_eq_of_le {M₀ k : ℕ} (hM : M₀ ≤ k) :
    ∑ n ∈ Finset.Icc 1 k, truncMoebius M₀ n / (n : ℝ)
      = ∑ n ∈ Finset.Icc 1 M₀, (μ n : ℝ) / (n : ℝ) := by
  have hsub : Finset.Icc 1 M₀ ⊆ Finset.Icc 1 k := Finset.Icc_subset_Icc_right hM
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hnM : n ≤ M₀ := (Finset.mem_Icc.mp hn).2
    simp [truncMoebius_apply, hnM]
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hnM : ¬ n ≤ M₀ := by omega
    simp [truncMoebius_apply, hnM]

/-- **Exact Multiplicative Square Factorization for `∑_{m=1}^k (truncMoebius M₀ * truncMoebius M₀)(m) / m`**:
whenever `M₀ ^ 2 ≤ k` (in particular for `M₀ = Nat.sqrt k`),
`∑_{m=1}^k (truncMoebius M₀)²(m) / m = (∑_{a=1}^{M₀} μ(a) / a)² ∈ [0, 1]`. -/
theorem sum_truncMoebius_sq_div_eq_sq {M₀ k : ℕ} (hk : M₀ ^ 2 ≤ k) :
    ∑ m ∈ Finset.Icc 1 k, (truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ)
      = (∑ a ∈ Finset.Icc 1 M₀, (μ a : ℝ) / (a : ℝ)) ^ 2 := by
  rw [sum_div_mul_eq_sum_div_left]
  have h1 :
      ∑ m ∈ Finset.Icc 1 k,
          (truncMoebius M₀ m / (m : ℝ))
            * (∑ n ∈ Finset.Icc 1 (k / m), truncMoebius M₀ n / (n : ℝ))
        = ∑ m ∈ Finset.Icc 1 k,
            (truncMoebius M₀ m / (m : ℝ))
              * (∑ a ∈ Finset.Icc 1 M₀, (μ a : ℝ) / (a : ℝ)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    rcases le_or_gt m M₀ with hmM | hmM
    · have hdiv : M₀ ≤ k / m := by
        rw [Nat.le_div_iff_mul_le hm1]
        calc M₀ * m ≤ M₀ * M₀ := Nat.mul_le_mul_left M₀ hmM
          _ = M₀ ^ 2 := (sq M₀).symm
          _ ≤ k := hk
      rw [sum_truncMoebius_div_eq_of_le hdiv]
    · have h0 : truncMoebius M₀ m = 0 := by simp [truncMoebius_apply, not_le.mpr hmM]
      rw [h0, zero_div, zero_mul, zero_mul]
  have hM_le_k : M₀ ≤ k := by
    rcases Nat.eq_zero_or_pos M₀ with rfl | hM0
    · exact Nat.zero_le k
    · calc M₀ = M₀ * 1 := (mul_one M₀).symm
        _ ≤ M₀ * M₀ := Nat.mul_le_mul_left M₀ hM0
        _ = M₀ ^ 2 := (sq M₀).symm
        _ ≤ k := hk
  rw [h1, ← Finset.sum_mul, sum_truncMoebius_div_eq_of_le hM_le_k, sq]

/-- **Exact 3-Cut Quadratic-Step (`√k → k`) Expansion of `partialSumHalf μ k`**:
for every `1 ≤ k`, `partialSumHalf μ k` equals `2 * partialSumHalf μ M₀ - zetaHalfConst * partialSumHalf μ M₀ ^ 2`
minus the nonpositive pole square `2 * √k * (∑_{a=1}^{M₀} μ(a) / a)²` minus the `zetaRealRem` sum. -/
theorem partialSumHalf_moebius_eq_three_cut_asymptotic {k : ℕ} (hk : 1 ≤ k) :
    partialSumHalf (μ : ArithmeticFunction ℝ) k
      = 2 * partialSumHalf (μ : ArithmeticFunction ℝ) (Nat.sqrt k)
        - zetaHalfConst * partialSumHalf (μ : ArithmeticFunction ℝ) (Nat.sqrt k) ^ 2
        - 2 * Real.sqrt (k : ℝ)
            * (∑ a ∈ Finset.Icc 1 (Nat.sqrt k), (μ a : ℝ) / (a : ℝ)) ^ 2
        - ∑ m ∈ Finset.Icc 1 k,
            (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)) m
              * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * zetaRealRem ((k : ℝ) / (m : ℝ)) := by
  set M₀ := Nat.sqrt k
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hsq_le : M₀ ^ 2 ≤ k := by
    rw [sq]
    exact Nat.sqrt_le k
  rw [partialSumHalf_moebius_eq_two_mul_sqrt_sub,
    partialSumHalf_mul_eq_sum_div_left (truncMoebius M₀ * truncMoebius M₀) (ζ : ArithmeticFunction ℝ) k]
  have hsum :
      ∑ m ∈ Finset.Icc 1 k,
          (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * partialSumHalf (ζ : ArithmeticFunction ℝ) (k / m)
        = zetaHalfConst * partialSumHalf (truncMoebius M₀ * truncMoebius M₀) k
          + 2 * Real.sqrt (k : ℝ)
              * (∑ m ∈ Finset.Icc 1 k,
                  (truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ))
          + ∑ m ∈ Finset.Icc 1 k,
              (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
                * zetaRealRem ((k : ℝ) / (m : ℝ)) := by
    unfold partialSumHalf
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hsq :
        (m : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt ((k : ℝ) / (m : ℝ))
          = Real.sqrt (k : ℝ) / (m : ℝ) := by
      rw [rpow_neg_half_eq_inv_sqrt hm0.le, Real.sqrt_div hk0.le]
      have hsm : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt hm0.le
      calc (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (k : ℝ) / Real.sqrt (m : ℝ))
          = Real.sqrt (k : ℝ) / (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by ring
        _ = Real.sqrt (k : ℝ) / (m : ℝ) := by rw [hsm]
    have hterm :
        (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * (2 * Real.sqrt ((k : ℝ) / (m : ℝ)))
          = 2 * Real.sqrt (k : ℝ) * ((truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ)) := by
      calc (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * (2 * Real.sqrt ((k : ℝ) / (m : ℝ)))
          = 2 * (truncMoebius M₀ * truncMoebius M₀) m
              * ((m : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt ((k : ℝ) / (m : ℝ))) := by ring
        _ = 2 * (truncMoebius M₀ * truncMoebius M₀) m * (Real.sqrt (k : ℝ) / (m : ℝ)) := by rw [hsq]
        _ = 2 * Real.sqrt (k : ℝ) * ((truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ)) := by ring
    unfold zetaRealRem partialSumHalf
    rw [nat_floor_div_eq_div (k : ℝ) m, Nat.floor_natCast]
    linear_combination hterm
  rw [hsum, partialSumHalf_truncMoebius_sq_eq_sq hsq_le, sum_truncMoebius_sq_div_eq_sq hsq_le]
  ring

/-- **Exact 3-Cut Decomposition of `rieszMean (truncMoebius M₀) x`**: for `M₀ ≤ ⌊x⌋₊`,
`rieszMean (truncMoebius M₀) x = rieszMean μ M₀ + (log x - log M₀) * partialSumHalf μ M₀`. -/
theorem rieszMean_truncMoebius_eq_of_le {M₀ : ℕ} {x : ℝ} (hM : M₀ ≤ ⌊x⌋₊) :
    rieszMean (truncMoebius M₀) x
      = rieszMean (μ : ArithmeticFunction ℝ) (M₀ : ℝ)
        + (Real.log x - Real.log (M₀ : ℝ)) * partialSumHalf (μ : ArithmeticFunction ℝ) M₀ := by
  unfold rieszMean partialSumHalf
  rw [Nat.floor_natCast, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hsub : Finset.Icc 1 M₀ ⊆ Finset.Icc 1 ⌊x⌋₊ := Finset.Icc_subset_Icc_right hM
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hnM : n ≤ M₀ := (Finset.mem_Icc.mp hn).2
    simp only [truncMoebius_apply, hnM, ↓reduceIte, ArithmeticFunction.intCoe_apply]
    ring
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hnM : ¬ n ≤ M₀ := by omega
    simp [truncMoebius_apply, hnM]

/-- **Exact Quadratic-Step (`√k → k`) Newton–Schulz Formula for `rieszMean μ k`**:
for every `k : ℕ`, `rieszMean μ k = 2 * rieszMean (truncMoebius (Nat.sqrt k)) k - rieszMean (truncMoebius (Nat.sqrt k)² * ζ) k`. -/
theorem rieszMean_moebius_eq_two_mul_truncMoebius_sub (k : ℕ) :
    rieszMean (μ : ArithmeticFunction ℝ) (k : ℝ)
      = 2 * rieszMean (truncMoebius (Nat.sqrt k)) (k : ℝ)
        - rieszMean
            (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)
              * (ζ : ArithmeticFunction ℝ)) (k : ℝ) := by
  have hlt : k < (Nat.sqrt k + 1) ^ 2 := Nat.lt_succ_sqrt' k
  have heq :
      rieszMean (μ : ArithmeticFunction ℝ) (k : ℝ)
        = rieszMean
            ((2 : ℝ) • truncMoebius (Nat.sqrt k)
              - truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)
                * (ζ : ArithmeticFunction ℝ)) (k : ℝ) := by
    unfold rieszMean
    rw [Nat.floor_natCast]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnk : n ≤ k := (Finset.mem_Icc.mp hn).2
    rw [moebius_apply_eq_newton_schulz_of_lt_sq (lt_of_le_of_lt hnk hlt), two_smul, two_smul]
  rw [heq, rieszMean_sub, rieszMean_smul]

/-- **Exact 3-Cut Asymptotic Expansion of `rieszMean μ k`**: for every `1 ≤ k` with `M₀ = Nat.sqrt k`,
`rieszMean μ k` decomposes into `2 * rieszMean (truncMoebius M₀) k`, the sub-`√k` Riesz and square terms,
the `-4 * √k * (∑_{a=1}^{M₀} μ(a) / a)²` pole square, and the `rieszZetaRem` convolution sum. -/
theorem rieszMean_moebius_eq_three_cut_asymptotic {k : ℕ} (hk : 1 ≤ k) :
    rieszMean (μ : ArithmeticFunction ℝ) (k : ℝ)
      = 2 * rieszMean (truncMoebius (Nat.sqrt k)) (k : ℝ)
        - zetaHalfConst
            * rieszMean (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)) (k : ℝ)
        - rieszZetaConst * partialSumHalf (μ : ArithmeticFunction ℝ) (Nat.sqrt k) ^ 2
        - 4 * Real.sqrt (k : ℝ)
            * (∑ a ∈ Finset.Icc 1 (Nat.sqrt k), (μ a : ℝ) / (a : ℝ)) ^ 2
        - ∑ m ∈ Finset.Icc 1 k,
            (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)) m
              * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * rieszZetaRem ((k : ℝ) / (m : ℝ)) := by
  set M₀ := Nat.sqrt k
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hsq_le : M₀ ^ 2 ≤ k := by
    rw [sq]
    exact Nat.sqrt_le k
  rw [rieszMean_moebius_eq_two_mul_truncMoebius_sub k,
    rieszMean_mul_eq_sum_div_left
      (truncMoebius M₀ * truncMoebius M₀) (ζ : ArithmeticFunction ℝ) (k : ℝ),
    Nat.floor_natCast]
  have hsum :
      ∑ m ∈ Finset.Icc 1 k,
          (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * rieszMean (ζ : ArithmeticFunction ℝ) ((k : ℝ) / (m : ℝ))
        = zetaHalfConst * rieszMean (truncMoebius M₀ * truncMoebius M₀) (k : ℝ)
          + rieszZetaConst * partialSumHalf (truncMoebius M₀ * truncMoebius M₀) k
          + 4 * Real.sqrt (k : ℝ)
              * (∑ m ∈ Finset.Icc 1 k,
                  (truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ))
          + ∑ m ∈ Finset.Icc 1 k,
              (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
                * rieszZetaRem ((k : ℝ) / (m : ℝ)) := by
    unfold rieszMean partialSumHalf
    rw [Nat.floor_natCast, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hsq :
        (m : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt ((k : ℝ) / (m : ℝ))
          = Real.sqrt (k : ℝ) / (m : ℝ) := by
      rw [rpow_neg_half_eq_inv_sqrt hm0.le, Real.sqrt_div hk0.le]
      have hsm : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt hm0.le
      calc (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (k : ℝ) / Real.sqrt (m : ℝ))
          = Real.sqrt (k : ℝ) / (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by ring
        _ = Real.sqrt (k : ℝ) / (m : ℝ) := by rw [hsm]
    have hlog : Real.log ((k : ℝ) / (m : ℝ)) = Real.log (k : ℝ) - Real.log (m : ℝ) :=
      Real.log_div hk0.ne' hm0.ne'
    have hterm :
        (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * (4 * Real.sqrt ((k : ℝ) / (m : ℝ)))
          = 4 * Real.sqrt (k : ℝ) * ((truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ)) := by
      calc (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * (4 * Real.sqrt ((k : ℝ) / (m : ℝ)))
          = 4 * (truncMoebius M₀ * truncMoebius M₀) m
              * ((m : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt ((k : ℝ) / (m : ℝ))) := by ring
        _ = 4 * (truncMoebius M₀ * truncMoebius M₀) m * (Real.sqrt (k : ℝ) / (m : ℝ)) := by rw [hsq]
        _ = 4 * Real.sqrt (k : ℝ) * ((truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ)) := by ring
    unfold rieszZetaRem rieszMean
    rw [hlog]
    linear_combination hterm
  rw [hsum, partialSumHalf_truncMoebius_sq_eq_sq hsq_le, sum_truncMoebius_sq_div_eq_sq hsq_le]
  ring

/-- **Exact Pole-Cancelled 3-Cut Identity for `rieszMean μ k - 2 * partialSumHalf μ k`**:
subtracting `2 * partialSumHalf_moebius_eq_three_cut_asymptotic` from
`rieszMean_moebius_eq_three_cut_asymptotic` cancels the `-4 * √k` pole square identically! -/
theorem rieszMean_moebius_sub_two_mul_partialSumHalf_eq_three_cut {k : ℕ} (hk : 1 ≤ k) :
    rieszMean (μ : ArithmeticFunction ℝ) (k : ℝ)
        - 2 * partialSumHalf (μ : ArithmeticFunction ℝ) k
      = 2 * rieszMean (truncMoebius (Nat.sqrt k)) (k : ℝ)
        - 4 * partialSumHalf (μ : ArithmeticFunction ℝ) (Nat.sqrt k)
        - zetaHalfConst
            * rieszMean (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)) (k : ℝ)
        + (2 * zetaHalfConst - rieszZetaConst)
            * partialSumHalf (μ : ArithmeticFunction ℝ) (Nat.sqrt k) ^ 2
        - ∑ m ∈ Finset.Icc 1 k,
            (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)) m
              * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * (rieszZetaRem ((k : ℝ) / (m : ℝ))
                - 2 * zetaRealRem ((k : ℝ) / (m : ℝ))) := by
  have h1 := rieszMean_moebius_eq_three_cut_asymptotic hk
  have h2 := partialSumHalf_moebius_eq_three_cut_asymptotic hk
  have hsum :
      ∑ m ∈ Finset.Icc 1 k,
          (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)) m
            * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * (rieszZetaRem ((k : ℝ) / (m : ℝ))
              - 2 * zetaRealRem ((k : ℝ) / (m : ℝ)))
        = (∑ m ∈ Finset.Icc 1 k,
            (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)) m
              * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * rieszZetaRem ((k : ℝ) / (m : ℝ)))
          - 2 * ∑ m ∈ Finset.Icc 1 k,
              (truncMoebius (Nat.sqrt k) * truncMoebius (Nat.sqrt k)) m
                * (m : ℝ) ^ (-(1 / 2 : ℝ))
                * zetaRealRem ((k : ℝ) / (m : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => by ring
  linarith

/-! ### 6. Continuous Real-Variable (`x → ∞`) Asymptotic Behavior and 3-Cut (`√x → x`) Formulas -/

/-- **Unconditional Lower Bound on `M x - Psihalf x` on Every Finite Real Interval `(1, X₀]`**:
for any `1 < x ≤ X₀`, `(archSymbol 0 / 2) * log X₀ - Psihalf X₀ ≤ M x - Psihalf x`. -/
theorem M_sub_Psihalf_ge_on_Ioc {x X₀ : ℝ} (hx : 1 < x) (hxX₀ : x ≤ X₀) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * Real.log X₀ - Psihalf X₀ ≤ M x - Psihalf x := by
  have hx0 : 0 < x := by linarith
  have hsq : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx.le
  have htriv : trivTail x ≤ S0 - 4 := trivTail_le_S0_sub_four hx.le
  have hlog : Real.log x ≤ Real.log X₀ := Real.log_le_log hx0 hxX₀
  have harch0 := archSymbol_zero_nonpos
  have harch : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * Real.log X₀ ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * Real.log x := by
    nlinarith
  have hpsi : Psihalf x ≤ Psihalf X₀ := Psihalf_mono hx0 hxX₀
  unfold M
  linarith

/-- **Asymptotic Real-Variable (`x ≥ X₀`) Linear Criterion for `RiemannHypothesis`**:
if there exist `X₀ ≥ 1` and `A, B : ℝ` (`0 ≤ A`) such that `-A * log x - B ≤ M x - Psihalf x`
for all `x ≥ X₀` with `1 < x`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_eventually_M_sub_Psihalf_ge_neg_linear {X₀ A B : ℝ}
    (hA : 0 ≤ A)
    (h : ∀ x : ℝ, X₀ ≤ x → 1 < x → -A * Real.log x - B ≤ M x - Psihalf x) :
    RiemannHypothesis := by
  set B₁ : ℝ := max B (Psihalf X₀ - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * Real.log X₀)
  refine riemannHypothesis_of_M_sub_Psihalf_ge_neg_linear (A := A) (B := B₁) fun x hx => ?_
  rcases le_or_gt X₀ x with hxX₀ | hxX₀
  · have h1 := h x hxX₀ hx
    have hB : B ≤ B₁ := le_max_left _ _
    linarith
  · have h1 := M_sub_Psihalf_ge_on_Ioc hx hxX₀.le
    have hB : Psihalf X₀ - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * Real.log X₀ ≤ B₁ := le_max_right _ _
    have hL : 0 ≤ A * Real.log x := mul_nonneg hA (Real.log_nonneg hx.le)
    linarith

/-- **Asymptotic Real-Variable (`x ≥ X₀`) Sub-Power Criterion for `RiemannHypothesis`**:
if for every `0 < ε < 1 / 2` there exist `X₀ ≥ 1` and `C, A, B : ℝ` (`0 ≤ C`, `0 ≤ A`) such that
`-C * x ^ ε - A * log x - B ≤ M x - Psihalf x` for all `x ≥ X₀` (`1 < x`), then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_eventually_M_sub_Psihalf_ge_neg_rpow
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ X₀ C A B : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ x : ℝ, X₀ ≤ x → 1 < x →
        -C * x ^ ε - A * Real.log x - B ≤ M x - Psihalf x) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_M_sub_Psihalf_ge_neg_rpow fun ε hε0 hε_half => ?_
  obtain ⟨X₀, C, A, B, hC, hA, hX₀⟩ := h ε hε0 hε_half
  set B₁ : ℝ := max B (Psihalf X₀ - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * Real.log X₀)
  refine ⟨C, A, B₁, fun x hx => ?_⟩
  rcases le_or_gt X₀ x with hxX₀ | hxX₀
  · have h1 := hX₀ x hxX₀ hx
    have hB : B ≤ B₁ := le_max_left _ _
    linarith
  · have h1 := M_sub_Psihalf_ge_on_Ioc hx hxX₀.le
    have hB : Psihalf X₀ - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * Real.log X₀ ≤ B₁ := le_max_right _ _
    have hL : 0 ≤ A * Real.log x := mul_nonneg hA (Real.log_nonneg hx.le)
    have hC0 : 0 ≤ C * x ^ ε := mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
    linarith

/-- **Asymptotic Real-Variable (`x ≥ X₀`) Chebyshev Upper Criterion for `RiemannHypothesis`**:
if for every `ε > 0` there exist `X₀ : ℝ` and `C ≥ 0` such that `Psihalf x ≤ M x + C * x ^ ε`
for all `x ≥ X₀` with `1 < x`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_eventually_Psihalf_le_M_add_rpow
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ X₀ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X₀ ≤ x → 1 < x → Psihalf x ≤ M x + C * x ^ ε) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_eventually_M_sub_Psihalf_ge_neg_rpow fun ε hε0 _ => ?_
  obtain ⟨X₀, C, hC, hX₀⟩ := h ε hε0
  refine ⟨X₀, C, 0, 0, hC, le_rfl, fun x hxX₀ hx => ?_⟩
  have h1 := hX₀ x hxX₀ hx
  linarith

/-- For every real `x ≥ 0`, `⌊√x⌋₊ ^ 2 ≤ ⌊x⌋₊`. -/
theorem floor_sqrt_sq_le_floor {x : ℝ} (hx : 0 ≤ x) :
    ⌊Real.sqrt x⌋₊ ^ 2 ≤ ⌊x⌋₊ := by
  rw [Nat.le_floor_iff hx]
  have hle : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  calc ((⌊Real.sqrt x⌋₊ ^ 2 : ℕ) : ℝ)
      = (⌊Real.sqrt x⌋₊ : ℝ) ^ 2 := by push_cast; rfl
    _ ≤ (Real.sqrt x) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hle 2
    _ = x := Real.sq_sqrt hx

/-- For every real `x ≥ 0`, `⌊x⌋₊ < (⌊√x⌋₊ + 1) ^ 2`. -/
theorem floor_lt_floor_sqrt_succ_sq {x : ℝ} (hx : 0 ≤ x) :
    ⌊x⌋₊ < (⌊Real.sqrt x⌋₊ + 1) ^ 2 := by
  have hlt : Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (Real.sqrt x)
  have hsq : x < ((⌊Real.sqrt x⌋₊ : ℝ) + 1) ^ 2 := by
    calc x = (Real.sqrt x) ^ 2 := (Real.sq_sqrt hx).symm
      _ < ((⌊Real.sqrt x⌋₊ : ℝ) + 1) ^ 2 :=
        pow_lt_pow_left₀ hlt (Real.sqrt_nonneg x) (by norm_num)
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hlt' : (⌊x⌋₊ : ℝ) < (((⌊Real.sqrt x⌋₊ + 1) ^ 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hlt'

/-- Exact equality `Nat.sqrt ⌊x⌋₊ = ⌊√x⌋₊` for all real `x ≥ 0`. -/
theorem nat_sqrt_floor_eq_floor_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Nat.sqrt ⌊x⌋₊ = ⌊Real.sqrt x⌋₊ := by
  apply le_antisymm
  · by_contra hnot
    rw [not_le] at hnot
    have h1 : (⌊Real.sqrt x⌋₊ + 1) ^ 2 ≤ (Nat.sqrt ⌊x⌋₊) ^ 2 := Nat.pow_le_pow_left hnot 2
    have h2 : (Nat.sqrt ⌊x⌋₊) ^ 2 ≤ ⌊x⌋₊ := by rw [sq]; exact Nat.sqrt_le ⌊x⌋₊
    have h3 := floor_lt_floor_sqrt_succ_sq hx
    omega
  · rw [Nat.le_sqrt, ← sq]
    exact floor_sqrt_sq_le_floor hx

/-- For every real `x ≥ 1`, `⌊√x⌋₊ ≤ ⌊x⌋₊`. -/
theorem floor_sqrt_le_floor {x : ℝ} (hx : 1 ≤ x) :
    ⌊Real.sqrt x⌋₊ ≤ ⌊x⌋₊ := by
  rw [← nat_sqrt_floor_eq_floor_sqrt (by linarith)]
  exact Nat.sqrt_le_self ⌊x⌋₊

/-- **Unconditional `O(x^{1/4})` Bound on `partialSumHalf μ ⌊√x⌋₊` for All Real `x ≥ 0`**:
`|partialSumHalf μ ⌊√x⌋₊| ≤ 2 * x ^ (1 / 4)`. -/
theorem abs_partialSumHalf_moebius_floor_sqrt_le_two_mul_rpow_one_fourth {x : ℝ} (hx : 0 ≤ x) :
    |partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊|
      ≤ 2 * x ^ (1 / 4 : ℝ) := by
  have hle : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  calc |partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊|
      ≤ 2 * Real.sqrt (⌊Real.sqrt x⌋₊ : ℝ) := abs_partialSumHalf_moebius_le_two_sqrt _
    _ ≤ 2 * Real.sqrt (Real.sqrt x) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (by norm_num)
    _ = 2 * x ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
      norm_num

/-- **Exact Real-Variable Half-Log Split of `rieszMean (truncMoebius ⌊√x⌋₊) x`**:
for every real `x ≥ 1`, `rieszMean (truncMoebius ⌊√x⌋₊) x = rieszMean μ √x + (1 / 2) * log x * partialSumHalf μ ⌊√x⌋₊`
with zero floor discrepancy because `log √x = (1 / 2) * log x` is exact! -/
theorem rieszMean_truncMoebius_floor_sqrt_eq {x : ℝ} (hx : 1 ≤ x) :
    rieszMean (truncMoebius ⌊Real.sqrt x⌋₊) x
      = rieszMean (μ : ArithmeticFunction ℝ) (Real.sqrt x)
        + (1 / 2) * Real.log x * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊ := by
  have hx0 : 0 ≤ x := by linarith
  have hlog : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0
  unfold rieszMean partialSumHalf
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have hsub : Finset.Icc 1 ⌊Real.sqrt x⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ :=
    Finset.Icc_subset_Icc_right (floor_sqrt_le_floor hx)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hnM : n ≤ ⌊Real.sqrt x⌋₊ := (Finset.mem_Icc.mp hn).2
    simp only [truncMoebius_apply, hnM, ↓reduceIte, ArithmeticFunction.intCoe_apply, hlog]
    ring
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hnM : ¬ n ≤ ⌊Real.sqrt x⌋₊ := by omega
    simp [truncMoebius_apply, hnM]

/-- Helper expansion of `rieszMean (truncMoebius M₀) y` when `M₀ ≤ ⌊y⌋₊`:
for any `L : ℝ`, `rieszMean (truncMoebius M₀) y = (∑_{n=1}^{M₀} μ(n) n^{-1/2} (L - log n)) + (log y - L) * partialSumHalf μ M₀`. -/
theorem rieszMean_truncMoebius_eq_sum_sub_add {M₀ : ℕ} {y : ℝ} (hM : M₀ ≤ ⌊y⌋₊) (L : ℝ) :
    rieszMean (truncMoebius M₀) y
      = (∑ n ∈ Finset.Icc 1 M₀,
          (μ n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (L - Real.log (n : ℝ)))
        + (Real.log y - L) * partialSumHalf (μ : ArithmeticFunction ℝ) M₀ := by
  unfold rieszMean partialSumHalf
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have hsub : Finset.Icc 1 M₀ ⊆ Finset.Icc 1 ⌊y⌋₊ := Finset.Icc_subset_Icc_right hM
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hnM : n ≤ M₀ := (Finset.mem_Icc.mp hn).2
    simp only [truncMoebius_apply, hnM, ↓reduceIte, ArithmeticFunction.intCoe_apply]
    ring
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hnM : ¬ n ≤ M₀ := by omega
    simp [truncMoebius_apply, hnM]

/-- **Exact Real-Variable Product Factorization of `rieszMean (truncMoebius ⌊√x⌋₊ ^ 2) x`**:
for every real `x ≥ 1`, because `log (x / m) - log √x = log √x - log m`, the Riesz mean of
`truncMoebius ⌊√x⌋₊ ^ 2` at `x` factors identically as `2 * partialSumHalf μ ⌊√x⌋₊ * rieszMean μ √x`! -/
theorem rieszMean_truncMoebius_floor_sqrt_sq_eq {x : ℝ} (hx : 1 ≤ x) :
    rieszMean (truncMoebius ⌊Real.sqrt x⌋₊ * truncMoebius ⌊Real.sqrt x⌋₊) x
      = 2 * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊
          * rieszMean (μ : ArithmeticFunction ℝ) (Real.sqrt x) := by
  have hx0 : 0 < x := by linarith
  set M₀ := ⌊Real.sqrt x⌋₊
  have hsq_le : M₀ ^ 2 ≤ ⌊x⌋₊ := floor_sqrt_sq_le_floor hx0.le
  have hM_le : M₀ ≤ ⌊x⌋₊ := floor_sqrt_le_floor hx
  have hlog_sqrt : Real.log x - Real.log (Real.sqrt x) = Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]
    ring
  rw [rieszMean_mul_eq_sum_div_left]
  have hsub : Finset.Icc 1 M₀ ⊆ Finset.Icc 1 ⌊x⌋₊ := Finset.Icc_subset_Icc_right hM_le
  rw [← Finset.sum_subset hsub]
  · have hcongr :
        ∑ m ∈ Finset.Icc 1 M₀,
            truncMoebius M₀ m * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * rieszMean (truncMoebius M₀) (x / (m : ℝ))
          = ∑ m ∈ Finset.Icc 1 M₀,
              ((μ m : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ))
                  * rieszMean (μ : ArithmeticFunction ℝ) (Real.sqrt x)
                + (μ m : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ))
                    * (Real.log (Real.sqrt x) - Real.log (m : ℝ))
                    * partialSumHalf (μ : ArithmeticFunction ℝ) M₀) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmM : m ≤ M₀ := (Finset.mem_Icc.mp hm).2
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hdiv : M₀ ≤ ⌊x / (m : ℝ)⌋₊ := by
        rw [nat_floor_div_eq_div x m, Nat.le_div_iff_mul_le hm1]
        calc M₀ * m ≤ M₀ * M₀ := Nat.mul_le_mul_left M₀ hmM
          _ = M₀ ^ 2 := (sq M₀).symm
          _ ≤ ⌊x⌋₊ := hsq_le
      have hrm := rieszMean_truncMoebius_eq_sum_sub_add hdiv (Real.log (Real.sqrt x))
      have hrm_eq :
          (∑ n ∈ Finset.Icc 1 M₀,
              (μ n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (Real.sqrt x) - Real.log (n : ℝ)))
            = rieszMean (μ : ArithmeticFunction ℝ) (Real.sqrt x) := by
        unfold rieszMean
        rfl
      have hlog_div :
          Real.log (x / (m : ℝ)) - Real.log (Real.sqrt x)
            = Real.log (Real.sqrt x) - Real.log (m : ℝ) := by
        rw [Real.log_div hx0.ne' hm0.ne']
        linarith [hlog_sqrt]
      rw [hrm, hrm_eq, hlog_div]
      simp only [truncMoebius_apply, hmM, ↓reduceIte]
      ring
    rw [hcongr, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    change partialSumHalf (μ : ArithmeticFunction ℝ) M₀
        * rieszMean (μ : ArithmeticFunction ℝ) (Real.sqrt x)
      + rieszMean (μ : ArithmeticFunction ℝ) (Real.sqrt x)
          * partialSumHalf (μ : ArithmeticFunction ℝ) M₀ = _
    ring
  · intro m hm hnot
    simp only [Finset.mem_Icc] at hm hnot
    have hmM : ¬ m ≤ M₀ := by omega
    simp [truncMoebius_apply, hmM]

/-- **Exact Real-Variable Quadratic-Step (`√x → x`) Newton–Schulz Formula for `rieszMean μ x`**:
for every real `x ≥ 0`, `rieszMean μ x = 2 * rieszMean (truncMoebius ⌊√x⌋₊) x - rieszMean (truncMoebius ⌊√x⌋₊ ^ 2 * ζ) x`. -/
theorem rieszMean_moebius_real_eq_two_mul_truncMoebius_sub {x : ℝ} (hx : 0 ≤ x) :
    rieszMean (μ : ArithmeticFunction ℝ) x
      = 2 * rieszMean (truncMoebius ⌊Real.sqrt x⌋₊) x
        - rieszMean
            (truncMoebius ⌊Real.sqrt x⌋₊ * truncMoebius ⌊Real.sqrt x⌋₊
              * (ζ : ArithmeticFunction ℝ)) x := by
  have hlt : ⌊x⌋₊ < (⌊Real.sqrt x⌋₊ + 1) ^ 2 := floor_lt_floor_sqrt_succ_sq hx
  have heq :
      rieszMean (μ : ArithmeticFunction ℝ) x
        = rieszMean
            ((2 : ℝ) • truncMoebius ⌊Real.sqrt x⌋₊
              - truncMoebius ⌊Real.sqrt x⌋₊ * truncMoebius ⌊Real.sqrt x⌋₊
                * (ζ : ArithmeticFunction ℝ)) x := by
    unfold rieszMean
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnk : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hn).2
    rw [moebius_apply_eq_newton_schulz_of_lt_sq (lt_of_le_of_lt hnk hlt), two_smul, two_smul]
  rw [heq, rieszMean_sub, rieszMean_smul]

/-- **Exact Real-Variable (`x ≥ 1`) 3-Cut Asymptotic Expansion of `rieszMean μ x`**:
for every real `x ≥ 1`, `rieszMean μ x` is given in terms of `rieszMean μ √x`, `partialSumHalf μ ⌊√x⌋₊`,
the pole square `-4 * √x * (∑_{a ≤ ⌊√x⌋₊} μ(a) / a)²`, and the `rieszZetaRem (x / m)` sum! -/
theorem rieszMean_moebius_real_eq_three_cut_asymptotic {x : ℝ} (hx : 1 ≤ x) :
    rieszMean (μ : ArithmeticFunction ℝ) x
      = 2 * (1 - zetaHalfConst * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊)
            * rieszMean (μ : ArithmeticFunction ℝ) (Real.sqrt x)
        + Real.log x * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊
        - rieszZetaConst * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊ ^ 2
        - 4 * Real.sqrt x
            * (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (μ a : ℝ) / (a : ℝ)) ^ 2
        - ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
            (truncMoebius ⌊Real.sqrt x⌋₊ * truncMoebius ⌊Real.sqrt x⌋₊) m
              * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * rieszZetaRem (x / (m : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set M₀ := ⌊Real.sqrt x⌋₊
  have hsq_le : M₀ ^ 2 ≤ ⌊x⌋₊ := floor_sqrt_sq_le_floor hx0.le
  rw [rieszMean_moebius_real_eq_two_mul_truncMoebius_sub hx0.le,
    rieszMean_truncMoebius_floor_sqrt_eq hx,
    rieszMean_mul_eq_sum_div_left
      (truncMoebius M₀ * truncMoebius M₀) (ζ : ArithmeticFunction ℝ) x]
  have hsum :
      ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * rieszMean (ζ : ArithmeticFunction ℝ) (x / (m : ℝ))
        = zetaHalfConst * rieszMean (truncMoebius M₀ * truncMoebius M₀) x
          + rieszZetaConst * partialSumHalf (truncMoebius M₀ * truncMoebius M₀) ⌊x⌋₊
          + 4 * Real.sqrt x
              * (∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
                  (truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ))
          + ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
              (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
                * rieszZetaRem (x / (m : ℝ)) := by
    unfold rieszMean partialSumHalf
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hsq :
        (m : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (x / (m : ℝ))
          = Real.sqrt x / (m : ℝ) := by
      rw [rpow_neg_half_eq_inv_sqrt hm0.le, Real.sqrt_div hx0.le]
      have hsm : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt hm0.le
      calc (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt x / Real.sqrt (m : ℝ))
          = Real.sqrt x / (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by ring
        _ = Real.sqrt x / (m : ℝ) := by rw [hsm]
    have hlog : Real.log (x / (m : ℝ)) = Real.log x - Real.log (m : ℝ) :=
      Real.log_div hx0.ne' hm0.ne'
    have hterm :
        (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * (4 * Real.sqrt (x / (m : ℝ)))
          = 4 * Real.sqrt x * ((truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ)) := by
      calc (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * (4 * Real.sqrt (x / (m : ℝ)))
          = 4 * (truncMoebius M₀ * truncMoebius M₀) m
              * ((m : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (x / (m : ℝ))) := by ring
        _ = 4 * (truncMoebius M₀ * truncMoebius M₀) m * (Real.sqrt x / (m : ℝ)) := by rw [hsq]
        _ = 4 * Real.sqrt x * ((truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ)) := by ring
    unfold rieszZetaRem rieszMean
    rw [hlog]
    linear_combination hterm
  rw [hsum, rieszMean_truncMoebius_floor_sqrt_sq_eq hx,
    partialSumHalf_truncMoebius_sq_eq_sq hsq_le, sum_truncMoebius_sq_div_eq_sq hsq_le]
  ring

/-- **Exact Real-Variable (`x ≥ 1`) 3-Cut Asymptotic Expansion of `partialSumHalf μ ⌊x⌋₊`**:
for every real `x ≥ 1`, `partialSumHalf μ ⌊x⌋₊` expands with unfloored `2 * √x` and `x / m`! -/
theorem partialSumHalf_moebius_floor_eq_three_cut_asymptotic {x : ℝ} (hx : 1 ≤ x) :
    partialSumHalf (μ : ArithmeticFunction ℝ) ⌊x⌋₊
      = 2 * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊
        - zetaHalfConst * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊ ^ 2
        - 2 * Real.sqrt x
            * (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (μ a : ℝ) / (a : ℝ)) ^ 2
        - ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
            (truncMoebius ⌊Real.sqrt x⌋₊ * truncMoebius ⌊Real.sqrt x⌋₊) m
              * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * zetaRealRem (x / (m : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set M₀ := ⌊Real.sqrt x⌋₊
  have hsq_le : M₀ ^ 2 ≤ ⌊x⌋₊ := floor_sqrt_sq_le_floor hx0.le
  have hns := @partialSumHalf_moebius_eq_two_mul_sqrt_sub ⌊x⌋₊
  rw [nat_sqrt_floor_eq_floor_sqrt hx0.le] at hns
  rw [hns, partialSumHalf_mul_eq_sum_div_left
    (truncMoebius M₀ * truncMoebius M₀) (ζ : ArithmeticFunction ℝ) ⌊x⌋₊]
  have hsum :
      ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * partialSumHalf (ζ : ArithmeticFunction ℝ) (⌊x⌋₊ / m)
        = zetaHalfConst * partialSumHalf (truncMoebius M₀ * truncMoebius M₀) ⌊x⌋₊
          + 2 * Real.sqrt x
              * (∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
                  (truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ))
          + ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
              (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
                * zetaRealRem (x / (m : ℝ)) := by
    unfold partialSumHalf
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hsq :
        (m : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (x / (m : ℝ))
          = Real.sqrt x / (m : ℝ) := by
      rw [rpow_neg_half_eq_inv_sqrt hm0.le, Real.sqrt_div hx0.le]
      have hsm : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt hm0.le
      calc (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt x / Real.sqrt (m : ℝ))
          = Real.sqrt x / (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by ring
        _ = Real.sqrt x / (m : ℝ) := by rw [hsm]
    have hterm :
        (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * (2 * Real.sqrt (x / (m : ℝ)))
          = 2 * Real.sqrt x * ((truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ)) := by
      calc (truncMoebius M₀ * truncMoebius M₀) m * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * (2 * Real.sqrt (x / (m : ℝ)))
          = 2 * (truncMoebius M₀ * truncMoebius M₀) m
              * ((m : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (x / (m : ℝ))) := by ring
        _ = 2 * (truncMoebius M₀ * truncMoebius M₀) m * (Real.sqrt x / (m : ℝ)) := by rw [hsq]
        _ = 2 * Real.sqrt x * ((truncMoebius M₀ * truncMoebius M₀) m / (m : ℝ)) := by ring
    unfold zetaRealRem partialSumHalf
    rw [nat_floor_div_eq_div x m]
    linear_combination hterm
  rw [hsum, partialSumHalf_truncMoebius_sq_eq_sq hsq_le, sum_truncMoebius_sq_div_eq_sq hsq_le]
  ring

/-- **Exact Real-Variable (`x ≥ 1`) Pole-Cancelled 3-Cut Identity**:
for every real `x ≥ 1`, `rieszMean μ x - 2 * partialSumHalf μ ⌊x⌋₊` is completely free of the
`4 * √x * (∑_{a ≤ ⌊√x⌋₊} μ(a) / a)²` pole square and depends only on `√x` and `x / m`! -/
theorem rieszMean_moebius_real_sub_two_mul_partialSumHalf_eq_three_cut {x : ℝ} (hx : 1 ≤ x) :
    rieszMean (μ : ArithmeticFunction ℝ) x
        - 2 * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊x⌋₊
      = 2 * (1 - zetaHalfConst * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊)
            * rieszMean (μ : ArithmeticFunction ℝ) (Real.sqrt x)
        + (Real.log x - 4) * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊
        + (2 * zetaHalfConst - rieszZetaConst)
            * partialSumHalf (μ : ArithmeticFunction ℝ) ⌊Real.sqrt x⌋₊ ^ 2
        - ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
            (truncMoebius ⌊Real.sqrt x⌋₊ * truncMoebius ⌊Real.sqrt x⌋₊) m
              * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * (rieszZetaRem (x / (m : ℝ)) - 2 * zetaRealRem (x / (m : ℝ))) := by
  have h1 := rieszMean_moebius_real_eq_three_cut_asymptotic hx
  have h2 := partialSumHalf_moebius_floor_eq_three_cut_asymptotic hx
  have hsum :
      ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          (truncMoebius ⌊Real.sqrt x⌋₊ * truncMoebius ⌊Real.sqrt x⌋₊) m
            * (m : ℝ) ^ (-(1 / 2 : ℝ))
            * (rieszZetaRem (x / (m : ℝ)) - 2 * zetaRealRem (x / (m : ℝ)))
        = (∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
            (truncMoebius ⌊Real.sqrt x⌋₊ * truncMoebius ⌊Real.sqrt x⌋₊) m
              * (m : ℝ) ^ (-(1 / 2 : ℝ))
              * rieszZetaRem (x / (m : ℝ)))
          - 2 * ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
              (truncMoebius ⌊Real.sqrt x⌋₊ * truncMoebius ⌊Real.sqrt x⌋₊) m
                * (m : ℝ) ^ (-(1 / 2 : ℝ))
                * zetaRealRem (x / (m : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => by ring
  linarith

/-! ### 7. Connes Rung–Bulk Spectral Spine, Double-Pole Cancellation, and 3-Cut Window Transfer -/

/-- **Exact Operator-Budget Identity `atomBudget = opChebOffDiag c Λ`**: when `1 < c`, `c ≤ P + 1`,
and `Nat.clog 2 c ≤ R + 1`, `atomBudget c P R` equals `opChebOffDiag c ArithmeticFunction.vonMangoldt`. -/
theorem atomBudget_eq_opChebOffDiag_vonMangoldt {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    atomBudget c P R = opChebOffDiag c ArithmeticFunction.vonMangoldt := by
  unfold atomBudget opChebOffDiag
  rw [Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1 ^ x.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, r⟩ hmem hne
    simp only [Finset.mem_sigma, primeRange, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Icc] at hmem
    have hp : p.Prime := hmem.1.2
    have hr : 1 ≤ r := hmem.2.1
    rw [Finset.mem_Ico]
    refine ⟨le_trans hp.two_le (Nat.le_self_pow (Nat.one_le_iff_ne_zero.mp hr) p), ?_⟩
    by_contra hge
    rw [Cvs.PrimeOperator.cap_eq_one hc (not_lt.mp hge),
      Cvs.PrimeOperator.chebFactor_one, zero_mul] at hne
    exact hne rfl
  · rintro ⟨p₁, r₁⟩ h₁ _ ⟨p₂, r₂⟩ h₂ _ heq
    simp only [Finset.mem_sigma, primeRange, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Icc] at h₁ h₂
    dsimp only at heq
    have hp₁ : p₁.Prime := h₁.1.2
    have hp₂ : p₂.Prime := h₂.1.2
    have hr₁ : 1 ≤ r₁ := h₁.2.1
    have hdvd : p₁ ∣ p₂ ^ r₂ := by
      rw [← heq]
      exact dvd_pow_self p₁ (by omega)
    have hp_eq : p₁ = p₂ :=
      (Nat.dvd_prime hp₂).mp (hp₁.dvd_of_dvd_pow hdvd) |>.resolve_left hp₁.ne_one
    subst hp_eq
    have hr_eq : r₁ = r₂ := Nat.pow_right_injective hp₁.two_le heq
    subst hr_eq
    rfl
  · intro n hn hne
    have hnc : n < c := (Finset.mem_Ico.mp hn).2
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0 := by
      intro h0
      rw [h0, abs_zero, zero_mul, zero_mul] at hne
      exact hne rfl
    have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨p, r, hp, hr, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hp_le : p ≤ p ^ r := Nat.le_self_pow hr.ne' p
    have hpP : p < P + 1 := lt_of_le_of_lt hp_le (lt_of_lt_of_le hnc hP)
    have hrR : r ≤ R := by
      by_contra hgt
      have hR1 : R + 1 ≤ r := by omega
      have hcle : c ≤ p ^ r :=
        le_trans (Cvs.WeilForm.NilpotentResolventEulerSquares.le_prime_pow_of_clog_le hp hR)
          (Nat.pow_le_pow_right hp.pos hR1)
      omega
    refine ⟨⟨p, r⟩, ?_, ?_, rfl⟩
    · simp only [Finset.mem_sigma, primeRange, Finset.mem_filter, Finset.mem_range,
        Finset.mem_Icc]
      exact ⟨⟨hpP, hp⟩, hr, hrR⟩
    · intro hz
      apply hne
      dsimp only at hz
      simp only [wt_eq_vonMangoldt_mul_rpow] at hz
      rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      linarith
  · rintro ⟨p, r⟩ _ _
    dsimp only
    rw [wt_eq_vonMangoldt_mul_rpow, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    ring

/-- **Exact 3-Cut Decomposition of `atomBudget`**: for `1 < c`, `c ≤ P + 1`, and
`Nat.clog 2 c ≤ R + 1`, `atomBudget c P R = opChainOffDiag c Λ + opDimerOffDiag c Λ`. -/
theorem atomBudget_eq_three_cut_vonMangoldt {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    atomBudget c P R
      = opChainOffDiag c ArithmeticFunction.vonMangoldt
        + opDimerOffDiag c ArithmeticFunction.vonMangoldt := by
  rw [atomBudget_eq_opChebOffDiag_vonMangoldt hc hP hR,
    opChebOffDiag_eq_chain_add_dimer hc]

/-- Sub-`√c` bound `opChainOffDiag c Λ ≤ 2 * partialSumHalf Λ (Nat.sqrt c)`. -/
theorem opChainOffDiag_vonMangoldt_le_two_mul_partialSumHalf_sqrt (c : ℕ) :
    opChainOffDiag c ArithmeticFunction.vonMangoldt
      ≤ 2 * partialSumHalf ArithmeticFunction.vonMangoldt (Nat.sqrt c) := by
  unfold opChainOffDiag partialSumHalf
  rw [Finset.mul_sum]
  have hsub : ((Finset.Ico 2 c).filter (fun n => n ^ 2 < c)) ⊆ Finset.Icc 1 (Nat.sqrt c) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    rw [Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    have h1 : n = Nat.sqrt (n ^ 2) := by rw [sq, Nat.sqrt_eq]
    rw [h1]
    exact Nat.sqrt_le_sqrt hn.2.le
  calc
    ∑ n ∈ (Finset.Ico 2 c).filter (fun n => n ^ 2 < c),
        |ArithmeticFunction.vonMangoldt n| * (n : ℝ) ^ (-(1 / 2 : ℝ))
          * Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n))
      ≤ ∑ n ∈ (Finset.Ico 2 c).filter (fun n => n ^ 2 < c),
          2 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        have hch := (Cvs.PrimeOperator.chebFactor_lt_two (cap (Real.log c) (Real.log n))).le
        nlinarith
    _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.sqrt c),
          2 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
        have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        linarith

/-- Canonical Möbius radical coordinate `Op x μ (windowCircle hx φ)` on `L²(𝕋)` attached to any
window form-domain class `φ : Dom x` (`1 < x`), with no smoothness or bump hypotheses. -/
def windowMoebius {x : ℕ} (hx : 1 < x) (φ : Cvs.Route.L1FloorFromBulkD0.Dom x) : L2 :=
  Op x (μ : ArithmeticFunction ℝ)
    (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))

/-- Exact window reconstruction `Op x ζ (windowMoebius hx φ) = windowCircle hx φ`. -/
theorem Op_zeta_windowMoebius {x : ℕ} (hx : 1 < x) (φ : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Op x (ζ : ArithmeticFunction ℝ) (windowMoebius hx φ)
      = Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) :=
  Op_zeta_Op_moebius_apply hx _

/-- Norm isometry `‖Op x ζ (windowMoebius hx φ)‖² = ‖φ‖²` on `Dom x`. -/
theorem norm_Op_zeta_windowMoebius_sq {x : ℕ} (hx : 1 < x) (φ : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    ‖Op x (ζ : ArithmeticFunction ℝ) (windowMoebius hx φ)‖ ^ 2 = ‖φ‖ ^ 2 := by
  rw [Op_zeta_windowMoebius, Cvs.WeilForm.WindowCircleIsometry.norm_sq_windowCircle]
  rfl

/-- **3-Cut Newton–Schulz Formula for `windowMoebius`** (`1 < x`): expresses `windowMoebius hx φ`
purely in terms of `truncMoebius (Nat.sqrt (x - 1))` and smooth `Op x ζ`. -/
theorem windowMoebius_eq_three_cut {x : ℕ} (hx : 1 < x) (φ : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    windowMoebius hx φ
      = (2 : ℝ) • Op x (truncMoebius (Nat.sqrt (x - 1)))
          (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - Op x (truncMoebius (Nat.sqrt (x - 1)) * truncMoebius (Nat.sqrt (x - 1)))
            (Op x (ζ : ArithmeticFunction ℝ)
              (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx
                (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))) := by
  have halg : truncMoebius (Nat.sqrt (x - 1))
        * ((2 : ℝ) • (1 : ArithmeticFunction ℝ)
          - (ζ : ArithmeticFunction ℝ) * truncMoebius (Nat.sqrt (x - 1)))
      = (2 : ℝ) • truncMoebius (Nat.sqrt (x - 1))
        - (truncMoebius (Nat.sqrt (x - 1)) * truncMoebius (Nat.sqrt (x - 1)))
          * (ζ : ArithmeticFunction ℝ) := by
    rw [mul_sub, mul_smul_comm, mul_one,
      mul_comm (ζ : ArithmeticFunction ℝ) (truncMoebius (Nat.sqrt (x - 1))), ← mul_assoc]
  unfold windowMoebius
  rw [Op_moebius_eq_Op_truncMoebius_newton_schulz hx, halg, Op_sub, Op_smul, ← Op_mul hx,
    _root_.sub_apply, _root_.smul_apply, mul_apply_eq_comp]

/-- **General Window 3-Cut Decomposition of `primeTerm`** on `Dom x` (`1 < x`): splits `primeTerm`
into the sub-`√x` chain form `OpChain x Λ` and the square-zero dimer form `OpDimer x Λ`. -/
theorem primeTerm_rep_eq_three_cut {x P R : ℕ}
    (hx : 1 < x) (hP : x ≤ P + 1) (hR : Nat.clog 2 x ≤ R + 1)
    (φ : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R
        (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
      = 2 * ⟪OpChain x ArithmeticFunction.vonMangoldt
            (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))),
          Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))⟫_ℝ
        + 2 * ⟪OpDimer x ArithmeticFunction.vonMangoldt
            (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))),
          Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))⟫_ℝ := by
  rw [Cvs.WeilForm.WindowCircleIsometry.primeTerm_rep_eq_inner_primeOperator hx P R,
    inner_primeOperator_eq_two_inner_Op_vonMangoldt hx hP hR,
    Op_eq_three_cut hx ArithmeticFunction.vonMangoldt,
    ArithmeticFunction.vonMangoldt_apply_one, zero_smul, zero_add,
    _root_.add_apply, inner_add_left, mul_add]

/-- **Prime-Free Radical Representation of `primeTerm` on All of `Dom x`** (`1 < x`): eliminates
all prime weights `Λ(n)` in favor of the smooth pair `(Op x log, Op x ζ)` at `windowMoebius hx φ`. -/
theorem primeTerm_rep_eq_moebius_zeta {x P R : ℕ}
    (hx : 1 < x) (hP : x ≤ P + 1) (hR : Nat.clog 2 x ≤ R + 1)
    (φ : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R
        (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
      = 2 * ⟪Op x ArithmeticFunction.log (windowMoebius hx φ),
          Op x (ζ : ArithmeticFunction ℝ) (windowMoebius hx φ)⟫_ℝ := by
  rw [Cvs.WeilForm.WindowCircleIsometry.primeTerm_rep_eq_inner_primeOperator hx P R,
    ← Op_zeta_windowMoebius hx φ, inner_primeOperator_Op_zeta hx hP hR]

/-- **Prime-Free Radical Decomposition of `Qx` on All of `Dom x`** (`1 < x`): holds for every
Hilbert-space window class `φ : Dom x` without continuity or tameness hypotheses. -/
theorem Qx_eq_pole_add_arch_sub_moebius_zeta {x : ℕ} (hx : 1 < x)
    (φ : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.Route.WindowPositivityBulkCoupling.Qx x φ
      = Cvs.WeilForm.PoleArchPrimeProblem.poleTerm
          (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        + Cvs.WeilForm.PoleArchPrimeProblem.archTerm
            (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - 2 * ⟪Op x ArithmeticFunction.log (windowMoebius hx φ),
            Op x (ζ : ArithmeticFunction ℝ) (windowMoebius hx φ)⟫_ℝ := by
  change Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ = _
  rw [Cvs.WeilForm.WindowCircleIsometry.Q_eq_split_general x x (Nat.clog 2 x) φ,
    primeTerm_rep_eq_moebius_zeta hx (Nat.le_succ x) (Nat.le_succ _) φ]

/-- **General Form-Domain Dirichlet-Schur Identity for `Qx`** (`1 < x`, `a * b = Λ`, `0 < γ`):
removes all continuity and tameness hypotheses from `Cvs.WeilForm.DirichletSchurFactorisation.Q_wv_eq_dirichlet_schur`. -/
theorem Qx_eq_dirichlet_schur_general {x : ℕ} (hx : 1 < x)
    {a b : ArithmeticFunction ℝ} (hab : a * b = ArithmeticFunction.vonMangoldt)
    {γ : ℝ} (hγ : 0 < γ) (φ : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.Route.WindowPositivityBulkCoupling.Qx x φ
      = Cvs.WeilForm.PoleArchPrimeProblem.poleTerm
          (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        + Cvs.WeilForm.PoleArchPrimeProblem.archTerm
            (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - γ * ‖Op x b
            (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx
              (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ ^ 2
        - γ⁻¹ * ‖ContinuousLinearMap.adjoint (Op x a)
            (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx
              (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ ^ 2
        + ‖Real.sqrt γ • Op x b
              (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx
                (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
            - (Real.sqrt γ)⁻¹ • ContinuousLinearMap.adjoint (Op x a)
                (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx
                  (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ ^ 2 := by
  change Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ = _
  rw [Cvs.WeilForm.WindowCircleIsometry.Q_eq_split_general x x (Nat.clog 2 x) φ,
    Cvs.WeilForm.WindowCircleIsometry.primeTerm_rep_eq_inner_primeOperator hx x (Nat.clog 2 x),
    inner_primeOperator_eq_dirichlet_schur hx (Nat.le_succ x) (Nat.le_succ _) hab hγ]
  ring

/-- **Double-Pole Divisor Residual `ζ * ζ - β • ζ - log`**: at `β = 2 γ_Euler`, its Dirichlet
series `ζ(s)² - 2 γ ζ(s) + ζ'(s)` cancels both the double and simple poles at `s = 1`. -/
def divisorResidual (β : ℝ) : ArithmeticFunction ℝ :=
  (ζ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)
    - β • (ζ : ArithmeticFunction ℝ) - ArithmeticFunction.log

/-- Exact Dirichlet convolution identity `(ζ² - β • ζ - log) * μ = ζ - β • 1 - Λ`. -/
theorem divisorResidual_mul_moebius (β : ℝ) :
    divisorResidual β * (μ : ArithmeticFunction ℝ)
      = (ζ : ArithmeticFunction ℝ) - β • (1 : ArithmeticFunction ℝ)
        - ArithmeticFunction.vonMangoldt := by
  unfold divisorResidual
  rw [sub_mul, sub_mul, mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one,
    smul_mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius,
    ArithmeticFunction.log_mul_moebius_eq_vonMangoldt]

/-- Whole-domain operator factorization `Op c ζ - β • 1 - Op c Λ = Op c (divisorResidual β) * Op c μ`. -/
theorem Op_zeta_sub_vonMangoldt_eq_divisorResidual_mul_moebius {c : ℕ} (hc : 1 < c) (β : ℝ) :
    Op c (ζ : ArithmeticFunction ℝ) - β • (1 : L2 →L[ℝ] L2) - Op c ArithmeticFunction.vonMangoldt
      = Op c (divisorResidual β) * Op c (μ : ArithmeticFunction ℝ) := by
  have hsub : ∀ x y : ArithmeticFunction ℝ, Op c (x - y) = Op c x - Op c y := fun x y => by
    rw [sub_eq_add_neg, Op_add, show -y = (-1 : ℝ) • y by simp, Op_smul, neg_one_smul,
      ← sub_eq_add_neg]
  rw [Op_mul hc, divisorResidual_mul_moebius, hsub, hsub, Op_smul, Op_one hc]

/-- **Whole-Domain Double-Pole Cancelled Pairing**: for `1 < c`, `c ≤ P + 1`, `Nat.clog 2 c ≤ R + 1`,
`β : ℝ`, and `f : L²(𝕋)`, `2 ⟪Op c ζ f, f⟫ - 2 β ‖f‖² - ⟪primeOperator c P R f, f⟫` equals
`2 ⟪Op c μ f, (Op c (divisorResidual β))* f⟫`. -/
theorem two_inner_Op_zeta_sub_primeOperator_eq_divisorResidual {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) (β : ℝ) (f : L2) :
    2 * ⟪Op c (ζ : ArithmeticFunction ℝ) f, f⟫_ℝ - 2 * β * ‖f‖ ^ 2
        - ⟪primeOperator c P R f, f⟫_ℝ
      = 2 * ⟪Op c (μ : ArithmeticFunction ℝ) f,
          ContinuousLinearMap.adjoint (Op c (divisorResidual β)) f⟫_ℝ := by
  rw [inner_primeOperator_eq_two_inner_Op_vonMangoldt hc hP hR, ← real_inner_self_eq_norm_sq,
    ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp,
    ← Op_zeta_sub_vonMangoldt_eq_divisorResidual_mul_moebius hc β,
    _root_.sub_apply, _root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
    inner_sub_left, inner_sub_left, real_inner_smul_left]
  ring

/-- **Vacuum Double-Pole Cancelled Identity**: `rieszMean ζ c - β * log c - Psihalf c` equals
`log c * ⟪moebiusVac c, (Op c (divisorResidual β))* vac⟫`. -/
theorem rieszMean_zeta_sub_Psihalf_eq_divisorResidual {c : ℕ} (hc : 1 < c) (β : ℝ) :
    rieszMean (ζ : ArithmeticFunction ℝ) (c : ℝ) - β * Real.log c - Psihalf c
      = Real.log c *
        ⟪moebiusVac c, ContinuousLinearMap.adjoint (Op c (divisorResidual β)) vac⟫_ℝ := by
  have hpair := two_inner_Op_zeta_sub_primeOperator_eq_divisorResidual
    hc (Nat.le_succ c) (Nat.le_succ _) β vac
  have hzeta := rieszMean_nat_eq_log_mul_inner_Op_vac hc (ζ : ArithmeticFunction ℝ)
  have hpsi := two_mul_Psihalf_eq_log_mul_inner_primeOperator_vac
    hc (Nat.le_succ c) (Nat.le_succ _)
  rw [norm_vac_sq, mul_one] at hpair
  have hmul := congr_arg (Real.log c * ·) hpair
  unfold moebiusVac
  linarith

/-- **Cauchy–Schwarz Bound via `divisorResidual`**: for `1 < c` and `β : ℝ`,
`|rieszMean ζ c - β * log c - Psihalf c| ≤ log c * ‖moebiusVac c‖ * ‖Op c (divisorResidual β) vac‖`. -/
theorem abs_rieszMean_zeta_sub_Psihalf_le_divisorResidual {c : ℕ} (hc : 1 < c) (β : ℝ) :
    |rieszMean (ζ : ArithmeticFunction ℝ) (c : ℝ) - β * Real.log c - Psihalf c|
      ≤ Real.log c * ‖moebiusVac c‖ * ‖Op c (divisorResidual β) vac‖ := by
  have hL : 0 < Real.log c := Real.log_pos (by exact_mod_cast hc)
  rw [rieszMean_zeta_sub_Psihalf_eq_divisorResidual hc β, abs_mul, abs_of_pos hL, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hL.le
  calc
    |⟪moebiusVac c, ContinuousLinearMap.adjoint (Op c (divisorResidual β)) vac⟫_ℝ|
      ≤ ‖moebiusVac c‖ * ‖ContinuousLinearMap.adjoint (Op c (divisorResidual β)) vac‖ :=
        abs_real_inner_le_norm _ _
    _ = ‖moebiusVac c‖ * ‖Op c (divisorResidual β) vac‖ := by
        rw [norm_adj_Op_vac_eq hc]

/-- **Exact `4 √x` Pole Cancellation Between `M x` and `rieszMean ζ x`**: their difference has
zero `√x` term and equals `(archSymbol 0 / 2 - zetaHalfConst) log x + O(1)`. -/
theorem M_sub_rieszMean_zeta_eq (x : ℝ) :
    M x - rieszMean (ζ : ArithmeticFunction ℝ) x
      = (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst) * Real.log x
        + (S0 - 8 - rieszZetaConst) - trivTail x - rieszZetaRem x := by
  unfold M rieszZetaRem
  ring

/-- Unconditional logarithmic lower bound on `M x - rieszMean ζ x` for every real `1 ≤ x`. -/
theorem M_sub_rieszMean_zeta_ge {x : ℝ} (hx : 1 ≤ x) :
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst) * Real.log x
        - rieszZetaConst - 14
      ≤ M x - rieszMean (ζ : ArithmeticFunction ℝ) x := by
  have htriv := trivTail_le_S0_sub_four hx
  have hrem := (abs_le.mp (abs_rieszZetaRem_le_ten_div_sqrt hx)).2
  have hsq1 : (1 : ℝ) ≤ Real.sqrt x := by
    simpa using Real.sqrt_le_sqrt hx
  have h10 : 10 / Real.sqrt x ≤ 10 := div_le_self (by norm_num) hsq1
  rw [M_sub_rieszMean_zeta_eq]
  linarith

/-- **Double-Pole Divisor Criterion for `RiemannHypothesis`**: if for some `β : ℝ`, `c₀ : ℕ`, and
`A, B : ℝ` (`0 ≤ A`), `log c * ‖moebiusVac c‖ * ‖Op c (divisorResidual β) vac‖ ≤ A * log c + B`
for `c ≥ c₀` (`1 < c`), then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_eventually_divisorResidual_vac {c₀ : ℕ} {β A B : ℝ} (hA : 0 ≤ A)
    (h : ∀ c : ℕ, c₀ ≤ c → 1 < c →
      Real.log c * ‖moebiusVac c‖ * ‖Op c (divisorResidual β) vac‖ ≤ A * Real.log c + B) :
    RiemannHypothesis := by
  set CL : ℝ := A + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst + β|
  have hCL : 0 ≤ CL := add_nonneg hA (abs_nonneg _)
  refine riemannHypothesis_of_eventually_M_sub_Psihalf_ge_neg_linear
    (X₀ := max (c₀ : ℝ) 2) (A := CL)
    (B := CL + max B 0 + |rieszZetaConst + 14| + (S0 - 2))
    hCL fun x hx₀ hx1 => ?_
  have hc₀ : c₀ ≤ ⌈x⌉₊ := by
    have h1 : (c₀ : ℝ) ≤ (⌈x⌉₊ : ℝ) := (le_max_left _ _).trans (hx₀.trans (Nat.le_ceil x))
    exact_mod_cast h1
  have hc1 : 1 < ⌈x⌉₊ := one_lt_ceil_of_one_lt hx1
  have hc_real : (1 : ℝ) ≤ ⌈x⌉₊ := by exact_mod_cast hc1.le
  have hdiv := (abs_le.mp (abs_rieszMean_zeta_sub_Psihalf_le_divisorResidual hc1 β)).1
  have hbound := h ⌈x⌉₊ hc₀ hc1
  have hM := M_sub_rieszMean_zeta_ge hc_real
  have hinterp := M_sub_Psihalf_ge_ceil_sub_interp hx1
  have hstep := M_ceil_sub_M_le hx1
  have hceil := log_ceil_le_log_add_one hx1
  have hlog0 : 0 ≤ Real.log (⌈x⌉₊ : ℝ) := Real.log_nonneg hc_real
  have hcoef :
      -|Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst + β| * Real.log (⌈x⌉₊ : ℝ)
        ≤ (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 - zetaHalfConst + β) * Real.log (⌈x⌉₊ : ℝ) :=
    mul_le_mul_of_nonneg_right (neg_abs_le _) hlog0
  have hconst : -|rieszZetaConst + 14| ≤ -rieszZetaConst - 14 := by
    have := le_abs_self (rieszZetaConst + 14)
    linarith
  have hCL_ceil : -CL * (Real.log x + 1) ≤ -CL * Real.log (⌈x⌉₊ : ℝ) := by
    nlinarith
  have hB0 : B ≤ max B 0 := le_max_left B 0
  dsimp only [CL] at hCL_ceil ⊢
  linarith

/-- `vonMangoldtSymbol x * rho w` is integrable on `Dom x`. -/
theorem integrable_vonMangoldtSymbol_mul_rho (x : ℕ) (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Integrable fun t =>
      Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
  have heq : (fun t =>
      Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
    = fun t => Cvs.WeilForm.BandFreeLogTwoBase.shellSymbol 2 x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    funext t
    rw [Cvs.WeilForm.BandFreeLogTwoBase.vonMangoldtSymbol_eq_shellSymbol]
  rw [heq]
  exact Cvs.WeilForm.MeanFreeSpectralIdentity.integrable_shellSymbol_mul_rho 2 x w

/-- **Spectral Representation of `primeTerm` on `Dom x`**:
`primeTerm x (Nat.clog 2 x) (rep w) = ∫ t, vonMangoldtSymbol x t * rho w t`. -/
theorem primeTerm_rep_eq_integral_vonMangoldtSymbol (x : ℕ) (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.WeilForm.PoleArchPrimeProblem.primeTerm x (Nat.clog 2 x)
        (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
      = ∫ t, Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
  have hQsplit : Cvs.Route.WindowPositivityBulkCoupling.Qx x w
      = Cvs.WeilForm.PoleArchPrimeProblem.poleTerm
          (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        + Cvs.WeilForm.PoleArchPrimeProblem.archTerm
            (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - Cvs.WeilForm.PoleArchPrimeProblem.primeTerm x (Nat.clog 2 x)
            (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) :=
    Cvs.WeilForm.WindowCircleIsometry.Q_eq_split_general x x (Nat.clog 2 x) w
  have hQint := Cvs.WeilForm.VonMangoldtMultiplier.Qx_eq_integral x w
  have hpole := Cvs.WeilForm.GreenTailCancellation.poleTerm_rep_eq_integral_poleSymbol w
  have harch := Cvs.WeilForm.WindowCircleIsometry.archTerm_rep_eq_integral_archSymbol
    (Real.log_natCast_nonneg x) w
  have hi_scale : Integrable fun t =>
      Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    simpa only [Cvs.WeilForm.AdmissibleMultiplierMinorants.formSpec_self] using
      Cvs.WeilForm.AdmissibleMultiplierMinorants.mem_admissible.1
        (Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol_mem_admissible x) w w
  have hi_pole := Cvs.WeilForm.GreenTailCancellation.integrable_poleSymbol_mul_rho w
  have hi_vm := integrable_vonMangoldtSymbol_mul_rho x w
  have hi_arch : Integrable fun t =>
      Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    refine ((hi_scale.add hi_vm).sub hi_pole).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol]
    ring
  have hsum_int :
      (∫ t, Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
        = (∫ t, Cvs.WeilForm.PolePrimeCosineMultipliers.poleSymbol (Real.log x) t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
          + (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
          - ∫ t, Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    have h1 := integral_add hi_pole hi_arch
    have h2 := integral_sub (hi_pole.add hi_arch) hi_vm
    dsimp only [Pi.add_apply, Pi.sub_apply] at h1 h2
    rw [← h1, ← h2]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only [Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol]
    ring
  change Cvs.Route.WindowPositivityBulkCoupling.Qx x w = ∫ t, Cvs.WeilForm.VonMangoldtMultiplier.scaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t at hQint
  change Cvs.WeilForm.PoleArchPrimeProblem.archTerm _ = ∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho w t at harch
  linarith

/-- Pointwise bound `|vonMangoldtSymbol x t| ≤ vonMangoldtSymbol x 0`. -/
theorem abs_vonMangoldtSymbol_le_zero (x : ℕ) (t : ℝ) :
    |Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t|
      ≤ Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x 0 := by
  unfold Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have hw : 0 ≤ 2 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2) : ℝ)) := by
    have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have : 0 ≤ (n : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  rw [abs_mul, abs_of_nonneg hw, zero_mul, Real.cos_zero, mul_one]
  exact mul_le_of_le_one_right hw (Real.abs_cos_le_one _)

/-- **Frequency-Split Upper Bound on `primeTerm`**: separates the low-band peak (weighted by
`∫_{|t| < T} rho w`) from the high-band oscillatory integral `∫_{T ≤ |t|} vonMangoldtSymbol · rho w`. -/
theorem primeTerm_rep_le_lowBand_add_highBand (x : ℕ) (T : ℝ)
    (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.WeilForm.PoleArchPrimeProblem.primeTerm x (Nat.clog 2 x)
        (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
      ≤ Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x 0
          * (∫ t in {t : ℝ | |t| < T}, Cvs.WeilForm.EvenBulkVisibility.rho w t)
        + ∫ t in {t : ℝ | T ≤ |t|},
            Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
  set S : Set ℝ := {t : ℝ | |t| < T}
  have hSm : MeasurableSet S := (isOpen_lt continuous_abs continuous_const).measurableSet
  have hSc : Sᶜ = {t : ℝ | T ≤ |t|} := by
    ext t; simp [S]
  have hi_vm := integrable_vonMangoldtSymbol_mul_rho x w
  have hi_rho := Cvs.WeilForm.EvenBulkVisibility.integrable_rho w
  rw [primeTerm_rep_eq_integral_vonMangoldtSymbol x w,
    ← integral_add_compl hSm hi_vm, hSc]
  have hlow :
      (∫ t in S, Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
        ≤ Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x 0
            * ∫ t in S, Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hi_vm.integrableOn
      (hi_rho.const_mul _).integrableOn hSm fun t _ => ?_
    have hρ : 0 ≤ Cvs.WeilForm.EvenBulkVisibility.rho w t := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t
    exact mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (abs_vonMangoldtSymbol_le_zero x t)) hρ
  linarith

/-- **Connes Reflection-Even High-Band Coercivity Inequality**: on `Ev x`, `poleTerm ≥ 0` and the
`4 √x` low-band prime peak is suppressed by `∫_{|t| < T} rho w`, leaving only `T ≤ |t|`. -/
theorem Qx_even_ge_truncSymbol_sub_highBand_prime (x N : ℕ) {T : ℝ} (hT : 0 ≤ T)
    {w : Cvs.Route.L1FloorFromBulkD0.Dom x} (hw : w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x) :
    Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N T * ‖w‖ ^ 2
        - ((∑ n ∈ Finset.range N, Cvs.Zeta.digammaDeficit T n)
            + Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x 0)
          * (∫ t in {t : ℝ | |t| < T}, Cvs.WeilForm.EvenBulkVisibility.rho w t)
        - (∫ t in {t : ℝ | T ≤ |t|},
            Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
      ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x w := by
  have hQ : Cvs.Route.WindowPositivityBulkCoupling.Qx x w
      = Cvs.WeilForm.PoleArchPrimeProblem.poleTerm
          (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        + Cvs.WeilForm.PoleArchPrimeProblem.archTerm
            (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - Cvs.WeilForm.PoleArchPrimeProblem.primeTerm x (Nat.clog 2 x)
            (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) :=
    Cvs.WeilForm.WindowCircleIsometry.Q_eq_split_general x x (Nat.clog 2 x) w
  have hpole := Cvs.WeilForm.WindowCircleIsometry.poleTerm_rep_nonneg_of_Uc_eq_zero
    (Real.log_natCast_nonneg x)
    (Cvs.WeilForm.CentredHodgeIndexWindow.Uc_eq_zero_of_mem_evenSub (Real.log_natCast_nonneg x) hw)
  have harch := Cvs.WeilForm.TruncSymbolMonotone.archTerm_rep_ge_truncSymbol (Real.log_natCast_nonneg x) hT N w
  have hprime := primeTerm_rep_le_lowBand_add_highBand x T w
  linarith

/-- **Connes `EvenBulkFloor` from Prolate Low-Band Suppression + High-Band Prime Oscillation**:
eliminates the low-frequency `4 √x` barrier on `Ev x ⊓ (R1 x)ᗮ`. -/
theorem evenBulkFloor_of_lowBand_and_highBand_prime (x N : ℕ) {T η γHigh : ℝ} (hT : 0 ≤ T)
    (hlow : ∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
      (∫ t in {t : ℝ | |t| < T}, Cvs.WeilForm.EvenBulkVisibility.rho w t) ≤ η * ‖w‖ ^ 2)
    (hhigh : ∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
      (∫ t in {t : ℝ | T ≤ |t|},
          Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
        ≤ γHigh * ‖w‖ ^ 2) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x
      (Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N T
        - ((∑ n ∈ Finset.range N, Cvs.Zeta.digammaDeficit T n)
            + Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x 0) * η
        - γHigh) := by
  intro w hwe hwR
  have hbase := Qx_even_ge_truncSymbol_sub_highBand_prime x N hT hwe
  have hdef_nn : 0 ≤ (∑ n ∈ Finset.range N, Cvs.Zeta.digammaDeficit T n)
      + Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x 0 := by
    have h1 : 0 ≤ ∑ n ∈ Finset.range N, Cvs.Zeta.digammaDeficit T n := by
      rw [← Cvs.WeilForm.TruncSymbolMonotone.truncSymbol_sub_archSymbol_zero]
      linarith [Cvs.WeilForm.TruncSymbolMonotone.archSymbol_zero_le_truncSymbol N T]
    have h2 : 0 ≤ Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x 0 :=
      (abs_nonneg _).trans (abs_vonMangoldtSymbol_le_zero x 0)
    linarith
  have hmul := mul_le_mul_of_nonneg_left (hlow w hwe hwR) hdef_nn
  have hh := hhigh w hwe hwR
  linarith

/-- For every `x : ℕ`, `log x ≤ 2 * log (Nat.sqrt x + 1)` so the dimer shell `[Nat.sqrt x + 1, x]`
satisfies the band-free sum-frequency condition on `Dom x`. -/
theorem log_le_two_mul_log_sqrt_succ (x : ℕ) :
    Real.log x ≤ 2 * Real.log ((Nat.sqrt x + 1 : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have hlt : (x : ℝ) ≤ (((Nat.sqrt x + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [sq]
      exact_mod_cast (Nat.lt_succ_sqrt x).le
    calc
      Real.log x ≤ Real.log ((((Nat.sqrt x + 1 : ℕ) : ℝ)) ^ 2) :=
        Real.log_le_log (by exact_mod_cast hx) hlt
      _ = 2 * Real.log ((Nat.sqrt x + 1 : ℕ) : ℝ) := by
        rw [Real.log_pow]
        ring

/-- **3-Cut Frequency Split of `vonMangoldtSymbol x`** (`4 ≤ x`): decomposes `vonMangoldtSymbol x`
into the sub-`√x` chain shell `shellSymbol 2 (Nat.sqrt x)` plus the dimer shell `[Nat.sqrt x + 1, x]`. -/
theorem vonMangoldtSymbol_eq_subSqrt_add_dimer_shell {x : ℕ} (hx : 4 ≤ x) (t : ℝ) :
    Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t
      = Cvs.WeilForm.BandFreeLogTwoBase.shellSymbol 2 (Nat.sqrt x) t
        + Cvs.WeilForm.BandFreeLogTwoBase.shellSymbol (Nat.sqrt x + 1) x t := by
  have h2 : 2 ≤ Nat.sqrt x := Nat.le_sqrt.mpr (by omega)
  rw [Cvs.WeilForm.BandFreeLogTwoBase.vonMangoldtSymbol_eq_shellSymbol]
  exact Cvs.WeilForm.BandFreeLogTwoBase.shellSymbol_split h2 (Nat.sqrt_le_self x) t

/-- **Exact Dimer-Cut Phase-Deficit Square Identity on `Dom x`**: all sum frequencies on
`[Nat.sqrt x + 1, x]` are band-free on `(0, log x]`, equating `∫ dimerShell² · ρ_w` to `2 |D(1/2+it)|²`. -/
theorem integral_dimerShell_sq_mul_rho_eq (x : ℕ) (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    ∫ t, Cvs.WeilForm.BandFreeLogTwoBase.shellSymbol (Nat.sqrt x + 1) x t ^ 2
        * Cvs.WeilForm.EvenBulkVisibility.rho w t
      = 2 * (∑ n ∈ Finset.Icc (Nat.sqrt x + 1) x, Cvs.WeilForm.BandFreeLogTwoBase.shellWeight n) ^ 2
          * ‖w‖ ^ 2
        - ∫ t, Cvs.WeilForm.InterPrimePhaseCancellation.pairwisePhaseDeficit
            (Finset.Icc (Nat.sqrt x + 1) x) Cvs.WeilForm.BandFreeLogTwoBase.shellWeight
            (fun n => Real.log n) t * Cvs.WeilForm.EvenBulkVisibility.rho w t :=
  Cvs.WeilForm.BandFreeLogTwoBase.integral_shellSymbol_sq_mul_rho_eq_budget_sub_deficit
    (log_le_two_mul_log_sqrt_succ x) w

/-- **Connes Rung–Bulk High-Band Criterion for `RiemannHypothesis`**: combines Connes' even form
coupling (`0 ≤ δ < 1`) with a strictly positive high-band prime-split bulk floor on `Ev x ⊓ (R1 x)ᗮ`. -/
theorem riemannHypothesis_of_connes_highBand_primeSplit
    (h : ∃ᶠ x : ℕ in atTop, ∃ (N : ℕ) (T η γHigh δ : ℝ),
      0 ≤ T ∧ 0 ≤ δ ∧ δ < 1 ∧
      0 < Cvs.WeilForm.Archimedean.TruncationBelowSymbol.truncSymbol N T
        - ((∑ n ∈ Finset.range N, Cvs.Zeta.digammaDeficit T n)
            + Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x 0) * η
        - γHigh ∧
      (∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
        (∫ t in {t : ℝ | |t| < T}, Cvs.WeilForm.EvenBulkVisibility.rho w t) ≤ η * ‖w‖ ^ 2) ∧
      (∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
        (∫ t in {t : ℝ | T ≤ |t|},
            Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
          ≤ γHigh * ‖w‖ ^ 2) ∧
      Cvs.Route.EvenWindowBulkCoupling.EvenFormCoupling x δ) :
    RiemannHypothesis := by
  refine Cvs.Route.EvenWindowBulkCoupling.riemannHypothesis_of_even_floor_pos_coupling
    (h.mono fun x ⟨N, T, η, γHigh, δ, hT, hδ0, hδ1, hb, hlow, hhigh, hC⟩ => ?_)
  exact ⟨_, δ, hb, hδ0, hδ1, evenBulkFloor_of_lowBand_and_highBand_prime x N hT hlow hhigh, hC⟩

/-! ### 8. High-Bulk Coercivity, 3-Cut Budget Halving, and Low-Bulk Schur Reduction -/

open scoped Matrix

/-- **Exact Dimer-Cut Evaluation of `opDimerOffDiag c Λ`** (`1 < c`): on `c ≤ n² < c²`, capacity
is `2` (`chebFactor 2 = 1`), giving `partialSumHalf Λ (c - 1) - partialSumHalf Λ √(c - 1)`. -/
theorem opDimerOffDiag_vonMangoldt_eq_sub {c : ℕ} (hc : 1 < c) :
    opDimerOffDiag c ArithmeticFunction.vonMangoldt
      = partialSumHalf ArithmeticFunction.vonMangoldt (c - 1)
        - partialSumHalf ArithmeticFunction.vonMangoldt (Nat.sqrt (c - 1)) := by
  unfold opDimerOffDiag partialSumHalf
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (c - 1))
    (fun n => n ≤ Nat.sqrt (c - 1))
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)))).symm
  have h1 : (Finset.Icc 1 (c - 1)).filter (fun n => n ≤ Nat.sqrt (c - 1))
      = Finset.Icc 1 (Nat.sqrt (c - 1)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hsq : Nat.sqrt (c - 1) ≤ c - 1 := Nat.sqrt_le_self (c - 1)
    omega
  have h2 : (Finset.Icc 1 (c - 1)).filter (fun n => ¬ n ≤ Nat.sqrt (c - 1))
      = (Finset.Ico 2 c).filter (fun n => c ≤ n ^ 2) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, Nat.le_sqrt, sq]
    constructor
    · rintro ⟨⟨hn1, hnc⟩, hnsq⟩
      have hn2 : 2 ≤ n := by
        by_contra hlt
        have hn_eq : n = 1 := by omega
        subst hn_eq
        omega
      exact ⟨⟨hn2, by omega⟩, by omega⟩
    · rintro ⟨⟨hn2, hnc⟩, hcsq⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [h1, h2] at hsplit
  have habs : (∑ n ∈ (Finset.Ico 2 c).filter (fun n => c ≤ n ^ 2),
        |(ArithmeticFunction.vonMangoldt n : ℝ)| * (n : ℝ) ^ (-(1 / 2 : ℝ)))
      = ∑ n ∈ (Finset.Ico 2 c).filter (fun n => c ≤ n ^ 2),
          (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [habs]
  linarith

/-- Sharp sub-`√(c - 1)` bound `opChainOffDiag c Λ ≤ 2 * partialSumHalf Λ (Nat.sqrt (c - 1))`. -/
theorem opChainOffDiag_vonMangoldt_le_two_mul_partialSumHalf_sqrt_pred {c : ℕ} (hc : 1 < c) :
    opChainOffDiag c ArithmeticFunction.vonMangoldt
      ≤ 2 * partialSumHalf ArithmeticFunction.vonMangoldt (Nat.sqrt (c - 1)) := by
  unfold opChainOffDiag partialSumHalf
  rw [Finset.mul_sum]
  have hsub : ((Finset.Ico 2 c).filter (fun n => n ^ 2 < c))
      ⊆ Finset.Icc 1 (Nat.sqrt (c - 1)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico, sq] at hn
    rw [Finset.mem_Icc, Nat.le_sqrt]
    exact ⟨by omega, by omega⟩
  calc
    ∑ n ∈ (Finset.Ico 2 c).filter (fun n => n ^ 2 < c),
        |ArithmeticFunction.vonMangoldt n| * (n : ℝ) ^ (-(1 / 2 : ℝ))
          * Cvs.Operator.chebFactor (cap (Real.log c) (Real.log n))
      ≤ ∑ n ∈ (Finset.Ico 2 c).filter (fun n => n ^ 2 < c),
          2 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        have hch := (Cvs.PrimeOperator.chebFactor_lt_two (cap (Real.log c) (Real.log n))).le
        nlinarith
    _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.sqrt (c - 1)),
          2 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
        have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        linarith

/-- **Exact 3-Cut Dimer-Halved Identity for `atomBudget`**: isolates the unit-factor dimer sum
`partialSumHalf Λ (c - 1) - partialSumHalf Λ √(c - 1)` plus the sub-`√c` chain sum. -/
theorem atomBudget_eq_dimer_exact_add_chain {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    atomBudget c P R
      = partialSumHalf ArithmeticFunction.vonMangoldt (c - 1)
        - partialSumHalf ArithmeticFunction.vonMangoldt (Nat.sqrt (c - 1))
        + opChainOffDiag c ArithmeticFunction.vonMangoldt := by
  rw [atomBudget_eq_three_cut_vonMangoldt hc hP hR, opDimerOffDiag_vonMangoldt_eq_sub hc]
  ring

/-- Closed 3-cut Chebyshev prime bound `partialSumHalf Λ (c - 1) + partialSumHalf Λ √(c - 1)`,
halving the leading `4 √c` translation budget on the dimer range to `2 √c + O(c^(1/4))`. -/
def chebPrimeBound (c : ℕ) : ℝ :=
  partialSumHalf ArithmeticFunction.vonMangoldt (c - 1)
    + partialSumHalf ArithmeticFunction.vonMangoldt (Nat.sqrt (c - 1))

/-- `chebPrimeBound c` is nonnegative for every `c : ℕ`. -/
theorem chebPrimeBound_nonneg (c : ℕ) : 0 ≤ chebPrimeBound c := by
  have hp : ∀ N : ℕ, 0 ≤ partialSumHalf ArithmeticFunction.vonMangoldt N := fun N =>
    Finset.sum_nonneg fun n _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact add_nonneg (hp _) (hp _)

/-- **3-Cut Halving Bound on `atomBudget`**: for `1 < c`, `c ≤ P + 1`, and `Nat.clog 2 c ≤ R + 1`,
`atomBudget c P R ≤ chebPrimeBound c`. -/
theorem atomBudget_le_chebPrimeBound {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    atomBudget c P R ≤ chebPrimeBound c := by
  unfold chebPrimeBound
  linarith [atomBudget_eq_dimer_exact_add_chain hc hP hR,
    opChainOffDiag_vonMangoldt_le_two_mul_partialSumHalf_sqrt_pred hc]

/-- `atomBudget c P R` is nonnegative for `1 < c` and all `P R : ℕ`. -/
theorem atomBudget_nonneg {c : ℕ} (hc : 1 < c) (P R : ℕ) :
    0 ≤ atomBudget c P R :=
  (norm_nonneg (primeOperator c P R)).trans (Cvs.PrimeOperator.norm_primeOperator_le_atomBudget hc P R)

/-- Explicit 3-cut high-bulk frequency threshold `2 π exp(|b| + |archSymbol 0| + chebPrimeBound x + 30)`
with square-root-reduced growth `exp(2 √x + O(x^(1/4)))`. -/
def highBulkThreshold (x : ℕ) (b : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (|b| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + chebPrimeBound x + 30)

/-- `2 ≤ highBulkThreshold x b` for all `x : ℕ` and `b : ℝ`. -/
theorem two_le_highBulkThreshold (x : ℕ) (b : ℝ) :
    2 ≤ highBulkThreshold x b := by
  have he : 1 ≤ Real.exp (|b| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + chebPrimeBound x + 30) := by
    rw [Real.one_le_exp_iff]
    linarith [abs_nonneg b, abs_nonneg (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0),
      chebPrimeBound_nonneg x]
  unfold highBulkThreshold
  nlinarith [Real.pi_gt_three]

/-- At `T = highBulkThreshold x b`, `archSymbol 0 + 1 ≤ floorAt T`. -/
theorem archSymbol_zero_add_one_le_floorAt_highBulkThreshold (x : ℕ) (b : ℝ) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + 1
      ≤ Cvs.L2a.ArchChannelFloorAbove.floorAt (highBulkThreshold x b) := by
  set E := |b| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + chebPrimeBound x + 30
  set T := highBulkThreshold x b
  have hT : 2 ≤ T := two_le_highBulkThreshold x b
  have hlog : Real.log (T / 2) = Real.log Real.pi + E := by
    have ht : T / 2 = Real.pi * Real.exp E := by
      dsimp [T, highBulkThreshold, E]
      ring
    rw [ht, Real.log_mul Real.pi_pos.ne' (Real.exp_pos E).ne', Real.log_exp]
  have h57 : 57 / T ≤ 57 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT
  unfold Cvs.L2a.ArchChannelFloorAbove.floorAt
  rw [hlog]
  dsimp only [E]
  linarith [le_abs_self (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0), abs_nonneg b,
    chebPrimeBound_nonneg x]

/-- At `T = highBulkThreshold x b`, `b + 1 + chebPrimeBound x ≤ floorAt T`. -/
theorem add_one_add_chebPrimeBound_le_floorAt_highBulkThreshold (x : ℕ) (b : ℝ) :
    b + 1 + chebPrimeBound x ≤ Cvs.L2a.ArchChannelFloorAbove.floorAt (highBulkThreshold x b) := by
  set E := |b| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + chebPrimeBound x + 30
  set T := highBulkThreshold x b
  have hT : 2 ≤ T := two_le_highBulkThreshold x b
  have hlog : Real.log (T / 2) = Real.log Real.pi + E := by
    have ht : T / 2 = Real.pi * Real.exp E := by
      dsimp [T, highBulkThreshold, E]
      ring
    rw [ht, Real.log_mul Real.pi_pos.ne' (Real.exp_pos E).ne', Real.log_exp]
  have h57 : 57 / T ≤ 57 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT
  unfold Cvs.L2a.ArchChannelFloorAbove.floorAt
  rw [hlog]
  dsimp only [E]
  linarith [le_abs_self b, abs_nonneg (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)]

/-- **Pure High-Bulk Coercivity on `Ev x`** (`1 < x`): any reflection-even window class `w ∈ Ev x`
supported in `{t : ℝ | highBulkThreshold x b ≤ |t|}` satisfies `(b + 1) * ‖w‖² ≤ Qx x w`. -/
theorem Qx_even_ge_of_highBulk_supp {x : ℕ} (hx : 1 < x) (b : ℝ)
    {w : Cvs.Route.L1FloorFromBulkD0.Dom x} (hw : w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x)
    (hsupp : (∫ t in {t : ℝ | |t| < highBulkThreshold x b}, Cvs.WeilForm.EvenBulkVisibility.rho w t) ≤ 0) :
    (b + 1) * ‖w‖ ^ 2 ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x w := by
  have h0 : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      ≤ Cvs.L2a.ArchChannelFloorAbove.floorAt (highBulkThreshold x b) := by
    linarith [archSymbol_zero_add_one_le_floorAt_highBulkThreshold x b]
  have hbase := Cvs.WeilForm.WindowCircleIsometry.Qx_even_ge_highBand_floor hx (η := 0) h0
    (fun _ ht => Cvs.L2a.ArchChannelFloorAbove.floorAt_le_archSymbol (two_le_highBulkThreshold x b) ht)
    hw (by simpa using hsupp)
  have hbud := atomBudget_le_chebPrimeBound hx (Nat.le_succ x) (Nat.le_succ _)
  have hfl := add_one_add_chebPrimeBound_le_floorAt_highBulkThreshold x b
  have hcoef : b + 1
      ≤ Cvs.L2a.ArchChannelFloorAbove.floorAt (highBulkThreshold x b)
        - (Cvs.L2a.ArchChannelFloorAbove.floorAt (highBulkThreshold x b)
            - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * 0
        - atomBudget x x (Nat.clog 2 x) := by
    linarith
  exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖w‖)).trans hbase

/-- Explicit low-bulk spectral leakage cap `1 / (floorAt (highBulkThreshold x b) - archSymbol 0)`. -/
def lowBulkLeakageCap (x : ℕ) (b : ℝ) : ℝ :=
  1 / (Cvs.L2a.ArchChannelFloorAbove.floorAt (highBulkThreshold x b) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)

/-- `lowBulkLeakageCap x b` is strictly positive for all `x : ℕ` and `b : ℝ`. -/
theorem lowBulkLeakageCap_pos (x : ℕ) (b : ℝ) :
    0 < lowBulkLeakageCap x b := by
  unfold lowBulkLeakageCap
  refine one_div_pos.mpr ?_
  linarith [archSymbol_zero_add_one_le_floorAt_highBulkThreshold x b]

/-- **Connes `EvenBulkFloor` from Low-Bulk Concentration Alone** (`1 < x`): discharges the entire
high-frequency bulk `highBulkThreshold x b ≤ |t|` unconditionally via 3-cut `atomBudget`. -/
theorem evenBulkFloor_of_lowBulk_only {x : ℕ} (hx : 1 < x) (b : ℝ)
    (hlow : ∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
      (∫ t in {t : ℝ | |t| < highBulkThreshold x b}, Cvs.WeilForm.EvenBulkVisibility.rho w t)
        ≤ lowBulkLeakageCap x b * ‖w‖ ^ 2) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b := by
  intro w hwe hwR
  set D := Cvs.L2a.ArchChannelFloorAbove.floorAt (highBulkThreshold x b)
    - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [archSymbol_zero_add_one_le_floorAt_highBulkThreshold x b]
  have hD0 : D ≠ 0 := by linarith
  have h0 : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      ≤ Cvs.L2a.ArchChannelFloorAbove.floorAt (highBulkThreshold x b) := by linarith
  have hbase := Cvs.WeilForm.WindowCircleIsometry.Qx_even_ge_highBand_floor hx h0
    (fun _ ht => Cvs.L2a.ArchChannelFloorAbove.floorAt_le_archSymbol (two_le_highBulkThreshold x b) ht)
    hwe (hlow w hwe hwR)
  have hmul : D * lowBulkLeakageCap x b = 1 := by
    unfold lowBulkLeakageCap
    change D * (1 / D) = 1
    field_simp [hD0]
  have hbud := atomBudget_le_chebPrimeBound hx (Nat.le_succ x) (Nat.le_succ _)
  have hfl := add_one_add_chebPrimeBound_le_floorAt_highBulkThreshold x b
  have hcoef : b ≤ Cvs.L2a.ArchChannelFloorAbove.floorAt (highBulkThreshold x b)
      - D * lowBulkLeakageCap x b - atomBudget x x (Nat.clog 2 x) := by
    rw [hmul]
    linarith
  exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖w‖)).trans hbase

/-- **Connes Low-Bulk-Only Criterion for `RiemannHypothesis`**: requires only low-band suppression
below `highBulkThreshold x b` on `Ev x ⊓ (R1 x)ᗮ` and `EvenFormCoupling x δ` (`0 ≤ δ < 1`). -/
theorem riemannHypothesis_of_connes_lowBulk_only
    (h : ∃ᶠ x : ℕ in atTop, ∃ b δ : ℝ,
      0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧
      (∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
        (∫ t in {t : ℝ | |t| < highBulkThreshold x b}, Cvs.WeilForm.EvenBulkVisibility.rho w t)
          ≤ lowBulkLeakageCap x b * ‖w‖ ^ 2) ∧
      Cvs.Route.EvenWindowBulkCoupling.EvenFormCoupling x δ) :
    RiemannHypothesis := by
  refine Cvs.Route.EvenWindowBulkCoupling.riemannHypothesis_of_even_floor_pos_coupling
    ((h.and_eventually (eventually_gt_atTop 1)).mono fun x ⟨⟨b, δ, hb, hδ0, hδ1, hlow, hC⟩, hx⟩ =>
      ⟨b, δ, hb, hδ0, hδ1, evenBulkFloor_of_lowBulk_only hx b hlow, hC⟩)

/-- Squared window norm of `modeClass hx0 N v` for even `v : Idx N → ℝ` equals `log x * (v ⬝ᵥ v)`. -/
theorem norm_modeClass_sq {x : ℕ} (hx : 1 < x) (N : ℕ)
    {v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hv : ∀ i, v (Cvs.Finite.SymmetricModeSet.negI N i) = v i) :
    ‖(Cvs.Approximant.CosineColumnTailPairing.modeClass (by exact_mod_cast (by omega : 0 < x) : (0 : ℝ) < x) N v :
        Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))‖ ^ 2
      = Real.log x * (v ⬝ᵥ v) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  set φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x) :=
    (Cvs.Approximant.CosineColumnTailPairing.modeClass hx0 N v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
  have hae : Cvs.WeilForm.WindowRepresentative.rep φ
      =ᵐ[volume] Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) v :=
    (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ).symm.trans (Cvs.Approximant.CosineColumnTailPairing.coe_modeClass_ae hx0 N v)
  rw [← (Cvs.WeilForm.WindowRepresentative.weilQW_rep 0 0 φ).2,
    Cvs.WeilForm.WeilFormAeClass.selfConvolution_congr_ae hae 0,
    Cvs.Finite.PairFormDividedDifference.selfConvolution_modeSum_zero hL
      (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.negI_involutive N)
      (Cvs.Finite.SymmetricModeSet.mode_negI N) hv]

/-- **Exact Bridge from `translationPrimeMatrix` to `primeTerm`** (`1 < x`): for even `v : Idx N → ℝ`,
`log x * (v ⬝ᵥ (translationPrimeMatrix *ᵥ v)) = primeTerm P R (rep (modeClass hx0 N v))`. -/
theorem log_mul_translationPrime_quad_eq_primeTerm {x : ℕ} (hx : 1 < x) (P R N : ℕ)
    {v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hv : ∀ i, v (Cvs.Finite.SymmetricModeSet.negI N i) = v i) :
    Real.log x
        * (v ⬝ᵥ (Cvs.WeilForm.PrimeDiagonalBulkSchur.translationPrimeMatrix P R (Real.log x) N *ᵥ v))
      = Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R
          (Cvs.WeilForm.WindowRepresentative.rep
            (Cvs.Approximant.CosineColumnTailPairing.modeClass
              (by exact_mod_cast (by omega : 0 < x) : (0 : ℝ) < x) N v :
              Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  set φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x) :=
    (Cvs.Approximant.CosineColumnTailPairing.modeClass hx0 N v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
  have hae : Cvs.WeilForm.WindowRepresentative.rep φ
      =ᵐ[volume] Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) v :=
    (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ).symm.trans (Cvs.Approximant.CosineColumnTailPairing.coe_modeClass_ae hx0 N v)
  unfold Cvs.WeilForm.PoleArchPrimeProblem.primeTerm
  rw [Cvs.WeilForm.WeilFormAeClass.selfConvolution_eq_of_ae hae,
    Cvs.Finite.ModeSumPairValues.prime_modeSum hL P R (Cvs.Finite.SymmetricModeSet.mode N)
      (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) hv]
  simp only [dotProduct, Matrix.mulVec, Cvs.WeilForm.PrimeDiagonalBulkSchur.translationPrimeMatrix,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Path-Law Bound on `translationPrimeMatrix`** (`1 < x`): for even `v : Idx N → ℝ`,
`|v ⬝ᵥ (translationPrimeMatrix *ᵥ v)| ≤ atomBudget x P R * (v ⬝ᵥ v)`, uniformly in `N`. -/
theorem abs_translationPrime_quad_le_atomBudget {x : ℕ} (hx : 1 < x) (P R N : ℕ)
    {v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hv : ∀ i, v (Cvs.Finite.SymmetricModeSet.negI N i) = v i) :
    |v ⬝ᵥ (Cvs.WeilForm.PrimeDiagonalBulkSchur.translationPrimeMatrix P R (Real.log x) N *ᵥ v)|
      ≤ atomBudget x P R * (v ⬝ᵥ v) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  set φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x) :=
    (Cvs.Approximant.CosineColumnTailPairing.modeClass hx0 N v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
  have h := Cvs.WeilForm.WindowCircleIsometry.abs_primeTerm_rep_le_atomBudget hx P R φ
  rw [← log_mul_translationPrime_quad_eq_primeTerm hx P R N hv,
    norm_modeClass_sq hx N hv, abs_mul, abs_of_pos hL] at h
  exact le_of_mul_le_mul_left (by linarith) hL

/-- **3-Cut Halved Bound on `translationPrimeMatrix`** (`1 < x`, `x ≤ P + 1`, `Nat.clog 2 x ≤ R + 1`):
`|v ⬝ᵥ (translationPrimeMatrix *ᵥ v)| ≤ chebPrimeBound x * (v ⬝ᵥ v)` across all `N : ℕ`. -/
theorem abs_translationPrime_quad_le_chebPrimeBound {x P R : ℕ}
    (hx : 1 < x) (hP : x ≤ P + 1) (hR : Nat.clog 2 x ≤ R + 1) (N : ℕ)
    {v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hv : ∀ i, v (Cvs.Finite.SymmetricModeSet.negI N i) = v i) :
    |v ⬝ᵥ (Cvs.WeilForm.PrimeDiagonalBulkSchur.translationPrimeMatrix P R (Real.log x) N *ᵥ v)|
      ≤ chebPrimeBound x * (v ⬝ᵥ v) :=
  (abs_translationPrime_quad_le_atomBudget hx P R N hv).trans
    (mul_le_mul_of_nonneg_right (atomBudget_le_chebPrimeBound hx hP hR)
      (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' v))

/-- Positive remainder matrix `archMatrix (log x) N + atomBudget x P R • I - translationPrimeMatrix`. -/
def chebPositiveRemainder (x P R N : ℕ) :
    Matrix (Cvs.Finite.SymmetricModeSet.Idx N) (Cvs.Finite.SymmetricModeSet.Idx N) ℝ :=
  Cvs.WeilForm.PrimeDiagonalBulkSchur.archMatrix (Real.log x) N
    + Matrix.diagonal (fun _ => atomBudget x P R)
    - Cvs.WeilForm.PrimeDiagonalBulkSchur.translationPrimeMatrix P R (Real.log x) N

/-- Upper spectral norm budget `archBudget (log x) + 2 * atomBudget x P R` for `chebPositiveRemainder`. -/
def chebRemainderBudget (x P R : ℕ) : ℝ :=
  Cvs.WeilForm.EvenBoundaryKernelBound.archBudget (Real.log x) + 2 * atomBudget x P R

/-- High-mode cosine bulk floor `archLower T - atomBudget x P R` with 3-cut `atomBudget`. -/
def chebHighFloor (x P R : ℕ) (T : ℝ) : ℝ :=
  Cvs.WeilForm.ArithmeticFloorAboveBand.archLower T - atomBudget x P R

/-- `chebPositiveRemainder x P R N` is symmetric for `1 < x`. -/
theorem chebPositiveRemainder_symm {x : ℕ} (hx : 1 < x) (P R N : ℕ)
    (i j : Cvs.Finite.SymmetricModeSet.Idx N) :
    chebPositiveRemainder x P R N i j = chebPositiveRemainder x P R N j i := by
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  simp only [chebPositiveRemainder, Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply,
    Cvs.WeilForm.PrimeDiagonalBulkSchur.archMatrix_symm (Real.log x) N i j,
    Cvs.WeilForm.PrimeDiagonalBulkSchur.translationPrimeMatrix_symm hL P R N i j]
  by_cases hij : i = j
  · subst hij; rfl
  · simp [hij, Ne.symm hij]

/-- `chebRemainderBudget x P R` is strictly positive for `1 < x`. -/
theorem chebRemainderBudget_pos {x : ℕ} (hx : 1 < x) (P R : ℕ) :
    0 < chebRemainderBudget x P R := by
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  have hp := Cvs.Finite.WindowMatrixSymbolKernel.poleFactor_nonneg (Real.log x)
  have hd := Cvs.WeilForm.EvenBoundaryKernelBound.first_gap_pos hL
  have hz := Cvs.WeilForm.EvenBoundaryKernelBound.zeroBudget_nonneg hL
  have hc := atomBudget_nonneg hx P R
  unfold chebRemainderBudget Cvs.WeilForm.EvenBoundaryKernelBound.archBudget Cvs.WeilForm.EvenBoundaryKernelBound.ladderBudget
  positivity

/-- Decomposition of `Cvs.Finite.TruncationQuadraticForm.M` into the `atomBudget`-shifted archimedean diagonal plus
`chebPositiveRemainder`. -/
theorem matrix_eq_cheb_shifted_positive {x : ℕ} (hx : 1 < x) (P R N : ℕ) :
    Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) =
      Matrix.diagonal (fun i =>
        Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
          (2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x)
          - atomBudget x P R)
      + chebPositiveRemainder x P R N := by
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  rw [Cvs.WeilForm.PrimeDiagonalBulkSchur.matrix_eq_arch_sub_prime hL]
  ext i j
  simp only [chebPositiveRemainder, Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply]
  split_ifs <;> ring

/-- Two-sided quadratic interval `0 ≤ v ⬝ᵥ (chebPositiveRemainder *ᵥ v) ≤ chebRemainderBudget * (v ⬝ᵥ v)`
for even vectors `v : Idx N → ℝ`, uniformly in `N`. -/
theorem chebPositiveRemainder_quad_interval {x : ℕ} (hx : 1 < x) (P R N : ℕ)
    {v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hv : ∀ i, v (Cvs.Finite.SymmetricModeSet.negI N i) = v i) :
    0 ≤ v ⬝ᵥ (chebPositiveRemainder x P R N *ᵥ v) ∧
      v ⬝ᵥ (chebPositiveRemainder x P R N *ᵥ v) ≤ chebRemainderBudget x P R * (v ⬝ᵥ v) := by
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  have ha := Cvs.WeilForm.PrimeDiagonalBulkSchur.arch_quad_interval hL N v hv
  have hp := abs_le.mp (abs_translationPrime_quad_le_atomBudget hx P R N hv)
  have hd : v ⬝ᵥ (Matrix.diagonal (fun _ : Cvs.Finite.SymmetricModeSet.Idx N => atomBudget x P R) *ᵥ v)
      = atomBudget x P R * (v ⬝ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  unfold chebPositiveRemainder chebRemainderBudget
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add, hd]
  constructor <;> nlinarith

/-- `chebPositiveRemainder x P R N` is positive semidefinite on even mode vectors. -/
theorem chebPositiveRemainder_quad_nonneg {x : ℕ} (hx : 1 < x) (P R N : ℕ)
    {v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hv : ∀ i, v (Cvs.Finite.SymmetricModeSet.negI N i) = v i) :
    0 ≤ v ⬝ᵥ (chebPositiveRemainder x P R N *ᵥ v) :=
  (chebPositiveRemainder_quad_interval hx P R N hv).1

private theorem cheb_shifted_diagonal_high_floor {x P R N : ℕ} {T : ℝ} (hT : 2 ≤ T)
    (w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ)
    (hband : ∀ i, |2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x| < T → w i = 0) :
    chebHighFloor x P R T * (w ⬝ᵥ w) ≤
      w ⬝ᵥ (Matrix.diagonal (fun i =>
        Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
          (2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x)
          - atomBudget x P R) *ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : |2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x| < T
  · simp [hband i hi]
  · have hs := Cvs.WeilForm.ArithmeticFloorAboveBand.archLower_le_archSymbol hT (le_of_not_gt hi)
    unfold chebHighFloor
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (w i))]

/-- **Cosine High-Bulk Floor with 3-Cut `atomBudget`** (`1 < x`, `2 ≤ T`): every even `w : Idx N → ℝ`
supported above frequency `T` satisfies `chebHighFloor x P R T * (w ⬝ᵥ w) ≤ w ⬝ᵥ (M *ᵥ w)` for all `N`. -/
theorem matrix_high_bulk_floor_atomBudget {x : ℕ} (hx : 1 < x) {T : ℝ} (hT : 2 ≤ T)
    (P R N : ℕ) {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : ∀ i, w (Cvs.Finite.SymmetricModeSet.negI N i) = w i)
    (hband : ∀ i, |2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x| < T → w i = 0) :
    chebHighFloor x P R T * (w ⬝ᵥ w) ≤
      w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) := by
  have hd := cheb_shifted_diagonal_high_floor (P := P) (R := R) hT w hband
  have hp := chebPositiveRemainder_quad_nonneg hx P R N hw
  rw [matrix_eq_cheb_shifted_positive hx P R N, Matrix.add_mulVec, dotProduct_add]
  linarith

/-- At `T = highBulkThreshold x b` (`1 < x`), `b + 1 ≤ chebHighFloor x x (Nat.clog 2 x) T`. -/
theorem add_one_le_chebHighFloor_highBulkThreshold {x : ℕ} (hx : 1 < x) (b : ℝ) :
    b + 1 ≤ chebHighFloor x x (Nat.clog 2 x) (highBulkThreshold x b) := by
  have hbud := atomBudget_le_chebPrimeBound hx (Nat.le_succ x) (Nat.le_succ _)
  have hfl := add_one_add_chebPrimeBound_le_floorAt_highBulkThreshold x b
  change b + 1 ≤ Cvs.L2a.ArchChannelFloorAbove.floorAt (highBulkThreshold x b) - atomBudget x x (Nat.clog 2 x)
  linarith

/-- **Explicit Cosine High-Bulk Coercivity above `highBulkThreshold x b`** (`1 < x`): for all `N : ℕ`,
`(b + 1) * (w ⬝ᵥ w) ≤ w ⬝ᵥ (M *ᵥ w)` on every even `w : Idx N → ℝ` vanishing below `highBulkThreshold x b`. -/
theorem matrix_high_bulk_floor_highBulkThreshold {x : ℕ} (hx : 1 < x) (b : ℝ) (N : ℕ)
    {w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hw : ∀ i, w (Cvs.Finite.SymmetricModeSet.negI N i) = w i)
    (hband : ∀ i,
      |2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x|
        < highBulkThreshold x b → w i = 0) :
    (b + 1) * (w ⬝ᵥ w) ≤
      w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x)
        (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ w) :=
  (mul_le_mul_of_nonneg_right (add_one_le_chebHighFloor_highBulkThreshold hx b)
    (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' w)).trans
    (matrix_high_bulk_floor_atomBudget hx (two_le_highBulkThreshold x b) x (Nat.clog 2 x) N hw hband)

private theorem quad_add_smul_symm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hA : ∀ i j, A i j = A j i) (u w : ι → ℝ) (t : ℝ) :
    (u + t • w) ⬝ᵥ (A *ᵥ (u + t • w)) =
      u ⬝ᵥ (A *ᵥ u) + 2 * t * (u ⬝ᵥ (A *ᵥ w)) + t ^ 2 * (w ⬝ᵥ (A *ᵥ w)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, smul_dotProduct,
    dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm hA w u]
  ring

/-- Damped Schur lower bound for `chebPositiveRemainder x P R N` on even vectors `u, w`. -/
theorem chebRemainder_damped_lower {x : ℕ} (hx : 1 < x) (P R N : ℕ)
    {u w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hu : ∀ i, u (Cvs.Finite.SymmetricModeSet.negI N i) = u i)
    (hw : ∀ i, w (Cvs.Finite.SymmetricModeSet.negI N i) = w i)
    {a : ℝ} (ha : 0 < a) :
    a / (a + chebRemainderBudget x P R) * (u ⬝ᵥ (chebPositiveRemainder x P R N *ᵥ u)) ≤
      (u + w) ⬝ᵥ (chebPositiveRemainder x P R N *ᵥ (u + w)) + a * (w ⬝ᵥ w) := by
  set C := chebRemainderBudget x P R
  set A := chebPositiveRemainder x P R N
  have hC : 0 < C := chebRemainderBudget_pos hx P R
  let t := (a + C) / C
  have hp : 0 ≤ (u + t • w) ⬝ᵥ (A *ᵥ (u + t • w)) :=
    (chebPositiveRemainder_quad_interval hx P R N (v := u + t • w) (fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu, hw])).1
  have hq : w ⬝ᵥ (A *ᵥ w) ≤ C * (w ⬝ᵥ w) :=
    (chebPositiveRemainder_quad_interval hx P R N hw).2
  have hrem : 0 ≤ w ⬝ᵥ w - (w ⬝ᵥ (A *ᵥ w)) / C := by
    rw [sub_nonneg, div_le_iff₀ hC]
    simpa only [mul_comm] using hq
  have hm : 0 ≤ C / (a + C) := div_nonneg hC.le (by positivity)
  have hsum := add_nonneg (mul_nonneg hm hp) (mul_nonneg ha.le hrem)
  have he : C / (a + C) * ((u + t • w) ⬝ᵥ (A *ᵥ (u + t • w))) +
      a * (w ⬝ᵥ w - (w ⬝ᵥ (A *ᵥ w)) / C) =
        (u + w) ⬝ᵥ (A *ᵥ (u + w)) + a * (w ⬝ᵥ w) -
          a / (a + C) * (u ⬝ᵥ (A *ᵥ u)) := by
    rw [quad_add_smul_symm A (chebPositiveRemainder_symm hx P R N)]
    have hadd := quad_add_smul_symm A (chebPositiveRemainder_symm hx P R N) u w 1
    simp only [one_smul, one_pow, mul_one] at hadd
    rw [hadd]
    dsimp only [t]
    field_simp
    ring
  rw [he] at hsum
  exact sub_nonneg.mp hsum

/-- **3-Cut Damped Low–High Schur Complement Inequality** (`1 < x`, `2 ≤ T`): absorbs the high-mode
block `w` and all low–high cross-coupling `2 (u ⬝ᵥ (M *ᵥ w))` across every cosine order `N : ℕ`. -/
theorem cheb_damped_low_high_lower {x : ℕ} (hx : 1 < x) {T s : ℝ} (hT : 2 ≤ T)
    (P R N : ℕ) {u w : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hu : ∀ i, u (Cvs.Finite.SymmetricModeSet.negI N i) = u i)
    (hw : ∀ i, w (Cvs.Finite.SymmetricModeSet.negI N i) = w i)
    (hdisjoint : ∀ i, u i * w i = 0)
    (hband : ∀ i, |2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x| < T → w i = 0)
    (hreserve : s < chebHighFloor x P R T) :
    u ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ u)
        - s * (u ⬝ᵥ u)
        - chebRemainderBudget x P R
          / (chebHighFloor x P R T - s + chebRemainderBudget x P R)
          * (u ⬝ᵥ (chebPositiveRemainder x P R N *ᵥ u)) ≤
      (u + w) ⬝ᵥ
          (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ (u + w))
        - s * ((u + w) ⬝ᵥ (u + w)) := by
  let a := chebHighFloor x P R T - s
  let C := chebRemainderBudget x P R
  let A := chebPositiveRemainder x P R N
  let D : Matrix (Cvs.Finite.SymmetricModeSet.Idx N) (Cvs.Finite.SymmetricModeSet.Idx N) ℝ :=
    Matrix.diagonal (fun i =>
      Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
        (2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x) - atomBudget x P R)
  have ha : 0 < a := sub_pos.mpr hreserve
  have hC : 0 < C := chebRemainderBudget_pos hx P R
  have hd : chebHighFloor x P R T * (w ⬝ᵥ w) ≤ w ⬝ᵥ (D *ᵥ w) :=
    cheb_shifted_diagonal_high_floor (P := P) (R := R) hT w hband
  have hp : a / (a + C) * (u ⬝ᵥ (A *ᵥ u)) ≤ (u + w) ⬝ᵥ (A *ᵥ (u + w)) + a * (w ⬝ᵥ w) :=
    chebRemainder_damped_lower hx P R N hu hw ha
  have hnorm : (u + w) ⬝ᵥ (u + w) = u ⬝ᵥ u + w ⬝ᵥ w := by
    have hz : u ⬝ᵥ w = 0 := Finset.sum_eq_zero fun i _ => hdisjoint i
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm w u, hz]
    ring
  have hdiag : (u + w) ⬝ᵥ (D *ᵥ (u + w)) = u ⬝ᵥ (D *ᵥ u) + w ⬝ᵥ (D *ᵥ w) := by
    change (u + w) ⬝ᵥ (Matrix.diagonal _ *ᵥ (u + w)) =
      u ⬝ᵥ (Matrix.diagonal _ *ᵥ u) + w ⬝ᵥ (Matrix.diagonal _ *ᵥ w)
    simp only [dotProduct, Matrix.mulVec_diagonal, ← Finset.sum_add_distrib, Pi.add_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc
      _ = u i * ((Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
              (2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x)
              - atomBudget x P R) * u i) +
          w i * ((Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
              (2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x)
              - atomBudget x P R) * w i) +
          2 * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
              (2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x)
              - atomBudget x P R) * (u i * w i) := by ring
      _ = _ := by rw [hdisjoint i]; ring
  have hlo : u ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ u)
      = u ⬝ᵥ (D *ᵥ u) + u ⬝ᵥ (A *ᵥ u) := by
    rw [matrix_eq_cheb_shifted_positive hx P R N, Matrix.add_mulVec, dotProduct_add]
  have hfull :
      (u + w) ⬝ᵥ
          (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ (u + w))
        = u ⬝ᵥ (D *ᵥ u) + w ⬝ᵥ (D *ᵥ w) + (u + w) ⬝ᵥ (A *ᵥ (u + w)) := by
    rw [matrix_eq_cheb_shifted_positive hx P R N, Matrix.add_mulVec, dotProduct_add]
    rw [show (u + w) ⬝ᵥ (Matrix.diagonal _ *ᵥ (u + w)) = (u + w) ⬝ᵥ (D *ᵥ (u + w)) from rfl, hdiag]
  have hr : a / (a + C) + C / (a + C) = 1 := by
    rw [← add_div, div_self (add_pos ha hC).ne']
  have hrq := congrArg (fun z : ℝ => z * (u ⬝ᵥ (A *ᵥ u))) hr
  change _ - C / (a + C) * (u ⬝ᵥ (A *ᵥ u)) ≤ _
  rw [hlo, hfull, hnorm]
  dsimp only [a] at hp hrq
  nlinarith

/-- Damped retention weight `chebHighFloor / (chebHighFloor + chebRemainderBudget)` on `ModeBox M₀`. -/
def chebDampedFloorConst (x P R : ℕ) (T : ℝ) : ℝ :=
  chebHighFloor x P R T / (chebHighFloor x P R T + chebRemainderBudget x P R)

/-- `atomBudget`-shifted archimedean diagonal quadratic form on the finite box `ModeBox M₀`. -/
def boxChebShiftedDiagQ (x P R M₀ : ℕ)
    (η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ) : ℝ :=
  ∑ m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * Real.pi * (m.1 : ℝ) / Real.log x) - atomBudget x P R)
      * η m ^ 2

/-- `toModeBox` preserves the `atomBudget`-shifted archimedean diagonal form for `r` supported on
`modeCutoffSet N M₀`. -/
theorem toModeBox_chebShiftedDiag_eq (x P R N M₀ : ℕ)
    {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : ∀ i, i ∉ Cvs.Route.FreqThresholdModeCutoff.modeCutoffSet N M₀ → r i = 0) :
    r ⬝ᵥ (Matrix.diagonal (fun i =>
        Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
          (2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x)
          - atomBudget x P R) *ᵥ r) =
      boxChebShiftedDiagQ x P R M₀ (Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r) := by
  have h := Cvs.Route.ModeBoxIsometricTransfer.toModeBox_quad_eq N M₀
    (fun m₁ m₂ : ℤ =>
      if m₁ = m₂ then
        Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * Real.pi * (m₁ : ℝ) / Real.log x) - atomBudget x P R
      else 0) hr
  have h1 : Matrix.of (fun m₁ m₂ : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ =>
      if Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m₁ = Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m₂ then
        Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
          (2 * Real.pi * (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m₁ : ℝ) / Real.log x)
          - atomBudget x P R
      else 0) =
      Matrix.diagonal (fun m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ =>
        Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * Real.pi * (m.1 : ℝ) / Real.log x)
          - atomBudget x P R) := by
    ext m₁ m₂
    simp [Matrix.diagonal_apply, Cvs.Route.ModeBoxIsometricTransfer.boxMode]
  have h2 : Matrix.of (fun i j : Cvs.Finite.SymmetricModeSet.Idx N =>
      if Cvs.Finite.SymmetricModeSet.mode N i = Cvs.Finite.SymmetricModeSet.mode N j then
        Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
          (2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x)
          - atomBudget x P R
      else 0) =
      Matrix.diagonal (fun i : Cvs.Finite.SymmetricModeSet.Idx N =>
        Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
          (2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x)
          - atomBudget x P R) := by
    ext i j
    simp [(Cvs.Finite.SymmetricModeSet.mode_injective N).eq_iff, Matrix.diagonal_apply]
  rw [h1, h2] at h
  rw [← h]
  simp only [dotProduct, Matrix.mulVec_diagonal, boxChebShiftedDiagQ]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- On `r` supported on `modeCutoffSet N M₀`, `r ⬝ᵥ (chebPositiveRemainder *ᵥ r)` equals
`r ⬝ᵥ (M *ᵥ r) - boxChebShiftedDiagQ x P R M₀ (toModeBox N M₀ r)`. -/
theorem chebPositiveRemainder_quad_eq_M_sub_boxChebShiftedDiagQ {x : ℕ} (hx : 1 < x)
    (P R N M₀ : ℕ) {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : ∀ i, i ∉ Cvs.Route.FreqThresholdModeCutoff.modeCutoffSet N M₀ → r i = 0) :
    r ⬝ᵥ (chebPositiveRemainder x P R N *ᵥ r) =
      r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r)
        - boxChebShiftedDiagQ x P R M₀ (Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r) := by
  have hdecomp :
      r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) =
        r ⬝ᵥ (Matrix.diagonal (fun i =>
          Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
            (2 * Real.pi * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / Real.log x)
            - atomBudget x P R) *ᵥ r) +
        r ⬝ᵥ (chebPositiveRemainder x P R N *ᵥ r) := by
    rw [matrix_eq_cheb_shifted_positive hx P R N, Matrix.add_mulVec, dotProduct_add]
  rw [toModeBox_chebShiftedDiag_eq x P R N M₀ hr] at hdecomp
  linarith

/-- **`∀ N`-Free Even-Sector Positivity of `Cvs.Finite.TruncationQuadraticForm.M` from Finite `ModeBox M₀` Damped Positivity**:
transfers damped positivity on `ModeBox M₀` across every cosine order `N : ℕ`. -/
theorem M_even_nonneg_of_modeBox_cheb_damped {x : ℕ} (hx : 1 < x) {T : ℝ} (hT : 2 ≤ T)
    {P R M₀ : ℕ} (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) T ≤ M₀ + 1)
    (hgap : 0 < chebHighFloor x P R T)
    (hbox : ∀ η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀),
      0 ≤ boxChebShiftedDiagQ x P R M₀ η +
        chebDampedFloorConst x P R T *
          (η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ η)
            - boxChebShiftedDiagQ x P R M₀ η))
    (N : ℕ) :
    ∀ v ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ v) := by
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  intro v hv
  obtain ⟨r, hr, w, hw, rfl⟩ :=
    Cvs.Route.EvenMatrixSlotPoleRestored.exists_dec
      (Cvs.Route.FreqThresholdModeCutoff.modeCutoffRung_le_evenModeSub N M₀) v hv
  have hsupp : ∀ i, i ∉ Cvs.Route.FreqThresholdModeCutoff.modeCutoffSet N M₀ → r i = 0 :=
    fun _ hi => Cvs.Route.ModeBoxIsometricTransfer.apply_eq_zero_of_mem_modeCutoffRung hr hi
  have hev : Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r
      ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀) :=
    Cvs.Route.ModeBoxIsometricTransfer.toModeBox_mem_evenModeSub N M₀
      (Cvs.Route.FreqThresholdModeCutoff.modeCutoffRung_le_evenModeSub N M₀ hr)
  have hη := hbox (Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r) hev
  rw [Cvs.Route.ModeBoxIsometricTransfer.toModeBox_M_quad_eq P R N M₀ (Real.log x) hsupp] at hη
  have hdamp := cheb_damped_low_high_lower (s := 0) hx hT P R N
    (Cvs.Route.FreqThresholdModeCutoff.modeCutoffRung_le_evenModeSub N M₀ hr) hw.1
    (Cvs.Route.ModeBoxDampedReduction.modeCutoffRung_mul_bulk_eq_zero hr hw)
    (Cvs.Route.ModeBoxDampedReduction.bulk_apply_eq_zero_of_freq_lt hL hK hw) hgap
  simp only [zero_mul, sub_zero] at hdamp
  rw [chebPositiveRemainder_quad_eq_M_sub_boxChebShiftedDiagQ hx P R N M₀ hsupp] at hdamp
  have hden : chebHighFloor x P R T + chebRemainderBudget x P R ≠ 0 :=
    (add_pos hgap (chebRemainderBudget_pos hx P R)).ne'
  have hid :
      r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) -
        chebRemainderBudget x P R /
          (chebHighFloor x P R T + chebRemainderBudget x P R) *
          (r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) -
            boxChebShiftedDiagQ x P R M₀ (Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r)) =
      boxChebShiftedDiagQ x P R M₀ (Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r) +
        chebDampedFloorConst x P R T *
          (r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) -
            boxChebShiftedDiagQ x P R M₀ (Cvs.Route.ModeBoxIsometricTransfer.toModeBox N M₀ r)) := by
    unfold chebDampedFloorConst
    field_simp [hden]
    ring
  linarith

/-- Euclidean low-bulk energy on `ModeBox M₀` below `cutoffOrder (log x) (highBulkThreshold x 0)`
(supported on `O(log x · exp(2 √x))` modes). -/
def boxChebLowBulkEnergy (x M₀ : ℕ) (η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ) : ℝ :=
  ∑ m ∈ Finset.univ.filter
    (fun m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ =>
      m.1.natAbs < Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) (highBulkThreshold x 0)),
    η m ^ 2

/-- `boxChebLowBulkEnergy x M₀ η` is nonnegative. -/
theorem boxChebLowBulkEnergy_nonneg (x M₀ : ℕ) (η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ) :
    0 ≤ boxChebLowBulkEnergy x M₀ η :=
  Finset.sum_nonneg fun m _ => sq_nonneg (η m)

/-- Lower bound on `boxChebShiftedDiagQ` in terms of `boxChebLowBulkEnergy`: above
`cutoffOrder (log x) (highBulkThreshold x 0)`, every mode has positive `atomBudget`-shifted weight. -/
theorem neg_mul_boxChebLowBulkEnergy_le_boxChebShiftedDiagQ {x : ℕ} (hx : 1 < x) (M₀ : ℕ)
    (η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ) :
    -(max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
        * boxChebLowBulkEnergy x M₀ η
      ≤ boxChebShiftedDiagQ x x (Nat.clog 2 x) M₀ η := by
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  have hdef : -boxChebShiftedDiagQ x x (Nat.clog 2 x) M₀ η
      ≤ ∑ m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
          max 0 (atomBudget x x (Nat.clog 2 x)
            - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * Real.pi * (m.1 : ℝ) / Real.log x)) * η m ^ 2 := by
    unfold boxChebShiftedDiagQ
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun m _ => ?_
    have hle := le_max_right 0 (atomBudget x x (Nat.clog 2 x)
      - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * Real.pi * (m.1 : ℝ) / Real.log x))
    have hmul := mul_le_mul_of_nonneg_right hle (sq_nonneg (η m))
    linarith
  have hfilt : (∑ m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
        max 0 (atomBudget x x (Nat.clog 2 x)
          - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * Real.pi * (m.1 : ℝ) / Real.log x)) * η m ^ 2)
      = ∑ m ∈ Finset.univ.filter
          (fun m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ =>
            m.1.natAbs < Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) (highBulkThreshold x 0)),
          max 0 (atomBudget x x (Nat.clog 2 x)
            - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * Real.pi * (m.1 : ℝ) / Real.log x)) * η m ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · rfl
    · have hfreq := Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder_frequency hL
        (highBulkThreshold x 0) m.1 (le_of_not_gt hm)
      have harch := Cvs.WeilForm.ArithmeticFloorAboveBand.archLower_le_archSymbol
        (two_le_highBulkThreshold x 0) hfreq
      have hfl := add_one_le_chebHighFloor_highBulkThreshold hx 0
      unfold chebHighFloor at hfl
      rw [max_eq_left (by linarith), zero_mul]
  have hle_cap : (∑ m ∈ Finset.univ.filter
          (fun m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ =>
            m.1.natAbs < Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) (highBulkThreshold x 0)),
          max 0 (atomBudget x x (Nat.clog 2 x)
            - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * Real.pi * (m.1 : ℝ) / Real.log x)) * η m ^ 2)
      ≤ max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
          * boxChebLowBulkEnergy x M₀ η := by
    rw [boxChebLowBulkEnergy, Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    have h0 : max 0 (atomBudget x x (Nat.clog 2 x)
          - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * Real.pi * (m.1 : ℝ) / Real.log x))
        ≤ max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) :=
      max_le_max_left 0 (sub_le_sub_left (Cvs.WeilForm.Archimedean.ArchSymbolGlobalMinimum.archSymbol_zero_le _) _)
    exact mul_le_mul_of_nonneg_right h0 (sq_nonneg (η m))
  rw [hfilt] at hdef
  linarith

/-- Explicit 3-cut damped frequency threshold achieving an `ε`-small low-bulk floor on `ModeBox M₀`. -/
def chebDampedThreshold (x : ℕ) (ε : ℝ) : ℝ :=
  highBulkThreshold x
    (chebRemainderBudget x x (Nat.clog 2 x)
      * max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / ε)

/-- `2 ≤ chebDampedThreshold x ε` for all `x : ℕ` and `ε : ℝ`. -/
theorem two_le_chebDampedThreshold (x : ℕ) (ε : ℝ) :
    2 ≤ chebDampedThreshold x ε :=
  two_le_highBulkThreshold x _

/-- `chebHighFloor` at `chebDampedThreshold x ε` strictly exceeds the required Schur damping ratio. -/
theorem chebHighFloor_chebDampedThreshold_gt {x : ℕ} (hx : 1 < x) (ε : ℝ) :
    chebRemainderBudget x x (Nat.clog 2 x)
        * max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / ε
      < chebHighFloor x x (Nat.clog 2 x) (chebDampedThreshold x ε) := by
  have h := add_one_le_chebHighFloor_highBulkThreshold hx
    (chebRemainderBudget x x (Nat.clog 2 x)
      * max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / ε)
  unfold chebDampedThreshold
  linarith

/-- `chebHighFloor` at `chebDampedThreshold x ε` is strictly positive for `1 < x` and `0 < ε`. -/
theorem chebHighFloor_chebDampedThreshold_pos {x : ℕ} (hx : 1 < x) {ε : ℝ} (hε : 0 < ε) :
    0 < chebHighFloor x x (Nat.clog 2 x) (chebDampedThreshold x ε) := by
  have hnn : 0 ≤ chebRemainderBudget x x (Nat.clog 2 x)
      * max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / ε :=
    div_nonneg (mul_nonneg (chebRemainderBudget_pos hx x (Nat.clog 2 x)).le (le_max_left 0 _)) hε.le
  exact hnn.trans_lt (chebHighFloor_chebDampedThreshold_gt hx ε)

/-- Any `η` on `ModeBox M₀` with `ε * boxChebLowBulkEnergy x M₀ η ≤ η ⬝ᵥ (M *ᵥ η)` satisfies the
3-cut damped Schur inequality at `T = chebDampedThreshold x ε`. -/
theorem cheb_damped_ineq_of_boxChebLowBulkEnergy_eps {x : ℕ} (hx : 1 < x) {ε : ℝ} (hε : 0 < ε)
    {M₀ : ℕ} {η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ}
    (hη : ε * boxChebLowBulkEnergy x M₀ η ≤
      η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x)
        (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ η)) :
    0 ≤ boxChebShiftedDiagQ x x (Nat.clog 2 x) M₀ η +
      chebDampedFloorConst x x (Nat.clog 2 x) (chebDampedThreshold x ε) *
        (η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x)
            (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ η)
          - boxChebShiftedDiagQ x x (Nat.clog 2 x) M₀ η) := by
  set T := chebDampedThreshold x ε
  set c := chebDampedFloorConst x x (Nat.clog 2 x) T
  have hgap : 0 < chebHighFloor x x (Nat.clog 2 x) T :=
    chebHighFloor_chebDampedThreshold_pos hx hε
  have hrem : 0 < chebRemainderBudget x x (Nat.clog 2 x) :=
    chebRemainderBudget_pos hx x (Nat.clog 2 x)
  have hc_pos : 0 < c := div_pos hgap (add_pos hgap hrem)
  have hc_lt : c < 1 := by
    dsimp [c, chebDampedFloorConst]
    rw [div_lt_one (add_pos hgap hrem)]
    linarith
  have hrat_eq : (1 - c) / c
      = chebRemainderBudget x x (Nat.clog 2 x) / chebHighFloor x x (Nat.clog 2 x) T := by
    dsimp [c, chebDampedFloorConst]
    have hden : chebHighFloor x x (Nat.clog 2 x) T + chebRemainderBudget x x (Nat.clog 2 x) ≠ 0 :=
      (add_pos hgap hrem).ne'
    have ha : chebHighFloor x x (Nat.clog 2 x) T ≠ 0 := hgap.ne'
    field_simp [hden, ha]
    ring
  have hrat_le : ((1 - c) / c)
      * max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) ≤ ε := by
    rw [hrat_eq, div_mul_eq_mul_div, div_le_iff₀ hgap]
    have hgt := (chebHighFloor_chebDampedThreshold_gt hx ε).le
    have hmul := (div_le_iff₀ hε).mp hgt
    linarith
  have hrat_nn : 0 ≤ (1 - c) / c := div_nonneg (sub_nonneg.mpr hc_lt.le) hc_pos.le
  have hdef : -boxChebShiftedDiagQ x x (Nat.clog 2 x) M₀ η
      ≤ max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
        * boxChebLowBulkEnergy x M₀ η := by
    linarith [neg_mul_boxChebLowBulkEnergy_le_boxChebShiftedDiagQ hx M₀ η]
  have h1 := mul_le_mul_of_nonneg_left hdef hrat_nn
  have h2 := mul_le_mul_of_nonneg_right hrat_le (boxChebLowBulkEnergy_nonneg x M₀ η)
  have h3 : ((1 - c) / c) * (-boxChebShiftedDiagQ x x (Nat.clog 2 x) M₀ η) ≤
      η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x)
        (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ η) := by
    have h12 : ((1 - c) / c) *
        (max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
          * boxChebLowBulkEnergy x M₀ η) =
        (((1 - c) / c)
          * max 0 (atomBudget x x (Nat.clog 2 x) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
          * boxChebLowBulkEnergy x M₀ η := by ring
    exact h1.trans ((le_of_eq h12).trans (h2.trans hη))
  have h4 := mul_le_mul_of_nonneg_left h3 hc_pos.le
  have hrew : c * ((1 - c) / c * -boxChebShiftedDiagQ x x (Nat.clog 2 x) M₀ η) =
      -(1 - c) * boxChebShiftedDiagQ x x (Nat.clog 2 x) M₀ η := by
    field_simp [hc_pos.ne']
  rw [hrew] at h4
  linarith

/-- **`∀ N`-Free Even-Sector Positivity of `Cvs.Finite.TruncationQuadraticForm.M` from Low-Bulk Energy on `ModeBox M₀`** (`1 < x`):
discharges all high modes and low–high cross-coupling across all `N : ℕ` via 3-cut `atomBudget`. -/
theorem M_even_nonneg_of_modeBox_cheb_lowBand_eps {x : ℕ} (hx : 1 < x) {ε : ℝ} (hε : 0 < ε)
    {M₀ : ℕ}
    (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) (chebDampedThreshold x ε) ≤ M₀ + 1)
    (hbox : ∀ η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀),
      ε * boxChebLowBulkEnergy x M₀ η ≤
        η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x)
          (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ η))
    (N : ℕ) :
    ∀ v ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x)
        (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ v) :=
  M_even_nonneg_of_modeBox_cheb_damped hx (two_le_chebDampedThreshold x ε) hK
    (chebHighFloor_chebDampedThreshold_pos hx hε)
    (fun η hη => cheb_damped_ineq_of_boxChebLowBulkEnergy_eps hx hε (hbox η hη)) N

/-- **Continuous Window Positivity on `Ev x` from Finite `ModeBox M₀` Low-Bulk Positivity** (`2 ≤ x`):
transfers the finite low-mode `ModeBox M₀` bound directly to `∀ φ ∈ Ev x, 0 ≤ Qx x φ`. -/
theorem Qx_Ev_nonneg_of_modeBox_cheb_lowBand_eps {x : ℕ} (hx2 : 2 ≤ x) {ε : ℝ} (hε : 0 < ε)
    {M₀ : ℕ}
    (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) (chebDampedThreshold x ε) ≤ M₀ + 1)
    (hbox : ∀ η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀),
      ε * boxChebLowBulkEnergy x M₀ η ≤
        η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x)
          (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ η)) :
    ∀ φ ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, 0 ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x φ :=
  (Cvs.Route.EvenMatrixSlotPoleRestored.Qx_Ev_nonneg_iff_M_even_nonneg hx2).2
    (M_even_nonneg_of_modeBox_cheb_lowBand_eps (by omega : 1 < x) hε hK hbox)

/-- **`∀ N`-Free Low-Bulk `ModeBox M₀` Criterion for `RiemannHypothesis`**: with the entire high bulk
and low–high Schur coupling discharged by the 3-cut, only the finite low-mode box is required. -/
theorem riemannHypothesis_of_modeBox_cheb_lowBulk
    (h : ∃ᶠ x : ℕ in atTop, ∃ (ε : ℝ) (M₀ : ℕ),
      0 < ε ∧
      Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) (chebDampedThreshold x ε) ≤ M₀ + 1 ∧
      ∀ η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀),
        ε * boxChebLowBulkEnergy x M₀ η ≤
          η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x)
            (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ η)) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨⟨ε, M₀, hε, hK, hbox⟩, hx2⟩ =>
      Qx_Ev_nonneg_of_modeBox_cheb_lowBand_eps hx2 hε hK hbox)

/-- **Four-Channel Log-Minorant Low-Bulk Criterion for `RiemannHypothesis`**: replaces `Cvs.Finite.TruncationQuadraticForm.M` on
the finite low-mode box `ModeBox M₀` with the closed-form minorant `Cvs.Route.ModeBoxLogMinorant.boxFourChannelLogMinorant`. -/
theorem riemannHypothesis_of_lowBulk_fourChannelMinorant
    (h : ∃ᶠ x : ℕ in atTop, ∃ (ε : ℝ) (M₀ : ℕ),
      0 < ε ∧
      Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) (chebDampedThreshold x ε) ≤ M₀ + 1 ∧
      ∀ η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀),
        ε * boxChebLowBulkEnergy x M₀ η ≤
          η ⬝ᵥ (Cvs.Route.ModeBoxLogMinorant.boxFourChannelLogMinorant
            x (Nat.clog 2 x) (Real.log x) M₀ *ᵥ η)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_modeBox_cheb_lowBulk
    ((h.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨⟨ε, M₀, hε, hK, hmin⟩, hx2⟩ => ?_)
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
  refine ⟨ε, M₀, hε, hK, fun η hη => (hmin η hη).trans
    (Cvs.Route.ModeBoxLogMinorant.boxFourChannelLogMinorant_le_boxM hL x (Nat.clog 2 x) M₀ hη)⟩

/-!
## Section 9: Structure and Decomposition of the Low-Bulk Band

Excises the infrared origin band on `Dom x`, diagonalizes the intermediate Green channels on
`ModeBox M₀`, and reduces the low-bulk core to `boxUniversalCoreEnergy` and `boxPureCurvatureMatrix`.
-/

/-! ### Part 9A: Unconditional Origin-Band Excision and Three-Band Mesoscopic Pinch on `Dom x` -/

/-- Radius around `t = 0` on which `Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol x (b + 3)` exceeds `b + 1`. -/
def originBulkRadius (x : ℕ) (b : ℝ) : ℝ :=
  (1 / 2) / (Cvs.WeilForm.StepQuadratureResidual.totalMeanFreeSlope (x - 1) + (b + 3) * Real.log x + 1)

/-- Outer frequency threshold above which `Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol x (b + 3)` exceeds `b + 1`. -/
def mesoOuterThreshold (x : ℕ) (b : ℝ) : ℝ :=
  2 * Real.pi * Real.exp
    (|(b + 1) + Cvs.WeilForm.MeanFreeSpectralIdentity.totalMeanFreeMaxAmp (x - 1) + (b + 3)| + 30)

/-- Uniform depth bound for `-Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol x (b + 3)` across the mesoscopic shell. -/
def mesoShellDepth (x : ℕ) (b : ℝ) : ℝ :=
  1.3801 + Cvs.WeilForm.MeanFreeSpectralIdentity.totalMeanFreeMaxAmp (x - 1) + (b + 3)

/-- Admissible spectral mass fraction on the punctured mesoscopic shell `originBulkRadius ≤ |t| < mesoOuterThreshold`. -/
def mesoShellLeakageCap (x : ℕ) (b : ℝ) : ℝ :=
  1 / (b + 1 + mesoShellDepth x b)

/-- `originBulkRadius x b` is strictly positive for `0 ≤ b`. -/
theorem originBulkRadius_pos {x : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    0 < originBulkRadius x b := by
  unfold originBulkRadius
  have hs := Cvs.WeilForm.StepQuadratureResidual.totalMeanFreeSlope_nonneg (x - 1)
  have hlog : 0 ≤ (b + 3) * Real.log x :=
    mul_nonneg (by linarith) (Real.log_natCast_nonneg x)
  exact div_pos (by norm_num) (by linarith)

/-- `originBulkRadius x b ≤ 1 / 2` for `0 ≤ b`. -/
theorem originBulkRadius_le_half {x : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    originBulkRadius x b ≤ 1 / 2 := by
  unfold originBulkRadius
  have hs := Cvs.WeilForm.StepQuadratureResidual.totalMeanFreeSlope_nonneg (x - 1)
  have hlog : 0 ≤ (b + 3) * Real.log x :=
    mul_nonneg (by linarith) (Real.log_natCast_nonneg x)
  exact div_le_self (by norm_num) (by linarith)

/-- `2 ≤ mesoOuterThreshold x b` for all `x : ℕ` and `b : ℝ`. -/
theorem two_le_mesoOuterThreshold (x : ℕ) (b : ℝ) :
    2 ≤ mesoOuterThreshold x b := by
  unfold mesoOuterThreshold
  have he : 1 ≤ Real.exp
      (|(b + 1) + Cvs.WeilForm.MeanFreeSpectralIdentity.totalMeanFreeMaxAmp (x - 1) + (b + 3)| + 30) := by
    rw [Real.one_le_exp_iff]
    linarith [abs_nonneg ((b + 1) + Cvs.WeilForm.MeanFreeSpectralIdentity.totalMeanFreeMaxAmp (x - 1) + (b + 3))]
  nlinarith [Real.pi_gt_three]

/-- `originBulkRadius x b < mesoOuterThreshold x b` for `0 ≤ b`. -/
theorem originBulkRadius_lt_mesoOuterThreshold {x : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    originBulkRadius x b < mesoOuterThreshold x b :=
  lt_of_le_of_lt (originBulkRadius_le_half hb)
    (lt_of_lt_of_le (by norm_num : (1 / 2 : ℝ) < 2) (two_le_mesoOuterThreshold x b))

/-- `mesoShellDepth x b` is strictly positive for `0 ≤ b`. -/
theorem mesoShellDepth_pos {x : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    0 < mesoShellDepth x b := by
  unfold mesoShellDepth
  linarith [Cvs.WeilForm.MeanFreeSpectralIdentity.totalMeanFreeMaxAmp_nonneg (x - 1)]

/-- `mesoShellLeakageCap x b` is strictly positive for `0 ≤ b`. -/
theorem mesoShellLeakageCap_pos {x : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    0 < mesoShellLeakageCap x b := by
  unfold mesoShellLeakageCap
  have hd := mesoShellDepth_pos (x := x) hb
  exact div_pos zero_lt_one (by linarith)

/-- **Unconditional Infrared Origin Coercivity**: for `0 ≤ b` and `|t| < originBulkRadius x b`,
`b + 1 ≤ Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol x (b + 3) t`. -/
theorem augShiftedScaleSymbol_ge_of_lt_originBulkRadius {x : ℕ} {b t : ℝ} (hb : 0 ≤ b)
    (ht : |t| < originBulkRadius x b) :
    b + 1 ≤ Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol x (b + 3) t := by
  set S := Cvs.WeilForm.StepQuadratureResidual.totalMeanFreeSlope (x - 1) + (b + 3) * Real.log x
  have hS : 0 ≤ S := add_nonneg (Cvs.WeilForm.StepQuadratureResidual.totalMeanFreeSlope_nonneg (x - 1))
    (mul_nonneg (by linarith) (Real.log_natCast_nonneg x))
  have hden : 0 < S + 1 := by linarith
  have hlt : |t| * (S + 1) < 1 / 2 := (lt_div_iff₀ hden).mp ht
  have hSt : S * |t| ≤ 1 / 2 := by nlinarith [abs_nonneg t]
  have horig := Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol_ge_origin_sub_slope x
    (by linarith : 0 ≤ b + 3) t
  have ha0 := Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.archSymbol_zero_lower'
  linarith

/-- `Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t ≤ Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t` for every `t : ℝ`. -/
theorem archSymbol_le_shiftedArchSymbol (t : ℝ) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t ≤ Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t := by
  unfold Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier
  have hpos : 0 ≤ 1 / (t ^ 2 + 1 / 4) := by positivity
  linarith

/-- `Cvs.WeilForm.ArithmeticFloorAboveBand.archLower (mesoOuterThreshold x b)` strictly exceeds the outer amplitude cost. -/
theorem archLower_mesoOuterThreshold_gt (x : ℕ) (b : ℝ) :
    (b + 1) + Cvs.WeilForm.MeanFreeSpectralIdentity.totalMeanFreeMaxAmp (x - 1) + (b + 3) <
      Cvs.WeilForm.ArithmeticFloorAboveBand.archLower (mesoOuterThreshold x b) := by
  set C := (b + 1) + Cvs.WeilForm.MeanFreeSpectralIdentity.totalMeanFreeMaxAmp (x - 1) + (b + 3)
  set T := mesoOuterThreshold x b
  have hT : 2 ≤ T := two_le_mesoOuterThreshold x b
  have hlog : Real.log (T / 2) = Real.log Real.pi + (|C| + 30) := by
    have ht : T / 2 = Real.pi * Real.exp (|C| + 30) := by
      dsimp [T, mesoOuterThreshold, C]
      ring
    rw [ht, Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have h57 : 57 / T ≤ 57 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT
  unfold Cvs.WeilForm.ArithmeticFloorAboveBand.archLower
  rw [hlog]
  have hC : C ≤ |C| := le_abs_self C
  linarith

/-- **Unconditional Ultraviolet Coercivity of `augShiftedScaleSymbol`**: for `0 ≤ b` and
`mesoOuterThreshold x b ≤ |t|`, `b + 1 ≤ Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol x (b + 3) t`. -/
theorem augShiftedScaleSymbol_ge_of_mesoOuterThreshold_le {x : ℕ} {b t : ℝ} (hb : 0 ≤ b)
    (ht : mesoOuterThreshold x b ≤ |t|) :
    b + 1 ≤ Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol x (b + 3) t := by
  unfold Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol Cvs.WeilForm.GreenTailCancellation.shiftedAbelScaleSymbol
  have h1 := (Cvs.WeilForm.ArithmeticFloorAboveBand.archLower_le_archSymbol
    (two_le_mesoOuterThreshold x b) ht).trans (archSymbol_le_shiftedArchSymbol t)
  have h2 := (abs_le.mp (Cvs.WeilForm.MeanFreeSpectralIdentity.abs_meanFreeOscSymbol_le_amp (x - 1) t)).2
  have h3 : -(b + 3) ≤ (b + 3) * Real.cos (t * Real.log x) := by
    have h := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (t * Real.log x))
      (by linarith : 0 ≤ b + 3)
    linarith
  have h4 := archLower_mesoOuterThreshold_gt x b
  linarith

/-- Global lower bound `-mesoShellDepth x b ≤ Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol x (b + 3) t` (`0 ≤ b`). -/
theorem neg_mesoShellDepth_le_augShiftedScaleSymbol {x : ℕ} {b : ℝ} (hb : 0 ≤ b) (t : ℝ) :
    -mesoShellDepth x b ≤ Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol x (b + 3) t := by
  unfold mesoShellDepth Cvs.WeilForm.TruncSymbolMonotone.augShiftedScaleSymbol
    Cvs.WeilForm.GreenTailCancellation.shiftedAbelScaleSymbol
  have h1 := Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol_ge t
  have ha0 := Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.archSymbol_zero_lower'
  have h2 := (abs_le.mp (Cvs.WeilForm.MeanFreeSpectralIdentity.abs_meanFreeOscSymbol_le_amp (x - 1) t)).2
  have h3 : -(b + 3) ≤ (b + 3) * Real.cos (t * Real.log x) := by
    have h := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (t * Real.log x))
      (by linarith : 0 ≤ b + 3)
    linarith
  linarith

/-- **Three-Band Punctured Mesoscopic Coercivity on `Dom x`** (`1 ≤ x`, `0 ≤ b`): eliminates both
the origin disk `|t| < originBulkRadius x b` and the high tail `mesoOuterThreshold x b ≤ |t|`. -/
theorem Qx_ge_mesoShell_sub {x : ℕ} (hx : 1 ≤ x) {b : ℝ} (hb : 0 ≤ b)
    (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    (b + 1) * ‖w‖ ^ 2 -
        (b + 1 + mesoShellDepth x b) *
          (∫ t in {t : ℝ | originBulkRadius x b ≤ |t| ∧ |t| < mesoOuterThreshold x b},
            Cvs.WeilForm.EvenBulkVisibility.rho w t) ≤
      Cvs.Route.WindowPositivityBulkCoupling.Qx x w := by
  have h3 := Cvs.WeilForm.TruncSymbolMonotone.Qx_ge_threeBand_of_symbol
    (Cvs.WeilForm.TruncSymbolMonotone.Qx_eq_integral_augShiftedScaleSymbol hx (b + 3) w)
    (Cvs.WeilForm.TruncSymbolMonotone.integrable_augShiftedScaleSymbol_mul_rho hx (b + 3) w)
    (fun t ht => augShiftedScaleSymbol_ge_of_lt_originBulkRadius hb ht)
    (fun t _ _ => neg_mesoShellDepth_le_augShiftedScaleSymbol hb t)
    (fun t ht => augShiftedScaleSymbol_ge_of_mesoOuterThreshold_le hb ht)
  rw [min_self] at h3
  linarith

/-- **Punctured Mesoscopic Floor Theorem on `Dom x`** (`1 ≤ x`, `0 ≤ b`): bounding spectral mass in
`originBulkRadius x b ≤ |t| < mesoOuterThreshold x b` by `mesoShellLeakageCap x b` yields `b ‖w‖² ≤ Qx x w`. -/
theorem Qx_ge_of_mesoShell_cap {x : ℕ} (hx : 1 ≤ x) {b : ℝ} (hb : 0 ≤ b)
    (w : Cvs.Route.L1FloorFromBulkD0.Dom x)
    (hmeso : (∫ t in {t : ℝ | originBulkRadius x b ≤ |t| ∧ |t| < mesoOuterThreshold x b},
        Cvs.WeilForm.EvenBulkVisibility.rho w t) ≤
      mesoShellLeakageCap x b * ‖w‖ ^ 2) :
    b * ‖w‖ ^ 2 ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x w := by
  have hsub := Qx_ge_mesoShell_sub hx hb w
  have hd : 0 < b + 1 + mesoShellDepth x b := by
    have := mesoShellDepth_pos (x := x) hb; linarith
  have hmul := mul_le_mul_of_nonneg_left hmeso hd.le
  have hcap : (b + 1 + mesoShellDepth x b) * (mesoShellLeakageCap x b * ‖w‖ ^ 2) = ‖w‖ ^ 2 := by
    unfold mesoShellLeakageCap
    field_simp [hd.ne']
  linarith

/-- **`EvenBulkFloor` from Punctured Mesoscopic Shell Control Alone** (`1 ≤ x`, `0 ≤ b`):
both `|t| < originBulkRadius x b` and `mesoOuterThreshold x b ≤ |t|` are unconditionally discharged. -/
theorem evenBulkFloor_of_mesoShell_only {x : ℕ} (hx : 1 ≤ x) {b : ℝ} (hb : 0 ≤ b)
    (hmeso : ∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
      (∫ t in {t : ℝ | originBulkRadius x b ≤ |t| ∧ |t| < mesoOuterThreshold x b},
        Cvs.WeilForm.EvenBulkVisibility.rho w t) ≤
      mesoShellLeakageCap x b * ‖w‖ ^ 2) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b :=
  fun w hwE hwO => Qx_ge_of_mesoShell_cap hx hb w (hmeso w hwE hwO)

/-- **Connes Route Criterion from Punctured Mesoscopic Shell Control + `EvenFormCoupling`**: excises
both the infrared origin neighborhood and the ultraviolet bulk unconditionally. -/
theorem riemannHypothesis_of_connes_mesoShell_only
    (h : ∃ᶠ x : ℕ in atTop, ∃ b δ : ℝ, 0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧
      (∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
        (∫ t in {t : ℝ | originBulkRadius x b ≤ |t| ∧ |t| < mesoOuterThreshold x b},
          Cvs.WeilForm.EvenBulkVisibility.rho w t) ≤
        mesoShellLeakageCap x b * ‖w‖ ^ 2) ∧
      Cvs.Route.EvenWindowBulkCoupling.EvenFormCoupling x δ) :
    RiemannHypothesis := by
  refine Cvs.Route.EvenWindowBulkCoupling.riemannHypothesis_of_even_floor_pos_coupling
    ((h.and_eventually (eventually_ge_atTop 1)).mono fun x ⟨⟨b, δ, hb, hδ0, hδ1, hm, hc⟩, hx⟩ =>
      ⟨b, δ, hb, hδ0, hδ1, evenBulkFloor_of_mesoShell_only hx hb.le hm, hc⟩)

/-! ### Part 9B: Green-Channel Diagonalization and Logarithmic Cushion on `ModeBox M₀` -/

/-- On `evenModeSub (negBox M₀)`, the intermediate boundary tail difference `k = 1, 2, 3` is nonnegative. -/
theorem boxTailMatrix_sub_tailFrom_four_nonneg {L : ℝ} (hL : 0 < L) (M₀ : ℕ)
    {η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ}
    (hη : η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀)) :
    0 ≤ η ⬝ᵥ (Cvs.Route.ModeBoxShiftedArchGreen.boxTailMatrix L M₀ *ᵥ η) -
      η ⬝ᵥ (Cvs.Route.ModeBoxGreenLaplace.boxTailMatrixFrom 4 L M₀ *ᵥ η) := by
  let ω : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ :=
    fun m => 2 * Real.pi * (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m : ℝ) / L
  have heq : η ⬝ᵥ (Cvs.Route.ModeBoxShiftedArchGreen.boxTailMatrix L M₀ *ᵥ η) -
      η ⬝ᵥ (Cvs.Route.ModeBoxGreenLaplace.boxTailMatrixFrom 4 L M₀ *ᵥ η) =
      (∑ k ∈ Finset.Ico 1 4, ∑ i : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
        ∑ j : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
          η i * η j * Cvs.WeilForm.ArchGreenSecondChannel.atom L k (ω i) (ω j)) / L := by
    have hsplit : ∀ i j : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
        Cvs.Route.ModeBoxShiftedArchGreen.boxTailMatrix L M₀ i j -
          Cvs.Route.ModeBoxGreenLaplace.boxTailMatrixFrom 4 L M₀ i j =
        (∑ k ∈ Finset.Ico 1 4, Cvs.WeilForm.ArchGreenSecondChannel.atom L k (ω i) (ω j)) / L := by
      intro i j
      dsimp [Cvs.Route.ModeBoxShiftedArchGreen.boxTailMatrix, Cvs.Route.ModeBoxGreenLaplace.boxTailMatrixFrom, ω]
      rw [Cvs.Route.ModeBoxGreenLaplace.boundaryTail_eq_sum_Ico_add_boundaryTailFrom hL 4 (by omega),
        add_div]
      ring
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have h1 : (∑ i : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
        ∑ j : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
          (η i * (Cvs.Route.ModeBoxShiftedArchGreen.boxTailMatrix L M₀ i j * η j) -
            η i * (Cvs.Route.ModeBoxGreenLaplace.boxTailMatrixFrom 4 L M₀ i j * η j))) =
        ∑ i : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
          ∑ j : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
            (∑ k ∈ Finset.Ico 1 4, η i * η j *
              Cvs.WeilForm.ArchGreenSecondChannel.atom L k (ω i) (ω j)) / L := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hsub : η i * (Cvs.Route.ModeBoxShiftedArchGreen.boxTailMatrix L M₀ i j * η j) -
          η i * (Cvs.Route.ModeBoxGreenLaplace.boxTailMatrixFrom 4 L M₀ i j * η j) =
          (η i * η j) * (Cvs.Route.ModeBoxShiftedArchGreen.boxTailMatrix L M₀ i j -
            Cvs.Route.ModeBoxGreenLaplace.boxTailMatrixFrom 4 L M₀ i j) := by ring
      rw [hsub, hsplit i j, mul_div_assoc', Finset.mul_sum]
    rw [h1]
    simp only [← Finset.sum_div]
    congr 1
    calc ∑ i : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
          ∑ j : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
            ∑ k ∈ Finset.Ico 1 4, η i * η j * Cvs.WeilForm.ArchGreenSecondChannel.atom L k (ω i) (ω j)
        = ∑ i : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
            ∑ k ∈ Finset.Ico 1 4,
              ∑ j : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
                η i * η j * Cvs.WeilForm.ArchGreenSecondChannel.atom L k (ω i) (ω j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k ∈ Finset.Ico 1 4,
            ∑ i : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
              ∑ j : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
                η i * η j * Cvs.WeilForm.ArchGreenSecondChannel.atom L k (ω i) (ω j) :=
          Finset.sum_comm
  rw [heq]
  refine div_nonneg (Finset.sum_nonneg fun k _ => ?_) hL.le
  dsimp only [Cvs.WeilForm.ArchGreenSecondChannel.atom]
  rw [Cvs.Finite.WindowMatrixSymbolKernel.rank2_quad,
    Cvs.Route.ModeBoxShiftedArchGreen.box_sum_even_mul_vv_eq_zero L (Cvs.Finite.WindowMatrixSymbolKernel.bk k) hη]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  exact mul_nonneg (Cvs.WeilForm.EvenBoundaryKernelBound.weight_nonneg hL k) (sq_nonneg _)

/-- **Diagonal Upper Bound on the Three Intermediate Green Channels**: on `evenModeSub (negBox M₀)`,
`∑_{k=1}^3 ηᵀ G_k η ≤ boxResidualLevyDiagQ L M₀ η`. -/
theorem sum_Ico_boxGreenChannelMatrix_quad_le_residualLevyDiagQ {L : ℝ} (hL : 0 < L) (M₀ : ℕ)
    {η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ}
    (hη : η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀)) :
    (∑ k ∈ Finset.Ico 1 4,
        η ⬝ᵥ (Cvs.Route.ModeBoxGreenLaplace.boxGreenChannelMatrix L k M₀ *ᵥ η)) ≤
      Cvs.Route.ModeBoxFourChannelLevy.boxResidualLevyDiagQ L M₀ η := by
  linarith [Cvs.Route.ModeBoxGreenLaplace.sum_Ico_boxGreenChannelMatrix_quad_eq hL M₀ η,
    boxTailMatrix_sub_tailFrom_four_nonneg hL M₀ hη]

/-- Pointwise peak bound `2 * uu (bk k) t ≤ 1 / (k + 1 / 4)` for every Lévy channel `k`. -/
theorem two_mul_uu_bk_le_inv (k : ℕ) (t : ℝ) :
    2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t ≤ 1 / ((k : ℝ) + 1 / 4) := by
  have hb : 0 < Cvs.Finite.WindowMatrixSymbolKernel.bk k := Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k
  have huu : Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t ≤
      Cvs.Finite.WindowMatrixSymbolKernel.bk k / (Cvs.Finite.WindowMatrixSymbolKernel.bk k) ^ 2 := by
    unfold Cvs.Finite.WindowMatrixSymbolKernel.uu
    exact div_le_div_of_nonneg_left hb.le (sq_pos_of_pos hb) (by nlinarith [sq_nonneg t])
  have h0 : 2 * (Cvs.Finite.WindowMatrixSymbolKernel.bk k / (Cvs.Finite.WindowMatrixSymbolKernel.bk k) ^ 2) =
      1 / ((k : ℝ) + 1 / 4) := by
    unfold Cvs.Finite.WindowMatrixSymbolKernel.bk
    have h1 : (2 * (k : ℝ) + 1 / 2) ≠ 0 := hb.ne'
    have h2 : ((k : ℝ) + 1 / 4) ≠ 0 := by positivity
    field_simp
    ring
  linarith

/-- Global lower bound `-coreDeficit ≤ truncConst 4 - ∑_{k=1}^3 2 uu(b_k, t)`. -/
theorem truncConst_four_sub_sum_Ico_uu_ge_neg_coreDeficit (t : ℝ) :
    -Cvs.WeilForm.LowHeadSignedCorrection.coreDeficit ≤
      Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 -
        ∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t := by
  have hsum : ∑ k ∈ Finset.Ico (1 : ℕ) 4,
      2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t ≤
      ∑ k ∈ Finset.Ico (1 : ℕ) 4, (1 / ((k : ℝ) + 1 / 4)) :=
    Finset.sum_le_sum fun k _ => two_mul_uu_bk_le_inv k t
  have htc : Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 =
      Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + 4 +
        ∑ k ∈ Finset.Ico (1 : ℕ) 4, (1 / ((k : ℝ) + 1 / 4)) := by
    unfold Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst
    have hsp := Finset.sum_range_add_sum_Ico
      (fun k : ℕ => 1 / ((k : ℝ) + 1 / 4)) (by omega : 1 ≤ 4)
    have h0 : ∑ k ∈ Finset.range (1 : ℕ), (1 / ((k : ℝ) + 1 / 4)) = 4 := by norm_num
    linarith
  unfold Cvs.WeilForm.LowHeadSignedCorrection.coreDeficit
  linarith

/-- Pointwise piecewise lower bound on `truncConst 4 - ∑_{k=1}^3 2 uu(b_k, t)` across all `t : ℝ`. -/
theorem truncConst_four_sub_sum_Ico_uu_ge_piecewise (t : ℝ) :
    -Cvs.WeilForm.LowHeadSignedCorrection.coreDeficit *
        (if |t| < Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolPosThreshold then 1 else 0) +
      (Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 / 2) *
        (if Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolHalfFloorThreshold ≤ |t| then 1 else 0) ≤
      Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 -
        ∑ k ∈ Finset.Ico 1 4, 2 * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) t := by
  by_cases h1 : |t| < Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolPosThreshold
  · have h2 : ¬ Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolHalfFloorThreshold ≤ |t| :=
      not_le_of_gt (lt_of_lt_of_le h1
        Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolPosThreshold_le_halfFloorThreshold)
    rw [ite_eq_left h1, ite_eq_right h2]
    linarith [truncConst_four_sub_sum_Ico_uu_ge_neg_coreDeficit t]
  · rw [ite_eq_right h1]
    have hge1 : Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolPosThreshold ≤ |t| := le_of_not_gt h1
    have hpos1 := Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolPosThreshold_pos
    have ht0 : t ≠ 0 := abs_pos.mp (lt_of_lt_of_le hpos1 hge1)
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
    have hc : 0 < Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 := Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst_four_pos
    have huu := Cvs.Route.ShiftedSymbolPositivity.sum_Ico_two_mul_uu_le_twenty_seven_div_sq ht0
    by_cases h2 : Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolHalfFloorThreshold ≤ |t|
    · rw [ite_eq_left h2]
      have hpos2 := Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolHalfFloorThreshold_pos
      have hsq : Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolHalfFloorThreshold ^ 2 ≤ t ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ hpos2.le h2 2
      rw [Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolHalfFloorThreshold_sq] at hsq
      have hdiv : 27 / t ^ 2 ≤ Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 / 2 := by
        rw [div_le_iff₀ ht2]
        have hmul := (div_le_iff₀ hc).mp hsq
        linarith
      linarith
    · rw [ite_eq_right h2]
      have hsq : Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolPosThreshold ^ 2 ≤ t ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ hpos1.le hge1 2
      rw [Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolPosThreshold_sq] at hsq
      have hdiv : 27 / t ^ 2 ≤ Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 := by
        rw [div_le_iff₀ ht2]
        have hmul := (div_le_iff₀ hc).mp hsq
        linarith
      linarith

/-- Quadratic lower bound on `truncConst 4 * (η ⬝ᵥ η) - boxResidualLevyDiagQ L M₀ η`. -/
theorem truncConst_four_sub_residualLevyDiagQ_ge_core_and_high (L : ℝ) (M₀ : ℕ)
    (η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ) :
    -Cvs.WeilForm.LowHeadSignedCorrection.coreDeficit *
        Cvs.Route.ShiftedSymbolPositivity.boxUniversalCoreEnergy L M₀ η +
      (Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 / 2) *
        Cvs.Route.ShiftedSymbolPositivity.boxUniversalHighEnergy L M₀ η ≤
      Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 * (η ⬝ᵥ η) -
        Cvs.Route.ModeBoxFourChannelLevy.boxResidualLevyDiagQ L M₀ η := by
  unfold Cvs.Route.ShiftedSymbolPositivity.boxUniversalCoreEnergy
    Cvs.Route.ShiftedSymbolPositivity.boxUniversalHighEnergy Cvs.Route.ModeBoxFourChannelLevy.boxResidualLevyDiagQ
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  have h := mul_le_mul_of_nonneg_right
    (truncConst_four_sub_sum_Ico_uu_ge_piecewise
      (2 * Real.pi * (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m : ℝ) / L))
    (sq_nonneg (η m))
  split_ifs at h ⊢ <;> nlinarith [sq (η m)]

/-- **Diagonalized Four-Channel Log-Cushion Lower Bound on `boxFourChannelLogMinorant`**: eliminates
all three Green matrices while retaining both `boxUniversalHighEnergy` and `boxLogGainQ 4`. -/
theorem boxFourChannelLogMinorant_quad_ge_core_high_logGain_sub_pureCurvature
    {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ)
    {η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ}
    (hη : η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀)) :
    -Cvs.WeilForm.LowHeadSignedCorrection.coreDeficit *
        Cvs.Route.ShiftedSymbolPositivity.boxUniversalCoreEnergy L M₀ η +
      (Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 / 2) *
        Cvs.Route.ShiftedSymbolPositivity.boxUniversalHighEnergy L M₀ η +
      Cvs.Route.ModeBoxLogMinorant.boxLogGainQ 4 L M₀ η -
      (2 * (Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R L - Cvs.WeilForm.PrimeMomentVolterra.meanRamp L) / L) *
        (Cvs.Route.ModeBoxRightInverse.boxEndpoint M₀ η) ^ 2 -
      η ⬝ᵥ (Cvs.Route.ModeBoxPureCurvature.boxPureCurvatureMatrix L M₀
        (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t - Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) *ᵥ η) ≤
      η ⬝ᵥ (Cvs.Route.ModeBoxLogMinorant.boxFourChannelLogMinorant P R L M₀ *ᵥ η) := by
  rw [Cvs.Route.ModeBoxLogMinorant.boxFourChannelLogMinorant_quad_eq P R L M₀ η,
    Cvs.Route.ModeBoxVolterraCurvature.boxDiscrepancyMatrix_quad_eq_endpoint_add_curvature P R L M₀ η,
    Cvs.Route.ModeBoxVolterraCurvature.discrepancyEntry_zero_zero hL P R,
    Cvs.Route.ModeBoxPureCurvature.boxCurvatureDiscrepancyMatrix_quad_eq_pureCurvature hL P R M₀ hη]
  have hgreen := sum_Ico_boxGreenChannelMatrix_quad_le_residualLevyDiagQ hL M₀ hη
  have hdiag := truncConst_four_sub_residualLevyDiagQ_ge_core_and_high L M₀ η
  linarith

/-- **Diagonalized Four-Channel Log-Cushion Lower Bound on `Cvs.Finite.TruncationQuadraticForm.M` on `ModeBox M₀`**. -/
theorem boxM_quad_ge_core_high_logGain_sub_pureCurvature
    {L : ℝ} (hL : 0 < L) (P R M₀ : ℕ)
    {η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ}
    (hη : η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀)) :
    -Cvs.WeilForm.LowHeadSignedCorrection.coreDeficit *
        Cvs.Route.ShiftedSymbolPositivity.boxUniversalCoreEnergy L M₀ η +
      (Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 / 2) *
        Cvs.Route.ShiftedSymbolPositivity.boxUniversalHighEnergy L M₀ η +
      Cvs.Route.ModeBoxLogMinorant.boxLogGainQ 4 L M₀ η -
      (2 * (Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R L - Cvs.WeilForm.PrimeMomentVolterra.meanRamp L) / L) *
        (Cvs.Route.ModeBoxRightInverse.boxEndpoint M₀ η) ^ 2 -
      η ⬝ᵥ (Cvs.Route.ModeBoxPureCurvature.boxPureCurvatureMatrix L M₀
        (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t - Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) *ᵥ η) ≤
      η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ η) :=
  (boxFourChannelLogMinorant_quad_ge_core_high_logGain_sub_pureCurvature hL P R M₀ hη).trans
    (Cvs.Route.ModeBoxLogMinorant.boxFourChannelLogMinorant_le_boxM hL P R M₀ hη)

/-- **3-Cut Universal-Core + Logarithmic-Gain + Pure-Curvature Criterion for `RiemannHypothesis`**:
restricts `-coreDeficit` to the `O(log x)` core modes while keeping `boxLogGainQ 4`. -/
theorem riemannHypothesis_of_cheb_universalCore_logGain_pureCurvature
    (h : ∃ᶠ x : ℕ in atTop, ∃ (ε : ℝ) (M₀ : ℕ),
      0 < ε ∧
      Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) (chebDampedThreshold x ε) ≤ M₀ + 1 ∧
      ∀ η ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀),
        (2 * (Cvs.WeilForm.PrimeMomentVolterra.primeRamp x (Nat.clog 2 x) (Real.log x) -
            Cvs.WeilForm.PrimeMomentVolterra.meanRamp (Real.log x)) / Real.log x) *
          (Cvs.Route.ModeBoxRightInverse.boxEndpoint M₀ η) ^ 2 +
        η ⬝ᵥ (Cvs.Route.ModeBoxPureCurvature.boxPureCurvatureMatrix (Real.log x) M₀
          (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp x (Nat.clog 2 x) t -
            Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) *ᵥ η) ≤
        -Cvs.WeilForm.LowHeadSignedCorrection.coreDeficit *
          Cvs.Route.ShiftedSymbolPositivity.boxUniversalCoreEnergy (Real.log x) M₀ η +
        (Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 / 2) *
          Cvs.Route.ShiftedSymbolPositivity.boxUniversalHighEnergy (Real.log x) M₀ η +
        Cvs.Route.ModeBoxLogMinorant.boxLogGainQ 4 (Real.log x) M₀ η -
        ε * boxChebLowBulkEnergy x M₀ η) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_lowBulk_fourChannelMinorant
    ((h.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨⟨ε, M₀, hε, hK, hcurv⟩, hx2⟩ => ?_)
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
  refine ⟨ε, M₀, hε, hK, fun η hη => ?_⟩
  have h1 := hcurv η hη
  have h2 := boxFourChannelLogMinorant_quad_ge_core_high_logGain_sub_pureCurvature
    hL x (Nat.clog 2 x) M₀ hη
  linarith

/-! ### Part 9C: Finite Low-Rung Excision (`boxEvenBasisVec` + `boxOnesVec`) and Pure-Curvature Slot -/

/-- **`ε`-Floor Matrix Slot Theorem**: a minorant `A ≤ Q` with `ε`-slack on `R` and `Bulk E R` yields
`ε * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ (Q *ᵥ ξ)` on `E` (since `ε • 1` drops out of off-diagonal coupling `r ⬝ᵥ (Q *ᵥ w)`). -/
theorem eps_floor_of_slot {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q A : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    {E R : Submodule ℝ (ι → ℝ)} (hRE : R ≤ E) {ε : ℝ} {κ : (ι → ℝ) → ℝ}
    (hfloor : ∀ w, Cvs.Route.EvenMatrixSlotPoleRestored.Bulk E R w → ε * (w ⬝ᵥ w) ≤ w ⬝ᵥ (A *ᵥ w))
    (hcomp : ∀ w, Cvs.Route.EvenMatrixSlotPoleRestored.Bulk E R w → w ⬝ᵥ (A *ᵥ w) ≤ w ⬝ᵥ (Q *ᵥ w))
    (hchan : ∀ r ∈ R, ∀ w, Cvs.Route.EvenMatrixSlotPoleRestored.Bulk E R w →
      (r ⬝ᵥ (Q *ᵥ w)) ^ 2 ≤ κ r * (w ⬝ᵥ (A *ᵥ w) - ε * (w ⬝ᵥ w)))
    (hκ0 : ∀ r ∈ R, 0 ≤ κ r)
    (hκ : ∀ r ∈ R, κ r + ε * (r ⬝ᵥ r) ≤ r ⬝ᵥ (Q *ᵥ r)) :
    ∀ ξ ∈ E, ε * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ (Q *ᵥ ξ) := by
  let Q' : Matrix ι ι ℝ := Q - ε • 1
  let A' : Matrix ι ι ℝ := A - ε • 1
  have hsh : ∀ (B : Matrix ι ι ℝ) (u v : ι → ℝ),
      u ⬝ᵥ ((B - ε • (1 : Matrix ι ι ℝ)) *ᵥ v) = u ⬝ᵥ (B *ᵥ v) - ε * (u ⬝ᵥ v) := by
    intro B u v
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hQ' : Q'.IsSymm := Matrix.IsSymm.ext fun i j => by
    simp only [Q', Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hQ.apply i j, eq_comm]
  have hnn := Cvs.Route.EvenMatrixSlotPoleRestored.nonneg_of_slot (Q := Q') (A := A') hQ' hRE (κ := κ)
    (fun w hw => by rw [hsh]; linarith [hfloor w hw])
    (fun w hw => by rw [hsh, hsh]; linarith [hcomp w hw])
    (fun r hr w hw => by rw [hsh, hw.2 r hr, mul_zero, sub_zero, hsh]; exact hchan r hr w hw)
    hκ0
    (fun r hr => by rw [hsh]; linarith [hκ r hr])
  intro ξ hξ
  have h1 := hnn ξ hξ
  rw [hsh] at h1
  linarith

/-- Symmetrized basis vector `e_m + e_{-m}` on `ModeBox M₀` for excising individual low modes. -/
def boxEvenBasisVec (M₀ : ℕ) (m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀) :
    Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ :=
  fun j => (if j = m then 1 else 0) + (if j = Cvs.Route.ModeBoxIsometricTransfer.negBox M₀ m then 1 else 0)

/-- `boxEvenBasisVec M₀ m` belongs to `evenModeSub (negBox M₀)`. -/
theorem boxEvenBasisVec_mem_evenModeSub (M₀ : ℕ) (m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀) :
    boxEvenBasisVec M₀ m ∈
      Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀) := by
  intro j
  dsimp [boxEvenBasisVec]
  have h1 : (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀ j = m) ↔ (j = Cvs.Route.ModeBoxIsometricTransfer.negBox M₀ m) :=
    ⟨fun h => by rw [← h, Cvs.Route.ModeBoxIsometricTransfer.negBox_involutive M₀ j],
     fun h => by rw [h, Cvs.Route.ModeBoxIsometricTransfer.negBox_involutive M₀ m]⟩
  have h2 : (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀ j = Cvs.Route.ModeBoxIsometricTransfer.negBox M₀ m) ↔ (j = m) :=
    (Cvs.Route.ModeBoxIsometricTransfer.negBox_involutive M₀).injective.eq_iff
  simp only [h1, h2]
  ring

/-- Dot product of `boxEvenBasisVec M₀ m` with any even vector `w` equals `2 * w m`. -/
theorem dotProduct_boxEvenBasisVec_of_even {M₀ : ℕ}
    {w : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ}
    (hw : w ∈ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀))
    (m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀) :
    boxEvenBasisVec M₀ m ⬝ᵥ w = 2 * w m := by
  simp only [dotProduct, boxEvenBasisVec, add_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hw m]
  ring

/-- Any bulk vector `w` against a rung `Rg` containing `boxEvenBasisVec M₀ m` vanishes at `m`. -/
theorem apply_eq_zero_of_boxEvenBasisVec_mem_rung {M₀ : ℕ}
    {Rg : Submodule ℝ (Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ)}
    {w : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ}
    (hw : Cvs.Route.EvenMatrixSlotPoleRestored.Bulk
      (Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀)) Rg w)
    {m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀}
    (hm : boxEvenBasisVec M₀ m ∈ Rg) :
    w m = 0 := by
  have h0 := hw.2 (boxEvenBasisVec M₀ m) hm
  rw [dotProduct_boxEvenBasisVec_of_even hw.1 m] at h0
  linarith

/-- Radial monotonicity of `Cvs.WeilForm.ChannelModeSumEnclosure.phi` in frequency magnitude: `|s| ≤ |t|` implies `phi s a ≤ phi t a`. -/
theorem phi_mono_abs {a s t : ℝ} (ha : 0 < a) (h : |s| ≤ |t|) :
    Cvs.WeilForm.ChannelModeSumEnclosure.phi s a ≤ Cvs.WeilForm.ChannelModeSumEnclosure.phi t a := by
  unfold Cvs.WeilForm.ChannelModeSumEnclosure.phi
  have hsq : s ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs s, ← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg s) h 2
  have hlog : Real.log (a ^ 2 + (s / 2) ^ 2) ≤ Real.log (a ^ 2 + (t / 2) ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  linarith

/-- `boxChebLowBulkEnergy x M₀ η` is bounded above by the full box norm `η ⬝ᵥ η`. -/
theorem boxChebLowBulkEnergy_le_dotProduct (x M₀ : ℕ)
    (η : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ) :
    boxChebLowBulkEnergy x M₀ η ≤ η ⬝ᵥ η := by
  unfold boxChebLowBulkEnergy
  simp only [dotProduct]
  refine (Finset.sum_le_univ_sum_of_nonneg fun m => sq_nonneg (η m)).trans ?_
  exact Finset.sum_le_sum fun m _ => le_of_eq (sq (η m))

/-- **Complete Core + Endpoint + Green Elimination on the Low-Rung Bulk**: if `Rg` contains
`boxOnesVec M₀` and `boxEvenBasisVec M₀ m` for `|ω_m| < T_core` (`shiftedSymbolHalfFloorThreshold ≤ T_core`),
only the positive log-cushion minus `boxPureCurvatureMatrix` remains! -/
theorem boxFourChannelLogMinorant_quad_ge_logCushion_sub_pureCurvature_of_bulk
    {L T_core : ℝ} (hL : 0 < L)
    (hTc : Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolHalfFloorThreshold ≤ T_core)
    (P R M₀ : ℕ) {Rg : Submodule ℝ (Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ)}
    (h1 : Cvs.Route.ModeBoxLogSlotConnesRung.boxOnesVec M₀ ∈ Rg)
    (hcore : ∀ m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
      |2 * Real.pi * (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m : ℝ) / L| < T_core →
      boxEvenBasisVec M₀ m ∈ Rg)
    {w : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ}
    (hw : Cvs.Route.EvenMatrixSlotPoleRestored.Bulk
      (Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀)) Rg w) :
    (Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 / 2 +
        Cvs.WeilForm.ChannelModeSumEnclosure.phi T_core (17 / 4)) * (w ⬝ᵥ w) -
      w ⬝ᵥ (Cvs.Route.ModeBoxPureCurvature.boxPureCurvatureMatrix L M₀
        (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t - Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) *ᵥ w) ≤
      w ⬝ᵥ (Cvs.Route.ModeBoxLogMinorant.boxFourChannelLogMinorant P R L M₀ *ᵥ w) := by
  have hend : Cvs.Route.ModeBoxRightInverse.boxEndpoint M₀ w = 0 :=
    Cvs.Route.ModeBoxLogSlotConnesRung.boxEndpoint_eq_zero_of_bulk_of_boxOnesVec_mem h1 hw
  have hvan : ∀ m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
      |2 * Real.pi * (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m : ℝ) / L| < T_core → w m = 0 :=
    fun m hm => apply_eq_zero_of_boxEvenBasisVec_mem_rung hw (hcore m hm)
  have hce : Cvs.Route.ShiftedSymbolPositivity.boxUniversalCoreEnergy L M₀ w = 0 := by
    unfold Cvs.Route.ShiftedSymbolPositivity.boxUniversalCoreEnergy
    refine Finset.sum_eq_zero fun m _ => ?_
    split_ifs with hm
    · have hlt : |2 * Real.pi * (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m : ℝ) / L| < T_core :=
        lt_of_lt_of_le hm
          (Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolPosThreshold_le_halfFloorThreshold.trans hTc)
      rw [hvan m hlt, sq, zero_mul]
    · rfl
  have hhe : Cvs.Route.ShiftedSymbolPositivity.boxUniversalHighEnergy L M₀ w = w ⬝ᵥ w := by
    unfold Cvs.Route.ShiftedSymbolPositivity.boxUniversalHighEnergy
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · exact sq (w m)
    · have hlt : |2 * Real.pi * (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m : ℝ) / L| < T_core :=
        lt_of_lt_of_le (not_le.mp hm) hTc
      rw [hvan m hlt, zero_mul]
  have hTc0 : 0 ≤ T_core :=
    Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolHalfFloorThreshold_pos.le.trans hTc
  have hlg : Cvs.WeilForm.ChannelModeSumEnclosure.phi T_core (17 / 4) * (w ⬝ᵥ w) ≤
      Cvs.Route.ModeBoxLogMinorant.boxLogGainQ 4 L M₀ w := by
    unfold Cvs.Route.ModeBoxLogMinorant.boxLogGainQ
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    by_cases hm : |2 * Real.pi * (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m : ℝ) / L| < T_core
    · rw [hvan m hm]; ring_nf; exact le_rfl
    · have hge : |T_core| ≤ |2 * Real.pi * (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m : ℝ) / L| := by
        rw [abs_of_nonneg hTc0]; exact not_lt.mp hm
      have hp := phi_mono_abs (by norm_num : (0 : ℝ) < 17 / 4) hge
      have h17 : ((4 : ℕ) : ℝ) + 1 / 4 = 17 / 4 := by norm_num
      rw [h17, ← sq]
      exact mul_le_mul_of_nonneg_right hp (sq_nonneg (w m))
  have hbase := boxFourChannelLogMinorant_quad_ge_core_high_logGain_sub_pureCurvature
    hL P R M₀ hw.1
  rw [hend, hce, hhe] at hbase
  linarith

/-- **`∀ N`-Free Low-Rung Pure-Curvature Slot Criterion for `RiemannHypothesis`**: once `Rg`
excises `boxOnesVec` and `|ω_m| < T_core`, only pure Volterra curvature and finite `Rg` coupling remain. -/
theorem riemannHypothesis_of_lowRung_pureCurvature_slot
    (h : ∃ᶠ x : ℕ in atTop, ∃ (ε T_core : ℝ) (M₀ : ℕ)
      (Rg : Submodule ℝ (Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ))
      (κ : (Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀ → ℝ) → ℝ),
      0 < ε ∧
      Cvs.Route.ShiftedSymbolPositivity.shiftedSymbolHalfFloorThreshold ≤ T_core ∧
      Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder (Real.log x) (chebDampedThreshold x ε) ≤ M₀ + 1 ∧
      Rg ≤ Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀) ∧
      Cvs.Route.ModeBoxLogSlotConnesRung.boxOnesVec M₀ ∈ Rg ∧
      (∀ m : Cvs.Route.ModeBoxIsometricTransfer.ModeBox M₀,
        |2 * Real.pi * (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀ m : ℝ) / Real.log x| < T_core →
        boxEvenBasisVec M₀ m ∈ Rg) ∧
      (∀ w, Cvs.Route.EvenMatrixSlotPoleRestored.Bulk
        (Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀)) Rg w →
        w ⬝ᵥ (Cvs.Route.ModeBoxPureCurvature.boxPureCurvatureMatrix (Real.log x) M₀
          (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp x (Nat.clog 2 x) t -
            Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) *ᵥ w) ≤
          (Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 4 / 2 +
            Cvs.WeilForm.ChannelModeSumEnclosure.phi T_core (17 / 4) - ε) * (w ⬝ᵥ w)) ∧
      (∀ r ∈ Rg, ∀ w, Cvs.Route.EvenMatrixSlotPoleRestored.Bulk
        (Cvs.Route.EvenMatrixSlotPoleRestored.evenModeSub (Cvs.Route.ModeBoxIsometricTransfer.negBox M₀)) Rg w →
        (r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x)
          (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ w)) ^ 2 ≤
          κ r * (w ⬝ᵥ (Cvs.Route.ModeBoxLogMinorant.boxFourChannelLogMinorant
            x (Nat.clog 2 x) (Real.log x) M₀ *ᵥ w) - ε * (w ⬝ᵥ w))) ∧
      (∀ r ∈ Rg, 0 ≤ κ r ∧ κ r + ε * (r ⬝ᵥ r) ≤
        r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x)
          (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀) *ᵥ r))) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_modeBox_cheb_lowBulk
    ((h.and_eventually (eventually_ge_atTop 2)).mono
      fun x ⟨⟨ε, T_core, M₀, Rg, κ, hε, hTc, hK, hRE, h1, hcore, hcurv, hchan, hκ⟩, hx2⟩ => ?_)
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
  refine ⟨ε, M₀, hε, hK, fun η hη => ?_⟩
  have hle : ε * boxChebLowBulkEnergy x M₀ η ≤ ε * (η ⬝ᵥ η) :=
    mul_le_mul_of_nonneg_left (boxChebLowBulkEnergy_le_dotProduct x M₀ η) hε.le
  refine hle.trans (eps_floor_of_slot
    (Cvs.Route.ModeBoxLogSlotConnesRung.M_mode_isSymm x (Nat.clog 2 x) (Real.log x)
      (Cvs.Route.ModeBoxIsometricTransfer.boxMode M₀))
    hRE
    (fun w hw => ?_)
    (fun w hw => Cvs.Route.ModeBoxLogMinorant.boxFourChannelLogMinorant_le_boxM
      hL x (Nat.clog 2 x) M₀ hw.1)
    hchan
    (fun r hr => (hκ r hr).1)
    (fun r hr => (hκ r hr).2)
    η hη)
  have hmin := boxFourChannelLogMinorant_quad_ge_logCushion_sub_pureCurvature_of_bulk
    hL hTc x (Nat.clog 2 x) M₀ h1 hcore hw
  have hc := hcurv w hw
  linarith

end Cvs.Route.SpectralChainThreeCut
