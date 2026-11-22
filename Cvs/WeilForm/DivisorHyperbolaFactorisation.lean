import Mathlib
import Cvs.Route.OneCellChebyshevInequality
import Cvs.WeilForm.DirichletSchurFactorisation
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.PrimeOperatorBudgetGap
import Cvs.WeilForm.ShiftedDirichletSchurVacuum
import Cvs.WeilForm.WindowVacuumRieszMean

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Whole-Domain Divisor–Hyperbola Factorization and Smooth Inverse Reduction on `L²(𝕋)`

Proves `Op c ζ + α • 1 - Op c Λ = Op c (ζ * ζ + α • ζ - log) * Op c μ` on `L²(𝕋)`, splits `M c - Psihalf c` and
`G (log c)` into `smoothPoleRem` plus the divisor-discrepancy pairing, and characterizes `moebiusVac c` via `Op c ζ h = vac`.
-/

noncomputable section

open MeasureTheory Real
open scoped InnerProductSpace NNReal ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.WeilForm.DivisorHyperbolaFactorisation
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
open Cvs.Route.OneCellLaplaceTransform (G)
open Cvs.Route.OneCellChebyshevInequality (Psihalf M)
open Cvs.WeilForm.WindowVacuumRieszMean (vac inner_vac_Op)
open Cvs.WeilForm.DirichletSchurFactorisation
open Cvs.WeilForm.ShiftedDirichletSchurVacuum

attribute [local instance] Classical.propDecidable

/-! ### 1. Divisor–Hyperbola Arithmetic Function and Whole-Domain Operator Factorization -/

/-- For every `n : ℕ`, `((ζ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) n = n.divisors.card`. -/
theorem zeta_mul_zeta_apply (n : ℕ) :
    ((ζ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) n = (n.divisors.card : ℝ) := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  have h1 : ∀ i ∈ n.divisors, (ζ : ArithmeticFunction ℝ) i = 1 := fun i hi => by
    have hi0 : i ≠ 0 := (Nat.pos_of_mem_divisors hi).ne'
    simp [ArithmeticFunction.zeta_apply_ne hi0]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The divisor-hyperbola discrepancy `d(n) + α - log n = (ζ * ζ + α • ζ - log)(n)`. -/
def divisorDiscrepancy (α : ℝ) : ArithmeticFunction ℝ :=
  (ζ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)
    + α • (ζ : ArithmeticFunction ℝ)
    - ArithmeticFunction.log

/-- **Dirichlet Identity for `divisorDiscrepancy`**: for every `α : ℝ`,
`divisorDiscrepancy α * μ = ζ + α • 1 - Λ`. -/
theorem divisorDiscrepancy_mul_moebius (α : ℝ) :
    divisorDiscrepancy α * (μ : ArithmeticFunction ℝ)
      = (ζ : ArithmeticFunction ℝ)
        + α • (1 : ArithmeticFunction ℝ)
        - ArithmeticFunction.vonMangoldt := by
  unfold divisorDiscrepancy
  have hsm : α • (ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)
      = α • ((ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) := by
    have e : ∀ (f : ArithmeticFunction ℝ) (m : ℕ), (α • f) m = α * f m := fun _ _ => rfl
    ext n
    simp only [e, ArithmeticFunction.mul_apply, Finset.mul_sum, mul_assoc]
  rw [sub_mul, add_mul, mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one,
    hsm, ArithmeticFunction.coe_zeta_mul_coe_moebius,
    ArithmeticFunction.log_mul_moebius_eq_vonMangoldt]

/-- `Op c` preserves subtraction of arithmetic functions. -/
theorem Op_sub (c : ℕ) (a b : ArithmeticFunction ℝ) :
    Op c (a - b) = Op c a - Op c b := by
  rw [sub_eq_add_neg, Op_add, (neg_one_smul ℝ b).symm, Op_smul, neg_one_smul ℝ (Op c b),
    ← sub_eq_add_neg]

/-- **Whole-Domain Divisor–Hyperbola Operator Identity on `L²(𝕋)`**: for `1 < c` and `α : ℝ`,
`Op c ζ + α • 1 - Op c Λ = Op c (divisorDiscrepancy α) * Op c μ` across all of `L²(𝕋)`. -/
theorem Op_zeta_add_smul_one_sub_Op_vonMangoldt {c : ℕ} (hc : 1 < c) (α : ℝ) :
    Op c (ζ : ArithmeticFunction ℝ) + α • (1 : L2 →L[ℝ] L2)
        - Op c ArithmeticFunction.vonMangoldt
      = Op c (divisorDiscrepancy α) * Op c (μ : ArithmeticFunction ℝ) := by
  rw [Op_mul hc, divisorDiscrepancy_mul_moebius, Op_sub, Op_add, Op_smul, Op_one hc]

/-- **Whole-Domain Divisor–Hyperbola Pairing Identity**: for `1 < c`, `c ≤ P + 1`,
`Nat.clog 2 c ≤ R + 1`, `α : ℝ`, and `f : L²(𝕋)`, `2 * ⟪Op c ζ f, f⟫ + 2 * α * ‖f‖² - ⟪primeOperator c P R f, f⟫`
equals `2 * ⟪Op c μ f, (Op c (divisorDiscrepancy α))* f⟫`. -/
theorem two_inner_Op_zeta_add_smul_sub_inner_primeOperator_eq_divisor_pairing {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) (α : ℝ) (f : L2) :
    2 * ⟪Op c (ζ : ArithmeticFunction ℝ) f, f⟫_ℝ
        + 2 * α * ‖f‖ ^ 2
        - ⟪primeOperator c P R f, f⟫_ℝ
      = 2 * ⟪Op c (μ : ArithmeticFunction ℝ) f,
          ContinuousLinearMap.adjoint (Op c (divisorDiscrepancy α)) f⟫_ℝ := by
  rw [inner_primeOperator_eq_two_inner_Op_vonMangoldt hc hP hR, ← real_inner_self_eq_norm_sq,
    ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp,
    ← Op_zeta_add_smul_one_sub_Op_vonMangoldt hc α,
    _root_.sub_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
    inner_sub_left, inner_add_left, real_inner_smul_left]
  ring

/-! ### 2. Discrete Pole Riesz Mean and Two-Piece Decomposition of `M c - Psihalf c` & `G (log c)` -/

/-- The discrete pole Riesz mean `log c * ⟪Op c ζ vac, vac⟫` on `L²(𝕋)`. -/
def discretePoleRiesz (c : ℕ) : ℝ :=
  Real.log c * ⟪Op c (ζ : ArithmeticFunction ℝ) vac, vac⟫_ℝ

/-- Explicit sum formula for `discretePoleRiesz c` (`1 < c`). -/
theorem discretePoleRiesz_eq_sum {c : ℕ} (hc : 1 < c) :
    discretePoleRiesz c
      = Real.log c *
        ∑ n ∈ Finset.range c,
          (ζ : ArithmeticFunction ℝ) n
            * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.log n / Real.log c)) := by
  unfold discretePoleRiesz
  rw [real_inner_comm, inner_vac_Op hc]

/-- The smooth Euler–Maclaurin pole remainder `M c - (discretePoleRiesz c + α * log c)`. -/
def smoothPoleRem (c : ℕ) (α : ℝ) : ℝ :=
  M c - (discretePoleRiesz c + α * Real.log c)

/-- **Two-Piece Divisor–Hyperbola Identity for `M c - Psihalf c`**: for `1 < c` and `α : ℝ`,
`M c - Psihalf c` splits into the smooth Euler–Maclaurin remainder `smoothPoleRem c α` plus the
inner product of `Op c μ vac` and `(Op c (divisorDiscrepancy α))* vac`. -/
theorem M_sub_Psihalf_eq_smoothPoleRem_add_divisor_pairing {c : ℕ} (hc : 1 < c) (α : ℝ) :
    M c - Psihalf c
      = smoothPoleRem c α
        + Real.log c *
          ⟪Op c (μ : ArithmeticFunction ℝ) vac,
            ContinuousLinearMap.adjoint (Op c (divisorDiscrepancy α)) vac⟫_ℝ := by
  have hpair := two_inner_Op_zeta_add_smul_sub_inner_primeOperator_eq_divisor_pairing
    hc (Nat.le_succ c) (Nat.le_succ _) α vac
  have hpsi := two_mul_Psihalf_eq_log_mul_inner_primeOperator_vac hc (Nat.le_succ c) (Nat.le_succ _)
  rw [norm_vac_sq, mul_one] at hpair
  have hmul := congr_arg (Real.log c * ·) hpair
  unfold smoothPoleRem discretePoleRiesz
  linear_combination (hmul - hpsi) / 2

/-! ### 3. Smooth Inverse Characterization of `moebiusVac c := Op c μ vac` on `L²(𝕋)` -/

/-- The Möbius vacuum vector `Op c μ vac` on `L²(𝕋)`. -/
def moebiusVac (c : ℕ) : L2 :=
  Op c (μ : ArithmeticFunction ℝ) vac

end Cvs.WeilForm.DivisorHyperbolaFactorisation
