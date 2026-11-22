import Mathlib
import Cvs.WeilForm.DivisorHyperbolaFactorisation
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.GreenRemovesFirstArchChannel
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.PrimeOperatorBudgetGap
import Cvs.WeilForm.OrganisingIdentityGreen
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.ShiftedDirichletSchurVacuum
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowCircleIsometry
import Cvs.WeilForm.WindowRepresentative
import Cvs.WeilForm.WindowVacuumRieszMean

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Whole-Domain Unification of `Q = E + A - F`, Radical Tail Pairing, and Divisor–Hyperbola `Op c`

Combines the `Q = E + A - F` / `shiftedArchSymbol` representation (`Cvs.WeilForm.OrganisingIdentityGreen`), the `windowCircle` isometry (`Cvs.WeilForm.WindowCircleIsometry`),
the Möbius-tail radical bridge (`Cvs.WeilForm.TailBridgeCOneWindow`), and the divisor–hyperbola `Op c` factorization (`Cvs.WeilForm.DivisorHyperbolaFactorisation`) across `Dom c`.
-/

noncomputable section

open MeasureTheory Real Set
open scoped InnerProductSpace NNReal ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.WeilForm.WholeDomainUnification
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.WeilForm.ThetaSpaceParseval (weilθ)
open Cvs.WeilForm.PoleArchPrimeProblem (poleTerm archTerm primeTerm)
open Cvs.WeilForm.WindowVacuumRieszMean (vac)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.NilpotentResolventEulerSquares (resolvent_toeplitz_identity inner_resolvent_toeplitz)
open Cvs.WeilForm.WindowCircleIsometry (windowCircle norm_sq_windowCircle primeTerm_rep_eq_inner_primeOperator)
open Cvs.WeilForm.OrganisingIdentityGreen (windowGreenEnergy windowMeanTerm meanFreePrimeTerm)
open Cvs.WeilForm.DirichletSchurFactorisation
open Cvs.WeilForm.ShiftedDirichletSchurVacuum
open Cvs.WeilForm.DivisorHyperbolaFactorisation

attribute [local instance] Classical.propDecidable

/-! ### 1. Global Zeta–Möbius Toeplitz Resolvent Identities on `L²(𝕋)` -/

/-! ### 2. Whole-Domain Unification of `Q = E + A - F` and Divisor–Hyperbola `Op c` on `formDomain` -/

/-- For every `φ ∈ window (log c)` (`1 < c`, `c ≤ P + 1`, `Nat.clog 2 c ≤ R + 1`) and `α : ℝ`,
`primeTerm P R (rep φ)` decomposes into the discrete pole term `2 ⟪Op c ζ g_φ, g_φ⟫ + 2 α ‖φ‖²`
minus the divisor–hyperbola Möbius pairing on `L²(𝕋)`. -/
theorem primeTerm_rep_eq_zeta_add_smul_sub_divisor_pairing {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1)
    (α : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    primeTerm P R (Cvs.WeilForm.WindowRepresentative.rep φ)
      = 2 * ⟪Op c (ζ : ArithmeticFunction ℝ) (windowCircle hc φ), windowCircle hc φ⟫_ℝ
        + 2 * α * ‖φ‖ ^ 2
        - 2 * ⟪Op c (μ : ArithmeticFunction ℝ) (windowCircle hc φ),
            ContinuousLinearMap.adjoint (Op c (divisorDiscrepancy α)) (windowCircle hc φ)⟫_ℝ := by
  have h := two_inner_Op_zeta_add_smul_sub_inner_primeOperator_eq_divisor_pairing
    hc hP hR α (windowCircle hc φ)
  rw [← primeTerm_rep_eq_inner_primeOperator hc P R φ, norm_sq_windowCircle hc φ] at h
  linarith

/-- The smooth pole–zeta quadrature remainder on `window (log c)`:
`windowMeanTerm (rep φ) - (2 * ⟪Op c ζ (windowCircle hc φ), windowCircle hc φ⟫ + 2 * α * ‖φ‖²)`. -/
def smoothPoleZetaRem {c : ℕ} (hc : 1 < c) (α : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) : ℝ :=
  windowMeanTerm (Cvs.WeilForm.WindowRepresentative.rep φ)
    - (2 * ⟪Op c (ζ : ArithmeticFunction ℝ) (windowCircle hc φ), windowCircle hc φ⟫_ℝ
      + 2 * α * ‖φ‖ ^ 2)

/-- **Whole-Window `meanFreePrimeTerm` Divisor–Hyperbola Identity**: for `1 < c`, `c ≤ P + 1`,
`Nat.clog 2 c ≤ R + 1`, `α : ℝ`, and `φ ∈ window (log c)`, `-meanFreePrimeTerm P R (rep φ)` equals
`smoothPoleZetaRem hc α φ + 2 * ⟪Op c μ g_φ, (Op c (divisorDiscrepancy α))* g_φ⟫`. -/
theorem neg_meanFreePrimeTerm_rep_eq_smooth_add_divisor_pairing {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1)
    (α : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    -meanFreePrimeTerm P R (Cvs.WeilForm.WindowRepresentative.rep φ)
      = smoothPoleZetaRem hc α φ
        + 2 * ⟪Op c (μ : ArithmeticFunction ℝ) (windowCircle hc φ),
            ContinuousLinearMap.adjoint (Op c (divisorDiscrepancy α)) (windowCircle hc φ)⟫_ℝ := by
  unfold meanFreePrimeTerm smoothPoleZetaRem
  rw [primeTerm_rep_eq_zeta_add_smul_sub_divisor_pairing hc hP hR α φ]
  ring

/-- **Shifted-Arch + Divisor–Hyperbola Representation of `Q` on `formDomain (log c)`**:
combines `∫ shiftedArchSymbol · ρ_φ` with `smoothPoleZetaRem` and the divisor–hyperbola pairing. -/
theorem Q_eq_shiftedArch_add_smooth_add_divisor_pairing {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1)
    (α : ℝ) (φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg c)) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg c) P R φ
      = (∫ t, Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
        + smoothPoleZetaRem hc α (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c))
        + 2 * ⟪Op c (μ : ArithmeticFunction ℝ) (windowCircle hc (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c))),
            ContinuousLinearMap.adjoint (Op c (divisorDiscrepancy α))
              (windowCircle hc (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)))⟫_ℝ := by
  have h1 := Cvs.WeilForm.OrganisingIdentityGreen.Q_eq_shiftedArch_sub_meanFreePrime (Real.log_natCast_nonneg c) P R φ
  have h2 := neg_meanFreePrimeTerm_rep_eq_smooth_add_divisor_pairing
    hc hP hR α (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c))
  linarith

/-! ### 3. Telescopic Partial-Sum Formula for `rieszCorrelation` and `L²(𝕋)` Norm Bound -/

/-- The `1/2`-weighted partial sum `∑_{1 ≤ n ≤ k} a(n) n^{-1/2}` of an arithmetic function `a`. -/
def partialSumHalf (a : ArithmeticFunction ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 k, a n * (n : ℝ) ^ (-(1 / 2 : ℝ))

/-- The logarithmic step weight `log (k + 1) - log k`. -/
def logStep (k : ℕ) : ℝ :=
  Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)

/-- `logStep k` is nonnegative for `1 ≤ k`. -/
theorem logStep_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ logStep k := by
  unfold logStep
  refine sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast Nat.le_succ k))

/-- Telescoping sum of `logStep k` over `k ∈ Finset.Ico m c` for `m ≤ c`. -/
theorem sum_Ico_logStep {m c : ℕ} (hmc : m ≤ c) :
    ∑ k ∈ Finset.Ico m c, logStep k = Real.log c - Real.log m :=
  Finset.sum_Ico_sub (fun k : ℕ => Real.log (k : ℝ)) hmc

/-- For `1 ≤ c`, `∑_{k ∈ Ico 1 c} logStep k = log c`. -/
theorem sum_Ico_one_logStep {c : ℕ} (hc : 1 ≤ c) :
    ∑ k ∈ Finset.Ico 1 c, logStep k = Real.log c := by
  rw [sum_Ico_logStep hc, Nat.cast_one, Real.log_one, sub_zero]

/-- Indicator rewriting of `sum_Ico_logStep` over `Finset.Ico 1 c` for `1 ≤ m ≤ c` and `n ≤ c`. -/
theorem log_sub_log_max_eq_sum_Ico {c m n : ℕ} (hm1 : 1 ≤ m) (hmc : m ≤ c)
    (hnc : n ≤ c) :
    Real.log c - Real.log (max (m : ℝ) (n : ℝ))
      = ∑ k ∈ Finset.Ico 1 c,
          (if m ≤ k ∧ n ≤ k then logStep k else 0) := by
  have hcast : max (m : ℝ) (n : ℝ) = ((max m n : ℕ) : ℝ) := (Nat.cast_max m n).symm
  rw [hcast, ← sum_Ico_logStep (max_le hmc hnc), ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_Ico, Finset.mem_filter, max_le_iff]
  constructor
  · rintro ⟨⟨hm, hn⟩, hkc⟩
    exact ⟨⟨le_trans hm1 hm, hkc⟩, hm, hn⟩
  · rintro ⟨⟨_, hkc⟩, hm, hn⟩
    exact ⟨⟨hm, hn⟩, hkc⟩

/-- Sum over `Finset.range c` of a function vanishing at `0` equals the sum over `Finset.Ico 1 c`. -/
theorem sum_range_eq_sum_Ico_one {c : ℕ} {f : ℕ → ℝ} (h0 : f 0 = 0) :
    ∑ n ∈ Finset.range c, f n = ∑ n ∈ Finset.Ico 1 c, f n := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · rw [← Nat.Ico_zero_eq_range, ← Finset.sum_Ico_consecutive f (Nat.zero_le 1) hc,
      Nat.Ico_zero_eq_range, Finset.sum_range_one, h0, zero_add]

/-- **Telescopic Partial-Sum Formula for `rieszCorrelation`**: for `1 < c` and any arithmetic
functions `a, b`, `log c * rieszCorrelation c a b` equals `∑_{1 ≤ k < c} logStep k * A_{1/2}(k) * B_{1/2}(k)`. -/
theorem log_mul_rieszCorrelation_eq_sum_partialSumHalf {c : ℕ} (hc : 1 < c)
    (a b : ArithmeticFunction ℝ) :
    Real.log c * rieszCorrelation c a b
      = ∑ k ∈ Finset.Ico 1 c,
          logStep k * partialSumHalf a k * partialSumHalf b k := by
  have hL : (0 : ℝ) < Real.log c := Real.log_pos (by exact_mod_cast hc)
  unfold rieszCorrelation
  rw [Finset.mul_sum]
  rw [sum_range_eq_sum_Ico_one (by simp)]
  have hinner : ∀ m ∈ Finset.Ico 1 c,
      Real.log c *
          ∑ n ∈ Finset.range c,
            a m * b n * ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))
              * (1 - max (Real.log m / Real.log c) (Real.log n / Real.log c)))
        = ∑ k ∈ Finset.Ico 1 c,
            logStep k *
              ((if m ≤ k then a m * (m : ℝ) ^ (-(1 / 2 : ℝ)) else 0)
                * partialSumHalf b k) := by
    intro m hm
    rw [Finset.mul_sum, sum_range_eq_sum_Ico_one (by simp)]
    have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    have hmc : m ≤ c := (Finset.mem_Ico.mp hm).2.le
    have hterm : ∀ n ∈ Finset.Ico 1 c,
        Real.log c *
            (a m * b n * ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))
              * (1 - max (Real.log m / Real.log c) (Real.log n / Real.log c))))
          = ∑ k ∈ Finset.Ico 1 c,
              logStep k *
                (if m ≤ k then a m * (m : ℝ) ^ (-(1 / 2 : ℝ)) else 0) *
                (if n ≤ k then b n * (n : ℝ) ^ (-(1 / 2 : ℝ)) else 0) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
      have hnc : n ≤ c := (Finset.mem_Ico.mp hn).2.le
      have hdiv : Real.log c * (1 - max (Real.log m / Real.log c) (Real.log n / Real.log c))
          = Real.log c - Real.log (max (m : ℝ) (n : ℝ)) := by
        rcases le_total (m : ℝ) (n : ℝ) with hle | hle
        · have hlog : Real.log m ≤ Real.log n := Real.log_le_log (by exact_mod_cast hm1) hle
          have hdiv_le : Real.log m / Real.log c ≤ Real.log n / Real.log c :=
            div_le_div_of_nonneg_right hlog hL.le
          rw [max_eq_right hle, max_eq_right hdiv_le]
          field_simp
        · have hlog : Real.log n ≤ Real.log m := Real.log_le_log (by exact_mod_cast hn1) hle
          have hdiv_le : Real.log n / Real.log c ≤ Real.log m / Real.log c :=
            div_le_div_of_nonneg_right hlog hL.le
          rw [max_eq_left hle, max_eq_left hdiv_le]
          field_simp
      calc
        Real.log c *
            (a m * b n * ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))
              * (1 - max (Real.log m / Real.log c) (Real.log n / Real.log c))))
          = (a m * (m : ℝ) ^ (-(1 / 2 : ℝ))) * (b n * (n : ℝ) ^ (-(1 / 2 : ℝ)))
              * (Real.log c * (1 - max (Real.log m / Real.log c) (Real.log n / Real.log c))) := by
            ring
        _ = (a m * (m : ℝ) ^ (-(1 / 2 : ℝ))) * (b n * (n : ℝ) ^ (-(1 / 2 : ℝ)))
              * ∑ k ∈ Finset.Ico 1 c, (if m ≤ k ∧ n ≤ k then logStep k else 0) := by
            rw [hdiv, log_sub_log_max_eq_sum_Ico hm1 hmc hnc]
        _ = ∑ k ∈ Finset.Ico 1 c,
              logStep k *
                (if m ≤ k then a m * (m : ℝ) ^ (-(1 / 2 : ℝ)) else 0) *
                (if n ≤ k then b n * (n : ℝ) ^ (-(1 / 2 : ℝ)) else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            by_cases hmk : m ≤ k <;> by_cases hnk : n ≤ k <;> (simp [hmk, hnk]; try ring)
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.mul_sum, mul_assoc]
    congr 2
    unfold partialSumHalf
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
    have hkc : k < c := (Finset.mem_Ico.mp hk).2
    omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  unfold partialSumHalf
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
  have hkc : k < c := (Finset.mem_Ico.mp hk).2
  omega

/-- **Telescopic Partial-Sum Formula for `‖Op c a vac‖²`**: for `1 < c` and any arithmetic
function `a`, `log c * ‖Op c a vac‖² = ∑_{1 ≤ k < c} (log(k+1) - log k) * (∑_{1 ≤ n ≤ k} a(n) n^{-1/2})²`. -/
theorem log_mul_norm_sq_Op_vac_eq_sum_partialSumHalf_sq {c : ℕ} (hc : 1 < c)
    (a : ArithmeticFunction ℝ) :
    Real.log c * ‖Op c a vac‖ ^ 2
      = ∑ k ∈ Finset.Ico 1 c, logStep k * partialSumHalf a k ^ 2 := by
  rw [norm_sq_Op_vac_eq_rieszCorrelation hc, log_mul_rieszCorrelation_eq_sum_partialSumHalf hc]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- **Uniform Partial-Sum Bound on `‖Op c a vac‖`**: if `|∑_{1 ≤ n ≤ k} a(n) n^{-1/2}| ≤ B` for every
`1 ≤ k < c`, then `‖Op c a vac‖ ≤ B` on `L²(𝕋)`. -/
theorem norm_Op_vac_le_of_partialSumHalf_le {c : ℕ} (hc : 1 < c)
    (a : ArithmeticFunction ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ k ∈ Finset.Ico 1 c, |partialSumHalf a k| ≤ B) :
    ‖Op c a vac‖ ≤ B := by
  have hL : (0 : ℝ) < Real.log c := Real.log_pos (by exact_mod_cast hc)
  have hsq : Real.log c * ‖Op c a vac‖ ^ 2 ≤ Real.log c * B ^ 2 := by
    rw [log_mul_norm_sq_Op_vac_eq_sum_partialSumHalf_sq hc,
      ← sum_Ico_one_logStep hc.le, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hstep : 0 ≤ logStep k := logStep_nonneg hk1
    have hle : partialSumHalf a k ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs (partialSumHalf a k)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB k hk) 2
    exact mul_le_mul_of_nonneg_left hle hstep
  have hsq' : ‖Op c a vac‖ ^ 2 ≤ B ^ 2 := le_of_mul_le_mul_left hsq hL
  exact nonneg_le_nonneg_of_sq_le_sq hB0 (by simpa only [sq] using hsq')

end Cvs.WeilForm.WholeDomainUnification
