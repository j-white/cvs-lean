import Mathlib
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InterPrimePhaseCancellation
import Cvs.WeilForm.VonMangoldtMultiplier
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Universal `log 2` Band-Free Base, Dyadic Shell Dimer Reduction, and Abel Summation

Establishes `vonMangoldtSymbol x ∈ bandFree (log 2)`, general shell dimer square reduction on
`[a, b]` when `L ≤ 2 log a`, and mean-free step cancellation via Abel summation by parts.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Cvs.WeilForm.BandFreeLogTwoBase
open Cvs.ZeroCounting

/-! ### 1. Universal `bandFree (Real.log 2)` Base & General Shell Dimer Reduction -/

/-- The von Mangoldt function vanishes at `0` and `1`. -/
theorem vonMangoldt_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) :
    ArithmeticFunction.vonMangoldt n = 0 := by
  interval_cases n <;> simp

/-- Prime-power shell weight `w(n) = Λ(n) n^{-1/2}`. -/
def shellWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2) : ℝ)

theorem shellWeight_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : shellWeight n = 0 := by
  unfold shellWeight
  rw [vonMangoldt_eq_zero_of_lt_two hn, zero_mul]

/-- General prime-power shell symbol on `Finset.Icc a b`:
`∑_{a ≤ n ≤ b} 2 Λ(n) n^{-1/2} cos(t log n)`. -/
def shellSymbol (a b : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc a b, 2 * shellWeight n * Real.cos (t * Real.log n)

/-- `shellSymbol a b` is `Cvs.WeilForm.InterPrimePhaseCancellation.cosSum` on `Finset.Icc a b` with `shellWeight` and `log`. -/
theorem shellSymbol_eq_cosSum (a b : ℕ) (t : ℝ) :
    shellSymbol a b t = Cvs.WeilForm.InterPrimePhaseCancellation.cosSum (Finset.Icc a b) shellWeight (fun n => Real.log n) t := rfl

/-- `vonMangoldtSymbol x` equals `shellSymbol 2 x` since `Λ(0) = Λ(1) = 0`. -/
theorem vonMangoldtSymbol_eq_shellSymbol (x : ℕ) (t : ℝ) :
    Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol x t = shellSymbol 2 x t := by
  unfold Cvs.WeilForm.VonMangoldtMultiplier.vonMangoldtSymbol shellSymbol shellWeight
  refine (Finset.sum_subset (fun n hn => Finset.mem_range.2
    (Nat.lt_succ_of_le (Finset.mem_Icc.1 hn).2)) fun n hn hnI => ?_).symm
  have hnx : n ≤ x := Nat.le_of_lt_succ (Finset.mem_range.1 hn)
  have hlt : n < 2 := by
    by_contra hge
    exact hnI (Finset.mem_Icc.2 ⟨not_lt.mp hge, hnx⟩)
  rw [vonMangoldt_eq_zero_of_lt_two hlt]
  ring

/-- Additive dyadic/shell decomposition of `shellSymbol` across `[a, m]` and `[m + 1, b]`. -/
theorem shellSymbol_split {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b) (t : ℝ) :
    shellSymbol a b t = shellSymbol a m t + shellSymbol (m + 1) b t := by
  have hunion : Finset.Icc a b = Finset.Icc a m ∪ Finset.Icc (m + 1) b := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc a m) (Finset.Icc (m + 1) b) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  unfold shellSymbol
  rw [hunion, Finset.sum_union hdisj]

/-- Sum-frequency condition `L ≤ |log m + log n|` for `m, n ∈ Finset.Icc a b` when `L ≤ 2 log a`. -/
theorem le_abs_log_add_log_of_mem_Icc {a b : ℕ} {L : ℝ} (hLa : L ≤ 2 * Real.log a)
    {m n : ℕ} (hm : m ∈ Finset.Icc a b) (hn : n ∈ Finset.Icc a b) :
    L ≤ |Real.log m + Real.log n| := by
  have hm1 := Cvs.WeilForm.VonMangoldtMultiplier.log_natCast_le (Finset.mem_Icc.1 hm).1
  have hn1 := Cvs.WeilForm.VonMangoldtMultiplier.log_natCast_le (Finset.mem_Icc.1 hn).1
  exact (by linarith : L ≤ Real.log m + Real.log n).trans (le_abs_self _)

/-- **General Shell Dimer Square Identity on `formDomain hL`**: when `L ≤ 2 log a`, all sum
frequencies `log m + log n` (`m, n ∈ [a, b]`) are band-free on `(0, L]`, so
`∫ (shellSymbol a b)² ρ_φ = 2 (∑_{n=a}^b w(n))² ‖φ‖² − ∫ pairwisePhaseDeficit ρ_φ`. -/
theorem integral_shellSymbol_sq_mul_rho_eq_budget_sub_deficit {a b : ℕ} {L : ℝ} {hL : 0 ≤ L}
    (hLa : L ≤ 2 * Real.log a) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    ∫ t, shellSymbol a b t ^ 2 * Cvs.WeilForm.EvenBulkVisibility.rho φ t
      = 2 * (∑ n ∈ Finset.Icc a b, shellWeight n) ^ 2 * ‖φ‖ ^ 2
        - ∫ t, Cvs.WeilForm.InterPrimePhaseCancellation.pairwisePhaseDeficit (Finset.Icc a b) shellWeight (fun n => Real.log n) t
            * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  simp only [shellSymbol_eq_cosSum]
  exact Cvs.WeilForm.InterPrimePhaseCancellation.integral_cosSum_sq_mul_rho_eq_budget_sub_deficit shellWeight (fun n => Real.log n)
    (fun m hm n hn => le_abs_log_add_log_of_mem_Icc hLa hm hn) φ

/-! ### 2. Mean-Free Step Cancellation & Stieltjes / Abel Summation by Parts -/

/-- Continuous step mean weight `∫_n^{n+1} u^{-1/2} du = 2 (√(n+1) − √n)`. -/
def stepMeanWeight (n : ℕ) : ℝ :=
  2 * (Real.sqrt (n + 1) - Real.sqrt n)

/-- Mean-free arithmetic weight `w(n) − 2(√(n+1) − √n)`. -/
def meanFreeWeight (n : ℕ) : ℝ :=
  shellWeight n - stepMeanWeight n

/-- Cumulative mean-free discrepancy `D(m) = ∑_{n=1}^m (w(n) − 2(√(n+1) − √n))`. -/
def cumMeanFreeDiscrepancy (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, meanFreeWeight n

theorem stepMeanWeight_nonneg (n : ℕ) : 0 ≤ stepMeanWeight n := by
  unfold stepMeanWeight
  have h : Real.sqrt n ≤ Real.sqrt (n + 1) := Real.sqrt_le_sqrt (by linarith)
  linarith

/-- Exact telescoping of `stepMeanWeight`: `∑_{n=1}^m 2(√(n+1) − √n) = 2(√(m+1) − 1)`. -/
theorem sum_stepMeanWeight (m : ℕ) :
    ∑ n ∈ Finset.Icc 1 m, stepMeanWeight n = 2 * (Real.sqrt (m + 1) - 1) := by
  induction m with
  | zero =>
    simp [stepMeanWeight]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 k), ih]
    unfold stepMeanWeight
    push_cast
    ring

theorem cumMeanFreeDiscrepancy_succ (m : ℕ) :
    cumMeanFreeDiscrepancy (m + 1) = cumMeanFreeDiscrepancy m + meanFreeWeight (m + 1) :=
  Finset.sum_Icc_succ_top (Nat.le_add_left 1 m) meanFreeWeight

/-- **Abel Summation by Parts for `meanFreeWeight`**:
`∑_{n=1}^m meanFreeWeight n · g(n) = D(m) g(m+1) + ∑_{n=1}^m D(n) (g(n) − g(n+1))`. -/
theorem sum_meanFreeWeight_mul_eq_abel (m : ℕ) (g : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 m, meanFreeWeight n * g n
      = cumMeanFreeDiscrepancy m * g (m + 1)
        + ∑ n ∈ Finset.Icc 1 m, cumMeanFreeDiscrepancy n * (g n - g (n + 1)) := by
  induction m with
  | zero =>
    simp [cumMeanFreeDiscrepancy]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 k),
      Finset.sum_Icc_succ_top (Nat.le_add_left 1 k), ih, cumMeanFreeDiscrepancy_succ k]
    ring

/-- Mean-free cosine symbol `∑_{n=1}^m 2 meanFreeWeight(n) cos(t log n)`. -/
def meanFreeCosSymbol (m : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, 2 * meanFreeWeight n * Real.cos (t * Real.log n)

/-- Abel-differenced cosine symbol `∑_{n=1}^m 2 D(n) (cos(t log n) − cos(t log(n+1)))`. -/
def abelDiffCosSymbol (m : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m,
    2 * cumMeanFreeDiscrepancy n * (Real.cos (t * Real.log n) - Real.cos (t * Real.log (n + 1)))

/-- **Frequency-Space Abel Decomposition**: splits `meanFreeCosSymbol m` into the boundary cosine
at `log(m+1)` plus `abelDiffCosSymbol m`. -/
theorem meanFreeCosSymbol_eq_boundary_add_abelDiff (m : ℕ) (t : ℝ) :
    meanFreeCosSymbol m t
      = 2 * cumMeanFreeDiscrepancy m * Real.cos (t * Real.log ((m + 1 : ℕ) : ℝ))
        + abelDiffCosSymbol m t := by
  have h := sum_meanFreeWeight_mul_eq_abel m (fun n : ℕ => 2 * Real.cos (t * Real.log n))
  have hl : (∑ n ∈ Finset.Icc 1 m, meanFreeWeight n * (2 * Real.cos (t * Real.log n)))
      = meanFreeCosSymbol m t := by
    unfold meanFreeCosSymbol
    exact Finset.sum_congr rfl fun n _ => by ring
  have hr : (∑ n ∈ Finset.Icc 1 m,
        cumMeanFreeDiscrepancy n * (2 * Real.cos (t * Real.log n)
          - 2 * Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ))))
      = abelDiffCosSymbol m t := by
    unfold abelDiffCosSymbol
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  rw [hl, hr] at h
  linarith

/-- **Product-to-Sum Sine Factorization of Each Abel Step**:
`cos(t log n) − cos(t log(n+1)) = 2 sin(t (log(n+1) − log n) / 2) sin(t (log n + log(n+1)) / 2)`. -/
theorem cos_log_sub_cos_log_succ (n : ℕ) (t : ℝ) :
    Real.cos (t * Real.log n) - Real.cos (t * Real.log (n + 1))
      = 2 * Real.sin (t * ((Real.log (n + 1) - Real.log n) / 2))
          * Real.sin (t * ((Real.log n + Real.log (n + 1)) / 2)) := by
  have h1 : t * Real.log n
      = t * ((Real.log n + Real.log (n + 1)) / 2)
        - t * ((Real.log (n + 1) - Real.log n) / 2) := by ring
  have h2 : t * Real.log (n + 1)
      = t * ((Real.log n + Real.log (n + 1)) / 2)
        + t * ((Real.log (n + 1) - Real.log n) / 2) := by ring
  rw [h1, h2, Real.cos_sub, Real.cos_add]
  ring

end Cvs.WeilForm.BandFreeLogTwoBase
