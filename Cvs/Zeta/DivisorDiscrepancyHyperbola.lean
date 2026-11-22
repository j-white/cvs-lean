import Mathlib
import Cvs.WeilForm.DivisorHyperbolaFactorisation
import Cvs.WeilForm.WholeDomainUnification
import Cvs.Xi.MobiusReconstruction
import Cvs.Zeta.PartialSumHalfEulerMaclaurin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Unconditional Dirichlet Hyperbola Identity and Euler–Maclaurin Bounds for `divisorDiscrepancy`

Proves the summation-by-parts identity and unconditional bounds for `partialSumHalf log k`, the disjoint-wing
Dirichlet hyperbola theorem for `partialSumHalf (ζ * ζ) k`, and the `2√k log k` cancellation in `divisorDiscrepancy`.
-/

noncomputable section

open MeasureTheory Real Set
open scoped InnerProductSpace NNReal ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.Zeta.DivisorDiscrepancyHyperbola
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
open Cvs.Xi.MobiusReconstruction (sum_sigma_mul)
open Cvs.WeilForm.WindowVacuumRieszMean (vac inner_vac_Op)
open Cvs.WeilForm.DirichletSchurFactorisation
open Cvs.WeilForm.ShiftedDirichletSchurVacuum
open Cvs.WeilForm.DivisorHyperbolaFactorisation
open Cvs.WeilForm.WholeDomainUnification
open Cvs.Zeta.PartialSumHalfEulerMaclaurin

attribute [local instance] Classical.propDecidable

/-! ### 1. Linearity of `partialSumHalf` and Unconditional Bounds on `partialSumHalf log k` -/

/-- `partialSumHalf` preserves addition of arithmetic functions. -/
theorem partialSumHalf_add (a b : ArithmeticFunction ℝ) (k : ℕ) :
    partialSumHalf (a + b) k = partialSumHalf a k + partialSumHalf b k := by
  unfold partialSumHalf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  change (a n + b n) * _ = _
  ring

/-- `partialSumHalf` preserves subtraction of arithmetic functions. -/
theorem partialSumHalf_sub (a b : ArithmeticFunction ℝ) (k : ℕ) :
    partialSumHalf (a - b) k = partialSumHalf a k - partialSumHalf b k := by
  unfold partialSumHalf
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  change (a n - b n) * _ = _
  ring

/-- `partialSumHalf` preserves scalar multiplication of arithmetic functions. -/
theorem partialSumHalf_smul (α : ℝ) (a : ArithmeticFunction ℝ) (k : ℕ) :
    partialSumHalf (α • a) k = α * partialSumHalf a k := by
  unfold partialSumHalf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  change (α * a n) * _ = _
  ring

/-- Decomposition of `partialSumHalf (divisorDiscrepancy α) k` into `ζ * ζ`, `ζ`, and `log` pieces. -/
theorem partialSumHalf_divisorDiscrepancy (α : ℝ) (k : ℕ) :
    partialSumHalf (divisorDiscrepancy α) k
      = partialSumHalf ((ζ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) k
        + α * partialSumHalf (ζ : ArithmeticFunction ℝ) k
        - partialSumHalf ArithmeticFunction.log k := by
  unfold divisorDiscrepancy
  rw [partialSumHalf_sub, partialSumHalf_add, partialSumHalf_smul]

/-- At `k = 1`, `partialSumHalf log 1 = 0`. -/
theorem partialSumHalf_log_one :
    partialSumHalf ArithmeticFunction.log 1 = 0 := by
  unfold partialSumHalf
  simp

/-- **Summation-by-Parts Identity for `partialSumHalf log k`**: for `1 < k`,
`partialSumHalf log k = log k * partialSumHalf ζ k - discretePoleRiesz k`. -/
theorem partialSumHalf_log_eq_log_mul_zeta_sub_discretePoleRiesz {k : ℕ} (hk : 1 < k) :
    partialSumHalf ArithmeticFunction.log k
      = Real.log (k : ℝ) * partialSumHalf (ζ : ArithmeticFunction ℝ) k - discretePoleRiesz k := by
  have hL : (0 : ℝ) < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  rw [discretePoleRiesz_eq_sum hk, sum_range_eq_sum_Ico_one (by simp),
    partialSumHalf_zeta_eq_sum]
  unfold partialSumHalf
  have hIcc : Finset.Icc 1 k = insert k (Finset.Ico 1 k) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    mul_add, Finset.mul_sum, Finset.mul_sum]
  have hsub :
      ∑ n ∈ Finset.Ico 1 k, Real.log (k : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))
        - ∑ n ∈ Finset.Ico 1 k,
            Real.log (k : ℝ) *
              ((ζ : ArithmeticFunction ℝ) n *
                ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.log (n : ℝ) / Real.log (k : ℝ))))
        = ∑ n ∈ Finset.Ico 1 k,
            ArithmeticFunction.log n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ico.mp hn).1
      omega
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn0,
      Nat.cast_one, one_mul, ArithmeticFunction.log_apply]
    have hne : Real.log (k : ℝ) ≠ 0 := hL.ne'
    field_simp
    ring
  rw [ArithmeticFunction.log_apply]
  linarith

/-! ### 2. Disjoint-Wing Dirichlet Hyperbola Identity for `partialSumHalf (ζ * ζ) k` -/

/-- Convolution formula `partialSumHalf (ζ * ζ) k = ∑_{n=1}^k n^{-1/2} * partialSumHalf ζ (k / n)`. -/
theorem partialSumHalf_zeta_mul_zeta_eq_sum_div (k : ℕ) :
    partialSumHalf ((ζ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) k
      = ∑ n ∈ Finset.Icc 1 k,
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * partialSumHalf (ζ : ArithmeticFunction ℝ) (k / n) := by
  unfold partialSumHalf
  have hsig := sum_sigma_mul k (fun j : ℕ => (j : ℝ) ^ (-(1 / 2 : ℝ))) (fun _ => (1 : ℝ))
  have hrhs :
      ∑ j ∈ Finset.Icc 1 k,
          ((ζ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) j
            * (j : ℝ) ^ (-(1 / 2 : ℝ))
        = ∑ j ∈ Finset.Icc 1 k, (∑ m ∈ j.divisors, (1 : ℝ)) * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zeta_mul_zeta_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hrhs, ← hsig]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm_ne : m ≠ 0 := by
    have := (Finset.mem_Icc.mp hm).1
    omega
  rw [one_mul, Nat.cast_mul, Real.mul_rpow hm0 hn0,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hm_ne,
    Nat.cast_one, one_mul, mul_comm]

/-- Reindexing the vertical wing `M + 1 ≤ n ≤ k`, `1 ≤ m ≤ k / n` at `M = Nat.sqrt k`. -/
theorem sum_vertical_wing_eq_horizontal_wing (k : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc (Nat.sqrt k + 1) k, ∑ m ∈ Finset.Icc 1 (k / n), f m * f n
      = ∑ m ∈ Finset.Icc 1 (Nat.sqrt k), ∑ n ∈ Finset.Icc (Nat.sqrt k + 1) (k / m), f m * f n := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1⟩) (fun q => ⟨q.2, q.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨hnM, _⟩, hm1, hmk⟩ := hp
    have hmn : m * n ≤ k := (Nat.le_div_iff_mul_le (by omega)).mp hmk
    have hm_le : m ≤ Nat.sqrt k := by
      by_contra! hlt
      have hsq : (Nat.sqrt k + 1) * (Nat.sqrt k + 1) ≤ m * n := Nat.mul_le_mul hlt hnM
      have hgt : k < (Nat.sqrt k + 1) * (Nat.sqrt k + 1) := by
        simpa [sq] using Nat.lt_succ_sqrt' k
      omega
    exact ⟨⟨hm1, hm_le⟩, hnM, (Nat.le_div_iff_mul_le hm1).mpr (by rw [mul_comm]; exact hmn)⟩
  · rintro ⟨m, n⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hq ⊢
    obtain ⟨⟨hm1, _⟩, hnM, hnk⟩ := hq
    have hnm : n * m ≤ k := (Nat.le_div_iff_mul_le hm1).mp hnk
    have hnk_le : n ≤ k := le_trans (Nat.le_mul_of_pos_right n hm1) hnm
    exact ⟨⟨hnM, hnk_le⟩, hm1, (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hnm)⟩
  · rintro ⟨n, m⟩ _; rfl
  · rintro ⟨m, n⟩ _; rfl
  · rintro ⟨n, m⟩ _; rfl

/-- **Disjoint-Wing Dirichlet Hyperbola Identity for `partialSumHalf (ζ * ζ) k`**:
with `M = Nat.sqrt k`, `partialSumHalf (ζ * ζ) k = (partialSumHalf ζ M)² + 2 * ∑_{m=1}^M m^{-1/2} ∑_{n=M+1}^{k/m} n^{-1/2}`. -/
theorem partialSumHalf_zeta_mul_zeta_eq_hyperbola (k : ℕ) :
    partialSumHalf ((ζ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) k
      = partialSumHalf (ζ : ArithmeticFunction ℝ) (Nat.sqrt k) ^ 2
        + 2 * ∑ m ∈ Finset.Icc 1 (Nat.sqrt k),
            (m : ℝ) ^ (-(1 / 2 : ℝ))
              * ∑ n ∈ Finset.Icc (Nat.sqrt k + 1) (k / m), (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set M := Nat.sqrt k
  have hMk : M ≤ k := Nat.sqrt_le_self k
  rw [partialSumHalf_zeta_mul_zeta_eq_sum_div]
  have hsplit_outer :
      Finset.Icc 1 k = Finset.Icc 1 M ∪ Finset.Icc (M + 1) k := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj_outer : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) k) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  rw [hsplit_outer, Finset.sum_union hdisj_outer]
  have hfirst :
      ∑ n ∈ Finset.Icc 1 M,
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * partialSumHalf (ζ : ArithmeticFunction ℝ) (k / n)
        = partialSumHalf (ζ : ArithmeticFunction ℝ) M ^ 2
          + ∑ n ∈ Finset.Icc 1 M,
              (n : ℝ) ^ (-(1 / 2 : ℝ))
                * ∑ m ∈ Finset.Icc (M + 1) (k / n), (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hinner : ∀ n ∈ Finset.Icc 1 M,
        partialSumHalf (ζ : ArithmeticFunction ℝ) (k / n)
          = partialSumHalf (ζ : ArithmeticFunction ℝ) M
            + ∑ m ∈ Finset.Icc (M + 1) (k / n), (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
      have hM_div : M ≤ k / n := (Nat.le_div_iff_mul_le hn1).mpr
        (le_trans (Nat.mul_le_mul_left M hnM) (Nat.sqrt_le k))
      rw [partialSumHalf_zeta_eq_sum, partialSumHalf_zeta_eq_sum]
      have hu : Finset.Icc 1 (k / n) = Finset.Icc 1 M ∪ Finset.Icc (M + 1) (k / n) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_union]
        omega
      have hd : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) (k / n)) := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb
        simp only [Finset.mem_Icc] at ha hb
        omega
      rw [hu, Finset.sum_union hd]
    have hcongr :
        ∑ n ∈ Finset.Icc 1 M,
            (n : ℝ) ^ (-(1 / 2 : ℝ)) * partialSumHalf (ζ : ArithmeticFunction ℝ) (k / n)
          = ∑ n ∈ Finset.Icc 1 M,
              ((n : ℝ) ^ (-(1 / 2 : ℝ)) * partialSumHalf (ζ : ArithmeticFunction ℝ) M
                + (n : ℝ) ^ (-(1 / 2 : ℝ))
                  * ∑ m ∈ Finset.Icc (M + 1) (k / n), (m : ℝ) ^ (-(1 / 2 : ℝ))) := by
      refine Finset.sum_congr rfl fun n hn => by rw [hinner n hn, mul_add]
    rw [hcongr, Finset.sum_add_distrib, ← Finset.sum_mul, ← partialSumHalf_zeta_eq_sum, sq]
  have hsecond :
      ∑ n ∈ Finset.Icc (M + 1) k,
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * partialSumHalf (ζ : ArithmeticFunction ℝ) (k / n)
        = ∑ m ∈ Finset.Icc 1 M,
            (m : ℝ) ^ (-(1 / 2 : ℝ))
              * ∑ n ∈ Finset.Icc (M + 1) (k / m), (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simp_rw [partialSumHalf_zeta_eq_sum, Finset.mul_sum]
    have hcomm :
        ∑ n ∈ Finset.Icc (M + 1) k, ∑ m ∈ Finset.Icc 1 (k / n),
            (n : ℝ) ^ (-(1 / 2 : ℝ)) * (m : ℝ) ^ (-(1 / 2 : ℝ))
          = ∑ n ∈ Finset.Icc (M + 1) k, ∑ m ∈ Finset.Icc 1 (k / n),
              (m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => mul_comm _ _
    rw [hcomm, sum_vertical_wing_eq_horizontal_wing k (fun j : ℕ => (j : ℝ) ^ (-(1 / 2 : ℝ)))]
  rw [hfirst, hsecond]
  ring

/-! ### 3. Telescopic Wing Bounds, `k^{1/4}` Square Completion, and Harmonic Bounds -/

/-- The `M`-th harmonic sum `∑_{m=1}^M m⁻¹`. -/
def harmonicSum (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹

/-- Telescoping lower bound on the hyperbola wing `∑_{n=M+1}^N n^{-1/2}` (`M ≤ N`). -/
theorem two_mul_sqrt_succ_sub_le_wing_sum {M N : ℕ} (hMN : M ≤ N) :
    2 * Real.sqrt ((N + 1 : ℕ) : ℝ) - 2 * Real.sqrt ((M + 1 : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc (M + 1) N, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hIcc : Finset.Icc (M + 1) N = Finset.Ico (M + 1) (N + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have htel :
      ∑ n ∈ Finset.Icc (M + 1) N, 2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
        = 2 * Real.sqrt ((N + 1 : ℕ) : ℝ) - 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) := by
    rw [hIcc, ← Finset.mul_sum,
      Finset.sum_Ico_sub (fun n : ℕ => Real.sqrt (n : ℝ)) (Nat.add_le_add_right hMN 1)]
    ring
  rw [← htel]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  exact two_mul_sqrt_succ_sub_sqrt_le_rpow_neg_half hn1

/-- Telescoping upper bound on the hyperbola wing `∑_{n=M+1}^N n^{-1/2}` (`M ≤ N`). -/
theorem wing_sum_le_two_mul_sqrt_sub {M N : ℕ} (hMN : M ≤ N) :
    ∑ n ∈ Finset.Icc (M + 1) N, (n : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ 2 * Real.sqrt (N : ℝ) - 2 * Real.sqrt (M : ℝ) := by
  have htel :
      ∑ n ∈ Finset.Icc (M + 1) N, 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ))
        = 2 * Real.sqrt (N : ℝ) - 2 * Real.sqrt (M : ℝ) := by
    rw [← Finset.mul_sum]
    have hbij :
        ∑ n ∈ Finset.Icc (M + 1) N, (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ))
          = ∑ m ∈ Finset.Ico M N, (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ)) := by
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
    rw [hbij, Finset.sum_Ico_sub (fun m : ℕ => Real.sqrt (m : ℝ)) hMN]
    ring
  rw [← htel]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  exact rpow_neg_half_le_two_mul_sqrt_sub_sqrt_pred hn1

/-- Square-completion upper bound cancelling `k^{1/4}`: for `1 ≤ M`,
`partialSumHalf ζ M * (partialSumHalf ζ M - 4 * √M) ≤ -4 * M + 4`. -/
theorem partialSumHalf_zeta_mul_sub_four_sqrt_le {M : ℕ} (hM : 1 ≤ M) :
    partialSumHalf (ζ : ArithmeticFunction ℝ) M
        * (partialSumHalf (ζ : ArithmeticFunction ℝ) M - 4 * Real.sqrt (M : ℝ))
      ≤ -4 * (M : ℝ) + 4 := by
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hlow := two_mul_sqrt_succ_sub_two_le_partialSumHalf_zeta hM
  have hup := partialSumHalf_zeta_le_two_mul_sqrt_sub_one hM
  have hsq_le : Real.sqrt (M : ℝ) ≤ Real.sqrt ((M + 1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ M)
  have hid :
      partialSumHalf (ζ : ArithmeticFunction ℝ) M
          * (partialSumHalf (ζ : ArithmeticFunction ℝ) M - 4 * Real.sqrt (M : ℝ))
        = (partialSumHalf (ζ : ArithmeticFunction ℝ) M - 2 * Real.sqrt (M : ℝ)) ^ 2
          - 4 * Real.sqrt (M : ℝ) ^ 2 := by ring
  rw [hid, Real.sq_sqrt hM0]
  nlinarith

/-- Square-completion lower bound cancelling `k^{1/4}`: for `1 ≤ M`,
`-4 * M - 3 ≤ partialSumHalf ζ M * (partialSumHalf ζ M - 4 * √(M + 1))`. -/
theorem neg_four_mul_sub_three_le_partialSumHalf_zeta_mul_sub_four_sqrt_succ {M : ℕ} (hM : 1 ≤ M) :
    -4 * (M : ℝ) - 3
      ≤ partialSumHalf (ζ : ArithmeticFunction ℝ) M
          * (partialSumHalf (ζ : ArithmeticFunction ℝ) M - 4 * Real.sqrt ((M + 1 : ℕ) : ℝ)) := by
  have hM1 : (0 : ℝ) ≤ (M + 1 : ℕ) := Nat.cast_nonneg (M + 1)
  have hlow := two_mul_sqrt_succ_sub_two_le_partialSumHalf_zeta hM
  have hup := partialSumHalf_zeta_le_two_mul_sqrt_sub_one hM
  have hsq_le : Real.sqrt (M : ℝ) ≤ Real.sqrt ((M + 1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ M)
  have hsq2 : Real.sqrt ((M + 1 : ℕ) : ℝ) ^ 2 = (M : ℝ) + 1 := by
    rw [Real.sq_sqrt hM1, Nat.cast_add, Nat.cast_one]
  have hid :
      partialSumHalf (ζ : ArithmeticFunction ℝ) M
          * (partialSumHalf (ζ : ArithmeticFunction ℝ) M - 4 * Real.sqrt ((M + 1 : ℕ) : ℝ))
        = (partialSumHalf (ζ : ArithmeticFunction ℝ) M - 2 * Real.sqrt ((M + 1 : ℕ) : ℝ)) ^ 2
          - 4 * Real.sqrt ((M + 1 : ℕ) : ℝ) ^ 2 := by ring
  rw [hid, hsq2]
  nlinarith

/-- **Unconditional Upper Bound on `partialSumHalf (ζ * ζ) k`** (`O(1)`-accurate hyperbola bound):
for `1 ≤ k`, `partialSumHalf (ζ * ζ) k ≤ 4 * √k * harmonicSum (Nat.sqrt k) - 4 * Nat.sqrt k + 4`. -/
theorem partialSumHalf_zeta_mul_zeta_le_harmonic {k : ℕ} (hk : 1 ≤ k) :
    partialSumHalf ((ζ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) k
      ≤ 4 * Real.sqrt (k : ℝ) * harmonicSum (Nat.sqrt k) - 4 * (Nat.sqrt k : ℝ) + 4 := by
  set M := Nat.sqrt k
  have hM1 : 1 ≤ M := Nat.sqrt_pos.mpr hk
  rw [partialSumHalf_zeta_mul_zeta_eq_hyperbola]
  have hwing :
      ∑ m ∈ Finset.Icc 1 M,
          (m : ℝ) ^ (-(1 / 2 : ℝ))
            * ∑ n ∈ Finset.Icc (M + 1) (k / m), (n : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ ∑ m ∈ Finset.Icc 1 M,
            (2 * Real.sqrt (k : ℝ) * (m : ℝ)⁻¹
              - 2 * Real.sqrt (M : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ))) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hM_div : M ≤ k / m := (Nat.le_div_iff_mul_le hm1).mpr
      (le_trans (Nat.mul_le_mul_left M hmM) (Nat.sqrt_le k))
    have hw := wing_sum_le_two_mul_sqrt_sub hM_div
    have hdiv_le : ((k / m : ℕ) : ℝ) ≤ (k : ℝ) / (m : ℝ) :=
      Nat.cast_div_le
    have hsq_div : Real.sqrt ((k / m : ℕ) : ℝ) ≤ Real.sqrt (k : ℝ) / Real.sqrt (m : ℝ) := by
      rw [← Real.sqrt_div (Nat.cast_nonneg k)]
      exact Real.sqrt_le_sqrt hdiv_le
    have hrpow_pos : 0 ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have h1 :
        (m : ℝ) ^ (-(1 / 2 : ℝ))
            * ∑ n ∈ Finset.Icc (M + 1) (k / m), (n : ℝ) ^ (-(1 / 2 : ℝ))
          ≤ (m : ℝ) ^ (-(1 / 2 : ℝ))
              * (2 * (Real.sqrt (k : ℝ) / Real.sqrt (m : ℝ)) - 2 * Real.sqrt (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (hw.trans (by linarith)) hrpow_pos
    have h2 :
        (m : ℝ) ^ (-(1 / 2 : ℝ))
            * (2 * (Real.sqrt (k : ℝ) / Real.sqrt (m : ℝ)) - 2 * Real.sqrt (M : ℝ))
          = 2 * Real.sqrt (k : ℝ) * (m : ℝ)⁻¹
            - 2 * Real.sqrt (M : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [mul_sub, rpow_neg_half_eq_inv_sqrt hm0.le]
      have hsq_sq : (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ = (m : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt hm0.le]
      calc
        (Real.sqrt (m : ℝ))⁻¹ * (2 * (Real.sqrt (k : ℝ) / Real.sqrt (m : ℝ)))
            - (Real.sqrt (m : ℝ))⁻¹ * (2 * Real.sqrt (M : ℝ))
          = 2 * Real.sqrt (k : ℝ) * ((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹)
              - 2 * Real.sqrt (M : ℝ) * (Real.sqrt (m : ℝ))⁻¹ := by ring
        _ = 2 * Real.sqrt (k : ℝ) * (m : ℝ)⁻¹
              - 2 * Real.sqrt (M : ℝ) * (Real.sqrt (m : ℝ))⁻¹ := by rw [hsq_sq]
    linarith
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← partialSumHalf_zeta_eq_sum] at hwing
  unfold harmonicSum
  have hsq_comp := partialSumHalf_zeta_mul_sub_four_sqrt_le hM1
  linarith

/-- **Unconditional Lower Bound on `partialSumHalf (ζ * ζ) k`** (`O(1)`-accurate hyperbola bound):
for `1 ≤ k`, `4 * √k * harmonicSum (Nat.sqrt k) - 4 * Nat.sqrt k - 3 ≤ partialSumHalf (ζ * ζ) k`. -/
theorem harmonic_le_partialSumHalf_zeta_mul_zeta {k : ℕ} (hk : 1 ≤ k) :
    4 * Real.sqrt (k : ℝ) * harmonicSum (Nat.sqrt k) - 4 * (Nat.sqrt k : ℝ) - 3
      ≤ partialSumHalf ((ζ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) k := by
  set M := Nat.sqrt k
  have hM1 : 1 ≤ M := Nat.sqrt_pos.mpr hk
  rw [partialSumHalf_zeta_mul_zeta_eq_hyperbola]
  have hwing :
      ∑ m ∈ Finset.Icc 1 M,
          (2 * Real.sqrt (k : ℝ) * (m : ℝ)⁻¹
            - 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)))
        ≤ ∑ m ∈ Finset.Icc 1 M,
            (m : ℝ) ^ (-(1 / 2 : ℝ))
              * ∑ n ∈ Finset.Icc (M + 1) (k / m), (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hM_div : M ≤ k / m := (Nat.le_div_iff_mul_le hm1).mpr
      (le_trans (Nat.mul_le_mul_left M hmM) (Nat.sqrt_le k))
    have hw := two_mul_sqrt_succ_sub_le_wing_sum hM_div
    have hdiv_ge : (k : ℝ) / (m : ℝ) ≤ ((k / m + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ hm0]
      have hnat : k ≤ (k / m + 1) * m := by
        rw [Nat.add_mul, one_mul]
        exact (Nat.lt_div_mul_add hm1).le
      exact_mod_cast hnat
    have hsq_div : Real.sqrt (k : ℝ) / Real.sqrt (m : ℝ) ≤ Real.sqrt ((k / m + 1 : ℕ) : ℝ) := by
      rw [← Real.sqrt_div (Nat.cast_nonneg k)]
      exact Real.sqrt_le_sqrt hdiv_ge
    have hrpow_pos : 0 ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have h1 :
        (m : ℝ) ^ (-(1 / 2 : ℝ))
            * (2 * (Real.sqrt (k : ℝ) / Real.sqrt (m : ℝ)) - 2 * Real.sqrt ((M + 1 : ℕ) : ℝ))
          ≤ (m : ℝ) ^ (-(1 / 2 : ℝ))
              * ∑ n ∈ Finset.Icc (M + 1) (k / m), (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left ((by linarith : _ ≤ 2 * Real.sqrt ((k / m + 1 : ℕ) : ℝ) - _).trans hw) hrpow_pos
    have h2 :
        (m : ℝ) ^ (-(1 / 2 : ℝ))
            * (2 * (Real.sqrt (k : ℝ) / Real.sqrt (m : ℝ)) - 2 * Real.sqrt ((M + 1 : ℕ) : ℝ))
          = 2 * Real.sqrt (k : ℝ) * (m : ℝ)⁻¹
            - 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [mul_sub, rpow_neg_half_eq_inv_sqrt hm0.le]
      have hsq_sq : (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ = (m : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt hm0.le]
      calc
        (Real.sqrt (m : ℝ))⁻¹ * (2 * (Real.sqrt (k : ℝ) / Real.sqrt (m : ℝ)))
            - (Real.sqrt (m : ℝ))⁻¹ * (2 * Real.sqrt ((M + 1 : ℕ) : ℝ))
          = 2 * Real.sqrt (k : ℝ) * ((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹)
              - 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) * (Real.sqrt (m : ℝ))⁻¹ := by ring
        _ = 2 * Real.sqrt (k : ℝ) * (m : ℝ)⁻¹
              - 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) * (Real.sqrt (m : ℝ))⁻¹ := by rw [hsq_sq]
    linarith
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← partialSumHalf_zeta_eq_sum] at hwing
  unfold harmonicSum
  have hsq_comp := neg_four_mul_sub_three_le_partialSumHalf_zeta_mul_sub_four_sqrt_succ hM1
  linarith

/-! ### 4. Harmonic Log Bounds and `2√k log k` Cancellation in `divisorDiscrepancy` -/

/-- Upper step bound `logStep m ≤ m⁻¹` for `1 ≤ m`. -/
theorem logStep_le_inv {m : ℕ} (hm : 1 ≤ m) :
    logStep m ≤ (m : ℝ)⁻¹ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
  unfold logStep
  rw [← Real.log_div hm1.ne' hm0.ne']
  have hlog := Real.log_le_sub_one_of_pos (div_pos hm1 hm0)
  have hdiv : ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 = (m : ℝ)⁻¹ := by
    rw [Nat.cast_add, Nat.cast_one]
    have hne : (m : ℝ) ≠ 0 := hm0.ne'
    field_simp
    ring
  linarith

/-- Lower step bound `m⁻¹ ≤ logStep (m - 1)` for `2 ≤ m`. -/
theorem inv_le_logStep_pred {m : ℕ} (hm : 2 ≤ m) :
    (m : ℝ)⁻¹ ≤ logStep (m - 1) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hpred : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast (by omega : 0 < m - 1)
  have hsucc : m - 1 + 1 = m := by omega
  unfold logStep
  rw [hsucc]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hpred hm0)
  have hlog_inv :
      Real.log (((m - 1 : ℕ) : ℝ) / (m : ℝ))
        = -(Real.log (m : ℝ) - Real.log ((m - 1 : ℕ) : ℝ)) := by
    rw [Real.log_div hpred.ne' hm0.ne']
    ring
  have hdiv : ((m - 1 : ℕ) : ℝ) / (m : ℝ) - 1 = -(m : ℝ)⁻¹ := by
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    rw [hcast]
    have hne : (m : ℝ) ≠ 0 := hm0.ne'
    field_simp
    ring
  linarith

end Cvs.Zeta.DivisorDiscrepancyHyperbola
