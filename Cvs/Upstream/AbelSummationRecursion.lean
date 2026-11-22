import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Unrolling a first-order recursion with Abel summation

For `v_j = −a_j v_{j+1} + b_j + n_j` (`k ≤ j < J`) and `π_j = ∏_{k ≤ i < j} (−a_i)`:
`v_k = Σ_{k ≤ j < J} π_j (b_j + n_j) + π_J v_J`. With `β_j = b_j/(1 + a_j)` one has `π_j b_j = (π_j − π_{j+1})β_j`, and
summation by parts gives `Σ_{k ≤ j < J} π_j b_j = β_k − π_J β_{J−1} + Σ_{k < j < J} π_j(β_j − β_{j−1})`.
-/

noncomputable section

open Finset

namespace Cvs.Upstream.AbelSummationRecursion

/-- The running product `π_j = ∏_{k ≤ i < j} (−a_i)`. -/
def prodNeg (a : ℕ → ℂ) (k j : ℕ) : ℂ := ∏ i ∈ Ico k j, (-a i)

theorem prodNeg_self (a : ℕ → ℂ) (k : ℕ) : prodNeg a k k = 1 := by simp [prodNeg]

theorem prodNeg_succ (a : ℕ → ℂ) {k j : ℕ} (h : k ≤ j) : prodNeg a k (j + 1) = prodNeg a k j * (-a j) := by
  unfold prodNeg; rw [Finset.prod_Ico_succ_top h]

theorem prodNeg_bot (a : ℕ → ℂ) {k j : ℕ} (h : k < j) : prodNeg a k j = (-a k) * prodNeg a (k + 1) j := by
  unfold prodNeg; rw [Finset.prod_eq_prod_Ico_succ_bot h]

/-- **Unrolling.** -/
theorem unroll {a b n v : ℕ → ℂ} {k₀ J : ℕ} (hrec : ∀ j, k₀ ≤ j → j < J → v j = -a j * v (j + 1) + b j + n j) :
    ∀ k, k₀ ≤ k → k ≤ J → v k = (∑ j ∈ Ico k J, prodNeg a k j * (b j + n j)) + prodNeg a k J * v J := by
  intro k hk0 hk
  induction h : J - k generalizing k with
  | zero =>
    have : k = J := by omega
    subst this; simp [prodNeg_self]
  | succ m ih =>
    have hk' : k < J := by omega
    have IH := ih (k + 1) (by omega) (by omega) (by omega)
    have hs : ∑ j ∈ Ico (k + 1) J, prodNeg a k j * (b j + n j)
        = -a k * ∑ j ∈ Ico (k + 1) J, prodNeg a (k + 1) j * (b j + n j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      rw [prodNeg_bot a (by omega)]; ring
    rw [hrec k hk0 hk', IH, Finset.sum_eq_sum_Ico_succ_bot hk', prodNeg_self, prodNeg_bot a hk', hs]
    ring

/-- **Summation by parts** for `π_j b_j = (π_j − π_{j+1})β_j`. -/
theorem abel {a β : ℕ → ℂ} {k : ℕ} : ∀ J, k < J →
    ∑ j ∈ Ico k J, (prodNeg a k j - prodNeg a k (j + 1)) * β j
      = β k - prodNeg a k J * β (J - 1) + ∑ j ∈ Ico (k + 1) J, prodNeg a k j * (β j - β (j - 1)) := by
  intro J hJ
  induction J, hJ using Nat.le_induction with
  | base =>
    simp [prodNeg_self]; ring
  | succ J hJ ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih, Finset.sum_Ico_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    ring

/-- `π_j b_j = (π_j − π_{j+1})β_j` when `b_j = β_j (1 + a_j)`. -/
theorem prodNeg_mul_eq (a β : ℕ → ℂ) {k j : ℕ} (h : k ≤ j) :
    prodNeg a k j * (β j * (1 + a j)) = (prodNeg a k j - prodNeg a k (j + 1)) * β j := by
  rw [prodNeg_succ a h]; ring

/-- **The Abel bound.** If `v_j = −a_j v_{j+1} + β_j(1 + a_j) + n_j` for `k ≤ j < J` with `k < J`, then
`‖v_k‖ ≤ ‖β_k‖ + ‖π_J‖‖β_{J−1}‖ + Σ_{k<j<J} ‖π_j‖‖β_j − β_{j−1}‖ + Σ_{k≤j<J} ‖π_j‖‖n_j‖ + ‖π_J‖‖v_J‖`. -/
theorem norm_le_abel {a β n v : ℕ → ℂ} {k J : ℕ} (hkJ : k < J)
    (hrec : ∀ j < J, k ≤ j → v j = -a j * v (j + 1) + β j * (1 + a j) + n j) :
    ‖v k‖ ≤ ‖β k‖ + ‖prodNeg a k J‖ * ‖β (J - 1)‖
      + ∑ j ∈ Ico (k + 1) J, ‖prodNeg a k j‖ * ‖β j - β (j - 1)‖
      + ∑ j ∈ Ico k J, ‖prodNeg a k j‖ * ‖n j‖ + ‖prodNeg a k J‖ * ‖v J‖ := by
  have hu := unroll (a := a) (b := fun j => β j * (1 + a j)) (n := n) (v := v) (k₀ := k) (J := J)
    (fun j hj hjJ => hrec j hjJ hj) k le_rfl hkJ.le
  rw [show ∑ j ∈ Ico k J, prodNeg a k j * (β j * (1 + a j) + n j)
      = ∑ j ∈ Ico k J, prodNeg a k j * (β j * (1 + a j)) + ∑ j ∈ Ico k J, prodNeg a k j * n j by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring] at hu
  have e2 : ∑ j ∈ Ico k J, prodNeg a k j * (β j * (1 + a j))
      = β k - prodNeg a k J * β (J - 1) + ∑ j ∈ Ico (k + 1) J, prodNeg a k j * (β j - β (j - 1)) := by
    rw [← abel J hkJ]
    exact Finset.sum_congr rfl fun j hj => prodNeg_mul_eq a β (Finset.mem_Ico.mp hj).1
  rw [e2] at hu
  rw [hu]
  have t1 : ‖∑ j ∈ Ico (k + 1) J, prodNeg a k j * (β j - β (j - 1))‖
      ≤ ∑ j ∈ Ico (k + 1) J, ‖prodNeg a k j‖ * ‖β j - β (j - 1)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)
  have t2 : ‖∑ j ∈ Ico k J, prodNeg a k j * n j‖ ≤ ∑ j ∈ Ico k J, ‖prodNeg a k j‖ * ‖n j‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)
  have t3 : ‖prodNeg a k J * β (J - 1)‖ = ‖prodNeg a k J‖ * ‖β (J - 1)‖ := norm_mul _ _
  have t4 : ‖prodNeg a k J * v J‖ = ‖prodNeg a k J‖ * ‖v J‖ := norm_mul _ _
  set X1 := β k
  set X2 := prodNeg a k J * β (J - 1)
  set X3 := ∑ j ∈ Ico (k + 1) J, prodNeg a k j * (β j - β (j - 1))
  set X4 := ∑ j ∈ Ico k J, prodNeg a k j * n j
  set X5 := prodNeg a k J * v J
  have n1 := norm_add_le (X1 - X2 + X3 + X4) X5
  have n2 := norm_add_le (X1 - X2 + X3) X4
  have n3 := norm_add_le (X1 - X2) X3
  have n4 := norm_sub_le X1 X2
  linarith

end Cvs.Upstream.AbelSummationRecursion
