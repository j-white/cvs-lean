import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Summing a first-order recursion against its frozen forcing

If `v_k = −A_k v_{k+1} + β_k(1 + A_k) + n_k` and `a_k = 1/(1 + A_k)`, then `v_k − β_k = a_k n_k − (1 − a_k)(v_{k+1} − v_k)`,
and by parts `Σ_{m≤k<K} (v_k − β_k) = Σ a_k n_k − (v_K − v_m) + a_{K−1}v_K − a_m v_m − Σ_{m<k<K} v_k (a_k − a_{k−1})`.
-/

noncomputable section

open Finset

namespace Cvs.Upstream.RecursionFrozenForcingSum

/-- **The pointwise identity.** -/
theorem sub_eq {v₀ v₁ A β n : ℂ} (hA : 1 + A ≠ 0) (h : v₀ = -A * v₁ + β * (1 + A) + n) :
    v₀ - β = (1 + A)⁻¹ * n - (1 - (1 + A)⁻¹) * (v₁ - v₀) := by
  field_simp
  linear_combination h

/-- **Summation by parts** for `Σ a_k (v_{k+1} − v_k)`. -/
theorem sum_mul_diff (a v : ℕ → ℂ) {m : ℕ} : ∀ K, m < K →
    ∑ k ∈ Ico m K, a k * (v (k + 1) - v k)
      = a (K - 1) * v K - a m * v m - ∑ k ∈ Ico (m + 1) K, v k * (a k - a (k - 1)) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => simp; ring
  | succ K hK ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih, Finset.sum_Ico_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    ring

theorem sum_diff (v : ℕ → ℂ) {m K : ℕ} (h : m ≤ K) : ∑ k ∈ Ico m K, (v (k + 1) - v k) = v K - v m := by
  induction K, h using Nat.le_induction with
  | base => simp
  | succ K hK ih => rw [Finset.sum_Ico_succ_top hK, ih]; ring

/-- **The summed identity.** -/
theorem sum_sub_eq {A β n v : ℕ → ℂ} {m K : ℕ} (hmK : m < K) (hA : ∀ k, m ≤ k → k < K → 1 + A k ≠ 0)
    (hrec : ∀ k, m ≤ k → k < K → v k = -A k * v (k + 1) + β k * (1 + A k) + n k) :
    ∑ k ∈ Ico m K, (v k - β k)
      = ∑ k ∈ Ico m K, (1 + A k)⁻¹ * n k - (v K - v m) + (1 + A (K - 1))⁻¹ * v K - (1 + A m)⁻¹ * v m
        - ∑ k ∈ Ico (m + 1) K, v k * ((1 + A k)⁻¹ - (1 + A (k - 1))⁻¹) := by
  have e1 : ∑ k ∈ Ico m K, (v k - β k)
      = ∑ k ∈ Ico m K, ((1 + A k)⁻¹ * n k - (1 - (1 + A k)⁻¹) * (v (k + 1) - v k)) :=
    Finset.sum_congr rfl fun k hk => by
      rw [Finset.mem_Ico] at hk; exact sub_eq (hA k hk.1 hk.2) (hrec k hk.1 hk.2)
  have e2 : ∑ k ∈ Ico m K, ((1 + A k)⁻¹ * n k - (1 - (1 + A k)⁻¹) * (v (k + 1) - v k))
      = ∑ k ∈ Ico m K, (1 + A k)⁻¹ * n k - ∑ k ∈ Ico m K, (v (k + 1) - v k)
        + ∑ k ∈ Ico m K, (1 + A k)⁻¹ * (v (k + 1) - v k) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2, sum_diff v hmK.le, sum_mul_diff (fun k => (1 + A k)⁻¹) v K hmK]
  ring

/-- **The summed bound.** -/
theorem norm_sum_sub_le {A β n v : ℕ → ℂ} {m K : ℕ} (hmK : m < K) (hA : ∀ k, m ≤ k → k < K → 1 + A k ≠ 0)
    (hrec : ∀ k, m ≤ k → k < K → v k = -A k * v (k + 1) + β k * (1 + A k) + n k) :
    ‖∑ k ∈ Ico m K, (v k - β k)‖
      ≤ ∑ k ∈ Ico m K, ‖(1 + A k)⁻¹‖ * ‖n k‖ + (1 + ‖(1 + A (K - 1))⁻¹‖) * ‖v K‖
        + (1 + ‖(1 + A m)⁻¹‖) * ‖v m‖
        + ∑ k ∈ Ico (m + 1) K, ‖v k‖ * ‖(1 + A k)⁻¹ - (1 + A (k - 1))⁻¹‖ := by
  rw [sum_sub_eq hmK hA hrec]
  set X1 := ∑ k ∈ Ico m K, (1 + A k)⁻¹ * n k
  set X2 := ∑ k ∈ Ico (m + 1) K, v k * ((1 + A k)⁻¹ - (1 + A (k - 1))⁻¹)
  have t1 : ‖X1‖ ≤ ∑ k ∈ Ico m K, ‖(1 + A k)⁻¹‖ * ‖n k‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
  have t2 : ‖X2‖ ≤ ∑ k ∈ Ico (m + 1) K, ‖v k‖ * ‖(1 + A k)⁻¹ - (1 + A (k - 1))⁻¹‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
  have e : X1 - (v K - v m) + (1 + A (K - 1))⁻¹ * v K - (1 + A m)⁻¹ * v m - X2
      = X1 + ((1 + A (K - 1))⁻¹ * v K - v K) + (v m - (1 + A m)⁻¹ * v m) - X2 := by ring
  rw [e]
  have n1 := norm_sub_le (X1 + ((1 + A (K - 1))⁻¹ * v K - v K) + (v m - (1 + A m)⁻¹ * v m)) X2
  have n2 := norm_add_le (X1 + ((1 + A (K - 1))⁻¹ * v K - v K)) (v m - (1 + A m)⁻¹ * v m)
  have n3 := norm_add_le X1 ((1 + A (K - 1))⁻¹ * v K - v K)
  have n4 := norm_sub_le ((1 + A (K - 1))⁻¹ * v K) (v K)
  have n5 := norm_sub_le (v m) ((1 + A m)⁻¹ * v m)
  rw [norm_mul] at n4 n5
  nlinarith

end Cvs.Upstream.RecursionFrozenForcingSum
