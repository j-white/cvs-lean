import Mathlib
import Cvs.Upstream.AbelSummationRecursion

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The profiled bootstrap step for a first-order recursion

For `v_j = −a_j v_{j+1} + β_j(1 + a_j) + a_j v_{j+1}²/(1 + v_{j+1})` with `‖a_i‖ ≤ exp(g_i − d_i)`, the running
product factors as `‖π_{k,j}‖ ≤ (γ_k/γ_j) δ_{k,j}`; a profile `|v_j| ≤ 2γ_jΛ₁` above `k` then propagates to `k`.
-/

noncomputable section

open Finset

namespace Cvs.Upstream.ProfiledBootstrapStep

open Cvs.Upstream.AbelSummationRecursion

/-- **Factored product bound**: `‖π_{k,j}‖ ≤ exp(Σ_{k≤i<j} g_i) · exp(−Σ_{k≤i<j} d_i)`. -/
theorem norm_prodNeg_le {a : ℕ → ℂ} {g d : ℕ → ℝ} {k j : ℕ} (ha : ∀ i ∈ Ico k j, ‖a i‖ ≤ Real.exp (g i - d i)) :
    ‖prodNeg a k j‖ ≤ Real.exp (∑ i ∈ Ico k j, g i) * Real.exp (-∑ i ∈ Ico k j, d i) := by
  unfold prodNeg
  rw [norm_prod, ← Real.exp_add, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i hi => ?_
  rw [norm_neg, ← sub_eq_add_neg]; exact ha i hi

/-- The profile `γ_k = exp(Σ_{k≤i<J} g_i)` satisfies `exp(Σ_{k≤i<j} g_i) = γ_k/γ_j` for `k ≤ j ≤ J`. -/
theorem exp_sum_Ico_eq {g : ℕ → ℝ} {k j J : ℕ} (hkj : k ≤ j) (hjJ : j ≤ J) :
    Real.exp (∑ i ∈ Ico k j, g i) = Real.exp (∑ i ∈ Ico k J, g i) / Real.exp (∑ i ∈ Ico j J, g i) := by
  rw [← Real.exp_sub, ← Finset.sum_Ico_consecutive g hkj hjJ]; ring_nf

/-- **The profiled step.** -/
theorem profile_step {a β v : ℕ → ℂ} {γ δ : ℕ → ℝ} {k J : ℕ} {Bs DS VJ Γ T Λ₁ : ℝ} (hkJ : k < J)
    (hrec : ∀ j < J, k ≤ j → v j = -a j * v (j + 1) + β j * (1 + a j) + a j * v (j + 1) ^ 2 / (1 + v (j + 1)))
    (hπ : ∀ j, k ≤ j → j ≤ J → ‖prodNeg a k j‖ ≤ γ k / γ j * δ j)
    (hγ1 : ∀ j, 1 ≤ γ j) (hγΓ : ∀ j, γ j ≤ Γ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hT : ∑ j ∈ Ico k J, δ (j + 1) ≤ T)
    (hβ : ∀ j, k ≤ j → j < J → ‖β j‖ ≤ Bs) (hDS : ∑ j ∈ Ico (k + 1) J, ‖β j - β (j - 1)‖ ≤ DS)
    (hvJ : ‖v J‖ ≤ VJ) (hΛ : 2 * Bs + DS + VJ ≤ Λ₁)
    (hsmall : 40 / 9 * Λ₁ * Γ * T ≤ 1) (hsmall2 : 2 * Γ * Λ₁ ≤ 1 / 10)
    (hv : ∀ j, k < j → j ≤ J → ‖v j‖ ≤ 2 * γ j * Λ₁) :
    ‖v k‖ ≤ 2 * γ k * Λ₁ := by
  have hγk := hγ1 k
  have hγpos : ∀ j, 0 < γ j := fun j => lt_of_lt_of_le one_pos (hγ1 j)
  have hΛ0 : 0 ≤ Λ₁ := by
    have := hβ k le_rfl hkJ; have := norm_nonneg (v J)
    have := (norm_nonneg _).trans (hβ k le_rfl hkJ)
    have : 0 ≤ DS := (Finset.sum_nonneg fun j _ => norm_nonneg _).trans hDS
    linarith
  have hab := norm_le_abel (a := a) (β := β) (n := fun j => a j * v (j + 1) ^ 2 / (1 + v (j + 1))) (v := v) hkJ
    (fun j hj hkj => hrec j hj hkj)
  -- the ratio bound
  have hr : ∀ j, k ≤ j → j ≤ J → ‖prodNeg a k j‖ ≤ γ k := fun j h1 h2 => by
    refine (hπ j h1 h2).trans ?_
    have : γ k / γ j ≤ γ k := div_le_self (by linarith) (hγ1 j)
    calc γ k / γ j * δ j ≤ γ k * 1 := mul_le_mul this (hδ1 j) (hδ0 j) (by linarith)
      _ = γ k := mul_one _
  -- each term
  have t1 : ‖β k‖ ≤ γ k * Bs := by
    have := hβ k le_rfl hkJ; nlinarith [norm_nonneg (β k)]
  have hBs0 : 0 ≤ Bs := (norm_nonneg _).trans (hβ k le_rfl hkJ)
  have t2 : ‖prodNeg a k J‖ * ‖β (J - 1)‖ ≤ γ k * Bs :=
    mul_le_mul (hr J hkJ.le le_rfl) (hβ (J - 1) (by omega) (by omega)) (norm_nonneg _) (by linarith)
  have t3 : ∑ j ∈ Ico (k + 1) J, ‖prodNeg a k j‖ * ‖β j - β (j - 1)‖ ≤ γ k * DS := by
    calc _ ≤ ∑ j ∈ Ico (k + 1) J, γ k * ‖β j - β (j - 1)‖ := Finset.sum_le_sum fun j hj => by
            rw [Finset.mem_Ico] at hj
            exact mul_le_mul_of_nonneg_right (hr j (by omega) hj.2.le) (norm_nonneg _)
      _ = γ k * ∑ j ∈ Ico (k + 1) J, ‖β j - β (j - 1)‖ := by rw [Finset.mul_sum]
      _ ≤ γ k * DS := mul_le_mul_of_nonneg_left hDS (by linarith)
  have t5 : ‖prodNeg a k J‖ * ‖v J‖ ≤ γ k * VJ :=
    mul_le_mul (hr J hkJ.le le_rfl) hvJ (norm_nonneg _) (by linarith)
  have t4 : ∑ j ∈ Ico k J, ‖prodNeg a k j‖ * ‖a j * v (j + 1) ^ 2 / (1 + v (j + 1))‖ ≤ γ k * Λ₁ := by
    have hterm : ∀ j ∈ Ico k J, ‖prodNeg a k j‖ * ‖a j * v (j + 1) ^ 2 / (1 + v (j + 1))‖
        ≤ 40 / 9 * γ k * Γ * Λ₁ ^ 2 * δ (j + 1) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hvj := hv (j + 1) (by omega) (by omega)
      have hγj := hγΓ (j + 1)
      have hsm : ‖v (j + 1)‖ ≤ 1 / 10 := by nlinarith [hγ1 (j + 1)]
      have h1v : 9 / 10 ≤ ‖1 + v (j + 1)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (-v (j + 1))
        rw [norm_neg, sub_neg_eq_add, norm_one] at this; linarith
      have hpj : ‖prodNeg a k j‖ * ‖a j‖ = ‖prodNeg a k (j + 1)‖ := by
        rw [prodNeg_succ a hj.1, norm_mul, norm_neg]
      have hπj := hπ (j + 1) (by omega) (by omega)
      have e : ‖prodNeg a k j‖ * ‖a j * v (j + 1) ^ 2 / (1 + v (j + 1))‖
          = ‖prodNeg a k (j + 1)‖ * (‖v (j + 1)‖ ^ 2 / ‖1 + v (j + 1)‖) := by
        rw [← hpj, norm_div, norm_mul, norm_pow]; ring
      rw [e]
      have hq : ‖v (j + 1)‖ ^ 2 / ‖1 + v (j + 1)‖ ≤ 10 / 9 * (2 * γ (j + 1) * Λ₁) ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        have : ‖v (j + 1)‖ ^ 2 ≤ (2 * γ (j + 1) * Λ₁) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvj 2
        nlinarith [sq_nonneg (2 * γ (j + 1) * Λ₁)]
      have hγjp := hγpos (j + 1)
      calc ‖prodNeg a k (j + 1)‖ * (‖v (j + 1)‖ ^ 2 / ‖1 + v (j + 1)‖)
          ≤ γ k / γ (j + 1) * δ (j + 1) * (10 / 9 * (2 * γ (j + 1) * Λ₁) ^ 2) :=
            mul_le_mul hπj hq (by positivity) (by have := hδ0 (j + 1); positivity)
        _ = 40 / 9 * γ k * γ (j + 1) * Λ₁ ^ 2 * δ (j + 1) := by field_simp; ring
        _ ≤ 40 / 9 * γ k * Γ * Λ₁ ^ 2 * δ (j + 1) := by
            have := hδ0 (j + 1)
            gcongr
    calc _ ≤ ∑ j ∈ Ico k J, 40 / 9 * γ k * Γ * Λ₁ ^ 2 * δ (j + 1) := Finset.sum_le_sum hterm
      _ = 40 / 9 * γ k * Γ * Λ₁ ^ 2 * ∑ j ∈ Ico k J, δ (j + 1) := by rw [Finset.mul_sum]
      _ ≤ 40 / 9 * γ k * Γ * Λ₁ ^ 2 * T := by
          have hΓ0 : 0 ≤ Γ := (hγ1 0).trans' zero_le_one |>.trans (hγΓ 0)
          exact mul_le_mul_of_nonneg_left hT (by positivity)
      _ = γ k * Λ₁ * (40 / 9 * Λ₁ * Γ * T) := by ring
      _ ≤ γ k * Λ₁ * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = γ k * Λ₁ := mul_one _
  have : ‖v k‖ ≤ γ k * (2 * Bs + DS + VJ) + γ k * Λ₁ := by
    have := hab; linarith
  nlinarith

end Cvs.Upstream.ProfiledBootstrapStep
