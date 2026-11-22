import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FarRegionDamping
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Decay of the true step error in the far region

If `|v_k| ≤ q|v_{k+1}| + b_k` for all `k ≥ K₀` with `0 ≤ q < 1`, `b` nonincreasing and nonnegative and `v` bounded, then
`|v_k| ≤ b_k/(1 − q)`. On the line in the far region (`q = 5/6`, `b_k = 1000c²/x_k³`) this gives
`|v_k| ≤ 6000 c²/x_k³`.
-/

noncomputable section

open Finset Filter Topology

namespace Cvs.Prolate.Mellin.FarRegionStepDecay

/-- **Unrolled contraction.** -/
theorem le_of_contract {v b : ℕ → ℝ} {q M : ℝ} {K₀ : ℕ} (hq0 : 0 ≤ q) (hq : q < 1) (hb : ∀ k, K₀ ≤ k → b (k + 1) ≤ b k)
    (hb0 : ∀ k, K₀ ≤ k → 0 ≤ b k) (hM : ∀ k, K₀ ≤ k → v k ≤ M) (hv0 : ∀ k, K₀ ≤ k → 0 ≤ v k)
    (hrec : ∀ k, K₀ ≤ k → v k ≤ q * v (k + 1) + b k) :
    ∀ k, K₀ ≤ k → v k ≤ b k / (1 - q) := by
  intro k hk
  -- v_k ≤ Σ_{n<N} qⁿ b_k + q^N M for all N
  have key : ∀ N, v k ≤ (∑ n ∈ range N, q ^ n) * b k + q ^ N * M := by
    intro N
    induction N generalizing k with
    | zero => simpa using hM k hk
    | succ N ih =>
      have h1 := hrec k hk
      have h2 := ih (k + 1) (by omega)
      have hbk : b (k + 1) ≤ b k := hb k hk
      have hS : 0 ≤ ∑ n ∈ range N, q ^ n := Finset.sum_nonneg fun n _ => pow_nonneg hq0 n
      calc v k ≤ q * v (k + 1) + b k := h1
        _ ≤ q * ((∑ n ∈ range N, q ^ n) * b (k + 1) + q ^ N * M) + b k := by gcongr
        _ ≤ q * ((∑ n ∈ range N, q ^ n) * b k + q ^ N * M) + b k := by gcongr
        _ = (∑ n ∈ range (N + 1), q ^ n) * b k + q ^ (N + 1) * M := by
            have hS : ∑ n ∈ range (N + 1), q ^ n = 1 + q * ∑ n ∈ range N, q ^ n := by
              rw [Finset.sum_range_succ', Finset.mul_sum]
              simp only [pow_succ, pow_zero]
              rw [add_comm]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
            rw [hS]; ring
  have hgeom : ∀ N, (∑ n ∈ range N, q ^ n) * b k ≤ b k / (1 - q) := by
    intro N
    have h1 : (∑ n ∈ range N, q ^ n) * (1 - q) = 1 - q ^ N := geom_sum_mul_neg q N
    have hS : ∑ n ∈ range N, q ^ n ≤ 1 / (1 - q) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith [pow_nonneg hq0 N]
    calc (∑ n ∈ range N, q ^ n) * b k ≤ 1 / (1 - q) * b k := mul_le_mul_of_nonneg_right hS (hb0 k hk)
      _ = b k / (1 - q) := by ring
  have hlim : Tendsto (fun N => (∑ n ∈ range N, q ^ n) * b k + q ^ N * M) atTop
      (𝓝 (b k / (1 - q) + 0 * M)) := by
    refine Tendsto.add ?_ ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const M)
    have := (hasSum_geometric_of_lt_one hq0 hq).tendsto_sum_nat.mul_const (b k)
    rwa [show (1 - q)⁻¹ * b k = b k / (1 - q) by ring] at this
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall key)

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.ForcingSmallBound Cvs.Prolate.Mellin.TrueRatioDownwardStep in
/-- **The far step**: `|v_k| ≤ (5/6)|v_{k+1}| + 1000c²/x_k³` with `x_k = Re s₀ + 2k`. -/
theorem far_step {ε c : ℝ} {s₀ : ℂ} (h : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hε4 : ε ≤ 1 / 4) (hc7 : 7500 ≤ c)
    (K₀ : ℕ) (hK₀ : 2 * c ≤ s₀.re + 2 * K₀) (k : ℕ) (hk : K₀ ≤ k) :
    ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖ ≤ 5 / 6 * ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1)‖
      + 1000 * c ^ 2 / (s₀.re + 2 * k) ^ 3 := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hc := h.c_pos
  have hb := far_bootstrap h hε4 hc7 K₀ hK₀
  obtain ⟨hP1, hv1⟩ := hb (k + 1) (by omega)
  obtain ⟨hP2, _⟩ := hb (k + 2) (by omega)
  have hkh := Cvs.Prolate.Mellin.StepAmplification.hyp_line h k
  have hx : 2 * c ≤ (s₀ + 2 * (k : ℂ)).re := by
    simp; have : (K₀ : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hA := Cvs.Prolate.Mellin.FarRegionDamping.Hyp.far_norm_Af_le hkh hx
  have hB := Cvs.Prolate.Mellin.FarRegionDamping.Hyp.far_norm_Bf_le hkh hε4 hx
  have hre : (s₀ + 2 * (k : ℂ)).re = s₀.re + 2 * k := by simp
  rw [hre] at hB
  have hsm0 : 750 / c ≤ 1 / 10 := by rw [div_le_iff₀ hc]; linarith
  have hv1ne : 1 + vk c χ s₀ (k + 1) ≠ 0 := by
    intro h0
    have : ‖vk c χ s₀ (k + 1)‖ = 1 := by
      rw [show vk c χ s₀ (k + 1) = -1 by linear_combination h0]; simp
    linarith
  have hstep := line_step h k hP1 hP2 hv1ne
  set w := Af c χ (s₀ + 2 * k) * (-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))) + Bf c χ (s₀ + 2 * k)
  have hw : ‖w‖ ≤ 5 / 6 * ‖vk c χ s₀ (k + 1)‖ + 1000 * c ^ 2 / (s₀.re + 2 * k) ^ 3 := by
    have h1 : ‖1 + vk c χ s₀ (k + 1)‖ ≥ 9 / 10 := by
      have := norm_sub_norm_le (1 : ℂ) (-vk c χ s₀ (k + 1))
      rw [norm_neg, sub_neg_eq_add, norm_one] at this; linarith
    have h2 : ‖-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))‖ ≤ 10 / 9 * ‖vk c χ s₀ (k + 1)‖ := by
      rw [norm_div, norm_neg, div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg (vk c χ s₀ (k + 1))]
    calc ‖w‖ ≤ ‖Af c χ (s₀ + 2 * k)‖ * ‖-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))‖
          + ‖Bf c χ (s₀ + 2 * k)‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ 3 / 4 * (10 / 9 * ‖vk c χ s₀ (k + 1)‖) + 1000 * c ^ 2 / (s₀.re + 2 * k) ^ 3 := by gcongr
      _ = _ := by ring
  have ew : 1 + Af c χ (s₀ + 2 * k) * (-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))) + Bf c χ (s₀ + 2 * k)
      = 1 + w := by simp only [w]; ring
  rw [ew] at hstep
  have hP0 := (hb k hk).1
  have hρ := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.rho_ne hkh
  have : vk c χ s₀ k = w := by
    unfold vk
    rw [hstep]; field_simp; ring
  rw [this]; exact hw

open Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.TrueRatioDownwardStep in
/-- **Decay of the true step error in the far region**: `|v_k| ≤ 6000c²/x_k³` with `x_k = Re s₀ + 2k`. -/
theorem far_decay {ε c : ℝ} {s₀ : ℂ} (h : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hε4 : ε ≤ 1 / 4) (hc7 : 7500 ≤ c)
    (K₀ : ℕ) (hK₀ : 2 * c ≤ s₀.re + 2 * K₀) (k : ℕ) (hk : K₀ ≤ k) :
    ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖ ≤ 6000 * c ^ 2 / (s₀.re + 2 * k) ^ 3 := by
  have hc := h.c_pos
  have hxpos : ∀ j, K₀ ≤ j → 0 < s₀.re + 2 * (j : ℝ) := fun j hj => by
    have : (K₀ : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have := le_of_contract (v := fun j => ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ j‖)
    (b := fun j => 1000 * c ^ 2 / (s₀.re + 2 * j) ^ 3) (q := 5 / 6) (M := 750 / c) (K₀ := K₀)
    (by norm_num) (by norm_num)
    (fun j hj => by
      have h0 := hxpos j hj
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      push_cast; exact pow_le_pow_left₀ h0.le (by linarith) 3)
    (fun j hj => by have := hxpos j hj; positivity)
    (fun j hj => (far_bootstrap h hε4 hc7 K₀ hK₀ j hj).2) (fun j _ => norm_nonneg _)
    (fun j hj => far_step h hε4 hc7 K₀ hK₀ j hj) k hk
  refine this.trans (le_of_eq ?_)
  ring

end Cvs.Prolate.Mellin.FarRegionStepDecay
