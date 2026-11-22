import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FarRegionDamping
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Prolate.Mellin.RungThreeTermRecurrence
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.TrueRatioMatchesFrozen
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The downward step of the true ratio

If `(s+1)P(s) = qP(s+2) + (s+2)P(s+4)`, `ρ₀` is a nonzero root of `(s+2)ρ² + qρ − (s+1)`, `ρ₁ ≠ 0`, `P(s+2), P(s+4) ≠ 0`
and `v₁ = ρ₁P(s+2)/P(s+4) − 1 ≠ −1`, then `ρ₀P(s) = P(s+2)(1 + A·u + B)` with `u = −v₁/(1 + v₁)`,
`A = (s+2)ρ₀ρ₁/(s+1)` and `B = (s+2)ρ₀(ρ₁ − ρ₀)/(s+1)`.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Prolate.Mellin.TrueRatioDownwardStep

/-- **The downward step** (pure algebra). -/
theorem down_step {s q ρ₀ ρ₁ P₀ P₂ P₄ : ℂ} (hs1 : s + 1 ≠ 0) (hρ₀ : ρ₀ ≠ 0) (hρ₁ : ρ₁ ≠ 0) (hP₂ : P₂ ≠ 0)
    (hP₄ : P₄ ≠ 0) (hv : ρ₁ * P₂ / P₄ ≠ 0)
    (hrec : (s + 1) * P₀ - q * P₂ - (s + 2) * P₄ = 0)
    (hroot : (s + 2) * ρ₀ ^ 2 + q * ρ₀ - (s + 1) = 0) :
    ρ₀ * P₀ = P₂ * (1 + (s + 2) * ρ₀ * ρ₁ / (s + 1) * (-(ρ₁ * P₂ / P₄ - 1) / (1 + (ρ₁ * P₂ / P₄ - 1)))
      + (s + 2) * ρ₀ * (ρ₁ - ρ₀) / (s + 1)) := by
  have key : P₂ * (1 + (s + 2) * ρ₀ * ρ₁ / (s + 1) * (-(ρ₁ * P₂ / P₄ - 1) / (1 + (ρ₁ * P₂ / P₄ - 1)))
      + (s + 2) * ρ₀ * (ρ₁ - ρ₀) / (s + 1)) = P₂ + (s + 2) * ρ₀ * (P₄ - ρ₀ * P₂) / (s + 1) := by
    have e : 1 + (ρ₁ * P₂ / P₄ - 1) = ρ₁ * P₂ / P₄ := by ring
    rw [e]
    field_simp
    ring
  rw [key, eq_comm, ← sub_eq_zero]
  have : P₂ + (s + 2) * ρ₀ * (P₄ - ρ₀ * P₂) / (s + 1) - ρ₀ * P₀
      = -(ρ₀ * ((s + 1) * P₀ - q * P₂ - (s + 2) * P₄) + P₂ * ((s + 2) * ρ₀ ^ 2 + q * ρ₀ - (s + 1))) / (s + 1) := by
    field_simp; ring
  rw [this, hrec, hroot]; simp

open Cvs.Prolate.Mellin.RungThreeTermRecurrence (mel)
open Cvs.Prolate.Mellin.LawRatioRecurrence (mg lawRatio)
open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (rhoStar)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)
open Cvs.Prolate.Mellin.ForcingSmallBound (Af Bf)

/-- The ground law ratio along the line `s₀ + 2k`. -/
def Pk (c : ℝ) (s₀ : ℂ) (k : ℕ) : ℂ := lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)

/-- The true step error `v_k = ρ*(s_k)P_k/P_{k+1} − 1`. -/
def vk (c χ : ℝ) (s₀ : ℂ) (k : ℕ) : ℂ := rhoStar c χ (s₀ + 2 * k) * Pk c s₀ k / Pk c s₀ (k + 1) - 1

theorem sk_succ (s₀ : ℂ) (k : ℕ) : s₀ + 2 * ((k + 1 : ℕ) : ℂ) = s₀ + 2 * k + 2 := by push_cast; ring

/-- `P_k ≠ 0` eventually. -/
theorem eventually_Pk_ne {c : ℝ} (hc : 0 < c) {s₀ : ℂ} (hs₀ : 0 < s₀.re) : ∀ᶠ k : ℕ in atTop, Pk c s₀ k ≠ 0 := by
  have h1 := Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c hs₀
  have hne : (Cvs.Prolate.EvenRungsByIndex.rung c 0 1 : ℂ) ≠ 0 := by
    exact_mod_cast Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)
  filter_upwards [h1.eventually_ne hne] with k hk
  have hre : 0 < (s₀ + 2 * (k : ℂ)).re := by simp; positivity
  unfold Pk lawRatio
  refine div_ne_zero (fun h0 => hk (by rw [h0, mul_zero])) (Cvs.Prolate.Mellin.LawRatioRecurrence.mg_ne_zero hc hre)

/-- The recurrence of `P` along the line. -/
theorem Pk_rec {c : ℝ} (hc : 0 < c) {s₀ : ℂ} (hs₀ : 0 < s₀.re) (k : ℕ) :
    (s₀ + 2 * k + 1) * Pk c s₀ k - ((s₀ + 2 * k + 1) * (s₀ + 2 * k + 2) - Cvs.Prolate.EvenRungsByIndex.lev c 0) / c * Pk c s₀ (k + 1)
      - (s₀ + 2 * k + 2) * Pk c s₀ (k + 2) = 0 := by
  have hre : 0 < (s₀ + 2 * (k : ℂ)).re := by simp; positivity
  have := Cvs.Prolate.Mellin.LawRatioRecurrence.lawRatio_rung_recurrence hc (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c) hre
  unfold Pk
  rw [sk_succ, show s₀ + 2 * ((k + 2 : ℕ) : ℂ) = s₀ + 2 * k + 4 by push_cast; ring]
  exact this

/-- **One downward step on the line.** If `P_{k+1}, P_{k+2} ≠ 0` and `v_{k+1} ≠ −1`, then
`ρ*(s_k)P_k = P_{k+1}(1 + A(s_k)u + B(s_k))` with `u = −v_{k+1}/(1 + v_{k+1})`. -/
theorem line_step {ε c : ℝ} {s₀ : ℂ} (h : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (k : ℕ)
    (hP1 : Pk c s₀ (k + 1) ≠ 0) (hP2 : Pk c s₀ (k + 2) ≠ 0) (hv : 1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1) ≠ 0) :
    rhoStar c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k) * Pk c s₀ k
      = Pk c s₀ (k + 1) * (1 + Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k)
          * (-vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1) / (1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1)))
          + Bf c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k)) := by
  have hk := Cvs.Prolate.Mellin.StepAmplification.hyp_line h k
  have hk1 := Cvs.Prolate.Mellin.StepAmplification.hyp_line h (k + 1)
  have hc := h.c_pos
  rw [sk_succ] at hk1
  have hrec := Pk_rec hc (by linarith [h.hre]) k
  have hroot := Cvs.Prolate.Mellin.FrozenRootErrorIdentity.rhoStar_root (χ := Cvs.Prolate.EvenRungsByIndex.lev c 0) hc.ne' hk.m_ne hk.s2_ne hk.omega_ne
  have hρ0 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.rho_ne hk
  have hρ1 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.rho_ne hk1
  have hv' : rhoStar c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k + 2) * Pk c s₀ (k + 1) / Pk c s₀ (k + 2) ≠ 0 := by
    intro h0; apply hv; unfold vk; rw [sk_succ, show k + 1 + 1 = k + 2 by ring, h0]; ring
  have := down_step (Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.s1_ne hk) hρ0 hρ1 hP1 hP2 hv' hrec hroot
  unfold vk Af Bf
  rw [sk_succ, show k + 1 + 1 = k + 2 by ring]
  exact this

/-- `v_k → 0` in the `vk` form. -/
theorem tendsto_vk {ε c χ : ℝ} {s₀ : ℂ} (h : Hyp ε c χ s₀) : Tendsto (vk c χ s₀) atTop (𝓝 0) := by
  have := Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_v h
  refine this.congr fun k => ?_
  unfold vk Pk; rw [sk_succ]

/-- **The far-region bootstrap**: for `c ≥ 7500` and `Re s₀ + 2K₀ ≥ 2c`, every `k ≥ K₀` has `P_k ≠ 0` and
`|v_k| ≤ 750/c`. -/
theorem far_bootstrap {ε c : ℝ} {s₀ : ℂ} (h : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hε4 : ε ≤ 1 / 4) (hc7 : 7500 ≤ c)
    (K₀ : ℕ) (hK₀ : 2 * c ≤ s₀.re + 2 * K₀) :
    ∀ k, K₀ ≤ k → Pk c s₀ k ≠ 0 ∧ ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖ ≤ 750 / c := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hc := h.c_pos
  -- the tail
  obtain ⟨K, hK⟩ : ∃ K, ∀ j, K ≤ j → Pk c s₀ j ≠ 0 ∧ ‖vk c χ s₀ j‖ ≤ 750 / c := by
    have e1 := eventually_Pk_ne hc (s₀ := s₀) (by linarith [h.hre])
    have e2 : ∀ᶠ k : ℕ in atTop, ‖vk c χ s₀ k‖ ≤ 750 / c := by
      have := (tendsto_vk h).norm
      rw [norm_zero] at this
      exact this.eventually (ge_mem_nhds (by positivity))
    obtain ⟨K, hK⟩ := (e1.and e2).exists_forall_of_atTop
    exact ⟨K, hK⟩
  -- the step
  have step : ∀ k, K₀ ≤ k → (Pk c s₀ (k + 1) ≠ 0 ∧ ‖vk c χ s₀ (k + 1)‖ ≤ 750 / c) →
      (Pk c s₀ (k + 2) ≠ 0 ∧ ‖vk c χ s₀ (k + 2)‖ ≤ 750 / c) → Pk c s₀ k ≠ 0 ∧ ‖vk c χ s₀ k‖ ≤ 750 / c := by
    intro k hk ⟨hP1, hv1⟩ ⟨hP2, _⟩
    have hkh := Cvs.Prolate.Mellin.StepAmplification.hyp_line h k
    have hx : 2 * c ≤ (s₀ + 2 * (k : ℂ)).re := by
      simp; have : (K₀ : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hA := Cvs.Prolate.Mellin.FarRegionDamping.Hyp.far_norm_Af_le hkh hx
    have hB := Cvs.Prolate.Mellin.FarRegionDamping.Hyp.far_norm_Bf_le hkh hε4 hx
    have hB' : ‖Bf c χ (s₀ + 2 * k)‖ ≤ 125 / c := by
      refine hB.trans ?_
      set x := (s₀ + 2 * (k : ℂ)).re
      have hx0 : 0 < x := by linarith
      rw [div_le_div_iff₀ (by positivity) hc]
      have : (2 * c) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by positivity) hx 3
      nlinarith [pow_pos hc 2]
    have hsm0 : 750 / c ≤ 1 / 10 := by rw [div_le_iff₀ hc]; linarith
    have hv1ne : 1 + vk c χ s₀ (k + 1) ≠ 0 := by
      intro h0
      have : ‖vk c χ s₀ (k + 1)‖ = 1 := by
        rw [show vk c χ s₀ (k + 1) = -1 by linear_combination h0]; simp
      linarith
    have hstep := line_step h k hP1 hP2 hv1ne
    set w := Af c χ (s₀ + 2 * k) * (-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))) + Bf c χ (s₀ + 2 * k)
    have hw : ‖w‖ ≤ 750 / c := by
      have h1 : ‖1 + vk c χ s₀ (k + 1)‖ ≥ 9 / 10 := by
        have := norm_sub_norm_le (1 : ℂ) (-vk c χ s₀ (k + 1))
        rw [norm_neg, sub_neg_eq_add, norm_one] at this; linarith
      have h2 : ‖-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))‖ ≤ 750 / c * (10 / 9) := by
        rw [norm_div, norm_neg, div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg (vk c χ s₀ (k + 1))]
      calc ‖w‖ ≤ ‖Af c χ (s₀ + 2 * k)‖ * ‖-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))‖
            + ‖Bf c χ (s₀ + 2 * k)‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_mul]
        _ ≤ 3 / 4 * (750 / c * (10 / 9)) + 125 / c := by gcongr
        _ = 750 / c := by ring
    have hρ := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.rho_ne hkh
    have ew : 1 + Af c χ (s₀ + 2 * k) * (-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))) + Bf c χ (s₀ + 2 * k)
        = 1 + w := by simp only [w]; ring
    rw [ew] at hstep
    have h1w : 1 + w ≠ 0 := by
      intro h0
      have : ‖w‖ = 1 := by rw [show w = -1 by linear_combination h0]; simp
      linarith
    have hP0 : Pk c s₀ k ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hstep
      exact mul_ne_zero hP1 h1w hstep.symm
    refine ⟨hP0, ?_⟩
    have : vk c χ s₀ k = w := by
      unfold vk
      rw [hstep]; field_simp; ring
    rw [this]; exact hw
  -- downward induction
  have main : ∀ m k, K₀ ≤ k → K ≤ k + m → Pk c s₀ k ≠ 0 ∧ ‖vk c χ s₀ k‖ ≤ 750 / c := by
    intro m
    induction m with
    | zero => intro k _ hk; exact hK k (by simpa using hk)
    | succ m ih =>
      intro k hk hkm
      by_cases hkK : K ≤ k
      · exact hK k hkK
      · exact step k hk (ih (k + 1) (by omega) (by omega)) (ih (k + 2) (by omega) (by omega))
  intro k hk
  exact main K k hk (by omega)

end Cvs.Prolate.Mellin.TrueRatioDownwardStep
