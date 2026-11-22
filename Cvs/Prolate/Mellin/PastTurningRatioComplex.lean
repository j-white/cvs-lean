import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.FrozenRootCanonicalLog
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.NearRegionBetaStep
import Cvs.Prolate.Mellin.PastTurningCanonicalLog
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.PastTurningErrorsSummed
import Cvs.Prolate.Mellin.PastTurningForcingSum
import Cvs.Prolate.Mellin.PastTurningPhaseSum
import Cvs.Prolate.Mellin.PastTurningRootSizes
import Cvs.Prolate.Mellin.PastTurningStepErrors
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Upstream.ComplexArsinhStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ground law ratio along one line past the turning point, in complex form

On the region of Cvs.Prolate.Mellin.PastTurningContraction, `exp g_L = ρ*`, so `P(s₀) = P(s_K) exp(Σ_{k<K} (log(1 + v_k) − g_L(s_k)))` exactly. With
`Ψ(s) = ½Ĝ(s + 3/2) − ½ĝ(s + 3/2) − ½ log p(s) + ½ log(1 + r(s))`, Cvs.Prolate.Mellin.PastTurningErrorsSummed, Cvs.Prolate.Mellin.PastTurningForcingSum, Cvs.Prolate.Mellin.PastTurningCanonicalLog and Cvs.Prolate.Mellin.PastTurningPhaseSum give
`P(s₀) = P(s_K) exp(Ψ(s₀) − Ψ(s_K) + δ)` with `|δ| ≤ E_U(ε, c) + (1 + 4/√ε)|v_K|`.
-/

noncomputable section

open Complex Finset

namespace Cvs.Prolate.Mellin.PastTurningRatioComplex

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq omega omega_sq tau zeta rhoStar)
open Cvs.Prolate.Mellin.NearRegionBetaStep (betaf)
open Cvs.Prolate.Mellin.TrueRatioDownwardStep (Pk vk sk_succ)
open Cvs.Upstream.ComplexArsinhStrip (ash)
open Cvs.Prolate.Mellin.WkbPhaseAntiderivative (Gh gh csqrt_eq_of_sq)
open Cvs.Prolate.Mellin.FrozenRootCanonicalLog (tau0 gL)
open Cvs.Prolate.Mellin.FrozenForcingIdentities (rr pp)
open Cvs.Prolate.Mellin.PastTurningContraction (Up)

variable {ε c χ : ℝ} {s : ℂ}

theorem Up.zeta_tau0 (h : Up ε c χ s) : csqrt (tau0 s ^ 2 + 1) - tau0 s = (s + 2) / omega s := by
  have hω := h.omega_ne
  have hsq := omega_sq h.m_ne
  have hcs : csqrt (tau0 s ^ 2 + 1) = (s + 3 / 2) / omega s := by
    apply csqrt_eq_of_sq
    · unfold tau0; field_simp; linear_combination (-4) * hsq
    · have hd : (s + 3 / 2) / omega s = 1 - (omega s - (s + 3 / 2)) / omega s := by field_simp; ring
      rw [hd]
      have hb : ‖(omega s - (s + 3 / 2)) / omega s‖ ≤ 1 / 15 := by
        rw [norm_div, div_le_div_iff₀ (norm_pos_iff.mpr hω) (by norm_num)]
        have := h.norm_omega_sub; have := Cvs.Prolate.Mellin.PastTurningCanonicalLog.Up.norm_omega_ge' h; have := h.norm_m_ge; nlinarith
      have := Complex.abs_re_le_norm ((omega s - (s + 3 / 2)) / omega s)
      simp only [Complex.sub_re, Complex.one_re]
      have := abs_le.mp (this.trans hb); linarith
  rw [hcs]; unfold tau0; field_simp; ring

/-- **`exp g_L = ρ*`** past the turning point. -/
theorem Up.exp_gL (h : Up ε c χ s) : Complex.exp (gL c χ s) = rhoStar c χ s := by
  have hτ := h.re_tau_pos
  have e1 : Complex.exp (-ash (tau c χ s)) = csqrt (tau c χ s ^ 2 + 1) - tau c χ s := by
    rw [Complex.exp_neg]
    unfold ash
    rw [Complex.exp_log (slitPlane_ne_zero (Cvs.Prolate.Mellin.PastTurningCanonicalLog.add_csqrt_mem hτ))]
    have hq := slitPlane_ne_zero (Cvs.Prolate.Mellin.PastTurningCanonicalLog.add_csqrt_mem hτ)
    have hsq := csqrt_sq (tau c χ s ^ 2 + 1)
    field_simp
    linear_combination -hsq
  have hτ0 : |(tau0 s).im| < 1 := by
    have h1 := Cvs.Prolate.Mellin.PastTurningCanonicalLog.Up.norm_tau0 h
    have h2 := h.norm_m_ge
    have h3 : ‖tau0 s‖ ≤ 4 / 15 := h1.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    have := Complex.abs_im_le_norm (tau0 s); linarith
  have e2 := Cvs.Upstream.ComplexArsinhStrip.exp_neg_ash hτ0
  rw [Up.zeta_tau0 h] at e2
  have hs2 : s + 2 ≠ 0 := by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne h 2
  have hω := h.omega_ne
  unfold gL rhoStar zeta
  rw [show ash (tau0 s) - ash (tau c χ s) = -ash (tau c χ s) - -ash (tau0 s) by ring, Complex.exp_sub, e1, e2]
  field_simp

variable {s₀ : ℂ}

/-- **The exact telescope**: `P(s₀) = P(s_K) exp(Σ_{k<K} (log(1 + v_k) − g_L(s_k)))`. -/
theorem telescope (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hcb : 6000 / ε ^ 2 ≤ c) (K : ℕ) :
    Pk c s₀ 0 = Pk c s₀ K * Complex.exp (∑ k ∈ range K,
      (Complex.log (1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k) - gL c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k))) := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hb := Cvs.Prolate.Mellin.PastTurningStepErrors.bootstrap h hcb
  induction K with
  | zero => simp
  | succ K ih =>
    rw [ih, Finset.sum_range_succ, Complex.exp_add]
    have hP := (hb K).1
    have hP1 := (hb (K + 1)).1
    have hl := Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h K
    have hρ := Cvs.Prolate.Mellin.PastTurningStepErrors.Up.rho_ne hl
    have he := Up.exp_gL hl
    have hv : 1 + vk c χ s₀ K = rhoStar c χ (s₀ + 2 * K) * Pk c s₀ K / Pk c s₀ (K + 1) := by
      unfold vk; ring
    have hv0 : 1 + vk c χ s₀ K ≠ 0 := by rw [hv]; exact div_ne_zero (mul_ne_zero hρ hP) hP1
    rw [Complex.exp_sub, Complex.exp_log hv0, he, hv]
    field_simp

/-- The line constant `Ψ(s) = ½Ĝ(s + 3/2) − ½ĝ(s + 3/2) − ½ log p(s) + ½ log(1 + r(s))`. -/
def Psi (c χ : ℝ) (s : ℂ) : ℂ :=
  1 / 2 * Gh c (s + 3 / 2) - 1 / 2 * gh c (s + 3 / 2) - 1 / 2 * Complex.log (pp c χ s)
    + 1 / 2 * Complex.log (1 + rr s)

/-- The total error budget past the turning point. -/
def EU (ε c : ℝ) : ℝ :=
  Cvs.Prolate.Mellin.PastTurningErrorsSummed.E1U ε c + Cvs.Prolate.Mellin.PastTurningForcingSum.E2U ε c + 35 / (2 * ε * Real.sqrt ε * c)
    + 189 / (ε * Real.sqrt ε * c)

/-- **The line formula past the turning point.** -/
theorem line_formula (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hcb : 6000 / ε ^ 2 ≤ c) (K : ℕ) (hK : 1 ≤ K) :
    ∃ δ : ℂ, Pk c s₀ 0 = Pk c s₀ K * Complex.exp (Psi c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀
        - Psi c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * K) + δ)
      ∧ ‖δ‖ ≤ EU ε c + (1 + 4 / Real.sqrt ε) * ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ K‖ := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  set S := ∑ k ∈ range K, (Complex.log (1 + vk c χ s₀ k) - gL c χ (s₀ + 2 * k))
  refine ⟨S - (Psi c χ s₀ - Psi c χ (s₀ + 2 * K)), ?_, ?_⟩
  · rw [telescope h hcb K]
    change Pk c s₀ K * Complex.exp S = _
    exact congrArg (Pk c s₀ K * ·) (congrArg Complex.exp (by ring))
  -- the four pieces
  have e1 := Cvs.Prolate.Mellin.PastTurningErrorsSummed.sum_log_sub_le h hcb K hK
  have e2 := Cvs.Prolate.Mellin.PastTurningForcingSum.sum_betaf h hcb K
  have e3 := Cvs.Prolate.Mellin.PastTurningCanonicalLog.sum_gL_sub_gh_le h K
  have hx : 2 ≤ (s₀ + 3 / 2).re := by simp; linarith [h.hre]
  have hy : (2 + ε) * c ≤ (s₀ + 3 / 2).im := by simp; exact h.him
  have e4 := Cvs.Prolate.Mellin.PastTurningPhaseSum.norm_sum_gh_sub_le h.hε h.hε1 h.hc hx hy K
  rw [← Finset.range_eq_Ico] at e1
  have ek : ∀ k : ℕ, s₀ + 3 / 2 + 2 * (k : ℂ) = s₀ + 2 * k + 3 / 2 := fun k => by ring
  simp only [ek] at e4
  have hsum3 : ‖∑ k ∈ range K, (gL c χ (s₀ + 2 * k) - gh c (s₀ + 2 * k + 3 / 2))‖
      ≤ 35 / (2 * ε * Real.sqrt ε * c) := (norm_sum_le _ _).trans e3
  -- the decomposition
  have hdec : S - (Psi c χ s₀ - Psi c χ (s₀ + 2 * K))
      = (∑ k ∈ range K, (Complex.log (1 + vk c χ s₀ k) - betaf c χ (s₀ + 2 * (k : ℂ))))
        + (∑ k ∈ range K, betaf c χ (s₀ + 2 * k)
            - 1 / 2 * (Complex.log (pp c χ (s₀ + 2 * K)) - Complex.log (pp c χ (s₀ + 2 * (0 : ℕ))))
            + 1 / 2 * (Complex.log (1 + rr (s₀ + 2 * K)) - Complex.log (1 + rr (s₀ + 2 * (0 : ℕ)))))
        - (∑ k ∈ range K, (gL c χ (s₀ + 2 * k) - gh c (s₀ + 2 * k + 3 / 2)))
        - (∑ k ∈ range K, gh c (s₀ + 2 * k + 3 / 2) - (1 / 2 * (Gh c (s₀ + 2 * K + 3 / 2) - Gh c (s₀ + 3 / 2))
            + 1 / 2 * (gh c (s₀ + 3 / 2) - gh c (s₀ + 2 * K + 3 / 2)))) := by
    simp only [S, Psi, Finset.sum_sub_distrib]
    push_cast
    ring_nf
  rw [hdec]
  unfold EU
  set a1 := ∑ k ∈ range K, (Complex.log (1 + vk c χ s₀ k) - betaf c χ (s₀ + 2 * (k : ℂ)))
  set a2 := ∑ k ∈ range K, betaf c χ (s₀ + 2 * k)
            - 1 / 2 * (Complex.log (pp c χ (s₀ + 2 * K)) - Complex.log (pp c χ (s₀ + 2 * (0 : ℕ))))
            + 1 / 2 * (Complex.log (1 + rr (s₀ + 2 * K)) - Complex.log (1 + rr (s₀ + 2 * (0 : ℕ))))
  set a3 := ∑ k ∈ range K, (gL c χ (s₀ + 2 * k) - gh c (s₀ + 2 * k + 3 / 2))
  set a4 := ∑ k ∈ range K, gh c (s₀ + 2 * k + 3 / 2) - (1 / 2 * (Gh c (s₀ + 2 * K + 3 / 2) - Gh c (s₀ + 3 / 2))
            + 1 / 2 * (gh c (s₀ + 3 / 2) - gh c (s₀ + 2 * K + 3 / 2)))
  have t : ‖a1 + a2 - a3 - a4‖ ≤ ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖a4‖ := by
    have := norm_sub_le (a1 + a2 - a3) a4
    have := norm_sub_le (a1 + a2) a3
    have := norm_add_le a1 a2
    linarith
  have e4' : ‖a4‖ ≤ 189 / (ε * Real.sqrt ε * c) := e4
  linarith

end Cvs.Prolate.Mellin.PastTurningRatioComplex
