import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.FrozenForcingLineSum
import Cvs.Prolate.Mellin.FrozenRootCanonicalLog
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootLogErrorSum
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.GroundRatioLineModulus
import Cvs.Prolate.Mellin.GroundRatioStepErrors
import Cvs.Prolate.Mellin.NearRegionBetaStep
import Cvs.Prolate.Mellin.NearRegionForcingSize
import Cvs.Prolate.Mellin.PastTurningRatioComplex
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum
import Cvs.Upstream.ComplexArsinhStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ground law ratio along the real line, in complex form

At real `x ≥ ½`, `ω`, `τ`, `ζ` and `ρ*` are real, so `β` is real and `p ≥ 1`, `1 + r > 0`; the imaginary part of
the forcing telescope vanishes and its real part is `FrozenForcingLineSum`'s. With Cvs.Prolate.Mellin.GroundRatioStepErrors, Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum and Cvs.Prolate.Mellin.FrozenRootLogErrorSum, on the line `½ + 2k`:
`P(½) = P(½ + 2K) exp(Ψ(½) − Ψ(½ + 2K) + δ)` with `|δ| ≤ E(ε, c) + (1 + 12/√ε)|v_K|`.
-/

noncomputable section

open Complex Finset

namespace Cvs.Prolate.Mellin.RealLineRatioComplex

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)
open Cvs.Prolate.Mellin.ForcingSmallBound (Af Bf)
open Cvs.Prolate.Mellin.NearRegionBetaStep (betaf)
open Cvs.Prolate.Mellin.TrueRatioDownwardStep (Pk vk)
open Cvs.Prolate.Mellin.GroundRatioStepErrors (Std)
open Cvs.Upstream.ComplexArsinhStrip (csqrt_ofReal)
open Cvs.Prolate.Mellin.WkbPhaseAntiderivative (Gh gh)
open Cvs.Prolate.Mellin.FrozenRootCanonicalLog (gL)
open Cvs.Prolate.Mellin.FrozenForcingIdentities (rr pp)
open Cvs.Prolate.Mellin.PastTurningRatioComplex (Psi)

variable {c χ : ℝ}

theorem omega_real {x : ℝ} (hx : 0 ≤ x) :
    omega (x : ℂ) = (((x + 3 / 2) * Real.sqrt (1 - 1 / (4 * (x + 3 / 2) ^ 2)) : ℝ) : ℂ) := by
  have h : (1 : ℂ) - 1 / (4 * ((x : ℂ) + 3 / 2) ^ 2) = ((1 - 1 / (4 * (x + 3 / 2) ^ 2) : ℝ) : ℂ) := by push_cast; ring
  have hnn : 0 ≤ 1 - 1 / (4 * (x + 3 / 2) ^ 2) := by
    rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  unfold omega
  rw [h, csqrt_ofReal hnn]; push_cast; ring

theorem exists_real_rho (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) : ∃ r : ℝ, rhoStar c χ (x : ℂ) = r := by
  obtain ⟨w, hω⟩ : ∃ w : ℝ, omega (x : ℂ) = (w : ℂ) := ⟨_, omega_real hx⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, tau c χ (x : ℂ) = (t : ℂ) :=
    ⟨(w - χ / w) / (2 * c), by unfold tau; rw [hω]; push_cast; ring⟩
  have hz : zeta c χ (x : ℂ) = ((Real.sqrt (t ^ 2 + 1) - t : ℝ) : ℂ) := by
    unfold zeta
    rw [ht, show (t : ℂ) ^ 2 + 1 = ((t ^ 2 + 1 : ℝ) : ℂ) by push_cast; ring, csqrt_ofReal (by positivity)]
    push_cast; ring
  refine ⟨w * (Real.sqrt (t ^ 2 + 1) - t) / (x + 2), ?_⟩
  unfold rhoStar
  rw [hω, hz]; push_cast; ring

theorem im_log_of_real_pos {y : ℝ} (hy : 0 < y) : (Complex.log (y : ℂ)).im = 0 := by
  rw [← Complex.ofReal_log hy.le]; simp

theorem betaf_im (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) : (betaf c χ (x : ℂ)).im = 0 := by
  obtain ⟨a, ha⟩ := exists_real_rho (χ := χ) hc hx
  obtain ⟨b, hb⟩ := exists_real_rho (χ := χ) hc (x := x + 2) (by linarith)
  push_cast at hb
  unfold betaf Bf Af
  rw [ha, hb]
  have : ((x : ℂ) + 2) * a * (b - a) / ((x : ℂ) + 1) / (1 + ((x : ℂ) + 2) * a * b / ((x : ℂ) + 1))
      = (((x + 2) * a * (b - a) / (x + 1) / (1 + (x + 2) * a * b / (x + 1)) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_im]

theorem pp_eq (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) : ∃ y : ℝ, 1 ≤ y ∧ pp c χ (x : ℂ) = y := by
  obtain ⟨a, ha⟩ := exists_real_rho (χ := χ) hc hx
  refine ⟨1 + (x + 2) / (x + 1) * a ^ 2, by have : 0 ≤ (x + 2) / (x + 1) * a ^ 2 := by positivity
                                            linarith, ?_⟩
  unfold pp rr; rw [ha]; push_cast; ring

theorem im_log_pp (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) : (Complex.log (pp c χ (x : ℂ))).im = 0 := by
  obtain ⟨y, hy, he⟩ := pp_eq (χ := χ) hc hx
  rw [he]; exact im_log_of_real_pos (by linarith)

theorem im_log_one_add_rr {x : ℝ} (hx : 0 ≤ x) : (Complex.log (1 + rr (x : ℂ))).im = 0 := by
  have : 1 + rr (x : ℂ) = ((1 + (x + 2) / (x + 1) : ℝ) : ℂ) := by unfold rr; push_cast; ring
  rw [this]; exact im_log_of_real_pos (by positivity)

variable {ε : ℝ}

/-- **The exact telescope on a line of the strip.** -/
theorem telescope (S : Std ε c (1 / 2 : ℂ)) (K : ℕ) :
    Pk c (1 / 2 : ℂ) 0 = Pk c (1 / 2 : ℂ) K * Complex.exp (∑ k ∈ range K,
      (Complex.log (1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2 : ℂ) k) - gL c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + 2 * k))) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [ih, Finset.sum_range_succ, Complex.exp_add]
    have hP := (S.profile K).1
    have hP1 := (S.profile (K + 1)).1
    have hl := Cvs.Prolate.Mellin.StepAmplification.hyp_line S.h K
    have hρ := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.rho_ne hl
    have he := Cvs.Prolate.Mellin.FrozenRootCanonicalLog.Hyp.exp_gL hl
    have hv : 1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2 : ℂ) K
        = rhoStar c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + 2 * K) * Pk c (1 / 2 : ℂ) K / Pk c (1 / 2 : ℂ) (K + 1) := by
      unfold vk; ring
    have hv0 : 1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2 : ℂ) K ≠ 0 := by
      rw [hv]; exact div_ne_zero (mul_ne_zero hρ hP) hP1
    rw [Complex.exp_sub, Complex.exp_log hv0, he, hv]
    set q := rhoStar c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + 2 * K)
    field_simp

/-- **The line formula on the real line.** -/
theorem line_formula (S : Std ε c (1 / 2 : ℂ)) (hc5 : 100000 / ε ^ 2 ≤ c) (K : ℕ)
    (hK : Cvs.Prolate.Mellin.NearRegionForcingSize.Jn c (1 / 2 : ℂ) + 1 ≤ K) :
    ∃ δ : ℂ, Pk c (1 / 2 : ℂ) 0 = Pk c (1 / 2 : ℂ) K * Complex.exp (Psi c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2 : ℂ)
        - Psi c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + 2 * K) + δ)
      ∧ ‖δ‖ ≤ Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot ε c + (1 + 12 / Real.sqrt ε) * ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2 : ℂ) K‖ := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  set s₀ : ℂ := 1 / 2
  have h := S.h
  have hc := h.c_pos
  have hε := h.hε
  have hε4 : ε ≤ 1 / 4 := by linarith [S.hε16]
  set X := ∑ k ∈ range K, (Complex.log (1 + vk c χ s₀ k) - gL c χ (s₀ + 2 * k))
  refine ⟨X - (Psi c χ s₀ - Psi c χ (s₀ + 2 * K)), ?_, ?_⟩
  · rw [telescope S K]; exact congrArg (fun z => Pk c s₀ K * Complex.exp z) (by ring)
  have e1 := S.sum_log_sub_le K hK
  have e2 := Cvs.Prolate.Mellin.FrozenForcingLineSum.Hyp.sum_re_betaf h hε4 hc5 K
  have e3 := Cvs.Prolate.Mellin.FrozenRootLogErrorSum.Hyp.sum_gL_sub_gh_le h hε4 K
  have hx : 2 ≤ (s₀ + 3 / 2).re := by simp [s₀]; norm_num
  have hy : |(s₀ + 3 / 2).im| ≤ (2 - ε) * c := by
    simp [s₀]; nlinarith [h.c_pos]
  have e4 := Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum.norm_sum_gh_sub_le hε h.hε1 h.hc hx hy K
  rw [← Finset.range_eq_Ico] at e1
  have ek : ∀ k : ℕ, s₀ + 3 / 2 + 2 * (k : ℂ) = s₀ + 2 * k + 3 / 2 := fun k => by ring
  simp only [ek] at e4
  set a1 := ∑ k ∈ range K, (Complex.log (1 + vk c χ s₀ k) - betaf c χ (s₀ + 2 * (k : ℂ)))
  set a2 := ∑ k ∈ range K, betaf c χ (s₀ + 2 * k)
            - 1 / 2 * (Complex.log (pp c χ (s₀ + 2 * K)) - Complex.log (pp c χ (s₀ + 2 * (0 : ℕ))))
            + 1 / 2 * (Complex.log (1 + rr (s₀ + 2 * K)) - Complex.log (1 + rr (s₀ + 2 * (0 : ℕ))))
  set a3 := ∑ k ∈ range K, (gL c χ (s₀ + 2 * k) - gh c (s₀ + 2 * k + 3 / 2))
  set a4 := ∑ k ∈ range K, gh c (s₀ + 2 * k + 3 / 2) - (1 / 2 * (Gh c (s₀ + 2 * K + 3 / 2) - Gh c (s₀ + 3 / 2))
            + 1 / 2 * (gh c (s₀ + 3 / 2) - gh c (s₀ + 2 * K + 3 / 2)))
  have hdec : X - (Psi c χ s₀ - Psi c χ (s₀ + 2 * K)) = a1 + a2 - a3 - a4 := by
    simp only [X, a1, a2, a3, a4, Psi, Finset.sum_sub_distrib]
    push_cast
    ring
  rw [hdec]
  -- `a2` is real
  have hreal : ∀ k : ℕ, s₀ + 2 * (k : ℂ) = (((1 / 2 : ℝ) + 2 * k : ℝ) : ℂ) := fun k => by
    simp only [s₀]; push_cast; ring
  have hk0 : ∀ k : ℕ, (0 : ℝ) ≤ 1 / 2 + 2 * k := fun k => by positivity
  have him2 : a2.im = 0 := by
    simp only [a2, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.im_sum]
    have hb : ∀ k ∈ range K, (betaf c χ (s₀ + 2 * (k : ℂ))).im = 0 := fun k _ => by
      rw [hreal k]; exact betaf_im hc (hk0 k)
    rw [Finset.sum_eq_zero hb]
    rw [hreal K, hreal 0, im_log_pp hc (hk0 K), im_log_pp hc (hk0 0), im_log_one_add_rr (hk0 K),
      im_log_one_add_rr (hk0 0)]
    simp
  have hre2 : a2.re = ∑ k ∈ range K, (betaf c χ (s₀ + 2 * k)).re
        - 1 / 2 * (Real.log ‖pp c χ (s₀ + 2 * K)‖ - Real.log ‖pp c χ (s₀ + 2 * (0 : ℕ))‖)
        + 1 / 2 * (Real.log ‖1 + rr (s₀ + 2 * K)‖ - Real.log ‖1 + rr (s₀ + 2 * (0 : ℕ))‖) := by
    simp only [a2, Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.mul_re, Complex.log_re, Complex.log_im]
    norm_num
  have ha2 : ‖a2‖ ≤ Cvs.Prolate.Mellin.FrozenForcingLineSum.E2 ε c := by
    have : ‖a2‖ = |a2.re| := by
      rw [← Complex.re_add_im a2, him2]; simp
    rw [this, hre2]; exact e2
  have ha3 : ‖a3‖ ≤ 160 / (ε / 4) ^ 5 * ((1 + Real.log (1 + c / 2)) / (2 * c)) := (norm_sum_le _ _).trans e3
  have t : ‖a1 + a2 - a3 - a4‖ ≤ ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖a4‖ := by
    have := norm_sub_le (a1 + a2 - a3) a4
    have := norm_sub_le (a1 + a2) a3
    have := norm_add_le a1 a2
    linarith
  have e4' : ‖a4‖ ≤ 42 * (1 + 2 / Real.sqrt (3 * ε)) / (Real.sqrt (3 * ε) * c) := e4
  unfold Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot
  linarith

end Cvs.Prolate.Mellin.RealLineRatioComplex
