import Mathlib
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The frozen root past the turning point: uniform contraction

For every `t`, `√(t²+1) = a + ib` has `b² ≥ (Im t)² − 1`. If `Re t > 0` and `Im t ≥ 1` then `a, b > 0` and
`R = Re(√(t²+1) t̄) ≥ Im t · √((Im t)² − 1)`, and `|ζ|² = √(4R² + 1) − 2R ≤ 1/(1 + 2R)`. On the region
`Re s ≥ ½`, `Im s ≥ (2 + ε)c` the frozen `τ` has `Re τ > 0` and `Im τ ≥ 1 + ε/4`, so `|ζ|² ≤ 1/(1 + 2√(ε/2))`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.PastTurningContraction

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg omega tau zeta normSq_zeta_eq)
open Cvs.Prolate.Mellin.FrozenRootClosedBounds (csqrt_parts norm_omega_sub_le re_tau im_tau Rq)

/-- **`(Im √(t²+1))² ≥ (Im t)² − 1`** for every `t`. -/
theorem im_csqrt_sq_ge (t : ℂ) : t.im ^ 2 - 1 ≤ (csqrt (t ^ 2 + 1)).im ^ 2 := by
  obtain ⟨hD, hP⟩ := csqrt_parts t
  set a := (csqrt (t ^ 2 + 1)).re
  set b := (csqrt (t ^ 2 + 1)).im
  -- `S = a² + b²` satisfies `S² = D² + 4α²β²` and `S ≥ 0`; then `S ≥ α² + β² − 1`
  have hS2 : (a ^ 2 + b ^ 2) ^ 2 = (t.re ^ 2 - t.im ^ 2 + 1) ^ 2 + 4 * (t.re * t.im) ^ 2 := by
    rw [← hD, ← hP]; ring
  have hS0 : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hS : t.re ^ 2 + t.im ^ 2 - 1 ≤ a ^ 2 + b ^ 2 := by
    by_contra hlt
    push Not at hlt
    have h0 : 0 ≤ t.re ^ 2 + t.im ^ 2 - 1 := hS0.trans hlt.le
    nlinarith [sq_nonneg t.re, sq_nonneg (t.re * t.im)]
  nlinarith [hD]

/-- On `Re t > 0`, `Im t > 0`, both parts of `√(t²+1)` are positive. -/
theorem csqrt_parts_pos {t : ℂ} (hx : 0 < t.re) (hy : 0 < t.im) :
    0 < (csqrt (t ^ 2 + 1)).re ∧ 0 < (csqrt (t ^ 2 + 1)).im := by
  have hP := (csqrt_parts t).2
  have ha := re_csqrt_nonneg (t ^ 2 + 1)
  have hab : 0 < (csqrt (t ^ 2 + 1)).re * (csqrt (t ^ 2 + 1)).im := by rw [hP]; positivity
  rcases ha.lt_or_eq with ha | ha
  · exact ⟨ha, pos_of_mul_pos_right hab ha.le⟩
  · rw [← ha, zero_mul] at hab; exact absurd hab (lt_irrefl 0)

/-- **`R ≥ Im t · √((Im t)² − 1)`** on `Re t > 0`, `Im t ≥ 1`. -/
theorem Rq_ge_up {t : ℂ} (hx : 0 < t.re) (hy : 1 ≤ t.im) : t.im * Real.sqrt (t.im ^ 2 - 1) ≤ Rq t := by
  obtain ⟨ha, hb⟩ := csqrt_parts_pos hx (by linarith)
  have hb2 := im_csqrt_sq_ge t
  have hbs : Real.sqrt (t.im ^ 2 - 1) ≤ (csqrt (t ^ 2 + 1)).im := by
    rw [Real.sqrt_le_left hb.le]; exact hb2
  unfold Rq
  have : 0 ≤ (csqrt (t ^ 2 + 1)).re * t.re := by positivity
  nlinarith

/-- **`|ζ|² ≤ 1/(1 + 2R)`** whenever `R = Re(√(τ²+1) τ̄) ≥ 0`. -/
theorem normSq_zeta_le_inv (c χ : ℝ) (s : ℂ) (hR : 0 ≤ Rq (tau c χ s)) :
    Complex.normSq (zeta c χ s) ≤ 1 / (1 + 2 * Rq (tau c χ s)) := by
  have he := normSq_zeta_eq c χ s
  set R := Rq (tau c χ s)
  have hR' : (csqrt (tau c χ s ^ 2 + 1)).re * (tau c χ s).re
      + (csqrt (tau c χ s ^ 2 + 1)).im * (tau c χ s).im = R := rfl
  rw [hR'] at he
  rw [he, le_div_iff₀ (by linarith)]
  have h1 : 1 ≤ Real.sqrt (4 * R ^ 2 + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg R]
  have h2 : Real.sqrt (4 * R ^ 2 + 1) ^ 2 = 4 * R ^ 2 + 1 := Real.sq_sqrt (by positivity)
  nlinarith

/-- The region past the turning point. -/
structure Up (ε c χ : ℝ) (s : ℂ) : Prop where
  hε : 0 < ε
  hε1 : ε ≤ 1
  hc : 64 / ε ^ 2 ≤ c
  hχ0 : c - 1 ≤ χ
  hχ1 : χ ≤ c
  hre : 1 / 2 ≤ s.re
  him : (2 + ε) * c ≤ s.im

variable {ε c χ : ℝ} {s : ℂ}

theorem Up.c_ge (h : Up ε c χ s) : 64 ≤ c := by
  have h1 : 64 ≤ 64 / ε ^ 2 := by
    rw [le_div_iff₀ (by have := h.hε; positivity)]
    nlinarith [h.hε, h.hε1]
  linarith [h.hc]

theorem Up.c_pos (h : Up ε c χ s) : 0 < c := by linarith [h.c_ge]

theorem Up.c_ge_inv (h : Up ε c χ s) : 64 / ε ≤ c := by
  have hε := h.hε
  have : 64 / ε ≤ 64 / ε ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith [h.hε1]
  linarith [h.hc]

theorem Up.norm_m_ge (h : Up ε c χ s) : 2 ≤ ‖s + 3 / 2‖ := by
  have : (s + 3 / 2).re = s.re + 3 / 2 := by simp
  have h1 := Complex.re_le_norm (s + 3 / 2)
  linarith [h.hre]

theorem Up.m_ne (h : Up ε c χ s) : s + 3 / 2 ≠ 0 := by
  intro h0; have := h.norm_m_ge; rw [h0, norm_zero] at this; norm_num at this

theorem Up.norm_omega_sub (h : Up ε c χ s) : ‖omega s - (s + 3 / 2)‖ ≤ 1 / 8 := by
  have h1 := norm_omega_sub_le h.m_ne
  have h2 := h.norm_m_ge
  calc ‖omega s - (s + 3 / 2)‖ ≤ 1 / (4 * ‖s + 3 / 2‖) := h1
    _ ≤ 1 / 8 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

theorem Up.re_omega_ge (h : Up ε c χ s) : s.re + 11 / 8 ≤ (omega s).re := by
  have h1 := h.norm_omega_sub
  have h2 : |(omega s - (s + 3 / 2)).re| ≤ 1 / 8 := (Complex.abs_re_le_norm _).trans h1
  have : (omega s - (s + 3 / 2)).re = (omega s).re - s.re - 3 / 2 := by simp; ring
  rw [this] at h2
  linarith [(abs_le.mp h2).1]

theorem Up.im_omega_ge (h : Up ε c χ s) : s.im - 1 / 8 ≤ (omega s).im := by
  have h1 := h.norm_omega_sub
  have h2 : |(omega s - (s + 3 / 2)).im| ≤ 1 / 8 := (Complex.abs_im_le_norm _).trans h1
  have : (omega s - (s + 3 / 2)).im = (omega s).im - s.im := by simp
  rw [this] at h2
  linarith [(abs_le.mp h2).1]

theorem Up.omega_ne (h : Up ε c χ s) : omega s ≠ 0 := by
  intro h0; have := h.re_omega_ge; rw [h0] at this; simp at this; linarith [h.hre]

theorem Up.normSq_omega_gt (h : Up ε c χ s) : c < Complex.normSq (omega s) := by
  have hc := h.c_ge
  have hi := h.im_omega_ge
  have hε := h.hε
  have hy : 2 * c - 1 / 8 ≤ (omega s).im := by nlinarith [h.him]
  have : (omega s).im ^ 2 ≤ Complex.normSq (omega s) := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg (omega s).re]
  nlinarith

/-- **`Re τ > 0`** on the region. -/
theorem Up.re_tau_pos (h : Up ε c χ s) : 0 < (tau c χ s).re := by
  have hc := h.c_pos
  rw [re_tau hc.ne' h.omega_ne]
  have h1 : 0 < (omega s).re := by linarith [h.re_omega_ge, h.hre]
  have h2 : 0 < Complex.normSq (omega s) - χ := by linarith [h.normSq_omega_gt, h.hχ1]
  have h3 : 0 < Complex.normSq (omega s) := Complex.normSq_pos.mpr h.omega_ne
  positivity

/-- **`Im τ ≥ 1 + ε/4`** on the region. -/
theorem Up.im_tau_ge (h : Up ε c χ s) : 1 + ε / 4 ≤ (tau c χ s).im := by
  have hc := h.c_pos
  have hε := h.hε
  have hcε := h.c_ge_inv
  rw [im_tau hc.ne' h.omega_ne]
  have hn := Complex.normSq_pos.mpr h.omega_ne
  have hχ : 0 ≤ χ := by linarith [h.hχ0, h.c_ge]
  have hi := h.im_omega_ge
  have hy : (2 + ε) * c - 1 / 8 ≤ (omega s).im := by linarith [h.him]
  have hyp : 0 < (omega s).im := by nlinarith [h.c_ge]
  rw [le_div_iff₀ (by positivity)]
  have hk : 1 / 8 ≤ ε / 4 * c := by
    rw [div_le_iff₀ hε] at hcε; nlinarith
  nlinarith [mul_nonneg hyp.le hχ]

/-- **`R(τ) ≥ √(ε/2)`** on the region. -/
theorem Up.Rq_ge (h : Up ε c χ s) : Real.sqrt (ε / 2) ≤ Rq (tau c χ s) := by
  have hε := h.hε
  have hy := h.im_tau_ge
  have h1 := Rq_ge_up h.re_tau_pos (by linarith)
  have h2 : Real.sqrt (ε / 2) ≤ Real.sqrt ((tau c χ s).im ^ 2 - 1) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h3 : 0 ≤ Real.sqrt ((tau c χ s).im ^ 2 - 1) := Real.sqrt_nonneg _
  nlinarith

/-- **Uniform contraction**: `|ζ|² ≤ 1/(1 + 2√(ε/2))` on the region. -/
theorem Up.normSq_zeta_le (h : Up ε c χ s) :
    Complex.normSq (zeta c χ s) ≤ 1 / (1 + 2 * Real.sqrt (ε / 2)) := by
  have hR := h.Rq_ge
  have hR0 : 0 ≤ Rq (tau c χ s) := (Real.sqrt_nonneg _).trans hR
  refine (normSq_zeta_le_inv c χ s hR0).trans ?_
  apply one_div_le_one_div_of_le (by positivity)
  linarith

end Cvs.Prolate.Mellin.PastTurningContraction
