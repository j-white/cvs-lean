import Mathlib
import Cvs.Prolate.Mellin.CompanionRootGap
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.StepQuadraticRoots

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Uniform root bounds on the region `Re s ≥ 1/2, |Im s| ≤ (2 − ε)c`

For `0 < ε ≤ 1`, `c ≥ 64/ε²` and `c − 1 ≤ χ ≤ c`: `|Im τ| ≤ 1 − ε/4`, `(Re √(τ²+1))² ≥ ε/4`, the companion root has
`Re ρ₂ ≤ 0` (so `|1 − ρ₂| ≥ 1`), and the gap satisfies `|ρ* − ρ₂|² ≥ 9ε/16`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.UniformRootBounds

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg omega omega_sq tau zeta rhoStar)
open Cvs.Prolate.Mellin.FrozenRootClosedBounds (csqrt_parts re_csqrt_pos norm_omega_sub_le im_tau)
open Cvs.Prolate.Mellin.StepQuadraticRoots (comp)

/-- The region hypotheses. -/
structure Hyp (ε c χ : ℝ) (s : ℂ) : Prop where
  hε : 0 < ε
  hε1 : ε ≤ 1
  hc : 64 / ε ^ 2 ≤ c
  hχ0 : c - 1 ≤ χ
  hχ1 : χ ≤ c
  hre : 1 / 2 ≤ s.re
  him : |s.im| ≤ (2 - ε) * c

variable {ε c χ : ℝ} {s : ℂ}

theorem Hyp.c_ge (h : Hyp ε c χ s) : 64 ≤ c := by
  have h1 : 64 ≤ 64 / ε ^ 2 := by
    rw [le_div_iff₀ (by have := h.hε; positivity)]
    nlinarith [h.hε, h.hε1]
  linarith [h.hc]

theorem Hyp.c_pos (h : Hyp ε c χ s) : 0 < c := by linarith [h.c_ge]

theorem Hyp.norm_m_ge (h : Hyp ε c χ s) : 2 ≤ ‖s + 3 / 2‖ := by
  have : (s + 3 / 2).re = s.re + 3 / 2 := by simp
  have h1 := Complex.re_le_norm (s + 3 / 2)
  linarith [h.hre]

theorem Hyp.m_ne (h : Hyp ε c χ s) : s + 3 / 2 ≠ 0 := by
  intro h0; have := h.norm_m_ge; rw [h0, norm_zero] at this; norm_num at this

theorem Hyp.norm_s2_ge (h : Hyp ε c χ s) : 5 / 2 ≤ ‖s + 2‖ := by
  have : (s + 2).re = s.re + 2 := by simp
  have h1 := Complex.re_le_norm (s + 2)
  linarith [h.hre]

theorem Hyp.s2_ne (h : Hyp ε c χ s) : s + 2 ≠ 0 := by
  intro h0; have := h.norm_s2_ge; rw [h0, norm_zero] at this; norm_num at this

theorem Hyp.norm_omega_sub (h : Hyp ε c χ s) : ‖omega s - (s + 3 / 2)‖ ≤ 1 / 8 := by
  have h1 := norm_omega_sub_le h.m_ne
  have h2 := h.norm_m_ge
  calc ‖omega s - (s + 3 / 2)‖ ≤ 1 / (4 * ‖s + 3 / 2‖) := h1
    _ ≤ 1 / 8 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

theorem Hyp.norm_omega_ge (h : Hyp ε c χ s) : ‖s + 3 / 2‖ - 1 / 8 ≤ ‖omega s‖ := by
  have := h.norm_omega_sub
  have h2 := norm_sub_norm_le (s + 3 / 2) (omega s)
  rw [norm_sub_rev] at this
  linarith

theorem Hyp.omega_ne (h : Hyp ε c χ s) : omega s ≠ 0 := by
  intro h0; have := h.norm_omega_ge; rw [h0, norm_zero] at this; linarith [h.norm_m_ge]

theorem Hyp.abs_im_omega_le (h : Hyp ε c χ s) : |(omega s).im| ≤ |s.im| + 1 / 8 := by
  have h1 := h.norm_omega_sub
  have h2 : |(omega s - (s + 3 / 2)).im| ≤ ‖omega s - (s + 3 / 2)‖ := Complex.abs_im_le_norm _
  have e : (omega s - (s + 3 / 2)).im = (omega s).im - s.im := by simp
  rw [e] at h2
  have := abs_sub_abs_le_abs_sub (omega s).im s.im
  linarith

/-- **`|Im τ| ≤ 1 − ε/4`** on the region. -/
theorem Hyp.abs_im_tau_le (h : Hyp ε c χ s) : |(tau c χ s).im| ≤ 1 - ε / 4 := by
  have hc := h.c_pos
  have hω := h.omega_ne
  have hn : 0 < Complex.normSq (omega s) := Complex.normSq_pos.mpr hω
  rw [im_tau hc.ne' hω]
  have hχ0 : 0 ≤ χ := by linarith [h.hχ0, h.c_ge]
  set y := (omega s).im
  set N := Complex.normSq (omega s)
  have hNn : N = ‖omega s‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hyN : |y| ≤ ‖omega s‖ := Complex.abs_im_le_norm _
  have hωg := h.norm_omega_ge
  have hmg := h.norm_m_ge
  have hω0 : 15 / 8 ≤ ‖omega s‖ := by linarith
  have hyb := h.abs_im_omega_le
  -- |Im τ| = |y|/(2c) + |y|χ/(2cN)
  have e : |y * (N + χ) / (2 * c * N)| = |y| / (2 * c) + |y| * χ / (2 * c * N) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < N + χ), abs_of_pos (by positivity : 0 < 2 * c * N)]
    field_simp
  rw [e]
  -- second term ≤ 1/(2‖ω‖)
  have t2 : |y| * χ / (2 * c * N) ≤ 1 / (2 * ‖omega s‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), hNn]
    have : |y| * χ ≤ ‖omega s‖ * c := mul_le_mul hyN h.hχ1 hχ0 (norm_nonneg _)
    nlinarith [norm_nonneg (omega s)]
  have hε := h.hε
  have hε1 := h.hε1
  by_cases hz : 4 / ε ≤ |s.im|
  · -- far up the line
    have hm2 : |s.im| ≤ ‖s + 3 / 2‖ := by
      have := Complex.abs_im_le_norm (s + 3 / 2); simpa using this
    have hωz : 4 / ε - 1 / 8 ≤ ‖omega s‖ := by linarith
    have hωz' : 31 / (8 * ε) ≤ ‖omega s‖ := by
      have : 31 / (8 * ε) ≤ 4 / ε - 1 / 8 := by
        rw [div_le_iff₀ (by positivity)]
        have : (4 / ε - 1 / 8) * (8 * ε) = 32 - ε := by field_simp; ring
        rw [this]; linarith
      linarith
    have t2' : 1 / (2 * ‖omega s‖) ≤ 4 * ε / 31 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := mul_le_mul_of_nonneg_left hωz' (by positivity : (0 : ℝ) ≤ 8 * ε)
      have e2 : 8 * ε * (31 / (8 * ε)) = 31 := by field_simp
      nlinarith
    have t1 : |y| / (2 * c) ≤ ((2 - ε) * c + 1 / 8) / (2 * c) :=
      div_le_div_of_nonneg_right (by linarith [h.him]) (by positivity)
    have t1' : ((2 - ε) * c + 1 / 8) / (2 * c) = 1 - ε / 2 + 1 / (16 * c) := by field_simp; ring
    have hc16 : 1 / (16 * c) ≤ ε / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 64 / ε ≤ c := le_trans (by
        rw [div_le_div_iff₀ hε (by positivity)]; nlinarith) h.hc
      have := mul_le_mul_of_nonneg_left this hε.le
      have e3 : ε * (64 / ε) = 64 := by field_simp
      nlinarith
    linarith
  · -- low on the line
    push Not at hz
    have t1 : |y| / (2 * c) ≤ (4 / ε + 1 / 8) / (2 * c) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have t1' : (4 / ε + 1 / 8) / (2 * c) ≤ 5 / 128 := by
      rw [div_le_iff₀ (by positivity)]
      have hcε : 64 / ε ^ 2 ≤ c := h.hc
      have : 4 / ε + 1 / 8 ≤ 5 / ε := by
        rw [show (5 : ℝ) / ε = 4 / ε + 1 / ε by ring]
        have : (1 : ℝ) / 8 ≤ 1 / ε := by rw [div_le_div_iff₀ (by norm_num) hε]; linarith
        linarith
      have h5 : 5 / ε * 128 ≤ 5 / 128 * (2 * (64 / ε ^ 2)) * 128 := by
        rw [show 5 / 128 * (2 * (64 / ε ^ 2)) * 128 = 640 / ε ^ 2 by ring,
          show 5 / ε * 128 = 640 / ε by ring]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      nlinarith
    have t2' : 1 / (2 * ‖omega s‖) ≤ 4 / 15 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith

/-- **`(Re √(τ²+1))² ≥ ε/4`** on the region. -/
theorem Hyp.a_sq_ge (h : Hyp ε c χ s) : ε / 4 ≤ (csqrt (tau c χ s ^ 2 + 1)).re ^ 2 := by
  have h1 := Cvs.Prolate.Mellin.FrozenRootClosedBounds.re_csqrt_sq_ge (tau c χ s)
  have h2 := h.abs_im_tau_le
  have hε := h.hε
  have h3 : (tau c χ s).im ^ 2 ≤ (1 - ε / 4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  nlinarith [h.hε1]

/-- `|Im τ| ≤ (|Im s| + 1/8)/(2c) + 1/(2‖ω‖)` on the region. -/
theorem Hyp.abs_im_tau_le_gen (h : Hyp ε c χ s) :
    |(tau c χ s).im| ≤ (|s.im| + 1 / 8) / (2 * c) + 1 / (2 * ‖omega s‖) := by
  have hc := h.c_pos
  have hω := h.omega_ne
  have hn : 0 < Complex.normSq (omega s) := Complex.normSq_pos.mpr hω
  rw [im_tau hc.ne' hω]
  have hχ0 : 0 ≤ χ := by linarith [h.hχ0, h.c_ge]
  set y := (omega s).im
  set N := Complex.normSq (omega s)
  have hNn : N = ‖omega s‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hyN : |y| ≤ ‖omega s‖ := Complex.abs_im_le_norm _
  have hω0 : 0 < ‖omega s‖ := norm_pos_iff.mpr hω
  have hyb := h.abs_im_omega_le
  have e : |y * (N + χ) / (2 * c * N)| = |y| / (2 * c) + |y| * χ / (2 * c * N) := by
    rw [abs_div, abs_mul, abs_of_pos (by linarith : 0 < N + χ), abs_of_pos (by positivity : 0 < 2 * c * N)]
    field_simp
  rw [e]
  have t2 : |y| * χ / (2 * c * N) ≤ 1 / (2 * ‖omega s‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), hNn]
    have : |y| * χ ≤ ‖omega s‖ * c := mul_le_mul hyN h.hχ1 hχ0 (norm_nonneg _)
    nlinarith [norm_nonneg (omega s)]
  have t1 : |y| / (2 * c) ≤ (|s.im| + 1 / 8) / (2 * c) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- Low on the line, `|Im s| < 4/ε`: `|Im τ| ≤ 31/100`. -/
theorem Hyp.abs_im_tau_le_low (h : Hyp ε c χ s) (hz : |s.im| < 4 / ε) : |(tau c χ s).im| ≤ 31 / 100 := by
  have hg := h.abs_im_tau_le_gen
  have hc := h.c_pos
  have hε := h.hε
  have hε1 := h.hε1
  have hωg := h.norm_omega_ge
  have hmg := h.norm_m_ge
  have t1' : (|s.im| + 1 / 8) / (2 * c) ≤ 5 / 128 := by
    rw [div_le_iff₀ (by positivity)]
    have hcε : 64 / ε ^ 2 ≤ c := h.hc
    have : 4 / ε + 1 / 8 ≤ 5 / ε := by
      rw [show (5 : ℝ) / ε = 4 / ε + 1 / ε by ring]
      have : (1 : ℝ) / 8 ≤ 1 / ε := by rw [div_le_div_iff₀ (by norm_num) hε]; linarith
      linarith
    have h5 : 5 / ε * 128 ≤ 5 / 128 * (2 * (64 / ε ^ 2)) * 128 := by
      rw [show 5 / 128 * (2 * (64 / ε ^ 2)) * 128 = 640 / ε ^ 2 by ring,
        show 5 / ε * 128 = 640 / ε by ring]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    nlinarith
  have t2' : 1 / (2 * ‖omega s‖) ≤ 4 / 15 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

/-- **The companion root lies in the left half-plane**: `Re ρ₂ ≤ 0`, hence `|1 − ρ₂| ≥ 1`. -/
theorem Hyp.re_comp_nonpos (h : Hyp ε c χ s) : (comp s (rhoStar c χ s)).re ≤ 0 := by
  have hc := h.c_pos
  rw [Cvs.Prolate.Mellin.CompanionRootGap.comp_rhoStar h.m_ne h.s2_ne h.omega_ne, neg_div, Complex.neg_re, neg_nonpos,
    Cvs.Prolate.Mellin.CompanionRootGap.omega_W hc.ne' h.m_ne h.s2_ne h.omega_ne]
  set w := csqrt (tau c χ s ^ 2 + 1)
  set a := w.re
  have ha0 : 0 ≤ a := re_csqrt_nonneg _
  have hb : |w.im| ≤ |(tau c χ s).im| :=
    Cvs.Prolate.Mellin.CompanionRootGap.abs_im_csqrt_le (by
      have := h.abs_im_tau_le
      have hε := h.hε
      have : |(tau c χ s).im| < 1 := by linarith
      nlinarith [abs_nonneg (tau c χ s).im, sq_abs (tau c χ s).im])
  have hy1 : |(tau c χ s).im| ≤ 1 := by have := h.abs_im_tau_le; linarith [h.hε]
  have hwn : ‖w‖ ≤ a + 1 := by
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ a + 1 := by rw [abs_of_nonneg ha0]; linarith
  set N := ‖s + 2‖
  have hN := h.norm_s2_ge
  have hN0 : 0 < N := by linarith
  -- T1 = w + e w, ‖e‖ ≤ (5/8)/N
  have he : ‖(omega s - (s + 2)) / (s + 2)‖ ≤ 5 / 8 / N := by
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ hN0.le
    have h1 := h.norm_omega_sub
    calc ‖omega s - (s + 2)‖ = ‖(omega s - (s + 3 / 2)) + (-(1 / 2) : ℂ)‖ := by ring_nf
      _ ≤ ‖omega s - (s + 3 / 2)‖ + ‖(-(1 / 2) : ℂ)‖ := norm_add_le _ _
      _ ≤ 5 / 8 := by simp only [norm_neg]; norm_num at h1 ⊢; linarith
  have eT1 : omega s * w / (s + 2) = w + (omega s - (s + 2)) / (s + 2) * w := by
    field_simp [h.s2_ne]; ring
  have hT1 : a - 5 / 8 / N * (a + 1) ≤ (omega s * w / (s + 2)).re := by
    rw [eT1, Complex.add_re]
    have := Complex.re_le_norm (-((omega s - (s + 2)) / (s + 2) * w))
    have h2 : ‖(omega s - (s + 2)) / (s + 2) * w‖ ≤ 5 / 8 / N * (a + 1) := by
      rw [norm_mul]; exact mul_le_mul he hwn (norm_nonneg _) (by positivity)
    rw [Complex.neg_re, norm_neg] at this
    linarith
  -- T2 = (s+1)/(2c) − χ/(2c(s+2))
  have eT2 : ((s + 1) * (s + 2) - χ) / (2 * c * (s + 2)) = (s + 1) / (2 * c) - χ / (2 * c * (s + 2)) := by
    field_simp [h.s2_ne]
  have hT2 : -(1 / (2 * N)) ≤ (((s + 1) * (s + 2) - χ) / (2 * c * (s + 2))).re := by
    rw [eT2, Complex.sub_re]
    have r1 : 0 ≤ ((s + 1) / (2 * c)).re := by
      have : ((s + 1) / (2 * c)).re = (s.re + 1) / (2 * c) := by
        rw [show (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]; simp
      rw [this]; have := h.hre; positivity
    have r2 : (χ / (2 * c * (s + 2))).re ≤ 1 / (2 * N) := by
      have hχ0 : 0 ≤ χ := by linarith [h.hχ0, h.c_ge]
      calc (χ / (2 * c * (s + 2))).re ≤ ‖χ / (2 * c * (s + 2))‖ := Complex.re_le_norm _
        _ = χ / (2 * c * N) := by
            rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ0,
              Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ 1 / (2 * N) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h.hχ1]
    linarith
  -- combine: a (N − 5/8) ≥ 9/8
  have key : 9 / 8 ≤ a * (N - 5 / 8) := by
    have hε := h.hε
    have hε1 := h.hε1
    by_cases hA : 81 / (16 * ε) ≤ (N - 5 / 8) ^ 2
    · have ha2 := h.a_sq_ge
      have : (9 / 8) ^ 2 ≤ (a * (N - 5 / 8)) ^ 2 := by
        rw [mul_pow]
        have := mul_le_mul ha2 hA (by positivity) (sq_nonneg a)
        have e : ε / 4 * (81 / (16 * ε)) = (9 / 8) ^ 2 := by field_simp; ring
        nlinarith
      have hpos : 0 ≤ a * (N - 5 / 8) := mul_nonneg ha0 (by linarith)
      by_contra hlt
      push Not at hlt
      nlinarith
    · push Not at hA
      -- then |Im s| < 4/ε and |Im τ| ≤ 31/100, so a² ≥ 81/100
      have hNl : N - 5 / 8 < 9 / (4 * Real.sqrt ε) := by
        have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
        have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
        by_contra hc'
        push Not at hc'
        have : (9 / (4 * Real.sqrt ε)) ^ 2 ≤ (N - 5 / 8) ^ 2 := pow_le_pow_left₀ (by positivity) hc' 2
        have e : (9 / (4 * Real.sqrt ε)) ^ 2 = 81 / (16 * ε) := by rw [div_pow, mul_pow, hsq]; ring
        linarith
      have hzs : |s.im| ≤ N := by have := Complex.abs_im_le_norm (s + 2); simpa using this
      have hz : |s.im| < 4 / ε := by
        have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
        have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
        have hs1 : Real.sqrt ε ≤ 1 := by rw [Real.sqrt_le_one]; exact hε1
        -- 5/8 + 9/(4√ε) ≤ 4/ε
        have : 5 / 8 + 9 / (4 * Real.sqrt ε) ≤ 4 / ε := by
          set X := 1 / Real.sqrt ε
          have hX : 1 ≤ X := by rw [le_div_iff₀ hs]; linarith
          have e1 : 9 / (4 * Real.sqrt ε) = 9 / 4 * X := by simp only [X]; field_simp
          have e2 : 4 / ε = 4 * X ^ 2 := by simp only [X]; rw [div_pow, one_pow, hsq]; ring
          rw [e1, e2]
          nlinarith
        linarith
      have hyl := h.abs_im_tau_le_low hz
      have ha2 : 81 / 100 ≤ a ^ 2 := by
        have := Cvs.Prolate.Mellin.FrozenRootClosedBounds.re_csqrt_sq_ge (tau c χ s)
        have : (tau c χ s).im ^ 2 ≤ (31 / 100) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hyl 2
        nlinarith
      have ha' : 9 / 10 ≤ a := by nlinarith
      nlinarith
  have : 0 ≤ a - 5 / 8 / N * (a + 1) - 1 / (2 * N) := by
    have e : a - 5 / 8 / N * (a + 1) - 1 / (2 * N) = (a * (N - 5 / 8) - 9 / 8) / N := by
      field_simp; ring
    rw [e]; exact div_nonneg (by linarith) hN0.le
  rw [Complex.add_re]
  linarith

theorem Hyp.one_le_norm_one_sub_comp (h : Hyp ε c χ s) : 1 ≤ ‖1 - comp s (rhoStar c χ s)‖ := by
  have hr := h.re_comp_nonpos
  calc (1 : ℝ) ≤ (1 - comp s (rhoStar c χ s)).re := by simp; linarith
    _ ≤ ‖1 - comp s (rhoStar c χ s)‖ := Complex.re_le_norm _

end Cvs.Prolate.Mellin.UniformRootBounds
