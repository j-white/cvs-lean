import Mathlib
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.StepQuadraticRoots
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Size bounds for the frozen root on the region

On the region of Cvs.Prolate.Mellin.UniformRootBounds: `|Re τ| ≤ 1/(2‖ω‖)` when `Re τ < 0`, `|ζ|² ≤ 9/4`, `|ρ*| ≤ 9/4`, and
`|1 − ρ*| ≤ (‖s + 1‖ + 1)/c` (from `1 − ρ* = (1 + q)/((s+2)(1 − ρ₂))` with `|1 − ρ₂| ≥ 1`).
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.FrozenRootSizeBounds

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg omega omega_sq tau zeta rhoStar)
open Cvs.Prolate.Mellin.FrozenRootClosedBounds (csqrt_parts re_csqrt_pos norm_omega_sub_le im_tau re_tau Rq)
open Cvs.Prolate.Mellin.StepQuadraticRoots (comp Qs)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)

variable {ε c χ : ℝ} {s : ℂ}

/-- **The negative part of `Re τ`**: `Re τ ≥ −1/(2‖ω‖)`. -/
theorem Hyp.re_tau_ge (h : Hyp ε c χ s) : -(1 / (2 * ‖omega s‖)) ≤ (tau c χ s).re := by
  have hc := h.c_pos
  have hω := h.omega_ne
  have hn : 0 < Complex.normSq (omega s) := Complex.normSq_pos.mpr hω
  rw [re_tau hc.ne' hω]
  set N := Complex.normSq (omega s)
  have hNn : N = ‖omega s‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hω0 : 0 < ‖omega s‖ := norm_pos_iff.mpr hω
  have hxr : (omega s).re ≤ ‖omega s‖ := Complex.re_le_norm _
  have hxr0 : 0 ≤ (omega s).re := by
    have h1 := h.norm_omega_sub
    have h2 : |(omega s - (s + 3 / 2)).re| ≤ ‖omega s - (s + 3 / 2)‖ := Complex.abs_re_le_norm _
    have e : (omega s - (s + 3 / 2)).re = (omega s).re - (s.re + 3 / 2) := by simp
    rw [e] at h2
    have := h.hre
    have := (abs_le.mp (h2.trans h1)).1
    linarith
  have hχ0 : 0 ≤ χ := by linarith [h.hχ0, h.c_ge]
  have key : -((omega s).re * (N - χ)) ≤ ‖omega s‖ * c := by
    nlinarith [mul_le_mul hxr h.hχ1 hχ0 (norm_nonneg _), mul_nonneg hxr0 hn.le]
  have : -((omega s).re * (N - χ) / (2 * c * N)) ≤ 1 / (2 * ‖omega s‖) := by
    rw [← neg_div, div_le_div_iff₀ (by positivity) (by positivity), hNn]
    rw [hNn] at key
    nlinarith [mul_le_mul_of_nonneg_right key (by positivity : (0 : ℝ) ≤ 2 * ‖omega s‖)]
  linarith

/-- **`|R| ≤ 31/100` when `Re τ < 0`**, with `R = Re(√(τ²+1) τ̄)`. -/
theorem Hyp.abs_Rq_le (h : Hyp ε c χ s) (hx : (tau c χ s).re < 0) : |Rq (tau c χ s)| ≤ 31 / 100 := by
  set t := tau c χ s
  have hε := h.hε
  have hε1 := h.hε1
  have hyb := h.abs_im_tau_le
  have ht : t.im ^ 2 < 1 := by
    have h1 : |t.im| < 1 := by linarith
    nlinarith [abs_nonneg t.im, sq_abs t.im]
  have hy : 0 < 1 - t.im ^ 2 := by linarith
  set S := Real.sqrt (1 - t.im ^ 2)
  have hS : 0 < S := Real.sqrt_pos.mpr hy
  have hS2 : S ^ 2 = 1 - t.im ^ 2 := Real.sq_sqrt hy.le
  have hlo := Cvs.Prolate.Mellin.FrozenRootClosedBounds.Rq_ge_of_nonpos ht hx.le
  have hRneg : Rq t ≤ 0 := by
    rw [Cvs.Prolate.Mellin.FrozenRootClosedBounds.Rq_eq ht]
    have ha := re_csqrt_pos ht
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hx.le (by positivity)) ha.le
  set u := |t.re| / S
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ^ 2 = t.re ^ 2 / (1 - t.im ^ 2) := by
    simp only [u]; rw [div_pow, sq_abs, hS2]
  have hRu : |Rq t| ≤ u * (1 + u ^ 2) := by
    rw [abs_of_nonpos hRneg, hu2]
    have e : t.re * (1 + t.re ^ 2 / (1 - t.im ^ 2)) / S = -(u * (1 + t.re ^ 2 / (1 - t.im ^ 2))) := by
      simp only [u]; rw [abs_of_neg hx]; ring
    rw [e] at hlo
    linarith
  have hxw := Hyp.re_tau_ge h
  have hω0 : 0 < ‖omega s‖ := norm_pos_iff.mpr h.omega_ne
  have hxa : |t.re| ≤ 1 / (2 * ‖omega s‖) := by rw [abs_of_neg hx]; linarith
  have hu2b : u ^ 2 ≤ 2 / 25 := by
    rw [hu2, div_le_iff₀ hy]
    have hx2 : t.re ^ 2 ≤ (1 / (2 * ‖omega s‖)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hxa 2
    by_cases hz : |s.im| < 4 / ε
    · have hl := h.abs_im_tau_le_low hz
      have hy2 : t.im ^ 2 ≤ (31 / 100) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
      have hωg := h.norm_omega_ge
      have hmg := h.norm_m_ge
      have : (1 / (2 * ‖omega s‖)) ^ 2 ≤ (4 / 15) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      nlinarith
    · push Not at hz
      have hm2 : |s.im| ≤ ‖s + 3 / 2‖ := by
        have := Complex.abs_im_le_norm (s + 3 / 2); simpa using this
      have hωg := h.norm_omega_ge
      have hωz : 31 / (8 * ε) ≤ ‖omega s‖ := by
        have : 31 / (8 * ε) ≤ 4 / ε - 1 / 8 := by
          rw [div_le_iff₀ (by positivity)]
          have : (4 / ε - 1 / 8) * (8 * ε) = 32 - ε := by field_simp; ring
          rw [this]; linarith
        linarith
      have hxb : (1 / (2 * ‖omega s‖)) ^ 2 ≤ (4 * ε / 31) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have := mul_le_mul_of_nonneg_left hωz (by positivity : (0 : ℝ) ≤ 8 * ε)
        have e : 8 * ε * (31 / (8 * ε)) = 31 := by field_simp
        nlinarith
      have hy2 : t.im ^ 2 ≤ (1 - ε / 4) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hyb 2
      nlinarith
  have hub : u ≤ 71 / 250 := by nlinarith
  have h1 : u * (1 + u ^ 2) ≤ 71 / 250 * (1 + 2 / 25) :=
    mul_le_mul hub (by linarith) (by positivity) (by norm_num)
  linarith

/-- **`|ζ|² ≤ 9/4`** on the region. -/
theorem Hyp.norm_zeta_sq_le (h : Hyp ε c χ s) : ‖zeta c χ s‖ ^ 2 ≤ 9 / 4 := by
  rw [← Complex.normSq_eq_norm_sq, Cvs.Prolate.Mellin.FrozenRootErrorIdentity.normSq_zeta_eq]
  set R := Rq (tau c χ s)
  change Real.sqrt (4 * R ^ 2 + 1) - 2 * R ≤ 9 / 4
  by_cases hx : (tau c χ s).re < 0
  · have hR := Hyp.abs_Rq_le h hx
    have hs : Real.sqrt (4 * R ^ 2 + 1) ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have : R ^ 2 ≤ (31 / 100) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hR 2
      nlinarith
    have := neg_abs_le R
    linarith
  · push Not at hx
    have ht : (tau c χ s).im ^ 2 < 1 := by
      have := h.abs_im_tau_le
      have hε := h.hε
      have h1 : |(tau c χ s).im| < 1 := by linarith
      nlinarith [abs_nonneg (tau c χ s).im, sq_abs (tau c χ s).im]
    have hR0 : 0 ≤ R := by
      have := Cvs.Prolate.Mellin.FrozenRootClosedBounds.Rq_ge_of_nonneg ht hx
      have hn : 0 ≤ (tau c χ s).re / ‖csqrt (tau c χ s ^ 2 + 1)‖ := by positivity
      linarith
    have hs : Real.sqrt (4 * R ^ 2 + 1) ≤ 1 + 2 * R := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    linarith

theorem Hyp.norm_s2_ge_m (h : Hyp ε c χ s) : ‖s + 3 / 2‖ - 1 / 2 ≤ ‖s + 2‖ := by
  have := norm_sub_norm_le (s + 3 / 2) (-(1 / 2 : ℂ))
  rw [show s + 3 / 2 - -(1 / 2 : ℂ) = s + 2 by ring, norm_neg] at this
  norm_num at this ⊢; linarith

theorem Hyp.norm_omega_le (h : Hyp ε c χ s) : ‖omega s‖ ≤ ‖s + 3 / 2‖ + 1 / 8 := by
  have h1 := h.norm_omega_sub
  have := norm_le_norm_add_norm_sub' (omega s) (s + 3 / 2)
  linarith

theorem Hyp.zeta_norm_le (h : Hyp ε c χ s) : ‖zeta c χ s‖ ≤ 3 / 2 := by
  have := Hyp.norm_zeta_sq_le h
  nlinarith [norm_nonneg (zeta c χ s)]

/-- **`|ρ*| ≤ 9/4`** on the region. -/
theorem Hyp.norm_rho_le (h : Hyp ε c χ s) : ‖rhoStar c χ s‖ ≤ 9 / 4 := by
  have hz := Hyp.zeta_norm_le h
  have hω := Hyp.norm_omega_le h
  have hs2 := Hyp.norm_s2_ge_m h
  have hm := h.norm_m_ge
  have hN : 0 < ‖s + 2‖ := by linarith
  unfold rhoStar
  rw [norm_div, norm_mul, div_le_iff₀ hN]
  have h1 : ‖omega s‖ * ‖zeta c χ s‖ ≤ (‖s + 3 / 2‖ + 1 / 8) * (3 / 2) :=
    mul_le_mul hω hz (norm_nonneg _) (by positivity)
  nlinarith

theorem Hyp.rho_ne (h : Hyp ε c χ s) : rhoStar c χ s ≠ 0 := by
  unfold rhoStar
  exact div_ne_zero (mul_ne_zero h.omega_ne (Cvs.Prolate.Mellin.FrozenRootErrorIdentity.zeta_ne_zero c χ s)) h.s2_ne

theorem Hyp.Qs_rho (h : Hyp ε c χ s) :
    Qs s (((s + 1) * (s + 2) - χ) / c) (rhoStar c χ s) = 0 := by
  have := Cvs.Prolate.Mellin.FrozenRootErrorIdentity.rhoStar_root (χ := χ) h.c_pos.ne' h.m_ne h.s2_ne h.omega_ne
  unfold Qs; exact this

/-- **`|1 − ρ*| ≤ (‖s + 1‖ + 1)/c`** on the region. -/
theorem Hyp.norm_one_sub_rho_le (h : Hyp ε c χ s) : ‖1 - rhoStar c χ s‖ ≤ (‖s + 1‖ + 1) / c := by
  have hc := h.c_pos
  have h1 := h.one_le_norm_one_sub_comp
  have hne : 1 - comp s (rhoStar c χ s) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h1; norm_num at h1
  rw [Cvs.Prolate.Mellin.StepQuadraticRoots.one_sub_root h.s2_ne (Hyp.rho_ne h) (Hyp.Qs_rho h) hne]
  have hN := h.norm_s2_ge
  have hN0 : 0 < ‖s + 2‖ := by linarith
  have hq : ‖1 + ((s + 1) * (s + 2) - χ) / c‖ ≤ (‖s + 1‖ * ‖s + 2‖ + 1) / c := by
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have e : 1 + ((s + 1) * (s + 2) - χ) / c = ((s + 1) * (s + 2) + ((c - χ : ℝ) : ℂ)) / (c : ℂ) := by
      push_cast; field_simp; ring
    rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    apply div_le_div_of_nonneg_right _ hc.le
    calc ‖(s + 1) * (s + 2) + ((c - χ : ℝ) : ℂ)‖ ≤ ‖(s + 1) * (s + 2)‖ + ‖((c - χ : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖s + 1‖ * ‖s + 2‖ + 1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have : |c - χ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [h.hχ0, h.hχ1]
          linarith
  rw [norm_div, norm_mul]
  calc ‖1 + ((s + 1) * (s + 2) - χ) / c‖ / (‖s + 2‖ * ‖1 - comp s (rhoStar c χ s)‖)
      ≤ ‖1 + ((s + 1) * (s + 2) - χ) / c‖ / (‖s + 2‖ * 1) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (mul_le_mul_of_nonneg_left h1 hN0.le)
    _ ≤ (‖s + 1‖ * ‖s + 2‖ + 1) / c / ‖s + 2‖ := by rw [mul_one]; exact div_le_div_of_nonneg_right hq hN0.le
    _ ≤ (‖s + 1‖ + 1) / c := by
        rw [div_div, div_le_div_iff₀ (by positivity) hc]
        nlinarith [norm_nonneg (s + 1)]

end Cvs.Prolate.Mellin.FrozenRootSizeBounds
