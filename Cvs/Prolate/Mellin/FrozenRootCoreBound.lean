import Mathlib
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The core bound for `|ζ|`

`Σ_{i ≤ N} 1/(a + 2i) ≤ 1/a + ½ log((a + 2N)/a)`. On the region, `|ζ|² ≤ 1` when `Re τ ≥ 0`, and when `Re τ < 0`
(the oscillator core, where `Re ω < √c`) `|ζ|² ≤ exp(3/(2 Re ω))`.
-/

noncomputable section

open Complex Finset

namespace Cvs.Prolate.Mellin.FrozenRootCoreBound

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt re_csqrt_nonneg omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.FrozenRootClosedBounds (Rq re_tau im_tau)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)

/-- **Harmonic sums in steps of two**: `Σ_{i ≤ N} 1/(a + 2i) ≤ 1/a + ½ log((a + 2N)/a)`. -/
theorem sum_inv_le_log {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ i ∈ range (N + 1), 1 / (a + 2 * i) ≤ 1 / a + 1 / 2 * Real.log ((a + 2 * N) / a) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hN : (0 : ℝ) < a + 2 * N := by positivity
    have hN1 : (0 : ℝ) < a + 2 * ((N + 1 : ℕ) : ℝ) := by positivity
    have key : 1 / (a + 2 * ((N + 1 : ℕ) : ℝ))
        ≤ 1 / 2 * (Real.log ((a + 2 * ((N + 1 : ℕ) : ℝ)) / a) - Real.log ((a + 2 * N) / a)) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have e : (a + 2 * ((N + 1 : ℕ) : ℝ)) / a / ((a + 2 * N) / a) = (a + 2 * ((N + 1 : ℕ) : ℝ)) / (a + 2 * N) := by
        field_simp
      rw [e]
      have hl := Real.one_sub_inv_le_log_of_pos (show 0 < (a + 2 * ((N + 1 : ℕ) : ℝ)) / (a + 2 * N) by positivity)
      have e2 : 1 - ((a + 2 * ((N + 1 : ℕ) : ℝ)) / (a + 2 * N))⁻¹ = 2 / (a + 2 * ((N + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp; ring
      rw [e2] at hl
      have : 1 / (a + 2 * ((N + 1 : ℕ) : ℝ)) = 1 / 2 * (2 / (a + 2 * ((N + 1 : ℕ) : ℝ))) := by ring
      linarith
    push_cast at key ih ⊢
    linarith

variable {ε c χ : ℝ} {s : ℂ}

/-- `Re ω ≥ 15/8` on the region. -/
theorem Hyp.re_omega_ge (h : Hyp ε c χ s) : s.re + 3 / 2 - 1 / 8 ≤ (omega s).re := by
  have h1 := h.norm_omega_sub
  have h2 : |(omega s - (s + 3 / 2)).re| ≤ ‖omega s - (s + 3 / 2)‖ := Complex.abs_re_le_norm _
  have e : (omega s - (s + 3 / 2)).re = (omega s).re - (s.re + 3 / 2) := by simp
  rw [e] at h2
  have := (abs_le.mp (h2.trans h1)).1
  linarith

/-- **Outside the core `|ζ| ≤ 1`.** -/
theorem Hyp.normSq_zeta_le_one (h : Hyp ε c χ s) (hx : 0 ≤ (tau c χ s).re) : ‖zeta c χ s‖ ^ 2 ≤ 1 := by
  rw [← Complex.normSq_eq_norm_sq, Cvs.Prolate.Mellin.FrozenRootErrorIdentity.normSq_zeta_eq]
  set R := Rq (tau c χ s)
  change Real.sqrt (4 * R ^ 2 + 1) - 2 * R ≤ 1
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

/-- In the core (`Re τ < 0`), `‖ω‖² < χ ≤ c`. -/
theorem Hyp.normSq_omega_lt (h : Hyp ε c χ s) (hx : (tau c χ s).re < 0) : ‖omega s‖ ^ 2 < c := by
  have hc := h.c_pos
  have hω := h.omega_ne
  have hn : 0 < Complex.normSq (omega s) := Complex.normSq_pos.mpr hω
  rw [re_tau hc.ne' hω] at hx
  have hre : 0 < (omega s).re := by have := Hyp.re_omega_ge h; linarith [h.hre]
  have : Complex.normSq (omega s) - χ < 0 := by
    by_contra hn'; push Not at hn'
    have : 0 ≤ (omega s).re * (Complex.normSq (omega s) - χ) / (2 * c * Complex.normSq (omega s)) := by
      positivity
    linarith
  rw [← Complex.normSq_eq_norm_sq]; linarith [h.hχ1]

set_option maxHeartbeats 2000000 in
/-- **The core bound**: if `Re τ < 0` then `|ζ|² ≤ exp(3/(2 Re ω))`. -/
theorem Hyp.normSq_zeta_le_core (h : Hyp ε c χ s) (hx : (tau c χ s).re < 0) :
    ‖zeta c χ s‖ ^ 2 ≤ Real.exp (3 / (2 * (omega s).re)) := by
  set t := tau c χ s
  have hc := h.c_pos
  have hω := h.omega_ne
  have hω0 : 0 < ‖omega s‖ := norm_pos_iff.mpr hω
  have hre := Hyp.re_omega_ge h
  have hreω : 15 / 8 ≤ (omega s).re := by linarith [h.hre]
  have hcore := Hyp.normSq_omega_lt h hx
  -- |Im τ| ≤ 1/3 in the core
  have hy : |t.im| ≤ 1 / 3 := by
    have hg := h.abs_im_tau_le_gen
    have hzi : |s.im| + 1 / 8 ≤ ‖omega s‖ + 1 / 4 := by
      have := h.abs_im_omega_le
      have h2 : |(omega s).im| ≤ ‖omega s‖ := Complex.abs_im_le_norm _
      -- |s.im| ≤ |Im ω| + 1/8
      have h3 : |s.im| ≤ |(omega s).im| + 1 / 8 := by
        have h1 := h.norm_omega_sub
        have h4 : |(omega s - (s + 3 / 2)).im| ≤ ‖omega s - (s + 3 / 2)‖ := Complex.abs_im_le_norm _
        have e : (omega s - (s + 3 / 2)).im = (omega s).im - s.im := by simp
        rw [e] at h4
        have := abs_sub_abs_le_abs_sub s.im (omega s).im
        rw [abs_sub_comm] at this
        linarith
      linarith
    have hωc : ‖omega s‖ ≤ Real.sqrt c := by
      rw [← Real.sqrt_sq hω0.le]; exact Real.sqrt_le_sqrt hcore.le
    have hsc : Real.sqrt c ≥ 8 := by
      rw [show (8 : ℝ) = Real.sqrt 64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt h.c_ge
    have hcs : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
    have t1 : (|s.im| + 1 / 8) / (2 * c) ≤ 1 / 16 + 1 / 256 := by
      rw [div_le_iff₀ (by positivity)]
      set r := Real.sqrt c
      have : |s.im| + 1 / 8 ≤ r + 1 / 4 := by linarith
      have h8 : 8 * r ≤ r ^ 2 := by nlinarith
      have h128 : 64 ≤ r ^ 2 := by nlinarith
      nlinarith
    have hωg : 15 / 8 ≤ ‖omega s‖ := hreω.trans (Complex.re_le_norm _)
    have t2 : 1 / (2 * ‖omega s‖) ≤ 4 / 15 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have : (1 / 16 + 1 / 256 : ℝ) + 4 / 15 ≤ 1 / 3 := by norm_num
    linarith
  have ht : t.im ^ 2 < 1 := by nlinarith [abs_nonneg t.im, sq_abs t.im]
  have hy2 : t.im ^ 2 ≤ 1 / 9 := by rw [← sq_abs]; nlinarith [abs_nonneg t.im]
  have hyp : 0 < 1 - t.im ^ 2 := by linarith
  -- |Re τ| ≤ 1/(2 Re ω)
  have hxa : |t.re| ≤ 1 / (2 * (omega s).re) := by
    rw [abs_of_neg hx]
    have hxw := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.re_tau_ge h
    -- sharper: -Re τ ≤ Re ω χ/(2c|ω|²) ≤ 1/(2 Re ω)
    have hn : 0 < Complex.normSq (omega s) := Complex.normSq_pos.mpr hω
    have hχ0 : 0 ≤ χ := by linarith [h.hχ0, h.c_ge]
    rw [show t.re = (omega s).re * (Complex.normSq (omega s) - χ) / (2 * c * Complex.normSq (omega s)) from
      re_tau hc.ne' hω]
    have hNre : (omega s).re ^ 2 ≤ Complex.normSq (omega s) := by
      rw [Complex.normSq_apply]; nlinarith [sq_nonneg (omega s).im]
    have hre0 : 0 < (omega s).re := by linarith
    rw [← neg_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have k1 : (omega s).re ^ 2 * χ ≤ c * Complex.normSq (omega s) :=
      mul_le_mul hNre h.hχ1 hχ0 hn.le |>.trans_eq (by ring)
    nlinarith [mul_nonneg (sq_nonneg (omega s).re) hn.le]
  have hx2 : t.re ^ 2 ≤ (1 / (2 * (omega s).re)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hxa 2
  have hx415 : 1 / (2 * (omega s).re) ≤ 4 / 15 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- |R| ≤ u(1+u²), u = |x|/√(1−y²), u² ≤ (9/8) x²
  set S := Real.sqrt (1 - t.im ^ 2)
  have hS : 0 < S := Real.sqrt_pos.mpr hyp
  have hS2 : S ^ 2 = 1 - t.im ^ 2 := Real.sq_sqrt hyp.le
  have hlo := Cvs.Prolate.Mellin.FrozenRootClosedBounds.Rq_ge_of_nonpos ht hx.le
  have hRneg : Rq t ≤ 0 := by
    rw [Cvs.Prolate.Mellin.FrozenRootClosedBounds.Rq_eq ht]
    have ha := Cvs.Prolate.Mellin.FrozenRootClosedBounds.re_csqrt_pos ht
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hx.le (by positivity)) ha.le
  set u := |t.re| / S
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ^ 2 = t.re ^ 2 / (1 - t.im ^ 2) := by simp only [u]; rw [div_pow, sq_abs, hS2]
  have hRu : |Rq t| ≤ u * (1 + u ^ 2) := by
    rw [abs_of_nonpos hRneg, hu2]
    have e : t.re * (1 + t.re ^ 2 / (1 - t.im ^ 2)) / S = -(u * (1 + t.re ^ 2 / (1 - t.im ^ 2))) := by
      simp only [u]; rw [abs_of_neg hx]; ring
    rw [e] at hlo
    linarith
  have hu2b : u ^ 2 ≤ 9 / 8 * t.re ^ 2 := by
    rw [hu2, div_le_iff₀ hyp]; nlinarith [sq_nonneg t.re]
  have hx2' : t.re ^ 2 ≤ 16 / 225 := by
    have : |t.re| ≤ 4 / 15 := hxa.trans hx415
    have := pow_le_pow_left₀ (abs_nonneg t.re) this 2
    rw [sq_abs] at this; linarith
  have hu2s : u ^ 2 ≤ 2 / 25 := by linarith
  -- |R| ≤ (1.1455) |x| and 2|R| + 2R² ≤ 3|x|
  have hR2 : Rq t ^ 2 ≤ 9 / 8 * t.re ^ 2 * (27 / 25) ^ 2 := by
    have h1 : |Rq t| ^ 2 ≤ (u * (1 + u ^ 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hRu 2
    rw [sq_abs] at h1
    have h2 : (u * (1 + u ^ 2)) ^ 2 ≤ u ^ 2 * (27 / 25) ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 2)
        (sq_nonneg u)
    nlinarith
  have hRx : |Rq t| ≤ 1146 / 1000 * |t.re| := by
    have : |Rq t| ^ 2 ≤ (1146 / 1000 * |t.re|) ^ 2 := by
      rw [sq_abs, mul_pow, sq_abs]; nlinarith
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp this
  have hRs : |Rq t| ≤ 306 / 1000 := by
    have : |t.re| ≤ 4 / 15 := hxa.trans hx415
    have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 1146 / 1000)
    linarith
  -- conclude via |ζ|² ≤ exp(−2R + 2R²)
  have hz := Cvs.Prolate.Mellin.FrozenRootErrorIdentity.normSq_zeta_le_exp c χ s
  rw [Complex.normSq_eq_norm_sq] at hz
  refine hz.trans (Real.exp_le_exp.mpr ?_)
  change -2 * Rq t + 2 * Rq t ^ 2 ≤ 3 / (2 * (omega s).re)
  have h1 : -2 * Rq t + 2 * Rq t ^ 2 ≤ 2 * |Rq t| * (1 + 306 / 1000) := by
    rw [abs_of_nonpos hRneg] at hRs ⊢; nlinarith
  have h2 : 2 * |Rq t| * (1 + 306 / 1000) ≤ 3 * |t.re| := by linarith [abs_nonneg t.re]
  have h3 : 3 * |t.re| ≤ 3 / (2 * (omega s).re) := by
    have := mul_le_mul_of_nonneg_left hxa (by norm_num : (0 : ℝ) ≤ 3)
    rw [show 3 * (1 / (2 * (omega s).re)) = 3 / (2 * (omega s).re) by ring] at this; exact this
  linarith

end Cvs.Prolate.Mellin.FrozenRootCoreBound
