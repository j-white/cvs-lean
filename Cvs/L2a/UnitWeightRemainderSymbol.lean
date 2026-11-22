import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BernsteinRieszSymbolBounds
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityComplexWeight
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The unit-weight remainder symbol in the spectral variable

With unit weight the Q-step remainder is `R = A₂/Q_w² + A₃/Q_w³`, `Q_w(y) = c²(t² − 1)(y² − 1) − w − 2icty`, and the
rung enters only through `w = c² − χ`. For `c ≥ 80`, `2 ≤ m ≤ t`, `|w − c²/2| ≤ c²`, complex `|s| ≤ 3/2`:
`|Q_w(s/m)| ≥ c²(t² − 1)/4`, `|R| ≤ 200/(cmt) + 2600/(c²t²)`, and with `|ψ_g| ≤ F` the Bernstein–Riesz bound on
the disc of radius `3/2` gives `|∫ g e^{icst/m} R ds| ≤ 3F(200/(cmt) + 2600/(c²t²))`.
-/

noncomputable section

namespace Cvs.L2a.UnitWeightRemainderSymbol

open Real Set Complex Metric
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts Cvs.L2a.QIdentityComplexWeight

/-! ### The symbol -/

/-- `Q_w(y) = c²(t² − 1)(y² − 1) − w − 2icty` at complex `w` and `y`. -/
def qW (c t : ℝ) (w y : ℂ) : ℂ :=
  ((c ^ 2 * pP t : ℝ) : ℂ) * (y ^ 2 - 1) - w - 2 * I * ((c * t : ℝ) : ℂ) * y

/-- `Q′ = 2c²t(y² − 1) − 2icy` at complex `y`. -/
def qW₁ (c t : ℝ) (y : ℂ) : ℂ := ((2 * c ^ 2 * t : ℝ) : ℂ) * (y ^ 2 - 1) - 2 * I * (c : ℂ) * y

/-- `Q″ = 2c²(y² − 1)` at complex `y`. -/
def qW₂ (c : ℝ) (y : ℂ) : ℂ := ((2 * c ^ 2 : ℝ) : ℂ) * (y ^ 2 - 1)

/-- `2t + 2icy p` at complex `y`. -/
def kW (c t : ℝ) (y : ℂ) : ℂ := 2 * (t : ℂ) + 2 * I * (c : ℂ) * y * ((pP t : ℝ) : ℂ)

/-- The unit-weight second atom `A₂ = −((2t + 2icyp)Q′ + pQ″)`. -/
def a₂W (c t : ℝ) (y : ℂ) : ℂ := -(kW c t y * qW₁ c t y + ((pP t : ℝ) : ℂ) * qW₂ c y)

/-- The unit-weight third atom `A₃ = 2pQ′²`. -/
def a₃W (c t : ℝ) (y : ℂ) : ℂ := 2 * ((pP t : ℝ) : ℂ) * qW₁ c t y ^ 2

/-- The unit-weight remainder symbol `R = A₂/Q_w² + A₃/Q_w³`. -/
def fR (c : ℝ) (w y : ℂ) (t : ℝ) : ℂ := a₂W c t y / qW c t w y ^ 2 + a₃W c t y / qW c t w y ^ 3

/-- At `w = c² − χ` and real `y`, `Q_w` is `FarIntegrationByParts`'s `Q`. -/
theorem qW_ofReal (c χ y t : ℝ) : qW c t ((c ^ 2 - χ : ℝ) : ℂ) (y : ℂ) = qQ c χ y t := by
  unfold qW qQ pP; push_cast; ring

/-- **The unit-weight remainder is the symbol at `w = c² − χ`**: `R(1, 0, 0) = fR(c² − χ)`. -/
theorem rRc_one_eq (c χ y t : ℝ) :
    rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y t = fR c ((c ^ 2 - χ : ℝ) : ℂ) (y : ℂ) t := by
  have h1 : qW₁ c t (y : ℂ) = qQ₁ c y t := by unfold qW₁ qQ₁; push_cast; ring
  have h2 : qW₂ c (y : ℂ) = qQ₂ c y := by unfold qW₂ qQ₂; push_cast; ring
  have hk : kW c t (y : ℂ) = kK c y t := by unfold kW kK; push_cast; ring
  unfold fR a₂W a₃W
  rw [qW_ofReal, h1, h2, hk]
  by_cases hQ : qQ c χ y t = 0
  · unfold rRc gWc₁ gWc₂; simp [hQ]
  · rw [rRc_eq hQ]; unfold aC₁ aC₂ aC₃; simp

/-! ### Atom bounds at complex `y` -/

theorem norm_sq_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 3 / 4) : ‖y ^ 2 - 1‖ ≤ 25 / 16 := by
  calc ‖y ^ 2 - 1‖ ≤ ‖y‖ ^ 2 + 1 := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_pow, norm_one]
    _ ≤ 25 / 16 := by nlinarith [norm_nonneg y]

theorem norm_qW₁_le {c t : ℝ} {y : ℂ} (hc : 0 ≤ c) (ht : 0 ≤ t) (hy : ‖y‖ ≤ 3 / 4) :
    ‖qW₁ c t y‖ ≤ 25 / 8 * c ^ 2 * t + 3 / 2 * c := by
  unfold qW₁
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, Complex.norm_ofNat, mul_one]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (sq_nonneg c), abs_of_nonneg ht,
    abs_of_nonneg hc]
  have h1 := norm_sq_sub_one_le hy
  have h2 : 0 ≤ 2 * c ^ 2 * t := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h2, mul_le_mul_of_nonneg_left hy hc]

theorem norm_qW₂_le {c : ℝ} {y : ℂ} (hy : ‖y‖ ≤ 3 / 4) : ‖qW₂ c y‖ ≤ 25 / 8 * c ^ 2 := by
  unfold qW₂
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (norm_sq_sub_one_le hy) (by positivity : (0 : ℝ) ≤ 2 * c ^ 2)]

theorem pP_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ pP t := by unfold pP; nlinarith

theorem norm_kW_le {c t r : ℝ} {y : ℂ} (hc : 0 ≤ c) (ht : 1 ≤ t) (hy : ‖y‖ ≤ r) :
    ‖kW c t y‖ ≤ 2 * t + 2 * c * r * pP t := by
  have hp := pP_nonneg ht
  unfold kW
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, Complex.norm_ofNat, mul_one]
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t), abs_of_nonneg hc, abs_of_nonneg hp]
  nlinarith [mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 2 * c * pP t)]

theorem norm_a₂W_le {c t r : ℝ} {y : ℂ} (hc : 0 ≤ c) (ht : 1 ≤ t) (hy : ‖y‖ ≤ r) (hr : r ≤ 3 / 4) :
    ‖a₂W c t y‖ ≤ (2 * t + 2 * c * r * pP t) * (25 / 8 * c ^ 2 * t + 3 / 2 * c) + pP t * (25 / 8 * c ^ 2) := by
  have hp := pP_nonneg ht
  have hy' : ‖y‖ ≤ 3 / 4 := hy.trans hr
  unfold a₂W
  rw [norm_neg]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul (norm_kW_le hc ht hy) (norm_qW₁_le hc (by linarith) hy') (norm_nonneg _)
      ((norm_nonneg _).trans (norm_kW_le hc ht hy))
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left (norm_qW₂_le hy') hp

theorem norm_a₃W_le {c t : ℝ} {y : ℂ} (hc : 0 ≤ c) (ht : 1 ≤ t) (hy : ‖y‖ ≤ 3 / 4) :
    ‖a₃W c t y‖ ≤ 2 * pP t * (25 / 8 * c ^ 2 * t + 3 / 2 * c) ^ 2 := by
  have hp := pP_nonneg ht
  unfold a₃W
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp, norm_pow, Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_qW₁_le hc (by linarith) hy) 2)
    (by positivity)

/-! ### The lower bound on `Q_w` -/

theorem re_qW (c t : ℝ) (w y : ℂ) :
    (qW c t w y).re = c ^ 2 * pP t * (y.re ^ 2 - y.im ^ 2 - 1) - w.re + 2 * c * t * y.im := by
  simp only [qW, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, sq, Complex.one_re, Complex.sub_im, Complex.one_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

/-- **`|Q_w(y)| ≥ c²(t² − 1)/4`** for `c ≥ 80`, `t ≥ 2`, `|w − c²/2| ≤ c²` and complex `|y| ≤ 3/4`. -/
theorem le_norm_qW {c t : ℝ} {w y : ℂ} (hc : 80 ≤ c) (ht : 2 ≤ t)
    (hw : ‖w - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2) (hy : ‖y‖ ≤ 3 / 4) :
    c ^ 2 * pP t / 4 ≤ ‖qW c t w y‖ := by
  have hre : y.re ^ 2 + y.im ^ 2 ≤ 9 / 16 := by
    have h := Complex.sq_norm y
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg y]
  have him : y.im ≤ 3 / 4 := (le_abs_self _).trans ((Complex.abs_im_le_norm y).trans hy)
  have hwre : -(c ^ 2 / 2) ≤ w.re := by
    have h := (Complex.abs_re_le_norm _).trans hw
    rw [Complex.sub_re, Complex.ofReal_re] at h
    linarith [neg_abs_le (w.re - c ^ 2 / 2)]
  have hp3 : 3 ≤ pP t := by unfold pP; nlinarith
  have hpt : 3 / 2 * t ≤ pP t := by unfold pP; nlinarith
  have hc0 : 0 < c := by linarith
  have hcp : 0 ≤ c ^ 2 * pP t := by positivity
  have h1 : c ^ 2 * pP t * y.re ^ 2 ≤ c ^ 2 * pP t * (9 / 16 - y.im ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hcp
  have h2 : c * t * y.im ≤ c * t * (3 / 4) := mul_le_mul_of_nonneg_left him (by positivity)
  have h3 : c ^ 2 / 2 ≤ c ^ 2 * pP t / 6 := by nlinarith [sq_nonneg c]
  have h4 : 72 * t ≤ c * pP t := by nlinarith
  have h5 : 72 * c * t ≤ c ^ 2 * pP t := by nlinarith
  have h6 : 0 ≤ c ^ 2 * pP t * y.im ^ 2 := by positivity
  have key : c ^ 2 * pP t / 4 ≤ -(qW c t w y).re := by
    rw [re_qW]; nlinarith
  exact key.trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _))

theorem qW_ne_zero {c t : ℝ} {w y : ℂ} (hc : 80 ≤ c) (ht : 2 ≤ t)
    (hw : ‖w - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2) (hy : ‖y‖ ≤ 3 / 4) : qW c t w y ≠ 0 := by
  have hp : 0 < pP t := by unfold pP; nlinarith
  have h := le_norm_qW hc ht hw hy
  intro h0
  rw [h0, norm_zero] at h
  have : 0 < c ^ 2 * pP t / 4 := by positivity
  linarith

/-- `|Q_w(s/m)| ≥ c²(t² − 1)/4` for `2 ≤ m ≤ t` and complex `|s| ≤ 3/2`. -/
theorem le_norm_qW_div {c m t : ℝ} {w s : ℂ} (hc : 80 ≤ c) (hm : 2 ≤ m) (ht : m ≤ t)
    (hw : ‖w - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2) (hs : ‖s‖ ≤ 3 / 2) :
    c ^ 2 * pP t / 4 ≤ ‖qW c t w (s / m)‖ := by
  refine le_norm_qW hc (by linarith) hw ?_
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), div_le_iff₀ (by linarith)]
  nlinarith

/-! ### The bound on the symbol -/

theorem norm_fR_le_of {c t A₂ A₃ q : ℝ} {w y : ℂ} (hq : 0 < q) (hQ : q ≤ ‖qW c t w y‖)
    (h₂ : ‖a₂W c t y‖ ≤ A₂) (h₃ : ‖a₃W c t y‖ ≤ A₃) : ‖fR c w y t‖ ≤ A₂ / q ^ 2 + A₃ / q ^ 3 := by
  unfold fR
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_pow]
    exact div_le_div₀ ((norm_nonneg _).trans h₂) h₂ (by positivity) (pow_le_pow_left₀ hq.le hQ 2)
  · rw [norm_div, norm_pow]
    exact div_le_div₀ ((norm_nonneg _).trans h₃) h₃ (by positivity) (pow_le_pow_left₀ hq.le hQ 3)

/-- The second-atom ratio: `A₂/q² ≤ 200/(cmt) + 300/(c²t²)` with `q = c²(t² − 1)/4` and `|y| ≤ 3/(2m)`. -/
theorem a₂_ratio_le {c m t : ℝ} (hc : 80 ≤ c) (hm : 2 ≤ m) (ht : m ≤ t) :
    ((2 * t + 2 * c * (3 / (2 * m)) * pP t) * (25 / 8 * c ^ 2 * t + 3 / 2 * c) + pP t * (25 / 8 * c ^ 2))
        / (c ^ 2 * pP t / 4) ^ 2 ≤ 200 / (c * m * t) + 300 / (c ^ 2 * t ^ 2) := by
  set p := pP t with hpdef
  have hc0 : 0 < c := by linarith
  have hm0 : 0 < m := by linarith
  have ht0 : 0 < t := by linarith
  have hp3 : 3 * t ^ 2 ≤ 4 * p := by rw [hpdef]; unfold pP; nlinarith
  have hpt : 3 / 2 * t ≤ p := by rw [hpdef]; unfold pP; nlinarith
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < (c ^ 2 * p / 4) ^ 2 := by positivity
  have hsplit : (2 * t + 2 * c * (3 / (2 * m)) * p) * (25 / 8 * c ^ 2 * t + 3 / 2 * c) + p * (25 / 8 * c ^ 2)
      = 75 / 8 * c ^ 3 * p * t / m
        + (25 / 4 * c ^ 2 * t ^ 2 + 3 * c * t + 9 / 2 * c ^ 2 * p / m + 25 / 8 * c ^ 2 * p) := by
    field_simp; ring
  rw [hsplit, add_div]
  refine add_le_add ?_ ?_
  · rw [div_le_div_iff₀ hq0 (by positivity)]
    have e : 75 / 8 * c ^ 3 * p * t / m * (c * m * t) = 75 / 8 * c ^ 4 * p * t ^ 2 := by
      field_simp
    rw [e]
    have : 0 ≤ c ^ 4 * p := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hp3 this]
  · rw [div_le_div_iff₀ hq0 (by positivity)]
    have hpm : p / m ≤ p / 2 := div_le_div_of_nonneg_left hp0.le (by norm_num) hm
    have hR : 25 / 4 * c ^ 2 * t ^ 2 + 3 * c * t + 9 / 2 * c ^ 2 * p / m + 25 / 8 * c ^ 2 * p
        ≤ 1648 / 120 * (c ^ 2 * p) := by
      have e1 : 25 / 4 * c ^ 2 * t ^ 2 ≤ 25 / 3 * (c ^ 2 * p) := by nlinarith [sq_nonneg c]
      have e2' : 120 * t ≤ c * p := by nlinarith
      have e2 : 3 * c * t ≤ 1 / 40 * (c ^ 2 * p) := by nlinarith [mul_le_mul_of_nonneg_left e2' hc0.le]
      have e3 : 9 / 2 * c ^ 2 * p / m ≤ 9 / 4 * (c ^ 2 * p) := by
        have : 9 / 2 * c ^ 2 * p / m = 9 / 2 * c ^ 2 * (p / m) := by ring
        rw [this]; nlinarith [mul_le_mul_of_nonneg_left hpm (by positivity : (0 : ℝ) ≤ 9 / 2 * c ^ 2)]
      linarith
    have hc2p : 0 ≤ c ^ 2 * p := by positivity
    have hct : 0 ≤ c ^ 2 * t ^ 2 := by positivity
    calc (25 / 4 * c ^ 2 * t ^ 2 + 3 * c * t + 9 / 2 * c ^ 2 * p / m + 25 / 8 * c ^ 2 * p) * (c ^ 2 * t ^ 2)
        ≤ 1648 / 120 * (c ^ 2 * p) * (c ^ 2 * t ^ 2) := mul_le_mul_of_nonneg_right hR hct
      _ ≤ 1648 / 120 * (c ^ 2 * p) * (c ^ 2 * (4 / 3 * p)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 300 * (c ^ 2 * p / 4) ^ 2 := by nlinarith [mul_nonneg hc2p hc2p]

/-- The third-atom ratio: `A₃/q³ ≤ 2300/(c²t²)` with `q = c²(t² − 1)/4`. -/
theorem a₃_ratio_le {c t : ℝ} (hc : 80 ≤ c) (ht : 2 ≤ t) :
    2 * pP t * (25 / 8 * c ^ 2 * t + 3 / 2 * c) ^ 2 / (c ^ 2 * pP t / 4) ^ 3 ≤ 2300 / (c ^ 2 * t ^ 2) := by
  set p := pP t with hpdef
  have hc0 : 0 < c := by linarith
  have ht0 : 0 < t := by linarith
  have hp3 : 3 * t ^ 2 ≤ 4 * p := by rw [hpdef]; unfold pP; nlinarith
  have hp0 : 0 < p := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hY : 25 / 8 * c ^ 2 * t + 3 / 2 * c ≤ 1003 / 320 * (c ^ 2 * t) := by nlinarith
  have hY0 : 0 ≤ 25 / 8 * c ^ 2 * t + 3 / 2 * c := by positivity
  have hY2 : (25 / 8 * c ^ 2 * t + 3 / 2 * c) ^ 2 ≤ (1003 / 320) ^ 2 * (c ^ 2 * t) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hY0 hY 2
  have ht4 : (t ^ 2) ^ 2 ≤ (4 / 3 * p) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hc6 : 0 ≤ c ^ 6 := by positivity
  calc 2 * p * (25 / 8 * c ^ 2 * t + 3 / 2 * c) ^ 2 * (c ^ 2 * t ^ 2)
      ≤ 2 * p * ((1003 / 320) ^ 2 * (c ^ 2 * t) ^ 2) * (c ^ 2 * t ^ 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY2 (by positivity)) (by positivity)
    _ = 2 * (1003 / 320) ^ 2 * p * c ^ 6 * (t ^ 2) ^ 2 := by ring
    _ ≤ 2 * (1003 / 320) ^ 2 * p * c ^ 6 * (4 / 3 * p) ^ 2 :=
        mul_le_mul_of_nonneg_left ht4 (by positivity)
    _ ≤ 2300 * (c ^ 2 * p / 4) ^ 3 := by
        have : 0 ≤ p ^ 3 * c ^ 6 := by positivity
        nlinarith

/-- **The symbol bound**: `|fR(w, s/m, t)| ≤ 200/(cmt) + 2600/(c²t²)` for `c ≥ 80`, `2 ≤ m ≤ t`,
`|w − c²/2| ≤ c²` and complex `|s| ≤ 3/2`. -/
theorem norm_fR_le {c m t : ℝ} {w s : ℂ} (hc : 80 ≤ c) (hm : 2 ≤ m) (ht : m ≤ t)
    (hw : ‖w - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2) (hs : ‖s‖ ≤ 3 / 2) :
    ‖fR c w (s / m) t‖ ≤ 200 / (c * m * t) + 2600 / (c ^ 2 * t ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hm0 : 0 < m := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hp : 0 < pP t := by unfold pP; nlinarith
  have hy : ‖s / (m : ℂ)‖ ≤ 3 / (2 * m) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0, div_le_div_iff₀ hm0 (by positivity)]
    nlinarith
  have hr : 3 / (2 * m) ≤ 3 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h := norm_fR_le_of (by positivity) (le_norm_qW_div hc hm ht hw hs)
    (norm_a₂W_le hc0.le ht1 hy hr) (norm_a₃W_le hc0.le ht1 (hy.trans hr))
  refine h.trans ?_
  have e : 2600 / (c ^ 2 * t ^ 2) = 300 / (c ^ 2 * t ^ 2) + 2300 / (c ^ 2 * t ^ 2) := by ring
  rw [e, ← add_assoc]
  exact add_le_add (a₂_ratio_le hc hm ht) (a₃_ratio_le hc (by linarith))

/-! ### Holomorphy -/

theorem differentiable_qW_y (c t : ℝ) (w : ℂ) : Differentiable ℂ (fun y => qW c t w y) := by
  unfold qW; fun_prop

theorem differentiable_qW_w (c t : ℝ) (y : ℂ) : Differentiable ℂ (fun w => qW c t w y) := by
  unfold qW; fun_prop

theorem differentiable_a₂W (c t : ℝ) : Differentiable ℂ (a₂W c t) := by
  unfold a₂W kW qW₁ qW₂; fun_prop

theorem differentiable_a₃W (c t : ℝ) : Differentiable ℂ (a₃W c t) := by
  unfold a₃W qW₁; fun_prop

theorem differentiableAt_fR_y {c t : ℝ} {w y : ℂ} (hQ : qW c t w y ≠ 0) :
    DifferentiableAt ℂ (fun y => fR c w y t) y := by
  have hq := differentiable_qW_y c t w y
  unfold fR
  exact ((differentiable_a₂W c t y).div (hq.pow 2) (pow_ne_zero 2 hQ)).add
    ((differentiable_a₃W c t y).div (hq.pow 3) (pow_ne_zero 3 hQ))

theorem differentiableAt_fR_w {c t : ℝ} {w y : ℂ} (hQ : qW c t w y ≠ 0) :
    DifferentiableAt ℂ (fun w => fR c w y t) w := by
  have hq : DifferentiableAt ℂ (fun w => qW c t w y) w := differentiable_qW_w c t y w
  have h2 : DifferentiableAt ℂ (fun w => a₂W c t y / qW c t w y ^ 2) w :=
    (differentiableAt_const (a₂W c t y)).div (hq.pow 2) (pow_ne_zero 2 hQ)
  have h3 : DifferentiableAt ℂ (fun w => a₃W c t y / qW c t w y ^ 3) w :=
    (differentiableAt_const (a₃W c t y)).div (hq.pow 3) (pow_ne_zero 3 hQ)
  exact h2.add h3

/-- `s ↦ fR(w, s/m, t)` is holomorphic on the closed disc of radius `3/2`. -/
theorem differentiableOn_fR_s {c m t : ℝ} {w : ℂ} (hc : 80 ≤ c) (hm : 2 ≤ m) (ht : m ≤ t)
    (hw : ‖w - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2) :
    DifferentiableOn ℂ (fun s : ℂ => fR c w (s / m) t) (closedBall 0 (3 / 2)) := by
  intro s hs
  have hs' : ‖s‖ ≤ 3 / 2 := by simpa using hs
  have hp : 0 < pP t := by unfold pP; nlinarith
  have hQ : qW c t w (s / m) ≠ 0 := by
    have h := le_norm_qW_div hc hm ht hw hs'
    intro h0; rw [h0, norm_zero] at h
    have : 0 < c ^ 2 * pP t / 4 := by have : 0 < c := by linarith
                                      positivity
    linarith
  have hd : DifferentiableAt ℂ (fun z : ℂ => z / (m : ℂ)) s := by fun_prop
  have h := DifferentiableAt.comp (g := fun y => fR c w y t) (f := fun z : ℂ => z / (m : ℂ)) s
    (differentiableAt_fR_y hQ) hd
  exact h.differentiableWithinAt

/-- `w ↦ fR(w, y, t)` is holomorphic on the disc `|w − c²/2| < c²` and continuous on its closure. -/
theorem diffContOnCl_fR_w {c t : ℝ} {y : ℂ} (hc : 80 ≤ c) (ht : 2 ≤ t) (hy : ‖y‖ ≤ 3 / 4) :
    DiffContOnCl ℂ (fun w => fR c w y t) (ball ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2)) := by
  have hc2 : c ^ 2 ≠ 0 := by positivity
  refine DifferentiableOn.diffContOnCl ?_
  rw [closure_ball _ hc2]
  intro w hw
  have hw' : ‖w - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2 := by simpa [dist_eq_norm] using hw
  exact (differentiableAt_fR_w (qW_ne_zero hc ht hw' hy)).differentiableWithinAt

/-- Joint continuity of `(w, y, t) ↦ fR(w, y, t)` where `|w − c²/2| ≤ c²`, `|y| ≤ 3/4`, `t ≥ 2`. -/
theorem continuousOn_fR {c : ℝ} (hc : 80 ≤ c) :
    ContinuousOn (fun p : ℂ × ℂ × ℝ => fR c p.1 p.2.1 p.2.2)
      {p | ‖p.1 - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2 ∧ ‖p.2.1‖ ≤ 3 / 4 ∧ 2 ≤ p.2.2} := by
  have hQ : Continuous (fun p : ℂ × ℂ × ℝ => qW c p.2.2 p.1 p.2.1) := by unfold qW pP; fun_prop
  have h₂ : Continuous (fun p : ℂ × ℂ × ℝ => a₂W c p.2.2 p.2.1) := by unfold a₂W kW qW₁ qW₂ pP; fun_prop
  have h₃ : Continuous (fun p : ℂ × ℂ × ℝ => a₃W c p.2.2 p.2.1) := by unfold a₃W qW₁ pP; fun_prop
  have hne : ∀ p ∈ {p : ℂ × ℂ × ℝ | ‖p.1 - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2 ∧ ‖p.2.1‖ ≤ 3 / 4 ∧ 2 ≤ p.2.2},
      qW c p.2.2 p.1 p.2.1 ≠ 0 := fun p hp => qW_ne_zero hc hp.2.2 hp.1 hp.2.1
  have k₂ : ContinuousOn (fun p : ℂ × ℂ × ℝ => a₂W c p.2.2 p.2.1 / qW c p.2.2 p.1 p.2.1 ^ 2)
      {p | ‖p.1 - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2 ∧ ‖p.2.1‖ ≤ 3 / 4 ∧ 2 ≤ p.2.2} :=
    h₂.continuousOn.div (hQ.pow 2).continuousOn fun p hp => pow_ne_zero 2 (hne p hp)
  have k₃ : ContinuousOn (fun p : ℂ × ℂ × ℝ => a₃W c p.2.2 p.2.1 / qW c p.2.2 p.1 p.2.1 ^ 3)
      {p | ‖p.1 - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2 ∧ ‖p.2.1‖ ≤ 3 / 4 ∧ 2 ≤ p.2.2} :=
    h₃.continuousOn.div (hQ.pow 3).continuousOn fun p hp => pow_ne_zero 3 (hne p hp)
  exact k₂.add k₃

/-! ### The Bernstein–Riesz bound -/

/-- **The integrated symbol bound**: if `|ψ_g| ≤ F` with `g` continuous and even, then
`|∫_{−1}^{1} g(s) e^{ic(s/m)t} fR(w, s/m, t) ds| ≤ 3F(200/(cmt) + 2600/(c²t²))`. -/
theorem norm_integral_fR_le {c m t F : ℝ} {w : ℂ} {gj : ℝ → ℝ} (hgj : ContinuousOn gj (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, gj (-s) = gj s) (hpsi : ∀ x, |psi c gj x| ≤ F)
    (hc : 80 ≤ c) (hm : 2 ≤ m) (ht : m ≤ t) (hw : ‖w - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2) :
    ‖∫ s in (-1 : ℝ)..1, (gj s : ℂ) * eF c (s / m) t * fR c w ((s / m : ℝ) : ℂ) t‖
      ≤ 3 * F * (200 / (c * m * t) + 2600 / (c ^ 2 * t ^ 2)) := by
  have hc0 : c ≠ 0 := by positivity
  have hint : (∫ s in (-1 : ℝ)..1, (gj s : ℂ) * eF c (s / m) t * fR c w ((s / m : ℝ) : ℂ) t)
      = ∫ s in (-1 : ℝ)..1, (fun s : ℝ => (gj s : ℂ)) s * (fun z : ℂ => fR c w (z / m) t) (s : ℂ)
          * Cvs.L2a.BernsteinRieszSymbolBounds.ek c (t / m) s := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    have he : eF c (s / m) t = Cvs.L2a.BernsteinRieszSymbolBounds.ek c (t / m) s := by
      unfold eF Cvs.L2a.BernsteinRieszSymbolBounds.ek; rw [show c * (s / m) * t = c * (t / m) * s by ring]
    rw [he, Complex.ofReal_div]; ring
  rw [hint]
  have hg : ContinuousOn (fun s : ℝ => (gj s : ℂ)) (Icc (-1) 1) :=
    Complex.continuous_ofReal.comp_continuousOn hgj
  have h := Cvs.L2a.BernsteinRieszSymbolBounds.norm_integral_holo_le hg hc0 (Cvs.L2a.BernsteinRieszSymbolBounds.hF_of_psi hgj heven hpsi) (R := 3 / 2)
    (by norm_num) (differentiableOn_fR_s hc hm ht hw)
    (fun z hz => norm_fR_le hc hm ht hw (by rw [mem_sphere_zero_iff_norm] at hz; linarith)) (t / m)
  refine h.trans (le_of_eq ?_)
  ring

end Cvs.L2a.UnitWeightRemainderSymbol
