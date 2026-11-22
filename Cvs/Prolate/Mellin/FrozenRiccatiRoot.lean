import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The frozen root of the prolate Riccati map

The fixed point `σ = (a + √(a² + 4b))/2` of `r ↦ a + b/r` with `a = 1 − χw`, `b = c²w` satisfies `σ² = aσ + b`.
For `|χ| ≤ c²` and `c²|w| ≤ 1/16` it has `|σ − 1| ≤ 4c²|w|`, `|σ(w) − σ(w′)| ≤ 6c²|w − w′|`, and its logarithm
`h = log σ` has `|h(w)| ≤ 6c²|w|`, `|h(w) − h(w′)| ≤ 16c²|w − w′|`; `σ` and `h` are analytic for `c²|w| < 1/8`
and commute with conjugation.
-/

noncomputable section

open Complex
open scoped Real

namespace Cvs.Prolate.Mellin.FrozenRiccatiRoot

/-- The principal square root `z^{1/2}`. -/
def csq (z : ℂ) : ℂ := z ^ ((2 : ℂ)⁻¹)

theorem csq_sq (z : ℂ) : csq z ^ 2 = z := by unfold csq; exact cpow_ofNat_inv_pow z 2

/-- The principal square root has nonnegative real part. -/
theorem re_csq_nonneg (z : ℂ) : 0 ≤ (csq z).re := by
  unfold csq
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [cpow_def_of_ne_zero hz, exp_re]
  refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
  · have h1 := neg_pi_lt_arg z
    have : (log z * (2 : ℂ)⁻¹).im = z.arg / 2 := by
      rw [show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, mul_comm, im_ofReal_mul, log_im]; ring
    rw [this]; linarith
  · have h1 := arg_le_pi z
    have : (log z * (2 : ℂ)⁻¹).im = z.arg / 2 := by
      rw [show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, mul_comm, im_ofReal_mul, log_im]; ring
    rw [this]; linarith

/-- `|√(1 + u) − 1| ≤ |u|`. -/
theorem norm_csq_sub_one_le (u : ℂ) : ‖csq (1 + u) - 1‖ ≤ ‖u‖ := by
  set r := csq (1 + u)
  have hr : 0 ≤ r.re := re_csq_nonneg _
  have hfac : (r - 1) * (r + 1) = u := by
    have := csq_sq (1 + u); rw [show (r - 1) * (r + 1) = r ^ 2 - 1 by ring, this]; ring
  have h1 : 1 ≤ ‖r + 1‖ := by
    have := Complex.re_le_norm (r + 1); simp at this; linarith
  calc ‖r - 1‖ ≤ ‖r - 1‖ * ‖r + 1‖ := le_mul_of_one_le_right (norm_nonneg _) h1
    _ = ‖u‖ := by rw [← norm_mul, hfac]

/-- The frozen root `σ(w) = (a + √(a² + 4b))/2`, `a = 1 − χw`, `b = c²w`. -/
def sig (χ c : ℝ) (w : ℂ) : ℂ := ((1 - χ * w) + csq ((1 - χ * w) ^ 2 + 4 * (c ^ 2 * w))) / 2

/-- **The fixed point**: `σ² = (1 − χw)σ + c²w`. -/
theorem sig_sq (χ c : ℝ) (w : ℂ) : sig χ c w ^ 2 = (1 - χ * w) * sig χ c w + c ^ 2 * w := by
  have h := csq_sq ((1 - χ * w) ^ 2 + 4 * (c ^ 2 * w))
  unfold sig
  linear_combination h / 4

theorem sig_zero (χ c : ℝ) : sig χ c 0 = 1 := by
  unfold sig csq; simp

/-- The discriminant is `1 + u` with `|u| ≤ 7c²|w|` when `|χ| ≤ c²` and `c²|w| ≤ 1`. -/
theorem disc_eq {χ c : ℝ} (w : ℂ) :
    (1 - χ * w) ^ 2 + 4 * (c ^ 2 * w) = 1 + (-(2 * χ * w) + (χ * w) ^ 2 + 4 * (c ^ 2 * w)) := by ring

theorem norm_u_le {χ c : ℝ} (hχ : |χ| ≤ c ^ 2) {w : ℂ} (hw : c ^ 2 * ‖w‖ ≤ 1) :
    ‖-(2 * χ * w) + (χ * w) ^ 2 + 4 * (c ^ 2 * w)‖ ≤ 7 * (c ^ 2 * ‖w‖) := by
  have hχw : ‖(χ : ℂ) * w‖ ≤ c ^ 2 * ‖w‖ := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
  have hc : ‖((c : ℂ) ^ 2 * w)‖ = c ^ 2 * ‖w‖ := by
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
  have ht0 : 0 ≤ c ^ 2 * ‖w‖ := by positivity
  calc ‖-(2 * χ * w) + (χ * w) ^ 2 + 4 * (c ^ 2 * w)‖
      ≤ ‖-(2 * χ * w)‖ + ‖(χ * w) ^ 2‖ + ‖4 * (c ^ 2 * w)‖ := norm_add₃_le
    _ = 2 * ‖(χ : ℂ) * w‖ + ‖(χ : ℂ) * w‖ ^ 2 + 4 * ‖((c : ℂ) ^ 2 * w)‖ := by
        rw [norm_neg, show (2 : ℂ) * χ * w = 2 * (χ * w) by ring, norm_mul, norm_pow, norm_mul]; norm_num
    _ ≤ 2 * (c ^ 2 * ‖w‖) + (c ^ 2 * ‖w‖) ^ 2 + 4 * (c ^ 2 * ‖w‖) := by
        rw [hc]; gcongr
    _ ≤ 7 * (c ^ 2 * ‖w‖) := by nlinarith

/-- **`|σ(w) − 1| ≤ 4c²|w|`** for `|χ| ≤ c²`, `c²|w| ≤ 1`. -/
theorem norm_sig_sub_one_le {χ c : ℝ} (hχ : |χ| ≤ c ^ 2) {w : ℂ} (hw : c ^ 2 * ‖w‖ ≤ 1) :
    ‖sig χ c w - 1‖ ≤ 4 * (c ^ 2 * ‖w‖) := by
  have hχw : ‖(χ : ℂ) * w‖ ≤ c ^ 2 * ‖w‖ := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
  have hs := norm_csq_sub_one_le (-(2 * χ * w) + (χ * w) ^ 2 + 4 * (c ^ 2 * w))
  rw [← disc_eq] at hs
  have hu := norm_u_le hχ hw
  have e : sig χ c w - 1 = (-(χ * w) + (csq ((1 - χ * w) ^ 2 + 4 * (c ^ 2 * w)) - 1)) / 2 := by
    unfold sig; ring
  rw [e, norm_div, Complex.norm_ofNat]
  have := norm_add_le (-((χ : ℂ) * w)) (csq ((1 - χ * w) ^ 2 + 4 * (c ^ 2 * w)) - 1)
  rw [norm_neg] at this
  linarith

/-- **The frozen root is Lipschitz**: `|σ(w) − σ(w′)| ≤ 6c²|w − w′|` for `c²|w|, c²|w′| ≤ 1/16`. -/
theorem norm_sig_sub_le {χ c : ℝ} (hχ : |χ| ≤ c ^ 2) {w w' : ℂ} (hw : c ^ 2 * ‖w‖ ≤ 1 / 16)
    (hw' : c ^ 2 * ‖w'‖ ≤ 1 / 16) : ‖sig χ c w - sig χ c w'‖ ≤ 6 * c ^ 2 * ‖w - w'‖ := by
  set s := sig χ c w
  set s' := sig χ c w'
  have h1 := norm_sig_sub_one_le hχ (w := w) (by linarith)
  have h2 := norm_sig_sub_one_le hχ (w := w') (by linarith)
  have hχw : ‖(χ : ℂ) * w‖ ≤ c ^ 2 * ‖w‖ := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
  have hid : (s - s') * (s + s' - (1 - χ * w)) = (w - w') * (c ^ 2 - χ * s') := by
    have e1 := sig_sq χ c w
    have e2 := sig_sq χ c w'
    linear_combination e1 - e2
  have hden : 7 / 16 ≤ ‖s + s' - (1 - χ * w)‖ := by
    have e : s + s' - (1 - χ * w) = 1 + ((s - 1) + (s' - 1) + χ * w) := by ring
    rw [e]
    have := norm_sub_norm_le (1 : ℂ) (-((s - 1) + (s' - 1) + χ * w))
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    have := norm_add₃_le (a := s - 1) (b := s' - 1) (c := (χ : ℂ) * w)
    linarith
  have hnum : ‖(c : ℂ) ^ 2 - χ * s'‖ ≤ 9 / 4 * c ^ 2 := by
    have hs' : ‖s'‖ ≤ 5 / 4 := by
      have := norm_sub_norm_le s' 1; rw [norm_one] at this; linarith
    have hc : ‖(c : ℂ) ^ 2‖ = c ^ 2 := by rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
    calc ‖(c : ℂ) ^ 2 - χ * s'‖ ≤ ‖(c : ℂ) ^ 2‖ + ‖(χ : ℂ)‖ * ‖s'‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ c ^ 2 + c ^ 2 * (5 / 4) := by
          rw [hc, norm_real, Real.norm_eq_abs]; gcongr
      _ = 9 / 4 * c ^ 2 := by ring
  have hpos : 0 < ‖s + s' - (1 - χ * w)‖ := by linarith
  have key : ‖s - s'‖ * ‖s + s' - (1 - χ * w)‖ = ‖w - w'‖ * ‖(c : ℂ) ^ 2 - χ * s'‖ := by
    rw [← norm_mul, ← norm_mul, hid]
  have hc0 : 0 ≤ c ^ 2 := sq_nonneg c
  have : ‖s - s'‖ * (7 / 16) ≤ ‖w - w'‖ * (9 / 4 * c ^ 2) := by
    calc ‖s - s'‖ * (7 / 16) ≤ ‖s - s'‖ * ‖s + s' - (1 - χ * w)‖ :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ = ‖w - w'‖ * ‖(c : ℂ) ^ 2 - χ * s'‖ := key
      _ ≤ ‖w - w'‖ * (9 / 4 * c ^ 2) := mul_le_mul_of_nonneg_left hnum (norm_nonneg _)
  nlinarith [norm_nonneg (w - w')]

/-- The logarithm `h(w) = log σ(w)` of the frozen root. -/
def hh (χ c : ℝ) (w : ℂ) : ℂ := Complex.log (sig χ c w)

/-- `|h(w)| ≤ 6c²|w|` for `c²|w| ≤ 1/8`. -/
theorem norm_hh_le {χ c : ℝ} (hχ : |χ| ≤ c ^ 2) {w : ℂ} (hw : c ^ 2 * ‖w‖ ≤ 1 / 8) :
    ‖hh χ c w‖ ≤ 6 * (c ^ 2 * ‖w‖) := by
  have h1 := norm_sig_sub_one_le hχ (w := w) (by linarith)
  unfold hh
  have e : sig χ c w = 1 + (sig χ c w - 1) := by ring
  rw [e]
  refine (norm_log_one_add_half_le_self (by linarith)).trans ?_
  linarith

/-- `log x − log y` is at most `(8/3)|x − y|` on the disc `|z − 1| ≤ 1/4`. -/
theorem norm_log_sub_log_le {x y : ℂ} (hx : ‖x - 1‖ ≤ 1 / 4) (hy : ‖y - 1‖ ≤ 1 / 4) :
    ‖Complex.log x - Complex.log y‖ ≤ 8 / 3 * ‖x - y‖ := by
  have hy0 : y ≠ 0 := fun h => by rw [h] at hy; norm_num at hy
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; norm_num at hx
  have hyn : 3 / 4 ≤ ‖y‖ := by have := norm_sub_norm_le 1 y; rw [norm_one, norm_sub_rev] at this; linarith
  have hre : ∀ z : ℂ, ‖z - 1‖ ≤ 1 / 4 → 0 < z.re := fun z hz => by
    have := Complex.abs_re_le_norm (z - 1); simp at this
    have := abs_le.1 (this.trans hz); linarith
  have harg : ∀ z : ℂ, ‖z - 1‖ ≤ 1 / 4 → |z.arg| < π / 2 := fun z hz =>
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre z hz))
  have hsplit : Complex.log (x * y⁻¹) = Complex.log x + Complex.log y⁻¹ := by
    rw [Complex.log_mul_eq_add_log_iff hx0 (inv_ne_zero hy0)]
    have h1 := harg x hx
    have h2 : |(y⁻¹).arg| < π / 2 := by
      rw [Complex.arg_inv]
      have hne : y.arg ≠ π := fun h => by
        have := harg y hy; rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]
      simp only [hne, if_false]; rw [abs_neg]; exact harg y hy
    constructor <;> linarith [abs_lt.1 h1, abs_lt.1 h2]
  have hinv : Complex.log y⁻¹ = -Complex.log y := by
    rw [Complex.log_inv]
    have hne : y.arg ≠ π := fun h => by
      have := harg y hy; rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]
    simp [hne]
  have e : Complex.log x - Complex.log y = Complex.log (1 + (x - y) / y) := by
    rw [show 1 + (x - y) / y = x * y⁻¹ by field_simp; ring, hsplit, hinv]; ring
  have hz : ‖(x - y) / y‖ ≤ 4 / 3 * ‖x - y‖ := by
    rw [norm_div, div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg (x - y)]
  have hxy : ‖x - y‖ ≤ 1 / 2 := by
    have := norm_sub_le (x - 1) (y - 1); rw [sub_sub_sub_cancel_right] at this; linarith
  have hz1 : ‖(x - y) / y‖ ≤ 2 / 3 := by linarith
  rw [e]
  refine (norm_log_one_add_le (by linarith)).trans ?_
  set t := ‖(x - y) / y‖
  have ht0 : 0 ≤ t := norm_nonneg _
  have h3 : (1 - t)⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have : t ^ 2 * (1 - t)⁻¹ / 2 + t ≤ 2 * t := by
    have : t ^ 2 * (1 - t)⁻¹ ≤ t ^ 2 * 3 := mul_le_mul_of_nonneg_left h3 (sq_nonneg t)
    nlinarith
  linarith

/-- **`h` is Lipschitz**: `|h(w) − h(w′)| ≤ 16c²|w − w′|` for `c²|w|, c²|w′| ≤ 1/16`. -/
theorem norm_hh_sub_le {χ c : ℝ} (hχ : |χ| ≤ c ^ 2) {w w' : ℂ} (hw : c ^ 2 * ‖w‖ ≤ 1 / 16)
    (hw' : c ^ 2 * ‖w'‖ ≤ 1 / 16) : ‖hh χ c w - hh χ c w'‖ ≤ 16 * c ^ 2 * ‖w - w'‖ := by
  have h1 := norm_sig_sub_one_le hχ (w := w) (by linarith)
  have h2 := norm_sig_sub_one_le hχ (w := w') (by linarith)
  have hl := norm_log_sub_log_le (x := sig χ c w) (y := sig χ c w') (by linarith) (by linarith)
  have hs := norm_sig_sub_le hχ hw hw'
  unfold hh
  calc _ ≤ 8 / 3 * ‖sig χ c w - sig χ c w'‖ := hl
    _ ≤ 8 / 3 * (6 * c ^ 2 * ‖w - w'‖) := by gcongr
    _ = 16 * c ^ 2 * ‖w - w'‖ := by ring

/-- The discriminant lies in the slit plane for `c²|w| < 1/8`. -/
theorem disc_mem_slitPlane {χ c : ℝ} (hχ : |χ| ≤ c ^ 2) {w : ℂ} (hw : c ^ 2 * ‖w‖ < 1 / 8) :
    (1 - χ * w) ^ 2 + 4 * (c ^ 2 * w) ∈ slitPlane := by
  rw [disc_eq]
  have hu := norm_u_le hχ (w := w) (by linarith)
  refine (fun {z : ℂ} (h : 0 < z.re) => mem_slitPlane_iff.2 (Or.inl h)) ?_
  have := Complex.abs_re_le_norm (-(2 * χ * w) + (χ * w) ^ 2 + 4 * (c ^ 2 * w))
  have := abs_le.1 (this.trans hu)
  rw [Complex.add_re, Complex.one_re]
  linarith

/-- `σ` is complex differentiable at every `w` with `c²|w| < 1/8`. -/
theorem differentiableAt_sig {χ c : ℝ} (hχ : |χ| ≤ c ^ 2) {w : ℂ} (hw : c ^ 2 * ‖w‖ < 1 / 8) :
    DifferentiableAt ℂ (sig χ c) w := by
  have hd : DifferentiableAt ℂ (fun w : ℂ => (1 - χ * w) ^ 2 + 4 * (c ^ 2 * w)) w := by fun_prop
  have hs : DifferentiableAt ℂ (fun w : ℂ => csq ((1 - χ * w) ^ 2 + 4 * (c ^ 2 * w))) w := by
    unfold csq
    exact hd.cpow_const (disc_mem_slitPlane hχ hw)
  unfold sig
  exact (((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)).add hs).div_const _

/-- `h` is complex differentiable at every `w` with `c²|w| < 1/8`. -/
theorem differentiableAt_hh {χ c : ℝ} (hχ : |χ| ≤ c ^ 2) {w : ℂ} (hw : c ^ 2 * ‖w‖ < 1 / 8) :
    DifferentiableAt ℂ (hh χ c) w := by
  have h1 := norm_sig_sub_one_le hχ (w := w) (by linarith)
  have hre : 0 < (sig χ c w).re := by
    have := Complex.abs_re_le_norm (sig χ c w - 1); simp at this
    have := abs_le.1 (this.trans h1); linarith
  exact (differentiableAt_sig hχ hw).clog ((fun {z : ℂ} (h : 0 < z.re) => mem_slitPlane_iff.2 (Or.inl h)) hre)

/-- **`σ` commutes with conjugation** for `c²|w| < 1/8`. -/
theorem sig_conj {χ c : ℝ} (hχ : |χ| ≤ c ^ 2) {w : ℂ} (hw : c ^ 2 * ‖w‖ < 1 / 8) :
    sig χ c ((starRingEnd ℂ) w) = (starRingEnd ℂ) (sig χ c w) := by
  set Q := (1 - χ * w) ^ 2 + 4 * (c ^ 2 * w) with hQ
  have hQs := disc_mem_slitPlane hχ hw
  have hQarg : Q.arg ≠ π := by
    intro h
    have := (mem_slitPlane_iff_arg.1 hQs).1
    exact this h
  have hQc : (1 - χ * (starRingEnd ℂ) w) ^ 2 + 4 * (c ^ 2 * (starRingEnd ℂ) w) = (starRingEnd ℂ) Q := by
    simp [hQ, map_add, map_mul, map_sub, map_pow, Complex.conj_ofReal, map_ofNat]
  have hcs : csq ((starRingEnd ℂ) Q) = (starRingEnd ℂ) (csq Q) := by
    unfold csq
    have h := cpow_conj Q (2 : ℂ)⁻¹ hQarg
    have h2 : (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp [map_ofNat]
    rw [h2] at h
    rw [h, Complex.conj_conj]
  unfold sig
  rw [hQc, hcs, map_div₀, map_add, map_sub, map_one, map_mul, Complex.conj_ofReal, map_ofNat]

/-- **`h` commutes with conjugation** for `c²|w| < 1/8`. -/
theorem hh_conj {χ c : ℝ} (hχ : |χ| ≤ c ^ 2) {w : ℂ} (hw : c ^ 2 * ‖w‖ < 1 / 8) :
    hh χ c ((starRingEnd ℂ) w) = (starRingEnd ℂ) (hh χ c w) := by
  have h1 := norm_sig_sub_one_le hχ (w := w) (by linarith)
  have hre : 0 < (sig χ c w).re := by
    have := Complex.abs_re_le_norm (sig χ c w - 1); simp at this
    have := abs_le.1 (this.trans h1); linarith
  have harg : (sig χ c w).arg ≠ π := by
    have := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    intro h; rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]
  unfold hh
  rw [sig_conj hχ hw, Complex.log_conj _ harg]

end Cvs.Prolate.Mellin.FrozenRiccatiRoot

end
