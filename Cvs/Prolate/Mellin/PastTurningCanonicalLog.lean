import Mathlib
import Cvs.Prolate.Mellin.FrozenRootCanonicalLog
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.PastTurningErrorsSummed
import Cvs.Prolate.Mellin.PastTurningRootSizes
import Cvs.Prolate.Mellin.PastTurningStepErrors
import Cvs.Prolate.Mellin.PastTurningStepForcing
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Upstream.ArsinhLipschitzStrip
import Cvs.Upstream.ComplexArsinhStrip
import Cvs.Upstream.InvSqrtKernelStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The canonical logarithm of the frozen root against the WKB phase past the turning point

`ash` is holomorphic on `Re t > 0` with `ash′ = k = 1/√(t² + 1)` and `k′ = −tk³`. On `Re t > 0`, `Im t ≥ 1 + ε/4`,
`|√(t² + 1)| ≥ √ε|t|/3`, so `|k′| ≤ 27/ε^{3/2}`, and a second-order Taylor bound holds on that convex set. With
`k(u/2c) = 2c/S` and `u/(2S(S + 2c)) = 1/(2u) − c/(Su)`, on the region of Cvs.Prolate.Mellin.PastTurningContraction
`|g_L(s) − ĝ(s + 3/2)| ≤ 35/(ε^{3/2}|m|²)`, hence `Σ_{k<K} |g_L(s_k) − ĝ(s_k + 3/2)| ≤ 35/(2ε^{3/2}c)`.
-/

noncomputable section

open Complex Finset

namespace Cvs.Prolate.Mellin.PastTurningCanonicalLog

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg omega omega_sq tau)
open Cvs.Upstream.ComplexArsinhStrip (ash hasDerivAt_csqrt)
open Cvs.Upstream.InvSqrtKernelStrip (kf)
open Cvs.Prolate.Mellin.WkbPhaseAntiderivative (Sq Sq_sq gh csqrt_eq_of_sq)
open Cvs.Prolate.Mellin.FrozenRootCanonicalLog (tau0 gL)
open Cvs.Prolate.Mellin.PastTurningContraction (Up)

/-! ### `ash` on the right half-plane -/

theorem sq_add_one_mem {t : ℂ} (ht : 0 < t.re) : t ^ 2 + 1 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hi : t.im = 0
  · left; have : (t ^ 2 + 1).re = t.re ^ 2 - t.im ^ 2 + 1 := by simp [sq]
    rw [this, hi]; nlinarith [sq_nonneg t.re]
  · right; have : (t ^ 2 + 1).im = 2 * t.re * t.im := by simp [sq]; ring
    rw [this]; exact mul_ne_zero (mul_ne_zero two_ne_zero ht.ne') hi

theorem add_csqrt_mem {t : ℂ} (ht : 0 < t.re) : t + csqrt (t ^ 2 + 1) ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  simp only [add_re]; linarith [re_csqrt_nonneg (t ^ 2 + 1)]

theorem csqrt_ne {t : ℂ} (ht : 0 < t.re) : csqrt (t ^ 2 + 1) ≠ 0 := by
  intro h0
  have := csqrt_sq (t ^ 2 + 1)
  rw [h0] at this
  have hs := sq_add_one_mem ht
  rw [← this] at hs; simp at hs

theorem hasDerivAt_ash {t : ℂ} (ht : 0 < t.re) : HasDerivAt ash (kf t) t := by
  have hs := sq_add_one_mem ht
  have hn := csqrt_ne ht
  have hq := slitPlane_ne_zero (add_csqrt_mem ht)
  have h1 : HasDerivAt (fun x : ℂ => x ^ 2 + 1) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const 1
  have h2 := (hasDerivAt_csqrt hs).comp t h1
  have h3 := (hasDerivAt_id t).add h2
  have h4 := h3.clog (add_csqrt_mem ht)
  have h4' : HasDerivAt ash ((1 + 1 / (2 * csqrt (t ^ 2 + 1)) * (2 * t)) / (t + csqrt (t ^ 2 + 1))) t := h4
  refine h4'.congr_deriv ?_
  unfold kf
  field_simp
  ring

theorem hasDerivAt_kf {t : ℂ} (ht : 0 < t.re) : HasDerivAt kf (-t * kf t ^ 3) t := by
  have hs := sq_add_one_mem ht
  have hn := csqrt_ne ht
  have h1 : HasDerivAt (fun x : ℂ => x ^ 2 + 1) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const 1
  have h2 := (hasDerivAt_csqrt hs).comp t h1
  have h3 := (hasDerivAt_const t (1 : ℂ)).div h2 hn
  have h3' : HasDerivAt kf ((0 * csqrt (t ^ 2 + 1) - 1 * (1 / (2 * csqrt (t ^ 2 + 1)) * (2 * t)))
      / csqrt (t ^ 2 + 1) ^ 2) t := h3
  refine h3'.congr_deriv ?_
  unfold kf
  field_simp
  ring

/-! ### A second-order Taylor bound on a convex set -/

theorem taylor2 {s : Set ℂ} (hs : Convex ℝ s) {f f₁ f₂ : ℂ → ℂ} {M : ℝ}
    (hf : ∀ t ∈ s, HasDerivAt f (f₁ t) t) (hf₁ : ∀ t ∈ s, HasDerivAt f₁ (f₂ t) t)
    (hM : ∀ t ∈ s, ‖f₂ t‖ ≤ M) {a b : ℂ} (ha : a ∈ s) (hb : b ∈ s) :
    ‖f b - f a - (b - a) * f₁ a‖ ≤ M * ‖b - a‖ ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ha)
  set seg := segment ℝ a b
  have hseg : seg ⊆ s := hs.segment_subset ha hb
  have hcs : Convex ℝ seg := convex_segment a b
  -- `|f₁ t − f₁ a| ≤ M|b − a|` on the segment
  have h1 : ∀ t ∈ seg, ‖f₁ t - f₁ a‖ ≤ M * ‖b - a‖ := by
    intro t ht
    have := hcs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f₁) (f' := f₂)
      (fun x hx => (hf₁ x (hseg hx)).hasDerivWithinAt) (fun x hx => hM x (hseg hx)) (left_mem_segment ℝ a b) ht
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hM0)
    have ht' : t ∈ segment ℝ a b := ht
    rw [segment_eq_image'] at ht'
    obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := ht'
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  -- `φ(t) = f t − t f₁ a` has derivative `f₁ t − f₁ a`
  have := hcs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t => f t - t * f₁ a)
    (f' := fun t => f₁ t - f₁ a)
    (fun x hx => ((hf x (hseg hx)).sub (hasDerivAt_mul_const (f₁ a))).hasDerivWithinAt)
    h1 (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  have e : f b - f a - (b - a) * f₁ a = (f b - b * f₁ a) - (f a - a * f₁ a) := by ring
  rw [e]
  refine this.trans (le_of_eq ?_)
  ring

/-! ### Sizes on `Re t > 0`, `Im t ≥ 1 + ε/4` -/

/-- The convex region `Re t > 0`, `Im t ≥ 1 + ε/4`. -/
def Rg (ε : ℝ) : Set ℂ := {t | 0 < t.re ∧ 1 + ε / 4 ≤ t.im}

theorem convex_Rg (ε : ℝ) : Convex ℝ (Rg ε) := by
  intro x hx y hy a b ha hb hab
  simp only [Rg, Set.mem_setOf_eq] at *
  have hr : (a • x + b • y).re = a * x.re + b * y.re := by simp
  have hi : (a • x + b • y).im = a * x.im + b * y.im := by simp
  rw [hr, hi]
  constructor
  · rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' hx.1, mul_nonneg hb hy.1.le]
    · subst ha'; simp at hab; subst hab; simpa using hy.1
  · have e : a * (1 + ε / 4) + b * (1 + ε / 4) = 1 + ε / 4 := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

variable {ε : ℝ}

theorem norm_csqrt_ge (hε : 0 < ε) (hε1 : ε ≤ 1) {t : ℂ} (ht : 1 + ε / 4 ≤ t.im) :
    Real.sqrt ε * ‖t‖ / 3 ≤ ‖csqrt (t ^ 2 + 1)‖ := by
  have hw : ‖csqrt (t ^ 2 + 1)‖ ^ 2 = ‖t ^ 2 + 1‖ := by rw [← norm_pow, csqrt_sq]
  have hf : t ^ 2 + 1 = (t - I) * (t + I) := by ring_nf; rw [I_sq]; ring
  have h1 : ε / 4 ≤ ‖t - I‖ := by
    have := Cvs.Prolate.Mellin.PastTurningRootSizes.im_le_norm (t - I); simp at this; linarith
  have h2 : 2 ≤ ‖t + I‖ := by
    have := Cvs.Prolate.Mellin.PastTurningRootSizes.im_le_norm (t + I); simp at this; linarith
  have hlow : ε / 2 ≤ ‖t ^ 2 + 1‖ := by rw [hf, norm_mul]; nlinarith
  have hlow2 : ‖t‖ ^ 2 - 1 ≤ ‖t ^ 2 + 1‖ := by
    have h3 : ‖t ^ 2‖ ≤ ‖t ^ 2 + 1‖ + ‖(1 : ℂ)‖ := by
      have := norm_sub_le (t ^ 2 + 1) 1; rw [show t ^ 2 + 1 - 1 = t ^ 2 by ring] at this; exact this
    rw [norm_pow, norm_one] at h3; linarith
  have hsq : ε / 8 * ‖t‖ ^ 2 ≤ ‖csqrt (t ^ 2 + 1)‖ ^ 2 := by
    rw [hw]
    by_cases ht2 : 2 ≤ ‖t‖ ^ 2
    · nlinarith
    · push Not at ht2; nlinarith
  have hs : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have h3 : (Real.sqrt ε * ‖t‖ / 3) ^ 2 ≤ ‖csqrt (t ^ 2 + 1)‖ ^ 2 := by
    rw [div_pow, mul_pow, hs]; nlinarith [sq_nonneg ‖t‖]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h3

theorem norm_kf_cube_le (hε : 0 < ε) (hε1 : ε ≤ 1) {t : ℂ} (ht : 1 + ε / 4 ≤ t.im) :
    ‖-t * kf t ^ 3‖ ≤ 27 / (ε * Real.sqrt ε) := by
  have hc := norm_csqrt_ge hε hε1 ht
  set r := Real.sqrt ε with hr
  have hs0 : 0 < r := Real.sqrt_pos.mpr hε
  have hss : r * r = ε := Real.mul_self_sqrt hε.le
  have ht1 : 1 ≤ ‖t‖ := by have := Cvs.Prolate.Mellin.PastTurningRootSizes.im_le_norm t; linarith
  have hcpos : 0 < ‖csqrt (t ^ 2 + 1)‖ := lt_of_lt_of_le (by positivity) hc
  unfold kf
  rw [norm_mul, norm_neg, norm_pow, norm_div, norm_one]
  rw [show ‖t‖ * (1 / ‖csqrt (t ^ 2 + 1)‖) ^ 3 = ‖t‖ / ‖csqrt (t ^ 2 + 1)‖ ^ 3 by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (r * ‖t‖ / 3) ^ 3 ≤ ‖csqrt (t ^ 2 + 1)‖ ^ 3 := pow_le_pow_left₀ (by positivity) hc 3
  have ht2 : 1 ≤ ‖t‖ ^ 2 := by nlinarith
  have ht3 : ‖t‖ ≤ ‖t‖ ^ 3 := by nlinarith
  have : ‖t‖ * (ε * r) ≤ 27 * (r * ‖t‖ / 3) ^ 3 := by
    rw [← hss]
    have := mul_le_mul_of_nonneg_left ht3 (show 0 ≤ r ^ 3 by positivity)
    nlinarith
  nlinarith

/-- **Second-order Taylor for `ash`** on the region. -/
theorem ash_taylor (hε : 0 < ε) (hε1 : ε ≤ 1) {a b : ℂ} (ha : a ∈ Rg ε) (hb : b ∈ Rg ε) :
    ‖ash b - ash a - (b - a) * kf a‖ ≤ 27 / (ε * Real.sqrt ε) * ‖b - a‖ ^ 2 :=
  taylor2 (convex_Rg ε) (fun t ht => hasDerivAt_ash ht.1) (fun t ht => hasDerivAt_kf ht.1)
    (fun t ht => norm_kf_cube_le hε hε1 ht.2) ha hb

/-- `|ash t − t| ≤ |t|²` for `|t| ≤ ½`. -/
theorem ash_small {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) : ‖ash t - t‖ ≤ ‖t‖ ^ 2 := by
  set B := Metric.closedBall (0 : ℂ) (1 / 2)
  have hB : Convex ℝ B := convex_closedBall 0 _
  have hstrip : ∀ x ∈ B, |x.im| ≤ 1 - 1 / 2 := by
    intro x hx; rw [Metric.mem_closedBall, dist_zero_right] at hx
    have := Complex.abs_im_le_norm x; linarith
  have hk : ∀ x ∈ B, ‖-x * kf x ^ 3‖ ≤ 1 := by
    intro x hx
    have hxs := hstrip x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have hw : ‖csqrt (x ^ 2 + 1)‖ ^ 2 = ‖x ^ 2 + 1‖ := by rw [← norm_pow, csqrt_sq]
    have hl : 3 / 4 ≤ ‖x ^ 2 + 1‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(x ^ 2))
      rw [norm_neg, norm_one, sub_neg_eq_add, add_comm, norm_pow] at this
      nlinarith [norm_nonneg x]
    have hc : 3 / 4 ≤ ‖csqrt (x ^ 2 + 1)‖ ^ 2 := by rw [hw]; exact hl
    have hcpos : 0 < ‖csqrt (x ^ 2 + 1)‖ := by
      by_contra hn; push Not at hn
      have : ‖csqrt (x ^ 2 + 1)‖ = 0 := le_antisymm hn (norm_nonneg _)
      rw [this] at hc; norm_num at hc
    have hc' : 4 / 5 ≤ ‖csqrt (x ^ 2 + 1)‖ := by nlinarith
    unfold kf
    rw [norm_mul, norm_neg, norm_pow, norm_div, norm_one]
    calc ‖x‖ * (1 / ‖csqrt (x ^ 2 + 1)‖) ^ 3 ≤ 1 / 2 * (1 / (4 / 5)) ^ 3 := by gcongr
      _ ≤ 1 := by norm_num
  have h0 : (0 : ℂ) ∈ B := Metric.mem_closedBall_self (by norm_num)
  have ht' : t ∈ B := by rw [Metric.mem_closedBall, dist_zero_right]; exact ht
  have := taylor2 hB (f := ash) (f₁ := kf) (f₂ := fun x => -x * kf x ^ 3)
    (fun x hx => Cvs.Upstream.ComplexArsinhStrip.hasDerivAt_ash (Cvs.Upstream.InvSqrtKernelStrip.strip (by norm_num) (hstrip x hx)))
    (fun x hx => Cvs.Upstream.InvSqrtKernelStrip.hasDerivAt_kf (by norm_num) (hstrip x hx)) hk h0 ht'
  rw [Cvs.Upstream.ArsinhLipschitzStrip.ash_zero, Cvs.Upstream.ArsinhLipschitzStrip.kf_zero, sub_zero, sub_zero, mul_one,
    one_mul] at this
  exact this

/-! ### The comparison on the region -/

variable {c χ : ℝ} {s : ℂ}

theorem re_csqrt_pos_of_im {z : ℂ} (hz : z.im ≠ 0) : 0 < (csqrt z).re := by
  unfold csqrt
  rw [Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  apply div_pos _ two_pos
  have := Complex.abs_re_lt_norm.mpr hz
  linarith [neg_abs_le z.re]

/-- `2c·√((u/2c)² + 1) = S` for `Re u > 0`, `Im u > 0`. -/
theorem two_c_mul_csqrt' (hc : 0 < c) {u : ℂ} (hre : 0 < u.re) (him : 0 < u.im) :
    2 * (c : ℂ) * csqrt ((u / (2 * c)) ^ 2 + 1) = Sq c u := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold Sq
  symm
  apply csqrt_eq_of_sq
  · rw [mul_pow, csqrt_sq]; field_simp; ring
  · have e2 : (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) := by push_cast; ring
    have hr : (u / (2 * (c : ℂ))).re = u.re / (2 * c) := by rw [e2, Complex.div_ofReal_re]
    have hi : (u / (2 * (c : ℂ))).im = u.im / (2 * c) := by rw [e2, Complex.div_ofReal_im]
    have hv : ((u / (2 * c)) ^ 2 + 1).im ≠ 0 := by
      have : ((u / (2 * (c : ℂ))) ^ 2 + 1).im = 2 * (u / (2 * (c : ℂ))).re * (u / (2 * (c : ℂ))).im := by
        simp [sq]; ring
      rw [this, hr, hi]; positivity
    have := re_csqrt_pos_of_im hv
    have hre2 : (2 * (c : ℂ) * csqrt ((u / (2 * c)) ^ 2 + 1)).re
        = 2 * c * (csqrt ((u / (2 * c)) ^ 2 + 1)).re := by simp
    rw [hre2]; exact mul_pos (by positivity) this

theorem Up.norm_omega_ge' (h : Up ε c χ s) : 15 / 16 * ‖s + 3 / 2‖ ≤ ‖omega s‖ := by
  have h1 := h.norm_omega_sub
  have h2 := h.norm_m_ge
  have := norm_sub_norm_le (s + 3 / 2) (omega s)
  rw [norm_sub_rev] at h1
  linarith

theorem Up.norm_tau0 (h : Up ε c χ s) : ‖tau0 s‖ ≤ 8 / (15 * ‖s + 3 / 2‖) := by
  have hω := Up.norm_omega_ge' h
  have h2 := h.norm_m_ge
  unfold tau0
  rw [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_two,
    div_le_div_iff₀ (by have := norm_pos_iff.mpr h.omega_ne; positivity) (by positivity)]
  nlinarith

/-- **`|g_L(s) − ĝ(s + 3/2)| ≤ 35/(ε^{3/2}|m|²)`** on the region. -/
theorem Up.norm_gL_sub_gh_le (h : Up ε c χ s) :
    ‖gL c χ s - gh c (s + 3 / 2)‖ ≤ 35 / (ε * Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by
  have hc := h.c_pos
  have hc64 := h.c_ge
  have hε := h.hε
  have hε1 := h.hε1
  have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hm := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge h
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
  set u := s + 3 / 2
  set v := u / (2 * (c : ℂ))
  set S := Sq c u
  set τ := tau c χ s
  set ω := omega s
  have hω0 := h.omega_ne
  have hωn := Up.norm_omega_ge' h
  have hδ : ‖ω - u‖ ≤ 1 / (4 * ‖u‖) := Cvs.Prolate.Mellin.FrozenRootClosedBounds.norm_omega_sub_le h.m_ne
  have hu0 : u ≠ 0 := h.m_ne
  have hure : 0 < u.re := by simp [u]; linarith [h.hre]
  have huim : 2 * c ≤ u.im := by simp [u]; exact Cvs.Prolate.Mellin.PastTurningRootSizes.Up.two_c_le h
  -- `v` and `τ` are in the region
  have hvre : 0 < v.re := by
    simp only [v]; rw [show (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
    positivity
  have hvim : 1 + ε / 4 ≤ v.im := by
    simp only [v]; rw [show (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im,
      le_div_iff₀ (by positivity)]
    have : (2 + ε) * c ≤ u.im := by simp [u]; exact h.him
    nlinarith
  have hvR : v ∈ Rg ε := ⟨hvre, hvim⟩
  have hτR : τ ∈ Rg ε := ⟨h.re_tau_pos, h.im_tau_ge⟩
  -- `k(v) = 2c/S`
  have hS : 2 * (c : ℂ) * csqrt (v ^ 2 + 1) = S := two_c_mul_csqrt' hc hure (by linarith)
  have hSne : S ≠ 0 := by
    intro h0; rw [h0] at hS
    have := csqrt_ne hvre
    exact this (by have hc2 : (2 * (c : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * c) ≠ 0)
                   exact (mul_eq_zero.mp hS).resolve_left hc2)
  have hcs := csqrt_ne hvre
  have hkv : kf v = 2 * c / S := by
    unfold kf; rw [← hS]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  have hSn : Real.sqrt ε * ‖u‖ / 3 ≤ ‖S‖ := by
    have h1 := norm_csqrt_ge hε hε1 hvim
    rw [← hS, norm_mul, show ‖(2 * (c : ℂ))‖ = 2 * c by
      rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hc.le]]
    have hvn : ‖v‖ = ‖u‖ / (2 * c) := by
      simp only [v]; rw [norm_div, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hc.le]
    rw [hvn] at h1
    calc Real.sqrt ε * ‖u‖ / 3 = 2 * c * (Real.sqrt ε * (‖u‖ / (2 * c)) / 3) := by field_simp
      _ ≤ _ := by gcongr
  have hSpos : 0 < ‖S‖ := lt_of_lt_of_le (by positivity) hSn
  have hS2c : S + 2 * c ≠ 0 := by
    intro h0
    have : S = -(2 * c) := by linear_combination h0
    have hsq : S ^ 2 = u ^ 2 + 4 * (c : ℂ) ^ 2 := Sq_sq c u
    rw [this] at hsq
    have : u ^ 2 = 0 := by linear_combination -hsq
    exact hu0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  -- the correction identity `u/(2S(S + 2c)) = 1/(2u) − c/(Su)`
  have hcorr : u / (2 * S * (S + 2 * c)) = 1 / (2 * u) - c / (S * u) := by
    have hsq := Sq_sq c u
    field_simp
    linear_combination (-1 : ℂ) * hsq
  -- decomposition
  have hτv : τ - v = (ω - u - χ / ω) / (2 * c) := by
    simp only [τ, v, ω]; unfold tau; ring
  have hdec : gL c χ s - gh c u
      = (ash (tau0 s) - tau0 s) - (ash τ - ash v - (τ - v) * kf v)
        + ((ω - u) / (2 * u * ω) - (ω - u) / S + (χ - c) / (ω * S) - c * (ω - u) / (ω * u * S)) := by
    unfold gL gh
    rw [hcorr, hkv, hτv]
    simp only [τ, ω, S]
    unfold tau0
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
    ring
  rw [hdec]
  -- the four pieces
  have hτ0 := Up.norm_tau0 h
  have hτ0h : ‖tau0 s‖ ≤ 1 / 2 := hτ0.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have p1 : ‖ash (tau0 s) - tau0 s‖ ≤ 1 / ‖u‖ ^ 2 := by
    refine (ash_small hτ0h).trans ?_
    calc ‖tau0 s‖ ^ 2 ≤ (8 / (15 * ‖u‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hτ0 2
      _ ≤ 1 / ‖u‖ ^ 2 := by
          rw [div_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg ‖u‖]
  have hτvn : ‖τ - v‖ ≤ 1 / ‖u‖ := by
    rw [hτv, norm_div, show ‖(2 * (c : ℂ))‖ = 2 * c by
      rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hc.le], div_le_div_iff₀ (by positivity) hmpos]
    have hχ0 : 0 ≤ χ := by linarith [h.hχ0]
    have hq : ‖(χ : ℂ) / ω‖ ≤ 16 * c / (15 * ‖u‖) := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hχ0, div_le_div_iff₀ (norm_pos_iff.mpr hω0) (by positivity)]
      nlinarith [h.hχ1]
    have : ‖ω - u - χ / ω‖ ≤ 1 / (4 * ‖u‖) + 16 * c / (15 * ‖u‖) := by
      refine (norm_sub_le _ _).trans ?_; linarith
    calc ‖ω - u - χ / ω‖ * ‖u‖ ≤ (1 / (4 * ‖u‖) + 16 * c / (15 * ‖u‖)) * ‖u‖ := by gcongr
      _ = 1 / 4 + 16 * c / 15 := by field_simp
      _ ≤ 1 * (2 * c) := by nlinarith
  have p2 : ‖ash τ - ash v - (τ - v) * kf v‖ ≤ 27 / (ε * Real.sqrt ε) * (1 / ‖u‖ ^ 2) := by
    refine (ash_taylor hε hε1 hvR hτR).trans ?_
    gcongr
    calc ‖τ - v‖ ^ 2 ≤ (1 / ‖u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hτvn 2
      _ = 1 / ‖u‖ ^ 2 := by rw [div_pow, one_pow]
  have hωpos : 0 < ‖ω‖ := norm_pos_iff.mpr hω0
  have q1 : ‖(ω - u) / (2 * u * ω)‖ ≤ 1 / ‖u‖ ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_two, div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖ω - u‖ * ‖u‖ ^ 2 ≤ 1 / (4 * ‖u‖) * ‖u‖ ^ 2 := by gcongr
      _ = ‖u‖ / 4 := by field_simp
      _ ≤ 1 * (2 * ‖u‖ * ‖ω‖) := by nlinarith
  have q2 : ‖(ω - u) / S‖ ≤ 1 / (Real.sqrt ε * ‖u‖ ^ 2) := by
    rw [norm_div, div_le_div_iff₀ hSpos (by positivity)]
    calc ‖ω - u‖ * (Real.sqrt ε * ‖u‖ ^ 2) ≤ 1 / (4 * ‖u‖) * (Real.sqrt ε * ‖u‖ ^ 2) := by gcongr
      _ = Real.sqrt ε * ‖u‖ / 4 := by field_simp
      _ ≤ 1 * ‖S‖ := by linarith
  have q3 : ‖((χ : ℂ) - c) / (ω * S)‖ ≤ 4 / (Real.sqrt ε * ‖u‖ ^ 2) := by
    have hχc : ‖((χ : ℂ) - c)‖ ≤ 1 := by
      rw [show ((χ : ℂ) - c) = ((χ - c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [h.hχ0, h.hχ1]
    rw [norm_div, norm_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have hd : 15 / 16 * ‖u‖ * (Real.sqrt ε * ‖u‖ / 3) ≤ ‖ω‖ * ‖S‖ := mul_le_mul hωn hSn (by positivity) hωpos.le
    calc ‖((χ : ℂ) - c)‖ * (Real.sqrt ε * ‖u‖ ^ 2) ≤ 1 * (Real.sqrt ε * ‖u‖ ^ 2) := by gcongr
      _ ≤ 4 * (15 / 16 * ‖u‖ * (Real.sqrt ε * ‖u‖ / 3)) := by
          have : 4 * (15 / 16 * ‖u‖ * (Real.sqrt ε * ‖u‖ / 3)) = 5 / 4 * (Real.sqrt ε * ‖u‖ ^ 2) := by ring
          rw [this]; have := mul_pos hs0 (pow_pos hmpos 2); linarith
      _ ≤ 4 * (‖ω‖ * ‖S‖) := by gcongr
  have q4 : ‖(c : ℂ) * (ω - u) / (ω * u * S)‖ ≤ 1 / (Real.sqrt ε * ‖u‖ ^ 2) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hden : 15 / 16 * ‖u‖ * ‖u‖ * (Real.sqrt ε * ‖u‖ / 3) ≤ ‖ω‖ * ‖u‖ * ‖S‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_right hωn (norm_nonneg _)) hSn (by positivity) (by positivity)
    have hcu : c ≤ 5 / 4 * ‖u‖ ^ 2 := by nlinarith
    calc c * ‖ω - u‖ * (Real.sqrt ε * ‖u‖ ^ 2) ≤ c * (1 / (4 * ‖u‖)) * (Real.sqrt ε * ‖u‖ ^ 2) := by gcongr
      _ = c * (Real.sqrt ε * ‖u‖ / 4) := by field_simp
      _ ≤ 5 / 4 * ‖u‖ ^ 2 * (Real.sqrt ε * ‖u‖ / 4) := by gcongr
      _ = 1 * (15 / 16 * ‖u‖ * ‖u‖ * (Real.sqrt ε * ‖u‖ / 3)) := by ring
      _ ≤ 1 * (‖ω‖ * ‖u‖ * ‖S‖) := by gcongr
  have hu2 : 0 < ‖u‖ ^ 2 := by positivity
  have hεs : ε * Real.sqrt ε ≤ Real.sqrt ε := mul_le_of_le_one_left hs0.le hε1
  have hεs1 : ε * Real.sqrt ε ≤ 1 := mul_le_one₀ hε1 hs0.le hs1
  have hεpos : 0 < ε * Real.sqrt ε := by positivity
  set Y := 1 / (ε * Real.sqrt ε * ‖u‖ ^ 2)
  have r1 : 1 / ‖u‖ ^ 2 ≤ Y :=
    one_div_le_one_div_of_le (by positivity) (mul_le_of_le_one_left hu2.le hεs1)
  have r2 : 1 / (Real.sqrt ε * ‖u‖ ^ 2) ≤ Y :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hεs hu2.le)
  have p2' : ‖ash τ - ash v - (τ - v) * kf v‖ ≤ 27 * Y := by
    refine p2.trans (le_of_eq ?_); simp only [Y]; field_simp
  have q3' : ‖((χ : ℂ) - c) / (ω * S)‖ ≤ 4 * (1 / (Real.sqrt ε * ‖u‖ ^ 2)) := by
    refine q3.trans (le_of_eq ?_); ring
  have tri : ‖(ash (tau0 s) - tau0 s) - (ash τ - ash v - (τ - v) * kf v)
        + ((ω - u) / (2 * u * ω) - (ω - u) / S + (χ - c) / (ω * S) - c * (ω - u) / (ω * u * S))‖
      ≤ ‖ash (tau0 s) - tau0 s‖ + ‖ash τ - ash v - (τ - v) * kf v‖
        + (‖(ω - u) / (2 * u * ω)‖ + ‖(ω - u) / S‖ + ‖((χ : ℂ) - c) / (ω * S)‖ + ‖(c : ℂ) * (ω - u) / (ω * u * S)‖) := by
    refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_sub_le _ _
  have e35 : 35 / (ε * Real.sqrt ε * ‖u‖ ^ 2) = 35 * Y := by simp only [Y]; ring
  rw [e35]
  linarith only [tri, p1, p2', q1, q2, q3', q4, r1, r2]

/-- **Summed along a line**: `Σ_{k<K} |g_L(s_k) − ĝ(s_k + 3/2)| ≤ 35/(2ε^{3/2}c)`. -/
theorem sum_gL_sub_gh_le {s₀ : ℂ} (h : Up ε c χ s₀) (K : ℕ) :
    ∑ k ∈ range K, ‖gL c χ (s₀ + 2 * k) - gh c (s₀ + 2 * k + 3 / 2)‖ ≤ 35 / (2 * ε * Real.sqrt ε * c) := by
  have hc := h.c_pos
  have hεs : 0 < ε * Real.sqrt ε := by have := Real.sqrt_pos.mpr h.hε; have := h.hε; positivity
  calc ∑ k ∈ range K, ‖gL c χ (s₀ + 2 * k) - gh c (s₀ + 2 * k + 3 / 2)‖
      ≤ ∑ k ∈ range K, 35 / (ε * Real.sqrt ε) * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2) := by
        refine sum_le_sum fun k _ => ?_
        have := Up.norm_gL_sub_gh_le (Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h k)
        have hp := Cvs.Prolate.Mellin.PastTurningErrorsSummed.Up.norm_m_pos h k
        refine this.trans (le_of_eq ?_)
        field_simp
    _ = 35 / (ε * Real.sqrt ε) * ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2 := by rw [mul_sum]
    _ ≤ 35 / (ε * Real.sqrt ε) * (1 / (2 * c)) := by gcongr; exact Cvs.Prolate.Mellin.PastTurningErrorsSummed.Up.sum_inv_sq_le h K
    _ = 35 / (2 * ε * Real.sqrt ε * c) := by field_simp

end Cvs.Prolate.Mellin.PastTurningCanonicalLog
