import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Upstream.ComplexArsinhStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The kernel `k = 1/√(1 + t²)` on the strip `|Im t| ≤ 1 − δ`

`‖t² + 1‖ ≥ (δ/3)²(1 + ‖t‖)²`, so `‖k(t)‖ ≤ 3/(δ(1 + ‖t‖))`; `k′ = −t k³`, `k″ = k⁵(2t² − 1)`, with
`‖k′‖ ≤ 27/δ³`, `‖k″‖ ≤ 486/δ⁵`, and `‖1 − k(t)‖ ≤ (3/δ)‖t‖`.
-/

noncomputable section

open Complex

namespace Cvs.Upstream.InvSqrtKernelStrip

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg)
open Cvs.Upstream.ComplexArsinhStrip

/-- The kernel `k(t) = 1/√(t² + 1)`. -/
def kf (t : ℂ) : ℂ := 1 / csqrt (t ^ 2 + 1)

variable {δ : ℝ} {t : ℂ}

theorem norm_sub_I_ge (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : |t.im| ≤ 1 - δ) :
    δ / 3 * (1 + ‖t‖) ≤ ‖t - I‖ ∧ δ / 3 * (1 + ‖t‖) ≤ ‖t + I‖ := by
  have h1 : δ ≤ ‖t - I‖ := by
    have := Complex.abs_im_le_norm (t - I); simp at this
    have := abs_le.mp ht; rw [abs_sub_comm] at *; linarith [le_abs_self (1 - t.im), this]
  have h2 : δ ≤ ‖t + I‖ := by
    have := Complex.abs_im_le_norm (t + I); simp at this
    have := abs_le.mp ht; linarith [le_abs_self (t.im + 1)]
  have h3 : ‖t‖ - 1 ≤ ‖t - I‖ := by
    have := norm_sub_norm_le t I; simp at this; linarith
  have h4 : ‖t‖ - 1 ≤ ‖t + I‖ := by
    have := norm_sub_norm_le t (-I); simp at this; linarith
  have key : ∀ m : ℝ, δ ≤ m → ‖t‖ - 1 ≤ m → δ / 3 * (1 + ‖t‖) ≤ m := by
    intro m hm1 hm2
    by_cases h : ‖t‖ ≤ 2
    · nlinarith [norm_nonneg t]
    · nlinarith [norm_nonneg t]
  exact ⟨key _ h1 h3, key _ h2 h4⟩

theorem norm_sq_add_one_ge (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : |t.im| ≤ 1 - δ) :
    (δ / 3 * (1 + ‖t‖)) ^ 2 ≤ ‖t ^ 2 + 1‖ := by
  obtain ⟨h1, h2⟩ := norm_sub_I_ge hδ hδ1 ht
  have e : t ^ 2 + 1 = (t - I) * (t + I) := by ring_nf; rw [Complex.I_sq]; ring
  rw [e, norm_mul, sq]
  exact mul_le_mul h1 h2 (by positivity) (norm_nonneg _)

theorem norm_csqrt_ge (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : |t.im| ≤ 1 - δ) :
    δ / 3 * (1 + ‖t‖) ≤ ‖csqrt (t ^ 2 + 1)‖ := by
  have h := norm_sq_add_one_ge hδ hδ1 ht
  have e : ‖csqrt (t ^ 2 + 1)‖ ^ 2 = ‖t ^ 2 + 1‖ := by rw [← norm_pow, csqrt_sq]
  rw [← e] at h
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h

theorem strip (hδ : 0 < δ) (ht : |t.im| ≤ 1 - δ) : |t.im| < 1 := by linarith

theorem norm_kf_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : |t.im| ≤ 1 - δ) : ‖kf t‖ ≤ 3 / (δ * (1 + ‖t‖)) := by
  have h := norm_csqrt_ge hδ hδ1 ht
  unfold kf
  rw [norm_div, norm_one, div_le_div_iff₀ (lt_of_lt_of_le (by positivity) h) (by positivity)]
  nlinarith

theorem kf_sq_mul (hδ : 0 < δ) (ht : |t.im| ≤ 1 - δ) : kf t ^ 2 * (t ^ 2 + 1) = 1 := by
  have hs := sq_add_one_mem_slitPlane (strip hδ ht)
  have hs0 : t ^ 2 + 1 ≠ 0 := slitPlane_ne_zero hs
  unfold kf
  rw [div_pow, one_pow, csqrt_sq]
  field_simp

theorem hasDerivAt_kf (hδ : 0 < δ) (ht : |t.im| ≤ 1 - δ) : HasDerivAt kf (-t * kf t ^ 3) t := by
  have hs := sq_add_one_mem_slitPlane (strip hδ ht)
  have hn := csqrt_ne_zero (strip hδ ht)
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

theorem hasDerivAt_kf1 (hδ : 0 < δ) (ht : |t.im| ≤ 1 - δ) :
    HasDerivAt (fun x => -x * kf x ^ 3) (kf t ^ 5 * (2 * t ^ 2 - 1)) t := by
  have h := ((hasDerivAt_id t).neg.mul ((hasDerivAt_kf hδ ht).pow 3))
  have hk := kf_sq_mul hδ ht
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by simp)
  simp only [Pi.pow_apply, Pi.neg_apply, id]
  push_cast
  linear_combination (kf t ^ 3) * hk

theorem norm_kf1_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : |t.im| ≤ 1 - δ) : ‖-t * kf t ^ 3‖ ≤ 27 / δ ^ 3 := by
  have hk := norm_kf_le hδ hδ1 ht
  rw [norm_mul, norm_neg, norm_pow]
  have h0 : 0 ≤ ‖kf t‖ := norm_nonneg _
  have h1 : ‖kf t‖ ^ 3 ≤ (3 / (δ * (1 + ‖t‖))) ^ 3 := pow_le_pow_left₀ h0 hk 3
  have ht0 := norm_nonneg t
  calc ‖t‖ * ‖kf t‖ ^ 3 ≤ ‖t‖ * (3 / (δ * (1 + ‖t‖))) ^ 3 := by gcongr
    _ = 27 / δ ^ 3 * (‖t‖ / (1 + ‖t‖) ^ 3) := by field_simp; ring
    _ ≤ 27 / δ ^ 3 * 1 := by
        gcongr
        rw [div_le_one (by positivity)]; nlinarith [sq_nonneg ‖t‖]
    _ = 27 / δ ^ 3 := mul_one _

theorem norm_kf2_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : |t.im| ≤ 1 - δ) :
    ‖kf t ^ 5 * (2 * t ^ 2 - 1)‖ ≤ 486 / δ ^ 5 := by
  have hk := norm_kf_le hδ hδ1 ht
  rw [norm_mul, norm_pow]
  have h0 : 0 ≤ ‖kf t‖ := norm_nonneg _
  have h1 : ‖kf t‖ ^ 5 ≤ (3 / (δ * (1 + ‖t‖))) ^ 5 := pow_le_pow_left₀ h0 hk 5
  have ht0 := norm_nonneg t
  have h2 : ‖2 * t ^ 2 - 1‖ ≤ 2 * (1 + ‖t‖) ^ 2 := by
    have := norm_sub_le (2 * t ^ 2) 1
    rw [norm_mul, norm_pow, norm_one] at this; norm_num at this; nlinarith
  calc ‖kf t‖ ^ 5 * ‖2 * t ^ 2 - 1‖ ≤ (3 / (δ * (1 + ‖t‖))) ^ 5 * (2 * (1 + ‖t‖) ^ 2) := by gcongr
    _ = 486 / δ ^ 5 * (1 / (1 + ‖t‖) ^ 3) := by field_simp; ring
    _ ≤ 486 / δ ^ 5 * 1 := by
        gcongr
        rw [div_le_one (by positivity)]; nlinarith [sq_nonneg ‖t‖, pow_nonneg ht0 3]
    _ = 486 / δ ^ 5 := mul_one _

/-- `‖1 − k(t)‖ ≤ (3/δ)‖t‖`. -/
theorem norm_one_sub_kf_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : |t.im| ≤ 1 - δ) :
    ‖1 - kf t‖ ≤ 3 / δ * ‖t‖ := by
  have hn := csqrt_ne_zero (strip hδ ht)
  have hc := norm_csqrt_ge hδ hδ1 ht
  set r := csqrt (t ^ 2 + 1)
  have hr1 : 1 ≤ ‖r + 1‖ := by
    have := Complex.re_le_norm (r + 1); have := re_csqrt_nonneg (t ^ 2 + 1); simp at *; linarith
  have hr1' : r + 1 ≠ 0 := fun h => by rw [h, norm_zero] at hr1; linarith
  have e : 1 - kf t = t ^ 2 / (r * (r + 1)) := by
    unfold kf
    change 1 - 1 / r = _
    have hsq : r ^ 2 = t ^ 2 + 1 := csqrt_sq _
    field_simp
    linear_combination hsq
  rw [e, norm_div, norm_mul, norm_pow]
  have ht0 := norm_nonneg t
  have hpos : 0 < δ / 3 * (1 + ‖t‖) := by positivity
  rw [div_le_iff₀ (by have := lt_of_lt_of_le hpos hc; positivity)]
  calc ‖t‖ ^ 2 ≤ 3 / δ * ‖t‖ * (δ / 3 * (1 + ‖t‖) * 1) := by
        field_simp; nlinarith
    _ ≤ 3 / δ * ‖t‖ * (‖r‖ * ‖r + 1‖) := by gcongr

end Cvs.Upstream.InvSqrtKernelStrip
