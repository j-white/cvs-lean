import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The complex inverse hyperbolic sine on the strip `|Im t| < 1`

`ash t = log(t + √(t² + 1))` is holomorphic on the strip with `ash′ = 1/√(t² + 1)`, satisfies `exp(ash t) = t + √(t² + 1)`
and `exp(−ash t) = √(t² + 1) − t`, and `ash(i sin θ) = iθ` for `|θ| < π/2`.
-/

noncomputable section

open Complex

namespace Cvs.Upstream.ComplexArsinhStrip

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg)

/-- The complex inverse hyperbolic sine. -/
def ash (t : ℂ) : ℂ := Complex.log (t + csqrt (t ^ 2 + 1))

theorem csqrt_ofReal {x : ℝ} (hx : 0 ≤ x) : csqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
  unfold csqrt
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]; push_cast; ring_nf

theorem sq_add_one_mem_slitPlane {t : ℂ} (ht : |t.im| < 1) : t ^ 2 + 1 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : t.re * t.im = 0
  · left
    have hre : (t ^ 2 + 1).re = t.re ^ 2 - t.im ^ 2 + 1 := by simp [sq]
    rw [hre]
    have : t.im ^ 2 < 1 := by
      have := abs_lt.mp ht; nlinarith
    rcases mul_eq_zero.mp h with h1 | h1
    · rw [h1]; nlinarith
    · rw [h1]; nlinarith
  · right
    have him : (t ^ 2 + 1).im = 2 * (t.re * t.im) := by simp [sq]; ring
    rw [him]; intro h0; apply h; linarith

theorem csqrt_ne_zero {t : ℂ} (ht : |t.im| < 1) : csqrt (t ^ 2 + 1) ≠ 0 := by
  intro h0
  have := csqrt_sq (t ^ 2 + 1)
  rw [h0] at this
  have hs := sq_add_one_mem_slitPlane ht
  rw [← this] at hs; simp at hs

theorem add_csqrt_mem_slitPlane {t : ℂ} (ht : |t.im| < 1) : t + csqrt (t ^ 2 + 1) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra hcon
  push_neg at hcon
  obtain ⟨hre, him⟩ := hcon
  set p := t + csqrt (t ^ 2 + 1)
  have hp : p = (p.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hsq := csqrt_sq (t ^ 2 + 1)
  have hs : csqrt (t ^ 2 + 1) = p - t := by simp only [p]; ring
  rw [hs] at hsq
  -- `p² − 2pt = 1`
  have h1 : p ^ 2 - 2 * p * t = 1 := by linear_combination hsq
  have hp0 : p ≠ 0 := by intro h0; rw [h0] at h1; simp at h1
  have ht' : t = (p ^ 2 - 1) / (2 * p) := by field_simp; linear_combination -h1
  have htim : t.im = 0 := by
    rw [ht', hp]; norm_cast
  have htr : t = (t.re : ℂ) := by apply Complex.ext <;> simp [htim]
  have hsqrt : csqrt (t ^ 2 + 1) = (Real.sqrt (t.re ^ 2 + 1) : ℂ) := by
    rw [htr]; push_cast
    rw [show (t.re : ℂ) ^ 2 + 1 = ((t.re ^ 2 + 1 : ℝ) : ℂ) by push_cast; ring]
    exact csqrt_ofReal (by positivity)
  have hpre : p.re = t.re + Real.sqrt (t.re ^ 2 + 1) := by
    simp only [p]; rw [hsqrt]; simp
  have : |t.re| < Real.sqrt (t.re ^ 2 + 1) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have := neg_abs_le t.re
  linarith

theorem add_csqrt_ne_zero {t : ℂ} (ht : |t.im| < 1) : t + csqrt (t ^ 2 + 1) ≠ 0 :=
  slitPlane_ne_zero (add_csqrt_mem_slitPlane ht)

theorem hasDerivAt_csqrt {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt csqrt (1 / (2 * csqrt z)) z := by
  have h := (Complex.hasStrictDerivAt_cpow_const (c := (2⁻¹ : ℂ)) hz).hasDerivAt
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hne : csqrt z ≠ 0 := by
    intro h0; have := csqrt_sq z; rw [h0] at this; exact hz0 (by simpa using this.symm)
  have e : z ^ ((2⁻¹ : ℂ) - 1) = (csqrt z)⁻¹ := by
    rw [show (2⁻¹ : ℂ) - 1 = -(2⁻¹ : ℂ) by norm_num, Complex.cpow_neg]; rfl
  have h' : HasDerivAt csqrt (2⁻¹ * z ^ ((2⁻¹ : ℂ) - 1)) z := h
  rw [e] at h'
  exact h'.congr_deriv (by field_simp)

theorem hasDerivAt_ash {t : ℂ} (ht : |t.im| < 1) : HasDerivAt ash (1 / csqrt (t ^ 2 + 1)) t := by
  have hs := sq_add_one_mem_slitPlane ht
  have hn := csqrt_ne_zero ht
  have hq := add_csqrt_ne_zero ht
  have h1 : HasDerivAt (fun x : ℂ => x ^ 2 + 1) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const 1
  have h2 := (hasDerivAt_csqrt hs).comp t h1
  have h3 := (hasDerivAt_id t).add h2
  have h4 := h3.clog (add_csqrt_mem_slitPlane ht)
  have h4' : HasDerivAt ash ((1 + 1 / (2 * csqrt (t ^ 2 + 1)) * (2 * t)) / (t + csqrt (t ^ 2 + 1))) t := h4
  refine h4'.congr_deriv ?_
  field_simp
  ring

theorem exp_ash {t : ℂ} (ht : |t.im| < 1) : Complex.exp (ash t) = t + csqrt (t ^ 2 + 1) :=
  Complex.exp_log (add_csqrt_ne_zero ht)

theorem exp_neg_ash {t : ℂ} (ht : |t.im| < 1) : Complex.exp (-ash t) = csqrt (t ^ 2 + 1) - t := by
  rw [Complex.exp_neg, exp_ash ht]
  have hq := add_csqrt_ne_zero ht
  have hsq := csqrt_sq (t ^ 2 + 1)
  field_simp
  linear_combination -hsq

/-- `ash(i sin θ) = iθ` for `|θ| < π/2`. -/
theorem ash_I_mul_sin {θ : ℝ} (hθ : |θ| < Real.pi / 2) : ash (I * Real.sin θ) = I * θ := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ], by linarith [le_abs_self θ]⟩
  have e1 : (I * (Real.sin θ : ℂ)) ^ 2 + 1 = ((Real.cos θ ^ 2 : ℝ) : ℂ) := by
    have := Real.sin_sq_add_cos_sq θ
    have h : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by exact_mod_cast this
    rw [Complex.ofReal_pow, mul_pow, Complex.I_sq]
    linear_combination -h
  unfold ash
  rw [e1, csqrt_ofReal (by positivity), Real.sqrt_sq hcos.le]
  have e2 : I * (Real.sin θ : ℂ) + (Real.cos θ : ℂ) = Complex.exp (I * θ) := by
    rw [show I * (θ : ℂ) = (θ : ℂ) * I by ring, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    ring
  rw [e2, Complex.log_exp]
  · simp; have := neg_abs_le θ; have := Real.pi_pos; linarith
  · simp; have := le_abs_self θ; have := Real.pi_pos; linarith

end Cvs.Upstream.ComplexArsinhStrip
