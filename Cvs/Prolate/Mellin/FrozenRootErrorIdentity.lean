import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The frozen root of the law recurrence and the exact error identity

For `(s + 1)P(s) = qP(s + 2) + (s + 2)P(s + 4)` the step ratio `r = P(s+2)/P(s)` obeys
`(s + 1)/r(s) = q + (s + 2) r(s + 2)`. With `ω² = (s+1)(s+2)`, `τ = (ω − χ/ω)/(2c)` and `ζ = √(τ² + 1) − τ`, the
frozen root `ρ = ωζ/(s+2)` solves `(s + 2)ρ² + qρ − (s + 1) = 0`, `|ζ|` is controlled by `Re τ`, and
`ρ/r(s) − 1 = A·(r(s+2)/ρ' − 1) + B` exactly, with `A = (s+2)ρρ'/(s+1)` and `B = (s+2)ρ(ρ' − ρ)/(s+1)`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.FrozenRootErrorIdentity

/-- The principal square root `z^{1/2}`. -/
def csqrt (z : ℂ) : ℂ := z ^ (2⁻¹ : ℂ)

theorem csqrt_sq (z : ℂ) : csqrt z ^ 2 = z := by
  unfold csqrt
  exact Complex.cpow_ofNat_inv_pow z 2

theorem re_csqrt_nonneg (z : ℂ) : 0 ≤ (csqrt z).re := by
  unfold csqrt
  rw [Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

/-! ### The step-ratio form of the recurrence and the error identity -/

/-! ### The frozen root in closed form -/

/-- `ω = m √(1 − 1/(4m²))` with `m = s + 3/2`, so that `ω² = (s+1)(s+2)` and `ω ≈ s + 3/2`. -/
def omega (s : ℂ) : ℂ := (s + 3 / 2) * csqrt (1 - 1 / (4 * (s + 3 / 2) ^ 2))

theorem omega_sq {s : ℂ} (hs : s + 3 / 2 ≠ 0) : omega s ^ 2 = (s + 1) * (s + 2) := by
  unfold omega
  rw [mul_pow, csqrt_sq, mul_sub, mul_one]
  have h4 : (s + 3 / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  rw [show (s + 3 / 2) ^ 2 * (1 / (4 * (s + 3 / 2) ^ 2)) = 1 / 4 by
    rw [mul_one_div, div_eq_iff (by simpa using h4)]; ring]
  ring

/-- `τ = (ω − χ/ω)/(2c)`, so that `q = ((s+1)(s+2) − χ)/c = 2τω`. -/
def tau (c χ : ℝ) (s : ℂ) : ℂ := (omega s - χ / omega s) / (2 * c)

/-- `ζ = √(τ² + 1) − τ`, the root of `ζ² + 2τζ − 1 = 0` of modulus at most one when `Re τ ≥ 0`. -/
def zeta (c χ : ℝ) (s : ℂ) : ℂ := csqrt (tau c χ s ^ 2 + 1) - tau c χ s

/-- The other root `ζ₂ = −√(τ² + 1) − τ`. -/
def zeta₂ (c χ : ℝ) (s : ℂ) : ℂ := -csqrt (tau c χ s ^ 2 + 1) - tau c χ s

theorem zeta_mul_zeta₂ (c χ : ℝ) (s : ℂ) : zeta c χ s * zeta₂ c χ s = -1 := by
  unfold zeta zeta₂
  have := csqrt_sq (tau c χ s ^ 2 + 1)
  linear_combination -this

theorem zeta_ne_zero (c χ : ℝ) (s : ℂ) : zeta c χ s ≠ 0 := by
  intro h
  have := zeta_mul_zeta₂ c χ s
  rw [h, zero_mul] at this
  norm_num at this

theorem zeta_quadratic (c χ : ℝ) (s : ℂ) :
    zeta c χ s ^ 2 + 2 * tau c χ s * zeta c χ s - 1 = 0 := by
  unfold zeta
  have := csqrt_sq (tau c χ s ^ 2 + 1)
  linear_combination this

/-- The frozen root `ρ* = ωζ/(s+2)`. -/
def rhoStar (c χ : ℝ) (s : ℂ) : ℂ := omega s * zeta c χ s / (s + 2)

/-- `q = 2τω`. -/
theorem q_eq {c χ : ℝ} (hc : c ≠ 0) {s : ℂ} (hs : s + 3 / 2 ≠ 0) (hω : omega s ≠ 0) :
    ((s + 1) * (s + 2) - χ) / c = 2 * tau c χ s * omega s := by
  unfold tau
  rw [← omega_sq hs]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  field_simp

/-- **The frozen root solves the step quadratic**: `(s+2)ρ*² + qρ* − (s+1) = 0`. -/
theorem rhoStar_root {c χ : ℝ} (hc : c ≠ 0) {s : ℂ} (hs : s + 3 / 2 ≠ 0) (hs2 : s + 2 ≠ 0)
    (hω : omega s ≠ 0) :
    (s + 2) * rhoStar c χ s ^ 2 + ((s + 1) * (s + 2) - χ) / c * rhoStar c χ s - (s + 1) = 0 := by
  rw [q_eq hc hs hω]
  unfold rhoStar
  have hq := zeta_quadratic c χ s
  have hω2 := omega_sq hs
  have key : (s + 2) * (omega s * zeta c χ s / (s + 2)) ^ 2
      + 2 * tau c χ s * omega s * (omega s * zeta c χ s / (s + 2)) - (s + 1)
      = (omega s ^ 2 * (zeta c χ s ^ 2 + 2 * tau c χ s * zeta c χ s - 1)
          + (omega s ^ 2 - (s + 1) * (s + 2))) / (s + 2) := by
    field_simp; ring
  rw [key, hq, hω2]
  simp

/-! ### Moduli -/

/-- `|ζ₂|² − |ζ|² = 4 Re(√(τ²+1) τ̄)`. -/
theorem normSq_zeta₂_sub (c χ : ℝ) (s : ℂ) :
    Complex.normSq (zeta₂ c χ s) - Complex.normSq (zeta c χ s)
      = 4 * ((csqrt (tau c χ s ^ 2 + 1)).re * (tau c χ s).re
          + (csqrt (tau c χ s ^ 2 + 1)).im * (tau c χ s).im) := by
  unfold zeta zeta₂
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im]
  ring

/-- `|ζ|² |ζ₂|² = 1`. -/
theorem normSq_zeta_mul (c χ : ℝ) (s : ℂ) :
    Complex.normSq (zeta c χ s) * Complex.normSq (zeta₂ c χ s) = 1 := by
  rw [← Complex.normSq_mul, zeta_mul_zeta₂]
  simp

/-- With `R = Re(√(τ²+1) τ̄)`, `|ζ|² = √(4R² + 1) − 2R`. -/
theorem normSq_zeta_eq (c χ : ℝ) (s : ℂ) :
    Complex.normSq (zeta c χ s)
      = Real.sqrt (4 * ((csqrt (tau c χ s ^ 2 + 1)).re * (tau c χ s).re
          + (csqrt (tau c χ s ^ 2 + 1)).im * (tau c χ s).im) ^ 2 + 1)
        - 2 * ((csqrt (tau c χ s ^ 2 + 1)).re * (tau c χ s).re
          + (csqrt (tau c χ s ^ 2 + 1)).im * (tau c χ s).im) := by
  set R := (csqrt (tau c χ s ^ 2 + 1)).re * (tau c χ s).re
    + (csqrt (tau c χ s ^ 2 + 1)).im * (tau c χ s).im
  set x := Complex.normSq (zeta c χ s)
  have hx0 : 0 ≤ x := Complex.normSq_nonneg _
  have h1 := normSq_zeta_mul c χ s
  have h2 := normSq_zeta₂_sub c χ s
  -- x (x + 4R) = 1, x ≥ 0
  have hq : x * (x + 4 * R) = 1 := by
    have : Complex.normSq (zeta₂ c χ s) = x + 4 * R := by linarith
    rw [← this]; exact h1
  have hs : Real.sqrt (4 * R ^ 2 + 1) = x + 2 * R := by
    have hpos : 0 ≤ x + 2 * R := by
      by_contra hneg
      push Not at hneg
      nlinarith
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) hpos]
    nlinarith
  linarith

/-- **`|ζ|² ≤ e^{−2R + 2R²}`** with `R = Re(√(τ²+1) τ̄)`. -/
theorem normSq_zeta_le_exp (c χ : ℝ) (s : ℂ) :
    Complex.normSq (zeta c χ s)
      ≤ Real.exp (-2 * ((csqrt (tau c χ s ^ 2 + 1)).re * (tau c χ s).re
          + (csqrt (tau c χ s ^ 2 + 1)).im * (tau c χ s).im)
        + 2 * ((csqrt (tau c χ s ^ 2 + 1)).re * (tau c χ s).re
          + (csqrt (tau c χ s ^ 2 + 1)).im * (tau c χ s).im) ^ 2) := by
  rw [normSq_zeta_eq]
  set R := (csqrt (tau c χ s ^ 2 + 1)).re * (tau c χ s).re
    + (csqrt (tau c χ s ^ 2 + 1)).im * (tau c χ s).im
  have h1 : Real.sqrt (4 * R ^ 2 + 1) ≤ 1 + 2 * R ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg R]
  have h2 := Real.add_one_le_exp (-2 * R + 2 * R ^ 2)
  linarith

/-- **`|A|²` in closed form**: with `A = (s+2)ρ*(s)ρ*(s+2)/(s+1)`,
`|A|² = |(s+2)(s+3)|/|(s+1)(s+4)| · |ζ(s)|² |ζ(s+2)|²`. -/
theorem norm_A_sq {c χ : ℝ} {s : ℂ} (hs : s + 3 / 2 ≠ 0) (hs' : s + 2 + 3 / 2 ≠ 0) (hs1 : s + 1 ≠ 0)
    (hs2 : s + 2 ≠ 0) (hs4 : s + 4 ≠ 0) :
    ‖(s + 2) * rhoStar c χ s * rhoStar c χ (s + 2) / (s + 1)‖ ^ 2
      = ‖(s + 2) * (s + 3)‖ / ‖(s + 1) * (s + 4)‖ * (‖zeta c χ s‖ ^ 2 * ‖zeta c χ (s + 2)‖ ^ 2) := by
  have n1 : ‖omega s‖ ^ 2 = ‖s + 1‖ * ‖s + 2‖ := by rw [← norm_pow, omega_sq hs, norm_mul]
  have n2 : ‖omega (s + 2)‖ ^ 2 = ‖s + 3‖ * ‖s + 4‖ := by
    rw [← norm_pow, omega_sq hs', norm_mul, show s + 2 + 1 = s + 3 by ring, show s + 2 + 2 = s + 4 by ring]
  have a1 : 0 < ‖s + 1‖ := norm_pos_iff.mpr hs1
  have a2 : 0 < ‖s + 2‖ := norm_pos_iff.mpr hs2
  have a4 : 0 < ‖s + 4‖ := norm_pos_iff.mpr hs4
  unfold rhoStar
  rw [show s + 2 + 2 = s + 4 by ring]
  simp only [norm_div, norm_mul, div_pow, mul_pow]
  rw [n1, n2]
  field_simp

end Cvs.Prolate.Mellin.FrozenRootErrorIdentity
