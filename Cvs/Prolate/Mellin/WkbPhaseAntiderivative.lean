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
# The WKB phase and its antiderivative

With `S = √(u² + 4c²)`, on the strip `|Im u| < 2c`: `Ĝ(u) = −u·ash(u/2c) + S − ½ log(2c + S)` has derivative
`ĝ(u) = −ash(u/2c) − u/(2S(S+2c))`, and `ĝ′ = −(2S³ + 4cS² − S² + 2cS + 4c²)/(2S³(S+2c))`,
`ĝ″ = u(S⁴ + 4cS³ − S³ + 4c²S² + 2cS² + 12c²S + 12c³)/(S⁵(S+2c)²)`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.WkbPhaseAntiderivative

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg)
open Cvs.Upstream.ComplexArsinhStrip

/-- `S = √(u² + 4c²)`. -/
def Sq (c : ℝ) (u : ℂ) : ℂ := csqrt (u ^ 2 + 4 * c ^ 2)

/-- The approximate log step `ĝ`. -/
def gh (c : ℝ) (u : ℂ) : ℂ := -ash (u / (2 * c)) - u / (2 * Sq c u * (Sq c u + 2 * c))

/-- Its antiderivative `Ĝ`. -/
def Gh (c : ℝ) (u : ℂ) : ℂ := -u * ash (u / (2 * c)) + Sq c u - 1 / 2 * Complex.log (2 * c + Sq c u)

/-- `ĝ′`. -/
def gh1 (c : ℝ) (u : ℂ) : ℂ :=
  -(2 * Sq c u ^ 3 + 4 * c * Sq c u ^ 2 - Sq c u ^ 2 + 2 * c * Sq c u + 4 * c ^ 2)
    / (2 * Sq c u ^ 3 * (Sq c u + 2 * c))

/-- `ĝ″`. -/
def gh2 (c : ℝ) (u : ℂ) : ℂ :=
  u * (Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2 + 2 * c * Sq c u ^ 2
    + 12 * c ^ 2 * Sq c u + 12 * c ^ 3) / (Sq c u ^ 5 * (Sq c u + 2 * c) ^ 2)

/-- The principal square root is the root with positive real part. -/
theorem csqrt_eq_of_sq {z w : ℂ} (hw : w ^ 2 = z) (hre : 0 < w.re) : csqrt z = w := by
  have h : csqrt z ^ 2 = w ^ 2 := by rw [csqrt_sq, hw]
  have : (csqrt z - w) * (csqrt z + w) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · linear_combination h1
  · have := re_csqrt_nonneg z
    have e : csqrt z = -w := by linear_combination h1
    rw [e] at this; simp at this; linarith

theorem re_csqrt_pos {z : ℂ} (hz : 0 < z.re) : 0 < (csqrt z).re := by
  unfold csqrt
  rw [Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  apply div_pos _ two_pos
  linarith [norm_nonneg z]

variable {c : ℝ} {u : ℂ}

theorem re_sq_add_pos (hc : 0 < c) (hu : |u.im| < 2 * c) : 0 < (u ^ 2 + 4 * c ^ 2).re := by
  have : (u ^ 2 + 4 * c ^ 2).re = u.re ^ 2 - u.im ^ 2 + 4 * c ^ 2 := by simp [sq]
  rw [this]
  have : u.im ^ 2 < 4 * c ^ 2 := by
    have := abs_lt.mp hu; nlinarith
  nlinarith [sq_nonneg u.re]

theorem re_Sq_pos (hc : 0 < c) (hu : |u.im| < 2 * c) : 0 < (Sq c u).re := re_csqrt_pos (re_sq_add_pos hc hu)

theorem Sq_ne_zero (hc : 0 < c) (hu : |u.im| < 2 * c) : Sq c u ≠ 0 := fun h => by
  have := re_Sq_pos hc hu; rw [h] at this; simp at this

theorem Sq_sq (c : ℝ) (u : ℂ) : Sq c u ^ 2 = u ^ 2 + 4 * c ^ 2 := csqrt_sq _

theorem re_Sq_add_pos (hc : 0 < c) (hu : |u.im| < 2 * c) : 2 * c < (2 * c + Sq c u).re := by
  have := re_Sq_pos hc hu; simp; linarith

theorem Sq_add_ne_zero (hc : 0 < c) (hu : |u.im| < 2 * c) : Sq c u + 2 * c ≠ 0 := fun h => by
  have := re_Sq_add_pos hc hu
  rw [add_comm] at h; rw [h] at this; simp at this; linarith

theorem im_div_lt (hc : 0 < c) (hu : |u.im| < 2 * c) : |(u / (2 * c)).im| < 1 := by
  have : (u / (2 * c)).im = u.im / (2 * c) := by
    rw [show (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]
  rw [this, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * c), div_lt_one (by linarith)]
  exact hu

/-- `2c·√((u/2c)² + 1) = S`. -/
theorem two_c_mul_csqrt (hc : 0 < c) (hu : |u.im| < 2 * c) :
    2 * (c : ℂ) * csqrt ((u / (2 * c)) ^ 2 + 1) = Sq c u := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold Sq
  symm
  apply csqrt_eq_of_sq
  · rw [mul_pow, csqrt_sq]; field_simp; ring
  · have hpos : 0 < ((u / (2 * (c : ℂ))) ^ 2 + 1).re := by
      have hre : ((u / (2 * (c : ℂ))) ^ 2 + 1).re = ((u ^ 2 + 4 * c ^ 2).re) / (4 * c ^ 2) := by
        rw [show (u / (2 * (c : ℂ))) ^ 2 + 1 = (u ^ 2 + 4 * c ^ 2) / ((4 * c ^ 2 : ℝ) : ℂ) by
          push_cast; field_simp; ring, Complex.div_ofReal_re]
      rw [hre]; exact div_pos (re_sq_add_pos hc hu) (by positivity)
    have h := re_csqrt_pos hpos
    have : (2 * (c : ℂ) * csqrt ((u / (2 * c)) ^ 2 + 1)).re = 2 * c * (csqrt ((u / (2 * c)) ^ 2 + 1)).re := by
      simp
    rw [this]; positivity

theorem hasDerivAt_Sq (hc : 0 < c) (hu : |u.im| < 2 * c) : HasDerivAt (Sq c) (u / Sq c u) u := by
  have hs : u ^ 2 + 4 * c ^ 2 ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; exact re_sq_add_pos hc hu
  have h1 : HasDerivAt (fun x : ℂ => x ^ 2 + 4 * c ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (4 * (c : ℂ) ^ 2)
  have h := HasDerivAt.comp (h₂ := csqrt) (h := fun x : ℂ => x ^ 2 + 4 * c ^ 2) u
    (hasDerivAt_csqrt hs) h1
  have hn := Sq_ne_zero hc hu
  have h' : HasDerivAt (Sq c) (1 / (2 * csqrt (u ^ 2 + 4 * c ^ 2)) * (2 * u)) u := h
  refine h'.congr_deriv ?_
  unfold Sq at hn ⊢; field_simp

theorem hasDerivAt_ash_div (hc : 0 < c) (hu : |u.im| < 2 * c) :
    HasDerivAt (fun x => ash (x / (2 * c))) (1 / Sq c u) u := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h := HasDerivAt.comp (h₂ := ash) (h := fun x : ℂ => x / (2 * (c : ℂ))) u
    (hasDerivAt_ash (im_div_lt hc hu)) ((hasDerivAt_id' u).div_const (2 * (c : ℂ)))
  have e := two_c_mul_csqrt hc hu
  have hn := Sq_ne_zero hc hu
  refine h.congr_deriv ?_
  rw [← e]; field_simp

/-- **`Ĝ′ = ĝ`.** -/
theorem hasDerivAt_Gh (hc : 0 < c) (hu : |u.im| < 2 * c) : HasDerivAt (Gh c) (gh c u) u := by
  have hn := Sq_ne_zero hc hu
  have hn2 := Sq_add_ne_zero hc hu
  have hA := hasDerivAt_ash_div hc hu
  have hS := hasDerivAt_Sq hc hu
  have hL := (hS.const_add (2 * (c : ℂ))).clog (by rw [mem_slitPlane_iff]; left; linarith [re_Sq_add_pos hc hu])
  have h := (((hasDerivAt_id u).neg.mul hA).add hS).sub (hL.const_mul (1 / 2 : ℂ))
  have h' : HasDerivAt (Gh c) (-1 * ash (u / (2 * c)) + -u * (1 / Sq c u) + u / Sq c u
      - 1 / 2 * (u / Sq c u / (2 * c + Sq c u))) u := by
    refine h.congr_deriv rfl |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun x => by simp [Gh]
  refine h'.congr_deriv ?_
  unfold gh
  have : 2 * (c : ℂ) + Sq c u ≠ 0 := by rw [add_comm]; exact hn2
  field_simp
  ring

/-- **`ĝ′`.** -/
theorem hasDerivAt_gh (hc : 0 < c) (hu : |u.im| < 2 * c) : HasDerivAt (gh c) (gh1 c u) u := by
  have hn := Sq_ne_zero hc hu
  have hn2 := Sq_add_ne_zero hc hu
  have hA := hasDerivAt_ash_div hc hu
  have hS := hasDerivAt_Sq hc hu
  have hD : HasDerivAt (fun x => 2 * Sq c x * (Sq c x + 2 * c)) (2 * (u / Sq c u) * (Sq c u + 2 * c)
      + 2 * Sq c u * (u / Sq c u)) u := by
    exact (hS.const_mul (2 : ℂ)).mul (hS.add_const (2 * (c : ℂ)))
  have hDne : 2 * Sq c u * (Sq c u + 2 * c) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hn) hn2
  have h := hA.neg.sub ((hasDerivAt_id u).div hD hDne)
  have h' : HasDerivAt (gh c) (-(1 / Sq c u) - (1 * (2 * Sq c u * (Sq c u + 2 * c))
      - u * (2 * (u / Sq c u) * (Sq c u + 2 * c) + 2 * Sq c u * (u / Sq c u))) / (2 * Sq c u * (Sq c u + 2 * c)) ^ 2) u := by
    refine (h.congr_deriv rfl).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun x => by simp [gh]
  refine h'.congr_deriv ?_
  have hS2 := Sq_sq c u
  unfold gh1
  field_simp
  linear_combination (-(2 * Sq c u + 2 * c)) * hS2

/-- **`ĝ″`.** -/
theorem hasDerivAt_gh1 (hc : 0 < c) (hu : |u.im| < 2 * c) : HasDerivAt (gh1 c) (gh2 c u) u := by
  have hn := Sq_ne_zero hc hu
  have hn2 := Sq_add_ne_zero hc hu
  have hS := hasDerivAt_Sq hc hu
  have hN : HasDerivAt (fun x => 2 * Sq c x ^ 3 + 4 * c * Sq c x ^ 2 - Sq c x ^ 2 + 2 * c * Sq c x + 4 * c ^ 2)
      ((6 * Sq c u ^ 2 + 8 * c * Sq c u - 2 * Sq c u + 2 * c) * (u / Sq c u)) u := by
    have h := (((((hS.pow 3).const_mul (2 : ℂ)).add ((hS.pow 2).const_mul (4 * (c : ℂ)))).sub (hS.pow 2)).add
      (hS.const_mul (2 * (c : ℂ)))).add_const (4 * (c : ℂ) ^ 2)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by simp)
    push_cast; ring
  have hD : HasDerivAt (fun x => 2 * Sq c x ^ 3 * (Sq c x + 2 * c))
      ((8 * Sq c u ^ 3 + 12 * c * Sq c u ^ 2) * (u / Sq c u)) u := by
    have h := ((hS.pow 3).const_mul (2 : ℂ)).mul (hS.add_const (2 * (c : ℂ)))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by simp)
    simp only [Pi.pow_apply]; push_cast; ring
  have hDne : 2 * Sq c u ^ 3 * (Sq c u + 2 * c) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 3 hn)) hn2
  have h := (hN.div hD hDne).neg
  refine (h.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => by simp only [gh1, Pi.neg_apply, Pi.div_apply]; ring)
  unfold gh2
  field_simp
  ring

/-- On the imaginary axis, `S(iz) = 2c cos θ` with `sin θ = z/(2c)`. -/
theorem Sq_I_mul (hc : 0 < c) {z : ℝ} (hz : |z| < 2 * c) :
    Sq c (I * z) = ((2 * c * Real.cos (Real.arcsin (z / (2 * c))) : ℝ) : ℂ) := by
  have hx : |z / (2 * c)| < 1 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * c), div_lt_one (by linarith)]; exact hz
  have hx1 := abs_lt.mp hx
  rw [Real.cos_arcsin]
  unfold Sq
  have e : (I * (z : ℂ)) ^ 2 + 4 * (c : ℂ) ^ 2 = ((4 * c ^ 2 - z ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [mul_pow, Complex.I_sq]; ring
  rw [e, csqrt_ofReal (by nlinarith [abs_lt.mp hz])]
  congr 1
  rw [show 4 * c ^ 2 - z ^ 2 = (2 * c) ^ 2 * (1 - (z / (2 * c)) ^ 2) by field_simp; ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]

/-- **`Ĝ` on the imaginary axis**: `Ĝ(iz) = 2c(θ sin θ + cos θ) − ½ log(2c(1 + cos θ))`, `sin θ = z/(2c)`. -/
theorem Gh_I_mul (hc : 0 < c) {z : ℝ} (hz : |z| < 2 * c) :
    Gh c (I * z) = ((2 * c * (Real.arcsin (z / (2 * c)) * (z / (2 * c)) + Real.cos (Real.arcsin (z / (2 * c))))
      - 1 / 2 * Real.log (2 * c * (1 + Real.cos (Real.arcsin (z / (2 * c))))) : ℝ) : ℂ) := by
  set θ := Real.arcsin (z / (2 * c))
  have hx : |z / (2 * c)| < 1 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * c), div_lt_one (by linarith)]; exact hz
  have hx1 := abs_lt.mp hx
  have hsin : Real.sin θ = z / (2 * c) := Real.sin_arcsin (by linarith) (by linarith)
  have hθ : |θ| < Real.pi / 2 := by
    rw [abs_lt]; constructor
    · have := Real.neg_pi_div_two_lt_arcsin.mpr hx1.1; exact this
    · exact Real.arcsin_lt_pi_div_two.mpr hx1.2
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ], by linarith [le_abs_self θ]⟩
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hw : I * (z : ℂ) / (2 * c) = I * (Real.sin θ : ℂ) := by
    rw [hsin]; push_cast; field_simp
  unfold Gh
  rw [hw, ash_I_mul_sin hθ, Sq_I_mul hc hz]
  have hpos : 0 < 2 * c * (1 + Real.cos θ) := by positivity
  rw [show (2 * (c : ℂ) + ((2 * c * Real.cos θ : ℝ) : ℂ)) = ((2 * c * (1 + Real.cos θ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log hpos.le]
  have hII : -(I * (z : ℂ)) * (I * (θ : ℂ)) = z * θ := by
    rw [show -(I * (z : ℂ)) * (I * θ) = -(I * I) * z * θ by ring, Complex.I_mul_I]; ring
  rw [hII]
  push_cast
  field_simp
  ring

/-- `ĝ` is purely imaginary on the imaginary axis. -/
theorem re_gh_I_mul (hc : 0 < c) {z : ℝ} (hz : |z| < 2 * c) : (gh c (I * z)).re = 0 := by
  set θ := Real.arcsin (z / (2 * c))
  have hx : |z / (2 * c)| < 1 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * c), div_lt_one (by linarith)]; exact hz
  have hx1 := abs_lt.mp hx
  have hsin : Real.sin θ = z / (2 * c) := Real.sin_arcsin (by linarith) (by linarith)
  have hθ : |θ| < Real.pi / 2 := by
    rw [abs_lt]; constructor
    · exact Real.neg_pi_div_two_lt_arcsin.mpr hx1.1
    · exact Real.arcsin_lt_pi_div_two.mpr hx1.2
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hw : I * (z : ℂ) / (2 * c) = I * (Real.sin θ : ℂ) := by
    rw [hsin]; push_cast; field_simp
  unfold gh
  rw [hw, ash_I_mul_sin hθ, Sq_I_mul hc hz]
  set r := 2 * c * Real.cos θ
  have e : I * (z : ℂ) / (2 * (r : ℂ) * ((r : ℂ) + 2 * c)) = I * ((z / (2 * r * (r + 2 * c)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

end Cvs.Prolate.Mellin.WkbPhaseAntiderivative
