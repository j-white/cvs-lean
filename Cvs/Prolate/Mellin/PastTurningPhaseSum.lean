import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.PastTurningCanonicalLog
import Cvs.Prolate.Mellin.PastTurningErrorsSummed
import Cvs.Prolate.Mellin.PastTurningRootSizes
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Upstream.ComplexArsinhStrip
import Cvs.Upstream.HolomorphicTrapezoidStep
import Cvs.Upstream.InvSqrtKernelStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The WKB phase summed along a line past the turning point

On `Re u > 0`, `Im u > 0`: `S = √(u² + 4c²)` is holomorphic with `S′ = u/S`, `(ash(u/2c))′ = 1/S`, and
`Ĝ′ = ĝ`, `ĝ′ = ĝ₁`, `ĝ₁′ = ĝ₂` as on the strip. With `|S| ≥ √ε|u|/3` when `Im u ≥ (2 + ε/2)c`, `WkbPhaseTrapezoidSum`'s bound gives
`|ĝ₂(u)| ≤ 189/(ε^{3/2}|u|²)`, and along `u_k = u₀ + 2k` with `Re u₀ ≥ 2`, `Im u₀ ≥ (2 + ε)c`:
`|Σ_{k<K} ĝ(u_k) − ½(Ĝ(u_K) − Ĝ(u₀)) − ½(ĝ(u₀) − ĝ(u_K))| ≤ 189/(ε^{3/2}c)`.
-/

noncomputable section

open Complex Finset

namespace Cvs.Prolate.Mellin.PastTurningPhaseSum

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg)
open Cvs.Upstream.ComplexArsinhStrip (ash hasDerivAt_csqrt)
open Cvs.Prolate.Mellin.WkbPhaseAntiderivative (Sq Sq_sq gh Gh gh1 gh2)
open Cvs.Prolate.Mellin.PastTurningCanonicalLog (re_csqrt_pos_of_im two_c_mul_csqrt' norm_csqrt_ge)

variable {c ε : ℝ} {u : ℂ}

theorem sq_add_mem (hc : 0 < c) (hre : 0 < u.re) : u ^ 2 + 4 * c ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hi : u.im = 0
  · left
    have : (u ^ 2 + 4 * (c : ℂ) ^ 2).re = u.re ^ 2 - u.im ^ 2 + 4 * c ^ 2 := by simp [sq]
    rw [this, hi]; nlinarith [sq_nonneg u.re, mul_pos hc hc]
  · right
    have : (u ^ 2 + 4 * (c : ℂ) ^ 2).im = 2 * u.re * u.im := by simp [sq]; ring
    rw [this]; exact mul_ne_zero (mul_ne_zero two_ne_zero hre.ne') hi

theorem Sq_ne (hc : 0 < c) (hre : 0 < u.re) : Sq c u ≠ 0 := by
  intro h0
  have := Sq_sq c u
  rw [h0] at this
  have hs := sq_add_mem hc hre
  rw [← this] at hs; simp at hs

theorem re_Sq_add_pos (hc : 0 < c) : 0 < (2 * (c : ℂ) + Sq c u).re := by
  have := re_csqrt_nonneg (u ^ 2 + 4 * c ^ 2)
  unfold Sq; simp; linarith

theorem Sq_add_ne (hc : 0 < c) : Sq c u + 2 * c ≠ 0 := by
  intro h0
  have := re_Sq_add_pos (u := u) hc
  rw [add_comm, h0] at this; simp at this

theorem hasDerivAt_Sq (hc : 0 < c) (hre : 0 < u.re) : HasDerivAt (Sq c) (u / Sq c u) u := by
  have hs := sq_add_mem hc hre
  have h1 : HasDerivAt (fun x : ℂ => x ^ 2 + 4 * c ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (4 * (c : ℂ) ^ 2)
  have h := HasDerivAt.comp (h₂ := csqrt) (h := fun x : ℂ => x ^ 2 + 4 * c ^ 2) u
    (hasDerivAt_csqrt hs) h1
  have hn := Sq_ne hc hre
  have h' : HasDerivAt (Sq c) (1 / (2 * csqrt (u ^ 2 + 4 * c ^ 2)) * (2 * u)) u := h
  refine h'.congr_deriv ?_
  unfold Sq at hn ⊢; field_simp

theorem hasDerivAt_ash_div (hc : 0 < c) (hre : 0 < u.re) (him : 0 < u.im) :
    HasDerivAt (fun x => ash (x / (2 * c))) (1 / Sq c u) u := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hv : 0 < (u / (2 * (c : ℂ))).re := by
    rw [show (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]; positivity
  have h := HasDerivAt.comp (h₂ := ash) (h := fun x : ℂ => x / (2 * (c : ℂ))) u
    (Cvs.Prolate.Mellin.PastTurningCanonicalLog.hasDerivAt_ash hv) ((hasDerivAt_id' u).div_const (2 * (c : ℂ)))
  have e := two_c_mul_csqrt' hc hre him
  have hn := Sq_ne hc hre
  refine h.congr_deriv ?_
  unfold Cvs.Upstream.InvSqrtKernelStrip.kf
  rw [← e]; field_simp

/-- **`Ĝ′ = ĝ`** on `Re u > 0`, `Im u > 0`. -/
theorem hasDerivAt_Gh (hc : 0 < c) (hre : 0 < u.re) (him : 0 < u.im) : HasDerivAt (Gh c) (gh c u) u := by
  have hn := Sq_ne hc hre
  have hn2 := Sq_add_ne (u := u) hc
  have hA := hasDerivAt_ash_div hc hre him
  have hS := hasDerivAt_Sq hc hre
  have hL := (hS.const_add (2 * (c : ℂ))).clog (by rw [mem_slitPlane_iff]; left; exact re_Sq_add_pos hc)
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

/-- **`ĝ′ = ĝ₁`** on `Re u > 0`, `Im u > 0`. -/
theorem hasDerivAt_gh (hc : 0 < c) (hre : 0 < u.re) (him : 0 < u.im) : HasDerivAt (gh c) (gh1 c u) u := by
  have hn := Sq_ne hc hre
  have hn2 := Sq_add_ne (u := u) hc
  have hA := hasDerivAt_ash_div hc hre him
  have hS := hasDerivAt_Sq hc hre
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

/-- **`ĝ₁′ = ĝ₂`** on `Re u > 0`. -/
theorem hasDerivAt_gh1 (hc : 0 < c) (hre : 0 < u.re) : HasDerivAt (gh1 c) (gh2 c u) u := by
  have hn := Sq_ne hc hre
  have hn2 := Sq_add_ne (u := u) hc
  have hS := hasDerivAt_Sq hc hre
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

/-- `|S|² + 4c² ≤ |S + 2c|²`, since `Re S ≥ 0`. -/
theorem norm_add_sq_ge (hc : 0 < c) : ‖Sq c u‖ ^ 2 + 4 * c ^ 2 ≤ ‖Sq c u + 2 * c‖ ^ 2 := by
  have hre := re_csqrt_nonneg (u ^ 2 + 4 * c ^ 2)
  have e1 : ‖Sq c u‖ ^ 2 = (Sq c u).re ^ 2 + (Sq c u).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e2 : ‖Sq c u + 2 * c‖ ^ 2 = ((Sq c u).re + 2 * c) ^ 2 + (Sq c u).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [e1, e2]
  unfold Sq at *
  nlinarith

/-- **`|ĝ₂| ≤ 7|u|/|S|³`** once `|S| ≥ 3`, `|S|² ≥ 3c`, `c ≥ 1`, `Re u > 0`. -/
theorem norm_gh2_le (hc : 1 ≤ c) (hre : 0 < u.re) (h3 : 3 ≤ ‖Sq c u‖) (h3c : 3 * c ≤ ‖Sq c u‖ ^ 2) :
    ‖gh2 c u‖ ≤ 7 * ‖u‖ / ‖Sq c u‖ ^ 3 := by
  have hc0 : 0 < c := by linarith
  set σ := ‖Sq c u‖
  have hσ : 0 < σ := by linarith
  have hQ := norm_add_sq_ge (u := u) hc0
  have hcn : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc0.le]
  have hP : ‖Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2 + 2 * c * Sq c u ^ 2
      + 12 * c ^ 2 * Sq c u + 12 * c ^ 3‖
      ≤ σ ^ 4 + 4 * c * σ ^ 3 + σ ^ 3 + 4 * c ^ 2 * σ ^ 2 + 2 * c * σ ^ 2 + 12 * c ^ 2 * σ + 12 * c ^ 3 := by
    have t := fun (a b : ℂ) => norm_add_le a b
    have s := fun (a b : ℂ) => norm_sub_le a b
    have n1 : ‖Sq c u ^ 4‖ = σ ^ 4 := by rw [norm_pow]
    have n2 : ‖4 * (c : ℂ) * Sq c u ^ 3‖ = 4 * c * σ ^ 3 := by
      rw [norm_mul, norm_mul, norm_pow, hcn]; norm_num; try (left; rfl)
    have n3 : ‖Sq c u ^ 3‖ = σ ^ 3 := by rw [norm_pow]
    have n4 : ‖4 * (c : ℂ) ^ 2 * Sq c u ^ 2‖ = 4 * c ^ 2 * σ ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, hcn]; norm_num; try (left; rfl)
    have n5 : ‖2 * (c : ℂ) * Sq c u ^ 2‖ = 2 * c * σ ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow, hcn]; norm_num; try (left; rfl)
    have n6 : ‖12 * (c : ℂ) ^ 2 * Sq c u‖ = 12 * c ^ 2 * σ := by
      rw [norm_mul, norm_mul, norm_pow, hcn]; norm_num; try (left; rfl)
    have n7 : ‖12 * (c : ℂ) ^ 3‖ = 12 * c ^ 3 := by
      rw [norm_mul, norm_pow, hcn]; norm_num; try (left; rfl)
    have := t (Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2 + 2 * c * Sq c u ^ 2
      + 12 * c ^ 2 * Sq c u) (12 * c ^ 3)
    have := t (Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2 + 2 * c * Sq c u ^ 2)
      (12 * c ^ 2 * Sq c u)
    have := t (Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2) (2 * c * Sq c u ^ 2)
    have := t (Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3) (4 * c ^ 2 * Sq c u ^ 2)
    have := s (Sq c u ^ 4 + 4 * c * Sq c u ^ 3) (Sq c u ^ 3)
    have := t (Sq c u ^ 4) (4 * c * Sq c u ^ 3)
    linarith
  have hP7 : σ ^ 4 + 4 * c * σ ^ 3 + σ ^ 3 + 4 * c ^ 2 * σ ^ 2 + 2 * c * σ ^ 2 + 12 * c ^ 2 * σ + 12 * c ^ 3
      ≤ 7 * σ ^ 2 * (σ ^ 2 + 4 * c ^ 2) := by
    have a1 : 4 * c * σ ^ 3 + σ ^ 3 ≤ 2 * σ ^ 2 * (σ ^ 2 + 4 * c ^ 2) := by
      have : 4 * c * σ ≤ σ ^ 2 + 4 * c ^ 2 := by nlinarith [sq_nonneg (σ - 2 * c)]
      have : σ ≤ σ ^ 2 + 4 * c ^ 2 := by nlinarith
      nlinarith [sq_nonneg σ]
    have a2 : 4 * c ^ 2 * σ ^ 2 + 2 * c * σ ^ 2 ≤ 2 * σ ^ 2 * (σ ^ 2 + 4 * c ^ 2) := by
      have : 2 * c ≤ 4 * c ^ 2 := by nlinarith
      nlinarith [sq_nonneg σ]
    have a3 : 12 * c ^ 2 * σ ≤ σ ^ 2 * (σ ^ 2 + 4 * c ^ 2) := by
      have : 12 * c ^ 2 ≤ σ * (4 * c ^ 2) := by nlinarith
      nlinarith [sq_nonneg σ]
    have a4 : 12 * c ^ 3 ≤ σ ^ 2 * (σ ^ 2 + 4 * c ^ 2) := by
      have : 12 * c ^ 3 ≤ σ ^ 2 * (4 * c ^ 2) := by nlinarith
      nlinarith [sq_nonneg σ, sq_nonneg (σ ^ 2)]
    nlinarith [sq_nonneg σ]
  unfold gh2
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
  have hD : 0 < σ ^ 5 * ‖Sq c u + 2 * c‖ ^ 2 := by
    have : 0 < ‖Sq c u + 2 * c‖ := norm_pos_iff.mpr (Sq_add_ne hc0)
    positivity
  rw [div_le_div_iff₀ hD (by positivity)]
  calc ‖u‖ * ‖Sq c u ^ 4 + 4 * c * Sq c u ^ 3 - Sq c u ^ 3 + 4 * c ^ 2 * Sq c u ^ 2 + 2 * c * Sq c u ^ 2
        + 12 * c ^ 2 * Sq c u + 12 * c ^ 3‖ * σ ^ 3
      ≤ ‖u‖ * (7 * σ ^ 2 * (σ ^ 2 + 4 * c ^ 2)) * σ ^ 3 := by gcongr; exact hP.trans hP7
    _ = 7 * ‖u‖ * (σ ^ 5 * (σ ^ 2 + 4 * c ^ 2)) := by ring
    _ ≤ 7 * ‖u‖ * (σ ^ 5 * ‖Sq c u + 2 * c‖ ^ 2) := by gcongr

/-- `|S| ≥ √ε|u|/3` when `Re u > 0` and `Im u ≥ (2 + ε/2)c`. -/
theorem norm_Sq_ge (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hre : 0 < u.re) (him : (2 + ε / 2) * c ≤ u.im) :
    Real.sqrt ε * ‖u‖ / 3 ≤ ‖Sq c u‖ := by
  have hpos : 0 < u.im := by nlinarith
  have e := two_c_mul_csqrt' hc hre hpos
  have hvim : 1 + ε / 4 ≤ (u / (2 * (c : ℂ))).im := by
    rw [show (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im,
      le_div_iff₀ (by positivity)]
    nlinarith
  have h1 := norm_csqrt_ge hε hε1 hvim
  rw [← e, norm_mul, show ‖(2 * (c : ℂ))‖ = 2 * c by
    rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hc.le]]
  have hvn : ‖u / (2 * (c : ℂ))‖ = ‖u‖ / (2 * c) := by
    rw [norm_div, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hc.le]
  rw [hvn] at h1
  calc Real.sqrt ε * ‖u‖ / 3 = 2 * c * (Real.sqrt ε * (‖u‖ / (2 * c)) / 3) := by field_simp
    _ ≤ _ := by gcongr

/-- **`|ĝ₂(u)| ≤ 189/(ε^{3/2}|u|²)`** on `Re u > 0`, `Im u ≥ (2 + ε/2)c`, `c ≥ 64/ε²`. -/
theorem norm_gh2_region (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 64 / ε ^ 2 ≤ c) (hre : 0 < u.re)
    (him : (2 + ε / 2) * c ≤ u.im) : ‖gh2 c u‖ ≤ 189 / (ε * Real.sqrt ε * ‖u‖ ^ 2) := by
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hrr : r * r = ε := Real.mul_self_sqrt hε.le
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hc64 : 64 ≤ c := by
    have : 64 ≤ 64 / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hc0 : 0 < c := by linarith
  have hcε : 64 ≤ c * ε ^ 2 := by rw [div_le_iff₀ (by positivity)] at hc; linarith
  have hun : 2 * c ≤ ‖u‖ := by
    have := Cvs.Prolate.Mellin.PastTurningRootSizes.im_le_norm u; nlinarith
  have hS := norm_Sq_ge hε hε1 hc0 hre him
  have hupos : 0 < ‖u‖ := by linarith
  -- `r·c ≥ 64`
  have hrc : 64 ≤ r * c := by
    have h4 : r ^ 4 = ε ^ 2 := by rw [← hrr]; ring
    have hr3 : r ^ 3 ≤ 1 := pow_le_one₀ hr0.le hr1
    nlinarith
  have h3 : 3 ≤ ‖Sq c u‖ := by
    refine le_trans ?_ hS
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have h3c : 3 * c ≤ ‖Sq c u‖ ^ 2 := by
    have : (r * ‖u‖ / 3) ^ 2 ≤ ‖Sq c u‖ ^ 2 := pow_le_pow_left₀ (by positivity) hS 2
    refine le_trans ?_ this
    have hεc : 64 ≤ ε * c := by nlinarith
    have hu2 : (2 * c) ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (by positivity) hun 2
    have : ε * (2 * c) ^ 2 ≤ (r * ‖u‖) ^ 2 := by
      have e : (r * ‖u‖) ^ 2 = ε * ‖u‖ ^ 2 := by rw [← hrr]; ring
      rw [e]; gcongr
    rw [div_pow]
    nlinarith
  refine (norm_gh2_le (by linarith) hre h3 h3c).trans ?_
  have hS3 : (r * ‖u‖ / 3) ^ 3 ≤ ‖Sq c u‖ ^ 3 := pow_le_pow_left₀ (by positivity) hS 3
  calc 7 * ‖u‖ / ‖Sq c u‖ ^ 3 ≤ 7 * ‖u‖ / (r * ‖u‖ / 3) ^ 3 := by gcongr
    _ = 189 / (r * r * r * ‖u‖ ^ 2) := by field_simp; ring
    _ = 189 / (ε * r * ‖u‖ ^ 2) := by rw [hrr]

/-- **The trapezoid sum past the turning point.** -/
theorem norm_sum_gh_sub_le (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 64 / ε ^ 2 ≤ c) {u₀ : ℂ} (hx : 2 ≤ u₀.re)
    (hy : (2 + ε) * c ≤ u₀.im) (K : ℕ) :
    ‖∑ k ∈ range K, gh c (u₀ + 2 * k) - (1 / 2 * (Gh c (u₀ + 2 * K) - Gh c u₀)
        + 1 / 2 * (gh c u₀ - gh c (u₀ + 2 * K)))‖
      ≤ 189 / (ε * Real.sqrt ε * c) := by
  have hc64 : 64 ≤ c := by
    have : 64 ≤ 64 / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hc0 : 0 < c := by linarith
  have hεs : 0 < ε * Real.sqrt ε := by have := Real.sqrt_pos.mpr hε; positivity
  set κ := 189 / (ε * Real.sqrt ε)
  have hκ : 0 ≤ κ := by positivity
  have hyi : (2 + ε / 2) * c ≤ u₀.im := by nlinarith
  -- `|u₀ + 2k + t| ≥ |u₀ + 2k|` and `|u₀ + 2k|² ≥ (2c)² + (2k + 2)²`
  have hmk : ∀ k : ℕ, (2 * c) ^ 2 + (2 * k + 2) ^ 2 ≤ ‖u₀ + 2 * k‖ ^ 2 := by
    intro k
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (u₀ + 2 * (k : ℂ)).re = u₀.re + 2 * k := by simp
    have him : (u₀ + 2 * (k : ℂ)).im = u₀.im := by simp
    rw [hre, him]
    have hk := k.cast_nonneg (α := ℝ)
    have : 2 * c ≤ u₀.im := by nlinarith
    nlinarith
  set err := fun k : ℕ => Gh c (u₀ + 2 * (k + 1 : ℕ)) - Gh c (u₀ + 2 * k) - (gh c (u₀ + 2 * k) + gh c (u₀ + 2 * (k + 1 : ℕ)))
  have herr : ∀ k : ℕ, ‖err k‖ ≤ 4 * (κ * (1 / ‖u₀ + 2 * k‖ ^ 2)) := by
    intro k
    set v := u₀ + 2 * (k : ℂ)
    have hvim : v.im = u₀.im := by simp [v]
    have hvre : v.re = u₀.re + 2 * k := by simp [v]
    have hvpos : 0 < ‖v‖ := by
      have := hmk k; have : 0 < (2 * c) ^ 2 + (2 * (k : ℝ) + 2) ^ 2 := by positivity
      by_contra hn; push Not at hn
      have : ‖v‖ = 0 := le_antisymm hn (norm_nonneg _); nlinarith
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 2, 0 < (v + t).re ∧ (2 + ε / 2) * c ≤ (v + t).im ∧ ‖v‖ ≤ ‖v + t‖ := by
      intro t ht
      refine ⟨by simp [hvre]; have := k.cast_nonneg (α := ℝ); linarith [ht.1], by simp [hvim]; exact hyi, ?_⟩
      have := Cvs.Prolate.Mellin.PastTurningRootSizes.norm_add_mono (s := v) (by rw [hvre]; have := k.cast_nonneg (α := ℝ); linarith)
        (a := 0) (b := t) le_rfl ht.1
      simpa using this
    have h := Cvs.Upstream.HolomorphicTrapezoidStep.norm_trapezoid_le (F := Gh c) (f := gh c) (f₁ := gh1 c) (f₂ := gh2 c)
      (u := v) (M := κ * (1 / ‖v‖ ^ 2))
      (fun t ht => hasDerivAt_Gh hc0 (hpt t ht).1 (by nlinarith [(hpt t ht).2.1]))
      (fun t ht => hasDerivAt_gh hc0 (hpt t ht).1 (by nlinarith [(hpt t ht).2.1]))
      (fun t ht => hasDerivAt_gh1 hc0 (hpt t ht).1)
      (fun t ht => by
        have h1 := norm_gh2_region hε hε1 hc (hpt t ht).1 (hpt t ht).2.1
        refine h1.trans ?_
        have hle := (hpt t ht).2.2
        have : 0 < ‖v + t‖ := lt_of_lt_of_le hvpos hle
        calc 189 / (ε * Real.sqrt ε * ‖v + t‖ ^ 2) = κ * (1 / ‖v + t‖ ^ 2) := by simp only [κ]; field_simp
          _ ≤ κ * (1 / ‖v‖ ^ 2) := by gcongr)
    have e : v + 2 = u₀ + 2 * ((k + 1 : ℕ) : ℂ) := by simp only [v]; push_cast; ring
    rw [e] at h
    exact h
  have htel : ∑ k ∈ range K, err k = Gh c (u₀ + 2 * K) - Gh c u₀ - (2 * ∑ k ∈ range K, gh c (u₀ + 2 * k)
      - gh c u₀ + gh c (u₀ + 2 * K)) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [err]; push_cast; ring
  have e : ∑ k ∈ range K, gh c (u₀ + 2 * k) - (1 / 2 * (Gh c (u₀ + 2 * K) - Gh c u₀)
      + 1 / 2 * (gh c u₀ - gh c (u₀ + 2 * K))) = -(1 / 2 : ℂ) * ∑ k ∈ range K, err k := by
    rw [htel]; ring
  rw [e, norm_mul]
  have hn : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hn]
  have hsum2 : ∑ k ∈ range K, 1 / ‖u₀ + 2 * k‖ ^ 2 ≤ 1 / (2 * c) := by
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (Cvs.Prolate.Mellin.PastTurningErrorsSummed.sum_inv_le' (a := 2 * c) (by positivity) K)
    exact one_div_le_one_div_of_le (by positivity) (hmk k)
  have hsum : ‖∑ k ∈ range K, err k‖ ≤ 4 * κ * (1 / (2 * c)) := by
    calc _ ≤ ∑ k ∈ range K, ‖err k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ range K, 4 * κ * (1 / ‖u₀ + 2 * k‖ ^ 2) := Finset.sum_le_sum fun k _ => by
          refine (herr k).trans (le_of_eq ?_); ring
      _ = 4 * κ * ∑ k ∈ range K, 1 / ‖u₀ + 2 * k‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * κ * (1 / (2 * c)) := by gcongr
  calc 1 / 2 * ‖∑ k ∈ range K, err k‖ ≤ 1 / 2 * (4 * κ * (1 / (2 * c))) := by gcongr
    _ = 189 / (ε * Real.sqrt ε * c) := by simp only [κ]; field_simp; ring

end Cvs.Prolate.Mellin.PastTurningPhaseSum
