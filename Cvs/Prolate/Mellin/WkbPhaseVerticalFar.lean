import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.PastTurningCanonicalLog
import Cvs.Prolate.Mellin.PastTurningPhaseSum
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Upstream.ComplexArsinhStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The WKB phase on vertical segments far out

`|ĝ′| ≤ 13/(2|S|)` once `|S| ≥ max(1, c)`, since `Re S ≥ 0`. On the segment `[x, x + iz]` with `z ≥ 0` and
`x ≥ z + c + 1`, `|S| ≥ x − z`, so `|ĝ(x + iz) − ĝ(x)| ≤ 13z/(2(x − z))` and
`|Ĝ(x + iz) − Ĝ(x) − iz ĝ(x)| ≤ 13z²/(2(x − z))`; and for real `x > 0`, `|x/(2S(S + 2c))| ≤ 1/(2x)`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.WkbPhaseVerticalFar

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg)
open Cvs.Prolate.Mellin.WkbPhaseAntiderivative (Sq Sq_sq gh Gh gh1)

variable {c : ℝ} {w : ℂ}

/-- **`|ĝ′| ≤ 13/(2|S|)`** once `|S| ≥ 1` and `|S| ≥ c`. -/
theorem norm_gh1_le (hc : 0 < c) (h1 : 1 ≤ ‖Sq c w‖) (hcs : c ≤ ‖Sq c w‖) : ‖gh1 c w‖ ≤ 13 / (2 * ‖Sq c w‖) := by
  set σ := ‖Sq c w‖
  have hσ : 0 < σ := by linarith
  have hcn : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hS2 : σ ≤ ‖Sq c w + 2 * c‖ := by
    have := Cvs.Prolate.Mellin.PastTurningPhaseSum.norm_add_sq_ge (u := w) hc
    nlinarith [norm_nonneg (Sq c w + 2 * c)]
  have hnum : ‖2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w + 4 * c ^ 2‖ ≤ 13 * σ ^ 3 := by
    have t1 := norm_add_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w) (4 * (c : ℂ) ^ 2)
    have t2 := norm_add_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2) (2 * (c : ℂ) * Sq c w)
    have t3 := norm_sub_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2) (Sq c w ^ 2)
    have t4 := norm_add_le (2 * Sq c w ^ 3) (4 * (c : ℂ) * Sq c w ^ 2)
    simp only [norm_mul, norm_pow, hcn, Complex.norm_ofNat] at t1 t2 t3 t4
    have : c * σ ^ 2 ≤ σ ^ 3 := by nlinarith
    have : σ ^ 2 ≤ σ ^ 3 := by nlinarith
    have : c * σ ≤ σ ^ 3 := by nlinarith
    have : c ^ 2 ≤ σ ^ 3 := by nlinarith
    linarith
  unfold gh1
  rw [norm_div, norm_neg, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat,
    div_le_div_iff₀ (by have := lt_of_lt_of_le hσ hS2; positivity) (by positivity)]
  calc ‖2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w + 4 * c ^ 2‖ * (2 * σ)
      ≤ 13 * σ ^ 3 * (2 * σ) := by gcongr
    _ = 13 * (2 * σ ^ 3 * σ) := by ring
    _ ≤ 13 * (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) := by gcongr

/-- `|S(w)| ≥ x − z` for `Re w = x ≥ z ≥ |Im w| ≥ 0`. -/
theorem norm_Sq_ge {x z : ℝ} (hz : 0 ≤ z) (hxz : z ≤ x) (hre : w.re = x) (him : |w.im| ≤ z) :
    x - z ≤ ‖Sq c w‖ := by
  have hw : ‖Sq c w‖ ^ 2 = ‖w ^ 2 + 4 * c ^ 2‖ := by unfold Sq; rw [← norm_pow, csqrt_sq]
  have h1 : (w ^ 2 + 4 * (c : ℂ) ^ 2).re ≤ ‖w ^ 2 + 4 * (c : ℂ) ^ 2‖ := Complex.re_le_norm _
  have h2 : (w ^ 2 + 4 * (c : ℂ) ^ 2).re = w.re ^ 2 - w.im ^ 2 + 4 * c ^ 2 := by simp [sq]
  have him2 : w.im ^ 2 ≤ z ^ 2 := by nlinarith [abs_nonneg w.im, sq_abs w.im]
  have hsq : (x - z) ^ 2 ≤ ‖Sq c w‖ ^ 2 := by rw [hw]; nlinarith [sq_nonneg c]
  exact (pow_le_pow_iff_left₀ (by linarith) (norm_nonneg _) two_ne_zero).mp hsq

/-- The derivatives along the segment `[x, x + iz]`. -/
theorem seg_facts (hc : 0 < c) {x z : ℝ} (hz : 0 ≤ z) (hx : z + c + 1 ≤ x) {w : ℂ}
    (hw : w ∈ segment ℝ (x : ℂ) ((x : ℂ) + I * z)) :
    HasDerivAt (Gh c) (gh c w) w ∧ HasDerivAt (gh c) (gh1 c w) w ∧ ‖gh1 c w‖ ≤ 13 / (2 * (x - z)) := by
  rw [segment_eq_image'] at hw
  obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := hw
  have hre : ((x : ℂ) + l • ((x : ℂ) + I * z - x)).re = x := by simp
  have him : ((x : ℂ) + l • ((x : ℂ) + I * z - x)).im = l * z := by simp
  set w := (x : ℂ) + l • ((x : ℂ) + I * z - x)
  have hxpos : 0 < w.re := by rw [hre]; linarith
  have himn : 0 ≤ w.im := by rw [him]; positivity
  have himz : |w.im| ≤ z := by rw [him, abs_of_nonneg (by positivity)]; nlinarith
  have hS := norm_Sq_ge (c := c) hz (by linarith) hre himz
  have hb := norm_gh1_le (w := w) hc (by linarith) (by linarith)
  refine ⟨?_, ?_, hb.trans ?_⟩
  · rcases himn.lt_or_eq with hp | h0
    · exact Cvs.Prolate.Mellin.PastTurningPhaseSum.hasDerivAt_Gh hc hxpos hp
    · exact Cvs.Prolate.Mellin.WkbPhaseAntiderivative.hasDerivAt_Gh hc (by rw [← h0]; simp; linarith)
  · rcases himn.lt_or_eq with hp | h0
    · exact Cvs.Prolate.Mellin.PastTurningPhaseSum.hasDerivAt_gh hc hxpos hp
    · exact Cvs.Prolate.Mellin.WkbPhaseAntiderivative.hasDerivAt_gh hc (by rw [← h0]; simp; linarith)
  · exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- **The vertical steps** of `ĝ` and `Ĝ`. -/
theorem vertical (hc : 0 < c) {x z : ℝ} (hz : 0 ≤ z) (hx : z + c + 1 ≤ x) :
    ‖gh c ((x : ℂ) + I * z) - gh c x‖ ≤ 13 / (2 * (x - z)) * z
      ∧ ‖Gh c ((x : ℂ) + I * z) - Gh c x - I * z * gh c x‖ ≤ 13 / (2 * (x - z)) * z ^ 2 := by
  have hconv : Convex ℝ (segment ℝ (x : ℂ) ((x : ℂ) + I * z)) := convex_segment _ _
  have ha := left_mem_segment ℝ (x : ℂ) ((x : ℂ) + I * z)
  have hb := right_mem_segment ℝ (x : ℂ) ((x : ℂ) + I * z)
  have hd : ‖(x : ℂ) + I * z - x‖ = z := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hz, one_mul]
  constructor
  · have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := gh c) (f' := gh1 c)
      (fun w hw => (seg_facts hc hz hx hw).2.1.hasDerivWithinAt) (fun w hw => (seg_facts hc hz hx hw).2.2) ha hb
    rwa [hd] at this
  · have := Cvs.Prolate.Mellin.PastTurningCanonicalLog.taylor2 hconv (f := Gh c) (f₁ := gh c) (f₂ := gh1 c)
      (fun w hw => (seg_facts hc hz hx hw).1) (fun w hw => (seg_facts hc hz hx hw).2.1)
      (fun w hw => (seg_facts hc hz hx hw).2.2) ha hb
    rw [hd, add_sub_cancel_left] at this
    exact this

/-- `|x/(2S(S + 2c))| ≤ 1/(2x)` for real `x > 0`. -/
theorem norm_corr_le (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) / (2 * Sq c x * (Sq c x + 2 * c))‖ ≤ 1 / (2 * x) := by
  have hS : Sq c (x : ℂ) = ((Real.sqrt (x ^ 2 + 4 * c ^ 2) : ℝ) : ℂ) := by
    unfold Sq
    rw [show (x : ℂ) ^ 2 + 4 * (c : ℂ) ^ 2 = ((x ^ 2 + 4 * c ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact Cvs.Upstream.ComplexArsinhStrip.csqrt_ofReal (by positivity)
  have hσ : x ≤ Real.sqrt (x ^ 2 + 4 * c ^ 2) := by
    rw [Real.le_sqrt hx.le (by positivity)]; nlinarith
  rw [hS]
  have e : (x : ℂ) / (2 * ((Real.sqrt (x ^ 2 + 4 * c ^ 2) : ℝ) : ℂ) * (((Real.sqrt (x ^ 2 + 4 * c ^ 2) : ℝ) : ℂ) + 2 * c))
      = ((x / (2 * Real.sqrt (x ^ 2 + 4 * c ^ 2) * (Real.sqrt (x ^ 2 + 4 * c ^ 2) + 2 * c)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : x * x ≤ Real.sqrt (x ^ 2 + 4 * c ^ 2) * (Real.sqrt (x ^ 2 + 4 * c ^ 2) + 2 * c) := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 4 * c ^ 2)]
  nlinarith

end Cvs.Prolate.Mellin.WkbPhaseVerticalFar
