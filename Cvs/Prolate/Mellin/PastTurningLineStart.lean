import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis
import Cvs.Upstream.ComplexArsinhStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The start of the line past the turning point

`√·` is continuous from the closed upper half-plane at the negative reals, so `Ĝ(iz + η) → Ĝ(iz)` and `ĝ(iz + η) → ĝ(iz)`
as `η → 0⁺` when `z > 2c`. On `[iz + η, iz + 2]` with `z ≥ (2 + ε)c` and `εc² ≥ 2`, `|S| ≥ √ε c`, so
`|ĝ′| ≤ 13/(2ε^{3/2}c)`; Taylor there and the limit give `|Ĝ(iz + 2) − Ĝ(iz) − 2ĝ(iz)| ≤ 4M`, `|ĝ(iz + 2) − ĝ(iz)| ≤ 2M`.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Prolate.Mellin.PastTurningLineStart

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg)
open Cvs.Upstream.ComplexArsinhStrip (ash)
open Cvs.Prolate.Mellin.WkbPhaseAntiderivative (Sq Sq_sq Gh gh gh1)

/-- `√·` is continuous from `{Im ≥ 0}` at a negative real. -/
theorem continuousWithinAt_csqrt {x : ℂ} (hre : x.re < 0) (him : x.im = 0) :
    ContinuousWithinAt csqrt {w : ℂ | 0 ≤ w.im} x := by
  have hx0 : x ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hlog := continuousWithinAt_log_of_re_neg_of_im_zero hre him
  have hexp : ContinuousWithinAt (fun w => Complex.exp (Complex.log w * 2⁻¹)) {w : ℂ | 0 ≤ w.im} x :=
    Complex.continuous_exp.continuousAt.comp_continuousWithinAt (hlog.mul continuousWithinAt_const)
  refine hexp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hx0)] with w hw
    unfold csqrt; rw [cpow_def_of_ne_zero hw]
  · unfold csqrt; rw [cpow_def_of_ne_zero hx0]

/-- A path `η ↦ f(η)` into `{Im ≥ 0}` tending to a negative real carries `√·` along. -/
theorem tendsto_csqrt_comp {f : ℝ → ℂ} {x : ℂ} (hre : x.re < 0) (him : x.im = 0)
    (hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 x)) (hfim : ∀ η : ℝ, 0 < η → 0 ≤ (f η).im) :
    Tendsto (fun η => csqrt (f η)) (𝓝[>] (0 : ℝ)) (𝓝 (csqrt x)) := by
  have hc := (continuousWithinAt_csqrt hre him).tendsto
  refine hc.comp (tendsto_nhdsWithin_iff.mpr ⟨hf, ?_⟩)
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact hfim η hη

variable {c z : ℝ}

/-- **`S(iz + η) → S(iz)`.** -/
theorem tendsto_Sq (hc : 0 < c) (hz : 2 * c < z) :
    Tendsto (fun η : ℝ => Sq c (I * z + η)) (𝓝[>] (0 : ℝ)) (𝓝 (Sq c (I * z))) := by
  unfold Sq
  apply tendsto_csqrt_comp
  · simp [sq]; nlinarith
  · simp [sq]
  · have : Tendsto (fun η : ℝ => (I * (z : ℂ) + η) ^ 2 + 4 * (c : ℂ) ^ 2) (𝓝 (0 : ℝ))
        (𝓝 ((I * (z : ℂ) + ((0 : ℝ) : ℂ)) ^ 2 + 4 * (c : ℂ) ^ 2)) := by
      apply Continuous.tendsto; fun_prop
    simp only [Complex.ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · intro η hη
    have : ((I * (z : ℂ) + η) ^ 2 + 4 * (c : ℂ) ^ 2).im = 2 * η * z := by simp [sq]; ring
    rw [this]; have : 0 < z := by linarith
    positivity

/-- **`ash((iz + η)/2c) → ash(iz/2c)`.** -/
theorem tendsto_ash (hc : 0 < c) (hz : 2 * c < z) :
    Tendsto (fun η : ℝ => ash ((I * z + η) / (2 * c))) (𝓝[>] (0 : ℝ)) (𝓝 (ash (I * z / (2 * c)))) := by
  have hw : 1 < z / (2 * c) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have ht : Tendsto (fun η : ℝ => (I * (z : ℂ) + η) / (2 * c)) (𝓝[>] (0 : ℝ)) (𝓝 (I * z / (2 * c))) := by
    have : Tendsto (fun η : ℝ => (I * (z : ℂ) + η) / (2 * c)) (𝓝 (0 : ℝ))
        (𝓝 ((I * (z : ℂ) + ((0 : ℝ) : ℂ)) / (2 * c))) := by
      apply Continuous.tendsto; fun_prop
    simp only [Complex.ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  set w := z / (2 * c) with hwd
  have hwC : I * (z : ℂ) / (2 * c) = I * (w : ℂ) := by rw [hwd]; push_cast; ring
  have hre : ((I * (z : ℂ) / (2 * c)) ^ 2 + 1).re < 0 := by
    rw [hwC, mul_pow, I_sq]
    have : (-1 * (w : ℂ) ^ 2 + 1).re = 1 - w ^ 2 := by simp [sq]; ring
    rw [this]; nlinarith
  have him : ((I * (z : ℂ) / (2 * c)) ^ 2 + 1).im = 0 := by
    rw [hwC, mul_pow, I_sq]; simp [sq]
  have hsq := tendsto_csqrt_comp hre him ((ht.pow 2).add_const 1) (fun η hη => by
    have e : (I * (z : ℂ) + η) / (2 * c) = (((η / (2 * c)) : ℝ) : ℂ) + I * (w : ℂ) := by
      rw [hwd]; push_cast; ring
    rw [e]
    have : ((((η / (2 * c)) : ℝ) : ℂ) + I * (w : ℂ)) ^ 2 + 1 = ((((η / (2 * c)) ^ 2 - w ^ 2 + 1) : ℝ) : ℂ)
        + I * ((2 * (η / (2 * c)) * w : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [this]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      zero_mul, one_mul, zero_add]
    have h1 : 0 < η / (2 * c) := div_pos hη (by positivity)
    have h2 : 0 < w := by linarith
    have := mul_pos (mul_pos two_pos h1) h2
    linarith)
  have hsum := ht.add hsq
  -- the limit point is in the slit plane
  have hmem : I * (z : ℂ) / (2 * c) + csqrt ((I * (z : ℂ) / (2 * c)) ^ 2 + 1) ∈ slitPlane := by
    rw [show I * (z : ℂ) / (2 * c) = I * ((z / (2 * c) : ℝ) : ℂ) by push_cast; ring]
    have hs : 0 ≤ (z / (2 * c)) ^ 2 - 1 := by nlinarith
    have hsC : ((Real.sqrt ((z / (2 * c)) ^ 2 - 1) : ℝ) : ℂ) ^ 2 = ((z / (2 * c) : ℝ) : ℂ) ^ 2 - 1 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hs]; push_cast; ring
    have e1 : (I * ((z / (2 * c) : ℝ) : ℂ)) ^ 2 + 1 = -(((Real.sqrt ((z / (2 * c)) ^ 2 - 1) : ℝ) : ℂ) ^ 2) := by
      rw [mul_pow, I_sq, hsC]; ring
    rw [e1, Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis.csqrt_neg_sq (Real.sqrt_nonneg _), mem_slitPlane_iff]
    right
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, zero_add]
    have := Real.sqrt_nonneg ((z / (2 * c)) ^ 2 - 1)
    have h2 : 0 < z / (2 * c) := by linarith
    intro h0; linarith
  have hlog := (continuousAt_clog hmem).tendsto.comp hsum
  exact hlog

end Cvs.Prolate.Mellin.PastTurningLineStart
