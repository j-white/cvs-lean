import Mathlib
import Cvs.Zeta.ContourShift
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.GuinandWeilFourier

/-!
# `φ̂ = e^{3t/2}·ĥ` — the exponent dictionary, completed

`Cvs.Zeta.CriticalParam` showed that this development's prime side, `Σ Λ(n)·n^{−2}·φ̂(log n)`,
becomes the classical `Σ Λ(n)·n^{−1/2}·ĥ(log n)` provided the transform's contour can be moved
from `Im = −3/2` to the real axis.
-/

open Complex

namespace Cvs.Zeta

/-- `‖e^{−iwt}‖ = e^{Im w · t}`, bounded on the strip by `max 1 e^{−at}`. -/
theorem norm_exp_strip {t a : ℝ} {w : ℂ} (h1 : -a ≤ w.im) (h2 : w.im ≤ 0) :
    ‖Complex.exp (-(w * (t : ℂ)) * I)‖ ≤ max 1 (Real.exp (-a * t)) := by
  rw [Complex.norm_exp]
  have hre : (-(w * (t : ℂ)) * I).re = w.im * t := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  rcases le_or_gt 0 t with ht | ht
  · refine le_trans (Real.exp_le_one_iff.mpr ?_) (le_max_left _ _)
    exact mul_nonpos_of_nonpos_of_nonneg h2 ht
  · refine le_trans (Real.exp_le_exp.mpr ?_) (le_max_right _ _)
    nlinarith

/-- **The transform shift.**  Moving the contour of `∫ e^{−ixt} h(x − ia) dx` to the real
axis costs the factor `e^{−at}` that the exponential picks up. -/
theorem fourier_shift {h : ℂ → ℂ} {B a t : ℝ} (hh : Differentiable ℂ h) (ha : 0 ≤ a)
    (hB : 0 ≤ B) (hd : StripDecayRe h B a) :
    (∫ x : ℝ, Complex.exp (-(((x : ℂ) - a * I) * (t : ℂ)) * I) * h ((x : ℂ) - a * I))
      = ∫ x : ℝ, Complex.exp (-((x : ℂ) * (t : ℂ)) * I) * h (x : ℂ) := by
  have hmax : (0 : ℝ) ≤ max 1 (Real.exp (-a * t)) := le_trans zero_le_one (le_max_left _ _)
  refine contour_shift (f := fun w => Complex.exp (-(w * (t : ℂ)) * I) * h w)
    (B := max 1 (Real.exp (-a * t)) * B)
    ((by fun_prop : Differentiable ℂ fun w : ℂ => Complex.exp (-(w * (t : ℂ)) * I)).mul hh)
    ha (by positivity) ?_
  intro w h1 h2
  rw [norm_mul]
  have hb := hd w h1 h2
  calc ‖Complex.exp (-(w * (t : ℂ)) * I)‖ * ‖h w‖
      ≤ max 1 (Real.exp (-a * t)) * (B / (1 + |w.re|) ^ 2) :=
        mul_le_mul (norm_exp_strip h1 h2) hb (norm_nonneg _) hmax
    _ = max 1 (Real.exp (-a * t)) * B / (1 + |w.re|) ^ 2 := by ring

/-- `ofCritical h` on the line `Re s = 2` is `h` shifted down by `3i/2`. -/
theorem ofCritical_vline (h : ℂ → ℂ) (y : ℝ) :
    ofCritical h ((2 : ℂ) + y * I) = h ((y : ℂ) - (3 / 2 : ℝ) * I) := by
  unfold ofCritical
  congr 1
  push_cast
  linear_combination (-(y : ℂ)) * Complex.I_sq

/-- The transform of `h` along the real axis — the classical `ĥ`. -/
noncomputable def fourierReal (h : ℂ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-((x : ℂ) * (t : ℂ)) * I) * h (x : ℂ)

/-- **`φ̂ = e^{3t/2}·ĥ`.**  The transform this development computes, along `Re s = 2`, is the
classical one along the real axis times `e^{3t/2}` — and at `t = log n` that factor is
`n^{3/2}`, which turns `n^{−2}` into `n^{−1/2}`. -/
theorem fourierVline_ofCritical {h : ℂ → ℂ} {B t : ℝ} (hh : Differentiable ℂ h)
    (hB : 0 ≤ B) (hd : StripDecayRe h B (3 / 2)) :
    fourierVline (ofCritical h) t
      = Complex.exp (((3 / 2 : ℝ) * t : ℝ)) * fourierReal h t := by
  have hshift := fourier_shift (h := h) (a := 3 / 2) (t := t) hh (by norm_num) hB hd
  have hpt : ∀ x : ℝ,
      Complex.exp (-(((x : ℂ) - (3 / 2 : ℝ) * I) * (t : ℂ)) * I)
          * h ((x : ℂ) - (3 / 2 : ℝ) * I)
        = Complex.exp ((-(3 / 2 : ℝ) * t : ℝ))
          * (Complex.exp (-((x : ℂ) * (t : ℂ)) * I) * h ((x : ℂ) - (3 / 2 : ℝ) * I)) := by
    intro x
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    linear_combination ((3 : ℂ) / 2 * (t : ℂ)) * Complex.I_sq
  simp_rw [hpt] at hshift
  rw [MeasureTheory.integral_const_mul] at hshift
  have hfv : fourierVline (ofCritical h) t
      = ∫ x : ℝ, Complex.exp (-((x : ℂ) * (t : ℂ)) * I) * h ((x : ℂ) - (3 / 2 : ℝ) * I) := by
    unfold fourierVline
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun y => by simp only; rw [ofCritical_vline])
  rw [hfv, fourierReal, ← hshift, ← mul_assoc, ← Complex.exp_add]
  norm_num

end Cvs.Zeta
