import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
The winding integral of a rectangle.

`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` gives
Cauchy–Goursat for rectangles, so the *holomorphic* part of `f'/f` contributes
nothing on a rectangular contour, exactly as on a circle.  What Mathlib does
**not** have is a rectangular Cauchy *formula* — nothing carrying the `1/(z−w)`
kernel; `integral_sub_center_inv` and `integral_sub_inv_of_mem_ball` are circles
only.

So `∮_∂R dz/(z−ρ) = 2πi` is the one piece that cannot be transported from the
circle.  A conformal disc-to-rectangle map is Schwarz–Christoffel (absent, and
not elementary); homotopy invariance of contour integrals is absent; and the
primitive device used for the Newman deformation cannot apply, because
`1/(z−ρ)` has *no* primitive on any region encircling `ρ` — which is precisely
why the answer is `2πi` rather than `0`.

It has to be computed side by side.  Three of the four are routine: their paths
keep either the imaginary part or the real part of `ζ − ρ` away from zero, so
`log` is an antiderivative.  The fourth — the vertical side *left* of `ρ` —
crosses the branch cut, and `log(−·)` serves instead.  That is the same device
`Cvs.Zeta.WindingD` uses for the `D`-contour's closing chord.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex

/-- A horizontal side: `∫ dx/(x + bi − ρ) = log-difference`, valid because the
path has constant imaginary part `b − ρ.im ≠ 0`, hence never meets the cut. -/
theorem integral_horiz_inv {p q b : ℝ} {ρ : ℂ} (hb : b ≠ ρ.im) :
    (∫ x : ℝ in p..q, ((x : ℂ) + b * I - ρ)⁻¹)
      = Complex.log ((q : ℂ) + b * I - ρ) - Complex.log ((p : ℂ) + b * I - ρ) := by
  have hmem : ∀ x : ℝ, ((x : ℂ) + b * I - ρ) ∈ Complex.slitPlane := by
    intro x
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.ofReal_im]
    simpa using sub_ne_zero.mpr hb
  have hd : ∀ x ∈ Set.uIcc p q,
      HasDerivAt (fun t : ℝ => Complex.log ((t : ℂ) + b * I - ρ))
        (((x : ℂ) + b * I - ρ)⁻¹) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ) + b * I - ρ)) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const (b * I - ρ)
    simpa using h1.clog_real (hmem x)
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt hd ?_
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.inv₀ ?_ (fun x _ => Complex.slitPlane_ne_zero (hmem x))
  fun_prop

/-- A vertical side to the **right** of `ρ`: the path stays in the right
half-plane, so `log` itself is the antiderivative. -/
theorem integral_vert_inv_right {p q a : ℝ} {ρ : ℂ} (ha : ρ.re < a) :
    (∫ y : ℝ in p..q, ((a : ℂ) + y * I - ρ)⁻¹)
      = -I * (Complex.log ((a : ℂ) + q * I - ρ) - Complex.log ((a : ℂ) + p * I - ρ)) := by
  have hmem : ∀ y : ℝ, ((a : ℂ) + y * I - ρ) ∈ Complex.slitPlane := by
    intro y
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    simpa using sub_pos.mpr ha
  have hd : ∀ y ∈ Set.uIcc p q,
      HasDerivAt (fun t : ℝ => -I * Complex.log ((a : ℂ) + t * I - ρ))
        (((a : ℂ) + y * I - ρ)⁻¹) y := by
    intro y _
    have h1 : HasDerivAt (fun t : ℝ => ((a : ℂ) + t * I - ρ)) I y := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add
        ((a : ℂ))).sub_const ρ
    have h2 := (h1.clog_real (hmem y)).const_mul (-I)
    refine h2.congr_deriv ?_
    simp [div_eq_mul_inv, ← mul_assoc, Complex.I_mul_I]
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt hd ?_).trans (by ring)
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.inv₀ ?_ (fun y _ => Complex.slitPlane_ne_zero (hmem y))
  fun_prop

/-- A vertical side to the **left** of `ρ`: the path crosses the branch cut, so
`log(−·)` is the antiderivative instead — the same device `WindingD` uses. -/
theorem integral_vert_inv_left {p q a : ℝ} {ρ : ℂ} (ha : a < ρ.re) :
    (∫ y : ℝ in p..q, ((a : ℂ) + y * I - ρ)⁻¹)
      = -I * (Complex.log (-((a : ℂ) + q * I - ρ))
        - Complex.log (-((a : ℂ) + p * I - ρ))) := by
  have hmem : ∀ y : ℝ, (-((a : ℂ) + y * I - ρ)) ∈ Complex.slitPlane := by
    intro y
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    simpa using sub_pos.mpr ha
  have hne : ∀ y : ℝ, ((a : ℂ) + y * I - ρ) ≠ 0 := by
    intro y hcon
    exact Complex.slitPlane_ne_zero (hmem y) (by rw [hcon, neg_zero])
  have hd : ∀ y ∈ Set.uIcc p q,
      HasDerivAt (fun t : ℝ => -I * Complex.log (-((a : ℂ) + t * I - ρ)))
        (((a : ℂ) + y * I - ρ)⁻¹) y := by
    intro y _
    have h1 : HasDerivAt (fun t : ℝ => -((a : ℂ) + t * I - ρ)) (-I) y := by
      have h0 : (fun t : ℝ => -((a : ℂ) + t * I - ρ))
          = fun t : ℝ => (ρ - (a : ℂ)) - t * I := by funext t; ring
      rw [h0]
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_sub (ρ - (a : ℂ))
    have h2 := (h1.clog_real (hmem y)).const_mul (-I)
    refine h2.congr_deriv ?_
    simp [div_eq_mul_inv, ← mul_assoc, Complex.I_mul_I, neg_inv]
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt hd ?_).trans (by ring)
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.inv₀ ?_ (fun y _ => hne y)
  fun_prop

/-!
### The winding number

Summing the four sides.
-/

/-- **The branch jump, lower half-plane.**  Passing from `u` to `−u` across the
cut costs exactly `+πi`. -/
theorem log_neg_sub_log_of_im_neg {u : ℂ} (hu : u.im < 0) :
    Complex.log (-u) - Complex.log u = (Real.pi : ℂ) * I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hu]
  push_cast; ring

/-- **The branch jump, upper half-plane** — the opposite sign. -/
theorem log_neg_sub_log_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    Complex.log (-u) - Complex.log u = -((Real.pi : ℂ) * I) := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hu]
  push_cast; ring

/-- The boundary integral of a rectangle, in Mathlib's orientation. -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + z.im * I))
    - (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + w.im * I))
    + I * (∫ y : ℝ in z.im..w.im, f ((w.re : ℂ) + y * I))
    - I * (∫ y : ℝ in z.im..w.im, f ((z.re : ℂ) + y * I))

/-- **The winding integral of a rectangle.** Three of the four sides cancel in pairs; what
survives is the branch jump at the two corners on the *left* edge — `+πi` at the bottom-left
(lower half-plane) and `−πi` at the top-left — and those combine to `2πi`. -/
theorem rectBoundaryIntegral_inv_eq {z w ρ : ℂ}
    (hre1 : z.re < ρ.re) (hre2 : ρ.re < w.re)
    (him1 : z.im < ρ.im) (him2 : ρ.im < w.im) :
    rectBoundaryIntegral (fun u => (u - ρ)⁻¹) z w = 2 * (Real.pi : ℂ) * I := by
  have hA : ((z.re : ℂ) + (z.im : ℂ) * I - ρ).im < 0 := by simpa using him1
  have hD : 0 < ((z.re : ℂ) + (w.im : ℂ) * I - ρ).im := by simpa using him2
  have jA := log_neg_sub_log_of_im_neg hA
  have jD := log_neg_sub_log_of_im_pos hD
  rw [rectBoundaryIntegral,
    integral_horiz_inv (b := z.im) (ρ := ρ) (ne_of_lt him1),
    integral_horiz_inv (b := w.im) (ρ := ρ) (ne_of_gt him2),
    integral_vert_inv_right (a := w.re) (ρ := ρ) hre2,
    integral_vert_inv_left (a := z.re) (ρ := ρ) hre1]
  have hII : ∀ X : ℂ, I * (-I * X) = X := by
    intro X
    have hr : I * (-I * X) = -(I * I) * X := by ring
    rw [hr, Complex.I_mul_I]
    ring
  rw [hII, hII]
  linear_combination jA - jD

end Cvs.Zeta
