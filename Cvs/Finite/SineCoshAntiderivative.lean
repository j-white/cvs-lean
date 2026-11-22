import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The sine-against-cosh integral, by antiderivative

`∫ sin(ax/L + b) cosh x` has an elementary antiderivative whenever `b² + (a/L)² ≠ 0`, which is
what turns the pole term into a closed form rather than a quadrature.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real intervalIntegral

namespace Cvs.Finite.SineCoshAntiderivative

/-- The two forms of the denominator agree, off `L = 0`. -/
theorem den_ne_zero {L a b : ℝ} (hL : L ≠ 0) (hd : b ^ 2 + (a / L) ^ 2 ≠ 0) :
    b ^ 2 * L ^ 2 + a ^ 2 ≠ 0 := by
  intro h
  apply hd
  have : b ^ 2 + (a / L) ^ 2 = (b ^ 2 * L ^ 2 + a ^ 2) / L ^ 2 := by field_simp
  rw [this, h, zero_div]

/-- The antiderivative of `sin(a(1 − y/L))·cosh(by)`. -/
def psiAntideriv (L a b y : ℝ) : ℝ :=
  (b * Real.sin (a * (1 - y / L)) * Real.sinh (b * y)
      + (a / L) * Real.cos (a * (1 - y / L)) * Real.cosh (b * y))
    / (b ^ 2 + (a / L) ^ 2)

/-- **It is one.** -/
theorem hasDerivAt_psiAntideriv {L a b : ℝ} (hL : L ≠ 0) (hd : b ^ 2 + (a / L) ^ 2 ≠ 0)
    (y : ℝ) :
    HasDerivAt (psiAntideriv L a b) (Real.sin (a * (1 - y / L)) * Real.cosh (b * y)) y := by
  have hu : HasDerivAt (fun z : ℝ => a * (1 - z / L)) (-(a / L)) y := by
    have h0 : HasDerivAt (fun z : ℝ => z / L) (1 / L) y := (hasDerivAt_id y).div_const L
    have h1 : HasDerivAt (fun z : ℝ => 1 - z / L) (-(1 / L)) y := h0.const_sub 1
    have h2 := h1.const_mul a
    exact h2.congr_deriv (by field_simp)
  have hby : HasDerivAt (fun z : ℝ => b * z) b y := by
    simpa using (hasDerivAt_id y).const_mul b
  have hs : HasDerivAt (fun z : ℝ => Real.sin (a * (1 - z / L)))
      (Real.cos (a * (1 - y / L)) * -(a / L)) y := hu.sin
  have hc : HasDerivAt (fun z : ℝ => Real.cos (a * (1 - z / L)))
      (-Real.sin (a * (1 - y / L)) * -(a / L)) y := hu.cos
  have hsh : HasDerivAt (fun z : ℝ => Real.sinh (b * z)) (Real.cosh (b * y) * b) y := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sinh (b * y)).comp y hby
  have hch : HasDerivAt (fun z : ℝ => Real.cosh (b * z)) (Real.sinh (b * y) * b) y := by
    simpa [Function.comp_def] using (Real.hasDerivAt_cosh (b * y)).comp y hby
  have hnum := (((hs.const_mul b).mul hsh).add (((hc.const_mul (a / L)).mul hch)))
  have hfin := hnum.div_const (b ^ 2 + (a / L) ^ 2)
  have hden2 := den_ne_zero hL hd
  refine hfin.congr_deriv ?_
  field_simp
  ring

/-- **The integral, in closed form.**  `ψ`'s building block, with `b` free. -/
theorem integral_sin_affine_cosh {L a b : ℝ} (hL : L ≠ 0) (hd : b ^ 2 + (a / L) ^ 2 ≠ 0) :
    (∫ y in (0:ℝ)..L, Real.sin (a * (1 - y / L)) * Real.cosh (b * y))
      = a * L * (Real.cosh (b * L) - Real.cos a) / (a ^ 2 + (b * L) ^ 2) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := psiAntideriv L a b)
    (f' := fun y => Real.sin (a * (1 - y / L)) * Real.cosh (b * y))
    (fun y _ => hasDerivAt_psiAntideriv hL hd y)
    (Continuous.intervalIntegrable (by fun_prop) 0 L)
  rw [hFTC, psiAntideriv, psiAntideriv]
  have hLL : L / L = 1 := div_self hL
  rw [hLL]
  simp only [sub_self, mul_zero, Real.sin_zero, Real.cos_zero, zero_div, Real.sinh_zero,
    Real.cosh_zero, mul_one, mul_zero, zero_mul, zero_add, sub_zero]
  have hden2 := den_ne_zero hL hd
  have hden : a ^ 2 + (b * L) ^ 2 ≠ 0 := by
    intro h; apply hden2; nlinarith [h]
  field_simp
  ring

/-! ### The pole part of `𝒟`, and its `ψ` -/

-- The whole matrix of the pole part is the divided difference of this one function.
/-- **CvS's `ψ` for the pole kernel `2cosh(y/2)`**, in closed form:
`ψ_pole(x) = 4·L·x·(cosh(L/2) − cos 2πx) / ((2πx)² + (L/2)²)`. -/
theorem psi_pole {L : ℝ} (hL : L ≠ 0) (x : ℝ) :
    (2 / Real.pi) * (∫ y in (0:ℝ)..L,
        Real.sin (2 * Real.pi * x * (1 - y / L)) * Real.cosh (y / 2))
      = 4 * L * x * (Real.cosh (L / 2) - Real.cos (2 * Real.pi * x))
          / ((2 * Real.pi * x) ^ 2 + (L / 2) ^ 2) := by
  have hb : ∀ y : ℝ, Real.cosh (y / 2) = Real.cosh ((1 / 2 : ℝ) * y) := by
    intro y; congr 1; ring
  have hd : (1 / 2 : ℝ) ^ 2 + (2 * Real.pi * x / L) ^ 2 ≠ 0 := by positivity
  rw [intervalIntegral.integral_congr (g := fun y =>
      Real.sin (2 * Real.pi * x * (1 - y / L)) * Real.cosh ((1 / 2 : ℝ) * y))
    (fun y _ => by rw [hb y])]
  rw [integral_sin_affine_cosh hL hd]
  have hhalf : (1 / 2 : ℝ) * L = L / 2 := by ring
  rw [hhalf]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : (2 * Real.pi * x) ^ 2 + (L / 2) ^ 2 ≠ 0 := by
    intro h
    apply hd
    have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
    field_simp at h ⊢
    nlinarith [h, sq_nonneg (2 * Real.pi * x), sq_nonneg L]
  field_simp
  ring

end Cvs.Finite.SineCoshAntiderivative
