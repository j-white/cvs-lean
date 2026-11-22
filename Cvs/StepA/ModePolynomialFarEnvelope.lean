import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.ModeTruncationBound
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.SectorBottomsLowerBound
import Cvs.StepA.SectorGramBoxTransform
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.OddPoleTermBound
import Cvs.Zeta.ExplicitFormula.ExpCosIntegral
import Cvs.Zeta.ExplicitFormula.RemainderPieceBounds
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.QuadraticWeightSummable
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The far envelope of a mode polynomial at a complex point

For `z = x + iy` and real `ω`, `|∫_{−L/2}^{L/2} cos(ωt + φ) ve_z| ≤ cosh(yL/2)(1/‖z + ω‖ + 1/‖z − ω‖)`,
likewise `uo_z`; so `2|ω| ≤ |x|` gives `4 cosh(yL/2)/|x|`, and `2·(2πN/L) ≤ |x|` gives
`(∫ cosPoly_ξ ve_z)² ≤ 16(2N+1)cosh²(yL/2)/x²·‖ξ‖²`. The envelopes `envE`, `envO` bound one zero's even
pairing below and odd pairing above by `envE·L‖ξ‖²`, `envO·L‖o‖²`, and are summable over the zeros.
-/

noncomputable section

open Real MeasureTheory Matrix

namespace Cvs.StepA.ModePolynomialFarEnvelope
open Cvs.ZeroCounting

open Cvs.Finite.TruncationZeroFreeOffAxes (omega)
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.StepA.OneZeroParitySectors (ue ve uo vo)

/-! ### One exponential against one sinusoid -/

/-- `|∫_a^b e^{yt} cos(βt + φ)| ≤ (e^{ya} + e^{yb})/√(y² + β²)` whenever `y² + β² ≠ 0`. -/
theorem abs_integral_exp_mul_cos_le_of_interval {y β : ℝ} (h : y ^ 2 + β ^ 2 ≠ 0) (φ a b : ℝ) :
    |∫ t in a..b, exp (y * t) * cos (β * t + φ)|
      ≤ (exp (y * a) + exp (y * b)) / √(y ^ 2 + β ^ 2) := by
  rw [Cvs.Moments.integral_exp_cos h φ a b, add_div]
  have h1 := Cvs.Enclosure.abs_expCosAnti_le h φ b
  have h2 := Cvs.Enclosure.abs_expCosAnti_le h φ a
  have h3 := abs_sub (Cvs.Moments.expCosAnti y β φ b) (Cvs.Moments.expCosAnti y β φ a)
  linarith

/-- `|∫_a^b e^{yt} sin(βt + φ)| ≤ (e^{ya} + e^{yb})/√(y² + β²)` whenever `y² + β² ≠ 0`. -/
theorem abs_integral_exp_mul_sin_le_of_interval {y β : ℝ} (h : y ^ 2 + β ^ 2 ≠ 0) (φ a b : ℝ) :
    |∫ t in a..b, exp (y * t) * sin (β * t + φ)|
      ≤ (exp (y * a) + exp (y * b)) / √(y ^ 2 + β ^ 2) := by
  have e : ∀ t, sin (β * t + φ) = cos (β * t + (φ - π / 2)) := fun t => by
    rw [← Real.cos_sub_pi_div_two]; congr 1; ring
  simp_rw [e]
  exact abs_integral_exp_mul_cos_le_of_interval h _ a b

/-- On a symmetric window, `|∫_{−a}^{a} e^{yt} sin(βt + φ)| ≤ 2 cosh(ya)/√(y² + β²)` whenever
`y² + β² ≠ 0`. -/
theorem abs_integral_exp_mul_sin_le_sqrt {y β : ℝ} (h : y ^ 2 + β ^ 2 ≠ 0) (φ a : ℝ) :
    |∫ t in -a..a, exp (y * t) * sin (β * t + φ)| ≤ 2 * cosh (y * a) / √(y ^ 2 + β ^ 2) := by
  have hc : 2 * cosh (y * a) = exp (y * -a) + exp (y * a) := by
    rw [Real.cosh_eq, mul_neg]; ring
  rw [hc]
  exact abs_integral_exp_mul_sin_le_of_interval h φ (-a) a

/-! ### One mode against one zero's sector weights -/

/-- With `y² + (x ± ω)² ≠ 0`, `|∫_{−a}^{a} cos(ωt + φ) sin(xt) e^{yt}|` is at most
`cosh(ya)(1/√(y² + (x + ω)²) + 1/√(y² + (x − ω)²))`. -/
theorem abs_integral_cos_mul_sin_mul_exp_le {x y ω : ℝ} (hP : y ^ 2 + (x + ω) ^ 2 ≠ 0)
    (hM : y ^ 2 + (x - ω) ^ 2 ≠ 0) (φ a : ℝ) :
    |∫ t in -a..a, cos (ω * t + φ) * (sin (x * t) * exp (y * t))|
      ≤ cosh (y * a) * (1 / √(y ^ 2 + (x + ω) ^ 2) + 1 / √(y ^ 2 + (x - ω) ^ 2)) := by
  have hpt : ∀ t, cos (ω * t + φ) * (sin (x * t) * exp (y * t))
      = (exp (y * t) * sin ((x + ω) * t + φ) + exp (y * t) * sin ((x - ω) * t + -φ)) / 2 := by
    intro t
    rw [show (x + ω) * t + φ = x * t + (ω * t + φ) by ring,
      show (x - ω) * t + -φ = x * t - (ω * t + φ) by ring, Real.sin_add, Real.sin_sub]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun t => exp (y * t) * sin ((x + ω) * t + φ)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => exp (y * t) * sin ((x - ω) * t + -φ)).intervalIntegrable _ _)]
  have b1 := abs_integral_exp_mul_sin_le_sqrt hP φ a
  have b2 := abs_integral_exp_mul_sin_le_sqrt hM (-φ) a
  have h3 := abs_add_le (∫ t in -a..a, exp (y * t) * sin ((x + ω) * t + φ))
    (∫ t in -a..a, exp (y * t) * sin ((x - ω) * t + -φ))
  have hr : cosh (y * a) * (1 / √(y ^ 2 + (x + ω) ^ 2) + 1 / √(y ^ 2 + (x - ω) ^ 2))
      = (2 * cosh (y * a) / √(y ^ 2 + (x + ω) ^ 2) + 2 * cosh (y * a) / √(y ^ 2 + (x - ω) ^ 2))
        / 2 := by ring
  rw [abs_div, abs_two, hr]
  linarith

/-- `‖z + ω‖ = √((Im z)² + (Re z + ω)²)` for real `ω`. -/
theorem norm_add_ofReal (z : ℂ) (ω : ℝ) : ‖z + ω‖ = √(z.im ^ 2 + (z.re + ω) ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
  ring

/-- `‖z − ω‖ = √((Im z)² + (Re z − ω)²)` for real `ω`. -/
theorem norm_sub_ofReal (z : ℂ) (ω : ℝ) : ‖z - ω‖ = √(z.im ^ 2 + (z.re - ω) ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  ring

/-- **One mode against `ve_z`**: for every `z`, real `ω` and phase `φ`,
`|∫_{−L/2}^{L/2} cos(ωt + φ) ve_z| ≤ cosh(Im z·L/2)(1/‖z + ω‖ + 1/‖z − ω‖)`. -/
theorem abs_integral_cos_mul_ve_le_norm (L ω φ : ℝ) (z : ℂ) :
    |∫ t in -(L / 2)..L / 2, cos (ω * t + φ) * ve z t|
      ≤ cosh (z.im * L / 2) * (1 / ‖z + ω‖ + 1 / ‖z - ω‖) := by
  rcases eq_or_ne z.im 0 with hy | hy
  · simp only [Cvs.StepA.OneZeroParitySectors.ve_eq_zero (Or.inr hy), mul_zero,
      intervalIntegral.integral_zero, abs_zero]
    positivity
  have hP : z.im ^ 2 + (z.re + ω) ^ 2 ≠ 0 := by positivity
  have hM : z.im ^ 2 + (z.re - ω) ^ 2 ≠ 0 := by positivity
  have hP' : (-z.im) ^ 2 + (z.re + ω) ^ 2 ≠ 0 := by rwa [neg_sq]
  have hM' : (-z.im) ^ 2 + (z.re - ω) ^ 2 ≠ 0 := by rwa [neg_sq]
  have hpt : ∀ t, cos (ω * t + φ) * ve z t
      = (cos (ω * t + φ) * (sin (z.re * t) * exp (z.im * t))
        - cos (ω * t + φ) * (sin (z.re * t) * exp (-z.im * t))) / 2 := by
    intro t
    rw [Cvs.StepA.OneZeroParitySectors.ve, Real.sinh_eq, neg_mul]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun t =>
      cos (ω * t + φ) * (sin (z.re * t) * exp (z.im * t))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t =>
      cos (ω * t + φ) * (sin (z.re * t) * exp (-z.im * t))).intervalIntegrable _ _)]
  have b1 := abs_integral_cos_mul_sin_mul_exp_le hP hM φ (L / 2)
  have b2 := abs_integral_cos_mul_sin_mul_exp_le hP' hM' φ (L / 2)
  have hc : cosh (-z.im * (L / 2)) = cosh (z.im * (L / 2)) := by rw [neg_mul, Real.cosh_neg]
  rw [neg_sq, hc] at b2
  have h3 := abs_sub (∫ t in -(L / 2)..L / 2, cos (ω * t + φ) * (sin (z.re * t) * exp (z.im * t)))
    (∫ t in -(L / 2)..L / 2, cos (ω * t + φ) * (sin (z.re * t) * exp (-z.im * t)))
  rw [norm_add_ofReal, norm_sub_ofReal, show z.im * L / 2 = z.im * (L / 2) by ring, abs_div,
    abs_two]
  linarith

/-- **One mode against `uo_z`**: for `z ≠ ±ω` and every phase `φ`,
`|∫_{−L/2}^{L/2} cos(ωt + φ) uo_z| ≤ cosh(Im z·L/2)(1/‖z + ω‖ + 1/‖z − ω‖)`. -/
theorem abs_integral_cos_mul_uo_le_norm (L ω φ : ℝ) {z : ℂ} (hP : z + ω ≠ 0) (hM : z - ω ≠ 0) :
    |∫ t in -(L / 2)..L / 2, cos (ω * t + φ) * uo z t|
      ≤ cosh (z.im * L / 2) * (1 / ‖z + ω‖ + 1 / ‖z - ω‖) := by
  have hnP : z.im ^ 2 + (z.re + ω) ^ 2 ≠ 0 := fun h0 =>
    norm_ne_zero_iff.mpr hP (by rw [norm_add_ofReal, h0, Real.sqrt_zero])
  have hnM : z.im ^ 2 + (z.re - ω) ^ 2 ≠ 0 := fun h0 =>
    norm_ne_zero_iff.mpr hM (by rw [norm_sub_ofReal, h0, Real.sqrt_zero])
  have hnP' : (-z.im) ^ 2 + (z.re + ω) ^ 2 ≠ 0 := by rwa [neg_sq]
  have hnM' : (-z.im) ^ 2 + (z.re - ω) ^ 2 ≠ 0 := by rwa [neg_sq]
  have hpt : ∀ t, cos (ω * t + φ) * uo z t
      = (cos (ω * t + φ) * (sin (z.re * t) * exp (z.im * t))
        + cos (ω * t + φ) * (sin (z.re * t) * exp (-z.im * t))) / 2 := by
    intro t
    rw [Cvs.StepA.OneZeroParitySectors.uo, Real.cosh_eq, neg_mul]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun t =>
      cos (ω * t + φ) * (sin (z.re * t) * exp (z.im * t))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t =>
      cos (ω * t + φ) * (sin (z.re * t) * exp (-z.im * t))).intervalIntegrable _ _)]
  have b1 := abs_integral_cos_mul_sin_mul_exp_le hnP hnM φ (L / 2)
  have b2 := abs_integral_cos_mul_sin_mul_exp_le hnP' hnM' φ (L / 2)
  have hc : cosh (-z.im * (L / 2)) = cosh (z.im * (L / 2)) := by rw [neg_mul, Real.cosh_neg]
  rw [neg_sq, hc] at b2
  have h3 := abs_add_le
    (∫ t in -(L / 2)..L / 2, cos (ω * t + φ) * (sin (z.re * t) * exp (z.im * t)))
    (∫ t in -(L / 2)..L / 2, cos (ω * t + φ) * (sin (z.re * t) * exp (-z.im * t)))
  rw [norm_add_ofReal, norm_sub_ofReal, show z.im * L / 2 = z.im * (L / 2) by ring, abs_div,
    abs_two]
  linarith

/-- **One sine mode against `uo_z`**: for `z ≠ ±ω` and every phase `φ`,
`|∫_{−L/2}^{L/2} sin(ωt + φ) uo_z| ≤ cosh(Im z·L/2)(1/‖z + ω‖ + 1/‖z − ω‖)`. -/
theorem abs_integral_sin_mul_uo_le_norm (L ω φ : ℝ) {z : ℂ} (hP : z + ω ≠ 0) (hM : z - ω ≠ 0) :
    |∫ t in -(L / 2)..L / 2, sin (ω * t + φ) * uo z t|
      ≤ cosh (z.im * L / 2) * (1 / ‖z + ω‖ + 1 / ‖z - ω‖) := by
  have e : ∀ t, sin (ω * t + φ) = cos (ω * t + (φ - π / 2)) := fun t => by
    rw [← Real.cos_sub_pi_div_two]; congr 1; ring
  simp_rw [e]
  exact abs_integral_cos_mul_uo_le_norm L ω _ hP hM

/-- If `2|ω| ≤ |Re z|` then `|Re z|/2 ≤ ‖z + ω‖` and `|Re z|/2 ≤ ‖z − ω‖`. -/
theorem half_abs_re_le_norm {z : ℂ} {ω : ℝ} (h : 2 * |ω| ≤ |z.re|) :
    |z.re| / 2 ≤ ‖z + ω‖ ∧ |z.re| / 2 ≤ ‖z - ω‖ := by
  have rP := Complex.abs_re_le_norm (z + ω)
  have rM := Complex.abs_re_le_norm (z - ω)
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at rP rM
  have tP := abs_add_le (z.re + ω) (-ω)
  have tM := abs_add_le (z.re - ω) ω
  rw [add_neg_cancel_right, abs_neg] at tP
  rw [sub_add_cancel] at tM
  constructor <;> linarith

/-- If `Re z ≠ 0` and `2|ω| ≤ |Re z|` then `1/‖z + ω‖ + 1/‖z − ω‖ ≤ 4/|Re z|`. -/
theorem inv_norm_add_inv_norm_le {z : ℂ} {ω : ℝ} (hx : z.re ≠ 0) (h : 2 * |ω| ≤ |z.re|) :
    1 / ‖z + ω‖ + 1 / ‖z - ω‖ ≤ 4 / |z.re| := by
  have hx' : 0 < |z.re| / 2 := by positivity
  obtain ⟨nP, nM⟩ := half_abs_re_le_norm h
  have iP := one_div_le_one_div_of_le hx' nP
  have iM := one_div_le_one_div_of_le hx' nM
  have e : 1 / (|z.re| / 2) + 1 / (|z.re| / 2) = 4 / |z.re| := by
    rw [one_div_div]; ring
  linarith

/-- **The far bound for one cosine mode against `ve_z`**: if `2|ω| ≤ |Re z|` then
`|∫_{−L/2}^{L/2} cos(ω(t + L/2)) ve_z| ≤ 4 cosh(Im z·L/2)/|Re z|`. -/
theorem abs_integral_cos_mul_ve_le (L ω : ℝ) (z : ℂ) (h : 2 * |ω| ≤ |z.re|) :
    |∫ t in -(L / 2)..L / 2, cos (ω * (t + L / 2)) * ve z t| ≤ 4 * cosh (z.im * L / 2) / |z.re| := by
  rcases eq_or_ne z.re 0 with hx | hx
  · simp only [Cvs.StepA.OneZeroParitySectors.ve_eq_zero (Or.inl hx), mul_zero,
      intervalIntegral.integral_zero, abs_zero, hx, div_zero, le_refl]
  have e : ∀ t, ω * (t + L / 2) = ω * t + ω * (L / 2) := fun t => by ring
  simp_rw [e]
  refine (abs_integral_cos_mul_ve_le_norm L ω (ω * (L / 2)) z).trans ?_
  calc cosh (z.im * L / 2) * (1 / ‖z + ω‖ + 1 / ‖z - ω‖)
      ≤ cosh (z.im * L / 2) * (4 / |z.re|) :=
        mul_le_mul_of_nonneg_left (inv_norm_add_inv_norm_le hx h) (Real.cosh_pos _).le
    _ = 4 * cosh (z.im * L / 2) / |z.re| := by ring

/-- **The far bound for one sine mode against `uo_z`**: if `2|ω| ≤ |Re z|` then
`|∫_{−L/2}^{L/2} sin(ω(t + L/2)) uo_z| ≤ 4 cosh(Im z·L/2)/|Re z|`. -/
theorem abs_integral_sin_mul_uo_le (L ω : ℝ) (z : ℂ) (h : 2 * |ω| ≤ |z.re|) :
    |∫ t in -(L / 2)..L / 2, sin (ω * (t + L / 2)) * uo z t| ≤ 4 * cosh (z.im * L / 2) / |z.re| := by
  rcases eq_or_ne z.re 0 with hx | hx
  · simp only [Cvs.StepA.OneZeroParitySectors.uo_eq_zero hx, mul_zero,
      intervalIntegral.integral_zero, abs_zero, hx, div_zero, le_refl]
  have hx' : 0 < |z.re| / 2 := by positivity
  obtain ⟨nP, nM⟩ := half_abs_re_le_norm h
  have hP : z + ω ≠ 0 := fun h0 => by rw [h0, norm_zero] at nP; linarith
  have hM : z - ω ≠ 0 := fun h0 => by rw [h0, norm_zero] at nM; linarith
  have e : ∀ t, ω * (t + L / 2) = ω * t + ω * (L / 2) := fun t => by ring
  simp_rw [e]
  refine (abs_integral_sin_mul_uo_le_norm L ω (ω * (L / 2)) hP hM).trans ?_
  calc cosh (z.im * L / 2) * (1 / ‖z + ω‖ + 1 / ‖z - ω‖)
      ≤ cosh (z.im * L / 2) * (4 / |z.re|) :=
        mul_le_mul_of_nonneg_left (inv_norm_add_inv_norm_le hx h) (Real.cosh_pos _).le
    _ = 4 * cosh (z.im * L / 2) / |z.re| := by ring

/-! ### A mode polynomial against one zero's sector weights -/

section Modes

variable {ι : Type*} [Fintype ι]

/-- **Cauchy–Schwarz over the modes**: for continuous `w`,
`(∫_{−L/2}^{L/2} cosPoly_ξ(t + L/2) w)² ≤ ‖ξ‖² ∑ᵢ (∫_{−L/2}^{L/2} cos(ωᵢ(t + L/2)) w)²`. -/
theorem sq_integral_cosPoly_mul_le (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) :
    (∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L mode ξ (t + L / 2) * w t) ^ 2
      ≤ (ξ ⬝ᵥ ξ) * ∑ i, (∫ t in -(L / 2)..L / 2, cos (omega L mode i * (t + L / 2)) * w t) ^ 2 := by
  have hpt : ∀ t, Cvs.Finite.EvenSectorZeroSide.cosPoly L mode ξ (t + L / 2) * w t
      = ∑ i, ξ i * (cos (omega L mode i * (t + L / 2)) * w t) := by
    intro t
    unfold Cvs.Finite.EvenSectorZeroSide.cosPoly
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun i _ => (by fun_prop : Continuous fun t =>
    ξ i * (cos (omega L mode i * (t + L / 2)) * w t)).intervalIntegrable _ _]
  simp_rw [intervalIntegral.integral_const_mul]
  simp only [dotProduct, ← sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **Cauchy–Schwarz over the modes**: for continuous `w`,
`(∫_{−L/2}^{L/2} sinePoly_o(t + L/2) w)² ≤ ‖o‖² ∑ᵢ (∫_{−L/2}^{L/2} sin(ωᵢ(t + L/2)) w)²`. -/
theorem sq_integral_sinePoly_mul_le (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) :
    (∫ t in -(L / 2)..L / 2, Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (t + L / 2) * w t) ^ 2
      ≤ (o ⬝ᵥ o) * ∑ i, (∫ t in -(L / 2)..L / 2, sin (omega L mode i * (t + L / 2)) * w t) ^ 2 := by
  have hpt : ∀ t, Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (t + L / 2) * w t
      = ∑ i, o i * (sin (omega L mode i * (t + L / 2)) * w t) := by
    intro t
    unfold Cvs.Finite.OddSectorZeroSide.sinePoly
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun i _ => (by fun_prop : Continuous fun t =>
    o i * (sin (omega L mode i * (t + L / 2)) * w t)).intervalIntegrable _ _]
  simp_rw [intervalIntegral.integral_const_mul]
  simp only [dotProduct, ← sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- A real whose absolute value is at most `4 cosh(Im z·L/2)/|Re z|` has square at most
`16 cosh²(Im z·L/2)/(Re z)²`. -/
theorem sq_le_of_abs_le_far {a L : ℝ} {z : ℂ} (h : |a| ≤ 4 * cosh (z.im * L / 2) / |z.re|) :
    a ^ 2 ≤ 16 * cosh (z.im * L / 2) ^ 2 / z.re ^ 2 := by
  calc a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    _ ≤ (4 * cosh (z.im * L / 2) / |z.re|) ^ 2 := pow_le_pow_left₀ (abs_nonneg a) h 2
    _ = 16 * cosh (z.im * L / 2) ^ 2 / z.re ^ 2 := by rw [div_pow, sq_abs]; ring

/-- If `f i ≤ c` for every `i`, then `‖v‖²·∑ᵢ f i ≤ #ι·c·‖v‖²`. -/
theorem dot_mul_sum_le {v : ι → ℝ} {f : ι → ℝ} {c : ℝ} (hf : ∀ i, f i ≤ c) :
    (v ⬝ᵥ v) * ∑ i, f i ≤ Fintype.card ι * c * (v ⬝ᵥ v) := by
  have hv := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' v
  have hs : ∑ i, f i ≤ Fintype.card ι * c := by
    calc ∑ i, f i ≤ ∑ _i : ι, c := Finset.sum_le_sum fun i _ => hf i
      _ = Fintype.card ι * c := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  nlinarith

/-- **Far even bound over any mode set**: if `2|ωᵢ| ≤ |Re z|` for every mode then
`(∫_{−L/2}^{L/2} cosPoly_ξ(t + L/2) ve_z)² ≤ 16·#ι·cosh²(Im z·L/2)/(Re z)²·‖ξ‖²`. -/
theorem sq_integral_cosPoly_mul_ve_le_of_modes (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) (z : ℂ)
    (hω : ∀ i, 2 * |omega L mode i| ≤ |z.re|) :
    (∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L mode ξ (t + L / 2) * ve z t) ^ 2
      ≤ 16 * Fintype.card ι * cosh (z.im * L / 2) ^ 2 / z.re ^ 2 * (ξ ⬝ᵥ ξ) := by
  refine (sq_integral_cosPoly_mul_le L mode ξ (Cvs.StepA.OneZeroParitySectors.continuous_ve z)).trans ?_
  have h := dot_mul_sum_le (v := ξ)
    (fun i => sq_le_of_abs_le_far (abs_integral_cos_mul_ve_le L (omega L mode i) z (hω i)))
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **Far odd bound over any mode set**: if `2|ωᵢ| ≤ |Re z|` for every mode then
`(∫_{−L/2}^{L/2} sinePoly_o(t + L/2) uo_z)² ≤ 16·#ι·cosh²(Im z·L/2)/(Re z)²·‖o‖²`. -/
theorem sq_integral_sinePoly_mul_uo_le_of_modes (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) (z : ℂ)
    (hω : ∀ i, 2 * |omega L mode i| ≤ |z.re|) :
    (∫ t in -(L / 2)..L / 2, Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (t + L / 2) * uo z t) ^ 2
      ≤ 16 * Fintype.card ι * cosh (z.im * L / 2) ^ 2 / z.re ^ 2 * (o ⬝ᵥ o) := by
  refine (sq_integral_sinePoly_mul_le L mode o (Cvs.StepA.OneZeroParitySectors.continuous_uo z)).trans ?_
  have h := dot_mul_sum_le (v := o)
    (fun i => sq_le_of_abs_le_far (abs_integral_sin_mul_uo_le L (omega L mode i) z (hω i)))
  calc _ ≤ _ := h
    _ = _ := by ring

/-- For an involution `neg`, `|v ⬝ᵥ (v ∘ neg)| ≤ v ⬝ᵥ v`. -/
theorem abs_dotProduct_comp_le {neg : ι → ι} (hinv : Function.Involutive neg) (v : ι → ℝ) :
    |v ⬝ᵥ fun i => v (neg i)| ≤ v ⬝ᵥ v := by
  have hperm : ∑ i, v (neg i) ^ 2 = ∑ i, v i ^ 2 := by
    have := Equiv.sum_comp (Function.Involutive.toPerm neg hinv) fun i => v i ^ 2
    simpa only [Function.Involutive.coe_toPerm] using this
  have hd : (v ⬝ᵥ fun i => v (neg i)) = ∑ i, v i * v (neg i) := rfl
  have hlo : ∑ i, -(v i ^ 2 + v (neg i) ^ 2) ≤ ∑ i, 2 * (v i * v (neg i)) :=
    Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (v i + v (neg i))]
  have hhi : ∑ i, 2 * (v i * v (neg i)) ≤ ∑ i, (v i ^ 2 + v (neg i) ^ 2) :=
    Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (v i - v (neg i))]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hperm] at hlo
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hperm] at hhi
  have hs : v ⬝ᵥ v = ∑ i, v i ^ 2 := by simp only [dotProduct, sq]
  rw [abs_le, hd, hs]
  constructor <;> linarith

/-- **The cosine energy without parity**: for a symmetric injective mode set and `L > 0`,
`∫_{−L/2}^{L/2} cosPoly_ξ(t + L/2)² ≤ L‖ξ‖²` for every `ξ`. -/
theorem integral_cosPoly_centred_sq_le {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) (ξ : ι → ℝ) :
    ∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L mode ξ (t + L / 2) ^ 2
      ≤ L * (ξ ⬝ᵥ ξ) := by
  rw [intervalIntegral.integral_comp_add_right
      (fun s => Cvs.Finite.EvenSectorZeroSide.cosPoly L mode ξ s ^ 2),
    show -(L / 2) + L / 2 = 0 by ring, show L / 2 + L / 2 = L by ring,
    Cvs.StepA.SectorBottomsLowerBound.integral_cosPoly_sq hL.ne' hinj hmode]
  have h := (abs_le.mp (abs_dotProduct_comp_le hinv ξ)).2
  nlinarith

/-- **The sine energy without parity**: for a symmetric injective mode set and `L > 0`,
`∫_{−L/2}^{L/2} sinePoly_o(t + L/2)² ≤ L‖o‖²` for every `o`. -/
theorem integral_sinePoly_centred_sq_le {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) (o : ι → ℝ) :
    ∫ t in -(L / 2)..L / 2, Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (t + L / 2) ^ 2
      ≤ L * (o ⬝ᵥ o) := by
  rw [intervalIntegral.integral_comp_add_right
      (fun s => Cvs.Finite.OddSectorZeroSide.sinePoly L mode o s ^ 2),
    show -(L / 2) + L / 2 = 0 by ring, show L / 2 + L / 2 = L by ring,
    Cvs.StepA.SectorBottomsLowerBound.integral_sinePoly_sq hL.ne' hinj hmode]
  have h := (abs_le.mp (abs_dotProduct_comp_le hinv o)).1
  nlinarith

end Modes

/-! ### The window modes `0, ±1, …, ±N` -/

/-- Every window mode has `|ωᵢ| ≤ 2πN/L` when `L ≥ 0`. -/
theorem abs_omega_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (i : Idx N) :
    |omega L (mode N) i| ≤ 2 * π * N / L := by
  unfold omega
  rw [abs_div, abs_of_nonneg hL, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hL
  have h := Cvs.Finite.ModeTruncationBound.abs_mode_le N i
  rw [← Int.cast_abs]
  exact_mod_cast h

/-- There are `2N + 1` window modes. -/
theorem card_idx (N : ℕ) : (Fintype.card (Idx N) : ℝ) = 2 * N + 1 := by
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  push_cast
  ring

/-- **The far even bound on the window modes**: for `L ≥ 0` and `2·(2πN/L) ≤ |Re z|`,
`(∫_{−L/2}^{L/2} cosPoly_ξ(t + L/2) ve_z)² ≤ 16(2N+1)cosh²(Im z·L/2)/(Re z)²·‖ξ‖²`. -/
theorem sq_integral_cosPoly_mul_ve_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (ξ : Idx N → ℝ) (z : ℂ)
    (h : 2 * (2 * π * N / L) ≤ |z.re|) :
    (∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) * ve z t) ^ 2
      ≤ 16 * (2 * N + 1) * cosh (z.im * L / 2) ^ 2 / z.re ^ 2 * (ξ ⬝ᵥ ξ) := by
  have h' := sq_integral_cosPoly_mul_ve_le_of_modes L (mode N) ξ z fun i =>
    (mul_le_mul_of_nonneg_left (abs_omega_le hL N i) zero_le_two).trans h
  rwa [card_idx] at h'

/-- **The far odd bound on the window modes**: for `L ≥ 0` and `2·(2πN/L) ≤ |Re z|`,
`(∫_{−L/2}^{L/2} sinePoly_o(t + L/2) uo_z)² ≤ 16(2N+1)cosh²(Im z·L/2)/(Re z)²·‖o‖²`. -/
theorem sq_integral_sinePoly_mul_uo_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (o : Idx N → ℝ) (z : ℂ)
    (h : 2 * (2 * π * N / L) ≤ |z.re|) :
    (∫ t in -(L / 2)..L / 2, Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (t + L / 2) * uo z t) ^ 2
      ≤ 16 * (2 * N + 1) * cosh (z.im * L / 2) ^ 2 / z.re ^ 2 * (o ⬝ᵥ o) := by
  have h' := sq_integral_sinePoly_mul_uo_le_of_modes L (mode N) o z fun i =>
    (mul_le_mul_of_nonneg_left (abs_omega_le hL N i) zero_le_two).trans h
  rwa [card_idx] at h'

/-! ### The envelopes -/

/-- **The even envelope** of one zero at `z`: `16(2N+1)cosh²(Im z·L/2)/(L(Re z)²)` when
`2·(2πN/L) ≤ |Re z|`, and `∫_{−L/2}^{L/2} ve_z²` otherwise. -/
def envE (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  if 2 * (2 * π * N / L) ≤ |z.re| then 16 * (2 * N + 1) * cosh (z.im * L / 2) ^ 2 / (L * z.re ^ 2)
  else ∫ t in -(L / 2)..L / 2, ve z t ^ 2

/-- **The odd envelope** of one zero at `z`: `16(2N+1)cosh²(Im z·L/2)/(L(Re z)²)` when
`2·(2πN/L) ≤ |Re z|`, and `∫_{−L/2}^{L/2} uo_z²` otherwise. -/
def envO (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  if 2 * (2 * π * N / L) ≤ |z.re| then 16 * (2 * N + 1) * cosh (z.im * L / 2) ^ 2 / (L * z.re ^ 2)
  else ∫ t in -(L / 2)..L / 2, uo z t ^ 2

/-- The even envelope is nonnegative for `L ≥ 0`. -/
theorem envE_nonneg {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (z : ℂ) : 0 ≤ envE L N z := by
  unfold envE
  split_ifs
  · positivity
  · exact intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _

/-- The odd envelope is nonnegative for `L ≥ 0`. -/
theorem envO_nonneg {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (z : ℂ) : 0 ≤ envO L N z := by
  unfold envO
  split_ifs
  · positivity
  · exact intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _

/-- The far expression times `L‖v‖²` is the far bound: `c/(L x²)·(L‖v‖²) = c/x²·‖v‖²` for `L ≠ 0`. -/
theorem far_mul_eq {L : ℝ} (hL : L ≠ 0) (c x d : ℝ) : c / (L * x ^ 2) * (L * d) = c / x ^ 2 * d := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · field_simp

/-- **The even pairing is at least minus the envelope**: for `L > 0` and every `ξ`,
`−envE·L‖ξ‖² ≤ (∫ cosPoly_ξ(t + L/2) ue_z)² − (∫ cosPoly_ξ(t + L/2) ve_z)²`. -/
theorem neg_envE_mul_le_sq_sub_sq {L : ℝ} (hL : 0 < L) (N : ℕ) (ξ : Idx N → ℝ) (z : ℂ) :
    -(envE L N z * (L * (ξ ⬝ᵥ ξ)))
      ≤ (∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) * ue z t) ^ 2
        - (∫ t in -(L / 2)..L / 2,
            Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) * ve z t) ^ 2 := by
  suffices h : (∫ t in -(L / 2)..L / 2,
      Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) * ve z t) ^ 2
        ≤ envE L N z * (L * (ξ ⬝ᵥ ξ)) by
    nlinarith [sq_nonneg (∫ t in -(L / 2)..L / 2,
      Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) * ue z t)]
  unfold envE
  split_ifs with hfar
  · rw [far_mul_eq hL.ne']
    exact sq_integral_cosPoly_mul_ve_le hL.le N ξ z hfar
  · have hc : Continuous fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) := by
      unfold Cvs.Finite.EvenSectorZeroSide.cosPoly; fun_prop
    have hw := Cvs.StepA.OneZeroParitySectors.continuous_ve z
    have cs := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le (show -(L / 2) ≤ L / 2 by linarith)
      ((hc.pow 2).intervalIntegrable _ _) ((hw.pow 2).intervalIntegrable _ _)
      ((hc.mul hw).intervalIntegrable _ _)
    have hE := integral_cosPoly_centred_sq_le hL (Cvs.Finite.SymmetricModeSet.mode_injective N)
      (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) ξ
    have hv : 0 ≤ ∫ t in -(L / 2)..L / 2, ve z t ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _
    nlinarith

/-- **The odd pairing is at most the envelope**: for `L > 0` and every `o`,
`(∫ sinePoly_o(t + L/2) uo_z)² − (∫ sinePoly_o(t + L/2) vo_z)² ≤ envO·L‖o‖²`. -/
theorem sq_sub_sq_le_envO_mul {L : ℝ} (hL : 0 < L) (N : ℕ) (o : Idx N → ℝ) (z : ℂ) :
    (∫ t in -(L / 2)..L / 2, Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (t + L / 2) * uo z t) ^ 2
        - (∫ t in -(L / 2)..L / 2,
            Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (t + L / 2) * vo z t) ^ 2
      ≤ envO L N z * (L * (o ⬝ᵥ o)) := by
  suffices h : (∫ t in -(L / 2)..L / 2,
      Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (t + L / 2) * uo z t) ^ 2
        ≤ envO L N z * (L * (o ⬝ᵥ o)) by
    nlinarith [sq_nonneg (∫ t in -(L / 2)..L / 2,
      Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (t + L / 2) * vo z t)]
  unfold envO
  split_ifs with hfar
  · rw [far_mul_eq hL.ne']
    exact sq_integral_sinePoly_mul_uo_le hL.le N o z hfar
  · have hc : Continuous fun t => Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (t + L / 2) := by
      unfold Cvs.Finite.OddSectorZeroSide.sinePoly; fun_prop
    have hw := Cvs.StepA.OneZeroParitySectors.continuous_uo z
    have cs := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le (show -(L / 2) ≤ L / 2 by linarith)
      ((hc.pow 2).intervalIntegrable _ _) ((hw.pow 2).intervalIntegrable _ _)
      ((hc.mul hw).intervalIntegrable _ _)
    have hE := integral_sinePoly_centred_sq_le hL (Cvs.Finite.SymmetricModeSet.mode_injective N)
      (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) o
    have hv : 0 ≤ ∫ t in -(L / 2)..L / 2, uo z t ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _
    nlinarith

/-! ### Summability over the zeros -/

/-- **The far expression under a bound on `cosh²`**: for `L > 0`, a zero with `|γ_ρ| ≥ 1` and any
`K ≥ cosh²(Im z_ρ·L/2)` has
`16(2N+1)cosh²(Im z_ρ·L/2)/(L(Re z_ρ)²) ≤ 2·16(2N+1)K/L · 1/(1 + γ_ρ²)`. -/
theorem far_le_of_cosh_sq_le {L : ℝ} (hL : 0 < L) (N : ℕ)
    (ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) (hγ : 1 ≤ |(ρ : ℂ).im|) {K : ℝ}
    (hK : cosh ((Cvs.ZeroCounting.zPoint ρ).im * L / 2) ^ 2 ≤ K) :
    16 * (2 * N + 1) * cosh ((Cvs.ZeroCounting.zPoint ρ).im * L / 2) ^ 2
        / (L * (Cvs.ZeroCounting.zPoint ρ).re ^ 2)
      ≤ 2 * (16 * (2 * N + 1) * K / L) * (1 / (1 + ((ρ : ℂ).im) ^ 2)) := by
  rw [Cvs.ZeroCounting.zPoint_re]
  set x := (ρ : ℂ).im with hxdef
  set y := (Cvs.ZeroCounting.zPoint ρ).im with hydef
  have hx2 : 1 ≤ x ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hγ 2
    rwa [one_pow, sq_abs] at this
  have hK0 : 0 ≤ K := (sq_nonneg _).trans hK
  have hKL : 0 ≤ 16 * (2 * (N : ℝ) + 1) * K / L := by positivity
  have hx0 : 0 < x ^ 2 := by linarith
  calc 16 * (2 * N + 1) * cosh (y * L / 2) ^ 2 / (L * x ^ 2)
      ≤ 16 * (2 * N + 1) * K / (L * x ^ 2) := by gcongr
    _ = 16 * (2 * N + 1) * K / L * (1 / x ^ 2) := by
        field_simp
    _ ≤ 16 * (2 * N + 1) * K / L * (2 / (1 + x ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKL
        rw [div_le_div_iff₀ hx0 (by positivity)]
        linarith
    _ = 2 * (16 * (2 * N + 1) * K / L) * (1 / (1 + x ^ 2)) := by ring

/-- For `L ≥ 0`, every zero has `cosh²(Im z_ρ·L/2) ≤ cosh²(L/4)`. -/
theorem cosh_sq_zPoint_le {L : ℝ} (hL : 0 ≤ L) (ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    cosh ((Cvs.ZeroCounting.zPoint ρ).im * L / 2) ^ 2 ≤ cosh (L / 4) ^ 2 := by
  set y := (Cvs.ZeroCounting.zPoint ρ).im with hydef
  have hy2 : y ^ 2 ≤ 1 / 4 := Cvs.ZeroCounting.sq_zPoint_im_le ρ
  have hy : |y| ≤ 1 / 2 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hcosh : cosh (y * L / 2) ≤ cosh (L / 4) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : 0 ≤ L / 4),
      show y * L / 2 = y * (L / 2) by ring, abs_mul, abs_of_nonneg (by positivity : 0 ≤ L / 2)]
    nlinarith
  exact pow_le_pow_left₀ (Real.cosh_pos _).le hcosh 2

/-- **The far expression is dominated by `1/(1 + γ²)`**: for `L > 0`, a zero with `|γ_ρ| ≥ 1`
has `16(2N+1)cosh²(Im z_ρ·L/2)/(L(Re z_ρ)²) ≤ 2·16(2N+1)cosh²(L/4)/L · 1/(1 + γ_ρ²)`. -/
theorem far_le_inv_one_add_sq {L : ℝ} (hL : 0 < L) (N : ℕ)
    (ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) (hγ : 1 ≤ |(ρ : ℂ).im|) :
    16 * (2 * N + 1) * cosh ((Cvs.ZeroCounting.zPoint ρ).im * L / 2) ^ 2
        / (L * (Cvs.ZeroCounting.zPoint ρ).re ^ 2)
      ≤ 2 * (16 * (2 * N + 1) * cosh (L / 4) ^ 2 / L) * (1 / (1 + ((ρ : ℂ).im) ^ 2)) :=
  far_le_of_cosh_sq_le hL N ρ hγ (cosh_sq_zPoint_le hL.le ρ)

/-- **Summability from the far expression**: for `L > 0`, a family equal to
`16(2N+1)cosh²(Im z_ρ·L/2)/(L(Re z_ρ)²)` wherever `2·(2πN/L) ≤ |Re z_ρ|` is summable against the
multiplicities. -/
theorem summable_of_eq_far {L : ℝ} (hL : 0 < L) (N : ℕ)
    {f : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet → ℝ}
    (hf : ∀ ρ, 2 * (2 * π * N / L) ≤ |(Cvs.ZeroCounting.zPoint ρ).re| →
      f ρ = 16 * (2 * N + 1) * cosh ((Cvs.ZeroCounting.zPoint ρ).im * L / 2) ^ 2
        / (L * (Cvs.ZeroCounting.zPoint ρ).re ^ 2)) :
    Summable fun ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * f ρ := by
  refine Summable.of_norm_bounded_eventually
    (Cvs.Zeta.QuadraticWeightSummable.summable_divisorWeight_sq.mul_left
      (2 * (16 * (2 * N + 1) * cosh (L / 4) ^ 2 / L))) ?_
  rw [Filter.eventually_cofinite]
  refine (Cvs.GaussKernel.finite_window (max 1 (2 * (2 * π * N / L)))).subset fun ρ hρ => ?_
  simp only [Set.mem_ofPred_eq] at hρ ⊢
  by_contra hfar
  apply hρ
  have hg : Cvs.GaussKernel.gam ρ = (ρ : ℂ).im := rfl
  rw [hg, not_le, max_lt_iff] at hfar
  have hre : (Cvs.ZeroCounting.zPoint ρ).re = (ρ : ℂ).im := Cvs.ZeroCounting.zPoint_re ρ
  have hfρ := hf ρ (by rw [hre]; exact hfar.2.le)
  have hle := far_le_inv_one_add_sq hL N ρ hfar.1.le
  have hm : (0 : ℝ) ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) := Nat.cast_nonneg _
  have hf0 : 0 ≤ f ρ := by rw [hfρ]; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hm hf0), hfρ]
  calc (Cvs.Criterion.divisorWeight ρ : ℝ)
        * (16 * (2 * N + 1) * cosh ((Cvs.ZeroCounting.zPoint ρ).im * L / 2) ^ 2
          / (L * (Cvs.ZeroCounting.zPoint ρ).re ^ 2))
      ≤ (Cvs.Criterion.divisorWeight ρ : ℝ)
          * (2 * (16 * (2 * N + 1) * cosh (L / 4) ^ 2 / L) * (1 / (1 + ((ρ : ℂ).im) ^ 2))) :=
        mul_le_mul_of_nonneg_left hle hm
    _ = 2 * (16 * (2 * N + 1) * cosh (L / 4) ^ 2 / L)
          * ((Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + ((ρ : ℂ).im) ^ 2))) := by ring

/-- **The even envelope is summable over the zeros**: for `L > 0`, `m_ρ envE(L, N, z_ρ)` is
summable. -/
theorem summable_envE {L : ℝ} (hL : 0 < L) (N : ℕ) :
    Summable fun ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * envE L N (Cvs.ZeroCounting.zPoint ρ) :=
  summable_of_eq_far hL N fun ρ hfar => by rw [envE, if_pos hfar]

/-- **The odd envelope is summable over the zeros**: for `L > 0`, `m_ρ envO(L, N, z_ρ)` is
summable. -/
theorem summable_envO {L : ℝ} (hL : 0 < L) (N : ℕ) :
    Summable fun ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * envO L N (Cvs.ZeroCounting.zPoint ρ) :=
  summable_of_eq_far hL N fun ρ hfar => by rw [envO, if_pos hfar]

end Cvs.StepA.ModePolynomialFarEnvelope
