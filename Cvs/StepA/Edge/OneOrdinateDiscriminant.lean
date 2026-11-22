import Mathlib
import Cvs.StepA.Edge.EdgeDiscriminant
import Cvs.StepA.Edge.TwoEdgeSplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge discriminant of one ordinate up to sign

For weights `m ≥ 0` and ordinates `±g`, `g ≠ 0`, at depth `δ > 0`, the edge form at
`L = arg(δ + ig)/g` is `(∑ m)((∫₀^a F Re w)² − (∫₀^a F Im w)²)` with `w = e^{iθ/2 − (δ+ig)u}`, whose
quotients have supremum `(∑ m)(1/(2δ) + 1/(2|δ + ig|))/2` and infimum
`−(∑ m)(1/(2δ) − 1/(2|δ + ig|))/2`, so `edgeDisc = (∑ m)/(2|δ + ig|) > 0` there.
-/
noncomputable section

open Real MeasureTheory

namespace Cvs.StepA.Edge.OneOrdinateDiscriminant
open Cvs.ZeroCounting

open Cvs.StepA.Edge.TwoEdgeSplit (edgePair edgeForm integral_exp_mul_eq)
open Cvs.StepA.Edge.EdgeDiscriminant (edgeRay edgeDisc edgeRay_nonempty edgeRay_bddBelow pos_of_integral_sq_pos)

/-! ### The edge form of one ordinate up to sign -/

/-- The edge pairing at `−γ` is the conjugate of that at `γ`. -/
theorem edgePair_neg (δ γ : ℝ) (F : ℝ → ℝ) (a : ℝ) :
    edgePair δ (-γ) F a = starRingEnd ℂ (edgePair δ γ F a) := by
  unfold edgePair
  rw [← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, map_add, Complex.conj_I]
  congr 2
  push_cast
  ring

/-- One term of the edge form is even in the ordinate. -/
theorem edgeTerm_neg (δ γ L : ℝ) (F : ℝ → ℝ) (a : ℝ) :
    (Complex.exp ((-γ : ℝ) * L * Complex.I) * edgePair δ (-γ) F a ^ 2).re
      = (Complex.exp (γ * L * Complex.I) * edgePair δ γ F a ^ 2).re := by
  have h : Complex.exp ((-γ : ℝ) * L * Complex.I)
      = starRingEnd ℂ (Complex.exp (γ * L * Complex.I)) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  rw [h, edgePair_neg, ← map_pow, ← map_mul, Complex.conj_re]

/-! ### The rotated edge weight -/

/-- The rotated edge weight `e^{iθ/2 − (δ + iγ)u}`. -/
def rotW (θ δ γ : ℝ) (u : ℝ) : ℂ :=
  Complex.exp (θ * Complex.I / 2 - ((δ : ℂ) + γ * Complex.I) * u)

/-- The rotated edge weight is continuous. -/
@[fun_prop] theorem continuous_rotW (θ δ γ : ℝ) : Continuous (rotW θ δ γ) := by
  unfold rotW; fun_prop

/-- `|rotW|² = e^{−2δu}`, in real and imaginary parts. -/
theorem rotW_re_sq_add_im_sq (θ δ γ u : ℝ) :
    (rotW θ δ γ u).re ^ 2 + (rotW θ δ γ u).im ^ 2 = Real.exp (-(2 * δ) * u) := by
  have h := Complex.sq_norm (rotW θ δ γ u)
  rw [Complex.normSq_apply] at h
  have hn : ‖rotW θ δ γ u‖ = Real.exp (-(δ * u)) := by
    unfold rotW; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  rw [hn, ← Real.exp_nat_mul] at h
  rw [show -(2 * δ) * u = (2 : ℕ) * -(δ * u) by push_cast; ring, h]
  ring

/-- `(rotW)² = e^{iθ} e^{−2(δ + iγ)u}`, in real and imaginary parts. -/
theorem rotW_sq (θ δ γ u : ℝ) :
    rotW θ δ γ u ^ 2
      = Complex.exp (θ * Complex.I) * Complex.exp (-(2 * ((δ : ℂ) + γ * Complex.I)) * u) := by
  unfold rotW
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring

/-- `∫₀^a (rotW)² = e^{iθ}(1 − e^{−2(δ+iγ)a})/(2(δ + iγ))` for `δ > 0`. -/
theorem integral_rotW_sq {θ δ : ℝ} (hδ : 0 < δ) (γ a : ℝ) :
    ∫ u in (0 : ℝ)..a, rotW θ δ γ u ^ 2
      = Complex.exp (θ * Complex.I)
        * ((1 - Complex.exp (-(2 * ((δ : ℂ) + γ * Complex.I)) * a))
          / (2 * ((δ : ℂ) + γ * Complex.I))) := by
  have hc : -(2 * ((δ : ℂ) + γ * Complex.I)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  simp_rw [rotW_sq]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
  congr 1
  push_cast
  rw [mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- The real-part energy of `rotW` on `[0, a]`: `∫ (Re w)² = (∫ e^{−2δu} + Re ∫ w²)/2`. -/
theorem integral_rotW_re_sq (θ δ γ a : ℝ) :
    ∫ u in (0 : ℝ)..a, (rotW θ δ γ u).re ^ 2
      = ((∫ u in (0 : ℝ)..a, Real.exp (-(2 * δ) * u))
          + (∫ u in (0 : ℝ)..a, rotW θ δ γ u ^ 2).re) / 2 := by
  have hint : IntervalIntegrable (fun u => rotW θ δ γ u ^ 2) volume 0 a :=
    (by fun_prop : Continuous fun u => rotW θ δ γ u ^ 2).intervalIntegrable _ _
  have hre := intervalIntegral.intervalIntegral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  have hpt : ∀ u, (rotW θ δ γ u).re ^ 2
      = (Real.exp (-(2 * δ) * u) + (rotW θ δ γ u ^ 2).re) / 2 := by
    intro u
    rw [← rotW_re_sq_add_im_sq θ δ γ u, sq (rotW θ δ γ u), Complex.mul_re]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(2 * δ) * u)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u => (rotW θ δ γ u ^ 2).re).intervalIntegrable _ _)]

/-- The imaginary-part energy of `rotW` on `[0, a]`: `∫ (Im w)² = (∫ e^{−2δu} − Re ∫ w²)/2`. -/
theorem integral_rotW_im_sq (θ δ γ a : ℝ) :
    ∫ u in (0 : ℝ)..a, (rotW θ δ γ u).im ^ 2
      = ((∫ u in (0 : ℝ)..a, Real.exp (-(2 * δ) * u))
          - (∫ u in (0 : ℝ)..a, rotW θ δ γ u ^ 2).re) / 2 := by
  have hint : IntervalIntegrable (fun u => rotW θ δ γ u ^ 2) volume 0 a :=
    (by fun_prop : Continuous fun u => rotW θ δ γ u ^ 2).intervalIntegrable _ _
  have hre := intervalIntegral.intervalIntegral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  have hpt : ∀ u, (rotW θ δ γ u).im ^ 2
      = (Real.exp (-(2 * δ) * u) - (rotW θ δ γ u ^ 2).re) / 2 := by
    intro u
    rw [← rotW_re_sq_add_im_sq θ δ γ u, sq (rotW θ δ γ u), Complex.mul_re]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(2 * δ) * u)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u => (rotW θ δ γ u ^ 2).re).intervalIntegrable _ _)]

/-- The cross energy of `rotW` on `[0, a]`: `∫ Re w · Im w = (Im ∫ w²)/2`. -/
theorem integral_rotW_re_mul_im (θ δ γ a : ℝ) :
    ∫ u in (0 : ℝ)..a, (rotW θ δ γ u).re * (rotW θ δ γ u).im
      = (∫ u in (0 : ℝ)..a, rotW θ δ γ u ^ 2).im / 2 := by
  have hint : IntervalIntegrable (fun u => rotW θ δ γ u ^ 2) volume 0 a :=
    (by fun_prop : Continuous fun u => rotW θ δ γ u ^ 2).intervalIntegrable _ _
  have him := intervalIntegral.intervalIntegral_im hint
  simp only [RCLike.im_to_complex] at him
  rw [← him, ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [sq, Complex.mul_im]
  ring

/-- At `θ = arg(δ + iγ)`, `∫₀^a (rotW)² = (1 − e^{−2(δ+iγ)a})/(2|δ + iγ|)`, for `δ > 0`. -/
theorem integral_rotW_sq_arg {δ : ℝ} (hδ : 0 < δ) (γ a : ℝ) :
    ∫ u in (0 : ℝ)..a, rotW (Complex.arg ((δ : ℂ) + γ * Complex.I)) δ γ u ^ 2
      = (1 - Complex.exp (-(2 * ((δ : ℂ) + γ * Complex.I)) * a))
        / (2 * (‖(δ : ℂ) + γ * Complex.I‖ : ℂ)) := by
  have hζ0 : (δ : ℂ) + γ * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hn : (‖(δ : ℂ) + γ * Complex.I‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hζ0
  have hpolar : Complex.exp (Complex.arg ((δ : ℂ) + γ * Complex.I) * Complex.I)
      = ((δ : ℂ) + γ * Complex.I) / ‖(δ : ℂ) + γ * Complex.I‖ := by
    rw [eq_div_iff hn, mul_comm]; exact Complex.norm_mul_exp_arg_mul_I _
  rw [integral_rotW_sq hδ, hpolar]
  field_simp

/-- The norm of `e^{−2(δ+iγ)a}` is `e^{−2δa}`. -/
theorem norm_exp_neg_two_zeta (δ γ a : ℝ) :
    ‖Complex.exp (-(2 * ((δ : ℂ) + γ * Complex.I)) * a)‖ = Real.exp (-(2 * δ) * a) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]

/-- `δ < |δ + iγ|` for `γ ≠ 0`. -/
theorem lt_norm_of_ne_zero (δ : ℝ) {γ : ℝ} (hγ : γ ≠ 0) :
    δ < ‖(δ : ℂ) + γ * Complex.I‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
  exact Real.lt_sqrt_of_sq_lt (by nlinarith [sq_pos_of_ne_zero hγ])

/-- `δ ≤ |δ + iγ|`. -/
theorem le_norm_add_mul_I (δ γ : ℝ) : δ ≤ ‖(δ : ℂ) + γ * Complex.I‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg γ])

/-- At `θ = arg(δ + iγ)`, `δ > 0`, `∫₀^a (rotW)²` is at distance `e^{−2δa}/(2|δ + iγ|)` from
`1/(2|δ + iγ|)`. -/
theorem norm_integral_rotW_sq_arg_sub {δ : ℝ} (hδ : 0 < δ) (γ a : ℝ) :
    ‖(∫ u in (0 : ℝ)..a, rotW (Complex.arg ((δ : ℂ) + γ * Complex.I)) δ γ u ^ 2)
        - ((1 / (2 * ‖(δ : ℂ) + γ * Complex.I‖) : ℝ) : ℂ)‖
      = Real.exp (-(2 * δ) * a) / (2 * ‖(δ : ℂ) + γ * Complex.I‖) := by
  have hZ : 0 < ‖(δ : ℂ) + γ * Complex.I‖ := hδ.trans_le (le_norm_add_mul_I δ γ)
  rw [integral_rotW_sq_arg hδ]
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = ‖(δ : ℂ) + γ * Complex.I‖ := ⟨_, rfl⟩
  rw [← hZdef] at hZ ⊢
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have e : (1 - Complex.exp (-(2 * ((δ : ℂ) + γ * Complex.I)) * a)) / (2 * (Z : ℂ))
      - ((1 / (2 * Z) : ℝ) : ℂ)
      = -Complex.exp (-(2 * ((δ : ℂ) + γ * Complex.I)) * a) / ((2 * Z : ℝ) : ℂ) := by
    push_cast; field_simp; ring
  rw [e, norm_div, norm_neg, norm_exp_neg_two_zeta, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-- `∫₀^a e^{−2δu} du = (1 − e^{−2δa})/(2δ)` for `δ ≠ 0`. -/
theorem integral_exp_neg_two_mul {δ : ℝ} (hδ : δ ≠ 0) (a : ℝ) :
    ∫ u in (0 : ℝ)..a, Real.exp (-(2 * δ) * u) = (1 - Real.exp (-(2 * δ) * a)) / (2 * δ) := by
  rw [integral_exp_mul_eq (by simpa using hδ)]
  field_simp
  ring

/-- **The energies of `w = rotW` at `arg(δ + iγ)`**, `δ > 0`, `x = e^{−2δa}`, `Z = |δ + iγ|`:
`((1 − x)/(2δ) + (1 − x)/(2Z))/2 ≤ ∫₀^a (Re w)² ≤ (1/(2δ) + 1/(2Z))/2`, `|∫₀^a Re w Im w| ≤ x/(4Z)`,
`((1 − x)/(2δ) − (1 + x)/(2Z))/2 ≤ ∫₀^a (Im w)² ≤ (1/(2δ) − 1/(2Z))/2`. -/
theorem rotW_arg_energies {δ : ℝ} (hδ : 0 < δ) (γ a : ℝ) :
    ((1 - Real.exp (-(2 * δ) * a)) / (2 * δ)
        + (1 - Real.exp (-(2 * δ) * a)) / (2 * ‖(δ : ℂ) + γ * Complex.I‖)) / 2
      ≤ ∫ u in (0 : ℝ)..a, (rotW (Complex.arg ((δ : ℂ) + γ * Complex.I)) δ γ u).re ^ 2 ∧
    ∫ u in (0 : ℝ)..a, (rotW (Complex.arg ((δ : ℂ) + γ * Complex.I)) δ γ u).re ^ 2
      ≤ (1 / (2 * δ) + 1 / (2 * ‖(δ : ℂ) + γ * Complex.I‖)) / 2 ∧
    ((1 - Real.exp (-(2 * δ) * a)) / (2 * δ)
        - (1 + Real.exp (-(2 * δ) * a)) / (2 * ‖(δ : ℂ) + γ * Complex.I‖)) / 2
      ≤ ∫ u in (0 : ℝ)..a, (rotW (Complex.arg ((δ : ℂ) + γ * Complex.I)) δ γ u).im ^ 2 ∧
    ∫ u in (0 : ℝ)..a, (rotW (Complex.arg ((δ : ℂ) + γ * Complex.I)) δ γ u).im ^ 2
      ≤ (1 / (2 * δ) - 1 / (2 * ‖(δ : ℂ) + γ * Complex.I‖)) / 2 ∧
    |∫ u in (0 : ℝ)..a, (rotW (Complex.arg ((δ : ℂ) + γ * Complex.I)) δ γ u).re
        * (rotW (Complex.arg ((δ : ℂ) + γ * Complex.I)) δ γ u).im|
      ≤ Real.exp (-(2 * δ) * a) / (4 * ‖(δ : ℂ) + γ * Complex.I‖) := by
  have hZδ := le_norm_add_mul_I δ γ
  have hdist := norm_integral_rotW_sq_arg_sub hδ γ a
  rw [integral_rotW_re_sq, integral_rotW_im_sq, integral_rotW_re_mul_im,
    integral_exp_neg_two_mul hδ.ne']
  obtain ⟨K, hK⟩ : ∃ K, K = ∫ u in (0 : ℝ)..a,
      rotW (Complex.arg ((δ : ℂ) + γ * Complex.I)) δ γ u ^ 2 := ⟨_, rfl⟩
  rw [← hK] at hdist ⊢
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ‖(δ : ℂ) + γ * Complex.I‖ := ⟨_, rfl⟩
  rw [← hZ] at hdist hZδ ⊢
  obtain ⟨x, hx⟩ : ∃ x, x = Real.exp (-(2 * δ) * a) := ⟨_, rfl⟩
  rw [← hx] at hdist ⊢
  have hZ0 : 0 < Z := hδ.trans_le hZδ
  have hx0 : 0 ≤ x := hx ▸ (Real.exp_pos _).le
  have hre : |K.re - 1 / (2 * Z)| ≤ x / (2 * Z) := by
    rw [← hdist]
    simpa using Complex.abs_re_le_norm (K - ((1 / (2 * Z) : ℝ) : ℂ))
  have him : |K.im| ≤ x / (2 * Z) := by
    rw [← hdist]
    simpa using Complex.abs_im_le_norm (K - ((1 / (2 * Z) : ℝ) : ℂ))
  have hre' := abs_le.mp hre
  have hxZ : x / (2 * Z) ≤ x / (2 * δ) :=
    div_le_div_of_nonneg_left hx0 (by positivity) (by linarith)
  have e1 : (1 - x) / (2 * δ) = 1 / (2 * δ) - x / (2 * δ) := by ring
  have e2 : (1 - x) / (2 * Z) = 1 / (2 * Z) - x / (2 * Z) := by ring
  have e3 : (1 + x) / (2 * Z) = 1 / (2 * Z) + x / (2 * Z) := by ring
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
  rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc |K.im| ≤ x / (2 * Z) := him
    _ = x / (4 * Z) * 2 := by field_simp; ring

/-- `e^{−2δa} → 0` as `a → ∞`, for `δ > 0`. -/
theorem tendsto_exp_neg_two_mul {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun a : ℝ => Real.exp (-(2 * δ) * a)) Filter.atTop (nhds 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Filter.tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * δ))
  refine h.congr fun a => ?_
  simp only [Function.comp_apply, id]
  congr 1
  ring

/-! ### The exact edge discriminant at `arg(δ + ig)/g` -/

/-! ### Edge positivity of finite families -/

/-- **Edge positivity of every finite family**: positive weights and nonzero ordinates at a common
depth `δ > 0` have a positive edge discriminant at some scale. -/
def EdgePositiveFamilies : Prop :=
  ∀ {α : Type} (s : Finset α) (m γ : α → ℝ) (δ : ℝ), 0 < δ → s.Nonempty →
    (∀ i ∈ s, 0 < m i) → (∀ i ∈ s, γ i ≠ 0) → ∃ L : ℝ, 0 < edgeDisc s m γ δ L

end Cvs.StepA.Edge.OneOrdinateDiscriminant
