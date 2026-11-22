import Mathlib
import Cvs.Zeta.XiVerticalFull

/-!
# The Paley–Wiener contour shift

`Cvs.Zeta.CriticalParam` identified the last gap between this development's explicit formula
and the classical one: the prime side carries `n^{−2}·φ̂(log n)` where the classical form has
`n^{−1/2}·ĥ(log n)`, and the two agree once the transform's contour is shifted from `Im =
−3/2` to the real axis.
-/

open Complex MeasureTheory

namespace Cvs.Zeta

variable {f : ℂ → ℂ} {B a : ℝ}

/-- Decay of `f` on the horizontal strip `−a ≤ Im w ≤ 0`. -/
def StripDecayRe (f : ℂ → ℂ) (B a : ℝ) : Prop :=
  ∀ w : ℂ, -a ≤ w.im → w.im ≤ 0 → ‖f w‖ ≤ B / (1 + |w.re|) ^ 2

theorem norm_le_of_stripDecay (hd : StripDecayRe f B a) (x : ℝ) {y : ℝ}
    (h1 : -a ≤ y) (h2 : y ≤ 0) : ‖f ((x : ℂ) + y * I)‖ ≤ B / (1 + |x|) ^ 2 := by
  have h := hd ((x : ℂ) + y * I) (by simpa using h1) (by simpa using h2)
  simpa using h

/-- The two vertical sides of the shifting rectangle vanish as `R → ∞`. -/
theorem norm_vertical_side_le (ha : 0 ≤ a) (hd : StripDecayRe f B a)
    (R : ℝ) (σ : ℝ) (hσ : |σ| = R) :
    ‖∫ y in (-a)..0, f ((σ : ℂ) + y * I)‖ ≤ a * (B / (1 + R) ^ 2) := by
  have hpt : ∀ y ∈ Set.uIoc (-a) 0, ‖f ((σ : ℂ) + y * I)‖ ≤ B / (1 + R) ^ 2 := by
    intro y hy
    rw [Set.uIoc_of_le (by linarith)] at hy
    have := norm_le_of_stripDecay hd σ hy.1.le hy.2
    rwa [hσ] at this
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  calc ‖∫ y in (-a)..0, f ((σ : ℂ) + y * I)‖
      ≤ B / (1 + R) ^ 2 * |(0 : ℝ) - -a| := h
    _ = a * (B / (1 + R) ^ 2) := by rw [show (0 : ℝ) - -a = a from by ring, abs_of_nonneg ha]; ring

/-- Integrability on a horizontal line inside the strip. -/
theorem integrable_line (hf : Continuous f) (hB : 0 ≤ B) (hd : StripDecayRe f B a)
    {y : ℝ} (h1 : -a ≤ y) (h2 : y ≤ 0) :
    Integrable fun x : ℝ => f ((x : ℂ) + y * I) := by
  have hdom : Integrable (fun x : ℝ => B * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hdom (hf.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  refine (norm_le_of_stripDecay hd x h1 h2).trans ?_
  have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hsq : (1 : ℝ) + x ^ 2 ≤ (1 + |x|) ^ 2 := by
    have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hB (by positivity) hsq

/-- **The contour shift.** For `f` entire and decaying in the real direction uniformly on the
strip `−a ≤ Im ≤ 0`, the integral along `Im = −a` equals the one along `Im = 0`. -/
theorem contour_shift (hf : Differentiable ℂ f) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hd : StripDecayRe f B a) :
    (∫ x : ℝ, f ((x : ℂ) - a * I)) = ∫ x : ℝ, f (x : ℂ) := by
  -- the rectangle identity at each `R`
  have hrect : ∀ R : ℝ,
      (∫ x in (-R)..R, f ((x : ℂ) - a * I)) - (∫ x in (-R)..R, f (x : ℂ))
        = -(I * ∫ y in (-a)..0, f ((R : ℂ) + y * I))
          + I * ∫ y in (-a)..0, f ((-R : ℂ) + y * I) := by
    intro R
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      f ((-R : ℂ) - a * I) (R : ℂ) hf.differentiableOn
    norm_num at h
    simp only [← sub_eq_add_neg] at h
    linear_combination h
  -- the vertical sides vanish
  have hvert : Filter.Tendsto
      (fun R : ℝ => -(I * ∫ y in (-a)..0, f ((R : ℂ) + y * I))
        + I * ∫ y in (-a)..0, f ((-R : ℂ) + y * I)) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun R : ℝ => 2 * a * B / (1 + R)) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds
        (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    have hR1 : (0 : ℝ) < 1 + R := by linarith
    have h1 := norm_vertical_side_le ha hd R R (abs_of_nonneg hR)
    have h2 := norm_vertical_side_le ha hd R (-R) (by rw [abs_neg, abs_of_nonneg hR])
    have hsq : (1 : ℝ) + R ≤ (1 + R) ^ 2 := by nlinarith
    have hle : B / (1 + R) ^ 2 ≤ B / (1 + R) :=
      div_le_div_of_nonneg_left hB hR1 hsq
    have hstep : ∀ σ : ℝ, ‖∫ y in (-a)..0, f ((σ : ℂ) + y * I)‖ ≤ a * (B / (1 + R) ^ 2) →
        ‖I * ∫ y in (-a)..0, f ((σ : ℂ) + y * I)‖ ≤ a * (B / (1 + R)) := by
      intro σ hσ
      rw [norm_mul, Complex.norm_I, one_mul]
      exact hσ.trans (mul_le_mul_of_nonneg_left hle ha)
    have e1 := hstep R h1
    have e2 : ‖I * ∫ y in (-a)..0, f ((-R : ℂ) + y * I)‖ ≤ a * (B / (1 + R)) := by
      have := hstep (-R) (by simpa using h2)
      simpa using this
    calc ‖-(I * ∫ y in (-a)..0, f ((R : ℂ) + y * I))
            + I * ∫ y in (-a)..0, f ((-R : ℂ) + y * I)‖
        ≤ ‖-(I * ∫ y in (-a)..0, f ((R : ℂ) + y * I))‖
          + ‖I * ∫ y in (-a)..0, f ((-R : ℂ) + y * I)‖ := norm_add_le _ _
      _ ≤ a * (B / (1 + R)) + a * (B / (1 + R)) := by
          rw [norm_neg]; exact add_le_add e1 e2
      _ = 2 * a * B / (1 + R) := by ring
  -- the horizontal sides converge to the full-line integrals
  have hint0 : Integrable fun x : ℝ => f (x : ℂ) := by
    have := integrable_line hf.continuous hB hd (y := 0) (by linarith) le_rfl
    simpa using this
  have hinta : Integrable fun x : ℝ => f ((x : ℂ) - a * I) := by
    have := integrable_line hf.continuous hB hd (y := -a) le_rfl (by linarith)
    simpa [sub_eq_add_neg] using this
  have hA : Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..R, f ((x : ℂ) - a * I))
      Filter.atTop (nhds (∫ x : ℝ, f ((x : ℂ) - a * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hinta tendsto_neg_atBot Filter.tendsto_id
  have hC : Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..R, f (x : ℂ))
      Filter.atTop (nhds (∫ x : ℝ, f (x : ℂ))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hint0 tendsto_neg_atBot Filter.tendsto_id
  have hdiff := hA.sub hC
  rw [funext hrect] at hdiff
  have := tendsto_nhds_unique hdiff hvert
  linear_combination this

end Cvs.Zeta
