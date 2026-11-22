import Mathlib
import Cvs.Route.Visibility.ProjectionShareSawtooth

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trigonometric Mellin integrals on `(1, ∞)` and their continuation by parts

`C(y, s) = ∫₁^∞ θ^{s−1} cos(yθ) dθ` and `S(y, s) = ∫₁^∞ θ^{s−1} sin(yθ) dθ` satisfy, for `Re s < 0` and `y ≠ 0`,
`C(y, s) = −sin y/y − ((s − 1)/y)S(y, s − 1)` and `S(y, s) = cos y/y + ((s − 1)/y)C(y, s − 1)`. Four steps give
`C(y, s) = C̃(y, s)` with `C̃` polynomial in `s` up to `C(y, s − 4)`, which converges on `Re s < 4`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Complex

namespace Cvs.Upstream.TrigMellinIntegralsContinuation

/-! ### The integrals -/

/-- `C(y, s) = ∫₁^∞ θ^{s−1} cos(yθ) dθ`. -/
def cosM (y : ℝ) (s : ℂ) : ℂ := ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * (Real.cos (y * θ) : ℂ)

/-- `S(y, s) = ∫₁^∞ θ^{s−1} sin(yθ) dθ`. -/
def sinM (y : ℝ) (s : ℂ) : ℂ := ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * (Real.sin (y * θ) : ℂ)

theorem norm_cpow_sub_one {θ : ℝ} (hθ : 0 < θ) (s : ℂ) : ‖(θ : ℂ) ^ (s - 1)‖ = θ ^ (s.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hθ]; simp

theorem integrableOn_rpow_re {s : ℂ} (hs : s.re < 0) : IntegrableOn (fun θ : ℝ => θ ^ (s.re - 1)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) one_pos

theorem integral_rpow_re {s : ℂ} (hs : s.re < 0) : ∫ θ in Ioi (1 : ℝ), θ ^ (s.re - 1) = 1 / (-s.re) := by
  rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]; field_simp; ring

theorem continuousOn_cpow_sub_one (s : ℂ) : ContinuousOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1)) (Ioi 0) :=
  fun _ hθ => (Cvs.Route.Visibility.ProjectionShareSawtooth.hasDerivAt_ofReal_cpow hθ (s - 1)).continuousAt.continuousWithinAt

/-- A bounded measurable factor against `θ^{s−1}` is integrable on `(1, ∞)` for `Re s < 0`. -/
theorem integrableOn_cpow_mul {s : ℂ} (hs : s.re < 0) {f : ℝ → ℂ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ θ, ‖f θ‖ ≤ M) : IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * f θ) (Ioi 1) := by
  have hm : AEStronglyMeasurable (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * f θ) (volume.restrict (Ioi 1)) :=
    ((continuousOn_cpow_sub_one s).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
      |>.mul hf.aestronglyMeasurable
  refine ((integrableOn_rpow_re hs).mul_const M).mono' hm
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_))
  rw [norm_mul, norm_cpow_sub_one (by linarith) s]
  exact mul_le_mul_of_nonneg_left (hM θ) (Real.rpow_nonneg (by linarith) _)

theorem integrableOn_cos {s : ℂ} (hs : s.re < 0) (y : ℝ) :
    IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * (Real.cos (y * θ) : ℂ)) (Ioi 1) :=
  integrableOn_cpow_mul hs (Complex.measurable_ofReal.comp (by fun_prop)) fun θ => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cos_le_one _

theorem integrableOn_sin {s : ℂ} (hs : s.re < 0) (y : ℝ) :
    IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * (Real.sin (y * θ) : ℂ)) (Ioi 1) :=
  integrableOn_cpow_mul hs (Complex.measurable_ofReal.comp (by fun_prop)) fun θ => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sin_le_one _

/-- `‖∫₁^∞ θ^{s−1} f‖ ≤ M/(−Re s)` for `|f| ≤ M`, `Re s < 0`. -/
theorem norm_integral_cpow_mul_le {s : ℂ} (hs : s.re < 0) {f : ℝ → ℂ} {M : ℝ} (hM : ∀ θ, ‖f θ‖ ≤ M) :
    ‖∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * f θ‖ ≤ M / (-s.re) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  calc ‖∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * f θ‖ ≤ ∫ θ in Ioi (1 : ℝ), θ ^ (s.re - 1) * M := by
        refine norm_integral_le_of_norm_le ((integrableOn_rpow_re hs).mul_const M)
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_))
        rw [norm_mul, norm_cpow_sub_one (by linarith) s]
        exact mul_le_mul_of_nonneg_left (hM θ) (Real.rpow_nonneg (by linarith) _)
    _ = M / (-s.re) := by rw [integral_mul_const, integral_rpow_re hs]; field_simp

theorem norm_cosM_le {s : ℂ} (hs : s.re < 0) (y : ℝ) : ‖cosM y s‖ ≤ 1 / (-s.re) :=
  norm_integral_cpow_mul_le hs fun θ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cos_le_one _

theorem norm_sinM_le {s : ℂ} (hs : s.re < 0) (y : ℝ) : ‖sinM y s‖ ≤ 1 / (-s.re) :=
  norm_integral_cpow_mul_le hs fun θ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sin_le_one _

/-! ### One integration by parts -/

theorem tendsto_cpow_mul_atTop {s : ℂ} (hs : s.re < 1) {f : ℝ → ℂ} {M : ℝ} (hM : ∀ θ, ‖f θ‖ ≤ M) :
    Tendsto (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * f θ) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h1 : Tendsto (fun θ : ℝ => θ ^ (s.re - 1) * M) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - s.re)).mul_const M
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards with θ
    congr 1; ring_nf
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [eventually_gt_atTop 0] with θ hθ
  rw [norm_mul, norm_cpow_sub_one hθ s]
  exact mul_le_mul_of_nonneg_left (hM θ) (Real.rpow_nonneg hθ.le _)

/-- **Parts for the cosine integral**: `C(y, s) = −sin y/y − ((s − 1)/y)S(y, s − 1)` for `Re s < 0`, `y ≠ 0`. -/
theorem cosM_eq {s : ℂ} (hs : s.re < 0) {y : ℝ} (hy : y ≠ 0) :
    cosM y s = -((Real.sin y / y : ℝ) : ℂ) - (s - 1) / y * sinM y (s - 1) := by
  have hu : ∀ θ ∈ Ioi (1 : ℝ), HasDerivAt (fun θ : ℝ => (θ : ℂ) ^ (s - 1)) ((s - 1) * (θ : ℂ) ^ (s - 1 - 1)) θ :=
    fun θ hθ => Cvs.Route.Visibility.ProjectionShareSawtooth.hasDerivAt_ofReal_cpow (lt_trans one_pos hθ) (s - 1)
  have hv : ∀ θ ∈ Ioi (1 : ℝ), HasDerivAt (fun θ : ℝ => ((Real.sin (y * θ) / y : ℝ) : ℂ))
      ((Real.cos (y * θ) : ℝ) : ℂ) θ := fun θ _ => by
    have h := ((hasDerivAt_id θ).const_mul y).sin.div_const y
    exact (h.congr_deriv (by simp only [id]; field_simp)).ofReal_comp
  have hs1 : (s - 1).re < 0 := by simp; linarith
  have i1 : IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * ((Real.cos (y * θ) : ℝ) : ℂ)) (Ioi 1) :=
    integrableOn_cos hs y
  have i2 : IntegrableOn (fun θ : ℝ => (s - 1) * (θ : ℂ) ^ (s - 1 - 1) * ((Real.sin (y * θ) / y : ℝ) : ℂ))
      (Ioi 1) := by
    have : IntegrableOn (fun θ : ℝ => (s - 1) / y * ((θ : ℂ) ^ (s - 1 - 1) * ((Real.sin (y * θ) : ℝ) : ℂ)))
        (Ioi 1) := (integrableOn_sin hs1 y).const_mul ((s - 1) / y)
    refine IntegrableOn.congr_fun this (fun θ _ => ?_) measurableSet_Ioi
    push_cast; ring
  have h0 : Tendsto (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * ((Real.sin (y * θ) / y : ℝ) : ℂ)) (𝓝[>] 1)
      (𝓝 ((Real.sin y / y : ℝ) : ℂ)) := by
    have hc : ContinuousAt (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * ((Real.sin (y * θ) / y : ℝ) : ℂ)) 1 :=
      (Cvs.Route.Visibility.ProjectionShareSawtooth.hasDerivAt_ofReal_cpow one_pos (s - 1)).continuousAt.mul
        (Complex.continuous_ofReal.comp (by fun_prop)).continuousAt
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
    simpa using this
  have hinf := tendsto_cpow_mul_atTop (s := s) (by linarith) (f := fun θ => ((Real.sin (y * θ) / y : ℝ) : ℂ))
    (M := 1 / |y|) fun θ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
      exact div_le_div_of_nonneg_right (abs_sin_le_one _) (abs_nonneg _)
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv i1 i2 h0 hinf
  unfold cosM sinM
  rw [h]
  have e : ∫ θ in Ioi (1 : ℝ), (s - 1) * (θ : ℂ) ^ (s - 1 - 1) * ((Real.sin (y * θ) / y : ℝ) : ℂ)
      = (s - 1) / y * ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1 - 1) * ((Real.sin (y * θ) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
    push_cast; field_simp
  rw [e]; ring

/-- `‖C(y, s)‖ ≤ (1 + ‖s − 1‖/(1 − Re s))/|y|` for `Re s < 0`, `y ≠ 0`. -/
theorem norm_cosM_le_div {s : ℂ} (hs : s.re < 0) {y : ℝ} (hy : y ≠ 0) :
    ‖cosM y s‖ ≤ (1 + ‖s - 1‖ / (1 - s.re)) / |y| := by
  rw [cosM_eq hs hy]
  have hs1 : (s - 1).re < 0 := by simp; linarith
  have h1 := norm_sinM_le hs1 y
  have hre : -(s - 1).re = 1 - s.re := by simp
  rw [hre] at h1
  have hy0 : 0 < |y| := abs_pos.2 hy
  calc ‖-((Real.sin y / y : ℝ) : ℂ) - (s - 1) / y * sinM y (s - 1)‖
      ≤ ‖((Real.sin y / y : ℝ) : ℂ)‖ + ‖(s - 1) / y‖ * ‖sinM y (s - 1)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_mul]
    _ ≤ 1 / |y| + ‖s - 1‖ / |y| * (1 / (1 - s.re)) := by
        gcongr
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
          exact div_le_div_of_nonneg_right (abs_sin_le_one _) (abs_nonneg _)
        · rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    _ = (1 + ‖s - 1‖ / (1 - s.re)) / |y| := by
        have : 0 < 1 - s.re := by linarith
        field_simp

/-- `y ↦ C(y, s)` is continuous for `Re s < 0`. -/
theorem continuous_cosM {s : ℂ} (hs : s.re < 0) : Continuous fun y : ℝ => cosM y s := by
  unfold cosM
  refine continuous_of_dominated (bound := fun θ => θ ^ (s.re - 1))
    (fun y => (integrableOn_cos hs y).aestronglyMeasurable)
    (fun y => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_))
    (integrableOn_rpow_re hs) (Eventually.of_forall fun θ => ?_)
  · rw [norm_mul, norm_cpow_sub_one (by linarith) s, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (by linarith) _) (abs_cos_le_one _)
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (by fun_prop))

theorem cosM_neg (y : ℝ) (s : ℂ) : cosM (-y) s = cosM y s := by
  unfold cosM
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  rw [neg_mul, Real.cos_neg]

end Cvs.Upstream.TrigMellinIntegralsContinuation

end
