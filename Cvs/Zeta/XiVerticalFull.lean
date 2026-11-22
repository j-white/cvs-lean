import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiConj
import Cvs.Zeta.XiVertical
import Cvs.Zeta.XiVerticalLimit

/-!
# Both verticals, on the whole line

`Cvs.Zeta.XiContourLimit` leaves the two truncated vertical integrals `∫_{−T'}^{T'}` on the
left-hand side.
-/

open Complex MeasureTheory Set

namespace Cvs.Zeta

/-- The left vertical is the fold of the right one, reflected.  `−1 + iy = 1 − conj(2 + iy)`,
so `logDeriv_riemannXi_one_sub` and `logDeriv_riemannXi_conj` compose to give it. -/
theorem logDeriv_riemannXi_left (y : ℝ) :
    logDeriv riemannXi ((-1 : ℂ) + y * I)
      = - (starRingEnd ℂ) (logDeriv riemannXi ((2 : ℂ) + y * I)) := by
  have hc : ((-1 : ℂ) + y * I) = 1 - (starRingEnd ℂ) ((2 : ℂ) + y * I) := by
    apply Complex.ext <;> simp
    norm_num
  rw [hc, logDeriv_riemannXi_one_sub, logDeriv_riemannXi_conj]

theorem norm_logDeriv_riemannXi_left (y : ℝ) :
    ‖logDeriv riemannXi ((-1 : ℂ) + y * I)‖ = ‖logDeriv riemannXi ((2 : ℂ) + y * I)‖ := by
  rw [logDeriv_riemannXi_left, norm_neg, Complex.norm_conj]

theorem continuous_logDeriv_riemannXi_left :
    Continuous fun y : ℝ => logDeriv riemannXi ((-1 : ℂ) + y * I) := by
  simp only [logDeriv_riemannXi_left]
  exact (Complex.continuous_conj.comp continuous_logDeriv_riemannXi_vertical).neg

/-- The left vertical is integrable off `|y| ≤ 2`, by the same domination as the right —
literally: `−1 + iy = (2 + iy) − 3`, so shifting the test function by `3` (which does not
change its imaginary part, hence not its decay) reduces to `integrableOn_vline`. -/
theorem integrableOn_vline_left {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((-1 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    IntegrableOn (fun y : ℝ =>
        logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I))
      {y : ℝ | 2 ≤ |y|} := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_riemannXi_le_re_two
  have hshift : ∀ y : ℝ, ((2 : ℂ) + y * I) - 3 = (-1 : ℂ) + y * I := by intro y; ring
  have hφ' : ∀ y : ℝ, ‖φ (((2 : ℂ) + y * I) - 3)‖ ≤ A / (1 + |y|) ^ 3 := by
    intro y
    rw [hshift y]
    exact hφ y
  have hmeas : MeasurableSet {y : ℝ | 2 ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hcont : ContinuousOn (fun y : ℝ =>
      logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I)) {y : ℝ | 2 ≤ |y|} :=
    (continuous_logDeriv_riemannXi_left.mul (hφc.comp (by fun_prop))).continuousOn
  have hdom : Integrable (fun y : ℝ => (2 * C * A) * (1 + y ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hdom.restrict (hcont.aestronglyMeasurable hmeas) ?_
  refine (ae_restrict_iff' hmeas).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have h := norm_vline_integrand_le (f := logDeriv riemannXi) (φ := fun z => φ (z - 3))
    hA hC0 hC hφ' hy
  rw [hshift] at h
  rw [norm_mul, norm_logDeriv_riemannXi_left, ← norm_mul]
  exact h

/-- Off a bounded window, continuity gives the rest: both verticals are integrable on `ℝ`. -/
theorem integrable_of_integrableOn_far {f : ℝ → ℂ} (hc : Continuous f)
    (h : IntegrableOn f {y : ℝ | 2 ≤ |y|}) : Integrable f := by
  have hnear : IntegrableOn f {y : ℝ | |y| < 2} := by
    refine (hc.integrableOn_Icc (a := (-2 : ℝ)) (b := 2)).mono_set ?_
    intro y hy
    have : |y| < 2 := hy
    rw [abs_lt] at this
    exact ⟨this.1.le, this.2.le⟩
  have huniv : {y : ℝ | |y| < 2} ∪ {y : ℝ | 2 ≤ |y|} = Set.univ := by
    ext y; simp [lt_or_ge]
  rw [← integrableOn_univ, ← huniv]
  exact hnear.union h

theorem integrable_vline {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    Integrable fun y : ℝ =>
      logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I) :=
  integrable_of_integrableOn_far
    (continuous_logDeriv_riemannXi_vertical.mul (hφc.comp (by fun_prop)))
    (integrableOn_vertical hA hφc hφ)

theorem integrable_vline_left {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((-1 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    Integrable fun y : ℝ =>
      logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I) :=
  integrable_of_integrableOn_far
    (continuous_logDeriv_riemannXi_left.mul (hφc.comp (by fun_prop)))
    (integrableOn_vline_left hA hφc hφ)

/-! ### The truncated verticals converge to the full-line integrals -/

theorem tendsto_neg_atBot : Filter.Tendsto (fun T : ℝ => -T) Filter.atTop Filter.atBot := by
  refine Filter.tendsto_atBot.mpr fun b => ?_
  filter_upwards [Filter.eventually_ge_atTop (-b)] with T hT
  linarith

theorem tendsto_vline_interval {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    Filter.Tendsto
      (fun T : ℝ => ∫ y in (-T)..T,
        logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
      Filter.atTop
      (nhds (∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral (integrable_vline hA hφc hφ)
    tendsto_neg_atBot Filter.tendsto_id

theorem tendsto_vline_left_interval {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((-1 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    Filter.Tendsto
      (fun T : ℝ => ∫ y in (-T)..T,
        logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I))
      Filter.atTop
      (nhds (∫ y : ℝ, logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral (integrable_vline_left hA hφc hφ)
    tendsto_neg_atBot Filter.tendsto_id

end Cvs.Zeta
