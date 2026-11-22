import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Cvs.Upstream.L2TranslationContinuity

/-!
# Dilation is continuous in `L²`

    ∫ (a^{−1/2}·f (x/a) − f x)² dx → 0   as   a → 1

The normalised dilation is an isometry of `L²`, so only a continuous compactly supported
function needs an argument, and there dominated convergence settles it.  Mathlib only.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace Cvs.Upstream.L2DilationContinuity

/-- The normalised dilation. -/
def dilate (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => (Real.sqrt a)⁻¹ * f (x / a)

/-- **The normalised dilation preserves the energy.** -/
theorem integral_dilate_sq {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ x : ℝ, dilate a f x ^ 2) = ∫ x : ℝ, f x ^ 2 := by
  have hcomp := MeasureTheory.Measure.integral_comp_div (fun t : ℝ => f t ^ 2) a
  rw [abs_of_pos ha, smul_eq_mul] at hcomp
  have hexp : ∀ x : ℝ, dilate a f x ^ 2 = (Real.sqrt a)⁻¹ ^ 2 * f (x / a) ^ 2 := by
    intro x; rw [dilate]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_const_mul, hcomp,
    inv_pow, Real.sq_sqrt ha.le]
  field_simp

/-- **The dilation is linear, so it preserves distances.** -/
theorem integral_dilate_sub_sq {a : ℝ} (ha : 0 < a) (f g : ℝ → ℝ) :
    (∫ x : ℝ, (dilate a f x - dilate a g x) ^ 2) = ∫ x : ℝ, (f x - g x) ^ 2 := by
  have hrw : ∀ x : ℝ, (dilate a f x - dilate a g x) ^ 2
      = dilate a (fun t => f t - g t) x ^ 2 := by
    intro x; rw [dilate, dilate, dilate]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw), integral_dilate_sq ha]

/-- **A dilate of an `L²` function is `L²`.** -/
theorem memLp_dilate {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (dilate a f) 2 (volume : Measure ℝ) := by
  have hqmp : QuasiMeasurePreserving (fun x : ℝ => x / a)
      (volume : Measure ℝ) (volume : Measure ℝ) := by
    refine ⟨(measurable_id.div_const a).aemeasurable, ?_⟩
    have hfun : (fun x : ℝ => x / a) = fun x : ℝ => a⁻¹ * x := by
      funext x; rw [div_eq_inv_mul]
    rw [hfun, Real.map_volume_mul_left (inv_ne_zero ha.ne')]
    exact Measure.smul_absolutelyContinuous
  have hbase : MemLp (fun x : ℝ => f (x / a)) 2 (volume : Measure ℝ) := by
    have hmeasA : AEStronglyMeasurable (fun x : ℝ => f (x / a)) (volume : Measure ℝ) :=
      hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
    refine (memLp_two_iff_integrable_sq hmeasA).mpr ?_
    exact (hf.integrable_sq).comp_div ha.ne'
  exact hbase.const_mul _

/-- **Dilation is continuous in `L²` for a continuous function of compact support.** -/
theorem tendsto_integral_sub_dilate_sq_of_compactSupport {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun a : ℝ => ∫ x : ℝ, (dilate a g x - g x) ^ 2)
      (nhdsWithin 1 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hMnn : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0)
  obtain ⟨R0, hR0⟩ := hgc.isBounded.subset_closedBall (0:ℝ)
  set R : ℝ := max R0 0 with hRdef
  have hRnn : (0:ℝ) ≤ R := le_max_right _ _
  have hR : tsupport g ⊆ Metric.closedBall (0:ℝ) R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hsupp : ∀ x : ℝ, g x ≠ 0 → |x| ≤ R := by
    intro x hne
    have hmem := hR (subset_tsupport g (Function.mem_support.mpr hne))
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
  -- outside a fixed compact the integrand vanishes for dilations near one
  have hzero : ∀ a : ℝ, 0 < a → a ≤ 2 → ∀ x : ℝ, x ∉ Set.Icc (-(2 * R)) (2 * R) →
      (dilate a g x - g x) ^ 2 = 0 := by
    intro a ha0 ha2 x hx
    have hgx : g x = 0 := by
      by_contra hne
      have h := abs_le.mp (hsupp x hne)
      exact hx ⟨by linarith [h.1], by linarith [h.2]⟩
    have hgxa : g (x / a) = 0 := by
      by_contra hne
      have h := abs_le.mp (hsupp (x / a) hne)
      have h1 : x / a * a = x := div_mul_cancel₀ x ha0.ne'
      have h2 : -(R * a) ≤ x := by nlinarith [h.1, ha0, h1]
      have h3 : x ≤ R * a := by nlinarith [h.2, ha0, h1]
      exact hx ⟨by nlinarith [h2, hRnn, ha2], by nlinarith [h3, hRnn, ha2]⟩
    rw [dilate, hgx, hgxa]
    ring
  set bound : ℝ → ℝ := Set.indicator (Set.Icc (-(2 * R)) (2 * R)) (fun _ => 9 * M ^ 2) with hbd
  have hbint : Integrable bound (volume : Measure ℝ) := by
    rw [hbd]
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
    refine integrableOn_const (C := 9 * M ^ 2) ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hmain : Tendsto (fun a : ℝ => ∫ x : ℝ, (dilate a g x - g x) ^ 2)
      (nhdsWithin 1 (Set.Ioi 0)) (nhds (∫ _x : ℝ, (0:ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbint ?_
    · filter_upwards [self_mem_nhdsWithin] with a ha
      have hcont : Continuous (fun x : ℝ => (dilate a g x - g x) ^ 2) := by
        have h1 : Continuous fun x : ℝ => g (x / a) :=
          hg.comp (continuous_id.div_const a)
        exact (((continuous_const.mul h1).sub hg).pow 2)
      exact hcont.aestronglyMeasurable
    · filter_upwards [mem_nhdsWithin_of_mem_nhds
        (Ioo_mem_nhds (by norm_num : (1:ℝ)/2 < 1) (by norm_num : (1:ℝ) < 2))] with a ha
      have ha0 : (0:ℝ) < a := by linarith [ha.1]
      have ha2 : a ≤ 2 := le_of_lt ha.2
      have hinv : (Real.sqrt a)⁻¹ ≤ 2 := by
        have hhalf : (1:ℝ)/2 ≤ Real.sqrt a := by
          rw [show (1:ℝ)/2 = Real.sqrt ((1/2)^2) by rw [Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by nlinarith [ha.1])
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      filter_upwards with x
      by_cases hx : x ∈ Set.Icc (-(2 * R)) (2 * R)
      · rw [hbd, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hgx := hM x
        have hgxa := hM (x / a)
        rw [Real.norm_eq_abs] at hgx hgxa
        have hsqrtnn : 0 ≤ (Real.sqrt a)⁻¹ := by positivity
        have h1 : |dilate a g x - g x| ≤ 3 * M := by
          have hd : |dilate a g x| ≤ 2 * M := by
            rw [dilate, abs_mul, abs_of_nonneg hsqrtnn]
            nlinarith [hgxa, hsqrtnn, hinv, abs_nonneg (g (x / a))]
          calc |dilate a g x - g x| ≤ |dilate a g x| + |g x| := abs_sub _ _
            _ ≤ 2 * M + M := add_le_add hd hgx
            _ = 3 * M := by ring
        nlinarith [abs_nonneg (dilate a g x - g x), sq_abs (dilate a g x - g x), hMnn]
      · rw [hzero a ha0 ha2 x hx, hbd, Set.indicator_of_notMem hx]
        simp
    · filter_upwards with x
      have hcont : Tendsto (fun a : ℝ => (dilate a g x - g x) ^ 2) (nhds (1:ℝ))
          (nhds ((dilate 1 g x - g x) ^ 2)) := by
        have hs : ContinuousAt (fun a : ℝ => (Real.sqrt a)⁻¹) 1 := by
          refine ContinuousAt.inv₀ (Real.continuous_sqrt.continuousAt) ?_
          simp
        have hq : ContinuousAt (fun a : ℝ => g (x / a)) 1 := by
          refine hg.continuousAt.comp ?_
          exact ContinuousAt.div continuousAt_const continuousAt_id one_ne_zero
        exact (((hs.mul hq).sub continuousAt_const).pow 2).tendsto
      have h0 : (dilate 1 g x - g x) ^ 2 = 0 := by
        rw [dilate]; simp
      rw [h0] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
  simpa using hmain

/-- **Dilation is continuous in `L²`.** -/
theorem tendsto_integral_sub_dilate_sq {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    Tendsto (fun a : ℝ => ∫ x : ℝ, (dilate a f x - f x) ^ 2)
      (nhdsWithin 1 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set r : ℝ := Real.sqrt ε / 4 with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  obtain ⟨g, hgc, hgle, hgcont, hgmem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by norm_num)
      (ε := ENNReal.ofReal r) (ENNReal.ofReal_ne_zero_iff.mpr hrpos)
  have hd : Real.sqrt (∫ x : ℝ, (f x - g x) ^ 2) ≤ r := by
    have hsub : MemLp (f - g) 2 (volume : Measure ℝ) := hf.sub hgmem
    have hnorm : ‖hsub.toLp (f - g)‖ = (eLpNorm (f - g) 2 (volume : Measure ℝ)).toReal :=
      MeasureTheory.Lp.norm_toLp (f - g) hsub
    have h1 : ‖hsub.toLp (f - g)‖ ≤ r := by
      rw [hnorm]
      have := ENNReal.toReal_mono (by simp) hgle
      simpa [ENNReal.toReal_ofReal hrpos.le] using this
    have h2 : Real.sqrt (∫ x : ℝ, (f x - g x) ^ 2) = ‖hsub.toLp (f - g)‖ := by
      have h3 : ‖hsub.toLp (f - g)‖ ^ 2 = ∫ x : ℝ, (f x - g x) ^ 2 := by
        rw [Cvs.Upstream.L2TranslationContinuity.norm_toLp_sq hsub]
        rfl
      rw [← h3, Real.sqrt_sq (norm_nonneg _)]
    rw [h2]; exact h1
  have hcore := tendsto_integral_sub_dilate_sq_of_compactSupport hgcont hgc
  rw [Metric.tendsto_nhds] at hcore
  have hrsq : (0:ℝ) < r ^ 2 := by positivity
  filter_upwards [hcore (r ^ 2) hrsq, self_mem_nhdsWithin] with a hu ha
  have ha0 : (0:ℝ) < a := ha
  have hga : Real.sqrt (∫ x : ℝ, (dilate a g x - g x) ^ 2) ≤ r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)] at hu
    calc Real.sqrt (∫ x : ℝ, (dilate a g x - g x) ^ 2) ≤ Real.sqrt (r ^ 2) :=
          Real.sqrt_le_sqrt hu.le
      _ = r := Real.sqrt_sq hrpos.le
  have hfa := memLp_dilate ha0 hf
  have hgam := memLp_dilate ha0 hgmem
  have hfirst : Real.sqrt (∫ x : ℝ, (dilate a f x - dilate a g x) ^ 2) ≤ r := by
    rw [integral_dilate_sub_sq ha0]
    exact hd
  have htri : Real.sqrt (∫ x : ℝ, (dilate a f x - f x) ^ 2) ≤ 3 * r := by
    have h1 := Cvs.Upstream.L2TranslationContinuity.sqrt_integral_sub_sq_triangle hfa hgam hf
    have h2 := Cvs.Upstream.L2TranslationContinuity.sqrt_integral_sub_sq_triangle hgam hgmem hf
    have h3 : Real.sqrt (∫ x : ℝ, (g x - f x) ^ 2) ≤ r := by
      have hcomm : (∫ x : ℝ, (g x - f x) ^ 2) = ∫ x : ℝ, (f x - g x) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [hcomm]; exact hd
    linarith
  have hfinal : (∫ x : ℝ, (dilate a f x - f x) ^ 2) ≤ (3 * r) ^ 2 := by
    have hnn : 0 ≤ ∫ x : ℝ, (dilate a f x - f x) ^ 2 := integral_nonneg fun x => sq_nonneg _
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ x : ℝ, (dilate a f x - f x) ^ 2), htri,
      hrpos.le]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
  have h3r : (3 * r) ^ 2 = 9 * ε / 16 := by
    rw [hr]
    have : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
    field_simp
    nlinarith [this]
  calc (∫ x : ℝ, (dilate a f x - f x) ^ 2) ≤ (3 * r) ^ 2 := hfinal
    _ = 9 * ε / 16 := h3r
    _ < ε := by linarith

end Cvs.Upstream.L2DilationContinuity
