import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Translation is continuous in `L²`

    ∫ (g x − g (x + u))² dx → 0   as   u → 0

for `g` continuous with compact support, by dominated convergence.  Mathlib only.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace Cvs.Upstream.L2TranslationContinuity

/-- **Translation is continuous in `L²` for a continuous function of compact support.** -/
theorem tendsto_integral_sub_translate_sq_of_compactSupport {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun u : ℝ => ∫ x : ℝ, (g x - g (x + u)) ^ 2) (nhds 0) (nhds 0) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hMnn : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0)
  -- the support sits in a bounded interval
  obtain ⟨R0, hR0⟩ := hgc.isBounded.subset_closedBall (0:ℝ)
  set R : ℝ := max R0 0 with hRdef
  have hRnn : (0:ℝ) ≤ R := le_max_right _ _
  have hR : tsupport g ⊆ Metric.closedBall (0:ℝ) R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  -- outside a fixed compact the integrand vanishes for small shifts
  have hzero : ∀ u : ℝ, |u| ≤ 1 → ∀ x : ℝ, x ∉ Set.Icc (-(R+1)) (R+1) →
      (g x - g (x + u)) ^ 2 = 0 := by
    intro u hu x hx
    have hgx : g x = 0 := by
      by_contra hne
      have hmem := hR (subset_tsupport g (Function.mem_support.mpr hne))
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
      have habs := abs_le.mp hmem
      exact hx ⟨by linarith [habs.1], by linarith [habs.2]⟩
    have hgxu : g (x + u) = 0 := by
      by_contra hne
      have hmem := hR (subset_tsupport g (Function.mem_support.mpr hne))
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
      have habs := abs_le.mp hmem
      have huabs := abs_le.mp hu
      exact hx ⟨by linarith [habs.1, huabs.2], by linarith [habs.2, huabs.1]⟩
    rw [hgx, hgxu]
    ring
  set bound : ℝ → ℝ := Set.indicator (Set.Icc (-(R+1)) (R+1)) (fun _ => 4 * M ^ 2) with hbd
  have hbint : Integrable bound (volume : Measure ℝ) := by
    rw [hbd]
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
    refine integrableOn_const (C := 4 * M ^ 2) ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hmain : Tendsto (fun u : ℝ => ∫ x : ℝ, (g x - g (x + u)) ^ 2) (nhds 0)
      (nhds (∫ _x : ℝ, (0:ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbint ?_
    · filter_upwards with u
      exact ((hg.sub (hg.comp (continuous_id.add continuous_const))).pow 2).aestronglyMeasurable
    · filter_upwards [Metric.closedBall_mem_nhds (0:ℝ) one_pos] with u hu
      filter_upwards with x
      have hu1 : |u| ≤ 1 := by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hu
        exact hu
      by_cases hx : x ∈ Set.Icc (-(R+1)) (R+1)
      · rw [hbd, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 : |g x - g (x + u)| ≤ 2 * M := by
          calc |g x - g (x + u)| ≤ |g x| + |g (x + u)| := abs_sub _ _
            _ ≤ M + M := add_le_add (hM x) (hM _)
            _ = 2 * M := by ring
        nlinarith [abs_nonneg (g x - g (x + u)), sq_abs (g x - g (x + u))]
      · rw [hzero u hu1 x hx, hbd, Set.indicator_of_notMem hx]
        simp
    · filter_upwards with x
      have hcont : ContinuousAt (fun u : ℝ => (g x - g (x + u)) ^ 2) 0 := by
        have : Continuous fun u : ℝ => (g x - g (x + u)) ^ 2 :=
          ((continuous_const.sub (hg.comp (continuous_const.add continuous_id))).pow 2)
        exact this.continuousAt
      have h0 : (g x - g (x + 0)) ^ 2 = 0 := by simp
      have h1 := hcont.tendsto
      rwa [h0] at h1
  simpa using hmain

/-! ### From compact support to all of `L²` -/

/-- The `L²` norm of a class, as an integral. -/
theorem norm_toLp_sq {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : ℝ, f x ^ 2 := by
  have hinner : (inner (𝕜 := ℝ) (hf.toLp f) (hf.toLp f) : ℝ) = ∫ x : ℝ, f x ^ 2 := by
    rw [L2.inner_def]
    refine integral_congr_ae (hf.coeFn_toLp.mono fun x hx => ?_)
    simp [hx, sq]
  rw [← hinner, real_inner_self_eq_norm_sq]

/-- The root-mean-square distance obeys the triangle inequality. -/
theorem sqrt_integral_sub_sq_triangle {f g h : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) (hh : MemLp h 2 (volume : Measure ℝ)) :
    Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2)
      ≤ Real.sqrt (∫ x : ℝ, (f x - g x) ^ 2) + Real.sqrt (∫ x : ℝ, (g x - h x) ^ 2) := by
  have key : ∀ {a b : ℝ → ℝ} (ha : MemLp a 2 (volume : Measure ℝ))
      (hb : MemLp b 2 (volume : Measure ℝ)),
      Real.sqrt (∫ x : ℝ, (a x - b x) ^ 2) = ‖ha.toLp a - hb.toLp b‖ := by
    intro a b ha hb
    have hsub : (ha.sub hb).toLp (a - b) = ha.toLp a - hb.toLp b := MemLp.toLp_sub ha hb
    have : ‖ha.toLp a - hb.toLp b‖ ^ 2 = ∫ x : ℝ, (a x - b x) ^ 2 := by
      rw [← hsub, norm_toLp_sq (ha.sub hb)]
      rfl
    rw [← this, Real.sqrt_sq (norm_nonneg _)]
  rw [key hf hh, key hf hg, key hg hh]
  simpa [dist_eq_norm] using dist_triangle (hf.toLp f) (hg.toLp g) (hh.toLp h)

/-- Translating both arguments does not change the distance. -/
theorem integral_sub_sq_translate (f g : ℝ → ℝ) (u : ℝ) :
    (∫ x : ℝ, (f (x + u) - g (x + u)) ^ 2) = ∫ x : ℝ, (f x - g x) ^ 2 :=
  integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ => (f x - g x) ^ 2) u

/-- Translation preserves `L²` membership. -/
theorem memLp_translate {f : ℝ → ℝ} (u : ℝ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (fun x => f (x + u)) 2 (volume : Measure ℝ) :=
  hf.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) u)

/-- **Translation is continuous in `L²`.** -/
theorem tendsto_integral_sub_translate_sq {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    Tendsto (fun u : ℝ => ∫ x : ℝ, (f x - f (x + u)) ^ 2) (nhds 0) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- a continuous compactly supported approximant, within `√ε / 3`
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
        rw [norm_toLp_sq hsub]
        rfl
      rw [← h3, Real.sqrt_sq (norm_nonneg _)]
    rw [h2]; exact h1
  -- the approximant's own translation continuity
  have hcore := tendsto_integral_sub_translate_sq_of_compactSupport hgcont hgc
  rw [Metric.tendsto_nhds] at hcore
  have hrsq : (0:ℝ) < r ^ 2 := by positivity
  filter_upwards [hcore (r ^ 2) hrsq] with u hu
  have hgu : Real.sqrt (∫ x : ℝ, (g x - g (x + u)) ^ 2) ≤ r := by
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)] at hu
    calc Real.sqrt (∫ x : ℝ, (g x - g (x + u)) ^ 2) ≤ Real.sqrt (r ^ 2) :=
          Real.sqrt_le_sqrt hu.le
      _ = r := Real.sqrt_sq hrpos.le
  -- three pieces
  have hfu := memLp_translate u hf
  have hgum := memLp_translate u hgmem
  have hlast : Real.sqrt (∫ x : ℝ, (g (x + u) - f (x + u)) ^ 2) ≤ r := by
    rw [integral_sub_sq_translate g f u]
    have hcomm : (∫ x : ℝ, (g x - f x) ^ 2) = ∫ x : ℝ, (f x - g x) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hcomm]; exact hd
  have htri : Real.sqrt (∫ x : ℝ, (f x - f (x + u)) ^ 2) ≤ 3 * r := by
    have h1 := sqrt_integral_sub_sq_triangle hf hgmem hfu
    have h2 := sqrt_integral_sub_sq_triangle hgmem hgum hfu
    have h3 : Real.sqrt (∫ x : ℝ, (g x - f (x + u)) ^ 2)
        ≤ Real.sqrt (∫ x : ℝ, (g x - g (x + u)) ^ 2)
          + Real.sqrt (∫ x : ℝ, (g (x + u) - f (x + u)) ^ 2) := h2
    linarith
  have hfinal : (∫ x : ℝ, (f x - f (x + u)) ^ 2) ≤ (3 * r) ^ 2 := by
    have hnn : 0 ≤ ∫ x : ℝ, (f x - f (x + u)) ^ 2 := integral_nonneg fun x => sq_nonneg _
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ x : ℝ, (f x - f (x + u)) ^ 2), htri,
      hrpos.le]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
  have h3r : (3 * r) ^ 2 = 9 * ε / 16 := by
    rw [hr]
    have : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
    field_simp
    nlinarith [this]
  calc (∫ x : ℝ, (f x - f (x + u)) ^ 2) ≤ (3 * r) ^ 2 := hfinal
    _ = 9 * ε / 16 := h3r
    _ < ε := by linarith
  
end Cvs.Upstream.L2TranslationContinuity
