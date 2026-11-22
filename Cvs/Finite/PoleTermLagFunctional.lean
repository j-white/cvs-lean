import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-!
# The pole term as a lag functional, for bounded functions supported in the window

`(∫ f e^{cs})(∫ f e^{−cs}) = ∫ e^{−cx}·(f ⋆ f)(x) dx` for `f` measurable, bounded, supported in
`(0, L]` — Fubini and one change of variables, with no continuity.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.PoleTermLagFunctional

variable {L : ℝ} {f : ℝ → ℝ}

/-- A bounded function supported in the window, times an exponential, is integrable. -/
theorem integrable_mul_exp (hL : 0 < L) (c : ℝ) (hm : Measurable f) {C : ℝ}
    (hb : ∀ s, |f s| ≤ C) (hsupp : ∀ s, s ∉ Ioc (0:ℝ) L → f s = 0) :
    Integrable (fun s => f s * Real.exp (c * s)) (volume : Measure ℝ) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
  have hbd : ∀ s, ‖f s * Real.exp (c * s)‖
      ≤ Set.indicator (Ioc (0:ℝ) L) (fun _ => C * Real.exp (|c| * L)) s := by
    intro s
    by_cases hs : s ∈ Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : Real.exp (c * s) ≤ Real.exp (|c| * L) := by
        apply Real.exp_le_exp.mpr
        calc c * s ≤ abs (c * s) := le_abs_self _
          _ = |c| * |s| := abs_mul _ _
          _ ≤ |c| * L := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
              rw [abs_of_pos hs.1]; exact hs.2
      exact mul_le_mul (hb s) h1 (Real.exp_pos _).le hC
    · rw [Set.indicator_of_notMem hs, hsupp s hs]; simp
  refine Integrable.mono' (g := Set.indicator (Ioc (0:ℝ) L) (fun _ => C * Real.exp (|c| * L)))
    ((integrable_indicator_iff measurableSet_Ioc).mpr
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)))
    (hm.mul (by fun_prop : Measurable fun s : ℝ => Real.exp (c * s))).aestronglyMeasurable
    (Filter.Eventually.of_forall hbd)

/-- The two-variable integrand `f(s)·f(s−x)·e^{cx}` is integrable on the plane. -/
theorem integrable_lag_prod (hL : 0 < L) (c : ℝ) (hm : Measurable f) {C : ℝ}
    (hb : ∀ s, |f s| ≤ C) (hsupp : ∀ s, s ∉ Ioc (0:ℝ) L → f s = 0) :
    Integrable (fun p : ℝ × ℝ => f p.1 * f (p.1 - p.2) * Real.exp (c * p.2))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
  have hbd : ∀ p : ℝ × ℝ, ‖f p.1 * f (p.1 - p.2) * Real.exp (c * p.2)‖
      ≤ Set.indicator ((Ioc (0:ℝ) L) ×ˢ (Ioo (-L) L)) (fun _ => C * C * Real.exp (|c| * L)) p := by
    intro p
    by_cases hs : p.1 ∈ Ioc (0:ℝ) L
    · by_cases ht : p.1 - p.2 ∈ Ioc (0:ℝ) L
      · have hx : p.2 ∈ Ioo (-L) L := ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
        rw [Set.indicator_of_mem (Set.mk_mem_prod hs hx), Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos (Real.exp_pos _)]
        have h1 : Real.exp (c * p.2) ≤ Real.exp (|c| * L) := by
          apply Real.exp_le_exp.mpr
          calc c * p.2 ≤ abs (c * p.2) := le_abs_self _
            _ = |c| * |p.2| := abs_mul _ _
            _ ≤ |c| * L := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
                exact abs_le.mpr ⟨by linarith [hx.1], hx.2.le⟩
        exact mul_le_mul (mul_le_mul (hb _) (hb _) (abs_nonneg _) hC) h1 (Real.exp_pos _).le
          (by positivity)
      · rw [hsupp _ ht]; simp
        exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · rw [hsupp _ hs]; simp
      exact Set.indicator_nonneg (fun _ _ => by positivity) _
  refine Integrable.mono' (g := Set.indicator ((Ioc (0:ℝ) L) ×ˢ (Ioo (-L) L))
      (fun _ => C * C * Real.exp (|c| * L)))
    ((integrable_indicator_iff (measurableSet_Ioc.prod measurableSet_Ioo)).mpr
      (integrableOn_const (hs := by
        rw [Measure.prod_prod]
        exact (ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioo_lt_top).ne))) ?_
    (Filter.Eventually.of_forall hbd)
  exact ((hm.comp measurable_fst).mul (hm.comp (measurable_fst.sub measurable_snd))).mul
    (by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (c * p.2)) |>.aestronglyMeasurable

/-- **The pairing of the two exponential moments is the lag integral of the self-convolution.** -/
theorem pairing_exp_bounded (hL : 0 < L) (c : ℝ) (hm : Measurable f) {C : ℝ}
    (hb : ∀ s, |f s| ≤ C) (hsupp : ∀ s, s ∉ Ioc (0:ℝ) L → f s = 0) :
    (∫ s : ℝ, f s * Real.exp (c * s)) * (∫ s : ℝ, f s * Real.exp (-(c * s)))
      = ∫ x : ℝ, Real.exp (-(c * x)) * selfConvolution f x := by
  have hf1 := integrable_mul_exp hL c hm hb hsupp
  have hf2 : Integrable (fun s => f s * Real.exp (-(c * s))) (volume : Measure ℝ) := by
    have := integrable_mul_exp hL (-c) hm hb hsupp
    simpa [neg_mul] using this
  -- the product of the two integrals is a double integral
  rw [← integral_prod_mul, integral_prod _ (Integrable.mul_prod hf1 hf2)]
  -- inner change of variables `t = s − x`
  have hinner : ∀ s : ℝ, (∫ t : ℝ, f s * Real.exp (c * s) * (f t * Real.exp (-(c * t))))
      = ∫ x : ℝ, f s * f (s - x) * Real.exp (c * x) := by
    intro s
    rw [← integral_sub_left_eq_self (fun t => f s * Real.exp (c * s) * (f t * Real.exp (-(c * t)))) volume s]
    congr 1; funext x
    rw [show -(c * (s - x)) = c * x - c * s by ring, Real.exp_sub]
    field_simp
  simp_rw [hinner]
  -- swap the order
  rw [integral_integral_swap (integrable_lag_prod hL c hm hb hsupp)]
  -- the inner integral is the self-convolution at `−x`
  have hconv : ∀ x : ℝ, (∫ s : ℝ, f s * f (s - x) * Real.exp (c * x))
      = Real.exp (c * x) * selfConvolution f (-x) := by
    intro x
    unfold selfConvolution
    rw [← integral_const_mul]
    congr 1; funext s
    rw [show s + -x = s - x by ring]; ring
  simp_rw [hconv]
  rw [← integral_neg_eq_self _ volume]
  congr 1; funext x
  simp

end Cvs.Finite.PoleTermLagFunctional
