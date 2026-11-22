import Mathlib
import Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount
import Cvs.Prolate.LiouvilleGreen.TurningLayerZeros
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungDepthBound
import Cvs.Prolate.TopRungZeroSplitHalf

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Weyl zero count on `(α, 1)` at level `c²v`, with error `O(log c)`

Cut the allowed interval where `pq = 1`: Liouville–Green counts the zeros before the cut to within
`½ log a(α) ≤ ¼ log(c²V)`, the layer after it holds at most `1 + log(8c²V)/(2√2)` zeros, the edge `[1 − η, 1]`,
`η = 1/(4c²V)`, and the forbidden region hold none, and the phase integral misses at most `½ log(8c²V) + 1`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)
open Cvs.Prolate.TopRungDepthBound (af qf Lf)
open Cvs.Prolate.TopRungZeroSplitHalf (ZerosOn)

namespace Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog
open Cvs.ZeroCounting

/-! ### Elementary integrals -/

/-- `∫_a^b dt/(1 − t²) ≤ ½ log(2/η)` for `0 ≤ a ≤ b ≤ 1 − η`, `0 < η ≤ 1`. -/
theorem integral_inv_p_le {a b η : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 - η) (hη : 0 < η) :
    ∫ t in a..b, 1 / (1 - t ^ 2) ≤ log (2 / η) / 2 := by
  have hreg : ∀ t ∈ Icc 0 (1 - η), t ^ 2 < 1 := fun t ht => by nlinarith [ht.1, ht.2]
  have hpi : ∀ u w : ℝ, 0 ≤ u → u ≤ w → w ≤ 1 - η → IntervalIntegrable (fun s => 1 / (1 - s ^ 2)) volume u w :=
    fun u w hu huw hw => ContinuousOn.intervalIntegrable_of_Icc huw
      (ContinuousOn.div (f := fun _ => (1 : ℝ)) (g := fun s => 1 - s ^ 2) continuousOn_const
      (by fun_prop) fun s hs => by nlinarith [hs.1, hs.2])
  have hmono : ∫ t in a..b, 1 / (1 - t ^ 2) ≤ ∫ t in (0 : ℝ)..(1 - η), 1 / (1 - t ^ 2) :=
    intervalIntegral.integral_mono_interval ha hab hb (by
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      have : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      simp only [Pi.zero_apply]; positivity) (hpi 0 (1 - η) le_rfl (by linarith) le_rfl)
  have hft : ∫ t in (0 : ℝ)..(1 - η), 1 / (1 - t ^ 2) = Lf (1 - η) - Lf 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => Cvs.Prolate.TopRungDepthBound.hasDerivAt_Lf (hreg t (by
      rwa [uIcc_of_le (by linarith)] at ht))) (hpi 0 (1 - η) le_rfl (by linarith) le_rfl)
  have hL0 : Lf 0 = 0 := by simp [Lf]
  have hL : Lf (1 - η) ≤ log (2 / η) / 2 := by
    unfold Lf
    rw [show (1 : ℝ) - (1 - η) = η by ring, Real.log_div (by norm_num) hη.ne']
    have := Real.log_le_log (by linarith) (show 1 + (1 - η) ≤ 2 by linarith)
    linarith
  linarith

/-- `∫_{1−η}^1 dt/√(1 − t) = 2√η`. -/
theorem integral_inv_sqrt_one_sub {η : ℝ} (hη : 0 ≤ η) :
    ∫ t in (1 - η)..1, 1 / √(1 - t) = 2 * √η := by
  have hd : ∀ t ∈ Ioo (1 - η) 1, HasDerivAt (fun t => -(2 * √(1 - t))) (1 / √(1 - t)) t := fun t ht => by
    have h1 : 0 < 1 - t := by linarith [ht.2]
    have := (((hasDerivAt_id t).const_sub 1).sqrt h1.ne').const_mul 2 |>.neg
    refine this.congr_deriv ?_
    have hs : 0 < √(1 - t) := Real.sqrt_pos.mpr h1
    simp only [id]
    field_simp
  have hc : ContinuousOn (fun t => -(2 * √(1 - t))) (Icc (1 - η) 1) := by fun_prop
  have hi := intervalIntegral.integrableOn_deriv_of_nonneg hc hd (fun t ht => by
    have : 0 < √(1 - t) := Real.sqrt_pos.mpr (by linarith [ht.2])
    positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hc hd
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr hi)]
  simp

/-! ### The level `c²v` -/

section Level

variable {c v : ℝ}

/-- `pq = (1 − t²)(c²v − c²t²)` is antitone on `[0, min(√v, 1)]`. -/
theorem pq_anti (hv : 0 ≤ v) :
    AntitoneOn (fun t : ℝ => (1 - t ^ 2) * (c ^ 2 * v - c ^ 2 * t ^ 2)) (Icc 0 (min √v 1)) := by
  intro t ht t' ht' htt
  have hv' : ∀ s ∈ Icc 0 (min √v 1), s ^ 2 ≤ v ∧ s ^ 2 ≤ 1 := fun s hs => by
    have h1 : s ≤ √v := hs.2.trans (min_le_left _ _)
    have h2 : s ≤ 1 := hs.2.trans (min_le_right _ _)
    exact ⟨by nlinarith [Real.sq_sqrt hv, hs.1], by nlinarith [hs.1]⟩
  obtain ⟨a1, a2⟩ := hv' t ht
  obtain ⟨b1, b2⟩ := hv' t' ht'
  have hsq : t ^ 2 ≤ t' ^ 2 := pow_le_pow_left₀ ht.1 htt 2
  simp only
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have e : ∀ s : ℝ, c ^ 2 * v - c ^ 2 * s ^ 2 = c ^ 2 * (v - s ^ 2) := fun s => by ring
  rw [e, e]
  exact mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (by linarith) hc2)
    (mul_nonneg hc2 (by linarith)) (by linarith)

/-- Once `pq ≤ 1` at `β ≥ 0`, it stays `≤ 1` on `[β, 1]`. -/
theorem pq_le_one {β : ℝ} (hv : 0 ≤ v) (hβ : 0 ≤ β) (hβ1 : (1 - β ^ 2) * (c ^ 2 * v - c ^ 2 * β ^ 2) ≤ 1) :
    ∀ t ∈ Icc β 1, (1 - t ^ 2) * (c ^ 2 * v - c ^ 2 * t ^ 2) ≤ 1 := by
  intro t ht
  have hp : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  rcases eq_or_ne c 0 with h0 | h0
  · subst h0; simp
  by_cases hq : 0 ≤ c ^ 2 * v - c ^ 2 * t ^ 2
  · have hc2 : 0 < c ^ 2 := by positivity
    have htv : t ≤ √v := by
      rw [Real.le_sqrt (hβ.trans ht.1) hv]
      nlinarith
    have hmem : t ∈ Icc 0 (min √v 1) := ⟨hβ.trans ht.1, le_min htv ht.2⟩
    have hmemβ : β ∈ Icc 0 (min √v 1) := ⟨hβ, le_min (ht.1.trans htv) (ht.1.trans ht.2)⟩
    exact (pq_anti hv hmemβ hmem ht.1).trans hβ1
  · push Not at hq
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hp hq.le]

theorem qf_eq (c v t : ℝ) : qf c (c * (1 - v)) t = c ^ 2 * v - c ^ 2 * t ^ 2 := by unfold qf; ring

theorem level_eq (c v : ℝ) : c ^ 2 - c * (1 - v) * c = c ^ 2 * v := by ring

/-- The Liouville–Green frequency is the Weyl integrand: `a/(1 − t²) = c√((v − t²)₊/(1 − t²))`. -/
theorem omega_eq {c v t : ℝ} (hc : 0 ≤ c) (ht : t ^ 2 < 1) :
    af c (c * (1 - v)) t / (1 - t ^ 2) = c * √((v - t ^ 2) / (1 - t ^ 2)) := by
  have hp : 0 < 1 - t ^ 2 := by linarith
  unfold af
  rw [qf_eq]
  have e : (1 - t ^ 2) * (c ^ 2 * v - c ^ 2 * t ^ 2) = (1 - t ^ 2) ^ 2 * (c ^ 2 * ((v - t ^ 2) / (1 - t ^ 2))) := by
    field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le, Real.sqrt_mul (by positivity), Real.sqrt_sq hc]
  field_simp

/-- **No zeros past `min(√v, 1 − η)`**, `η = 1/(4c²V)`, for `0 ≤ v ≤ V`, `1 ≤ V`, `c ≠ 0`. -/
theorem no_zero_beyond {c v V : ℝ} (hc1 : 1 ≤ c) (hv : 0 ≤ v) (hvV : v ≤ V) (hV : 1 ≤ V) :
    ∀ t ∈ Icc (min √v (1 - 1 / (4 * c ^ 2 * V))) 1, regSol (sqC c) (c ^ 2 * v) t ≠ 0 := by
  intro t ht
  have hc : c ≠ 0 := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hc21 : 1 ≤ c ^ 2 := by nlinarith
  set η := 1 / (4 * c ^ 2 * V) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  by_cases h1 : 1 - η ≤ t
  · refine (Cvs.Prolate.LiouvilleGreen.TurningLayerZeros.regSol_pos_near_one (c := c) (χ := c ^ 2 * v) (Q₀ := c ^ 2 * V) hη0.le hη1
      (fun s hs => ?_) ?_ t ⟨h1, ht.2⟩).ne'
    · have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
      rw [← mul_sub, abs_mul, abs_of_pos hc2]
      refine mul_le_mul_of_nonneg_left ?_ hc2.le
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg s]
    · rw [hη]; field_simp; norm_num
  · push Not at h1
    have htv : √v ≤ t := by
      rcases min_choice √v (1 - η) with h | h
      · rw [h] at ht; exact ht.1
      · rw [h] at ht; linarith [ht.1]
    exact Cvs.Prolate.LiouvilleGreen.TurningLayerZeros.regSol_ne_zero_forbidden (c := c) (χ := c ^ 2 * v) (Real.sqrt_nonneg v)
      (by rw [Real.sq_sqrt hv]) t ⟨htv, ht.2⟩

/-- `1/√(1 − t)` is integrable on `[1 − η, 1]`. -/
theorem intervalIntegrable_inv_sqrt_one_sub {η : ℝ} (hη : 0 ≤ η) :
    IntervalIntegrable (fun t => 1 / √(1 - t)) volume (1 - η) 1 := by
  have hd : ∀ t ∈ Ioo (1 - η) 1, HasDerivAt (fun t => -(2 * √(1 - t))) (1 / √(1 - t)) t := fun t ht => by
    have h1 : 0 < 1 - t := by linarith [ht.2]
    have := (((hasDerivAt_id t).const_sub 1).sqrt h1.ne').const_mul 2 |>.neg
    refine this.congr_deriv ?_
    have hs : 0 < √(1 - t) := Real.sqrt_pos.mpr h1
    simp only [id]
    field_simp
  have hc : ContinuousOn (fun t => -(2 * √(1 - t))) (Icc (1 - η) 1) := by fun_prop
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
    (intervalIntegral.integrableOn_deriv_of_nonneg hc hd (fun t ht => by
      have : 0 < √(1 - t) := Real.sqrt_pos.mpr (by linarith [ht.2])
      positivity))

/-- **The phase integral past a point with `pq ≤ 1`**: `c∫_β^1 √((v − t²)₊/(1 − t²)) ≤ ½ log(8c²V) + 1`. -/
theorem tail_le {c v V β : ℝ} (hc1 : 1 ≤ c) (hvV : v ≤ V) (hV : 1 ≤ V) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpq : ∀ t ∈ Icc β 1, (1 - t ^ 2) * (c ^ 2 * v - c ^ 2 * t ^ 2) ≤ 1) :
    IntervalIntegrable (fun t => √((v - t ^ 2) / (1 - t ^ 2))) volume β 1 ∧
      c * ∫ t in β..1, √((v - t ^ 2) / (1 - t ^ 2)) ≤ log (8 * c ^ 2 * V) / 2 + 1 := by
  have hc : 0 < c := by linarith
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  set g : ℝ → ℝ := fun t => √((v - t ^ 2) / (1 - t ^ 2)) with hg
  set η := 1 / (4 * c ^ 2 * V) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by rw [hη, div_le_one (by positivity)]; nlinarith
  set b := max β (1 - η) with hb
  have hβb : β ≤ b := le_max_left _ _
  have hb1 : b ≤ 1 := max_le hβ1 (by linarith)
  have hbη : 1 - η ≤ b := le_max_right _ _
  -- the two pointwise bounds
  have hp1 : ∀ t ∈ Icc β 1, t < 1 → c * g t ≤ 1 / (1 - t ^ 2) := fun t ht ht1 => by
    have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1]
    have e : c * g t = √((c ^ 2 * v - c ^ 2 * t ^ 2) / (1 - t ^ 2)) := by
      rw [hg]; simp only
      rw [show (c ^ 2 * v - c ^ 2 * t ^ 2) / (1 - t ^ 2) = c ^ 2 * ((v - t ^ 2) / (1 - t ^ 2)) by ring,
        Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
    rw [e, Real.sqrt_le_left (by positivity)]
    have h := hpq t ht
    rcases le_total (c ^ 2 * v - c ^ 2 * t ^ 2) 0 with hq | hq
    · exact (div_nonpos_of_nonpos_of_nonneg hq hp.le).trans (by positivity)
    · rw [div_le_iff₀ hp, div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      nlinarith
  have hp2 : ∀ t ∈ Icc (1 - η) 1, t < 1 → g t ≤ √V * (1 / √(1 - t)) := fun t ht ht1 => by
    have h1t : 0 < 1 - t := by linarith
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hp : 0 < 1 - t ^ 2 := by nlinarith
    have hpt : 1 - t ≤ 1 - t ^ 2 := by nlinarith
    rw [hg, mul_one_div, ← Real.sqrt_div' V h1t.le]
    refine Real.sqrt_le_sqrt ?_
    rcases le_total (v - t ^ 2) 0 with hq | hq
    · exact (div_nonpos_of_nonpos_of_nonneg hq hp.le).trans (by positivity)
    · exact div_le_div₀ (by linarith) (by nlinarith [sq_nonneg t]) h1t hpt
  have hmeas : Measurable g := by rw [hg]; fun_prop
  have hgnn : ∀ t, 0 ≤ g t := fun t => Real.sqrt_nonneg _
  -- integrability
  have hi1 : IntervalIntegrable g volume β b := by
    rcases eq_or_lt_of_le hβb with h | h
    · rw [← h]
    · have hb' : b = 1 - η := by
        rcases max_choice β (1 - η) with h' | h'
        · rw [hb, h'] at h; exact absurd h (lt_irrefl _)
        · rw [hb, h']
      refine ContinuousOn.intervalIntegrable_of_Icc hβb ?_
      intro t ht
      have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2, hb']
      exact (ContinuousAt.sqrt ((by fun_prop : ContinuousAt (fun t : ℝ => v - t ^ 2) t).div (by fun_prop)
        hp.ne')).continuousWithinAt
  have hmaj := (intervalIntegrable_inv_sqrt_one_sub hη0.le).const_mul √V
  have hi2 : IntervalIntegrable g volume b 1 := by
    have hsub : IntervalIntegrable (fun t => √V * (1 / √(1 - t))) volume b 1 :=
      hmaj.mono_set (by rw [uIcc_of_le hb1, uIcc_of_le (by linarith)]; exact Icc_subset_Icc hbη le_rfl)
    refine hsub.mono_fun' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hb1] at ht
    show ‖g t‖ ≤ √V * (1 / √(1 - t))
    rw [Real.norm_eq_abs, abs_of_nonneg (hgnn t)]
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1]; simp [hg]
    · exact hp2 t ⟨hbη.trans ht.1.le, ht.2⟩ h1
  refine ⟨hi1.trans hi2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, mul_add]
  -- the first piece
  have e1 : c * ∫ t in β..b, g t ≤ log (2 / η) / 2 := by
    rcases eq_or_lt_of_le hβb with h | h
    · rw [← h, intervalIntegral.integral_same, mul_zero]
      exact div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)) (by norm_num)
    · have hb' : b = 1 - η := by
        rcases max_choice β (1 - η) with h' | h'
        · rw [hb, h'] at h; exact absurd h (lt_irrefl _)
        · rw [hb, h']
      rw [← intervalIntegral.integral_const_mul]
      refine le_trans (intervalIntegral.integral_mono_on hβb (hi1.const_mul c)
        (ContinuousOn.intervalIntegrable_of_Icc hβb (ContinuousOn.div continuousOn_const (by fun_prop)
          fun s hs => by nlinarith [hs.1, hs.2, hb'])) fun t ht => hp1 t ⟨ht.1, ht.2.trans hb1⟩ (by
          linarith [ht.2, hb'])) ?_
      exact integral_inv_p_le hβ hβb hb'.le hη0
  -- the second piece
  have e2 : c * ∫ t in b..1, g t ≤ 1 := by
    have h1 : ∫ t in b..1, g t ≤ ∫ t in b..1, √V * (1 / √(1 - t)) :=
      intervalIntegral.integral_mono_ae_restrict hb1 hi2
        (hmaj.mono_set (by rw [uIcc_of_le hb1, uIcc_of_le (by linarith)]; exact Icc_subset_Icc hbη le_rfl)) (by
        have hne : ∀ᵐ t ∂(volume.restrict (Icc b 1)), t ≠ 1 := by
          refine ae_restrict_of_ae ?_; rw [ae_iff]; simp
        filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with t h1 ht
        exact hp2 t ⟨hbη.trans ht.1, ht.2⟩ (lt_of_le_of_ne ht.2 h1))
    have h2 : ∫ t in b..1, √V * (1 / √(1 - t)) ≤ ∫ t in (1 - η)..1, √V * (1 / √(1 - t)) :=
      intervalIntegral.integral_mono_interval hbη hb1 le_rfl (Eventually.of_forall fun t => by
        simp only [Pi.zero_apply]; positivity) hmaj
    have h4 : ∫ t in (1 - η)..1, √V * (1 / √(1 - t)) = √V * (2 * √η) := by
      rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_one_sub hη0.le]
    rw [h4] at h2
    have h3 : c * (√V * (2 * √η)) = 1 := by
      rw [hη]
      have hcV : 0 < c ^ 2 * V := by positivity
      rw [show c * (√V * (2 * √(1 / (4 * c ^ 2 * V)))) = 2 * (√(c ^ 2) * √V * √(1 / (4 * c ^ 2 * V))) by
        rw [Real.sqrt_sq hc.le]; ring, ← Real.sqrt_mul (sq_nonneg c), ← Real.sqrt_mul (by positivity)]
      rw [show c ^ 2 * V * (1 / (4 * c ^ 2 * V)) = 1 / 4 by field_simp,
        show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      norm_num
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hc.le]
  have e3 : log (2 / η) = log (8 * c ^ 2 * V) := by rw [hη]; congr 1; field_simp; ring
  rw [← e3]
  linarith

end Level

/-! ### The count -/

theorem one_sub_sq_pos {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : 0 < 1 - t ^ 2 := by
  have : t ^ 2 < 1 := (sq_lt_one_iff₀ h0).mpr h1
  linarith

/-- The Weyl integral `I(α, v) = ∫_α^1 √((v − t²)₊/(1 − t²)) dt`. -/
def weylI (α v : ℝ) : ℝ := ∫ t in α..1, √((v - t ^ 2) / (1 - t ^ 2))

/-- The upper error `2 + log(c²V)/(4π) + log(8c²V)/(2√2)`. -/
def errUp (c V : ℝ) : ℝ := 2 + log (c ^ 2 * V) / (4 * π) + log (8 * c ^ 2 * V) / (2 * √2)

/-- The lower error `1 + (½ log(8c²V) + 1 + ¼ log(c²V))/π`. -/
def errLow (c V : ℝ) : ℝ := 1 + (log (8 * c ^ 2 * V) / 2 + 1 + log (c ^ 2 * V) / 4) / π

section Count

variable {c v V α : ℝ}

theorem setup (hc1 : 1 ≤ c) (hV : 1 ≤ V) :
    0 ≤ log (c ^ 2 * V) ∧ 0 ≤ log (8 * c ^ 2 * V) ∧ log (8 * c ^ 2 * V) / 2 = log (2 / (1 / (4 * c ^ 2 * V))) / 2 ∧
      0 < 1 / (4 * c ^ 2 * V) ∧ 1 / (4 * c ^ 2 * V) ≤ 1 := by
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  refine ⟨Real.log_nonneg (by nlinarith), Real.log_nonneg (by nlinarith), by congr 2; field_simp; ring,
    by positivity, ?_⟩
  rw [div_le_one (by positivity)]; nlinarith

/-- Zeros of the regular solution in `(α, 1)` lie below `min(√v, 1 − η)`. -/
theorem lt_of_zero (hc1 : 1 ≤ c) (hv : 0 ≤ v) (hvV : v ≤ V) (hV : 1 ≤ V) {w : ℝ} (hw : w ∈ Ioo α 1)
    (hw0 : regSol (sqC c) (c ^ 2 * v) w = 0) : w < min √v (1 - 1 / (4 * c ^ 2 * V)) := by
  by_contra h
  push Not at h
  exact no_zero_beyond hc1 hv hvV hV w ⟨h, hw.2.le⟩ hw0

theorem weylI_nonneg (hα1 : α ≤ 1) : 0 ≤ weylI α v :=
  intervalIntegral.integral_nonneg hα1 fun _ _ => Real.sqrt_nonneg _

/-- **The upper Weyl count**: `k` zeros in `(α, 1)` give `k ≤ (c/π)I(α, v) + errUp`. -/
theorem zero_count_le (hc1 : 1 ≤ c) (hv : 0 ≤ v) (hvV : v ≤ V) (hV : 1 ≤ V) (hα : 0 ≤ α) (hα1 : α < 1) {k : ℕ}
    (hz : ZerosOn (regSol (sqC c) (c ^ 2 * v)) (Ioo α 1) k) : (k : ℝ) ≤ c / π * weylI α v + errUp c V := by
  obtain ⟨hl1, hl2, hl3, hη0, hη1⟩ := setup hc1 hV
  set η := 1 / (4 * c ^ 2 * V) with hη
  set γ := min √v (1 - η) with hγ
  have hγ1 : γ < 1 := (min_le_right _ _).trans_lt (by linarith)
  have hγv : γ ≤ √v := min_le_left _ _
  have hc0 : 0 < c := by linarith
  have hI0 : 0 ≤ c / π * weylI α v := mul_nonneg (by positivity) (weylI_nonneg hα1.le)
  have hπ : 0 < π := Real.pi_pos
  set pq : ℝ → ℝ := fun t => (1 - t ^ 2) * (c ^ 2 * v - c ^ 2 * t ^ 2) with hpq
  -- the layer condition after a point with `pq ≤ 1`
  have hlay : ∀ β, 0 ≤ β → pq β ≤ 1 → ∀ t ∈ Icc β γ, (1 - t ^ 2) * |c ^ 2 * v - c ^ 2 * t ^ 2| ≤ 1 :=
    fun β hβ hβ1 t ht => by
      have htv : t ≤ √v := ht.2.trans hγv
      have hq : 0 ≤ c ^ 2 * v - c ^ 2 * t ^ 2 := by
        have : t ^ 2 ≤ v := by nlinarith [Real.sq_sqrt hv, hβ.trans ht.1]
        nlinarith
      rw [abs_of_nonneg hq]
      exact pq_le_one hv hβ hβ1 t ⟨ht.1, ht.2.trans hγ1.le⟩
  -- all zeros lie in `(α, γ)`
  have hin : ∀ {a : ℝ} {n : ℕ}, a ≤ 1 → ZerosOn (regSol (sqC c) (c ^ 2 * v)) (Ioo a 1) n →
      ZerosOn (regSol (sqC c) (c ^ 2 * v)) (Icc a γ) n := fun {a n} _ ⟨w, hw, hwI, hw0⟩ =>
    ⟨w, hw, fun i => ⟨(hwI i).1.le, (lt_of_zero hc1 hv hvV hV (hwI i) (hw0 i)).le⟩, hw0⟩
  -- a layer holds few zeros
  have hlayer : ∀ β, 0 ≤ β → pq β ≤ 1 → ∀ n : ℕ, ZerosOn (regSol (sqC c) (c ^ 2 * v)) (Icc β γ) n →
      (n : ℝ) ≤ 1 + log (8 * c ^ 2 * V) / (2 * √2) := fun β hβ hβ1 n hn => by
    rcases n with _ | n
    · simp; positivity
    have hβγ : β ≤ γ := by obtain ⟨w, -, hwI, -⟩ := hn; exact (hwI 0).1.trans (hwI 0).2
    have h := Cvs.Prolate.LiouvilleGreen.TurningLayerZeros.layer_count hβ hγ1 (hlay β hβ hβ1) hn
    have hi := integral_inv_p_le hβ hβγ (min_le_right _ _) hη0
    rw [← hl3] at hi
    have hs2 : 0 < √2 := by positivity
    have h3 : (n : ℝ) ≤ log (8 * c ^ 2 * V) / (2 * √2) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    push_cast; linarith
  by_cases hA : pq α ≤ 1
  · -- the whole allowed interval is a layer
    have := hlayer α hα hA k (hin hα1.le hz)
    unfold errUp
    have : 0 ≤ log (c ^ 2 * V) / (4 * π) := by positivity
    linarith
  · push Not at hA
    -- the cut `pq(β) = 1`
    have hαv : α < √v := by
      by_contra h; push Not at h
      have hv2 : v ≤ α ^ 2 := by
        have := mul_self_le_mul_self (Real.sqrt_nonneg v) h
        rw [Real.mul_self_sqrt hv] at this; nlinarith
      have : c ^ 2 * v - c ^ 2 * α ^ 2 ≤ 0 := by
        rw [← mul_sub]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) (by linarith)
      have : pq α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by nlinarith) this
      linarith
    set γ' := min √v 1 with hγ'
    have hαγ' : α ≤ γ' := le_min hαv.le hα1.le
    have hpqγ' : pq γ' = 0 := by
      rcases min_choice √v 1 with h | h
      · simp only [hpq]; rw [hγ', h, Real.sq_sqrt hv]; ring
      · simp only [hpq]; rw [hγ', h]; ring
    have hpqc : ContinuousOn pq (Icc α γ') := by simp only [hpq]; fun_prop
    obtain ⟨β, hβI, hβ1⟩ := intermediate_value_Icc' hαγ' hpqc ⟨by rw [hpqγ']; norm_num, hA.le⟩
    have hβ0 : 0 ≤ β := hα.trans hβI.1
    have hβγ' : β < γ' := lt_of_le_of_ne hβI.2 (fun h => by rw [h, hpqγ'] at hβ1; norm_num at hβ1)
    have hβ1' : β < 1 := hβγ'.trans_le (min_le_right _ _)
    -- `q > 0` on `[α, β]`
    have hqpos : ∀ t ∈ Icc α β, 0 < qf c (c * (1 - v)) t := fun t ht => by
      rw [qf_eq]
      have h1 : pq β ≤ pq t := pq_anti hv ⟨hα.trans ht.1, ht.2.trans hβγ'.le⟩ ⟨hβ0, hβI.2⟩ ht.2
      have hp : 0 < 1 - t ^ 2 := one_sub_sq_pos (hα.trans ht.1) (ht.2.trans_lt hβ1')
      have : 0 < pq t := by linarith
      simp only [hpq] at this
      exact pos_of_mul_pos_right this hp.le
    -- the Liouville–Green part
    have haβ : af c (c * (1 - v)) β = 1 := by
      unfold af; rw [qf_eq]; simp only [hpq] at hβ1; rw [hβ1, Real.sqrt_one]
    have haα : log (af c (c * (1 - v)) α) ≤ log (c ^ 2 * V) / 2 := by
      unfold af; rw [qf_eq, Real.log_sqrt (by simp only [hpq] at hA; linarith)]
      have h1 : (1 - α ^ 2) * (c ^ 2 * v - c ^ 2 * α ^ 2) ≤ c ^ 2 * V := by
        have hq : c ^ 2 * v - c ^ 2 * α ^ 2 ≤ c ^ 2 * V := by nlinarith [sq_nonneg α, sq_nonneg c]
        have hq0 : 0 < c ^ 2 * v - c ^ 2 * α ^ 2 := by
          have := hqpos α ⟨le_rfl, hβI.1⟩; rwa [qf_eq] at this
        nlinarith [sq_nonneg α]
      have := Real.log_le_log (by simp only [hpq] at hA; linarith) h1
      linarith
    have haα0 : 0 ≤ log (af c (c * (1 - v)) α) := by
      unfold af; rw [qf_eq]; exact Real.log_nonneg (Real.le_sqrt_of_sq_le (by simp only [hpq] at hA; nlinarith))
    -- `Ω ≤ cI`
    have hΩ : Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount.Omg c (c * (1 - v)) α β ≤ c * weylI α v := by
      have hcont : ContinuousOn (fun t => √((v - t ^ 2) / (1 - t ^ 2))) (Icc α β) := fun t ht => by
        have hp : 0 < 1 - t ^ 2 := one_sub_sq_pos (hα.trans ht.1) (ht.2.trans_lt hβ1')
        exact (ContinuousAt.sqrt ((by fun_prop : ContinuousAt (fun t : ℝ => v - t ^ 2) t).div (by fun_prop)
          hp.ne')).continuousWithinAt
      have hi1 := hcont.intervalIntegrable_of_Icc (μ := volume) hβI.1
      obtain ⟨hi2, -⟩ := tail_le hc1 hvV hV hβ0 hβ1'.le (pq_le_one hv hβ0 hβ1.le)
      unfold Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount.Omg weylI
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, mul_add,
        ← intervalIntegral.integral_const_mul]
      have e : ∫ t in α..β, af c (c * (1 - v)) t / (1 - t ^ 2) = ∫ t in α..β, c * √((v - t ^ 2) / (1 - t ^ 2)) :=
        intervalIntegral.integral_congr fun t ht => by
          rw [uIcc_of_le hβI.1] at ht
          exact omega_eq hc0.le ((sq_lt_one_iff₀ (hα.trans ht.1)).mpr (ht.2.trans_lt hβ1'))
      rw [e]
      have : 0 ≤ c * ∫ t in β..1, √((v - t ^ 2) / (1 - t ^ 2)) :=
        mul_nonneg hc0.le (intervalIntegral.integral_nonneg hβ1'.le fun _ _ => Real.sqrt_nonneg _)
      linarith
    set X := (Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount.Omg c (c * (1 - v)) α β + log (af c (c * (1 - v)) α) / 2) / π with hX
    have hX0 : 0 ≤ X := by
      rw [hX]; refine div_nonneg ?_ hπ.le
      have : 0 ≤ Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount.Omg c (c * (1 - v)) α β :=
        intervalIntegral.integral_nonneg hβI.1 fun t ht => by
          have hp : 0 < 1 - t ^ 2 := one_sub_sq_pos (hα.trans ht.1) (ht.2.trans_lt hβ1')
          exact div_nonneg (Real.sqrt_nonneg _) hp.le
      linarith
    set N₁ := ⌊X⌋₊ + 1 with hN₁
    have hN₁X : X < N₁ := by rw [hN₁]; push_cast; exact Nat.lt_floor_add_one X
    have hnot : ¬ZerosOn (regSol (sqC c) (c ^ 2 * v)) (Ioc α β) (N₁ + 1) := fun h => by
      have h' : ZerosOn (regSol (sqC c) (c ^ 2 - c * (1 - v) * c)) (Icc α β) (N₁ + 1) := by
        rw [level_eq]; obtain ⟨w, hw, hwI, hw0⟩ := h; exact ⟨w, hw, fun i => ⟨(hwI i).1.le, (hwI i).2⟩, hw0⟩
      have := Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount.count_le hα hβI.1 hβ1' hqpos h'
      rw [haβ, Real.log_one, sub_zero] at this
      have : (N₁ : ℝ) ≤ X := by rw [hX, le_div_iff₀ hπ]; linarith
      linarith
    have hXb : X ≤ (c * weylI α v + log (c ^ 2 * V) / 4) / π := by
      rw [hX]; exact div_le_div_of_nonneg_right (by linarith) hπ.le
    have hcI : c / π * weylI α v = c * weylI α v / π := by ring
    rcases le_or_gt k N₁ with hk | hk
    · have : (k : ℝ) ≤ N₁ := by exact_mod_cast hk
      unfold errUp
      have h2 : 0 ≤ log (8 * c ^ 2 * V) / (2 * √2) := by positivity
      rw [hcI]
      have : (N₁ : ℝ) ≤ X + 1 := by rw [hN₁]; push_cast; linarith [Nat.floor_le hX0]
      have e : (c * weylI α v + log (c ^ 2 * V) / 4) / π = c * weylI α v / π + log (c ^ 2 * V) / (4 * π) := by
        rw [add_div, div_div]
      linarith
    · obtain ⟨n, rfl⟩ : ∃ n, k = N₁ + n := ⟨k - N₁, by omega⟩
      have ht := Cvs.Prolate.TopRungZeroSplitHalf.zerosOn_tail hz hnot
      have hn := hlayer β hβ0 hβ1.le n (hin hβ1'.le ht)
      unfold errUp
      push_cast
      rw [hcI]
      have : (N₁ : ℝ) ≤ X + 1 := by rw [hN₁]; push_cast; linarith [Nat.floor_le hX0]
      have e : (c * weylI α v + log (c ^ 2 * V) / 4) / π = c * weylI α v / π + log (c ^ 2 * V) / (4 * π) := by
        rw [add_div, div_div]
      linarith

/-- **The lower Weyl count**: `m ≤ (c/π)I(α, v) − errLow` gives `m` zeros in `(α, 1)`. -/
theorem zero_count_ge (hc1 : 1 ≤ c) (hv : 0 ≤ v) (hvV : v ≤ V) (hV : 1 ≤ V) (hα : 0 ≤ α) (hα1 : α < 1) {m : ℕ}
    (hm : (m : ℝ) ≤ c / π * weylI α v - errLow c V) : ZerosOn (regSol (sqC c) (c ^ 2 * v)) (Ioo α 1) m := by
  obtain ⟨hl1, hl2, hl3, hη0, hη1⟩ := setup hc1 hV
  have hc0 : 0 < c := by linarith
  have hπ : 0 < π := Real.pi_pos
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set pq : ℝ → ℝ := fun t => (1 - t ^ 2) * (c ^ 2 * v - c ^ 2 * t ^ 2) with hpq
  have hcI : c / π * weylI α v = c * weylI α v / π := by ring
  by_cases hA : pq α ≤ 1
  · exfalso
    obtain ⟨-, h⟩ := tail_le hc1 hvV hV hα hα1.le (pq_le_one hv hα hA)
    have : c * weylI α v ≤ log (8 * c ^ 2 * V) / 2 + 1 := h
    unfold errLow at hm
    rw [hcI] at hm
    have h2 : c * weylI α v / π ≤ (log (8 * c ^ 2 * V) / 2 + 1 + log (c ^ 2 * V) / 4) / π :=
      div_le_div_of_nonneg_right (by linarith) hπ.le
    linarith
  · push Not at hA
    have hαv : α < √v := by
      by_contra h; push Not at h
      have hv2 : v ≤ α ^ 2 := by
        have := mul_self_le_mul_self (Real.sqrt_nonneg v) h
        rw [Real.mul_self_sqrt hv] at this; nlinarith
      have : c ^ 2 * v - c ^ 2 * α ^ 2 ≤ 0 := by
        rw [← mul_sub]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) (by linarith)
      have : pq α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by nlinarith) this
      linarith
    set γ' := min √v 1 with hγ'
    have hαγ' : α ≤ γ' := le_min hαv.le hα1.le
    have hpqγ' : pq γ' = 0 := by
      rcases min_choice √v 1 with h | h
      · simp only [hpq]; rw [hγ', h, Real.sq_sqrt hv]; ring
      · simp only [hpq]; rw [hγ', h]; ring
    have hpqc : ContinuousOn pq (Icc α γ') := by simp only [hpq]; fun_prop
    obtain ⟨β, hβI, hβ1⟩ := intermediate_value_Icc' hαγ' hpqc ⟨by rw [hpqγ']; norm_num, hA.le⟩
    have hβ0 : 0 ≤ β := hα.trans hβI.1
    have hβγ' : β < γ' := lt_of_le_of_ne hβI.2 (fun h => by rw [h, hpqγ'] at hβ1; norm_num at hβ1)
    have hβ1' : β < 1 := hβγ'.trans_le (min_le_right _ _)
    have hqpos : ∀ t ∈ Icc α β, 0 < qf c (c * (1 - v)) t := fun t ht => by
      rw [qf_eq]
      have h1 : pq β ≤ pq t := pq_anti hv ⟨hα.trans ht.1, ht.2.trans hβγ'.le⟩ ⟨hβ0, hβI.2⟩ ht.2
      have hp : 0 < 1 - t ^ 2 := one_sub_sq_pos (hα.trans ht.1) (ht.2.trans_lt hβ1')
      have : 0 < pq t := by linarith
      simp only [hpq] at this
      exact pos_of_mul_pos_right this hp.le
    have haβ : af c (c * (1 - v)) β = 1 := by
      unfold af; rw [qf_eq]; simp only [hpq] at hβ1; rw [hβ1, Real.sqrt_one]
    have haα : log (af c (c * (1 - v)) α) ≤ log (c ^ 2 * V) / 2 := by
      unfold af; rw [qf_eq, Real.log_sqrt (by simp only [hpq] at hA; linarith)]
      have h1 : (1 - α ^ 2) * (c ^ 2 * v - c ^ 2 * α ^ 2) ≤ c ^ 2 * V := by
        have hq : c ^ 2 * v - c ^ 2 * α ^ 2 ≤ c ^ 2 * V := by nlinarith [sq_nonneg α, sq_nonneg c]
        have hq0 : 0 < c ^ 2 * v - c ^ 2 * α ^ 2 := by
          have := hqpos α ⟨le_rfl, hβI.1⟩; rwa [qf_eq] at this
        nlinarith [sq_nonneg α]
      have := Real.log_le_log (by simp only [hpq] at hA; linarith) h1
      linarith
    -- `Ω ≥ cI − ½ log(8c²V) − 1`
    have hΩ : c * weylI α v - (log (8 * c ^ 2 * V) / 2 + 1) ≤ Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount.Omg c (c * (1 - v)) α β := by
      have hcont : ContinuousOn (fun t => √((v - t ^ 2) / (1 - t ^ 2))) (Icc α β) := fun t ht => by
        have hp : 0 < 1 - t ^ 2 := one_sub_sq_pos (hα.trans ht.1) (ht.2.trans_lt hβ1')
        exact (ContinuousAt.sqrt ((by fun_prop : ContinuousAt (fun t : ℝ => v - t ^ 2) t).div (by fun_prop)
          hp.ne')).continuousWithinAt
      have hi1 := hcont.intervalIntegrable_of_Icc (μ := volume) hβI.1
      obtain ⟨hi2, htail⟩ := tail_le hc1 hvV hV hβ0 hβ1'.le (pq_le_one hv hβ0 hβ1.le)
      unfold Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount.Omg weylI
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, mul_add,
        ← intervalIntegral.integral_const_mul]
      have e : ∫ t in α..β, af c (c * (1 - v)) t / (1 - t ^ 2) = ∫ t in α..β, c * √((v - t ^ 2) / (1 - t ^ 2)) :=
        intervalIntegral.integral_congr fun t ht => by
          rw [uIcc_of_le hβI.1] at ht
          exact omega_eq hc0.le ((sq_lt_one_iff₀ (hα.trans ht.1)).mpr (ht.2.trans_lt hβ1'))
      rw [e]
      linarith
    have hcount := Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount.count_ge (m := m) hα hβI.1 hβ1' hqpos (by
      rw [haβ, Real.log_one, sub_zero]
      unfold errLow at hm
      rw [hcI] at hm
      have h1 : ((m : ℝ) + 1) * π ≤ c * weylI α v - (log (8 * c ^ 2 * V) / 2 + 1 + log (c ^ 2 * V) / 4) := by
        have := mul_le_mul_of_nonneg_right hm hπ.le
        have e : (c * weylI α v / π - (1 + (log (8 * c ^ 2 * V) / 2 + 1 + log (c ^ 2 * V) / 4) / π)) * π =
            c * weylI α v - (log (8 * c ^ 2 * V) / 2 + 1 + log (c ^ 2 * V) / 4) - π := by
          field_simp; ring
        rw [e] at this; linarith
      linarith)
    rw [level_eq] at hcount
    obtain ⟨w, hw, hwI, hw0⟩ := hcount
    exact ⟨w, hw, fun i => ⟨(hwI i).1, (hwI i).2.trans hβ1'⟩, hw0⟩

end Count

end Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog

end
