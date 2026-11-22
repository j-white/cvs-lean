import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Lévy integral by unit blocks

`densityU u ≤ 1/u + 1/4`, `∫₂^∞ densityU ≤ D₂ ≤ 3`, and
`archFull f ≤ (2D₂ + 6)‖f‖² + 2 Σ_L ā_L max 1 (log (H_L V_L / 2ā_L))`; `√archFull` is a seminorm.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Set Filter Topology MeasureTheory Cvs.WeilForm.Archimedean.LevyDensity Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.LevyUnitBlocks

/-- The closed-form bound on the far Lévy mass. -/
noncomputable def D2 : ℝ := 4 * Real.exp (-(1 / 2)) / (1 - Real.exp (-2))

/-- **The Lévy density sits under `1/u + 1/4`.** -/
theorem densityU_le {u : ℝ} (hu : 0 < u) : densityU u ≤ 1 / u + 1 / 4 := by
  set v : ℝ := u / 4 with hv
  have hv0 : 0 < v := by rw [hv]; positivity
  set s := Real.sinh v
  set c := Real.cosh v
  set x := Real.exp v with hx
  have hcs : c ^ 2 = s ^ 2 + 1 := Real.cosh_sq v
  have hxe : x = c + s := (Real.cosh_add_sinh v).symm
  have hsv : v ≤ s := Real.self_le_sinh_iff.mpr hv0.le
  have hc1 : 1 ≤ c := Real.one_le_cosh v
  have hx1 : 1 < x := Real.one_lt_exp_iff.mpr hv0
  have hkey : 0 ≤ (1 + v) * c * s - v * (c + s) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c) (by linarith : 0 ≤ s - v),
      mul_nonneg (mul_nonneg hv0.le (by linarith : (0:ℝ) ≤ s)) (by linarith : 0 ≤ c - 1)]
  have hpoly : (1 + v) * (x ^ 4 - 1) - 4 * v * x ^ 3
      = 4 * x ^ 2 * ((1 + v) * c * s - v * (c + s)) := by
    rw [hxe]; linear_combination ((1 + v) * (c ^ 2 - s ^ 2 + 1)) * hcs
  have hineq : 4 * v * x ^ 3 ≤ (1 + v) * (x ^ 4 - 1) := by
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 4 * x ^ 2) hkey]
  have hx4 : 0 < x ^ 4 - 1 := by nlinarith [one_lt_pow₀ hx1 (by norm_num : (4:ℕ) ≠ 0)]
  have he1 : Real.exp (-(u / 4)) = x⁻¹ := by rw [Real.exp_neg]
  have he2 : Real.exp (-u) = (x ^ 4)⁻¹ := by
    rw [Real.exp_neg, hx, ← Real.exp_nat_mul]; congr 2; rw [hv]; push_cast; ring
  have hx0 : 0 < x := by linarith
  unfold densityU
  rw [he1, he2, show x⁻¹ / (1 - (x ^ 4)⁻¹) = x ^ 3 / (x ^ 4 - 1) by
    field_simp, div_le_iff₀ hx4,
    show (1 / u + 1 / 4) * (x ^ 4 - 1) = (1 + v) * (x ^ 4 - 1) / (4 * v) by
      rw [hv]; field_simp, le_div_iff₀ (by positivity)]
  linarith

/-- The far density is dominated by an exponential. -/
theorem densityU_le_exp {u : ℝ} (hu : 2 ≤ u) :
    densityU u ≤ Real.exp (-(u / 4)) / (1 - Real.exp (-2)) := by
  have h2 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hle : Real.exp (-u) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
  unfold densityU
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith) (by linarith)

/-- The Lévy density is measurable. -/
theorem measurable_densityU : Measurable densityU := by
  unfold densityU; fun_prop

/-- The exponential majorant is integrable on `(2, ∞)`. -/
theorem integrableOn_exp_div_Ioi_two :
    IntegrableOn (fun u : ℝ => Real.exp (-(u / 4)) / (1 - Real.exp (-2))) (Ioi 2) := by
  have h := (exp_neg_integrableOn_Ioi 2 (by norm_num : (0:ℝ) < 1 / 4)).div_const
    (1 - Real.exp (-2))
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  congr 2; ring

/-- The exponential majorant integrates to `D₂` on `(2, ∞)`. -/
theorem integral_exp_div_Ioi_two :
    ∫ u in Ioi (2 : ℝ), Real.exp (-(u / 4)) / (1 - Real.exp (-2)) = D2 := by
  rw [integral_div]
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 2
    (by norm_num : (0:ℝ) < 1 / 4)
  simp only [integral_exp_neg_Ioi, smul_eq_mul] at h
  rw [D2, show (fun u : ℝ => Real.exp (-(u / 4))) = fun u => Real.exp (-(1 / 4 * u)) by
    funext u; congr 2; ring, h]
  norm_num

/-- The Lévy density is integrable on `(2, ∞)`. -/
theorem integrableOn_densityU_Ioi_two : IntegrableOn densityU (Ioi 2) := by
  refine integrableOn_exp_div_Ioi_two.mono' measurable_densityU.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (densityU_pos (by linarith [mem_Ioi.mp hu]))]
  exact densityU_le_exp (le_of_lt hu)

/-- **The far Lévy mass is at most `D₂`.** -/
theorem integral_densityU_Ioi_two_le : ∫ u in Ioi (2 : ℝ), densityU u ≤ D2 := by
  rw [← integral_exp_div_Ioi_two]
  exact setIntegral_mono_on integrableOn_densityU_Ioi_two integrableOn_exp_div_Ioi_two
    measurableSet_Ioi fun u hu => densityU_le_exp (le_of_lt hu)

/-- The block kernel is integrable on `(0, 2]`. -/
theorem integrableOn_kernel {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) :
    IntegrableOn (fun u : ℝ => (1 / u + 1 / 4) * min (2 * a) (K * u / 2)) (Ioc 0 2) := by
  have hm : Measurable fun u : ℝ => (1 / u + 1 / 4) * min (2 * a) (K * u / 2) := by fun_prop
  refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable
    (M := K / 2 + a / 2) (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
  have hu := hu.1
  have hm0 : 0 ≤ min (2 * a) (K * u / 2) := le_min (by linarith) (by positivity)
  have e : (1 / u + 1 / 4) * min (2 * a) (K * u / 2)
      = min (2 * a) (K * u / 2) / u + min (2 * a) (K * u / 2) / 4 := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), e]
  have h1 : min (2 * a) (K * u / 2) / u ≤ K / 2 := by
    rw [div_le_iff₀ hu]; have := min_le_right (2 * a) (K * u / 2); linarith
  have h2 : min (2 * a) (K * u / 2) / 4 ≤ a / 2 := by
    have := min_le_left (2 * a) (K * u / 2); linarith
  linarith

/-- The block kernel at a positive block mass. -/
theorem integral_kernel_le {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) :
    ∫ u in Ioc (0 : ℝ) 2, (1 / u + 1 / 4) * min (2 * a) (K * u / 2)
      ≤ 3 * a + 2 * a * max 0 (Real.log (K / (2 * a))) := by
  have hmax : 0 ≤ max 0 (Real.log (K / (2 * a))) := le_max_left _ _
  have hRHS : 0 ≤ 3 * a + 2 * a * max 0 (Real.log (K / (2 * a))) := by positivity
  rcases hK.eq_or_lt with hK0 | hKpos
  · subst hK0
    have : (fun u : ℝ => (1 / u + 1 / 4) * min (2 * a) (0 * u / 2)) = fun _ => 0 := by
      funext u; rw [zero_mul, zero_div, min_eq_right (by linarith), mul_zero]
    rw [this, integral_zero]; exact hRHS
  set F : ℝ → ℝ := fun u => (1 / u + 1 / 4) * min (2 * a) (K * u / 2) with hF
  have hsplitF : ∀ u, F u = min (2 * a) (K * u / 2) / u + min (2 * a) (K * u / 2) / 4 := by
    intro u; simp only [hF]; ring
  have hbd : ∀ u, 0 < u → F u ≤ K / 2 + a / 2 := by
    intro u hu
    rw [hsplitF]
    have h1 : min (2 * a) (K * u / 2) / u ≤ K / 2 := by
      rw [div_le_iff₀ hu]; have := min_le_right (2 * a) (K * u / 2); linarith
    have h2 : min (2 * a) (K * u / 2) / 4 ≤ a / 2 := by
      have := min_le_left (2 * a) (K * u / 2); linarith
    linarith
  have hI : IntegrableOn F (Ioc 0 2) := integrableOn_kernel ha.le hK
  have hII : IntervalIntegrable F volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hI
  set t : ℝ := min (4 * a / K) 2 with ht
  have ht0 : 0 < t := lt_min (by positivity) (by norm_num)
  have ht2 : t ≤ 2 := min_le_right _ _
  have htK : t * K ≤ 4 * a := by
    have := mul_le_mul_of_nonneg_right (min_le_left (4 * a / K) 2) hKpos.le
    rwa [div_mul_cancel₀ _ hKpos.ne'] at this
  have hlog : Real.log (2 / t) ≤ max 0 (Real.log (K / (2 * a))) := by
    rcases min_cases (4 * a / K) 2 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [← ht] at h; rw [h, show 2 / (4 * a / K) = K / (2 * a) by field_simp; ring]
      exact le_max_right _ _
    · rw [← ht] at h; rw [h, div_self (by norm_num), Real.log_one]; exact le_max_left _ _
  have hI1 : IntervalIntegrable F volume 0 t := hII.mono_set (by
    rw [uIcc_of_le ht0.le, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc le_rfl ht2)
  have hI2 : IntervalIntegrable F volume t 2 := hII.mono_set (by
    rw [uIcc_of_le ht2, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc ht0.le le_rfl)
  have hinv : IntervalIntegrable (fun u : ℝ => 2 * a * (1 / u)) volume t 2 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht2]
    refine continuousOn_const.mul (continuousOn_const.div continuousOn_id fun u hu => ?_)
    exact (lt_of_lt_of_le ht0 hu.1).ne'
  have hg2 : IntervalIntegrable (fun u : ℝ => 2 * a * (1 / u) + a / 2) volume t 2 :=
    hinv.add intervalIntegrable_const
  have hP1 : ∫ u in (0 : ℝ)..t, F u ≤ t * (K / 2 + a / 2) := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo ht0.le hI1
      (intervalIntegrable_const (c := K / 2 + a / 2)) fun u hu => hbd u hu.1
    simp at this; linarith
  have hP2 : ∫ u in t..2, F u ≤ 2 * a * Real.log (2 / t) + (2 - t) * (a / 2) := by
    have hle := intervalIntegral.integral_mono_on_of_le_Ioo ht2 hI2 hg2 fun u hu => by
      have hu0 : 0 < u := lt_trans ht0 hu.1
      rw [hsplitF]
      have h1 : min (2 * a) (K * u / 2) / u ≤ 2 * a * (1 / u) := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (min_le_left _ _) hu0.le
      have h2 : min (2 * a) (K * u / 2) / 4 ≤ a / 2 := by
        have := min_le_left (2 * a) (K * u / 2); linarith
      linarith
    have hval : ∫ u in t..2, (2 * a * (1 / u) + a / 2)
        = 2 * a * Real.log (2 / t) + (2 - t) * (a / 2) := by
      rw [intervalIntegral.integral_add hinv intervalIntegrable_const,
        intervalIntegral.integral_const_mul, integral_one_div_of_pos ht0 two_pos,
        intervalIntegral.integral_const, smul_eq_mul]
    linarith
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2),
    ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  nlinarith [mul_le_mul_of_nonneg_left hlog (by linarith : (0:ℝ) ≤ 2 * a)]

/-- The block kernel at a nonnegative block mass. -/
theorem integral_kernel_le_of_nonneg {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) :
    ∫ u in Ioc (0 : ℝ) 2, (1 / u + 1 / 4) * min (2 * a) (K * u / 2)
      ≤ 3 * a + 2 * a * max 0 (Real.log (K / (2 * a))) := by
  rcases ha.eq_or_lt with ha0 | ha0
  · subst ha0
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ)) fun u hu => by
      simp only; rw [mul_zero, min_eq_left (by have := hu.1; positivity), mul_zero],
      integral_zero]
    simp
  · exact integral_kernel_le ha0 hK

/-- `a log⁺ (K / 2a)` is dominated at any larger mass `ā`, with `log⁺` raised to `max 1`. -/
theorem mul_log_le_of_le {a ā K : ℝ} (ha : 0 ≤ a) (haā : a ≤ ā) (hā : 0 < ā) (hK : 0 ≤ K) :
    a * max 0 (Real.log (K / (2 * a))) ≤ ā * max 1 (Real.log (K / (2 * ā))) := by
  set ℓ := max 1 (Real.log (K / (2 * ā))) with hℓdef
  have hℓ1 : 1 ≤ ℓ := le_max_left _ _
  have hℓ : Real.log (K / (2 * ā)) ≤ ℓ := le_max_right _ _
  have hR : 0 ≤ ā * ℓ := mul_nonneg hā.le (by linarith)
  rcases le_total (Real.log (K / (2 * a))) 0 with h | h
  · rw [max_eq_left h, mul_zero]; exact hR
  rw [max_eq_right h]
  rcases ha.eq_or_lt with ha0 | ha0
  · rw [← ha0, zero_mul]; exact hR
  rcases hK.eq_or_lt with hK0 | hK0
  · rw [← hK0, zero_div, Real.log_zero, mul_zero]; exact hR
  have hsplit : Real.log (K / (2 * a)) = Real.log (K / (2 * ā)) + Real.log (ā / a) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have hl : Real.log (ā / a) ≤ ā / a - 1 := Real.log_le_sub_one_of_pos (div_pos hā ha0)
  have hal : a * Real.log (ā / a) ≤ ā - a := by
    have := mul_le_mul_of_nonneg_left hl ha0.le
    rwa [mul_sub, mul_div_cancel₀ _ ha0.ne', mul_one] at this
  rw [hsplit, mul_add]
  nlinarith [mul_le_mul_of_nonneg_left hℓ ha0.le,
    mul_le_mul_of_nonneg_left hℓ1 (sub_nonneg.mpr haā)]

/-- A translate of an `L²` function is in `L²`. -/
theorem memLp_shift {f : ℝ → ℝ} (h2 : MemLp f 2 volume) (t : ℝ) :
    MemLp (fun s => f (s + t)) 2 volume :=
  h2.comp_measurePreserving (measurePreserving_add_right volume t)

/-- The translation difference of an `L²` function is in `L²`. -/
theorem memLp_sub_shift {f : ℝ → ℝ} (h2 : MemLp f 2 volume) (t : ℝ) :
    MemLp (fun s => f s - f (s + t)) 2 volume :=
  h2.sub (memLp_shift h2 t)

/-- The Lévy integrand is the density times half the translation energy. -/
theorem levy_eq_half {f : ℝ → ℝ} (h2 : MemLp f 2 volume) (u : ℝ) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u
      = densityU u * ((1 / 2) * ∫ s, (f s - f (s + u / 2)) ^ 2) := by
  rw [Cvs.WeilForm.SelfConvolutionFunctional.integral_sq_sub_eq (u / 2) h2.integrable_sq
    (h2.integrable_mul (memLp_shift h2 _))]
  simp only [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy]; ring

/-- The Lévy integrand is nonnegative for `u > 0`. -/
theorem levy_nonneg {f : ℝ → ℝ} (h2 : MemLp f 2 volume) {u : ℝ} (hu : 0 < u) :
    0 ≤ Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u := by
  rw [levy_eq_half h2]
  exact mul_nonneg (densityU_pos hu).le
    (mul_nonneg (by norm_num) (integral_nonneg fun s => sq_nonneg _))

/-- The Lévy integrand of an `L²` function is measurable. -/
theorem measurable_levy {f : ℝ → ℝ} (h2 : MemLp f 2 volume) :
    Measurable (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) :=
  measurable_densityU.mul (measurable_const.sub
    ((Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution h2).measurable.comp
      (measurable_id.div_const 2)))

/-- The Lévy integral is nonnegative. -/
theorem archFull_nonneg {f : ℝ → ℝ} (h2 : MemLp f 2 volume) :
    0 ≤ Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f :=
  setIntegral_nonneg measurableSet_Ioi fun _ hu => levy_nonneg h2 hu

/-- Half the translation energy is at most `2‖f‖²`. -/
theorem half_integral_sq_sub_le {f : ℝ → ℝ} (h2 : MemLp f 2 volume) (t : ℝ) :
    (1 / 2) * ∫ s, (f s - f (s + t)) ^ 2 ≤ 2 * ∫ s, f s ^ 2 := by
  have hs := (memLp_shift h2 t).integrable_sq
  have hle : ∫ s, (f s - f (s + t)) ^ 2 ≤ ∫ s, (2 * f s ^ 2 + 2 * f (s + t) ^ 2) :=
    integral_mono (memLp_sub_shift h2 t).integrable_sq
      ((h2.integrable_sq.const_mul 2).add (hs.const_mul 2))
      fun s => by nlinarith [sq_nonneg (f s + f (s + t))]
  rw [integral_add (h2.integrable_sq.const_mul 2) (hs.const_mul 2), integral_const_mul,
    integral_const_mul, integral_add_right_eq_self (μ := volume) (fun s => f s ^ 2) t] at hle
  linarith

/-- The Lévy integrand against `2‖f‖²`. -/
theorem levy_le_far {f : ℝ → ℝ} (h2 : MemLp f 2 volume) {u : ℝ} (hu : 0 < u) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u ≤ densityU u * (2 * ∫ s, f s ^ 2) := by
  rw [levy_eq_half h2]
  exact mul_le_mul_of_nonneg_left (half_integral_sq_sub_le h2 _) (densityU_pos hu).le

/-- The Lévy integrand is integrable on `(2, ∞)`. -/
theorem integrableOn_levy_Ioi_two {f : ℝ → ℝ} (h2 : MemLp f 2 volume) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 2) := by
  refine (integrableOn_densityU_Ioi_two.mul_const (2 * ∫ s, f s ^ 2)).mono'
    (measurable_levy h2).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_))
  have hu0 : (0 : ℝ) < u := by linarith [mem_Ioi.mp hu]
  rw [Real.norm_eq_abs, abs_of_nonneg (levy_nonneg h2 hu0)]
  exact levy_le_far h2 hu0

/-- The far Lévy integral is at most `2 D₂ ‖f‖²`. -/
theorem integral_levy_Ioi_two_le {f : ℝ → ℝ} (h2 : MemLp f 2 volume) :
    ∫ u in Ioi (2 : ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u ≤ 2 * D2 * ∫ s, f s ^ 2 := by
  have hn : 0 ≤ ∫ s, f s ^ 2 := integral_nonneg fun s => sq_nonneg _
  calc ∫ u in Ioi (2 : ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u
      ≤ ∫ u in Ioi (2 : ℝ), densityU u * (2 * ∫ s, f s ^ 2) :=
        setIntegral_mono_on (integrableOn_levy_Ioi_two h2)
          (integrableOn_densityU_Ioi_two.mul_const (2 * ∫ s, f s ^ 2)) measurableSet_Ioi
          fun u hu => levy_le_far h2 (by linarith [mem_Ioi.mp hu])
    _ = (∫ u in Ioi (2 : ℝ), densityU u) * (2 * ∫ s, f s ^ 2) := integral_mul_const _ _
    _ ≤ D2 * (2 * ∫ s, f s ^ 2) :=
        mul_le_mul_of_nonneg_right integral_densityU_Ioi_two_le (by positivity)
    _ = 2 * D2 * ∫ s, f s ^ 2 := by ring

/-- The unit blocks `[L - 1, L)` tile `[-1, ∞)`. -/
theorem iUnion_Ico_eq : ⋃ L : ℕ, Ico ((L : ℝ) - 1) L = Ici (-1) := by
  ext s; simp only [mem_iUnion, mem_Ico, mem_Ici]
  constructor
  · rintro ⟨L, h1, -⟩; have : (0:ℝ) ≤ L := L.cast_nonneg; linarith
  · intro hs
    refine ⟨⌊s + 1⌋₊, ?_, ?_⟩
    · have := Nat.floor_le (by linarith : (0:ℝ) ≤ s + 1); linarith
    · have := Nat.lt_floor_add_one (s + 1); linarith

/-- The unit blocks are pairwise disjoint. -/
theorem pairwise_disjoint_Ico :
    Pairwise (Function.onFun Disjoint fun L : ℕ => Ico ((L : ℝ) - 1) L) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro s hi hj
  apply hij
  have h1 : (i : ℝ) < j + 1 := by linarith [hi.1, hj.2]
  have h2 : (j : ℝ) < i + 1 := by linarith [hj.1, hi.2]
  have h1' : i < j + 1 := by exact_mod_cast h1
  have h2' : j < i + 1 := by exact_mod_cast h2
  omega

/-- The translation energy of a function vanishing on `(-∞, 0]` is the sum of its blocks. -/
theorem hasSum_blocks {f : ℝ → ℝ} (h2 : MemLp f 2 volume) (hf0 : ∀ s ≤ 0, f s = 0) {h : ℝ}
    (hh1 : h ≤ 1) :
    HasSum (fun L : ℕ => ∫ s in Ico ((L : ℝ) - 1) L, (f s - f (s + h)) ^ 2)
      (∫ s, (f s - f (s + h)) ^ 2) := by
  have hI := (memLp_sub_shift h2 h).integrable_sq
  have := hasSum_integral_iUnion (fun _ : ℕ => measurableSet_Ico) pairwise_disjoint_Ico
    hI.integrableOn
  rwa [iUnion_Ico_eq, setIntegral_eq_integral_of_forall_compl_eq_zero] at this
  intro s hs
  simp only [mem_Ici, not_le] at hs
  rw [hf0 s (by linarith), hf0 (s + h) (by linarith)]; ring

/-- A block's translation energy against its local sup and variation. -/
theorem block_le_var {f : ℝ → ℝ} (h2 : MemLp f 2 volume) {L : ℕ} {H V h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (hH : ∀ s ∈ Icc ((L : ℝ) - 1) (L + 1), |f s| ≤ H)
    (hV : ∫ s in Ico ((L : ℝ) - 1) L, |f s - f (s + h)| ≤ h * V) :
    ∫ s in Ico ((L : ℝ) - 1) L, (f s - f (s + h)) ^ 2 ≤ 2 * H * (h * V) := by
  have hd := memLp_sub_shift h2 h
  have hab : Integrable (fun s => |f s - f (s + h)|) (volume.restrict (Ico ((L : ℝ) - 1) L)) :=
    ((hd.restrict _).integrable (by norm_num)).abs
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) (hH L ⟨by linarith, by linarith⟩)
  calc ∫ s in Ico ((L : ℝ) - 1) L, (f s - f (s + h)) ^ 2
      ≤ ∫ s in Ico ((L : ℝ) - 1) L, 2 * H * |f s - f (s + h)| :=
        setIntegral_mono_on hd.integrable_sq.integrableOn (hab.const_mul _) measurableSet_Ico
          fun s hs => by
          have h1 := abs_le.mp (hH s ⟨hs.1, by linarith [hs.2]⟩)
          have h2' := abs_le.mp (hH (s + h) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
          have hdd : |f s - f (s + h)| ≤ 2 * H := abs_le.mpr ⟨by linarith, by linarith⟩
          rw [← sq_abs]; nlinarith [abs_nonneg (f s - f (s + h))]
    _ = 2 * H * ∫ s in Ico ((L : ℝ) - 1) L, |f s - f (s + h)| := integral_const_mul _ _
    _ ≤ 2 * H * (h * V) := mul_le_mul_of_nonneg_left hV (by positivity)

/-- A block's translation energy against the mass of its doubled block. -/
theorem block_le_mass {f : ℝ → ℝ} (h2 : MemLp f 2 volume) {L : ℕ} {h : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1) :
    ∫ s in Ico ((L : ℝ) - 1) L, (f s - f (s + h)) ^ 2
      ≤ 4 * ∫ s in Icc ((L : ℝ) - 1) (L + 1), f s ^ 2 := by
  set A := ∫ s in Icc ((L : ℝ) - 1) (L + 1), f s ^ 2 with hA
  have hsq := h2.integrable_sq
  have hs := (memLp_shift h2 h).integrable_sq
  have hnn : 0 ≤ᵐ[volume.restrict (Icc ((L : ℝ) - 1) (L + 1))] fun s => f s ^ 2 :=
    Eventually.of_forall fun s => sq_nonneg _
  have hA1 : ∫ s in Ico ((L : ℝ) - 1) L, f s ^ 2 ≤ A :=
    setIntegral_mono_set hsq.integrableOn hnn
      (Eventually.of_forall (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))))
  have hA2 : ∫ s in Ico ((L : ℝ) - 1) L, f (s + h) ^ 2 ≤ A := by
    rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_add_right (fun s => f s ^ 2) h,
      intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set hsq.integrableOn hnn
      (Eventually.of_forall (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) (by linarith))))
  have hle : ∫ s in Ico ((L : ℝ) - 1) L, (f s - f (s + h)) ^ 2
      ≤ ∫ s in Ico ((L : ℝ) - 1) L, (2 * f s ^ 2 + 2 * f (s + h) ^ 2) :=
    integral_mono (memLp_sub_shift h2 h).integrable_sq.integrableOn
      ((hsq.const_mul 2).add (hs.const_mul 2)).integrableOn
      fun s => by nlinarith [sq_nonneg (f s + f (s + h))]
  rw [integral_add (hsq.const_mul 2).integrableOn (hs.const_mul 2).integrableOn,
    integral_const_mul, integral_const_mul] at hle
  linarith

/-- The doubled blocks cover `ℝ` at most twice. -/
theorem sum_range_mass_le {f : ℝ → ℝ} (h2 : MemLp f 2 volume) (N : ℕ) :
    ∑ L ∈ Finset.range N, ∫ s in Icc ((L : ℝ) - 1) (L + 1), f s ^ 2 ≤ 2 * ∫ s, f s ^ 2 := by
  have hsq := h2.integrable_sq
  have hnn : 0 ≤ᵐ[volume] fun s => f s ^ 2 := Eventually.of_forall fun s => sq_nonneg _
  have hsplit : ∀ L : ℕ, ∫ s in Icc ((L : ℝ) - 1) (L + 1), f s ^ 2
      = (∫ s in ((L : ℝ) - 1)..L, f s ^ 2) + ∫ s in (L : ℝ)..(L + 1), f s ^ 2 := by
    intro L
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_add_adjacent_intervals hsq.intervalIntegrable
        hsq.intervalIntegrable]
  have hfull : ∀ a b : ℝ, a ≤ b → ∫ s in a..b, f s ^ 2 ≤ ∫ s, f s ^ 2 := fun a b hab => by
    rw [intervalIntegral.integral_of_le hab]; exact setIntegral_le_integral hsq hnn
  have e1 := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun s => f s ^ 2) (a := fun k : ℕ => (k : ℝ) - 1) (n := N)
    fun k _ => hsq.intervalIntegrable
  have e2 := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun s => f s ^ 2) (a := fun k : ℕ => (k : ℝ)) (n := N)
    fun k _ => hsq.intervalIntegrable
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.cast_zero] at e1 e2
  simp only [hsplit, Finset.sum_add_distrib, e1, e2]
  have := hfull (0 - 1) (N - 1) (by have : (0:ℝ) ≤ N := N.cast_nonneg; linarith)
  have := hfull 0 N N.cast_nonneg
  linarith

/-- The doubled-block masses sum to at most `2‖f‖²`. -/
theorem tsum_mass_le {f : ℝ → ℝ} (h2 : MemLp f 2 volume) :
    ∑' L : ℕ, ∫ s in Icc ((L : ℝ) - 1) (L + 1), f s ^ 2 ≤ 2 * ∫ s, f s ^ 2 :=
  Real.tsum_le_of_sum_range_le (fun _ => setIntegral_nonneg measurableSet_Icc
    fun _ _ => sq_nonneg _) (sum_range_mass_le h2)

/-- **The block lemma.**  The Lévy integral of a function vanishing on `(-∞, 0]`, bounded by
its unit-block sups `H`, variations `V` and doubled-block mass bounds `ā`. -/
theorem archFull_le_block {f : ℝ → ℝ} (h2 : MemLp f 2 volume) (hf0 : ∀ s ≤ 0, f s = 0)
    {H V abar : ℕ → ℝ} (habar : ∀ L, 0 < abar L)
    (hH : ∀ L : ℕ, ∀ s ∈ Icc ((L : ℝ) - 1) (L + 1), |f s| ≤ H L)
    (hV : ∀ L : ℕ, ∀ h ∈ Ioc (0 : ℝ) 1, ∫ s in Ico ((L : ℝ) - 1) L, |f s - f (s + h)| ≤ h * V L)
    (ha : ∀ L : ℕ, ∫ s in Icc ((L : ℝ) - 1) (L + 1), f s ^ 2 ≤ abar L)
    (hsum : Summable fun L => abar L * max 1 (Real.log (H L * V L / (2 * abar L)))) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume ∧
      Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f
        ≤ (2 * D2 + 6) * (∫ s, f s ^ 2)
          + 2 * ∑' L, abar L * max 1 (Real.log (H L * V L / (2 * abar L))) := by
  set a : ℕ → ℝ := fun L => ∫ s in Icc ((L : ℝ) - 1) (L + 1), f s ^ 2 with hadef
  set T : ℕ → ℝ := fun L => abar L * max 1 (Real.log (H L * V L / (2 * abar L))) with hT
  set F : ℕ → ℝ → ℝ := fun L u => (1 / u + 1 / 4) * min (2 * a L) (H L * V L * u / 2) with hF
  have ha0 : ∀ L, 0 ≤ a L := fun L => setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  have hH0 : ∀ L : ℕ, 0 ≤ H L := fun L =>
    le_trans (abs_nonneg _) (hH L L ⟨by linarith, by linarith⟩)
  have hV0 : ∀ L : ℕ, 0 ≤ V L := fun L => by
    have := hV L 1 ⟨one_pos, le_rfl⟩
    have h0 : 0 ≤ ∫ s in Ico ((L : ℝ) - 1) L, |f s - f (s + 1)| :=
      setIntegral_nonneg measurableSet_Ico fun _ _ => abs_nonneg _
    linarith
  have hK0 : ∀ L, 0 ≤ H L * V L := fun L => mul_nonneg (hH0 L) (hV0 L)
  have haT : ∀ L, a L ≤ T L := fun L =>
    (ha L).trans (le_mul_of_one_le_right (habar L).le (le_max_left _ _))
  have hasum : Summable a := Summable.of_nonneg_of_le ha0 haT hsum
  have hF0 : ∀ L, ∀ u, 0 ≤ u → 0 ≤ F L u := fun L u hu => by
    have : 0 ≤ min (2 * a L) (H L * V L * u / 2) :=
      le_min (by linarith [ha0 L]) (by have := hK0 L; positivity)
    simp only [hF]; positivity
  -- each block's kernel integral
  have hFint : ∀ L, IntegrableOn (F L) (Ioc 0 2) := fun L => integrableOn_kernel (ha0 L) (hK0 L)
  have hFbd : ∀ L, ∫ u in Ioc (0 : ℝ) 2, F L u ≤ 3 * a L + 2 * T L := fun L => by
    have h1 := integral_kernel_le_of_nonneg (ha0 L) (hK0 L)
    have h2' := mul_log_le_of_le (ha0 L) (ha L) (habar L) (hK0 L)
    simp only [hF, hT]; linarith
  have hFI0 : ∀ L, 0 ≤ ∫ u in Ioc (0 : ℝ) 2, F L u := fun L =>
    setIntegral_nonneg measurableSet_Ioc fun u hu => hF0 L u hu.1.le
  have hsumI : Summable fun L => ∫ u in Ioc (0 : ℝ) 2, F L u :=
    Summable.of_nonneg_of_le hFI0 hFbd ((hasum.mul_left 3).add (hsum.mul_left 2))
  -- pointwise: the Lévy integrand under the summed kernels
  have hpt : ∀ u ∈ Ioc (0 : ℝ) 2, Summable (fun L => F L u) ∧
      Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u ≤ ∑' L, F L u := by
    intro u hu
    have hu0 := hu.1
    have hsF : Summable fun L => F L u := by
      refine Summable.of_nonneg_of_le (fun L => hF0 L u hu0.le) (fun L => ?_)
        (hsum.mul_left ((1 / u + 1 / 4) * 2))
      have : min (2 * a L) (H L * V L * u / 2) ≤ 2 * T L :=
        (min_le_left _ _).trans (by linarith [haT L])
      simp only [hF]
      calc (1 / u + 1 / 4) * min (2 * a L) (H L * V L * u / 2)
          ≤ (1 / u + 1 / 4) * (2 * T L) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = (1 / u + 1 / 4) * 2 * T L := by ring
    refine ⟨hsF, ?_⟩
    have hB := (hasSum_blocks h2 hf0 (h := u / 2) (by linarith [hu.2])).mul_left
      (densityU u * (1 / 2))
    rw [levy_eq_half h2, ← mul_assoc]
    refine hasSum_le (fun L => ?_) hB hsF.hasSum
    have hBnn : 0 ≤ ∫ s in Ico ((L : ℝ) - 1) L, (f s - f (s + u / 2)) ^ 2 :=
      setIntegral_nonneg measurableSet_Ico fun _ _ => sq_nonneg _
    have hm := block_le_mass h2 (L := L) (h := u / 2) (by positivity) (by linarith [hu.2])
    have hv := block_le_var h2 (L := L) (by positivity : (0 : ℝ) < u / 2) (by linarith [hu.2])
      (hH L) (hV L (u / 2) ⟨by positivity, by linarith [hu.2]⟩)
    have hmin : (1 / 2) * ∫ s in Ico ((L : ℝ) - 1) L, (f s - f (s + u / 2)) ^ 2
        ≤ min (2 * a L) (H L * V L * u / 2) :=
      le_min (by simp only [hadef]; linarith) (by linarith)
    simp only [hF]
    rw [mul_assoc]
    exact mul_le_mul (densityU_le hu0) hmin (by positivity) (by positivity)
  -- the near piece through the lower integral
  have hlnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 2)] Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => levy_nonneg h2 hu.1
  have hlint : ∫⁻ u in Ioc (0 : ℝ) 2, ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u)
      ≤ ENNReal.ofReal (∑' L, ∫ u in Ioc (0 : ℝ) 2, F L u) := by
    calc ∫⁻ u in Ioc (0 : ℝ) 2, ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u)
        ≤ ∫⁻ u in Ioc (0 : ℝ) 2, ∑' L, ENNReal.ofReal (F L u) := by
          refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun L => hF0 L u hu.1.le) (hpt u hu).1]
          exact ENNReal.ofReal_le_ofReal (hpt u hu).2
      _ = ∑' L, ∫⁻ u in Ioc (0 : ℝ) 2, ENNReal.ofReal (F L u) :=
          lintegral_tsum fun L =>
            (by simp only [hF]; fun_prop : Measurable (F L)).ennreal_ofReal.aemeasurable
      _ = ∑' L, ENNReal.ofReal (∫ u in Ioc (0 : ℝ) 2, F L u) := by
          congr 1; funext L
          exact (ofReal_integral_eq_lintegral_ofReal (hFint L)
            (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => hF0 L u hu.1.le)).symm
      _ = ENNReal.ofReal (∑' L, ∫ u in Ioc (0 : ℝ) 2, F L u) :=
          (ENNReal.ofReal_tsum_of_nonneg hFI0 hsumI).symm
  have hI1 : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioc 0 2) :=
    ⟨(measurable_levy h2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hlnn).mpr (lt_of_le_of_lt hlint ENNReal.ofReal_lt_top)⟩
  have hnear : ∫ u in Ioc (0 : ℝ) 2, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u
      ≤ 3 * ∑' L, a L + 2 * ∑' L, T L := by
    rw [integral_eq_lintegral_of_nonneg_ae hlnn (measurable_levy h2).aestronglyMeasurable]
    refine (ENNReal.toReal_le_of_le_ofReal (tsum_nonneg hFI0) hlint).trans ?_
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (hasum.mul_left 3) (hsum.mul_left 2)]
    exact Summable.tsum_le_tsum hFbd hsumI ((hasum.mul_left 3).add (hsum.mul_left 2))
  have hI2 := integrableOn_levy_Ioi_two h2
  have hfar := integral_levy_Ioi_two_le h2
  have hmass := tsum_mass_le h2
  have hunion : Ioc (0 : ℝ) 2 ∪ Ioi 2 = Ioi 0 := Ioc_union_Ioi_eq_Ioi (by norm_num)
  refine ⟨hunion ▸ hI1.union hI2, ?_⟩
  show ∫ u in Ioi (0 : ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u ≤ _
  rw [← hunion, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hI1 hI2]
  have hT' : ∑' L, T L = ∑' L, abar L * max 1 (Real.log (H L * V L / (2 * abar L))) := rfl
  rw [← hT']
  nlinarith

/-- The Lévy integrand of a difference, in the two translation differences. -/
theorem levy_sub_eq {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (u : ℝ) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (f - g) u = densityU u * ((1 / 2) *
      ∫ s, ((f s - f (s + u / 2)) - (g s - g (s + u / 2))) ^ 2) := by
  rw [levy_eq_half (hf.sub hg)]
  congr 3; funext s; simp only [Pi.sub_apply]; ring

/-- The Lévy integrand of a difference is at most twice the sum of the two integrands. -/
theorem levy_sub_le {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) {u : ℝ}
    (hu : 0 < u) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (f - g) u
      ≤ 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u + 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g u := by
  have hA := (memLp_sub_shift hf (u / 2)).integrable_sq
  have hB := (memLp_sub_shift hg (u / 2)).integrable_sq
  have hle : ∫ s, ((f s - f (s + u / 2)) - (g s - g (s + u / 2))) ^ 2
      ≤ ∫ s, (2 * (f s - f (s + u / 2)) ^ 2 + 2 * (g s - g (s + u / 2)) ^ 2) :=
    integral_mono ((memLp_sub_shift hf (u / 2)).sub (memLp_sub_shift hg (u / 2))).integrable_sq
      ((hA.const_mul 2).add (hB.const_mul 2))
      fun s => by nlinarith [sq_nonneg ((f s - f (s + u / 2)) + (g s - g (s + u / 2)))]
  rw [integral_add (hA.const_mul 2) (hB.const_mul 2), integral_const_mul,
    integral_const_mul] at hle
  rw [levy_sub_eq hf hg, levy_eq_half hf, levy_eq_half hg]
  have hd := (densityU_pos hu).le
  nlinarith [mul_le_mul_of_nonneg_left hle hd]

/-- A difference of functions of finite Lévy energy has finite Lévy energy. -/
theorem integrableOn_levy_sub {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hlf : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume)
    (hlg : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Ioi 0) volume) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (f - g)) (Ioi 0) volume := by
  refine Integrable.mono' ((hlf.const_mul 2).add (hlg.const_mul 2))
    (measurable_levy (hf.sub hg)).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (levy_nonneg (hf.sub hg) hu)]
  exact levy_sub_le hf hg hu

/-- Pointwise, the Lévy integrand of a difference dominates the expanded square with the
cross term replaced by its Cauchy-Schwarz bound. -/
theorem levy_add_levy_sub_le {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    {u : ℝ} (hu : 0 < u) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u + Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g u
        - 2 * (√(Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u) * √(Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g u))
      ≤ Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (f - g) u := by
  have mf := memLp_sub_shift hf (u / 2)
  have mg := memLp_sub_shift hg (u / 2)
  set A := ∫ s, (f s - f (s + u / 2)) ^ 2 with hAdef
  set B := ∫ s, (g s - g (s + u / 2)) ^ 2 with hBdef
  set C := ∫ s, (f s - f (s + u / 2)) * (g s - g (s + u / 2)) with hCdef
  set r := densityU u * (1 / 2) with hr
  have hr0 : 0 ≤ r := by have := densityU_pos hu; positivity
  have hA0 : 0 ≤ A := integral_nonneg fun s => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun s => sq_nonneg _
  have hexp : ∫ s, ((f s - f (s + u / 2)) - (g s - g (s + u / 2))) ^ 2 = A - 2 * C + B := by
    have e : ∀ s, ((f s - f (s + u / 2)) - (g s - g (s + u / 2))) ^ 2
        = ((f s - f (s + u / 2)) ^ 2 - 2 * ((f s - f (s + u / 2)) * (g s - g (s + u / 2))))
          + (g s - g (s + u / 2)) ^ 2 := fun s => by ring
    have i2 : Integrable (fun s => 2 * ((f s - f (s + u / 2)) * (g s - g (s + u / 2)))) :=
      (mf.integrable_mul mg).const_mul 2
    have i1 : Integrable (fun s => (f s - f (s + u / 2)) ^ 2
        - 2 * ((f s - f (s + u / 2)) * (g s - g (s + u / 2)))) := mf.integrable_sq.sub i2
    simp_rw [e]
    rw [integral_add i1 mg.integrable_sq, integral_sub mf.integrable_sq i2, integral_const_mul]
  have hC : C ≤ √A * √B :=
    (le_abs_self C).trans (Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le mf mg)
  have hlf : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u = r * A := by rw [levy_eq_half hf]; ring
  have hlg : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g u = r * B := by rw [levy_eq_half hg]; ring
  have hlfg : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (f - g) u = r * (A - 2 * C + B) := by
    rw [levy_sub_eq hf hg, hexp]; ring
  have hsq : √(r * A) * √(r * B) = r * (√A * √B) := by
    rw [Real.sqrt_mul hr0, Real.sqrt_mul hr0]
    have := Real.mul_self_sqrt hr0
    linear_combination (√A * √B) * this
  rw [hlf, hlg, hlfg, hsq]
  nlinarith [mul_le_mul_of_nonneg_left hC hr0]

/-- **`√archFull` is a seminorm on the functions of finite Lévy energy.** -/
theorem abs_sqrt_archFull_sub_le {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hlf : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume)
    (hlg : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Ioi 0) volume) :
    |√(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f) - √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g)|
      ≤ √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (f - g)) := by
  set μ := volume.restrict (Ioi (0 : ℝ))
  set lf := Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f
  set lg := Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g
  have hEf : Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f = ∫ u, lf u ∂μ := rfl
  have hEg : Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g = ∫ u, lg u ∂μ := rfl
  have hEfg : Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (f - g)
      = ∫ u, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (f - g) u ∂μ := rfl
  have hmf : AEStronglyMeasurable (fun u => √(lf u)) μ :=
    (measurable_levy hf).sqrt.aestronglyMeasurable
  have hmg : AEStronglyMeasurable (fun u => √(lg u)) μ :=
    (measurable_levy hg).sqrt.aestronglyMeasurable
  have hsqf : (fun u => √(lf u) ^ 2) =ᵐ[μ] lf :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => Real.sq_sqrt (levy_nonneg hf hu)
  have hsqg : (fun u => √(lg u) ^ 2) =ᵐ[μ] lg :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => Real.sq_sqrt (levy_nonneg hg hu)
  have hp : Integrable (fun u => √(lf u) * √(lg u)) μ := by
    refine Integrable.mono' ((hlf.add hlg).div_const 2) (hmf.mul hmg)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    have h1 := Real.sq_sqrt (levy_nonneg hf hu)
    have h2 := Real.sq_sqrt (levy_nonneg hg hu)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (√(lf u) - √(lg u))]
  have hCS : ∫ u, √(lf u) * √(lg u) ∂μ
      ≤ √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f) * √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g) := by
    have hMf : MemLp (fun u => √(lf u)) (ENNReal.ofReal 2) μ := by
      rw [ENNReal.ofReal_ofNat]
      exact (memLp_two_iff_integrable_sq hmf).mpr (Integrable.congr hlf hsqf.symm)
    have hMg : MemLp (fun u => √(lg u)) (ENNReal.ofReal 2) μ := by
      rw [ENNReal.ofReal_ofNat]
      exact (memLp_two_iff_integrable_sq hmg).mpr (Integrable.congr hlg hsqg.symm)
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
      (Eventually.of_forall fun u => Real.sqrt_nonneg (lf u))
      (Eventually.of_forall fun u => Real.sqrt_nonneg (lg u)) hMf hMg
    simp only [Real.rpow_two] at h
    rw [integral_congr_ae hsqf, integral_congr_ae hsqg] at h
    rwa [hEf, hEg, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hlow : ∫ u, (lf u + lg u - 2 * (√(lf u) * √(lg u))) ∂μ
      ≤ ∫ u, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (f - g) u ∂μ :=
    setIntegral_mono_on ((hlf.add hlg).sub (hp.const_mul 2))
      (integrableOn_levy_sub hf hg hlf hlg) measurableSet_Ioi
      fun u hu => levy_add_levy_sub_le hf hg hu
  have i12 : Integrable (fun u => lf u + lg u) μ := hlf.add hlg
  have i3 : Integrable (fun u => 2 * (√(lf u) * √(lg u))) μ := hp.const_mul 2
  rw [integral_sub i12 i3, integral_add hlf hlg,
    integral_const_mul, ← hEf, ← hEg, ← hEfg] at hlow
  have hf0 := archFull_nonneg hf
  have hg0 := archFull_nonneg hg
  apply Real.abs_le_sqrt
  have e1 := Real.sq_sqrt hf0
  have e2 := Real.sq_sqrt hg0
  nlinarith

end Cvs.WeilForm.Archimedean.LevyUnitBlocks
