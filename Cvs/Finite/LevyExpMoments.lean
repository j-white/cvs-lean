import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.KernelLipschitzOrigin
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.Finite.LevyKernelIncrement
import Cvs.WeilForm.Archimedean.LevyDensity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Lévy channel as a series of exponential moments

The bracket `K(0) − Kc(u/2)` grows at most linearly in the lag on the whole half-line, the cut
kernel vanishing past the edge, so against each exponential of the density's series the integral
is finite and their sum over the poles converges; the Lévy pairing is therefore the sum over `k`
of the bracket's moments against `exp(−(k + 1/4) u)`.
-/

noncomputable section

open Real MeasureTheory Set

namespace Cvs.Finite.LevyExpMoments

open Cvs.Finite.CosineModeOverlap Cvs.Finite.LevyKernelIncrement

/-- The slope the bracket is charged at, on the whole half-line. -/
def slope (L : ℝ) (m n : ℤ) : ℝ := (2 / L + 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / L) / 2 + 1 / L

theorem slope_nonneg {L : ℝ} (hL : 0 < L) (m n : ℤ) : 0 ≤ slope L m n := by
  unfold slope; positivity

/-- **The bracket grows at most linearly in the lag**, across the edge and beyond it. -/
theorem abs_bracket_le {L : ℝ} (hL : 0 < L) (m n : ℤ) {u : ℝ} (hu : 0 ≤ u) :
    |K L m n 0 - Kc L m n (u / 2)| ≤ slope L m n * u := by
  by_cases h : u / 2 ≤ L
  · rw [Kc_of_le h]
    have hK := Cvs.Finite.KernelLipschitzOrigin.abs_K_sub_le hL m n (u / 2)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)] at hK
    have h1 : (0 : ℝ) ≤ 1 / L * u := by positivity
    unfold slope
    linarith
  · push Not at h
    rw [Kc_of_gt h, sub_zero]
    have hK0 : |K L m n 0| ≤ 2 := by
      unfold K
      split_ifs
      · simp
      · simp
    have hL2 : 2 * L < u := by linarith
    have h1 : (2 : ℝ) ≤ 1 / L * u := by
      rw [one_div_mul_eq_div, le_div_iff₀ hL]; linarith
    have h2 : (0 : ℝ) ≤ (2 / L + 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / L) / 2 * u := by positivity
    unfold slope
    linarith

/-- The `k`-th exponential moment of the bracket. -/
def moment (L : ℝ) (m n : ℤ) (k : ℕ) : ℝ :=
  ∫ u in Ioi (0:ℝ), Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - Kc L m n (u / 2))

theorem measurable_term (L : ℝ) (m n : ℤ) (k : ℕ) :
    Measurable fun u : ℝ => Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - Kc L m n (u / 2)) := by
  refine (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg).mul ?_
  exact measurable_const.sub ((measurable_Kc L m n).comp (measurable_id.div_const 2))

/-- **The moment of the lag against an exponential**, in closed form. -/
theorem integral_mul_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) :
    ∫ u in Ioi (0:ℝ), u * Real.exp (-(r * u)) = 1 / r ^ 2 := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := r) (by norm_num) hr
  rw [Real.Gamma_two, mul_one] at h
  have h2 : (1 / r) ^ (2 : ℝ) = 1 / r ^ 2 := by
    rw [div_rpow (by norm_num) hr.le, Real.one_rpow, Real.rpow_two]
  rw [h2] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

/-- **The lag against an exponential is integrable on the half-line.** -/
theorem integrableOn_mul_exp_neg_mul {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-(r * u))) (Ioi 0) volume := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((2 : ℝ) - 1)) (Ioi 0) volume :=
    Real.GammaIntegral_convergent (by norm_num)
  have h2 : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi 0) volume := by
    refine h1.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    ring
  have h3 : IntegrableOn (fun x : ℝ => (r * x) * Real.exp (-(r * x))) (Ioi 0) volume := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => x * Real.exp (-x)) 0 hr).mpr
      (by rw [mul_zero]; exact h2)
    exact this
  have h4 : IntegrableOn (fun x : ℝ => 1 / r * ((r * x) * Real.exp (-(r * x)))) (Ioi 0) volume :=
    h3.const_mul (1 / r)
  refine h4.congr_fun (fun u _ => ?_) measurableSet_Ioi
  field_simp

/-- **The summed absolute moments are finite.** -/
theorem lintegral_term_le {L : ℝ} (hL : 0 < L) (m n : ℤ) (k : ℕ) :
    ∫⁻ u in Ioi (0:ℝ), ‖Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - Kc L m n (u / 2))‖ₑ
      ≤ ENNReal.ofReal (slope L m n * (1 / (1 / 4 + (k : ℝ)) ^ 2)) := by
  have hr : (0 : ℝ) < 1 / 4 + (k : ℝ) := by positivity
  have hbound : ∀ u ∈ Ioi (0:ℝ),
      ‖Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - Kc L m n (u / 2))‖
        ≤ slope L m n * (u * Real.exp (-((1 / 4 + (k : ℝ)) * u))) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hb := abs_bracket_le hL m n hu0.le
    have he : (0 : ℝ) ≤ Real.exp (-((1 / 4 + (k : ℝ)) * u)) := (Real.exp_pos _).le
    calc Real.exp (-((1 / 4 + (k : ℝ)) * u)) * |K L m n 0 - Kc L m n (u / 2)|
        ≤ Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (slope L m n * u) :=
          mul_le_mul_of_nonneg_left hb he
      _ = slope L m n * (u * Real.exp (-((1 / 4 + (k : ℝ)) * u))) := by ring
  have hint : IntegrableOn (fun u : ℝ => slope L m n * (u * Real.exp (-((1 / 4 + (k : ℝ)) * u))))
      (Ioi 0) volume := by
    exact (integrableOn_mul_exp_neg_mul hr).const_mul (slope L m n)
  calc ∫⁻ u in Ioi (0:ℝ), ‖Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - Kc L m n (u / 2))‖ₑ
      ≤ ∫⁻ u in Ioi (0:ℝ),
          ENNReal.ofReal (slope L m n * (u * Real.exp (-((1 / 4 + (k : ℝ)) * u)))) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbound u hu)
    _ = ENNReal.ofReal (∫ u in Ioi (0:ℝ), slope L m n * (u * Real.exp (-((1 / 4 + (k : ℝ)) * u)))) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)]
        have hu0 : (0 : ℝ) < u := hu
        have := slope_nonneg hL m n
        positivity
    _ = ENNReal.ofReal (slope L m n * (1 / (1 / 4 + (k : ℝ)) ^ 2)) := by
        rw [integral_const_mul, integral_mul_exp_neg_mul_Ioi hr]

theorem summable_bound (L : ℝ) (m n : ℤ) :
    Summable fun k : ℕ => slope L m n * (1 / (1 / 4 + (k : ℝ)) ^ 2) := by
  have hs : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      (add_left_injective 1)
    refine h.congr fun k => ?_
    simp [Function.comp]
  have h16 := hs.mul_left (16 : ℝ)
  refine Summable.mul_left _ (Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h16)
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]

/-- **The Lévy pairing is the sum of the moments.** -/
theorem levyPair_eq_tsum {L : ℝ} (hL : 0 < L) (m n : ℤ) :
    Cvs.Finite.LevyChannelDoubleSum.levyPair L m n = ∑' k : ℕ, moment L m n k := by
  unfold Cvs.Finite.LevyChannelDoubleSum.levyPair moment
  have hpt : ∀ u ∈ Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (K L m n 0 - Kc L m n (u / 2))
      = ∑' k : ℕ, Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - Kc L m n (u / 2)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [← (Cvs.WeilForm.Archimedean.LevyDensity.hasSum_exp u hu0).tsum_eq, tsum_mul_right]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  refine integral_tsum (fun k => (measurable_term L m n k).aestronglyMeasurable) ?_
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun k => lintegral_term_le hL m n k)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by have := slope_nonneg hL m n; positivity)
    (summable_bound L m n)]
  exact ENNReal.ofReal_ne_top

end Cvs.Finite.LevyExpMoments
