import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.PoleTermSplit

/-!
# The entire summand's horizontals vanish

`PoleTermSplit` split the second pole term into an entire part `dslope (ofCritical h) 1` and an
explicit pole.
-/

namespace Cvs.Zeta.ExplicitFormula.EntireSummandHorizontals
open Cvs.Detection

open Complex MeasureTheory Filter
open scoped Real Topology

/-- **The difference quotient decays like `1/|Im z|`** on the strip — no better,
since its numerator carries the constant `G 1`. -/
theorem norm_poleTwoEntire_le {h : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    {z : ℂ} (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 2) (h3 : 1 ≤ |z.im|) :
    ‖Cvs.Detection.poleTwoEntire h z‖ ≤ (A + ‖Cvs.Zeta.ofCritical h 1‖) / |z.im| := by
  have hzne : z ≠ 1 := by
    intro hz
    rw [hz] at h3
    norm_num at h3
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hzne
  have hnorm : |z.im| ≤ ‖z - 1‖ := by
    have := Complex.abs_im_le_norm (z - 1)
    simpa using this
  have himpos : (0 : ℝ) < |z.im| := by linarith
  have hnpos : (0 : ℝ) < ‖z - 1‖ := by linarith
  have hGz : ‖Cvs.Zeta.ofCritical h z‖ ≤ A := by
    refine (hdec z (by linarith) h2).trans ?_
    have hden : (1 : ℝ) ≤ (1 + |z.im|) ^ 3 := by
      have h0 : (1 : ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
      calc (1 : ℝ) = 1 ^ 3 := by norm_num
        _ ≤ (1 + |z.im|) ^ 3 := pow_le_pow_left₀ (by norm_num) h0 3
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hA, hden]
  show ‖dslope (Cvs.Zeta.ofCritical h) 1 z‖ ≤ _
  rw [dslope_of_ne _ hzne, slope_def_field, norm_div]
  rw [div_le_div_iff₀ hnpos himpos]
  have hnum : ‖Cvs.Zeta.ofCritical h z - Cvs.Zeta.ofCritical h 1‖
      ≤ A + ‖Cvs.Zeta.ofCritical h 1‖ := by
    refine (norm_sub_le _ _).trans ?_
    linarith
  nlinarith [hnum, hnorm, himpos, norm_nonneg (Cvs.Zeta.ofCritical h 1), hA]

/-- The horizontal at height `±R`, bounded by `O(1/R)`. -/
theorem horizontal_le {h : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    {t : ℝ} (R : ℝ) (hR : 1 ≤ R) (ht : |t| = R) :
    ‖∫ x in (1 / 2 : ℝ)..2, Cvs.Detection.poleTwoEntire h ((x : ℂ) + (t : ℝ) * I)‖
      ≤ 3 / 2 * ((A + ‖Cvs.Zeta.ofCritical h 1‖) / R) := by
  have hunif : ∀ x ∈ Set.uIoc (1 / 2 : ℝ) 2,
      ‖Cvs.Detection.poleTwoEntire h ((x : ℂ) + (t : ℝ) * I)‖
        ≤ (A + ‖Cvs.Zeta.ofCritical h 1‖) / R := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
    have hre : (((x : ℂ) + (t : ℝ) * I)).re = x := by simp
    have him : (((x : ℂ) + (t : ℝ) * I)).im = t := by simp
    have hb := norm_poleTwoEntire_le hA hdec (z := (x : ℂ) + (t : ℝ) * I)
      (by rw [hre]; exact le_of_lt hx.1) (by rw [hre]; exact hx.2)
      (by rw [him, ht]; exact hR)
    rwa [him, ht] at hb
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hunif).trans (le_of_eq ?_)
  rw [show |(2 : ℝ) - 1 / 2| = 3 / 2 from by rw [abs_of_nonneg] <;> norm_num]
  ring

theorem tendsto_horizontal {h : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    Tendsto (fun R : ℝ => ∫ x in (1 / 2 : ℝ)..2,
        Cvs.Detection.poleTwoEntire h ((x : ℂ) + (R : ℝ) * I)) atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun R : ℝ => 3 / 2 * ((A + ‖Cvs.Zeta.ofCritical h 1‖) / R)) atTop (𝓝 0) := by
    have hh : Tendsto (fun R : ℝ => (A + ‖Cvs.Zeta.ofCritical h 1‖) / R) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
    have := hh.const_mul (3 / 2 : ℝ)
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  exact horizontal_le hA hdec R hR (abs_of_nonneg (by linarith))

theorem tendsto_horizontal_neg {h : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    Tendsto (fun R : ℝ => ∫ x in (1 / 2 : ℝ)..2,
        Cvs.Detection.poleTwoEntire h ((x : ℂ) + (-R : ℝ) * I)) atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun R : ℝ => 3 / 2 * ((A + ‖Cvs.Zeta.ofCritical h 1‖) / R)) atTop (𝓝 0) := by
    have hh : Tendsto (fun R : ℝ => (A + ‖Cvs.Zeta.ofCritical h 1‖) / R) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
    have := hh.const_mul (3 / 2 : ℝ)
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  exact horizontal_le hA hdec R hR (by rw [abs_neg, abs_of_nonneg (by linarith)])

end Cvs.Zeta.ExplicitFormula.EntireSummandHorizontals
