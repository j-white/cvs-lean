import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.SineLevyFirstMoment
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf

/-!
# The Lévy representation of the imaginary half

    ∫₀^∞ sin(tu/2)·densityU u du = archSymbolIm t

The sine companion to `Cvs.Zeta.DigammaLimitDischarged`. Its integrand changes sign, so the interchange runs on a
summable majorant — `|sin x| ≤ |x|` against `Cvs.WeilForm.Archimedean.SineLevyFirstMoment`'s first moment, since `|sin| ≤ 1` diverges.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set Filter Topology Cvs.Zeta

namespace Cvs.WeilForm.Archimedean.LevyImaginaryHalf

open Cvs.WeilForm.Archimedean.SineLevyFirstMoment Cvs.WeilForm.Archimedean.SymbolImaginaryHalf

/-- The `k`-th sine Lévy integrand. -/
def termSin (t : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  Real.sin (t / 2 * u) * Real.exp (-((1 / 4 + (k : ℝ)) * u))

theorem coeff_pos (k : ℕ) : (0:ℝ) < 1 / 4 + (k : ℝ) := by
  have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith

theorem integrable_termSin (t : ℝ) (k : ℕ) : IntegrableOn (termSin t k) (Ioi 0) :=
  integrableOnSin (coeff_pos k) (t / 2)

/-- **The `k`-th integral is the `k`-th term of the series.** -/
theorem integral_termSin (t : ℝ) (k : ℕ) :
    (∫ u in Ioi (0:ℝ), termSin t k u) = imTerm t k := by
  simp only [termSin, imTerm]
  exact integral_sin_mul_exp (coeff_pos k) (t / 2)

/-- The majorant: `|sin x| ≤ |x|` against the first moment. -/
theorem integral_norm_le (t : ℝ) (k : ℕ) :
    (∫ u in Ioi (0:ℝ), ‖termSin t k u‖) ≤ |t| / 2 * (1 / (1 / 4 + (k : ℝ)) ^ 2) := by
  have hc := coeff_pos k
  have hmaj : IntegrableOn (fun u : ℝ => |t| / 2 * (u * Real.exp (-((1 / 4 + (k : ℝ)) * u))))
      (Ioi 0) := (integrableOnId hc).const_mul _
  have hle : ∀ u ∈ Ioi (0:ℝ), ‖termSin t k u‖
      ≤ |t| / 2 * (u * Real.exp (-((1 / 4 + (k : ℝ)) * u))) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    have hE : (0:ℝ) < Real.exp (-((1 / 4 + (k : ℝ)) * u)) := Real.exp_pos _
    have hs : |Real.sin (t / 2 * u)| ≤ |t| / 2 * u := by
      refine Real.abs_sin_le_abs.trans ?_
      rw [abs_mul, abs_of_pos hu0, abs_div]
      norm_num
    rw [termSin, Real.norm_eq_abs, abs_mul, abs_of_pos hE, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hs hE.le
  have hint := setIntegral_mono_on ((integrable_termSin t k).norm) hmaj measurableSet_Ioi hle
  refine hint.trans_eq ?_
  rw [integral_const_mul, integral_id_mul_exp hc]

theorem summable_integral_norm (t : ℝ) :
    Summable fun k : ℕ => ∫ u in Ioi (0:ℝ), ‖termSin t k u‖ := by
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun u => norm_nonneg _)
    (integral_norm_le t) ?_
  have hb : Summable fun k : ℕ => (1 : ℝ) / (1 / 4 + (k : ℝ)) ^ 2 := by
    have hbase : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
      have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      simpa using (summable_nat_add_iff 1).mpr h
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (hbase.mul_left 16)
    have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hp : (0:ℝ) < 1 / 4 + (k : ℝ) := by linarith
    have hlow : ((k : ℝ) + 1) ^ 2 / 16 ≤ (1 / 4 + (k : ℝ)) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 / 4 + (k : ℝ)) ^ 2)]
    have h1 : 16 * (1 / ((k : ℝ) + 1) ^ 2) * (((k : ℝ) + 1) ^ 2 / 16) = 1 := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hlow
      (by positivity : (0:ℝ) ≤ 16 * (1 / ((k : ℝ) + 1) ^ 2))
    linarith [h1, h2]
  exact hb.mul_left _

/-- **The terms sum pointwise to the sine against the density**, off the origin. -/
theorem hasSum_termSin {u : ℝ} (hu : 0 < u) (t : ℝ) :
    HasSum (fun k => termSin t k u) (Real.sin (t / 2 * u) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u) :=
  (Cvs.WeilForm.Archimedean.LevyDensity.hasSum_exp u hu).mul_left _

/-- **The Lévy representation of the imaginary half.** -/
theorem integral_rep_im (t : ℝ) :
    (∫ u in Ioi (0:ℝ), Real.sin (t / 2 * u) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u)
      = archSymbolIm t := by
  have hHS := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0:ℝ))) (F := termSin t)
    (fun k => integrable_termSin t k) (summable_integral_norm t)
  have hae : (∫ u in Ioi (0:ℝ), ∑' k, termSin t k u)
      = ∫ u in Ioi (0:ℝ), Real.sin (t / 2 * u) * Cvs.WeilForm.Archimedean.LevyDensity.densityU u :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => (hasSum_termSin hu t).tsum_eq
  have hdef : (fun k => ∫ u in Ioi (0:ℝ), termSin t k u) = imTerm t :=
    funext (integral_termSin t)
  rw [hdef] at hHS
  rw [← hae]
  exact tendsto_nhds_unique hHS.tendsto_sum_nat (hasSum_imTerm t).tendsto_sum_nat

end Cvs.WeilForm.Archimedean.LevyImaginaryHalf
