import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.KernelLipschitzOrigin
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityIntegrable
import Cvs.WeilForm.Archimedean.LevyMeasure
import Cvs.WeilForm.WindowSetNonempty

/-!
# The Lévy density against a kernel increment is integrable on the half-line

For the CvS kernel cut at the window's length, `u ↦ densityU u · (K 0 − Kc (u/2))` is integrable
on `(0, ∞)`: Lipschitz control of the kernel and the `1/u` pole of the density cancel below the
scale `min 1 (2L)`, and above it the kernel is bounded while the density is integrable.
-/

noncomputable section

open Real MeasureTheory Set

namespace Cvs.Finite.LevyKernelIncrement

/-- The kernel cut at the window's length. -/
def Kc (L : ℝ) (m n : ℤ) (v : ℝ) : ℝ := if v ≤ L then Cvs.Finite.CosineModeOverlap.K L m n v else 0

theorem Kc_of_le {L : ℝ} {m n : ℤ} {v : ℝ} (hv : v ≤ L) :
    Kc L m n v = Cvs.Finite.CosineModeOverlap.K L m n v := if_pos hv

theorem Kc_of_gt {L : ℝ} {m n : ℤ} {v : ℝ} (hv : L < v) : Kc L m n v = 0 := if_neg (not_le.mpr hv)

/-- The kernel is measurable in its lag. -/
theorem measurable_K (L : ℝ) (m n : ℤ) : Measurable (Cvs.Finite.CosineModeOverlap.K L m n) := by
  unfold Cvs.Finite.CosineModeOverlap.K
  by_cases hmn : m = n
  · subst hmn
    simp only [if_true]
    fun_prop
  · simp only [if_neg hmn]
    fun_prop

theorem measurable_Kc (L : ℝ) (m n : ℤ) : Measurable (Kc L m n) :=
  Measurable.ite measurableSet_Iic (measurable_K L m n) measurable_const

/-- The kernel is bounded by an explicit constant on the window. -/
theorem abs_K_le {L : ℝ} (hL : 0 < L) (m n : ℤ) {v : ℝ} (hv0 : 0 ≤ v) (hvL : v ≤ L) :
    |Cvs.Finite.CosineModeOverlap.K L m n v| ≤ 2 + 2 / π := by
  have hπ : 0 < π := Real.pi_pos
  have h2π : 0 ≤ 2 / π := by positivity
  by_cases hmn : m = n
  · subst hmn
    simp only [Cvs.Finite.CosineModeOverlap.K, if_true]
    have h1 : |1 - v / L| ≤ 1 := by
      rw [abs_le]; constructor
      · have : v / L ≤ 1 := by rw [div_le_one hL]; exact hvL
        linarith
      · have : 0 ≤ v / L := by positivity
        linarith
    calc |2 * (1 - v / L) * Real.cos (2 * π * m * v / L)|
        = 2 * |1 - v / L| * |Real.cos (2 * π * m * v / L)| := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      _ ≤ 2 * 1 * 1 := by gcongr; simp [Real.abs_cos_le_one]
      _ ≤ 2 + 2 / π := by linarith
  · simp only [Cvs.Finite.CosineModeOverlap.K, if_neg hmn]
    rw [abs_div]
    have hden : π ≤ |π * ((n : ℝ) - m)| := by
      rw [abs_mul, abs_of_pos hπ]
      have : (1:ℝ) ≤ |(n : ℝ) - m| := by
        have hz : ((n - m : ℤ) : ℝ) = (n : ℝ) - m := by push_cast; ring
        rw [← hz, ← Int.cast_abs]
        have : (1 : ℤ) ≤ |n - m| := Int.one_le_abs (by omega)
        exact_mod_cast this
      nlinarith
    have hnum : |Real.sin (2 * π * m * v / L) - Real.sin (2 * π * n * v / L)| ≤ 2 := by
      calc |Real.sin (2 * π * m * v / L) - Real.sin (2 * π * n * v / L)|
          ≤ |Real.sin (2 * π * m * v / L)| + |Real.sin (2 * π * n * v / L)| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
        _ = 2 := by norm_num
    have hpos : 0 < |π * ((n : ℝ) - m)| := lt_of_lt_of_le hπ hden
    calc |Real.sin (2 * π * m * v / L) - Real.sin (2 * π * n * v / L)| / |π * ((n : ℝ) - m)|
        ≤ 2 / π := by
          rw [div_le_div_iff₀ hpos hπ]
          nlinarith [abs_nonneg (Real.sin (2 * π * m * v / L) - Real.sin (2 * π * n * v / L))]
      _ ≤ 2 + 2 / π := by linarith

/-- The cut kernel is bounded everywhere on the half-line. -/
theorem abs_Kc_le {L : ℝ} (hL : 0 < L) (m n : ℤ) {v : ℝ} (hv0 : 0 ≤ v) :
    |Kc L m n v| ≤ 2 + 2 / π := by
  by_cases hv : v ≤ L
  · rw [Kc_of_le hv]; exact abs_K_le hL m n hv0 hv
  · rw [Kc_of_gt (not_le.mp hv), abs_zero]; positivity

/-- **The Lévy density against the kernel increment is integrable on the half-line.** -/
theorem integrableOn_densityU_mul_K_sub {L : ℝ} (hL : 0 < L) (m n : ℤ) :
    IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (Cvs.Finite.CosineModeOverlap.K L m n 0 - Kc L m n (u / 2))) (Ioi 0) (volume : Measure ℝ) := by
  have hπ : 0 < π := Real.pi_pos
  set C : ℝ := 2 / L + 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / L with hC
  have hC0 : 0 ≤ C := by positivity
  set δ : ℝ := min 1 (2 * L) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδL : δ ≤ 2 * L := min_le_right _ _
  have hmeas : Measurable (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (Cvs.Finite.CosineModeOverlap.K L m n 0 - Kc L m n (u / 2))) := by
    apply Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.mul
    apply measurable_const.sub
    exact (measurable_Kc L m n).comp (measurable_id.div_const 2)
  have hsplit : Ioi (0:ℝ) = Ioc 0 δ ∪ Ioi δ := by
    ext u; simp only [mem_Ioi, mem_union, mem_Ioc]; constructor
    · intro h; by_cases h1 : u ≤ δ
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_le.mp h1)
    · rintro (⟨h, _⟩ | h) <;> linarith
  rw [hsplit]
  apply IntegrableOn.union
  · -- near zero: the Lipschitz increment absorbs the pole of the density
    refine (integrableOn_const (C := 3 * C / 2) (hs := measure_Ioc_lt_top.ne)).mono'
      hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
    obtain ⟨hu0, huδ⟩ := hu
    have hu1 : u ≤ 1 := le_trans huδ hδ1
    have huL : u / 2 ≤ L := by linarith
    rw [Kc_of_le huL, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0)]
    have hK := Cvs.Finite.KernelLipschitzOrigin.abs_K_sub_le hL m n (u / 2)
    rw [abs_of_pos (by linarith : (0:ℝ) < u / 2)] at hK
    have hd := Cvs.WeilForm.WindowSetNonempty.densityU_mul_le hu0 hu1
    have hdpos := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
    calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * |Cvs.Finite.CosineModeOverlap.K L m n 0 - Cvs.Finite.CosineModeOverlap.K L m n (u / 2)|
        ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (C * (u / 2)) := by gcongr
      _ = (Cvs.WeilForm.Archimedean.LevyDensity.densityU u * u) * C / 2 := by ring
      _ ≤ 3 * C / 2 := by gcongr
  · -- away from zero: the kernel is bounded and the density integrable
    refine ((Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU hδ0).const_mul (2 * (2 + 2 / π))).mono'
      hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    have hu0 : 0 < u := lt_trans hδ0 hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0), mul_comm]
    have hdpos := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
    refine mul_le_mul_of_nonneg_right ?_ hdpos.le
    have h1 := abs_K_le hL m n (le_refl 0) hL.le
    have h2 := abs_Kc_le hL m n (by linarith : (0:ℝ) ≤ u / 2)
    calc |Cvs.Finite.CosineModeOverlap.K L m n 0 - Kc L m n (u / 2)|
        ≤ |Cvs.Finite.CosineModeOverlap.K L m n 0| + |Kc L m n (u / 2)| := abs_sub _ _
      _ ≤ (2 + 2 / π) + (2 + 2 / π) := add_le_add h1 h2
      _ = 2 * (2 + 2 / π) := by ring

end Cvs.Finite.LevyKernelIncrement
