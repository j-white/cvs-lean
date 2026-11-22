import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Zeta.WeilPositivityStatement

/-!
# The kernel is Lipschitz at the origin, and the mode sum's self-convolution vanishes beyond the
window

Both are what the Lévy channel needs to act on the double sum term by term.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.KernelLipschitzOrigin

/-- `|1 − cos x| ≤ |x|`. -/
theorem abs_one_sub_cos_le (x : ℝ) : |1 - Real.cos x| ≤ |x| := by
  have h1 : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have h := Real.cos_sq (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  rw [h1]
  have hs : |Real.sin (x / 2)| ≤ |x / 2| := by
    have := Real.abs_sin_sub_sin_le (x / 2) 0
    simpa using this
  have hs1 : |Real.sin (x / 2)| ≤ 1 := Real.abs_sin_le_one _
  calc |2 * Real.sin (x / 2) ^ 2| = 2 * |Real.sin (x / 2)| * |Real.sin (x / 2)| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), sq, abs_mul]; ring
    _ ≤ 2 * 1 * |x / 2| := by gcongr
    _ = |x| := by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; ring

/-- **The kernel's increment from the origin is Lipschitz.** -/
theorem abs_K_sub_le {L : ℝ} (hL : 0 < L) (m n : ℤ) (v : ℝ) :
    |Cvs.Finite.CosineModeOverlap.K L m n 0 - Cvs.Finite.CosineModeOverlap.K L m n v|
      ≤ (2 / L + 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / L) * |v| := by
  have hπ : 0 < π := Real.pi_pos
  have hC : 0 ≤ 2 / L + 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / L := by positivity
  by_cases hmn : m = n
  · subst hmn
    simp only [Cvs.Finite.CosineModeOverlap.K, if_true, eq_self_iff_true]
    -- `2 − 2(1 − v/L)cos(ωv) = 2(1 − cos ωv) + 2(v/L)cos ωv`
    have h : 2 * (1 - 0 / L) * Real.cos (2 * π * m * 0 / L) - 2 * (1 - v / L) * Real.cos (2 * π * m * v / L)
        = 2 * (1 - Real.cos (2 * π * m * v / L)) + 2 * (v / L) * Real.cos (2 * π * m * v / L) := by
      simp; ring
    rw [h]
    have h1 : |2 * (1 - Real.cos (2 * π * m * v / L))| ≤ 2 * (2 * π * |(m : ℝ)| / L) * |v| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have := abs_one_sub_cos_le (2 * π * m * v / L)
      have h2 : |2 * π * (m : ℝ) * v / L| = 2 * π * |(m : ℝ)| / L * |v| := by
        rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos hL, abs_of_pos hπ,
          abs_of_pos (by norm_num : (0:ℝ) < 2)]; ring
      rw [h2] at this
      linarith
    have h2 : |2 * (v / L) * Real.cos (2 * π * m * v / L)| ≤ 2 / L * |v| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_div, abs_of_pos hL]
      have := Real.abs_cos_le_one (2 * π * m * v / L)
      have hv : 0 ≤ |v| / L := by positivity
      calc 2 * (|v| / L) * |Real.cos (2 * π * m * v / L)| ≤ 2 * (|v| / L) * 1 := by gcongr
        _ = 2 / L * |v| := by ring
    calc |2 * (1 - Real.cos (2 * π * m * v / L)) + 2 * (v / L) * Real.cos (2 * π * m * v / L)|
        ≤ |2 * (1 - Real.cos (2 * π * m * v / L))| + |2 * (v / L) * Real.cos (2 * π * m * v / L)| :=
          abs_add_le _ _
      _ ≤ 2 * (2 * π * |(m : ℝ)| / L) * |v| + 2 / L * |v| := add_le_add h1 h2
      _ ≤ (2 / L + 4 * π * (|(m : ℝ)| + |(m : ℝ)|) / L) * |v| := by
          have hgap : (2 / L + 4 * π * (|(m : ℝ)| + |(m : ℝ)|) / L) * |v|
              - (2 * (2 * π * |(m : ℝ)| / L) * |v| + 2 / L * |v|) = 4 * π * |(m : ℝ)| * |v| / L := by
            ring
          have : 0 ≤ 4 * π * |(m : ℝ)| * |v| / L := by positivity
          linarith
  · simp only [Cvs.Finite.CosineModeOverlap.K, if_neg hmn]
    simp only [mul_zero, zero_div, Real.sin_zero, sub_self, zero_sub, abs_neg, abs_div]
    have hden : |π * ((n : ℝ) - m)| ≥ π := by
      rw [abs_mul, abs_of_pos hπ]
      have : (1:ℝ) ≤ |(n : ℝ) - m| := by
        have h : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hmn))
        have hz : ((n - m : ℤ) : ℝ) = (n : ℝ) - m := by push_cast; ring
        rw [← hz, ← Int.cast_abs]
        have : (1 : ℤ) ≤ |n - m| := Int.one_le_abs (by omega)
        exact_mod_cast this
      nlinarith
    have hnum : |Real.sin (2 * π * m * v / L) - Real.sin (2 * π * n * v / L)|
        ≤ 2 * π * (|(m : ℝ)| + |(n : ℝ)|) / L * |v| := by
      have := Real.abs_sin_sub_sin_le (2 * π * m * v / L) (2 * π * n * v / L)
      have h2 : |2 * π * (m : ℝ) * v / L - 2 * π * n * v / L| ≤ 2 * π * (|(m : ℝ)| + |(n : ℝ)|) / L * |v| := by
        have h2π : |(2:ℝ) * π| = 2 * π := abs_of_pos (by positivity)
        rw [show 2 * π * (m : ℝ) * v / L - 2 * π * n * v / L = 2 * π / L * v * ((m : ℝ) - n) by ring,
          abs_mul, abs_mul, abs_div, h2π, abs_of_pos hL]
        have : |(m : ℝ) - n| ≤ |(m : ℝ)| + |(n : ℝ)| := abs_sub _ _
        have hv : 0 ≤ 2 * π / L * |v| := by positivity
        calc 2 * π / L * |v| * |(m : ℝ) - n| ≤ 2 * π / L * |v| * (|(m : ℝ)| + |(n : ℝ)|) := by gcongr
          _ = 2 * π * (|(m : ℝ)| + |(n : ℝ)|) / L * |v| := by ring
      linarith
    have hpos : 0 < |π * ((n : ℝ) - m)| := lt_of_lt_of_le hπ hden
    calc |Real.sin (2 * π * m * v / L) - Real.sin (2 * π * n * v / L)| / |π * ((n : ℝ) - m)|
        ≤ |Real.sin (2 * π * m * v / L) - Real.sin (2 * π * n * v / L)| / π := by
          gcongr
      _ ≤ 2 * π * (|(m : ℝ)| + |(n : ℝ)|) / L * |v| / π := by gcongr
      _ = 2 * (|(m : ℝ)| + |(n : ℝ)|) / L * |v| := by field_simp
      _ ≤ (2 / L + 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / L) * |v| := by
          have : 0 ≤ |v| := abs_nonneg v
          have : 0 ≤ |(m : ℝ)| + |(n : ℝ)| := by positivity
          have h1 : (2 : ℝ) ≤ 4 * π := by nlinarith [Real.pi_gt_three]
          have : 2 * (|(m : ℝ)| + |(n : ℝ)|) / L ≤ 4 * π * (|(m : ℝ)| + |(n : ℝ)|) / L := by
            gcongr
          nlinarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) hL.le]

/-- **The mode sum's self-convolution vanishes at lags of the window's length or more.** -/
theorem selfConvolution_modeSum_eq_zero {ι : Type*} [Fintype ι] {L : ℝ} (mode : ι → ℤ) (xi : ι → ℝ)
    {v : ℝ} (hv : L ≤ v) :
    selfConvolution (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) v = 0 := by
  unfold selfConvolution
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum]
  by_cases hs : s ∈ Ioc (0:ℝ) L
  · have : s + v ∉ Ioc (0:ℝ) L := fun h => by linarith [hs.1, h.2]
    simp [this]
  · simp [hs]

end Cvs.Finite.KernelLipschitzOrigin
