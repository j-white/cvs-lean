import Mathlib

/-!
# The Gaussian regulariser

    G c x = exp(−π c x²),   𝓕 (G c) t = c^{−1/2} exp(−π t²/c) ≥ 0,   ∫ 𝓕 (G c) = 1

a nonnegative kernel of unit mass whose multiplier `G c` rises to `1` as `c ↓ 0`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real

namespace Cvs.WeilForm.GaussianRegulariser

/-- The Gaussian multiplier, as a real function. -/
def gauss (c x : ℝ) : ℝ := Real.exp (-π * c * x ^ 2)

/-- Its transform, as a real function. -/
def gaussHat (c x : ℝ) : ℝ := (Real.sqrt c)⁻¹ * Real.exp (-π * x ^ 2 / c)

theorem gauss_pos (c x : ℝ) : 0 < gauss c x := Real.exp_pos _

theorem gauss_le_one {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : gauss c x ≤ 1 := by
  rw [gauss, Real.exp_le_one_iff]
  have : 0 ≤ π * c * x ^ 2 := by positivity
  linarith

theorem gaussHat_nonneg {c : ℝ} (hc : 0 < c) (x : ℝ) : 0 ≤ gaussHat c x := by
  rw [gaussHat]
  have h1 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  positivity

/-- **The regularising kernel has unit mass.** -/
theorem integral_gaussHat {c : ℝ} (hc : 0 < c) : (∫ x : ℝ, gaussHat c x) = 1 := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hrw : ∀ x : ℝ, gaussHat c x = (Real.sqrt c)⁻¹ * Real.exp (-(π / c) * x ^ 2) := by
    intro x
    rw [gaussHat]
    congr 2
    field_simp
  simp only [hrw]
  rw [integral_const_mul, integral_gaussian]
  have hpc : π / (π / c) = c := by
    field_simp
  rw [hpc]
  field_simp

/-- **The multiplier rises to one.** -/
theorem tendsto_gauss (x : ℝ) :
    Filter.Tendsto (fun c : ℝ => gauss c x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hc : Continuous (fun c : ℝ => gauss c x) := by
    unfold gauss
    fun_prop
  have h0 : gauss 0 x = 1 := by simp [gauss]
  have h1 : Filter.Tendsto (fun c : ℝ => gauss c x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (gauss 0 x)) :=
    (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  rwa [h0] at h1

/-- The multiplier is monotone in the regularisation parameter. -/
theorem gauss_mono {c d x : ℝ} (hcd : c ≤ d) : gauss d x ≤ gauss c x := by
  rw [gauss, gauss, Real.exp_le_exp]
  have h : 0 ≤ π * x ^ 2 * (d - c) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [h]

end Cvs.WeilForm.GaussianRegulariser
