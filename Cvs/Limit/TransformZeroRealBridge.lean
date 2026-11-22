import Mathlib
import Cvs.Finite.WindowCosineSumTransform
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# Bridge (a): a transform zero is real if the sum's zeros are

    𝓛 (1_{(0,L]}·modeSum) z = 0  ⟹  z.im = 0

given that the partial-fraction sum's zeros are real.  The other two factors contribute only
`z = 0` and the lattice `2πm/L`, both real.
-/

set_option maxHeartbeats 3200000

noncomputable section

open Complex MeasureTheory

namespace Cvs.Limit.TransformZeroRealBridge

/-- The sine factor's zeros are real. -/
theorem im_eq_zero_of_sin {L : ℝ} (hL : 0 < L) {z : ℂ}
    (h : Complex.sin (z * (L : ℂ) / 2) = 0) : z.im = 0 := by
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hL)
  have hz : z = ((2 * (k : ℝ) * Real.pi / L : ℝ) : ℂ) := by
    have h2 : z * (L : ℂ) = 2 * (k : ℂ) * (Real.pi : ℂ) := by
      field_simp at hk
      linear_combination hk
    push_cast
    rw [eq_div_iff hLC]
    linear_combination h2
  rw [hz]
  simp

/-- **Bridge (a).**  A zero of the transform is real once the sum's zeros are. -/
theorem im_eq_zero_of_fourierLaplace {L : ℝ} (hL : 0 < L) (s : Finset ℕ) (a : ℕ → ℝ) {z : ℂ}
    (hlat : ∀ n ∈ s, z ^ 2 ≠ ((2 * Real.pi * n / L : ℝ) : ℂ) ^ 2)
    (hint : Integrable (fun t : ℝ =>
      ((Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a) t : ℝ) : ℂ)
        * Complex.exp (Complex.I * z * (t : ℂ))) (volume : Measure ℝ))
    (hsum : (∑ n ∈ s, ((a n : ℝ) : ℂ)
      / (z ^ 2 - ((2 * Real.pi * n / L : ℝ) : ℂ) ^ 2)) = 0 → z.im = 0)
    (hzero : FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
      (Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a))) z = 0) :
    z.im = 0 := by
  rw [Cvs.Finite.WindowCosineSumTransform.fourierLaplace_modeSum hL s a hlat hint] at hzero
  -- a product vanishes, so one factor does
  rcases mul_eq_zero.mp hzero with hA | hS
  · rcases mul_eq_zero.mp hA with hB | hsin
    · rcases mul_eq_zero.mp hB with hz2 | hexp
      · -- `2 z = 0`
        have : z = 0 := by
          rcases mul_eq_zero.mp hz2 with h2 | hz0
          · exact absurd h2 (by norm_num)
          · exact hz0
        rw [this]; simp
      · exact absurd hexp (Complex.exp_ne_zero _)
    · exact im_eq_zero_of_sin hL hsin
  · exact hsum hS

end Cvs.Limit.TransformZeroRealBridge
