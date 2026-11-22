import Mathlib
import Cvs.Limit.HurwitzRealZerosL2Limit
import Cvs.Limit.TransformZeroRealBridge
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The conditional terminal for link ③

    approximants realised as window cosine sums, whose partial-fraction sums have real zeros
    and which converge in `L²` to `ξ`  ⟹  every zero of `ξ`'s transform is real

the statement the CvS chain plugs into.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Complex

namespace Cvs.Limit.ConditionalRealZerosTerminal

/-- On the lattice the frequency is real, so nothing needs proving there. -/
theorem im_eq_zero_of_sq_eq {L : ℝ} {n : ℕ} {z : ℂ}
    (h : z ^ 2 = ((2 * Real.pi * n / L : ℝ) : ℂ) ^ 2) : z.im = 0 := by
  set w : ℂ := ((2 * Real.pi * n / L : ℝ) : ℂ) with hw
  have hfac : (z - w) * (z + w) = 0 := by
    rw [show (z - w) * (z + w) = z ^ 2 - w ^ 2 by ring, h, sub_self]
  rcases mul_eq_zero.mp hfac with h1 | h2
  · rw [sub_eq_zero.mp h1, hw]; simp
  · have : z = -w := by linear_combination h2
    rw [this, hw]; simp

/-- **The approximants' transforms have only real zeros.** -/
theorem im_eq_zero_of_modeSum {L : ℝ} (hL : 0 < L) (s : Finset ℕ) (a : ℕ → ℝ) {z : ℂ}
    (hint : ∀ w : ℂ, Integrable (fun t : ℝ =>
      ((Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a) t : ℝ) : ℂ)
        * Complex.exp (Complex.I * w * (t : ℂ))) (volume : Measure ℝ))
    (hsum : (∑ n ∈ s, ((a n : ℝ) : ℂ)
      / (z ^ 2 - ((2 * Real.pi * n / L : ℝ) : ℂ) ^ 2)) = 0 → z.im = 0)
    (hzero : FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
      (Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a))) z = 0) :
    z.im = 0 := by
  classical
  by_cases hlat : ∀ n ∈ s, z ^ 2 ≠ ((2 * Real.pi * n / L : ℝ) : ℂ) ^ 2
  · exact Cvs.Limit.TransformZeroRealBridge.im_eq_zero_of_fourierLaplace hL s a hlat (hint z) hsum hzero
  · push_neg at hlat
    obtain ⟨n, _, hn⟩ := hlat
    exact im_eq_zero_of_sq_eq hn

/-- **The conditional terminal.**  Real zeros pass to the `L²` limit. -/
theorem zeros_real_of_modeSum_approx {L : ℝ} (hL : 0 < L) {ξ : ℝ → ℝ}
    (hξ : MemLp ξ 2 (volume : Measure ℝ)) (hξs : ∀ s ∉ Set.Ioc (0:ℝ) L, ξ s = 0)
    (hξn : (∫ x : ℝ, ξ x ^ 2) = 1)
    (S : ℕ → Finset ℕ) (A : ℕ → ℕ → ℝ)
    (hmem : ∀ k, MemLp (Set.indicator (Set.Ioc (0:ℝ) L)
      (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L (S k) (A k))) 2 (volume : Measure ℝ))
    (hint : ∀ k, ∀ w : ℂ, Integrable (fun t : ℝ =>
      ((Set.indicator (Set.Ioc (0:ℝ) L)
        (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L (S k) (A k)) t : ℝ) : ℂ)
        * Complex.exp (Complex.I * w * (t : ℂ))) (volume : Measure ℝ))
    (hsum : ∀ k, ∀ z : ℂ, (∑ n ∈ S k, ((A k n : ℝ) : ℂ)
      / (z ^ 2 - ((2 * Real.pi * n / L : ℝ) : ℂ) ^ 2)) = 0 → z.im = 0)
    (hconv : Tendsto (fun k => ∫ x : ℝ,
      (Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L (S k) (A k)) x
        - ξ x) ^ 2) atTop (nhds 0)) :
    ∀ z : ℂ, FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf ξ) z = 0 → z.im = 0 :=
  Cvs.Limit.HurwitzRealZerosL2Limit.zeros_real_of_approx hL hξ hξs hξn hmem
    (fun k s hs => by rw [Set.indicator_of_notMem hs])
    (fun k z hz => im_eq_zero_of_modeSum hL (S k) (A k) (hint k) (hsum k z) hz)
    hconv

end Cvs.Limit.ConditionalRealZerosTerminal
