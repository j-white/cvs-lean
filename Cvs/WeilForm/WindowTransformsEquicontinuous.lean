import Mathlib
import Cvs.Upstream.FourierFirstMomentLipschitz

/-!
# The window's transforms are equicontinuous

A family of tests supported in `Ioc 0 L` with a common `L²` bound has transforms sharing one
global continuity modulus, so `Metric.equicontinuous_of_continuity_modulus` applies and the
family is equicontinuous — the hypothesis Arzelà–Ascoli asks for.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped FourierTransform

namespace Cvs.WeilForm.WindowTransformsEquicontinuous

/-- **A linear modulus tends to zero.** -/
theorem tendsto_linear_modulus (C : ℝ) :
    Tendsto (fun d : ℝ => C * d) (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun d : ℝ => C * d) (𝓝 0) (𝓝 (C * 0)) :=
    (continuous_const.mul continuous_id).tendsto 0
  simpa using h

/-- **Equicontinuity from a common Lipschitz constant.**  Any family of functions on `ℝ`
sharing one Lipschitz bound is equicontinuous. -/
theorem equicontinuous_of_common_lipschitz {ι : Type*} {F : ι → ℝ → ℂ} {C : ℝ}
    (H : ∀ (x y : ℝ) (i : ι), ‖F i x - F i y‖ ≤ C * |x - y|) :
    Equicontinuous F := by
  refine Metric.equicontinuous_of_continuity_modulus (fun d => C * d)
    (tendsto_linear_modulus C) F ?_
  intro x y i
  rw [Complex.dist_eq, Real.dist_eq]
  exact H x y i

/-- **The window's transforms share a Lipschitz constant.**  `an earlier result`'s `L¹` bound turned into
the modulus `Cvs.Upstream/FourierLipschitz` asks for, uniform over any family with a common
first-moment bound. -/
theorem equicontinuous_fourier {ι : Type*} {f : ι → ℝ → ℂ} {M : ℝ}
    (hf : ∀ i, Integrable (f i))
    (hxf : ∀ i, Integrable fun x => |x| * ‖f i x‖)
    (hM : ∀ i, (∫ x : ℝ, |x| * ‖f i x‖) ≤ M) (hMnn : 0 ≤ M) :
    Equicontinuous (fun i => 𝓕 (f i)) := by
  refine equicontinuous_of_common_lipschitz (C := 2 * π * M) ?_
  intro x y i
  have h := Cvs.Upstream.FourierFirstMomentLipschitz.norm_fourier_sub_le (hf i) (hxf i) x y
  have hpi : (0:ℝ) ≤ 2 * π * |x - y| := by positivity
  have hstep : 2 * π * |x - y| * (∫ x : ℝ, |x| * ‖f i x‖) ≤ 2 * π * |x - y| * M :=
    mul_le_mul_of_nonneg_left (hM i) hpi
  calc ‖𝓕 (f i) x - 𝓕 (f i) y‖ ≤ 2 * π * |x - y| * ∫ x : ℝ, |x| * ‖f i x‖ := h
    _ ≤ 2 * π * |x - y| * M := hstep
    _ = 2 * π * M * |x - y| := by ring

end Cvs.WeilForm.WindowTransformsEquicontinuous
