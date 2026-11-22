import Mathlib
import Cvs.WeilForm.AutocorrSelfConvolution
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncated test is continuous, and the last three hypotheses follow

    f continuous, f 0 = 0, f L = 0  ⟹  indicator (Ioc 0 L) f continuous

The endpoint zeros are what make the cut-off continuous, and continuity with compact support
gives integrability of the test, of its self-convolution, and continuity of that.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil
open scoped Convolution

namespace Cvs.WeilForm.TruncatedTestContinuous

open Cvs.WeilForm.SelfConvolutionTransform

/-- **The truncated test is continuous.**  A cut-off is discontinuous at the endpoints
unless the test vanishes there, which `h0` and `hLz` say it does. -/
theorem continuous_indicator_Ioc {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : Continuous f) (h0 : f 0 = 0) (hLz : f L = 0) :
    Continuous (Set.indicator (Set.Ioc (0:ℝ) L) f) := by
  classical
  have heq : Set.indicator (Set.Ioc (0:ℝ) L) f
      = Set.piecewise (Set.Icc (0:ℝ) L) f 0 := by
    funext s
    by_cases hs : s ∈ Set.Icc (0:ℝ) L
    · rw [Set.piecewise_eq_of_mem _ _ _ hs]
      by_cases hs' : s ∈ Set.Ioc (0:ℝ) L
      · rw [Set.indicator_of_mem hs']
      · have hz : s = 0 := by
          obtain ⟨h1, h2⟩ := hs
          rcases lt_or_eq_of_le h1 with h | h
          · exact absurd (Set.mem_Ioc.mpr ⟨h, h2⟩) hs'
          · exact h.symm
        rw [Set.indicator_of_notMem hs', hz, h0]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hs,
        Set.indicator_of_notMem (fun hc => hs (Set.Ioc_subset_Icc_self hc))]
      rfl
  rw [heq]
  refine Continuous.piecewise ?_ hf continuous_const
  intro a ha
  rw [frontier_Icc hL.le] at ha
  rcases ha with h | h
  · rw [h]; exact h0
  · rw [Set.mem_singleton_iff.mp h]; exact hLz

/-- The truncated test has compact support. -/
theorem hasCompactSupport_indicator {L : ℝ} (f : ℝ → ℝ) :
    HasCompactSupport (Set.indicator (Set.Ioc (0:ℝ) L) f) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := L)) fun x hx => ?_
  refine Set.indicator_of_notMem (fun hc => hx ?_) f
  exact Set.Ioc_subset_Icc_self hc

/-- **`hFint`.** -/
theorem integrable_indicator {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : Continuous f) (h0 : f 0 = 0) (hLz : f L = 0) :
    Integrable (Set.indicator (Set.Ioc (0:ℝ) L) f) :=
  (continuous_indicator_Ioc hL hf h0 hLz).integrable_of_hasCompactSupport
    (hasCompactSupport_indicator f)

/-- **`hcont`.**  `Cvs.WeilForm.SelfConvolutionTransform` writes the self-convolution as a convolution against the reflected
test, and the reflected test is continuous with compact support. -/
theorem continuous_selfConvolution {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : Continuous f) (h0 : f 0 = 0) (hLz : f L = 0) :
    Continuous fun u : ℝ =>
      ((selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) f) u : ℝ) : ℂ) := by
  set F : ℝ → ℝ := Set.indicator (Set.Ioc (0:ℝ) L) f with hF
  have hFc : Continuous F := continuous_indicator_Ioc hL hf h0 hLz
  have hFk : HasCompactSupport F := hasCompactSupport_indicator f
  have hcfc : Continuous (cf F) := Complex.continuous_ofReal.comp hFc
  have hrefl : Continuous fun x : ℝ => cf F (-x) := hcfc.comp continuous_neg
  have hreflk : HasCompactSupport fun x : ℝ => cf F (-x) := by
    have : HasCompactSupport (cf F) := by
      refine hFk.comp_left (g := fun r : ℝ => (r : ℂ)) ?_
      simp
    exact this.comp_homeomorph (Homeomorph.neg ℝ)
  have hloc : LocallyIntegrable (cf F) :=
    (hcfc.locallyIntegrable)
  have hconv := hreflk.continuous_convolution_right
    (L := ContinuousLinearMap.mul ℂ ℂ) hloc hrefl
  refine hconv.congr ?_
  intro u
  exact (Cvs.WeilForm.SelfConvolutionTransform.selfConvolution_eq_convolution F u).symm

/-- **`hgint`.**  The self-convolution is continuous and vanishes past `L`. -/
theorem integrable_selfConvolution {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : Continuous f) (h0 : f 0 = 0) (hLz : f L = 0) :
    Integrable fun u : ℝ =>
      ((selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) f) u : ℝ) : ℂ) := by
  refine (continuous_selfConvolution hL hf h0 hLz).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun x hx => ?_
  have habs : L ≤ |x| := by
    rcases abs_cases x with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
      by_contra hc <;> push_neg at hc <;> exact hx (Set.mem_Icc.mpr (by constructor <;> linarith))
  rw [Cvs.WeilForm.AutocorrSelfConvolution.selfConvolution_indicator_eq_zero L f habs]
  simp

end Cvs.WeilForm.TruncatedTestContinuous
