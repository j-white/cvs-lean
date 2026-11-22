import Mathlib

/-!
# The bridge for a window-cut bounded function

The functions the secular rows produce are bounded and cut to the window, nonzero at its ends and
jumping at interior cuts; for `f = 1_{(0,L]} · g` with `g` bounded and measurable the operator's
quadratic form is still the truncated Weil form of its `L²` class, so an eigenfunction of that
shape carries its eigenvalue into the form as an exact Rayleigh value.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set

namespace Cvs.WeilForm.WindowCutBoundedBridge

variable {L : ℝ} {g : ℝ → ℝ}

/-- The window cut of a function. -/
def cut (L : ℝ) (g : ℝ → ℝ) : ℝ → ℝ := Set.indicator (Ioc (0:ℝ) L) g

theorem cut_of_mem {s : ℝ} (hs : s ∈ Ioc (0:ℝ) L) : cut L g s = g s :=
  Set.indicator_of_mem hs g

theorem cut_of_notMem {s : ℝ} (hs : s ∉ Ioc (0:ℝ) L) : cut L g s = 0 :=
  Set.indicator_of_notMem hs g

/-- A continuous function is bounded on the window. -/
theorem bound_of_continuous (hg : Continuous g) (L : ℝ) : ∃ C, ∀ s ∈ Ioc (0:ℝ) L, |g s| ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0:ℝ) L) hg.continuousOn
  exact ⟨M, fun s hs => hM s (Ioc_subset_Icc_self hs)⟩

/-! ### Bounded measurable functions on intervals -/

/-! ### The bridge for a bounded measurable function -/

end Cvs.WeilForm.WindowCutBoundedBridge
