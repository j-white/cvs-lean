import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.PowerLawVisibilityBulkFloor
import Cvs.Route.Visibility.VisibilityUnconditional
import Cvs.Upstream.ConstrainedFormPivotChain

/-!
# The Riemann hypothesis as a sign condition on the R1-perp pivots

`Cvs.Upstream.ConstrainedFormPivotChain.kappa (cosQ x) (cosR x) M` is the `M`-th pivot of the even window form on the complement of the rung
rows. RH holds iff every pivot is nonnegative at every integer scale `x ≥ 2`, and iff, for some constant shift
`C`, every pivot of `cosQ x + C • cosW` is nonnegative at arbitrarily large scales.
-/

namespace Cvs.Route.PerpPivotSignCriterion
open Cvs.ZeroCounting

open Cvs.ZeroCounting

/-- RH iff every R1-perp pivot of the even window form is nonnegative at every integer scale `x ≥ 2`. -/
theorem rh_iff_forall_kappa :
    RiemannHypothesis ↔
      ∀ x : ℕ, 2 ≤ x → ∀ M : ℕ, 0 ≤ Cvs.Upstream.ConstrainedFormPivotChain.kappa (Cvs.Upstream.ConstrainedFormPivotChain.cosQ x) (Cvs.Upstream.ConstrainedFormPivotChain.cosR x) M := by
  rw [Cvs.Route.Visibility.VisibilityUnconditional.rh_iff_forall_evenBulkFloor]
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  exact Cvs.Upstream.ConstrainedFormPivotChain.evenBulkFloor_zero_iff_kappa (by exact_mod_cast hx)

/-- RH iff, for some constant `C`, every R1-perp pivot of `cosQ x + C • cosW` is nonnegative at
arbitrarily large integer scales. -/
theorem rh_iff_bdd_kappa :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∃ᶠ x : ℕ in Filter.atTop,
        ∀ M : ℕ, 0 ≤ Cvs.Upstream.ConstrainedFormPivotChain.kappa (Cvs.Upstream.ConstrainedFormPivotChain.cosQ x - (-C) • Cvs.Upstream.ConstrainedFormPivotChain.cosW) (Cvs.Upstream.ConstrainedFormPivotChain.cosR x) M := by
  rw [Cvs.Route.PowerLawVisibilityBulkFloor.rh_iff_bdd_evenBulkFloor]
  refine exists_congr fun C => ?_
  constructor
  · intro h
    refine (h.and_eventually (Filter.eventually_gt_atTop 1)).mono fun x ⟨hf, hx⟩ => ?_
    exact (Cvs.Upstream.ConstrainedFormPivotChain.evenBulkFloor_iff_kappa (by exact_mod_cast hx) (-C)).1 hf
  · intro h
    refine (h.and_eventually (Filter.eventually_gt_atTop 1)).mono fun x ⟨hk, hx⟩ => ?_
    exact (Cvs.Upstream.ConstrainedFormPivotChain.evenBulkFloor_iff_kappa (by exact_mod_cast hx) (-C)).2 hk

end Cvs.Route.PerpPivotSignCriterion
