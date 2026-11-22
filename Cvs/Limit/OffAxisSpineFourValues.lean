import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.OffAxisSpineLimitFree
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Upstream.OffAxisFourQuadrants

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The off-axis spine from four non-zero values

The recentred ground spine off the axes, asking for one point in each quadrant at which the limit
does not vanish, in place of the condition that the limit vanish identically on no neighbourhood of
any off-axis point.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Limit.OffAxisSpineFourValues
open Cvs.ZeroCounting

open Cvs.Limit.OffAxesLimit Cvs.Limit.ZeroFreeApproximantsRH

/-- **The off-axis spine, with the limit's non-vanishing supplied by one value per quadrant.** -/
theorem riemannHypothesis_of_ground_centred_offAxes_quadrants
    {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ) (c : ℕ → ℂ) (hc : ∀ n, c n ≠ 0) (f : ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z)
      f atTop offAxes)
    (hne : ∀ s t : ℝ, s ≠ 0 → t ≠ 0 → ∃ w ∈ Cvs.Upstream.OffAxisFourQuadrants.quad s t, f w ≠ 0)
    (hsees : ∀ z ∈ offAxes, Xi z = 0 → f z = 0) :
    RiemannHypothesis := by
  have hfd : DifferentiableOn ℂ f offAxes :=
    hconv.differentiableOn (Eventually.of_forall fun n =>
      ((differentiable_const (c n)).mul
        (Cvs.Finite.RecentredTransform.differentiable_cgtransform
          (P n) (R n) (hL n) (N n))).differentiableOn)
      isOpen_offAxes
  exact Cvs.Limit.OffAxisSpineLimitFree.riemannHypothesis_of_ground_centred_offAxes_sees hL P R N c hc f
    hconv (fun z hz => Cvs.Upstream.OffAxisFourQuadrants.not_eventually_zero_of_quadrants hfd hne hz) hsees

end Cvs.Limit.OffAxisSpineFourValues
