import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Limit.ConstantModeRemovesZero
import Cvs.Limit.MomentLimitsBoundedUnique
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.OffAxisSpineChosenConstants
import Cvs.Limit.RecentredPointwiseBound
import Cvs.Limit.RiemannHypothesisLocallyBounded
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Limit.ZeroFreeApproximantsRH

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Riemann Hypothesis from two scalars of the secular polynomial and the `sees` hypothesis

`Cvs.Limit.RiemannHypothesisLocallyBounded` takes local boundedness of the normalised recentred family as a hypothesis, and `Cvs.Limit.ConstantModeRemovesZero`
derives it from a bound on the reciprocal moduli of the secular roots, a non-zero constant mode
and `L² / N` bounded.  Normalising at a non-zero point whose square is purely imaginary, the
route's hypotheses are those scalars and the `sees` hypothesis.
-/

set_option maxHeartbeats 3200000

noncomputable section

open Filter

namespace Cvs.Limit.TwoScalarsRiemannHypothesis
open Cvs.ZeroCounting

open Cvs.Limit.SpineWithoutSimplicity

/-- **RH from the secular scalars and a subsequential limit that sees the off-axis zeros of
`Ξ`.** -/
theorem riemannHypothesis_of_scalars_sees {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ)
    {w₀ : ℂ} (hw : w₀ ≠ 0) (hw₀ : (w₀ ^ 2).re = 0) (hN : ∀ n, 0 < N n) {K C : ℝ}
    (hS : ∀ n, ((Cvs.Limit.MomentLimitsBoundedUnique.gpoly hL P R N n).roots.map fun r => ‖r‖⁻¹).sum ≤ K)
    (hx0 : ∀ n, ground (P n) (R n) (L n) (hL n) (N n) none ≠ 0)
    (hC : ∀ n, L n ^ 2 / (N n : ℝ) ≤ C)
    (hSees : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ f : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun k z => Cvs.Limit.OffAxisSpineChosenConstants.cnorm (P (φ k)) (R (φ k)) (hL (φ k)) (N (φ k)) w₀
          * Cvs.Finite.RecentredTransform.cgtransform (P (φ k)) (R (φ k)) (hL (φ k)) (N (φ k)) z)
        f atTop Cvs.Limit.OffAxesLimit.offAxes →
      ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, Cvs.Limit.ZeroFreeApproximantsRH.Xi z = 0 → f z = 0) :
    RiemannHypothesis :=
  Cvs.Limit.RiemannHypothesisLocallyBounded.riemannHypothesis_of_bdd_sees hL P R N
    (Cvs.Limit.RecentredPointwiseBound.offAxes_of_sq_re_zero hw hw₀)
    (Cvs.Limit.ConstantModeRemovesZero.bdd_of_constant_mode hL P R N hw hw₀ hN hS hx0 hC) hSees

end Cvs.Limit.TwoScalarsRiemannHypothesis
