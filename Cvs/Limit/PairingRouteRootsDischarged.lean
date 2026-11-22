import Mathlib
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Limit.MomentLimitsBoundedUnique
import Cvs.Limit.MomentSpineAlone
import Cvs.Limit.SpineWithoutSimplicity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pairing route's root hypotheses, discharged

The ground-state polynomial's constant term is nonzero because `shiftP` removes the zeros at the
origin, and its roots are real with nonzero real part for the same reason; the one thing left is
their sign, which `NoNonposRoot` supplies. The pairing route then asks only for that, the pairing
and uniqueness.
-/

noncomputable section

open Finset Polynomial Cvs.Zeta Filter Topology

namespace Cvs.Limit.PairingRouteRootsDischarged
open Cvs.ZeroCounting


/-- **Its roots are real with nonzero real part**, with no hypothesis. -/
theorem gpoly_roots_real {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ) (n : ℕ) :
    ∀ r ∈ (Cvs.Limit.MomentLimitsBoundedUnique.gpoly hL P R N n).roots, r.im = 0 ∧ r.re ≠ 0 :=
  Cvs.Limit.MomentSpineAlone.roots_shiftP
    (Cvs.Limit.MomentSpineAlone.ground_ne_zero (hL n) (P n) (R n) (N n))
    (Cvs.Limit.MomentSpineAlone.ground_real (hL n) (P n) (R n) (N n))

end Cvs.Limit.PairingRouteRootsDischarged
