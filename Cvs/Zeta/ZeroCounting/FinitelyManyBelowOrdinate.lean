import Mathlib
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Finitely many zeros below any ordinate

A non-trivial zero of ordinate below any threshold lies in a closed ball whose radius that
threshold fixes, so there are finitely many of them, and a bound holding above the threshold
suffices for summability however high the threshold is set.
-/

noncomputable section

open Cvs.Zeta.GaussKernel.AdmissibleKernel

namespace Cvs.Zeta.ZeroCounting.FinitelyManyBelowOrdinate


/-- **The non-trivial zeros below any ordinate are finitely many.** -/
theorem finite_ordinate_below (T : ℝ) :
    {rho : nonTrivialZeroSet | |((rho : ℂ)).im| < T}.Finite := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (|T| + 2)) := isCompact_closedBall _ _
  have hfin := hK.inter_riemannZetaZeros_finite
  refine Set.Finite.of_finite_image (f := fun rho : nonTrivialZeroSet => (rho : ℂ)) ?_
    (Set.injOn_of_injective Subtype.coe_injective)
  refine hfin.subset ?_
  rintro z ⟨rho, hrho, rfl⟩
  obtain ⟨hz, h0, h1⟩ := rho.2
  refine ⟨?_, hz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |((rho : ℂ)).re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have him : |((rho : ℂ)).im| ≤ |T| := le_of_lt (lt_of_lt_of_le hrho (le_abs_self T))
  have := Complex.norm_le_abs_re_add_abs_im (rho : ℂ)
  linarith

end Cvs.Zeta.ZeroCounting.FinitelyManyBelowOrdinate
