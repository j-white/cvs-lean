import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Xi.CompletedZetaPairSymmetry
import Cvs.Xi.ConjugateExponentsCosine
import Cvs.Xi.MellinSplitAtOne
import Cvs.Xi.MellinWeightEndpoint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The completed zeta on the critical line

Both halves of the pair integrate the same function over the same ray, so they combine into one
integral of the sum of the two powers. On the critical line that sum is a cosine, the integrand is
real, and the whole is the real integral the theta transform produces.
-/

noncomputable section

open Set MeasureTheory Complex HurwitzZeta

namespace Cvs.Xi.CompletedZetaCriticalLine

/-- The integrand is integrable beyond one. -/
theorem integrableOn_Ioi (P : WeakFEPair ℂ) (w : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • P.f_modif t) (Ioi (1 : ℝ)) :=
  (Cvs.Xi.MellinSplitAtOne.integrableOn_Ici P w).mono_set Set.Ioi_subset_Ici_self

/-- **The two halves combine into one integral.** -/
theorem Λ₀_zero_combined (w : ℂ) :
    (hurwitzEvenFEPair 0).Λ₀ w
      = ∫ x in Ioi (1 : ℝ),
          (((x : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - w - 1) + ((x : ℝ) : ℂ) ^ (w - 1))
            • (hurwitzEvenFEPair 0).f_modif x := by
  rw [Cvs.Xi.CompletedZetaPairSymmetry.Λ₀_zero_eq, Cvs.Xi.MellinWeightEndpoint.setIntegral_Ici_eq_Ioi,
    ← integral_add (integrableOn_Ioi (hurwitzEvenFEPair 0) ((1 / 2 : ℂ) - w))
      (integrableOn_Ioi (hurwitzEvenFEPair 0) w)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  rw [add_smul]

/-- **On the critical line the integrand is real.** -/
theorem integrand_critical {x : ℝ} (hx : 1 < x) (τ : ℝ) :
    (((x : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - ((1 : ℂ) / 2 + (τ : ℂ) * I) / 2 - 1)
        + ((x : ℝ) : ℂ) ^ (((1 : ℂ) / 2 + (τ : ℂ) * I) / 2 - 1))
      • (hurwitzEvenFEPair 0).f_modif x
      = ((2 * x ^ (-3 / 4 : ℝ) * Real.cos (τ / 2 * Real.log x)
          * (evenKernel 0 x - 1) : ℝ) : ℂ) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  rw [add_comm, Cvs.Xi.ConjugateExponentsCosine.bracket_eq hx0 τ,
    Cvs.Xi.CompletedZetaPairSymmetry.f_modif_of_one_lt hx, smul_eq_mul]
  have hp : ((x : ℝ) : ℂ) ^ ((-3 / 4 : ℝ) : ℂ) = ((x ^ (-3 / 4 : ℝ) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow hx0.le _).symm
  rw [hp]
  push_cast
  ring

end Cvs.Xi.CompletedZetaCriticalLine
