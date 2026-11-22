import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.PhiThetaDifferentialOperator
import Cvs.Xi.ThetaTermThirdDeriv

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The theta term's fourth derivative

The argument the index and the exponential enter through has itself twice that argument for a
slope, so differentiating the cubic factor once more returns a quartic in the same argument: the
factor contributes its own slope against the argument, and the cubic contributes its derivative
carried along the argument's slope.
-/

noncomputable section

open Real

namespace Cvs.Xi.ThetaTermFourthDeriv

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaTermThirdDeriv

/-- The fourth derivative of the `n`-th theta term. -/
noncomputable def thetaTerm4 (n : ℕ) (u : ℝ) : ℝ :=
  thetaTerm n u * (1 / 16 - 39 / 2 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u))
    + 83 / 2 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 2
    - 14 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
    + (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 4)

theorem thetaTerm4_eq_prod (n : ℕ) (u : ℝ) :
    thetaTerm4 n u = exp (u / 2) * exp (-(π * exp (2 * u) * (n : ℝ) ^ 2))
      * (1 / 16 - 39 / 2 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u))
        + 83 / 2 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 2
        - 14 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
        + (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 4) := by
  unfold thetaTerm4
  rw [thetaTerm_eq_prod]

/-- **The theta term's fourth derivative.** -/
theorem hasDerivAt_thetaTerm3 (n : ℕ) (u : ℝ) :
    HasDerivAt (thetaTerm3 n) (thetaTerm4 n u) u := by
  have hE := hasDerivAt_exp_two_mul u
  have hP : HasDerivAt (fun v : ℝ => 1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * v))
      (0 - 2 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2)) u :=
    (hasDerivAt_const u (1 / 2 : ℝ)).sub (hE.const_mul _)
  have hF : HasDerivAt
      (fun v : ℝ => (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * v)) ^ 3
        - 12 * π * (n : ℝ) ^ 2 * exp (2 * v)
          * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * v))
        - 8 * π * (n : ℝ) ^ 2 * exp (2 * v))
      (((3 : ℕ) : ℝ) * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ (3 - 1)
            * (0 - 2 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2))
          - (12 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2)
              * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))
            + 12 * π * (n : ℝ) ^ 2 * exp (2 * u)
              * (0 - 2 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2)))
        - 8 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2)) u :=
    ((hP.pow 3).sub ((hE.const_mul (12 * π * (n : ℝ) ^ 2)).mul hP)).sub
      (hE.const_mul (8 * π * (n : ℝ) ^ 2))
  have hmul : HasDerivAt (thetaTerm3 n)
      (thetaTerm1 n u * ((1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
          - 12 * π * (n : ℝ) ^ 2 * exp (2 * u)
            * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))
          - 8 * π * (n : ℝ) ^ 2 * exp (2 * u))
        + thetaTerm n u
          * (((3 : ℕ) : ℝ) * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ (3 - 1)
                * (0 - 2 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2))
              - (12 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2)
                  * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))
                + 12 * π * (n : ℝ) ^ 2 * exp (2 * u)
                  * (0 - 2 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2)))
            - 8 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2))) u :=
    (hasDerivAt_thetaTerm n u).mul hF
  convert hmul using 1
  unfold thetaTerm4 thetaTerm1
  push_cast
  norm_num
  ring

end Cvs.Xi.ThetaTermFourthDeriv
