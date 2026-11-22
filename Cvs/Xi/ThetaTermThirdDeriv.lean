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

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The theta term's third derivative

Differentiating the second derivative term by the product rule carries the quadratic factor to a
cubic one: the square contributes twice the factor against its own slope, and the linear part
contributes its slope, so the two collect into a single cubic in the same factor.
-/

noncomputable section

open Real

namespace Cvs.Xi.ThetaTermThirdDeriv

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums

/-- The third derivative of the `n`-th theta term. -/
noncomputable def thetaTerm3 (n : ℕ) (u : ℝ) : ℝ :=
  thetaTerm n u * ((1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
    - 12 * π * (n : ℝ) ^ 2 * exp (2 * u) * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))
    - 8 * π * (n : ℝ) ^ 2 * exp (2 * u))

theorem thetaTerm3_eq_prod (n : ℕ) (u : ℝ) :
    thetaTerm3 n u = exp (u / 2) * exp (-(π * exp (2 * u) * (n : ℝ) ^ 2))
      * ((1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
        - 12 * π * (n : ℝ) ^ 2 * exp (2 * u) * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))
        - 8 * π * (n : ℝ) ^ 2 * exp (2 * u)) := by
  unfold thetaTerm3
  rw [thetaTerm_eq_prod]

/-- **The theta term's third derivative.** -/
theorem hasDerivAt_thetaTerm2 (n : ℕ) (u : ℝ) :
    HasDerivAt (thetaTerm2 n) (thetaTerm3 n u) u := by
  have hE := hasDerivAt_exp_two_mul u
  have hP : HasDerivAt (fun v : ℝ => 1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * v))
      (0 - 2 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2)) u :=
    (hasDerivAt_const u (1 / 2 : ℝ)).sub (hE.const_mul _)
  have hQ : HasDerivAt
      (fun v : ℝ => (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * v)) ^ 2
        - 4 * π * (n : ℝ) ^ 2 * exp (2 * v))
      (((2 : ℕ) : ℝ) * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ (2 - 1)
          * (0 - 2 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2))
        - 4 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2)) u :=
    (hP.pow 2).sub (hE.const_mul (4 * π * (n : ℝ) ^ 2))
  have hmul : HasDerivAt (thetaTerm2 n)
      (thetaTerm1 n u * ((1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 2
          - 4 * π * (n : ℝ) ^ 2 * exp (2 * u))
        + thetaTerm n u * (((2 : ℕ) : ℝ)
            * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ (2 - 1)
            * (0 - 2 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2))
          - 4 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2))) u :=
    (hasDerivAt_thetaTerm n u).mul hQ
  convert hmul using 1
  unfold thetaTerm3 thetaTerm1
  push_cast
  norm_num
  ring

end Cvs.Xi.ThetaTermThirdDeriv
