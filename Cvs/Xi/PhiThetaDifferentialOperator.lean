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
import Cvs.Xi.RiemannPhiKernel

/-!
# The kernel as a differential operator on the theta terms

The `n`-th term of `Φ` is `(D² − 1/4)/2` applied, in the variable `u`, to the theta term
`e^{u/2}e^{−πn²e^{2u}}`. Under a cosine transform `D² − 1/4` acts as `−(t² + 1/4)`, which is the value
of `s(s − 1)` at `s = 1/2 + it`.
-/

open Real

namespace Cvs.Xi.PhiThetaDifferentialOperator

open Cvs.Xi.RiemannPhiKernel

/-- The `n`-th theta term in the variable `u`. -/
noncomputable def thetaTerm (n : ℕ) (u : ℝ) : ℝ :=
  exp (u / 2) * exp (-(π * (n : ℝ) ^ 2 * exp (2 * u)))

/-- The first derivative of the `n`-th theta term. -/
noncomputable def thetaTerm1 (n : ℕ) (u : ℝ) : ℝ :=
  thetaTerm n u * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))

/-- The second derivative of the `n`-th theta term. -/
noncomputable def thetaTerm2 (n : ℕ) (u : ℝ) : ℝ :=
  thetaTerm n u * ((1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 2
    - 4 * π * (n : ℝ) ^ 2 * exp (2 * u))

theorem thetaTerm_eq_exp (n : ℕ) (u : ℝ) :
    thetaTerm n u = exp (u / 2 - π * (n : ℝ) ^ 2 * exp (2 * u)) := by
  unfold thetaTerm
  rw [show u / 2 - π * (n : ℝ) ^ 2 * exp (2 * u)
      = u / 2 + -(π * (n : ℝ) ^ 2 * exp (2 * u)) by ring, Real.exp_add]

theorem thetaTerm_pos (n : ℕ) (u : ℝ) : 0 < thetaTerm n u := by
  unfold thetaTerm; positivity

theorem hasDerivAt_exp_two_mul (u : ℝ) :
    HasDerivAt (fun v : ℝ => exp (2 * v)) (exp (2 * u) * 2) u := by
  have hlin : HasDerivAt (fun v : ℝ => 2 * v) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  exact hlin.exp

/-- **The theta term's first derivative.** -/
theorem hasDerivAt_thetaTerm (n : ℕ) (u : ℝ) :
    HasDerivAt (thetaTerm n) (thetaTerm1 n u) u := by
  have hE := hasDerivAt_exp_two_mul u
  have harg : HasDerivAt (fun v : ℝ => v / 2 - π * (n : ℝ) ^ 2 * exp (2 * v))
      (1 / 2 - π * (n : ℝ) ^ 2 * (exp (2 * u) * 2)) u :=
    ((hasDerivAt_id u).div_const 2).sub (hE.const_mul _)
  have hres := harg.exp
  simp only [← thetaTerm_eq_exp] at hres
  convert hres using 1
  unfold thetaTerm1
  ring

/-- **The theta term's second derivative.** -/
theorem hasDerivAt_thetaTerm1 (n : ℕ) (u : ℝ) :
    HasDerivAt (thetaTerm1 n) (thetaTerm2 n u) u := by
  have hE := hasDerivAt_exp_two_mul u
  have hfac : HasDerivAt (fun v : ℝ => 1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * v))
      (0 - 2 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2)) u :=
    (hasDerivAt_const u (1 / 2 : ℝ)).sub (hE.const_mul _)
  have hmul : HasDerivAt (thetaTerm1 n)
      (thetaTerm1 n u * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))
        + thetaTerm n u * (0 - 2 * π * (n : ℝ) ^ 2 * (exp (2 * u) * 2))) u :=
    (hasDerivAt_thetaTerm n u).mul hfac
  convert hmul using 1
  unfold thetaTerm2 thetaTerm1
  ring

/-- **The kernel term is `(D² − 1/4)/2` of the theta term.** -/
theorem two_mul_phiTerm_eq (n : ℕ) (u : ℝ) :
    2 * phiTerm n u = thetaTerm2 n u - thetaTerm n u / 4 := by
  have h5 : exp (5 * u / 2) = exp (u / 2) * exp (2 * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h9 : exp (9 * u / 2) = exp (u / 2) * exp (2 * u) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  unfold phiTerm thetaTerm2 thetaTerm
  rw [h5, h9]
  ring

/-- The term identity, cleared of denominators. -/
theorem eight_mul_phiTerm_eq (n : ℕ) (u : ℝ) :
    8 * phiTerm n u = 4 * thetaTerm2 n u - thetaTerm n u := by
  have := two_mul_phiTerm_eq n u
  linarith

end Cvs.Xi.PhiThetaDifferentialOperator
