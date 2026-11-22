import Mathlib

/-!
# The exponential kernel localises

    (d²/ds² − b²) Kb f = −2b·f

Splitting `∫₀ᴸ e^{−b|s−u|}f(u)du` at `s` and differentiating twice returns the kernel itself
plus a multiple of `f`, so an equation carrying this kernel becomes a differential equation.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory intervalIntegral

namespace Cvs.Finite.ExponentialKernelLocalises

/-- The part of the kernel integral to the left of `s`. -/
def leftMoment (b : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u in (0:ℝ)..s, Real.exp (b * u) * f u

/-- The part to the right of `s`. -/
def rightMoment (b L : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u in s..L, Real.exp (-b * u) * f u

/-- `∫₀ᴸ e^{−b|s−u|}f(u)du`, split at `s`. -/
def convSplit (b L : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp (-b * s) * leftMoment b f s + Real.exp (b * s) * rightMoment b L f s

/-- Its derivative. -/
def convDeriv (b L : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  -b * Real.exp (-b * s) * leftMoment b f s + b * Real.exp (b * s) * rightMoment b L f s

variable {b L : ℝ} {f : ℝ → ℝ}

theorem hasDerivAt_leftMoment (hf : Continuous f) (s : ℝ) :
    HasDerivAt (leftMoment b f) (Real.exp (b * s) * f s) s := by
  have hg : Continuous fun u => Real.exp (b * u) * f u := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

theorem hasDerivAt_rightMoment (hf : Continuous f) (s : ℝ) :
    HasDerivAt (rightMoment b L f) (-(Real.exp (-b * s) * f s)) s := by
  have hg : Continuous fun u => Real.exp (-b * u) * f u := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_left (hg.intervalIntegrable _ _)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

theorem hasDerivAt_expMul (c s : ℝ) :
    HasDerivAt (fun z : ℝ => Real.exp (c * z)) (c * Real.exp (c * s)) s := by
  have h : HasDerivAt (fun z : ℝ => c * z) c s := by
    simpa using (hasDerivAt_id s).const_mul c
  simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_exp (c * s)).comp s h

/-- **The split kernel's derivative.**  The two boundary contributions cancel. -/
theorem hasDerivAt_convSplit (hf : Continuous f) (s : ℝ) :
    HasDerivAt (convSplit b L f) (convDeriv b L f s) s := by
  have h1 := (hasDerivAt_expMul (-b) s).mul (hasDerivAt_leftMoment (b := b) hf s)
  have h2 := (hasDerivAt_expMul b s).mul (hasDerivAt_rightMoment (b := b) (L := L) hf s)
  refine (h1.add h2).congr_deriv ?_
  unfold convDeriv
  ring

/-- **The second derivative.**  `Kb f″ = b²·Kb f − 2b·f`. -/
theorem hasDerivAt_convDeriv (hf : Continuous f) (s : ℝ) :
    HasDerivAt (convDeriv b L f) (b ^ 2 * convSplit b L f s - 2 * b * f s) s := by
  have h1 := ((hasDerivAt_expMul (-b) s).const_mul (-b)).mul
    (hasDerivAt_leftMoment (b := b) hf s)
  have h2 := ((hasDerivAt_expMul b s).const_mul b).mul
    (hasDerivAt_rightMoment (b := b) (L := L) hf s)
  refine (h1.add h2).congr_deriv ?_
  unfold convSplit
  have e : Real.exp (-b * s) * Real.exp (b * s) = 1 := by
    rw [← Real.exp_add]
    simp
  linear_combination (-2 * b * f s) * e

/-- **The split form is the kernel integral.**  Inside the window, splitting at `s` removes the
absolute value. -/
theorem convSplit_eq {s : ℝ} (h0 : 0 ≤ s) (hs : s ≤ L) (hf : Continuous f) :
    convSplit b L f s = ∫ u in (0:ℝ)..L, Real.exp (-b * |s - u|) * f u := by
  have hc : Continuous fun u => Real.exp (-b * |s - u|) * f u := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s L)]
  have hleft : (∫ u in (0:ℝ)..s, Real.exp (-b * |s - u|) * f u)
      = Real.exp (-b * s) * leftMoment b f s := by
    rw [leftMoment, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le h0] at hu
    rw [abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ s - u),
      show -b * (s - u) = -b * s + b * u by ring, Real.exp_add, mul_assoc]
  have hright : (∫ u in s..L, Real.exp (-b * |s - u|) * f u)
      = Real.exp (b * s) * rightMoment b L f s := by
    rw [rightMoment, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hs] at hu
    rw [abs_of_nonpos (by linarith [hu.1] : s - u ≤ (0:ℝ)),
      show -b * -(s - u) = b * s + -b * u by ring, Real.exp_add, mul_assoc]
  rw [hleft, hright, convSplit]

/-- **The boundary condition at `0`.**  `(Kb f)′(0) = b·(Kb f)(0)`. -/
theorem convDeriv_zero : convDeriv b L f 0 = b * convSplit b L f 0 := by
  unfold convDeriv convSplit leftMoment
  rw [intervalIntegral.integral_same]
  ring

/-- **The boundary condition at `L`.**  `(Kb f)′(L) = −b·(Kb f)(L)`. -/
theorem convDeriv_end : convDeriv b L f L = -b * convSplit b L f L := by
  unfold convDeriv convSplit rightMoment
  rw [intervalIntegral.integral_same]
  ring

end Cvs.Finite.ExponentialKernelLocalises
