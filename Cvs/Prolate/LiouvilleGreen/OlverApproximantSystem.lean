import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.BesselAlongPhase
import Cvs.Prolate.LiouvilleGreen.OlverResidualIdentity
import Cvs.Upstream.BesselJZeroEquation
import Cvs.Upstream.BesselJZeroIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Olver's approximant as a first-order system

With `Pζ′² = Q`, `W = Pζ′` and the amplitude relation `A²W = ζ` holding near `x`, the approximant `g = A·J₀(ζ)` and
its flux `g_p = P(A′J₀(ζ) + Aζ′J₀′(ζ))` satisfy `g′ = g_p/P` and `g_p′ = (PA′)′J₀(ζ) − Qg`: the system of an earlier result with
residual `r = (PA′)′J₀(ζ)`.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverApproximantSystem

open Real Filter Topology Cvs.Upstream.BesselJZeroIntegral Cvs.Upstream.BesselJZeroEquation Cvs.Prolate.LiouvilleGreen.BesselAlongPhase Cvs.Prolate.LiouvilleGreen.OlverResidualIdentity

/-- **The approximant's derivative is its flux over `P`.** -/
theorem hasDerivAt_approx {P A A' ζ ζ' : ℝ → ℝ} {x : ℝ} (hA : HasDerivAt A (A' x) x)
    (hζ : HasDerivAt ζ (ζ' x) x) (hP0 : P x ≠ 0) :
    HasDerivAt (fun y => A y * besselJ0 (ζ y))
      (P x * (A' x * besselJ0 (ζ x) + A x * ζ' x * besselJ0' (ζ x)) / P x) x := by
  refine (hA.mul (hasDerivAt_besselJ0_comp hζ)).congr_deriv ?_
  field_simp

/-- **The flux's derivative is the residual minus `Q·g`**, with the amplitude relation needed only near `x`. -/
theorem hasDerivAt_flux {P Q A A' ζ ζ' W : ℝ → ℝ} {w W' x : ℝ}
    (hA : HasDerivAt A (A' x) x) (hζ : HasDerivAt ζ (ζ' x) x) (hW : HasDerivAt W W' x)
    (hU : HasDerivAt (fun y => P y * A' y) w x)
    (hrel : ∀ᶠ y in 𝓝 x, A y ^ 2 * W y = ζ y) (hWeq : ∀ᶠ y in 𝓝 x, W y = P y * ζ' y)
    (hphase : P x * ζ' x ^ 2 = Q x) (hA0 : A x ≠ 0) (hζ0 : ζ x ≠ 0) :
    HasDerivAt (fun y => P y * (A' y * besselJ0 (ζ y) + A y * ζ' y * besselJ0' (ζ y)))
      (w * besselJ0 (ζ x) - Q x * (A x * besselJ0 (ζ x))) x := by
  -- `V = P·A·ζ′` agrees with `A·W` near `x`
  have hV : HasDerivAt (fun y => P y * A y * ζ' y) (A' x * W x + A x * W') x := by
    refine (hA.mul hW).congr_of_eventuallyEq ?_
    filter_upwards [hWeq] with y hy
    simp only [Pi.mul_apply]; rw [hy]; ring
  -- the relation's derivative, from its local form
  have hζ' : HasDerivAt (fun y => A y ^ 2 * W y) (ζ' x) x :=
    hζ.congr_of_eventuallyEq (hrel.mono fun y hy => hy)
  have hder : 2 * A x * A' x * W x + A x ^ 2 * W' = ζ' x :=
    (((hA.pow 2).mul hW).congr_deriv (by simp)).unique hζ'
  have hWx : W x = P x * ζ' x := hWeq.self_of_nhds
  have hζx : ζ x = A x ^ 2 * W x := hrel.self_of_nhds.symm
  refine hasDerivAt_olver (U := fun y => P y * A' y) (V := fun y => P y * A y * ζ' y) hζ hζ0 hU rfl hV rfl
    hphase ?_
  -- Olver's cancellation, as in an earlier result
  have hP : A x ^ 2 * (P x * ζ' x) ≠ 0 := by rw [← hWx, ← hζx]; exact hζ0
  rw [hζx, hWx]
  rw [hWx] at hder
  have hPz : P x * ζ' x ≠ 0 := fun h => hP (by rw [h, mul_zero])
  have hP0 : P x ≠ 0 := left_ne_zero_of_mul hPz
  field_simp
  linear_combination hder

end Cvs.Prolate.LiouvilleGreen.OlverApproximantSystem
