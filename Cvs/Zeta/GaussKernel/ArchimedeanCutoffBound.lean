import Mathlib
import Cvs.Zeta.Digamma.ArchPairingLowerBound
import Cvs.Zeta.Digamma.ArchScoreViaDigamma
import Cvs.Zeta.Digamma.ReDigammaMonotoneImag

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real

namespace Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound
open Cvs.GaussKernel

/-!
# The archimedean bound at a frequency cutoff

`Cvs.Zeta.Digamma.ArchPairingLowerBound` bounds `archimedeanPairing` below by `archConst · mass`, with `archConst` the value at
frequency `0` of a density that increases in `|u|`.
-/

/-- The archimedean density at frequency `u`.  `Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst` is `archScore 0`. -/
noncomputable def archScore (u : ℝ) : ℝ :=
  -(Real.log π) / 2 + (Complex.digamma ((1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I)).re / 2

/-- `Cvs.Zeta.Digamma.ArchPairingLowerBound`'s constant is this density read at frequency zero. -/
theorem archScore_zero : archScore 0 = Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst := by
  rw [archScore, Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst]
  norm_num

/-- **The density increases in `|u|`** — `ReDigammaMonotoneImag`'s monotonicity, transported. -/
theorem archScore_mono {u₀ u₁ : ℝ} (h : u₀ ^ 2 ≤ u₁ ^ 2) :
    archScore u₀ ≤ archScore u₁ := by
  have hx : (0 : ℝ) < 1 / 4 := by norm_num
  have hy : (u₀ / 2) ^ 2 ≤ (u₁ / 2) ^ 2 := by nlinarith
  have h := Cvs.GaussKernel.re_digamma_mono (x := (1 / 4 : ℝ)) (y₁ := u₀ / 2) (y₂ := u₁ / 2) hx hy
  have e : ∀ v : ℝ, (((1 / 4 : ℝ)) : ℂ) + (((v / 2 : ℝ)) : ℂ) * Complex.I
      = (1 / 4 : ℂ) + (v : ℂ) / 2 * Complex.I := by intro v; push_cast; ring
  rw [e u₀, e u₁] at h
  rw [archScore, archScore]
  linarith

/-- `archScore 0` is the minimum, which is all `Cvs.Zeta.Digamma.ArchPairingLowerBound` uses. -/
theorem archConst_le_archScore (u : ℝ) : Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst ≤ archScore u := by
  rw [← archScore_zero]
  exact archScore_mono (by simpa using sq_nonneg u)

/-!
## The loss is unbounded, and the bound that avoids it

Monotonicity says the discarded amount is nonnegative.
-/

/-!
## Keeping the halo

`Cvs.Zeta.Digamma.ArchPairingLowerBound` pairs the frequency density against `archConst`, the value of `archScore` at the origin.
-/

theorem archScore_eq_logDeriv (u : ℝ) :
    archScore u = (logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (u : ℂ) * Complex.I)).re := by
  rw [Cvs.Digamma.re_logDeriv_Gammaℝ_boundary u, archScore]

/-!
## The halo at a test, as a number

`archimedeanPairing_ge_halo` pairs the density against the profile, which is exact but not in
a shape a numerical evaluation consumes.
-/

/-!
## Supplying the fraction

`archimedeanPairing_ge_frac` wants `θ`, the fraction of frequency mass beyond the cutoff.
-/

/-!
## What `archScore` is

Not merely a bound that happens to grow.
-/

end Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound
