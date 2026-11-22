import Mathlib
import Cvs.Zeta.Digamma
import Cvs.Zeta.ExplicitFormula.ArchimedeanBoundTestFree
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrand
import Cvs.Zeta.ExplicitFormula.HaloAnyDepth

/-!
# The halo bound at any depth

`an earlier result` integrated `an earlier result`'s bound — the `k = 0` filter alone — against the density on the
critical line, and measurement showed it is too coarse there: at the `(lam, a)` where
`gaussAmp` is most sensitive to an off-line zero it returns `-0.434` for a channel whose true
value is `+0.244`, losing the sign outright.
-/

namespace Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth
open Cvs.Detection

open Complex MeasureTheory
open scoped Real

/-- The partial bank, as a function of the frequency. -/
noncomputable def bank (K : ℕ) (y : ℝ) : ℝ :=
  (∑ k ∈ Finset.range K, Cvs.Zeta.digammaDeficit y k) / 2

/-- Its ceiling, uniform in `y`: filter `k` never returns more than `1/(¼+k)`. -/
noncomputable def bankCeil (K : ℕ) : ℝ :=
  (∑ k ∈ Finset.range K, 1 / (1 / 4 + (k : ℝ))) / 2

/-- `archScore` is bounded below by its value at the origin plus the bank to
depth `K`. -/
theorem archScore_ge (K : ℕ) (y : ℝ) :
    Cvs.Detection.archScore 0 + bank K y ≤ Cvs.Detection.archScore y := by
  have h := Cvs.Detection.W_ge_partial K y
  rw [Cvs.Detection.W_eq_archScore_sub] at h
  rw [bank]
  linarith

end Cvs.Zeta.ExplicitFormula.HaloBoundAnyDepth
