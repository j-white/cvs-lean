import Mathlib
import Cvs.Finite.CutModeLevySeries
import Cvs.Finite.CutModePoleChannel
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.PairFormDividedDifference
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.Zeta.PrimePowerSideTruncated

/-!
# The one-mode entries in closed form, and step (a) at every scale as one explicit sign
Each pairing of a cut mode is twice its pole closed form (`Cvs.Finite.CutModePoleChannel`), plus the archimedean constant
at the origin, plus its Lévy series (`Cvs.Finite.CutModeLevySeries`), minus its finite prime sum (`Pair_cosCut`,
`Pair_sinCut`, `Pair_vcosCut`). With `A = Pair(cosCut 0) − Pair(vcosCut 0)/L`, `B` the same at
`ω = 2π/L` and `C = −Pair(sinCut (2π/L))/(2π)`, `cert_one_symbolic` gives `Cert P R L 1` from
`Csym·(Asym − Bsym) < 0`, every quantity an explicit expression in `L`, `P`, `R`.
-/

noncomputable section

open Real MeasureTheory Set

namespace Cvs.Finite.OneModeEntries

open Cvs.Finite.DiagonalCutSymbol Cvs.Finite.CutModeLevySeries

/-- The pole closed forms (`Cvs.Finite.CutModePoleChannel`). -/
def poleCos (L ω : ℝ) : ℝ :=
  (-1 / 2) * (Real.exp ((-1 / 2) * L) - 1) / ((-1 / 2) ^ 2 + ω ^ 2)
    + (1 / 2) * (Real.exp ((1 / 2) * L) - 1) / ((1 / 2) ^ 2 + ω ^ 2)
def poleSin (L ω : ℝ) : ℝ :=
  ω * (1 - Real.exp ((-1 / 2) * L)) / ((-1 / 2) ^ 2 + ω ^ 2)
    + ω * (1 - Real.exp ((1 / 2) * L)) / ((1 / 2) ^ 2 + ω ^ 2)

def levySin (L ω : ℝ) (k : ℕ) : ℝ :=
  -(ω / 2) * (1 - Real.exp (-(cq k * (2 * L)))) / (cq k ^ 2 + (ω / 2) ^ 2)

/-- The finite prime sum of a test function. -/
def primeSum (P R : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
    Cvs.Zeta.Explicit.Weil.primePowerWeight p r * (2 * h (r * Real.log p))

theorem Pair_sinCut (P R : ℕ) {L ω : ℝ} (hL : 0 < L) (hs : Real.sin (ω * L) = 0)
    (hc : Real.cos (ω * L) = 1) :
    Cvs.Finite.PairFormDividedDifference.Pair P R (sinCut L ω)
      = 2 * poleSin L ω + ∑' k, levySin L ω k - primeSum P R (sinCut L ω) := by
  unfold Cvs.Finite.PairFormDividedDifference.Pair
  rw [← (hasSum_levy_sinCut hL hs hc).tsum_eq, Cvs.Finite.CutModePoleChannel.poleInt_sinCut hL hs hc,
    sinCut_zero L ω hL.le]
  unfold poleSin levySin primeSum
  ring

end Cvs.Finite.OneModeEntries
