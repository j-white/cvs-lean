import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.OneModeEntries
import Cvs.Finite.PairFormDividedDifference

/-!
# The generator `bval` in closed form at every mode

At a lattice frequency `ω = 2πk/L` one has `ω L = 2πk`, so `Cvs.Finite.OneModeEntries.Pair_sinCut` applies and `bval`
is twice the pole closed form plus the Lévy series minus the finite prime sum (`bval_closed`).
-/

noncomputable section

open Real

namespace Cvs.Finite.GeneratorClosedForm

open Cvs.Finite.DiagonalCutSymbol Cvs.Finite.OneModeEntries

/-- The lattice frequency of a mode collapses the sine: `sin (2πk/L · L) = 0`. -/
theorem sin_lattice {L : ℝ} (hL : 0 < L) (k : ℤ) : Real.sin (2 * π * k / L * L) = 0 := by
  rw [div_mul_cancel₀ _ hL.ne', show 2 * π * (k : ℝ) = ((2 * k : ℤ) : ℝ) * π by push_cast; ring,
    Real.sin_int_mul_pi]

/-- The lattice frequency of a mode collapses the cosine: `cos (2πk/L · L) = 1`. -/
theorem cos_lattice {L : ℝ} (hL : 0 < L) (k : ℤ) : Real.cos (2 * π * k / L * L) = 1 := by
  rw [div_mul_cancel₀ _ hL.ne', show 2 * π * (k : ℝ) = ((k : ℤ) : ℝ) * (2 * π) by push_cast; ring,
    Real.cos_int_mul_two_pi]

/-- **The pairing of the cut mode in closed form**: pole, Lévy series, prime sum. -/
theorem Pair_sinCut_lattice (P R : ℕ) {L : ℝ} (hL : 0 < L) (k : ℤ) :
    Cvs.Finite.PairFormDividedDifference.Pair P R (sinCut L (2 * π * k / L))
      = 2 * poleSin L (2 * π * k / L) + ∑' j, levySin L (2 * π * k / L) j
        - primeSum P R (sinCut L (2 * π * k / L)) :=
  Pair_sinCut P R hL (sin_lattice hL k) (cos_lattice hL k)

/-- **The generator of the divided-difference matrix, in closed form at every mode.** -/
theorem bval_closed (P R : ℕ) {L : ℝ} (hL : 0 < L) (k : ℤ) :
    Cvs.Finite.PairFormDividedDifference.bval P R L k
      = -(2 * poleSin L (2 * π * k / L) + ∑' j, levySin L (2 * π * k / L) j
          - primeSum P R (sinCut L (2 * π * k / L))) / L := by
  rw [Cvs.Finite.DiagonalCutSymbol.bval_eq P R L k, Pair_sinCut_lattice P R hL k]

end Cvs.Finite.GeneratorClosedForm
