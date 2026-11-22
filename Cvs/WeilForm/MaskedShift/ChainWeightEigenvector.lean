import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
import Cvs.WeilForm.MaskedShift.PathGraphSpectrum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Real

namespace Cvs.Operator

open Cvs.Operator

/-!
# The chain weight is an eigenvector, boundary included

`chainWeight β x = sin((j+1)π/(k+1))` with `j` the position in the chain and `k` its length —
the path-graph eigenvector.
-/

/-- **First point of a chain.**  The backward hop is masked off, and the forward
hop alone already gives `ν k · w(x)` — by the double-angle identity. -/
theorem chainWeight_first (β x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x)
    (h0 : chainPos β x = 0) :
    chainWeight β (x + β)
      = Cvs.Operator.chebFactor (chainLength β (chainBase β x)) * chainWeight β x := by
  set k := chainLength β (chainBase β x) with hk
  set θ := π / ((k : ℝ) + 1) with hθ
  rw [chainWeight_add_step β x hβ hx, h0]
  unfold chainWeight Cvs.Operator.chebFactor
  rw [h0]
  push_cast
  have h1 : (0 + 2) * π / ((k : ℝ) + 1) = 2 * θ := by rw [hθ]; ring
  have h2 : (0 + 1) * π / ((k : ℝ) + 1) = θ := by rw [hθ]; ring
  rw [h1, h2, Real.sin_two_mul, ← hθ]
  ring

/-- **Last point of a chain.**  The forward hop is masked off, and the backward
hop alone gives `ν k · w(x)` — because `sin((k+1)θ) = sin π = 0`. -/
theorem chainWeight_last (β x : ℝ) (hβ : 0 < β) (hpos : 1 ≤ chainPos β x)
    (hlast : chainPos β x + 1 = chainLength β (chainBase β x)) :
    chainWeight β (x - β)
      = Cvs.Operator.chebFactor (chainLength β (chainBase β x)) * chainWeight β x := by
  set j := chainPos β x with hj
  set k := chainLength β (chainBase β x) with hk
  set θ := π / ((k : ℝ) + 1) with hθ
  have hkpos : 0 < k := by omega
  -- the rung identity at the top of the chain
  have hrung := Cvs.Operator.sin_rung θ j
  -- `sin ((k+1) θ) = sin π = 0`
  have hzero : Real.sin (((j : ℝ) + 2) * θ) = 0 := by
    have hjk : ((j : ℝ) + 2) = (k : ℝ) + 1 := by
      have : (j : ℝ) + 1 = (k : ℝ) := by exact_mod_cast hlast
      linarith
    rw [hjk, hθ]
    have : ((k : ℝ) + 1) * (π / ((k : ℝ) + 1)) = π := by
      field_simp
    rw [this, Real.sin_pi]
  rw [chainWeight_sub_step β x hβ hpos]
  unfold chainWeight Cvs.Operator.chebFactor
  have e1 : (j : ℝ) * π / ((k : ℝ) + 1) = (j : ℝ) * θ := by rw [hθ]; ring
  have e2 : ((j : ℝ) + 1) * π / ((k : ℝ) + 1) = ((j : ℝ) + 1) * θ := by rw [hθ]; ring
  rw [e1, e2]
  rw [hzero] at hrung
  linarith [hrung]

end Cvs.Operator
