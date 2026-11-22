import Mathlib
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# An explicit threshold for the archimedean floor

With `floorK x K = log x + c_K − s_K/(πx)²` (Cvs.L2a.ArchChannelFloorAbove), `floorK x K ≥ A` as soon as `x ≥ exp(A − c_K + 1)` and
`(πx)² ≥ s_K`: any bounded prime constant is beaten by the floor above an explicit cutoff, the form in which the
resonant constant with a bounded `ε₃` (Cvs.L2a.MassBeyondFrame) enters L2a.
-/

namespace Cvs.WeilForm.Archimedean.ArchFloorThreshold

open Real Cvs.WeilForm.Archimedean.ArchimedeanUnbounded Cvs.L2a.ArchChannelFloorAbove

/-- The constant `c_K` of the floor. -/
noncomputable def cFloor (K : ℕ) : ℝ :=
  archSymbol 0 + ∑ k ∈ Finset.range K, 1 / (1 / 4 + (k : ℝ)) + log (π / (K + 1 / 4))

/-- The constant `s_K` of the floor. -/
noncomputable def sFloor (K : ℕ) : ℝ := ∑ k ∈ Finset.range K, (1 / 4 + (k : ℝ))

/-- **The floor above an explicit cutoff.** -/
theorem floorK_ge {x A : ℝ} (K : ℕ) (hx : 0 < x) (hlog : exp (A - cFloor K + 1) ≤ x)
    (hs : sFloor K ≤ (π * x) ^ 2) : A ≤ floorK x K := by
  rw [floorK_eq hx K]
  have h1 : A - cFloor K + 1 ≤ log x := by
    rw [← Real.log_exp (A - cFloor K + 1)]
    exact Real.log_le_log (exp_pos _) hlog
  have hpx : 0 < (π * x) ^ 2 := by positivity
  have h2 : sFloor K / (π * x) ^ 2 ≤ 1 := by rw [div_le_one hpx]; exact hs
  unfold cFloor at h1
  unfold sFloor at h2
  linarith

end Cvs.WeilForm.Archimedean.ArchFloorThreshold
