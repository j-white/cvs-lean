import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.RungMirrorIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cosine-transform Mellin formula and the spectrum of the tail

For even `g` with `g′` integrable on `[−1, 1]`, `ψ = psi c g` and `0 < Re s < 1`:
`∫₀^∞ w^{s−1} ψ(w) dw = 2Γ(s) cos(πs/2) c^{−s} M(1 − s)`, `M = mel g`. If `ψ = μg` on `[0, 1]`, the tail
`ψ^> = ψ·1_(1,∞)` has Mellin transform `mg c s · D(s)`, `D = √(2π/c) P(1 − s) − μP(s)` (Cvs.Prolate.Mellin.LawRatioFunctionalDefect). `|ψ(w)| ≤ B/(cw)`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology
open Cvs.L2a.AngularProlateTailPositive (psi)

namespace Cvs.Prolate.Mellin.CosineTransformMellin

variable {c : ℝ} {g g₁ : ℝ → ℝ}

/-- For even `g`, `ψ(w) = 2∫₀¹ g(y) cos(cyw) dy`. -/
theorem psi_eq_two_integral (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (w : ℝ) :
    psi c g w = 2 * ∫ y in Ioc (0 : ℝ) 1, g y * Real.cos (c * y * w) := by
  rw [Cvs.Prolate.RungMirrorIdentity.psi_eq_integral hgc heven w]
  congr 1
  have e : ∀ x, (Icc (0 : ℝ) 1).indicator g x * Real.cos (c * x * w)
      = (Icc (0 : ℝ) 1).indicator (fun x => g x * Real.cos (c * x * w)) x :=
    fun x => by by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [hx]
  simp only [e]
  rw [setIntegral_indicator measurableSet_Icc, Cvs.Prolate.RungMirrorIdentity.Ioi_inter_Icc_eq]

end Cvs.Prolate.Mellin.CosineTransformMellin
