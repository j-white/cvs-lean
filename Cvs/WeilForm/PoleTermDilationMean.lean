import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole term is the prime-number-theorem mean of the dilation pairing

For tame `F`, `G`, `∫₀^∞ ⟨F, G(u·)⟩ du = P₋F · P₊G`; so the θ-space Weil pairing is the arch term
less the dilation pairing integrated against `dψ(u) − du`, the Chebyshev error.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology

namespace Cvs.WeilForm.PoleTermDilationMean


/-- The dilation pairing at a real dilation `u`: `⟨F, G(u·)⟩ = ∫_{θ>0} F(θ) G(uθ) dθ`. -/
def dilR (F G : ℝ → ℝ) (u : ℝ) : ℝ := ∫ θ in Ioi (0 : ℝ), F θ * G (u * θ)

end Cvs.WeilForm.PoleTermDilationMean
