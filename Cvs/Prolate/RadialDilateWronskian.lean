import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Wronskian of two dilates of a radial solution

If `(ξ² − 1)ψ″ + 2ξψ′ + (c²ξ² − χ)ψ = 0`, the dilates `F = ψ(m·)`, `G = ψ(n·)` have Wronskian `W = F′G − FG′` with
`c²(m² − n²)FG = −W′ + (c² − χ)(m² − n²)FG/((m²θ² − 1)(n²θ² − 1)) − 2m³θψ′(mθ)G/(m²θ² − 1) + 2n³θFψ′(nθ)/(n²θ² − 1)`
wherever `mθ, nθ ≠ ±1`: the frequency correction is itself a multiple of `m² − n²`.
-/

noncomputable section

open Real

namespace Cvs.Prolate.RadialDilateWronskian

/-- The Wronskian `W(θ) = mψ′(mθ)ψ(nθ) − nψ(mθ)ψ′(nθ)` of the dilates. -/
def wron (ψ v : ℝ → ℝ) (m n θ : ℝ) : ℝ := m * v (m * θ) * ψ (n * θ) - n * ψ (m * θ) * v (n * θ)

/-- **Its derivative**: `W′ = m²ψ″(mθ)ψ(nθ) − n²ψ(mθ)ψ″(nθ)`. -/
theorem hasDerivAt_wron {ψ v v' : ℝ → ℝ} {m n θ : ℝ} (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ)
    (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) :
    HasDerivAt (wron ψ v m n) (m ^ 2 * v' (m * θ) * ψ (n * θ) - n ^ 2 * ψ (m * θ) * v' (n * θ)) θ := by
  have hm : HasDerivAt (fun θ => m * θ) m θ := by simpa using (hasDerivAt_id θ).const_mul m
  have hn : HasDerivAt (fun θ => n * θ) n θ := by simpa using (hasDerivAt_id θ).const_mul n
  have hvm := (hv (m * θ)).comp θ hm
  have hvn := (hv (n * θ)).comp θ hn
  have hψm := (hψ (m * θ)).comp θ hm
  have hψn := (hψ (n * θ)).comp θ hn
  have := ((hvm.const_mul m).mul hψn).sub ((hψm.const_mul n).mul hvn)
  refine this.congr_deriv ?_
  simp only [Function.comp]; ring

/-- **The Wronskian identity of the dilates.** -/
theorem wron_identity {ψ v v' : ℝ → ℝ} {c χ m n θ : ℝ}
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hm : (m * θ) ^ 2 - 1 ≠ 0) (hn : (n * θ) ^ 2 - 1 ≠ 0) :
    c ^ 2 * (m ^ 2 - n ^ 2) * (ψ (m * θ) * ψ (n * θ))
      = -(m ^ 2 * v' (m * θ) * ψ (n * θ) - n ^ 2 * ψ (m * θ) * v' (n * θ))
        + (c ^ 2 - χ) * (m ^ 2 - n ^ 2) * (ψ (m * θ) * ψ (n * θ)) / (((m * θ) ^ 2 - 1) * ((n * θ) ^ 2 - 1))
        - 2 * m ^ 3 * θ * v (m * θ) * ψ (n * θ) / ((m * θ) ^ 2 - 1)
        + 2 * n ^ 3 * θ * ψ (m * θ) * v (n * θ) / ((n * θ) ^ 2 - 1) := by
  have em : v' (m * θ) = -(2 * (m * θ) * v (m * θ) + (c ^ 2 * (m * θ) ^ 2 - χ) * ψ (m * θ)) / ((m * θ) ^ 2 - 1) := by
    rw [eq_div_iff hm]; linarith [hode (m * θ)]
  have en : v' (n * θ) = -(2 * (n * θ) * v (n * θ) + (c ^ 2 * (n * θ) ^ 2 - χ) * ψ (n * θ)) / ((n * θ) ^ 2 - 1) := by
    rw [eq_div_iff hn]; linarith [hode (n * θ)]
  rw [em, en]
  have hm2 : m ^ 2 * θ ^ 2 - 1 ≠ 0 := by rw [← mul_pow]; exact hm
  have hn2 : n ^ 2 * θ ^ 2 - 1 ≠ 0 := by rw [← mul_pow]; exact hn
  field_simp
  ring

end Cvs.Prolate.RadialDilateWronskian
