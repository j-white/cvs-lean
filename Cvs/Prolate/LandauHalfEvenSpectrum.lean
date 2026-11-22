import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Landau's half on the even spectrum, from one pivot rung

ORD (Cvs.Prolate.SlepianEvenOrdering) makes `λ = (μ√(c/2π))²` antitone in the level, and the count of even levels below is monotone in the level.
So one even rung with `λ ≥ ½` and at least `k` even levels below it gives `λ ≥ ½` at every even rung with at most `k`
below; dually for `λ ≤ ½`. At `c = 2πx` the pivots are the even indices `4x − 2` and `4x` (Landau's `λ_{4x−1} ≥ ½ ≥
λ_{4x}` with the cross-parity order). Consequences: `(1 − τ)² ≤ (3 − 2√2)(1 − λ)` and E3 with `λ_min = ½`.
-/

noncomputable section

open Real Set Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign
open scoped Interval

namespace Cvs.Prolate.LandauHalfEvenSpectrum

/-! ### The pivots -/

/-- **Lower pivot at `c`**: an even angular eigen-rung with at least `k` even levels below it and concentration
`λ = (μ√(c/2π))² ≥ ½`. -/
def LandauLower (c : ℝ) (k : ℕ) : Prop :=
  ∃ (χ μ : ℝ) (g g₁ g₂ : ℝ → ℝ), (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) ∧
    (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) ∧ ContinuousOn g₂ (uIcc (-1) 1) ∧
    (∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) ∧
    (∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) ∧ (∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) ∧
    (∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) ∧ k ≤ (evenSpec (sqC c) ∩ Iio χ).ncard ∧
    1 / 2 ≤ (μ * √(c / (2 * π))) ^ 2

/-! ### Level count and level order -/

/-- **The count orders the levels**: if `χ'` is an even level and at most as many even levels lie below `χ` as below
`χ'`, then `χ ≤ χ'`. -/
theorem le_of_ncard_le {c χ χ' : ℝ} (hχ' : χ' ∈ evenSpec (sqC c))
    (h : (evenSpec (sqC c) ∩ Iio χ).ncard ≤ (evenSpec (sqC c) ∩ Iio χ').ncard) : χ ≤ χ' := by
  by_contra hlt
  push Not at hlt
  have hss : evenSpec (sqC c) ∩ Iio χ' ⊂ evenSpec (sqC c) ∩ Iio χ := by
    refine ⟨fun z hz => ⟨hz.1, lt_trans hz.2 hlt⟩, fun hsub => ?_⟩
    exact lt_irrefl χ' (mem_Iio.mp (hsub ⟨hχ', hlt⟩).2)
  have := Set.ncard_lt_ncard hss (finite_evenSpec_Iio _ χ)
  omega

/-! ### Propagation from the pivots -/

/-- **`λ ≥ ½` below the lower pivot**: every even rung with at most `k` even levels below it has `λ ≥ ½`. -/
theorem half_le_lam_of_lower {h h₁ h₂ : ℝ → ℝ} {c χ μ : ℝ} {k : ℕ} (hc : 0 < c) (hL : LandauLower c k)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ * h s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (hh0 : ∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ * h s) (hk : (evenSpec (sqC c) ∩ Iio χ).ncard ≤ k) :
    1 / 2 ≤ (μ * √(c / (2 * π))) ^ 2 := by
  obtain ⟨χL, μL, g, g₁, g₂, hg, hg₁, hg₂c, hangL, hevenL, hg0, hμL, hkL, hhalf⟩ := hL
  have hle : χ ≤ χL := le_of_ncard_le (mem_evenSpec_of_angular hg hg₁ hangL hevenL hg0) (hk.trans hkL)
  exact hhalf.trans (Cvs.Prolate.SlepianEvenOrdering.lam_le_of_chi_le hc hh hh₁ hh₂c hang heven hh0 hg hg₁ hg₂c hangL
    hevenL hg0 hμ hμL hle)

/-! ### The arm constant `2q′ = 3 − 2√2` -/

/-! ### E3 with `λ_min = ½` -/

end Cvs.Prolate.LandauHalfEvenSpectrum
