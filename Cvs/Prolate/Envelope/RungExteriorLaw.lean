import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.Envelope.RungEdgeMassExterior
import Cvs.Prolate.EvenRungsByIndex

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior law on every rung, and `HPRe`

For the rung of index `k` with `D = c² − χ_k > 0`, `λ = lamR c k` and `ψ = psi c (rung c k)`:
`λ h(1)² ≤ (72/49)(2D + 3c)(1 − λ)` and `λ ∫₁^∞(ψ'/μ)² ≤ (72/49)(2D + 3c)(1 − λ)·derivFactor c D`, from Cvs.Prolate.Envelope.RungEdgeMassExterior at
`ξ₀ = 1 + 1/c` and `AngularBesselInequality`'s mass identity. With `FullSpanIndexFloor`'s index floor and `WindowChainInputsProlate`'s `λ ≥ ½` this gives `HPRe`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity
open Cvs.Prolate.RungSpanBernsteinNikolskii (psiD)
open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx rung lev muR lamR rung_spec psi_rung continuousOn_rung lev_spec)

namespace Cvs.Prolate.Envelope.RungExteriorLaw
open Cvs.ZeroCounting

/-! ### A rung of a single index -/

section rung

variable {c : ℝ} {k : ℕ}

/-- `λ = μ²c/(2π)`. -/
theorem lamR_eq (hc : 0 < c) : lamR c k = muR c k ^ 2 * (c / (2 * π)) := by
  unfold lamR; rw [mul_pow, Real.sq_sqrt (by positivity)]

/-- **The exterior mass of a rung**: `∫₁^∞ψ² = (π/c)(1 − λ)`. -/
theorem mass_eq (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) :
    ∫ ξ in Ioi 1, psi c (rung c k) ξ ^ 2 = π / c * (1 - lamR c k) := by
  obtain ⟨-, -, -, -, heven, hnorm⟩ := rung_spec h
  exact Cvs.Prolate.AngularBesselInequality.mass_eq hc (continuousOn_rung h) heven (psi_rung h) hnorm

/-- `λ ≤ 1` for a rung. -/
theorem lamR_le_one (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) : lamR c k ≤ 1 := by
  have hm := mass_eq hc h
  have h0 : 0 ≤ ∫ ξ in Ioi 1, psi c (rung c k) ξ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  rw [hm] at h0
  have : 0 < π / c := by positivity
  nlinarith

/-- `ψ(1)² c/(2π) = λ h(1)²`. -/
theorem psi_one_sq (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) :
    psi c (rung c k) 1 ^ 2 * (c / (2 * π)) = rung c k 1 ^ 2 * lamR c k := by
  rw [psi_rung h 1 ⟨by norm_num, le_rfl⟩, lamR_eq hc]; ring

/-- **The edge value of a rung**: for `c ≥ 1` and `χ_k < c²`, `λ h(1)² ≤ (72/49)(2D + 3c)(1 − λ)`, `D = c² − χ_k`. -/
theorem edge_sq_le (hc : 1 ≤ c) (h : ∃ χ, IsLevelIdx c k χ) (hχc : lev c k < c ^ 2) :
    rung c k 1 ^ 2 * lamR c k ≤ 72 / 49 * (2 * (c ^ 2 - lev c k) + 3 * c) * (1 - lamR c k) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := rung_spec h
  have hB := Cvs.Prolate.Envelope.RungEdgeMassExterior.edge_mass hc hχc hg hg₁ hg₂c hang
  rw [mass_eq hc0 h] at hB
  rw [← psi_one_sq hc0 h]
  have hk : 0 < c / (2 * π) := by positivity
  calc psi c (rung c k) 1 ^ 2 * (c / (2 * π))
      ≤ 144 / 49 * (2 * (c ^ 2 - lev c k) + 3 * c) * (π / c * (1 - lamR c k)) * (c / (2 * π)) :=
        mul_le_mul_of_nonneg_right hB hk.le
    _ = 72 / 49 * (2 * (c ^ 2 - lev c k) + 3 * c) * (1 - lamR c k) := by field_simp; ring

end rung

/-! ### The derivative factor on the index window -/

/-! ### `HPRe`: the exterior law on the plunge edge -/

end Cvs.Prolate.Envelope.RungExteriorLaw
