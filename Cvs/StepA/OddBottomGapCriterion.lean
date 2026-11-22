import Mathlib
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.StepA.EvenBelowOdd
import Cvs.StepA.OddAboveDisplacement
import Cvs.StepA.OddAboveUnderRH
import Cvs.StepA.PosDefOffLattice
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Step (a) at every large scale and mode count, and RH with an odd bottom gap gives it

`StepA L₀ N₀` is `OddAbove` for the window matrix at `P = ⌈e^L⌉₊`, `R = ⌈L / log 2⌉₊` for all `L ≥ L₀`,
`N ≥ N₀`; `StepANat` restricts it to `L = log x` with `x ∈ ℕ`, where `⌈e^{log x}⌉₊ = x`. Under RH an odd
bottom eigenpair with positive level and `Ω_h` below every zero ordinate gives step (a) at its scale.
-/

noncomputable section

open Matrix Real

namespace Cvs.StepA.OddBottomGapCriterion
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Finite.OddEigenvectorResolvent (xdiv)
open Cvs.StepA.OddAboveDisplacement (OddAbove)
open Cvs.Finite.ParitySectorDefect (MX)
open Cvs.StepA.EvenBelowOdd (omegaSq)

variable {L : ℝ} {N : ℕ}

/-! ### The predicates -/

/-- An odd bottom eigenpair of the window matrix with positive level and `Ω_h` below every zero
ordinate. -/
def OddBottomGap (L : ℝ) (N : ℕ) : Prop :=
  ∃ (μ : ℝ) (o : Idx N → ℝ), (∀ i, o (negI N i) = -o i) ∧ o ≠ 0 ∧
    MX L N *ᵥ o = μ • o ∧
    (∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) → μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (MX L N *ᵥ v)) ∧
    0 < μ ∧ ∀ ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, omegaSq L N o < ((ρ : ℂ).im) ^ 2

/-- An odd bottom eigenpair of the window matrix with `Ω_h` below every zero ordinate. -/
def OddBottomBelow (L : ℝ) (N : ℕ) : Prop :=
  ∃ (μ : ℝ) (o : Idx N → ℝ), (∀ i, o (negI N i) = -o i) ∧ o ≠ 0 ∧
    MX L N *ᵥ o = μ • o ∧
    (∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) → μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (MX L N *ᵥ v)) ∧
    ∀ ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, omegaSq L N o < ((ρ : ℂ).im) ^ 2

/-! ### Integer scales -/

/-- The prime cut at `L = log x` is `x`: `⌈e^{log x}⌉₊ = x` for `0 < x`. -/
theorem ceil_exp_log_natCast {x : ℕ} (hx : 0 < x) : ⌈Real.exp (Real.log x)⌉₊ = x := by
  rw [Real.exp_log (Nat.cast_pos.mpr hx), Nat.ceil_natCast]

/-! ### RH and the odd bottom gap -/

/-- **RH and an odd bottom gap at `(L, N)` give step (a) at `(L, N)`.** -/
theorem oddAbove_of_oddBottomGap (hRH : RiemannHypothesis) (hL : 0 < L) (h : OddBottomGap L N) :
    OddAbove ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  obtain ⟨μ, o, hodd, hne, hMo, hbot, hμ, hΩ⟩ := h
  exact Cvs.StepA.OddAboveUnderRH.oddAbove_of_RH hRH hL hodd hne hMo hbot hμ hΩ

/-! ### Below a common gap, and off the lattice `2πℤ/L` -/

/-- An odd bottom eigenpair with `|o|² < c²·|xdiv o|²` below a common gap `0 ≤ c ≤ |γ_ρ|` has `Ω_h`
below every zero ordinate. -/
theorem oddBottomBelow_of_gap (hL : 0 < L) {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, c ≤ |(ρ : ℂ).im|) {μ : ℝ} {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) (hMo : MX L N *ᵥ o = μ • o)
    (hbot : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) → μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (MX L N *ᵥ v))
    (hΩ : o ⬝ᵥ o < c ^ 2 * (xdiv L N o ⬝ᵥ xdiv L N o)) : OddBottomBelow L N :=
  ⟨μ, o, hodd, Cvs.StepA.OddAboveUnderRH.ne_zero_of_lt_sq_mul hΩ, hMo, hbot,
    Cvs.StepA.OddAboveUnderRH.omegaSq_lt_of_gap hL hodd hc hgap hΩ⟩

/-- **Under RH, when the zeros whose ordinate avoids `2πℤ/L` have more than `N` distinct squared
ordinates, an odd bottom eigenpair with `Ω_h` below every zero ordinate has positive level.** -/
theorem oddBottomGap_of_RH_offLattice (hRH : RiemannHypothesis) (hL : 0 < L)
    (hZ : (N : ℕ∞) < (Cvs.StepA.PosDefOffLattice.offLatticeSq L).encard) (h : OddBottomBelow L N) :
    OddBottomGap L N := by
  obtain ⟨μ, o, hodd, hne, hMo, hbot, hΩ⟩ := h
  have ho : 0 < o ⬝ᵥ o := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
    (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
  have hpos := Cvs.StepA.PosDefOffLattice.oddForm_pos_of_RH hRH hL hodd hne hZ
  rw [hMo, dotProduct_smul, smul_eq_mul] at hpos
  exact ⟨μ, o, hodd, hne, hMo, hbot, pos_of_mul_pos_left hpos ho.le, hΩ⟩

end Cvs.StepA.OddBottomGapCriterion
