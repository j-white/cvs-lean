import Mathlib
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.StepA.OddAboveDisplacement
import Cvs.Upstream.SymmetricMatrixBottom

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Step (a) is the even bottom below the odd bottom, and a sufficient condition over the zeros

`OddAbove` holds exactly when the even bottom lies below the odd bottom eigenvalue `μ`. The division
vector of the odd bottom eigenvector is an even trial: its Rayleigh quotient is below `μ` exactly when
the defect `∑ m_ρ Re[(Ω_h² − z_ρ²)·sq_x(z_ρ)]` at `Ω_h² = |o|²/|x|²` is negative.
-/

noncomputable section

open Matrix Real Cvs.Finite.SymmetricModeSet Cvs.Finite.OddEigenvectorResolvent Cvs.Finite.EvenMinimisers
open Cvs.StepA.OddAboveDisplacement

namespace Cvs.StepA.EvenBelowOdd
open Cvs.ZeroCounting

variable {P R : ℕ} {L : ℝ} {N : ℕ}

/-! ### Step (a) against the odd bottom -/

/-- **An odd lower bound strictly above the even bottom is step (a).** -/
theorem oddAbove_of_evLam_lt (hL : 0 < L) {μ : ℝ}
    (hbot : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) →
      μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
    (hlt : evLam P R L hL N < μ) : OddAbove P R L hL N := by
  intro o hodd hne
  have hpos : 0 < o ⬝ᵥ o := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
    (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hlt hpos) (hbot o hodd)

/-- Step (a) puts the even bottom strictly below every odd eigenvalue. -/
theorem evLam_lt_of_oddAbove {hL : 0 < L} (h : OddAbove P R L hL N) {μ : ℝ} {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) (hne : o ≠ 0)
    (hMo : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o = μ • o) : evLam P R L hL N < μ := by
  have hpos : 0 < o ⬝ᵥ o := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
    (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
  have h1 := h o hodd hne
  rw [hMo, dotProduct_smul, smul_eq_mul] at h1
  exact lt_of_mul_lt_mul_right h1 hpos.le

/-! ### The division vector as the even trial -/

theorem xdiv_zero (L : ℝ) (N : ℕ) : xdiv L N (0 : Idx N → ℝ) = 0 := by
  funext i
  rcases i with _ | j <;> simp [xdiv]

/-- The division vector of a nonzero odd vector is nonzero. -/
theorem xdiv_ne_zero (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) (hne : o ≠ 0) :
    xdiv L N o ≠ 0 := by
  intro h
  apply hne
  funext i
  rw [← om_mul_xdiv hL N hodd i, h, Pi.zero_apply, mul_zero]

/-- The squared division ratio `Ω_h² = |o|²/|xdiv o|²`. -/
def omegaSq (L : ℝ) (N : ℕ) (o : Idx N → ℝ) : ℝ := (o ⬝ᵥ o) / (xdiv L N o ⬝ᵥ xdiv L N o)

theorem omegaSq_nonneg (L : ℝ) (N : ℕ) (o : Idx N → ℝ) : 0 ≤ omegaSq L N o :=
  div_nonneg (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
    (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' _)

theorem dotProduct_xdiv_pos (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i)
    (hne : o ≠ 0) : 0 < xdiv L N o ⬝ᵥ xdiv L N o :=
  lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' _)
    (fun h => xdiv_ne_zero hL hodd hne (dotProduct_self_eq_zero.mp h.symm))

theorem omegaSq_mul (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) (hne : o ≠ 0) :
    omegaSq L N o * (xdiv L N o ⬝ᵥ xdiv L N o) = o ⬝ᵥ o :=
  div_mul_cancel₀ _ (dotProduct_xdiv_pos hL hodd hne).ne'

/-- `Ω_h² < b` is `|o|² < b·|xdiv o|²`. -/
theorem omegaSq_lt_iff (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) (hne : o ≠ 0)
    (b : ℝ) : omegaSq L N o < b ↔ o ⬝ᵥ o < b * (xdiv L N o ⬝ᵥ xdiv L N o) :=
  div_lt_iff₀ (dotProduct_xdiv_pos hL hodd hne)

/-! ### Step (a) from the zeros -/

end Cvs.StepA.EvenBelowOdd
