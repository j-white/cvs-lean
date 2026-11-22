import Mathlib
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Limit.ModeSumsToMinimiser
import Cvs.StepA.EvenBelowOdd
import Cvs.StepA.OddAboveDisplacement
import Cvs.StepA.StepAPredicate
import Cvs.TheoremSixOne.MinimiserTransformRealZeros
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Connes' Step A at a scale gives step (a) at every large mode count

Under Connes' Step A at scale `L` the odd window vectors have Rayleigh quotient at least the
isolation level `μ`, and the discrete bottoms `lamD(N)` fall below `μ` with even eigenvectors for all
large `N`; so the even-sector bottom `evLam(N)` lies below every odd Rayleigh quotient.
-/

noncomputable section

open Real Matrix Filter

namespace Cvs.StepA.ConnesStepAOddAbove
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI lamD xiD)

/-- **The even-sector bottom is at most the discrete bottom** when the discrete eigenvector is
even. -/
theorem evLam_le_lamD (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ)
    (hxe : ∀ i, xiD P R L hL N (negI N i) = xiD P R L hL N i) :
    Cvs.Finite.EvenMinimisers.evLam P R L hL N ≤ lamD P R L hL N := by
  obtain ⟨hxi1, -, hxi⟩ := Cvs.Finite.SymmetricModeSet.xiD_spec P R L hL N
  obtain ⟨-, -, hev, -⟩ := Cvs.Finite.EvenMinimisers.evMin_spec P R hL N
  have h := hev _ hxe
  rw [hxi, dotProduct_smul, smul_eq_mul, hxi1, mul_one, mul_one] at h
  exact h

/-- **Connes' Step A at scale `L` gives step (a) at every large mode count**: there is `N₀` with
`OddAbove` at every `N ≥ N₀`. -/
theorem eventually_oddAbove_of_connesStepA {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (h : Cvs.TheoremSixOne.MinimiserTransformRealZeros.ConnesStepA hL P R lam η) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → Cvs.StepA.OddAboveDisplacement.OddAbove P R L hL N := by
  have hA := h.stepA
  obtain ⟨mu, hmu, hiso⟩ := hA.isolated
  have hglb := Cvs.Limit.ModeSumsToMinimiser.isGLB_of_stepA hL P R hA
  obtain ⟨N₀, hN₀⟩ := Cvs.Finite.SymmetricModeSet.lamD_lt_of_glb P R hL hglb (ε := mu - lam)
    (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have hlt : lamD P R L hL N < mu := by have := hN₀ N hN; linarith
  have hxe := Cvs.Finite.DisplacementIdentity.xiD_even hL P R (lam := lam) hA.even hiso N hlt
  exact Cvs.StepA.EvenBelowOdd.oddAbove_of_evLam_lt hL (μ := mu)
    (fun v hv => Cvs.Finite.DiscreteTwoGap.odd_gap_of_stepA hL P R (lam := lam) hA.even hiso
      (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.negI_involutive N)
      (Cvs.Finite.SymmetricModeSet.mode_negI N) hv)
    (lt_of_le_of_lt (evLam_le_lamD P R hL N hxe) hlt)

end Cvs.StepA.ConnesStepAOddAbove
