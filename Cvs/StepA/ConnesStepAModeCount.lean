import Mathlib
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Limit.ModeSumsToMinimiser
import Cvs.StepA.OddAboveDisplacement
import Cvs.StepA.StepAPredicate
import Cvs.TheoremSixOne.MinimiserTransformRealZeros
import Cvs.Upstream.SymmetricMatrixBottom
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
# Connes' Step A at `N` modes is step (a) together with even simplicity

For the matrix `M` of the truncated Weil form on `N` mode pairs, "the smallest eigenvalue is simple
with even eigenvector" holds exactly when the odd sector lies strictly above the even bottom and
the even bottom is simple. Connes' operator-level Step A gives it at every large `N`.
-/

noncomputable section

open Real Matrix Filter

namespace Cvs.StepA.ConnesStepAModeCount
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI lamD xiD)
open Cvs.Finite.EvenMinimisers (evLam evMin EvenSimple)

/-- **Connes' Step A at `N` modes**: the smallest eigenvalue `μ` of the truncated Weil matrix is
simple, with an even eigenvector `v`. -/
def ConnesStepAN (P R : ℕ) (L : ℝ) (N : ℕ) : Prop :=
  ∃ (μ : ℝ) (v : Idx N → ℝ), v ≠ 0 ∧ (∀ i, v (negI N i) = v i) ∧
    Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v = μ • v ∧
    (∀ w : Idx N → ℝ, μ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w)) ∧
    ∀ w : Idx N → ℝ, Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w = μ • w → ∃ c : ℝ, w = c • v

/-- **Connes' Step A at `N` modes is step (a) together with even simplicity.** -/
theorem connesStepAN_iff (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    ConnesStepAN P R L N ↔
      Cvs.StepA.OddAboveDisplacement.OddAbove P R L hL N ∧ EvenSimple P R L hL N := by
  set M := Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) with hM
  have hinj := Cvs.Finite.SymmetricModeSet.mode_injective N
  have hinv := Cvs.Finite.SymmetricModeSet.negI_involutive N
  have hmode := Cvs.Finite.SymmetricModeSet.mode_negI N
  have hsymm : ∀ i j, M i j = M j i := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj
  have hA : ∀ i j, M (negI N i) (negI N j) = M i j := Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R hinj hmode
  obtain ⟨hme, hm1, hmbot, hmeig⟩ := Cvs.Finite.EvenMinimisers.evMin_spec P R hL N
  have hpos : ∀ w : Idx N → ℝ, w ≠ 0 → 0 < w ⬝ᵥ w := fun w hw =>
    lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' w)
      (fun h => hw (dotProduct_self_eq_zero.mp h.symm))
  constructor
  · rintro ⟨μ, v, hv0, hve, hMv, hbot, hsimple⟩
    -- the bottom is the even bottom
    have hle1 : evLam P R L hL N ≤ μ := by
      have h := hmbot v hve
      rw [hMv, dotProduct_smul, smul_eq_mul] at h
      exact le_of_mul_le_mul_right h (hpos v hv0)
    have hle2 : μ ≤ evLam P R L hL N := by
      have h := hbot (evMin P R L hL N)
      rw [hmeig, dotProduct_smul, smul_eq_mul, hm1, mul_one, mul_one] at h
      exact h
    have hμ : μ = evLam P R L hL N := le_antisymm hle2 hle1
    -- `M − μ` is positive semidefinite
    set D : Matrix (Idx N) (Idx N) ℝ := M - μ • (1 : Matrix (Idx N) (Idx N) ℝ) with hD
    have hDsymm : ∀ i j, D i j = D j i := by
      intro i j
      simp only [hD, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hsymm i j, smul_eq_mul]
      by_cases h : i = j
      · subst h; rfl
      · simp [h, Ne.symm h]
    have hDform : ∀ w, w ⬝ᵥ (D *ᵥ w) = w ⬝ᵥ (M *ᵥ w) - μ * (w ⬝ᵥ w) := by
      intro w
      simp only [hD, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
    have hDpsd : ∀ w, 0 ≤ w ⬝ᵥ (D *ᵥ w) := fun w => by rw [hDform]; linarith [hbot w]
    refine ⟨fun o hodd hne => ?_, fun w hwe hMw => ?_⟩
    · rw [← hμ]
      rcases (hbot o).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hz : o ⬝ᵥ (D *ᵥ o) = 0 := by rw [hDform]; linarith
        have hk := Cvs.Upstream.SymmetricMatrixBottom.mulVec_eq_zero_of_min hDsymm hDpsd hz
        have hMo : M *ᵥ o = μ • o := by
          rw [hD, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hk
          exact hk
        obtain ⟨c, hc⟩ := hsimple o hMo
        apply hne
        funext i
        have h1 := hodd i
        rw [hc] at h1 ⊢
        simp only [Pi.smul_apply, smul_eq_mul, hve i] at h1 ⊢
        simp only [Pi.zero_apply]
        linarith
    · rw [← hμ] at hMw
      obtain ⟨c, hc⟩ := hsimple w hMw
      have hMe : M *ᵥ evMin P R L hL N = μ • evMin P R L hL N := by rw [hmeig, hμ]
      obtain ⟨c', hc'⟩ := hsimple _ hMe
      have hc'0 : c' ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc'
        rw [hc', dotProduct_zero] at hm1
        exact zero_ne_one hm1
      refine ⟨c * c'⁻¹, ?_⟩
      rw [hc, hc', smul_smul, mul_assoc, inv_mul_cancel₀ hc'0, mul_one]
  · rintro ⟨hodd, hsim⟩
    have hge : ∀ w : Idx N → ℝ, evLam P R L hL N * (w ⬝ᵥ w) ≤ w ⬝ᵥ (M *ᵥ w) := by
      intro w
      have hsplit := Cvs.Finite.TruncationQuadraticForm.dotProduct_mulVec_split hsymm hinv hA w
      have hsp := Cvs.Finite.TruncationQuadraticForm.dotProduct_split hinv w
      have he := hmbot (Cvs.Finite.TruncationQuadraticForm.evenPart (negI N) w)
        (Cvs.Finite.TruncationQuadraticForm.evenPart_even hinv w)
      have ho : evLam P R L hL N * (Cvs.Finite.TruncationQuadraticForm.oddPart (negI N) w
          ⬝ᵥ Cvs.Finite.TruncationQuadraticForm.oddPart (negI N) w)
          ≤ Cvs.Finite.TruncationQuadraticForm.oddPart (negI N) w
            ⬝ᵥ (M *ᵥ Cvs.Finite.TruncationQuadraticForm.oddPart (negI N) w) := by
        by_cases h0 : Cvs.Finite.TruncationQuadraticForm.oddPart (negI N) w = 0
        · rw [h0]; simp
        · exact (hodd _ (Cvs.Finite.TruncationQuadraticForm.oddPart_odd hinv w) h0).le
      rw [hsplit, hsp]
      linarith
    refine ⟨evLam P R L hL N, evMin P R L hL N, ?_, hme, hmeig, hge,
      Cvs.Upstream.SymmetricMatrixBottom.kerline_of_even hsymm hinv hA hge hodd hsim⟩
    rintro h0
    rw [h0, dotProduct_zero] at hm1
    exact zero_ne_one hm1

/-- **Connes' Step A at scale `L` gives Connes' Step A at every large mode count `N`**, with the
discrete bottom `lamD N` and its eigenvector `xiD N`. -/
theorem eventually_connesStepAN_of_connesStepA {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (h : Cvs.TheoremSixOne.MinimiserTransformRealZeros.ConnesStepA hL P R lam η) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ConnesStepAN P R L N := by
  have hA := h.stepA
  obtain ⟨mu, hmu, hiso⟩ := hA.isolated
  have hglb := Cvs.Limit.ModeSumsToMinimiser.isGLB_of_stepA hL P R hA
  obtain ⟨N₁, hN₁⟩ := Cvs.Finite.SymmetricModeSet.lamD_lt_of_glb P R hL hglb (ε := mu - lam)
    (by linarith)
  refine ⟨N₁, fun N hN => ?_⟩
  have hlt : lamD P R L hL N < mu := by have := hN₁ N hN; linarith
  obtain ⟨hxi1, hge, hxi⟩ := Cvs.Finite.SymmetricModeSet.xiD_spec P R L hL N
  have hinj := Cvs.Finite.SymmetricModeSet.mode_injective N
  have hinv := Cvs.Finite.SymmetricModeSet.negI_involutive N
  have hmode := Cvs.Finite.SymmetricModeSet.mode_negI N
  have hsymm := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj
  have hAm := Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R hinj hmode
  have hxe := Cvs.Finite.DisplacementIdentity.xiD_even hL P R (lam := lam) hA.even hiso N hlt
  have hgap : ∀ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) → o ≠ 0 →
      lamD P R L hL N * (o ⬝ᵥ o) < o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o) := by
    intro o hodd hne
    have h1 := Cvs.Finite.DiscreteTwoGap.odd_gap_of_stepA hL P R (lam := lam) hA.even hiso hinj hinv
      hmode hodd
    have hpos : 0 < o ⬝ᵥ o := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
      (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
    calc lamD P R L hL N * (o ⬝ᵥ o) < mu * (o ⬝ᵥ o) := mul_lt_mul_of_pos_right hlt hpos
      _ ≤ _ := h1
  have hker := Cvs.Upstream.SymmetricMatrixBottom.kerline_of_even hsymm hinv hAm hge hgap
    (Cvs.Finite.DiscreteTwoGap.even_kerline_of_stepA hL P R hiso hinj hinv hmode hlt hxi1 hxe hxi)
  refine ⟨lamD P R L hL N, xiD P R L hL N, ?_, hxe, hxi, hge, hker⟩
  rintro h0
  rw [h0, dotProduct_zero] at hxi1
  exact zero_ne_one hxi1

end Cvs.StepA.ConnesStepAModeCount
