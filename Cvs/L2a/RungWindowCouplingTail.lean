import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The coupling of a rung with the window is its tail pairing

By the radical lemma, `weilθ(k_G, v) = −weilθ(τ_G, v)` for every tame `v` in the window, with
`τ_G = fullTail (psi c G)` the rung's tail beyond the window; since the tail lives on `θ > 1` and
`v` on `θ ≤ 1`, the prime channel of that pairing is `−Σ_n Λ(n) ∫ v(θ) τ_G(nθ) dθ` over every prime
power `n`, the ones beyond the window included.
-/

namespace Cvs.L2a.RungWindowCouplingTail

open Real Set Filter Topology MeasureTheory
open scoped ArithmeticFunction
open Cvs.WeilForm.ThetaSpaceParseval (mellinR poleP poleM dil weilθ)
open Cvs.L2a.TailLogScaleTest (logScale)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.FullTailPolarisation (crossSpec)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.WindowFormTailLimit (Tame tailRem)

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

theorem posTail_add_tailRem (Φ : ℝ → ℝ) (X : ℝ) :
    (fun θ => posTail Φ X θ + tailRem Φ X θ) = fullTail Φ := by
  funext θ; simp [Cvs.L2a.WindowFormTailLimit.tailRem]

/-- **The coupling of a window rung with a tame window function is minus its tail pairing.** -/
theorem coupling_eq_neg_tail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hG0 : G 0 = 0)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) {v : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) :
    weilθ (window (2 * π / c) G) v = -weilθ (fullTail (psi c G)) v := by
  have h := Cvs.L2a.WindowFormTailLimit.weilθ_split_eq_zero hg hg₁ hg₂c heven hc hG0 hGi (le_refl (1:ℝ)) hv
  have hadd := Cvs.L2a.WindowFormTailLimit.weilθ_add
    (Cvs.L2a.WindowFormTailLimit.adm_of_tame
      (Cvs.L2a.WindowFormTailLimit.tame_posTail_psi hg hg₁ hg₂c hc (le_refl (1:ℝ))) hv)
    (Cvs.L2a.WindowFormTailLimit.adm_tailRem hg hg₁ hg₂c heven hc hG0 hGi (le_refl (1:ℝ)) hv)
  rw [posTail_add_tailRem] at hadd
  linarith

/-- The tail lives beyond `θ = 1`, the window function below it: the left dilates vanish. -/
theorem dil_fullTail_left_eq_zero (Φ : ℝ → ℝ) {v : ℝ → ℝ} {α β : ℝ} (hβ : β ≤ 1)
    (hsupp : ∀ θ ∉ Icc α β, v θ = 0) {n : ℕ} (hn : 0 < n) : dil (fullTail Φ) v n = 0 := by
  unfold dil
  refine setIntegral_eq_zero_of_forall_eq_zero fun θ _ => ?_
  by_cases h1 : θ ≤ 1
  · rw [Cvs.Xi.EImageWindowPoisson.fullTail_of_le_one Φ h1, zero_mul]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : (1 : ℝ) < n * θ := by push_neg at h1; nlinarith
    have : v (n * θ) = 0 := hsupp _ fun h => by linarith [h.2]
    rw [this, mul_zero]

/-- **The coupling formula.** The coupling of the rung with `v` is minus the tail's pole and
archimedean pairings with `v`, plus the von Mangoldt sum of the correlations `∫ v(θ) τ_G(nθ) dθ`. -/
theorem coupling_formula (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hG0 : G 0 = 0)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) {v : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) (hβ : β ≤ 1) :
    weilθ (window (2 * π / c) G) v
      = -(poleP (fullTail (psi c G)) * poleM v + poleM (fullTail (psi c G)) * poleP v
          + (∫ t, archSymbol t * crossSpec (logScale (fullTail (psi c G))) (logScale v) t))
        + ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil v (fullTail (psi c G)) n := by
  rw [coupling_eq_neg_tail hg hg₁ hg₂c heven hc hG0 hGi hv]
  unfold weilθ
  have hd : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)
      * (dil (fullTail (psi c G)) v n + dil v (fullTail (psi c G)) n)
      = (ArithmeticFunction.vonMangoldt n : ℝ) * dil v (fullTail (psi c G)) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [dil_fullTail_left_eq_zero _ hβ hv.supp hn, zero_add]
  simp_rw [hd]
  ring

end Cvs.L2a.RungWindowCouplingTail
