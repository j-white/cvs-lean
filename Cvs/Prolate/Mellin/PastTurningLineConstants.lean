import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.GroundRatioLineModulus
import Cvs.Prolate.Mellin.GroundRatioStepErrors
import Cvs.Prolate.Mellin.GroundXiLawModulus
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Prolate.Mellin.LineConstantRatioLimit
import Cvs.Prolate.Mellin.NearRegionForcingSize
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.PastTurningRatioComplex
import Cvs.Prolate.Mellin.PastTurningStepErrors
import Cvs.Prolate.Mellin.RealLineRatioComplex
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The law ratio past the turning point against its line constants

Under `GroundXiLawModulus`'s largeness conditions and `z ≥ (2 + ε)c`, the two line formulas (Cvs.Prolate.Mellin.PastTurningRatioComplex, Cvs.Prolate.Mellin.RealLineRatioComplex) give, for every large `K`,
`W = P(½ + iz)/P(½) · exp(−(Ψ(½ + iz) − Ψ(½))) = Q_K exp(δ_K − δ′_K)`; with `Q_K → 1` (Cvs.Prolate.Mellin.LineConstantRatioLimit) and `v_K, v′_K → 0`,
`|W − 1| ≤ 2(E_U(ε, c) + E(ε, c))` whenever `E_U + E ≤ ½`.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Prolate.Mellin.PastTurningLineConstants
open Cvs.ZeroCounting

open Cvs.Prolate.Mellin.LawRatioRecurrence (lawRatio)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)
open Cvs.Prolate.Mellin.TrueRatioDownwardStep (Pk vk)
open Cvs.Prolate.Mellin.GroundRatioStepErrors (Std)
open Cvs.Prolate.Mellin.GroundXiLawModulus (Large)
open Cvs.Prolate.Mellin.PastTurningContraction (Up)
open Cvs.Prolate.Mellin.PastTurningRatioComplex (Psi EU)

variable {ε c : ℝ}

/-- The region past the turning point from the largeness conditions. -/
theorem Large.up (L : Large ε c) {z : ℝ} (hz : (2 + ε) * c ≤ z) : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + I * z) := by
  have h' : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2 : ℂ) := by
    simpa using L.hyp (z := 0) (by simp; nlinarith [L.hε16, L.hε, L.hc7])
  exact
    { hε := L.hε
      hε1 := by linarith [L.hε16]
      hc := L.hc
      hχ0 := h'.hχ0
      hχ1 := h'.hχ1
      hre := by simp
      him := by simpa using hz }

theorem Large.hcb (L : Large ε c) : 6000 / ε ^ 2 ≤ c := by
  have := L.hc5
  have : 6000 / ε ^ 2 ≤ 100000 / ε ^ 2 := by
    apply div_le_div_of_nonneg_right (by norm_num) (by have := L.hε; positivity)
  linarith [L.hc5]

/-- **The law ratio past the turning point against its line constants.** -/
theorem ratio_bound (L : Large ε c) {z : ℝ} (hz : (2 + ε) * c ≤ z) (hE : EU ε c + Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot ε c ≤ 1 / 2) :
    ‖lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) ((1 / 2 : ℂ) + I * z) / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (1 / 2)
        * Complex.exp (-(Psi c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + I * z) - Psi c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2))) - 1‖
      ≤ 2 * (EU ε c + Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot ε c) := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  set s₀ : ℂ := (1 / 2 : ℂ) + I * z
  have hc0 : 0 < c := by linarith [L.hc7]
  have hz0 : 0 ≤ z := by have := L.hε; nlinarith
  have h := Large.up L hz
  have hcb := Large.hcb L
  have h' : Hyp ε c χ (1 / 2 : ℂ) := by simpa using L.hyp (z := 0) (by simp; nlinarith [L.hε16, L.hε, L.hc7])
  have S' : Std ε c (1 / 2 : ℂ) := ⟨h', L.hε16, L.hc7, L.hs1, L.hs2⟩
  set W := lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) s₀ / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (1 / 2)
    * Complex.exp (-(Psi c χ s₀ - Psi c χ (1 / 2)))
  have hP0 : Pk c s₀ 0 = lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) s₀ := by unfold Pk; simp
  have hP0' : Pk c (1 / 2 : ℂ) 0 = lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (1 / 2) := by unfold Pk; simp
  have hb := Cvs.Prolate.Mellin.PastTurningStepErrors.bootstrap h hcb
  have hQ := Cvs.Prolate.Mellin.LineConstantRatioLimit.tendsto_Q hz0 h h'
  -- for every large `K = n + 1`: `exp(δ − δ′) = W/Q`
  set J := Cvs.Prolate.Mellin.NearRegionForcingSize.Jn c (1 / 2 : ℂ)
  have hkey : ∀ n : ℕ, J ≤ n →
      ∃ d : ℂ, ‖d‖ ≤ EU ε c + Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot ε c
          + ((1 + 4 / Real.sqrt ε) * ‖vk c χ s₀ (n + 1)‖ + (1 + 12 / Real.sqrt ε) * ‖vk c χ (1 / 2 : ℂ) (n + 1)‖)
        ∧ W = (Pk c s₀ (n + 1) / Pk c (1 / 2 : ℂ) (n + 1)
            * Complex.exp (Psi c χ ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)) - Psi c χ (s₀ + 2 * ((n + 1 : ℕ) : ℂ))))
          * Complex.exp d := by
    intro n hn
    obtain ⟨δ, hδ, hδb⟩ := Cvs.Prolate.Mellin.PastTurningRatioComplex.line_formula h hcb (n + 1) (by omega)
    obtain ⟨δ', hδ', hδb'⟩ := Cvs.Prolate.Mellin.RealLineRatioComplex.line_formula S' L.hc5 (n + 1) (by omega)
    refine ⟨δ - δ', ?_, ?_⟩
    · have := norm_sub_le δ δ'; linarith
    · simp only [W]
      rw [← hP0, ← hP0', hδ, hδ']
      set E1 := Complex.exp (Psi c χ s₀ - Psi c χ (s₀ + 2 * ((n + 1 : ℕ) : ℂ)) + δ)
      set E2 := Complex.exp (Psi c χ (1 / 2) - Psi c χ ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)) + δ')
      set E3 := Complex.exp (-(Psi c χ s₀ - Psi c χ (1 / 2)))
      have hE : E1 * E3 / E2 = Complex.exp (Psi c χ ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ))
          - Psi c χ (s₀ + 2 * ((n + 1 : ℕ) : ℂ))) * Complex.exp (δ - δ') := by
        simp only [E1, E2, E3]
        rw [← Complex.exp_add, ← Complex.exp_sub, ← Complex.exp_add]
        congr 1; ring
      calc Pk c s₀ (n + 1) * E1 / (Pk c (1 / 2 : ℂ) (n + 1) * E2) * E3
          = Pk c s₀ (n + 1) / Pk c (1 / 2 : ℂ) (n + 1) * (E1 * E3 / E2) := by ring
        _ = _ := by rw [hE]; ring
  -- pass to the limit
  set E := EU ε c + Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot ε c
  set η : ℕ → ℝ := fun n => (1 + 4 / Real.sqrt ε) * ‖vk c χ s₀ (n + 1)‖
    + (1 + 12 / Real.sqrt ε) * ‖vk c χ (1 / 2 : ℂ) (n + 1)‖
  have hv1 : Tendsto (fun n : ℕ => ‖vk c χ s₀ (n + 1)‖) atTop (𝓝 0) := by
    have := ((Cvs.Prolate.Mellin.PastTurningStepErrors.tendsto_vk h).comp (tendsto_add_atTop_nat 1)).norm
    rw [norm_zero] at this; exact this
  have hv2 : Tendsto (fun n : ℕ => ‖vk c χ (1 / 2 : ℂ) (n + 1)‖) atTop (𝓝 0) := by
    have := ((Cvs.Prolate.Mellin.TrueRatioDownwardStep.tendsto_vk h').comp (tendsto_add_atTop_nat 1)).norm
    rw [norm_zero] at this; exact this
  have hη : Tendsto η atTop (𝓝 0) := by
    have := (hv1.const_mul (1 + 4 / Real.sqrt ε)).add (hv2.const_mul (1 + 12 / Real.sqrt ε))
    rw [mul_zero, mul_zero, add_zero] at this; exact this
  set Q : ℕ → ℂ := fun n => Pk c s₀ (n + 1) / Pk c (1 / 2 : ℂ) (n + 1)
    * Complex.exp (Psi c χ ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)) - Psi c χ (s₀ + 2 * ((n + 1 : ℕ) : ℂ)))
  have hQ' : Tendsto Q atTop (𝓝 1) := hQ
  have hlim : Tendsto (fun n => ‖Q n‖ * (2 * (E + η n)) + ‖Q n - 1‖) atTop (𝓝 (‖(1 : ℂ)‖ * (2 * (E + 0)) + ‖(1 : ℂ) - 1‖)) :=
    (hQ'.norm.mul ((tendsto_const_nhds.add hη).const_mul 2)).add (hQ'.sub_const 1).norm
  simp only [norm_one, one_mul, add_zero, sub_self, norm_zero] at hlim
  have hev : ∀ᶠ n in atTop, ‖W - 1‖ ≤ ‖Q n‖ * (2 * (E + η n)) + ‖Q n - 1‖ := by
    have hsmall : ∀ᶠ n in atTop, η n ≤ 1 / 2 := hη.eventually (ge_mem_nhds (by norm_num))
    filter_upwards [eventually_ge_atTop J, hsmall] with n hn hs
    obtain ⟨d, hd, hW⟩ := hkey n hn
    have hd1 : ‖d‖ ≤ 1 := by linarith
    have hexp := Complex.norm_exp_sub_one_le hd1
    rw [hW]
    calc ‖Q n * Complex.exp d - 1‖ = ‖Q n * (Complex.exp d - 1) + (Q n - 1)‖ := by ring_nf
      _ ≤ ‖Q n‖ * ‖Complex.exp d - 1‖ + ‖Q n - 1‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ ‖Q n‖ * (2 * (E + η n)) + ‖Q n - 1‖ := by
          gcongr; linarith
  exact ge_of_tendsto hlim hev

end Cvs.Prolate.Mellin.PastTurningLineConstants
