import Mathlib
import Cvs.Prolate.Hardy.HardyExtensionOperator

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Conjugation and reflection against the `L²` Fourier transform

On `L²(ℝ, ℂ)`, `𝓕⁻ u = 𝓕 u ∘ (−·)` and `𝓕 ū = conj(𝓕 u ∘ (−·))`: both sides are continuous and agree on the dense
Schwartz functions, where they are the classical identities.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform SchwartzMap

namespace Cvs.Upstream.FourierLpConjReflect
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C)

/-- Complex conjugation on `L²(ℝ, ℂ)`, real-linear. -/
def conjLp : L2C →L[ℝ] L2C := (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 (volume : Measure ℝ)

/-- The reflection `u ↦ u(−·)` on `L²(ℝ, ℂ)`. -/
def reflLp : L2C →L[ℂ] L2C :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x) (Measure.measurePreserving_neg volume)).toContinuousLinearMap

theorem coeFn_conjLp (u : L2C) : (conjLp u : ℝ → ℂ) =ᵐ[volume] fun x => (starRingEnd ℂ) ((u : ℝ → ℂ) x) :=
  ContinuousLinearMap.coeFn_compLpL _ u

theorem coeFn_reflLp (u : L2C) : (reflLp u : ℝ → ℂ) =ᵐ[volume] fun x => (u : ℝ → ℂ) (-x) :=
  Lp.coeFn_compMeasurePreserving u _

theorem reflLp_toLp {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    reflLp (hg.toLp g) = (hg.comp_measurePreserving (Measure.measurePreserving_neg volume)).toLp _ :=
  Lp.toLp_compMeasurePreserving hg _

theorem conjLp_toLp {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    conjLp (hg.toLp g) = (hg.continuousLinearMap_comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).toLp _ :=
  Lp.ext ((coeFn_conjLp _).trans <| (hg.coeFn_toLp.fun_comp _).trans <|
    (MemLp.coeFn_toLp _).symm)

/-- The classical identity `𝓕 f̄ (ξ) = conj (𝓕 f (−ξ))`. -/
theorem fourier_conj_apply (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => (starRingEnd ℂ) (f x)) ξ = (starRingEnd ℂ) (𝓕 f (-ξ)) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_conj]
  congr 1
  ext v
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul, ← Circle.coe_inv_eq_conj,
    ← AddChar.map_neg_eq_inv]
  congr 3
  ring

theorem denseRange_schwartz :
    DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
  SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top

/-- **`𝓕⁻ u = 𝓕 u ∘ (−·)`** on `L²`. -/
theorem fourierInv_eq (u : L2C) : (𝓕⁻ u : L2C) = reflLp (𝓕 u) := by
  have hc1 : Continuous fun u : L2C => (𝓕⁻ u : L2C) := (Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous
  have hc2 : Continuous fun u : L2C => reflLp (𝓕 u : L2C) :=
    reflLp.continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  refine congrFun (denseRange_schwartz.equalizer hc1 hc2 ?_) u
  ext1 f
  simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply, SchwartzMap.toLp_fourierInv_eq,
    SchwartzMap.toLp_fourier_eq]
  rw [SchwartzMap.toLp, SchwartzMap.toLp, reflLp_toLp]
  refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
  simp [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, SchwartzMap.fourier_coe]

/-- **`𝓕 ū = conj(𝓕 u ∘ (−·))`** on `L²`. -/
theorem fourier_conjLp (u : L2C) : (𝓕 (conjLp u) : L2C) = conjLp (reflLp (𝓕 u)) := by
  have hc1 : Continuous fun u : L2C => (𝓕 (conjLp u) : L2C) :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp conjLp.continuous
  have hc2 : Continuous fun u : L2C => conjLp (reflLp (𝓕 u : L2C)) :=
    conjLp.continuous.comp (reflLp.continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
  refine congrFun (denseRange_schwartz.equalizer hc1 hc2 ?_) u
  ext1 f
  set g : 𝓢(ℝ, ℂ) := SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) f with hg
  have hgx : ∀ x, g x = (starRingEnd ℂ) (f x) := fun x => rfl
  have e1 : conjLp (f.toLp 2) = g.toLp 2 := by
    rw [SchwartzMap.toLp, SchwartzMap.toLp, conjLp_toLp]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => (hgx x).symm)
  simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply, SchwartzMap.toLp_fourier_eq]
  rw [e1, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp, SchwartzMap.toLp, reflLp_toLp, conjLp_toLp]
  refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
  simp only [SchwartzMap.fourier_coe, Function.comp_apply]
  rw [show (g : ℝ → ℂ) = fun x => (starRingEnd ℂ) (f x) from funext hgx, fourier_conj_apply]
  rfl

end Cvs.Upstream.FourierLpConjReflect

end
