import Mathlib
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Upstream.FourierLpConjReflect

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Hardy projection of a real function

`(specGe 0)ᗮ` consists of the `v` with `𝓕 v = 0` a.e. on `[0, ∞)`; so for real `F` the two halves are conjugate,
`conj (P₊ F) = F − P₊ F`.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform

namespace Cvs.Upstream.HardyProjectionReal
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C specGe posProj fourierL mulOp)
open Cvs.Upstream.FourierLpConjReflect (conjLp reflLp)

theorem fourierL_apply (u : L2C) : fourierL u = (𝓕 u : L2C) := rfl

theorem mem_specGe_iff {β : ℝ} {u : L2C} :
    u ∈ specGe β ↔ ∀ᵐ ξ ∂volume, ξ < β → ((𝓕 u : L2C) : ℝ → ℂ) ξ = 0 := by
  change (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Iio β)) (fourierL u) = 0 ↔ _
  rw [Lp.eq_zero_iff_ae_eq_zero, fourierL_apply]
  have h2 := LpToLpRestrictCLM_coeFn ℂ (Iio β) (𝓕 u : L2C)
  have h3 := Lp.coeFn_zero ℂ 2 (volume.restrict (Iio β))
  have e : ((LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Iio β)) (𝓕 u : L2C) : ℝ → ℂ) =ᵐ[volume.restrict (Iio β)] 0 ↔
      ((𝓕 u : L2C) : ℝ → ℂ) =ᵐ[volume.restrict (Iio β)] 0 := by
    constructor
    · intro h; exact h2.symm.trans h
    · intro h; exact h2.trans h
  rw [e, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iio]
  rfl

theorem coeFn_mulOp {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ)) (u : L2C) :
    (mulOp m u : ℝ → ℂ) =ᵐ[volume] fun x => m x * (u : ℝ → ℂ) x := by
  rw [mulOp, dif_pos hm, ContinuousLinearMap.holderL_apply_apply]
  filter_upwards [ContinuousLinearMap.coeFn_holder (r := 2) (ContinuousLinearMap.lsmul ℂ ℂ) (hm.toLp m) u,
    hm.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  rfl

theorem memLp_top_indicator_one (s : Set ℝ) (hs : MeasurableSet s) :
    MemLp (s.indicator fun _ => (1 : ℂ)) ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound ((measurable_const.indicator hs).aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ s <;> simp [hx])

/-- A function in `(specGe 0)ᗮ` has Fourier transform vanishing a.e. on `[0, ∞)`. -/
theorem fourier_vanish_of_mem_orthogonal {v : L2C} (hv : v ∈ (specGe 0)ᗮ) :
    ∀ᵐ ξ ∂volume, 0 ≤ ξ → ((𝓕 v : L2C) : ℝ → ℂ) ξ = 0 := by
  set g : L2C := 𝓕 v
  set χ : ℝ → ℂ := (Ici (0 : ℝ)).indicator fun _ => 1
  have hχ : MemLp χ ⊤ (volume : Measure ℝ) := memLp_top_indicator_one _ measurableSet_Ici
  set u : L2C := 𝓕⁻ (mulOp χ g)
  have hFu : (𝓕 u : L2C) = mulOp χ g := FourierTransform.fourier_fourierInv_eq _
  have hu : u ∈ specGe 0 := by
    rw [mem_specGe_iff, hFu]
    filter_upwards [coeFn_mulOp hχ g] with ξ h hξ
    rw [h]; simp [χ, indicator_of_notMem (show ξ ∉ Ici (0 : ℝ) from fun h => absurd h (not_le.2 hξ))]
  have h0 : inner ℂ u v = 0 := Submodule.inner_right_of_mem_orthogonal hu hv
  rw [← Lp.inner_fourier_eq, hFu, L2.inner_def] at h0
  have hint : ∫ ξ, (Ici (0 : ℝ)).indicator (fun ξ => ‖(g : ℝ → ℂ) ξ‖ ^ 2) ξ = 0 := by
    have e : (fun ξ => inner ℂ ((mulOp χ g : L2C) ξ) ((g : ℝ → ℂ) ξ)) =ᵐ[volume]
        fun ξ => (((Ici (0 : ℝ)).indicator (fun ξ => ‖(g : ℝ → ℂ) ξ‖ ^ 2) ξ : ℝ) : ℂ) := by
      filter_upwards [coeFn_mulOp hχ g] with ξ h
      rw [h]
      by_cases hξ : ξ ∈ Ici (0 : ℝ)
      · simp only [χ, indicator_of_mem hξ, one_mul]
        rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ((g : ℝ → ℂ) ξ)]; push_cast; rfl
      · simp [χ, indicator_of_notMem hξ]
    rw [integral_congr_ae e, integral_complex_ofReal] at h0
    exact_mod_cast h0
  rw [integral_indicator measurableSet_Ici] at hint
  have hnn : 0 ≤ᵐ[volume.restrict (Ici (0 : ℝ))] fun ξ => ‖(g : ℝ → ℂ) ξ‖ ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hI : Integrable (fun ξ => ‖(g : ℝ → ℂ) ξ‖ ^ 2) (volume.restrict (Ici (0 : ℝ))) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp g).aestronglyMeasurable).1 (Lp.memLp g)).restrict
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hI).1 hint
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ici] at this
  filter_upwards [this] with ξ h hξ
  have := h hξ
  simpa using this

theorem vanish_neg {g : ℝ → ℂ} {P : ℝ → Prop} (h : ∀ᵐ ξ ∂volume, P ξ → g ξ = 0) :
    ∀ᵐ ξ ∂volume, P (-ξ) → g (-ξ) = 0 :=
  (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae h

theorem fourier_conjLp_ae (u : L2C) :
    ((𝓕 (conjLp u) : L2C) : ℝ → ℂ) =ᵐ[volume] fun ξ => (starRingEnd ℂ) (((𝓕 u : L2C) : ℝ → ℂ) (-ξ)) := by
  rw [Cvs.Upstream.FourierLpConjReflect.fourier_conjLp]
  filter_upwards [Cvs.Upstream.FourierLpConjReflect.coeFn_conjLp (reflLp (𝓕 u)), Cvs.Upstream.FourierLpConjReflect.coeFn_reflLp (𝓕 u : L2C)] with ξ h1 h2
  rw [h1, h2]

theorem fourier_sub (a b : L2C) : (𝓕 (a - b) : L2C) = 𝓕 a - 𝓕 b :=
  map_sub (Lp.fourierTransformₗᵢ ℝ ℂ) a b

theorem conjLp_conjLp (u : L2C) : conjLp (conjLp u) = u := by
  refine Lp.ext ?_
  filter_upwards [Cvs.Upstream.FourierLpConjReflect.coeFn_conjLp (conjLp u), Cvs.Upstream.FourierLpConjReflect.coeFn_conjLp u] with x h1 h2
  rw [h1, h2, Complex.conj_conj]

theorem eq_zero_of_fourier_vanish {D : L2C} (h : ∀ᵐ ξ ∂volume, ξ ≠ 0 → ((𝓕 D : L2C) : ℝ → ℂ) ξ = 0) :
    D = 0 := by
  have hne : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∈ ({0} : Set ℝ)ᶜ := compl_mem_ae_iff.2 (measure_singleton 0)
  have h0 : (𝓕 D : L2C) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [h, hne] with ξ h1 h2 using h1 h2
  have : (Lp.fourierTransformₗᵢ ℝ ℂ) D = (Lp.fourierTransformₗᵢ ℝ ℂ) 0 := by
    rw [map_zero]; exact h0
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).injective this

/-- **The two Hardy halves of a real function are conjugate**: `conj (P₊ F) = F − P₊ F` when `F̄ = F`. -/
theorem conjLp_posProj {F : L2C} (hF : conjLp F = F) : conjLp (posProj F) = F - posProj F := by
  set A := posProj F with hAdef
  set Q := F - A with hQdef
  have hA : A ∈ specGe 0 := Submodule.starProjection_apply_mem _ F
  have hQ : Q ∈ (specGe 0)ᗮ := Submodule.sub_starProjection_mem_orthogonal F
  have FA := mem_specGe_iff.1 hA
  have FQ := fourier_vanish_of_mem_orthogonal hQ
  have hsplit : A + Q = conjLp A + conjLp Q := by
    rw [← map_add, show A + Q = F by rw [hQdef]; abel, hF]
  set D := A - conjLp Q with hD
  have hD' : D = conjLp A - Q := by
    rw [hD, sub_eq_sub_iff_add_eq_add, hsplit]
  have hD0 : D = 0 := by
    refine eq_zero_of_fourier_vanish ?_
    have e1 := fourier_sub A (conjLp Q)
    have e2 := fourier_sub (conjLp A) Q
    rw [← hD] at e1
    rw [← hD'] at e2
    filter_upwards [FA, FQ, vanish_neg FA, vanish_neg FQ, fourier_conjLp_ae A, fourier_conjLp_ae Q,
      Lp.coeFn_sub (𝓕 A : L2C) (𝓕 (conjLp Q)), Lp.coeFn_sub (𝓕 (conjLp A) : L2C) (𝓕 Q)]
      with ξ hA1 hQ1 hA2 hQ2 hcA hcQ hs1 hs2 hξ
    rcases lt_or_gt_of_ne hξ with hlt | hgt
    · rw [e1, hs1, Pi.sub_apply, hcQ, hA1 hlt, hQ2 (show 0 ≤ -ξ by linarith), map_zero, sub_zero]
    · rw [e2, hs2, Pi.sub_apply, hcA, hA2 (show -ξ < 0 by linarith), hQ1 hgt.le, map_zero, sub_zero]
  have : A = conjLp Q := sub_eq_zero.1 hD0
  rw [this, conjLp_conjLp]

end Cvs.Upstream.HardyProjectionReal

end
