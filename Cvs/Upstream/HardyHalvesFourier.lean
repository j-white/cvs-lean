import Mathlib
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Upstream.HardyProjectionReal
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.PlancherelL1L2SpectralDensity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two Hardy halves measure the two Fourier half-lines

`𝓕(P₊u) = 1_{[0,∞)}𝓕u` and `𝓕(u − P₊u) = 1_{(−∞,0)}𝓕u`, so `‖P₊u‖² = ∫_{ξ≥0}|𝓕u|²` and
`‖u − P₊u‖² = ∫_{ξ<0}|𝓕u|²`; on `L¹ ∩ L²` these are integrals of the Fourier integral.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform

namespace Cvs.Upstream.HardyHalvesFourier
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C specGe posProj)

theorem coeFn_fourier_sub (a b : L2C) :
    ((𝓕 (a - b) : L2C) : ℝ → ℂ) =ᵐ[volume] fun ξ => ((𝓕 a : L2C) : ℝ → ℂ) ξ - ((𝓕 b : L2C) : ℝ → ℂ) ξ := by
  rw [Cvs.Upstream.HardyProjectionReal.fourier_sub]
  exact Lp.coeFn_sub _ _

/-- `𝓕(u − P₊u) = 1_{(−∞,0)}𝓕u` a.e. -/
theorem fourier_sub_posProj (u : L2C) :
    ((𝓕 (u - posProj u) : L2C) : ℝ → ℂ) =ᵐ[volume] (Iio (0 : ℝ)).indicator ((𝓕 u : L2C) : ℝ → ℂ) := by
  have hA : posProj u ∈ specGe 0 := Submodule.starProjection_apply_mem _ u
  have hQ : u - posProj u ∈ (specGe 0)ᗮ := Submodule.sub_starProjection_mem_orthogonal u
  filter_upwards [Cvs.Upstream.HardyProjectionReal.mem_specGe_iff.1 hA, Cvs.Upstream.HardyProjectionReal.fourier_vanish_of_mem_orthogonal hQ,
    coeFn_fourier_sub u (posProj u)] with ξ h1 h2 h3
  by_cases hξ : ξ < 0
  · rw [indicator_of_mem (show ξ ∈ Iio (0 : ℝ) from hξ), h3, h1 hξ, sub_zero]
  · rw [indicator_of_notMem (show ξ ∉ Iio (0 : ℝ) from hξ), h2 (not_lt.1 hξ)]

/-- `𝓕(P₊u) = 1_{[0,∞)}𝓕u` a.e. -/
theorem fourier_posProj (u : L2C) :
    ((𝓕 (posProj u) : L2C) : ℝ → ℂ) =ᵐ[volume] (Ici (0 : ℝ)).indicator ((𝓕 u : L2C) : ℝ → ℂ) := by
  have e : posProj u = u - (u - posProj u) := by abel
  have h := coeFn_fourier_sub u (u - posProj u)
  rw [← e] at h
  filter_upwards [h, fourier_sub_posProj u] with ξ h1 h2
  rw [h1, h2]
  by_cases hξ : ξ < 0
  · rw [indicator_of_mem (show ξ ∈ Iio (0 : ℝ) from hξ),
      indicator_of_notMem (show ξ ∉ Ici (0 : ℝ) from not_le.2 hξ), sub_self]
  · rw [indicator_of_notMem (show ξ ∉ Iio (0 : ℝ) from hξ),
      indicator_of_mem (show ξ ∈ Ici (0 : ℝ) from not_lt.1 hξ), sub_zero]

theorem norm_sq_of_ae_indicator {g : L2C} {s : Set ℝ} (hs : MeasurableSet s) {F : ℝ → ℂ}
    (h : (g : ℝ → ℂ) =ᵐ[volume] s.indicator F) : ‖g‖ ^ 2 = ∫ ξ in s, ‖F ξ‖ ^ 2 := by
  rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.norm_sq_eq_integral, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [h] with ξ hξ
  rw [hξ]
  by_cases hm : ξ ∈ s
  · rw [indicator_of_mem hm, indicator_of_mem hm]
  · rw [indicator_of_notMem hm, indicator_of_notMem hm]; simp

/-- **`‖u − P₊u‖² = ∫_{ξ<0}|𝓕u|²`.** -/
theorem norm_sub_posProj_sq (u : L2C) :
    ‖u - posProj u‖ ^ 2 = ∫ ξ in Iio (0 : ℝ), ‖((𝓕 u : L2C) : ℝ → ℂ) ξ‖ ^ 2 := by
  rw [← Lp.norm_fourier_eq]
  exact norm_sq_of_ae_indicator measurableSet_Iio (fourier_sub_posProj u)

/-- **`‖P₊u‖² = ∫_{ξ≥0}|𝓕u|²`.** -/
theorem norm_posProj_sq (u : L2C) :
    ‖posProj u‖ ^ 2 = ∫ ξ in Ici (0 : ℝ), ‖((𝓕 u : L2C) : ℝ → ℂ) ξ‖ ^ 2 := by
  rw [← Lp.norm_fourier_eq]
  exact norm_sq_of_ae_indicator measurableSet_Ici (fourier_posProj u)

theorem setIntegral_fourier_toLp {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (s : Set ℝ) :
    ∫ ξ in s, ‖((𝓕 (hf2.toLp f) : L2C) : ℝ → ℂ) ξ‖ ^ 2 = ∫ ξ in s, ‖𝓕 f ξ‖ ^ 2 := by
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hf hf2] with ξ h
  rw [h]

/-- On `L¹ ∩ L²`: `‖f − P₊f‖² = ∫_{ξ<0}|𝓕f(ξ)|²` with the Fourier integral. -/
theorem norm_sub_posProj_toLp_sq {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ‖hf2.toLp f - posProj (hf2.toLp f)‖ ^ 2 = ∫ ξ in Iio (0 : ℝ), ‖𝓕 f ξ‖ ^ 2 := by
  rw [norm_sub_posProj_sq, setIntegral_fourier_toLp hf hf2]

/-- On `L¹ ∩ L²`: `‖P₊f‖² = ∫_{ξ≥0}|𝓕f(ξ)|²` with the Fourier integral. -/
theorem norm_posProj_toLp_sq {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ‖posProj (hf2.toLp f)‖ ^ 2 = ∫ ξ in Ici (0 : ℝ), ‖𝓕 f ξ‖ ^ 2 := by
  rw [norm_posProj_sq, setIntegral_fourier_toLp hf hf2]

/-- `‖P₊u‖ ≤ ‖u‖`. -/
theorem norm_posProj_le (u : L2C) : ‖posProj u‖ ≤ ‖u‖ :=
  (specGe 0).norm_starProjection_apply_le u

/-- `‖u − P₊u‖ ≤ ‖u‖`. -/
theorem norm_sub_posProj_le (u : L2C) : ‖u - posProj u‖ ≤ ‖u‖ := by
  have h1 := norm_sub_posProj_sq u
  have h2 := Cvs.Upstream.PlancherelL1L2SpectralDensity.norm_sq_eq_integral (𝓕 u : L2C)
  rw [Lp.norm_fourier_eq] at h2
  have h3 : ∫ ξ in Iio (0 : ℝ), ‖((𝓕 u : L2C) : ℝ → ℂ) ξ‖ ^ 2 ≤ ∫ ξ, ‖((𝓕 u : L2C) : ℝ → ℂ) ξ‖ ^ 2 :=
    setIntegral_le_integral ((memLp_two_iff_integrable_sq_norm (Lp.memLp _).aestronglyMeasurable).1
      (Lp.memLp _)) (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have : ‖u - posProj u‖ ^ 2 ≤ ‖u‖ ^ 2 := by rw [h1, h2]; exact h3
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

end Cvs.Upstream.HardyHalvesFourier

end
