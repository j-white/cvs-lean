import Mathlib
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.SpectrumCosineHighpass
import Cvs.Upstream.FourierLpConjReflect
import Cvs.Upstream.HardyHalvesFourier
import Cvs.Upstream.HardyProjectionReal

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The reflected wave: `P₊ū = conj(u − P₊u)` and the splitting of `P₊h + conj(h − P₊h)`

Conjugation exchanges the Hardy halves, so for `h = k − m₁ − (m₂ + r₂) − r₁` the field
`P₊h + conj(h − P₊h)` is `h + m₂ + r₂ − conj(m₂ + r₂)` plus `conj E − E`, where
`E = (1 − P₊)k − (1 − P₊)m₁ + P₊m₂ + P₊r₂ − (1 − P₊)r₁`; multiplication by `|w| ≤ 1` and `Re` are contractions.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform

namespace Cvs.Prolate.Hardy.ReflectedWaveSplit
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C specGe posProj mulOp reLp)
open Cvs.Upstream.FourierLpConjReflect (conjLp)
open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R)

/-- **The reflected half**: `P₊ū = conj(u − P₊u)`. -/
theorem posProj_conjLp (u : L2C) : posProj (conjLp u) = conjLp (u - posProj u) := by
  have hA : posProj u ∈ specGe 0 := Submodule.starProjection_apply_mem _ u
  have hQ : u - posProj u ∈ (specGe 0)ᗮ := Submodule.sub_starProjection_mem_orthogonal u
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [Cvs.Upstream.HardyProjectionReal.mem_specGe_iff]
    filter_upwards [Cvs.Upstream.HardyProjectionReal.fourier_conjLp_ae (u - posProj u),
      Cvs.Upstream.HardyProjectionReal.vanish_neg (Cvs.Upstream.HardyProjectionReal.fourier_vanish_of_mem_orthogonal hQ)] with ξ h1 h2 hξ
    rw [h1, h2 (by linarith), map_zero]
  · rw [← map_sub conjLp, show u - (u - posProj u) = posProj u by abel]
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [← Lp.inner_fourier_eq]
    refine Cvs.Prolate.Hardy.SpectrumCosineHighpass.inner_eq_zero_of_ae ?_
    filter_upwards [Cvs.Upstream.HardyProjectionReal.mem_specGe_iff.1 hw, Cvs.Upstream.HardyProjectionReal.fourier_conjLp_ae (posProj u),
      Cvs.Upstream.HardyProjectionReal.vanish_neg (Cvs.Upstream.HardyProjectionReal.mem_specGe_iff.1 hA), Cvs.Prolate.Hardy.SpectrumCosineHighpass.ae_ne 0] with ξ h1 h2 h3 h0
    rcases lt_or_gt_of_ne h0 with h | h
    · exact Or.inl (h1 h)
    · right; rw [h2, h3 (by linarith), map_zero]

theorem norm_conjLp (u : L2C) : ‖conjLp u‖ = ‖u‖ := by
  refine le_antisymm (Lp.norm_le_norm_of_ae_le ?_) ?_
  · filter_upwards [Cvs.Upstream.FourierLpConjReflect.coeFn_conjLp u] with x h
    rw [h, Complex.norm_conj]
  · refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [Cvs.Upstream.FourierLpConjReflect.coeFn_conjLp u] with x h
    rw [h, Complex.norm_conj]

theorem coeFn_reLp (u : L2C) : (reLp u : ℝ → ℝ) =ᵐ[volume] fun x => ((u : ℝ → ℂ) x).re :=
  ContinuousLinearMap.coeFn_compLpL _ u

theorem norm_reLp_le (u : L2C) : ‖reLp u‖ ≤ ‖u‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [coeFn_reLp u] with x h
  rw [h, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

theorem norm_mulOp_le {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ)) (hm1 : ∀ x, ‖m x‖ ≤ 1) (u : L2C) :
    ‖mulOp m u‖ ≤ ‖u‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Cvs.Upstream.HardyProjectionReal.coeFn_mulOp hm u] with x h
  rw [h, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm1 x)

/-- **The splitting** of `P₊h + conj(h − P₊h)` for `h = k − m₁ − (m₂ + r₂) − r₁`. -/
theorem split (h k m₁ m₂ r₁ r₂ : L2C) (hh : h = k - m₁ - (m₂ + r₂) - r₁) :
    posProj h + conjLp (h - posProj h) =
      (h + (m₂ + r₂) - conjLp (m₂ + r₂)) +
        (conjLp ((k - posProj k) - (m₁ - posProj m₁) + posProj m₂ + posProj r₂ - (r₁ - posProj r₁)) -
          ((k - posProj k) - (m₁ - posProj m₁) + posProj m₂ + posProj r₂ - (r₁ - posProj r₁))) := by
  have hD : h - posProj h = -(m₂ + r₂) +
      ((k - posProj k) - (m₁ - posProj m₁) + posProj m₂ + posProj r₂ - (r₁ - posProj r₁)) := by
    rw [hh, map_sub, map_sub, map_sub, map_add]; abel
  have e1 : posProj h + conjLp (h - posProj h) = h - (h - posProj h) + conjLp (h - posProj h) := by abel
  rw [e1, hD, map_add, map_neg]
  abel

/-- The error field `E` is bounded by its five pieces. -/
theorem norm_err_le (k m₁ m₂ r₁ r₂ : L2C) :
    ‖(k - posProj k) - (m₁ - posProj m₁) + posProj m₂ + posProj r₂ - (r₁ - posProj r₁)‖ ≤
      ‖k - posProj k‖ + ‖m₁ - posProj m₁‖ + ‖posProj m₂‖ + ‖r₂‖ + ‖r₁‖ := by
  have h1 := Cvs.Upstream.HardyHalvesFourier.norm_posProj_le r₂
  have h2 := Cvs.Upstream.HardyHalvesFourier.norm_sub_posProj_le r₁
  calc _ ≤ ‖(k - posProj k) - (m₁ - posProj m₁) + posProj m₂ + posProj r₂‖ + ‖r₁ - posProj r₁‖ := norm_sub_le _ _
    _ ≤ ‖(k - posProj k) - (m₁ - posProj m₁) + posProj m₂‖ + ‖posProj r₂‖ + ‖r₁ - posProj r₁‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖(k - posProj k) - (m₁ - posProj m₁)‖ + ‖posProj m₂‖ + ‖posProj r₂‖ + ‖r₁ - posProj r₁‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖k - posProj k‖ + ‖m₁ - posProj m₁‖ + ‖posProj m₂‖ + ‖posProj r₂‖ + ‖r₁ - posProj r₁‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith

/-- `‖Re(w(conj E − E))‖ ≤ 2‖E‖` for `|w| ≤ 1`. -/
theorem norm_reflect_le {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ)) (hm1 : ∀ x, ‖m x‖ ≤ 1) (E : L2C) :
    ‖reLp (mulOp m (conjLp E - E))‖ ≤ 2 * ‖E‖ := by
  refine (norm_reLp_le _).trans ((norm_mulOp_le hm hm1 _).trans ?_)
  refine (norm_sub_le _ _).trans ?_
  rw [norm_conjLp]; linarith

end Cvs.Prolate.Hardy.ReflectedWaveSplit

end
