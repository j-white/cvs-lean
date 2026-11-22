import Mathlib
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Upstream.CauchySchwarzLine
import Cvs.Upstream.HighpassExtensionScalar

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A highpass extension of `h|_I` bounds every central resolvent objective

If `v ∈ L²(ℝ)` equals `h` on `I` and its cosine transform vanishes on `(−c/2, c/2)`, then for every `f ∈ L²(I)`
`2∫_I hf − ∫_I f² + √(c/2π)∫_I∫_I f(s) cos(cst) f(t) ≤ 2∫_ℝ v²`: the variational form of
`(I − A)⁻¹ ≤ 2(I − A²)⁻¹ ≤ 2J*J` for `A = QFQ`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.Hardy.HighpassExtensionRung

open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI synth)

/-- The central operator `(Af)(s) = √(c/2π) ∫_I cos(cst) f(t) dt`. -/
def cenA (c : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := √(c / (2 * π)) * ∫ t in cI, cos (c * s * t) * f t

/-- `v` has no cosine frequencies in `(−c/2, c/2)`: it is orthogonal to every synthesis `S_c g`. -/
def CosHighpass (c : ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Continuous g → ∫ t, v t * synth c g t = 0

/-- `v ∈ L²(ℝ)` is a highpass extension of `h|_I`. -/
def IsHighpassExt (c : ℝ) (h v : ℝ → ℝ) : Prop :=
  MemLp v 2 (volume : Measure ℝ) ∧ (∀ᵐ t ∂(volume.restrict cI), v t = h t) ∧ CosHighpass c v

theorem continuous_cenA (c : ℝ) {f : ℝ → ℝ} (hf : IntegrableOn f cI) : Continuous (cenA c f) := by
  refine continuous_const.mul (continuous_of_dominated (bound := fun t => ‖f t‖) (fun s => ?_)
    (fun s => Filter.Eventually.of_forall fun t => ?_) hf.norm (Filter.Eventually.of_forall fun t => ?_))
  · exact (Real.continuous_cos.comp (by fun_prop : Continuous fun t => c * s * t)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
  · exact (Real.continuous_cos.comp (by fun_prop : Continuous fun s => c * s * t)).mul continuous_const

theorem memLp_restrict_of_continuous {g : ℝ → ℝ} (hg : Continuous g) : MemLp g 2 (volume.restrict cI) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn (s := cI)
  refine MemLp.of_bound hg.aestronglyMeasurable M ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hM s hs

/-- **The central resolvent objective is at most twice the energy of any highpass extension.** -/
theorem objective_le {c : ℝ} (hc : 0 < c) {h v f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict cI))
    (hv : IsHighpassExt c h v) :
    2 * (∫ s in cI, h s * f s) - (∫ s in cI, f s ^ 2) +
        √(c / (2 * π)) * (∫ s in cI, ∫ t in cI, f s * cos (c * s * t) * f t) ≤ 2 * ∫ t, v t ^ 2 := by
  obtain ⟨hv2, hvI, hH⟩ := hv
  have hfi : IntegrableOn f cI := hf.integrable one_le_two
  set A := cenA c f with hAdef
  have hA : Continuous A := continuous_cenA c hfi
  set k := √(c / (2 * π)) with hk
  have hk2 : k ^ 2 = c / (2 * π) := Real.sq_sqrt (by positivity)
  set g : ℝ → ℝ := fun s => k * A s with hgdef
  have hg : Continuous g := continuous_const.mul hA
  set x := cI.indicator f with hxdef
  have hx : MemLp x 2 (volume : Measure ℝ) := (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 hf
  set w := synth c g with hwdef
  have hw : MemLp w 2 (volume : Measure ℝ) := Cvs.Prolate.Hardy.CosineSynthesisPlancherel.memLp_synth hc hg
  have hAL : MemLp A 2 (volume.restrict cI) := memLp_restrict_of_continuous hA
  set F2 := ∫ s in cI, f s ^ 2
  set a2 := ∫ s in cI, A s ^ 2
  -- the pieces
  have hxx : ∫ t, x t ^ 2 = F2 := by
    rw [show F2 = ∫ s, cI.indicator (fun s => f s ^ 2) s from (integral_indicator measurableSet_Icc).symm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    by_cases ht : t ∈ cI
    · rw [hxdef, indicator_of_mem ht, indicator_of_mem ht]
    · rw [hxdef, indicator_of_notMem ht, indicator_of_notMem ht]; simp
  have hvx : ∫ t, v t * x t = ∫ s in cI, h s * f s := by
    have e : (fun t => v t * x t) = cI.indicator fun t => v t * f t := by
      ext t
      by_cases ht : t ∈ cI
      · rw [hxdef, indicator_of_mem ht, indicator_of_mem ht]
      · rw [hxdef, indicator_of_notMem ht, indicator_of_notMem ht, mul_zero]
    rw [e, integral_indicator measurableSet_Icc]
    refine integral_congr_ae ?_
    filter_upwards [hvI] with t ht
    rw [ht]
  have hvw : ∫ t, v t * w t = 0 := hH g hg
  have hxw : ∫ t, x t * w t = a2 := by
    have e : (fun t => x t * w t) = cI.indicator fun t => f t * w t := by
      ext t
      by_cases ht : t ∈ cI
      · rw [hxdef, indicator_of_mem ht, indicator_of_mem ht]
      · rw [hxdef, indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
    rw [e, integral_indicator measurableSet_Icc, hwdef, Cvs.Prolate.Hardy.CosineSynthesisPlancherel.integral_mul_synth c hfi hg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [hgdef, hAdef, cenA]
    ring
  have hww : ∫ t, w t ^ 2 ≤ a2 := by
    have h1 := Cvs.Prolate.Hardy.CosineSynthesisPlancherel.integral_synth_sq_le hc hg
    have e : ∫ s in cI, g s ^ 2 = c / (2 * π) * a2 := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [hgdef]; rw [mul_pow, hk2]
    rw [e] at h1
    have : 2 * π / c * (c / (2 * π) * a2) = a2 := by field_simp
    linarith
  -- the distance `D = ‖x − w‖²`
  have hD : ∫ t, (x t - w t) ^ 2 = F2 - 2 * a2 + ∫ t, w t ^ 2 := by
    have e : (fun t => (x t - w t) ^ 2) = fun t => x t ^ 2 - 2 * (x t * w t) + w t ^ 2 := by ext t; ring
    rw [e, integral_add, integral_sub, integral_const_mul, hxx, hxw]
    · exact hx.integrable_sq
    · exact (hx.integrable_mul hw).const_mul 2
    · exact hx.integrable_sq.sub ((hx.integrable_mul hw).const_mul 2)
    · exact hw.integrable_sq
  have hD0 : 0 ≤ ∫ t, (x t - w t) ^ 2 := integral_nonneg fun t => sq_nonneg _
  -- Cauchy–Schwarz
  have hp : ∫ s in cI, h s * f s ≤ √(∫ t, v t ^ 2) * √(∫ t, (x t - w t) ^ 2) := by
    have hsplit : ∫ t, v t * x t = ∫ t, v t * (x t - w t) := by
      have e : (fun t => v t * (x t - w t)) = fun t => v t * x t - v t * w t := by ext t; ring
      have h1 : Integrable fun t => v t * x t := hv2.integrable_mul hx
      have h2 : Integrable fun t => v t * w t := hv2.integrable_mul hw
      rw [e, integral_sub h1 h2, hvw, sub_zero]
    rw [← hvx, hsplit]
    exact (le_abs_self _).trans (Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hv2 (hx.sub hw))
  -- the central form
  have hcen : k * (∫ s in cI, ∫ t in cI, f s * cos (c * s * t) * f t) = ∫ s in cI, f s * A s := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [hAdef, cenA, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  have hq : 2 * (∫ s in cI, f s * A s) ≤ F2 + a2 := by
    have h0 : 0 ≤ ∫ s in cI, (f s - A s) ^ 2 := integral_nonneg fun s => sq_nonneg _
    have e : (fun s => (f s - A s) ^ 2) = fun s => f s ^ 2 - 2 * (f s * A s) + A s ^ 2 := by ext s; ring
    rw [e, integral_add, integral_sub, integral_const_mul] at h0
    · linarith
    · exact hf.integrable_sq
    · exact (hf.integrable_mul hAL).const_mul 2
    · exact hf.integrable_sq.sub ((hf.integrable_mul hAL).const_mul 2)
    · exact hAL.integrable_sq
  rw [hcen]
  exact Cvs.Upstream.HighpassExtensionScalar.scalar_bound (integral_nonneg fun t => sq_nonneg _) hD0 hp (by rw [hD]; linarith) hq

end Cvs.Prolate.Hardy.HighpassExtensionRung

end
