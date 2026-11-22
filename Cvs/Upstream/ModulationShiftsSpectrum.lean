import Mathlib
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Upstream.FourierLpConjReflect
import Cvs.Upstream.HardyProjectionReal
import Cvs.Upstream.L2FourierIntegralL1L2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Modulation shifts the `L²` spectrum

`𝓕(e^{ib·} u) = 𝓕 u (· − b/2π)` on `L²(ℝ, ℂ)`, so multiplication by `e^{ibx}` carries `specGe 0` into `specGe (b/2π)`.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform SchwartzMap
open Complex (I)

namespace Cvs.Upstream.ModulationShiftsSpectrum
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C specGe mulOp)

/-- The character `e_b(x) = e^{ibx}`. -/
def charE (b : ℝ) (x : ℝ) : ℂ := Complex.exp (I * b * x)

theorem norm_charE (b x : ℝ) : ‖charE b x‖ = 1 := by
  rw [charE, show I * (b : ℂ) * (x : ℂ) = ((b * x : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem continuous_charE (b : ℝ) : Continuous (charE b) := by unfold charE; fun_prop

theorem memLp_charE (b : ℝ) : MemLp (charE b) ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound (continuous_charE b).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => (norm_charE b x).le)

/-- The translation `g ↦ g(· − β)` on `L²(ℝ, ℂ)`. -/
def transLp (β : ℝ) : L2C →L[ℂ] L2C :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x - β) (measurePreserving_sub_right volume β)).toContinuousLinearMap

theorem coeFn_transLp (β : ℝ) (g : L2C) : (transLp β g : ℝ → ℂ) =ᵐ[volume] fun x => (g : ℝ → ℂ) (x - β) :=
  Lp.coeFn_compMeasurePreserving g _

/-- The classical modulation identity `𝓕(e_b f)(ξ) = 𝓕 f(ξ − b/2π)`. -/
theorem fourier_charE_mul (b : ℝ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => charE b x * f x) ξ = 𝓕 f (ξ - b / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  congr 1; ext v
  simp only [smul_eq_mul, charE, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring

/-- **Modulation in `L²`**: `𝓕(e_b u) = 𝓕 u (· − b/2π)`. -/
theorem fourier_mulOp_charE (b : ℝ) (u : L2C) :
    (𝓕 (mulOp (charE b) u) : L2C) = transLp (b / (2 * π)) (𝓕 u) := by
  have hc1 : Continuous fun u : L2C => (𝓕 (mulOp (charE b) u) : L2C) :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (mulOp (charE b)).continuous
  have hc2 : Continuous fun u : L2C => transLp (b / (2 * π)) (𝓕 u : L2C) :=
    (transLp _).continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  refine congrFun ((Cvs.Upstream.FourierLpConjReflect.denseRange_schwartz).equalizer hc1 hc2 ?_) u
  ext1 f
  simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply, SchwartzMap.toLp_fourier_eq]
  have hi : Integrable fun x => charE b x * f x :=
    f.integrable.bdd_mul (c := 1) (continuous_charE b).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (norm_charE b x).le)
  have h2 : MemLp (fun x => charE b x * f x) 2 (volume : Measure ℝ) :=
    (f.memLp 2 volume).of_le_mul (c := 1) ((continuous_charE b).mul f.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [norm_mul, norm_charE, one_mul])
  have e1 : mulOp (charE b) (f.toLp 2) = h2.toLp _ := by
    refine Lp.ext ((Cvs.Upstream.HardyProjectionReal.coeFn_mulOp (memLp_charE b) _).trans ?_)
    filter_upwards [SchwartzMap.coeFn_toLp f 2 volume, h2.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
  rw [e1]
  refine Lp.ext ?_
  filter_upwards [Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hi h2, coeFn_transLp (b / (2 * π)) ((𝓕 f).toLp 2),
    (measurePreserving_sub_right volume (b / (2 * π))).quasiMeasurePreserving.ae
      (SchwartzMap.coeFn_toLp (𝓕 f) 2 volume)] with ξ h1 h3 h4
  rw [h1, h3, h4, fourier_charE_mul, SchwartzMap.fourier_coe]

/-- Multiplication by `e^{ibx}` carries `specGe 0` into `specGe (b/2π)`. -/
theorem mulOp_charE_mem {b : ℝ} {u : L2C} (hu : u ∈ specGe 0) : mulOp (charE b) u ∈ specGe (b / (2 * π)) := by
  rw [Cvs.Upstream.HardyProjectionReal.mem_specGe_iff] at hu ⊢
  rw [fourier_mulOp_charE]
  filter_upwards [coeFn_transLp (b / (2 * π)) (𝓕 u : L2C),
    (measurePreserving_sub_right volume (b / (2 * π))).quasiMeasurePreserving.ae hu] with ξ h1 h2 hξ
  rw [h1]
  exact h2 (by linarith)

end Cvs.Upstream.ModulationShiftsSpectrum

end
