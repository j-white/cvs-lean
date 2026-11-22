import Mathlib
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CarrierUpperHalfPlane
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.HighpassExtensionRung
import Cvs.Prolate.Hardy.SpectrumCosineHighpass
import Cvs.Prolate.Hardy.TraceLimitHighpassOperator
import Cvs.Upstream.FourierLpConjReflect
import Cvs.Upstream.HardyProjectionReal
import Cvs.Upstream.ModulationShiftsSpectrum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `J_c` is a highpass extension operator

Given that bounded holomorphic multipliers preserve `H²` of the upper half-plane, `J_c f = 2 Re[w P₊(1_I f / w)]`
equals `f` on `I` and has no cosine frequencies in `(−c/2, c/2)`: `Cvs.Prolate.Hardy.TraceLimitHighpassOperator.HighpassOp c J_c`.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform
open Complex (I)

namespace Cvs.Prolate.Hardy.HardyExtensionHighpass
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.CentralResolventTrace (L2I)
open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI)
open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C specGe posProj mulOp wR wInvI ext0 ofRealLp reLp hardyJ)
open Cvs.Upstream.FourierLpConjReflect (conjLp)
open Cvs.Prolate.Hardy.CarrierUpperHalfPlane (carrierPhi)
open Cvs.Upstream.ModulationShiftsSpectrum (charE)

/-- **`H²` of the upper half-plane is a module over `H^∞`** (Garnett, *Bounded Analytic Functions*, Ch. II, with
Paley–Wiener, Rudin, *Real and Complex Analysis*, Thm. 19.2): boundary values of a bounded holomorphic `Φ` on
`Im z > 0`, continuous on `Im z ≥ 0`, multiply `{u ∈ L² : 𝓕 u = 0 on (−∞, 0)}` into itself. -/
def HardyModule : Prop :=
  ∀ (Φ : ℂ → ℂ) (M : ℝ), DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im} → ContinuousOn Φ {z : ℂ | 0 ≤ z.im} →
    (∀ z : ℂ, 0 ≤ z.im → ‖Φ z‖ ≤ M) → ∀ u ∈ specGe 0, mulOp (fun x : ℝ => Φ x) u ∈ specGe 0

theorem continuous_carrierPhi_real (b : ℝ) : Continuous fun x : ℝ => carrierPhi b x :=
  (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.continuousOn_carrierPhi b).comp_continuous Complex.continuous_ofReal (fun x => by simp)

theorem memLp_carrierPhi_real {b : ℝ} (hb : 0 ≤ b) : MemLp (fun x : ℝ => carrierPhi b x) ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound (continuous_carrierPhi_real b).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => Cvs.Prolate.Hardy.CarrierUpperHalfPlane.norm_carrierPhi_le hb (by simp))

/-- `w P = e_b · (Φ_b P)`. -/
theorem mulOp_wR_eq {b : ℝ} (hb : 0 ≤ b) (P : L2C) :
    mulOp (wR b) P = mulOp (charE b) (mulOp (fun x : ℝ => carrierPhi b x) P) := by
  refine Lp.ext ?_
  filter_upwards [Cvs.Upstream.HardyProjectionReal.coeFn_mulOp (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wR hb) P, Cvs.Upstream.HardyProjectionReal.coeFn_mulOp (Cvs.Upstream.ModulationShiftsSpectrum.memLp_charE b)
    (mulOp (fun x : ℝ => carrierPhi b x) P), Cvs.Upstream.HardyProjectionReal.coeFn_mulOp (memLp_carrierPhi_real hb) P] with x h1 h2 h3
  rw [h1, h2, h3, Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wR_eq, charE]
  ring

/-- The carrier maps the Hardy space into the functions with spectrum in `[c/4π, ∞)`. -/
theorem mulOp_wR_mem (hH : HardyModule) {c : ℝ} (hc : 0 < c) {P : L2C} (hP : P ∈ specGe 0) :
    mulOp (wR (c / 2)) P ∈ specGe (c / (4 * π)) := by
  have hb : 0 ≤ c / 2 := by positivity
  rw [mulOp_wR_eq hb]
  have h1 := hH (carrierPhi (c / 2)) 1 (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.differentiableOn_carrierPhi _) (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.continuousOn_carrierPhi _)
    (fun z hz => Cvs.Prolate.Hardy.CarrierUpperHalfPlane.norm_carrierPhi_le hb hz) P hP
  have h2 := Cvs.Upstream.ModulationShiftsSpectrum.mulOp_charE_mem (b := c / 2) h1
  rwa [show c / 2 / (2 * π) = c / (4 * π) by field_simp; ring] at h2

/-- **`J_c` is a highpass extension operator.** -/
theorem hardyJ_highpassOp (hH : HardyModule) {c : ℝ} (hc : 0 < c) : Cvs.Prolate.Hardy.TraceLimitHighpassOperator.HighpassOp c (hardyJ c) := by
  intro f
  set b := c / 2 with hbdef
  have hb : 0 ≤ b := by positivity
  set E := ext0 f
  set Fc := ofRealLp E
  set F := mulOp (wInvI b) Fc
  set P := posProj F
  set U := mulOp (wR b) P
  have hJ : hardyJ c f = (2 : ℝ) • reLp U := rfl
  have hE : (E : ℝ → ℝ) =ᵐ[volume] cI.indicator (f : ℝ → ℝ) := MemLp.coeFn_toLp (Cvs.Prolate.Hardy.HardyExtensionOperator.memLp_indicator_L2I f)
  have hFc : (Fc : ℝ → ℂ) =ᵐ[volume] fun x => ((E : ℝ → ℝ) x : ℂ) := ContinuousLinearMap.coeFn_compLpL _ _
  have hF : (F : ℝ → ℂ) =ᵐ[volume] fun x => wInvI b x * ((E : ℝ → ℝ) x : ℂ) := by
    filter_upwards [Cvs.Upstream.HardyProjectionReal.coeFn_mulOp (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wInvI hb) Fc, hFc] with x h1 h2
    rw [h1, h2]
  -- `F` is real
  have hFr : conjLp F = F := by
    refine Lp.ext ?_
    filter_upwards [Cvs.Upstream.FourierLpConjReflect.coeFn_conjLp F, hF] with x h1 h2
    rw [h1, h2, map_mul, Complex.conj_ofReal, Complex.conj_eq_iff_im.2 (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wInvI_im b x)]
  have hP := Cvs.Upstream.HardyProjectionReal.conjLp_posProj hFr
  have hJe : ((hardyJ c f : Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral.L2R) : ℝ → ℝ) =ᵐ[volume] fun t => 2 * ((U : ℝ → ℂ) t).re := by
    rw [hJ]
    filter_upwards [Lp.coeFn_smul (2 : ℝ) (reLp U), ContinuousLinearMap.coeFn_compLpL Complex.reCLM U]
      with t h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul]
    exact congrArg (2 * ·) h2
  refine ⟨Lp.memLp _, ?_, Cvs.Prolate.Hardy.SpectrumCosineHighpass.cosHighpass_two_re hc ?_ hJe⟩
  · -- equal to `f` on `I`
    filter_upwards [ae_restrict_of_ae hJe, ae_restrict_of_ae hE, ae_restrict_of_ae hF,
      ae_restrict_of_ae (Cvs.Upstream.FourierLpConjReflect.coeFn_conjLp P), ae_restrict_of_ae (Lp.coeFn_sub F P),
      ae_restrict_of_ae (Cvs.Upstream.HardyProjectionReal.coeFn_mulOp (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wR hb) P), ae_restrict_mem measurableSet_Icc]
      with t hJt hEt hFt hcP hsub hUt ht
    have hcj : (starRingEnd ℂ) ((P : ℝ → ℂ) t) = (F : ℝ → ℂ) t - (P : ℝ → ℂ) t := by
      rw [← hcP, hP]; exact hsub
    have hre : 2 * ((P : ℝ → ℂ) t).re = ((F : ℝ → ℂ) t).re := by
      have := congrArg Complex.re hcj
      simp only [Complex.conj_re, Complex.sub_re] at this
      linarith
    set r := Real.exp (-b * (Cvs.Prolate.Hardy.HardyExtensionOperator.sS t).im)
    have hr : 0 < r := Real.exp_pos _
    have hw : wR b t = (r : ℂ) := Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wR_on_I ht
    have hwi : wInvI b t = ((r⁻¹ : ℝ) : ℂ) := by
      rw [wInvI, indicator_of_mem ht, hw, Complex.ofReal_inv]
    rw [hJt, hUt, hw, Complex.re_ofReal_mul]
    rw [hFt, hwi, hEt, indicator_of_mem ht, ← Complex.ofReal_mul, Complex.ofReal_re] at hre
    rw [show 2 * (r * ((P : ℝ → ℂ) t).re) = r * (2 * ((P : ℝ → ℂ) t).re) by ring, hre, ← mul_assoc,
      mul_inv_cancel₀ hr.ne', one_mul]
  · exact mulOp_wR_mem hH hc (Submodule.starProjection_apply_mem _ F)

end Cvs.Prolate.Hardy.HardyExtensionHighpass

end
