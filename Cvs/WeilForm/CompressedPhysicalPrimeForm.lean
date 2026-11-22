import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.TailBridgeCOneWindow
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.AngularPrimeAdjointEWindow
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.MangoldtDilationEWindow
import Cvs.Xi.ReciprocalWindowPhysicalL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The compressed physical prime form

The centered logarithm and reciprocal window express the actual prime form
as a bounded symmetric operator on physical Lebesgue `L²`.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped InnerProductSpace

namespace Cvs.WeilForm.CompressedPhysicalPrimeForm
open Cvs.ZeroCounting

open Cvs.Xi.ReciprocalWindowPhysicalL2 (Physical windowOp)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.Xi.MangoldtDilationEWindow (centeredLog)

/-- Centered logarithm restricted to the physical window. -/
def cutLog (a : ℝ) : ℝ → ℝ := (Icc a 1).indicator (centeredLog a)

/-- The centered logarithm has half the logarithmic window width. -/
theorem abs_centeredLog_le {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Icc a 1) :
    |centeredLog a θ| ≤ |Real.log a| / 2 := by
  have ha1 : a ≤ 1 := hθ.1.trans hθ.2
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  have hla : Real.log a ≤ 0 := Real.log_nonpos ha.le ha1
  have hlo : Real.log a ≤ Real.log θ := Real.log_le_log ha hθ.1
  have hhi : Real.log θ ≤ 0 := Real.log_nonpos hθ0.le hθ.2
  rw [abs_of_nonpos hla, abs_le]
  unfold centeredLog
  constructor <;> linarith

theorem abs_cutLog_le {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    |cutLog a θ| ≤ |Real.log a| / 2 := by
  by_cases hθ : θ ∈ Icc a 1
  · rw [cutLog, indicator_of_mem hθ]
    exact abs_centeredLog_le ha hθ
  · rw [cutLog, indicator_of_notMem hθ, abs_zero]
    positivity

theorem measurable_cutLog (a : ℝ) : Measurable (cutLog a) :=
  (Real.measurable_log.sub measurable_const).indicator measurableSet_Icc

/-- Multiplication by the cut centered logarithm preserves physical `L²`. -/
theorem memLp_cutLog_mul {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hG : MemLp G 2 volume) :
    MemLp (fun θ => cutLog a θ * G θ) 2 volume := by
  apply hG.of_le_mul (f := fun θ => cutLog a θ * G θ) (c := |Real.log a| / 2)
    ((measurable_cutLog a).aestronglyMeasurable.mul hG.aestronglyMeasurable)
  exact ae_of_all _ fun θ => by
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_cutLog_le ha θ) (abs_nonneg _)

/-- Multiplication by the actual centered angular logarithm on physical `L²`. -/
def logLinear {a : ℝ} (ha : 0 < a) : Physical →ₗ[ℝ] Physical where
  toFun G := (memLp_cutLog_mul ha (Lp.memLp G)).toLp (fun θ => cutLog a θ * G θ)
  map_add' G H := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_add G H] with θ hθ
    simp only [Pi.add_apply] at hθ ⊢
    rw [hθ, mul_add]
  map_smul' r G := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_smul r G] with θ hθ
    simp only [Pi.smul_apply, smul_eq_mul] at hθ ⊢
    rw [hθ]
    ring

theorem coe_logLinear_ae {a : ℝ} (ha : 0 < a) (G : Physical) :
    (logLinear ha G : ℝ → ℝ) =ᵐ[volume] (fun θ => cutLog a θ * G θ) :=
  (memLp_cutLog_mul ha (Lp.memLp G)).coeFn_toLp

theorem norm_logLinear_le {a : ℝ} (ha : 0 < a) (G : Physical) :
    ‖logLinear ha G‖ ≤ (|Real.log a| / 2) * ‖G‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coe_logLinear_ae ha G] with θ hθ
  rw [hθ, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_cutLog_le ha θ) (abs_nonneg _)

/-- The physical centered-log multiplier as a bounded operator. -/
def logOp {a : ℝ} (ha : 0 < a) : Physical →L[ℝ] Physical :=
  (logLinear ha).mkContinuous (|Real.log a| / 2) (norm_logLinear_le ha)

theorem coe_logOp_ae {a : ℝ} (ha : 0 < a) (G : Physical) :
    (logOp ha G : ℝ → ℝ) =ᵐ[volume] (fun θ => cutLog a θ * G θ) := coe_logLinear_ae ha G

/-- The physical centered-log multiplier is selfadjoint. -/
theorem inner_logOp {a : ℝ} (ha : 0 < a) (G H : Physical) :
    ⟪logOp ha G, H⟫_ℝ = ⟪G, logOp ha H⟫_ℝ := by
  rw [Cvs.L2a.PlaneCorrelationL2.inner_eq_integral, Cvs.L2a.PlaneCorrelationL2.inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [coe_logOp_ae ha G, coe_logOp_ae ha H] with θ hG hH
  rw [hG, hH]
  ring

/-- Cutting centered log before the window leaves every reciprocal sample unchanged. -/
theorem window_cutLog_mul {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) :
    window a (fun u => cutLog a u * G u)
      = window a (fun u => centeredLog a u * G u) := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · simp only [window, indicator_of_mem hθ]
    apply Cvs.WeilForm.TailBridgeCOneWindow.eimage_congr_Icc ha (hθ := hθ.2)
    intro u hu
    rw [cutLog, indicator_of_mem hu]
  · simp only [window, indicator_of_notMem hθ]

theorem cutLog_mul_window (a : ℝ) (G : ℝ → ℝ) :
    (fun θ => cutLog a θ * window a G θ)
      = (fun θ => centeredLog a θ * window a G θ) := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · rw [cutLog, indicator_of_mem hθ]
  · rw [Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hθ, mul_zero, mul_zero]

/-- The compressed prime operator in centered-log and reciprocal-window coordinates. -/
def primeCompression {a : ℝ} (ha : 0 < a) : Physical →L[ℝ] Physical :=
  (logOp ha).comp ((windowOp ha).comp (windowOp ha))
    + ((windowOp ha).comp (windowOp ha)).comp (logOp ha)
    + (2 : ℝ) • (windowOp ha).comp ((logOp ha).comp (windowOp ha))

/-- The compressed prime pairing contains the two logarithmic window intertwiners. -/
theorem inner_primeCompression {a : ℝ} (ha : 0 < a) (G H : Physical) :
    ⟪primeCompression ha G, H⟫_ℝ
      = ⟪logOp ha (windowOp ha G), windowOp ha H⟫_ℝ
        + ⟪windowOp ha (logOp ha G), windowOp ha H⟫_ℝ
        + ⟪logOp ha (windowOp ha H), windowOp ha G⟫_ℝ
        + ⟪windowOp ha (logOp ha H), windowOp ha G⟫_ℝ := by
  unfold primeCompression
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, inner_add_left, real_inner_smul_left]
  have h₁ : ⟪logOp ha (windowOp ha (windowOp ha G)), H⟫_ℝ
      = ⟪windowOp ha (logOp ha H), windowOp ha G⟫_ℝ := by
    rw [inner_logOp, Cvs.Xi.ReciprocalWindowPhysicalL2.inner_windowOp, real_inner_comm]
  have h₂ : ⟪windowOp ha (windowOp ha (logOp ha G)), H⟫_ℝ
      = ⟪windowOp ha (logOp ha G), windowOp ha H⟫_ℝ :=
    Cvs.Xi.ReciprocalWindowPhysicalL2.inner_windowOp ha _ _
  have h₃ : ⟪logOp ha (windowOp ha G), windowOp ha H⟫_ℝ
      = ⟪logOp ha (windowOp ha H), windowOp ha G⟫_ℝ := by
    rw [inner_logOp, real_inner_comm]
  have h₄ : ⟪windowOp ha (logOp ha (windowOp ha G)), H⟫_ℝ
      = ⟪logOp ha (windowOp ha G), windowOp ha H⟫_ℝ :=
    Cvs.Xi.ReciprocalWindowPhysicalL2.inner_windowOp ha _ _
  rw [h₁, h₂, h₄]
  linarith

/-- The actual prime adjoint of a window is represented by the two bounded log operators. -/
theorem coe_prime_intertwiner_ae {a : ℝ} (ha : 0 < a) (G : Physical) :
    ((logOp ha (windowOp ha G) + windowOp ha (logOp ha G) : Physical) : ℝ → ℝ)
      =ᵐ[volume] Cvs.Xi.AngularPrimeAdjointEWindow.primeAdjoint a (window a G) := by
  have hAY := (Cvs.Xi.ReciprocalWindowPhysicalL2.coe_windowOp_ae ha (logOp ha G)).trans
    (Cvs.Xi.ReciprocalWindowPhysicalL2.window_congr_ae ha (coe_logOp_ae ha G))
  have hid : Cvs.Xi.AngularPrimeAdjointEWindow.primeAdjoint a (window a G)
      = fun θ => cutLog a θ * window a G θ
        + window a (fun u => cutLog a u * G u) θ := by
    rw [Cvs.Xi.AngularPrimeAdjointEWindow.primeAdjoint_window_eq_anticommutator ha, ← window_cutLog_mul ha]
    funext θ
    rw [congrFun (cutLog_mul_window a (G : ℝ → ℝ)) θ]
  rw [hid]
  filter_upwards [Lp.coeFn_add (logOp ha (windowOp ha G)) (windowOp ha (logOp ha G)),
    coe_logOp_ae ha (windowOp ha G), Cvs.Xi.ReciprocalWindowPhysicalL2.coe_windowOp_ae ha G, hAY] with θ hsum hY hA hAY
  simp only [Pi.add_apply] at hsum
  rw [hsum, hY, hA, hAY]

/-- The bounded compression represents the actual complete angular prime channel. -/
theorem primeθ_window_eq_inner {a : ℝ} (ha : 0 < a) (G H : Physical) :
    Cvs.L2a.WindowFormTailLimit.primeθ (window a G) (window a H) = ⟪primeCompression ha G, H⟫_ℝ := by
  have hG := Cvs.Xi.ReciprocalWindowPhysicalL2.memLp_window ha (Lp.memLp G)
  have hH := Cvs.Xi.ReciprocalWindowPhysicalL2.memLp_window ha (Lp.memLp H)
  rw [Cvs.Xi.AngularPrimeAdjointEWindow.primeθ_eq_primeWindow_pairing ha hG hH
    (fun θ hθ => Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hθ)
    (fun θ hθ => Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hθ)]
  have hc : (∫ θ, window a G θ * Cvs.Xi.MangoldtDilationEWindow.primeWindow a (window a H) θ)
      = ∫ θ, Cvs.Xi.MangoldtDilationEWindow.primeWindow a (window a H) θ * window a G θ := by
    apply integral_congr_ae
    exact ae_of_all _ fun θ => mul_comm _ _
  rw [hc, Cvs.Xi.AngularPrimeAdjointEWindow.integral_primeWindow_mul ha hH hG, Cvs.Xi.AngularPrimeAdjointEWindow.integral_primeWindow_mul ha hG hH]
  have hI : ⟪primeCompression ha G, H⟫_ℝ
      = ⟪logOp ha (windowOp ha G) + windowOp ha (logOp ha G), windowOp ha H⟫_ℝ
        + ⟪logOp ha (windowOp ha H) + windowOp ha (logOp ha H), windowOp ha G⟫_ℝ := by
    rw [inner_primeCompression, inner_add_left, inner_add_left]
    ring
  rw [hI, Cvs.L2a.PlaneCorrelationL2.inner_eq_integral, Cvs.L2a.PlaneCorrelationL2.inner_eq_integral]
  have hfirst : (∫ θ, window a H θ * Cvs.Xi.AngularPrimeAdjointEWindow.primeAdjoint a (window a G) θ)
      = ∫ θ, (logOp ha (windowOp ha G) + windowOp ha (logOp ha G) : Physical) θ * windowOp ha H θ := by
    apply integral_congr_ae
    filter_upwards [coe_prime_intertwiner_ae ha G, Cvs.Xi.ReciprocalWindowPhysicalL2.coe_windowOp_ae ha H] with θ hD hA
    rw [hD, hA, mul_comm]
  have hsecond : (∫ θ, window a G θ * Cvs.Xi.AngularPrimeAdjointEWindow.primeAdjoint a (window a H) θ)
      = ∫ θ, (logOp ha (windowOp ha H) + windowOp ha (logOp ha H) : Physical) θ * windowOp ha G θ := by
    apply integral_congr_ae
    filter_upwards [coe_prime_intertwiner_ae ha H, Cvs.Xi.ReciprocalWindowPhysicalL2.coe_windowOp_ae ha G] with θ hD hA
    rw [hD, hA, mul_comm]
  rw [hfirst, hsecond]

/-- The double commutator of the reciprocal window with centered log. -/
def doubleLogCommutator {a : ℝ} (ha : 0 < a) : Physical →L[ℝ] Physical :=
  (windowOp ha).comp ((windowOp ha).comp (logOp ha) - (logOp ha).comp (windowOp ha))
    - ((windowOp ha).comp (logOp ha) - (logOp ha).comp (windowOp ha)).comp (windowOp ha)

/-- The actual prime pullback splits into a window logarithm and a double commutator. -/
theorem primeCompression_eq_double {a : ℝ} (ha : 0 < a) :
    primeCompression ha = (4 : ℝ) • (windowOp ha).comp ((logOp ha).comp (windowOp ha))
      + doubleLogCommutator ha := by
  apply ContinuousLinearMap.ext
  intro G
  simp only [primeCompression, doubleLogCommutator, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_sub]
  module

/-- The complete prime quadratic form splits off its output logarithmic diagonal. -/
theorem primeθ_window_self_eq_double {a : ℝ} (ha : 0 < a) (G : Physical) :
    Cvs.L2a.WindowFormTailLimit.primeθ (window a G) (window a G)
      = 4 * ⟪logOp ha (windowOp ha G), windowOp ha G⟫_ℝ
        + ⟪doubleLogCommutator ha G, G⟫_ℝ := by
  rw [primeθ_window_eq_inner ha, primeCompression_eq_double ha]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, real_inner_smul_left]
  rw [Cvs.Xi.ReciprocalWindowPhysicalL2.inner_windowOp]

/-- The actual Weil energy is archimedean and pole energy minus the prime double commutator and log diagonal. -/
theorem weilθ_window_self_eq_double {a : ℝ} (ha : 0 < a) (G : Physical) :
    Cvs.WeilForm.ThetaSpaceParseval.weilθ (window a G) (window a G)
      = 2 * Cvs.WeilForm.ThetaSpaceParseval.poleP (window a G) * Cvs.WeilForm.ThetaSpaceParseval.poleM (window a G)
        + (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t *
            Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale (window a G)) (Cvs.L2a.TailLogScaleTest.logScale (window a G)) t)
        - 4 * ⟪logOp ha (windowOp ha G), windowOp ha G⟫_ℝ
        - ⟪doubleLogCommutator ha G, G⟫_ℝ := by
  have hp := primeθ_window_self_eq_double ha G
  unfold Cvs.L2a.WindowFormTailLimit.primeθ at hp
  unfold Cvs.WeilForm.ThetaSpaceParseval.weilθ
  rw [hp]
  ring

end Cvs.WeilForm.CompressedPhysicalPrimeForm
