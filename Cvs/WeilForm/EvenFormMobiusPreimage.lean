import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.CompressedPhysicalPrimeForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.MobiusInversePhysicalL2
import Cvs.Xi.PhysicalReciprocalReflection
import Cvs.Xi.ReciprocalWindowPhysicalL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The full even Weil form at its constructed Möbius preimage

The actual even projection has a finite Möbius preimage, and its centered-log
diagonal vanishes, leaving the arithmetic double commutator explicitly.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped InnerProductSpace

namespace Cvs.WeilForm.EvenFormMobiusPreimage
open Cvs.ZeroCounting

open Cvs.Xi.ReciprocalWindowPhysicalL2 (Physical windowOp)
open Cvs.WeilForm.CompressedPhysicalPrimeForm (logOp doubleLogCommutator)

/-- The concrete physical Möbius preimage of the reciprocal-even projection. -/
def evenPreimage {a : ℝ} (ha : 0 < a) : Physical →L[ℝ] Physical :=
  (Cvs.Xi.MobiusInversePhysicalL2.profileOp ha).comp (Cvs.Xi.PhysicalReciprocalReflection.evenOp ha)

/-- The actual reciprocal window reconstructs its even projection through Möbius inversion. -/
theorem windowOp_evenPreimage {a : ℝ} (ha : 0 < a) (F : Physical) :
    windowOp ha (evenPreimage ha F) = Cvs.Xi.PhysicalReciprocalReflection.evenOp ha F :=
  Cvs.Xi.MobiusInversePhysicalL2.windowOp_profileOp ha _ (Cvs.Xi.PhysicalReciprocalReflection.evenOp_mem_intervalSpace ha F)

/-- The reconstructed physical class has the exact reciprocal-even representative. -/
theorem window_evenPreimage_ae {a : ℝ} (ha : 0 < a) (F : Physical) :
    Cvs.Xi.EImageWindowPoisson.window a (evenPreimage ha F) =ᵐ[volume] Cvs.Xi.PhysicalReciprocalReflection.evenPhysical a F := by
  calc
    _ =ᵐ[volume] (windowOp ha (evenPreimage ha F) : ℝ → ℝ) :=
      (Cvs.Xi.ReciprocalWindowPhysicalL2.coe_windowOp_ae ha _).symm
    _ =ᵐ[volume] (Cvs.Xi.PhysicalReciprocalReflection.evenOp ha F : ℝ → ℝ) := by rw [windowOp_evenPreimage]
    _ =ᵐ[volume] _ := Cvs.Xi.PhysicalReciprocalReflection.coe_evenOp_ae ha F

/-- The logarithmic diagonal vanishes at the constructed even output. -/
theorem inner_logOp_window_evenPreimage {a : ℝ} (ha : 0 < a) (F : Physical) :
    ⟪logOp ha (windowOp ha (evenPreimage ha F)), windowOp ha (evenPreimage ha F)⟫_ℝ = 0 := by
  rw [windowOp_evenPreimage]
  exact Cvs.Xi.PhysicalReciprocalReflection.inner_logOp_evenOp ha F

/-- The Weil self-pairing respects almost-everywhere equality in both slots. -/
theorem weilθ_self_congr_ae {F G : ℝ → ℝ} (hFG : F =ᵐ[volume] G) :
    Cvs.WeilForm.ThetaSpaceParseval.weilθ F F = Cvs.WeilForm.ThetaSpaceParseval.weilθ G G := by
  calc
    _ = Cvs.WeilForm.ThetaSpaceParseval.weilθ G F := Cvs.L2a.WindowFormTailLimit.weilθ_congr_left hFG F
    _ = Cvs.WeilForm.ThetaSpaceParseval.weilθ F G := Cvs.WeilForm.ThetaSpaceParseval.weilθ_comm G F
    _ = _ := Cvs.L2a.WindowFormTailLimit.weilθ_congr_left hFG G

private theorem crossSpec_self_congr_ae {F G : ℝ → ℝ} (hFG : F =ᵐ[volume] G) :
    Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale F) (Cvs.L2a.TailLogScaleTest.logScale F)
      = Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale G) (Cvs.L2a.TailLogScaleTest.logScale G) := by
  funext t
  rw [Cvs.L2a.WindowFormTailLimit.crossSpec_congr_left (Cvs.L2a.WindowFormTailLimit.logScale_ae hFG), Cvs.WeilForm.ThetaSpaceParseval.crossSpec_comm,
    Cvs.L2a.WindowFormTailLimit.crossSpec_congr_left (Cvs.L2a.WindowFormTailLimit.logScale_ae hFG)]

/-- The full actual even Weil energy consists of arch and pole terms minus a concrete arithmetic double commutator. -/
theorem weilθ_evenPhysical_self_eq_double {a : ℝ} (ha : 0 < a) (F : Physical) :
    Cvs.WeilForm.ThetaSpaceParseval.weilθ (Cvs.Xi.PhysicalReciprocalReflection.evenPhysical a F) (Cvs.Xi.PhysicalReciprocalReflection.evenPhysical a F)
      = 2 * Cvs.WeilForm.ThetaSpaceParseval.poleP (Cvs.Xi.PhysicalReciprocalReflection.evenPhysical a F) * Cvs.WeilForm.ThetaSpaceParseval.poleM (Cvs.Xi.PhysicalReciprocalReflection.evenPhysical a F)
        + (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec
            (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.PhysicalReciprocalReflection.evenPhysical a F))
            (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.PhysicalReciprocalReflection.evenPhysical a F)) t)
        - ⟪doubleLogCommutator ha (evenPreimage ha F), evenPreimage ha F⟫_ℝ := by
  have h := Cvs.WeilForm.CompressedPhysicalPrimeForm.weilθ_window_self_eq_double ha (evenPreimage ha F)
  have hE := window_evenPreimage_ae ha F
  rw [weilθ_self_congr_ae hE, Cvs.L2a.WindowFormTailLimit.poleP_congr hE, Cvs.L2a.WindowFormTailLimit.poleM_congr hE,
    crossSpec_self_congr_ae hE, inner_logOp_window_evenPreimage ha F, mul_zero, sub_zero] at h
  exact h

/-- The actual reciprocal-even representative depends only on its physical class. -/
theorem evenPhysical_congr_ae {a : ℝ} (ha : 0 < a) {F G : ℝ → ℝ} (hFG : F =ᵐ[volume] G) :
    Cvs.Xi.PhysicalReciprocalReflection.evenPhysical a F =ᵐ[volume] Cvs.Xi.PhysicalReciprocalReflection.evenPhysical a G := by
  have hJ := Cvs.Xi.PhysicalReciprocalReflection.reciprocal_congr_ae ha hFG
  filter_upwards [hFG, hJ] with θ hFG hJ
  simp only [Cvs.Xi.PhysicalReciprocalReflection.evenPhysical, Cvs.Xi.PhysicalReciprocalReflection.cut, indicator_apply]
  split_ifs <;> simp only [hFG, hJ]

/-- The actual Connes even window's concrete Möbius preimage. -/
def connesPreimage {x : ℝ} (hx : 0 < x) : Physical :=
  evenPreimage (one_div_pos.mpr hx)
    ((Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularWindow hx).toLp
      (Cvs.Xi.EImageWindowPoisson.window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1)))

/-- The full even Connes energy has the same concrete double-commutator structure. -/
theorem weilθ_connesAngularEven_self_eq_double {x : ℝ} (hx : 0 < x) :
    Cvs.WeilForm.ThetaSpaceParseval.weilθ (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)
      = 2 * Cvs.WeilForm.ThetaSpaceParseval.poleP (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) * Cvs.WeilForm.ThetaSpaceParseval.poleM (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)
        + (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec
            (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x))
            (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t)
        - ⟪doubleLogCommutator (one_div_pos.mpr hx) (connesPreimage hx), connesPreimage hx⟫_ℝ := by
  have h := weilθ_evenPhysical_self_eq_double (one_div_pos.mpr hx)
    ((Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularWindow hx).toLp
      (Cvs.Xi.EImageWindowPoisson.window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1)))
  have hE := evenPhysical_congr_ae (one_div_pos.mpr hx)
    (Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularWindow hx).coeFn_toLp
  change Cvs.Xi.PhysicalReciprocalReflection.evenPhysical (1 / x) _ =ᵐ[volume] Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x at hE
  rw [weilθ_self_congr_ae hE, Cvs.L2a.WindowFormTailLimit.poleP_congr hE, Cvs.L2a.WindowFormTailLimit.poleM_congr hE,
    crossSpec_self_congr_ae hE] at h
  exact h

end Cvs.WeilForm.EvenFormMobiusPreimage
