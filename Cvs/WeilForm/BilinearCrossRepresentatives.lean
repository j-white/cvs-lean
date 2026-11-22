import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `QWbil` is `crossW` of representatives, and `crossW` is translation invariant

`QWbil φ ψ = crossW (rep φ) (rep ψ)`; `crossW` respects a.e. equality and is unchanged when both
arguments are translated by the same amount.
-/

namespace Cvs.WeilForm.BilinearCrossRepresentatives

open Real Set MeasureTheory
open Cvs.WeilForm.SymmetricBilinearForm (crossW QWbil)

/-- **`QWbil` is the cross term of representatives.** -/
theorem QWbil_apply {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (φ ψ : Cvs.WeilForm.FormDomain.formDomain hL) :
    QWbil hL P R φ ψ = crossW P R (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (Cvs.WeilForm.WindowRepresentative.rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  have hexp := Cvs.WeilForm.SymmetricBilinearForm.weilQW_expand hL P R φ ψ 1
  rw [one_smul, one_pow, one_mul] at hexp
  have hs := Cvs.WeilForm.SymmetricBilinearForm.QWbil_self hL P R (φ + ψ)
  rw [map_add (Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R) φ ψ, LinearMap.add_apply] at hs
  simp only [map_add] at hs
  rw [Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self,
    (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm hL P R).eq ψ φ] at hs
  linarith

theorem crossConv_congr {f f' g g' : ℝ → ℝ} (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') (v : ℝ) :
    Cvs.WeilForm.TruncatedFormPolarised.crossConv f g v = Cvs.WeilForm.TruncatedFormPolarised.crossConv f' g' v := by
  unfold Cvs.WeilForm.TruncatedFormPolarised.crossConv
  refine integral_congr_ae ?_
  have hg' : (fun x => g (x + v)) =ᵐ[volume] fun x => g' (x + v) :=
    (measurePreserving_add_right volume v).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hf, hg'] with x h1 h2
  rw [h1, h2]

theorem polar_congr {f f' g g' : ℝ → ℝ} (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    Cvs.WeilForm.TruncatedFormPolarised.polar f g = Cvs.WeilForm.TruncatedFormPolarised.polar f' g' := by
  funext v
  unfold Cvs.WeilForm.TruncatedFormPolarised.polar
  rw [crossConv_congr hf hg, crossConv_congr hg hf]

/-- **`crossW` respects a.e. equality.** -/
theorem crossW_congr (P R : ℕ) {f f' g g' : ℝ → ℝ} (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    crossW P R f g = crossW P R f' g' := by
  unfold crossW Cvs.WeilForm.TruncatedFormPolarised.poleF Cvs.WeilForm.TruncatedFormPolarised.poleG Cvs.L2a.FullTailPolarisation.archFullBil
  have e1 : (fun x => f x * Real.exp (x / 2)) =ᵐ[volume] fun x => f' x * Real.exp (x / 2) := by
    filter_upwards [hf] with x hx; rw [hx]
  have e2 : (fun x => g x * Real.exp (-(x / 2))) =ᵐ[volume] fun x => g' x * Real.exp (-(x / 2)) := by
    filter_upwards [hg] with x hx; rw [hx]
  have e3 : (fun x => g x * Real.exp (x / 2)) =ᵐ[volume] fun x => g' x * Real.exp (x / 2) := by
    filter_upwards [hg] with x hx; rw [hx]
  have e4 : (fun x => f x * Real.exp (-(x / 2))) =ᵐ[volume] fun x => f' x * Real.exp (-(x / 2)) := by
    filter_upwards [hf] with x hx; rw [hx]
  have e5 : (fun x => f x * g x) =ᵐ[volume] fun x => f' x * g' x := by
    filter_upwards [hf, hg] with x hx hy; rw [hx, hy]
  rw [polar_congr hf hg, integral_congr_ae e1, integral_congr_ae e2, integral_congr_ae e3,
    integral_congr_ae e4, integral_congr_ae e5]

theorem crossConv_translate (f g : ℝ → ℝ) (d v : ℝ) :
    Cvs.WeilForm.TruncatedFormPolarised.crossConv (fun s => f (s - d)) (fun s => g (s - d)) v = Cvs.WeilForm.TruncatedFormPolarised.crossConv f g v := by
  unfold Cvs.WeilForm.TruncatedFormPolarised.crossConv
  rw [← integral_sub_right_eq_self (μ := volume) (fun x => f x * g (x + v)) d]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show f (x - d) * g (x + v - d) = f (x - d) * g (x - d + v)
  rw [show x + v - d = x - d + v by ring]

theorem polar_translate (f g : ℝ → ℝ) (d : ℝ) :
    Cvs.WeilForm.TruncatedFormPolarised.polar (fun s => f (s - d)) (fun s => g (s - d)) = Cvs.WeilForm.TruncatedFormPolarised.polar f g := by
  funext v; unfold Cvs.WeilForm.TruncatedFormPolarised.polar; rw [crossConv_translate, crossConv_translate]

/-- **`crossW` is translation invariant.** -/
theorem crossW_translate (P R : ℕ) (f g : ℝ → ℝ) (d : ℝ) :
    crossW P R (fun s => f (s - d)) (fun s => g (s - d)) = crossW P R f g := by
  unfold crossW Cvs.WeilForm.TruncatedFormPolarised.poleF Cvs.WeilForm.TruncatedFormPolarised.poleG Cvs.L2a.FullTailPolarisation.archFullBil
  rw [polar_translate]
  have hF : ∀ h : ℝ → ℝ, ∫ x, h (x - d) * Real.exp (x / 2) = Real.exp (d / 2) * ∫ x, h x * Real.exp (x / 2) := by
    intro h
    rw [← integral_const_mul, ← integral_sub_right_eq_self (μ := volume)
      (fun x => Real.exp (d / 2) * (h x * Real.exp (x / 2))) d]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show h (x - d) * Real.exp (x / 2) = Real.exp (d / 2) * (h (x - d) * Real.exp ((x - d) / 2))
    rw [show x / 2 = d / 2 + (x - d) / 2 by ring, Real.exp_add]; ring
  have hG : ∀ h : ℝ → ℝ, ∫ x, h (x - d) * Real.exp (-(x / 2)) = Real.exp (-(d / 2)) * ∫ x, h x * Real.exp (-(x / 2)) := by
    intro h
    rw [← integral_const_mul, ← integral_sub_right_eq_self (μ := volume)
      (fun x => Real.exp (-(d / 2)) * (h x * Real.exp (-(x / 2)))) d]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show h (x - d) * Real.exp (-(x / 2)) = Real.exp (-(d / 2)) * (h (x - d) * Real.exp (-((x - d) / 2)))
    rw [show -(x / 2) = -(d / 2) + -((x - d) / 2) by ring, Real.exp_add]; ring
  have hfg : ∫ x, f (x - d) * g (x - d) = ∫ x, f x * g x :=
    integral_sub_right_eq_self (μ := volume) (fun x => f x * g x) d
  rw [hF f, hG g, hF g, hG f, hfg]
  have : Real.exp (d / 2) * Real.exp (-(d / 2)) = 1 := by rw [← Real.exp_add]; simp
  linear_combination ((∫ x, f x * Real.exp (x / 2)) * (∫ x, g x * Real.exp (-(x / 2)))
    + (∫ x, g x * Real.exp (x / 2)) * (∫ x, f x * Real.exp (-(x / 2)))) * this

end Cvs.WeilForm.BilinearCrossRepresentatives
