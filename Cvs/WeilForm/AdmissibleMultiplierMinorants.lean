import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.WindowFormTailLimit
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.BandFreedomCosine
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Admissible extensions give multiplier minorants, scalar and bilinear

`Ψ ↦ M_Ψ = ∫ Ψ ρ(·,·) dμ` is linear into bilinear forms, and `ρ(φ,φ) ≥ 0`, `M_h(φ,φ) = 0`, `Ψ ≤ Φ + h` give
`M_Ψ(φ,φ) ≤ M_Φ(φ,φ)`. On the form domain `bandFree L` gives the zero form, so `Q = ∫ Φ ρ` gives `Q = M_{Φ+h}`,
`M_Ψ ≤ Q` and `b‖φ‖² ≤ Q(φ)` from `b ≤ Φ + h`; at scale `x`, `M_Ψ` is an operator floor iff `M_Ψ ≥ 0` on `R_Fᗮ`,
and extensions with `Φ + h ≥ −ε` at arbitrarily large `x` give RH.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped InnerProductSpace
open Cvs.L2a.FullTailPolarisation (crossSpec)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)
open Cvs.WeilForm.WindowRepresentative (rep)

namespace Cvs.WeilForm.AdmissibleMultiplierMinorants

/-! ### The scalar minorant -/

section Scalar

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

end Scalar

/-! ### The bilinear minorant -/

section Bilinear

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The admissible multipliers** of a bilinear density `ρ`: those integrable against every `ρ(φ, ψ)`. -/
def admissible (ρ : V →ₗ[ℝ] V →ₗ[ℝ] X → ℝ) (μ : Measure X) : Submodule ℝ (X → ℝ) where
  carrier := {Ψ | ∀ φ ψ, Integrable (fun t => Ψ t * ρ φ ψ t) μ}
  zero_mem' := fun φ ψ => by simp
  add_mem' := fun {a b} ha hb φ ψ => ((ha φ ψ).add (hb φ ψ)).congr
    (Eventually.of_forall fun t => by simp only [Pi.add_apply]; ring)
  smul_mem' := fun c Ψ hΨ φ ψ => ((hΨ φ ψ).const_mul c).congr
    (Eventually.of_forall fun t => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-- Membership in `admissible ρ μ`. -/
theorem mem_admissible {ρ : V →ₗ[ℝ] V →ₗ[ℝ] X → ℝ} {Ψ : X → ℝ} :
    Ψ ∈ admissible ρ μ ↔ ∀ φ ψ, Integrable (fun t => Ψ t * ρ φ ψ t) μ :=
  Iff.rfl

end Bilinear

/-! ### The form domain -/

section Window

/-- `ρ_{rep(φ₁+φ₂), k} = ρ_{rep φ₁, k} + ρ_{rep φ₂, k}`. -/
theorem crossSpec_rep_add {L : ℝ} (φ₁ φ₂ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (k : ℝ → ℝ) :
    crossSpec (rep (φ₁ + φ₂)) k = crossSpec (rep φ₁) k + crossSpec (rep φ₂) k := by
  rw [Cvs.L2a.WindowFormTailLimit.crossSpec_congr_left (Cvs.WeilForm.LevyDomainSpectral.rep_add_ae φ₁ φ₂)]
  funext t
  exact Cvs.WeilForm.ThetaSpaceParseval.crossSpec_add_left (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ₁) (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ₂) k t

/-- `ρ_{rep(cφ), k} = c ρ_{rep φ, k}`. -/
theorem crossSpec_rep_smul {L : ℝ} (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (k : ℝ → ℝ) :
    crossSpec (rep (c • φ)) k = c • crossSpec (rep φ) k := by
  rw [Cvs.L2a.WindowFormTailLimit.crossSpec_congr_left (Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae c φ)]
  funext t
  exact Cvs.L2a.WindowFormTailLimit.crossSpec_smul_left (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ) k c t

/-- **The window's cross density** `ρ(φ, ψ) = ρ_{rep φ, rep ψ}`, bilinear on the window. -/
def windowSpec (L : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window L →ₗ[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window L →ₗ[ℝ] ℝ → ℝ :=
  LinearMap.mk₂ ℝ (fun φ ψ => crossSpec (rep φ) (rep ψ))
    (fun φ₁ φ₂ ψ => crossSpec_rep_add φ₁ φ₂ _)
    (fun c φ ψ => crossSpec_rep_smul c φ _)
    (fun φ ψ₁ ψ₂ => by
      have e : ∀ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L, crossSpec (rep φ) (rep ψ) = crossSpec (rep ψ) (rep φ) :=
        fun ψ => funext fun t => Cvs.WeilForm.ThetaSpaceParseval.crossSpec_comm _ _ t
      rw [e, e, e, crossSpec_rep_add])
    (fun c φ ψ => by
      have e : ∀ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L, crossSpec (rep φ) (rep ψ) = crossSpec (rep ψ) (rep φ) :=
        fun ψ => funext fun t => Cvs.WeilForm.ThetaSpaceParseval.crossSpec_comm _ _ t
      rw [e, e, crossSpec_rep_smul])

/-- **The form domain's cross density**, `ρ(φ, ψ) = ρ_{rep φ, rep ψ}` on `Cvs.WeilForm.FormDomain.formDomain hL`. -/
def formSpec {L : ℝ} (hL : 0 ≤ L) :
    Cvs.WeilForm.FormDomain.formDomain hL →ₗ[ℝ] Cvs.WeilForm.FormDomain.formDomain hL →ₗ[ℝ] ℝ → ℝ :=
  (windowSpec L).compl₁₂ (Cvs.WeilForm.FormDomain.formDomain hL).subtype (Cvs.WeilForm.FormDomain.formDomain hL).subtype

variable {L : ℝ} (hL : 0 ≤ L)

/-- On the diagonal `formSpec` is the spectral density of the representative. -/
theorem formSpec_self (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    formSpec hL φ φ = specDensity (rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) :=
  funext fun t => Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self _ t

/-- The representative of a form-domain class vanishes off `[0, L]`. -/
theorem rep_eq_zero (φ : Cvs.WeilForm.FormDomain.formDomain hL) : ∀ x ∉ Icc 0 L, rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) x = 0 :=
  fun x hx => Cvs.WeilForm.WindowRepresentative.rep_supp _ x fun h => hx (Ioc_subset_Icc_self h)

/-- **Band-free multipliers are admissible** on the form domain. -/
theorem bandFree_le_admissible : Cvs.WeilForm.BandFreedomCosine.bandFree L ≤ admissible (V := Cvs.WeilForm.FormDomain.formDomain hL) (formSpec hL) volume :=
  fun _ hh => mem_admissible.2 fun _ _ => Cvs.WeilForm.BandFreedomCosine.integrable_mul_crossSpec hh (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _)
    (Cvs.WeilForm.WindowRepresentative.memLp_rep _) (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _) (Cvs.WeilForm.WindowRepresentative.memLp_rep _)

variable (P R : ℕ)

/-- **The spectral mass of a window class is its squared norm**: `∫ ρ_{rep φ} = ‖φ‖²`. -/
theorem integral_specDensity_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ∫ t, specDensity (rep φ) t = ‖φ‖ ^ 2 := by
  rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ) (Cvs.WeilForm.WindowRepresentative.memLp_rep φ), Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]

end Window

/-! ### The operator floor at scale `x` -/

end Cvs.WeilForm.AdmissibleMultiplierMinorants
