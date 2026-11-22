import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.FullTailPolarisation
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.AdmissibleMultiplierMinorants
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.BandFreedomCosine
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.ThetaFormWindowIdentification
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
# Even Bulk Visibility, Rung-Projection Share, and Band-Free Split Certificates

Formalizes the even-bulk visibility criterion and Pythagorean rung-projection share bound,
together with band-free continuation split certificates and the cosine-comb equivalence.
-/

noncomputable section

open Real Filter MeasureTheory
open Complex (I)
open scoped InnerProductSpace
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)

namespace Cvs.WeilForm.EvenBulkVisibility
open Cvs.ZeroCounting

/-! ### 1. Even Bulk Visibility and Rung-Projection Share Interface -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For `r ∈ R` and `w ∈ Rᗮ`, `⟪w, r + w⟫ = ‖w‖²`. -/
theorem inner_add_of_perp {R : Submodule ℝ E} {r w : E} (hr : r ∈ R) (hw : w ∈ Rᗮ) :
    ⟪w, r + w⟫_ℝ = ‖w‖ ^ 2 := by
  have h0 : ⟪w, r⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact (Submodule.mem_orthogonal R w).1 hw r hr
  rw [inner_add_right, h0, zero_add, real_inner_self_eq_norm_sq]

/-- **Negative Bulk Direction from Visibility**: if `q ≤ M − 4⟪·, b⟫²` on `H`, `b = r + w` with
`r ∈ R`, `w ∈ H ∩ Rᗮ`, and `M w < 4‖w‖⁴`, then `q w < 0`. -/
theorem neg_of_visible {q M : E → ℝ} {H R : Submodule ℝ E} {b r w : E}
    (hq : ∀ u ∈ H, q u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2) (hwH : w ∈ H) (hr : r ∈ R) (hw : w ∈ Rᗮ)
    (hb : b = r + w) (hM : M w < 4 * ‖w‖ ^ 4) : q w < 0 := by
  have h1 := hq w hwH
  rw [hb, inner_add_of_perp hr hw] at h1
  have h4 : (‖w‖ ^ 2) ^ 2 = ‖w‖ ^ 4 := by ring
  rw [h4] at h1
  linarith

end Abstract

/-- **Visibility at `x` Refutes `EvenBulkFloor x 0`**: an even `b` with `Qx x ≤ M − 4⟪·, b⟫²` on
`Ev x` whose bulk part `w = b − P_{R₁} b` satisfies `M w < 4‖w‖⁴` refutes `EvenBulkFloor x 0`. -/
theorem not_evenBulkFloor_of_visible {x : ℕ} {M : Dom x → ℝ} {b : Dom x} (hbE : b ∈ Ev x)
    (hq : ∀ u ∈ Ev x, Qx x u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2)
    (hM : M (b - (R1 x).starProjection b) < 4 * ‖b - (R1 x).starProjection b‖ ^ 4) :
    ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  intro hF
  have hr : (R1 x).starProjection b ∈ R1 x := (R1 x).starProjection_apply_mem b
  have hw : b - (R1 x).starProjection b ∈ (R1 x)ᗮ := (R1 x).sub_starProjection_mem_orthogonal b
  have hwE : b - (R1 x).starProjection b ∈ Ev x := (Ev x).sub_mem hbE (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hr)
  have hb : b = (R1 x).starProjection b + (b - (R1 x).starProjection b) := by abel
  have hneg := neg_of_visible hq hwE hr hw hb hM
  have h0 := hF _ hwE hw
  rw [zero_mul] at h0
  linarith

/-- **Even Bulk Floor Carries `RiemannHypothesis` Under Visibility**: if, whenever RH fails,
every large `x` has a visible even vector `b`, then RH holds iff `EvenBulkFloor x 0` holds at
infinitely many `x`. -/
theorem rh_iff_frequently_evenBulkFloor_of_visible
    (hV : ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ∃ (M : Dom x → ℝ) (b : Dom x), b ∈ Ev x ∧
      (∀ u ∈ Ev x, Qx x u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2) ∧
      M (b - (R1 x).starProjection b) < 4 * ‖b - (R1 x).starProjection b‖ ^ 4) :
    RiemannHypothesis ↔ ∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  constructor
  · intro hRH
    exact (eventually_ge_atTop 2).frequently.mono fun x hx =>
      (Cvs.Route.EvenWindowBulkCoupling.even_floor_coupling_zero_of_rh hRH hx).2.1
  · intro hfreq
    by_contra hRH
    obtain ⟨x, hFx, M, b, hbE, hq, hM⟩ := (hfreq.and_eventually (hV hRH)).exists
    exact not_evenBulkFloor_of_visible hbE hq hM hFx

/-- **`RiemannHypothesis` from Eventual `EvenBulkFloor x 0` Under Visibility**. -/
theorem rh_of_eventually_evenBulkFloor_of_visible
    (hV : ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ∃ (M : Dom x → ℝ) (b : Dom x), b ∈ Ev x ∧
      (∀ u ∈ Ev x, Qx x u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2) ∧
      M (b - (R1 x).starProjection b) < 4 * ‖b - (R1 x).starProjection b‖ ^ 4)
    (hF : ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0) :
    RiemannHypothesis :=
  (rh_iff_frequently_evenBulkFloor_of_visible hV).mpr hF.frequently

/-! ### 2. Band-Free Continuation and Split Certificates on the Even Bulk -/

/-- The spectral density of a form-domain class, `ρ_φ = specDensity (rep φ)`. -/
abbrev rho {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) : ℝ → ℝ :=
  specDensity (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))

theorem integrable_rho {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) : Integrable (rho φ) :=
  Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity (Cvs.WeilForm.WindowRepresentative.memLp_rep _) (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _)

/-- A band-free `h` is integrable against `ρ_φ`. -/
theorem integrable_bandFree_mul_rho {L : ℝ} {hL : 0 ≤ L} {h : ℝ → ℝ} (hh : h ∈ Cvs.WeilForm.BandFreedomCosine.bandFree L)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) : Integrable fun t => h t * rho φ t := by
  have := Cvs.WeilForm.BandFreedomCosine.integrable_mul_crossSpec hh (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.WindowRepresentative.memLp_rep _) (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (Cvs.WeilForm.WindowRepresentative.memLp_rep _)
  simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using this

/-- A band-free `h` integrates against `ρ_φ` to `0`. -/
theorem integral_bandFree_mul_rho {L : ℝ} {hL : 0 ≤ L} {h : ℝ → ℝ} (hh : h ∈ Cvs.WeilForm.BandFreedomCosine.bandFree L)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) : ∫ t, h t * rho φ t = 0 :=
  Cvs.WeilForm.BandFreedomCosine.integral_mul_specDensity_eq_zero hh (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _) (Cvs.WeilForm.WindowRepresentative.memLp_rep _)
    (Cvs.WeilForm.AdmissibleMultiplierMinorants.rep_eq_zero hL φ) (sub_zero L).le

/-- Plancherel identity on `formDomain hL`: `∫ ρ_φ = ‖φ‖²`. -/
theorem integral_rho {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) : ∫ t, rho φ t = ‖φ‖ ^ 2 :=
  Cvs.WeilForm.AdmissibleMultiplierMinorants.integral_specDensity_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)

end Cvs.WeilForm.EvenBulkVisibility
