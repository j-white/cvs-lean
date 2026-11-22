import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.AveragedColumnEnergy
import Cvs.Prolate.Hardy.CentralRungExpansion
import Cvs.Prolate.Hardy.CentralTraceHighpass
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.HighpassExtensionRung
import Cvs.Route.Visibility.CEBoundFromTrace
import Cvs.Route.Visibility.VisibilityLandauTransition

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trace limit from a highpass extension operator with the exterior-column limits

A bounded `J : L²(I) → L²(ℝ)` taking every `f` to a highpass extension of `f` gives `T_c ≤ 2(S_J + O_J)`; so
`limsup S_J ≤ S_∞(3/5) = Θ₀/2` with `limsup O_J ≤ 0` gives `T_c ≤ 9/50` eventually, and so does `S_∞(1/√3) = Θ/2`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.Prolate.Hardy.TraceLimitHighpassOperator
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung IsLevelIdx)
open Cvs.Prolate.Gram.CentralResolventTrace (L2I)
open Cvs.Prolate.Hardy.HighpassExtensionRung (IsHighpassExt)
open Cvs.Prolate.Hardy.CentralRungExpansion (qI hk continuous_hk)
open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R extS extO eigTerm)

/-- `J` takes every `f ∈ L²(I)` to a highpass extension of `f`: `J f ∈ L²(ℝ)` equals `f` on `I` and has no cosine
frequencies in `(−c/2, c/2)`. -/
def HighpassOp (c : ℝ) (J : L2I →L[ℝ] L2R) : Prop := ∀ f : L2I, IsHighpassExt c f (J f)

theorem isHighpassExt_congr {c : ℝ} {h h' v : ℝ → ℝ} (hv : IsHighpassExt c h v)
    (hh : h =ᵐ[volume.restrict Cvs.Prolate.Hardy.CosineSynthesisPlancherel.cI] h') : IsHighpassExt c h' v :=
  ⟨hv.1, (hv.2.1.and hh).mono fun _ ht => ht.1.trans ht.2, hv.2.2⟩

theorem integral_sq_eq_norm_sq (g : L2R) : ∫ t, (g : ℝ → ℝ) t ^ 2 = ‖g‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [sq])

/-- The extensions `v_k = J(Qh_k)` of the central rungs. -/
theorem isHighpassExt_rung {c : ℝ} {J : L2I →L[ℝ] L2R} (hJ : HighpassOp c J) {k : ℕ}
    (hk' : ∃ χ, IsLevelIdx c k χ) : IsHighpassExt c (rung c k) (J (qI (continuous_hk c k))) := by
  refine isHighpassExt_congr (hJ _) ?_
  filter_upwards [Cvs.Prolate.Hardy.CentralRungExpansion.coeFn_qI (continuous_hk c k), ae_restrict_mem measurableSet_Icc] with t ht hmem
  rw [ht, Cvs.Prolate.Hardy.CentralRungExpansion.hk_eq hk' (Icc_subset_Icc (by norm_num) (by norm_num) hmem)]

/-- **A highpass extension operator bounds the trace**: the central rungs have highpass extensions with weighted
energy `S_J + O_J`. -/
theorem highpassTrace {c : ℝ} (hc : 0 < c) {J : L2I →L[ℝ] L2R} (hJ : HighpassOp c J) :
    Cvs.Prolate.Hardy.CentralTraceHighpass.HighpassTrace c (extS c J + extO c J) := by
  have hS := Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral.hasSum_eigTerm hc J
  refine ⟨fun k => J (qI (continuous_hk c k)), fun k hk' => isHighpassExt_rung hJ hk', ?_, ?_⟩
  · refine hS.summable.congr fun k => ?_
    unfold Cvs.Prolate.Hardy.CentralTraceHighpass.extTerm eigTerm
    split_ifs <;> simp [integral_sq_eq_norm_sq]
  · refine le_of_eq ((tsum_congr fun k => ?_).trans hS.tsum_eq)
    unfold Cvs.Prolate.Hardy.CentralTraceHighpass.extTerm eigTerm
    split_ifs <;> simp [integral_sq_eq_norm_sq]

/-- **The exterior-column limits** at level `σ`: for every `ε > 0`, eventually there is a highpass extension operator
`J_c` with `S_J ≤ σ + ε` and `O_J ≤ ε`. -/
def HighpassColumnLimsup (σ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℕ in atTop, ∃ J : L2I →L[ℝ] L2R, HighpassOp (2 * π * x) J ∧
    extS (2 * π * x) J ≤ σ + ε ∧ extO (2 * π * x) J ≤ ε

/-- The exterior-column limits give the limsup of the highpass trace. -/
theorem highpassTraceLimsup {σ : ℝ} (h : HighpassColumnLimsup σ) : Cvs.Prolate.Hardy.CentralTraceHighpass.HighpassTraceLimsup σ := by
  intro ε hε
  filter_upwards [h (ε / 2) (by positivity), eventually_ge_atTop 1] with x hx h1
  obtain ⟨J, hJ, hS, hO⟩ := hx
  have hc : 0 < 2 * π * x := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast h1
    positivity
  obtain ⟨v, hv, hs, hle⟩ := highpassTrace hc hJ
  exact ⟨v, hv, hs, by linarith⟩

theorem highpassColumnLimsup_mono {σ σ' : ℝ} (hσ : σ ≤ σ') (h : HighpassColumnLimsup σ) :
    HighpassColumnLimsup σ' := by
  intro ε hε
  filter_upwards [h ε hε] with x ⟨J, hJ, hS, hO⟩
  exact ⟨J, hJ, by linarith, hO⟩

/-- **The trace limit** from the exterior-column limits at the fixed ellipse: `limsup S_J ≤ S_∞(3/5) = Θ₀/2`. -/
theorem traceLimit (h : HighpassColumnLimsup (Cvs.Prolate.Hardy.AveragedColumnEnergy.avgEnergy (3 / 5))) : Cvs.Route.Visibility.CEBoundFromTrace.TraceLimit := by
  rw [Cvs.Prolate.Hardy.AveragedColumnEnergy.avgEnergy_three_fifths] at h
  exact Cvs.Prolate.Hardy.CentralTraceHighpass.traceLimit_of_highpass (highpassTraceLimsup h)

end Cvs.Prolate.Hardy.TraceLimitHighpassOperator

end
