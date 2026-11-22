import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CentralResolventTrace
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
# The central trace `T_c` is at most twice the weighted energy of highpass extensions

If each central rung `h_k|_I` has a highpass extension `v_k`, then `T_c` is well posed and
`T_c ≤ 2 Σ_k g(σ_k)‖v_k‖²`, the eigenbasis form of `T_c ≤ 2 Tr(J_c QGQ J_c*)`; so `limsup Σ_k g(σ_k)‖v_k‖² ≤ Θ₀/2`
gives the trace limit `T_c ≤ 9/50`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.Prolate.Hardy.CentralTraceHighpass
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung IsLevelIdx)
open Cvs.Prolate.Gram.CentralResolventTrace (resObj resQuad traceTerm traceT Tc WellPosed gpoly sigma)
open Cvs.Prolate.Hardy.HighpassExtensionRung (IsHighpassExt)

/-- Every resolvent objective of `h` is at most `2‖v‖²` for a highpass extension `v` of `h|_I`. -/
theorem resObj_le {c : ℝ} (hc : 0 < c) {h v : ℝ → ℝ} (hv : IsHighpassExt c h v) (f : Cvs.Prolate.Gram.CentralResolventTrace.L2I) :
    resObj c h f ≤ 2 * ∫ t, v t ^ 2 :=
  Cvs.Prolate.Hardy.HighpassExtensionRung.objective_le hc (Lp.memLp f) hv

theorem bddAbove_resObj {c : ℝ} (hc : 0 < c) {h v : ℝ → ℝ} (hv : IsHighpassExt c h v) :
    BddAbove (range (resObj c h)) :=
  ⟨2 * ∫ t, v t ^ 2, by rintro _ ⟨f, rfl⟩; exact resObj_le hc hv f⟩

/-- `⟨Qh, (I − A)⁻¹Qh⟩ ≤ 2‖v‖²` for a highpass extension `v` of `h|_I`. -/
theorem resQuad_le {c : ℝ} (hc : 0 < c) {h v : ℝ → ℝ} (hv : IsHighpassExt c h v) :
    resQuad c h ≤ 2 * ∫ t, v t ^ 2 :=
  ciSup_le (resObj_le hc hv)

open Classical in
/-- The `k`-th weighted extension energy `g(σ_k)‖v_k‖²`, over the levels that exist. -/
def extTerm (c : ℝ) (v : ℕ → ℝ → ℝ) (k : ℕ) : ℝ :=
  if ∃ χ, IsLevelIdx c k χ then gpoly (sigma c k) * ∫ t, v k t ^ 2 else 0

/-- **The highpass trace** at level `σ`: the central rungs have highpass extensions `v_k` with
`Σ_k g(σ_k)‖v_k‖² ≤ σ`. -/
def HighpassTrace (c σ : ℝ) : Prop :=
  ∃ v : ℕ → ℝ → ℝ, (∀ k, (∃ χ, IsLevelIdx c k χ) → IsHighpassExt c (rung c k) (v k)) ∧
    Summable (extTerm c v) ∧ ∑' k, extTerm c v k ≤ σ

/-- A highpass trace at level `σ` makes `T_c` well posed with `T_c ≤ 2σ`. -/
theorem traceT_le {c σ : ℝ} (hc : 0 < c) (h : HighpassTrace c σ) : WellPosed c ∧ traceT c ≤ 2 * σ := by
  obtain ⟨v, hv, hs, hσ⟩ := h
  have hB : ∀ k, (∃ χ, IsLevelIdx c k χ) → BddAbove (range (resObj c (rung c k))) :=
    fun k hk => bddAbove_resObj hc (hv k hk)
  have hle : ∀ k, traceTerm c k ≤ 2 * extTerm c v k := by
    intro k
    unfold traceTerm extTerm
    split_ifs with hk
    · rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (resQuad_le hc (hv k hk))
        (Cvs.Prolate.Gram.CentralResolventTrace.gpoly_nonneg (Cvs.Prolate.Gram.CentralResolventTrace.abs_sigma_le_one hc hk))
    · simp
  have h0 : ∀ k, 0 ≤ traceTerm c k := by
    intro k
    unfold traceTerm
    split_ifs with hk
    · exact mul_nonneg (Cvs.Prolate.Gram.CentralResolventTrace.gpoly_nonneg (Cvs.Prolate.Gram.CentralResolventTrace.abs_sigma_le_one hc hk)) (Cvs.Prolate.Gram.CentralResolventTrace.resQuad_nonneg (hB k hk))
    · exact le_rfl
  have hsum : Summable (traceTerm c) := (hs.mul_left 2).of_nonneg_of_le h0 hle
  refine ⟨⟨hB, hsum⟩, ?_⟩
  calc traceT c = ∑' k, traceTerm c k := rfl
    _ ≤ ∑' k, 2 * extTerm c v k := hsum.tsum_le_tsum hle (hs.mul_left 2)
    _ = 2 * ∑' k, extTerm c v k := tsum_mul_left
    _ ≤ 2 * σ := by linarith

/-- `limsup_c` of the weighted highpass extension energy is at most `σ`. -/
def HighpassTraceLimsup (σ : ℝ) : Prop := ∀ ε > 0, ∀ᶠ x : ℕ in atTop, HighpassTrace (2 * π * x) (σ + ε)

/-- `limsup Σ_k g(σ_k)‖v_k‖² ≤ σ` gives `limsup T_c ≤ 2σ`. -/
theorem traceLimsup_of_highpass {σ : ℝ} (h : HighpassTraceLimsup σ) : Cvs.Route.Visibility.VisibilityLandauTransition.TraceLimsup (2 * σ) := by
  intro ε hε
  filter_upwards [h (ε / 2) (by positivity), eventually_ge_atTop 1] with x hx h1
  have hc : 0 < 2 * π * x := by have : (1 : ℝ) ≤ x := by exact_mod_cast h1
                                positivity
  obtain ⟨hW, hT⟩ := traceT_le hc hx
  exact ⟨hW, by simp only [Tc]; linarith⟩

/-- **The trace limit** `T_c ≤ 9/50` from `limsup Σ_k g(σ_k)‖v_k‖² ≤ Θ₀/2 = log(16/3)/(2π²)`. -/
theorem traceLimit_of_highpass (h : HighpassTraceLimsup (Cvs.Route.Visibility.VisibilityLandauTransition.thetaCons / 2)) : Cvs.Route.Visibility.CEBoundFromTrace.TraceLimit := by
  have := traceLimsup_of_highpass h
  rw [mul_div_cancel₀ _ two_ne_zero] at this
  exact Cvs.Route.Visibility.VisibilityLandauTransition.traceLimit_of_thetaCons this

end Cvs.Prolate.Hardy.CentralTraceHighpass

end
