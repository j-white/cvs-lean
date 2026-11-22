import Mathlib
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Route.CoreSchurForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowWeilCriterion

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Weil positivity on windows, read as CORE(x)

`WindowWeilCriterion`'s `rh_iff_windowPos` through Cvs.Route.CoreSchurForm: RH holds iff CORE(x) for every `x ≥ x₀` (any `x₀ ≥ 2`),
iff CORE(x) for every `x` with `c₀W ≤ 2πx`, iff CORE against `⊥` for those `x`. The last form uses
only `CoreSchurForm`'s `coreAt_bot_iff_nonneg`; the step CORE(x) ⟺ CORE against `⊥` goes through L2a's
`Q > 0` on `R_F ∖ 0` (`SpineSubspace`'s `RF_pos`).
-/

noncomputable section

open Real

namespace Cvs.Route.WindowPositivityAsCore
open Cvs.ZeroCounting

open Cvs.Route.CoreSchurForm (Core)

/-- Past the index `⌈c₀W/2π⌉`, the threshold `c₀W ≤ 2πx` holds. -/
theorem c0W_le_of_ceil_le {x : ℕ} (hx : ⌈Cvs.L2a.WindowChainInputsProlate.c0W / (2 * π)⌉₊ ≤ x) :
    Cvs.L2a.WindowChainInputsProlate.c0W ≤ 2 * π * x := by
  have hp : 0 < 2 * π := by positivity
  have h1 : Cvs.L2a.WindowChainInputsProlate.c0W / (2 * π) ≤ x := (Nat.le_ceil _).trans (by exact_mod_cast hx)
  rw [div_le_iff₀ hp] at h1
  calc Cvs.L2a.WindowChainInputsProlate.c0W ≤ x * (2 * π) := h1
    _ = 2 * π * x := by ring

/-- **CORE(x) for every `x ≥ x₀` gives RH.** -/
theorem rh_of_core (x₀ : ℕ) (h : ∀ x : ℕ, x₀ ≤ x → Core x) : RiemannHypothesis := by
  set x₁ := max x₀ ⌈Cvs.L2a.WindowChainInputsProlate.c0W / (2 * π)⌉₊ with hx₁
  have h2 : 2 ≤ x₁ := Cvs.Route.CoreSchurForm.two_le_of_c0W (c0W_le_of_ceil_le (le_max_right _ _))
  refine (Cvs.WeilForm.WindowWeilCriterion.rh_iff_windowPos x₁ h2).2 fun x hx => ?_
  exact (Cvs.Route.CoreSchurForm.core_iff_nonneg x (c0W_le_of_ceil_le ((le_max_right _ _).trans hx))).1
    (h x ((le_max_left _ _).trans hx))

/-- **RH is CORE(x) for every `x ≥ x₀`**, for any `x₀ ≥ 2`. -/
theorem rh_iff_core (x₀ : ℕ) (hx₀ : 2 ≤ x₀) :
    RiemannHypothesis ↔ ∀ x : ℕ, x₀ ≤ x → Core x :=
  ⟨fun hRH x hx => Cvs.Route.CoreSchurForm.core_of_rh hRH x (hx₀.trans hx), rh_of_core x₀⟩

end Cvs.Route.WindowPositivityAsCore
