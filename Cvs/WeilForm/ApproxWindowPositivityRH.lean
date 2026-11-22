import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.NestedWindowsMonotoneBottom
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
# Approximate window positivity is RH

The window at `L = log x` embeds isometrically into the window at `log x'`, `x ≤ x'`, with its Weil
value unchanged (Cvs.WeilForm.NestedWindowsMonotoneBottom). So `Q ≥ −ε‖φ‖²` at arbitrarily large integers `x`, for every `ε > 0`, gives
`Q ≥ 0` at every `x ≥ 2`, and `WindowWeilCriterion`'s criterion gives RH: window positivity with an error `o(1)`
in the normalised form, along any sequence `x → ∞`, is RH.
-/

noncomputable section

open Real

namespace Cvs.WeilForm.ApproxWindowPositivityRH
open Cvs.ZeroCounting

/-- `log x ≤ log x'` for integers `2 ≤ x ≤ x'`. -/
theorem log_le_log_nat {x x' : ℕ} (hx : 2 ≤ x) (hxx : x ≤ x') : Real.log x ≤ Real.log x' :=
  Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hx : 0 < x))
    (by exact_mod_cast hxx)

/-- **The Weil value is unchanged by nesting the windows** at integer scales `2 ≤ x ≤ x'`. -/
theorem Q_embedD {x x' : ℕ} (hx : 2 ≤ x) (hxx : x ≤ x')
    (φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x') x' (Nat.clog 2 x')
        (Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD (Real.log_natCast_nonneg x) (Real.log_natCast_nonneg x')
          (log_le_log_nat hx hxx) φ)
      = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ := by
  obtain ⟨-, hP, hR⟩ := Cvs.Approximant.SpineSubspace.sizes x hx
  exact Cvs.WeilForm.NestedWindowsMonotoneBottom.weilQW_embed (Real.log_natCast_nonneg x) (log_le_log_nat hx hxx)
    hxx (Nat.clog_mono_right 2 hxx) hP hR φ

/-- **Approximate positivity at larger scales gives positivity**: if for every `ε > 0` some
`x' ≥ x` has `Q ≥ −ε‖·‖²`, then `Q ≥ 0` at `x`. -/
theorem Q_nonneg_of_approx {x : ℕ} (hx : 2 ≤ x)
    (h : ∀ ε > 0, ∃ x' : ℕ, x ≤ x' ∧
      ∀ ψ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x'),
        -ε * ‖ψ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x') x' (Nat.clog 2 x') ψ)
    (φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) :
    0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ := by
  have key : ∀ ε > 0, -ε * ‖φ‖ ^ 2
      ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ := by
    intro ε hε
    obtain ⟨x', hxx', hx'⟩ := h ε hε
    have h1 := hx' (Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD (Real.log_natCast_nonneg x)
      (Real.log_natCast_nonneg x') (log_le_log_nat hx hxx') φ)
    rw [Q_embedD hx hxx'] at h1
    have hn : ‖Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD (Real.log_natCast_nonneg x) (Real.log_natCast_nonneg x')
        (log_le_log_nat hx hxx') φ‖ = ‖φ‖ :=
      Cvs.WeilForm.NestedWindowsMonotoneBottom.norm_embed (Real.log_natCast_nonneg x) (log_le_log_nat hx hxx') φ
    rwa [hn] at h1
  by_contra hneg
  push Not at hneg
  set q := Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ with hq
  set n := ‖φ‖ ^ 2 with hn
  have hn0 : 0 ≤ n := by positivity
  have hε : 0 < -q / (2 * (n + 1)) := div_pos (by linarith) (by positivity)
  have h1 := key _ hε
  have h2 : -q / (2 * (n + 1)) * (2 * (n + 1)) = -q := div_mul_cancel₀ _ (by positivity)
  nlinarith

/-- **Approximate window positivity gives RH**: for every `ε > 0` and every `x₀`, some integer
`x ≥ x₀` has `Q ≥ −ε‖·‖²` on the form domain at `L = log x`, `P = x`, `R = ⌈log₂ x⌉`. -/
theorem rh_of_approx_windowPos
    (h : ∀ ε > 0, ∀ x₀ : ℕ, ∃ x : ℕ, x₀ ≤ x ∧
      ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        -ε * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) :
    RiemannHypothesis :=
  Cvs.WeilForm.WindowWeilCriterion.rh_of_windowPos 2 fun x hx φ =>
    Q_nonneg_of_approx hx (fun ε hε => h ε hε x) φ

/-- **RH is approximate window positivity along `x → ∞`.** -/
theorem rh_iff_approx_windowPos :
    RiemannHypothesis ↔ ∀ ε > 0, ∀ x₀ : ℕ, ∃ x : ℕ, x₀ ≤ x ∧
      ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        -ε * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ := by
  refine ⟨fun hRH ε hε x₀ => ?_, rh_of_approx_windowPos⟩
  refine ⟨max x₀ 2, le_max_left _ _, fun φ => ?_⟩
  have h0 := ((Cvs.WeilForm.WindowWeilCriterion.rh_iff_windowPos 2 le_rfl).mp hRH) (max x₀ 2)
    (le_max_right _ _) φ
  have : 0 ≤ ε * ‖φ‖ ^ 2 := by positivity
  linarith

end Cvs.WeilForm.ApproxWindowPositivityRH
