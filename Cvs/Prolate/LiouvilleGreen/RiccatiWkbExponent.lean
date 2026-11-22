import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Riccati variable and the closed-form WKB exponent

For the angular equation, `U = −(1 − s²)g′/g` solves `U′ = U²/p − q` (`p = 1 − s²`, `q = c²s² − χ`). The phase
`Φ₂ = −r + (s₀²/2)ℓ` has `Φ₂′ = (s − s₀²/(2s))/r ≥ √(s² − s₀²)/r`, and `g e^h` is monotone wherever `−g′/g ≤ h′`.
-/

noncomputable section

open Real Set

namespace Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent


/-- The Riccati variable `U = −(1 − s²)g′/g`. -/
def U (g g₁ : ℝ → ℝ) (s : ℝ) : ℝ := -((1 - s ^ 2) * g₁ s) / g s

/-- **The Riccati equation**: where `g ≠ 0`, `U′ = U²/(1 − s²) − (c²s² − χ)` for `|s| < 1`. -/
theorem hasDerivAt_U {g g₁ g₂ : ℝ → ℝ} {c χ s : ℝ} (hg : HasDerivAt g (g₁ s) s) (hg₁ : HasDerivAt g₁ (g₂ s) s)
    (hang : (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) (hs : s ^ 2 < 1)
    (h0 : g s ≠ 0) :
    HasDerivAt (U g g₁) (U g g₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χ)) s := by
  have hp : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := by
    simpa using ((hasDerivAt_pow 2 s).const_sub 1)
  have hm : HasDerivAt (fun x => (1 - x ^ 2) * g₁ x) (-(2 * s) * g₁ s + (1 - s ^ 2) * g₂ s) s := hp.mul hg₁
  have hn : HasDerivAt (fun x => -((1 - x ^ 2) * g₁ x) / g x)
      ((-(-(2 * s) * g₁ s + (1 - s ^ 2) * g₂ s) * g s - -((1 - s ^ 2) * g₁ s) * g₁ s) / g s ^ 2) s :=
    hm.neg.div hg h0
  refine hn.congr_deriv ?_
  have hp0 : 1 - s ^ 2 ≠ 0 := by linarith
  simp only [U]
  field_simp
  linear_combination (-(g s)) * hang

/-- **Monotone envelope**: if `g > 0` and `g′ + g h′ ≥ 0` on `(a, b)`, with `g`, `h` continuous on `[a, b]`, then
`g(a)e^{h(a)} ≤ g(b)e^{h(b)}`. -/
theorem mul_exp_le {g g₁ h h₁ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hgc : ContinuousOn g (Icc a b))
    (hhc : ContinuousOn h (Icc a b)) (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g₁ x) x)
    (hh : ∀ x ∈ Ioo a b, HasDerivAt h (h₁ x) x) (hd : ∀ x ∈ Ioo a b, 0 ≤ g₁ x + g x * h₁ x) :
    g a * exp (h a) ≤ g b * exp (h b) := by
  have hmono : MonotoneOn (fun x => g x * exp (h x)) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (hgc.mul (continuous_exp.comp_continuousOn hhc)) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hg x hx).mul ((hh x hx).exp)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hd' : HasDerivAt (fun x => g x * exp (h x)) (g₁ x * exp (h x) + g x * (exp (h x) * h₁ x)) x :=
        (hg x hx).mul ((hh x hx).exp)
      rw [hd'.deriv]
      have := hd x hx
      have he := exp_pos (h x)
      nlinarith [mul_nonneg this he.le]
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

end Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent
