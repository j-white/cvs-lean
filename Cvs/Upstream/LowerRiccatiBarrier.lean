import Mathlib
import Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Lower Riccati barriers

A nonnegative solution of `U′ = U²/p − q` lies above any subsolution-in-reverse `L′ ≥ L²/p − q` that it dominates at
the right end `b`. With the linear barrier `L = k(e − x)` this gives, for `0 < p ≤ 1` and `pq ≥ β²` on `[s, e]`,
`U(s) ≥ β − 1/(2(e − s))`. A positive `g` with `g′ + gh′ ≤ 0` has `g(b)e^{h(b)} ≤ g(a)e^{h(a)}`.
-/

noncomputable section

open Real Set

namespace Cvs.Upstream.LowerRiccatiBarrier

/-- **Antitone envelope**: if `g′ + gh′ ≤ 0` on `(a, b)`, with `g`, `h` continuous on `[a, b]`, then
`g(b)e^{h(b)} ≤ g(a)e^{h(a)}`. -/
theorem mul_exp_le_rev {g g₁ h h₁ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hgc : ContinuousOn g (Icc a b))
    (hhc : ContinuousOn h (Icc a b)) (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g₁ x) x)
    (hh : ∀ x ∈ Ioo a b, HasDerivAt h (h₁ x) x) (hd : ∀ x ∈ Ioo a b, g₁ x + g x * h₁ x ≤ 0) :
    g b * exp (h b) ≤ g a * exp (h a) := by
  have := Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent.mul_exp_le (g := fun x => -g x) (g₁ := fun x => -g₁ x) hab hgc.neg hhc
    (fun x hx => (hg x hx).neg) hh (fun x hx => by have := hd x hx; linarith)
  simp only [neg_mul] at this
  linarith

end Cvs.Upstream.LowerRiccatiBarrier
