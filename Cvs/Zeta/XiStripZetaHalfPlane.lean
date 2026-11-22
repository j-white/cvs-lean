import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiStrip
import Cvs.Zeta.XiVertical

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A zero-free strip for `ξ` is a zero-free half-plane for `ζ` left of `1`

Every zero of `ξ` has real part at most `θ` exactly when `ζ` has no zeros on `Re s > θ` with `Re s > 0`, and then at
least `1 − θ` by `ξ(1 − s) = ξ(s)`. So a strip `Re ρ ≤ 1 − δ` with `δ > 0` is a half-plane `Re s > θ`, `θ < 1`, free
of zeros of `ζ`; with `θ = 7/8` every zero of `ξ` lies in `1/8 ≤ Re ρ ≤ 7/8`.
-/

noncomputable section

open Cvs.Zeta

namespace Cvs.Zeta.XiStripZetaHalfPlane

/-- **A zero-free half-plane of `ζ`**: no zeros on `Re s > θ`. -/
def ZetaFreeAbove (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

/-- **The zeros of `ξ` against a half-plane of `ζ`**: every zero of `ξ` has real part at most `θ` exactly when `ζ` has
no zeros at `s` with `θ < Re s` and `0 < Re s`. -/
theorem re_le_iff_zeta_ne_zero (θ : ℝ) :
    (∀ ρ : ℂ, riemannXi ρ = 0 → ρ.re ≤ θ) ↔
      ∀ s : ℂ, θ < s.re → 0 < s.re → riemannZeta s ≠ 0 := by
  constructor
  · intro h s hθ h0 hz
    rcases eq_or_ne s 1 with rfl | hs1
    · exact riemannZeta_one_ne_zero hz
    · exact absurd (h s ((riemannXi_eq_zero_iff_riemannZeta h0 hs1).2 hz)) (not_le.2 hθ)
  · intro h ρ hρ
    have hst := riemannXi_zero_mem_strip hρ
    have hρ1 : ρ ≠ 1 := fun e => by rw [e] at hst; simp at hst
    by_contra hlt
    exact h ρ (not_le.1 hlt) hst.1 ((riemannXi_eq_zero_iff_riemannZeta hst.1 hρ1).1 hρ)

/-- **The reflected bound**: if every zero of `ξ` has real part at most `θ`, every zero has real part at least
`1 − θ`. -/
theorem one_sub_le_re {θ : ℝ} (h : ∀ ρ : ℂ, riemannXi ρ = 0 → ρ.re ≤ θ) {ρ : ℂ} (hρ : riemannXi ρ = 0) :
    1 - θ ≤ ρ.re := by
  have h' := h (1 - ρ) (by rw [riemannXi_one_sub]; exact hρ)
  simp only [Complex.sub_re, Complex.one_re] at h'
  linarith

end Cvs.Zeta.XiStripZetaHalfPlane
