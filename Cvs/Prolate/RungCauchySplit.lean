import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Envelope.RungCountEnvelope
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Cauchy split of a rung

For `ψ' = u/p`, `u' = −qψ`, `a² = pq`, `a' = wq`, the complex half `ψ⁺ = (ψ − iu/a)/2` has `ψ = 2 Re ψ⁺`,
`|ψ⁺|² = E/(4a)` and `ψ⁺' = (ik − β)ψ⁺ + β·conj ψ⁺` exactly, with `k = a/p` and `β = wq/(2a)`.
For a rung (Cvs.Prolate.Gram.RungGramFloorAtInfinity) this gives `|ψ⁺| = R/2` with `RungCountEnvelope`'s amplitude `R = √(E/a)`.
-/

namespace Cvs.Prolate.RungCauchySplit

open Complex Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.Envelope.RungCountEnvelope
open scoped ComplexConjugate

section general

variable {ψ u p q a w : ℝ → ℝ} {t : ℝ}

/-- The Cauchy half `ψ⁺ = (ψ − iu/a)/2` of a pair `(ψ, u)`. -/
noncomputable def split (a ψ u : ℝ → ℝ) (t : ℝ) : ℂ := ((ψ t : ℂ) - I * ((u t / a t : ℝ) : ℂ)) / 2

theorem re_split : (split a ψ u t).re = ψ t / 2 := by simp [split]

theorem im_split : (split a ψ u t).im = -(u t / a t) / 2 := by simp [split]

/-- `ψ = 2 Re ψ⁺`. -/
theorem eq_two_mul_re_split : ψ t = 2 * (split a ψ u t).re := by rw [re_split]; ring

/-- `ψ⁺ + conj ψ⁺ = ψ`. -/
theorem split_add_conj : split a ψ u t + conj (split a ψ u t) = (ψ t : ℂ) := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, re_split, im_split] <;>
    simp

/-- `ψ⁺ − conj ψ⁺ = −i u/a`. -/
theorem split_sub_conj : split a ψ u t - conj (split a ψ u t) = -I * ((u t / a t : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, re_split, im_split] <;>
    simp

/-- `|ψ⁺|² = E/(4a)`. -/
theorem norm_split_sq (ha : 0 < a t) : ‖split a ψ u t‖ ^ 2 = energy a ψ u t / (4 * a t) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, re_split, im_split]
  unfold energy
  field_simp
  ring

/-- `|ψ⁺| = √(E/a)/2`. -/
theorem norm_split (ha : 0 < a t) : ‖split a ψ u t‖ = √(energy a ψ u t / a t) / 2 := by
  have h := norm_split_sq (ψ := ψ) (u := u) ha
  have e : energy a ψ u t / (4 * a t) = (√(energy a ψ u t / a t) / 2) ^ 2 := by
    have hE : 0 ≤ energy a ψ u t / a t := by
      unfold energy
      have : 0 ≤ a t * ψ t ^ 2 + u t ^ 2 / a t := by positivity
      positivity
    rw [div_pow, Real.sq_sqrt hE]
    field_simp
    ring
  rw [e] at h
  have h0 : 0 ≤ √(energy a ψ u t / a t) / 2 := by positivity
  nlinarith [norm_nonneg (split a ψ u t), sq_nonneg (‖split a ψ u t‖ - √(energy a ψ u t / a t) / 2),
    sq_nonneg (‖split a ψ u t‖ + √(energy a ψ u t / a t) / 2)]

/-- **The split equation**: `ψ⁺' = (ik − β)ψ⁺ + β·conj ψ⁺`, `k = a/p`, `β = wq/(2a)`. -/
theorem hasDerivAt_split (ha : 0 < a t) (hp : p t ≠ 0) (hapq : a t ^ 2 = p t * q t)
    (hψ : HasDerivAt ψ (u t / p t) t) (hu : HasDerivAt u (-(q t * ψ t)) t)
    (haw : HasDerivAt a (w t * q t) t) :
    HasDerivAt (split a ψ u)
      ((I * ((a t / p t : ℝ) : ℂ) - ((w t * q t / (2 * a t) : ℝ) : ℂ)) * split a ψ u t
        + ((w t * q t / (2 * a t) : ℝ) : ℂ) * conj (split a ψ u t)) t := by
  have hd : HasDerivAt (fun s => u s / a s)
      ((-(q t * ψ t) * a t - u t * (w t * q t)) / a t ^ 2) t := hu.div haw ha.ne'
  have h := ((hψ.ofReal_comp).sub (hd.ofReal_comp.const_mul I)).div_const 2
  refine h.congr_deriv ?_
  have hq : q t = a t ^ 2 / p t := by rw [hapq]; field_simp
  have ha' : (a t : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hp' : (p t : ℂ) ≠ 0 := by exact_mod_cast hp
  simp only [split, map_div₀, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [hq]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end general

section rung

variable {c χ ξ : ℝ} {g g₁ g₂ : ℝ → ℝ}

/-- The rung's Cauchy half `ψ⁺ = (ψ − iu/a)/2`. -/
noncomputable def psiP (c χ : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : ℂ := split (aP c χ) (psi c g) (rungU c g) ξ

/-- The local wavenumber `k = a/p`. -/
noncomputable def kP (c χ ξ : ℝ) : ℝ := aP c χ ξ / pP ξ

/-- The coupling `β = wq/(2a)`. -/
noncomputable def betaP (c χ ξ : ℝ) : ℝ := wP c χ ξ * qP c χ ξ / (2 * aP c χ ξ)

theorem psi_eq_two_mul_re_psiP : psi c g ξ = 2 * (psiP c χ g ξ).re := eq_two_mul_re_split

theorem norm_psiP (hξ : 1 < ξ) (hc : 0 < c) (hχc : χ < c ^ 2) : ‖psiP c χ g ξ‖ = rungAmp c χ g ξ / 2 :=
  norm_split (aP_pos hξ (by positivity) hχc)

theorem hasDerivAt_psiP
    (hg : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (Set.uIcc (-1) 1))
    (hang : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hξ : 1 < ξ) (hc : 0 < c) (hχc : χ < c ^ 2) :
    HasDerivAt (psiP c χ g)
      ((I * (kP c χ ξ : ℂ) - (betaP c χ ξ : ℂ)) * psiP c χ g ξ + (betaP c χ ξ : ℂ) * conj (psiP c χ g ξ)) ξ := by
  obtain ⟨hψ, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
  have hc2 : 0 < c ^ 2 := by positivity
  exact hasDerivAt_split (aP_pos hξ hc2 hχc) (pP_pos hξ).ne' (aP_sq hξ hc2 hχc) (hψ ξ hξ) (hu ξ)
    (hasDerivAt_aP hξ hc2 hχc)

end rung

end Cvs.Prolate.RungCauchySplit
