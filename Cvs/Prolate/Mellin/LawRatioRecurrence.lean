import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.RungThreeTermRecurrence

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The law ratio `P = M/M_G` satisfies `(s+1)P(s) = qP(s+2) + (s+2)P(s+4)`

With the Gaussian reference `mg c s = ½(2/c)^{s/2}Γ(s/2)`, which satisfies `mg c (s + 2) = (s/c) mg c s`, the ratio
`lawRatio c h s = mel h s / mg c s` of a solution of the angular equation obeys
`(s + 1)P(s) − ((s + 1)(s + 2) − χ)/c · P(s + 2) − (s + 2)P(s + 4) = 0` for `Re s > 0`.
-/

noncomputable section

open Real Set Complex

namespace Cvs.Prolate.Mellin.LawRatioRecurrence

open Cvs.Prolate.Mellin.RungThreeTermRecurrence (mel mel_recurrence)

/-- The Gaussian reference `½(2/c)^{s/2}Γ(s/2)`, the Mellin transform of `e^{−cw²/2}` over `(0, ∞)`. -/
def mg (c : ℝ) (s : ℂ) : ℂ := 1 / 2 * ((2 / c : ℝ) : ℂ) ^ (s / 2) * Gamma (s / 2)

/-- `mg c (s + 2) = (s/c) mg c s`. -/
theorem mg_add_two {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : s ≠ 0) : mg c (s + 2) = s / c * mg c s := by
  have h2c : ((2 / c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos two_pos hc).ne'
  have hs2 : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold mg
  rw [show (s + 2) / 2 = s / 2 + 1 by ring, Complex.cpow_add _ _ h2c, Complex.cpow_one,
    Complex.Gamma_add_one _ hs2]
  push_cast
  field_simp

/-- `mg c s ≠ 0` for `Re s > 0`. -/
theorem mg_ne_zero {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) : mg c s ≠ 0 := by
  have h2c : ((2 / c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos two_pos hc).ne'
  unfold mg
  refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) (Complex.Gamma_ne_zero_of_re_pos ?_)
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl h2c)
  · simp; linarith

/-- The law ratio `P(s) = mel h s / mg c s`. -/
def lawRatio (c : ℝ) (h : ℝ → ℝ) (s : ℂ) : ℂ := mel h s / mg c s

/-- **The law-ratio recurrence** for any `C²` solution of the angular equation on `[0, 1]`. -/
theorem lawRatio_recurrence {c χ : ℝ} (hc : 0 < c) {h h₁ h₂ : ℝ → ℝ}
    (hd : ∀ w ∈ Icc (0 : ℝ) 1, HasDerivAt h (h₁ w) w) (hd₁ : ∀ w ∈ Icc (0 : ℝ) 1, HasDerivAt h₁ (h₂ w) w)
    (hode : ∀ w ∈ Icc (0 : ℝ) 1, (1 - w ^ 2) * h₂ w - 2 * w * h₁ w - c ^ 2 * w ^ 2 * h w + χ * h w = 0)
    {s : ℂ} (hs : 0 < s.re) :
    (s + 1) * lawRatio c h s - ((s + 1) * (s + 2) - χ) / c * lawRatio c h (s + 2)
      - (s + 2) * lawRatio c h (s + 4) = 0 := by
  have hs0 : s ≠ 0 := fun h0 => by simp [h0] at hs
  have hs2 : s + 2 ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hg := mg_ne_zero hc hs
  have hg2 : mg c (s + 2) = s / c * mg c s := mg_add_two hc hs0
  have hg4 : mg c (s + 4) = (s + 2) / c * (s / c * mg c s) := by
    rw [show s + 4 = (s + 2) + 2 by ring, mg_add_two hc hs2, hg2]
  have hg2' : mg c (s + 2) ≠ 0 := by rw [hg2]; exact mul_ne_zero (div_ne_zero hs0 hc0) hg
  have hg4' : mg c (s + 4) ≠ 0 := by
    rw [hg4]; exact mul_ne_zero (div_ne_zero hs2 hc0) (mul_ne_zero (div_ne_zero hs0 hc0) hg)
  have R := mel_recurrence hd hd₁ hode hs
  have e0 : mel h s = lawRatio c h s * mg c s := by unfold lawRatio; field_simp
  have e2 : mel h (s + 2) = lawRatio c h (s + 2) * mg c (s + 2) := by unfold lawRatio; field_simp
  have e4 : mel h (s + 4) = lawRatio c h (s + 4) * mg c (s + 4) := by unfold lawRatio; field_simp
  rw [e0, e2, e4, hg2, hg4] at R
  have key : s * mg c s * ((s + 1) * lawRatio c h s - ((s + 1) * (s + 2) - χ) / c * lawRatio c h (s + 2)
      - (s + 2) * lawRatio c h (s + 4)) = 0 := by
    rw [← R]; field_simp
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hs0 hg)

/-- **The law-ratio recurrence for the prolate rung of index `k`.** -/
theorem lawRatio_rung_recurrence {c : ℝ} (hc : 0 < c) {k : ℕ} (h : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c k χ) {s : ℂ}
    (hs : 0 < s.re) :
    (s + 1) * lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c k) s
      - ((s + 1) * (s + 2) - Cvs.Prolate.EvenRungsByIndex.lev c k) / c * lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c k) (s + 2)
      - (s + 2) * lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c k) (s + 4) = 0 := by
  obtain ⟨hd, hd₁, -, hang, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec h
  have hsub : Icc (0 : ℝ) 1 ⊆ uIcc (-1) 1 := by
    rw [uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  exact lawRatio_recurrence hc (fun w hw => hd w (hsub hw)) (fun w hw => hd₁ w (hsub hw))
    (fun w hw => hang w (hsub hw)) hs

end Cvs.Prolate.Mellin.LawRatioRecurrence
