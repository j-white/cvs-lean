import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The endpoint of an angular eigenfunction is at least `e^{−πc/2}/√2`

For `((1 − s²)h′)′ + (χ − c²s²)h = 0` with `0 ≤ χ ≤ c²`, the energy `Ẽ = h² + (1 − s²)h′²/c²` has
`Ẽ′ = 2sh′²/c² + 2hh′(c² + c²s² − χ)/c² ≥ −2cẼ/√(1 − s²)` on `[0, 1)`, so `Ẽ e^{2c arcsin s}` increases and
`h(1)² = Ẽ(1) ≥ e^{−πc} max h²`; an even `h` with `∫h² = 1` has `max h² ≥ ½`.
-/

namespace Cvs.Prolate.AngularEndpointLowerBound

open Real Set

/-- The angular energy `Ẽ = h² + (1 − s²)h₁²/c²`. -/
noncomputable def angE (c : ℝ) (g g₁ : ℝ → ℝ) (s : ℝ) : ℝ := g s ^ 2 + (1 - s ^ 2) * g₁ s ^ 2 / c ^ 2

theorem angE_one (c : ℝ) (g g₁ : ℝ → ℝ) : angE c g g₁ 1 = g 1 ^ 2 := by unfold angE; ring

theorem le_angE (c : ℝ) (g g₁ : ℝ → ℝ) {s : ℝ} (hs : s ^ 2 ≤ 1) : g s ^ 2 ≤ angE c g g₁ s := by
  unfold angE
  have : 0 ≤ (1 - s ^ 2) * g₁ s ^ 2 / c ^ 2 := by
    apply div_nonneg _ (sq_nonneg c); exact mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- **The weighted energy increases**: `Ẽ(s) e^{2c arcsin s}` is monotone on `[0, 1]`. -/
theorem monotoneOn_weighted {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    MonotoneOn (fun s => angE c g g₁ s * exp (2 * c * arcsin s)) (Icc 0 1) := by
  have hI : ∀ s ∈ Icc (0 : ℝ) 1, s ∈ uIcc (-1 : ℝ) 1 := fun s hs => by
    rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith [hs.1], hs.2⟩
  have hcont : ContinuousOn (fun s => angE c g g₁ s * exp (2 * c * arcsin s)) (Icc 0 1) := by
    intro s hs
    have h1 := (hg s (hI s hs)).continuousAt
    have h2 := (hg₁ s (hI s hs)).continuousAt
    unfold angE
    exact (((h1.pow 2).add (((continuousAt_const.sub (continuousAt_id.pow 2)).mul (h2.pow 2)).div_const _)).mul
      ((continuous_exp.comp (continuous_const.mul continuous_arcsin)).continuousAt)).continuousWithinAt
  -- the derivative on the interior
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s => angE c g g₁ s * exp (2 * c * arcsin s))
      ((2 * g s * g₁ s + (-(2 * s) * g₁ s ^ 2 + (1 - s ^ 2) * (2 * g₁ s * g₂ s)) / c ^ 2) * exp (2 * c * arcsin s)
        + angE c g g₁ s * (exp (2 * c * arcsin s) * (2 * c * (1 / √(1 - s ^ 2))))) s := by
    intro s hs
    have hs' : s ∈ uIcc (-1 : ℝ) 1 := hI s ⟨hs.1.le, hs.2.le⟩
    have hgs := hg s hs'
    have hg₁s := hg₁ s hs'
    have hE : HasDerivAt (angE c g g₁)
        (2 * g s * g₁ s + (-(2 * s) * g₁ s ^ 2 + (1 - s ^ 2) * (2 * g₁ s * g₂ s)) / c ^ 2) s := by
      unfold angE
      have h1 := hgs.pow 2
      have h2 := ((hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).pow 2)).mul (hg₁s.pow 2)
      have h3 := (h1.add (h2.div_const (c ^ 2)))
      refine h3.congr_deriv ?_
      simp only [id, Pi.sub_apply, Pi.pow_apply]; push_cast; ring
    have harc := hasDerivAt_arcsin (x := s) (by linarith [hs.1]) (by linarith [hs.2])
    have hexp := ((harc.const_mul (2 * c)).exp)
    exact hE.mul hexp |>.congr_deriv (by ring)
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont ?_ ?_
  · rw [interior_Icc]; exact fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro s hs
    rw [(hderiv s hs).deriv]
    have hs' : s ∈ uIcc (-1 : ℝ) 1 := hI s ⟨hs.1.le, hs.2.le⟩
    have hode : (1 - s ^ 2) * g₂ s = 2 * s * g₁ s + (c ^ 2 * s ^ 2 - χ) * g s := by
      have := hang s hs'; linarith
    have hr2 : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    set r := √(1 - s ^ 2) with hrd
    have hr : 0 < r := Real.sqrt_pos.mpr hr2
    have hrr : r ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hr2.le
    have he := exp_pos (2 * c * arcsin s)
    -- the bracket is nonnegative
    set x := g s
    set y := g₁ s
    have hw0 : 0 ≤ c ^ 2 + c ^ 2 * s ^ 2 - χ := by nlinarith [sq_nonneg s]
    have hw1 : c ^ 2 + c ^ 2 * s ^ 2 - χ ≤ 2 * c ^ 2 := by nlinarith [hs.2]
    have hdE : 2 * x * y + (-(2 * s) * y ^ 2 + (1 - s ^ 2) * (2 * y * g₂ s)) / c ^ 2
        = 2 * s * y ^ 2 / c ^ 2 + 2 * x * y * (c ^ 2 + c ^ 2 * s ^ 2 - χ) / c ^ 2 := by
      have : (1 - s ^ 2) * (2 * y * g₂ s) = 2 * y * ((1 - s ^ 2) * g₂ s) := by ring
      rw [this, hode]; field_simp; ring
    have hxy : |x * y| * (c ^ 2 + c ^ 2 * s ^ 2 - χ) ≤ |x * y| * (2 * c ^ 2) :=
      mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)
    have hneg : -(2 * |x * y| * (2 * c ^ 2)) / c ^ 2 ≤ 2 * x * y * (c ^ 2 + c ^ 2 * s ^ 2 - χ) / c ^ 2 := by
      rw [div_le_div_iff_of_pos_right (by positivity)]
      have := neg_abs_le (x * y)
      nlinarith [abs_nonneg (x * y)]
    have hamgm : 4 * |x * y| ≤ angE c g g₁ s * (2 * c * (1 / r)) := by
      unfold angE
      rw [← hrr]
      have hsq : 2 * r * c * |x * y| ≤ c ^ 2 * x ^ 2 + r ^ 2 * y ^ 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (c * |x| - r * |y|), sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]
      rw [show (x ^ 2 + r ^ 2 * y ^ 2 / c ^ 2) * (2 * c * (1 / r)) = 2 * (c ^ 2 * x ^ 2 + r ^ 2 * y ^ 2) / (c * r) by
        field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hsy : 0 ≤ 2 * s * y ^ 2 / c ^ 2 := by have := hs.1; positivity
    have hc4 : -(2 * |x * y| * (2 * c ^ 2)) / c ^ 2 = -(4 * |x * y|) := by field_simp; ring
    have hbr : 0 ≤ 2 * x * y + (-(2 * s) * y ^ 2 + (1 - s ^ 2) * (2 * y * g₂ s)) / c ^ 2
        + angE c g g₁ s * (2 * c * (1 / r)) := by
      rw [hdE]; linarith
    have := mul_nonneg hbr he.le
    nlinarith [this]

/-- **The endpoint lower bound**: an even `h` with `∫_{−1}^{1} h² = 1` solving the angular equation with
`0 ≤ χ ≤ c²`, `c > 0`, has `h(1)² ≥ ½ e^{−πc}`. -/
theorem endpoint_sq_ge {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1) :
    1 / 2 * exp (-(π * c)) ≤ g 1 ^ 2 := by
  have hgc : ContinuousOn g (Icc (-1) 1) := fun s hs =>
    (hg s (by rw [uIcc_of_le (by norm_num)]; exact hs)).continuousAt.continuousWithinAt
  -- a point of `[0, 1]` with `g² ≥ ½`
  obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1))
    (hgc.pow 2)
  have hint : ∫ s in (-1 : ℝ)..1, g s ^ 2 ≤ ∫ s in (-1 : ℝ)..1, g s₀ ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num) ((hgc.pow 2).intervalIntegrable_of_Icc (by norm_num))
      intervalIntegrable_const fun s hs => hmax hs
  rw [hnorm, intervalIntegral.integral_const, smul_eq_mul] at hint
  have hhalf : 1 / 2 ≤ g s₀ ^ 2 := by norm_num at hint; linarith
  set t := |s₀| with htd
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨abs_nonneg _, abs_le.mpr ⟨hs₀.1, hs₀.2⟩⟩
  have hgt : g t = g s₀ := by
    rcases le_or_gt 0 s₀ with h | h
    · rw [htd, abs_of_nonneg h]
    · rw [htd, abs_of_neg h, heven s₀ hs₀]
  -- monotonicity from `t` to `1`
  have hmono := monotoneOn_weighted hc hχ0 hχ hg hg₁ hang ht ⟨by norm_num, le_rfl⟩ ht.2
  simp only [arcsin_one] at hmono
  have hEt : g t ^ 2 ≤ angE c g g₁ t := le_angE c g g₁ (by nlinarith [ht.1, ht.2])
  have harc : 0 ≤ arcsin t := arcsin_nonneg.mpr ht.1
  have h1 : g t ^ 2 * 1 ≤ angE c g g₁ t * exp (2 * c * arcsin t) := by
    refine mul_le_mul hEt (one_le_exp (by positivity)) (by norm_num) ?_
    exact le_trans (sq_nonneg _) hEt
  rw [angE_one] at hmono
  have h2 : g t ^ 2 ≤ g 1 ^ 2 * exp (2 * c * (π / 2)) := by linarith
  have h3 : g t ^ 2 * exp (-(π * c)) ≤ g 1 ^ 2 := by
    have := mul_le_mul_of_nonneg_right h2 (exp_pos (-(π * c))).le
    rw [mul_assoc, ← exp_add, show 2 * c * (π / 2) + -(π * c) = 0 by ring, exp_zero, mul_one] at this
    exact this
  rw [hgt] at h3
  have := mul_le_mul_of_nonneg_right hhalf (exp_pos (-(π * c))).le
  linarith

end Cvs.Prolate.AngularEndpointLowerBound
