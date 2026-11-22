import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trapezoid step for a holomorphic function along a horizontal segment

If `F′ = f`, `f′ = f₁`, `f₁′ = f₂` on `[u, u + 2]` and `‖f₂‖ ≤ M` there, then
`‖F(u + 2) − F(u) − (f(u) + f(u + 2))‖ ≤ 4M`.
-/

noncomputable section

open Set

namespace Cvs.Upstream.HolomorphicTrapezoidStep

/-- Shifted restriction to the real parameter. -/
theorem hasDerivAt_shift {G g : ℂ → ℂ} {u : ℂ} {t : ℝ} (h : HasDerivAt G (g (u + t)) (u + t)) :
    HasDerivAt (fun r : ℝ => G (u + r)) (g (u + t)) t := by
  have h1 : HasDerivAt (fun x : ℂ => u + x) 1 (t : ℂ) := (hasDerivAt_id _).const_add u
  have h2 := (h.comp (t : ℂ) h1)
  rw [mul_one] at h2
  exact h2.comp_ofReal

/-- A first-order bound from a derivative bound. -/
theorem norm_sub_le_of_deriv {f₁ f₂ : ℂ → ℂ} {u : ℂ} {M : ℝ}
    (hf1 : ∀ t ∈ Icc (0 : ℝ) 2, HasDerivAt f₁ (f₂ (u + t)) (u + t))
    (hM : ∀ t ∈ Icc (0 : ℝ) 2, ‖f₂ (u + t)‖ ≤ M) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 2) (hb : b ∈ Icc (0 : ℝ) 2)
    (hab : a ≤ b) : ‖f₁ (u + b) - f₁ (u + a)‖ ≤ M * (b - a) := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r : ℝ => f₁ (u + r)) (f' := fun r => f₂ (u + r))
    (a := a) (b := b) (C := M)
    (fun x hx => (hasDerivAt_shift (hf1 x ⟨by linarith [hx.1, ha.1], by linarith [hx.2, hb.2]⟩)).hasDerivWithinAt)
    (fun x hx => hM x ⟨by linarith [hx.1, ha.1], by linarith [hx.2, hb.2]⟩) b ⟨hab, le_rfl⟩
  simpa using this

/-- **The trapezoid step.** -/
theorem norm_trapezoid_le {F f f₁ f₂ : ℂ → ℂ} {u : ℂ} {M : ℝ}
    (hF : ∀ t ∈ Icc (0 : ℝ) 2, HasDerivAt F (f (u + t)) (u + t))
    (hf : ∀ t ∈ Icc (0 : ℝ) 2, HasDerivAt f (f₁ (u + t)) (u + t))
    (hf1 : ∀ t ∈ Icc (0 : ℝ) 2, HasDerivAt f₁ (f₂ (u + t)) (u + t))
    (hM : ∀ t ∈ Icc (0 : ℝ) 2, ‖f₂ (u + t)‖ ≤ M) :
    ‖F (u + 2) - F u - (f u + f (u + 2))‖ ≤ 4 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, by norm_num⟩)
  -- φ(t) = F(u+t) − F(u) − (t/2)(f(u) + f(u+t))
  set φ : ℝ → ℂ := fun t => F (u + t) - F u - (t / 2 : ℂ) * (f u + f (u + t))
  set φ' : ℝ → ℂ := fun t => f (u + t) - (1 / 2 : ℂ) * (f u + f (u + t)) - (t / 2 : ℂ) * f₁ (u + t)
  have hφ : ∀ t ∈ Icc (0 : ℝ) 2, HasDerivAt φ (φ' t) t := by
    intro t ht
    have h1 := hasDerivAt_shift (hF t ht)
    have h2 := hasDerivAt_shift (hf t ht)
    have h3 : HasDerivAt (fun r : ℝ => ((r : ℂ) / 2)) (1 / 2 : ℂ) t := by
      have := (Complex.ofRealCLM.hasDerivAt (x := t)).div_const (2 : ℂ)
      simpa using this
    have h4 := (h1.sub_const (F u)).sub (h3.mul (h2.const_add (f u)))
    refine h4.congr_deriv ?_
    simp only [φ']; ring
  -- the derivative bound
  have hφ' : ∀ t ∈ Ico (0 : ℝ) 2, ‖φ' t‖ ≤ 2 * M := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 2 := Ico_subset_Icc_self ht
    -- χ(r) = f(u+r) − r f₁(u+t) on [0, t]
    have hχ := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r : ℝ => f (u + r) - (r : ℂ) * f₁ (u + t))
      (f' := fun r => f₁ (u + r) - f₁ (u + t)) (a := 0) (b := t) (C := 2 * M)
      (fun r hr => by
        have hr' : r ∈ Icc (0 : ℝ) 2 := ⟨hr.1, by linarith [hr.2, htI.2]⟩
        have h1 := hasDerivAt_shift (hf r hr')
        have h2 : HasDerivAt (fun x : ℝ => (x : ℂ) * f₁ (u + t)) (1 * f₁ (u + t)) r :=
          (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const _
        exact ((h1.sub h2).congr_deriv (by ring)).hasDerivWithinAt)
      (fun r hr => by
        have hr' : r ∈ Icc (0 : ℝ) 2 := ⟨hr.1, by linarith [hr.2, htI.2]⟩
        have := norm_sub_le_of_deriv hf1 hM hr' htI hr.2.le
        rw [norm_sub_rev]
        calc _ ≤ M * (t - r) := this
          _ ≤ 2 * M := by nlinarith [hr.1, htI.2])
      t ⟨ht.1, le_rfl⟩
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero] at hχ
    have e : φ' t = (1 / 2 : ℂ) * (f (u + t) - (t : ℂ) * f₁ (u + t) - f u) := by
      simp only [φ']; ring
    rw [e, norm_mul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    nlinarith [ht.1, ht.2, norm_nonneg (f (u + t) - (t : ℂ) * f₁ (u + t) - f u)]
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) (f' := φ') (a := 0) (b := 2) (C := 2 * M)
    (fun t ht => (hφ t ht).hasDerivWithinAt) hφ' 2 ⟨by norm_num, le_rfl⟩
  have e2 : φ 2 - φ 0 = F (u + 2) - F u - (f u + f (u + 2)) := by
    simp only [φ]; push_cast; simp
  rw [e2] at this
  linarith

end Cvs.Upstream.HolomorphicTrapezoidStep
