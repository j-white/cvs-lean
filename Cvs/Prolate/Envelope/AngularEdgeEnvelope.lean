import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The envelope: an even angular prolate is at most `√2·e^{5s/2}` times its edge value
With `s = (c² − χ)/c ≤ 3c/8`, three energies cover `[0, 1]`: `g² + (1 − x²)g'²/(c² − χ)` grows by at most
`e^{4s}` from the edge across the forbidden zone, `g² + g'²/c²` by at most `e^s` across the turning zone, and
Sonin's function is nondecreasing on the inner zone. So `g² ≤ 2e^{5s}g(1)²`; with `ψ = μg` on `[−1, 1]` and Cvs.Prolate.LiouvilleGreen.SoninFunction
outside, `|ψ| ≤ √2·e^{5s/2}|ψ(1)|` everywhere, and `|ψ| ≤ K_A|ψ(1)|` on the band `s < 10`.
-/

namespace Cvs.Prolate.Envelope.AngularEdgeEnvelope

open Real Set Cvs.L2a.AngularProlateTailPositive

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- A point of `[−1, 1]` lies in `uIcc (−1) 1`. -/
theorem mem_uIcc_of_mem_Icc {x : ℝ} (h0 : -1 ≤ x) (h1 : x ≤ 1) : x ∈ uIcc (-1 : ℝ) 1 := by
  rw [uIcc_of_le (by norm_num)]; exact ⟨h0, h1⟩

/-- **The forbidden zone.** Where `c²(1 − x²) ≤ σ² = c² − χ`, the energy `g² + (1 − x²)g'²/σ²` is at most
`e^{4σ√(1−a)}g(1)²` on `[a, 1]`. -/
theorem forbidden_le {σ a : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hσ : 0 < σ) (hσ2 : σ ^ 2 = c ^ 2 - χ) (ha0 : 0 ≤ a) (ha : c ^ 2 * (1 - a ^ 2) ≤ σ ^ 2) :
    ∀ x ∈ Icc a 1, g x ^ 2 + (1 - x ^ 2) * g₁ x ^ 2 / σ ^ 2 ≤ g 1 ^ 2 * exp (4 * σ * √(1 - a)) := by
  have mem : ∀ x ∈ Icc a 1, x ∈ uIcc (-1 : ℝ) 1 := fun x hx => mem_uIcc_of_mem_Icc (by linarith [hx.1]) hx.2
  have hEd : ∀ x ∈ Icc a 1, HasDerivAt (fun x => g x ^ 2 + (1 - x ^ 2) * g₁ x ^ 2 / σ ^ 2)
      (2 * g x * g₁ x + (-(2 * x) * g₁ x ^ 2 + (1 - x ^ 2) * (2 * g₁ x * g₂ x)) / σ ^ 2) x := by
    intro x hx
    have h1 := (hg x (mem x hx)).pow 2
    have h2 := (hg₁ x (mem x hx)).pow 2
    have h3 := ((hasDerivAt_pow 2 x).const_sub 1).mul h2
    have h4 := h1.add (h3.div_const (σ ^ 2))
    refine h4.congr_deriv ?_
    simp only [Pi.pow_apply]; push_cast; ring
  have hcont : ContinuousOn (fun x => (g x ^ 2 + (1 - x ^ 2) * g₁ x ^ 2 / σ ^ 2) * exp (-(4 * σ * √(1 - x))))
      (Icc a 1) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    exact (hEd x hx).continuousAt.mul (by fun_prop)
  have hmono : MonotoneOn (fun x => (g x ^ 2 + (1 - x ^ 2) * g₁ x ^ 2 / σ ^ 2) * exp (-(4 * σ * √(1 - x))))
      (Icc a 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a 1) hcont
    · rw [interior_Icc]; intro x hx
      have hx' := Ioo_subset_Icc_self hx
      have hr : 1 - x ≠ 0 := by linarith [hx.2]
      have hW : HasDerivAt (fun y => exp (-(4 * σ * √(1 - y))))
          (exp (-(4 * σ * √(1 - x))) * -(4 * σ * (-1 / (2 * √(1 - x))))) x :=
        ((((hasDerivAt_id' x).const_sub 1).sqrt hr).const_mul (4 * σ)).neg.exp
      exact ((hEd x hx').mul hW).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      have hx' := Ioo_subset_Icc_self hx
      have hr : 1 - x ≠ 0 := by linarith [hx.2]
      have hW : HasDerivAt (fun y => exp (-(4 * σ * √(1 - y))))
          (exp (-(4 * σ * √(1 - x))) * -(4 * σ * (-1 / (2 * √(1 - x))))) x :=
        ((((hasDerivAt_id' x).const_sub 1).sqrt hr).const_mul (4 * σ)).neg.exp
      have hFd : HasDerivAt (fun x => (g x ^ 2 + (1 - x ^ 2) * g₁ x ^ 2 / σ ^ 2) * exp (-(4 * σ * √(1 - x))))
          ((2 * g x * g₁ x + (-(2 * x) * g₁ x ^ 2 + (1 - x ^ 2) * (2 * g₁ x * g₂ x)) / σ ^ 2)
            * exp (-(4 * σ * √(1 - x)))
            + (g x ^ 2 + (1 - x ^ 2) * g₁ x ^ 2 / σ ^ 2)
              * (exp (-(4 * σ * √(1 - x))) * -(4 * σ * (-1 / (2 * √(1 - x)))))) x :=
        (hEd x hx').mul hW
      rw [hFd.deriv]
      have hr0 : 0 < √(1 - x) := Real.sqrt_pos.mpr (by linarith [hx.2])
      have hr2 : √(1 - x) ^ 2 = 1 - x := Real.sq_sqrt (by linarith [hx.2])
      have hW0 : 0 < exp (-(4 * σ * √(1 - x))) := exp_pos _
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have hode := hang x (mem x hx')
      generalize √(1 - x) = r at hr0 hr2 hW0 ⊢
      generalize exp (-(4 * σ * r)) = W at hW0 ⊢
      generalize g x = G at hode ⊢
      generalize g₁ x = G1 at hode ⊢
      generalize g₂ x = G2 at hode ⊢
      have hp : r ^ 2 ≤ 1 - x ^ 2 := by nlinarith
      have hca : c ^ 2 * (1 - x ^ 2) ≤ c ^ 2 * (1 - a ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg c); nlinarith [hx.1]
      have hcx : 0 ≤ c ^ 2 * (1 - x ^ 2) := by
        apply mul_nonneg (sq_nonneg c); nlinarith [hx.2]
      have hA1 : 0 ≤ 2 * σ ^ 2 + (σ ^ 2 + c ^ 2 * x ^ 2 - χ) := by nlinarith
      have hA2 : 0 ≤ 2 * σ ^ 2 - (σ ^ 2 + c ^ 2 * x ^ 2 - χ) := by nlinarith
      have hnum : 0 ≤ (2 * G * G1 * (σ ^ 2 + c ^ 2 * x ^ 2 - χ) + 2 * x * G1 ^ 2) * r
          + 2 * σ * (σ ^ 2 * G ^ 2 + (1 - x ^ 2) * G1 ^ 2) := by
        have k1 := mul_nonneg hA1 (sq_nonneg (σ * G + r * G1))
        have k2 := mul_nonneg hA2 (sq_nonneg (σ * G - r * G1))
        have k3 : 0 ≤ σ * (2 * σ * ((1 - x ^ 2) - r ^ 2) * G1 ^ 2 + 2 * x * r * G1 ^ 2) := by
          have : 0 ≤ (1 - x ^ 2) - r ^ 2 := by linarith
          positivity
        have h : 0 ≤ σ * ((2 * G * G1 * (σ ^ 2 + c ^ 2 * x ^ 2 - χ) + 2 * x * G1 ^ 2) * r
            + 2 * σ * (σ ^ 2 * G ^ 2 + (1 - x ^ 2) * G1 ^ 2)) := by nlinarith
        exact (mul_nonneg_iff_of_pos_left hσ).mp h
      have hpG2 : (1 - x ^ 2) * G2 = 2 * x * G1 + c ^ 2 * x ^ 2 * G - χ * G := by linarith
      have hE' : 2 * G * G1 + (-(2 * x) * G1 ^ 2 + (1 - x ^ 2) * (2 * G1 * G2)) / σ ^ 2
          = (2 * G * G1 * (σ ^ 2 + c ^ 2 * x ^ 2 - χ) + 2 * x * G1 ^ 2) / σ ^ 2 := by
        rw [show (1 - x ^ 2) * (2 * G1 * G2) = 2 * G1 * ((1 - x ^ 2) * G2) by ring, hpG2]
        field_simp; ring
      rw [hE']
      have : (2 * G * G1 * (σ ^ 2 + c ^ 2 * x ^ 2 - χ) + 2 * x * G1 ^ 2) / σ ^ 2 * W
          + (G ^ 2 + (1 - x ^ 2) * G1 ^ 2 / σ ^ 2) * (W * -(4 * σ * (-1 / (2 * r))))
          = W * ((2 * G * G1 * (σ ^ 2 + c ^ 2 * x ^ 2 - χ) + 2 * x * G1 ^ 2) * r
            + 2 * σ * (σ ^ 2 * G ^ 2 + (1 - x ^ 2) * G1 ^ 2)) / (σ ^ 2 * r) := by
        field_simp; ring
      rw [this]
      positivity
  intro x hx
  have h := hmono hx (right_mem_Icc.mpr (hx.1.trans hx.2)) hx.2
  simp only [one_pow, sub_self, zero_mul, zero_div, add_zero, Real.sqrt_zero, mul_zero, neg_zero,
    exp_zero, mul_one] at h
  have hu := exp_pos (4 * σ * √(1 - x))
  have h2 : g x ^ 2 + (1 - x ^ 2) * g₁ x ^ 2 / σ ^ 2 ≤ g 1 ^ 2 * exp (4 * σ * √(1 - x)) := by
    have := mul_le_mul_of_nonneg_right h hu.le
    rwa [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one] at this
  have h3 : exp (4 * σ * √(1 - x)) ≤ exp (4 * σ * √(1 - a)) := by
    apply exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact Real.sqrt_le_sqrt (by linarith [hx.1])
  exact h2.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))

/-- **The turning zone.** Where `c²(1 − x²) ≥ c² − χ ≥ 0`, the energy `g² + g'²/c²` grows by at most
`e^{c(a − b)}` from `a` down to `b`. -/
theorem turning_le {a b : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχc : χ ≤ c ^ 2) (hb0 : 0 ≤ b) (ha1 : a < 1) (ha : c ^ 2 - χ ≤ c ^ 2 * (1 - a ^ 2)) :
    ∀ x ∈ Icc b a, g x ^ 2 + g₁ x ^ 2 / c ^ 2 ≤ (g a ^ 2 + g₁ a ^ 2 / c ^ 2) * exp (c * (a - b)) := by
  have mem : ∀ x ∈ Icc b a, x ∈ uIcc (-1 : ℝ) 1 :=
    fun x hx => mem_uIcc_of_mem_Icc (by linarith [hx.1]) (by linarith [hx.2])
  have hFd : ∀ x ∈ Icc b a, HasDerivAt (fun x => (g x ^ 2 + g₁ x ^ 2 / c ^ 2) * exp (c * x))
      ((2 * g x * g₁ x + 2 * g₁ x * g₂ x / c ^ 2) * exp (c * x)
        + (g x ^ 2 + g₁ x ^ 2 / c ^ 2) * (exp (c * x) * c)) x := by
    intro x hx
    have h1 := (hg x (mem x hx)).pow 2
    have h2 := (hg₁ x (mem x hx)).pow 2
    have h4 := (h1.add (h2.div_const (c ^ 2))).mul ((hasDerivAt_id' x).const_mul c).exp
    refine (h4.congr_deriv ?_)
    simp only [Pi.pow_apply, Pi.add_apply]; push_cast; ring
  have hmono : MonotoneOn (fun x => (g x ^ 2 + g₁ x ^ 2 / c ^ 2) * exp (c * x)) (Icc b a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc b a)
      (fun x hx => (hFd x hx).continuousAt.continuousWithinAt)
    · rw [interior_Icc]; intro x hx
      exact (hFd x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      have hx' := Ioo_subset_Icc_self hx
      rw [(hFd x hx').deriv]
      have hode := hang x (mem x hx')
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.2]
      have hca : c ^ 2 * (1 - a ^ 2) ≤ c ^ 2 * (1 - x ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg c); nlinarith [hx.2]
      have hW0 := exp_pos (c * x)
      generalize exp (c * x) = W at hW0 ⊢
      generalize g x = G at hode ⊢
      generalize g₁ x = G1 at hode ⊢
      generalize g₂ x = G2 at hode ⊢
      have hpG2 : (1 - x ^ 2) * G2 = 2 * x * G1 + c ^ 2 * x ^ 2 * G - χ * G := by linarith
      have hnum : 0 ≤ c * (2 * (c ^ 2 - χ) * G * G1 + 4 * x * G1 ^ 2
          + (1 - x ^ 2) * c * (c ^ 2 * G ^ 2 + G1 ^ 2)) := by
        have k1 := mul_nonneg (by linarith : 0 ≤ c ^ 2 * (1 - x ^ 2) - (c ^ 2 - χ))
          (by positivity : 0 ≤ c ^ 2 * G ^ 2 + G1 ^ 2)
        have k2 := mul_nonneg (by linarith : 0 ≤ c ^ 2 - χ) (sq_nonneg (c * G + G1))
        have k3 : 0 ≤ c * (4 * x * G1 ^ 2) := by positivity
        nlinarith
      have hnum' := (mul_nonneg_iff_of_pos_left hc).mp hnum
      have : (2 * G * G1 + 2 * G1 * G2 / c ^ 2) * W + (G ^ 2 + G1 ^ 2 / c ^ 2) * (W * c)
          = W * (2 * (c ^ 2 - χ) * G * G1 + 4 * x * G1 ^ 2
            + (1 - x ^ 2) * c * (c ^ 2 * G ^ 2 + G1 ^ 2)) / ((1 - x ^ 2) * c ^ 2) := by
        rw [show 2 * G1 * G2 = 2 * G1 * ((1 - x ^ 2) * G2) / (1 - x ^ 2) by field_simp, hpG2]
        field_simp; ring
      rw [this]
      positivity
  intro x hx
  have h := hmono hx (right_mem_Icc.mpr (hx.1.trans hx.2)) hx.2
  have hu := exp_pos (c * x)
  simp only at h
  have h2 : g x ^ 2 + g₁ x ^ 2 / c ^ 2 ≤ (g a ^ 2 + g₁ a ^ 2 / c ^ 2) * exp (c * (a - x)) := by
    rw [mul_sub, exp_sub, ← mul_div_assoc, le_div_iff₀ hu]; exact h
  have h3 : exp (c * (a - x)) ≤ exp (c * (a - b)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hx.1]) hc.le)
  exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))

/-- **The inner zone.** Where `χ − c²x² > 0` and `χ + c² − 2c²x² ≥ 0`, Sonin's function
`g² + (1 − x²)g'²/(χ − c²x²)` is nondecreasing, so `g(x)²` is at most its value at `b`. -/
theorem inner_le {b : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hb1 : b ≤ 1) (hq : 0 < χ - c ^ 2 * b ^ 2) (hpq : 0 ≤ χ + c ^ 2 - 2 * c ^ 2 * b ^ 2) :
    ∀ x ∈ Icc 0 b, g x ^ 2 ≤ g b ^ 2 + (1 - b ^ 2) * g₁ b ^ 2 / (χ - c ^ 2 * b ^ 2) := by
  have mem : ∀ x ∈ Icc 0 b, x ∈ uIcc (-1 : ℝ) 1 :=
    fun x hx => mem_uIcc_of_mem_Icc (by linarith [hx.1]) (by linarith [hx.2])
  have hqx : ∀ x ∈ Icc 0 b, 0 < χ - c ^ 2 * x ^ 2 := fun x hx => by
    have : c ^ 2 * x ^ 2 ≤ c ^ 2 * b ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 2) (sq_nonneg c)
    linarith
  have hd : ∀ x ∈ Icc 0 b, HasDerivAt (Cvs.Prolate.LiouvilleGreen.SoninFunction.sonin g g₁ (fun r => 1 - r ^ 2)
      (fun r => χ - c ^ 2 * r ^ 2))
      (-(g₁ x ^ 2 * (-(2 * x) * (χ - c ^ 2 * x ^ 2) + (1 - x ^ 2) * -(2 * c ^ 2 * x)))
        / (χ - c ^ 2 * x ^ 2) ^ 2) x := by
    intro x hx
    apply Cvs.Prolate.LiouvilleGreen.SoninFunction.hasDerivAt_sonin (ψ := g) (v := g₁) (v' := g₂) (p := fun r => 1 - r ^ 2)
      (p' := fun r => -(2 * r)) (q := fun r => χ - c ^ 2 * r ^ 2) (q' := fun r => -(2 * c ^ 2 * r)) (t := x)
      (hqx x hx).ne' (hg x (mem x hx)) (hg₁ x (mem x hx))
    · simpa using (hasDerivAt_pow 2 x).const_sub 1
    · have := ((hasDerivAt_pow 2 x).const_mul (c ^ 2)).const_sub χ
      exact this.congr_deriv (by push_cast; ring)
    · have := hang x (mem x hx); linarith
  have hmono : MonotoneOn (Cvs.Prolate.LiouvilleGreen.SoninFunction.sonin g g₁ (fun r => 1 - r ^ 2)
      (fun r => χ - c ^ 2 * r ^ 2)) (Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    · rw [interior_Icc]; intro x hx
      exact (hd x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      have hx' := Ioo_subset_Icc_self hx
      rw [(hd x hx').deriv]
      apply div_nonneg _ (sq_nonneg _)
      have hx2 : c ^ 2 * x ^ 2 ≤ c ^ 2 * b ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx'.1 hx'.2 2) (sq_nonneg c)
      have : 0 ≤ x * (χ + c ^ 2 - 2 * c ^ 2 * x ^ 2) := mul_nonneg hx'.1 (by linarith)
      have := mul_nonneg (sq_nonneg (g₁ x)) this
      nlinarith
  intro x hx
  have h := hmono hx (right_mem_Icc.mpr (hx.1.trans hx.2)) hx.2
  unfold Cvs.Prolate.LiouvilleGreen.SoninFunction.sonin at h
  have : 0 ≤ (1 - x ^ 2) * g₁ x ^ 2 / (χ - c ^ 2 * x ^ 2) := by
    have := hqx x hx
    have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    positivity
  linarith

/-- **The angular envelope.** For an even solution of the angular equation with `0 ≤ χ < c²` and
`8(c² − χ) ≤ 3c²`, `g(t)² ≤ 2e^{5s}g(1)²` on `[−1, 1]`, `s = (c² − χ)/c`. -/
theorem angular_sq_le_edge
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hσ : χ < c ^ 2) (hs : 8 * (c ^ 2 - χ) ≤ 3 * c ^ 2) :
    ∀ t ∈ Icc (-1 : ℝ) 1, g t ^ 2 ≤ 2 * exp (5 * (c ^ 2 - χ) / c) * g 1 ^ 2 := by
  have _ := hg₂c
  set sv := (c ^ 2 - χ) / c with hsv
  have hsv0 : 0 ≤ sv := by rw [hsv]; exact div_nonneg (by linarith) hc.le
  have hc2 : 0 < c ^ 2 := by positivity
  -- the three cut points
  set σ := √(c ^ 2 - χ) with hσdef
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr (by linarith)
  have hσ2 : σ ^ 2 = c ^ 2 - χ := Real.sq_sqrt (by linarith)
  set a := √χ / c with hadef
  have ha0 : 0 ≤ a := by positivity
  have ha2 : c ^ 2 * a ^ 2 = χ := by
    rw [hadef, div_pow, Real.sq_sqrt hχ]; field_simp
  have ha1 : a < 1 := by
    by_contra! h
    have h1 : 1 ≤ a ^ 2 := one_le_pow₀ h
    nlinarith [mul_le_mul_of_nonneg_left h1 hc2.le]
  have h2χ : 0 ≤ 2 * χ - c ^ 2 := by nlinarith
  set b := √(2 * χ - c ^ 2) / c with hbdef
  have hb0 : 0 ≤ b := by positivity
  have hb2 : c ^ 2 * b ^ 2 = 2 * χ - c ^ 2 := by
    rw [hbdef, div_pow, Real.sq_sqrt h2χ]; field_simp
  have hbh : 1 / 2 ≤ b := by
    by_contra! h
    have h1 : b ^ 2 < 1 / 4 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h1 hc2]
  have hba : b ≤ a := by
    by_contra! h
    have h1 : a ^ 2 < b ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h1 hc2]
  -- the three zones
  have hZ1 := forbidden_le hg hg₁ hang hσ0 hσ2 ha0 (by nlinarith)
  have hZ2 := turning_le hg hg₁ hang hc hσ.le hb0 ha1 (by nlinarith)
  have hZ3 := inner_le hg hg₁ hang (by linarith) (by nlinarith) (by nlinarith)
  -- the exponents
  have hexp1 : 4 * σ * √(1 - a) ≤ 4 * sv := by
    have hsq : √(1 - a) ≤ σ / c := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ σ / c)]
      apply Real.sqrt_le_sqrt
      rw [div_pow, hσ2, le_div_iff₀ hc2]; nlinarith
    calc 4 * σ * √(1 - a) ≤ 4 * σ * (σ / c) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 4 * sv := by rw [hsv, ← hσ2]; ring
  have hexp2 : c * (a - b) ≤ sv := by
    rw [hsv, le_div_iff₀ hc]
    have : (a - b) * c ^ 2 ≤ c ^ 2 - χ := by nlinarith
    nlinarith
  set A1 := g 1 ^ 2 * exp (4 * sv) with hA1
  have hA10 : 0 ≤ A1 := by positivity
  have hHa : g a ^ 2 + g₁ a ^ 2 / c ^ 2 ≤ A1 := by
    have h := hZ1 a ⟨le_rfl, ha1.le⟩
    have he : (1 - a ^ 2) * g₁ a ^ 2 / σ ^ 2 = g₁ a ^ 2 / c ^ 2 := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; linear_combination (-(g₁ a ^ 2)) * (ha2 + hσ2)
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp1) (sq_nonneg _))
  have hes : 1 ≤ exp sv := one_le_exp hsv0
  have hgoal : 2 * exp (5 * (c ^ 2 - χ) / c) * g 1 ^ 2 = 2 * (A1 * exp sv) := by
    rw [show 5 * (c ^ 2 - χ) / c = 4 * sv + sv by rw [hsv]; ring, exp_add, hA1]; ring
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, g t ^ 2 ≤ 2 * (A1 * exp sv) := by
    intro t ht
    rcases le_or_gt t b with htb | htb
    · have h := hZ3 t ⟨ht.1, htb⟩
      have he : (1 - b ^ 2) * g₁ b ^ 2 / (χ - c ^ 2 * b ^ 2) = 2 * g₁ b ^ 2 / c ^ 2 := by
        rw [div_eq_div_iff (by nlinarith) (by positivity)]; linear_combination (g₁ b ^ 2) * hb2
      rw [he] at h
      have h2 := hZ2 b ⟨le_rfl, hba⟩
      have h3 : (g a ^ 2 + g₁ a ^ 2 / c ^ 2) * exp (c * (a - b)) ≤ A1 * exp sv :=
        mul_le_mul hHa (exp_le_exp.mpr hexp2) (exp_pos _).le hA10
      have : 0 ≤ g b ^ 2 := sq_nonneg _
      have : 2 * g₁ b ^ 2 / c ^ 2 = 2 * (g₁ b ^ 2 / c ^ 2) := by ring
      linarith
    rcases le_or_gt t a with hta | hta
    · have h2 := hZ2 t ⟨htb.le, hta⟩
      have h3 : (g a ^ 2 + g₁ a ^ 2 / c ^ 2) * exp (c * (a - b)) ≤ A1 * exp sv :=
        mul_le_mul hHa (exp_le_exp.mpr hexp2) (exp_pos _).le hA10
      have : 0 ≤ g₁ t ^ 2 / c ^ 2 := by positivity
      have : 0 ≤ A1 * exp sv := by positivity
      linarith
    · have h := hZ1 t ⟨hta.le, ht.2⟩
      have : 0 ≤ (1 - t ^ 2) * g₁ t ^ 2 / σ ^ 2 := by
        have : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
        positivity
      have h4 : g 1 ^ 2 * exp (4 * σ * √(1 - a)) ≤ A1 :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp1) (sq_nonneg _)
      have : A1 ≤ A1 * exp sv := le_mul_of_one_le_right hA10 hes
      linarith
  intro t ht
  rw [hgoal]
  rcases le_or_gt 0 t with h0 | h0
  · exact hpos t ⟨h0, ht.2⟩
  · have hm : -t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith [ht.1]⟩
    have he : g t = g (-t) := by rw [← heven (-t) hm, neg_neg]
    have h2 := hpos (-t) ⟨by linarith, hm.2⟩
    rw [he]; exact h2

/-- The cosine transform is even. -/
theorem psi_neg (c : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : psi c g (-ξ) = psi c g ξ := by
  simp only [psi, Cvs.Prolate.SlepianCommutingRelation.kint]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [show c * -ξ * s = -(c * ξ * s) by ring, cos_neg]

/-- **The envelope.** With `ψ = μg` on `[−1, 1]`, `|ψ(t)| ≤ √2·e^{5s/2}|ψ(1)|` for every real `t`. -/
theorem abs_psi_le_edge {μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hσ : χ < c ^ 2) (hs : 8 * (c ^ 2 - χ) ≤ 3 * c ^ 2)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    ∀ t : ℝ, |psi c g t| ≤ √2 * exp (5 * (c ^ 2 - χ) / (2 * c)) * |psi c g 1| := by
  set K := √2 * exp (5 * (c ^ 2 - χ) / (2 * c)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have h2 : 1 ≤ exp (5 * (c ^ 2 - χ) / (2 * c)) := one_le_exp (div_nonneg (by linarith) (by linarith))
    nlinarith
  have hKsq : K ^ 2 = 2 * exp (5 * (c ^ 2 - χ) / c) := by
    rw [hK, mul_pow, Real.sq_sqrt (by norm_num), ← exp_nat_mul]
    congr 2; field_simp; ring
  have hout : ∀ t, 1 ≤ t → |psi c g t| ≤ K * |psi c g 1| := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := psi_system hg hg₁ hg₂c hang
    have h := Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge (ξ₁ := t) (ξ := t) hσ ⟨ht, le_rfl⟩
      (fun r _ => h1 r) (fun r _ => h2 r) (fun r _ => h3 r)
    have := sq_le_sq.mp h
    nlinarith [abs_nonneg (psi c g 1)]
  intro t
  rcases le_or_gt 1 t with ht | ht
  · exact hout t ht
  rcases le_or_gt t (-1) with ht' | ht'
  · rw [← psi_neg]; exact hout (-t) (by linarith)
  have htI : t ∈ Icc (-1 : ℝ) 1 := ⟨ht'.le, ht.le⟩
  have hgt := angular_sq_le_edge hg hg₁ hg₂c hang heven hc hχ hσ hs t htI
  rw [← hKsq, ← mul_pow] at hgt
  have hab := sq_le_sq.mp hgt
  rw [abs_mul, abs_of_nonneg hK0] at hab
  rw [hμ t htI, hμ 1 ⟨by norm_num, le_rfl⟩, abs_mul, abs_mul]
  calc |μ| * |g t| ≤ |μ| * (K * |g 1|) := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    _ = K * (|μ| * |g 1|) := by ring

/-- The envelope constant on the band `c² − χ < 10c`, `K_A = √2·e^{25}`. -/
noncomputable def KA : ℝ := √2 * exp 25

/-- `K_A ≥ 1`. -/
theorem one_le_KA : 1 ≤ KA := by
  have h1 : 1 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h2 : 1 ≤ exp (25 : ℝ) := one_le_exp (by norm_num)
  unfold KA; nlinarith

/-- **The envelope on the band.** For `c ≥ 80` and `c² − χ < 10c`, `|ψ(t)| ≤ K_A|ψ(1)|` for every real `t`. -/
theorem abs_psi_le_band {μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hχ : 0 ≤ χ) (hσ : χ < c ^ 2)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hc : 80 ≤ c) (hband : c ^ 2 - χ < 10 * c) :
    ∀ t : ℝ, |psi c g t| ≤ KA * |psi c g 1| := by
  have hc0 : 0 < c := by linarith
  have hs : 8 * (c ^ 2 - χ) ≤ 3 * c ^ 2 := by nlinarith
  intro t
  have h := abs_psi_le_edge hg hg₁ hg₂c hang heven hc0 hχ hσ hs hμ t
  have he : exp (5 * (c ^ 2 - χ) / (2 * c)) ≤ exp 25 := by
    apply exp_le_exp.mpr
    rw [div_le_iff₀ (by linarith)]; linarith
  have : √2 * exp (5 * (c ^ 2 - χ) / (2 * c)) * |psi c g 1| ≤ KA * |psi c g 1| := by
    unfold KA
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (abs_nonneg _)
  exact h.trans this

end Cvs.Prolate.Envelope.AngularEdgeEnvelope
