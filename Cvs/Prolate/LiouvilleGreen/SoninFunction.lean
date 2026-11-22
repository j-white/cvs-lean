import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Sonin's function: a Sturm–Liouville solution never exceeds its value at the turning point

For `ψ' = v`, `p v' + p' v + q ψ = 0` (that is `(pψ')' + qψ = 0`), Sonin's `S = ψ² + p v²/q` has
`S' = −v²(pq)'/q²`, so `S` decreases where `q > 0` and `(pq)' ≥ 0`. For the prolate outside the window,
`p(1) = 0` gives `ψ(ξ)² ≤ ψ(1)²` on `[1, ξ₁]` when `χ < c²`: the bound across the Bessel strip.
-/

namespace Cvs.Prolate.LiouvilleGreen.SoninFunction

open Set

variable {ψ v v' p p' q q' : ℝ → ℝ}

/-- Sonin's function `ψ² + p v²/q`. -/
noncomputable def sonin (ψ v p q : ℝ → ℝ) (t : ℝ) : ℝ := ψ t ^ 2 + p t * v t ^ 2 / q t

/-- **Sonin's identity**: `S' = −v²(p'q + pq')/q²`. -/
theorem hasDerivAt_sonin {t : ℝ} (hq : q t ≠ 0) (hψ : HasDerivAt ψ (v t) t) (hv : HasDerivAt v (v' t) t)
    (hp : HasDerivAt p (p' t) t) (hqd : HasDerivAt q (q' t) t)
    (hode : p t * v' t + p' t * v t + q t * ψ t = 0) :
    HasDerivAt (sonin ψ v p q) (-(v t ^ 2 * (p' t * q t + p t * q' t)) / q t ^ 2) t := by
  have h := (hψ.fun_mul hψ).fun_add (((hp.fun_mul (hv.fun_mul hv))).fun_div hqd hq)
  have e : sonin ψ v p q = fun s => ψ s * ψ s + p s * (v s * v s) / q s := by
    funext s; unfold sonin; ring
  rw [e]
  refine h.congr_deriv ?_
  field_simp
  linear_combination (2 * v t * q t) * hode

/-- **Sonin's monotonicity.** On `[s, t]`, if `q > 0`, `p'q + pq' ≥ 0` and the system holds, `S t ≤ S s`. -/
theorem sonin_antitone {s t : ℝ} (hst : s ≤ t) (hq : ∀ r ∈ Icc s t, 0 < q r)
    (hmono : ∀ r ∈ Icc s t, 0 ≤ p' r * q r + p r * q' r)
    (hψ : ∀ r ∈ Icc s t, HasDerivAt ψ (v r) r) (hv : ∀ r ∈ Icc s t, HasDerivAt v (v' r) r)
    (hp : ∀ r ∈ Icc s t, HasDerivAt p (p' r) r) (hqd : ∀ r ∈ Icc s t, HasDerivAt q (q' r) r)
    (hode : ∀ r ∈ Icc s t, p r * v' r + p' r * v r + q r * ψ r = 0) :
    sonin ψ v p q t ≤ sonin ψ v p q s := by
  have hd : ∀ r ∈ Icc s t, HasDerivAt (sonin ψ v p q) (-(v r ^ 2 * (p' r * q r + p r * q' r)) / q r ^ 2) r :=
    fun r hr => hasDerivAt_sonin (hq r hr).ne' (hψ r hr) (hv r hr) (hp r hr) (hqd r hr) (hode r hr)
  have hanti : AntitoneOn (sonin ψ v p q) (Icc s t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc s t)
      (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    · rw [interior_Icc]; exact fun r hr => (hd r (Ioo_subset_Icc_self hr)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro r hr
      have hr' := Ioo_subset_Icc_self hr
      rw [(hd r hr').deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      have := mul_nonneg (sq_nonneg (v r)) (hmono r hr')
      linarith
  exact hanti (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst) hst

/-- **The prolate never exceeds its edge value outside the window**: for a solution of
`((ξ²−1)ψ')' + (c²ξ² − χ)ψ = 0` on `[1, ξ₁]` with `χ < c²`, `ψ(ξ)² ≤ ψ(1)²`. -/
theorem prolate_sq_le_edge {c χ ξ₁ ξ : ℝ} (hχ : χ < c ^ 2) (hξ : ξ ∈ Icc 1 ξ₁)
    (hψ : ∀ r ∈ Icc 1 ξ₁, HasDerivAt ψ (v r) r) (hv : ∀ r ∈ Icc 1 ξ₁, HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Icc 1 ξ₁, (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0) :
    ψ ξ ^ 2 ≤ ψ 1 ^ 2 := by
  have hq : ∀ r ∈ Icc (1 : ℝ) ξ, 0 < c ^ 2 * r ^ 2 - χ := fun r hr => by
    have : 1 ≤ r ^ 2 := by nlinarith [hr.1]
    have hc : 0 ≤ c ^ 2 := sq_nonneg c
    nlinarith
  have sub : ∀ r ∈ Icc (1 : ℝ) ξ, r ∈ Icc 1 ξ₁ := fun r hr => ⟨hr.1, hr.2.trans hξ.2⟩
  have h := sonin_antitone (ψ := ψ) (v := v) (v' := v') (p := fun r => r ^ 2 - 1) (p' := fun r => 2 * r)
    (q := fun r => c ^ 2 * r ^ 2 - χ) (q' := fun r => 2 * c ^ 2 * r) hξ.1 hq
    (fun r hr => by
      have hr1 : 1 ≤ r := hr.1
      have := hq r hr
      have : 0 ≤ r ^ 2 - 1 := by nlinarith
      have hc : 0 ≤ c ^ 2 := sq_nonneg c
      positivity)
    (fun r hr => hψ r (sub r hr)) (fun r hr => hv r (sub r hr))
    (fun r _ => by simpa using (hasDerivAt_pow 2 r).sub_const 1)
    (fun r _ => by
      have := ((hasDerivAt_pow 2 r).const_mul (c ^ 2)).sub_const χ
      exact this.congr_deriv (by ring))
    (fun r hr => hode r (sub r hr))
  unfold sonin at h
  simp only [one_pow, sub_self, zero_mul, zero_div, add_zero] at h
  have : 0 ≤ (ξ ^ 2 - 1) * v ξ ^ 2 / (c ^ 2 * ξ ^ 2 - χ) := by
    have := hq ξ (right_mem_Icc.mpr hξ.1)
    have : 0 ≤ ξ ^ 2 - 1 := by nlinarith [hξ.1]
    positivity
  linarith

end Cvs.Prolate.LiouvilleGreen.SoninFunction
