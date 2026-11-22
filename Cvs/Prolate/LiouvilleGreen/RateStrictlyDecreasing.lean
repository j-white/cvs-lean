import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Liouville–Green rate of the prolate coefficients is strictly decreasing

For `p = 1 − s²`, `q = c²(1 − s²) − Kc` and `a = √(pq)`, the rate `w = a'/q` satisfies `w a q = −s(q + c²p)` and
`w' = −(q² + c²p²q + 3c⁴s²p²)/(a³q) < 0` wherever `s² < 1` and `q > 0`, for every `K`; so `w` is strictly decreasing
on every interval of the allowed region, and `|w|` is strictly increasing on its part in `s ≥ 0`.
-/

noncomputable section

open Real Set Cvs.Prolate.TopRungDepthBound Cvs.Prolate.RegularSolutionEdge

namespace Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing

variable {c K s : ℝ}

/-- **The rate, closed form**: `w a q = −s(q + c²(1 − s²))`. -/
theorem wf_mul_af_mul_qf (hs : s ^ 2 < 1) (hq : 0 < qf c K s) :
    wf c K s * af c K s * qf c K s = -(s * (qf c K s + c ^ 2 * (1 - s ^ 2))) := by
  have ha := af_pos hs hq
  unfold wf
  field_simp

/-- **The rate derivative, closed form**: `w' = −(q² + c²p²q + 3c⁴s²p²)/(a³q)` with `p = 1 − s²`. -/
theorem wd_eq (hs : s ^ 2 < 1) (hq : 0 < qf c K s) :
    wd c K s = -((qf c K s ^ 2 + c ^ 2 * (1 - s ^ 2) ^ 2 * qf c K s + 3 * c ^ 4 * s ^ 2 * (1 - s ^ 2) ^ 2) /
      (af c K s ^ 3 * qf c K s)) := by
  have ha := af_pos hs hq
  have ha2 := af_sq hs hq
  have hw : wf c K s * qf c K s = -(s * (qf c K s + c ^ 2 * (1 - s ^ 2))) / af c K s := by
    rw [eq_div_iff ha.ne', ← wf_mul_af_mul_qf hs hq]; ring
  unfold wd
  rw [hw]
  set a := af c K s
  set q := qf c K s
  field_simp
  rw [ha2]
  ring

/-- **`w' < 0`** wherever `s² < 1` and `q > 0`, for every `K`. -/
theorem wd_neg (hc : c ≠ 0) (hs : s ^ 2 < 1) (hq : 0 < qf c K s) : wd c K s < 0 := by
  rw [wd_eq hs hq, neg_lt_zero]
  have ha := af_pos hs hq
  have hp : 0 < 1 - s ^ 2 := by linarith
  have : 0 < qf c K s ^ 2 := by positivity
  positivity

/-- `q` is non-increasing on `s ≥ 0`. -/
theorem qf_le_qf {s₁ s₂ : ℝ} (h0 : 0 ≤ s₁) (h : s₁ ≤ s₂) : qf c K s₂ ≤ qf c K s₁ := by
  unfold qf; nlinarith [sq_nonneg c, mul_le_mul h h h0 (h0.trans h)]

/-- **Lemma 1.2 (the rate is monotone)**: `w` is strictly decreasing on `[s₁, s₂]` when `s₂² < 1`, `q(s₂) > 0` and
`0 ≤ s₁`. -/
theorem wf_strictAntiOn {s₁ s₂ : ℝ} (hc : c ≠ 0) (h0 : 0 ≤ s₁) (hs : s₂ ^ 2 < 1) (hq : 0 < qf c K s₂) :
    StrictAntiOn (wf c K) (Icc s₁ s₂) := by
  have hmem : ∀ t ∈ Icc s₁ s₂, t ^ 2 < 1 ∧ 0 < qf c K t := fun t ht =>
    ⟨by nlinarith [ht.1, ht.2], hq.trans_le (qf_le_qf (h0.trans ht.1) ht.2)⟩
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _) (f' := wd c K) ?_ ?_ ?_
  · exact fun t ht => (hasDerivAt_wf (hmem t ht).1 (hmem t ht).2).continuousAt.continuousWithinAt
  · intro t ht
    have ht' := interior_subset ht
    exact (hasDerivAt_wf (hmem t ht').1 (hmem t ht').2).hasDerivWithinAt
  · intro t ht
    have ht' := interior_subset ht
    exact wd_neg hc (hmem t ht').1 (hmem t ht').2

/-- **Lemma 1.2, `|w|`**: `|w|` is strictly increasing on `[s₁, s₂]` under `wf_strictAntiOn`'s hypotheses. -/
theorem abs_wf_strictMonoOn {s₁ s₂ : ℝ} (hc : c ≠ 0) (h0 : 0 ≤ s₁) (hs : s₂ ^ 2 < 1) (hq : 0 < qf c K s₂) :
    StrictMonoOn (fun s => |wf c K s|) (Icc s₁ s₂) := by
  intro x hx y hy hxy
  have hmem : ∀ t ∈ Icc s₁ s₂, t ^ 2 < 1 ∧ 0 < qf c K t := fun t ht =>
    ⟨by nlinarith [ht.1, ht.2], hq.trans_le (qf_le_qf (h0.trans ht.1) ht.2)⟩
  have h := wf_strictAntiOn hc h0 hs hq hx hy hxy
  simp only
  rw [abs_of_nonpos (wf_nonpos (h0.trans hx.1) (hmem x hx).1 (hmem x hx).2),
    abs_of_nonpos (wf_nonpos (h0.trans hy.1) (hmem y hy).1 (hmem y hy).2)]
  linarith

/-! ### Lemma 1.3: the adiabatic bound -/

/-- The adiabatic constant `κ(M) = ((2 + M)/(2 − M)) e^{M/(2 − M)}`. -/
def kappa (M : ℝ) : ℝ := (2 + M) / (2 - M) * exp (M / (2 - M))

section Adiabatic

variable {ψ u p q a w w' : ℝ → ℝ} {t₀ t₁ M : ℝ}

/-- **Lemma 1.3 (the adiabatic bound)**: for `(pψ')' + qψ = 0` with `a² = pq`, `a' = wq`, `w' ≤ 0` and
`−M ≤ w ≤ 0` (`M < 2`) on `[t₀, t₁]`, the energy `G = aψ² + u²/a` obeys `G(t₁) ≤ κ(M) G(t₀)` and
`G(t₀) ≤ κ(M) G(t₁)`. -/
theorem energy_le_kappa (hle : t₀ ≤ t₁) (hM : M < 2)
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Icc t₀ t₁, HasDerivAt w (w' t) t)
    (hw' : ∀ t ∈ Icc t₀ t₁, w' t ≤ 0) (hwM : ∀ t ∈ Icc t₀ t₁, -M ≤ w t ∧ w t ≤ 0) :
    Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy a ψ u t₁ ≤ kappa M * Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy a ψ u t₀ ∧
      Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy a ψ u t₀ ≤ kappa M * Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy a ψ u t₁ := by
  set G := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy a ψ u
  set F : ℝ → ℝ := fun t => G t + w t * (ψ t * u t) with hF
  have hm : 0 < 2 - M := by linarith
  have hFd : ∀ t ∈ Icc t₀ t₁, HasDerivAt F (w' t * (ψ t * u t)) t := fun t ht =>
    Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.hasDerivAt_energy_add (ha t ht) (hp t ht) (hapq t ht) (hψ t ht) (hu t ht) (haw t ht) (hw t ht)
  have hGu : ∀ t ∈ Icc t₀ t₁, 2 * |ψ t * u t| ≤ G t := fun t ht => Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.two_mul_abs_le_energy (ha t ht)
  -- `F ≥ G(2 − M)/2` and `F ≤ G(2 + M)/2`
  have hFlo : ∀ t ∈ Icc t₀ t₁, G t * (2 - M) / 2 ≤ F t := by
    intro t ht
    have h1 := hGu t ht; have h2 := hwM t ht
    have h3 : |w t * (ψ t * u t)| ≤ M * |ψ t * u t| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (by rw [abs_of_nonpos h2.2]; linarith) (abs_nonneg _)
    have h4 := neg_abs_le (w t * (ψ t * u t))
    have h0 : 0 ≤ M := by linarith
    simp only [hF]; nlinarith [abs_nonneg (ψ t * u t)]
  have hFhi : ∀ t ∈ Icc t₀ t₁, F t ≤ G t * (2 + M) / 2 := by
    intro t ht
    have h1 := hGu t ht; have h2 := hwM t ht
    have h3 : |w t * (ψ t * u t)| ≤ M * |ψ t * u t| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (by rw [abs_of_nonpos h2.2]; linarith) (abs_nonneg _)
    have h4 := le_abs_self (w t * (ψ t * u t))
    have h0 : 0 ≤ M := by linarith
    simp only [hF]; nlinarith [abs_nonneg (ψ t * u t)]
  have hpu : ∀ t ∈ Icc t₀ t₁, |ψ t * u t| ≤ F t / (2 - M) := by
    intro t ht
    rw [le_div_iff₀ hm]; have := hFlo t ht; have := hGu t ht; nlinarith
  have hint : ∀ t ∈ interior (Icc t₀ t₁), t ∈ Icc t₀ t₁ := fun t ht => interior_subset ht
  -- `F e^{w/(2−M)}` is antitone, `F e^{−w/(2−M)}` is monotone
  have hH1 : AntitoneOn (fun t => F t * exp (w t / (2 - M))) (Icc t₀ t₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun t => exp (w t / (2 - M)) * (w' t * (ψ t * u t + F t / (2 - M)))) ?_ ?_ ?_
    · intro t ht
      exact ((hFd t ht).mul ((hw t ht).div_const (2 - M)).exp).continuousAt.continuousWithinAt
    · intro t ht
      refine ((hFd t (hint t ht)).mul ((hw t (hint t ht)).div_const (2 - M)).exp).hasDerivWithinAt.congr_deriv ?_
      ring
    · intro t ht
      have h1 := hpu t (hint t ht)
      have h2 : 0 ≤ ψ t * u t + F t / (2 - M) := by linarith [neg_abs_le (ψ t * u t)]
      exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (mul_nonpos_of_nonpos_of_nonneg (hw' t (hint t ht)) h2)
  have hH2 : MonotoneOn (fun t => F t * exp (-(w t / (2 - M)))) (Icc t₀ t₁) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (f' := fun t => exp (-(w t / (2 - M))) * (w' t * (ψ t * u t - F t / (2 - M)))) ?_ ?_ ?_
    · intro t ht
      exact ((hFd t ht).mul ((hw t ht).div_const (2 - M)).neg.exp).continuousAt.continuousWithinAt
    · intro t ht
      refine ((hFd t (hint t ht)).mul ((hw t (hint t ht)).div_const (2 - M)).neg.exp).hasDerivWithinAt.congr_deriv
        ?_
      simp only [Pi.neg_apply]; ring
    · intro t ht
      have h1 := hpu t (hint t ht)
      have h2 : ψ t * u t - F t / (2 - M) ≤ 0 := by linarith [le_abs_self (ψ t * u t)]
      exact mul_nonneg (exp_pos _).le (mul_nonneg_of_nonpos_of_nonpos (hw' t (hint t ht)) h2)
  have m0 : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, hle⟩
  have m1 : t₁ ∈ Icc t₀ t₁ := ⟨hle, le_rfl⟩
  have e1 := hH1 m0 m1 hle
  have e2 := hH2 m0 m1 hle
  simp only at e1 e2
  have w0 := hwM t₀ m0; have w1 := hwM t₁ m1
  have hG0 : 0 ≤ G t₀ := (abs_nonneg _).trans (by linarith [hGu t₀ m0, abs_nonneg (ψ t₀ * u t₀)])
  have hG1 : 0 ≤ G t₁ := (abs_nonneg _).trans (by linarith [hGu t₁ m1, abs_nonneg (ψ t₁ * u t₁)])
  have hF0 : 0 ≤ F t₀ := by have := hFlo t₀ m0; nlinarith
  have hF1 : 0 ≤ F t₁ := by have := hFlo t₁ m1; nlinarith
  -- exponent bounds
  have hx : (w t₀ - w t₁) / (2 - M) ≤ M / (2 - M) := div_le_div_of_nonneg_right (by linarith) hm.le
  have hE1 : F t₁ ≤ F t₀ * exp (M / (2 - M)) := by
    have : F t₁ = F t₁ * exp (w t₁ / (2 - M)) * exp (-(w t₁ / (2 - M))) := by
      rw [mul_assoc, ← exp_add]; simp
    rw [this]
    calc F t₁ * exp (w t₁ / (2 - M)) * exp (-(w t₁ / (2 - M)))
        ≤ F t₀ * exp (w t₀ / (2 - M)) * exp (-(w t₁ / (2 - M))) :=
          mul_le_mul_of_nonneg_right e1 (exp_pos _).le
      _ = F t₀ * exp ((w t₀ - w t₁) / (2 - M)) := by rw [mul_assoc, ← exp_add]; ring_nf
      _ ≤ F t₀ * exp (M / (2 - M)) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hx) hF0
  have hE2 : F t₀ ≤ F t₁ * exp (M / (2 - M)) := by
    have : F t₀ = F t₀ * exp (-(w t₀ / (2 - M))) * exp (w t₀ / (2 - M)) := by
      rw [mul_assoc, ← exp_add]; simp
    rw [this]
    calc F t₀ * exp (-(w t₀ / (2 - M))) * exp (w t₀ / (2 - M))
        ≤ F t₁ * exp (-(w t₁ / (2 - M))) * exp (w t₀ / (2 - M)) :=
          mul_le_mul_of_nonneg_right e2 (exp_pos _).le
      _ = F t₁ * exp ((w t₀ - w t₁) / (2 - M)) := by rw [mul_assoc, ← exp_add]; ring_nf
      _ ≤ F t₁ * exp (M / (2 - M)) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hx) hF1
  have hk : kappa M = (2 + M) / (2 - M) * exp (M / (2 - M)) := rfl
  have hex := exp_pos (M / (2 - M))
  constructor
  · have a1 := hFlo t₁ m1; have a2 := hFhi t₀ m0
    rw [hk, div_mul_eq_mul_div, mul_comm, ← mul_div_assoc, le_div_iff₀ hm]
    nlinarith [mul_le_mul_of_nonneg_right a2 hex.le]
  · have a1 := hFlo t₀ m0; have a2 := hFhi t₁ m1
    rw [hk, div_mul_eq_mul_div, mul_comm, ← mul_div_assoc, le_div_iff₀ hm]
    nlinarith [mul_le_mul_of_nonneg_right a2 hex.le]

end Adiabatic

end Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing
