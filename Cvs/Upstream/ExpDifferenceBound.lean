import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.OrbitGapIntegerM
import Cvs.Prolate.Envelope.RungCountEnvelope
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungCauchySplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Transport of the Cauchy half along a window

For `φ' = (ik − β)φ + β·conj φ` with `0 ≤ β ≤ B`: `|φ|² ' = −4β (Im φ)²`, so `|φ|` is antitone and
grows at most like `e^{2B|x−x₀|}` backwards; `φ(x) = e^{iθ}φ(x₀) + O((e^{2B|x−x₀|} − 1)|φ(x₀)|)`
with `θ = ∫k`; and `|θ − k(x₀)(x−x₀)| ≤ (K/2)(x−x₀)²` when `|k'| ≤ K`. For a rung (Cvs.Prolate.RungCauchySplit),
`β ≤ y/(y²−1)` and `|k'| ≤ c·y/(y²−1)²` above `y > 1`, and `c ≤ k ≤ c·Ymax`.
-/

namespace Cvs.Upstream.ExpDifferenceBound

open Complex Set Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.OrbitGapIntegerM Cvs.Prolate.Envelope.RungCountEnvelope Cvs.Prolate.RungCauchySplit
open scoped ComplexConjugate

section radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Radial comparison**: if `‖f' s‖ ≤ G'(|s − a|)` on the segment and `G 0 = 0`,
then `‖f x − f a‖ ≤ G |x − a|`. -/
theorem norm_sub_le_radial {f f' : ℝ → E} {G G' : ℝ → ℝ} {a x : ℝ}
    (hf : ∀ s ∈ uIcc a x, HasDerivAt f (f' s) s) (hG : ∀ r, HasDerivAt G (G' r) r)
    (hG0 : G 0 = 0) (hb : ∀ s ∈ uIcc a x, ‖f' s‖ ≤ G' |s - a|) : ‖f x - f a‖ ≤ G |x - a| := by
  rcases le_total a x with hax | hxa
  · rw [uIcc_of_le hax] at hf hb
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := a) (b := x)
      (f := fun s => f s - f a) (f' := f') (B := fun s => G (s - a)) (B' := fun s => G' (s - a))
      (fun s hs => ((hf s hs).continuousAt.sub continuousAt_const).continuousWithinAt)
      (fun s hs => ((hf s (Ico_subset_Icc_self hs)).sub_const (f a)).hasDerivWithinAt)
      (by simp [hG0])
      (fun s => (hG (s - a)).comp_sub_const s a)
      (fun s hs => by
        have := hb s (Ico_subset_Icc_self hs)
        rwa [abs_of_nonneg (by linarith [hs.1])] at this)
      ⟨hax, le_rfl⟩
    simpa [abs_of_nonneg (sub_nonneg.mpr hax)] using key
  · rw [uIcc_of_ge hxa] at hf hb
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := a - x)
      (f := fun r => f (a - r) - f a) (f' := fun r => -f' (a - r)) (B := G) (B' := G')
      (fun r hr => (((hf (a - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩).continuousAt.comp
        (continuousAt_const.sub continuousAt_id)).sub continuousAt_const).continuousWithinAt)
      (fun r hr => (((hf (a - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩).comp_const_sub a r).sub_const
        (f a)).hasDerivWithinAt)
      (by simp [hG0]) hG
      (fun r hr => by
        have := hb (a - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
        rw [norm_neg]
        rwa [show a - r - a = -r by ring, abs_neg, abs_of_nonneg hr.1] at this)
      ⟨sub_nonneg.mpr hxa, le_rfl⟩
    simpa [abs_sub_comm x a, abs_of_nonneg (sub_nonneg.mpr hxa)] using key

end radial

section transport

variable {φ : ℝ → ℂ} {k k' β θ : ℝ → ℝ} {a x B K : ℝ}

/-- The drift `φ' − ikφ = β(conj φ − φ)` has norm at most `2|β||φ|`. -/
theorem norm_drift_le (k β : ℝ) (z : ℂ) :
    ‖((I * (k : ℂ) - (β : ℂ)) * z + (β : ℂ) * conj z) - I * (k : ℂ) * z‖ ≤ 2 * |β| * ‖z‖ := by
  have e : ((I * (k : ℂ) - (β : ℂ)) * z + (β : ℂ) * conj z) - I * (k : ℂ) * z = (β : ℂ) * (conj z - z) := by
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have : ‖conj z - z‖ ≤ 2 * ‖z‖ := by
    calc ‖conj z - z‖ ≤ ‖conj z‖ + ‖z‖ := norm_sub_le _ _
      _ = 2 * ‖z‖ := by rw [Complex.norm_conj]; ring
  nlinarith [abs_nonneg β]

/-- `|φ|² ' = −4β (Im φ)²` along the split equation. -/
theorem hasDerivAt_norm_sq (h : HasDerivAt φ ((I * (k x : ℂ) - (β x : ℂ)) * φ x + (β x : ℂ) * conj (φ x)) x) :
    HasDerivAt (fun s => ‖φ s‖ ^ 2) (-(4 * β x * (φ x).im ^ 2)) x := by
  refine h.norm_sq.congr_deriv ?_
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- `|φ|` is antitone wherever `β ≥ 0`. -/
theorem norm_antitoneOn {b : ℝ}
    (hode : ∀ s ∈ Icc a b, HasDerivAt φ ((I * (k s : ℂ) - (β s : ℂ)) * φ s + (β s : ℂ) * conj (φ s)) s)
    (hβ : ∀ s ∈ Icc a b, 0 ≤ β s) : AntitoneOn (fun s => ‖φ s‖) (Icc a b) := by
  have h2 : AntitoneOn (fun s => ‖φ s‖ ^ 2) (Icc a b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun s => -(4 * β s * (φ s).im ^ 2))
      (convex_Icc a b)
      (fun s hs => (hasDerivAt_norm_sq (hode s hs)).continuousAt.continuousWithinAt)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs
      exact (hasDerivAt_norm_sq (hode s (Ioo_subset_Icc_self hs))).hasDerivWithinAt
    · rw [interior_Icc] at hs
      have := hβ s (Ioo_subset_Icc_self hs)
      have : 0 ≤ 4 * β s * (φ s).im ^ 2 := by positivity
      linarith
  intro s hs t ht hst
  have := h2 hs ht hst
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- Backward growth: `|φ(s)| ≤ e^{2B(a−s)} |φ(a)|` for `s ≤ a` when `0 ≤ β ≤ B` on `[s, a]`. -/
theorem norm_le_exp_of_le {s : ℝ} (hsa : s ≤ a)
    (hode : ∀ t ∈ Icc s a, HasDerivAt φ ((I * (k t : ℂ) - (β t : ℂ)) * φ t + (β t : ℂ) * conj (φ t)) t)
    (hβ : ∀ t ∈ Icc s a, 0 ≤ β t ∧ β t ≤ B) : ‖φ s‖ ≤ Real.exp (2 * B * (a - s)) * ‖φ a‖ := by
  have hder : ∀ t ∈ Icc s a, HasDerivAt (fun t => ‖φ t‖ ^ 2 * Real.exp (4 * B * t))
      (-(4 * β t * (φ t).im ^ 2) * Real.exp (4 * B * t)
        + ‖φ t‖ ^ 2 * (Real.exp (4 * B * t) * (4 * B))) t := fun t ht => by
    have h1 := hasDerivAt_norm_sq (hode t ht)
    have h2 := ((hasDerivAt_id t).const_mul (4 * B)).exp
    simp only [id, mul_one] at h2
    exact h1.mul h2
  have hmono : MonotoneOn (fun t => ‖φ t‖ ^ 2 * Real.exp (4 * B * t)) (Icc s a) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s a)
      (f' := fun t => -(4 * β t * (φ t).im ^ 2) * Real.exp (4 * B * t)
        + ‖φ t‖ ^ 2 * (Real.exp (4 * B * t) * (4 * B)))
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hder t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · rw [interior_Icc] at ht
      obtain ⟨h0, hB⟩ := hβ t (Ioo_subset_Icc_self ht)
      have him : (φ t).im ^ 2 ≤ ‖φ t‖ ^ 2 := by
        have := Complex.abs_im_le_norm (φ t)
        nlinarith [abs_nonneg (φ t).im, sq_abs (φ t).im]
      have hpos := Real.exp_pos (4 * B * t)
      have : β t * (φ t).im ^ 2 ≤ B * ‖φ t‖ ^ 2 := by
        nlinarith [sq_nonneg (φ t).im, sq_nonneg ‖φ t‖]
      nlinarith
  have key := hmono ⟨le_rfl, hsa⟩ ⟨hsa, le_rfl⟩ hsa
  simp only at key
  have e1 : Real.exp (4 * B * a) = Real.exp (4 * B * s) * Real.exp (2 * B * (a - s)) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  rw [e1] at key
  have hpos := Real.exp_pos (4 * B * s)
  have hsq : ‖φ s‖ ^ 2 ≤ (Real.exp (2 * B * (a - s)) * ‖φ a‖) ^ 2 := by
    rw [mul_pow]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **Growth**: `|φ(x)| ≤ e^{2B|x−a|} |φ(a)|` when `0 ≤ β ≤ B` on the segment. -/
theorem norm_le_exp
    (hode : ∀ s ∈ uIcc a x, HasDerivAt φ ((I * (k s : ℂ) - (β s : ℂ)) * φ s + (β s : ℂ) * conj (φ s)) s)
    (hβ : ∀ s ∈ uIcc a x, 0 ≤ β s ∧ β s ≤ B) : ‖φ x‖ ≤ Real.exp (2 * B * |x - a|) * ‖φ a‖ := by
  rcases le_total a x with hax | hxa
  · rw [uIcc_of_le hax] at hode hβ
    have h1 := norm_antitoneOn hode (fun s hs => (hβ s hs).1) ⟨le_rfl, hax⟩ ⟨hax, le_rfl⟩ hax
    have hB : 0 ≤ B := (hβ a ⟨le_rfl, hax⟩).1.trans (hβ a ⟨le_rfl, hax⟩).2
    have : 1 ≤ Real.exp (2 * B * |x - a|) := Real.one_le_exp (by positivity)
    simp only at h1
    nlinarith [norm_nonneg (φ a)]
  · rw [uIcc_of_ge hxa] at hode hβ
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxa)]
    exact norm_le_exp_of_le hxa hode hβ

/-- **Phase transport**: `|φ(x) − e^{i(θ(x)−θ(a))} φ(a)| ≤ (e^{2B|x−a|} − 1)|φ(a)|`
for `θ' = k` and `0 ≤ β ≤ B` on the segment. -/
theorem norm_sub_exp_phase_le
    (hode : ∀ s ∈ uIcc a x, HasDerivAt φ ((I * (k s : ℂ) - (β s : ℂ)) * φ s + (β s : ℂ) * conj (φ s)) s)
    (hθ : ∀ s ∈ uIcc a x, HasDerivAt θ (k s) s) (hβ : ∀ s ∈ uIcc a x, 0 ≤ β s ∧ β s ≤ B) :
    ‖φ x - exp (((θ x - θ a : ℝ) : ℂ) * I) * φ a‖ ≤ (Real.exp (2 * B * |x - a|) - 1) * ‖φ a‖ := by
  set v : ℝ → ℂ := fun s => exp (-(((θ s - θ a : ℝ) : ℂ) * I)) * φ s with hv
  have hvd : ∀ s ∈ uIcc a x, HasDerivAt v (exp (-(((θ s - θ a : ℝ) : ℂ) * I))
      * (((I * (k s : ℂ) - (β s : ℂ)) * φ s + (β s : ℂ) * conj (φ s)) - I * (k s : ℂ) * φ s)) s := by
    intro s hs
    have hph : HasDerivAt (fun t => -(((θ t - θ a : ℝ) : ℂ) * I)) (-((k s : ℂ) * I)) s :=
      (((hθ s hs).sub_const (θ a)).ofReal_comp.mul_const I).neg
    refine (hph.cexp.mul (hode s hs)).congr_deriv ?_
    ring
  have hs_sub : ∀ s ∈ uIcc a x, uIcc a s ⊆ uIcc a x := fun s hs => uIcc_subset_uIcc left_mem_uIcc hs
  have hG : ∀ r, HasDerivAt (fun r => (Real.exp (2 * B * r) - 1) * ‖φ a‖)
      (Real.exp (2 * B * r) * (2 * B) * ‖φ a‖) r := fun r => by
    have h := (((hasDerivAt_id r).const_mul (2 * B)).exp.sub_const 1).mul_const ‖φ a‖
    simpa using h
  have key := norm_sub_le_radial (f := v) hvd hG (by simp) (fun s hs => by
    rw [norm_mul, show -(((θ s - θ a : ℝ) : ℂ) * I) = (((-(θ s - θ a)) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    obtain ⟨h0, hB⟩ := hβ s hs
    have hn := norm_le_exp (fun t ht => hode t (hs_sub s hs ht)) (fun t ht => hβ t (hs_sub s hs ht))
    have hd := norm_drift_le (k s) (β s) (φ s)
    rw [abs_of_nonneg h0] at hd
    have hB0 : 0 ≤ B := h0.trans hB
    calc _ ≤ 2 * β s * ‖φ s‖ := hd
      _ ≤ 2 * B * (Real.exp (2 * B * |s - a|) * ‖φ a‖) := by
          apply mul_le_mul (by linarith) hn (norm_nonneg _) (by linarith)
      _ = _ := by ring)
  have hva : v a = φ a := by simp [hv]
  have e : φ x - exp (((θ x - θ a : ℝ) : ℂ) * I) * φ a
      = exp (((θ x - θ a : ℝ) : ℂ) * I) * (v x - v a) := by
    rw [hva, hv]
    simp only
    rw [mul_sub, ← mul_assoc, ← Complex.exp_add]
    simp
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact key

/-- **Chirp**: `|θ(x) − θ(a) − k(a)(x−a)| ≤ (K/2)(x−a)²` for `θ' = k`, `|k'| ≤ K` on the segment. -/
theorem abs_phase_sub_linear_le (hθ : ∀ s ∈ uIcc a x, HasDerivAt θ (k s) s)
    (hk : ∀ s ∈ uIcc a x, HasDerivAt k (k' s) s) (hK : ∀ s ∈ uIcc a x, |k' s| ≤ K) :
    |θ x - θ a - k a * (x - a)| ≤ K / 2 * (x - a) ^ 2 := by
  have hs_sub : ∀ s ∈ uIcc a x, uIcc a s ⊆ uIcc a x := fun s hs => uIcc_subset_uIcc left_mem_uIcc hs
  have hlip : ∀ s ∈ uIcc a x, |k s - k a| ≤ K * |s - a| := fun s hs => by
    have := norm_sub_le_radial (f := k) (G := fun r => K * r) (G' := fun _ => K)
      (fun t ht => hk t (hs_sub s hs ht)) (fun r => by simpa using (hasDerivAt_id r).const_mul K)
      (by simp) (fun t ht => by simpa using hK t (hs_sub s hs ht))
    simpa using this
  have := norm_sub_le_radial (f := fun s => θ s - k a * s) (f' := fun s => k s - k a)
    (G := fun r => K / 2 * r ^ 2) (G' := fun r => K * r)
    (fun s hs => ((hθ s hs).sub ((hasDerivAt_id s).const_mul (k a))).congr_deriv (by simp))
    (fun r => by
      have h := (hasDerivAt_pow 2 r).const_mul (K / 2)
      refine h.congr_deriv ?_; push_cast; ring)
    (by simp) (fun s hs => by simpa using hlip s hs)
  simp only [Real.norm_eq_abs, sq_abs] at this
  convert this using 2; ring

/-- `|e^{iα} − e^{iγ}| ≤ |α − γ|`. -/
theorem norm_exp_sub_exp_le (α γ : ℝ) : ‖exp ((α : ℂ) * I) - exp ((γ : ℂ) * I)‖ ≤ |α - γ| := by
  have e : exp ((α : ℂ) * I) - exp ((γ : ℂ) * I) = exp ((γ : ℂ) * I) * (exp (I * ((α - γ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := α - γ)

end transport

section bounds

/-- `y/(y²−1)` is antitone on `y > 1`. -/
theorem div_sq_sub_one_anti {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) : v / (v ^ 2 - 1) ≤ u / (u ^ 2 - 1) := by
  have hu2 : 0 < u ^ 2 - 1 := by nlinarith
  have hv2 : 0 < v ^ 2 - 1 := by nlinarith
  rw [div_le_div_iff₀ hv2 hu2]
  nlinarith [mul_nonneg (sub_nonneg.mpr huv) (by nlinarith : (0 : ℝ) ≤ u * v + 1)]

/-- `y/(y²−1)²` is antitone on `y > 1`. -/
theorem div_sq_sub_one_sq_anti {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    v / (v ^ 2 - 1) ^ 2 ≤ u / (u ^ 2 - 1) ^ 2 := by
  have hu2 : 0 < u ^ 2 - 1 := by nlinarith
  have hv2 : 0 < v ^ 2 - 1 := by nlinarith
  have e : ∀ y : ℝ, y / (y ^ 2 - 1) ^ 2 = y / (y ^ 2 - 1) * (1 / (y ^ 2 - 1)) := fun y => by
    rw [div_mul_div_comm, mul_one, sq]
  rw [e, e]
  exact mul_le_mul (div_sq_sub_one_anti hu huv) (one_div_le_one_div_of_le hu2 (by nlinarith))
    (by positivity) (by positivity)

/-- `e^t − 1 ≤ t e^t` for every real `t`. -/
theorem exp_sub_one_le_mul_exp {t : ℝ} : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.add_one_le_exp (-t)
  have hp := Real.exp_pos t
  have e : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  nlinarith

end bounds

section rung

variable {c χ ξ : ℝ} {g g₁ g₂ : ℝ → ℝ}

/-- `β = ξ/(2(ξ²−1)) + c²ξ/(2(c²ξ²−χ))`. -/
theorem betaP_eq (hξ : 1 < ξ) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) :
    betaP c χ ξ = ξ / (2 * (ξ ^ 2 - 1)) + c ^ 2 * ξ / (2 * (c ^ 2 * ξ ^ 2 - χ)) := by
  have ha := aP_pos hξ hc2 hχc
  have hq := qP_pos hξ hc2 hχc
  have hp := pP_pos hξ
  have hsq := aP_sq hξ hc2 hχc
  have e1 : betaP c χ ξ = dP c χ ξ / (4 * (pP ξ * qP c χ ξ)) := by
    unfold betaP wP; rw [← hsq]; field_simp; ring
  have hp' := pP_pos hξ
  have hq' := qP_pos hξ hc2 hχc
  rw [e1, show ξ ^ 2 - 1 = pP ξ from rfl, show c ^ 2 * ξ ^ 2 - χ = qP c χ ξ from rfl]
  field_simp
  unfold dP pP qP
  ring

theorem betaP_pos (hξ : 1 < ξ) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) : 0 < betaP c χ ξ := by
  rw [betaP_eq hξ hc2 hχc]
  have hq := qP_pos hξ hc2 hχc
  have hp := pP_pos hξ
  unfold qP at hq; unfold pP at hp
  have : 0 < ξ := by linarith
  positivity

/-- **`β ≤ ξ/(ξ²−1)`** on `ξ > 1`. -/
theorem betaP_le (hξ : 1 < ξ) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) : betaP c χ ξ ≤ ξ / (ξ ^ 2 - 1) := by
  rw [betaP_eq hξ hc2 hχc]
  have hq := qP_pos hξ hc2 hχc
  have hp := pP_pos hξ
  unfold qP at hq; unfold pP at hp
  have hξ0 : 0 < ξ := by linarith
  have h2 : c ^ 2 * ξ / (2 * (c ^ 2 * ξ ^ 2 - χ)) ≤ ξ / (2 * (ξ ^ 2 - 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hξ0 hp]
  have e : ξ / (ξ ^ 2 - 1) = ξ / (2 * (ξ ^ 2 - 1)) + ξ / (2 * (ξ ^ 2 - 1)) := by field_simp; ring
  linarith

/-- `k' = −ξ(c²−χ)/(a p)`. -/
theorem hasDerivAt_kP (hξ : 1 < ξ) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) :
    HasDerivAt (kP c χ) (-(ξ * (c ^ 2 - χ)) / (aP c χ ξ * pP ξ)) ξ := by
  have ha := aP_pos hξ hc2 hχc
  have hq := qP_pos hξ hc2 hχc
  have hp := pP_pos hξ
  have hsq := aP_sq hξ hc2 hχc
  have hpd : HasDerivAt pP (2 * ξ) ξ := by
    have h := (hasDerivAt_pow 2 ξ).sub_const 1
    exact (show (fun s : ℝ => s ^ 2 - 1) = pP from rfl) ▸ (by simpa using h)
  have h := (hasDerivAt_aP hξ hc2 hχc).div hpd hp.ne'
  refine h.congr_deriv ?_
  have hw : wP c χ ξ * qP c χ ξ = dP c χ ξ / (2 * aP c χ ξ) := by unfold wP; field_simp
  rw [hw]
  calc (dP c χ ξ / (2 * aP c χ ξ) * pP ξ - aP c χ ξ * (2 * ξ)) / pP ξ ^ 2
      = (dP c χ ξ * pP ξ - 4 * ξ * aP c χ ξ ^ 2) / (2 * aP c χ ξ * pP ξ ^ 2) := by
        field_simp; ring
    _ = (dP c χ ξ * pP ξ - 4 * ξ * (pP ξ * qP c χ ξ)) / (2 * aP c χ ξ * pP ξ ^ 2) := by rw [hsq]
    _ = -(ξ * (c ^ 2 - χ)) / (aP c χ ξ * pP ξ) := by
        unfold dP qP; field_simp; ring

/-- `c·p ≤ a` on `ξ > 1`. -/
theorem mul_pP_le_aP (hξ : 1 < ξ) (hc : 0 < c) (hχc : χ < c ^ 2) : c * pP ξ ≤ aP c χ ξ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos hξ hc2 hχc
  have hsq := aP_sq hξ hc2 hχc
  have hp := pP_pos hξ
  have h : (c * pP ξ) ^ 2 ≤ aP c χ ξ ^ 2 := by
    rw [hsq]; unfold qP; unfold pP at hp ⊢; nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) ha.le two_ne_zero).mp h

/-- **`|k'| ≤ c·ξ/(ξ²−1)²`** for `0 ≤ χ < c²`. -/
theorem abs_deriv_kP_le (hξ : 1 < ξ) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) :
    |-(ξ * (c ^ 2 - χ)) / (aP c χ ξ * pP ξ)| ≤ c * (ξ / (ξ ^ 2 - 1) ^ 2) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos hξ hc2 hχc
  have hp := pP_pos hξ
  have hle := mul_pP_le_aP hξ hc hχc
  have hξ0 : 0 < ξ := by linarith
  have hcχ : 0 ≤ c ^ 2 - χ := by linarith
  have hnn : 0 ≤ ξ * (c ^ 2 - χ) / (aP c χ ξ * pP ξ) := by positivity
  rw [neg_div, abs_neg, abs_of_nonneg hnn]
  rw [show ξ ^ 2 - 1 = pP ξ from rfl, div_le_iff₀ (by positivity)]
  calc ξ * (c ^ 2 - χ) ≤ ξ * c ^ 2 := by nlinarith
    _ = c * (ξ / pP ξ ^ 2) * (c * pP ξ * pP ξ) := by field_simp
    _ ≤ c * (ξ / pP ξ ^ 2) * (aP c χ ξ * pP ξ) := by gcongr

/-- **`c ≤ k ≤ c·Ymax ξ`** for `0 ≤ χ < c²`: the wavenumber lies in the band `c[1, Ymax]`. -/
theorem kP_mem_Icc (hξ : 1 < ξ) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) :
    kP c χ ξ ∈ Icc c (c * Ymax ξ) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp := pP_pos hξ
  have hq := qP_pos hξ hc2 hχc
  refine ⟨?_, ?_⟩
  · unfold kP; rw [le_div_iff₀ hp]; exact mul_pP_le_aP hξ hc hχc
  · have hs : 0 < √(pP ξ) := Real.sqrt_pos.mpr hp
    have hξ0 : 0 < ξ := by linarith
    have hqle : √(qP c χ ξ) ≤ c * ξ := by
      rw [Real.sqrt_le_left (by positivity)]; unfold qP; nlinarith
    have e : kP c χ ξ = √(qP c χ ξ) / √(pP ξ) := by
      unfold kP aP
      rw [Real.sqrt_mul hp.le, ← Real.sq_sqrt hp.le]
      rw [Real.sqrt_sq hs.le]
      field_simp
    rw [e]
    unfold Ymax
    rw [show ξ ^ 2 - 1 = pP ξ from rfl, mul_div_assoc']
    exact div_le_div_of_nonneg_right hqle hs.le

/-- The rung's phase `θ(x) = ∫_{x₀}^x k`. -/
noncomputable def phaseP (c χ x₀ x : ℝ) : ℝ := ∫ s in x₀..x, kP c χ s

theorem continuousOn_kP (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) : ContinuousOn (kP c χ) (Ioi 1) :=
  fun _ hs => (hasDerivAt_kP hs hc2 hχc).continuousAt.continuousWithinAt

theorem hasDerivAt_phaseP {x₀ s : ℝ} (h₀ : 1 < x₀) (hs : 1 < s) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) :
    HasDerivAt (phaseP c χ x₀) (kP c χ s) s := by
  have hcont := continuousOn_kP hc2 hχc
  have hsub : uIcc x₀ s ⊆ Ioi 1 := fun t ht => by
    rcases le_total x₀ s with h | h
    · rw [uIcc_of_le h] at ht; exact lt_of_lt_of_le h₀ ht.1
    · rw [uIcc_of_ge h] at ht; exact lt_of_lt_of_le hs ht.1
  exact intervalIntegral.integral_hasDerivAt_right ((hcont.mono hsub).intervalIntegrable)
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi s hs) ((hasDerivAt_kP hs hc2 hχc).continuousAt)

theorem phaseP_self (c χ x₀ : ℝ) : phaseP c χ x₀ x₀ = 0 := by simp [phaseP]

section window

variable {x₀ x y : ℝ}
  (hg : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
  (hg₁ : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
  (hg₂c : ContinuousOn g₂ (Set.uIcc (-1) 1))
  (hang : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
  (hc : 0 < c) (hχc : χ < c ^ 2) (hy : 1 < y) (hy₀ : y ≤ x₀) (hyx : y ≤ x)
include hg hg₁ hg₂c hang hc hχc

omit hg hg₁ hg₂c hang hc hχc in
theorem le_of_mem_uIcc (hy₀ : y ≤ x₀) (hyx : y ≤ x) {s : ℝ} (hs : s ∈ uIcc x₀ x) : y ≤ s :=
  le_trans (le_min hy₀ hyx) hs.1

include hy hy₀ hyx

omit hg hg₁ hg₂c hang in
theorem window_bounds {s : ℝ} (hs : s ∈ uIcc x₀ x) :
    1 < s ∧ (0 ≤ betaP c χ s ∧ betaP c χ s ≤ y / (y ^ 2 - 1)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hys := le_of_mem_uIcc hy₀ hyx hs
  have h1 : 1 < s := lt_of_lt_of_le hy hys
  exact ⟨h1, (betaP_pos h1 hc2 hχc).le,
    (betaP_le h1 hc2 hχc).trans (div_sq_sub_one_anti hy hys)⟩

/-- **Growth on the window**: `|ψ⁺(x)| ≤ e^{2β_y|x−x₀|} |ψ⁺(x₀)|`, `β_y = y/(y²−1)`. -/
theorem norm_psiP_le_exp :
    ‖psiP c χ g x‖ ≤ Real.exp (2 * (y / (y ^ 2 - 1)) * |x - x₀|) * ‖psiP c χ g x₀‖ :=
  norm_le_exp (k := kP c χ) (β := betaP c χ)
    (fun _ hs => hasDerivAt_psiP hg hg₁ hg₂c hang
      (window_bounds hc hχc hy hy₀ hyx hs).1 hc hχc)
    (fun _ hs => (window_bounds hc hχc hy hy₀ hyx hs).2)

/-- **Phase transport**: `|ψ⁺(x) − e^{i∫_{x₀}^x k} ψ⁺(x₀)| ≤ (e^{2β_y|x−x₀|} − 1)|ψ⁺(x₀)|`. -/
theorem psiP_phase_transport :
    ‖psiP c χ g x - exp ((phaseP c χ x₀ x : ℂ) * I) * psiP c χ g x₀‖
      ≤ (Real.exp (2 * (y / (y ^ 2 - 1)) * |x - x₀|) - 1) * ‖psiP c χ g x₀‖ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have h := norm_sub_exp_phase_le (θ := phaseP c χ x₀) (k := kP c χ) (β := betaP c χ)
    (fun s hs => hasDerivAt_psiP hg hg₁ hg₂c hang
      (window_bounds hc hχc hy hy₀ hyx hs).1 hc hχc)
    (fun s hs => hasDerivAt_phaseP (lt_of_lt_of_le hy hy₀)
      (window_bounds hc hχc hy hy₀ hyx hs).1 hc2 hχc)
    (fun _ hs => (window_bounds hc hχc hy hy₀ hyx hs).2)
  simpa [phaseP_self] using h

omit hg hg₁ hg₂c hang in
/-- **Chirp bound**: `|∫_{x₀}^x k − k(x₀)(x−x₀)| ≤ (c/2)·Y'_y·(x−x₀)²`, `Y'_y = y/(y²−1)²`. -/
theorem phaseP_chirp (hχ : 0 ≤ χ) :
    |phaseP c χ x₀ x - kP c χ x₀ * (x - x₀)| ≤ c / 2 * (y / (y ^ 2 - 1) ^ 2) * (x - x₀) ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hs1 : ∀ s ∈ uIcc x₀ x, 1 < s := fun s hs => lt_of_lt_of_le hy (le_of_mem_uIcc hy₀ hyx hs)
  have h := abs_phase_sub_linear_le (θ := phaseP c χ x₀) (k := kP c χ)
    (k' := fun s => -(s * (c ^ 2 - χ)) / (aP c χ s * pP s)) (K := c * (y / (y ^ 2 - 1) ^ 2))
    (fun s hs => hasDerivAt_phaseP (lt_of_lt_of_le hy hy₀) (hs1 s hs) hc2 hχc)
    (fun s hs => hasDerivAt_kP (hs1 s hs) hc2 hχc)
    (fun s hs => (abs_deriv_kP_le (hs1 s hs) hc hχ hχc).trans
      (mul_le_mul_of_nonneg_left (div_sq_sub_one_sq_anti hy (le_of_mem_uIcc hy₀ hyx hs)) hc.le))
  rw [phaseP_self, sub_zero] at h
  convert h using 1; ring

/-- **Per-rung transfer**: `|ψ⁺(x) − e^{ik(x₀)(x−x₀)} ψ⁺(x₀)|
≤ ((e^{2β_y|x−x₀|} − 1) + (c/2)Y'_y(x−x₀)²)|ψ⁺(x₀)|`. -/
theorem psiP_transfer (hχ : 0 ≤ χ) :
    ‖psiP c χ g x - exp (((kP c χ x₀ * (x - x₀) : ℝ) : ℂ) * I) * psiP c χ g x₀‖
      ≤ ((Real.exp (2 * (y / (y ^ 2 - 1)) * |x - x₀|) - 1)
          + c / 2 * (y / (y ^ 2 - 1) ^ 2) * (x - x₀) ^ 2) * ‖psiP c χ g x₀‖ := by
  have h1 := psiP_phase_transport hg hg₁ hg₂c hang hc hχc hy hy₀ hyx
  have h2 : ‖(exp ((phaseP c χ x₀ x : ℂ) * I) - exp (((kP c χ x₀ * (x - x₀) : ℝ) : ℂ) * I))
      * psiP c χ g x₀‖ ≤ c / 2 * (y / (y ^ 2 - 1) ^ 2) * (x - x₀) ^ 2 * ‖psiP c χ g x₀‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((norm_exp_sub_exp_le _ _).trans
      (phaseP_chirp hc hχc hy hy₀ hyx hχ)) (norm_nonneg _)
  calc _ = ‖(psiP c χ g x - exp ((phaseP c χ x₀ x : ℂ) * I) * psiP c χ g x₀)
        + (exp ((phaseP c χ x₀ x : ℂ) * I) - exp (((kP c χ x₀ * (x - x₀) : ℝ) : ℂ) * I))
          * psiP c χ g x₀‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- **Real transfer**: `|ψ(x) − 2 Re(e^{ik(x₀)(x−x₀)} ψ⁺(x₀))|
≤ ((e^{2β_y|x−x₀|} − 1) + (c/2)Y'_y(x−x₀)²)·R(x₀)`. -/
theorem psi_transfer (hχ : 0 ≤ χ) :
    |psi c g x - 2 * (exp (((kP c χ x₀ * (x - x₀) : ℝ) : ℂ) * I) * psiP c χ g x₀).re|
      ≤ ((Real.exp (2 * (y / (y ^ 2 - 1)) * |x - x₀|) - 1)
          + c / 2 * (y / (y ^ 2 - 1) ^ 2) * (x - x₀) ^ 2) * rungAmp c χ g x₀ := by
  have h := psiP_transfer hg hg₁ hg₂c hang hc hχc hy hy₀ hyx hχ
  rw [norm_psiP (lt_of_lt_of_le hy hy₀) hc hχc] at h
  rw [psi_eq_two_mul_re_psiP (χ := χ), ← mul_sub, ← Complex.sub_re, abs_mul, abs_two]
  have := Complex.abs_re_le_norm
    (psiP c χ g x - exp (((kP c χ x₀ * (x - x₀) : ℝ) : ℂ) * I) * psiP c χ g x₀)
  nlinarith

/-- **Envelope on the window**: `|ψ(x)| ≤ e^{2β_y|x−x₀|}·R(x₀)`. -/
theorem abs_psi_le_exp :
    |psi c g x| ≤ Real.exp (2 * (y / (y ^ 2 - 1)) * |x - x₀|) * rungAmp c χ g x₀ := by
  have h := norm_psiP_le_exp hg hg₁ hg₂c hang hc hχc hy hy₀ hyx
  rw [norm_psiP (lt_of_lt_of_le hy hy₀) hc hχc] at h
  rw [psi_eq_two_mul_re_psiP (χ := χ), abs_mul, abs_two]
  have := Complex.abs_re_le_norm (psiP c χ g x)
  nlinarith

end window

/-- `2 Re(e^{it} w) = e^{it} w + e^{−it} conj w`: the real transfer target is the sample
`μ(k)ψ⁺ + μ(−k)ψ⁻` with `ψ⁻ = conj ψ⁺`. -/
theorem two_re_exp_mul (t : ℝ) (w : ℂ) :
    ((2 * (exp ((t : ℂ) * I) * w).re : ℝ) : ℂ) = exp ((t : ℂ) * I) * w + exp ((-t : ℝ) * I) * conj w := by
  have h : exp (((-t : ℝ) : ℂ) * I) * conj w = conj (exp ((t : ℂ) * I) * w) := by
    rw [map_mul, ← Complex.exp_conj]; congr 1; simp
  rw [h, Complex.add_conj]

end rung

end Cvs.Upstream.ExpDifferenceBound
