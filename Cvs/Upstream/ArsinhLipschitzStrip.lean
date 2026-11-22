import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Upstream.ComplexArsinhStrip
import Cvs.Upstream.InvSqrtKernelStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Lipschitz and second-difference bounds for `ash` on the strip

On a convex subset of `|Im t| ≤ 1 − δ` where `‖k‖ ≤ K`, `ash` is `K`-Lipschitz. If `0, a, b, a + b` lie in the
strip, then `‖ash(a + b) − ash(a) − ash(b) − a(k(b) − 1)‖ ≤ ‖a‖²·min(54/δ³, 486‖b‖/δ⁵)`.
-/

noncomputable section

open Complex Set

namespace Cvs.Upstream.ArsinhLipschitzStrip

open Cvs.Upstream.ComplexArsinhStrip Cvs.Upstream.InvSqrtKernelStrip

variable {δ : ℝ}

/-- The closed strip. -/
def St (δ : ℝ) : Set ℂ := {t | |t.im| ≤ 1 - δ}

theorem convex_St (δ : ℝ) : Convex ℝ (St δ) := by
  intro x hx y hy a b ha hb hab
  simp only [St, Set.mem_setOf_eq] at *
  have : (a • x + b • y).im = a * x.im + b * y.im := by simp
  rw [this]
  calc |a * x.im + b * y.im| ≤ a * |x.im| + b * |y.im| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (1 - δ) + b * (1 - δ) := by gcongr
    _ = 1 - δ := by rw [← add_mul, hab, one_mul]

/-- **Lipschitz bound for `ash`.** -/
theorem norm_ash_sub_le (hδ : 0 < δ) {s : Set ℂ} (hs : Convex ℝ s) (hsS : s ⊆ St δ) {K : ℝ}
    (hK : ∀ t ∈ s, ‖kf t‖ ≤ K) {a b : ℂ} (ha : a ∈ s) (hb : b ∈ s) : ‖ash b - ash a‖ ≤ K * ‖b - a‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hasDerivAt_ash (strip hδ (hsS ht))).hasDerivWithinAt) hK ha hb

theorem ash_zero : ash 0 = 0 := by
  unfold ash
  rw [show (0 : ℂ) ^ 2 + 1 = ((1 : ℝ) : ℂ) by simp, csqrt_ofReal zero_le_one]; simp

theorem kf_zero : kf 0 = 1 := by
  unfold kf
  rw [show (0 : ℂ) ^ 2 + 1 = ((1 : ℝ) : ℂ) by simp, csqrt_ofReal zero_le_one]; simp

/-- The parallelogram spanned by `a, b` lies in the strip when its corners do. -/
theorem mem_St_of_corners {a b : ℂ} (h1 : a ∈ St δ) (h2 : b ∈ St δ) (h3 : a + b ∈ St δ) (hδ : δ ≤ 1)
    {l m : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1) : (l : ℂ) * a + (m : ℂ) * b ∈ St δ := by
  simp only [St, Set.mem_setOf_eq] at *
  have e : ((l : ℂ) * a + (m : ℂ) * b).im = l * (1 - m) * a.im + (1 - l) * m * b.im + l * m * (a + b).im := by
    simp; ring
  rw [e]
  have w1 : 0 ≤ l * (1 - m) := mul_nonneg hl.1 (by linarith [hm.2])
  have w2 : 0 ≤ (1 - l) * m := mul_nonneg (by linarith [hl.2]) hm.1
  have w3 : 0 ≤ l * m := mul_nonneg hl.1 hm.1
  calc |l * (1 - m) * a.im + (1 - l) * m * b.im + l * m * (a + b).im|
      ≤ l * (1 - m) * |a.im| + (1 - l) * m * |b.im| + l * m * |(a + b).im| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
          rw [abs_mul, abs_of_nonneg (by assumption)]
    _ ≤ l * (1 - m) * (1 - δ) + (1 - l) * m * (1 - δ) + l * m * (1 - δ) := by gcongr
    _ = (1 - (1 - l) * (1 - m)) * (1 - δ) := by ring
    _ ≤ 1 - δ := by
        have : 0 ≤ (1 - l) * (1 - m) := mul_nonneg (by linarith [hl.2]) (by linarith [hm.2])
        nlinarith

/-- **The second difference of `ash`.** -/
theorem norm_ash_second_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) {a b : ℂ} (h1 : a ∈ St δ) (h2 : b ∈ St δ)
    (h3 : a + b ∈ St δ) :
    ‖ash (a + b) - ash a - ash b - a * (kf b - 1)‖ ≤ ‖a‖ ^ 2 * min (54 / δ ^ 3) (486 * ‖b‖ / δ ^ 5) := by
  have h0 : (0 : ℂ) ∈ St δ := by simp [St]; linarith
  -- ψ(σ) = k(σ + b) − k(σ); its derivative is k′(σ + b) − k′(σ)
  have hψ : ∀ σ ∈ segment ℝ (0 : ℂ) a, ‖(kf (σ + b) - kf σ) - (kf b - 1)‖ ≤ ‖σ‖ * min (54 / δ ^ 3) (486 * ‖b‖ / δ ^ 5) := by
    intro σ hσ
    obtain ⟨l, hl, rfl⟩ : ∃ l ∈ Icc (0 : ℝ) 1, (l : ℂ) * a = σ := by
      rw [segment_eq_image'] at hσ
      obtain ⟨l, hl, e⟩ := hσ
      exact ⟨l, hl, by rw [← e]; simp [Complex.real_smul]⟩
    -- the segment [0, l a] and its shift by `b` lie in the strip
    have hseg : ∀ r ∈ segment ℝ (0 : ℂ) ((l : ℂ) * a), r ∈ St δ ∧ r + b ∈ St δ := by
      intro r hr
      rw [segment_eq_image'] at hr
      obtain ⟨m, hm, e⟩ := hr
      have er : r = ((m * l : ℝ) : ℂ) * a + ((0 : ℝ) : ℂ) * b := by rw [← e]; simp [Complex.real_smul]; ring
      have er' : r + b = ((m * l : ℝ) : ℂ) * a + ((1 : ℝ) : ℂ) * b := by rw [er]; simp
      have hml : m * l ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hm.1 hl.1, by nlinarith [hm.1, hm.2, hl.1, hl.2]⟩
      exact ⟨er ▸ mem_St_of_corners h1 h2 h3 hδ1 hml ⟨le_rfl, zero_le_one⟩,
        er' ▸ mem_St_of_corners h1 h2 h3 hδ1 hml ⟨zero_le_one, le_rfl⟩⟩
    have hderiv : ∀ r ∈ segment ℝ (0 : ℂ) ((l : ℂ) * a),
        HasDerivWithinAt (fun x => kf (x + b) - kf x) (-(r + b) * kf (r + b) ^ 3 - -r * kf r ^ 3)
          (segment ℝ (0 : ℂ) ((l : ℂ) * a)) r := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := hseg r hr
      have := ((hasDerivAt_kf hδ hr2).comp r ((hasDerivAt_id r).add_const b)).sub (hasDerivAt_kf hδ hr1)
      simp only [id, mul_one] at this
      exact this.hasDerivWithinAt
    have hbound : ∀ r ∈ segment ℝ (0 : ℂ) ((l : ℂ) * a),
        ‖-(r + b) * kf (r + b) ^ 3 - -r * kf r ^ 3‖ ≤ min (54 / δ ^ 3) (486 * ‖b‖ / δ ^ 5) := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := hseg r hr
      apply le_min
      · have := norm_sub_le (-(r + b) * kf (r + b) ^ 3) (-r * kf r ^ 3)
        have := norm_kf1_le hδ hδ1 hr2; have := norm_kf1_le hδ hδ1 hr1
        have e : 54 / δ ^ 3 = 27 / δ ^ 3 + 27 / δ ^ 3 := by ring
        linarith
      · -- along [r, r + b] the kernel `k′` has derivative `k″`, bounded by `486/δ⁵`
        have hsub : segment ℝ r (r + b) ⊆ St δ := (convex_St δ).segment_subset hr1 hr2
        have := (convex_segment r (r + b)).norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun x => -x * kf x ^ 3) (f' := fun x => kf x ^ 5 * (2 * x ^ 2 - 1)) (C := 486 / δ ^ 5)
          (fun x hx => (hasDerivAt_kf1 hδ (hsub hx)).hasDerivWithinAt)
          (fun x hx => norm_kf2_le hδ hδ1 (hsub hx)) (left_mem_segment ℝ r (r + b)) (right_mem_segment ℝ r (r + b))
        simp only [add_sub_cancel_left] at this
        calc _ ≤ 486 / δ ^ 5 * ‖b‖ := this
          _ = 486 * ‖b‖ / δ ^ 5 := by ring
    have := (convex_segment (0 : ℂ) ((l : ℂ) * a)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    simp only [zero_add, sub_zero, kf_zero] at this
    calc _ ≤ min (54 / δ ^ 3) (486 * ‖b‖ / δ ^ 5) * ‖(l : ℂ) * a‖ := this
      _ = _ := mul_comm _ _
  -- φ(σ) = ash(σ + b) − ash σ − ash b − σ(k(b) − 1), with φ′ = ψ(σ) − ψ(0)
  have hderiv : ∀ σ ∈ segment ℝ (0 : ℂ) a,
      HasDerivWithinAt (fun x => ash (x + b) - ash x - ash b - x * (kf b - 1))
        ((kf (σ + b) - kf σ) - (kf b - 1)) (segment ℝ (0 : ℂ) a) σ := by
    intro σ hσ
    have hs := (convex_St δ).segment_subset h0 h1 hσ
    have hsb : σ + b ∈ St δ := by
      rw [segment_eq_image'] at hσ
      obtain ⟨l, hl, e⟩ := hσ
      have : σ + b = ((l : ℝ) : ℂ) * a + ((1 : ℝ) : ℂ) * b := by rw [← e]; simp [Complex.real_smul]
      rw [this]; exact mem_St_of_corners h1 h2 h3 hδ1 hl ⟨zero_le_one, le_rfl⟩
    have h := (((hasDerivAt_ash (strip hδ hsb)).comp σ ((hasDerivAt_id σ).add_const b)).sub
      (hasDerivAt_ash (strip hδ hs))).sub_const (ash b) |>.sub ((hasDerivAt_id σ).mul_const (kf b - 1))
    simp only [id, mul_one, one_mul] at h
    refine (h.congr_deriv ?_).hasDerivWithinAt
    unfold kf; ring
  have hbd : ∀ σ ∈ segment ℝ (0 : ℂ) a, ‖(kf (σ + b) - kf σ) - (kf b - 1)‖ ≤ ‖a‖ * min (54 / δ ^ 3) (486 * ‖b‖ / δ ^ 5) := by
    intro σ hσ
    refine (hψ σ hσ).trans ?_
    have hm : 0 ≤ min (54 / δ ^ 3) (486 * ‖b‖ / δ ^ 5) := le_min (by positivity) (by positivity)
    gcongr
    rw [segment_eq_image'] at hσ
    obtain ⟨l, hl, e⟩ := hσ
    rw [← e]; simp [Complex.real_smul]
    rw [abs_of_nonneg hl.1]; nlinarith [hl.2, norm_nonneg a]
  have := (convex_segment (0 : ℂ) a).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  simp only [zero_add, zero_mul, sub_zero, ash_zero, sub_self] at this
  calc _ ≤ ‖a‖ * min (54 / δ ^ 3) (486 * ‖b‖ / δ ^ 5) * ‖a‖ := this
    _ = _ := by ring

end Cvs.Upstream.ArsinhLipschitzStrip
