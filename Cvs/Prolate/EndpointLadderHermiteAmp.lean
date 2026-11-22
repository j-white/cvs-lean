import Mathlib
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EndpointLadder
import Cvs.Prolate.EvenAngularPeak
import Cvs.Prolate.LadderRatioClosedForm
import Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint
import Cvs.Prolate.LiouvilleGreen.WkbEndpointLower
import Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The endpoint ladder at the Hermite amplitude

For an even `L²`-normalised angular solution, `((1 − s²)g′g)′ = (1 − s²)g′² + (c²s² − χ)g²` gives
`∫₀¹ (1 − s²)g′² + c²s²g² = χ/2`; so `g² ≤ 1 + 2√(χ/3)` on `[0, 1/2]` (AM–GM Agmon) and, with `∫_a^1 g² ≤ 1/8` at
`a = 2√χ/c`, the peak has `g(m)² ≥ 3c/(16√χ)`. The ladder of Cvs.Prolate.EndpointLadder then reads
`g_b(1)² ≥ B² (3c/(16√χ_b))/(1 + 2√(χ_a/3)) R^{(χ_b − χ_a)/c} g_a(1)²`, both amplitudes at the Hermite scale.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.EndpointLadderHermiteAmp

open Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent (U)
open Cvs.Prolate.EndpointLadder (aS startB ladR)

/-- A nonnegative continuous function on `[0, 1]` integrates over `[a, b] ⊆ [0, 1]` to at most its integral over
`[0, 1]`. -/
theorem integral_le_unit {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc 0 1)) (h0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ f s)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : ∫ s in a..b, f s ≤ ∫ s in (0 : ℝ)..1, f s := by
  refine intervalIntegral.integral_mono_interval ha hab hb ?_ ?_
  · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => h0 s ⟨hs.1.le, hs.2⟩)
  · exact (by rwa [uIcc_of_le zero_le_one] : ContinuousOn f (uIcc 0 1)).intervalIntegrable

/-- **The energy identity on the half interval**: for an even angular solution,
`∫₀¹ ((1 − s²)g′² + c²s²g²) = χ ∫₀¹ g²`. -/
theorem energy_half {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    ∫ s in (0 : ℝ)..1, ((1 - s ^ 2) * g₁ s ^ 2 + c ^ 2 * s ^ 2 * g s ^ 2) = χ * ∫ s in (0 : ℝ)..1, g s ^ 2 := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hm : ∀ s ∈ uIcc (0 : ℝ) 1, s ∈ uIcc (-1 : ℝ) 1 := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs; rw [hI]; exact ⟨by linarith [hs.1], hs.2⟩
  have hgc : ContinuousOn g (uIcc (0 : ℝ) 1) := fun s hs => (hg s (hm s hs)).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (uIcc (0 : ℝ) 1) := fun s hs => (hg₁ s (hm s hs)).continuousAt.continuousWithinAt
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => (1 - t ^ 2) * g₁ t * g t)
      ((1 - t ^ 2) * g₁ t ^ 2 + (c ^ 2 * t ^ 2 - χ) * g t ^ 2) t := by
    intro t ht
    have hp : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_sub 1)
    have h : HasDerivAt (fun t => (1 - t ^ 2) * g₁ t * g t)
        ((-(2 * t) * g₁ t + (1 - t ^ 2) * g₂ t) * g t + (1 - t ^ 2) * g₁ t * g₁ t) t :=
      (hp.mul (hg₁ t (hm t ht))).mul (hg t (hm t ht))
    refine h.congr_deriv ?_
    have e := hang t (hm t ht)
    linear_combination g t * e
  have hcont : ContinuousOn (fun t => (1 - t ^ 2) * g₁ t ^ 2 + (c ^ 2 * t ^ 2 - χ) * g t ^ 2) (uIcc (0 : ℝ) 1) :=
    ((continuousOn_const.sub (continuousOn_id.pow 2)).mul (hg₁c.pow 2)).add
      (((continuousOn_const.mul (continuousOn_id.pow 2)).sub continuousOn_const).mul (hgc.pow 2))
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  have h0 : g₁ 0 = 0 := Cvs.Prolate.EvenAngularPeak.deriv_zero_of_even (hg 0 (by rw [hI]; norm_num)) heven
  simp only [h0, one_pow, sub_self, zero_mul, mul_zero] at hF
  have hA : IntervalIntegrable (fun s => (1 - s ^ 2) * g₁ s ^ 2 + c ^ 2 * s ^ 2 * g s ^ 2) volume 0 1 :=
    (((continuousOn_const.sub (continuousOn_id.pow 2)).mul (hg₁c.pow 2)).add
      ((continuousOn_const.mul (continuousOn_id.pow 2)).mul (hgc.pow 2))).intervalIntegrable
  have hB : IntervalIntegrable (fun s => χ * g s ^ 2) volume 0 1 := (continuousOn_const.mul (hgc.pow 2)).intervalIntegrable
  have hsplit : (∫ s in (0 : ℝ)..1, ((1 - s ^ 2) * g₁ s ^ 2 + (c ^ 2 * s ^ 2 - χ) * g s ^ 2))
      = (∫ s in (0 : ℝ)..1, ((1 - s ^ 2) * g₁ s ^ 2 + c ^ 2 * s ^ 2 * g s ^ 2)) - ∫ s in (0 : ℝ)..1, χ * g s ^ 2 := by
    rw [← intervalIntegral.integral_sub hA hB]
    congr 1; ext s; ring
  rw [hsplit, intervalIntegral.integral_const_mul] at hF
  linarith

/-- **The energy bounds**: an even `L²`-normalised angular solution has `∫₀¹ g² = 1/2`,
`∫₀¹ (1 − s²)g′² ≤ χ/2` and `∫₀¹ c²s²g² ≤ χ/2`. -/
theorem energy_bounds {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1) :
    (∫ s in (0 : ℝ)..1, g s ^ 2) = 1 / 2 ∧ (∫ s in (0 : ℝ)..1, (1 - s ^ 2) * g₁ s ^ 2) ≤ χ / 2 ∧
      ∫ s in (0 : ℝ)..1, c ^ 2 * s ^ 2 * g s ^ 2 ≤ χ / 2 := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc' : ContinuousOn g (Icc (-1 : ℝ) 1) := fun s hs => (hg s (hI ▸ hs)).continuousAt.continuousWithinAt
  have hhalf : (∫ s in (0 : ℝ)..1, g s ^ 2) = 1 / 2 := by
    have := Cvs.Prolate.AngularBesselInequality.integral_sq_even hgc' heven; linarith
  have hE := energy_half hg hg₁ hang heven
  rw [hhalf] at hE
  have hm : ∀ s ∈ Icc (0 : ℝ) 1, s ∈ uIcc (-1 : ℝ) 1 := fun s hs => by rw [hI]; exact ⟨by linarith [hs.1], hs.2⟩
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := hgc'.mono (Icc_subset_Icc (by norm_num) le_rfl)
  have hg₁c : ContinuousOn g₁ (Icc (0 : ℝ) 1) := fun s hs => (hg₁ s (hm s hs)).continuousAt.continuousWithinAt
  have hu : ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) → IntervalIntegrable f volume 0 1 := fun f hf => by
    rw [← uIcc_of_le zero_le_one] at hf; exact hf.intervalIntegrable
  have h1c : ContinuousOn (fun s => (1 - s ^ 2) * g₁ s ^ 2) (Icc 0 1) :=
    (continuousOn_const.sub (continuousOn_id.pow 2)).mul (hg₁c.pow 2)
  have h2c : ContinuousOn (fun s => c ^ 2 * s ^ 2 * g s ^ 2) (Icc 0 1) :=
    (continuousOn_const.mul (continuousOn_id.pow 2)).mul (hgc.pow 2)
  rw [intervalIntegral.integral_add (hu _ h1c) (hu _ h2c)] at hE
  have hn1 : 0 ≤ ∫ s in (0 : ℝ)..1, (1 - s ^ 2) * g₁ s ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun s hs => mul_nonneg (by nlinarith [hs.1, hs.2]) (sq_nonneg _)
  have hn2 : 0 ≤ ∫ s in (0 : ℝ)..1, c ^ 2 * s ^ 2 * g s ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun s _ => by positivity
  exact ⟨hhalf, by linarith, by linarith⟩

set_option maxHeartbeats 1000000 in
/-- **The Agmon bound at the Hermite scale**: an even `L²`-normalised angular solution with `0 < χ` has
`g(s)² ≤ 1 + 2√(χ/3)` on `[0, 1/2]`. -/
theorem sq_le_sup {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1) (hχ : 0 < χ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) : g s ^ 2 ≤ 1 + 2 * √(χ / 3) := by
  obtain ⟨hhalf, hgrad, -⟩ := energy_bounds hg hg₁ hang heven hnorm
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hm : ∀ s ∈ Icc (0 : ℝ) 1, s ∈ uIcc (-1 : ℝ) 1 := fun s hs => by rw [hI]; exact ⟨by linarith [hs.1], hs.2⟩
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := fun s hs => (hg s (hm s hs)).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (Icc (0 : ℝ) 1) := fun s hs => (hg₁ s (hm s hs)).continuousAt.continuousWithinAt
  set l := 2 * √(χ / 3) with hld
  have hl : 0 < l := by positivity
  set f : ℝ → ℝ := fun t => l * g t ^ 2 + g₁ t ^ 2 / l with hfd
  have hfc : ContinuousOn f (Icc 0 1) := (continuousOn_const.mul (hgc.pow 2)).add ((hg₁c.pow 2).div_const _)
  have hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t := fun t _ => by simp only [hfd]; positivity
  have hamgm : ∀ t, |2 * g t * g₁ t| ≤ f t := by
    intro t
    have e1 : l * g t ^ 2 + g₁ t ^ 2 / l - 2 * g t * g₁ t = (l * g t - g₁ t) ^ 2 / l := by field_simp; ring
    have e2 : l * g t ^ 2 + g₁ t ^ 2 / l + 2 * g t * g₁ t = (l * g t + g₁ t) ^ 2 / l := by field_simp; ring
    have p1 : 0 ≤ (l * g t - g₁ t) ^ 2 / l := by positivity
    have p2 : 0 ≤ (l * g t + g₁ t) ^ 2 / l := by positivity
    simp only [hfd]
    rw [abs_le]
    constructor <;> linarith
  set E := ∫ t in (0 : ℝ)..1 / 2, f t with hEd
  have hfi : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable f volume a b := fun a b ha hab hb =>
    (hfc.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb)).intervalIntegrable
  have hdsq : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => g s ^ 2) (2 * g x * g₁ x) x := fun x hx =>
    Cvs.Prolate.EvenAngularPeak.hasDerivAt_sq (hg x (hm x hx))
  have hdc : ContinuousOn (fun x => 2 * g x * g₁ x) (Icc 0 1) := (continuousOn_const.mul hgc).mul hg₁c
  have hpair : ∀ t ∈ Icc (0 : ℝ) (1 / 2), g s ^ 2 ≤ g t ^ 2 + E := by
    intro t ht
    have hsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 / 2 →
        (∫ x in a..b, 2 * g x * g₁ x) ≤ E ∧ -(∫ x in a..b, 2 * g x * g₁ x) ≤ E := by
      intro a b ha hab hb
      have hii : IntervalIntegrable (fun x => 2 * g x * g₁ x) volume a b :=
        (hdc.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha (by linarith))).intervalIntegrable
      have hfab : (∫ x in a..b, f x) ≤ E :=
        intervalIntegral.integral_mono_interval ha hab hb
          ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun x hx =>
            hf0 x ⟨hx.1.le, by linarith [hx.2]⟩)) (hfi 0 (1 / 2) le_rfl (by norm_num) (by norm_num))
      have hle1 : (∫ x in a..b, 2 * g x * g₁ x) ≤ ∫ x in a..b, f x :=
        intervalIntegral.integral_mono_on hab hii (hfi a b ha hab (by linarith)) fun x _ => (le_abs_self _).trans (hamgm x)
      have hle2 : -(∫ x in a..b, 2 * g x * g₁ x) ≤ ∫ x in a..b, f x := by
        rw [← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_mono_on hab hii.neg (hfi a b ha hab (by linarith)) fun x _ =>
          (neg_le_abs _).trans (hamgm x)
      exact ⟨hle1.trans hfab, hle2.trans hfab⟩
    have hftc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 / 2 → (∫ x in a..b, 2 * g x * g₁ x) = g b ^ 2 - g a ^ 2 := by
      intro a b ha hab hb
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => by rw [uIcc_of_le hab] at hx; exact hdsq x ⟨ha.trans hx.1, by linarith [hx.2]⟩)
        (hdc.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha (by linarith))).intervalIntegrable
    rcases le_total t s with h | h
    · have := (hsub t s ht.1 h hs.2).1; rw [hftc t s ht.1 h hs.2] at this; linarith
    · have := (hsub s t hs.1 h ht.2).2; rw [hftc s t hs.1 h ht.2] at this; linarith
  -- average over `t ∈ [0, 1/2]`
  have hgi : IntervalIntegrable (fun t => g t ^ 2) volume 0 (1 / 2) :=
    ((hgc.pow 2).mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable
  have havg := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 2) intervalIntegrable_const
    (hgi.add intervalIntegrable_const) fun t ht => hpair t ht
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hgi intervalIntegrable_const,
    intervalIntegral.integral_const] at havg
  simp only [smul_eq_mul, sub_zero] at havg
  -- the two pieces of `E`
  have hJ1 : (∫ t in (0 : ℝ)..1 / 2, g t ^ 2) ≤ 1 / 2 := by
    exact (integral_le_unit (f := fun t => g t ^ 2) (hgc.pow 2) (fun _ _ => sq_nonneg _) le_rfl (by norm_num)
      (by norm_num)).trans hhalf.le
  have hJ2 : (∫ t in (0 : ℝ)..1 / 2, g₁ t ^ 2) ≤ 4 / 3 * (χ / 2) := by
    have hp : (∫ t in (0 : ℝ)..1 / 2, g₁ t ^ 2) ≤ ∫ t in (0 : ℝ)..1 / 2, 4 / 3 * ((1 - t ^ 2) * g₁ t ^ 2) := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        ((hg₁c.pow 2).mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable
        ((continuousOn_const.mul ((continuousOn_const.sub (continuousOn_id.pow 2)).mul (hg₁c.pow 2))).mono
          (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable
        fun t ht => ?_
      have : 3 / 4 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      nlinarith [sq_nonneg (g₁ t)]
    rw [intervalIntegral.integral_const_mul] at hp
    have hq := integral_le_unit (f := fun t => (1 - t ^ 2) * g₁ t ^ 2)
      ((continuousOn_const.sub (continuousOn_id.pow 2)).mul (hg₁c.pow 2))
      (fun t ht => mul_nonneg (by nlinarith [ht.1, ht.2]) (sq_nonneg _)) le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    nlinarith
  have hEsplit : E = l * (∫ t in (0 : ℝ)..1 / 2, g t ^ 2) + (∫ t in (0 : ℝ)..1 / 2, g₁ t ^ 2) / l := by
    rw [hEd, hfd]
    rw [intervalIntegral.integral_add (hgi.const_mul l) ?_, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_div]
    exact (((hg₁c.pow 2).div_const l).mono
      (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable
  have hsq : √(χ / 3) ^ 2 = χ / 3 := Real.sq_sqrt (by positivity)
  have hr0 : 0 < √(χ / 3) := by positivity
  have hEle : E ≤ l / 2 + 4 / 3 * (χ / 2) / l := by
    rw [hEsplit]
    have h1 : l * (∫ t in (0 : ℝ)..1 / 2, g t ^ 2) ≤ l * (1 / 2) := mul_le_mul_of_nonneg_left hJ1 hl.le
    have h2 : (∫ t in (0 : ℝ)..1 / 2, g₁ t ^ 2) / l ≤ 4 / 3 * (χ / 2) / l := div_le_div_of_nonneg_right hJ2 hl.le
    linarith
  have hval : l / 2 + 4 / 3 * (χ / 2) / l = 2 * √(χ / 3) := by
    rw [hld]; field_simp; rw [hsq]; ring
  have hgi0 : 0 ≤ ∫ t in (0 : ℝ)..1 / 2, g t ^ 2 := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  nlinarith

/-- **The peak at the Hermite scale**: if `g²` on `[0, 1]` is at most `M`, `∫₀¹ g² = 1/2`, `∫₀¹ c²s²g² ≤ χ/2` and
`a = 2√χ/c ≤ 1`, then `3c/(16√χ) ≤ M`. -/
theorem peak_ge {g : ℝ → ℝ} {c χ M : ℝ} (hc : 0 < c) (hχ : 0 < χ) (hgc : ContinuousOn g (Icc 0 1))
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 ≤ M) (hhalf : (∫ s in (0 : ℝ)..1, g s ^ 2) = 1 / 2)
    (hmom : ∫ s in (0 : ℝ)..1, c ^ 2 * s ^ 2 * g s ^ 2 ≤ χ / 2) (ha1 : aS c χ ≤ 1) :
    3 * c / (16 * √χ) ≤ M := by
  set a := aS c χ with had
  have hr : 0 < √χ := Real.sqrt_pos.2 hχ
  have ha0 : 0 < a := by rw [had]; unfold aS; positivity
  have ha2 : a ^ 2 = 4 * χ / c ^ 2 := by rw [had]; unfold aS; rw [div_pow, mul_pow, Real.sq_sqrt hχ.le]; ring
  have hu : ∀ {f : ℝ → ℝ} {x y : ℝ}, ContinuousOn f (Icc 0 1) → 0 ≤ x → x ≤ y → y ≤ 1 →
      IntervalIntegrable f volume x y := fun hf hx hxy hy =>
    (hf.mono (by rw [uIcc_of_le hxy]; exact Icc_subset_Icc hx hy)).intervalIntegrable
  have hsplit : (∫ s in (0 : ℝ)..a, g s ^ 2) + (∫ s in a..1, g s ^ 2) = ∫ s in (0 : ℝ)..1, g s ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hu (f := fun s => g s ^ 2) (hgc.pow 2) le_rfl ha0.le ha1)
      (hu (f := fun s => g s ^ 2) (hgc.pow 2) ha0.le ha1 le_rfl)
  rw [hhalf] at hsplit
  -- the inner piece
  have hin : (∫ s in (0 : ℝ)..a, g s ^ 2) ≤ a * M := by
    have := intervalIntegral.integral_mono_on ha0.le (hu (hgc.pow 2) le_rfl ha0.le ha1)
      (intervalIntegrable_const (c := M)) fun s hs => hM s ⟨hs.1, hs.2.trans ha1⟩
    simpa using this
  -- the outer piece
  have hmc : ContinuousOn (fun s => c ^ 2 * s ^ 2 * g s ^ 2) (Icc 0 1) :=
    (continuousOn_const.mul (continuousOn_id.pow 2)).mul (hgc.pow 2)
  have hout : (∫ s in a..1, g s ^ 2) ≤ (∫ s in a..1, c ^ 2 * s ^ 2 * g s ^ 2) / (c ^ 2 * a ^ 2) := by
    rw [le_div_iff₀ (by positivity), ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_mono_on ha1 (hu ((hgc.pow 2).mul_const _) ha0.le ha1 le_rfl)
      (hu hmc ha0.le ha1 le_rfl) fun s hs => ?_
    have : a ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ ha0.le hs.1 2
    have : c ^ 2 * a ^ 2 * g s ^ 2 ≤ c ^ 2 * s ^ 2 * g s ^ 2 := by
      have := mul_le_mul_of_nonneg_left this (sq_nonneg c); nlinarith [sq_nonneg (g s)]
    linarith
  have hmom' : (∫ s in a..1, c ^ 2 * s ^ 2 * g s ^ 2) ≤ χ / 2 :=
    (integral_le_unit hmc (fun _ _ => by positivity) ha0.le ha1 le_rfl).trans hmom
  have hca : c ^ 2 * a ^ 2 = 4 * χ := by rw [ha2]; field_simp
  rw [hca] at hout
  have hout' : (∫ s in a..1, g s ^ 2) ≤ 1 / 8 := by
    have := div_le_div_of_nonneg_right hmom' (by positivity : (0 : ℝ) ≤ 4 * χ)
    rw [show χ / 2 / (4 * χ) = 1 / 8 by field_simp; ring] at this
    linarith
  have haM : 3 / 8 ≤ a * M := by linarith
  have hae : a = 2 * √χ / c := rfl
  rw [div_le_iff₀ (by positivity)]
  rw [hae] at haM
  have : 3 / 8 * c ≤ 2 * √χ * M := by
    have := mul_le_mul_of_nonneg_right haM hc.le
    rw [show 2 * √χ / c * M * c = 2 * √χ * M by field_simp] at this; linarith
  nlinarith

/-- **The start at the Hermite scale**: with `a = 2√χ/c ≤ 1/2`, an even normalised angular solution with
`g(1) ≠ 0` has a sign `ε` with `εg > 0`, `(εg)(εg′) ≤ 0` on `[a, 1]` and `√(3c/(16√χ)) B ≤ εg(a)`. -/
theorem pos_start_sharp {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1)
    (hc : 0 < c) (hχ : 0 < χ) (ha2 : aS c χ ≤ 1 / 2) (hg1 : g 1 ≠ 0) :
    ∃ ε : ℝ, ε ^ 2 = 1 ∧ (∀ s ∈ Icc (aS c χ) 1, 0 < ε * g s ∧ (ε * g s) * (ε * g₁ s) ≤ 0) ∧
      √(3 * c / (16 * √χ)) * startB c χ ≤ ε * g (aS c χ) := by
  set T := √χ / c with hTd
  have hT0 : 0 < T := by positivity
  have haT : aS c χ = T + T := by unfold aS; rw [hTd]; ring
  have hT14 : T ≤ 1 / 4 := by linarith
  have h3 : 3 * χ ≤ c ^ 2 := by
    have h1 : √χ ≤ c / 4 := by rw [hTd, div_le_iff₀ hc] at hT14; linarith
    have := Real.sq_sqrt hχ.le
    nlinarith [Real.sqrt_nonneg χ]
  have hχc : χ < c ^ 2 := by nlinarith
  obtain ⟨ε, hε, m, hm, -, hpos, hmono, hmax⟩ :=
    Cvs.Prolate.EndpointLadder.exists_pos_peak hg hg₁ hang heven hnorm hc hχ hχc hg1
  have hma : m ≤ aS c χ := by rw [haT]; linarith [hm.2]
  refine ⟨ε, hε, fun s hs => ⟨hpos s ⟨hma.trans hs.1, hs.2⟩, hmono s ⟨hma.trans hs.1, hs.2⟩⟩, ?_⟩
  have hL := Cvs.Prolate.LiouvilleGreen.WkbEndpointLower.layer_ge (g := fun s => ε * g s) (g₁ := fun s => ε * g₁ s)
    (g₂ := fun s => ε * g₂ s) (m := m) (ε := T) (η := T)
    (fun s hs => (hg s hs).const_mul ε) (fun s hs => (hg₁ s hs).const_mul ε)
    (fun s hs => by have := hang s hs; linear_combination ε * this) hc hχ h3 hm.1 hm.2 hT0 le_rfl hT0
    (by rw [← haT]; exact ha2.trans (Cvs.Prolate.EndpointLadder.half_le_sm hc hχ)) hpos
  rw [← hTd] at hL
  simp only [sub_self, zero_div, exp_zero, mul_one] at hL
  -- the peak value
  obtain ⟨hhalf, -, hmom⟩ := energy_bounds hg hg₁ hang heven hnorm
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := fun s hs =>
    (hg s (by rw [hI]; exact ⟨by linarith [hs.1], hs.2⟩)).continuousAt.continuousWithinAt
  have hpk := peak_ge (M := (ε * g m) ^ 2) hc hχ hgc
    (fun s hs => by have := hmax s hs; rwa [mul_pow, hε, one_mul] at this) hhalf hmom (by linarith)
  have hgm0 : 0 < ε * g m := hpos m ⟨le_rfl, hm.2.trans (by linarith)⟩
  have hgm : √(3 * c / (16 * √χ)) ≤ ε * g m := by
    rw [← Real.sqrt_sq hgm0.le]; exact Real.sqrt_le_sqrt hpk
  rw [haT]
  unfold startB
  rw [← hTd]
  calc √(3 * c / (16 * √χ)) * exp (-(Cvs.Prolate.LiouvilleGreen.WkbEndpointLower.Kl c χ T * (T + T) / Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier.pp (T + T)))
      ≤ ε * g m * exp (-(Cvs.Prolate.LiouvilleGreen.WkbEndpointLower.Kl c χ T * (T + T) / Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier.pp (T + T))) :=
        mul_le_mul_of_nonneg_right hgm (exp_pos _).le
    _ ≤ ε * g (T + T) := hL

set_option maxHeartbeats 1000000 in
/-- **The endpoint ladder at the Hermite amplitude**: for even `L²`-normalised angular solutions `g_a`, `g_b` at
`0 < χ_a ≤ χ_b`, nonzero at `1`, with `a = 2√χ_b/c ≤ 1/2`:
`B² (3c/(16√χ_b))/(1 + 2√(χ_a/3)) R^{(χ_b − χ_a)/c} g_a(1)² ≤ g_b(1)²`, `B = startB c χ_b`, `R = ladR c χ_b`. -/
theorem ladder_sq_sharp {ga ga₁ ga₂ gb gb₁ gb₂ : ℝ → ℝ} {c χa χb : ℝ}
    (ha : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt ga (ga₁ t) t) (ha₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt ga₁ (ga₂ t) t)
    (hanga : ∀ t ∈ uIcc (-1 : ℝ) 1, (1 - t ^ 2) * ga₂ t - 2 * t * ga₁ t - c ^ 2 * t ^ 2 * ga t + χa * ga t = 0)
    (hevena : ∀ s ∈ Icc (-1 : ℝ) 1, ga (-s) = ga s) (hnorma : ∫ s in (-1 : ℝ)..1, ga s ^ 2 = 1)
    (hga1 : ga 1 ≠ 0)
    (hb : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt gb (gb₁ t) t) (hb₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt gb₁ (gb₂ t) t)
    (hangb : ∀ t ∈ uIcc (-1 : ℝ) 1, (1 - t ^ 2) * gb₂ t - 2 * t * gb₁ t - c ^ 2 * t ^ 2 * gb t + χb * gb t = 0)
    (hevenb : ∀ s ∈ Icc (-1 : ℝ) 1, gb (-s) = gb s) (hnormb : ∫ s in (-1 : ℝ)..1, gb s ^ 2 = 1)
    (hgb1 : gb 1 ≠ 0)
    (hc : 0 < c) (hχa : 0 < χa) (hχ : χa ≤ χb) (ha2 : aS c χb ≤ 1 / 2) :
    startB c χb ^ 2 * (3 * c / (16 * √χb)) / (1 + 2 * √(χa / 3)) * ladR c χb ^ ((χb - χa) / c) * ga 1 ^ 2
      ≤ gb 1 ^ 2 := by
  have hχb : 0 < χb := hχa.trans_le hχ
  set a := aS c χb with had
  have ha0 : 0 < a := by rw [had]; unfold aS; positivity
  have hTb : √χb / c ≤ 1 / 4 := by
    rw [had] at ha2; unfold aS at ha2
    have : 2 * √χb / c = 2 * (√χb / c) := by ring
    linarith
  have h3 : 3 * χb ≤ c ^ 2 := by
    have h1 : √χb ≤ c / 4 := by rw [div_le_iff₀ hc] at hTb; linarith
    have := Real.sq_sqrt hχb.le
    nlinarith [Real.sqrt_nonneg χb]
  have hχac : χa < c ^ 2 := by nlinarith
  obtain ⟨εb, hεb, hposb, hstart⟩ := pos_start_sharp hb hb₁ hangb hevenb hnormb hc hχb ha2 hgb1
  obtain ⟨εa, hεa, ma, hma, -, hposa, hmonoa, -⟩ :=
    Cvs.Prolate.EndpointLadder.exists_pos_peak ha ha₁ hanga hevena hnorma hc hχa hχac hga1
  have hmaa : ma ≤ a := by
    have : √χa / c ≤ √χb / c := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hχ) hc.le
    have h2 : √χb / c ≤ a := by
      rw [had]; unfold aS; rw [mul_div_assoc]; linarith [div_nonneg (Real.sqrt_nonneg χb) hc.le]
    linarith [hma.2]
  have hposa' : ∀ s ∈ Icc a 1, 0 < εa * ga s := fun s hs => hposa s ⟨hmaa.trans hs.1, hs.2⟩
  -- the amplitude of `g_a` at `a`
  set Ua := 1 + 2 * √(χa / 3) with hUad
  have hUa : 0 < Ua := by positivity
  have hA : εa * ga a ≤ √Ua := by
    have hsq := sq_le_sup ha ha₁ hanga hevena hnorma hχa (s := a) ⟨ha0.le, ha2⟩
    have h0 := hposa' a ⟨le_rfl, by linarith⟩
    rw [← Real.sqrt_sq h0.le]
    exact Real.sqrt_le_sqrt (by rw [mul_pow, hεa, one_mul]; exact hsq)
  -- the closed-form ratio on the positive versions
  have hR := Cvs.Prolate.LadderRatioClosedForm.log_ratio_closed (ga := fun t => εa * ga t) (ga₁ := fun t => εa * ga₁ t)
    (ga₂ := fun t => εa * ga₂ t) (gb := fun t => εb * gb t) (gb₁ := fun t => εb * gb₁ t)
    (gb₂ := fun t => εb * gb₂ t) (a := a)
    (fun t ht => (ha t ht).const_mul εa) (fun t ht => (ha₁ t ht).const_mul εa)
    (fun t ht => by have := hanga t ht; linear_combination εa * this)
    (fun t ht => (hb t ht).const_mul εb) (fun t ht => (hb₁ t ht).const_mul εb)
    (fun t ht => by have := hangb t ht; linear_combination εb * this)
    hc hχa hχ h3 (by rw [had]; rfl) (by rw [had]; exact ha2) hposa' (fun t ht => (hposb t ht).1)
    (fun t ht => Cvs.Prolate.EndpointLadder.U_nonneg (hposa' t ht) (hmonoa t ⟨hmaa.trans ht.1, ht.2⟩)
      (by nlinarith [ht.1, ht.2]))
    (fun t ht => Cvs.Prolate.EndpointLadder.U_nonneg (hposb t ht).1 (hposb t ht).2 (by nlinarith [ht.1, ht.2]))
  have hu := hposa' 1 ⟨by linarith, le_rfl⟩
  have hv := (hposb 1 ⟨by linarith, le_rfl⟩).1
  have hA0 := hposa' a ⟨le_rfl, by linarith⟩
  have hB0 := (hposb a ⟨le_rfl, by linarith⟩).1
  set u := εa * ga 1 with hud
  set v := εb * gb 1 with hvd
  set A := εa * ga a with hAd
  set B := εb * gb a with hBd
  have hRpos := Cvs.Prolate.EndpointLadder.ladR_pos hc hχb
  set x := (χb - χa) / c with hxd
  have hxR : (χb - χa) * (1 / (2 * c) * log (ladR c χb)) = x / 2 * log (ladR c χb) := by
    rw [hxd]; field_simp
  have hladR : ladR c χb = (2 * c + (2 / a + Cvs.Prolate.LadderRatioClosedForm.kap c χb a)) /
      (2 * c * a + (2 / a + Cvs.Prolate.LadderRatioClosedForm.kap c χb a)) := by rw [had]; rfl
  rw [← hladR, hxR, log_div hv.ne' hu.ne', log_div hB0.ne' hA0.ne'] at hR
  have hexp : ladR c χb ^ (x / 2) * u * B ≤ v * A := by
    have h1 : log (ladR c χb ^ (x / 2) * u * B) ≤ log (v * A) := by
      rw [log_mul (by positivity) hB0.ne', log_mul (by positivity) hu.ne', log_mul hv.ne' hA0.ne',
        Real.log_rpow hRpos]
      linarith
    exact (log_le_log_iff (by positivity) (by positivity)).1 h1
  set P := 3 * c / (16 * √χb) with hPd
  have hP : 0 < P := by positivity
  have hB' := Cvs.Prolate.EndpointLadder.startB_pos c χb
  have hv' : ladR c χb ^ (x / 2) * u * (√P * startB c χb) ≤ v * √Ua :=
    calc _ ≤ ladR c χb ^ (x / 2) * u * B := mul_le_mul_of_nonneg_left hstart (by positivity)
      _ ≤ v * A := hexp
      _ ≤ v * √Ua := mul_le_mul_of_nonneg_left hA hv.le
  have hsq : (ladR c χb ^ (x / 2)) ^ 2 = ladR c χb ^ x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hRpos.le]; norm_num
  have hga : ga 1 ^ 2 = u ^ 2 := by rw [hud, mul_pow, hεa, one_mul]
  have hgb : gb 1 ^ 2 = v ^ 2 := by rw [hvd, mul_pow, hεb, one_mul]
  rw [hga, hgb]
  have h0 : 0 ≤ ladR c χb ^ (x / 2) * u * (√P * startB c χb) := by positivity
  have hsq2 := pow_le_pow_left₀ h0 hv' 2
  have hPs : √P ^ 2 = P := Real.sq_sqrt hP.le
  have hUs : √Ua ^ 2 = Ua := Real.sq_sqrt hUa.le
  have e1 : (ladR c χb ^ (x / 2) * u * (√P * startB c χb)) ^ 2
      = startB c χb ^ 2 * √P ^ 2 * (ladR c χb ^ (x / 2)) ^ 2 * u ^ 2 := by ring
  have e2 : (v * √Ua) ^ 2 = v ^ 2 * Ua := by rw [mul_pow, hUs]
  rw [e1, hPs, hsq, e2] at hsq2
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hUa]
  linarith

end Cvs.Prolate.EndpointLadderHermiteAmp
