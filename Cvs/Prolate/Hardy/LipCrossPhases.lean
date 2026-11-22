import Mathlib
import Cvs.Prolate.Hardy.CarrierBoundaryValues
import Cvs.Prolate.Hardy.ColumnWaveErrorBound
import Cvs.Prolate.Hardy.LipPhaseDecay
import Cvs.Prolate.Hardy.LipSymmetricPieces
import Cvs.Upstream.RiemannLebesgueNonStationary

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cross phases on the lips `½ < |x| < ℓ` are non-stationary

`S' = x/S(x) > 1` there, and `> 2` exactly when `|x| < ℓ = 1/√3`; so `2x`, `2(x − S)`, `S` and `2x − S` have
derivatives of one sign on each lip, and `∫_{lips} g cos(cφ) → 0`, `∫_{lips} g sin(cφ) → 0` for integrable `g`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Prolate.Hardy.LipCrossPhases
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.CarrierBoundaryValues (sR)
open Cvs.Prolate.Hardy.LipSymmetricPieces (symS)
open Cvs.Prolate.Hardy.ColumnWaveErrorBound (ell)

theorem sR_of_pos {x : ℝ} (hx : 0 ≤ x) : sR x = √(x ^ 2 - 1 / 4) := by rw [sR, if_pos hx]

theorem sR_of_neg {x : ℝ} (hx : x < 0) : sR x = -√(x ^ 2 - 1 / 4) := by rw [sR, if_neg (not_le.2 hx)]

theorem sqrt_pos_abs {x : ℝ} (hx : 1 / 2 < |x|) : 0 < √(x ^ 2 - 1 / 4) :=
  Real.sqrt_pos.2 (by nlinarith [sq_abs x, abs_nonneg x])

theorem ratio_eq (x : ℝ) : x / sR x = |x| / √(x ^ 2 - 1 / 4) := by
  rcases le_or_gt 0 x with h | h
  · rw [sR_of_pos h, abs_of_nonneg h]
  · rw [sR_of_neg h, abs_of_neg h, div_neg, neg_div]

/-- `S' = x/S(x)` on `|x| > ½`. -/
theorem hasDerivAt_sR {x : ℝ} (hx : 1 / 2 < |x|) : HasDerivAt sR (x / sR x) x := by
  rcases le_or_gt 0 x with h | h
  · have hx' : 1 / 2 < x := by rwa [abs_of_nonneg h] at hx
    have hev : sR =ᶠ[𝓝 x] fun y => √(y ^ 2 - 1 / 4) := by
      filter_upwards [lt_mem_nhds (show (0 : ℝ) < x by linarith)] with y hy using sR_of_pos hy.le
    rw [sR_of_pos h]
    exact (Cvs.Prolate.Hardy.LipPhaseDecay.hasDerivAt_sqrt_lip hx').congr_of_eventuallyEq hev
  · have hx' : 1 / 2 < -x := by rwa [abs_of_neg h] at hx
    have hev : sR =ᶠ[𝓝 x] fun y => -√(y ^ 2 - 1 / 4) := by
      filter_upwards [gt_mem_nhds h] with y hy using sR_of_neg hy
    have h1 := (Cvs.Prolate.Hardy.LipPhaseDecay.hasDerivAt_sqrt_lip hx').comp x (hasDerivAt_neg x)
    have h2 : HasDerivAt (fun y => -√(y ^ 2 - 1 / 4)) (x / -√(x ^ 2 - 1 / 4)) x := by
      have e : (fun y => -√(y ^ 2 - 1 / 4)) = fun y => -((fun y => √(y ^ 2 - 1 / 4)) ∘ Neg.neg) y := by
        ext y; simp
      rw [e]
      refine h1.neg.congr_deriv ?_
      rw [neg_sq]; field_simp
    rw [sR_of_neg h]
    exact h2.congr_of_eventuallyEq hev

theorem one_lt_ratio {x : ℝ} (hx : 1 / 2 < |x|) : 1 < x / sR x := by
  rw [ratio_eq x, one_lt_div (sqrt_pos_abs hx)]
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 1 / 4 by nlinarith [sq_abs x, abs_nonneg x])
  nlinarith [sqrt_pos_abs hx, sq_abs x, abs_nonneg x, Real.sqrt_nonneg (x ^ 2 - 1 / 4)]

theorem two_lt_ratio {x : ℝ} (hx : 1 / 2 < |x|) (hxl : |x| < ell) : 2 < x / sR x := by
  rw [ratio_eq x, lt_div_iff₀ (sqrt_pos_abs hx)]
  have hs := sqrt_pos_abs hx
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 1 / 4 by nlinarith [sq_abs x, abs_nonneg x])
  have h3 : x ^ 2 < 1 / 3 := by
    have : |x| * √3 < 1 := by rw [ell, lt_div_iff₀ (by positivity)] at hxl; exact hxl
    have h33 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith [sq_abs x, abs_nonneg x, Real.sqrt_nonneg 3]
  have : (2 * √(x ^ 2 - 1 / 4)) ^ 2 < |x| ^ 2 := by rw [mul_pow, h, sq_abs]; nlinarith
  nlinarith [abs_nonneg x]

/-- A phase with derivative of one sign on `(a, b)` is non-stationary there. -/
theorem tendsto_Ioo {a b : ℝ} {φ φ' : ℝ → ℝ} (hd : ∀ x ∈ Ioo a b, HasDerivAt φ (φ' x) x)
    (hsgn : (∀ x ∈ Ioo a b, 0 < φ' x) ∨ ∀ x ∈ Ioo a b, φ' x < 0) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo a b)) :
    Tendsto (fun c : ℝ => ∫ x in Ioo a b, g x * Real.cos (c * φ x)) atTop (𝓝 0) ∧
      Tendsto (fun c : ℝ => ∫ x in Ioo a b, g x * Real.sin (c * φ x)) atTop (𝓝 0) := by
  have hcont : ContinuousOn φ (Ioo a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hdw : ∀ x ∈ Ioo a b, HasDerivWithinAt φ (φ' x) (Ioo a b) x := fun x hx => (hd x hx).hasDerivWithinAt
  have hdi : ∀ x ∈ interior (Ioo a b), HasDerivWithinAt φ (φ' x) (interior (Ioo a b)) x := by
    rw [interior_Ioo]; exact hdw
  have hinj : InjOn φ (Ioo a b) := by
    rcases hsgn with h | h
    · exact (strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo a b) hcont hdi
        (by rw [interior_Ioo]; exact h)).injOn
    · exact (strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioo a b) hcont hdi
        (by rw [interior_Ioo]; exact h)).injOn
  have hne : ∀ x ∈ Ioo a b, φ' x ≠ 0 := by
    rcases hsgn with h | h
    · exact fun x hx => (h x hx).ne'
    · exact fun x hx => (h x hx).ne
  exact ⟨Cvs.Upstream.RiemannLebesgueNonStationary.tendsto_setIntegral_mul_cos_comp measurableSet_Ioo hdw hinj hne hg,
    Cvs.Upstream.RiemannLebesgueNonStationary.tendsto_setIntegral_mul_sin_comp measurableSet_Ioo hdw hinj hne hg⟩

/-- The right and left lips. -/
abbrev lipR : Set ℝ := Ioo (1 / 2) ell
abbrev lipL : Set ℝ := Ioo (-ell) (-(1 / 2))

theorem abs_of_mem_lipR {x : ℝ} (hx : x ∈ lipR) : 1 / 2 < |x| ∧ |x| < ell := by
  rw [abs_of_pos (by linarith [hx.1])]; exact hx

theorem abs_of_mem_lipL {x : ℝ} (hx : x ∈ lipL) : 1 / 2 < |x| ∧ |x| < ell := by
  rw [abs_of_neg (by linarith [hx.2])]; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- The four cross phases. -/
def phase : Fin 4 → ℝ → ℝ
  | 0 => fun x => 2 * x
  | 1 => fun x => 2 * (x - sR x)
  | 2 => fun x => sR x
  | 3 => fun x => 2 * x - sR x

/-- Their derivatives. -/
def phase' : Fin 4 → ℝ → ℝ
  | 0 => fun _ => 2
  | 1 => fun x => 2 * (1 - x / sR x)
  | 2 => fun x => x / sR x
  | 3 => fun x => 2 - x / sR x

theorem hasDerivAt_phase (j : Fin 4) {x : ℝ} (hx : 1 / 2 < |x|) : HasDerivAt (phase j) (phase' j x) x := by
  have hs := hasDerivAt_sR hx
  fin_cases j
  · simpa [phase, phase'] using (hasDerivAt_id x).const_mul 2
  · simpa [phase, phase'] using ((hasDerivAt_id x).sub hs).const_mul 2
  · simpa [phase, phase'] using hs
  · show HasDerivAt (fun y => 2 * y - sR y) (2 - x / sR x) x
    exact (show HasDerivAt (fun y : ℝ => 2 * y) 2 x by simpa using (hasDerivAt_id x).const_mul 2).sub hs

theorem phase'_sgn (j : Fin 4) {x : ℝ} (hx : 1 / 2 < |x|) (hxl : |x| < ell) :
    (0 < phase' j x ∧ (j = 0 ∨ j = 2)) ∨ (phase' j x < 0 ∧ (j = 1 ∨ j = 3)) := by
  have h1 := one_lt_ratio hx
  have h2 := two_lt_ratio hx hxl
  fin_cases j
  · left; simp [phase']
  · right; simp only [phase']; constructor <;> [linarith; simp]
  · left; simp only [phase']; constructor <;> [linarith; simp]
  · right; simp only [phase']; constructor <;> [linarith; simp]

theorem tendsto_piece (j : Fin 4) {s : Set ℝ} (hs : s = lipR ∨ s = lipL) {g : ℝ → ℝ} (hg : IntegrableOn g s) :
    Tendsto (fun c : ℝ => ∫ x in s, g x * Real.cos (c * phase j x)) atTop (𝓝 0) ∧
      Tendsto (fun c : ℝ => ∫ x in s, g x * Real.sin (c * phase j x)) atTop (𝓝 0) := by
  have hab : ∀ x ∈ s, 1 / 2 < |x| ∧ |x| < ell := by
    rcases hs with rfl | rfl
    · exact fun x hx => abs_of_mem_lipR hx
    · exact fun x hx => abs_of_mem_lipL hx
  have hsgn : (∀ x ∈ s, 0 < phase' j x) ∨ ∀ x ∈ s, phase' j x < 0 := by
    fin_cases j
    · left; intro x hx; rcases phase'_sgn 0 (hab x hx).1 (hab x hx).2 with h | h
      · exact h.1
      · simp at h
    · right; intro x hx; rcases phase'_sgn 1 (hab x hx).1 (hab x hx).2 with h | h
      · simp at h
      · exact h.1
    · left; intro x hx; rcases phase'_sgn 2 (hab x hx).1 (hab x hx).2 with h | h
      · exact h.1
      · simp at h
    · right; intro x hx; rcases phase'_sgn 3 (hab x hx).1 (hab x hx).2 with h | h
      · simp at h
      · exact h.1
  rcases hs with rfl | rfl
  · exact tendsto_Ioo (fun x hx => hasDerivAt_phase j (hab x hx).1) hsgn hg
  · exact tendsto_Ioo (fun x hx => hasDerivAt_phase j (hab x hx).1) hsgn hg

theorem symS_ae_eq : (symS (1 / 2) ell : Set ℝ) =ᵐ[volume] (lipR ∪ lipL : Set ℝ) := by
  unfold symS
  exact (Ioo_ae_eq_Ioc.symm).union Ioo_ae_eq_Ioc.symm

theorem disjoint_lips : Disjoint lipR lipL := by
  rw [Set.disjoint_left]; intro x h1 h2; linarith [h1.1, h2.2]

theorem setIntegral_symS (F : ℝ → ℝ) (hF : IntegrableOn F (symS (1 / 2) ell)) :
    ∫ x in symS (1 / 2) ell, F x = (∫ x in lipR, F x) + ∫ x in lipL, F x := by
  rw [setIntegral_congr_set symS_ae_eq]
  have hF' : IntegrableOn F (lipR ∪ lipL) := hF.congr_set_ae symS_ae_eq.symm
  exact setIntegral_union disjoint_lips measurableSet_Ioo (hF'.mono_set subset_union_left)
    (hF'.mono_set subset_union_right)

/-- **The lip Riemann–Lebesgue lemma** for the four cross phases. -/
theorem tendsto_lips (j : Fin 4) {g : ℝ → ℝ} (hg : IntegrableOn g (symS (1 / 2) ell)) :
    Tendsto (fun c : ℝ => ∫ x in symS (1 / 2) ell, g x * Real.cos (c * phase j x)) atTop (𝓝 0) ∧
      Tendsto (fun c : ℝ => ∫ x in symS (1 / 2) ell, g x * Real.sin (c * phase j x)) atTop (𝓝 0) := by
  have hg' : IntegrableOn g (lipR ∪ lipL) := hg.congr_set_ae symS_ae_eq.symm
  have hR := tendsto_piece j (Or.inl rfl) (hg'.mono_set subset_union_left)
  have hL := tendsto_piece j (Or.inr rfl) (hg'.mono_set subset_union_right)
  have hcos : ∀ c : ℝ, IntegrableOn (fun x => g x * Real.cos (c * phase j x)) (symS (1 / 2) ell) := fun c =>
    hg.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by
      fin_cases j <;> simp only [phase] <;> have := Cvs.Prolate.Hardy.CarrierBoundaryValues.continuous_sR <;> fun_prop))
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
  have hsin : ∀ c : ℝ, IntegrableOn (fun x => g x * Real.sin (c * phase j x)) (symS (1 / 2) ell) := fun c =>
    hg.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by
      fin_cases j <;> simp only [phase] <;> have := Cvs.Prolate.Hardy.CarrierBoundaryValues.continuous_sR <;> fun_prop))
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_sin_le_one _)
  constructor
  · simpa using (hR.1.add hL.1).congr fun c => (setIntegral_symS _ (hcos c)).symm
  · simpa using (hR.2.add hL.2).congr fun c => (setIntegral_symS _ (hsin c)).symm

end Cvs.Prolate.Hardy.LipCrossPhases

end
