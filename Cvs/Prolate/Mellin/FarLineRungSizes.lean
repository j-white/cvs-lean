import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.Envelope.RungDuhamelRemainder
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.RungProfileOutsideCircle
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungProfileEntireExtension
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.WeilForm.OddPoleTermBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sizes entering the far-line bound of a rung profile

For `λ_k ≥ ½`: `|h_k(1)| ≤ 4c(1 − λ_k)^{1/2}` (Cvs.Prolate.Envelope.RungExteriorLaw), `∫|h_k| ≤ √2`, `M_k ≤ √c`; for the ground rung, which has no
zero, `M₀ = |h₀(0)|`, so the ground weight `α_j = ∫h_{4j}/∫h₀` has `α_j² M₀ ≤ c`.
-/

noncomputable section

open Real Set MeasureTheory Filter
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR lev IsLevelIdx)
open Cvs.Prolate.Mellin.RungProfileOutsideCircle (Mk)

namespace Cvs.Prolate.Mellin.FarLineRungSizes
open Cvs.ZeroCounting

/-- **The edge value against the plunge**: `|h_k(1)| ≤ 4c(1 − λ_k)^{1/2}` for `c ≥ 80`, `λ_k ≥ ½`. -/
theorem abs_rung_one_le {c : ℝ} (hc : 80 ≤ c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hχ : lev c k < c ^ 2)
    (hχ' : |lev c k| ≤ c ^ 2) (hl : 1 / 2 ≤ lamR c k) :
    |rung c k 1| ≤ 4 * c * (1 - lamR c k) ^ (1 / 2 : ℝ) := by
  have he := Cvs.Prolate.Envelope.RungExteriorLaw.edge_sq_le (by linarith) h hχ
  have hl1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one (by linarith) h
  have hω : 0 ≤ 1 - lamR c k := by linarith
  have hD : 2 * (c ^ 2 - lev c k) + 3 * c ≤ 5 * c ^ 2 := by
    have := (abs_le.1 hχ').1; nlinarith
  have hsq : rung c k 1 ^ 2 ≤ 16 * c ^ 2 * (1 - lamR c k) := by
    have h1 : rung c k 1 ^ 2 * lamR c k ≤ 72 / 49 * (5 * c ^ 2) * (1 - lamR c k) :=
      he.trans (by gcongr)
    nlinarith [sq_nonneg (rung c k 1)]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
  calc √(rung c k 1 ^ 2) ≤ √(16 * c ^ 2 * (1 - lamR c k)) := Real.sqrt_le_sqrt hsq
    _ = 4 * c * √(1 - lamR c k) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith)]
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `∫|h_k| ≤ √2`. -/
theorem integral_abs_rung_le {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) :
    ∫ u in (-1 : ℝ)..1, |rung c k u| ≤ √2 := by
  obtain ⟨-, -, -, -, -, hnorm⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec h
  have hi := Cvs.Prolate.RungProfileEntireExtension.intervalIntegrable_rung h
  have hc : ContinuousOn (rung c k) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num)]; exact Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h
  have hcs := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le (a := -1) (b := 1) (by norm_num)
    (f := fun u => |rung c k u|) (w := fun _ => 1)
    ((hc.abs.pow 2).intervalIntegrable) intervalIntegrable_const (hi.abs.mul_const 1)
  simp only [mul_one, sq_abs, one_pow, intervalIntegral.integral_const, smul_eq_mul] at hcs
  rw [hnorm] at hcs
  have h0 : 0 ≤ ∫ u in (-1 : ℝ)..1, |rung c k u| :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _
  have : (∫ u in (-1 : ℝ)..1, |rung c k u|) ^ 2 ≤ 2 := by norm_num at hcs; linarith
  calc ∫ u in (-1 : ℝ)..1, |rung c k u| = √((∫ u in (-1 : ℝ)..1, |rung c k u|) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ √2 := Real.sqrt_le_sqrt this

/-- `μ_k² ≥ π/c` for `λ_k ≥ ½`. -/
theorem muR_sq_ge {c : ℝ} (hc : 0 < c) {k : ℕ} (hl : 1 / 2 ≤ lamR c k) : π / c ≤ muR c k ^ 2 := by
  have := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq (k := k) hc
  rw [this] at hl
  rw [div_le_iff₀ hc]
  have : muR c k ^ 2 * (c / (2 * π)) * (2 * π) = muR c k ^ 2 * c := by field_simp
  nlinarith [Real.pi_pos]

/-- **`M_k ≤ √c`** for `λ_k ≥ ½`. -/
theorem Mk_le {c : ℝ} (hc : 0 < c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hl : 1 / 2 ≤ lamR c k) : Mk c k ≤ √c := by
  unfold Mk
  have hμ2 := muR_sq_ge hc hl
  have hμ0 : 0 < |muR c k| := by
    have : 0 < muR c k ^ 2 := lt_of_lt_of_le (by positivity) hμ2
    exact abs_pos.2 (fun h0 => by simp [h0] at this)
  rw [div_le_iff₀ hμ0]
  refine (integral_abs_rung_le h).trans ?_
  have h1 : √(π / c) ≤ |muR c k| := by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hμ2
  have h2 : √2 ≤ √c * √(π / c) := by
    rw [← Real.sqrt_mul hc.le, mul_div_cancel₀ _ hc.ne']
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  calc √2 ≤ √c * √(π / c) := h2
    _ ≤ √c * |muR c k| := by gcongr

/-- `∫h₀ = μ₀h₀(0)`. -/
theorem integral_rung_zero {c : ℝ} (k : ℕ) (h : ∃ χ, IsLevelIdx c k χ) :
    ∫ u in (-1 : ℝ)..1, rung c k u = muR c k * rung c k 0 := by
  have := Cvs.Prolate.EvenRungsByIndex.psi_rung h 0 ⟨by norm_num, by norm_num⟩
  rw [← this]
  unfold Cvs.L2a.AngularProlateTailPositive.psi Cvs.Prolate.SlepianCommutingRelation.kint
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp

/-- **The ground rung keeps its sign**, so `∫|h₀| = |∫h₀|`. -/
theorem integral_abs_rung_zero (c : ℝ) : ∫ u in (-1 : ℝ)..1, |rung c 0 u| = |∫ u in (-1 : ℝ)..1, rung c 0 u| := by
  obtain ⟨hg, hg₁, -, hang, heven, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)
  have h0 := (Cvs.Prolate.EvenRungsByIndex.lev_spec (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)).2
  have hpos := Cvs.Prolate.EdgeCentreSign.ground_pos hg hg₁ hang heven
    (Cvs.Prolate.EvenRungsByIndex.rung_ne_zero (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)) h0
  set s₁ := rung c 0 1 with hs₁
  have hs₁0 : s₁ ≠ 0 := Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)
  have habs : ∀ u ∈ uIcc (-1 : ℝ) 1, |rung c 0 u| = SignType.sign s₁ * rung c 0 u := by
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    have := hpos u hu
    rcases lt_or_gt_of_ne hs₁0 with hn | hp
    · have : rung c 0 u < 0 := by nlinarith
      rw [sign_neg hn, abs_of_neg this]; simp
    · have : 0 < rung c 0 u := by nlinarith
      rw [sign_pos hp, abs_of_pos this]; simp
  rw [intervalIntegral.integral_congr habs, intervalIntegral.integral_const_mul]
  rcases lt_or_gt_of_ne hs₁0 with hn | hp
  · rw [sign_neg hn]
    have : ∫ u in (-1 : ℝ)..1, rung c 0 u ≤ 0 := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      exact setIntegral_nonpos measurableSet_Ioc fun u hu => by
        have := hpos u ⟨hu.1.le, hu.2⟩; nlinarith
    simp [abs_of_nonpos this]
  · rw [sign_pos hp]
    have : 0 ≤ ∫ u in (-1 : ℝ)..1, rung c 0 u :=
      intervalIntegral.integral_nonneg (by norm_num) fun u hu => by
        have := hpos u hu; nlinarith
    simp [abs_of_nonneg this]

/-- **The ground weight against the ground profile**: `α_j² M₀ ≤ c` for `λ_{4j} ≥ ½`. -/
theorem alpha_sq_mul_Mk_le {c : ℝ} (hc : 0 < c) {j : ℕ} (h : ∃ χ, IsLevelIdx c (2 * j) χ)
    (hl : 1 / 2 ≤ lamR c (2 * j)) : Cvs.Approximant.DeepIndexSpineSpan.alpha c j ^ 2 * Mk c 0 ≤ c := by
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have hl0 : 1 / 2 ≤ lamR c 0 := hl.trans (Cvs.Prolate.EvenRungsByIndex.lamR_anti hc h (Nat.zero_le _))
  have hμ0 : 0 < muR c 0 := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h0 ⟨0, rfl⟩
  have hz := Cvs.Prolate.Envelope.RungDuhamelRemainder.half_le_rung_zero_sq c
  have hI0 := integral_rung_zero 0 h0
  have hM0 : Mk c 0 = |rung c 0 0| := by
    unfold Mk
    rw [integral_abs_rung_zero, hI0, abs_mul, abs_of_pos hμ0]; field_simp
  have hnum : (∫ u in (-1 : ℝ)..1, rung c (2 * j) u) ^ 2 ≤ 2 := by
    have h1 : |∫ u in (-1 : ℝ)..1, rung c (2 * j) u| ≤ √2 :=
      (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans (integral_abs_rung_le h)
    have h2 : (∫ u in (-1 : ℝ)..1, rung c (2 * j) u) ^ 2 = |∫ u in (-1 : ℝ)..1, rung c (2 * j) u| ^ 2 :=
      (sq_abs _).symm
    rw [h2]
    calc |∫ u in (-1 : ℝ)..1, rung c (2 * j) u| ^ 2 ≤ √2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = 2 := Real.sq_sqrt (by norm_num)
  have hμ2 := muR_sq_ge hc hl0
  have hza : 1 / √2 ≤ |rung c 0 0| := by
    rw [div_le_iff₀ (by positivity), ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
    calc (1 : ℝ) = √1 := Real.sqrt_one.symm
      _ ≤ √(rung c 0 0 ^ 2 * 2) := Real.sqrt_le_sqrt (by linarith)
  have hza0 : 0 < |rung c 0 0| := lt_of_lt_of_le (by positivity) hza
  unfold Cvs.Approximant.DeepIndexSpineSpan.alpha
  rw [hM0, hI0, div_pow, mul_pow]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hsq : rung c 0 0 ^ 2 = |rung c 0 0| * |rung c 0 0| := by rw [← sq_abs]; ring
  rw [hsq]
  have h3 : 2 * |rung c 0 0| ≤ c * (muR c 0 ^ 2 * (|rung c 0 0| * |rung c 0 0|)) := by
    have : π / c * c = π := by field_simp
    have h4 : 1 ≤ √2 * |rung c 0 0| := by rw [div_le_iff₀ (by positivity)] at hza; linarith
    have h5 : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [Real.pi_gt_three, mul_le_mul_of_nonneg_left hμ2 hc.le]
  nlinarith [abs_nonneg (rung c 0 0)]

end Cvs.Prolate.Mellin.FarLineRungSizes

end
