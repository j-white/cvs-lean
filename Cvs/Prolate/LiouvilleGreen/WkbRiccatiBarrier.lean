import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The WKB Riccati barrier for the angular prolate equation

For `((1 − s²)g′)′ = (c²s² − χ)g` on the forbidden zone, `B = √(pq)` has `B′ = 2Bγ/p` with
`γ = (pq)′/(4q)`, and `γ′ ≤ γ²/p` when `χ/c² ≤ 1/3`; hence `W = B + γ` satisfies the Riccati
supersolution inequality `W′ ≤ W²/p − q`, and `B` alone does wherever `γ ≤ 0`.
-/

noncomputable section
open Real Set
namespace Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier

/-- The leading coefficient `p(s) = 1 − s²` of the angular prolate operator. -/
def pp (s : ℝ) : ℝ := 1 - s ^ 2

/-- The potential `q(s) = c²s² − χ` of the angular prolate equation. -/
def qq (c χ s : ℝ) : ℝ := c ^ 2 * s ^ 2 - χ

/-- The WKB barrier `B(s) = √(p(s) q(s))`. -/
def Bb (c χ s : ℝ) : ℝ := √(pp s * qq c χ s)

/-- The WKB correction `γ(s) = (pq)′/(4q) = s(c²p − q)/(2q)`. -/
def gam (c χ s : ℝ) : ℝ := s * (c ^ 2 * pp s - qq c χ s) / (2 * qq c χ s)

/-- The closed-form derivative of `γ`. -/
def gamD (c χ s : ℝ) : ℝ :=
  ((c ^ 2 + χ - 6 * c ^ 2 * s ^ 2) * qq c χ s
      - s * (c ^ 2 * pp s - qq c χ s) * (2 * c ^ 2 * s)) / (2 * qq c χ s ^ 2)

/-- On the forbidden zone, `B′ = 2Bγ/p`. -/
theorem hasDerivAt_Bb {c χ s : ℝ} (hp : 0 < pp s) (hq : 0 < qq c χ s) :
    HasDerivAt (Bb c χ) (2 * Bb c χ s * gam c χ s / pp s) s := by
  have hpq : 0 < pp s * qq c χ s := mul_pos hp hq
  have hf : HasDerivAt (fun x => pp x * qq c χ x)
      ((-(2 * s)) * qq c χ s + pp s * (c ^ 2 * (2 * s))) s := by
    have h1 : HasDerivAt pp (-(2 * s)) s := by
      have := ((hasDerivAt_pow 2 s).const_sub 1)
      exact (by simpa using this : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * s)) s)
    have h2 : HasDerivAt (qq c χ) (c ^ 2 * (2 * s)) s := by
      have := (((hasDerivAt_pow 2 s).const_mul (c ^ 2)).sub_const χ)
      exact (by simpa using this : HasDerivAt (fun x : ℝ => c ^ 2 * x ^ 2 - χ) (c ^ 2 * (2 * s)) s)
    exact h1.mul h2
  have hd := hf.sqrt hpq.ne'
  have hBpos : 0 < Bb c χ s := Real.sqrt_pos.mpr hpq
  have hB2 : Bb c χ s ^ 2 = pp s * qq c χ s := Real.sq_sqrt hpq.le
  convert hd using 1
  · rfl
  · change 2 * Bb c χ s * gam c χ s / pp s = _ / (2 * Bb c χ s)
    unfold gam
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    linear_combination (s * c ^ 2 * pp s - s * qq c χ s) * hB2

/-- `γ′ = gamD` wherever `q ≠ 0`. -/
theorem hasDerivAt_gam {c χ s : ℝ} (hq : qq c χ s ≠ 0) :
    HasDerivAt (gam c χ) (gamD c χ s) s := by
  have hN : HasDerivAt (fun x => x * (c ^ 2 * pp x - qq c χ x))
      (c ^ 2 + χ - 6 * c ^ 2 * s ^ 2) s := by
    have e : (fun x => x * (c ^ 2 * pp x - qq c χ x)) =
        fun x => (c ^ 2 + χ) * x - 2 * c ^ 2 * x ^ 3 := by
      funext x; simp only [pp, qq]; ring
    rw [e]
    have := ((hasDerivAt_id s).const_mul (c ^ 2 + χ)).sub
      ((hasDerivAt_pow 3 s).const_mul (2 * c ^ 2))
    refine this.congr_deriv ?_
    norm_num
    ring
  have hD : HasDerivAt (fun x => 2 * qq c χ x) (2 * (c ^ 2 * (2 * s))) s := by
    have := (((hasDerivAt_pow 2 s).const_mul (c ^ 2)).sub_const χ)
    have h2 : HasDerivAt (qq c χ) (c ^ 2 * (2 * s)) s :=
      (by simpa using this : HasDerivAt (fun x : ℝ => c ^ 2 * x ^ 2 - χ) (c ^ 2 * (2 * s)) s)
    exact h2.const_mul 2
  have := hN.div hD (by simpa using hq)
  have e : gam c χ = fun x => (x * (c ^ 2 * pp x - qq c χ x)) / (2 * qq c χ x) := rfl
  rw [e]
  refine this.congr_deriv ?_
  unfold gamD
  field_simp

/-- The convexity estimate: for `χ/c² ≤ 1/3`, on the forbidden part of `(0,1)`, `γ′ ≤ γ²/p`. -/
theorem gamD_le {c χ s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hq : 0 < qq c χ s)
    (hχ : 0 ≤ χ) (h3 : 3 * χ ≤ c ^ 2) (hc : 0 < c) :
    gamD c χ s ≤ gam c χ s ^ 2 / pp s := by
  have hp : 0 < pp s := by unfold pp; nlinarith
  set E := 2 * c ^ 4 * s ^ 4 - 3 * c ^ 4 * s ^ 2 - 6 * c ^ 2 * χ * s ^ 4
    + 10 * c ^ 2 * χ * s ^ 2 - 2 * c ^ 2 * χ + χ ^ 2 * s ^ 2 - 2 * χ ^ 2 with hE
  have key : gam c χ s ^ 2 / pp s - gamD c χ s = -(4 * E) / (16 * pp s * qq c χ s ^ 2) := by
    have hq' := hq.ne'
    have hp' := hp.ne'
    unfold gam gamD
    rw [hE]
    field_simp
    simp only [pp, qq]
    ring
  have hEle : E ≤ 0 := by
    set u := s ^ 2 with hu
    have hu0 : 0 ≤ u := by positivity
    have hu1 : u ≤ 1 := by nlinarith
    have hc2 : 0 ≤ c ^ 2 := by positivity
    have hEu : E = (1 - u) * (-2 * c ^ 2 * χ - 2 * χ ^ 2) + u * (-(c ^ 2 - χ) ^ 2)
        + (2 * c ^ 4 - 6 * c ^ 2 * χ) * (u * (u - 1)) := by
      rw [hE, hu]; ring
    rw [hEu]
    have a1 : 0 ≤ (1 - u) * (2 * c ^ 2 * χ + 2 * χ ^ 2) :=
      mul_nonneg (by linarith) (by positivity)
    have a2 : 0 ≤ u * (c ^ 2 - χ) ^ 2 := mul_nonneg hu0 (sq_nonneg _)
    have a3 : 0 ≤ (2 * c ^ 4 - 6 * c ^ 2 * χ) * (u * (1 - u)) :=
      mul_nonneg (by nlinarith) (mul_nonneg hu0 (by linarith))
    nlinarith
  have : 0 ≤ -(4 * E) / (16 * pp s * qq c χ s ^ 2) :=
    div_nonneg (by linarith) (by positivity)
  linarith

/-- `γ ≤ 0` past the turning point of `c²p − q`, i.e. when `2c²s² ≥ c² + χ`. -/
theorem gam_nonpos {c χ s : ℝ} (hq : 0 < qq c χ s) (hs : 0 < s)
    (h : c ^ 2 + χ ≤ 2 * c ^ 2 * s ^ 2) : gam c χ s ≤ 0 := by
  unfold gam
  apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
  apply mul_nonpos_of_nonneg_of_nonpos hs.le
  simp only [pp, qq]; nlinarith

/-- `γ ≥ 0` before the turning point of `c²p − q`, i.e. when `2c²s² ≤ c² + χ`. -/
theorem gam_nonneg {c χ s : ℝ} (hq : 0 < qq c χ s) (hs : 0 < s)
    (h : 2 * c ^ 2 * s ^ 2 ≤ c ^ 2 + χ) : 0 ≤ gam c χ s := by
  unfold gam
  apply div_nonneg _ (by linarith)
  apply mul_nonneg hs.le
  simp only [pp, qq]; nlinarith

/-- The Riccati barrier inequality `W′ ≤ W²/p − q` for `W = B + γ` when `χ/c² ≤ 1/3`. -/
theorem barrier_le {c χ s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hq : 0 < qq c χ s)
    (hχ : 0 ≤ χ) (h3 : 3 * χ ≤ c ^ 2) (hc : 0 < c) :
    2 * Bb c χ s * gam c χ s / pp s + gamD c χ s ≤
      (Bb c χ s + gam c χ s) ^ 2 / pp s - qq c χ s := by
  have hp : 0 < pp s := by unfold pp; nlinarith
  have hB2 : Bb c χ s ^ 2 = pp s * qq c χ s := Real.sq_sqrt (mul_pos hp hq).le
  have e : (Bb c χ s + gam c χ s) ^ 2 / pp s - qq c χ s =
      2 * Bb c χ s * gam c χ s / pp s + gam c χ s ^ 2 / pp s := by
    field_simp
    linear_combination hB2
  rw [e]
  linarith [gamD_le hs0 hs1 hq hχ h3 hc]

/-- Where `γ ≤ 0`, `B` alone is a Riccati supersolution: `2Bγ/p ≤ B²/p − q = 0`. -/
theorem Bb_barrier_le {c χ s : ℝ} (hp : 0 < pp s) (hq : 0 < qq c χ s)
    (hg : gam c χ s ≤ 0) :
    2 * Bb c χ s * gam c χ s / pp s ≤ Bb c χ s ^ 2 / pp s - qq c χ s := by
  have hB2 : Bb c χ s ^ 2 = pp s * qq c χ s := Real.sq_sqrt (mul_pos hp hq).le
  have hB0 : 0 ≤ Bb c χ s := Real.sqrt_nonneg _
  rw [hB2, mul_div_cancel_left₀ _ hp.ne', sub_self]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) hg) hp.le

end Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier
