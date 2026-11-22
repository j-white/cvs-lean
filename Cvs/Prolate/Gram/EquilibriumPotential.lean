import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The equilibrium potential is `−Ψ_a` (eq-cpb Lemma 2 mass balance and Proposition 3)

With `t_e = 2a√(1 − a²)` (so `asin t_e = 2 asin a`) and weight `w(t) = sgn(t − a)/√(1 − t²)` on `(0, t_e)`, the
signed measure `μ_a = (1/2π)∫ w(t)[δ_{t² + u²} − δ_{u²}] du dt` has zero mass and potential
`∫ log|s − y| dμ_a(y) = Ψ_a(s) = ½∫_0^{t_e} sgn(t − a)√((t² − s)₊/(1 − t²)) dt` for `s > 0`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped Interval

namespace Cvs.Prolate.Gram.EquilibriumPotential

/-- The cell edge `t_e = sin(2 asin a) = 2a√(1 − a²)`. -/
def tE (a : ℝ) : ℝ := 2 * a * √(1 - a ^ 2)

/-- The sign of `t − a` (with `−1` at `t = a`). -/
def sgnA (a t : ℝ) : ℝ := if t ≤ a then -1 else 1

/-- The equilibrium weight `w(t) = sgn(t − a)/√(1 − t²)`. -/
def wA (a t : ℝ) : ℝ := sgnA a t / √(1 - t ^ 2)

/-- `Ψ_a(s) = ½∫_0^{t_e} sgn(t − a)√((t² − s)₊)/√(1 − t²) dt`. -/
def psiA (a s : ℝ) : ℝ := 1 / 2 * ∫ t in (0 : ℝ)..tE a, wA a t * √(t ^ 2 - s)

/-! ### The cell edge -/

theorem tE_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ tE a := by unfold tE; positivity

/-- `t_e < 1` for `2a² < 1`. -/
theorem tE_lt_one {a : ℝ} (ha2 : 2 * a ^ 2 < 1) : tE a < 1 := by
  unfold tE
  have h1 : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hs := Real.sq_sqrt h1
  have hsq : (2 * a * √(1 - a ^ 2)) ^ 2 < 1 := by
    rw [mul_pow, hs]; nlinarith [sq_nonneg (2 * a ^ 2 - 1)]
  nlinarith [Real.sqrt_nonneg (1 - a ^ 2), sq_nonneg (2 * a * √(1 - a ^ 2) - 1)]

/-- `a ≤ t_e` for `4a² ≤ 3`. -/
theorem le_tE {a : ℝ} (ha : 0 ≤ a) (ha3 : 4 * a ^ 2 ≤ 3) : a ≤ tE a := by
  unfold tE
  have h1 : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hh : 1 / 2 ≤ √(1 - a ^ 2) := by
    rw [show (1 / 2 : ℝ) = √(1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
    exact Real.sqrt_le_sqrt (by linarith)
  nlinarith

/-- **The mass balance** `asin t_e = 2 asin a` for `0 ≤ a` and `2a² ≤ 1`. -/
theorem arcsin_tE {a : ℝ} (ha : 0 ≤ a) (ha2 : 2 * a ^ 2 ≤ 1) : arcsin (tE a) = 2 * arcsin a := by
  have ha1 : a ≤ 1 := by nlinarith
  have hq : arcsin a ≤ π / 4 := by
    rw [Real.arcsin_le_iff_le_sin ⟨by linarith, ha1⟩ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      Real.sin_pi_div_four]
    have h2 : 0 < √2 := by positivity
    have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [sq_nonneg (a - √2 / 2)]
  have hq0 : 0 ≤ arcsin a := Real.arcsin_nonneg.mpr ha
  rw [← Real.arcsin_sin (x := 2 * arcsin a) (by linarith [Real.pi_pos]) (by linarith), Real.sin_two_mul,
    Real.sin_arcsin (by linarith) ha1, Real.cos_arcsin]
  rfl

/-! ### The weight -/

theorem hasDerivAt_arcsin' {t : ℝ} (h : t ^ 2 < 1) : HasDerivAt arcsin (1 / √(1 - t ^ 2)) t :=
  Real.hasDerivAt_arcsin (by nlinarith) (by nlinarith)

/-- `1/√(1 − t²)` times a function continuous on `[α, β] ⊆ [0, 1)` is interval integrable there. -/
theorem intervalIntegrable_inv_sqrt_mul {g : ℝ → ℝ} {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β < 1)
    (hg : ContinuousOn g (Icc α β)) : IntervalIntegrable (fun t => 1 / √(1 - t ^ 2) * g t) volume α β := by
  refine (ContinuousOn.mul (ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_) ?_).intervalIntegrable
  · rw [uIcc_of_le hαβ] at ht
    exact (Real.sqrt_pos.mpr (by nlinarith [ht.1, ht.2])).ne'
  · rwa [uIcc_of_le hαβ]

/-- `∫_α^β dt/√(1 − t²) = asin β − asin α` on `[0, 1)`. -/
theorem integral_inv_sqrt {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β < 1) :
    ∫ t in α..β, 1 / √(1 - t ^ 2) = arcsin β - arcsin α := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_arcsin' ?_) ?_
  · rw [uIcc_of_le hαβ] at ht; nlinarith [ht.1, ht.2]
  · simpa using intervalIntegrable_inv_sqrt_mul hα hαβ hβ continuousOn_const (g := fun _ => (1 : ℝ))

/-- **Splitting the weight**: `∫_0^{t_e} w g = −∫_0^a g/√(1 − t²) + ∫_a^{t_e} g/√(1 − t²)`, with integrability. -/
theorem integral_wA_mul {a : ℝ} (ha : 0 ≤ a) (ha2 : 2 * a ^ 2 < 1) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 (tE a))) :
    IntervalIntegrable (fun t => wA a t * g t) volume 0 (tE a) ∧
      ∫ t in (0 : ℝ)..tE a, wA a t * g t =
        -(∫ t in (0 : ℝ)..a, 1 / √(1 - t ^ 2) * g t) + ∫ t in a..tE a, 1 / √(1 - t ^ 2) * g t := by
  have hte := tE_lt_one ha2
  have hat := le_tE ha (by linarith)
  have h1 := intervalIntegrable_inv_sqrt_mul le_rfl ha (hat.trans_lt hte) (hg.mono (Icc_subset_Icc le_rfl hat))
  have h2 := intervalIntegrable_inv_sqrt_mul ha hat hte (hg.mono (Icc_subset_Icc ha le_rfl))
  have e1 : EqOn (fun t => wA a t * g t) (fun t => -(1 / √(1 - t ^ 2) * g t)) (Ι 0 a) := by
    intro t ht
    rw [uIoc_of_le ha] at ht
    simp only [wA, sgnA, if_pos ht.2]; ring
  have e2 : EqOn (fun t => wA a t * g t) (fun t => 1 / √(1 - t ^ 2) * g t) (Ι a (tE a)) := by
    intro t ht
    rw [uIoc_of_le hat] at ht
    simp only [wA, sgnA, if_neg (not_le.mpr ht.1)]
  have i1 : IntervalIntegrable (fun t => wA a t * g t) volume 0 a := (intervalIntegrable_congr e1).mpr h1.neg
  have i2 : IntervalIntegrable (fun t => wA a t * g t) volume a (tE a) := (intervalIntegrable_congr e2).mpr h2
  refine ⟨i1.trans i2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, intervalIntegral.integral_congr_ae
    (Eventually.of_forall fun t ht => e1 ht), intervalIntegral.integral_congr_ae
    (Eventually.of_forall fun t ht => e2 ht), intervalIntegral.integral_neg]

/-! ### The potential -/

/-! ### The shape of `Ψ_a` -/

/-- `Ψ_a ≥ 0` on `[a², ∞)` (so the potential `P = −Ψ_a ≤ 0` there). -/
theorem psiA_nonneg {a s : ℝ} (ha : 0 ≤ a) (ha2 : 2 * a ^ 2 < 1) (hs : a ^ 2 ≤ s) : 0 ≤ psiA a s := by
  have hte := tE_lt_one ha2
  unfold psiA
  refine mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg (tE_nonneg ha) fun t ht => ?_)
  unfold wA sgnA
  split_ifs with h
  · rw [Real.sqrt_eq_zero_of_nonpos (show t ^ 2 - s ≤ 0 by nlinarith [ht.1]), mul_zero]
  · have : 0 < √(1 - t ^ 2) := Real.sqrt_pos.mpr (by nlinarith [ht.1, ht.2])
    positivity

end Cvs.Prolate.Gram.EquilibriumPotential

end
