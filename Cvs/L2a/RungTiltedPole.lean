import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.ProlateWindowMassIdentity
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The per-rung tilted pole

For a rung `ψ = psi c g` with `c ≥ 80`, `0 ≤ χ`, `5c ≤ c² − χ` and `X ≥ 2`,
`|∫_{(1,∞)} posTail ψ X θ (1 − 1/θ)| ≤ 7√(∫₁^X ψ²)/c`: Cvs.L2a.PositionTailSpanAdapters splits the integral into the modes
`m⁻¹∫_m^X ψ(1 − m/ξ)`, each integrated by parts against `u' = −qψ`; the mode `m = 1` uses `ProlateWindowMassIdentity`'s weighted mass
identity, the modes `m ≥ 2` `ProlateWindowMassIdentity`'s far energy bound and `Σ_{m≥2} 1/(m² − 1) ≤ 3/4`.
-/

namespace Cvs.L2a.RungTiltedPole

open Real Set MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- `x ≤ tA + B/t` for every `t > 0` gives `x ≤ 2√(AB)`. -/
theorem le_two_sqrt_mul {x A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : ∀ t : ℝ, 0 < t → x ≤ t * A + B / t) :
    x ≤ 2 * √(A * B) := by
  by_contra hx
  push Not at hx
  have hs : 0 ≤ √(A * B) := sqrt_nonneg _
  have hx0 : 0 < x := by linarith
  rcases hA.eq_or_lt with hA0 | hA0
  · have h1 := h ((B + 1) / x) (by positivity)
    have e : (B + 1) / x * A + B / ((B + 1) / x) = B * x / (B + 1) := by
      rw [← hA0]; field_simp; ring
    rw [e, le_div_iff₀ (by positivity)] at h1
    nlinarith
  rcases hB.eq_or_lt with hB0 | hB0
  · have h1 := h (x / (2 * A)) (by positivity)
    have e : x / (2 * A) * A + B / (x / (2 * A)) = x / 2 := by
      rw [← hB0]; field_simp; ring
    linarith
  · have h1 := h (√B / √A) (by positivity)
    have hA' : 0 < √A := sqrt_pos.mpr hA0
    have hB' : 0 < √B := sqrt_pos.mpr hB0
    have e : √B / √A * A + B / (√B / √A) = 2 * √(A * B) := by
      rw [sqrt_mul hA]
      have eA : A = √A ^ 2 := (sq_sqrt hA).symm
      have eB : B = √B ^ 2 := (sq_sqrt hB).symm
      rw [eA, eB, sqrt_sq hA'.le, sqrt_sq hB'.le]
      field_simp; ring
    linarith

/-- `Σ_{m=2}^K 1/(m² − 1) = 3/4 − 1/(2K) − 1/(2(K + 1))` for `K ≥ 1`. -/
theorem sum_inv_sq_sub_one (K : ℕ) (hK : 1 ≤ K) :
    ∑ m ∈ Finset.Ioc 1 K, 1 / ((m : ℝ) ^ 2 - 1)
      = (3 / 4 : ℝ) - 1 / (2 * (K : ℝ)) - 1 / (2 * ((K : ℝ) + 1)) := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    push_cast
    have h1 : ((K : ℝ) + 1) ^ 2 - 1 = K * (K + 2) := by ring
    rw [h1]
    field_simp
    ring

/-- `Σ_{m=2}^K 1/(m² − 1) ≤ 3/4`. -/
theorem sum_inv_sq_sub_one_le (K : ℕ) : ∑ m ∈ Finset.Ioc 1 K, 1 / ((m : ℝ) ^ 2 - 1) ≤ 3 / 4 := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · norm_num
  rw [sum_inv_sq_sub_one K hK]
  have : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : 0 ≤ 1 / (2 * (K : ℝ)) := by positivity
  have h2 : 0 ≤ 1 / (2 * ((K : ℝ) + 1)) := by positivity
  linarith

/-- `q = c²ξ² − χ > 0` for `ξ ≥ 1` and `χ < c²`. -/
theorem qP_pos_of_one_le {c χ ξ : ℝ} (hχ : χ < c ^ 2) (hξ : 1 ≤ ξ) : 0 < qP c χ ξ := by
  unfold qP
  nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ ξ ^ 2 by nlinarith) (sq_nonneg c)]

/-- `c²p ≤ q` for `χ ≤ c²`. -/
theorem c_sq_pP_le_qP {c χ ξ : ℝ} (hχ : χ ≤ c ^ 2) : c ^ 2 * pP ξ ≤ qP c χ ξ := by
  unfold pP qP; nlinarith

/-- `q' = 2c²ξ`. -/
theorem hasDerivAt_qP (c χ ξ : ℝ) : HasDerivAt (qP c χ) (2 * c ^ 2 * ξ) ξ := by
  have h := ((hasDerivAt_pow 2 ξ).const_mul (c ^ 2)).sub_const χ
  exact h.congr_deriv (by ring)

/-- The tilted weight `h_m = (w_m/q)'` of the mode `m`, `w_m(ξ) = 1 − m/ξ`. -/
noncomputable def hW (c χ m ξ : ℝ) : ℝ :=
  m / (ξ ^ 2 * qP c χ ξ) - (1 - m / ξ) * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2

/-- `h_m` is continuous on `[m, X]` for `m ≥ 1`, `χ < c²`. -/
theorem continuousOn_hW {c χ m X : ℝ} (hχ : χ < c ^ 2) (hm : 1 ≤ m) :
    ContinuousOn (hW c χ m) (Icc m X) := by
  have hq : ∀ ξ ∈ Icc m X, qP c χ ξ ≠ 0 := fun ξ hξ => (qP_pos_of_one_le hχ (hm.trans hξ.1)).ne'
  have hξ : ∀ ξ ∈ Icc m X, ξ ≠ 0 := fun ξ hξ => by linarith [hξ.1]
  have hqc : Continuous (qP c χ) := by unfold qP; fun_prop
  unfold hW
  have hd1 : ContinuousOn (fun ξ : ℝ => ξ ^ 2 * qP c χ ξ) (Icc m X) :=
    (continuousOn_id.pow 2).mul hqc.continuousOn
  have hd2 : ContinuousOn (fun ξ : ℝ => 1 - m / ξ) (Icc m X) :=
    continuousOn_const.sub (continuousOn_const.div₀ continuousOn_id hξ)
  have hd3 : ContinuousOn (fun ξ : ℝ => 2 * c ^ 2 * ξ) (Icc m X) :=
    continuousOn_const.mul continuousOn_id
  have hd4 : ContinuousOn (fun ξ : ℝ => qP c χ ξ ^ 2) (Icc m X) := hqc.continuousOn.pow 2
  refine ContinuousOn.sub (continuousOn_const.div₀ hd1 fun ξ hξ' => ?_) ?_
  · exact mul_ne_zero (pow_ne_zero 2 (hξ ξ hξ')) (hq ξ hξ')
  · exact ContinuousOn.div₀ (hd2.mul hd3) hd4 fun ξ hξ' => pow_ne_zero 2 (hq ξ hξ')

/-- **Integration by parts of a mode**: for `1 ≤ m ≤ X`, `u' = −qψ` and `χ < c²`,
`∫_m^X ψ(1 − m/ξ) = −u(X)(1 − m/X)/q(X) + ∫_m^X u h_m`. -/
theorem integral_mode_eq {c χ m X : ℝ} {ψ u : ℝ → ℝ} (hχ : χ < c ^ 2) (hm : 1 ≤ m) (hmX : m ≤ X)
    (hψc : ContinuousOn ψ (Icc 1 X)) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) :
    ∫ ξ in m..X, ψ ξ * (1 - m / ξ)
      = -(u X * (1 - m / X) / qP c χ X) + ∫ ξ in m..X, u ξ * hW c χ m ξ := by
  have hI : uIcc m X = Icc m X := uIcc_of_le hmX
  have hq : ∀ ξ ∈ Icc m X, qP c χ ξ ≠ 0 := fun ξ hξ => (qP_pos_of_one_le hχ (hm.trans hξ.1)).ne'
  have hξ : ∀ ξ ∈ Icc m X, ξ ≠ 0 := fun ξ hξ => by linarith [hξ.1]
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun ξ => (hu ξ).continuousAt
  have hψm : ContinuousOn ψ (Icc m X) := hψc.mono (Icc_subset_Icc hm le_rfl)
  have hwc : ContinuousOn (fun ξ => 1 - m / ξ) (Icc m X) :=
    continuousOn_const.sub (continuousOn_const.div₀ continuousOn_id hξ)
  have hc1 : ContinuousOn (fun ξ => ψ ξ * (1 - m / ξ)) (Icc m X) := hψm.mul hwc
  have hc2 : ContinuousOn (fun ξ => u ξ * hW c χ m ξ) (Icc m X) :=
    huc.continuousOn.mul (continuousOn_hW hχ hm)
  have hderiv : ∀ ξ ∈ uIcc m X, HasDerivAt (fun ξ => -(u ξ * (1 - m / ξ) / qP c χ ξ))
      (ψ ξ * (1 - m / ξ) - u ξ * hW c χ m ξ) ξ := by
    intro ξ hξ'
    rw [hI] at hξ'
    have hw : HasDerivAt (fun ξ => 1 - m / ξ) (m / ξ ^ 2) ξ := by
      have := ((hasDerivAt_const ξ m).div (hasDerivAt_id ξ) (hξ ξ hξ')).const_sub 1
      refine this.congr_deriv ?_
      simp only [id]; field_simp; ring
    have := (((hu ξ).mul hw).div (hasDerivAt_qP c χ ξ) (hq ξ hξ')).neg
    refine this.congr_deriv ?_
    have := hq ξ hξ'; have := hξ ξ hξ'
    simp only [Pi.mul_apply]
    unfold hW; field_simp; ring
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv ((hc1.sub hc2).intervalIntegrable_of_Icc hmX)
  rw [integral_sub (hc1.intervalIntegrable_of_Icc hmX) (hc2.intervalIntegrable_of_Icc hmX)] at hFTC
  have hm0 : m ≠ 0 := by linarith
  simp only [div_self hm0, sub_self, mul_zero, zero_div, neg_zero, sub_zero] at hFTC
  linarith

/-- `25p(2c²ξ)² ≤ q³` for `c ≥ 80`, `5c ≤ c² − χ` and `ξ ≥ 1`. -/
theorem qP_cube_ge {c χ ξ : ℝ} (hc : 80 ≤ c) (hσ : 5 * c ≤ c ^ 2 - χ) (hξ : 1 ≤ ξ) :
    25 * pP ξ * (2 * c ^ 2 * ξ) ^ 2 ≤ qP c χ ξ ^ 3 := by
  set A := c ^ 2 * pP ξ with hA
  set B := c ^ 2 - χ with hB
  have hp : 0 ≤ pP ξ := by unfold pP; nlinarith
  have hA0 : 0 ≤ A := mul_nonneg (sq_nonneg c) hp
  have hB25 : 25 ≤ B := by nlinarith
  have hB2 : 25 * c ^ 2 ≤ B ^ 2 := by nlinarith
  have e1 : 25 * pP ξ * (2 * c ^ 2 * ξ) ^ 2 = 100 * A ^ 2 + 100 * c ^ 2 * A := by
    rw [hA]; unfold pP; ring
  have e2 : qP c χ ξ = A + B := by rw [hA, hB]; unfold qP pP; ring
  rw [e1, e2]
  nlinarith [mul_nonneg (add_nonneg hA0 (by linarith : (0:ℝ) ≤ B)) (sq_nonneg (A - B)),
    mul_le_mul_of_nonneg_left hB25 (sq_nonneg A), mul_le_mul_of_nonneg_left hB2 hA0]

/-- If `25pd² ≤ q³` with `p, q > 0`, then `|abd/q²| ≤ (a² + b²/(pq))/10`. -/
theorem abs_cross_le {a b p q d : ℝ} (hp : 0 < p) (hq : 0 < q) (hd : 25 * p * d ^ 2 ≤ q ^ 3) :
    |a * b * d / q ^ 2| ≤ (a ^ 2 + b ^ 2 / (p * q)) / 10 := by
  set β := b ^ 2 / (p * q) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have h1 : (a * b * d / q ^ 2) ^ 2 = a ^ 2 * (b ^ 2 * d ^ 2 / q ^ 4) := by field_simp
  have h2 : b ^ 2 * d ^ 2 / q ^ 4 ≤ β / 25 := by
    rw [hβ, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hd hq.le
    have := mul_le_mul_of_nonneg_left this (sq_nonneg b)
    nlinarith
  have h3 : (a * b * d / q ^ 2) ^ 2 ≤ ((a ^ 2 + β) / 10) ^ 2 := by
    rw [h1]
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg a)
    nlinarith [sq_nonneg (a ^ 2 - β)]
  exact abs_le.mpr (abs_le_of_sq_le_sq' h3 (by positivity))

/-- `|vh| ≤ (t/2)β + κ/(2t)` when `(vh)² = βγ`, `0 ≤ γ ≤ κ`, `0 ≤ β`, `t > 0`. -/
theorem abs_mul_le_amgm {v h β γ κ t : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγκ : γ ≤ κ)
    (hvh : (v * h) ^ 2 = β * γ) : |v * h| ≤ t / 2 * β + 1 / (2 * t) * κ := by
  have hκ : 0 ≤ κ := hγ.trans hγκ
  have e : t / 2 * β + 1 / (2 * t) * κ = (t * β + κ / t) / 2 := by field_simp
  have h3 : (v * h) ^ 2 ≤ (t / 2 * β + 1 / (2 * t) * κ) ^ 2 := by
    rw [hvh, e]
    have h4 : β * γ ≤ β * κ := mul_le_mul_of_nonneg_left hγκ hβ
    have h5 : (t * β + κ / t) ^ 2 - 4 * (β * κ) = (t * β - κ / t) ^ 2 := by field_simp; ring
    nlinarith [sq_nonneg (t * β - κ / t)]
  exact abs_le.mpr (abs_le_of_sq_le_sq' h3 (by positivity))

/-- `pq h₁² ≤ (3/ξ⁴ + 6/(ξ+1)²)/c²` for `ξ > 1`, `c > 0` and `χ ≤ c²`. -/
theorem pq_hW_one_sq_le {c χ ξ : ℝ} (hc : 0 < c) (hχ : χ ≤ c ^ 2) (hξ : 1 < ξ) :
    pP ξ * qP c χ ξ * hW c χ 1 ξ ^ 2 ≤ (3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) / c ^ 2 := by
  have hp : 0 < pP ξ := pP_pos hξ
  have hcp := c_sq_pP_le_qP (ξ := ξ) hχ
  have hq : 0 < qP c χ ξ := lt_of_lt_of_le (by positivity) hcp
  have ex : hW c χ 1 ξ = 1 / (ξ ^ 2 * qP c χ ξ) - 2 * c ^ 2 * (ξ - 1) / qP c χ ξ ^ 2 := by
    unfold hW; have : ξ ≠ 0 := by linarith
    field_simp
  set p := pP ξ with hpdef
  set q := qP c χ ξ
  set x := 1 / (ξ ^ 2 * q)
  set y := 2 * c ^ 2 * (ξ - 1) / q ^ 2
  have hx : p * q * x ^ 2 ≤ 1 / (c ^ 2 * ξ ^ 4) := by
    have e : p * q * x ^ 2 = p / (ξ ^ 4 * q) := by simp only [x]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (by linarith : (0:ℝ) < ξ) 4]
  have hy : p * q * y ^ 2 ≤ 4 / (c ^ 2 * (ξ + 1) ^ 2) := by
    have e : p * q * y ^ 2 = 4 * c ^ 4 * p * (ξ - 1) ^ 2 / q ^ 3 := by simp only [y]; field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpp : (ξ - 1) ^ 2 * (ξ + 1) ^ 2 = p ^ 2 := by rw [hpdef]; unfold pP; ring
    have h3 : (c ^ 2 * p) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by positivity) hcp 3
    have e2 : 4 * c ^ 4 * p * (ξ - 1) ^ 2 * (c ^ 2 * (ξ + 1) ^ 2) = 4 * (c ^ 2 * p) ^ 3 := by
      rw [show 4 * c ^ 4 * p * (ξ - 1) ^ 2 * (c ^ 2 * (ξ + 1) ^ 2)
        = 4 * c ^ 6 * p * ((ξ - 1) ^ 2 * (ξ + 1) ^ 2) by ring, hpp]; ring
    rw [e2]; linarith
  have hxy : (x - y) ^ 2 ≤ 3 * x ^ 2 + 3 / 2 * y ^ 2 := by nlinarith [sq_nonneg (2 * x + y)]
  have hpq : 0 ≤ p * q := by positivity
  rw [ex]
  calc p * q * (x - y) ^ 2 ≤ p * q * (3 * x ^ 2 + 3 / 2 * y ^ 2) := mul_le_mul_of_nonneg_left hxy hpq
    _ = 3 * (p * q * x ^ 2) + 3 / 2 * (p * q * y ^ 2) := by ring
    _ ≤ 3 * (1 / (c ^ 2 * ξ ^ 4)) + 3 / 2 * (4 / (c ^ 2 * (ξ + 1) ^ 2)) := by linarith
    _ = (3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) / c ^ 2 := by field_simp; ring

/-- The majorant primitive of the mode `m ≥ 2`: `K(−m/(2ξ²) − 1/ξ) − (ξ − m)/(ξ² − 1)`, `K = m²/(m² − 1)`. -/
noncomputable def Gm (m ξ : ℝ) : ℝ := m ^ 2 / (m ^ 2 - 1) * (-(m / (2 * ξ ^ 2)) - 1 / ξ) - (ξ - m) / (ξ ^ 2 - 1)

/-- The derivative of `Gm`. -/
noncomputable def Gm' (m ξ : ℝ) : ℝ :=
  m ^ 2 / (m ^ 2 - 1) * (m / ξ ^ 3 + 1 / ξ ^ 2) - ((ξ ^ 2 - 1) - (ξ - m) * (2 * ξ)) / (ξ ^ 2 - 1) ^ 2

/-- `Gm' = (Gm)'` at every `ξ > 1`. -/
theorem hasDerivAt_Gm (m : ℝ) {ξ : ℝ} (hξ : 1 < ξ) : HasDerivAt (Gm m) (Gm' m ξ) ξ := by
  have h0 : ξ ≠ 0 := by linarith
  have hp : ξ ^ 2 - 1 ≠ 0 := by nlinarith
  have h1 : HasDerivAt (fun ξ => -(m / (2 * ξ ^ 2)) - 1 / ξ) (m / ξ ^ 3 + 1 / ξ ^ 2) ξ := by
    have a := ((hasDerivAt_const ξ m).div (((hasDerivAt_pow 2 ξ).const_mul 2))
      (by positivity : (2 : ℝ) * ξ ^ 2 ≠ 0)).neg.sub ((hasDerivAt_const ξ (1 : ℝ)).div (hasDerivAt_id ξ) h0)
    refine a.congr_deriv ?_
    simp only [id]; field_simp; ring
  have h2 : HasDerivAt (fun ξ => (ξ - m) / (ξ ^ 2 - 1)) (((ξ ^ 2 - 1) - (ξ - m) * (2 * ξ)) / (ξ ^ 2 - 1) ^ 2) ξ := by
    have a := ((hasDerivAt_id ξ).sub_const m).div ((hasDerivAt_pow 2 ξ).sub_const 1) hp
    refine a.congr_deriv ?_
    simp only [id]; ring
  exact (h1.const_mul (m ^ 2 / (m ^ 2 - 1))).sub h2

/-- `Gm'` is continuous on `[m, X]` for `m ≥ 2`. -/
theorem continuousOn_Gm' {m X : ℝ} (hm : 2 ≤ m) : ContinuousOn (Gm' m) (Icc m X) := by
  have h0 : ∀ ξ ∈ Icc m X, ξ ≠ 0 := fun ξ hξ => by linarith [hξ.1]
  have hp : ∀ ξ ∈ Icc m X, ξ ^ 2 - 1 ≠ 0 := fun ξ hξ => by nlinarith [hξ.1]
  unfold Gm'
  have hd1 : ContinuousOn (fun ξ : ℝ => ξ ^ 3) (Icc m X) := continuousOn_id.pow 3
  have hd2 : ContinuousOn (fun ξ : ℝ => ξ ^ 2) (Icc m X) := continuousOn_id.pow 2
  have hd3 : ContinuousOn (fun ξ : ℝ => (ξ ^ 2 - 1) - (ξ - m) * (2 * ξ)) (Icc m X) := by
    fun_prop
  have hd4 : ContinuousOn (fun ξ : ℝ => (ξ ^ 2 - 1) ^ 2) (Icc m X) := by fun_prop
  refine ContinuousOn.sub (continuousOn_const.mul (ContinuousOn.add
    (continuousOn_const.div₀ hd1 fun ξ hξ => pow_ne_zero 3 (h0 ξ hξ))
    (continuousOn_const.div₀ hd2 fun ξ hξ => pow_ne_zero 2 (h0 ξ hξ))))
    (ContinuousOn.div₀ hd3 hd4 fun ξ hξ => pow_ne_zero 2 (hp ξ hξ))

/-- **The pointwise majorant of a mode `m ≥ 2`**: on `[m, ∞)`, if `|u(ξ)| ≤ cξS` then
`|u h_m| ≤ (S/c) Gm'`. -/
theorem abs_u_hW_le {c χ m ξ S v : ℝ} (hc : 0 < c) (hχ : χ ≤ c ^ 2) (hm : 2 ≤ m) (hξ : m ≤ ξ)
    (hS : 0 ≤ S) (hv : |v| ≤ c * ξ * S) : |v * hW c χ m ξ| ≤ S / c * Gm' m ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hp : 0 < pP ξ := pP_pos (by linarith)
  have hcp := c_sq_pP_le_qP (ξ := ξ) hχ
  have hq : 0 < qP c χ ξ := lt_of_lt_of_le (by positivity) hcp
  have ex : hW c χ m ξ = m / (ξ ^ 2 * qP c χ ξ) - 2 * c ^ 2 * (ξ - m) / qP c χ ξ ^ 2 := by
    unfold hW; field_simp
  set p := pP ξ with hpdef
  set q := qP c χ ξ
  set x := m / (ξ ^ 2 * q)
  set y := 2 * c ^ 2 * (ξ - m) / q ^ 2
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  have hx : x ≤ m / (ξ ^ 2 * (c ^ 2 * p)) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (mul_le_mul_of_nonneg_left hcp (by positivity))
  have hy : y ≤ 2 * c ^ 2 * (ξ - m) / (c ^ 2 * p) ^ 2 :=
    div_le_div_of_nonneg_left (mul_nonneg (by positivity) (by linarith)) (by positivity)
      (pow_le_pow_left₀ (by positivity) hcp 2)
  have hh : |hW c χ m ξ| ≤ m / (ξ ^ 2 * (c ^ 2 * p)) + 2 * c ^ 2 * (ξ - m) / (c ^ 2 * p) ^ 2 := by
    rw [ex]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hx0, abs_of_nonneg hy0]; linarith
  have hK : m / (ξ * p) + 2 * ξ * (ξ - m) / p ^ 2 ≤ Gm' m ξ := by
    have hm1 : 0 < m ^ 2 - 1 := by nlinarith
    have e : Gm' m ξ - (m / (ξ * p) + 2 * ξ * (ξ - m) / p ^ 2)
        = (m + ξ) * (ξ ^ 2 - m ^ 2) / ((m ^ 2 - 1) * ξ ^ 3 * p) := by
      unfold Gm'; rw [hpdef]; unfold pP
      have : ξ ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp; ring
    have : 0 ≤ (m + ξ) * (ξ ^ 2 - m ^ 2) / ((m ^ 2 - 1) * ξ ^ 3 * p) :=
      div_nonneg (mul_nonneg (by linarith) (by nlinarith)) (by positivity)
    linarith
  rw [abs_mul]
  calc |v| * |hW c χ m ξ|
      ≤ c * ξ * S * (m / (ξ ^ 2 * (c ^ 2 * p)) + 2 * c ^ 2 * (ξ - m) / (c ^ 2 * p) ^ 2) :=
        mul_le_mul hv hh (abs_nonneg _) (by positivity)
    _ = S / c * (m / (ξ * p) + 2 * ξ * (ξ - m) / p ^ 2) := by field_simp
    _ ≤ S / c * Gm' m ξ := mul_le_mul_of_nonneg_left hK (by positivity)

/-- **The boundary term**: for `m ≤ X`, `X > 1`, `χ ≤ c²` and `|u(X)| ≤ cXS`,
`|u(X)(1 − m/X)/q(X)| ≤ (S/c)(X − m)/(X² − 1)`. -/
theorem abs_bdry_le {c χ m X S v : ℝ} (hc : 0 < c) (hχ : χ ≤ c ^ 2) (hmX : m ≤ X) (hX : 1 < X)
    (hS : 0 ≤ S) (hv : |v| ≤ c * X * S) :
    |v * (1 - m / X) / qP c χ X| ≤ S / c * ((X - m) / (X ^ 2 - 1)) := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < pP X := pP_pos hX
  have hcp := c_sq_pP_le_qP (ξ := X) hχ
  have hq : 0 < qP c χ X := lt_of_lt_of_le (by positivity) hcp
  have hw : 0 ≤ 1 - m / X := by rw [sub_nonneg, div_le_one hX0]; exact hmX
  rw [abs_div, abs_mul, abs_of_nonneg hw, abs_of_pos hq]
  calc |v| * (1 - m / X) / qP c χ X ≤ c * X * S * (1 - m / X) / qP c χ X :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv hw) hq.le
    _ ≤ c * X * S * (1 - m / X) / (c ^ 2 * pP X) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hcp
    _ = S / c * ((X - m) / (X ^ 2 - 1)) := by unfold pP; field_simp

/-- **A mode `m ≥ 2`**: if `|u(ξ)| ≤ cξS` on `[m, X]`, then
`|∫_m^X ψ(1 − m/ξ)| ≤ (S/c)·(m²/(m² − 1))·(3/(2m))`. -/
theorem abs_mode_le {c χ m X S : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ : χ < c ^ 2) (hm : 2 ≤ m) (hmX : m ≤ X)
    (hS : 0 ≤ S) (hψc : ContinuousOn ψ (Icc 1 X)) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hus : ∀ ξ ∈ Icc m X, |u ξ| ≤ c * ξ * S) :
    |∫ ξ in m..X, ψ ξ * (1 - m / ξ)| ≤ S / c * (m ^ 2 / (m ^ 2 - 1) * (3 / (2 * m))) := by
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun ξ => (hu ξ).continuousAt
  rw [integral_mode_eq hχ (by linarith) hmX hψc hu]
  have hB := abs_bdry_le hc hχ.le hmX (by linarith) hS (hus X ⟨hmX, le_rfl⟩)
  have hc2 : ContinuousOn (fun ξ => u ξ * hW c χ m ξ) (Icc m X) :=
    huc.continuousOn.mul (continuousOn_hW hχ (by linarith))
  have hG : ContinuousOn (fun ξ => S / c * Gm' m ξ) (Icc m X) :=
    continuousOn_const.mul (continuousOn_Gm' hm)
  have hI : |∫ ξ in m..X, u ξ * hW c χ m ξ| ≤ S / c * (Gm m X - Gm m m) := by
    refine (abs_integral_le_integral_abs hmX).trans ?_
    refine (integral_mono_on hmX (hc2.abs.intervalIntegrable_of_Icc hmX) (hG.intervalIntegrable_of_Icc hmX)
      fun ξ hξ => abs_u_hW_le hc hχ.le hm hξ.1 hS (hus ξ hξ)).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul]
    congr 1
    refine integral_eq_sub_of_hasDerivAt (fun ξ hξ => hasDerivAt_Gm m ?_)
      ((continuousOn_Gm' hm).intervalIntegrable_of_Icc hmX)
    rw [uIcc_of_le hmX] at hξ; linarith [hξ.1]
  have hm1 : 0 < m ^ 2 - 1 := by nlinarith
  have hX1 : 0 < X ^ 2 - 1 := by nlinarith
  have hGmm : Gm m m = -(m ^ 2 / (m ^ 2 - 1) * (3 / (2 * m))) := by
    unfold Gm; have : m ≠ 0 := by linarith
    field_simp; ring
  have hneg : m ^ 2 / (m ^ 2 - 1) * (-(m / (2 * X ^ 2)) - 1 / X) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (by have : 0 ≤ m / (2 * X ^ 2) := by positivity
          have : 0 ≤ 1 / X := by have : 0 < X := by linarith
                                 positivity
          linarith)
  have hsum : (X - m) / (X ^ 2 - 1) + (Gm m X - Gm m m) ≤ m ^ 2 / (m ^ 2 - 1) * (3 / (2 * m)) := by
    rw [hGmm]; unfold Gm; linarith
  calc |-(u X * (1 - m / X) / qP c χ X) + ∫ ξ in m..X, u ξ * hW c χ m ξ|
      ≤ |u X * (1 - m / X) / qP c χ X| + |∫ ξ in m..X, u ξ * hW c χ m ξ| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_neg]
    _ ≤ S / c * ((X - m) / (X ^ 2 - 1)) + S / c * (Gm m X - Gm m m) := add_le_add hB hI
    _ = S / c * ((X - m) / (X ^ 2 - 1) + (Gm m X - Gm m m)) := by ring
    _ ≤ S / c * (m ^ 2 / (m ^ 2 - 1) * (3 / (2 * m))) := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **The weighted mass is at most `5/4` of the mass**: for `c ≥ 80`, `5c ≤ c² − χ`, `X ≥ 2`, a prolate system with
`u(1) = 0` and `E(X) ≤ 6c∫₁^X ψ²`, `∫₁^X u²/(pq) ≤ (5/4)∫₁^X ψ²`. -/
theorem integral_u_sq_le {c χ X : ℝ} {ψ u : ℝ → ℝ} (hc : 80 ≤ c) (hσ : 5 * c ≤ c ^ 2 - χ) (hX : 2 ≤ X)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hψc : Continuous ψ) (hu1 : u 1 = 0)
    (hUi : IntervalIntegrable (fun ξ => u ξ ^ 2 / (pP ξ * qP c χ ξ)) volume 1 X)
    (hEX : energy (aP c χ) ψ u X ≤ 6 * c * ∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2) :
    ∫ ξ in (1 : ℝ)..X, u ξ ^ 2 / (pP ξ * qP c χ ξ) ≤ 5 / 4 * ∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hχ : χ < c ^ 2 := by nlinarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun ξ => (hu ξ).continuousAt
  have hid := Cvs.Prolate.ProlateWindowMassIdentity.integral_u_sq_eq hX1 hχ hψc.continuousOn huc.continuousOn
    (fun t ht => hψ t ht.1) (fun t _ => hu t) hu1
  set M := ∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2 with hMdef
  set U := ∫ ξ in (1 : ℝ)..X, u ξ ^ 2 / (pP ξ * qP c χ ξ)
  have hψ2 : IntervalIntegrable (fun ξ => ψ ξ ^ 2) volume 1 X := (hψc.pow 2).intervalIntegrable 1 X
  have hM : 0 ≤ M := integral_nonneg hX1 fun ξ _ => sq_nonneg _
  have hqX : 3 * c ^ 2 ≤ qP c χ X := by
    unfold qP; nlinarith [mul_le_mul_of_nonneg_left (show (4 : ℝ) ≤ X ^ 2 by nlinarith) hc2.le]
  have hV : |ψ X * u X / qP c χ X| ≤ M / c := by
    have hE := (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos (by linarith : (1 : ℝ) < X) hc2 hχ)).trans hEX
    rw [abs_div, abs_of_pos (by linarith : 0 < qP c χ X)]
    calc |ψ X * u X| / qP c χ X ≤ (3 * c * M) / (3 * c ^ 2) :=
          div_le_div₀ (by positivity) (by linarith) (by positivity) hqX
      _ = M / c := by field_simp
  have hq : ∀ ξ ∈ Icc 1 X, 0 < qP c χ ξ := fun ξ hξ => qP_pos_of_one_le hχ hξ.1
  have hqc : Continuous (qP c χ) := by unfold qP; fun_prop
  have hTc : ContinuousOn (fun ξ => ψ ξ * u ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2) (Icc 1 X) :=
    ((hψc.mul huc).mul (by fun_prop)).continuousOn.div₀ (hqc.pow 2).continuousOn
      fun t ht => by have := hq t ht; positivity
  have hJ : ∫ ξ in (1 : ℝ)..X, ψ ξ * u ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2 ≤ (M + U) / 10 := by
    have hR : IntervalIntegrable (fun ξ => (ψ ξ ^ 2 + u ξ ^ 2 / (pP ξ * qP c χ ξ)) / 10) volume 1 X :=
      (hψ2.add hUi).div_const 10
    refine (integral_mono_on_of_le_Ioo hX1 (hTc.intervalIntegrable_of_Icc hX1) hR fun ξ hξ => ?_).trans
      (le_of_eq ?_)
    · exact (le_abs_self _).trans (abs_cross_le (pP_pos hξ.1) (hq ξ (Ioo_subset_Icc_self hξ))
        (qP_cube_ge hc hσ hξ.1.le))
    · rw [intervalIntegral.integral_div, integral_add hψ2 hUi]
  have hMc : M / c ≤ M / 80 := div_le_div_of_nonneg_left hM (by norm_num) hc
  have hVle := (le_abs_self _).trans hV
  rw [hid] at hJ ⊢
  linarith

/-- `∫₁^X (3/ξ⁴ + 6/(ξ+1)²) ≤ 4`. -/
theorem integral_kappa_le {X : ℝ} (hX : 1 ≤ X) : ∫ ξ in (1 : ℝ)..X, (3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) ≤ 4 := by
  have hd : ∀ ξ ∈ uIcc 1 X, HasDerivAt (fun ξ => -(1 / ξ ^ 3) - 6 / (ξ + 1)) (3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) ξ := by
    intro ξ hξ
    rw [uIcc_of_le hX] at hξ
    have h0 : ξ ≠ 0 := by linarith [hξ.1]
    have h1 : ξ + 1 ≠ 0 := by linarith [hξ.1]
    have a := ((hasDerivAt_const ξ (1 : ℝ)).div (hasDerivAt_pow 3 ξ) (pow_ne_zero 3 h0)).neg.sub
      ((hasDerivAt_const ξ (6 : ℝ)).div ((hasDerivAt_id ξ).add_const 1) h1)
    refine a.congr_deriv ?_
    simp only [id]; field_simp; ring
  have hc : ContinuousOn (fun ξ : ℝ => 3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) (Icc 1 X) := by
    have hd1 : ContinuousOn (fun ξ : ℝ => ξ ^ 4) (Icc 1 X) := continuousOn_id.pow 4
    have hd2 : ContinuousOn (fun ξ : ℝ => (ξ + 1) ^ 2) (Icc 1 X) :=
      (continuousOn_id.add continuousOn_const).pow 2
    refine ContinuousOn.add (continuousOn_const.div₀ hd1 fun ξ hξ => ?_)
      (continuousOn_const.div₀ hd2 fun ξ hξ => ?_)
    · exact pow_ne_zero 4 (show ξ ≠ 0 by linarith [hξ.1])
    · exact pow_ne_zero 2 (show ξ + 1 ≠ 0 by linarith [hξ.1])
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hX)]
  have hX0 : 0 < X := by linarith
  have : 0 ≤ 1 / X ^ 3 := by positivity
  have : 0 ≤ 6 / (X + 1) := by positivity
  have e : (-(1 / (1 : ℝ) ^ 3) - 6 / ((1 : ℝ) + 1)) = -4 := by norm_num
  rw [e]; linarith

/-- **The interior of the mode `m = 1`**: if `∫₁^X u²/(pq) ≤ A`, then `|∫₁^X u h₁| ≤ 2√((A/2)(2/c²))`. -/
theorem abs_mode_one_interior_le {c χ X A : ℝ} {u : ℝ → ℝ} (hc : 0 < c) (hχ : χ < c ^ 2) (hX : 1 ≤ X)
    (huc : Continuous u) (hUi : IntervalIntegrable (fun ξ => u ξ ^ 2 / (pP ξ * qP c χ ξ)) volume 1 X)
    (hA : ∫ ξ in (1 : ℝ)..X, u ξ ^ 2 / (pP ξ * qP c χ ξ) ≤ A) :
    |∫ ξ in (1 : ℝ)..X, u ξ * hW c χ 1 ξ| ≤ 2 * √(A / 2 * (2 / c ^ 2)) := by
  have hq : ∀ ξ ∈ Icc 1 X, 0 < qP c χ ξ := fun ξ hξ => qP_pos_of_one_le hχ hξ.1
  have hU0 : 0 ≤ ∫ ξ in (1 : ℝ)..X, u ξ ^ 2 / (pP ξ * qP c χ ξ) :=
    intervalIntegral.integral_nonneg (μ := volume) hX fun ξ hξ => div_nonneg (sq_nonneg _)
      (mul_nonneg (by unfold pP; nlinarith [hξ.1]) (hq ξ hξ).le)
  have hκc : ContinuousOn (fun ξ : ℝ => 3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) (Icc 1 X) := by
    have hd1 : ContinuousOn (fun ξ : ℝ => ξ ^ 4) (Icc 1 X) := continuousOn_id.pow 4
    have hd2 : ContinuousOn (fun ξ : ℝ => (ξ + 1) ^ 2) (Icc 1 X) :=
      (continuousOn_id.add continuousOn_const).pow 2
    refine ContinuousOn.add (continuousOn_const.div₀ hd1 fun ξ hξ => ?_)
      (continuousOn_const.div₀ hd2 fun ξ hξ => ?_)
    · exact pow_ne_zero 4 (show ξ ≠ 0 by linarith [hξ.1])
    · exact pow_ne_zero 2 (show ξ + 1 ≠ 0 by linarith [hξ.1])
  have hκi := hκc.intervalIntegrable_of_Icc (μ := volume) hX
  have hc2 : ContinuousOn (fun ξ => u ξ * hW c χ 1 ξ) (Icc 1 X) :=
    huc.continuousOn.mul (continuousOn_hW hχ le_rfl)
  refine le_two_sqrt_mul (by linarith) (by positivity) fun t ht => ?_
  have hR : IntervalIntegrable (fun ξ => t / 2 * (u ξ ^ 2 / (pP ξ * qP c χ ξ))
      + 1 / (2 * t) * ((3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) / c ^ 2)) volume 1 X :=
    (hUi.const_mul _).add ((hκi.div_const _).const_mul _)
  have hpt : ∀ ξ ∈ Ioo 1 X, |u ξ * hW c χ 1 ξ| ≤ t / 2 * (u ξ ^ 2 / (pP ξ * qP c χ ξ))
      + 1 / (2 * t) * ((3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) / c ^ 2) := by
    intro ξ hξ
    have hp := pP_pos hξ.1
    have hqξ := hq ξ (Ioo_subset_Icc_self hξ)
    refine abs_mul_le_amgm ht (by positivity) (by positivity) (pq_hW_one_sq_le hc hχ.le hξ.1) ?_
    field_simp
  calc |∫ ξ in (1 : ℝ)..X, u ξ * hW c χ 1 ξ|
      ≤ ∫ ξ in (1 : ℝ)..X, |u ξ * hW c χ 1 ξ| := abs_integral_le_integral_abs hX
    _ ≤ ∫ ξ in (1 : ℝ)..X, (t / 2 * (u ξ ^ 2 / (pP ξ * qP c χ ξ))
          + 1 / (2 * t) * ((3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) / c ^ 2)) :=
        integral_mono_on_of_le_Ioo hX (hc2.abs.intervalIntegrable_of_Icc hX) hR hpt
    _ = t / 2 * (∫ ξ in (1 : ℝ)..X, u ξ ^ 2 / (pP ξ * qP c χ ξ))
          + 1 / (2 * t) * ((∫ ξ in (1 : ℝ)..X, (3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2)) / c ^ 2) := by
        rw [integral_add (hUi.const_mul _) ((hκi.div_const _).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_div]
    _ ≤ t / 2 * A + 1 / (2 * t) * (4 / c ^ 2) := by
        gcongr
        exact integral_kappa_le hX
    _ = t * (A / 2) + 2 / c ^ 2 / t := by field_simp; ring

/-- `|u(ξ)| ≤ cξ·(5/2)√M` at `ξ > 1` from `E(ξ) ≤ 6cM`, for `0 ≤ χ < c²`. -/
theorem abs_u_le_of_energy {c χ ξ M : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hξ : 1 < ξ) (hM : 0 ≤ M) (hE : energy (aP c χ) ψ u ξ ≤ 6 * c * M) : |u ξ| ≤ c * ξ * (5 / 2 * √M) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos hξ hc2 hχ
  have haξ : aP c χ ξ ≤ c * ξ ^ 2 := by
    unfold aP
    rw [sqrt_le_left (by positivity)]
    have hp' : pP ξ ≤ ξ ^ 2 := by unfold pP; linarith
    have hq' : qP c χ ξ ≤ c ^ 2 * ξ ^ 2 := by unfold qP; linarith
    have hq0 : 0 ≤ qP c χ ξ := (qP_pos hξ hc2 hχ).le
    calc pP ξ * qP c χ ξ ≤ ξ ^ 2 * (c ^ 2 * ξ ^ 2) := mul_le_mul hp' hq' hq0 (sq_nonneg _)
      _ = (c * ξ ^ 2) ^ 2 := by ring
  have h1 : u ξ ^ 2 / aP c χ ξ ≤ 6 * c * M := by
    unfold energy at hE
    have : 0 ≤ aP c χ ξ * ψ ξ ^ 2 := by positivity
    linarith
  have h2 : u ξ ^ 2 ≤ 6 * c * M * (c * ξ ^ 2) := by
    rw [div_le_iff₀ ha] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left haξ (by positivity))
  have h3 : |u ξ| ^ 2 ≤ (c * ξ * (5 / 2 * √M)) ^ 2 := by
    rw [sq_abs]
    have : (c * ξ * (5 / 2 * √M)) ^ 2 = 25 / 4 * c ^ 2 * ξ ^ 2 * M := by
      rw [show (c * ξ * (5 / 2 * √M)) ^ 2 = 25 / 4 * c ^ 2 * ξ ^ 2 * √M ^ 2 by ring, sq_sqrt hM]
    rw [this]; nlinarith [mul_nonneg (mul_nonneg hc2.le (sq_nonneg ξ)) hM]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp h3

/-- **The tilted pole of a prolate solution**: for `c ≥ 80`, `0 ≤ χ`, `5c ≤ c² − χ`, `X ≥ 2` and a system
`ψ' = u/p` (`ξ > 1`), `u' = −qψ` with `u(1) = 0` and `u²/(pq)` integrable on `[1, X]`,
`|∫_{(1,∞)} posTail ψ X θ (1 − 1/θ)| ≤ 7√(∫₁^X ψ²)/c`. -/
theorem tilt_le {c χ X : ℝ} {ψ u : ℝ → ℝ} (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hσ : 5 * c ≤ c ^ 2 - χ) (hX : 2 ≤ X)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hψc : Continuous ψ) (hu1 : u 1 = 0)
    (hUi : IntervalIntegrable (fun ξ => u ξ ^ 2 / (pP ξ * qP c χ ξ)) volume 1 X) :
    |∫ θ in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail ψ X θ * (1 - 1 / θ)|
      ≤ 7 * √(∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2) / c := by
  have hc0 : 0 < c := by linarith
  have hχ : χ < c ^ 2 := by nlinarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun ξ => (hu ξ).continuousAt
  have hE := Cvs.Prolate.ProlateWindowMassIdentity.far_energy_le hc hχ0 hχ hX (fun t ht => hψ t (by linarith [ht.1]))
    (fun t _ => hu t) hψc.continuousOn
  set M := ∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2 with hMdef
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg hX1 fun ξ _ => sq_nonneg _
  set r := √M with hrdef
  have hr : 0 ≤ r := sqrt_nonneg _
  have hr2 : r ^ 2 = M := sq_sqrt hM
  set S := 5 / 2 * r with hSdef
  have hS : 0 ≤ S := by positivity
  have hus : ∀ ξ ∈ Icc (6 / 5 : ℝ) X, |u ξ| ≤ c * ξ * S := fun ξ hξ =>
    abs_u_le_of_energy hc0 hχ0 hχ (by linarith [hξ.1]) hM (hE ξ hξ)
  have hw : ContinuousOn (fun θ : ℝ => 1 - 1 / θ) (Icc 1 X) :=
    continuousOn_const.sub (continuousOn_const.div₀ continuousOn_id fun θ hθ => by
      have := hθ.1; linarith)
  rw [Cvs.L2a.PositionTailSpanAdapters.integral_posTail_mul hX1 hψc.continuousOn hw]
  have hK : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ ⌊X⌋₊)]
  -- the mode `m = 1`
  have h1 : |((1 : ℕ) : ℝ)⁻¹ * ∫ ξ in ((1 : ℕ) : ℝ)..X, ψ ξ * (1 - 1 / (ξ / ((1 : ℕ) : ℝ)))|
      ≤ 9 / 4 * r / c + S / c * (1 / 3) := by
    simp only [Nat.cast_one, inv_one, one_mul, div_one]
    rw [integral_mode_eq hχ le_rfl hX1 hψc.continuousOn hu]
    have hB := abs_bdry_le (m := 1) hc0 hχ.le hX1 (by linarith : (1 : ℝ) < X) hS (hus X ⟨by linarith, le_rfl⟩)
    have hB' : (X - 1) / (X ^ 2 - 1) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
    have hU := integral_u_sq_le hc hσ hX hψ hu hψc hu1 hUi (hE X ⟨by linarith, le_rfl⟩)
    have hI := abs_mode_one_interior_le (A := 5 / 4 * M) hc0 hχ hX1 huc hUi hU
    have hsq : √(5 / 4 * M / 2 * (2 / c ^ 2)) ≤ 9 / 8 * r / c := by
      rw [sqrt_le_left (by positivity)]
      have e1 : 5 / 4 * M / 2 * (2 / c ^ 2) = (5 / 4 * M) / c ^ 2 := by field_simp
      have e2 : (9 / 8 * r / c) ^ 2 = (81 / 64 * M) / c ^ 2 := by rw [div_pow, mul_pow, hr2]; ring
      rw [e1, e2]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hB'' : S / c * ((X - 1) / (X ^ 2 - 1)) ≤ S / c * (1 / 3) :=
      mul_le_mul_of_nonneg_left hB' (by positivity)
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    calc _ ≤ S / c * ((X - 1) / (X ^ 2 - 1)) + 2 * √(5 / 4 * M / 2 * (2 / c ^ 2)) := add_le_add hB hI
      _ ≤ S / c * (1 / 3) + 2 * (9 / 8 * r / c) :=
          add_le_add hB'' (mul_le_mul_of_nonneg_left hsq (by norm_num))
      _ = 9 / 4 * r / c + S / c * (1 / 3) := by ring
  -- the modes `m ≥ 2`
  have h2 : |∑ m ∈ Finset.Ioc 1 ⌊X⌋₊, (m : ℝ)⁻¹ * ∫ ξ in (m : ℝ)..X, ψ ξ * (1 - 1 / (ξ / m))|
      ≤ S / c * (3 / 2) * (3 / 4) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ Finset.Ioc 1 ⌊X⌋₊, |(m : ℝ)⁻¹ * ∫ ξ in (m : ℝ)..X, ψ ξ * (1 - 1 / (ξ / m))|
        ≤ ∑ m ∈ Finset.Ioc 1 ⌊X⌋₊, S / c * (3 / 2) * (1 / ((m : ℝ) ^ 2 - 1)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' := Finset.mem_Ioc.mp hm
          have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm'.1
          have hmX : (m : ℝ) ≤ X :=
            le_trans (by exact_mod_cast hm'.2) (Nat.floor_le (by linarith))
          have hm0 : (m : ℝ) ≠ 0 := by linarith
          have hm1 : (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
          have e : ∫ ξ in (m : ℝ)..X, ψ ξ * (1 - 1 / (ξ / m)) = ∫ ξ in (m : ℝ)..X, ψ ξ * (1 - m / ξ) :=
            intervalIntegral.integral_congr fun ξ _ => by simp only [one_div_div]
          rw [e, abs_mul, abs_inv, Nat.abs_cast]
          have hb := abs_mode_le hc0 hχ hm2 hmX hS hψc.continuousOn hu
            (fun ξ hξ => hus ξ ⟨by linarith [hξ.1], hξ.2⟩)
          calc (m : ℝ)⁻¹ * |∫ ξ in (m : ℝ)..X, ψ ξ * (1 - m / ξ)|
              ≤ (m : ℝ)⁻¹ * (S / c * ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1) * (3 / (2 * m)))) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = S / c * (3 / 2) * (1 / ((m : ℝ) ^ 2 - 1)) := by field_simp
      _ = S / c * (3 / 2) * ∑ m ∈ Finset.Ioc 1 ⌊X⌋₊, 1 / ((m : ℝ) ^ 2 - 1) := by rw [Finset.mul_sum]
      _ ≤ S / c * (3 / 2) * (3 / 4) :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_sub_one_le _) (by positivity)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ (9 / 4 * r / c + S / c * (1 / 3)) + S / c * (3 / 2) * (3 / 4) := add_le_add h1 h2
    _ = 283 / 48 * r / c := by rw [hSdef]; ring
    _ ≤ 7 * r / c := div_le_div_of_nonneg_right (by linarith) hc0.le

section rung

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- **The per-rung tilted pole**: for a rung `ψ = psi c g` with `c ≥ 80`, `0 ≤ χ`, `5c ≤ c² − χ` and `X ≥ 2`,
`|∫_{(1,∞)} posTail ψ X θ (1 − 1/θ)| ≤ 7√(∫₁^X ψ²)/c`. -/
theorem tilt_le_rung (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {X : ℝ} (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hσ : 5 * c ≤ c ^ 2 - χ) (hX : 2 ≤ X) :
    |∫ θ in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail (psi c g) X θ * (1 - 1 / θ)|
      ≤ 7 * √(∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2) / c := by
  obtain ⟨hψ, hu, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hχ : χ < c ^ 2 := by nlinarith
  refine tilt_le hc hχ0 hσ hX hψ hu hψc (Cvs.L2a.PositionTailSpanAdapters.rungU_one c g) ?_
  obtain ⟨-, hv, -⟩ := psi_system hg hg₁ hg₂c hang
  set v := Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s)))
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun ξ => (hv ξ).continuousAt
  have hq : ∀ ξ ∈ Icc 1 X, qP c χ ξ ≠ 0 := fun ξ hξ => (qP_pos_of_one_le hχ hξ.1).ne'
  have hqc : Continuous (qP c χ) := by unfold qP; fun_prop
  have hpc : Continuous pP := by unfold pP; fun_prop
  have hcont : ContinuousOn (fun ξ => pP ξ * v ξ ^ 2 / qP c χ ξ) (Icc 1 X) :=
    (hpc.mul (hvc.pow 2)).continuousOn.div₀ hqc.continuousOn hq
  refine (hcont.congr fun ξ hξ => ?_).intervalIntegrable_of_Icc (by linarith)
  show (pP ξ * v ξ) ^ 2 / (pP ξ * qP c χ ξ) = pP ξ * v ξ ^ 2 / qP c χ ξ
  by_cases hp : pP ξ = 0
  · simp [hp]
  · have := hq ξ hξ
    field_simp

end rung

end Cvs.L2a.RungTiltedPole
