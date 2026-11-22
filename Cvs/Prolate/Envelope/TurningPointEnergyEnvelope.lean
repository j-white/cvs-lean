import Mathlib
import Cvs.L2a.RungTiltedPole
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyGrowth
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy
import Cvs.Prolate.ProlateWindowMassIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cut at `1 + 6/c` and the energy envelope past the turning point

On `[1 + 6/c, ∞)` with `c ≥ 80` and `χ ≤ c² + c/2`: ellipticity `(23/24)c²p ≤ q` and the cube inequality.
For `0 ≤ χ ≤ c² + c/2` the sign polynomial stays nonnegative, so Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval–`ProlateArcsinMassLaw`'s energy window and arcsin
law hold with `q > 0` in place of `χ < c²`; hence `E ≤ (25/4)cM` on `[6/5, X]` and `E(1 + 6/c) ≤ 9cM`.
-/

namespace Cvs.Prolate.Envelope.TurningPointEnergyEnvelope

open Real Set MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungTiltedPole

/-! ### The cut `ξ₀ = 1 + 6/c` -/

/-- `12 ≤ c(ξ² − 1)` for `c > 0` and `ξ ≥ 1 + 6/c`. -/
theorem twelve_le_c_pP {c ξ : ℝ} (hc : 0 < c) (hξ : 1 + 6 / c ≤ ξ) : 12 ≤ c * pP ξ := by
  have hy6 : 6 ≤ c * (ξ - 1) := by
    have h := mul_le_mul_of_nonneg_left (show 6 / c ≤ ξ - 1 by linarith) hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at h
  have hξ1 : 0 ≤ ξ - 1 := by have : 0 < 6 / c := by positivity
                             linarith
  have e : c * pP ξ = c * (ξ - 1) * (ξ + 1) := by unfold pP; ring
  rw [e]; nlinarith

/-- `10ξ ≤ c(ξ² − 1)` for `c ≥ 12` and `ξ ≥ 1 + 6/c`. -/
theorem ten_mul_le_c_pP {c ξ : ℝ} (hc : 12 ≤ c) (hξ : 1 + 6 / c ≤ ξ) : 10 * ξ ≤ c * pP ξ := by
  have hc0 : 0 < c := by linarith
  have hy6 : 6 ≤ c * (ξ - 1) := by
    have h := mul_le_mul_of_nonneg_left (show 6 / c ≤ ξ - 1 by linarith) hc0.le
    rwa [mul_div_cancel₀ _ hc0.ne'] at h
  have e : c * pP ξ - 10 * ξ = (c * (ξ - 1)) * (ξ - 1) + 2 * (c * (ξ - 1)) - 10 * (ξ - 1) - 10 := by
    unfold pP; ring
  -- with `y = c(ξ − 1) ≥ 6`: `y(ξ − 1) + 2y − 10(ξ − 1) − 10 = (y − 10)(ξ − 1) + 2y − 10`, and `c(ξ − 1) = y`
  have hξ1 : 0 ≤ ξ - 1 := by have : 0 < 6 / c := by positivity
                             linarith
  have key : 0 ≤ (c * (ξ - 1) - 10) * (ξ - 1) + 2 * (c * (ξ - 1)) - 10 := by
    rcases le_or_gt 10 (c * (ξ - 1)) with h | h
    · nlinarith
    · have hc1 : c * ((c * (ξ - 1) - 10) * (ξ - 1) + 2 * (c * (ξ - 1)) - 10)
          = (c * (ξ - 1) - 10) * (c * (ξ - 1)) + c * (2 * (c * (ξ - 1)) - 10) := by ring
      have hm : 0 ≤ c * ((c * (ξ - 1) - 10) * (ξ - 1) + 2 * (c * (ξ - 1)) - 10) := by
        rw [hc1]
        nlinarith [mul_le_mul_of_nonneg_right hc (show (0:ℝ) ≤ 2 * (c * (ξ - 1)) - 10 by linarith)]
      exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hm) hc0
  linarith [e]

/-- `11ξ ≤ c(ξ² − 1)` for `c ≥ 80` and `ξ ≥ 1 + 6/c`. -/
theorem eleven_mul_le_c_pP {c ξ : ℝ} (hc : 80 ≤ c) (hξ : 1 + 6 / c ≤ ξ) : 11 * ξ ≤ c * pP ξ := by
  have hc0 : 0 < c := by linarith
  have hy6 : 6 ≤ c * (ξ - 1) := by
    have h := mul_le_mul_of_nonneg_left (show 6 / c ≤ ξ - 1 by linarith) hc0.le
    rwa [mul_div_cancel₀ _ hc0.ne'] at h
  have e : c * pP ξ - 11 * ξ = (c * (ξ - 1) - 11) * (ξ - 1) + 2 * (c * (ξ - 1)) - 11 := by unfold pP; ring
  have hξ1 : 0 ≤ ξ - 1 := by have : 0 < 6 / c := by positivity
                             linarith
  have key : 0 ≤ (c * (ξ - 1) - 11) * (ξ - 1) + 2 * (c * (ξ - 1)) - 11 := by
    rcases le_or_gt 11 (c * (ξ - 1)) with h | h
    · nlinarith
    · have hc1 : c * ((c * (ξ - 1) - 11) * (ξ - 1) + 2 * (c * (ξ - 1)) - 11)
          = (c * (ξ - 1) - 11) * (c * (ξ - 1)) + c * (2 * (c * (ξ - 1)) - 11) := by ring
      have hm : 0 ≤ c * ((c * (ξ - 1) - 11) * (ξ - 1) + 2 * (c * (ξ - 1)) - 11) := by
        rw [hc1]
        nlinarith [mul_le_mul_of_nonneg_right hc (show (0:ℝ) ≤ 2 * (c * (ξ - 1)) - 11 by linarith)]
      exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hm) hc0
  linarith [e]

/-- **Ellipticity beyond the cut for `χ ≤ c² + c/2`**: `(23/24)c²p ≤ q` on `[1 + 6/c, ∞)`. -/
theorem ell_of_le {c χ ξ : ℝ} (hc : 0 < c) (hχ1 : χ ≤ c ^ 2 + c / 2) (hξ : 1 + 6 / c ≤ ξ) :
    23 / 24 * (c ^ 2 * pP ξ) ≤ qP c χ ξ := by
  have h12 := twelve_le_c_pP hc hξ
  have e : qP c χ ξ = c ^ 2 * pP ξ + (c ^ 2 - χ) := by unfold qP pP; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h12 hc.le]

/-- **The cube inequality with no σ cut**: `25p(2c²ξ)² ≤ q³` wherever `10ξ ≤ cp`, `ξ ≥ 1`, `χ ≤ c²`. -/
theorem qP_cube_ge_of_ten {c χ ξ : ℝ} (hc : 0 < c) (hχ : χ ≤ c ^ 2) (hξ : 1 ≤ ξ) (h10 : 10 * ξ ≤ c * pP ξ) :
    25 * pP ξ * (2 * c ^ 2 * ξ) ^ 2 ≤ qP c χ ξ ^ 3 := by
  have hp : 0 ≤ pP ξ := by unfold pP; nlinarith
  have hcp := c_sq_pP_le_qP (c := c) (ξ := ξ) hχ
  have h1 : (c ^ 2 * pP ξ) ^ 3 ≤ qP c χ ξ ^ 3 := pow_le_pow_left₀ (by positivity) hcp 3
  have h2 : 100 * ξ ^ 2 ≤ (c * pP ξ) ^ 2 := by nlinarith
  calc 25 * pP ξ * (2 * c ^ 2 * ξ) ^ 2 = c ^ 4 * pP ξ * (100 * ξ ^ 2) := by ring
    _ ≤ c ^ 4 * pP ξ * (c * pP ξ) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (c ^ 2 * pP ξ) ^ 3 := by ring
    _ ≤ qP c χ ξ ^ 3 := h1

/-- **The cube inequality for `χ ≤ c² + c/2`**: `25p(2c²ξ)² ≤ q³` on `[1 + 6/c, ∞)`, `c ≥ 80`. -/
theorem cube_of_le {c χ ξ : ℝ} (hc : 80 ≤ c) (hχ1 : χ ≤ c ^ 2 + c / 2) (hξ : 1 + 6 / c ≤ ξ) :
    25 * pP ξ * (2 * c ^ 2 * ξ) ^ 2 ≤ qP c χ ξ ^ 3 := by
  have hc0 : 0 < c := by linarith
  have h6 : 0 < 6 / c := by positivity
  have hξ1 : 1 ≤ ξ := by linarith
  have hp : 0 ≤ pP ξ := by unfold pP; nlinarith
  have hell := ell_of_le hc0 hχ1 hξ
  have h11 := eleven_mul_le_c_pP hc hξ
  have h1 : (23 / 24 * (c ^ 2 * pP ξ)) ^ 3 ≤ qP c χ ξ ^ 3 := pow_le_pow_left₀ (by positivity) hell 3
  have h2 : 121 * ξ ^ 2 ≤ (c * pP ξ) ^ 2 := by nlinarith
  calc 25 * pP ξ * (2 * c ^ 2 * ξ) ^ 2 = c ^ 4 * pP ξ * (100 * ξ ^ 2) := by ring
    _ ≤ c ^ 4 * pP ξ * ((23 / 24) ^ 3 * (c * pP ξ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = (23 / 24 * (c ^ 2 * pP ξ)) ^ 3 := by ring
    _ ≤ qP c χ ξ ^ 3 := h1

/-- `2√A ≤ B` from `4A ≤ B²`, `A, B ≥ 0`. -/
theorem two_sqrt_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : 4 * A ≤ B ^ 2) : 2 * √A ≤ B := by
  have e : (2 * √A) ^ 2 = 4 * A := by rw [mul_pow, sq_sqrt hA]; norm_num
  exact (pow_le_pow_iff_left₀ (by positivity) hB two_ne_zero).mp (by rw [e]; exact h)

/-- `∫₁^a (ξ − 1)² = (a − 1)³/3`. -/
theorem integral_sub_one_sq (a : ℝ) : ∫ ξ in (1 : ℝ)..a, (ξ - 1) ^ 2 = (a - 1) ^ 3 / 3 := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ 2) 1, integral_pow]
  norm_num

/-- `∫_a^X (3/ξ⁴ + 6/(ξ+1)²) ≤ 4` for `1 ≤ a ≤ X`. -/
theorem integral_kappa_le_from {a X : ℝ} (ha : 1 ≤ a) (haX : a ≤ X) :
    ∫ ξ in a..X, (3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) ≤ 4 := by
  have hd : ∀ ξ ∈ uIcc a X, HasDerivAt (fun ξ => -(1 / ξ ^ 3) - 6 / (ξ + 1)) (3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) ξ := by
    intro ξ hξ
    rw [uIcc_of_le haX] at hξ
    have h0 : ξ ≠ 0 := by linarith [hξ.1]
    have h1 : ξ + 1 ≠ 0 := by linarith [hξ.1]
    have := ((hasDerivAt_const ξ (1 : ℝ)).div (hasDerivAt_pow 3 ξ) (pow_ne_zero 3 h0)).neg.sub
      ((hasDerivAt_const ξ (6 : ℝ)).div ((hasDerivAt_id ξ).add_const 1) h1)
    refine this.congr_deriv ?_
    simp only [id]; field_simp; ring
  have hc : ContinuousOn (fun ξ : ℝ => 3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) (Icc a X) := by
    have hc4 : ContinuousOn (fun ξ : ℝ => ξ ^ 4) (Icc a X) := continuousOn_id.pow 4
    have hc2 : ContinuousOn (fun ξ : ℝ => (ξ + 1) ^ 2) (Icc a X) :=
      (continuousOn_id.add continuousOn_const).pow 2
    refine ContinuousOn.add (continuousOn_const.div₀ hc4 fun ξ hξ => ?_)
      (continuousOn_const.div₀ hc2 fun ξ hξ => ?_)
    · exact pow_ne_zero 4 (by linarith [hξ.1] : (0 : ℝ) < ξ).ne'
    · exact pow_ne_zero 2 (by linarith [hξ.1] : (0 : ℝ) < ξ + 1).ne'
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc haX)]
  have hX0 : 0 < X := by linarith
  have ha0 : 0 < a := by linarith
  have h1 : 0 ≤ 1 / X ^ 3 := by positivity
  have h2 : 0 ≤ 6 / (X + 1) := by positivity
  have h3 : 1 / a ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ ha
  have h4 : 6 / (a + 1) ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

/-! ### Calculus from the cut -/

/-- `h_m` is continuous on `[a, X]` where `q > 0` and `a > 0`. -/
theorem continuousOn_hW_of_pos {c χ m a X : ℝ} (ha : 0 < a) (hq : ∀ ξ ∈ Icc a X, 0 < qP c χ ξ) :
    ContinuousOn (hW c χ m) (Icc a X) := by
  have hq' : ∀ ξ ∈ Icc a X, qP c χ ξ ≠ 0 := fun ξ hξ => (hq ξ hξ).ne'
  have hξ : ∀ ξ ∈ Icc a X, ξ ≠ 0 := fun ξ hξ => by linarith [hξ.1]
  have hqc : Continuous (qP c χ) := by unfold qP; fun_prop
  unfold hW
  have hden : ContinuousOn (fun ξ => ξ ^ 2 * qP c χ ξ) (Icc a X) :=
    (continuousOn_id.pow 2).mul hqc.continuousOn
  refine ContinuousOn.sub (continuousOn_const.div₀ hden fun ξ hξ' => ?_) ?_
  · exact mul_ne_zero (pow_ne_zero 2 (hξ ξ hξ')) (hq' ξ hξ')
  · have hlin : ContinuousOn (fun ξ : ℝ => 2 * c ^ 2 * ξ) (Icc a X) :=
      continuousOn_const.mul continuousOn_id
    have hm : ContinuousOn (fun ξ : ℝ => 1 - m / ξ) (Icc a X) :=
      continuousOn_const.sub (continuousOn_const.div₀ continuousOn_id hξ)
    exact ContinuousOn.div₀ (hm.mul hlin) (hqc.continuousOn.pow 2)
      fun ξ hξ' => pow_ne_zero 2 (hq' ξ hξ')

/-- **Integration by parts of a mode from `a`**: where `q > 0` on `[a, X]`, `a > 0` and `u' = −qψ`,
`∫_a^X ψ(1 − m/ξ) = −u(X)(1 − m/X)/q(X) + u(a)(1 − m/a)/q(a) + ∫_a^X u h_m`. -/
theorem integral_mode_eq_from {c χ m a X : ℝ} {ψ u : ℝ → ℝ} (ha : 0 < a) (haX : a ≤ X)
    (hq : ∀ ξ ∈ Icc a X, 0 < qP c χ ξ) (hψc : ContinuousOn ψ (Icc a X))
    (hu : ∀ ξ ∈ Icc a X, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) :
    ∫ ξ in a..X, ψ ξ * (1 - m / ξ)
      = -(u X * (1 - m / X) / qP c χ X) + u a * (1 - m / a) / qP c χ a + ∫ ξ in a..X, u ξ * hW c χ m ξ := by
  have hI : uIcc a X = Icc a X := uIcc_of_le haX
  have hξ : ∀ ξ ∈ Icc a X, ξ ≠ 0 := fun ξ hξ => by linarith [hξ.1]
  have huc : ContinuousOn u (Icc a X) := fun ξ hξ' => (hu ξ hξ').continuousAt.continuousWithinAt
  have hwc : ContinuousOn (fun ξ => 1 - m / ξ) (Icc a X) :=
    continuousOn_const.sub (continuousOn_const.div continuousOn_id hξ)
  have hc1 : ContinuousOn (fun ξ => ψ ξ * (1 - m / ξ)) (Icc a X) := hψc.mul hwc
  have hc2 : ContinuousOn (fun ξ => u ξ * hW c χ m ξ) (Icc a X) := huc.mul (continuousOn_hW_of_pos ha hq)
  have hderiv : ∀ ξ ∈ uIcc a X, HasDerivAt (fun ξ => -(u ξ * (1 - m / ξ) / qP c χ ξ))
      (ψ ξ * (1 - m / ξ) - u ξ * hW c χ m ξ) ξ := by
    intro ξ hξ'
    rw [hI] at hξ'
    have hw : HasDerivAt (fun ξ => 1 - m / ξ) (m / ξ ^ 2) ξ := by
      have := ((hasDerivAt_const ξ m).div (hasDerivAt_id ξ) (hξ ξ hξ')).const_sub 1
      refine this.congr_deriv ?_
      simp only [id]; field_simp; ring
    have := (((hu ξ hξ').mul hw).div (hasDerivAt_qP c χ ξ) (hq ξ hξ').ne').neg
    refine this.congr_deriv ?_
    have := (hq ξ hξ').ne'; have := hξ ξ hξ'
    simp only [Pi.mul_apply]
    unfold hW; field_simp; ring
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv ((hc1.sub hc2).intervalIntegrable_of_Icc haX)
  rw [integral_sub (hc1.intervalIntegrable_of_Icc haX) (hc2.intervalIntegrable_of_Icc haX)] at hFTC
  linarith

/-- **The weighted mass identity from `a > 1`**: where `q > 0` on `[a, X]`, `ψ' = u/p` and `u' = −qψ`,
`∫_a^X u²/(pq) = ∫_a^X ψ² + ψ(X)u(X)/q(X) − ψ(a)u(a)/q(a) + ∫_a^X ψu(2c²ξ)/q²`. -/
theorem integral_u_sq_eq_from {c χ a X : ℝ} {ψ u : ℝ → ℝ} (ha : 1 < a) (haX : a ≤ X)
    (hq : ∀ ξ ∈ Icc a X, 0 < qP c χ ξ) (hψ : ∀ ξ ∈ Icc a X, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc a X, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) :
    ∫ ξ in a..X, u ξ ^ 2 / (pP ξ * qP c χ ξ)
      = (∫ ξ in a..X, ψ ξ ^ 2) + ψ X * u X / qP c χ X - ψ a * u a / qP c χ a
        + ∫ ξ in a..X, ψ ξ * u ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2 := by
  have hI : uIcc a X = Icc a X := uIcc_of_le haX
  have hp : ∀ ξ ∈ Icc a X, 0 < pP ξ := fun ξ hξ => pP_pos (lt_of_lt_of_le ha hξ.1)
  have hψc : ContinuousOn ψ (Icc a X) := fun ξ hξ => (hψ ξ hξ).continuousAt.continuousWithinAt
  have huc : ContinuousOn u (Icc a X) := fun ξ hξ => (hu ξ hξ).continuousAt.continuousWithinAt
  have hqc : Continuous (qP c χ) := by unfold qP; fun_prop
  have hpc : Continuous pP := by unfold pP; fun_prop
  have hA : ContinuousOn (fun ξ => u ξ ^ 2 / (pP ξ * qP c χ ξ)) (Icc a X) :=
    (huc.pow 2).div (hpc.continuousOn.mul hqc.continuousOn) fun ξ hξ => (mul_pos (hp ξ hξ) (hq ξ hξ)).ne'
  have hB : ContinuousOn (fun ξ => ψ ξ ^ 2) (Icc a X) := hψc.pow 2
  have hC : ContinuousOn (fun ξ => ψ ξ * u ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2) (Icc a X) :=
    ((hψc.mul huc).mul (by fun_prop)).div (hqc.continuousOn.pow 2) fun ξ hξ => pow_ne_zero 2 (hq ξ hξ).ne'
  have hd : ∀ ξ ∈ uIcc a X, HasDerivAt (fun ξ => ψ ξ * u ξ / qP c χ ξ)
      (u ξ ^ 2 / (pP ξ * qP c χ ξ) - ψ ξ ^ 2 - ψ ξ * u ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2) ξ := by
    intro ξ hξ
    rw [hI] at hξ
    have := ((hψ ξ hξ).mul (hu ξ hξ)).div (hasDerivAt_qP c χ ξ) (hq ξ hξ).ne'
    refine this.congr_deriv ?_
    have := (hp ξ hξ).ne'; have := (hq ξ hξ).ne'
    simp only [Pi.mul_apply]
    field_simp; ring
  have hAB : ContinuousOn (fun ξ => u ξ ^ 2 / (pP ξ * qP c χ ξ) - ψ ξ ^ 2) (Icc a X) := hA.sub hB
  have hABC : ContinuousOn (fun ξ => u ξ ^ 2 / (pP ξ * qP c χ ξ) - ψ ξ ^ 2
      - ψ ξ * u ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2) (Icc a X) := hAB.sub hC
  have hFTC := integral_eq_sub_of_hasDerivAt hd (hABC.intervalIntegrable_of_Icc haX)
  rw [intervalIntegral.integral_sub (hAB.intervalIntegrable_of_Icc haX) (hC.intervalIntegrable_of_Icc haX),
    intervalIntegral.integral_sub (hA.intervalIntegrable_of_Icc haX) (hB.intervalIntegrable_of_Icc haX)] at hFTC
  linarith

/-- **The edge piece by Cauchy–Schwarz**: for `1 ≤ a`, `ψ` continuous on `[1, a]` and `∫₁^a ψ² ≤ M`,
`|∫₁^a ψ(1 − 1/ξ)| ≤ 2√((M/2)((a − 1)³/6))`. -/
theorem abs_edge_le {a M : ℝ} {ψ : ℝ → ℝ} (ha : 1 ≤ a) (hψc : ContinuousOn ψ (Icc 1 a))
    (hM : ∫ ξ in (1 : ℝ)..a, ψ ξ ^ 2 ≤ M) :
    |∫ ξ in (1 : ℝ)..a, ψ ξ * (1 - 1 / ξ)| ≤ 2 * √(M / 2 * ((a - 1) ^ 3 / 6)) := by
  have hM0 : 0 ≤ M := (intervalIntegral.integral_nonneg ha fun ξ _ => sq_nonneg (ψ ξ)).trans hM
  have ha1 : 0 ≤ a - 1 := by linarith
  have hw : ContinuousOn (fun ξ : ℝ => 1 - 1 / ξ) (Icc 1 a) :=
    continuousOn_const.sub (continuousOn_const.div continuousOn_id fun ξ hξ =>
      (lt_of_lt_of_le one_pos hξ.1).ne')
  have hc1 : ContinuousOn (fun ξ => ψ ξ * (1 - 1 / ξ)) (Icc 1 a) := hψc.mul hw
  refine le_two_sqrt_mul (by positivity) (by positivity) fun t ht => ?_
  have hA : ContinuousOn (fun ξ => t / 2 * ψ ξ ^ 2) (Icc 1 a) := continuousOn_const.mul (hψc.pow 2)
  have hB : ContinuousOn (fun ξ : ℝ => 1 / (2 * t) * (ξ - 1) ^ 2) (Icc 1 a) := by fun_prop
  have hAB : ContinuousOn (fun ξ => t / 2 * ψ ξ ^ 2 + 1 / (2 * t) * (ξ - 1) ^ 2) (Icc 1 a) := hA.add hB
  have hR : IntervalIntegrable (fun ξ => t / 2 * ψ ξ ^ 2 + 1 / (2 * t) * (ξ - 1) ^ 2) volume 1 a :=
    hAB.intervalIntegrable_of_Icc ha
  have hpt : ∀ ξ ∈ Ioo 1 a, |ψ ξ * (1 - 1 / ξ)| ≤ t / 2 * ψ ξ ^ 2 + 1 / (2 * t) * (ξ - 1) ^ 2 := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have hw0 : 0 ≤ 1 - 1 / ξ := by rw [sub_nonneg, div_le_one hξ0]; exact hξ.1.le
    have hw1 : 1 - 1 / ξ ≤ ξ - 1 := by
      rw [show 1 - 1 / ξ = (ξ - 1) / ξ by field_simp]
      exact div_le_self (by linarith [hξ.1]) hξ.1.le
    exact abs_mul_le_amgm ht (sq_nonneg _) (sq_nonneg _) (pow_le_pow_left₀ hw0 hw1 2) (by ring)
  calc |∫ ξ in (1 : ℝ)..a, ψ ξ * (1 - 1 / ξ)|
      ≤ ∫ ξ in (1 : ℝ)..a, |ψ ξ * (1 - 1 / ξ)| := abs_integral_le_integral_abs ha
    _ ≤ ∫ ξ in (1 : ℝ)..a, (t / 2 * ψ ξ ^ 2 + 1 / (2 * t) * (ξ - 1) ^ 2) :=
        integral_mono_on_of_le_Ioo ha (hc1.abs.intervalIntegrable_of_Icc ha) hR hpt
    _ = t / 2 * (∫ ξ in (1 : ℝ)..a, ψ ξ ^ 2) + 1 / (2 * t) * ((a - 1) ^ 3 / 3) := by
        rw [intervalIntegral.integral_add (hA.intervalIntegrable_of_Icc ha) (hB.intervalIntegrable_of_Icc ha),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_sub_one_sq]
    _ ≤ t / 2 * M + 1 / (2 * t) * ((a - 1) ^ 3 / 3) := by gcongr
    _ = t * (M / 2) + (a - 1) ^ 3 / 6 / t := by field_simp; ring

/-! ### The energy envelope for `0 ≤ χ ≤ c² + c/2` -/

section envelope

variable {c χ : ℝ}

/-- **The sign polynomial past the turning point**: for `c > 0`, `0 ≤ χ ≤ c² + c/2`, `Y ≥ 1` and
`c(Y − 1) ≥ 1/3`, `c⁴(2Y³ − 3Y² + 2Y) + c²χ(Y² − 4Y + 1) + χ² ≥ 0`. -/
theorem signPoly_nonneg_turn {Y : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ c ^ 2 + c / 2) (hY : 1 ≤ Y)
    (hcy : 1 / 3 ≤ c * (Y - 1)) :
    0 ≤ c ^ 4 * (2 * Y ^ 3 - 3 * Y ^ 2 + 2 * Y) + c ^ 2 * χ * (Y ^ 2 - 4 * Y + 1) + χ ^ 2 := by
  have e : c ^ 4 * (2 * Y ^ 3 - 3 * Y ^ 2 + 2 * Y) + c ^ 2 * χ * (Y ^ 2 - 4 * Y + 1) + χ ^ 2
      = (c ^ 2 - χ) ^ 2 + 2 * c ^ 2 * (Y - 1) * (c ^ 2 - χ) + c ^ 2 * (Y - 1) ^ 2 * (3 * c ^ 2 + χ)
        + 2 * c ^ 4 * (Y - 1) ^ 3 := by ring
  rw [e]
  have hy : 0 ≤ Y - 1 := by linarith
  have h3 : 0 ≤ 2 * c ^ 4 * (Y - 1) ^ 3 := by positivity
  have h2 : 3 * c ^ 4 * (Y - 1) ^ 2 ≤ c ^ 2 * (Y - 1) ^ 2 * (3 * c ^ 2 + χ) := by
    have : 0 ≤ c ^ 2 * (Y - 1) ^ 2 * χ := by positivity
    nlinarith
  have h1 : -(c ^ 3 * (Y - 1)) ≤ 2 * c ^ 2 * (Y - 1) * (c ^ 2 - χ) := by
    have : -(c / 2) ≤ c ^ 2 - χ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 2 * c ^ 2 * (Y - 1))]
  have h4 : 0 ≤ c ^ 3 * (Y - 1) * (3 * (c * (Y - 1)) - 1) := mul_nonneg (by positivity) (by linarith)
  nlinarith [sq_nonneg (c ^ 2 - χ)]

section posq
variable {ξ : ℝ} (hξ : 1 < ξ) (hq : 0 < qP c χ ξ)
include hξ hq

/-- `a > 0` where `ξ > 1` and `q(ξ) > 0`. -/
theorem aP_pos_q : 0 < aP c χ ξ := sqrt_pos.mpr (mul_pos (pP_pos hξ) hq)

/-- `d > 0` where `ξ > 1` and `q(ξ) > 0`. -/
theorem dP_pos_q : 0 < dP c χ ξ := by
  have hp := pP_pos hξ
  have e : dP c χ ξ = 2 * ξ * (c ^ 2 * pP ξ + qP c χ ξ) := by unfold dP pP qP; ring
  rw [e]
  have : 0 ≤ c ^ 2 * pP ξ := by positivity
  have : 0 < ξ := by linarith
  positivity

/-- `w > 0` where `ξ > 1` and `q(ξ) > 0`. -/
theorem wP_pos_q : 0 < wP c χ ξ := by
  unfold wP
  have := aP_pos_q hξ hq; have := dP_pos_q hξ hq
  positivity

/-- `a² = pq` where `ξ > 1` and `q(ξ) > 0`. -/
theorem aP_sq_q : aP c χ ξ ^ 2 = pP ξ * qP c χ ξ := sq_sqrt (mul_pos (pP_pos hξ) hq).le

/-- `a' = wq` where `ξ > 1` and `q(ξ) > 0`. -/
theorem hasDerivAt_aP_q : HasDerivAt (aP c χ) (wP c χ ξ * qP c χ ξ) ξ := by
  have hf : HasDerivAt (fun s => pP s * qP c χ s) (dP c χ ξ) ξ := by
    have h := ((hasDerivAt_pow 2 ξ).sub_const 1).mul
      (((hasDerivAt_pow 2 ξ).const_mul (c ^ 2)).sub_const χ)
    refine h.congr_deriv ?_
    simp only [dP, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring
  have hs := hf.sqrt (mul_pos (pP_pos hξ) hq).ne'
  refine hs.congr_deriv ?_
  have ha := aP_pos_q hξ hq
  unfold wP
  rw [show √(pP ξ * qP c χ ξ) = aP c χ ξ from rfl]
  field_simp

/-- `w` has derivative `w'` where `ξ > 1` and `q(ξ) > 0`. -/
theorem hasDerivAt_wP_q : HasDerivAt (wP c χ) (wP' c χ ξ) ξ := by
  have hd : HasDerivAt (dP c χ) (2 * (6 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ)) ξ := by
    have h := (((hasDerivAt_pow 3 ξ).const_mul (4 * c ^ 2)).sub
      ((hasDerivAt_id ξ).const_mul (2 * (c ^ 2 + χ))))
    have e : dP c χ = fun s => 4 * c ^ 2 * s ^ 3 - 2 * (c ^ 2 + χ) * id s := by
      funext s; unfold dP; simp; ring
    rw [e]; refine h.congr_deriv ?_; simp; ring
  have hq' : HasDerivAt (qP c χ) (2 * c ^ 2 * ξ) ξ := by
    have h := ((hasDerivAt_pow 2 ξ).const_mul (c ^ 2)).sub_const χ
    have e : qP c χ = fun s => c ^ 2 * s ^ 2 - χ := rfl
    rw [e]; refine h.congr_deriv ?_; ring
  have hden := ((hq'.const_mul 2).fun_mul (hasDerivAt_aP_q hξ hq))
  have hne : 2 * qP c χ ξ * aP c χ ξ ≠ 0 := by
    have := aP_pos_q hξ hq; positivity
  have h := hd.fun_div hden hne
  have e : wP c χ = fun s => dP c χ s / (2 * qP c χ s * aP c χ s) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold wP'
  ring

/-- `w' ≤ 0` where `ξ > 1`, `q(ξ) > 0` and the sign polynomial at `ξ²` is nonnegative. -/
theorem wP'_nonpos_q
    (hSP : 0 ≤ c ^ 4 * (2 * (ξ ^ 2) ^ 3 - 3 * (ξ ^ 2) ^ 2 + 2 * ξ ^ 2) + c ^ 2 * χ * ((ξ ^ 2) ^ 2 - 4 * ξ ^ 2 + 1)
      + χ ^ 2) : wP' c χ ξ ≤ 0 := by
  have ha := aP_pos_q hξ hq
  have ha2 := aP_sq_q hξ hq
  unfold wP' wP
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have key : (2 * (6 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ) * (2 * qP c χ ξ * aP c χ ξ)
      - dP c χ ξ * (2 * (2 * c ^ 2 * ξ * aP c χ ξ
        + qP c χ ξ * (dP c χ ξ / (2 * qP c χ ξ * aP c χ ξ) * qP c χ ξ)))) * aP c χ ξ
      = qP c χ ξ * (-4 * (c ^ 4 * (2 * (ξ ^ 2) ^ 3 - 3 * (ξ ^ 2) ^ 2 + 2 * ξ ^ 2)
        + c ^ 2 * χ * ((ξ ^ 2) ^ 2 - 4 * ξ ^ 2 + 1) + χ ^ 2)) := by
    field_simp
    rw [ha2]
    unfold pP qP dP
    ring
  have hrhs : qP c χ ξ * (-4 * (c ^ 4 * (2 * (ξ ^ 2) ^ 3 - 3 * (ξ ^ 2) ^ 2 + 2 * ξ ^ 2)
        + c ^ 2 * χ * ((ξ ^ 2) ^ 2 - 4 * ξ ^ 2 + 1) + χ ^ 2)) ≤ 0 := by nlinarith
  by_contra hcon
  push Not at hcon
  have := mul_pos hcon ha
  linarith

/-- `w'` is continuous where `ξ > 1` and `q(ξ) > 0`. -/
theorem continuousAt_wP'_q : ContinuousAt (wP' c χ) ξ := by
  have ha := (hasDerivAt_aP_q hξ hq).continuousAt
  have hw := (hasDerivAt_wP_q hξ hq).continuousAt
  have hqc : ContinuousAt (qP c χ) ξ := by unfold qP; fun_prop
  have hd : ContinuousAt (dP c χ) ξ := by unfold dP; fun_prop
  have hne : (2 * qP c χ ξ * aP c χ ξ) ^ 2 ≠ 0 := by
    have := aP_pos_q hξ hq; positivity
  unfold wP'
  refine ContinuousAt.div ?_ ((continuousAt_const.mul hqc).mul ha |>.pow 2) hne
  refine (((continuousAt_const.mul ((continuousAt_const.mul (continuousAt_id.pow 2)).sub
    continuousAt_const |>.sub continuousAt_const)).mul
    ((continuousAt_const.mul hqc).mul ha))).sub ?_
  exact hd.mul (continuousAt_const.mul (((continuousAt_const.mul continuousAt_id).mul ha).add
    (hqc.mul (hw.mul hqc))))

end posq

/-- The sign polynomial at `t²`. -/
noncomputable def sP (c χ t : ℝ) : ℝ :=
  c ^ 4 * (2 * (t ^ 2) ^ 3 - 3 * (t ^ 2) ^ 2 + 2 * t ^ 2) + c ^ 2 * χ * ((t ^ 2) ^ 2 - 4 * t ^ 2 + 1) + χ ^ 2

/-- **The prolate energy bound on a window with `q > 0` and `sP ≥ 0`** (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.prolate_energy_le without
`χ < c²`). -/
theorem prolate_energy_le_q {ψ u : ℝ → ℝ} {ξ₀ ξ₁ : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hq : ∀ t ∈ Icc ξ₀ ξ₁, 0 < qP c χ t) (hSP : ∀ t ∈ Icc ξ₀ ξ₁, 0 ≤ sP c χ t)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    energy (aP c χ) ψ u ξ₁ ≤ energy (aP c χ) ψ u ξ₀ * (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
      * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) := by
  have gt1 : ∀ t ∈ Icc ξ₀ ξ₁, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
  have hw'c : ContinuousOn (wP' c χ) (Icc ξ₀ ξ₁) := fun t ht =>
    (continuousAt_wP'_q (gt1 t ht) (hq t ht)).continuousWithinAt
  have hwc : ContinuousOn (wP c χ) (Icc ξ₀ ξ₁) := fun t ht =>
    (hasDerivAt_wP_q (gt1 t ht) (hq t ht)).continuousAt.continuousWithinAt
  have hanti : AntitoneOn (wP c χ) (Icc ξ₀ ξ₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ξ₀ ξ₁) hwc
    · rw [interior_Icc]; exact fun t ht =>
        (hasDerivAt_wP_q (gt1 t (Ioo_subset_Icc_self ht)) (hq t (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      rw [(hasDerivAt_wP_q (gt1 t (Ioo_subset_Icc_self ht)) (hq t (Ioo_subset_Icc_self ht))).deriv]
      exact wP'_nonpos_q (gt1 t (Ioo_subset_Icc_self ht)) (hq t (Ioo_subset_Icc_self ht))
        (hSP t (Ioo_subset_Icc_self ht))
  have hmem0 : ξ₀ ∈ Icc ξ₀ ξ₁ := left_mem_Icc.mpr hle
  have hmem1 : ξ₁ ∈ Icc ξ₀ ξ₁ := right_mem_Icc.mpr hle
  have hWb : ∀ t ∈ Icc ξ₀ ξ₁, |wP c χ t| ≤ wP c χ ξ₀ := fun t ht => by
    rw [abs_of_pos (wP_pos_q (gt1 t ht) (hq t ht))]; exact hanti hmem0 ht ht.1
  have hE := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyGrowth.energy_le_exp hle (fun t ht => aP_pos_q (gt1 t ht) (hq t ht))
    (fun t ht => (pP_pos (gt1 t ht)).ne') (fun t ht => aP_sq_q (gt1 t ht) (hq t ht)) hψ hu
    (fun t ht => hasDerivAt_aP_q (gt1 t ht) (hq t ht)) (fun t ht => hasDerivAt_wP_q (gt1 t ht) (hq t ht))
    hw'c hWb hW
  have hI : uIcc ξ₀ ξ₁ = Icc ξ₀ ξ₁ := uIcc_of_le hle
  have hint : ∫ t in ξ₀..ξ₁, |wP' c χ t| / (2 - wP c χ ξ₀)
      = (wP c χ ξ₀ - wP c χ ξ₁) / (2 - wP c χ ξ₀) := by
    rw [intervalIntegral.integral_div]
    congr 1
    have hcongr : ∫ t in ξ₀..ξ₁, |wP' c χ t| = ∫ t in ξ₀..ξ₁, -wP' c χ t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [hI] at ht
      exact abs_of_nonpos (wP'_nonpos_q (gt1 t ht) (hq t ht) (hSP t ht))
    rw [hcongr, intervalIntegral.integral_neg,
      integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_wP_q (gt1 t (hI ▸ ht)) (hq t (hI ▸ ht)))
        (hw'c.intervalIntegrable_of_Icc hle)]
    ring
  rw [hint, abs_of_pos (wP_pos_q h1 (hq ξ₀ hmem0))] at hE
  have hW0 := wP_pos_q h1 (hq ξ₀ hmem0)
  have hW1 := (wP_pos_q (gt1 ξ₁ hmem1) (hq ξ₁ hmem1)).le
  have hd : 0 < 2 - wP c χ ξ₀ := by linarith
  have hexp : exp ((wP c χ ξ₀ - wP c χ ξ₁) / (2 - wP c χ ξ₀))
      ≤ exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) :=
    exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hd.le)
  have hG0 : 0 ≤ energy (aP c χ) ψ u ξ₀ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos_q h1 (hq ξ₀ hmem0)))
  have hpre : 0 ≤ energy (aP c χ) ψ u ξ₀ * (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2) := by
    apply div_nonneg (mul_nonneg hG0 (by linarith)); linarith
  exact hE.trans (mul_le_mul_of_nonneg_left hexp hpre)

/-- **The prolate energy bounded below on a window with `q > 0` and `sP ≥ 0`** (Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower without `χ < c²`). -/
theorem prolate_energy_ge_q {ψ u : ℝ → ℝ} {ξ₀ ξ₁ : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hq : ∀ t ∈ Icc ξ₀ ξ₁, 0 < qP c χ t) (hSP : ∀ t ∈ Icc ξ₀ ξ₁, 0 ≤ sP c χ t)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    energy (aP c χ) ψ u ξ₀ * (1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2)
      * exp (-(wP c χ ξ₀ / (2 - wP c χ ξ₀))) ≤ energy (aP c χ) ψ u ξ₁ := by
  have gt1 : ∀ t ∈ Icc ξ₀ ξ₁, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
  have hw'c : ContinuousOn (wP' c χ) (Icc ξ₀ ξ₁) := fun t ht =>
    (continuousAt_wP'_q (gt1 t ht) (hq t ht)).continuousWithinAt
  have hwc : ContinuousOn (wP c χ) (Icc ξ₀ ξ₁) := fun t ht =>
    (hasDerivAt_wP_q (gt1 t ht) (hq t ht)).continuousAt.continuousWithinAt
  have hanti : AntitoneOn (wP c χ) (Icc ξ₀ ξ₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ξ₀ ξ₁) hwc
    · rw [interior_Icc]; exact fun t ht =>
        (hasDerivAt_wP_q (gt1 t (Ioo_subset_Icc_self ht)) (hq t (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      rw [(hasDerivAt_wP_q (gt1 t (Ioo_subset_Icc_self ht)) (hq t (Ioo_subset_Icc_self ht))).deriv]
      exact wP'_nonpos_q (gt1 t (Ioo_subset_Icc_self ht)) (hq t (Ioo_subset_Icc_self ht))
        (hSP t (Ioo_subset_Icc_self ht))
  have hmem0 : ξ₀ ∈ Icc ξ₀ ξ₁ := left_mem_Icc.mpr hle
  have hmem1 : ξ₁ ∈ Icc ξ₀ ξ₁ := right_mem_Icc.mpr hle
  have hWb : ∀ t ∈ Icc ξ₀ ξ₁, |wP c χ t| ≤ wP c χ ξ₀ := fun t ht => by
    rw [abs_of_pos (wP_pos_q (gt1 t ht) (hq t ht))]; exact hanti hmem0 ht ht.1
  have hE := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower.energy_le_exp_rev hle (fun t ht => aP_pos_q (gt1 t ht) (hq t ht))
    (fun t ht => (pP_pos (gt1 t ht)).ne') (fun t ht => aP_sq_q (gt1 t ht) (hq t ht)) hψ hu
    (fun t ht => hasDerivAt_aP_q (gt1 t ht) (hq t ht)) (fun t ht => hasDerivAt_wP_q (gt1 t ht) (hq t ht))
    hw'c hWb hW
  have hI : uIcc ξ₀ ξ₁ = Icc ξ₀ ξ₁ := uIcc_of_le hle
  have hint : ∫ t in ξ₀..ξ₁, |wP' c χ t| / (2 - wP c χ ξ₀)
      = (wP c χ ξ₀ - wP c χ ξ₁) / (2 - wP c χ ξ₀) := by
    rw [intervalIntegral.integral_div]
    congr 1
    have hcongr : ∫ t in ξ₀..ξ₁, |wP' c χ t| = ∫ t in ξ₀..ξ₁, -wP' c χ t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [hI] at ht
      exact abs_of_nonpos (wP'_nonpos_q (gt1 t ht) (hq t ht) (hSP t ht))
    rw [hcongr, intervalIntegral.integral_neg,
      integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_wP_q (gt1 t (hI ▸ ht)) (hq t (hI ▸ ht)))
        (hw'c.intervalIntegrable_of_Icc hle)]
    ring
  rw [hint] at hE
  have hW0 := wP_pos_q h1 (hq ξ₀ hmem0)
  have hW1 := wP_pos_q (gt1 ξ₁ hmem1) (hq ξ₁ hmem1)
  have hw1le : wP c χ ξ₁ ≤ wP c χ ξ₀ := hanti hmem0 hmem1 hle
  rw [abs_of_pos hW1] at hE
  have hd : 0 < 2 - wP c χ ξ₀ := by linarith
  have hd1 : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
  have hG1 : 0 ≤ energy (aP c χ) ψ u ξ₁ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos_q (gt1 ξ₁ hmem1) (hq ξ₁ hmem1)))
  have hexp : exp ((wP c χ ξ₀ - wP c χ ξ₁) / (2 - wP c χ ξ₀))
      ≤ exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) :=
    exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hd.le)
  have hfac : (1 + wP c χ ξ₁ / 2) ≤ (1 + wP c χ ξ₀ / 2) := by linarith
  have hG0 : energy (aP c χ) ψ u ξ₀ ≤ energy (aP c χ) ψ u ξ₁ * (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
      * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) := by
    refine hE.trans ?_
    apply mul_le_mul _ hexp (exp_pos _).le
    · apply div_nonneg (mul_nonneg hG1 (by linarith)) hd1.le
    · apply div_le_div_of_nonneg_right _ hd1.le
      exact mul_le_mul_of_nonneg_left hfac hG1
  have hA : 0 < (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2) * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) := by
    apply mul_pos (div_pos (by linarith) hd1) (exp_pos _)
  have : energy (aP c χ) ψ u ξ₀ * (1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2)
      * exp (-(wP c χ ξ₀ / (2 - wP c χ ξ₀)))
      = energy (aP c χ) ψ u ξ₀ / ((1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
        * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀))) := by
    rw [exp_neg]; field_simp
  rw [this, div_le_iff₀ hA]
  calc energy (aP c χ) ψ u ξ₀ ≤ _ := hG0
    _ = energy (aP c χ) ψ u ξ₁ * ((1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
        * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀))) := by ring

/-- **The two-sided energy window with `q > 0` and `sP ≥ 0`** (Cvs.Prolate.ProlateWindowMassIdentity.energy_window without `χ < c²`). -/
theorem energy_window_q {ψ u : ℝ → ℝ} {ξ₀ ξ₁ W : ℝ} (h1 : 1 < ξ₀)
    (hq : ∀ t ∈ Icc ξ₀ ξ₁, 0 < qP c χ t) (hSP : ∀ t ∈ Icc ξ₀ ξ₁, 0 ≤ sP c χ t)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ ≤ W) (hW1 : W < 1) :
    ∀ t ∈ Icc ξ₀ ξ₁, energy (aP c χ) ψ u ξ₀ * ((1 - W) / (1 + W / 2)) ≤ energy (aP c χ) ψ u t
      ∧ energy (aP c χ) ψ u t ≤ energy (aP c χ) ψ u ξ₀ * ((1 + W / 2) / (1 - W)) := by
  intro t ht
  have hle : ξ₀ ≤ ξ₁ := ht.1.trans ht.2
  set w := wP c χ ξ₀ with hw
  have hw0 : 0 < w := wP_pos_q h1 (hq ξ₀ ⟨le_rfl, hle⟩)
  have hw2 : w < 2 := by linarith
  set G₀ := energy (aP c χ) ψ u ξ₀
  have hG0 : 0 ≤ G₀ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos_q h1 (hq ξ₀ ⟨le_rfl, hle⟩)))
  have sub : ∀ s ∈ Icc ξ₀ t, s ∈ Icc ξ₀ ξ₁ := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hx0 : 0 ≤ w / (2 - w) := div_nonneg hw0.le (by linarith)
  have hx1 : w / (2 - w) < 1 := by rw [div_lt_one (by linarith)]; linarith
  constructor
  · have hge := prolate_energy_ge_q h1 ht.1 (fun s hs => hq s (sub s hs)) (fun s hs => hSP s (sub s hs))
      (fun s hs => hψ s (sub s hs)) (fun s hs => hu s (sub s hs)) hw2
    have hexp : 1 - w / (2 - w) ≤ exp (-(w / (2 - w))) := by linarith [add_one_le_exp (-(w / (2 - w)))]
    have hfac : (1 - W) / (1 + W / 2) ≤ (1 - w / 2) / (1 + w / 2) * (1 - w / (2 - w)) := by
      have e : (1 - w / 2) / (1 + w / 2) * (1 - w / (2 - w)) = (1 - w) / (1 + w / 2) := by
        have : (2 : ℝ) - w ≠ 0 := by linarith
        have : (1 : ℝ) - w / (2 - w) = (2 - 2 * w) / (2 - w) := by field_simp; ring
        rw [this]; field_simp
      rw [e, div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    calc G₀ * ((1 - W) / (1 + W / 2)) ≤ G₀ * ((1 - w / 2) / (1 + w / 2) * (1 - w / (2 - w))) :=
          mul_le_mul_of_nonneg_left hfac hG0
      _ ≤ G₀ * ((1 - w / 2) / (1 + w / 2) * exp (-(w / (2 - w)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp
            (div_nonneg (by linarith) (by linarith))) hG0
      _ = G₀ * (1 - w / 2) / (1 + w / 2) * exp (-(w / (2 - w))) := by ring
      _ ≤ _ := hge
  · have hle' := prolate_energy_le_q h1 ht.1 (fun s hs => hq s (sub s hs)) (fun s hs => hSP s (sub s hs))
      (fun s hs => hψ s (sub s hs)) (fun s hs => hu s (sub s hs)) hw2
    have hexp : exp (w / (2 - w)) ≤ 1 / (1 - w / (2 - w)) := exp_bound_div_one_sub_of_interval hx0 hx1
    have hfac : (1 + w / 2) / (1 - w / 2) * (1 / (1 - w / (2 - w))) ≤ (1 + W / 2) / (1 - W) := by
      have e : (1 + w / 2) / (1 - w / 2) * (1 / (1 - w / (2 - w))) = (1 + w / 2) / (1 - w) := by
        have : (1 : ℝ) - w ≠ 0 := by linarith
        have : (2 : ℝ) - w ≠ 0 := by linarith
        have : (1 : ℝ) - w / (2 - w) = (2 - 2 * w) / (2 - w) := by field_simp; ring
        rw [this]; field_simp
      rw [e, div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    calc energy (aP c χ) ψ u t ≤ G₀ * (1 + w / 2) / (1 - w / 2) * exp (w / (2 - w)) := hle'
      _ = G₀ * ((1 + w / 2) / (1 - w / 2) * exp (w / (2 - w))) := by ring
      _ ≤ G₀ * ((1 + w / 2) / (1 - w / 2) * (1 / (1 - w / (2 - w)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp
            (div_nonneg (by linarith) (by linarith))) hG0
      _ ≤ G₀ * ((1 + W / 2) / (1 - W)) := mul_le_mul_of_nonneg_left hfac hG0

/-- `1/(cξ√(ξ²−1)) ≤ 1/a` for `ξ > 1`, `c > 0`, `χ ≥ 0`, `q(ξ) > 0`. -/
theorem inv_a_ge_q {ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hχ : 0 ≤ χ) (hq : 0 < qP c χ ξ) :
    1 / (c * (ξ * √(ξ ^ 2 - 1))) ≤ 1 / aP c χ ξ := by
  have ha := aP_pos_q hξ hq
  have hB : 0 < ξ ^ 2 - 1 := by nlinarith
  apply one_div_le_one_div_of_le ha
  unfold aP pP qP
  rw [sqrt_mul hB.le]
  have hq' : √(c ^ 2 * ξ ^ 2 - χ) ≤ c * ξ := by
    rw [sqrt_le_left (by positivity)]; nlinarith
  have := sqrt_nonneg (ξ ^ 2 - 1)
  nlinarith

/-- **The arcsin law from below with `q > 0`**: `ProlateArcsinMassLaw`'s lower bound without `χ < c²`. -/
theorem prolate_mass_lower_q {ψ u : ℝ → ℝ} {ξ₀ ξ₁ Gm GM : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hq : ∀ t ∈ Icc ξ₀ ξ₁, 0 < qP c χ t)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hGm : ∀ t ∈ Icc ξ₀ ξ₁, Gm ≤ energy (aP c χ) ψ u t)
    (hGM : ∀ t ∈ Icc ξ₀ ξ₁, energy (aP c χ) ψ u t ≤ GM) (hGm0 : 0 ≤ Gm) :
    Gm * (arccos (1 / ξ₁) - arccos (1 / ξ₀)) / (2 * c) - GM / (2 * qP c χ ξ₀)
        ≤ ∫ t in ξ₀..ξ₁, ψ t ^ 2 := by
  have gt1 : ∀ t ∈ Icc ξ₀ ξ₁, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
  have hI : uIcc ξ₀ ξ₁ = Icc ξ₀ ξ₁ := uIcc_of_le hle
  have hmem0 : ξ₀ ∈ Icc ξ₀ ξ₁ := left_mem_Icc.mpr hle
  have hmem1 : ξ₁ ∈ Icc ξ₀ ξ₁ := right_mem_Icc.mpr hle
  have ha : ∀ t ∈ Icc ξ₀ ξ₁, 0 < aP c χ t := fun t ht => aP_pos_q (gt1 t ht) (hq t ht)
  have hqd : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt (qP c χ) (2 * c ^ 2 * t) t := fun t _ => by
    have h := ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).sub_const χ
    exact h.congr_deriv (by ring)
  have cont : ∀ f : ℝ → ℝ, (∀ t ∈ Icc ξ₀ ξ₁, DifferentiableAt ℝ f t) → ContinuousOn f (Icc ξ₀ ξ₁) :=
    fun f hf t ht => (hf t ht).continuousAt.continuousWithinAt
  have hac : ContinuousOn (aP c χ) (Icc ξ₀ ξ₁) :=
    cont _ fun t ht => (hasDerivAt_aP_q (gt1 t ht) (hq t ht)).differentiableAt
  have hpc : ContinuousOn pP (Icc ξ₀ ξ₁) := by unfold pP; fun_prop
  have hqc : ContinuousOn (qP c χ) (Icc ξ₀ ξ₁) := by unfold qP; fun_prop
  have hψc := cont ψ fun t ht => (hψ t ht).differentiableAt
  have huc := cont u fun t ht => (hu t ht).differentiableAt
  have hid := Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy.integral_sq_eq (q' := fun t => 2 * c ^ 2 * t) hle ha
    (fun t ht => (pP_pos (gt1 t ht)).ne') (fun t ht => (hq t ht).ne')
    (fun t ht => aP_sq_q (gt1 t ht) (hq t ht)) hψ hu hqd (by fun_prop) hac hpc
  set Δ := arccos (1 / ξ₁) - arccos (1 / ξ₀)
  have hsec : ContinuousOn (fun t => 1 / (t * √(t ^ 2 - 1))) (Icc ξ₀ ξ₁) := by
    refine continuousOn_const.div₀ (by fun_prop) fun t ht => ?_
    have := gt1 t ht; have : 0 < t ^ 2 - 1 := by nlinarith
    positivity
  have hΔ : ∫ t in ξ₀..ξ₁, 1 / (t * √(t ^ 2 - 1)) = Δ :=
    integral_eq_sub_of_hasDerivAt (fun t ht => Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.hasDerivAt_arcsec (gt1 t (hI ▸ ht)))
      (hsec.intervalIntegrable_of_Icc hle)
  have hqq : ∫ t in ξ₀..ξ₁, 2 * c ^ 2 * t / qP c χ t ^ 2 = 1 / qP c χ ξ₀ - 1 / qP c χ ξ₁ := by
    have hd : ∀ t ∈ uIcc ξ₀ ξ₁, HasDerivAt (fun s => -(1 / qP c χ s))
        (2 * c ^ 2 * t / qP c χ t ^ 2) t := fun t ht => by
      have := ((hqd t (hI ▸ ht)).inv (hq t (hI ▸ ht)).ne').neg
      refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards with s; simp [one_div]
    rw [integral_eq_sub_of_hasDerivAt hd]
    · ring
    · exact ContinuousOn.intervalIntegrable_of_Icc hle
        ((continuousOn_const.mul continuousOn_id).div₀ (hqc.pow 2)
          fun t ht => pow_ne_zero 2 (hq t ht).ne')
  have hint1 : ContinuousOn (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)) (Icc ξ₀ ξ₁) := by
    unfold energy
    refine ContinuousOn.sub ?_ ?_
    · exact ((hac.mul (hψc.pow 2)).add ((huc.pow 2).div hac fun t ht => (ha t ht).ne')).div
        (continuousOn_const.mul hac) fun t ht => mul_ne_zero two_ne_zero (ha t ht).ne'
    · have hlin : ContinuousOn (fun t : ℝ => 2 * c ^ 2 * t) (Icc ξ₀ ξ₁) :=
        continuousOn_const.mul continuousOn_id
      exact ((hψc.mul huc).mul hlin).div₀ (continuousOn_const.mul (hqc.pow 2))
        fun t ht => mul_ne_zero two_ne_zero (pow_ne_zero 2 (hq t ht).ne')
  have hqq' : ContinuousOn (fun t => 2 * c ^ 2 * t / qP c χ t ^ 2) (Icc ξ₀ ξ₁) :=
    (continuousOn_const.mul continuousOn_id).div₀ (hqc.pow 2) fun t ht => pow_ne_zero 2 (hq t ht).ne'
  have hcross : ∀ t ∈ Icc ξ₀ ξ₁, |ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)|
      ≤ GM / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2) := fun t ht => by
    have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht)
    have hqt := hq t ht
    have ht0 : 0 ≤ 2 * c ^ 2 * t := by have := gt1 t ht; positivity
    rw [abs_div, abs_mul, abs_of_nonneg ht0, abs_of_pos (by positivity : 0 < 2 * qP c χ t ^ 2)]
    rw [div_le_iff₀ (by positivity)]
    have : |ψ t * u t| ≤ GM / 2 := by linarith [hGM t ht]
    have e : GM / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2) * (2 * qP c χ t ^ 2) = GM / 2 * (2 * c ^ 2 * t) := by
      field_simp; ring
    rw [e]; exact mul_le_mul_of_nonneg_right this ht0
  have hmainL : ∀ t ∈ Icc ξ₀ ξ₁, Gm / (2 * c) * (1 / (t * √(t ^ 2 - 1)))
      - GM / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2)
      ≤ energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2) := by
    intro t ht
    have hat := ha t ht
    have hge' := inv_a_ge_q (gt1 t ht) hc hχ (hq t ht)
    have h1' : Gm / 2 * (1 / aP c χ t) ≤ energy (aP c χ) ψ u t / (2 * aP c χ t) := by
      have e : energy (aP c χ) ψ u t / (2 * aP c χ t) = energy (aP c χ) ψ u t / 2 * (1 / aP c χ t) := by
        field_simp
      rw [e]; exact mul_le_mul_of_nonneg_right (by linarith [hGm t ht]) (by positivity)
    have h2' : Gm / (2 * c) * (1 / (t * √(t ^ 2 - 1))) ≤ Gm / 2 * (1 / aP c χ t) := by
      calc Gm / (2 * c) * (1 / (t * √(t ^ 2 - 1)))
          = Gm / 2 * (1 / (c * (t * √(t ^ 2 - 1)))) := by field_simp
        _ ≤ Gm / 2 * (1 / aP c χ t) := mul_le_mul_of_nonneg_left hge' (by positivity)
    have := le_abs_self (ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2))
    linarith [hcross t ht]
  have iS : IntervalIntegrable (fun t => 1 / (t * √(t ^ 2 - 1))) MeasureTheory.volume ξ₀ ξ₁ :=
    hsec.intervalIntegrable_of_Icc hle
  have iQ : IntervalIntegrable (fun t => 2 * c ^ 2 * t / qP c χ t ^ 2) MeasureTheory.volume ξ₀ ξ₁ :=
    hqq'.intervalIntegrable_of_Icc hle
  have iH : IntervalIntegrable (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)) MeasureTheory.volume ξ₀ ξ₁ :=
    hint1.intervalIntegrable_of_Icc hle
  have iL := integral_mono_on hle ((iS.const_mul (Gm / (2 * c))).sub (iQ.const_mul (GM / 4))) iH hmainL
  rw [intervalIntegral.integral_sub (iS.const_mul _) (iQ.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hΔ, hqq] at iL
  have e0 : |ψ ξ₀ * u ξ₀ / qP c χ ξ₀ / 2| ≤ GM / (4 * qP c χ ξ₀) := by
    have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha ξ₀ hmem0)
    have hq0 := hq ξ₀ hmem0
    rw [abs_div, abs_div, abs_of_pos hq0, abs_two, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hGM ξ₀ hmem0]
  have e1 : |ψ ξ₁ * u ξ₁ / qP c χ ξ₁ / 2| ≤ GM / (4 * qP c χ ξ₁) := by
    have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha ξ₁ hmem1)
    have hq1 := hq ξ₁ hmem1
    rw [abs_div, abs_div, abs_of_pos hq1, abs_two, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hGM ξ₁ hmem1]
  have hq0 := hq ξ₀ hmem0
  have hq1 := hq ξ₁ hmem1
  have hGM0 : 0 ≤ GM := le_trans hGm0 (le_trans (hGm ξ₀ hmem0) (hGM ξ₀ hmem0))
  have hsum : GM / 4 * (1 / qP c χ ξ₀ - 1 / qP c χ ξ₁) + GM / (4 * qP c χ ξ₁) + GM / (4 * qP c χ ξ₀)
      = GM / (2 * qP c χ ξ₀) := by field_simp; ring
  have a0' := neg_abs_le (ψ ξ₀ * u ξ₀ / qP c χ ξ₀ / 2)
  have a1 := le_abs_self (ψ ξ₁ * u ξ₁ / qP c χ ξ₁ / 2)
  rw [hid]
  have : Gm * Δ / (2 * c) = Gm / (2 * c) * Δ := by ring
  rw [this]
  nlinarith [iL, e0, e1, hsum]

/-- `w ≤ (21/10)ξ/(cp)` wherever `(23/24)c²p ≤ q` (`ξ > 1`, `c > 0`). -/
theorem wP_le_turn {ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hell : 23 / 24 * (c ^ 2 * pP ξ) ≤ qP c χ ξ) :
    wP c χ ξ ≤ 21 / 10 * ξ / (c * pP ξ) := by
  have hp : 0 < pP ξ := pP_pos hξ
  have hq : 0 < qP c χ ξ := lt_of_lt_of_le (by positivity) hell
  have ha := aP_pos_q hξ hq
  have ha2 := aP_sq_q hξ hq
  have hξ0 : 0 < ξ := by linarith
  -- `a ≥ (39/40)cp`
  have hacp : 39 / 40 * (c * pP ξ) ≤ aP c χ ξ := by
    have h2 : (39 / 40 * (c * pP ξ)) ^ 2 ≤ aP c χ ξ ^ 2 := by
      rw [ha2]
      have : pP ξ * (23 / 24 * (c ^ 2 * pP ξ)) ≤ pP ξ * qP c χ ξ := mul_le_mul_of_nonneg_left hell hp.le
      nlinarith [sq_nonneg (c * pP ξ)]
    exact (pow_le_pow_iff_left₀ (by positivity) ha.le two_ne_zero).mp h2
  have edP : dP c χ ξ = 2 * ξ * (c ^ 2 * pP ξ + qP c χ ξ) := by unfold dP pP qP; ring
  unfold wP
  rw [edP, div_le_div_iff₀ (by positivity) (by positivity)]
  -- `2ξ(c²p + q)·cp ≤ (94/23)ξ q cp ≤ (21/5)(39/40) ξ q cp ≤ (21/10)ξ·(2 q a)`
  have h1 : c ^ 2 * pP ξ ≤ 24 / 23 * qP c χ ξ := by linarith
  have hqcp : 0 ≤ ξ * qP c χ ξ * (c * pP ξ) := by positivity
  have hA : 2 * ξ * (c ^ 2 * pP ξ + qP c χ ξ) * (c * pP ξ) ≤ 94 / 23 * (ξ * qP c χ ξ * (c * pP ξ)) := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * ξ * (c * pP ξ))
    nlinarith
  have hB : 21 / 5 * (39 / 40) * (ξ * qP c χ ξ * (c * pP ξ)) ≤ 21 / 10 * ξ * (2 * qP c χ ξ * aP c χ ξ) := by
    have := mul_le_mul_of_nonneg_left hacp (by positivity : (0:ℝ) ≤ 21 / 5 * ξ * qP c χ ξ)
    nlinarith
  nlinarith

/-- **The far energy for `0 ≤ χ ≤ c² + c/2`**: for `c ≥ 80`, `X ≥ 2`, `E ≤ (25/4)c∫₁^Xψ²` on `[6/5, X]`
(Cvs.Prolate.ProlateWindowMassIdentity.far_energy_le without `χ < c²`, window `w(6/5) ≤ 3/40`, `q(6/5) ≥ (347/800)c²`). -/
theorem far_energy_le_turn {X : ℝ} {ψ u : ℝ → ℝ} (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ c ^ 2 + c / 2)
    (hX : 2 ≤ X) (hψ : ∀ t ∈ Icc (6 / 5 : ℝ) X, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc (6 / 5 : ℝ) X, HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hcont : ContinuousOn ψ (Icc 1 X)) :
    ∀ ξ ∈ Icc (6 / 5 : ℝ) X, energy (aP c χ) ψ u ξ ≤ 25 / 4 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2 := by
  intro ξ hξ
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have h1 : (1 : ℝ) < 6 / 5 := by norm_num
  have h65 : 1 + 6 / c ≤ 6 / 5 := by
    have : 6 / c ≤ 1 / 5 := by rw [div_le_div_iff₀ hc0 (by norm_num)]; linarith
    linarith
  have hell : ∀ t, 6 / 5 ≤ t → 23 / 24 * (c ^ 2 * pP t) ≤ qP c χ t := fun t ht =>
    ell_of_le hc0 hχ1 (h65.trans ht)
  have hq : ∀ t ∈ Icc (6 / 5 : ℝ) X, 0 < qP c χ t := fun t ht =>
    lt_of_lt_of_le (by have := pP_pos (show 1 < t by linarith [ht.1]); positivity) (hell t ht.1)
  have hSP : ∀ t ∈ Icc (6 / 5 : ℝ) X, 0 ≤ sP c χ t := fun t ht => by
    have ht1 : 6 / 5 ≤ t := ht.1
    have hY : 1 ≤ t ^ 2 := by nlinarith
    have hcy : 1 / 3 ≤ c * (t ^ 2 - 1) := by nlinarith
    exact signPoly_nonneg_turn hc0 hχ0 hχ1 hY hcy
  have hW : wP c χ (6 / 5) ≤ 3 / 40 := by
    refine (wP_le_turn h1 hc0 (hell (6 / 5) le_rfl)).trans ?_
    unfold pP
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hwin := energy_window_q h1 hq hSP hψ hu hW (by norm_num)
  have sub : ∀ t ∈ Icc (6 / 5 : ℝ) 2, t ∈ Icc (6 / 5 : ℝ) X := fun t ht => ⟨ht.1, ht.2.trans hX⟩
  set G₀ := energy (aP c χ) ψ u (6 / 5)
  have hG0 : 0 ≤ G₀ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos_q h1 (hq (6 / 5) ⟨le_rfl, by linarith⟩)))
  have hmass := prolate_mass_lower_q h1 (by norm_num) hc0 hχ0 (fun t ht => hq t (sub t ht))
    (fun t ht => hψ t (sub t ht)) (fun t ht => hu t (sub t ht))
    (fun t ht => (hwin t (sub t ht)).1) (fun t ht => (hwin t (sub t ht)).2)
    (mul_nonneg hG0 (by norm_num))
  have hΔ : (447 / 1000 : ℝ) ≤ arccos (1 / 2) - arccos (1 / (6 / 5)) := by
    have := Cvs.Prolate.ProlateWindowMassIdentity.arccos_far_ge; norm_num at this ⊢; linarith
  have hq65 : 347 / 800 * c ^ 2 ≤ qP c χ (6 / 5) := by unfold qP; nlinarith
  have hEξ := (hwin ξ hξ).2
  have hsub : ∫ t in (6 / 5 : ℝ)..2, ψ t ^ 2 ≤ ∫ t in (1 : ℝ)..X, ψ t ^ 2 :=
    intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) hX
      (Filter.Eventually.of_forall fun t => sq_nonneg (ψ t))
      ((hcont.pow 2).intervalIntegrable_of_Icc (by linarith))
  norm_num at hEξ hmass hΔ
  set Δ := arccos (1 / 2) - arccos (5 / 6)
  have hA : G₀ * (74 / 83) * (447 / 1000) / (2 * c) ≤ G₀ * (74 / 83) * Δ / (2 * c) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ (by positivity)) (by positivity)
  have hB : G₀ * (83 / 74) / (2 * qP c χ (6 / 5)) ≤ G₀ * (83 / 74) / (347 / 400 * c * 80) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have hK : 0 ≤ G₀ / c := div_nonneg hG0 hc0.le
  have e2 : G₀ * (74 / 83) * (447 / 1000) / (2 * c) = G₀ / c * (74 * 447 / (83 * 2000)) := by ring
  have e3 : G₀ * (83 / 74) / (347 / 400 * c * 80) = G₀ / c * (83 * 400 / (74 * 347 * 80)) := by
    field_simp
  rw [e2] at hA; rw [e3] at hB
  have hlow : G₀ / c * (74 * 447 / (83 * 2000) - 83 * 400 / (74 * 347 * 80)) ≤ ∫ t in (1 : ℝ)..X, ψ t ^ 2 := by
    have e4 : G₀ * (74 / 83) * Δ / (2 * c) = G₀ * 74 / 83 * Δ / (2 * c) := by ring
    have e5 : G₀ * (83 / 74) / (2 * qP c χ (6 / 5)) = G₀ * 83 / 74 / (2 * qP c χ (6 / 5)) := by ring
    nlinarith
  have hnum := mul_le_mul_of_nonneg_left
    (show (83 / 74 : ℝ) ≤ 25 / 4 * (74 * 447 / (83 * 2000) - 83 * 400 / (74 * 347 * 80)) by norm_num) hG0
  have hcK : c * (G₀ / c) = G₀ := mul_div_cancel₀ G₀ hc0.ne'
  calc energy (aP c χ) ψ u ξ ≤ G₀ * (83 / 74) := by linarith
    _ ≤ G₀ * (25 / 4 * (74 * 447 / (83 * 2000) - 83 * 400 / (74 * 347 * 80))) := by linarith
    _ = 25 / 4 * (c * (G₀ / c)) * (74 * 447 / (83 * 2000) - 83 * 400 / (74 * 347 * 80)) := by rw [hcK]; ring
    _ = 25 / 4 * c * (G₀ / c * (74 * 447 / (83 * 2000) - 83 * 400 / (74 * 347 * 80))) := by ring
    _ ≤ 25 / 4 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2 := mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **The envelope at the cut for `0 ≤ χ ≤ c² + c/2`**: `E(1 + 6/c) ≤ 9c∫₁^Xψ²` for `c ≥ 80`, `X ≥ 2`. -/
theorem energy_envelope_turn {X : ℝ} {ψ u : ℝ → ℝ} (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ c ^ 2 + c / 2)
    (hX : 2 ≤ X) (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hψc : ContinuousOn ψ (Icc 1 X)) :
    energy (aP c χ) ψ u (1 + 6 / c) ≤ 9 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2 := by
  have hc0 : 0 < c := by linarith
  have h60 : 0 < 6 / c := by positivity
  have h65 : 1 + 6 / c ≤ 6 / 5 := by
    have : 6 / c ≤ 1 / 5 := by rw [div_le_div_iff₀ hc0 (by norm_num)]; linarith
    linarith
  set ξ₀ := 1 + 6 / c with hξ₀
  have h1 : 1 < ξ₀ := by linarith
  have hfar := far_energy_le_turn hc hχ0 hχ1 hX (fun t ht => hψ t (by linarith [ht.1])) (fun t _ => hu t) hψc
  set M := ∫ t in (1 : ℝ)..X, ψ t ^ 2 with hMdef
  have hell : ∀ t, ξ₀ ≤ t → 23 / 24 * (c ^ 2 * pP t) ≤ qP c χ t := fun t ht => ell_of_le hc0 hχ1 ht
  have hq : ∀ t ∈ Icc ξ₀ (6 / 5), 0 < qP c χ t := fun t ht =>
    lt_of_lt_of_le (by have := pP_pos (show 1 < t by linarith [ht.1]); positivity) (hell t ht.1)
  have hSP : ∀ t ∈ Icc ξ₀ (6 / 5), 0 ≤ sP c χ t := fun t ht => by
    have ht1 : ξ₀ ≤ t := ht.1
    have hY : 1 ≤ t ^ 2 := by nlinarith
    have h12 := twelve_le_c_pP hc0 ht1
    have hcy : 1 / 3 ≤ c * (t ^ 2 - 1) := by unfold pP at h12; linarith
    exact signPoly_nonneg_turn hc0 hχ0 hχ1 hY hcy
  have hW : wP c χ ξ₀ ≤ 1 / 5 := by
    refine (wP_le_turn h1 hc0 (hell ξ₀ le_rfl)).trans ?_
    have h11 := eleven_mul_le_c_pP hc (le_refl ξ₀)
    have hp := pP_pos h1
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hwin := energy_window_q h1 hq hSP (fun t ht => hψ t (by linarith [ht.1])) (fun t _ => hu t) hW
    (by norm_num) (6 / 5) ⟨h65, le_rfl⟩
  have h65E := hfar (6 / 5) ⟨le_rfl, by linarith⟩
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _
  have hcM : 0 ≤ c * M := mul_nonneg hc0.le hM
  have hlow := hwin.1
  norm_num at hlow
  linarith

end envelope

end Cvs.Prolate.Envelope.TurningPointEnergyEnvelope
