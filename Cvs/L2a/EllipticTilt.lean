import Mathlib
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungTiltedPole
import Cvs.Prolate.Envelope.TurningPointEnergyEnvelope
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungEdgeCorrectedEnergy

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tilt with ellipticity `θ`

Given `θc²p ≤ q` and the cube inequality on `[1 + 6/c, ∞)`, `E ≤ (25/4)cM` on `[6/5, X]` and
`E(1 + 6/c) ≤ 9cM` with `M = ∫₁^X ψ²`: `|∫_{(1,∞)} posTail ψ X θ (1 − 1/θ)| ≤ tiltK θ c · √M/c`.
Only `0 ≤ χ` enters, not `χ < c²`; `tiltK (23/24) c ≤ 9` for `c ≥ 80` and `≤ 7` for `c ≥ 10⁴`.
-/

namespace Cvs.L2a.EllipticTilt

open Real Set MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungTiltedPole Cvs.Prolate.Envelope.TurningPointEnergyEnvelope

/-! ### The tilt with ellipticity `θ` -/

/-- `|u(ξ)| ≤ cξ(5/2)√M` from `E(ξ) ≤ (25/4)cM`, for `0 ≤ χ`, `ξ > 1` and `q(ξ) > 0` (no `χ < c²`). -/
theorem abs_u_le_of_energy' {c χ ξ M : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hξ : 1 < ξ)
    (hq : 0 < qP c χ ξ) (hM : 0 ≤ M) (hE : energy (aP c χ) ψ u ξ ≤ 25 / 4 * c * M) :
    |u ξ| ≤ c * ξ * (5 / 2 * √M) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp := pP_pos hξ
  have ha : 0 < aP c χ ξ := sqrt_pos.mpr (mul_pos hp hq)
  have haξ : aP c χ ξ ≤ c * ξ ^ 2 := by
    unfold aP
    rw [sqrt_le_left (by positivity)]
    have hp' : pP ξ ≤ ξ ^ 2 := by unfold pP; linarith
    have hq' : qP c χ ξ ≤ c ^ 2 * ξ ^ 2 := by unfold qP; linarith
    calc pP ξ * qP c χ ξ ≤ ξ ^ 2 * (c ^ 2 * ξ ^ 2) := mul_le_mul hp' hq' hq.le (sq_nonneg _)
      _ = (c * ξ ^ 2) ^ 2 := by ring
  have h1 : u ξ ^ 2 / aP c χ ξ ≤ 25 / 4 * c * M := by
    unfold energy at hE
    have : 0 ≤ aP c χ ξ * ψ ξ ^ 2 := by positivity
    linarith
  have h2 : u ξ ^ 2 ≤ 25 / 4 * c * M * (c * ξ ^ 2) := by
    rw [div_le_iff₀ ha] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left haξ (by positivity))
  have h3 : |u ξ| ^ 2 ≤ (c * ξ * (5 / 2 * √M)) ^ 2 := by
    rw [sq_abs]
    have : (c * ξ * (5 / 2 * √M)) ^ 2 = 25 / 4 * c ^ 2 * ξ ^ 2 * M := by
      rw [show (c * ξ * (5 / 2 * √M)) ^ 2 = 25 / 4 * c ^ 2 * ξ ^ 2 * √M ^ 2 by ring, sq_sqrt hM]
    rw [this]; nlinarith [mul_nonneg (mul_nonneg hc2.le (sq_nonneg ξ)) hM]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp h3

/-- **A mode `m ≥ 2` with ellipticity `θ`**: where `θc²p ≤ q` on `[m, X]` and `|u| ≤ cξS` there,
`|∫_m^X ψ(1 − m/ξ)| ≤ (S/(cθ²))(m²/(m² − 1))(3/(2m))`. -/
theorem abs_mode_le_θ {c χ m X S θ : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hm : 2 ≤ m) (hmX : m ≤ X) (hS : 0 ≤ S) (hell : ∀ ξ ∈ Icc m X, θ * (c ^ 2 * pP ξ) ≤ qP c χ ξ)
    (hψc : ContinuousOn ψ (Icc m X)) (hu : ∀ ξ ∈ Icc m X, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hus : ∀ ξ ∈ Icc m X, |u ξ| ≤ c * ξ * S) :
    |∫ ξ in m..X, ψ ξ * (1 - m / ξ)| ≤ S / (c * θ ^ 2) * (m ^ 2 / (m ^ 2 - 1) * (3 / (2 * m))) := by
  have hp : ∀ ξ ∈ Icc m X, 0 < pP ξ := fun ξ hξ => pP_pos (by linarith [hξ.1])
  have hq : ∀ ξ ∈ Icc m X, 0 < qP c χ ξ := fun ξ hξ =>
    lt_of_lt_of_le (by have := hp ξ hξ; positivity) (hell ξ hξ)
  have huc : ContinuousOn u (Icc m X) := fun ξ hξ => (hu ξ hξ).continuousAt.continuousWithinAt
  rw [integral_mode_eq_from (by linarith) hmX hq hψc hu]
  have hm0 : m ≠ 0 := by linarith
  simp only [div_self hm0, sub_self, mul_zero, zero_div, add_zero]
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hθ2' : 0 < θ ^ 2 := by positivity
  -- the boundary at `X`
  have hX1 : 1 < X := by linarith
  have hpX := hp X ⟨hmX, le_rfl⟩
  have hqX := hq X ⟨hmX, le_rfl⟩
  have hw : 0 ≤ 1 - m / X := by rw [sub_nonneg, div_le_one (by linarith)]; exact hmX
  have hB : |u X * (1 - m / X) / qP c χ X| ≤ S / (c * θ ^ 2) * ((X - m) / (X ^ 2 - 1)) := by
    rw [abs_div, abs_mul, abs_of_nonneg hw, abs_of_pos hqX]
    have hden : θ ^ 2 * (c ^ 2 * pP X) ≤ qP c χ X :=
      (mul_le_mul_of_nonneg_right hθ2 (by positivity)).trans (hell X ⟨hmX, le_rfl⟩)
    calc |u X| * (1 - m / X) / qP c χ X ≤ c * X * S * (1 - m / X) / qP c χ X :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hus X ⟨hmX, le_rfl⟩) hw) hqX.le
      _ ≤ c * X * S * (1 - m / X) / (θ ^ 2 * (c ^ 2 * pP X)) :=
          div_le_div_of_nonneg_left (by have : 0 < X := by linarith
                                        positivity) (by positivity) hden
      _ = S / (c * θ ^ 2) * ((X - m) / (X ^ 2 - 1)) := by
          have : X ≠ 0 := by linarith
          unfold pP; field_simp
  -- the interior
  have hpt : ∀ ξ ∈ Icc m X, |u ξ * hW c χ m ξ| ≤ S / (c * θ ^ 2) * Gm' m ξ := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have hpξ := hp ξ hξ
    have hqξ := hq ξ hξ
    have ex : hW c χ m ξ = m / (ξ ^ 2 * qP c χ ξ) - 2 * c ^ 2 * (ξ - m) / qP c χ ξ ^ 2 := by
      unfold hW; field_simp
    set p := pP ξ with hpdef
    set q := qP c χ ξ with hqdef
    have hθq : θ ^ 2 * (c ^ 2 * p) ≤ q :=
      (mul_le_mul_of_nonneg_right hθ2 (by positivity)).trans (hell ξ hξ)
    have hθq' : θ * (c ^ 2 * p) ≤ q := hell ξ hξ
    have hx0 : 0 ≤ m / (ξ ^ 2 * q) := by have : 0 < m := by linarith
                                         positivity
    have hy0 : 0 ≤ 2 * c ^ 2 * (ξ - m) / q ^ 2 :=
      div_nonneg (mul_nonneg (by positivity) (by linarith [hξ.1])) (by positivity)
    have hx : m / (ξ ^ 2 * q) ≤ m / (ξ ^ 2 * (θ ^ 2 * (c ^ 2 * p))) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) (mul_le_mul_of_nonneg_left hθq (by positivity))
    have hy : 2 * c ^ 2 * (ξ - m) / q ^ 2 ≤ 2 * c ^ 2 * (ξ - m) / (θ * (c ^ 2 * p)) ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg (by positivity) (by linarith [hξ.1])) (by positivity)
        (pow_le_pow_left₀ (by positivity) hθq' 2)
    have hy' : 2 * c ^ 2 * (ξ - m) / (θ * (c ^ 2 * p)) ^ 2 ≤ 2 * c ^ 2 * (ξ - m) / (θ ^ 2 * (c ^ 2 * p) ^ 2) := by
      rw [mul_pow]
    have hh : |hW c χ m ξ| ≤ m / (ξ ^ 2 * (θ ^ 2 * (c ^ 2 * p))) + 2 * c ^ 2 * (ξ - m) / (θ ^ 2 * (c ^ 2 * p) ^ 2) := by
      rw [ex]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg hx0, abs_of_nonneg hy0]
      linarith
    have hK : m / (ξ * p) + 2 * ξ * (ξ - m) / p ^ 2 ≤ Gm' m ξ := by
      have hm1 : 0 < m ^ 2 - 1 := by nlinarith
      have e : Gm' m ξ - (m / (ξ * p) + 2 * ξ * (ξ - m) / p ^ 2)
          = (m + ξ) * (ξ ^ 2 - m ^ 2) / ((m ^ 2 - 1) * ξ ^ 3 * p) := by
        unfold Gm'; rw [hpdef]; unfold pP
        have : ξ ^ 2 - 1 ≠ 0 := by nlinarith [hξ.1]
        field_simp; ring
      have : 0 ≤ (m + ξ) * (ξ ^ 2 - m ^ 2) / ((m ^ 2 - 1) * ξ ^ 3 * p) :=
        div_nonneg (mul_nonneg (by linarith [hξ.1]) (by nlinarith [hξ.1])) (by positivity)
      linarith
    rw [abs_mul]
    calc |u ξ| * |hW c χ m ξ|
        ≤ c * ξ * S * (m / (ξ ^ 2 * (θ ^ 2 * (c ^ 2 * p))) + 2 * c ^ 2 * (ξ - m) / (θ ^ 2 * (c ^ 2 * p) ^ 2)) :=
          mul_le_mul (hus ξ hξ) hh (abs_nonneg _) (by positivity)
      _ = S / (c * θ ^ 2) * (m / (ξ * p) + 2 * ξ * (ξ - m) / p ^ 2) := by field_simp
      _ ≤ S / (c * θ ^ 2) * Gm' m ξ := mul_le_mul_of_nonneg_left hK (by positivity)
  have hc2 : ContinuousOn (fun ξ => u ξ * hW c χ m ξ) (Icc m X) :=
    huc.mul (continuousOn_hW_of_pos (by linarith) hq)
  have hG : ContinuousOn (fun ξ => S / (c * θ ^ 2) * Gm' m ξ) (Icc m X) :=
    continuousOn_const.mul (continuousOn_Gm' hm)
  have hI : |∫ ξ in m..X, u ξ * hW c χ m ξ| ≤ S / (c * θ ^ 2) * (Gm m X - Gm m m) := by
    refine (abs_integral_le_integral_abs hmX).trans ?_
    refine (integral_mono_on hmX (hc2.abs.intervalIntegrable_of_Icc hmX) (hG.intervalIntegrable_of_Icc hmX)
      fun ξ hξ => hpt ξ hξ).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul]
    congr 1
    refine integral_eq_sub_of_hasDerivAt (fun ξ hξ => hasDerivAt_Gm m ?_)
      ((continuousOn_Gm' hm).intervalIntegrable_of_Icc hmX)
    rw [uIcc_of_le hmX] at hξ; linarith [hξ.1]
  have hm1 : 0 < m ^ 2 - 1 := by nlinarith
  have hGmm : Gm m m = -(m ^ 2 / (m ^ 2 - 1) * (3 / (2 * m))) := by
    unfold Gm; field_simp; ring
  have hneg : m ^ 2 / (m ^ 2 - 1) * (-(m / (2 * X ^ 2)) - 1 / X) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (by have : 0 ≤ m / (2 * X ^ 2) := by have : 0 < m := by linarith
                                           positivity
          have : 0 ≤ 1 / X := by have : 0 < X := by linarith
                                 positivity
          linarith)
  have hsum : (X - m) / (X ^ 2 - 1) + (Gm m X - Gm m m) ≤ m ^ 2 / (m ^ 2 - 1) * (3 / (2 * m)) := by
    rw [hGmm]; unfold Gm; linarith
  calc |-(u X * (1 - m / X) / qP c χ X) + ∫ ξ in m..X, u ξ * hW c χ m ξ|
      ≤ |u X * (1 - m / X) / qP c χ X| + |∫ ξ in m..X, u ξ * hW c χ m ξ| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_neg]
    _ ≤ S / (c * θ ^ 2) * ((X - m) / (X ^ 2 - 1)) + S / (c * θ ^ 2) * (Gm m X - Gm m m) := add_le_add hB hI
    _ = S / (c * θ ^ 2) * ((X - m) / (X ^ 2 - 1) + (Gm m X - Gm m m)) := by ring
    _ ≤ S / (c * θ ^ 2) * (m ^ 2 / (m ^ 2 - 1) * (3 / (2 * m))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)

/-- `pq h₁² ≤ (3/ξ⁴ + 6/(ξ+1)²)/(θ³c²)` for `ξ > 1`, `c > 0`, `θ ∈ (0, 1]` and `θc²p ≤ q`. -/
theorem pq_hW_one_sq_le_θ {c χ ξ θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hell : θ * (c ^ 2 * pP ξ) ≤ qP c χ ξ) (hξ : 1 < ξ) :
    pP ξ * qP c χ ξ * hW c χ 1 ξ ^ 2 ≤ (3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) / (θ ^ 3 * c ^ 2) := by
  have hp : 0 < pP ξ := pP_pos hξ
  have hq : 0 < qP c χ ξ := lt_of_lt_of_le (by positivity) hell
  have ex : hW c χ 1 ξ = 1 / (ξ ^ 2 * qP c χ ξ) - 2 * c ^ 2 * (ξ - 1) / qP c χ ξ ^ 2 := by
    unfold hW; have : ξ ≠ 0 := by linarith
    field_simp
  have hθ3 : θ ^ 3 ≤ θ := by nlinarith [pow_le_one₀ hθ.le hθ1 (n := 2)]
  set p := pP ξ with hpdef
  set q := qP c χ ξ
  set x := 1 / (ξ ^ 2 * q)
  set y := 2 * c ^ 2 * (ξ - 1) / q ^ 2
  have hx : p * q * x ^ 2 ≤ 1 / (θ ^ 3 * c ^ 2 * ξ ^ 4) := by
    have e : p * q * x ^ 2 = p / (ξ ^ 4 * q) := by simp only [x]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : θ ^ 3 * (c ^ 2 * p) ≤ q := (mul_le_mul_of_nonneg_right hθ3 (by positivity)).trans hell
    nlinarith [pow_pos (by linarith : (0:ℝ) < ξ) 4]
  have hy : p * q * y ^ 2 ≤ 4 / (θ ^ 3 * c ^ 2 * (ξ + 1) ^ 2) := by
    have e : p * q * y ^ 2 = 4 * c ^ 4 * p * (ξ - 1) ^ 2 / q ^ 3 := by simp only [y]; field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpp : (ξ - 1) ^ 2 * (ξ + 1) ^ 2 = p ^ 2 := by rw [hpdef]; unfold pP; ring
    have h3 : (θ * (c ^ 2 * p)) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by positivity) hell 3
    have e2 : 4 * c ^ 4 * p * (ξ - 1) ^ 2 * (θ ^ 3 * c ^ 2 * (ξ + 1) ^ 2) = 4 * (θ * (c ^ 2 * p)) ^ 3 := by
      rw [show 4 * c ^ 4 * p * (ξ - 1) ^ 2 * (θ ^ 3 * c ^ 2 * (ξ + 1) ^ 2)
        = 4 * θ ^ 3 * c ^ 6 * p * ((ξ - 1) ^ 2 * (ξ + 1) ^ 2) by ring, hpp]; ring
    rw [e2]; linarith
  have hxy : (x - y) ^ 2 ≤ 3 * x ^ 2 + 3 / 2 * y ^ 2 := by nlinarith [sq_nonneg (2 * x + y)]
  have hpq : 0 ≤ p * q := by positivity
  rw [ex]
  calc p * q * (x - y) ^ 2 ≤ p * q * (3 * x ^ 2 + 3 / 2 * y ^ 2) := mul_le_mul_of_nonneg_left hxy hpq
    _ = 3 * (p * q * x ^ 2) + 3 / 2 * (p * q * y ^ 2) := by ring
    _ ≤ 3 * (1 / (θ ^ 3 * c ^ 2 * ξ ^ 4)) + 3 / 2 * (4 / (θ ^ 3 * c ^ 2 * (ξ + 1) ^ 2)) := by linarith
    _ = (3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) / (θ ^ 3 * c ^ 2) := by field_simp; ring

/-- **The interior of the mode `m = 1` from `a > 1` with ellipticity `θ`**: where `θc²p ≤ q` on `[a, X]` and
`∫_a^X u²/(pq) ≤ U`, `|∫_a^X u h₁| ≤ 2√((U/2)(2/(θ³c²)))`. -/
theorem abs_mode_one_interior_le_θ {c χ a X U θ : ℝ} {u : ℝ → ℝ} (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (ha : 1 < a) (haX : a ≤ X) (huc : ContinuousOn u (Icc a X))
    (hell : ∀ ξ ∈ Icc a X, θ * (c ^ 2 * pP ξ) ≤ qP c χ ξ)
    (hU : ∫ ξ in a..X, u ξ ^ 2 / (pP ξ * qP c χ ξ) ≤ U) :
    |∫ ξ in a..X, u ξ * hW c χ 1 ξ| ≤ 2 * √(U / 2 * (2 / (θ ^ 3 * c ^ 2))) := by
  have hp : ∀ ξ ∈ Icc a X, 0 < pP ξ := fun ξ hξ => pP_pos (lt_of_lt_of_le ha hξ.1)
  have hq : ∀ ξ ∈ Icc a X, 0 < qP c χ ξ := fun ξ hξ =>
    lt_of_lt_of_le (by have := hp ξ hξ; positivity) (hell ξ hξ)
  have hqc : Continuous (qP c χ) := by unfold qP; fun_prop
  have hpc : Continuous pP := by unfold pP; fun_prop
  have hUc : ContinuousOn (fun ξ => u ξ ^ 2 / (pP ξ * qP c χ ξ)) (Icc a X) :=
    (huc.pow 2).div (hpc.continuousOn.mul hqc.continuousOn) fun ξ hξ => (mul_pos (hp ξ hξ) (hq ξ hξ)).ne'
  have hUi := hUc.intervalIntegrable_of_Icc (μ := volume) haX
  have hU0 : 0 ≤ U := (intervalIntegral.integral_nonneg haX fun ξ hξ =>
    div_nonneg (sq_nonneg _) (mul_pos (hp ξ hξ) (hq ξ hξ)).le).trans hU
  have hκc : ContinuousOn (fun ξ : ℝ => 3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) (Icc a X) := by
    have h4 : ContinuousOn (fun ξ : ℝ => ξ ^ 4) (Icc a X) := by fun_prop
    have h2 : ContinuousOn (fun ξ : ℝ => (ξ + 1) ^ 2) (Icc a X) := by fun_prop
    refine ContinuousOn.add (ContinuousOn.div₀ (f := fun _ : ℝ => (3 : ℝ)) continuousOn_const h4
      fun ξ hξ => ?_) (ContinuousOn.div₀ (f := fun _ : ℝ => (6 : ℝ)) continuousOn_const h2 fun ξ hξ => ?_)
    · have : ξ ≠ 0 := by linarith [hξ.1]
      exact pow_ne_zero 4 this
    · have : ξ + 1 ≠ 0 := by linarith [hξ.1]
      exact pow_ne_zero 2 this
  have hκi := hκc.intervalIntegrable_of_Icc (μ := volume) haX
  have hc2 : ContinuousOn (fun ξ => u ξ * hW c χ 1 ξ) (Icc a X) :=
    huc.mul (continuousOn_hW_of_pos (by linarith) hq)
  refine le_two_sqrt_mul (by linarith) (by positivity) fun t ht => ?_
  have hR : IntervalIntegrable (fun ξ => t / 2 * (u ξ ^ 2 / (pP ξ * qP c χ ξ))
      + 1 / (2 * t) * ((3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) / (θ ^ 3 * c ^ 2))) volume a X :=
    (hUi.const_mul _).add ((hκi.div_const _).const_mul _)
  have hpt : ∀ ξ ∈ Ioo a X, |u ξ * hW c χ 1 ξ| ≤ t / 2 * (u ξ ^ 2 / (pP ξ * qP c χ ξ))
      + 1 / (2 * t) * ((3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) / (θ ^ 3 * c ^ 2)) := by
    intro ξ hξ
    have hpξ := hp ξ (Ioo_subset_Icc_self hξ)
    have hqξ := hq ξ (Ioo_subset_Icc_self hξ)
    refine abs_mul_le_amgm ht (by positivity) (by positivity)
      (pq_hW_one_sq_le_θ hc hθ hθ1 (hell ξ (Ioo_subset_Icc_self hξ)) (lt_trans ha hξ.1)) ?_
    field_simp
  calc |∫ ξ in a..X, u ξ * hW c χ 1 ξ|
      ≤ ∫ ξ in a..X, |u ξ * hW c χ 1 ξ| := abs_integral_le_integral_abs haX
    _ ≤ ∫ ξ in a..X, (t / 2 * (u ξ ^ 2 / (pP ξ * qP c χ ξ))
          + 1 / (2 * t) * ((3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2) / (θ ^ 3 * c ^ 2))) :=
        integral_mono_on_of_le_Ioo haX (hc2.abs.intervalIntegrable_of_Icc haX) hR hpt
    _ = t / 2 * (∫ ξ in a..X, u ξ ^ 2 / (pP ξ * qP c χ ξ))
          + 1 / (2 * t) * ((∫ ξ in a..X, (3 / ξ ^ 4 + 6 / (ξ + 1) ^ 2)) / (θ ^ 3 * c ^ 2)) := by
        rw [intervalIntegral.integral_add (hUi.const_mul _) ((hκi.div_const _).const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_div]
    _ ≤ t / 2 * U + 1 / (2 * t) * (4 / (θ ^ 3 * c ^ 2)) := by
        gcongr
        exact integral_kappa_le_from ha.le haX
    _ = t * (U / 2) + 2 / (θ ^ 3 * c ^ 2) / t := by field_simp; ring

/-- **The weighted mass above the layer, from the envelope**: with `θc²p ≤ q` and the cube inequality on
`[1 + 6/c, ∞)`, `E(X) ≤ (25/4)cM` and `E(1 + 6/c) ≤ 9cM` (`M = ∫₁^Xψ²`),
`∫_{1+6/c}^X u²/(pq) ≤ (10/9)((11/10)M + (5/(384θ))M + (3/(8θ))M)`. -/
theorem integral_u_sq_le_env {c χ X θ : ℝ} {ψ u : ℝ → ℝ} (hc : 80 ≤ c) (hθ : 0 < θ) (hX : 2 ≤ X)
    (hell : ∀ ξ, 1 + 6 / c ≤ ξ → θ * (c ^ 2 * pP ξ) ≤ qP c χ ξ)
    (hcube : ∀ ξ, 1 + 6 / c ≤ ξ → 25 * pP ξ * (2 * c ^ 2 * ξ) ^ 2 ≤ qP c χ ξ ^ 3)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hψc : Continuous ψ)
    (hEX : energy (aP c χ) ψ u X ≤ 25 / 4 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2)
    (hE0 : energy (aP c χ) ψ u (1 + 6 / c) ≤ 9 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2) :
    ∫ ξ in (1 + 6 / c)..X, u ξ ^ 2 / (pP ξ * qP c χ ξ)
      ≤ 10 / 9 * (11 / 10 * (∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2) + 5 / (384 * θ) * (∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2)
        + 3 / (8 * θ) * ∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have h60 : 0 < 6 / c := by positivity
  have h6 : 6 / c ≤ 3 / 40 := by rw [div_le_div_iff₀ hc0 (by norm_num)]; linarith
  set ξ₀ := 1 + 6 / c with hξ₀
  have hξ₀1 : 1 < ξ₀ := by linarith
  have hξ₀X : ξ₀ ≤ X := by linarith
  have hp : ∀ ξ ∈ Icc ξ₀ X, 0 < pP ξ := fun ξ hξ => pP_pos (by linarith [hξ.1])
  have hq : ∀ ξ ∈ Icc ξ₀ X, 0 < qP c χ ξ := fun ξ hξ =>
    lt_of_lt_of_le (by have := hp ξ hξ; positivity) (hell ξ hξ.1)
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun ξ => (hu ξ).continuousAt
  have hid := integral_u_sq_eq_from hξ₀1 hξ₀X hq (fun ξ hξ => hψ ξ (by linarith [hξ.1])) (fun ξ _ => hu ξ)
  set M := ∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2 with hMdef
  set M₀ := ∫ ξ in ξ₀..X, ψ ξ ^ 2 with hM₀def
  set U₀ := ∫ ξ in ξ₀..X, u ξ ^ 2 / (pP ξ * qP c χ ξ) with hU₀def
  set J := ∫ ξ in ξ₀..X, ψ ξ * u ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2 with hJdef
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg (by linarith) fun ξ _ => sq_nonneg _
  have hM₀ : M₀ ≤ M :=
    intervalIntegral.integral_mono_interval hξ₀1.le hξ₀X le_rfl
      (Filter.Eventually.of_forall fun t => sq_nonneg (ψ t)) ((hψc.pow 2).intervalIntegrable 1 X)
  -- the boundary at `X`
  have hXmem : X ∈ Icc ξ₀ X := ⟨hξ₀X, le_rfl⟩
  have hqX : 3 * θ * c ^ 2 ≤ qP c χ X := by
    refine le_trans ?_ (hell X hξ₀X)
    have : 3 ≤ pP X := by unfold pP; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ θ * c ^ 2)]
  have hVX : |ψ X * u X / qP c χ X| ≤ 5 / (384 * θ) * M := by
    have haX : 0 < aP c χ X := sqrt_pos.mpr (mul_pos (hp X hXmem) (hq X hXmem))
    have hE := (two_mul_abs_le_energy (ψ := ψ) (u := u) haX).trans hEX
    rw [abs_div, abs_of_pos (hq X hXmem)]
    calc |ψ X * u X| / qP c χ X ≤ (25 / 8 * c * M) / (3 * θ * c ^ 2) :=
          div_le_div₀ (by positivity) (by linarith) (by positivity) hqX
      _ = 25 / 24 * M / (θ * c) := by field_simp; ring
      _ ≤ 25 / 24 * M / (θ * 80) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      _ = 5 / (384 * θ) * M := by field_simp; ring
  -- the boundary at `ξ₀`
  have h0mem : ξ₀ ∈ Icc ξ₀ X := ⟨le_rfl, hξ₀X⟩
  have hq0 : 12 * θ * c ≤ qP c χ ξ₀ := by
    refine le_trans ?_ (hell ξ₀ le_rfl)
    have h12 := twelve_le_c_pP hc0 (le_refl ξ₀)
    nlinarith [mul_le_mul_of_nonneg_left h12 (by positivity : (0:ℝ) ≤ θ * c)]
  have hV0 : |ψ ξ₀ * u ξ₀ / qP c χ ξ₀| ≤ 3 / (8 * θ) * M := by
    have ha0 : 0 < aP c χ ξ₀ := sqrt_pos.mpr (mul_pos (hp ξ₀ h0mem) (hq ξ₀ h0mem))
    have hE := (two_mul_abs_le_energy (ψ := ψ) (u := u) ha0).trans hE0
    have hq0' : 0 < qP c χ ξ₀ := hq ξ₀ h0mem
    rw [abs_div, abs_of_pos hq0']
    calc |ψ ξ₀ * u ξ₀| / qP c χ ξ₀ ≤ (9 / 2 * c * M) / (12 * θ * c) :=
          div_le_div₀ (by positivity) (by linarith) (by positivity) hq0
      _ = 3 / (8 * θ) * M := by field_simp; ring
  -- the cross term
  have hqc : Continuous (qP c χ) := by unfold qP; fun_prop
  have hpc : Continuous pP := by unfold pP; fun_prop
  have hTc : ContinuousOn (fun ξ => ψ ξ * u ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2) (Icc ξ₀ X) :=
    ((hψc.mul huc).mul (by fun_prop)).continuousOn.div (hqc.pow 2).continuousOn
      fun t ht => pow_ne_zero 2 (hq t ht).ne'
  have hUc : ContinuousOn (fun ξ => u ξ ^ 2 / (pP ξ * qP c χ ξ)) (Icc ξ₀ X) :=
    (huc.pow 2).continuousOn.div (hpc.mul hqc).continuousOn fun t ht => (mul_pos (hp t ht) (hq t ht)).ne'
  have hUi := hUc.intervalIntegrable_of_Icc (μ := volume) hξ₀X
  have hψ2 : IntervalIntegrable (fun ξ => ψ ξ ^ 2) volume ξ₀ X := (hψc.pow 2).intervalIntegrable ξ₀ X
  have hJ : J ≤ (M₀ + U₀) / 10 := by
    have hS : ContinuousOn (fun ξ => (ψ ξ ^ 2 + u ξ ^ 2 / (pP ξ * qP c χ ξ)) / 10) (Icc ξ₀ X) :=
      ((hψc.pow 2).continuousOn.add hUc).div_const 10
    refine (integral_mono_on_of_le_Ioo hξ₀X (hTc.intervalIntegrable_of_Icc hξ₀X)
      (hS.intervalIntegrable_of_Icc hξ₀X) fun ξ hξ => ?_).trans (le_of_eq ?_)
    · exact (le_abs_self _).trans (abs_cross_le (hp ξ (Ioo_subset_Icc_self hξ)) (hq ξ (Ioo_subset_Icc_self hξ))
        (hcube ξ hξ.1.le))
    · rw [intervalIntegral.integral_div, intervalIntegral.integral_add hψ2 hUi]
  have h1 := le_abs_self (ψ X * u X / qP c χ X)
  have h2 := neg_abs_le (ψ ξ₀ * u ξ₀ / qP c χ ξ₀)
  linarith

/-- **The boundary at `ξ₀ = 1 + 6/c` from the envelope**: with `θc²p ≤ q` at `ξ₀` (`θ ∈ (0, 1]`) and
`E(ξ₀) ≤ 9cM`, `(u(ξ₀)(1 − 1/ξ₀)/q(ξ₀))² ≤ 27M/(θ²c³)`. -/
theorem bdry_xi0_sq_le_env {c χ θ M : ℝ} {ψ u : ℝ → ℝ} (hc : 80 ≤ c) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hell : θ * (c ^ 2 * pP (1 + 6 / c)) ≤ qP c χ (1 + 6 / c)) (hM : 0 ≤ M)
    (hE0 : energy (aP c χ) ψ u (1 + 6 / c) ≤ 9 * c * M) :
    (u (1 + 6 / c) * (1 - 1 / (1 + 6 / c)) / qP c χ (1 + 6 / c)) ^ 2 ≤ 27 * M / (θ ^ 2 * c ^ 3) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have h60 : 0 < 6 / c := by positivity
  set ξ₀ := 1 + 6 / c with hξ₀
  have hξ₀1 : 1 < ξ₀ := by linarith
  have hp0 : 0 < pP ξ₀ := pP_pos hξ₀1
  set E := energy (aP c χ) ψ u ξ₀ with hEdef
  set a := aP c χ ξ₀ with hadef
  set q := qP c χ ξ₀ with hqdef
  set w := 1 - 1 / ξ₀ with hwdef
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hell
  have ha : 0 < a := sqrt_pos.mpr (mul_pos hp0 hq)
  have hq12 : 12 * θ * c ≤ q := by
    refine le_trans ?_ hell
    have h12 := twelve_le_c_pP hc0 (le_refl ξ₀)
    nlinarith [mul_le_mul_of_nonneg_left h12 (by positivity : (0:ℝ) ≤ θ * c)]
  have hu2 : u ξ₀ ^ 2 ≤ a * E := by
    have : u ξ₀ ^ 2 / a ≤ E := by
      rw [hEdef]; unfold energy; have : 0 ≤ a * ψ ξ₀ ^ 2 := by positivity
      linarith
    rwa [div_le_iff₀ ha, mul_comm] at this
  have haq : a ≤ q / (θ * c) := by
    rw [hadef, aP, Real.sqrt_le_left (by positivity)]
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hθ2 : θ ^ 2 ≤ θ := by nlinarith
    -- `pq θ²c² ≤ pq θ c² ≤ q·q`
    have h1 : pP ξ₀ * qP c χ ξ₀ * (θ * c) ^ 2 ≤ pP ξ₀ * qP c χ ξ₀ * (θ * c ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right hθ2 hc2.le
    have h2 : pP ξ₀ * qP c χ ξ₀ * (θ * c ^ 2) ≤ q ^ 2 := by
      rw [sq]; nlinarith [mul_le_mul_of_nonneg_left hell hq.le]
    linarith
  have hw0 : 0 ≤ w := by rw [hwdef, sub_nonneg, div_le_one (by linarith)]; exact hξ₀1.le
  have hw6 : w ≤ 6 / c := by
    rw [hwdef, show 1 - 1 / ξ₀ = (ξ₀ - 1) / ξ₀ by field_simp]
    exact (div_le_self (by linarith) hξ₀1.le).trans (by rw [hξ₀]; ring_nf; rfl)
  have hE0' : 0 ≤ E := le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) ha)
  have hstep : (u ξ₀ * w / q) ^ 2 ≤ E * w ^ 2 / (θ * c * q) := by
    rw [div_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : u ξ₀ ^ 2 ≤ q / (θ * c) * E := hu2.trans (mul_le_mul_of_nonneg_right haq hE0')
    have h2 : u ξ₀ ^ 2 * (θ * c) ≤ q * E := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h1; linarith
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ w ^ 2 * q)
    nlinarith
  have hfin : E * w ^ 2 / (θ * c * q) ≤ 27 * M / (θ ^ 2 * c ^ 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hw2 : w ^ 2 ≤ 36 / c ^ 2 :=
      calc w ^ 2 ≤ (6 / c) ^ 2 := pow_le_pow_left₀ hw0 hw6 2
        _ = 36 / c ^ 2 := by ring
    have hEw : E * w ^ 2 ≤ 9 * c * M * (36 / c ^ 2) := mul_le_mul hE0 hw2 (sq_nonneg _) (by positivity)
    have e : 9 * c * M * (36 / c ^ 2) * (θ ^ 2 * c ^ 3) = 27 * M * (θ * c * (12 * θ * c)) := by
      field_simp; ring
    calc E * w ^ 2 * (θ ^ 2 * c ^ 3) ≤ 9 * c * M * (36 / c ^ 2) * (θ ^ 2 * c ^ 3) :=
          mul_le_mul_of_nonneg_right hEw (by positivity)
      _ = 27 * M * (θ * c * (12 * θ * c)) := e
      _ ≤ 27 * M * (θ * c * q) := by gcongr
  exact hstep.trans hfin

/-- **The tilt from ellipticity and the envelope**: `θc²p ≤ q`, `25p(2c²ξ)² ≤ q³` beyond `1 + 6/c`, `E ≤ (25/4)cM`
on `[6/5, X]`, `E(1 + 6/c) ≤ 9cM`, `72/c ≤ k₁²`, `27/(θ²c) ≤ k₂²`, `40(11/10 + 5/(384θ) + 3/(8θ)) ≤ 9θ³k₃²` give
`|∫_{(1,∞)} posTail ψ X θ (1 − 1/θ)| ≤ (45/(16θ²) + 5/(6θ) + k₁ + k₂ + k₃)√M/c`, `M = ∫₁^X ψ²`. -/
theorem tilt_le_env_of {c χ X θ k₁ k₂ k₃ : ℝ} {ψ u : ℝ → ℝ} (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hX : 2 ≤ X)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hell : ∀ ξ, 1 + 6 / c ≤ ξ → θ * (c ^ 2 * pP ξ) ≤ qP c χ ξ)
    (hcube : ∀ ξ, 1 + 6 / c ≤ ξ → 25 * pP ξ * (2 * c ^ 2 * ξ) ^ 2 ≤ qP c χ ξ ^ 3)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hψc : Continuous ψ)
    (hFar : ∀ ξ ∈ Icc (6 / 5 : ℝ) X, energy (aP c χ) ψ u ξ ≤ 25 / 4 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2)
    (hEnv : energy (aP c χ) ψ u (1 + 6 / c) ≤ 9 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hk₃ : 0 ≤ k₃) (h₁ : 72 / c ≤ k₁ ^ 2) (h₂ : 27 / (θ ^ 2 * c) ≤ k₂ ^ 2)
    (h₃ : 4 * (10 / 9 * (11 / 10 + 5 / (384 * θ) + 3 / (8 * θ))) / θ ^ 3 ≤ k₃ ^ 2) :
    |∫ θ in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail ψ X θ * (1 - 1 / θ)|
      ≤ (45 / (16 * θ ^ 2) + 5 / (6 * θ) + k₁ + k₂ + k₃) * √(∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2) / c := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have h60 : 0 < 6 / c := by positivity
  have h6 : 6 / c ≤ 3 / 40 := by rw [div_le_div_iff₀ hc0 (by norm_num)]; linarith
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun ξ => (hu ξ).continuousAt
  set M := ∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2 with hMdef
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg hX1 fun ξ _ => sq_nonneg _
  set r := √M with hrdef
  have hr : 0 ≤ r := sqrt_nonneg _
  have hr2 : r ^ 2 = M := sq_sqrt hM
  set S := 5 / 2 * r with hSdef
  have hS : 0 ≤ S := by positivity
  have hqpos : ∀ ξ, 1 + 6 / c ≤ ξ → 0 < qP c χ ξ := fun ξ hξ =>
    lt_of_lt_of_le (by have := pP_pos (show 1 < ξ by linarith); positivity) (hell ξ hξ)
  have hus : ∀ ξ ∈ Icc (6 / 5 : ℝ) X, |u ξ| ≤ c * ξ * S := fun ξ hξ =>
    abs_u_le_of_energy' hc0 hχ0 (by linarith [hξ.1]) (hqpos ξ (by linarith [hξ.1])) hM (hFar ξ hξ)
  have hw : ContinuousOn (fun θ : ℝ => 1 - 1 / θ) (Icc 1 X) :=
    continuousOn_const.sub (continuousOn_const.div continuousOn_id fun θ hθ =>
      (lt_of_lt_of_le one_pos hθ.1).ne')
  rw [Cvs.L2a.PositionTailSpanAdapters.integral_posTail_mul hX1 hψc.continuousOn hw]
  have hK : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ ⌊X⌋₊)]
  -- the mode `m = 1`
  have h1 : |((1 : ℕ) : ℝ)⁻¹ * ∫ ξ in ((1 : ℕ) : ℝ)..X, ψ ξ * (1 - 1 / (ξ / ((1 : ℕ) : ℝ)))|
      ≤ (5 / (6 * θ) + k₁ + k₂ + k₃) * r / c := by
    simp only [Nat.cast_one, inv_one, one_mul, div_one]
    set ξ₀ := 1 + 6 / c with hξ₀
    have hξ₀1 : 1 < ξ₀ := by linarith
    have hξ₀X : ξ₀ ≤ X := by linarith
    have hq : ∀ ξ ∈ Icc ξ₀ X, 0 < qP c χ ξ := fun ξ hξ => hqpos ξ hξ.1
    have hfc : ContinuousOn (fun ξ => ψ ξ * (1 - 1 / ξ)) (Icc 1 X) := hψc.continuousOn.mul hw
    have hsplit : ∫ ξ in (1 : ℝ)..X, ψ ξ * (1 - 1 / ξ)
        = (∫ ξ in (1 : ℝ)..ξ₀, ψ ξ * (1 - 1 / ξ)) + ∫ ξ in ξ₀..X, ψ ξ * (1 - 1 / ξ) :=
      (intervalIntegral.integral_add_adjacent_intervals
        ((hfc.mono (Icc_subset_Icc le_rfl hξ₀X)).intervalIntegrable_of_Icc hξ₀1.le)
        ((hfc.mono (Icc_subset_Icc hξ₀1.le le_rfl)).intervalIntegrable_of_Icc hξ₀X)).symm
    rw [hsplit, integral_mode_eq_from (m := 1) (by linarith) hξ₀X hq hψc.continuousOn (fun ξ _ => hu ξ)]
    -- the edge piece
    have hM₁ : ∫ ξ in (1 : ℝ)..ξ₀, ψ ξ ^ 2 ≤ M :=
      intervalIntegral.integral_mono_interval le_rfl hξ₀1.le hξ₀X
        (Filter.Eventually.of_forall fun t => sq_nonneg (ψ t)) ((hψc.pow 2).intervalIntegrable 1 X)
    have hedge := abs_edge_le hξ₀1.le hψc.continuousOn hM₁
    have hedge' : 2 * √(M / 2 * ((ξ₀ - 1) ^ 3 / 6)) ≤ k₁ * r / c := by
      refine two_sqrt_le (by positivity) (by positivity) ?_
      have e : 4 * (M / 2 * ((ξ₀ - 1) ^ 3 / 6)) = 72 / c * (M / c ^ 2) := by
        rw [hξ₀]; field_simp; ring
      rw [e, div_pow, mul_pow, hr2, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right h₁ (by positivity)
    -- the boundary at `ξ₀`
    have hB0 : |u ξ₀ * (1 - 1 / ξ₀) / qP c χ ξ₀| ≤ k₂ * r / c := by
      have hsq := bdry_xi0_sq_le_env hc hθ hθ1 (hell ξ₀ le_rfl) hM hEnv
      refine abs_le.mpr (abs_le_of_sq_le_sq' (hsq.trans ?_) (by positivity))
      have e : 27 * M / (θ ^ 2 * c ^ 3) = 27 / (θ ^ 2 * c) * (M / c ^ 2) := by field_simp
      rw [e, div_pow, mul_pow, hr2, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right h₂ (by positivity)
    -- the boundary at `X`
    have hBX : |u X * (1 - 1 / X) / qP c χ X| ≤ 5 / (6 * θ) * r / c := by
      have hX0 : 0 < X := by linarith
      have hpX : 3 ≤ pP X := by unfold pP; nlinarith
      have hqX := hqpos X hξ₀X
      have hw0 : 0 ≤ 1 - 1 / X := by rw [sub_nonneg, div_le_one hX0]; exact hX1
      have huX := hus X ⟨by linarith, le_rfl⟩
      rw [abs_div, abs_mul, abs_of_nonneg hw0, abs_of_pos hqX]
      calc |u X| * (1 - 1 / X) / qP c χ X ≤ c * X * S * (1 - 1 / X) / qP c χ X :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right huX hw0) hqX.le
        _ ≤ c * X * S * (1 - 1 / X) / (θ * (c ^ 2 * pP X)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (hell X hξ₀X)
        _ = S / (c * θ) * (1 / (X + 1)) := by
            have hX2 : X - 1 ≠ 0 := by linarith
            have hX3 : X + 1 ≠ 0 := by linarith
            have hXne : X ≠ 0 := by linarith
            have hp' : pP X = (X - 1) * (X + 1) := by unfold pP; ring
            rw [hp', show 1 - 1 / X = (X - 1) / X by field_simp]
            field_simp
        _ ≤ S / (c * θ) * (1 / 3) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        _ = 5 / (6 * θ) * r / c := by rw [hSdef]; field_simp; ring
    -- the interior
    have hU := integral_u_sq_le_env hc hθ hX hell hcube hψ hu hψc (hFar X ⟨by linarith, le_rfl⟩) hEnv
    have hI := abs_mode_one_interior_le_θ hc0 hθ hθ1 hξ₀1 hξ₀X huc.continuousOn
      (fun ξ hξ => hell ξ hξ.1) hU
    have hI' : 2 * √(10 / 9 * (11 / 10 * M + 5 / (384 * θ) * M + 3 / (8 * θ) * M) / 2 * (2 / (θ ^ 3 * c ^ 2)))
        ≤ k₃ * r / c := by
      refine two_sqrt_le (by positivity) (by positivity) ?_
      have e : 4 * (10 / 9 * (11 / 10 * M + 5 / (384 * θ) * M + 3 / (8 * θ) * M) / 2 * (2 / (θ ^ 3 * c ^ 2)))
          = 4 * (10 / 9 * (11 / 10 + 5 / (384 * θ) + 3 / (8 * θ))) / θ ^ 3 * (M / c ^ 2) := by
        field_simp
      have e2 : (k₃ * r / c) ^ 2 = k₃ ^ 2 * (M / c ^ 2) := by rw [div_pow, mul_pow, hr2]; ring
      rw [e, e2]
      exact mul_le_mul_of_nonneg_right h₃ (by positivity)
    calc |(∫ ξ in (1 : ℝ)..ξ₀, ψ ξ * (1 - 1 / ξ)) + (-(u X * (1 - 1 / X) / qP c χ X)
          + u ξ₀ * (1 - 1 / ξ₀) / qP c χ ξ₀ + ∫ ξ in ξ₀..X, u ξ * hW c χ 1 ξ)|
        ≤ |∫ ξ in (1 : ℝ)..ξ₀, ψ ξ * (1 - 1 / ξ)| + (|u X * (1 - 1 / X) / qP c χ X|
          + |u ξ₀ * (1 - 1 / ξ₀) / qP c χ ξ₀| + |∫ ξ in ξ₀..X, u ξ * hW c χ 1 ξ|) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) le_rfl)
          rw [abs_neg]
      _ ≤ k₁ * r / c + (5 / (6 * θ) * r / c + k₂ * r / c + k₃ * r / c) := by
          gcongr
          · exact hedge.trans hedge'
          · exact hI.trans hI'
      _ = (5 / (6 * θ) + k₁ + k₂ + k₃) * r / c := by ring
  -- the modes `m ≥ 2`
  have h2 : |∑ m ∈ Finset.Ioc 1 ⌊X⌋₊, (m : ℝ)⁻¹ * ∫ ξ in (m : ℝ)..X, ψ ξ * (1 - 1 / (ξ / m))|
      ≤ S / (c * θ ^ 2) * (3 / 2) * (3 / 4) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ Finset.Ioc 1 ⌊X⌋₊, |(m : ℝ)⁻¹ * ∫ ξ in (m : ℝ)..X, ψ ξ * (1 - 1 / (ξ / m))|
        ≤ ∑ m ∈ Finset.Ioc 1 ⌊X⌋₊, S / (c * θ ^ 2) * (3 / 2) * (1 / ((m : ℝ) ^ 2 - 1)) := by
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
          have hb := abs_mode_le_θ hc0 hθ hθ1 hm2 hmX hS (fun ξ hξ => hell ξ (by linarith [hξ.1]))
            hψc.continuousOn (fun ξ _ => hu ξ) (fun ξ hξ => hus ξ ⟨by linarith [hξ.1], hξ.2⟩)
          calc (m : ℝ)⁻¹ * |∫ ξ in (m : ℝ)..X, ψ ξ * (1 - m / ξ)|
              ≤ (m : ℝ)⁻¹ * (S / (c * θ ^ 2) * ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1) * (3 / (2 * m)))) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = S / (c * θ ^ 2) * (3 / 2) * (1 / ((m : ℝ) ^ 2 - 1)) := by field_simp
      _ = S / (c * θ ^ 2) * (3 / 2) * ∑ m ∈ Finset.Ioc 1 ⌊X⌋₊, 1 / ((m : ℝ) ^ 2 - 1) := by
          rw [Finset.mul_sum]
      _ ≤ S / (c * θ ^ 2) * (3 / 2) * (3 / 4) :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_sub_one_le _) (by positivity)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ (5 / (6 * θ) + k₁ + k₂ + k₃) * r / c + S / (c * θ ^ 2) * (3 / 2) * (3 / 4) := add_le_add h1 h2
    _ = (45 / (16 * θ ^ 2) + 5 / (6 * θ) + k₁ + k₂ + k₃) * r / c := by rw [hSdef]; field_simp; ring

/-- The tilt constant: `45/(16θ²) + 5/(6θ) + √(72/c) + √(27/(θ²c)) + √(4·(10/9)(11/10 + 5/(384θ) + 3/(8θ))/θ³)`. -/
noncomputable def tiltK (θ c : ℝ) : ℝ :=
  45 / (16 * θ ^ 2) + 5 / (6 * θ) + √(72 / c) + √(27 / (θ ^ 2 * c))
    + √(4 * (10 / 9 * (11 / 10 + 5 / (384 * θ) + 3 / (8 * θ))) / θ ^ 3)

/-- **The tilted pole from ellipticity and the envelope**: `tilt_le_env_of` at its exact constants,
`|∫_{(1,∞)} posTail ψ X θ (1 − 1/θ)| ≤ tiltK θ c · √(∫₁^X ψ²)/c`. -/
theorem tilt_le_env {c χ X θ : ℝ} {ψ u : ℝ → ℝ} (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hX : 2 ≤ X)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hell : ∀ ξ, 1 + 6 / c ≤ ξ → θ * (c ^ 2 * pP ξ) ≤ qP c χ ξ)
    (hcube : ∀ ξ, 1 + 6 / c ≤ ξ → 25 * pP ξ * (2 * c ^ 2 * ξ) ^ 2 ≤ qP c χ ξ ^ 3)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hψc : Continuous ψ)
    (hFar : ∀ ξ ∈ Icc (6 / 5 : ℝ) X, energy (aP c χ) ψ u ξ ≤ 25 / 4 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2)
    (hEnv : energy (aP c χ) ψ u (1 + 6 / c) ≤ 9 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2) :
    |∫ θ in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail ψ X θ * (1 - 1 / θ)|
      ≤ tiltK θ c * √(∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2) / c := by
  have hc0 : 0 < c := by linarith
  have hk3 : 0 ≤ 4 * (10 / 9 * (11 / 10 + 5 / (384 * θ) + 3 / (8 * θ))) / θ ^ 3 := by positivity
  exact tilt_le_env_of hc hχ0 hX hθ hθ1 hell hcube hψ hu hψc hFar hEnv (sqrt_nonneg _) (sqrt_nonneg _)
    (sqrt_nonneg _) (by rw [sq_sqrt (by positivity)]) (by rw [sq_sqrt (by positivity)])
    (by rw [sq_sqrt hk3])

/-- `tiltK (23/24) c ≤ 7` for `c ≥ 10⁴`. -/
theorem tiltK_turn_le_seven {c : ℝ} (hc : 10 ^ 4 ≤ c) : tiltK (23 / 24) c ≤ 7 := by
  have hc0 : 0 < c := by linarith
  have h1 : √(72 / c) ≤ 1 / 10 := by
    rw [sqrt_le_left (by norm_num), div_le_iff₀ hc0]; linarith
  have h2 : √(27 / ((23 / 24) ^ 2 * c)) ≤ 1 / 10 := by
    rw [sqrt_le_left (by norm_num), div_le_iff₀ (by positivity)]; nlinarith
  have h3 : √(4 * (10 / 9 * (11 / 10 + 5 / (384 * (23 / 24 : ℝ)) + 3 / (8 * (23 / 24))))
      / (23 / 24 : ℝ) ^ 3) ≤ 69 / 25 := by
    rw [sqrt_le_left (by norm_num)]; norm_num
  unfold tiltK
  norm_num at h1 h2 h3 ⊢
  linarith

end Cvs.L2a.EllipticTilt
