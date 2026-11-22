import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityComplexWeight
import Cvs.L2a.QIdentityCutPoint
import Cvs.Prolate.BandMassLaw
import Cvs.Prolate.CosineChristoffelDarboux
import Cvs.Prolate.Envelope.RungCountEnvelope
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungCauchySplit
import Cvs.Prolate.RungConnectionIdentity
import Cvs.Prolate.RungOrthogonalityAtInfinity
import Cvs.Prolate.RungStieltjesIdentity
import Cvs.Prolate.RungStieltjesTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-! Decay of the z-Stieltjes transform of an even angular rung: for `c ≥ 80`, `0 ≤ χ < c²`,
`c² − χ ≤ 10c`, `y ≥ 3/2` and `c(z² − 1) ≥ 16`,
`‖Fs(y, z)‖ ≤ 25|A|/(c(y − 1)√(z² − 1))` with `A = g(1) + g(−1)`. -/

noncomputable section
open Real Set Filter Topology MeasureTheory Complex Metric
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts
open Cvs.Prolate.RungStieltjesTransform Cvs.Prolate.RungStieltjesIdentity
open scoped Interval

namespace Cvs.Prolate.RungStieltjesDecay

open Cvs.L2a.QIdentityComplexWeight in
/-- `w(z) ≤ 1/7` once `c(z² − 1) ≥ 16`, `c ≥ 80`. -/
theorem wUp_le_seventh {c z : ℝ} (hc : 80 ≤ c) (hz : 1 < z) (h16 : 16 ≤ c * (z ^ 2 - 1)) :
    Cvs.Prolate.BandMassLaw.wUp c z ≤ 1 / 7 := by
  unfold Cvs.Prolate.BandMassLaw.wUp pP
  have hp : 0 < z ^ 2 - 1 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  rcases le_or_gt z (8 / 7) with h | h
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right hc (by nlinarith : (0 : ℝ) ≤ z ^ 2 - 1)]

/-- `Re Q ≥ c²p(y² − 1)/2` for `σ² ≤ 10c`, `y ≥ 3/2`, `cp ≥ 16`. -/
theorem re_qQ_ge {c χ y x : ℝ} (hc : 0 < c) (hσ : c ^ 2 - χ ≤ 10 * c) (hy : 3 / 2 ≤ y)
    (h16 : 16 ≤ c * pP x) : c ^ 2 * pP x * (y ^ 2 - 1) / 2 ≤ (qQ c χ y x).re := by
  rw [qQ_re]
  have hu : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  have h1 : 10 * c ≤ c * (c * pP x) * (y ^ 2 - 1) / 2 := by
    have := mul_le_mul h16 hu (by norm_num) (by linarith)
    nlinarith
  unfold pP at *
  nlinarith

/-- `‖Q‖ ≥ c²p(y² − 1)/2` for `σ² ≤ 10c`, `y ≥ 3/2`, `cp ≥ 16`. -/
theorem norm_qQ_ge {c χ y x : ℝ} (hc : 0 < c) (hσ : c ^ 2 - χ ≤ 10 * c) (hy : 3 / 2 ≤ y)
    (h16 : 16 ≤ c * pP x) : c ^ 2 * pP x * (y ^ 2 - 1) / 2 ≤ ‖qQ c χ y x‖ :=
  (re_qQ_ge hc hσ hy h16).trans (Complex.re_le_norm _)

/-- `k ≤ (51/40)c` for `σ² ≤ 10c`, `cp ≥ 16`. -/
theorem kP_le {c χ x : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hσ : c ^ 2 - χ ≤ 10 * c) (hx : 1 < x)
    (h16 : 16 ≤ c * pP x) : Cvs.Prolate.RungCauchySplit.kP c χ x ≤ 51 / 40 * c := by
  rw [Cvs.L2a.QIdentityCutPoint.kP_eq_cY hx hc hχc]
  have hp : 0 < pP x := pP_pos hx
  have hy : Cvs.L2a.QIdentityCutPoint.yN c χ x ≤ 51 / 40 := by
    unfold Cvs.L2a.QIdentityCutPoint.yN
    rw [Real.sqrt_le_left (by norm_num)]
    have h1 : (c ^ 2 - χ) / (c ^ 2 * (x ^ 2 - 1)) ≤ 10 / 16 := by
      rw [div_le_div_iff₀ (by unfold pP at hp; positivity) (by norm_num)]
      unfold pP at h16 hp
      nlinarith
    nlinarith
  nlinarith

/-- The `μ`-bound algebra, normalised. -/
theorem key_mu (c p y x : ℝ) (hc : c ≠ 0) (hp : p ≠ 0) (hy1 : y - 1 ≠ 0) (hy2 : y + 1 ≠ 0) :
    p * ((51 / 40 * c + c * y) / (c ^ 2 * p * (y ^ 2 - 1) / 2)
        + (2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y) * x / (c ^ 2 * p * (y ^ 2 - 1) / 2) ^ 2)
      = (2 * (51 / 40 + y) / (y + 1) + 8 * (x / (c * p)) / (y + 1)
          + 8 * (y / (y ^ 2 - 1)) * (x / (c * p)) / (c * (y + 1))) / (c * (y - 1)) := by
  have e : y ^ 2 - 1 = (y - 1) * (y + 1) := by ring
  rw [e]
  field_simp
  ring

/-- The `R`-bound algebra, normalised. -/
theorem key_R (c p u x y : ℝ) (hc : c ≠ 0) (hp : p ≠ 0) (hu : u ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    ((2 * x + 2 * (c * y) * p) * ((2 * c ^ 2 * u + 2 * c * y) * x) + p * (2 * c ^ 2 * u)) / (c ^ 2 * p * u / 2) ^ 2
        + 2 * p * ((2 * c ^ 2 * u + 2 * c * y) * x) ^ 2 / (c ^ 2 * p * u / 2) ^ 3
      = y * x / (c * p * u) * (16 + 80 * (x / (c * p)) / y + 144 * (x / (c * p)) / (c * u)
          + 16 * (y / u) / c + 8 / (c * y * x) + 64 * (y / u) * (x / (c * p)) / (c ^ 2 * u)) := by
  field_simp
  ring

/-- `|μ_cut(±k)| ≤ (5/2)/(c(y − 1))` for `c ≥ 80`, `σ² ≤ 10c`, `y ≥ 3/2`, `cp ≥ 16`, `w(x) ≤ 1/7`. -/
theorem norm_muQ_kP_le {c χ y x ξ : ℝ} (hc : 80 ≤ c) (hχc : χ < c ^ 2) (hσ : c ^ 2 - χ ≤ 10 * c)
    (hy : 3 / 2 ≤ y) (hx : 1 < x) (h16 : 16 ≤ c * pP x) (hw : Cvs.Prolate.BandMassLaw.wUp c x ≤ 1 / 7)
    (hξ : |ξ| = Cvs.Prolate.RungCauchySplit.kP c χ x) :
    ‖Cvs.L2a.QIdentityCutPoint.muCut c y x ξ‖ ≤ 5 / 2 / (c * (y - 1)) := by
  have hc0 : 0 < c := by linarith
  have hp : 0 < pP x := pP_pos hx
  have hu : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  have hQeq : Cvs.L2a.QIdentityCutPoint.qQk c y x ξ = qQ c χ y x := by
    rcases abs_eq (show 0 ≤ Cvs.Prolate.RungCauchySplit.kP c χ x from hξ ▸ abs_nonneg ξ) |>.1 hξ with h | h
    · rw [h, Cvs.L2a.QIdentityCutPoint.qQk_kP hx hc0 hχc]
    · rw [h, Cvs.L2a.QIdentityCutPoint.qQk_neg, Cvs.L2a.QIdentityCutPoint.qQk_kP hx hc0 hχc]
  set D := c ^ 2 * pP x * (y ^ 2 - 1) / 2 with hD
  have hD0 : 0 < D := by positivity
  have hQ := norm_qQ_ge hc0 hσ hy h16 (χ := χ)
  have hQ0 : 0 < ‖qQ c χ y x‖ := hD0.trans_le hQ
  have hk := kP_le hc0 hχc hσ hx h16
  have hQ1 := Cvs.L2a.FarIntegrationByParts.norm_qQ₁_le hc0 hx.le (by linarith : (1 : ℝ) ≤ y)
  have hX : x / (c * pP x) ≤ 1 / 14 := by
    unfold Cvs.Prolate.BandMassLaw.wUp at hw
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)] at hw
    linarith
  unfold Cvs.L2a.QIdentityCutPoint.muCut Cvs.L2a.QIdentityCutPoint.muQ
  rw [norm_mul, (continuous_eF c y).2 x, one_mul, hQeq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp]
  have t1 : ‖I * ((ξ - c * y : ℝ) : ℂ) / qQ c χ y x‖ ≤ (51 / 40 * c + c * y) / D := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have : |ξ - c * y| ≤ 51 / 40 * c + c * y := by
      have := abs_sub (ξ) (c * y)
      rw [abs_of_pos (by positivity : 0 < c * y)] at this
      linarith
    exact div_le_div₀ (by positivity) this hD0 hQ
  have t2 : ‖qQ₁ c y x / qQ c χ y x ^ 2‖ ≤ (2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y) * x / D ^ 2 := by
    rw [norm_div, norm_pow]
    exact div_le_div₀ (by positivity) hQ1 (by positivity) (pow_le_pow_left₀ hD0.le hQ 2)
  calc pP x * ‖I * ((ξ - c * y : ℝ) : ℂ) / qQ c χ y x + qQ₁ c y x / qQ c χ y x ^ 2‖
      ≤ pP x * ((51 / 40 * c + c * y) / D + (2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y) * x / D ^ 2) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add t1 t2)) hp.le
    _ = (2 * (51 / 40 + y) / (y + 1) + 8 * (x / (c * pP x)) / (y + 1)
          + 8 * (y / (y ^ 2 - 1)) * (x / (c * pP x)) / (c * (y + 1))) / (c * (y - 1)) := by
        rw [hD]
        exact key_mu c (pP x) y x hc0.ne' hp.ne' (by linarith) (by linarith)
    _ ≤ 5 / 2 / (c * (y - 1)) := by
        apply div_le_div_of_nonneg_right _ (by nlinarith)
        have hyu : y / (y ^ 2 - 1) ≤ 6 / 5 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
        have a1 : 2 * (51 / 40 + y) / (y + 1) ≤ 111 / 50 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
        have a2 : 8 * (x / (c * pP x)) / (y + 1) ≤ 8 * (1 / 14) / (5 / 2) := by
          apply div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by linarith)
        have a3 : 8 * (y / (y ^ 2 - 1)) * (x / (c * pP x)) / (c * (y + 1)) ≤ 8 * (6 / 5) * (1 / 14) / (80 * (5 / 2)) := by
          apply div_le_div₀ (by norm_num) _ (by norm_num) (by nlinarith)
          have h0 : 0 ≤ x / (c * pP x) := by positivity
          have h1 : 0 ≤ y / (y ^ 2 - 1) := by
            apply div_nonneg (by linarith) (by linarith)
          nlinarith [mul_le_mul hyu hX h0 (by norm_num)]
        norm_num at a2 a3 ⊢
        linarith

set_option maxHeartbeats 2000000 in
/-- `|R| ≤ (41/2)yx/(cp(y² − 1))` for `w ≡ 1`, `c ≥ 80`, `σ² ≤ 10c`, `y ≥ 3/2`, `cp ≥ 16`,
`w(x) ≤ 1/7`. -/
theorem norm_rRc_one_le {c χ y x : ℝ} (hc : 80 ≤ c) (hσ : c ^ 2 - χ ≤ 10 * c)
    (hy : 3 / 2 ≤ y) (hx : 1 < x) (h16 : 16 ≤ c * pP x) (hw : Cvs.Prolate.BandMassLaw.wUp c x ≤ 1 / 7) :
    ‖Cvs.L2a.QIdentityComplexWeight.rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y x‖
      ≤ 41 / 2 * y * x / (c * pP x * (y ^ 2 - 1)) := by
  have hc0 : 0 < c := by linarith
  have hp : 0 < pP x := pP_pos hx
  have hu : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  set u := y ^ 2 - 1 with hudef
  set D := c ^ 2 * pP x * u / 2 with hD
  have hD0 : 0 < D := by positivity
  have hQ := norm_qQ_ge hc0 hσ hy h16 (χ := χ)
  have hQ0 : 0 < ‖qQ c χ y x‖ := hD0.trans_le hQ
  have hQne : qQ c χ y x ≠ 0 := norm_pos_iff.1 hQ0
  have hQ1 := Cvs.L2a.FarIntegrationByParts.norm_qQ₁_le hc0 hx.le (by linarith : (1 : ℝ) ≤ y)
  have hQ2 := Cvs.L2a.QIdentityComplexWeight.norm_qQ₂_eq (c := c) (by linarith : (1 : ℝ) ≤ y)
  have hK := Cvs.L2a.QIdentityComplexWeight.norm_kK_le hc0.le (by linarith : (0 : ℝ) ≤ y) hx.le
  set q1 := (2 * c ^ 2 * u + 2 * c * y) * x with hq1
  have hQ1' : ‖qQ₁ c y x‖ ≤ q1 := hQ1
  have hq10 : 0 ≤ q1 := by positivity
  have h1 : ‖Cvs.L2a.QIdentityComplexWeight.aC₁ (fun _ => (0 : ℂ)) (fun _ => 0) c y x‖ = 0 := by
    unfold Cvs.L2a.QIdentityComplexWeight.aC₁; simp
  have h2 : ‖Cvs.L2a.QIdentityComplexWeight.aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖
      ≤ (2 * x + 2 * (c * y) * pP x) * q1 + pP x * (2 * c ^ 2 * u) := by
    have := Cvs.L2a.QIdentityComplexWeight.norm_aC₂_le (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0) hc0.le
      (by linarith : (0 : ℝ) ≤ y) hx.le (x := x)
    simp only [norm_one, mul_one, norm_zero, mul_zero, add_zero] at this
    rw [hQ2] at this
    refine this.trans ?_
    gcongr
  have h3 : ‖Cvs.L2a.QIdentityComplexWeight.aC₃ (fun _ => (1 : ℂ)) c y x‖ ≤ 2 * pP x * q1 ^ 2 := by
    rw [Cvs.L2a.QIdentityComplexWeight.norm_aC₃_eq hx.le]
    simp only [norm_one, mul_one]
    gcongr
  have hR := Cvs.L2a.QIdentityComplexWeight.norm_rRc_le (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0) (w₂ := fun _ => 0) hQne
  rw [h1, zero_div, zero_add] at hR
  refine hR.trans ?_
  have e2 : ‖Cvs.L2a.QIdentityComplexWeight.aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖ / ‖qQ c χ y x‖ ^ 2
      ≤ ((2 * x + 2 * (c * y) * pP x) * q1 + pP x * (2 * c ^ 2 * u)) / D ^ 2 :=
    div_le_div₀ (by positivity) h2 (by positivity) (pow_le_pow_left₀ hD0.le hQ 2)
  have e3 : ‖Cvs.L2a.QIdentityComplexWeight.aC₃ (fun _ => (1 : ℂ)) c y x‖ / ‖qQ c χ y x‖ ^ 3
      ≤ 2 * pP x * q1 ^ 2 / D ^ 3 :=
    div_le_div₀ (by positivity) h3 (by positivity) (pow_le_pow_left₀ hD0.le hQ 3)
  refine (add_le_add e2 e3).trans ?_
  have hX : x / (c * pP x) ≤ 1 / 14 := by
    unfold Cvs.Prolate.BandMassLaw.wUp at hw
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)] at hw
    linarith
  have hyu : y / u ≤ 6 / 5 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have hx1 : 1 ≤ x := hx.le
  have key := key_R c (pP x) u x y hc0.ne' hp.ne' (by linarith) (by linarith) (by linarith)
  rw [← hD, ← hq1] at key
  rw [key, show 41 / 2 * y * x / (c * pP x * u) = y * x / (c * pP x * u) * (41 / 2) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hX0 : 0 ≤ x / (c * pP x) := by positivity
  have hyu0 : 0 ≤ y / u := div_nonneg (by linarith) (by linarith)
  have b1 : 80 * (x / (c * pP x)) / y ≤ 80 * (1 / 14) / (3 / 2) :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) hy
  have b2 : 144 * (x / (c * pP x)) / (c * u) ≤ 144 * (1 / 14) / (80 * (5 / 4)) :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by nlinarith)
  have b3 : 16 * (y / u) / c ≤ 16 * (6 / 5) / 80 :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) hc
  have b4 : 8 / (c * y * x) ≤ 8 / (80 * (3 / 2) * 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by
      have := mul_le_mul hc hy (by norm_num) (by linarith)
      nlinarith)
  have b5 : 64 * (y / u) * (x / (c * pP x)) / (c ^ 2 * u) ≤ 64 * (6 / 5) * (1 / 14) / (80 ^ 2 * (5 / 4)) := by
    apply div_le_div₀ (by norm_num) _ (by norm_num) (by nlinarith)
    nlinarith [mul_le_mul hyu hX hX0 (by norm_num)]
  norm_num at b1 b2 b3 b4 b5 ⊢
  linarith

/-! ### The energy tail, the boundary term, the kernel integral -/

section tail
variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- The tail amplitude: for `t ≥ z > 1` with `w(z) ≤ 1/7`,
`√(E(t)/a(t)) ≤ (14/13)√(E∞/(c p(t)))`. -/
theorem rungAmp_tail_le
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) {z t : ℝ} (hz : 1 < z) (hzt : z ≤ t)
    (hw : Cvs.Prolate.BandMassLaw.wUp c z ≤ 1 / 7) :
    Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c χ g t
      ≤ 14 / 13 * √(Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g ^ 2 / c / (c * pP t)) := by
  obtain ⟨hψ, hu, -, -⟩ := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang
  have hE := Cvs.Prolate.RungConnectionIdentity.tendsto_energy hg hg₁ hg₂c hc hχ hχc
  have ht : 1 < t := lt_of_lt_of_le hz hzt
  have hw0 : 0 ≤ Cvs.Prolate.BandMassLaw.wUp c z := by
    unfold Cvs.Prolate.BandMassLaw.wUp; have := pP_pos hz; positivity
  have hEt := Cvs.Prolate.BandMassLaw.energy_le_of_ge hc hχ hχc hz hzt hψ (fun t _ => hu t) hE (by linarith)
  have ha := Cvs.Prolate.BandMassLaw.mul_pP_le_aP hc hχc.le ht
  have hp := pP_pos ht
  have ha0 : 0 < aP c χ t := lt_of_lt_of_le (by positivity) ha
  set E := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy (aP c χ) (psi c g) (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c g) t with hEdef
  have hE0 : 0 ≤ E := Cvs.Prolate.BandMassLaw.energy_nonneg ha0
  set Ei := Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g ^ 2 / c with hEi
  have hEi0 : 0 ≤ Ei := by positivity
  have hfac : Ei / (1 - Cvs.Prolate.BandMassLaw.wUp c z / 2) ^ 2 ≤ (14 / 13) ^ 2 * Ei := by
    rw [div_le_iff₀ (by nlinarith)]
    have h1 : 13 / 14 ≤ 1 - Cvs.Prolate.BandMassLaw.wUp c z / 2 := by linarith
    have h2 : (13 / 14) ^ 2 ≤ (1 - Cvs.Prolate.BandMassLaw.wUp c z / 2) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
    nlinarith
  unfold Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp
  rw [← hEdef]
  have hq : E / aP c χ t ≤ (14 / 13) ^ 2 * (Ei / (c * pP t)) := by
    calc E / aP c χ t ≤ (14 / 13) ^ 2 * Ei / (c * pP t) :=
          div_le_div₀ (by positivity) (hEt.trans hfac) (by positivity) ha
      _ = (14 / 13) ^ 2 * (Ei / (c * pP t)) := by ring
  calc √(E / aP c χ t) ≤ √((14 / 13) ^ 2 * (Ei / (c * pP t))) := Real.sqrt_le_sqrt hq
    _ = 14 / 13 * √(Ei / (c * pP t)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- The boundary term: `|S[μ_cut](z)| ≤ (5/(c(y − 1)))·(7/13)√(E∞/(c p(z)))`. -/
theorem norm_smp_le
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hσ : c ^ 2 - χ ≤ 10 * c) {y z : ℝ} (hy : 3 / 2 ≤ y)
    (hz : 1 < z) (h16 : 16 ≤ c * pP z) (hw : Cvs.Prolate.BandMassLaw.wUp c z ≤ 1 / 7) :
    ‖Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c y z) c χ g z‖
      ≤ 5 / (c * (y - 1)) * (7 / 13 * √(Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g ^ 2 / c / (c * pP z))) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 ≤ Cvs.Prolate.RungCauchySplit.kP c χ z := by
    unfold Cvs.Prolate.RungCauchySplit.kP
    exact div_nonneg (Real.sqrt_nonneg _) (pP_pos hz).le
  have m1 := norm_muQ_kP_le hc hχc hσ hy hz h16 hw (ξ := Cvs.Prolate.RungCauchySplit.kP c χ z) (abs_of_nonneg hk0)
  have m2 := norm_muQ_kP_le hc hχc hσ hy hz h16 hw (ξ := -Cvs.Prolate.RungCauchySplit.kP c χ z)
    (by rw [abs_neg, abs_of_nonneg hk0])
  have hpp : ‖Cvs.Prolate.RungCauchySplit.psiP c χ g z‖ ≤ 7 / 13 * √(Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g ^ 2 / c / (c * pP z)) := by
    rw [Cvs.Prolate.RungCauchySplit.norm_psiP hz hc0 hχc]
    have := rungAmp_tail_le hg hg₁ hg₂c hang hc0 hχ hχc hz le_rfl hw
    linarith
  unfold Cvs.L2a.BandTransferBandForm.smp
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have hy1 : 0 < c * (y - 1) := by nlinarith
  calc ‖Cvs.L2a.QIdentityCutPoint.muCut c y z (Cvs.Prolate.RungCauchySplit.kP c χ z)‖ * ‖Cvs.Prolate.RungCauchySplit.psiP c χ g z‖
        + ‖Cvs.L2a.QIdentityCutPoint.muCut c y z (-Cvs.Prolate.RungCauchySplit.kP c χ z)‖ * ‖Cvs.Prolate.RungCauchySplit.psiP c χ g z‖
      ≤ 5 / 2 / (c * (y - 1)) * ‖Cvs.Prolate.RungCauchySplit.psiP c χ g z‖
        + 5 / 2 / (c * (y - 1)) * ‖Cvs.Prolate.RungCauchySplit.psiP c χ g z‖ := by gcongr
    _ = 5 / (c * (y - 1)) * ‖Cvs.Prolate.RungCauchySplit.psiP c χ g z‖ := by ring
    _ ≤ _ := by gcongr

end tail

/-- `∫_z^Z t/((t² − 1)√(t² − 1)) dt = 1/√(z² − 1) − 1/√(Z² − 1)`. -/
theorem integral_tail_kernel {z Z : ℝ} (hz : 1 < z) (hzZ : z ≤ Z) :
    ∫ t in z..Z, t / ((t ^ 2 - 1) * √(t ^ 2 - 1)) = 1 / √(z ^ 2 - 1) - 1 / √(Z ^ 2 - 1) := by
  have hd : ∀ t ∈ uIcc z Z, HasDerivAt (fun t => -(1 / √(t ^ 2 - 1))) (t / ((t ^ 2 - 1) * √(t ^ 2 - 1))) t := by
    intro t ht
    rw [uIcc_of_le hzZ] at ht
    have hp : 0 < t ^ 2 - 1 := by nlinarith [ht.1]
    have hs : 0 < √(t ^ 2 - 1) := Real.sqrt_pos.2 hp
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).sub_const 1
    have h2 := h1.sqrt hp.ne'
    have h3 := (h2.inv hs.ne').neg
    refine (h3.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => by simp [one_div])
    rw [Real.sq_sqrt hp.le]
    field_simp
  have hcont : ContinuousOn (fun t => t / ((t ^ 2 - 1) * √(t ^ 2 - 1))) (uIcc z Z) := by
    rw [uIcc_of_le hzZ]
    have hden : ContinuousOn (fun t : ℝ => (t ^ 2 - 1) * √(t ^ 2 - 1)) (Icc z Z) := by fun_prop
    refine ContinuousOn.div₀ (f := fun t : ℝ => t) (g := fun t : ℝ => (t ^ 2 - 1) * √(t ^ 2 - 1))
      continuousOn_id hden fun t ht => ?_
    have hp : 0 < t ^ 2 - 1 := by nlinarith [ht.1]
    exact mul_ne_zero hp.ne' (Real.sqrt_pos.2 hp).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)]
  ring

/-- `1/√(Z² − 1) → 0`. -/
theorem tendsto_inv_sqrt_sq_sub_one : Tendsto (fun Z : ℝ => 1 / √(Z ^ 2 - 1)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun Z : ℝ => Z ^ 2 - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun Z : ℝ => √(Z ^ 2 - 1)) atTop atTop := Real.tendsto_sqrt_atTop.comp h1
  refine (h2.inv_tendsto_atTop).congr fun Z => ?_
  simp [one_div]

/-- Stieltjes decay: `|Fs(y, z)| ≤ 25|A|/(c(y − 1)√(z² − 1))`, `A = g(1) + g(−1)`, for an even angular rung
with `0 ≤ χ < c²`, `c² − χ ≤ 10c`, `c ≥ 80`, `y ≥ 3/2` and `c(z² − 1) ≥ 16`. -/
theorem norm_fsZ_le {g g₁ g₂ : ℝ → ℝ} {c χ y z : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hσ : c ^ 2 - χ ≤ 10 * c) (hy : 3 / 2 ≤ y) (hz : 1 < z) (h16 : 16 ≤ c * (z ^ 2 - 1)) :
    ‖fsZ c g y z‖ ≤ 25 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / (c * (y - 1) * √(z ^ 2 - 1)) := by
  have hc0 : 0 < c := by linarith
  have hgc : ContinuousOn g (Icc (-1) 1) := Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt hg
  have h16' : 16 ≤ c * pP z := h16
  have hw := wUp_le_seventh hc hz h16
  have hu : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  have hy1 : 0 < y - 1 := by linarith
  have hpz : 0 < z ^ 2 - 1 := by nlinarith
  have hsz : 0 < √(z ^ 2 - 1) := Real.sqrt_pos.2 hpz
  set A := Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g ^ 2 / c with hA
  set S := √(A / c) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set u := y ^ 2 - 1 with hudef
  set Kint := 14 / 13 * (41 / 2) * (y / (c * u)) * S with hKint
  have hKint0 : 0 ≤ Kint := by positivity
  -- pointwise bound on the remainder integrand
  have hpt : ∀ t, z ≤ t → ‖eF c y t * (psi c g t : ℂ)
        * Cvs.L2a.QIdentityComplexWeight.rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y t‖
      ≤ Kint * (t / ((t ^ 2 - 1) * √(t ^ 2 - 1))) := by
    intro t hzt
    have ht : 1 < t := lt_of_lt_of_le hz hzt
    have hpt0 : 0 < t ^ 2 - 1 := by nlinarith
    have hst : 0 < √(t ^ 2 - 1) := Real.sqrt_pos.2 hpt0
    have h16t : 16 ≤ c * pP t := by
      unfold pP at h16' ⊢; nlinarith
    have hwt : Cvs.Prolate.BandMassLaw.wUp c t ≤ 1 / 7 := (Cvs.Prolate.BandMassLaw.wUp_le_wUp hc0 hz hzt).trans hw
    have hR := norm_rRc_one_le hc hσ hy ht h16t hwt (χ := χ)
    have hψ := (Cvs.Prolate.Envelope.RungCountEnvelope.abs_psi_le_rungAmp ht hc0 hχc (g := g)).trans
      (rungAmp_tail_le hg hg₁ hg₂c hang hc0 hχ hχc hz hzt hw)
    rw [norm_mul, norm_mul, (continuous_eF c y).2 t, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsq : √(A / (c * pP t)) = S / √(t ^ 2 - 1) := by
      rw [hS, show A / (c * pP t) = (A / c) / (t ^ 2 - 1) by unfold pP; field_simp,
        Real.sqrt_div' _ hpt0.le]
    rw [hsq] at hψ
    calc |psi c g t| * ‖Cvs.L2a.QIdentityComplexWeight.rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y t‖
        ≤ 14 / 13 * (S / √(t ^ 2 - 1)) * (41 / 2 * y * t / (c * pP t * u)) :=
          mul_le_mul hψ hR (norm_nonneg _) (by positivity)
      _ = Kint * (t / ((t ^ 2 - 1) * √(t ^ 2 - 1))) := by
          rw [hKint]; unfold pP; field_simp
  -- the boundary term at any point `≥ z`
  have hB : ∀ t, z ≤ t → ‖Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c y t) c χ g t‖
      ≤ 35 / 13 * S / (c * (y - 1) * √(t ^ 2 - 1)) := by
    intro t hzt
    have ht : 1 < t := lt_of_lt_of_le hz hzt
    have hpt0 : 0 < t ^ 2 - 1 := by nlinarith
    have h16t : 16 ≤ c * pP t := by unfold pP at h16' ⊢; nlinarith
    have hwt : Cvs.Prolate.BandMassLaw.wUp c t ≤ 1 / 7 := (Cvs.Prolate.BandMassLaw.wUp_le_wUp hc0 hz hzt).trans hw
    refine (norm_smp_le hg hg₁ hg₂c hang hc hχ hχc hσ hy ht h16t hwt).trans (le_of_eq ?_)
    rw [show A / (c * pP t) = (A / c) / (t ^ 2 - 1) by unfold pP; field_simp, Real.sqrt_div' _ hpt0.le, ← hS]
    field_simp
    ring
  -- the identity on `[z, Z]` and the bound for every `Z ≥ z`
  have hall : ∀ Z, z ≤ Z → ‖fsZ c g y z‖
      ≤ (‖fsZ c g y Z‖ + 35 / 13 * S / ((y - 1) * √(Z ^ 2 - 1)))
        + (c * (Kint / √(z ^ 2 - 1)) + 35 / 13 * S / ((y - 1) * √(z ^ 2 - 1))) := by
    intro Z hzZ
    have hid := fsZ_identity hg hg₁ hg₂c hang heven hc0 hχc (by linarith : 1 < y) hz hzZ (χ := χ)
    have hint : ‖∫ t in z..Z, eF c y t * (psi c g t : ℂ)
          * Cvs.L2a.QIdentityComplexWeight.rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y t‖
        ≤ Kint / √(z ^ 2 - 1) := by
      have hcont : ContinuousOn (fun t => t / ((t ^ 2 - 1) * √(t ^ 2 - 1))) (uIcc z Z) := by
        rw [uIcc_of_le hzZ]
        have hden : ContinuousOn (fun t : ℝ => (t ^ 2 - 1) * √(t ^ 2 - 1)) (Icc z Z) := by fun_prop
        refine ContinuousOn.div₀ (f := fun t : ℝ => t) (g := fun t : ℝ => (t ^ 2 - 1) * √(t ^ 2 - 1))
          continuousOn_id hden fun t ht => ?_
        have hp : 0 < t ^ 2 - 1 := by nlinarith [ht.1]
        exact mul_ne_zero hp.ne' (Real.sqrt_pos.2 hp).ne'
      refine (intervalIntegral.norm_integral_le_of_norm_le hzZ
        (Filter.Eventually.of_forall fun t ht => hpt t ht.1.le)
        ((hcont.intervalIntegrable).const_mul Kint)).trans ?_
      rw [intervalIntegral.integral_const_mul, integral_tail_kernel hz hzZ]
      have : 0 ≤ 1 / √(Z ^ 2 - 1) := by positivity
      have e : Kint / √(z ^ 2 - 1) = Kint * (1 / √(z ^ 2 - 1)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) hKint0
    have h1 : ‖fsZ c g y z‖ = ‖eF c y z * fsZ c g y z‖ := by
      rw [norm_mul, (continuous_eF c y).2 z, one_mul]
    rw [h1, hid]
    have hBZ := hB Z hzZ
    have hBz := hB z le_rfl
    have hcy : 0 < c * (y - 1) := by positivity
    calc ‖eF c y Z * fsZ c g y Z - I * ↑c * ((∫ t in z..Z, eF c y t * (psi c g t : ℂ)
            * Cvs.L2a.QIdentityComplexWeight.rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y t)
          + Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c y Z) c χ g Z
          - Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c y z) c χ g z)‖
        ≤ ‖fsZ c g y Z‖ + c * (Kint / √(z ^ 2 - 1) + 35 / 13 * S / (c * (y - 1) * √(Z ^ 2 - 1))
            + 35 / 13 * S / (c * (y - 1) * √(z ^ 2 - 1))) := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, (continuous_eF c y).2 Z, one_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
          gcongr
          refine (norm_sub_le _ _).trans ?_
          refine add_le_add ((norm_add_le _ _).trans (add_le_add hint hBZ)) hBz
      _ = _ := by field_simp; ring
  -- let `Z → ∞`
  have hT : Tendsto (fun Z => (‖fsZ c g y Z‖ + 35 / 13 * S / ((y - 1) * √(Z ^ 2 - 1)))
        + (c * (Kint / √(z ^ 2 - 1)) + 35 / 13 * S / ((y - 1) * √(z ^ 2 - 1)))) atTop
      (𝓝 ((0 + 35 / 13 * S / (y - 1) * 0) + (c * (Kint / √(z ^ 2 - 1)) + 35 / 13 * S / ((y - 1) * √(z ^ 2 - 1))))) := by
    refine Tendsto.add (Tendsto.add ?_ ?_) tendsto_const_nhds
    · simpa using (tendsto_fsZ hc0 hgc (by linarith : 1 < y)).norm
    · have := tendsto_inv_sqrt_sq_sub_one.const_mul (35 / 13 * S / (y - 1))
      refine this.congr fun Z => ?_
      field_simp
  have hle := ge_of_tendsto hT (Filter.eventually_atTop.2 ⟨z, fun Z hZ => hall Z hZ⟩)
  -- the constant
  have hSa : S = |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / c := by
    rw [hS, hA, show Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g ^ 2 / c / c = (Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g / c) ^ 2 by
      field_simp, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hc0]
  have hyu : y * (y - 1) / u ≤ 1 := by
    rw [div_le_one (by linarith)]; nlinarith
  have hyu0 : 0 ≤ y * (y - 1) / u := div_nonneg (by nlinarith) (by linarith)
  have hab : 0 ≤ |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| := abs_nonneg _
  calc ‖fsZ c g y z‖
      ≤ (0 + 35 / 13 * S / (y - 1) * 0) + (c * (Kint / √(z ^ 2 - 1)) + 35 / 13 * S / ((y - 1) * √(z ^ 2 - 1))) := hle
    _ = (14 / 13 * (41 / 2) * (y * (y - 1) / u) + 35 / 13) * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g|
          / (c * (y - 1) * √(z ^ 2 - 1)) := by
        rw [hKint, hSa]
        have hu0 : u ≠ 0 := by linarith
        field_simp
        ring
    _ ≤ 25 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / (c * (y - 1) * √(z ^ 2 - 1)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hab
        nlinarith

end Cvs.Prolate.RungStieltjesDecay
