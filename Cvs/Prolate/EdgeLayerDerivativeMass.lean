import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Envelope.EnergyFromReferencePoint
import Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge layer's derivative mass: `∫_1^2 |ψ′| ≤ 4·2^{−3/4}√(96ec)|ψ(1)|`

On `(1, 2]` the Liouville–Green energy is at most `48eψ(1)²` (Cvs.Prolate.Envelope.EnergyFromReferencePoint from the edge, Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi), so `u = (ξ² − 1)ψ′` has
`u² ≤ aE`, and `a ≤ 2c√(ξ² − 1)` gives `|ψ′| ≤ √(96ec)|ψ(1)|(ξ² − 1)^{−3/4} ≤ 2^{−3/4}√(96ec)|ψ(1)|(ξ − 1)^{−3/4}`,
whose integral over `(1, 2)` is `4·2^{−3/4}√(96ec)|ψ(1)|`: the `A₁ ~ √c|ψ(1)|` of an earlier result.
-/

noncomputable section

open Real Set MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SlepianCommutingRelation (kint)

namespace Cvs.Prolate.EdgeLayerDerivativeMass

/-- **The edge energy**: `E(ξ) ≤ 48eψ(1)²` for `1 < ξ ≤ 2`. -/
theorem energy_edge_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) {ξ : ℝ} (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2) :
    energy (aP c χ) (psi c g) (fun r => pP r * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) r) ξ
      ≤ 48 * exp 1 * psi c g 1 ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hχc : χ < c ^ 2 := by nlinarith
  obtain ⟨hψ, hv, hode⟩ := Cvs.L2a.AngularProlateTailPositive.psi_system hg hg₁ hg₂c hang
  set v := kint g (fun ξ s => -(c * s * sin (c * ξ * s)))
  set v' := kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s)))
  set ψ := psi c g
  have hξ0 : 0 < ξ := by linarith
  have hξ : 1 ≤ ξ := hξ1.le
  -- Liouville–Green beyond `2`
  set ξ₀ : ℝ := 1 + 1 / c ^ 2 with hξ₀
  have he : 0 < 1 / c ^ 2 := by positivity
  have h1ξ₀ : 1 < ξ₀ := by linarith
  have hξ₀2 : ξ₀ ≤ 2 := by
    have : 1 / c ^ 2 ≤ 1 := by rw [div_le_one hc2]; nlinarith
    linarith
  set Ξ : ℝ := 2 with hΞ
  obtain ⟨hpq1, hpq3⟩ := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.pq_bounds hc hχ0 hχ
  obtain ⟨ha1, ha2⟩ := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.a_bounds hc hχ0 hχ
  have hw1 := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.w_le hc hχ0 hχ
  have hfac := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.fac_le hc hχ0 hχ
  have hedge := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.edge_const_le hc hχ0 hχ
  have hsup := Cvs.Prolate.Envelope.EnergyFromReferencePoint.energy_sup_le (Ξ := Ξ) (ψ := ψ) (v := v) (v' := v') hc0 hχ0 hχc
    (fun r _ => hψ r) (fun r _ => hv r) (fun r _ => hode r) h1ξ₀ (by linarith) (by linarith) (by linarith)
    ξ ⟨hξ1, hξ2⟩
  have hE0 := Cvs.Prolate.Envelope.EnergyFromReferencePoint.energy_le_edge (Ξ := Ξ) (ψ := ψ) (v := v) (v' := v') hc2 hχc
    ⟨h1ξ₀, by linarith⟩ (fun r _ => hψ r) (fun r _ => hv r) (fun r _ => hode r)
  set E0 := energy (aP c χ) ψ (fun r => pP r * v r) ξ₀
  have hE00 : 0 ≤ E0 := by
    have hapos := aP_pos h1ξ₀ hc2 hχc
    exact le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := fun r => pP r * v r) hapos)
  have he1 : (0 : ℝ) < exp 1 := exp_pos 1
  have hM : max (aP c χ ξ₀ * (Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / (aP c χ ξ₀ * (1 - pP ξ₀ * qP c χ ξ₀ / 4))))
      (Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀) ≤ 24 * exp 1 := by
    refine max_le ?_ (by linarith)
    have hfac0 : 0 ≤ Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / (aP c χ ξ₀ * (1 - pP ξ₀ * qP c χ ξ₀ / 4)) := by
      have : 0 < Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ := by
        unfold Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac
        have := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.w_pos hc hχ
        have : wP c χ ξ₀ / 2 < 1 := by linarith
        apply mul_pos (div_pos (by linarith) (by linarith)) (exp_pos _)
      exact div_nonneg this.le (mul_nonneg (by linarith) (by linarith))
    nlinarith [mul_le_mul ha2 hedge hfac0 (by norm_num)]
  have hEξ : energy (aP c χ) ψ (fun r => pP r * v r) ξ ≤ 48 * exp 1 * ψ 1 ^ 2 := by
    have hM0 : 0 ≤ max (aP c χ ξ₀ * (Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / (aP c χ ξ₀ * (1 - pP ξ₀ * qP c χ ξ₀ / 4))))
        (Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀) := le_trans (by
          unfold Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac
          have := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.w_pos hc hχ
          have : wP c χ ξ₀ / 2 < 1 := by linarith
          exact (mul_pos (div_pos (by linarith) (by linarith)) (exp_pos _)).le) (le_max_right _ _)
    calc _ ≤ _ := hsup
      _ ≤ 24 * exp 1 * (aP c χ ξ₀ * ψ 1 ^ 2) := mul_le_mul hM hE0 hE00 (by positivity)
      _ ≤ 24 * exp 1 * (2 * ψ 1 ^ 2) := by gcongr
      _ = 48 * exp 1 * ψ 1 ^ 2 := by ring
  exact hEξ

/-- **The derivative's edge envelope**: `|ψ′(ξ)| ≤ 2^{−3/4}√(96ec)|ψ(1)|(ξ − 1)^{−3/4}` for `1 < ξ ≤ 2`. -/
theorem abs_deriv_edge_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) {ξ : ℝ} (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2) :
    |kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ|
      ≤ 2 ^ (-(3 / 4) : ℝ) * √(96 * exp 1 * c) * |psi c g 1| * (ξ - 1) ^ (-(3 / 4) : ℝ) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hχc : χ < c ^ 2 := by nlinarith
  set v := kint g (fun ξ s => -(c * s * sin (c * ξ * s)))
  have hE := energy_edge_le hg hg₁ hg₂c hang hc hχ0 hχ hξ1 hξ2
  have ha := aP_pos (c := c) (χ := χ) hξ1 hc2 hχc
  have hp0 : 0 < pP ξ := by unfold pP; nlinarith
  have hp2 : 2 * (ξ - 1) ≤ pP ξ := by unfold pP; nlinarith
  have hau : aP c χ ξ ≤ 2 * c * √(pP ξ) := by
    unfold aP
    rw [show 2 * c * √(pP ξ) = √((2 * c) ^ 2 * pP ξ) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have hξsq : ξ ^ 2 ≤ 4 := by nlinarith
    have : qP c χ ξ ≤ (2 * c) ^ 2 := by unfold qP; nlinarith [mul_le_mul_of_nonneg_left hξsq hc2.le]
    nlinarith [mul_le_mul_of_nonneg_left this hp0.le]
  -- `(pψ′)² ≤ aE`
  have hu : (pP ξ * v ξ) ^ 2 ≤ aP c χ ξ * (48 * exp 1 * psi c g 1 ^ 2) := by
    have h0 : 0 ≤ aP c χ ξ * psi c g ξ ^ 2 := by positivity
    have e : energy (aP c χ) (psi c g) (fun r => pP r * v r) ξ
        = aP c χ ξ * psi c g ξ ^ 2 + (pP ξ * v ξ) ^ 2 / aP c χ ξ := rfl
    rw [e] at hE
    have h1 : (pP ξ * v ξ) ^ 2 / aP c χ ξ ≤ 48 * exp 1 * psi c g 1 ^ 2 := by linarith
    rw [div_le_iff₀ ha] at h1; linarith
  -- in rpow form
  set K := √(96 * exp 1 * c) * |psi c g 1| with hK
  have hK0 : 0 ≤ K := by positivity
  have hsq : v ξ ^ 2 * pP ξ ^ 2 ≤ K ^ 2 * √(pP ξ) := by
    have := hu.trans (mul_le_mul_of_nonneg_right hau (by positivity))
    rw [hK, mul_pow, Real.sq_sqrt (by positivity), sq_abs]
    nlinarith [this]
  -- `|v| ≤ K p^{−3/4}`
  have hv : |v ξ| ≤ K * pP ξ ^ (-(3 / 4) : ℝ) := by
    have hpr : pP ξ ^ (-(3 / 4) : ℝ) * pP ξ ^ (3 / 4 : ℝ) = 1 := by
      rw [← rpow_add hp0]; norm_num
    have hp34 : (pP ξ ^ (3 / 4 : ℝ)) ^ 2 = pP ξ ^ 2 / √(pP ξ) := by
      rw [← rpow_natCast, ← rpow_mul hp0.le, Real.sqrt_eq_rpow, ← rpow_natCast, ← rpow_sub hp0]; norm_num
    have hpos : 0 < pP ξ ^ (3 / 4 : ℝ) := rpow_pos_of_pos hp0 _
    have h1 : (|v ξ| * pP ξ ^ (3 / 4 : ℝ)) ^ 2 ≤ K ^ 2 := by
      rw [mul_pow, sq_abs, hp34, ← mul_div_assoc, div_le_iff₀ (Real.sqrt_pos.2 hp0)]
      exact hsq
    have h2 : |v ξ| * pP ξ ^ (3 / 4 : ℝ) ≤ K := abs_le_of_sq_le_sq' h1 hK0 |>.2 |> fun h => by
      nlinarith [abs_nonneg (v ξ), hpos, sq_nonneg (|v ξ| * pP ξ ^ (3 / 4 : ℝ) - K),
        abs_le_of_sq_le_sq' h1 hK0]
    calc |v ξ| = |v ξ| * pP ξ ^ (3 / 4 : ℝ) * pP ξ ^ (-(3 / 4) : ℝ) := by
          rw [mul_assoc, mul_comm (pP ξ ^ (3 / 4 : ℝ)), hpr, mul_one]
      _ ≤ K * pP ξ ^ (-(3 / 4) : ℝ) := mul_le_mul_of_nonneg_right h2 (rpow_nonneg hp0.le _)
  -- `p^{−3/4} ≤ (2(ξ − 1))^{−3/4}`
  have hmono : pP ξ ^ (-(3 / 4) : ℝ) ≤ (2 * (ξ - 1)) ^ (-(3 / 4) : ℝ) :=
    rpow_le_rpow_of_nonpos (by linarith) hp2 (by norm_num)
  have hsplit : (2 * (ξ - 1)) ^ (-(3 / 4) : ℝ) = 2 ^ (-(3 / 4) : ℝ) * (ξ - 1) ^ (-(3 / 4) : ℝ) :=
    mul_rpow (by norm_num) (by linarith)
  calc |v ξ| ≤ K * pP ξ ^ (-(3 / 4) : ℝ) := hv
    _ ≤ K * (2 * (ξ - 1)) ^ (-(3 / 4) : ℝ) := mul_le_mul_of_nonneg_left hmono hK0
    _ = _ := by rw [hsplit, hK]; ring

/-- **The edge layer's derivative mass**: `∫_1^2 |ψ′| ≤ 4·2^{−3/4}√(96ec)|ψ(1)|`. -/
theorem integral_abs_deriv_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) :
    ∫ ξ in (1 : ℝ)..2, |kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ|
      ≤ 4 * (2 ^ (-(3 / 4) : ℝ) * √(96 * exp 1 * c) * |psi c g 1|) := by
  obtain ⟨hψ, hv, -⟩ := Cvs.L2a.AngularProlateTailPositive.psi_system hg hg₁ hg₂c hang
  set v := kint g (fun ξ s => -(c * s * sin (c * ξ * s)))
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun ξ => (hv ξ).continuousAt
  set K := 2 ^ (-(3 / 4) : ℝ) * √(96 * exp 1 * c) * |psi c g 1| with hK
  have hmaj : IntervalIntegrable (fun ξ : ℝ => K * (ξ - 1) ^ (-(3 / 4) : ℝ)) volume 1 2 := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 1 - 1) (b := 2 - 1) (r := (-(3 / 4) : ℝ))
      (by norm_num)).comp_sub_right 1
    simpa using h.const_mul K
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) (hvc.abs.intervalIntegrable 1 2) hmaj
    fun ξ hξ => abs_deriv_edge_le hg hg₁ hg₂c hang hc hχ0 hχ hξ.1 hξ.2.le
  have hval : ∫ ξ in (1 : ℝ)..2, K * (ξ - 1) ^ (-(3 / 4) : ℝ) = 4 * K := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right (fun x => x ^ (-(3 / 4) : ℝ)),
      integral_rpow (Or.inl (by norm_num))]
    norm_num; ring
  linarith

end Cvs.Prolate.EdgeLayerDerivativeMass
