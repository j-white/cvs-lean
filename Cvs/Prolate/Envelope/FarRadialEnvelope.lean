import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Envelope.EnergyFromReferencePoint
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.RungConnectionIdentity
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The far radial envelope keeps the factor `1/c`

Past `ξ = 2` the Liouville–Green energy bound `E ≤ 48eψ(1)²` (Cvs.Prolate.Envelope.EnergyFromReferencePoint, Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi) and `a ≥ c(ξ² − 1) ≥ (3/4)cξ²` (Cvs.Prolate.RungConnectionIdentity) give
`ψ(ξ)² ≤ 64eψ(1)²/(cξ²)`: the far amplitude is `√(64e/c)|ψ(1)|`, a factor `√c` below the edge envelope of Cvs.Prolate.LowRungRadialTailEdge.
So the dilates `m ≥ 2` of the full tail have diagonal at most `(π²/6 − 1)·64eψ(1)²/c`.
-/

noncomputable section

open Real Set MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SlepianCommutingRelation (kint)

namespace Cvs.Prolate.Envelope.FarRadialEnvelope

/-- **The far envelope**: `ψ(ξ)² ≤ 64eψ(1)²/(cξ²)` for `ξ ≥ 2`, `0 ≤ χ ≤ (2/5)c²`, `c ≥ 100`. -/
theorem sq_psi_far_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) {ξ : ℝ} (h2 : 2 ≤ ξ) :
    psi c g ξ ^ 2 ≤ 64 * exp 1 * psi c g 1 ^ 2 / (c * ξ ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hχc : χ < c ^ 2 := by nlinarith
  obtain ⟨hψ, hv, hode⟩ := Cvs.L2a.AngularProlateTailPositive.psi_system hg hg₁ hg₂c hang
  set v := kint g (fun ξ s => -(c * s * sin (c * ξ * s)))
  set v' := kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s)))
  set ψ := psi c g
  have hξ0 : 0 < ξ := by linarith
  have hξ : 1 ≤ ξ := by linarith
  -- Liouville–Green beyond `2`
  set ξ₀ : ℝ := 1 + 1 / c ^ 2 with hξ₀
  have he : 0 < 1 / c ^ 2 := by positivity
  have h1ξ₀ : 1 < ξ₀ := by linarith
  have hξ₀2 : ξ₀ ≤ 2 := by
    have : 1 / c ^ 2 ≤ 1 := by rw [div_le_one hc2]; nlinarith
    linarith
  set Ξ := ξ with hΞ
  obtain ⟨hpq1, hpq3⟩ := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.pq_bounds hc hχ0 hχ
  obtain ⟨ha1, ha2⟩ := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.a_bounds hc hχ0 hχ
  have hw1 := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.w_le hc hχ0 hχ
  have hfac := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.fac_le hc hχ0 hχ
  have hedge := Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi.edge_const_le hc hχ0 hχ
  have hsup := Cvs.Prolate.Envelope.EnergyFromReferencePoint.energy_sup_le (Ξ := Ξ) (ψ := ψ) (v := v) (v' := v') hc0 hχ0 hχc
    (fun r _ => hψ r) (fun r _ => hv r) (fun r _ => hode r) h1ξ₀ (by linarith) (by linarith) (by linarith)
    ξ ⟨by linarith, le_rfl⟩
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
  have haξ := aP_pos (by linarith : 1 < ξ) hc2 hχc
  have hsq := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.sq_le_energy_div (ψ := ψ) (u := fun r => pP r * v r) haξ
  have hfar := Cvs.Prolate.RungConnectionIdentity.le_aP_far hχc.le hξ
  have hξ2 : 3 / 4 * ξ ^ 2 ≤ ξ ^ 2 - 1 := by nlinarith
  have hlow : c * (3 / 4 * ξ ^ 2) ≤ aP c χ ξ := le_trans (mul_le_mul_of_nonneg_left hξ2 hc0.le) hfar
  have h1 : ψ ξ ^ 2 ≤ 48 * exp 1 * ψ 1 ^ 2 / aP c χ ξ :=
    hsq.trans (div_le_div_of_nonneg_right hEξ haξ.le)
  have h2' : 48 * exp 1 * ψ 1 ^ 2 / aP c χ ξ ≤ 48 * exp 1 * ψ 1 ^ 2 / (c * (3 / 4 * ξ ^ 2)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
  have e : 48 * exp 1 * ψ 1 ^ 2 / (c * (3 / 4 * ξ ^ 2)) = 64 * exp 1 * ψ 1 ^ 2 / (c * ξ ^ 2) := by
    field_simp; ring
  linarith

end Cvs.Prolate.Envelope.FarRadialEnvelope
