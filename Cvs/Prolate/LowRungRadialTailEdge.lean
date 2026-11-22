import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.Prolate.Envelope.EnergyFromReferencePoint
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.LiouvilleGreen.LGFactorsLowChi
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.SoninFunction
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
# The radial tail of a low rung is its edge value: `∫₁^∞ψ² ≤ 4ψ(1)²`

For `0 ≤ χ ≤ (2/5)c²`, `c ≥ 100`, `LGFactorsLowChi`'s factors at `ξ₀ = 1 + 1/c²` and Cvs.Prolate.Envelope.EnergyFromReferencePoint bound the Liouville–Green energy by
`48e·ψ(1)²` on all of `(1, ∞)`; with `a ≥ c(ξ² − 1)` (Cvs.Prolate.RungConnectionIdentity) and Sonin's `ψ² ≤ ψ(1)²` near the edge,
`|ψ(ξ)| ≤ 2|ψ(1)|/ξ` for `ξ ≥ 1`.
-/

noncomputable section

open Real Set MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SlepianCommutingRelation (kint)

namespace Cvs.Prolate.LowRungRadialTailEdge

/-- **The radial envelope**: `|ψ(ξ)| ≤ 2|ψ(1)|/ξ` for `ξ ≥ 1`. -/
theorem abs_psi_le_edge {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) {ξ : ℝ} (hξ : 1 ≤ ξ) :
    |psi c g ξ| ≤ 2 * |psi c g 1| / ξ := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hχc : χ < c ^ 2 := by nlinarith
  obtain ⟨hψ, hv, hode⟩ := Cvs.L2a.AngularProlateTailPositive.psi_system hg hg₁ hg₂c hang
  set v := kint g (fun ξ s => -(c * s * sin (c * ξ * s)))
  set v' := kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s)))
  set ψ := psi c g
  have hξ0 : 0 < ξ := by linarith
  rw [le_div_iff₀ hξ0]
  -- Sonin on `[1, 2]`
  have hsonin : ∀ t ∈ Icc (1 : ℝ) 2, ψ t ^ 2 ≤ ψ 1 ^ 2 := fun t ht =>
    Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge (ξ₁ := 2) hχc ht (fun r _ => hψ r) (fun r _ => hv r) (fun r _ => hode r)
  rcases le_or_gt ξ 2 with h2 | h2
  · have hs := hsonin ξ ⟨hξ, h2⟩
    have habs : |ψ ξ| ≤ |ψ 1| := by
      have h := sq_le_sq.mp hs
      simpa using h
    nlinarith [abs_nonneg (ψ 1)]
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
  have hψ2 : ψ ξ ^ 2 ≤ 4 * ψ 1 ^ 2 / ξ ^ 2 := by
    have h1 : ψ ξ ^ 2 ≤ 48 * exp 1 * ψ 1 ^ 2 / aP c χ ξ :=
      hsq.trans (div_le_div_of_nonneg_right hEξ haξ.le)
    have h2 : 48 * exp 1 * ψ 1 ^ 2 / aP c χ ξ ≤ 48 * exp 1 * ψ 1 ^ 2 / (c * (3 / 4 * ξ ^ 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
    have h3 : 48 * exp 1 * ψ 1 ^ 2 / (c * (3 / 4 * ξ ^ 2)) ≤ 4 * ψ 1 ^ 2 / ξ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have he3 : exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      nlinarith [sq_nonneg (ψ 1), pow_pos hξ0 2, mul_nonneg (sq_nonneg (ψ 1)) (pow_pos hξ0 2).le]
    linarith
  have hsq' : (|ψ ξ| * ξ) ^ 2 ≤ (2 * |ψ 1|) ^ 2 := by
    rw [mul_pow, sq_abs, mul_pow, sq_abs]
    have := (le_div_iff₀ (pow_pos hξ0 2)).mp hψ2
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq'

/-- **The radial tail of a low rung**: `∫₁^∞ ψ² ≤ 4ψ(1)²` for `0 ≤ χ ≤ (2/5)c²`, `c ≥ 100`. -/
theorem tail_le_edge {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) :
    ∫ ξ in Ioi 1, psi c g ξ ^ 2 ≤ 4 * psi c g 1 ^ 2 := by
  have hcont : Continuous (psi c g) :=
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  set f := (Ioi (1 : ℝ)).indicator (psi c g)
  have hf : Measurable f := hcont.measurable.indicator measurableSet_Ioi
  have hb : ∀ θ, 0 < θ → |f θ| ≤ 2 * |psi c g 1| / θ := by
    intro θ hθ
    by_cases h : θ ∈ Ioi (1 : ℝ)
    · simp only [f, indicator_of_mem h]
      exact abs_psi_le_edge hg hg₁ hg₂c hang hc hχ0 hχ (le_of_lt h)
    · simp only [f, indicator_of_notMem h, abs_zero]; positivity
  have h := Cvs.L2a.FullTailConvergence.integral_sq_le_of_le hf hb
  have he : ∫ θ in Ioi 1, f θ ^ 2 = ∫ θ in Ioi 1, psi c g θ ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioi fun θ hθ => by simp only [f, indicator_of_mem hθ]
  rw [he] at h
  calc _ ≤ _ := h
    _ = 4 * psi c g 1 ^ 2 := by rw [mul_pow, sq_abs]; ring

end Cvs.Prolate.LowRungRadialTailEdge
