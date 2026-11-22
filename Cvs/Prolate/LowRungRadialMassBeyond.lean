import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.Prolate.EdgeLayerDerivativeMass
import Cvs.Prolate.Envelope.FarRadialEnvelope
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The radial mass of a low rung beyond `b` is `O(ψ(1)²/(cb))`

On `(1, 2]` the Liouville–Green energy is at most `48eψ(1)²` and `a ≥ c√(6/5)√(ξ − 1)`, so
`ψ² ≤ 48eψ(1)²(ξ − 1)^{−1/2}/(c√(6/5))`; on `ξ ≥ 2`, `ψ² ≤ 64eψ(1)²/(cξ²)` (Cvs.Prolate.Envelope.FarRadialEnvelope). Hence
`∫_b^{b′} ψ² ≤ 400eψ(1)²/(cb)` for `1 ≤ b ≤ b′`: a factor `c` below the edge bound `4ψ(1)²` of Cvs.Prolate.LowRungRadialTailEdge.
-/

noncomputable section

open Real Set MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SlepianCommutingRelation (kint)

namespace Cvs.Prolate.LowRungRadialMassBeyond

/-- **The edge envelope of `ψ²`**: `ψ(ξ)² ≤ 48eψ(1)²/(c√(6/5))·(ξ − 1)^{−1/2}` for `1 < ξ ≤ 2`. -/
theorem sq_psi_edge_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) {ξ : ℝ} (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2) :
    psi c g ξ ^ 2 ≤ 48 * exp 1 * psi c g 1 ^ 2 / (c * √(6 / 5)) * (ξ - 1) ^ (-(1 / 2) : ℝ) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hχc : χ < c ^ 2 := by nlinarith
  have hE := Cvs.Prolate.EdgeLayerDerivativeMass.energy_edge_le hg hg₁ hg₂c hang hc hχ0 hχ hξ1 hξ2
  have ha := aP_pos (c := c) (χ := χ) hξ1 hc2 hχc
  have hsq := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.sq_le_energy_div (ψ := psi c g)
    (u := fun r => pP r * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) r) ha
  have hξ0 : 0 < ξ - 1 := by linarith
  -- `a ≥ c√(6/5)√(ξ − 1)`
  have halow : c * √(6 / 5) * √(ξ - 1) ≤ aP c χ ξ := by
    unfold aP pP qP
    rw [show c * √(6 / 5) * √(ξ - 1) = √(c ^ 2 * (6 / 5) * (ξ - 1)) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hc0.le]]
    apply Real.sqrt_le_sqrt
    have h1 : 2 * (ξ - 1) ≤ ξ ^ 2 - 1 := by nlinarith
    have h2 : 3 / 5 * c ^ 2 ≤ c ^ 2 * ξ ^ 2 - χ := by nlinarith
    nlinarith [mul_le_mul h1 h2 (by positivity) (by nlinarith)]
  have hpos : 0 < c * √(6 / 5) * √(ξ - 1) := by positivity
  have h1 : psi c g ξ ^ 2 ≤ 48 * exp 1 * psi c g 1 ^ 2 / aP c χ ξ :=
    hsq.trans (div_le_div_of_nonneg_right hE ha.le)
  have h2 : 48 * exp 1 * psi c g 1 ^ 2 / aP c χ ξ ≤ 48 * exp 1 * psi c g 1 ^ 2 / (c * √(6 / 5) * √(ξ - 1)) :=
    div_le_div_of_nonneg_left (by positivity) hpos halow
  have e : 48 * exp 1 * psi c g 1 ^ 2 / (c * √(6 / 5) * √(ξ - 1))
      = 48 * exp 1 * psi c g 1 ^ 2 / (c * √(6 / 5)) * (ξ - 1) ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow (ξ - 1), rpow_neg hξ0.le]; field_simp
  linarith

/-- **The radial mass beyond `b`**: `∫_b^{b′} ψ² ≤ 400eψ(1)²/(cb)` for `1 ≤ b ≤ b′`. -/
theorem integral_sq_le {g g₁ g₂ : ℝ → ℝ} {c χ b b' : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) (hb : 1 ≤ b) (hbb : b ≤ b') :
    ∫ ξ in b..b', psi c g ξ ^ 2 ≤ 400 * exp 1 * psi c g 1 ^ 2 / (c * b) := by
  have hc0 : 0 < c := by linarith
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hψc : Continuous (psi c g) := (Cvs.L2a.FullTailConvergence.contDiff_psi hgc c).continuous
  have hsqc : Continuous fun ξ => psi c g ξ ^ 2 := hψc.pow 2
  set Y := psi c g 1 ^ 2 with hY
  have hY0 : 0 ≤ Y := sq_nonneg _
  have he := exp_pos 1
  -- the far part: `∫_{b₀}^{b′} ψ² ≤ 64eY/(c b₀)` for `2 ≤ b₀ ≤ b′`
  have hfar : ∀ b₀, 2 ≤ b₀ → b₀ ≤ b' → ∫ ξ in b₀..b', psi c g ξ ^ 2 ≤ 64 * exp 1 * Y / (c * b₀) := fun b₀ h2 hb' => by
    have hcont : ContinuousOn (fun ξ : ℝ => 1 / ξ ^ 2) (uIcc b₀ b') := by
      refine continuousOn_const.div (continuousOn_id.pow 2) fun ξ hξ => ?_
      rw [uIcc_of_le hb'] at hξ; exact pow_ne_zero 2 (by linarith [hξ.1])
    have hle := intervalIntegral.integral_mono_on (μ := volume) (f := fun ξ => psi c g ξ ^ 2) hb'
      (hsqc.intervalIntegrable _ _) ((hcont.intervalIntegrable).const_mul (64 * exp 1 * Y / c)) fun ξ hξ => by
        have h := Cvs.Prolate.Envelope.FarRadialEnvelope.sq_psi_far_le hg hg₁ hg₂c hang hc hχ0 hχ (le_trans h2 hξ.1)
        calc psi c g ξ ^ 2 ≤ 64 * exp 1 * Y / (c * ξ ^ 2) := h
          _ = 64 * exp 1 * Y / c * (1 / ξ ^ 2) := by field_simp
    rw [intervalIntegral.integral_const_mul] at hle
    have hI : ∫ ξ in b₀..b', 1 / ξ ^ 2 ≤ 1 / b₀ := by
      have hd : ∀ ξ ∈ uIcc b₀ b', HasDerivAt (fun ξ : ℝ => -ξ⁻¹) (1 / ξ ^ 2) ξ := fun ξ hξ => by
        rw [uIcc_of_le hb'] at hξ
        have hξ0 : ξ ≠ 0 := by linarith [hξ.1]
        refine (hasDerivAt_inv hξ0).neg.congr_deriv ?_; field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
      have : 0 < b' := by linarith
      have : 0 < b'⁻¹ := inv_pos.2 this
      rw [one_div]; linarith
    calc ∫ ξ in b₀..b', psi c g ξ ^ 2 ≤ 64 * exp 1 * Y / c * ∫ ξ in b₀..b', 1 / ξ ^ 2 := hle
      _ ≤ 64 * exp 1 * Y / c * (1 / b₀) := mul_le_mul_of_nonneg_left hI (by positivity)
      _ = 64 * exp 1 * Y / (c * b₀) := by field_simp
  -- the edge part: `∫_b^2 ψ² ≤ 2·48eY/(c√(6/5))` for `1 ≤ b ≤ 2`
  have hedge : ∀ b₀, 1 ≤ b₀ → b₀ ≤ 2 → ∫ ξ in b₀..2, psi c g ξ ^ 2 ≤ 2 * (48 * exp 1 * Y / (c * √(6 / 5))) :=
    fun b₀ h1 h2 => by
    set K := 48 * exp 1 * Y / (c * √(6 / 5)) with hK
    have hK0 : 0 ≤ K := by positivity
    have hmaj : IntervalIntegrable (fun ξ : ℝ => K * (ξ - 1) ^ (-(1 / 2) : ℝ)) volume b₀ 2 := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := b₀ - 1) (b := 2 - 1) (r := (-(1 / 2) : ℝ))
        (by norm_num)).comp_sub_right 1
      simpa using h.const_mul K
    have hle := intervalIntegral.integral_mono_on_of_le_Ioo h2 (hsqc.intervalIntegrable b₀ 2) hmaj
      fun ξ hξ => sq_psi_edge_le hg hg₁ hg₂c hang hc hχ0 hχ (by linarith [hξ.1]) hξ.2.le
    have hval : ∫ ξ in b₀..2, K * (ξ - 1) ^ (-(1 / 2) : ℝ) = K * (2 * (1 - (b₀ - 1) ^ (1 / 2 : ℝ))) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right (fun x => x ^ (-(1 / 2) : ℝ)),
        integral_rpow (Or.inl (by norm_num))]
      congr 1
      norm_num; ring
    have hr : 0 ≤ (b₀ - 1) ^ (1 / 2 : ℝ) := rpow_nonneg (by linarith) _
    rw [hval] at hle
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 2 * (1 - (b₀ - 1) ^ (1 / 2 : ℝ)) ≤ 2) hK0]
  have hs65 : 1 ≤ √(6 / 5) := by rw [Real.one_le_sqrt]; norm_num
  have hs65' : 0 < √(6 / 5) := by positivity
  rcases le_or_gt 2 b with h2 | h2
  · calc ∫ ξ in b..b', psi c g ξ ^ 2 ≤ 64 * exp 1 * Y / (c * b) := hfar b h2 hbb
      _ ≤ 400 * exp 1 * Y / (c * b) := by
          apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  · -- `b < 2`: split at `2` if `b′ > 2`
    have hb0 : 0 < b := by linarith
    have hedgeK : 2 * (48 * exp 1 * Y / (c * √(6 / 5))) ≤ 96 * exp 1 * Y / c := by
      rw [show 96 * exp 1 * Y / c = 2 * (48 * exp 1 * Y / (c * 1)) by ring]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hs65 hc0.le)) (by norm_num)
    have htarget : 96 * exp 1 * Y / c + 32 * exp 1 * Y / c ≤ 400 * exp 1 * Y / (c * b) := by
      rw [show 96 * exp 1 * Y / c + 32 * exp 1 * Y / c = 128 * exp 1 * Y / c by ring,
        div_le_div_iff₀ hc0 (by positivity)]
      nlinarith [mul_nonneg he.le hY0, mul_nonneg (mul_nonneg he.le hY0) hc0.le]
    rcases le_or_gt b' 2 with hb'2 | hb'2
    · -- `[b, b′] ⊂ [1, 2]`
      have hsub : ∫ ξ in b..b', psi c g ξ ^ 2 ≤ ∫ ξ in b..2, psi c g ξ ^ 2 :=
        intervalIntegral.integral_mono_interval le_rfl hbb hb'2
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hsqc.intervalIntegrable _ _)
      have := hedge b hb h2.le
      have h0 : 0 ≤ 32 * exp 1 * Y / c := by positivity
      linarith
    · have hsplit : ∫ ξ in b..b', psi c g ξ ^ 2 = (∫ ξ in b..2, psi c g ξ ^ 2) + ∫ ξ in (2 : ℝ)..b', psi c g ξ ^ 2 :=
        (intervalIntegral.integral_add_adjacent_intervals (hsqc.intervalIntegrable _ _)
          (hsqc.intervalIntegrable _ _)).symm
      have h1 := hedge b hb h2.le
      have h3 := hfar 2 le_rfl hb'2.le
      have h3' : 64 * exp 1 * Y / (c * 2) = 32 * exp 1 * Y / c := by field_simp; ring
      rw [hsplit]; linarith

end Cvs.Prolate.LowRungRadialMassBeyond
