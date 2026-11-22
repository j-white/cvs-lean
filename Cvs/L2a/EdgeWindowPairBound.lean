import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.EdgeStationaryPairWindow
import Cvs.L2a.EdgeWindowPairMonomial
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.StationaryPairMismatchSign
import Cvs.Prolate.Envelope.ProlateWeightToEdge
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One edge-window stationary pair, as a monomial bound

Cvs.L2a.EdgeStationaryPairWindow with `t_r = √(k² + 1/m²) + δ`, `D > 0` beyond `t_r` from Cvs.L2a.StationaryPairMismatchSign, the window factor and right piece of Cvs.L2a.EdgeWindowPairMonomial:
`|∫_k^b ψ(mt)ψ(t/k)| ≤ (t_r − k)√(2K/(√3σ)) G/(mk) + G√κ₀(16k²/(3m) + 8k²√k√(t_r − k))/(c²m²k³δ)`,
given `ψ(1)² ≤ K G`, `k ≥ 1`, `km ≥ 2`, `0 < δ ≤ k/2`.
-/

namespace Cvs.L2a.EdgeWindowPairBound

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge

/-- **The edge-window pair, bounded.** -/
theorem pairB_le {c χ G K ξ₁ Ξ k m δ tr b : ℝ} {ψ u : ℝ → ℝ}
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hδ : 0 < δ) (hδk : δ ≤ k / 2)
    (htrdef : tr = √(k ^ 2 + 1 / m ^ 2) + δ) (hrb : tr ≤ b)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ tr / k) (hlo' : ξ₁ ≤ m * k) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψ : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ (tr - k) * (√(2 * K / (√3 * √(c ^ 2 - χ))) * G / (m * k))
        + G * √(c / √(c ^ 2 - χ)) * (16 * k ^ 2 / (3 * m) + 8 * k ^ 2 * √k * √(tr - k))
          / (c ^ 2 * m ^ 2 * k ^ 3 * δ) := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hkm : 1 < k * m := by nlinarith
  have hkS : k ≤ √(k ^ 2 + 1 / m ^ 2) :=
    Real.le_sqrt_of_sq_le (by have : 0 ≤ 1 / m ^ 2 := by positivity
                              linarith)
  have hktr : k < tr := by rw [htrdef]; linarith
  have hd : 0 < c ^ 2 - χ := by linarith
  have hsd : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  have hDR : ∀ τ ∈ Icc tr b, 0 < Dmr c χ m (1 / k) τ := fun τ hτ => by
    rw [Cvs.L2a.StationaryPairMismatchSign.Dmr_eq_Est hk0.ne' hm0.ne']
    have hE := Cvs.L2a.StationaryPairMismatchSign.Est_right (c := c) (χ := χ) (k := k) (m := m) (t := τ) hχ0 hδ hm0.ne'
      (by rw [← htrdef]; exact hτ.1)
    have hτ0 : 0 < τ := lt_of_lt_of_le (hk0.trans hktr) hτ.1
    have : 0 < 2 * c ^ 2 * τ ^ 2 * √(k ^ 2 + 1 / m ^ 2) * δ := by
      have : 0 < √(k ^ 2 + 1 / m ^ 2) := lt_of_lt_of_le hk0 hkS
      positivity
    have hmk : 0 < m ^ 2 - 1 / k ^ 2 := by
      have : 1 / k ^ 2 < m ^ 2 := by rw [div_lt_iff₀ (by positivity)]; nlinarith
      nlinarith
    exact mul_pos hmk (lt_of_lt_of_le this hE)
  have key := Cvs.L2a.EdgeStationaryPairWindow.edge_pair_le hc hχ0 hχ hk0 hm0 hkm hktr hrb hξ₁ hlo hlo' hhi hhi'
    hψ hu hG hcont hedge hDR
  have hw := Cvs.L2a.EdgeWindowPairMonomial.window_factor_le (σ := √(c ^ 2 - χ)) (ψ1 := ψ 1) hsd hG0 hK
    (by nlinarith) hm0 hk0 hedge1
  have hr := Cvs.L2a.EdgeWindowPairMonomial.right_le (c := c) (χ := χ) (k := k) (m := m) (δ := δ) (G := G)
    (κ := c / √(c ^ 2 - χ)) (tr := tr) hc hχ0 hk1 hkm2 hm hδ hδk hG0 (by positivity) htrdef
  have hwin : (tr - k) * (√(G / (√(c ^ 2 - χ) * ew (m * k))) * |ψ 1|)
      ≤ (tr - k) * (√(2 * K / (√3 * √(c ^ 2 - χ))) * G / (m * k)) :=
    mul_le_mul_of_nonneg_left hw (by linarith)
  linarith

end Cvs.L2a.EdgeWindowPairBound
