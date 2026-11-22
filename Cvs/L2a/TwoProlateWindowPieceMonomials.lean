import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.EdgeWindowPairMonomial
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.StationaryPairElementarySizes
import Cvs.L2a.TwoProlateCrossBound
import Cvs.L2a.TwoProlateEdgeWindowPair
import Cvs.L2a.TwoProlateStationaryWindows
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
# The window pieces of two prolates, as monomials

`EdgeWindowPairMonomial`'s right piece with the two-prolate `D₂` (`TwoProlateStationaryWindows`'s half margin): the constants double,
`G√κ (32k²/(3m) + 16k²√k √(t_r − k))/(c²m²k³δ)`; with Cvs.L2a.TwoProlateEdgeWindowPair the edge-regime pair of two prolates.
-/

namespace Cvs.L2a.TwoProlateWindowPieceMonomials

open Real Set Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryEnvelopeMonotone Cvs.L2a.StationaryPairElementarySizes Cvs.L2a.TwoProlateCrossBound

set_option maxHeartbeats 1000000 in
/-- **The right piece of two prolates, bounded.** For `|χ' − χ| ≤ (3/4)m²c²kδ`, `k ≥ 1`, `km ≥ 2`, `0 < δ ≤ k/2`, `0 ≤ χ < c²`, `t_r = √S + δ`, `G, κ ≥ 0`:
`2(p_m(t_r) G√κ/m + p_{1/k}(t_r)(G/m)√(κ R(t_r)))/D(t_r) ≤ G√κ (32k²/(3m) + 16k²√k √(t_r − k))/(c² m² k³ δ)`. -/
theorem right2_le {c χ χ' k m δ G κ tr : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ)
    (hΔ : |χ' - χ| ≤ 3 / 4 * m ^ 2 * c ^ 2 * k * δ) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hδ : 0 < δ) (hδk : δ ≤ k / 2) (hG : 0 ≤ G) (hκ : 0 ≤ κ) (htrdef : tr = √(k ^ 2 + 1 / m ^ 2) + δ) :
    2 * (pm m tr * (G * √κ / m) + pm (1 / k) tr * (G / m * √(κ * (ew (m * tr) / ew (tr / k)))))
        / Dmr2 c χ χ' m (1 / k) tr
      ≤ G * √κ * (32 * k ^ 2 / (3 * m) + 16 * k ^ 2 * √k * √(tr - k)) / (c ^ 2 * m ^ 2 * k ^ 3 * δ) := by
  have hk : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  set S := k ^ 2 + 1 / m ^ 2 with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hkS : k ≤ √S := Real.le_sqrt_of_sq_le (by have : 0 ≤ 1 / m ^ 2 := by positivity
                                                 linarith)
  have hgap := sqrtS_sub_le hk0 hm0
  have hkm1 : 1 ≤ k * m := by nlinarith
  have hgap1 : 1 / (2 * k * m ^ 2) ≤ k / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hkm1 hkm1 zero_le_one (by linarith), mul_le_mul hk hkm1 zero_le_one (by linarith)]
  have htrk : δ ≤ tr - k := by rw [htrdef]; linarith
  have htr2 : tr ≤ 2 * k := by rw [htrdef]; linarith
  have htr0 : 0 < tr := by linarith
  -- D₂(t_r) ≥ (m² − 1/k²) c²k³δ
  have hmk : 3 / 4 * m ^ 2 ≤ m ^ 2 - 1 / k ^ 2 := by
    have : 1 / k ^ 2 ≤ m ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  have hE := Cvs.L2a.TwoProlateStationaryWindows.D2_right (c := c) (χa := χ) (χb := χ') (k := k) (m := m) (t := tr) hχ0 hδ hk0 hm0
    hkm2 hΔ (le_of_eq htrdef.symm)
  have hD : (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * k ^ 3 * δ) ≤ Dmr2 c χ χ' m (1 / k) tr := by
    refine le_trans ?_ hE
    apply mul_le_mul_of_nonneg_left _ (by nlinarith [hmk, sq_nonneg m])
    have : k ^ 2 ≤ tr ^ 2 := by nlinarith
    calc c ^ 2 * k ^ 3 * δ = c ^ 2 * k ^ 2 * k * δ := by ring
      _ ≤ c ^ 2 * tr ^ 2 * √S * δ := by
          apply mul_le_mul_of_nonneg_right _ hδ.le
          apply mul_le_mul (mul_le_mul_of_nonneg_left this (by positivity)) hkS hk0.le (by positivity)
  have hDpos : 0 < (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * k ^ 3 * δ) := by
    have : 0 < m ^ 2 - 1 / k ^ 2 := by nlinarith
    positivity
  -- the numerator
  have hpm : pm m tr ≤ 4 * k ^ 2 := (pm_le hm0.ne').trans (by nlinarith)
  have hpr : pm (1 / k) tr ≤ 3 * k * (tr - k) := by
    rw [pm_inv hk0.ne']; nlinarith
  have hpr0 : 0 ≤ pm (1 / k) tr := by rw [pm_inv hk0.ne']; nlinarith
  have hR : ew (m * tr) / ew (tr / k) ≤ 4 * m ^ 2 * k ^ 3 / (tr - k) := by
    have h1 : 1 ≤ tr / k := by rw [le_div_iff₀ hk0]; linarith
    have h2 : (tr - k) / k ≤ ew (tr / k) := by
      have := ew_ge_sub h1; rw [show tr / k - 1 = (tr - k) / k by field_simp] at this; exact this
    have hew1 : ew (m * tr) ≤ (m * tr) ^ 2 := by
      unfold ew
      have : √((m * tr) ^ 2 - 1) ≤ m * tr := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
      calc m * tr * √((m * tr) ^ 2 - 1) ≤ m * tr * (m * tr) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = (m * tr) ^ 2 := by ring
    have hpos : 0 < (tr - k) / k := by apply div_pos (by linarith) hk0
    rw [div_le_div_iff₀ (lt_of_lt_of_le hpos h2) (by linarith)]
    calc ew (m * tr) * (tr - k) ≤ (m * tr) ^ 2 * (tr - k) :=
          mul_le_mul_of_nonneg_right hew1 (by linarith)
      _ ≤ (m * (2 * k)) ^ 2 * (tr - k) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left htr2 hm0.le) 2
      _ = 4 * m ^ 2 * k ^ 3 * ((tr - k) / k) := by field_simp; ring
      _ ≤ 4 * m ^ 2 * k ^ 3 * ew (tr / k) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hflux : pm (1 / k) tr * √(κ * (ew (m * tr) / ew (tr / k))) ≤ √κ * (6 * m * k ^ 2 * √k * √(tr - k)) := by
    have hq : 0 < tr - k := by linarith
    have hR' : √(κ * (ew (m * tr) / ew (tr / k))) ≤ √κ * (2 * m * k * √k / √(tr - k)) := by
      rw [sqrt_mul hκ]
      apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
      calc √(ew (m * tr) / ew (tr / k)) ≤ √(4 * m ^ 2 * k ^ 3 / (tr - k)) := sqrt_le_sqrt hR
        _ = 2 * m * k * √k / √(tr - k) := by
            rw [sqrt_div' _ hq.le, show 4 * m ^ 2 * k ^ 3 = (2 * m * k) ^ 2 * k by ring,
              sqrt_mul (by positivity), sqrt_sq (by positivity)]
    have hsq : √(tr - k) * √(tr - k) = tr - k := mul_self_sqrt hq.le
    have hs : 0 < √(tr - k) := sqrt_pos.mpr hq
    calc pm (1 / k) tr * √(κ * (ew (m * tr) / ew (tr / k)))
        ≤ 3 * k * (tr - k) * (√κ * (2 * m * k * √k / √(tr - k))) :=
          mul_le_mul hpr hR' (sqrt_nonneg _) (mul_nonneg (by linarith) hq.le)
      _ = √κ * (6 * m * k ^ 2 * √k * ((tr - k) / √(tr - k))) := by ring
      _ = √κ * (6 * m * k ^ 2 * √k * √(tr - k)) := by
          have hdv : (tr - k) / √(tr - k) = √(tr - k) := by
            rw [div_eq_iff hs.ne', hsq]
          rw [hdv]
  -- combine
  have hnum : 2 * (pm m tr * (G * √κ / m) + pm (1 / k) tr * (G / m * √(κ * (ew (m * tr) / ew (tr / k)))))
      ≤ 2 * (4 * k ^ 2 * (G * √κ / m) + G / m * (√κ * (6 * m * k ^ 2 * √k * √(tr - k)))) := by
    have e1 : pm m tr * (G * √κ / m) ≤ 4 * k ^ 2 * (G * √κ / m) :=
      mul_le_mul_of_nonneg_right hpm (by positivity)
    have e2 : pm (1 / k) tr * (G / m * √(κ * (ew (m * tr) / ew (tr / k))))
        ≤ G / m * (√κ * (6 * m * k ^ 2 * √k * √(tr - k))) := by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hflux (by positivity)
    exact mul_le_mul_of_nonneg_left (add_le_add e1 e2) (by norm_num)
  calc _ ≤ 2 * (4 * k ^ 2 * (G * √κ / m) + G / m * (√κ * (6 * m * k ^ 2 * √k * √(tr - k))))
        / ((m ^ 2 - 1 / k ^ 2) * (c ^ 2 * k ^ 3 * δ)) := by
        apply div_le_div₀ (by positivity) hnum hDpos hD
    _ ≤ 2 * (4 * k ^ 2 * (G * √κ / m) + G / m * (√κ * (6 * m * k ^ 2 * √k * √(tr - k))))
        / (3 / 4 * m ^ 2 * (c ^ 2 * k ^ 3 * δ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hmk (by positivity)
    _ = G * √κ * (32 * k ^ 2 / (3 * m) + 16 * k ^ 2 * √k * √(tr - k)) / (c ^ 2 * m ^ 2 * k ^ 3 * δ) := by
        field_simp; ring

open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval in
/-- **The edge-window pair of two prolates, bounded.** -/
theorem pairB2_le {c χa χb χm G K ξ₁ Ξ k m δ tr b : ℝ} {ψa ua ψb ub : ℝ → ℝ}
    (hc : 0 < c) (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2)
    (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hδ : 0 < δ) (hδk : δ ≤ k / 2)
    (hΔ : |χb - χa| ≤ 3 / 4 * m ^ 2 * c ^ 2 * k * δ)
    (htrdef : tr = √(k ^ 2 + 1 / m ^ 2) + δ) (hrb : tr ≤ b)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ tr / k) (hlo' : ξ₁ ≤ m * k) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψa : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χb) ψb ub ξ ≤ G)
    (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcontb : ContinuousOn ψb (Icc 1 Ξ)) (hedgeb : ∀ ξ ∈ Icc 1 Ξ, |ψb ξ| ≤ |ψb 1|) (hedge1 : ψb 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψa (m * t) * ψb (1 / k * t)|
      ≤ (tr - k) * (√(2 * K / (√3 * √(c ^ 2 - χm))) * G / (m * k))
        + G * √(c / √(c ^ 2 - χm)) * (32 * k ^ 2 / (3 * m) + 16 * k ^ 2 * √k * √(tr - k))
          / (c ^ 2 * m ^ 2 * k ^ 3 * δ) := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hkm : 1 < k * m := by nlinarith
  have hm2 : 0 ≤ 1 / m ^ 2 := by positivity
  have hkS : k ≤ √(k ^ 2 + 1 / m ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
  have hktr : k < tr := by rw [htrdef]; linarith
  have hd : 0 < c ^ 2 - χm := by linarith
  have hsd : 0 < √(c ^ 2 - χm) := sqrt_pos.mpr hd
  have hmk : 0 < m ^ 2 - 1 / k ^ 2 := by
    have := Cvs.L2a.TwoProlateStationaryWindows.mk_ge hk0 hkm2; nlinarith
  have hDR : ∀ τ ∈ Icc tr b, 0 < Dmr2 c χa χb m (1 / k) τ := fun τ hτ => by
    have hE := Cvs.L2a.TwoProlateStationaryWindows.D2_right (c := c) (χa := χa) (χb := χb) (k := k) (m := m) (t := τ) hχa0 hδ
      hk0 hm0 hkm2 hΔ (by rw [← htrdef]; exact hτ.1)
    have hτ0 : 0 < τ := lt_of_lt_of_le (hk0.trans hktr) hτ.1
    have hc0 : 0 < c ^ 2 * τ ^ 2 * √(k ^ 2 + 1 / m ^ 2) * δ := by
      have : 0 < √(k ^ 2 + 1 / m ^ 2) := lt_of_lt_of_le hk0 hkS
      positivity
    exact lt_of_lt_of_le (mul_pos hmk hc0) hE
  have key := Cvs.L2a.TwoProlateEdgeWindowPair.edge_pair2_le hc hχa0 hχam hχb0 hχbm hχm hk0 hm0 hkm hktr hrb hξ₁ hlo hlo'
    hhi hhi' hψa hua hψb hub hGa hGb hcontb hedgeb hDR
  have hw := Cvs.L2a.EdgeWindowPairMonomial.window_factor_le (σ := √(c ^ 2 - χm)) (ψ1 := ψb 1) hsd hG0 hK
    (by nlinarith) hm0 hk0 hedge1
  have hr := right2_le (c := c) (χ := χa) (χ' := χb) (k := k) (m := m) (δ := δ) (G := G)
    (κ := c / √(c ^ 2 - χm)) (tr := tr) hc hχa0 hΔ hk1 hkm2 hm hδ hδk hG0 (by positivity) htrdef
  have hwin : (tr - k) * (√(G / (√(c ^ 2 - χm) * ew (m * k))) * |ψb 1|)
      ≤ (tr - k) * (√(2 * K / (√3 * √(c ^ 2 - χm))) * G / (m * k)) :=
    mul_le_mul_of_nonneg_left hw (by linarith)
  linarith

end Cvs.L2a.TwoProlateWindowPieceMonomials
