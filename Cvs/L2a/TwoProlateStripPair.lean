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
import Cvs.L2a.NearEdgePairLeftPiece
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.StationaryCrossPairSplit
import Cvs.L2a.StationaryEnvelopeMonotone
import Cvs.L2a.StationaryPairElementarySizes
import Cvs.L2a.TwoProlateCrossBound
import Cvs.L2a.TwoProlateStationaryWindows
import Cvs.L2a.TwoProlateWindowPieceMonomials
import Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi
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
# The strip-regime pair of two prolates

For the mode `m` of `ψ_a` and `1/k` of `ψ_b`, with `|χ_b − χ_a| ≤ (3/8) m²c²kδ`, the pair over `[k, b]` splits into
the strip `[k, k(1 + 1/c)]` (value envelope for `ψ_a`, Sonin for `ψ_b`), the left piece where `D₂ < 0`, the window, and
the right piece where `D₂ > 0`; each is bounded in closed form.
-/

namespace Cvs.L2a.TwoProlateStripPair

open Real Set Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryEnvelopeMonotone Cvs.L2a.StationaryPairElementarySizes Cvs.L2a.TwoProlateCrossBound

set_option maxHeartbeats 1000000 in
/-- **The left piece of two prolates, bounded** (half margin: the constant doubles). -/
theorem left2_le {c χ χ' k m δ G κ tl : ℝ} (hc : 1 ≤ c)
    (hΔ : |χ' - χ| ≤ 3 / 8 * m ^ 2 * c ^ 2 * k * δ) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hδ : 0 < δ) (hδχ : χ / (c ^ 2 * m ^ 2 * k) ≤ δ) (hG : 0 ≤ G) (hκ : 0 ≤ κ)
    (hktl : k * (1 + 1 / c) ≤ tl) (htl : tl ≤ √(k ^ 2 + 1 / m ^ 2) - δ) :
    2 * (-(pm m tl / Dmr2 c χ χ' m (1 / k) tl) * (G * √κ / m)
          + -(pm (1 / k) tl / Dmr2 c χ χ' m (1 / k) tl)
            * (G / m * √(κ * (ew (m * (k * (1 + 1 / c))) / ew (k * (1 + 1 / c) / k)))))
      ≤ 16 * G * √κ * (1 / m + 2 * k * √c / (m ^ 2 * tl ^ 2)) / (3 * c ^ 2 * k * δ * m ^ 2) := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hc0 : 0 < c := by linarith
  set a := k * (1 + 1 / c) with ha
  have hka : k ≤ a := by rw [ha]; nlinarith [show 0 < 1 / c by positivity]
  have hktl' : k ≤ tl := hka.trans hktl
  have htl0 : 0 < tl := by linarith
  -- −D₂(t_l) ≥ ½(m² − 1/k²) c² t_l² k δ
  have hmk : 3 / 4 * m ^ 2 ≤ m ^ 2 - 1 / k ^ 2 := by
    have : 1 / k ^ 2 ≤ m ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  have hmk0 : 0 < m ^ 2 - 1 / k ^ 2 := by nlinarith
  have hE := Cvs.L2a.TwoProlateStationaryWindows.D2_left (c := c) (χa := χ) (χb := χ') (k := k) (m := m) (t := tl) (δ := δ)
    hc0 hδ hk0 hm0 hkm2 hδχ hΔ hktl' htl
  have hD : 1 / 2 * (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * tl ^ 2 * k * δ) ≤ -Dmr2 c χ χ' m (1 / k) tl := by linarith
  have hDpos : 0 < 1 / 2 * (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * tl ^ 2 * k * δ) := by positivity
  have hDneg : Dmr2 c χ χ' m (1 / k) tl < 0 := by linarith
  -- numerators
  have hpm : pm m tl ≤ tl ^ 2 := pm_le hm0.ne'
  have hmt : 1 ≤ m * tl := by nlinarith
  have hpm0 : 0 ≤ pm m tl := by
    unfold pm; apply div_nonneg _ (by positivity); nlinarith [hmt]
  have hpr : pm (1 / k) tl ≤ 1 / m ^ 2 := by
    rw [pm_inv hk0.ne']
    have hS : 0 ≤ √(k ^ 2 + 1 / m ^ 2) := sqrt_nonneg _
    have hsq : √(k ^ 2 + 1 / m ^ 2) ^ 2 = k ^ 2 + 1 / m ^ 2 := sq_sqrt (by positivity)
    have hle : tl ≤ √(k ^ 2 + 1 / m ^ 2) := by linarith [htl, hδ]
    have : tl ^ 2 ≤ √(k ^ 2 + 1 / m ^ 2) ^ 2 := pow_le_pow_left₀ htl0.le hle 2
    linarith
  have hpr0 : 0 ≤ pm (1 / k) tl := by rw [pm_inv hk0.ne']; nlinarith
  -- R(a) ≤ 4 m² k² c
  have hR : ew (m * a) / ew (a / k) ≤ 4 * m ^ 2 * k ^ 2 * c := by
    have hak : a / k = 1 + 1 / c := by rw [ha]; field_simp
    rw [hak]
    have hc1 : (1 : ℝ) ≤ 1 + 1 / c := by
      have : 0 ≤ 1 / c := by positivity
      linarith
    have h1 : 1 / c ≤ ew (1 + 1 / c) := by
      have := ew_ge_sub hc1
      linarith
    have hew1 : ew (m * a) ≤ (m * a) ^ 2 := by
      unfold ew
      have hma : 1 ≤ m * a := by nlinarith
      have : √((m * a) ^ 2 - 1) ≤ m * a := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
      calc m * a * √((m * a) ^ 2 - 1) ≤ m * a * (m * a) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = (m * a) ^ 2 := by ring
    have hc1' : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
    have ha2 : a ≤ 2 * k := by
      rw [ha]
      calc k * (1 + 1 / c) ≤ k * (1 + 1) := mul_le_mul_of_nonneg_left (by linarith) hk0.le
        _ = 2 * k := by ring
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) h1)]
    calc ew (m * a) ≤ (m * a) ^ 2 := hew1
      _ ≤ (m * (2 * k)) ^ 2 := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left ha2 hm0.le) 2
      _ = 4 * m ^ 2 * k ^ 2 * c * (1 / c) := by field_simp; ring
      _ ≤ 4 * m ^ 2 * k ^ 2 * c * ew (1 + 1 / c) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hsR : √(κ * (ew (m * a) / ew (a / k))) ≤ √κ * (2 * m * k * √c) := by
    rw [sqrt_mul hκ]
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    calc √(ew (m * a) / ew (a / k)) ≤ √(4 * m ^ 2 * k ^ 2 * c) := sqrt_le_sqrt hR
      _ = 2 * m * k * √c := by
          rw [show 4 * m ^ 2 * k ^ 2 * c = (2 * m * k) ^ 2 * c by ring, sqrt_mul (by positivity),
            sqrt_sq (by positivity)]
  -- assemble
  have e : 2 * (-(pm m tl / Dmr2 c χ χ' m (1 / k) tl) * (G * √κ / m)
          + -(pm (1 / k) tl / Dmr2 c χ χ' m (1 / k) tl) * (G / m * √(κ * (ew (m * a) / ew (a / k)))))
      = 2 * (pm m tl * (G * √κ / m) + pm (1 / k) tl * (G / m * √(κ * (ew (m * a) / ew (a / k)))))
        / (-Dmr2 c χ χ' m (1 / k) tl) := by
    have hDne := hDneg.ne
    field_simp
    ring
  rw [e]
  have hnum : 2 * (pm m tl * (G * √κ / m) + pm (1 / k) tl * (G / m * √(κ * (ew (m * a) / ew (a / k)))))
      ≤ 2 * (tl ^ 2 * (G * √κ / m) + 1 / m ^ 2 * (G / m * (√κ * (2 * m * k * √c)))) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply add_le_add (mul_le_mul_of_nonneg_right hpm (by positivity))
    exact mul_le_mul hpr (mul_le_mul_of_nonneg_left hsR (by positivity)) (by positivity) (by positivity)
  calc _ ≤ 2 * (tl ^ 2 * (G * √κ / m) + 1 / m ^ 2 * (G / m * (√κ * (2 * m * k * √c))))
        / (1 / 2 * (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * tl ^ 2 * k * δ)) := div_le_div₀ (by positivity) hnum hDpos hD
    _ ≤ 2 * (tl ^ 2 * (G * √κ / m) + 1 / m ^ 2 * (G / m * (√κ * (2 * m * k * √c))))
        / (1 / 2 * (3 / 4 * m ^ 2) * (c ^ 2 * tl ^ 2 * k * δ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmk (by norm_num)) (by positivity)
    _ = 16 * G * √κ * (1 / m + 2 * k * √c / (m ^ 2 * tl ^ 2)) / (3 * c ^ 2 * k * δ * m ^ 2) := by
        field_simp; ring

open intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval in
set_option maxHeartbeats 1000000 in
/-- **The near-edge pair of two prolates, bounded.** -/
theorem pairA2_le {c χa χb χm G K ξ₁ Ξ k m δ tl tr b : ℝ} {ψa ua ψb ub : ℝ → ℝ}
    (hc : 1 ≤ c) (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hδ : 0 < δ) (hδk : δ ≤ k / 2)
    (hδχ : χa / (c ^ 2 * m ^ 2 * k) ≤ δ) (hΔ : |χb - χa| ≤ 3 / 8 * m ^ 2 * c ^ 2 * k * δ)
    (htldef : tl = √(k ^ 2 + 1 / m ^ 2) - δ) (htrdef : tr = √(k ^ 2 + 1 / m ^ 2) + δ) (hrb : tr ≤ b)
    (hatl : k * (1 + 1 / c) ≤ tl) (hgap : 1 / (6 * k * m ^ 2) ≤ tl - k)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ 1 + 1 / c) (hlo' : ξ₁ ≤ m * k) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψa : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χb) ψb ub ξ ≤ G)
    (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcontb : ContinuousOn ψb (Icc 1 Ξ)) (hedgeb : ∀ ξ ∈ Icc 1 Ξ, |ψb ξ| ≤ |ψb 1|) (hedge1 : ψb 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψa (m * t) * ψb (1 / k * t)|
      ≤ k / c * (√(2 * K / (√3 * √(c ^ 2 - χm))) * G / (m * k))
        + 16 * G * √(c / √(c ^ 2 - χm)) * (1 / m + 2 * k * √c / (m ^ 2 * tl ^ 2)) / (3 * c ^ 2 * k * δ * m ^ 2)
        + 2 * δ * (G * √(4 * √3) / √(c ^ 2 - χm))
        + G * √(c / √(c ^ 2 - χm)) * (32 * k ^ 2 / (3 * m) + 16 * k ^ 2 * √k * √(tr - k))
          / (c ^ 2 * m ^ 2 * k ^ 3 * δ) := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hc0 : 0 < c := by linarith
  have hkm : 1 < k * m := by nlinarith
  have hχa : χa < c ^ 2 := by linarith
  have hχb : χb < c ^ 2 := by linarith
  have hd : 0 < c ^ 2 - χm := by linarith
  have hsd : 0 < √(c ^ 2 - χm) := sqrt_pos.mpr hd
  have hΔ' : |χb - χa| ≤ 3 / 4 * m ^ 2 * c ^ 2 * k * δ := by
    have : 0 ≤ m ^ 2 * c ^ 2 * k * δ := by positivity
    linarith
  set a := k * (1 + 1 / c) with ha
  have hic : 0 < 1 / c := by positivity
  have hka : k < a := by rw [ha]; nlinarith
  have hlr : tl ≤ tr := by rw [htldef, htrdef]; linarith
  have hab : a ≤ b := hatl.trans (hlr.trans hrb)
  have hak : a / k = 1 + 1 / c := by rw [ha]; field_simp
  have hkS : k ≤ √(k ^ 2 + 1 / m ^ 2) :=
    Real.le_sqrt_of_sq_le (by have : 0 ≤ 1 / m ^ 2 := by positivity
                              linarith)
  -- D < 0 on [a, tl], D > 0 on [tr, b]
  have hmk : 0 < m ^ 2 - 1 / k ^ 2 := by
    have : 1 / k ^ 2 < m ^ 2 := by rw [div_lt_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hDL : ∀ τ ∈ Icc a tl, Dmr2 c χa χb m (1 / k) τ < 0 := fun τ hτ => by
    have hE := Cvs.L2a.TwoProlateStationaryWindows.D2_left (c := c) (χa := χa) (χb := χb) (k := k) (m := m) (t := τ) (δ := δ)
      hc0 hδ hk0 hm0 hkm2 hδχ hΔ (hka.le.trans hτ.1) (by rw [← htldef]; exact hτ.2)
    have hτ0 : 0 < τ := lt_of_lt_of_le (hk0.trans hka) hτ.1
    have : 0 < 1 / 2 * (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * τ ^ 2 * k * δ) := by positivity
    linarith
  have hDR : ∀ τ ∈ Icc tr b, 0 < Dmr2 c χa χb m (1 / k) τ := fun τ hτ => by
    have hE := Cvs.L2a.TwoProlateStationaryWindows.D2_right (c := c) (χa := χa) (χb := χb) (k := k) (m := m) (t := τ) hχa0 hδ
      hk0 hm0 hkm2 hΔ' (by rw [← htrdef]; exact hτ.1)
    have hτ0 : 0 < τ := lt_of_lt_of_le (hk0.trans (lt_of_lt_of_le hka (hatl.trans hlr))) hτ.1
    have : 0 < c ^ 2 * τ ^ 2 * √(k ^ 2 + 1 / m ^ 2) * δ := by
      have : 0 < √(k ^ 2 + 1 / m ^ 2) := lt_of_lt_of_le hk0 hkS
      positivity
    exact lt_of_lt_of_le (mul_pos hmk this) hE
  -- the strip [k, a]
  have in1 : ∀ τ ∈ Icc k b, m * τ ∈ Icc ξ₁ Ξ := fun τ hτ =>
    ⟨hlo'.trans (mul_le_mul_of_nonneg_left hτ.1 hm0.le), le_trans (mul_le_mul_of_nonneg_left hτ.2 hm0.le) hhi⟩
  have hdiv : ∀ τ : ℝ, 1 / k * τ = τ / k := fun τ => by ring
  have hmk1 : 1 < m * k := by linarith
  have hval1 : ∀ τ ∈ Icc k a, |ψa (m * τ)| ≤ √(G / (√(c ^ 2 - χm) * ew (m * k))) := fun τ hτ => by
    have hξ := in1 τ ⟨hτ.1, hτ.2.trans hab⟩
    have hξ1 : 1 < m * τ := lt_of_lt_of_le hξ₁ hξ.1
    have h2 := Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi.val_sq_le hχa0 hχam hχm hξ1 (hGa _ hξ)
    have hmono := Cvs.L2a.StationaryEnvelopeMonotone.ew_mono hmk1.le (mul_le_mul_of_nonneg_left hτ.1 hm0.le)
    have hew := Cvs.L2a.StationaryEnvelopeMonotone.ew_pos hmk1
    have h3 : ψa (m * τ) ^ 2 ≤ G / (√(c ^ 2 - χm) * ew (m * k)) :=
      h2.trans (div_le_div_of_nonneg_left hG0 (by positivity) (mul_le_mul_of_nonneg_left hmono hsd.le))
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h3
  have inE : ∀ τ ∈ Icc k b, 1 / k * τ ∈ Icc 1 Ξ := fun τ hτ => by
    rw [hdiv]
    exact ⟨by rw [le_div_iff₀ hk0]; linarith [hτ.1], le_trans (div_le_div_of_nonneg_right hτ.2 hk0.le) hhi'⟩
  have hval2 : ∀ τ ∈ Icc k a, |ψb (1 / k * τ)| ≤ |ψb 1| := fun τ hτ => hedgeb _ (inE τ ⟨hτ.1, hτ.2.trans hab⟩)
  have hcf1 : ContinuousOn (fun τ => ψa (m * τ)) (Icc k b) := fun τ hτ =>
    ((hψa _ (in1 τ hτ)).continuousAt.comp (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  have hcf2 : ContinuousOn (fun τ => ψb (1 / k * τ)) (Icc k b) :=
    hcontb.comp (continuousOn_const.mul continuousOn_id) (fun τ hτ => inE τ hτ)
  have strip := Cvs.L2a.StationaryCrossPairSplit.window_le hka.le (hcf1.mono (Icc_subset_Icc_right hab))
    (hcf2.mono (Icc_subset_Icc_right hab)) hval1 hval2
  have hw := Cvs.L2a.EdgeWindowPairMonomial.window_factor_le (σ := √(c ^ 2 - χm)) (ψ1 := ψb 1) hsd hG0 hK
    (by nlinarith) hm0 hk0 hedge1
  have hak' : a - k = k / c := by rw [ha]; field_simp; ring
  have hstrip : |∫ t in k..a, ψa (m * t) * ψb (1 / k * t)|
      ≤ k / c * (√(2 * K / (√3 * √(c ^ 2 - χm))) * G / (m * k)) := by
    refine strip.trans ?_
    rw [hak']; exact mul_le_mul_of_nonneg_left hw (by positivity)
  -- the rest by Cvs.L2a.StationaryEnvelopeMonotone
  have hmain := Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi.stationary_pair2_le (c := c) (χa := χa) (χb := χb) (χm := χm) (G := G)
    (ξ₁ := ξ₁) (Ξ := Ξ) (k := k) (m := m) (a := a) (tl := tl) (tr := tr) (b := b) hc0 hχa0 hχam hχb0 hχbm hχm
    hk0 hm0 hkm hka hatl hlr hrb
    hξ₁ (by rw [hak]; exact hlo) (hlo'.trans (by nlinarith)) hhi hhi' hψa hua hψb hub hGa hGb hDL hDR
  have hL := left2_le (c := c) (χ := χa) (χ' := χb) (k := k) (m := m) (δ := δ) (G := G)
    (κ := c / √(c ^ 2 - χm)) (tl := tl) hc hΔ hk1 hkm2 hm hδ hδχ hG0 (by positivity) hatl (le_of_eq htldef)
  have hW := Cvs.L2a.NearEdgePairLeftPiece.window_le' (σ := √(c ^ 2 - χm)) (G := G) (k := k) (m := m) (tl := tl)
    (δ := δ) hsd hG0 hk0 hm0 hδ.le (by nlinarith) hgap
  have hR := Cvs.L2a.TwoProlateWindowPieceMonomials.right2_le (c := c) (χ := χa) (χ' := χb) (k := k) (m := m) (δ := δ) (G := G)
    (κ := c / √(c ^ 2 - χm)) (tr := tr) hc0 hχa0 hΔ' hk1 hkm2 hm hδ hδk hG0 (by positivity) htrdef
  have htrl : tr - tl = 2 * δ := by rw [htrdef, htldef]; ring
  rw [htrl] at hmain
  -- additivity
  have hcf : ContinuousOn (fun τ => ψa (m * τ) * ψb (1 / k * τ)) (Icc k b) := hcf1.mul hcf2
  have i1 : IntervalIntegrable (fun τ => ψa (m * τ) * ψb (1 / k * τ)) MeasureTheory.volume k a :=
    (hcf.mono (Icc_subset_Icc_right hab)).intervalIntegrable_of_Icc hka.le
  have i2 : IntervalIntegrable (fun τ => ψa (m * τ) * ψb (1 / k * τ)) MeasureTheory.volume a b :=
    (hcf.mono (Icc_subset_Icc_left hka.le)).intervalIntegrable_of_Icc hab
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  calc |(∫ t in k..a, ψa (m * t) * ψb (1 / k * t)) + ∫ t in a..b, ψa (m * t) * ψb (1 / k * t)|
      ≤ |∫ t in k..a, ψa (m * t) * ψb (1 / k * t)| + |∫ t in a..b, ψa (m * t) * ψb (1 / k * t)| := abs_add_le _ _
    _ ≤ _ := add_le_add hstrip (hmain.trans (add_le_add (add_le_add hL hW) hR))
    _ = _ := by ring

end Cvs.L2a.TwoProlateStripPair
