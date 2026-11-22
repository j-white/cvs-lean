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
import Cvs.L2a.ExactRootPairPieces
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.StationaryCrossPairSplit
import Cvs.L2a.StationaryEnvelopeMonotone
import Cvs.L2a.StationaryMismatchExactRoots
import Cvs.L2a.StationaryPairMismatchSign
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
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
# One near-edge stationary pair at the exact root, for every `χ < c²`

The strip `[k, k(1 + 1/c)]` by Sonin and the window factor, then Cvs.L2a.StationaryEnvelopeMonotone with `ExactRootPairPieces`'s left piece, right piece and window,
`t_l = √T₊ − δ`, `t_r = √T₊ + δ`, gap `g ≤ t_l − k`: `|∫_k^b ψ(mt)ψ(t/k)| ≤ strip + left + window + right`, each in
closed form, with no condition tying `δ` to `χ`.
-/

namespace Cvs.L2a.ExactRootNearEdgePair

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryMismatchExactRoots

set_option maxHeartbeats 1000000 in
/-- **The near-edge pair at the exact root, bounded.** -/
theorem pairA_le {c χ G K ξ₁ Ξ k m δ tl tr b : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hδ : 0 < δ) (hδk : δ ≤ k / 2)
    (htldef : tl = √(Tp c χ k m) - δ) (htrdef : tr = √(Tp c χ k m) + δ) (hrb : tr ≤ b)
    (hatl : k * (1 + 1 / c) ≤ tl) {g : ℝ} (hg : 0 < g) (hgap : g ≤ tl - k)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ 1 + 1 / c) (hlo' : ξ₁ ≤ m * k) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψ : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ k / c * (√(2 * K / (√3 * √(c ^ 2 - χ))) * G / (m * k))
        + 16 * G * √(c / √(c ^ 2 - χ)) * (tl ^ 2 / m + 2 * k * √c / m ^ 2) / (9 * c ^ 2 * k ^ 3 * δ * m ^ 2)
        + 2 * δ * (G / √(c ^ 2 - χ) * √(2 / (√3 * (m ^ 2 * k * g))))
        + G * √(c / √(c ^ 2 - χ)) * (64 * k ^ 2 / (9 * m) + 32 * k ^ 2 * √k * √(tr - k) / 3)
          / (c ^ 2 * m ^ 2 * k ^ 3 * δ) := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hc0 : 0 < c := by linarith
  have hkm : 1 < k * m := by nlinarith
  have hd : 0 < c ^ 2 - χ := by linarith
  have hsd : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  set a := k * (1 + 1 / c) with ha
  have hic : 0 < 1 / c := by positivity
  have hka : k < a := by rw [ha]; nlinarith
  have hlr : tl ≤ tr := by rw [htldef, htrdef]; linarith
  have hab : a ≤ b := hatl.trans (hlr.trans hrb)
  have hak : a / k = 1 + 1 / c := by rw [ha]; field_simp
  have hkm1' : 1 ≤ m * k := by nlinarith
  have hTp := Tp_ge hc0 hk0 hm0 hkm1' hχ0 hχ.le
  have hT0 : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
  have hkS : k ≤ √(Tp c χ k m) := Real.le_sqrt_of_sq_le (by linarith)
  have hk2 : 0 < k ^ 2 - 1 / m ^ 2 := by
    rw [sub_pos, div_lt_iff₀ (by positivity)]; nlinarith
  -- D < 0 on [a, tl], D > 0 on [tr, b]
  have hmk : 0 < m ^ 2 - 1 / k ^ 2 := by
    have : 1 / k ^ 2 < m ^ 2 := by rw [div_lt_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hDL : ∀ τ ∈ Icc a tl, Dmr c χ m (1 / k) τ < 0 := fun τ hτ => by
    rw [Cvs.L2a.StationaryPairMismatchSign.Dmr_eq_Est hk0.ne' hm0.ne']
    have hE := Est_left (t := τ) hc0 hk0 hm0 hkm1' hχ0 hχ.le hδ (hka.le.trans hτ.1) (by rw [← htldef]; exact hτ.2)
    have : 0 < 2 * c ^ 2 * k * δ * (k ^ 2 - 1 / m ^ 2) := by positivity
    exact mul_neg_of_pos_of_neg hmk (by linarith)
  have hDR : ∀ τ ∈ Icc tr b, 0 < Dmr c χ m (1 / k) τ := fun τ hτ => by
    rw [Cvs.L2a.StationaryPairMismatchSign.Dmr_eq_Est hk0.ne' hm0.ne']
    have hE := Est_right (t := τ) hc0 hk0 hm0 hkm1' hχ0 hχ.le hδ (by rw [← htrdef]; exact hτ.1)
    have : 0 < 2 * c ^ 2 * √(Tp c χ k m) * δ * (k ^ 2 - 1 / m ^ 2) := by
      have : 0 < √(Tp c χ k m) := lt_of_lt_of_le hk0 hkS
      positivity
    exact mul_pos hmk (lt_of_lt_of_le this hE)
  -- the strip [k, a]
  have in1 : ∀ τ ∈ Icc k b, m * τ ∈ Icc ξ₁ Ξ := fun τ hτ =>
    ⟨hlo'.trans (mul_le_mul_of_nonneg_left hτ.1 hm0.le), le_trans (mul_le_mul_of_nonneg_left hτ.2 hm0.le) hhi⟩
  have hdiv : ∀ τ : ℝ, 1 / k * τ = τ / k := fun τ => by ring
  have hmk1 : 1 < m * k := by linarith
  have hval1 : ∀ τ ∈ Icc k a, |ψ (m * τ)| ≤ √(G / (√(c ^ 2 - χ) * ew (m * k))) := fun τ hτ => by
    have hξ := in1 τ ⟨hτ.1, hτ.2.trans hab⟩
    have hξ1 : 1 < m * τ := lt_of_lt_of_le hξ₁ hξ.1
    have ha' := aP_pos hξ1 (by positivity) hχ
    have h1 := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.sq_le_energy_div (ψ := ψ) (u := u) ha'
    have h2 : ψ (m * τ) ^ 2 ≤ G / (√(c ^ 2 - χ) * ew (m * k)) := by
      refine h1.trans ?_
      have lo := le_aP' hχ0 hχ hξ1.le
      have hmono := Cvs.L2a.StationaryEnvelopeMonotone.ew_mono hmk1.le (mul_le_mul_of_nonneg_left hτ.1 hm0.le)
      have hew := Cvs.L2a.StationaryEnvelopeMonotone.ew_pos hmk1
      calc energy (aP c χ) ψ u (m * τ) / aP c χ (m * τ) ≤ G / aP c χ (m * τ) :=
            div_le_div_of_nonneg_right (hG _ hξ) ha'.le
        _ ≤ G / (√(c ^ 2 - χ) * ew (m * k)) := by
            apply div_le_div_of_nonneg_left hG0 (by positivity)
            exact le_trans (mul_le_mul_of_nonneg_left hmono hsd.le) lo
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h2
  have inE : ∀ τ ∈ Icc k b, 1 / k * τ ∈ Icc 1 Ξ := fun τ hτ => by
    rw [hdiv]
    exact ⟨by rw [le_div_iff₀ hk0]; linarith [hτ.1], le_trans (div_le_div_of_nonneg_right hτ.2 hk0.le) hhi'⟩
  have hval2 : ∀ τ ∈ Icc k a, |ψ (1 / k * τ)| ≤ |ψ 1| := fun τ hτ => hedge _ (inE τ ⟨hτ.1, hτ.2.trans hab⟩)
  have hcf1 : ContinuousOn (fun τ => ψ (m * τ)) (Icc k b) := fun τ hτ =>
    ((hψ _ (in1 τ hτ)).continuousAt.comp (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  have hcf2 : ContinuousOn (fun τ => ψ (1 / k * τ)) (Icc k b) :=
    hcont.comp (continuousOn_const.mul continuousOn_id) (fun τ hτ => inE τ hτ)
  have strip := Cvs.L2a.StationaryCrossPairSplit.window_le hka.le (hcf1.mono (Icc_subset_Icc_right hab))
    (hcf2.mono (Icc_subset_Icc_right hab)) hval1 hval2
  have hw := Cvs.L2a.EdgeWindowPairMonomial.window_factor_le (σ := √(c ^ 2 - χ)) (ψ1 := ψ 1) hsd hG0 hK
    (by nlinarith) hm0 hk0 hedge1
  have hak' : a - k = k / c := by rw [ha]; field_simp; ring
  have hstrip : |∫ t in k..a, ψ (m * t) * ψ (1 / k * t)|
      ≤ k / c * (√(2 * K / (√3 * √(c ^ 2 - χ))) * G / (m * k)) := by
    refine strip.trans ?_
    rw [hak']; exact mul_le_mul_of_nonneg_left hw (by positivity)
  -- the rest by Cvs.L2a.StationaryEnvelopeMonotone
  have hmain := Cvs.L2a.StationaryEnvelopeMonotone.stationary_pair_le (c := c) (χ := χ) (G := G) (ξ₁ := ξ₁) (Ξ := Ξ)
    (k := k) (m := m) (a := a) (tl := tl) (tr := tr) (b := b) hc0 hχ0 hχ hk0 hm0 hkm hka hatl hlr hrb
    hξ₁ (by rw [hak]; exact hlo) (hlo'.trans (by nlinarith)) hhi hhi' hψ hu hG hDL hDR
  have hL := Cvs.L2a.ExactRootPairPieces.left_le (c := c) (χ := χ) (k := k) (m := m) (δ := δ) (G := G)
    (κ := c / √(c ^ 2 - χ)) (tl := tl) hc hχ0 hχ.le hk1 hkm2 hm hδ hG0 (by positivity) hatl (le_of_eq htldef)
  have hW := Cvs.L2a.ExactRootPairPieces.window_gap_le (σ := √(c ^ 2 - χ)) (G := G) (k := k) (m := m) (tl := tl)
    (δ := δ) hsd hG0 hk0 hm0 hδ.le (by nlinarith) hg hgap
  have hR := Cvs.L2a.ExactRootPairPieces.right_le (c := c) (χ := χ) (k := k) (m := m) (δ := δ) (G := G)
    (κ := c / √(c ^ 2 - χ)) (tr := tr) hc0 hχ0 hχ.le hk1 hkm2 hm hδ hδk hG0 (by positivity) htrdef
  have htrl : tr - tl = 2 * δ := by rw [htrdef, htldef]; ring
  rw [htrl] at hmain
  -- additivity
  have hcf : ContinuousOn (fun τ => ψ (m * τ) * ψ (1 / k * τ)) (Icc k b) := hcf1.mul hcf2
  have i1 : IntervalIntegrable (fun τ => ψ (m * τ) * ψ (1 / k * τ)) MeasureTheory.volume k a :=
    (hcf.mono (Icc_subset_Icc_right hab)).intervalIntegrable_of_Icc hka.le
  have i2 : IntervalIntegrable (fun τ => ψ (m * τ) * ψ (1 / k * τ)) MeasureTheory.volume a b :=
    (hcf.mono (Icc_subset_Icc_left hka.le)).intervalIntegrable_of_Icc hab
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  calc |(∫ t in k..a, ψ (m * t) * ψ (1 / k * t)) + ∫ t in a..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ |∫ t in k..a, ψ (m * t) * ψ (1 / k * t)| + |∫ t in a..b, ψ (m * t) * ψ (1 / k * t)| := abs_add_le _ _
    _ ≤ _ := add_le_add hstrip (hmain.trans (add_le_add (add_le_add hL hW) hR))
    _ = _ := by ring

end Cvs.L2a.ExactRootNearEdgePair
