import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.SigmaFreePairPieces
import Cvs.L2a.SigmaFreeStationaryEdgePairs
import Cvs.L2a.StationaryCrossPairSplit
import Cvs.L2a.StationaryMismatchExactRoots
import Cvs.L2a.StationaryPairMismatchSign
import Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree
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
# One near-edge stationary pair with `σ`-free envelopes, for every `χ < c²`

The strip `[k, k(1 + 1/c)]` by Sonin and `ψ(mτ)² ≤ G/((3/4)cm²τ²)`, then `SigmaFreeStationaryEdgePairs`'s stationary pair with `SigmaFreePairPieces`'s
left and right pieces and the window `2δ(G/c)√(2/(3m²kg))` for a gap `g ≤ t_l − k`: every piece is free of `σ`.
-/

namespace Cvs.L2a.SigmaFreeNearEdgePair

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryMismatchExactRoots

set_option maxHeartbeats 2000000 in
/-- **The near-edge pair with `σ`-free envelopes.** -/
theorem pairA_le {c χ G K ξ₁ Ξ k m δ tl tr b : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hδ : 0 < δ) (hδk : δ ≤ k / 2)
    (htldef : tl = √(Tp c χ k m) - δ) (htrdef : tr = √(Tp c χ k m) + δ) (hrb : tr ≤ b)
    (hatl : k * (1 + 1 / c) ≤ tl) {g : ℝ} (hg : 0 < g) (hgap : g ≤ tl - k)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ 1 + 1 / c) (hlo' : ξ₁ ≤ m * k) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψ : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ k / c * (G * √(4 * K / (3 * c)) / (m * k))
        + 16 / 9 * G * (tl ^ 2 * (2 / √3) / m + (Tp c χ k m - k ^ 2) * (√2 * k * √c)) / (m ^ 2 * c ^ 2 * k ^ 3 * δ)
        + 2 * δ * (G / c * √(2 / (3 * (m ^ 2 * k * g))))
        + 16 / 9 * G * (8 * k ^ 2 / (√3 * m) + 2 * √3 * k ^ 2 * √k * √(tr - k)) / (m ^ 2 * c ^ 2 * k ^ 3 * δ) := by
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
  have hval1 : ∀ τ ∈ Icc k a, |ψ (m * τ)| ≤ √(G / (3 / 4 * c * (m * k) ^ 2)) := fun τ hτ => by
    have hξ := in1 τ ⟨hτ.1, hτ.2.trans hab⟩
    have hmt : m * k ≤ m * τ := mul_le_mul_of_nonneg_left hτ.1 hm0.le
    have h2' : 2 ≤ m * τ := by linarith [mul_comm m k]
    have h := Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree.psi_sq_le (u := u) hc0 hχ.le h2' (hG _ hξ)
    have h2 : ψ (m * τ) ^ 2 ≤ G / (3 / 4 * c * (m * k) ^ 2) :=
      h.trans (div_le_div_of_nonneg_left hG0 (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmt 2) (by positivity)))
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
  have hw : √(G / (3 / 4 * c * (m * k) ^ 2)) * |ψ 1| ≤ G * √(4 * K / (3 * c)) / (m * k) := by
    have hp1 : |ψ 1| ≤ √(K * G) := Real.abs_le_sqrt hedge1
    calc √(G / (3 / 4 * c * (m * k) ^ 2)) * |ψ 1| ≤ √(G / (3 / 4 * c * (m * k) ^ 2)) * √(K * G) :=
          mul_le_mul_of_nonneg_left hp1 (sqrt_nonneg _)
      _ = G * √(4 * K / (3 * c)) / (m * k) := by
          rw [← sqrt_mul (by positivity), show G / (3 / 4 * c * (m * k) ^ 2) * (K * G)
            = (G / (m * k)) ^ 2 * (4 * K / (3 * c)) by field_simp, sqrt_mul (sq_nonneg _),
            sqrt_sq (by positivity)]
          ring
  have hak' : a - k = k / c := by rw [ha]; field_simp; ring
  have hstrip : |∫ t in k..a, ψ (m * t) * ψ (1 / k * t)|
      ≤ k / c * (G * √(4 * K / (3 * c)) / (m * k)) := by
    refine strip.trans ?_
    rw [hak']; exact mul_le_mul_of_nonneg_left hw (by positivity)
  -- the rest by Cvs.L2a.StationaryEnvelopeMonotone
  have hmain := Cvs.L2a.SigmaFreeStationaryEdgePairs.stationary_pair_le (c := c) (χ := χ) (G := G) (ξ₁ := ξ₁) (Ξ := Ξ)
    (k := k) (m := m) (a := a) (tl := tl) (tr := tr) (b := b) hc0 hχ0 hχ hk0 hm0 hkm2 hka hatl hlr hrb
    hξ₁ (by rw [hak]; exact hlo) (hlo'.trans (by nlinarith)) hhi hhi' hψ hu hG hDL hDR
  have hL := Cvs.L2a.SigmaFreePairPieces.left_le (c := c) (χ := χ) (k := k) (m := m) (δ := δ) (G := G)
    (tl := tl) hc hχ0 hχ.le hk1 hkm2 hm hδ hG0 hatl (le_of_eq htldef)
  have hW : 2 * δ * (√(G / (3 / 4 * c * (m * tl) ^ 2)) * √(G / (c * ((tl / k) ^ 2 - 1))))
      ≤ 2 * δ * (G / c * √(2 / (3 * (m ^ 2 * k * g)))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hkt : k < tl := by linarith
    have htl0 : 0 < tl := by linarith
    have hp : 2 * g / k ≤ (tl / k) ^ 2 - 1 := by
      have e : (tl / k) ^ 2 - 1 = (tl - k) * (tl + k) / k ^ 2 := by field_simp; ring
      have h2k : 2 * k ≤ tl + k := by linarith
      have hm2 := mul_le_mul hgap h2k (by linarith) (by linarith)
      rw [e, div_le_div_iff₀ hk0 (by positivity)]; nlinarith
    have hp0 : 0 < 2 * g / k := by positivity
    calc √(G / (3 / 4 * c * (m * tl) ^ 2)) * √(G / (c * ((tl / k) ^ 2 - 1)))
        ≤ √(G / (3 / 4 * c * (m * k) ^ 2)) * √(G / (c * (2 * g / k))) := by
          apply mul_le_mul (sqrt_le_sqrt (div_le_div_of_nonneg_left hG0 (by positivity)
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
              (mul_le_mul_of_nonneg_left hkt.le hm0.le) 2) (by positivity))))
            (sqrt_le_sqrt (div_le_div_of_nonneg_left hG0 (by positivity)
              (mul_le_mul_of_nonneg_left hp hc0.le))) (sqrt_nonneg _) (sqrt_nonneg _)
      _ = G / c * √(2 / (3 * (m ^ 2 * k * g))) := by
          rw [← sqrt_mul (by positivity), show G / (3 / 4 * c * (m * k) ^ 2) * (G / (c * (2 * g / k)))
            = (G / c) ^ 2 * (2 / (3 * (m ^ 2 * k * g))) by field_simp; ring, sqrt_mul (sq_nonneg _),
            sqrt_sq (by positivity)]
  have hR := Cvs.L2a.SigmaFreePairPieces.right_le (c := c) (χ := χ) (k := k) (m := m) (δ := δ) (G := G)
    (tr := tr) hc0 hχ0 hχ.le hk1 hkm2 hm hδ hδk hG0 htrdef
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

end Cvs.L2a.SigmaFreeNearEdgePair
