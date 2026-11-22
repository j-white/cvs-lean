import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.NonstationaryCrossPairClosed
import Cvs.L2a.StationaryCrossPairSplit
import Cvs.L2a.StationaryEnvelopeMonotone
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
# A stationary pair whose stationary point sits at the edge: one window from `k`

For the modes `m` and `1/k` on `[k, b]` with `D > 0` on `[t_r, b]`: the window `[k, t_r]` is at most
`(t_r − k) √(G/(√(c²−χ) ew(mk))) |ψ(1)|` (Sonin bounds the slow mode by its edge value) and the rest is `NonresonantCrossIntegral`'s
telescoped bound with the sups of Cvs.L2a.StationaryEnvelopeMonotone. Valid for every `t_r > k`; used where `km` is large.
-/

namespace Cvs.L2a.EdgeStationaryPairWindow

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryEnvelopeMonotone

/-- **The edge-window pair bound.** -/
theorem edge_pair_le {c χ G ξ₁ Ξ k m tr b : ℝ} {ψ u : ℝ → ℝ}
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk : 0 < k) (hm : 0 < m) (hkm : 1 < k * m)
    (hktr : k < tr) (hrb : tr ≤ b)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ tr / k) (hlo' : ξ₁ ≤ m * k) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψ : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χ) ψ u ξ ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|)
    (hDR : ∀ τ ∈ Icc tr b, 0 < Dmr c χ m (1 / k) τ) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ (tr - k) * (√(G / (√(c ^ 2 - χ) * ew (m * k))) * |ψ 1|)
        + 2 * (pm m tr * (G * √(c / √(c ^ 2 - χ)) / m)
            + pm (1 / k) tr * (G / m * √(c / √(c ^ 2 - χ) * (ew (m * tr) / ew (tr / k))))) / Dmr c χ m (1 / k) tr := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hd : 0 < c ^ 2 - χ := by linarith
  have hsd : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  have hr : (0 : ℝ) < 1 / k := by positivity
  have hrm : 1 / k < m := by rw [div_lt_iff₀ hk]; linarith
  have hkb : k ≤ b := hktr.le.trans hrb
  set κ₀ := c / √(c ^ 2 - χ) with hκ₀
  have hdiv : ∀ τ : ℝ, 1 / k * τ = τ / k := fun τ => by ring
  have hmk1 : 1 < m * k := by linarith
  have hG0 : 0 ≤ G := by
    have hmem : ξ₁ ∈ Icc ξ₁ Ξ := ⟨le_rfl, hlo'.trans (le_trans (by nlinarith) hhi)⟩
    have ha := aP_pos hξ₁ hc2 hχ
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) ha
    linarith [hG ξ₁ hmem, abs_nonneg (ψ ξ₁ * u ξ₁)]
  -- the window [k, tr]
  have in1 : ∀ τ ∈ Icc k b, m * τ ∈ Icc ξ₁ Ξ := fun τ hτ =>
    ⟨hlo'.trans (by nlinarith [hτ.1]), le_trans (by nlinarith [hτ.2]) hhi⟩
  have hval1 : ∀ τ ∈ Icc k tr, |ψ (m * τ)| ≤ √(G / (√(c ^ 2 - χ) * ew (m * k))) := fun τ hτ => by
    have hτ' : τ ∈ Icc k b := ⟨hτ.1, hτ.2.trans hrb⟩
    have hξ := in1 τ hτ'
    have hξ1 : 1 < m * τ := lt_of_lt_of_le hξ₁ hξ.1
    have ha := aP_pos hξ1 hc2 hχ
    have h1 := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.sq_le_energy_div (ψ := ψ) (u := u) ha
    have h2 : ψ (m * τ) ^ 2 ≤ G / (√(c ^ 2 - χ) * ew (m * k)) := by
      refine h1.trans ?_
      have lo := le_aP' hχ0 hχ hξ1.le
      have hmono := ew_mono hmk1.le (by nlinarith [hτ.1] : m * k ≤ m * τ)
      have hew := ew_pos hmk1
      calc energy (aP c χ) ψ u (m * τ) / aP c χ (m * τ) ≤ G / aP c χ (m * τ) :=
            div_le_div_of_nonneg_right (hG _ hξ) ha.le
        _ ≤ G / (√(c ^ 2 - χ) * ew (m * k)) := by
            apply div_le_div_of_nonneg_left hG0 (by positivity)
            exact le_trans (mul_le_mul_of_nonneg_left hmono hsd.le) lo
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h2
  have hval2 : ∀ τ ∈ Icc k tr, |ψ (1 / k * τ)| ≤ |ψ 1| := fun τ hτ => by
    apply hedge
    rw [hdiv]
    constructor
    · rw [le_div_iff₀ hk]; linarith [hτ.1]
    · exact le_trans (div_le_div_of_nonneg_right (hτ.2.trans hrb) hk.le) hhi'
  have hc1 : ContinuousOn (fun τ => ψ (m * τ)) (Icc k tr) := fun τ hτ => by
    have hξ := in1 τ ⟨hτ.1, hτ.2.trans hrb⟩
    exact ((hψ _ hξ).continuousAt.comp (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  have hc2' : ContinuousOn (fun τ => ψ (1 / k * τ)) (Icc k tr) := by
    apply hcont.comp (continuousOn_const.mul continuousOn_id)
    intro τ hτ
    show 1 ≤ 1 / k * τ ∧ 1 / k * τ ≤ Ξ
    rw [hdiv]
    constructor
    · rw [le_div_iff₀ hk]; linarith [hτ.1]
    · exact le_trans (div_le_div_of_nonneg_right (hτ.2.trans hrb) hk.le) hhi'
  have win := Cvs.L2a.StationaryCrossPairSplit.window_le hktr.le hc1 hc2' hval1 hval2
  -- the right piece [tr, b]
  have in1' : ∀ τ ∈ Icc tr b, m * τ ∈ Icc ξ₁ Ξ := fun τ hτ => in1 τ ⟨hktr.le.trans hτ.1, hτ.2⟩
  have in2 : ∀ τ ∈ Icc tr b, 1 / k * τ ∈ Icc ξ₁ Ξ := fun τ hτ => by
    rw [hdiv]
    exact ⟨hlo.trans (div_le_div_of_nonneg_right hτ.1 hk.le),
      le_trans (div_le_div_of_nonneg_right hτ.2 hk.le) hhi'⟩
  have sys : ∀ s : ℝ, 0 < s → (∀ τ ∈ Icc tr b, s * τ ∈ Icc ξ₁ Ξ) → ∀ τ ∈ Icc tr b,
      HasDerivAt (fun t => ψ (s * t)) ((u (s * τ) / s) / pm s τ) τ ∧
      HasDerivAt (fun t => u (s * t) / s) (-(qm c χ s τ * ψ (s * τ))) τ := fun s hs hin τ hτ =>
    Cvs.L2a.NonstationaryCrossPairClosed.scale_system hs (hψ _ (hin τ hτ)) (hu _ (hin τ hτ))
  have gt : ∀ τ ∈ Icc tr b, k < τ := fun τ hτ => lt_of_lt_of_le hktr hτ.1
  have arg1 : ∀ τ ∈ Icc tr b, 1 < m * τ := fun τ hτ => lt_of_lt_of_le hξ₁ (in1' τ hτ).1
  have arg2 : ∀ τ ∈ Icc tr b, 1 < 1 / k * τ := fun τ hτ => lt_of_lt_of_le hξ₁ (in2 τ hτ).1
  have hZ : ∀ τ ∈ Icc tr b, |ψ (m * τ) * (u (1 / k * τ) / (1 / k))| ≤ G * √κ₀ / m := fun τ hτ => by
    have h := cross_env' hc hχ0 hχ (arg1 τ hτ) (arg2 τ hτ) (hG _ (in1' τ hτ)) (hG _ (in2 τ hτ))
    have hr' := ratio_le hk hm hkm (gt τ hτ)
    rw [← hdiv] at hr'
    have e : ψ (m * τ) * (u (1 / k * τ) / (1 / k)) = k * (ψ (m * τ) * u (1 / k * τ)) := by field_simp
    rw [e, abs_mul, abs_of_pos hk]
    calc k * |ψ (m * τ) * u (1 / k * τ)| ≤ k * (G * √(κ₀ * (ew (1 / k * τ) / ew (m * τ)))) :=
          mul_le_mul_of_nonneg_left h hk.le
      _ ≤ k * (G * √(κ₀ * (1 / (k ^ 2 * m ^ 2)))) := by gcongr
      _ = G * √κ₀ / m := by
          have e2 : √(κ₀ * (1 / (k ^ 2 * m ^ 2))) = √κ₀ * (1 / (k * m)) := by
            rw [sqrt_mul' _ (by positivity), show 1 / (k ^ 2 * m ^ 2) = (1 / (k * m)) ^ 2 by field_simp,
              sqrt_sq (by positivity)]
          rw [e2]; field_simp
  have hV : ∀ τ ∈ Icc tr b, |u (m * τ) / m * ψ (1 / k * τ)| ≤ G / m * √(κ₀ * (ew (m * tr) / ew (tr / k))) :=
    fun τ hτ => by
    have h := cross_env' hc hχ0 hχ (arg2 τ hτ) (arg1 τ hτ) (hG _ (in2 τ hτ)) (hG _ (in1' τ hτ))
    have hR := R_anti hk hm hkm hktr hτ.1
    rw [← hdiv] at hR
    have e : u (m * τ) / m * ψ (1 / k * τ) = (ψ (1 / k * τ) * u (m * τ)) / m := by ring
    rw [e, abs_div, abs_of_pos hm]
    have hκ : 0 ≤ κ₀ := by positivity
    calc |ψ (1 / k * τ) * u (m * τ)| / m ≤ G * √(κ₀ * (ew (m * τ) / ew (1 / k * τ))) / m :=
          div_le_div_of_nonneg_right h hm.le
      _ ≤ G * √(κ₀ * (ew (m * tr) / ew (tr / k))) / m := by
          apply div_le_div_of_nonneg_right _ hm.le
          exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hR hκ)) hG0
      _ = G / m * √(κ₀ * (ew (m * tr) / ew (tr / k))) := by ring
  have right := prolate_cross_le (c := c) (χ := χ) (m := m) (r := 1 / k)
    (f₁ := fun t => ψ (m * t)) (u₁ := fun t => u (m * t) / m)
    (f₂ := fun t => ψ (1 / k * t)) (u₂ := fun t => u (1 / k * t) / (1 / k)) hrb hr hrm
    (by rw [one_div_mul_eq_div, lt_div_iff₀ hk]; linarith) hχ hDR
    (fun τ hτ => (sys m hm in1' τ hτ).1) (fun τ hτ => (sys m hm in1' τ hτ).2)
    (fun τ hτ => (sys (1 / k) hr in2 τ hτ).1) (fun τ hτ => (sys (1 / k) hr in2 τ hτ).2) hZ hV
  -- add the two pieces
  have hcf : ContinuousOn (fun τ => ψ (m * τ) * ψ (1 / k * τ)) (Icc k b) := by
    intro τ hτ
    have hξ := in1 τ hτ
    have h1 := ((hψ _ hξ).continuousAt.comp (continuousAt_const.mul continuousAt_id)).continuousWithinAt
      (s := Icc k b)
    have h2 : ContinuousWithinAt (fun τ => ψ (1 / k * τ)) (Icc k b) τ := by
      apply (hcont.comp (continuousOn_const.mul continuousOn_id) ?_) τ hτ
      intro σ hσ; show 1 ≤ 1 / k * σ ∧ 1 / k * σ ≤ Ξ; rw [hdiv]
      exact ⟨by rw [le_div_iff₀ hk]; linarith [hσ.1],
        le_trans (div_le_div_of_nonneg_right hσ.2 hk.le) hhi'⟩
    exact h1.mul h2
  have i1 : IntervalIntegrable (fun τ => ψ (m * τ) * ψ (1 / k * τ)) MeasureTheory.volume k tr :=
    (hcf.mono (Icc_subset_Icc_right hrb)).intervalIntegrable_of_Icc hktr.le
  have i2 : IntervalIntegrable (fun τ => ψ (m * τ) * ψ (1 / k * τ)) MeasureTheory.volume tr b :=
    (hcf.mono (Icc_subset_Icc_left hktr.le)).intervalIntegrable_of_Icc hrb
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  exact (abs_add_le _ _).trans (add_le_add win right)

end Cvs.L2a.EdgeStationaryPairWindow
