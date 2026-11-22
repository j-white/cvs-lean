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
import Cvs.L2a.TwoProlateCrossBound
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
# The edge-window pair of two prolates

Cvs.L2a.EdgeStationaryPairWindow for the mode `m` of `ψ_a` and `1/k` of `ψ_b`: the window `[k, t_r]` by `|ψ_a| ≤ √(G/(σₘ ew))` and Sonin for
`ψ_b`, the right piece by Cvs.L2a.TwoProlateCrossBound with the two-prolate `D > 0`.
-/

namespace Cvs.L2a.TwoProlateEdgeWindowPair

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryEnvelopeMonotone Cvs.L2a.TwoProlateCrossBound Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi

/-- **The edge-window pair of two prolates.** -/
theorem edge_pair2_le {c χa χb χm G ξ₁ Ξ k m tr b : ℝ} {ψa ua ψb ub : ℝ → ℝ}
    (hc : 0 < c) (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2)
    (hk : 0 < k) (hm : 0 < m) (hkm : 1 < k * m) (hktr : k < tr) (hrb : tr ≤ b)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ tr / k) (hlo' : ξ₁ ≤ m * k) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψa : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χb) ψb ub ξ ≤ G)
    (hcontb : ContinuousOn ψb (Icc 1 Ξ)) (hedgeb : ∀ ξ ∈ Icc 1 Ξ, |ψb ξ| ≤ |ψb 1|)
    (hDR : ∀ τ ∈ Icc tr b, 0 < Dmr2 c χa χb m (1 / k) τ) :
    |∫ t in k..b, ψa (m * t) * ψb (1 / k * t)|
      ≤ (tr - k) * (√(G / (√(c ^ 2 - χm) * ew (m * k))) * |ψb 1|)
        + 2 * (pm m tr * (G * √(c / √(c ^ 2 - χm)) / m)
            + pm (1 / k) tr * (G / m * √(c / √(c ^ 2 - χm) * (ew (m * tr) / ew (tr / k))))) / Dmr2 c χa χb m (1 / k) tr := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hχa : χa < c ^ 2 := by linarith
  have hχb : χb < c ^ 2 := by linarith
  have hd : 0 < c ^ 2 - χm := by linarith
  have hsd : 0 < √(c ^ 2 - χm) := sqrt_pos.mpr hd
  have hr : (0 : ℝ) < 1 / k := by positivity
  have hrm : 1 / k < m := by rw [div_lt_iff₀ hk]; linarith
  set κ₀ := c / √(c ^ 2 - χm) with hκ₀
  have hdiv : ∀ τ : ℝ, 1 / k * τ = τ / k := fun τ => by ring
  have hmk1 : 1 < m * k := by linarith
  have hG0 : 0 ≤ G := by
    have hmem : ξ₁ ∈ Icc ξ₁ Ξ := ⟨le_rfl, hlo'.trans (le_trans (by nlinarith) hhi)⟩
    have ha := aP_pos hξ₁ hc2 hχa
    have := two_mul_abs_le_energy (ψ := ψa) (u := ua) ha
    linarith [hGa ξ₁ hmem, abs_nonneg (ψa ξ₁ * ua ξ₁)]
  -- the window [k, tr]
  have in1 : ∀ τ ∈ Icc k b, m * τ ∈ Icc ξ₁ Ξ := fun τ hτ =>
    ⟨hlo'.trans (by nlinarith [hτ.1]), le_trans (by nlinarith [hτ.2]) hhi⟩
  have hval1 : ∀ τ ∈ Icc k tr, |ψa (m * τ)| ≤ √(G / (√(c ^ 2 - χm) * ew (m * k))) := fun τ hτ => by
    have hξ := in1 τ ⟨hτ.1, hτ.2.trans hrb⟩
    have hξ1 : 1 < m * τ := lt_of_lt_of_le hξ₁ hξ.1
    have h2 := val_sq_le hχa0 hχam hχm hξ1 (hGa _ hξ)
    have hmono := ew_mono hmk1.le (by nlinarith [hτ.1] : m * k ≤ m * τ)
    have hew := Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi.ew_pos hmk1
    have h3 : ψa (m * τ) ^ 2 ≤ G / (√(c ^ 2 - χm) * ew (m * k)) :=
      h2.trans (div_le_div_of_nonneg_left hG0 (by positivity) (mul_le_mul_of_nonneg_left hmono hsd.le))
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h3
  have hval2 : ∀ τ ∈ Icc k tr, |ψb (1 / k * τ)| ≤ |ψb 1| := fun τ hτ => by
    apply hedgeb
    rw [hdiv]
    constructor
    · rw [le_div_iff₀ hk]; linarith [hτ.1]
    · exact le_trans (div_le_div_of_nonneg_right (hτ.2.trans hrb) hk.le) hhi'
  have hc1 : ContinuousOn (fun τ => ψa (m * τ)) (Icc k tr) := fun τ hτ => by
    have hξ := in1 τ ⟨hτ.1, hτ.2.trans hrb⟩
    exact ((hψa _ hξ).continuousAt.comp (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  have hc2' : ContinuousOn (fun τ => ψb (1 / k * τ)) (Icc k tr) := by
    apply hcontb.comp (continuousOn_const.mul continuousOn_id)
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
  have sysa : ∀ τ ∈ Icc tr b, HasDerivAt (fun t => ψa (m * t)) ((ua (m * τ) / m) / pm m τ) τ ∧
      HasDerivAt (fun t => ua (m * t) / m) (-(qm c χa m τ * ψa (m * τ))) τ := fun τ hτ =>
    Cvs.L2a.NonstationaryCrossPairClosed.scale_system hm (hψa _ (in1' τ hτ)) (hua _ (in1' τ hτ))
  have sysb : ∀ τ ∈ Icc tr b, HasDerivAt (fun t => ψb (1 / k * t)) ((ub (1 / k * τ) / (1 / k)) / pm (1 / k) τ) τ ∧
      HasDerivAt (fun t => ub (1 / k * t) / (1 / k)) (-(qm c χb (1 / k) τ * ψb (1 / k * τ))) τ := fun τ hτ =>
    Cvs.L2a.NonstationaryCrossPairClosed.scale_system hr (hψb _ (in2 τ hτ)) (hub _ (in2 τ hτ))
  have gt : ∀ τ ∈ Icc tr b, k < τ := fun τ hτ => lt_of_lt_of_le hktr hτ.1
  have arg1 : ∀ τ ∈ Icc tr b, 1 < m * τ := fun τ hτ => lt_of_lt_of_le hξ₁ (in1' τ hτ).1
  have arg2 : ∀ τ ∈ Icc tr b, 1 < 1 / k * τ := fun τ hτ => lt_of_lt_of_le hξ₁ (in2 τ hτ).1
  have hZ : ∀ τ ∈ Icc tr b, |ψa (m * τ) * (ub (1 / k * τ) / (1 / k))| ≤ G * √κ₀ / m := fun τ hτ => by
    have h := cross_env2 hc hχa0 hχam hχb0 hχbm hχm (arg1 τ hτ) (arg2 τ hτ) (hGa _ (in1' τ hτ)) (hGb _ (in2 τ hτ))
    have hr' := ratio_le hk hm hkm (gt τ hτ)
    rw [← hdiv] at hr'
    have e : ψa (m * τ) * (ub (1 / k * τ) / (1 / k)) = k * (ψa (m * τ) * ub (1 / k * τ)) := by field_simp
    rw [e, abs_mul, abs_of_pos hk]
    calc k * |ψa (m * τ) * ub (1 / k * τ)| ≤ k * (G * √(κ₀ * (ew (1 / k * τ) / ew (m * τ)))) :=
          mul_le_mul_of_nonneg_left h hk.le
      _ ≤ k * (G * √(κ₀ * (1 / (k ^ 2 * m ^ 2)))) := by gcongr
      _ = G * √κ₀ / m := by
          have e2 : √(κ₀ * (1 / (k ^ 2 * m ^ 2))) = √κ₀ * (1 / (k * m)) := by
            rw [sqrt_mul' _ (by positivity), show 1 / (k ^ 2 * m ^ 2) = (1 / (k * m)) ^ 2 by field_simp,
              sqrt_sq (by positivity)]
          rw [e2]; field_simp
  have hV : ∀ τ ∈ Icc tr b, |ua (m * τ) / m * ψb (1 / k * τ)| ≤ G / m * √(κ₀ * (ew (m * tr) / ew (tr / k))) :=
    fun τ hτ => by
    have h := cross_env2 hc hχb0 hχbm hχa0 hχam hχm (arg2 τ hτ) (arg1 τ hτ) (hGb _ (in2 τ hτ)) (hGa _ (in1' τ hτ))
    have hR := R_anti hk hm hkm hktr hτ.1
    rw [← hdiv] at hR
    have e : ua (m * τ) / m * ψb (1 / k * τ) = (ψb (1 / k * τ) * ua (m * τ)) / m := by ring
    rw [e, abs_div, abs_of_pos hm]
    have hκ : 0 ≤ κ₀ := by positivity
    calc |ψb (1 / k * τ) * ua (m * τ)| / m ≤ G * √(κ₀ * (ew (m * τ) / ew (1 / k * τ))) / m :=
          div_le_div_of_nonneg_right h hm.le
      _ ≤ G * √(κ₀ * (ew (m * tr) / ew (tr / k))) / m := by
          apply div_le_div_of_nonneg_right _ hm.le
          exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hR hκ)) hG0
      _ = G / m * √(κ₀ * (ew (m * tr) / ew (tr / k))) := by ring
  have right := prolate_cross2_le (c := c) (χ := χa) (χ' := χb) (m := m) (r := 1 / k)
    (f₁ := fun t => ψa (m * t)) (u₁ := fun t => ua (m * t) / m)
    (f₂ := fun t => ψb (1 / k * t)) (u₂ := fun t => ub (1 / k * t) / (1 / k)) hrb hr hrm
    (by rw [one_div_mul_eq_div, lt_div_iff₀ hk]; linarith) hχa hχb hDR
    (fun τ hτ => (sysa τ hτ).1) (fun τ hτ => (sysa τ hτ).2)
    (fun τ hτ => (sysb τ hτ).1) (fun τ hτ => (sysb τ hτ).2) hZ hV
  -- add the two pieces
  have hcf : ContinuousOn (fun τ => ψa (m * τ) * ψb (1 / k * τ)) (Icc k b) := by
    intro τ hτ
    have hξ := in1 τ hτ
    have h1 := ((hψa _ hξ).continuousAt.comp (continuousAt_const.mul continuousAt_id)).continuousWithinAt
      (s := Icc k b)
    have h2 : ContinuousWithinAt (fun τ => ψb (1 / k * τ)) (Icc k b) τ := by
      apply (hcontb.comp (continuousOn_const.mul continuousOn_id) ?_) τ hτ
      intro σ hσ; show 1 ≤ 1 / k * σ ∧ 1 / k * σ ≤ Ξ; rw [hdiv]
      exact ⟨by rw [le_div_iff₀ hk]; linarith [hσ.1],
        le_trans (div_le_div_of_nonneg_right hσ.2 hk.le) hhi'⟩
    exact h1.mul h2
  have i1 : IntervalIntegrable (fun τ => ψa (m * τ) * ψb (1 / k * τ)) MeasureTheory.volume k tr :=
    (hcf.mono (Icc_subset_Icc_right hrb)).intervalIntegrable_of_Icc hktr.le
  have i2 : IntervalIntegrable (fun τ => ψa (m * τ) * ψb (1 / k * τ)) MeasureTheory.volume tr b :=
    (hcf.mono (Icc_subset_Icc_left hktr.le)).intervalIntegrable_of_Icc hrb
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  exact (abs_add_le _ _).trans (add_le_add win right)

end Cvs.L2a.TwoProlateEdgeWindowPair
