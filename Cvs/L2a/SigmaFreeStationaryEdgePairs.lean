import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.NonstationaryCrossPairClosed
import Cvs.L2a.StationaryCrossPairSplit
import Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset
import Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree
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
# The stationary and edge-window pairs with envelopes free of `σ`

For the modes `m` (`mk ≥ 2`) and `1/k`: the value-times-flux sup is `|ψ(mτ)·k u(τ/k)| ≤ (2/√3)G/m`, the
flux-times-value sup past `t₀ > k` is `|u(mτ)/m·ψ(τ/k)| ≤ Gkt₀/√(t₀² − k²)`, and on a window `ψ(mτ)² ≤ G/((3/4)c m²τ²)`,
`ψ(τ/k)² ≤ G/(c((τ/k)² − 1))`; Cvs.L2a.StationaryEnvelopeMonotone and Cvs.L2a.EdgeStationaryPairWindow hold with these in place of the `σ`-envelopes, for every `χ < c²`.
-/

namespace Cvs.L2a.SigmaFreeStationaryEdgePairs

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryEnvelopeMonotone

/-- **The value-times-flux sup**: `|ψ(mτ)·k u(τ/k)| ≤ (2/√3)G/m` for `τ > k`, `mτ ≥ 2`. -/
theorem Z_le {c χ G k m τ : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk : 0 < k)
    (hm : 0 < m) (hkτ : k < τ) (h1 : 2 ≤ m * τ) (h2 : 1 < 1 / k * τ)
    (hG1 : energy (aP c χ) ψ u (m * τ) ≤ G) (hG2 : energy (aP c χ) ψ u (1 / k * τ) ≤ G) :
    |ψ (m * τ) * (u (1 / k * τ) / (1 / k))| ≤ 2 / √3 * G / m := by
  have hτ : 0 < τ := hk.trans hkτ
  have e1 := Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree.psi_sq_le (u := u) hc hχ.le h1 hG1
  have e2 := Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi.flux_sq_le hc hχ0 hχ h2 hG2
  have hG : 0 ≤ G := by
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos h2 (by positivity) hχ)
    linarith [abs_nonneg (ψ (1 / k * τ) * u (1 / k * τ))]
  have hew : ew (1 / k * τ) ≤ (1 / k * τ) ^ 2 := by
    unfold ew
    have hx : 0 < 1 / k * τ := by positivity
    have : √((1 / k * τ) ^ 2 - 1) ≤ 1 / k * τ := by rw [sqrt_le_left hx.le]; linarith
    nlinarith
  have e : ψ (m * τ) * (u (1 / k * τ) / (1 / k)) = k * (ψ (m * τ) * u (1 / k * τ)) := by field_simp
  rw [e, abs_mul, abs_of_pos hk, ← sqrt_sq_eq_abs]
  have hs3 : 0 < √3 := by positivity
  have h33 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  rw [show k * √((ψ (m * τ) * u (1 / k * τ)) ^ 2) = √(k ^ 2 * (ψ (m * τ) * u (1 / k * τ)) ^ 2) by
    rw [sqrt_mul (sq_nonneg _), sqrt_sq hk.le]]
  rw [show 2 / √3 * G / m = √((2 / √3 * G / m) ^ 2) by rw [sqrt_sq (by positivity)]]
  apply sqrt_le_sqrt
  calc k ^ 2 * (ψ (m * τ) * u (1 / k * τ)) ^ 2 = k ^ 2 * (ψ (m * τ) ^ 2 * u (1 / k * τ) ^ 2) := by ring
    _ ≤ k ^ 2 * (G / (3 / 4 * c * (m * τ) ^ 2) * (c * ew (1 / k * τ) * G)) := by
        gcongr
    _ ≤ k ^ 2 * (G / (3 / 4 * c * (m * τ) ^ 2) * (c * (1 / k * τ) ^ 2 * G)) := by gcongr
    _ = (2 / √3 * G / m) ^ 2 := by field_simp; rw [h33]; ring

/-- **The flux-times-value sup past `t₀`**: `|u(mτ)/m·ψ(τ/k)| ≤ Gkt₀/√(t₀² − k²)` for `τ ≥ t₀ > k`. -/
theorem V_le {c χ G k m t₀ τ : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk : 0 < k)
    (hm : 0 < m) (hkt : k < t₀) (htτ : t₀ ≤ τ) (h1 : 1 < m * τ) (h2 : 1 < 1 / k * τ)
    (hG1 : energy (aP c χ) ψ u (m * τ) ≤ G) (hG2 : energy (aP c χ) ψ u (1 / k * τ) ≤ G) :
    |u (m * τ) / m * ψ (1 / k * τ)| ≤ G * k * t₀ / √(t₀ ^ 2 - k ^ 2) := by
  have hτ : 0 < τ := hk.trans (hkt.trans_le htτ)
  have h := Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset.flux_val_le (ψa := ψ) (ub := u) hc hχ0 hχ hχ h1 h2 hG1 hG2
  have hG : 0 ≤ G := by
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos h2 (by positivity) hχ)
    linarith [abs_nonneg (ψ (1 / k * τ) * u (1 / k * τ))]
  have hew : ew (m * τ) ≤ (m * τ) ^ 2 := by
    unfold ew
    have hx : 0 < m * τ := by positivity
    have : √((m * τ) ^ 2 - 1) ≤ m * τ := by rw [sqrt_le_left hx.le]; linarith
    nlinarith
  have hd0 : 0 < t₀ ^ 2 - k ^ 2 := by nlinarith
  have hp : (1 / k * τ) ^ 2 - 1 = (τ ^ 2 - k ^ 2) / k ^ 2 := by field_simp
  have hp0 : 0 < τ ^ 2 - k ^ 2 := by nlinarith
  -- `τ²/(τ² − k²) ≤ t₀²/(t₀² − k²)`
  have hmono : τ ^ 2 / (τ ^ 2 - k ^ 2) ≤ t₀ ^ 2 / (t₀ ^ 2 - k ^ 2) := by
    rw [div_le_div_iff₀ hp0 hd0]; nlinarith [pow_le_pow_left₀ (hk.trans hkt).le htτ 2]
  have hR : ew (m * τ) / ((1 / k * τ) ^ 2 - 1) ≤ m ^ 2 * k ^ 2 * (t₀ ^ 2 / (t₀ ^ 2 - k ^ 2)) := by
    rw [hp]
    calc ew (m * τ) / ((τ ^ 2 - k ^ 2) / k ^ 2) ≤ (m * τ) ^ 2 / ((τ ^ 2 - k ^ 2) / k ^ 2) :=
          div_le_div_of_nonneg_right hew (by positivity)
      _ = m ^ 2 * k ^ 2 * (τ ^ 2 / (τ ^ 2 - k ^ 2)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by positivity)
  have e : u (m * τ) / m * ψ (1 / k * τ) = (u (m * τ) * ψ (1 / k * τ)) / m := by ring
  rw [e, abs_div, abs_of_pos hm, div_le_iff₀ hm]
  calc |u (m * τ) * ψ (1 / k * τ)| ≤ G * √(ew (m * τ) / ((1 / k * τ) ^ 2 - 1)) := h
    _ ≤ G * √(m ^ 2 * k ^ 2 * (t₀ ^ 2 / (t₀ ^ 2 - k ^ 2))) := by gcongr
    _ = G * k * t₀ / √(t₀ ^ 2 - k ^ 2) * m := by
        rw [sqrt_mul (by positivity), sqrt_div' _ hd0.le, show m ^ 2 * k ^ 2 = (m * k) ^ 2 by ring,
          sqrt_sq (by positivity), sqrt_sq (by linarith)]
        field_simp

/-- **The stationary pair with `σ`-free envelopes.** -/
theorem stationary_pair_le {c χ G ξ₁ Ξ k m a tl tr b : ℝ} {ψ u : ℝ → ℝ}
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk : 0 < k) (hm : 0 < m) (hkm : 2 ≤ k * m)
    (hka : k < a) (hal : a ≤ tl) (hlr : tl ≤ tr) (hrb : tr ≤ b)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ a / k) (hlo' : ξ₁ ≤ m * a) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψ : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χ) ψ u ξ ≤ G)
    (hDL : ∀ τ ∈ Icc a tl, Dmr c χ m (1 / k) τ < 0) (hDR : ∀ τ ∈ Icc tr b, 0 < Dmr c χ m (1 / k) τ) :
    |∫ t in a..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ 2 * (-(pm m tl / Dmr c χ m (1 / k) tl) * (2 / √3 * G / m)
            + -(pm (1 / k) tl / Dmr c χ m (1 / k) tl) * (G * k * a / √(a ^ 2 - k ^ 2)))
        + (tr - tl) * (√(G / (3 / 4 * c * (m * tl) ^ 2)) * √(G / (c * ((tl / k) ^ 2 - 1))))
        + 2 * (pm m tr * (2 / √3 * G / m)
            + pm (1 / k) tr * (G * k * tr / √(tr ^ 2 - k ^ 2))) / Dmr c χ m (1 / k) tr := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hd : 0 < c ^ 2 - χ := by linarith
  have hsd : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  have hr : (0 : ℝ) < 1 / k := by positivity
  have hrm : 1 / k < m := by rw [div_lt_iff₀ hk]; linarith
  have hkm1 : 1 < k * m := by linarith
  have hra : 1 < 1 / k * a := by rw [one_div_mul_eq_div, lt_div_iff₀ hk]; linarith
  have hG0 : 0 ≤ G := by
    have hmem : ξ₁ ∈ Icc ξ₁ Ξ := ⟨le_rfl, hlo.trans (by
      have : a / k ≤ b / k := div_le_div_of_nonneg_right (hal.trans (hlr.trans hrb)) hk.le
      linarith)⟩
    have ha := aP_pos hξ₁ hc2 hχ
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) ha
    linarith [hG ξ₁ hmem, abs_nonneg (ψ ξ₁ * u ξ₁)]
  -- arguments of both modes stay in [ξ₁, Ξ] and above 1
  have in1 : ∀ τ ∈ Icc a b, m * τ ∈ Icc ξ₁ Ξ := fun τ hτ =>
    ⟨hlo'.trans (by nlinarith [hτ.1]), le_trans (by nlinarith [hτ.2]) hhi⟩
  have in2 : ∀ τ ∈ Icc a b, 1 / k * τ ∈ Icc ξ₁ Ξ := fun τ hτ => by
    constructor
    · calc ξ₁ ≤ a / k := hlo
        _ ≤ τ / k := div_le_div_of_nonneg_right hτ.1 hk.le
        _ = 1 / k * τ := by ring
    · calc 1 / k * τ = τ / k := by ring
        _ ≤ b / k := div_le_div_of_nonneg_right hτ.2 hk.le
        _ ≤ Ξ := hhi'
  have sys : ∀ s : ℝ, 0 < s → (∀ τ ∈ Icc a b, s * τ ∈ Icc ξ₁ Ξ) → ∀ τ ∈ Icc a b,
      HasDerivAt (fun t => ψ (s * t)) ((u (s * τ) / s) / pm s τ) τ ∧
      HasDerivAt (fun t => u (s * t) / s) (-(qm c χ s τ * ψ (s * τ))) τ := fun s hs hin τ hτ =>
    Cvs.L2a.NonstationaryCrossPairClosed.scale_system hs (hψ _ (hin τ hτ)) (hu _ (hin τ hτ))
  have gt1 : ∀ τ ∈ Icc a b, k < τ := fun τ hτ => lt_of_lt_of_le hka hτ.1
  have arg1 : ∀ τ ∈ Icc a b, 1 < m * τ := fun τ hτ => lt_of_lt_of_le hξ₁ (in1 τ hτ).1
  have arg2 : ∀ τ ∈ Icc a b, 1 < 1 / k * τ := fun τ hτ => lt_of_lt_of_le hξ₁ (in2 τ hτ).1
  have hdiv : ∀ τ : ℝ, 1 / k * τ = τ / k := fun τ => by ring
  have arg1' : ∀ τ ∈ Icc a b, 2 ≤ m * τ := fun τ hτ => by
    have : k * m ≤ m * τ := by nlinarith [gt1 τ hτ]
    linarith
  -- the value-times-flux sups
  have hZ : ∀ τ ∈ Icc a b, |ψ (m * τ) * (u (1 / k * τ) / (1 / k))| ≤ 2 / √3 * G / m := fun τ hτ =>
    Z_le hc hχ0 hχ hk hm (gt1 τ hτ) (arg1' τ hτ) (arg2 τ hτ) (hG _ (in1 τ hτ)) (hG _ (in2 τ hτ))
  have hV : ∀ t₀ ∈ Icc a b, ∀ τ ∈ Icc t₀ b,
      |u (m * τ) / m * ψ (1 / k * τ)| ≤ G * k * t₀ / √(t₀ ^ 2 - k ^ 2) := fun t₀ ht₀ τ hτ => by
    have hτ' : τ ∈ Icc a b := ⟨ht₀.1.trans hτ.1, hτ.2⟩
    exact V_le hc hχ0 hχ hk hm (gt1 t₀ ht₀) hτ.1 (arg1 τ hτ') (arg2 τ hτ') (hG _ (in1 τ hτ')) (hG _ (in2 τ hτ'))
  -- the value sups on the window
  have hval1 : ∀ τ ∈ Icc tl tr, |ψ (m * τ)| ≤ √(G / (3 / 4 * c * (m * tl) ^ 2)) := fun τ hτ => by
    have hτ' : τ ∈ Icc a b := ⟨hal.trans hτ.1, hτ.2.trans hrb⟩
    have h := Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree.psi_sq_le (u := u) hc hχ.le (arg1' τ hτ') (hG _ (in1 τ hτ'))
    have hmt : m * tl ≤ m * τ := mul_le_mul_of_nonneg_left hτ.1 hm.le
    have htl0 : 0 < m * tl := mul_pos hm (hk.trans (gt1 tl ⟨hal, hlr.trans hrb⟩))
    have h2 : ψ (m * τ) ^ 2 ≤ G / (3 / 4 * c * (m * tl) ^ 2) :=
      h.trans (div_le_div_of_nonneg_left hG0 (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htl0.le hmt 2) (by positivity)))
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h2
  have hval2 : ∀ τ ∈ Icc tl tr, |ψ (1 / k * τ)| ≤ √(G / (c * ((tl / k) ^ 2 - 1))) := fun τ hτ => by
    have hτ' : τ ∈ Icc a b := ⟨hal.trans hτ.1, hτ.2.trans hrb⟩
    have h := Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset.psi_sq_le_edge (u := u) hc hχ (arg2 τ hτ') (hG _ (in2 τ hτ'))
    have htl1 : 1 < tl / k := by rw [← hdiv]; exact arg2 tl ⟨hal, hlr.trans hrb⟩
    have hle : tl / k ≤ 1 / k * τ := by rw [hdiv]; exact div_le_div_of_nonneg_right hτ.1 hk.le
    have hp : 0 < (tl / k) ^ 2 - 1 := by nlinarith
    have h2 : ψ (1 / k * τ) ^ 2 ≤ G / (c * ((tl / k) ^ 2 - 1)) := by
      refine h.trans (div_le_div_of_nonneg_left hG0 (by positivity) ?_)
      apply mul_le_mul_of_nonneg_left _ hc.le
      nlinarith
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h2
  have key := Cvs.L2a.StationaryCrossPairSplit.prolate_stationary_le (c := c) (χ := χ) (m := m) (r := 1 / k)
    (f₁ := fun t => ψ (m * t)) (u₁ := fun t => u (m * t) / m)
    (f₂ := fun t => ψ (1 / k * t)) (u₂ := fun t => u (1 / k * t) / (1 / k))
    (MzL := 2 / √3 * G / m) (MvL := G * k * a / √(a ^ 2 - k ^ 2))
    (MzR := 2 / √3 * G / m) (MvR := G * k * tr / √(tr ^ 2 - k ^ 2))
    (F₁ := √(G / (3 / 4 * c * (m * tl) ^ 2))) (F₂ := √(G / (c * ((tl / k) ^ 2 - 1))))
    hr hrm hra hχ hal hlr hrb hDL hDR
    (fun τ hτ => (sys m hm in1 τ hτ).1) (fun τ hτ => (sys m hm in1 τ hτ).2)
    (fun τ hτ => (sys (1 / k) hr in2 τ hτ).1) (fun τ hτ => (sys (1 / k) hr in2 τ hτ).2)
    (fun τ hτ => hZ τ ⟨hτ.1, hτ.2.trans (hlr.trans hrb)⟩)
    (fun τ hτ => hV a ⟨le_rfl, hal.trans (hlr.trans hrb)⟩ τ ⟨hτ.1, hτ.2.trans (hlr.trans hrb)⟩)
    (fun τ hτ => hZ τ ⟨hal.trans (hlr.trans hτ.1), hτ.2⟩)
    (fun τ hτ => hV tr ⟨hal.trans hlr, hrb⟩ τ hτ)
    hval1 hval2
  simpa using key

/-- **The edge-window pair with `σ`-free envelopes.** -/
theorem edge_pair_le {c χ G ξ₁ Ξ k m tr b : ℝ} {ψ u : ℝ → ℝ}
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk : 0 < k) (hm : 0 < m) (hkm : 2 ≤ k * m)
    (hktr : k < tr) (hrb : tr ≤ b)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ tr / k) (hlo' : ξ₁ ≤ m * k) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψ : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χ) ψ u ξ ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|)
    (hDR : ∀ τ ∈ Icc tr b, 0 < Dmr c χ m (1 / k) τ) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ (tr - k) * (√(G / (3 / 4 * c * (m * k) ^ 2)) * |ψ 1|)
        + 2 * (pm m tr * (2 / √3 * G / m)
            + pm (1 / k) tr * (G * k * tr / √(tr ^ 2 - k ^ 2))) / Dmr c χ m (1 / k) tr := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hd : 0 < c ^ 2 - χ := by linarith
  have hsd : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  have hr : (0 : ℝ) < 1 / k := by positivity
  have hrm : 1 / k < m := by rw [div_lt_iff₀ hk]; linarith
  have hkb : k ≤ b := hktr.le.trans hrb
  have hdiv : ∀ τ : ℝ, 1 / k * τ = τ / k := fun τ => by ring
  have hmk1 : 1 < m * k := by linarith
  have hkm1 : 1 < k * m := by linarith
  have hG0 : 0 ≤ G := by
    have hmem : ξ₁ ∈ Icc ξ₁ Ξ := ⟨le_rfl, hlo'.trans (le_trans (by nlinarith) hhi)⟩
    have ha := aP_pos hξ₁ hc2 hχ
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) ha
    linarith [hG ξ₁ hmem, abs_nonneg (ψ ξ₁ * u ξ₁)]
  -- the window [k, tr]
  have in1 : ∀ τ ∈ Icc k b, m * τ ∈ Icc ξ₁ Ξ := fun τ hτ =>
    ⟨hlo'.trans (by nlinarith [hτ.1]), le_trans (by nlinarith [hτ.2]) hhi⟩
  have hval1 : ∀ τ ∈ Icc k tr, |ψ (m * τ)| ≤ √(G / (3 / 4 * c * (m * k) ^ 2)) := fun τ hτ => by
    have hτ' : τ ∈ Icc k b := ⟨hτ.1, hτ.2.trans hrb⟩
    have hmt : m * k ≤ m * τ := mul_le_mul_of_nonneg_left hτ.1 hm.le
    have h2' : 2 ≤ m * τ := by linarith [mul_comm m k]
    have h := Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree.psi_sq_le (u := u) hc hχ.le h2' (hG _ (in1 τ hτ'))
    have h2 : ψ (m * τ) ^ 2 ≤ G / (3 / 4 * c * (m * k) ^ 2) :=
      h.trans (div_le_div_of_nonneg_left hG0 (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmt 2) (by positivity)))
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
  have arg1' : ∀ τ ∈ Icc tr b, 2 ≤ m * τ := fun τ hτ => by
    have : k * m ≤ m * τ := by nlinarith [gt τ hτ]
    linarith
  have hZ : ∀ τ ∈ Icc tr b, |ψ (m * τ) * (u (1 / k * τ) / (1 / k))| ≤ 2 / √3 * G / m := fun τ hτ =>
    Z_le hc hχ0 hχ hk hm (gt τ hτ) (arg1' τ hτ) (arg2 τ hτ) (hG _ (in1' τ hτ)) (hG _ (in2 τ hτ))
  have hV : ∀ τ ∈ Icc tr b, |u (m * τ) / m * ψ (1 / k * τ)| ≤ G * k * tr / √(tr ^ 2 - k ^ 2) := fun τ hτ =>
    V_le hc hχ0 hχ hk hm hktr hτ.1 (arg1 τ hτ) (arg2 τ hτ) (hG _ (in1' τ hτ)) (hG _ (in2 τ hτ))
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

end Cvs.L2a.SigmaFreeStationaryEdgePairs
