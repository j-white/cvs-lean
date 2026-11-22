import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.NonstationaryCrossPairClosed
import Cvs.L2a.StationaryEnvelopeMonotone
import Cvs.L2a.TwoProlateCrossBound
import Cvs.L2a.TwoProlateStationarySplit
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
# Envelopes of a prolate whose `χ` is at most `χₘ`

For `0 ≤ χ ≤ χₘ < c²`, `ξ > 1` and energy `≤ G`: `ψ(ξ)² ≤ G/(σₘ ew(ξ))`, `u(ξ)² ≤ c ew(ξ) G`, `σₘ = √(c² − χₘ)`;
so for two such prolates `|ψ_a(ξ₁) u_b(ξ₂)| ≤ G √(c/σₘ · ew(ξ₂)/ew(ξ₁))`, `ProlateWeightToEdge`'s envelope at `χ = χₘ`; hence
`StationaryEnvelopeMonotone`'s stationary pair for the mode `m` of `ψ_a` and `1/k` of `ψ_b`, with `D` the two-prolate one.
-/

namespace Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi

open Real Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Envelope.ProlateWeightToEdge

theorem ew_pos {ξ : ℝ} (h : 1 < ξ) : 0 < ew ξ := by
  unfold ew; have : 0 < ξ ^ 2 - 1 := by nlinarith
  have := sqrt_pos.mpr this; positivity

/-- **The value envelope** at `χₘ`. -/
theorem val_sq_le {c χ χm G ξ : ℝ} {ψ u : ℝ → ℝ} (hχ0 : 0 ≤ χ) (hχm : χ ≤ χm) (hχc : χm < c ^ 2)
    (h1 : 1 < ξ) (hG : energy (aP c χ) ψ u ξ ≤ G) :
    ψ ξ ^ 2 ≤ G / (√(c ^ 2 - χm) * ew ξ) := by
  have hc2 : 0 < c ^ 2 := by nlinarith
  have hχ : χ < c ^ 2 := by linarith
  have ha := aP_pos h1 hc2 hχ
  have hG0 : 0 ≤ G := le_trans (by
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) ha; linarith [abs_nonneg (ψ ξ * u ξ)]) hG
  have lo := le_aP' hχ0 hχ h1.le
  have hσ : √(c ^ 2 - χm) ≤ √(c ^ 2 - χ) := Real.sqrt_le_sqrt (by linarith)
  have hσ0 : 0 < √(c ^ 2 - χm) := sqrt_pos.mpr (by linarith)
  have he := ew_pos h1
  calc ψ ξ ^ 2 ≤ energy (aP c χ) ψ u ξ / aP c χ ξ := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.sq_le_energy_div ha
    _ ≤ G / aP c χ ξ := div_le_div_of_nonneg_right hG ha.le
    _ ≤ G / (√(c ^ 2 - χm) * ew ξ) :=
        div_le_div_of_nonneg_left hG0 (by positivity) (le_trans (mul_le_mul_of_nonneg_right hσ he.le) lo)

/-- **The flux envelope**. -/
theorem flux_sq_le {c χ G ξ : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (h1 : 1 < ξ) (hG : energy (aP c χ) ψ u ξ ≤ G) : u ξ ^ 2 ≤ c * ew ξ * G := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos h1 hc2 hχ
  have hE0 : 0 ≤ energy (aP c χ) ψ u ξ := by unfold energy; positivity
  calc u ξ ^ 2 ≤ aP c χ ξ * energy (aP c χ) ψ u ξ := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.flux_sq_le ha
    _ ≤ c * ew ξ * G := mul_le_mul (aP_le' hc hχ0 h1.le) hG hE0 (by have := ew_pos h1; positivity)

/-- **The two-prolate cross envelope.** -/
theorem cross_env2 {c χa χb χm G ξ₁ ξ₂ : ℝ} {ψa ua ψb ub : ℝ → ℝ} (hc : 0 < c)
    (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχc : χm < c ^ 2)
    (h₁ : 1 < ξ₁) (h₂ : 1 < ξ₂) (hGa : energy (aP c χa) ψa ua ξ₁ ≤ G) (hGb : energy (aP c χb) ψb ub ξ₂ ≤ G) :
    |ψa ξ₁ * ub ξ₂| ≤ G * √(c / √(c ^ 2 - χm) * (ew ξ₂ / ew ξ₁)) := by
  have e1 := val_sq_le hχa0 hχam hχc h₁ hGa
  have e2 := flux_sq_le hc hχb0 (by linarith) h₂ hGb
  have he1 := ew_pos h₁
  have he2 := ew_pos h₂
  have hσ0 : 0 < √(c ^ 2 - χm) := sqrt_pos.mpr (by linarith)
  have hG0 : 0 ≤ G := by
    have := (sq_nonneg (ψa ξ₁)).trans e1
    rwa [le_div_iff₀ (by positivity), zero_mul] at this
  rw [show G * √(c / √(c ^ 2 - χm) * (ew ξ₂ / ew ξ₁)) = √(G ^ 2 * (c / √(c ^ 2 - χm) * (ew ξ₂ / ew ξ₁))) by
    rw [sqrt_mul (sq_nonneg G), sqrt_sq hG0]]
  apply Real.abs_le_sqrt
  rw [mul_pow]
  calc ψa ξ₁ ^ 2 * ub ξ₂ ^ 2 ≤ G / (√(c ^ 2 - χm) * ew ξ₁) * (c * ew ξ₂ * G) :=
        mul_le_mul e1 e2 (sq_nonneg _) (by positivity)
    _ = G ^ 2 * (c / √(c ^ 2 - χm) * (ew ξ₂ / ew ξ₁)) := by field_simp

open Cvs.L2a.NonresonantCrossIntegral Cvs.L2a.TwoProlateCrossBound Cvs.L2a.StationaryEnvelopeMonotone Set in
/-- **One stationary pair of two prolates, in closed form.** -/
theorem stationary_pair2_le {c χa χb χm G ξ₁ Ξ k m a tl tr b : ℝ} {ψa ua ψb ub : ℝ → ℝ}
    (hc : 0 < c) (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2)
    (hk : 0 < k) (hm : 0 < m) (hkm : 1 < k * m)
    (hka : k < a) (hal : a ≤ tl) (hlr : tl ≤ tr) (hrb : tr ≤ b)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ a / k) (hlo' : ξ₁ ≤ m * a) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψa : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χb) ψb ub ξ ≤ G)
    (hDL : ∀ τ ∈ Icc a tl, Dmr2 c χa χb m (1 / k) τ < 0) (hDR : ∀ τ ∈ Icc tr b, 0 < Dmr2 c χa χb m (1 / k) τ) :
    |∫ t in a..b, ψa (m * t) * ψb (1 / k * t)|
      ≤ 2 * (-(pm m tl / Dmr2 c χa χb m (1 / k) tl) * (G * √(c / √(c ^ 2 - χm)) / m)
            + -(pm (1 / k) tl / Dmr2 c χa χb m (1 / k) tl) * (G / m * √(c / √(c ^ 2 - χm) * (ew (m * a) / ew (a / k)))))
        + (tr - tl) * (√(G / (√(c ^ 2 - χm) * ew (m * tl))) * √(G / (√(c ^ 2 - χm) * ew (tl / k))))
        + 2 * (pm m tr * (G * √(c / √(c ^ 2 - χm)) / m)
            + pm (1 / k) tr * (G / m * √(c / √(c ^ 2 - χm) * (ew (m * tr) / ew (tr / k))))) / Dmr2 c χa χb m (1 / k) tr := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hχa : χa < c ^ 2 := by linarith
  have hχb : χb < c ^ 2 := by linarith
  have hd : 0 < c ^ 2 - χm := by linarith
  have hsd : 0 < √(c ^ 2 - χm) := sqrt_pos.mpr hd
  have hr : (0 : ℝ) < 1 / k := by positivity
  have hrm : 1 / k < m := by rw [div_lt_iff₀ hk]; linarith
  have hra : 1 < 1 / k * a := by rw [one_div_mul_eq_div, lt_div_iff₀ hk]; linarith
  set κ₀ := c / √(c ^ 2 - χm) with hκ₀
  have hG0 : 0 ≤ G := by
    have hmem : ξ₁ ∈ Icc ξ₁ Ξ := ⟨le_rfl, hlo.trans (by
      have : a / k ≤ b / k := div_le_div_of_nonneg_right (hal.trans (hlr.trans hrb)) hk.le
      linarith)⟩
    have ha := aP_pos hξ₁ hc2 hχa
    have := two_mul_abs_le_energy (ψ := ψa) (u := ua) ha
    linarith [hGa ξ₁ hmem, abs_nonneg (ψa ξ₁ * ua ξ₁)]
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
  have sysa : ∀ τ ∈ Icc a b, HasDerivAt (fun t => ψa (m * t)) ((ua (m * τ) / m) / pm m τ) τ ∧
      HasDerivAt (fun t => ua (m * t) / m) (-(qm c χa m τ * ψa (m * τ))) τ := fun τ hτ =>
    Cvs.L2a.NonstationaryCrossPairClosed.scale_system hm (hψa _ (in1 τ hτ)) (hua _ (in1 τ hτ))
  have sysb : ∀ τ ∈ Icc a b, HasDerivAt (fun t => ψb (1 / k * t)) ((ub (1 / k * τ) / (1 / k)) / pm (1 / k) τ) τ ∧
      HasDerivAt (fun t => ub (1 / k * t) / (1 / k)) (-(qm c χb (1 / k) τ * ψb (1 / k * τ))) τ := fun τ hτ =>
    Cvs.L2a.NonstationaryCrossPairClosed.scale_system hr (hψb _ (in2 τ hτ)) (hub _ (in2 τ hτ))
  have gt1 : ∀ τ ∈ Icc a b, k < τ := fun τ hτ => lt_of_lt_of_le hka hτ.1
  have arg1 : ∀ τ ∈ Icc a b, 1 < m * τ := fun τ hτ => lt_of_lt_of_le hξ₁ (in1 τ hτ).1
  have arg2 : ∀ τ ∈ Icc a b, 1 < 1 / k * τ := fun τ hτ => lt_of_lt_of_le hξ₁ (in2 τ hτ).1
  have hdiv : ∀ τ : ℝ, 1 / k * τ = τ / k := fun τ => by ring
  have hZ : ∀ τ ∈ Icc a b, |ψa (m * τ) * (ub (1 / k * τ) / (1 / k))| ≤ G * √κ₀ / m := fun τ hτ => by
    have h := cross_env2 hc hχa0 hχam hχb0 hχbm hχm (arg1 τ hτ) (arg2 τ hτ) (hGa _ (in1 τ hτ)) (hGb _ (in2 τ hτ))
    have hr' := ratio_le hk hm hkm (gt1 τ hτ)
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
  have hV : ∀ t₀ ∈ Icc a b, ∀ τ ∈ Icc t₀ b,
      |ua (m * τ) / m * ψb (1 / k * τ)| ≤ G / m * √(κ₀ * (ew (m * t₀) / ew (t₀ / k))) := fun t₀ ht₀ τ hτ => by
    have hτ' : τ ∈ Icc a b := ⟨ht₀.1.trans hτ.1, hτ.2⟩
    have h := cross_env2 hc hχb0 hχbm hχa0 hχam hχm (arg2 τ hτ') (arg1 τ hτ') (hGb _ (in2 τ hτ')) (hGa _ (in1 τ hτ'))
    have hR := R_anti hk hm hkm (gt1 t₀ ht₀) hτ.1
    rw [← hdiv] at hR
    have e : ua (m * τ) / m * ψb (1 / k * τ) = (ψb (1 / k * τ) * ua (m * τ)) / m := by ring
    rw [e, abs_div, abs_of_pos hm]
    calc |ψb (1 / k * τ) * ua (m * τ)| / m ≤ G * √(κ₀ * (ew (m * τ) / ew (1 / k * τ))) / m :=
          div_le_div_of_nonneg_right h hm.le
      _ ≤ G * √(κ₀ * (ew (m * t₀) / ew (t₀ / k))) / m := by
          have hκ : 0 ≤ κ₀ := by positivity
          apply div_le_div_of_nonneg_right _ hm.le
          exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hR hκ)) hG0
      _ = G / m * √(κ₀ * (ew (m * t₀) / ew (t₀ / k))) := by ring
  have hval : ∀ {χ : ℝ} {ψ u : ℝ → ℝ}, 0 ≤ χ → χ ≤ χm → (∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χ) ψ u ξ ≤ G) →
      ∀ ξ ∈ Icc ξ₁ Ξ, ∀ η, 1 < η → η ≤ ξ → |ψ ξ| ≤ √(G / (√(c ^ 2 - χm) * ew η)) := by
    intro χ ψ u h0 hmx hGχ ξ hξ η hη hηξ
    have hξ1 : 1 < ξ := lt_of_lt_of_le hξ₁ hξ.1
    have h2 := val_sq_le h0 hmx hχm hξ1 (hGχ ξ hξ)
    have hmono := ew_mono hη.le hηξ
    have hew := ew_pos hη
    have h3 : ψ ξ ^ 2 ≤ G / (√(c ^ 2 - χm) * ew η) :=
      h2.trans (div_le_div_of_nonneg_left hG0 (by positivity) (mul_le_mul_of_nonneg_left hmono hsd.le))
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h3
  have key := Cvs.L2a.TwoProlateStationarySplit.prolate_stationary2_le (c := c) (χ := χa) (χ' := χb) (m := m) (r := 1 / k)
    (f₁ := fun t => ψa (m * t)) (u₁ := fun t => ua (m * t) / m)
    (f₂ := fun t => ψb (1 / k * t)) (u₂ := fun t => ub (1 / k * t) / (1 / k))
    (MzL := G * √κ₀ / m) (MvL := G / m * √(κ₀ * (ew (m * a) / ew (a / k))))
    (MzR := G * √κ₀ / m) (MvR := G / m * √(κ₀ * (ew (m * tr) / ew (tr / k))))
    (F₁ := √(G / (√(c ^ 2 - χm) * ew (m * tl)))) (F₂ := √(G / (√(c ^ 2 - χm) * ew (tl / k))))
    hr hrm hra hχa hχb hal hlr hrb hDL hDR
    (fun τ hτ => (sysa τ hτ).1) (fun τ hτ => (sysa τ hτ).2)
    (fun τ hτ => (sysb τ hτ).1) (fun τ hτ => (sysb τ hτ).2)
    (fun τ hτ => hZ τ ⟨hτ.1, hτ.2.trans (hlr.trans hrb)⟩)
    (fun τ hτ => hV a ⟨le_rfl, hal.trans (hlr.trans hrb)⟩ τ ⟨hτ.1, hτ.2.trans (hlr.trans hrb)⟩)
    (fun τ hτ => hZ τ ⟨hal.trans (hlr.trans hτ.1), hτ.2⟩)
    (fun τ hτ => hV tr ⟨hal.trans hlr, hrb⟩ τ hτ)
    (fun τ hτ => hval hχa0 hχam hGa _ (in1 τ ⟨hal.trans hτ.1, hτ.2.trans hrb⟩) (m * tl)
      (arg1 tl ⟨hal, hlr.trans hrb⟩) (by nlinarith [hτ.1]))
    (fun τ hτ => by
      have := hval hχb0 hχbm hGb _ (in2 τ ⟨hal.trans hτ.1, hτ.2.trans hrb⟩) (tl / k)
        (by rw [← hdiv]; exact arg2 tl ⟨hal, hlr.trans hrb⟩)
        (by rw [hdiv]; exact div_le_div_of_nonneg_right hτ.1 hk.le)
      simpa using this)
  simpa using key

end Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi
