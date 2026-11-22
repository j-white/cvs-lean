import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.NonstationaryCrossPairClosed
import Cvs.L2a.StationaryCrossPairSplit
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
# The monotone pieces of the stationary pair's envelopes

With `ew(ξ) = ξ√(ξ²−1)`: `ew` increases on `[1, ∞)`; `ew(t/k)/ew(mt) ≤ 1/(k²m²)` for `t > k`, `km > 1`; and
`R(t) = ew(mt)/ew(t/k)` decreases on `t > k`. So the value-times-flux sups of a stationary pair are `G√κ₀/m` and
`(G/m)√(κ₀ R(t₀))` at the left end `t₀` of each piece.
-/

namespace Cvs.L2a.StationaryEnvelopeMonotone

open Real Set Cvs.Prolate.Envelope.ProlateWeightToEdge

/-- `ew` increases on `[1, ∞)`. -/
theorem ew_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : ew a ≤ ew b := by
  unfold ew
  have h1 : √(a ^ 2 - 1) ≤ √(b ^ 2 - 1) := sqrt_le_sqrt (by nlinarith)
  exact mul_le_mul hab h1 (sqrt_nonneg _) (by linarith)

theorem ew_pos {ξ : ℝ} (h : 1 < ξ) : 0 < ew ξ := by
  unfold ew; have : 0 < ξ ^ 2 - 1 := by nlinarith
  have := sqrt_pos.mpr this; positivity

/-- `ew(ξ)² = ξ²(ξ² − 1)`. -/
theorem ew_sq {ξ : ℝ} (h : 1 ≤ ξ) : ew ξ ^ 2 = ξ ^ 2 * (ξ ^ 2 - 1) := by
  unfold ew; rw [mul_pow, sq_sqrt (by nlinarith)]

/-- `ew(t/k)/ew(mt) ≤ 1/(k²m²)` for `t > k > 0`, `m > 0`, `km > 1`. -/
theorem ratio_le {k m t : ℝ} (hk : 0 < k) (hm : 0 < m) (hkm : 1 < k * m) (ht : k < t) :
    ew (t / k) / ew (m * t) ≤ 1 / (k ^ 2 * m ^ 2) := by
  have ht1 : 1 < t / k := by rw [lt_div_iff₀ hk]; linarith
  have hmt : 1 < m * t := by nlinarith
  have h1 := ew_pos ht1
  have h2 := ew_pos hmt
  rw [div_le_div_iff₀ h2 (by positivity), one_mul]
  -- compare squares
  have hs : (ew (t / k) * (k ^ 2 * m ^ 2)) ^ 2 ≤ ew (m * t) ^ 2 := by
    rw [mul_pow, ew_sq ht1.le, ew_sq hmt.le]
    have e : (t / k) ^ 2 = t ^ 2 / k ^ 2 := by ring
    rw [e]
    have hk2 : 0 < k ^ 2 := by positivity
    field_simp
    have ht2 : k ^ 2 < t ^ 2 := by nlinarith
    have hkm2 : 1 < k ^ 2 * m ^ 2 := by nlinarith
    nlinarith [mul_pos (by linarith : (0:ℝ) < t ^ 2 - k ^ 2) (by linarith : (0:ℝ) < k ^ 2 * m ^ 2 - 1),
      sq_nonneg t, sq_nonneg m, sq_nonneg k]
  exact (pow_le_pow_iff_left₀ (by positivity) h2.le two_ne_zero).mp hs

/-- `R(t) = ew(mt)/ew(t/k)` decreases on `t > k` (for `km > 1`). -/
theorem R_anti {k m t₁ t₂ : ℝ} (hk : 0 < k) (hm : 0 < m) (hkm : 1 < k * m) (h1 : k < t₁) (h12 : t₁ ≤ t₂) :
    ew (m * t₂) / ew (t₂ / k) ≤ ew (m * t₁) / ew (t₁ / k) := by
  have h2 : k < t₂ := lt_of_lt_of_le h1 h12
  have p1 : 1 < t₁ / k := by rw [lt_div_iff₀ hk]; linarith
  have p2 : 1 < t₂ / k := by rw [lt_div_iff₀ hk]; linarith
  have q1 : 1 < m * t₁ := by nlinarith
  have q2 : 1 < m * t₂ := by nlinarith
  have e1 := ew_pos p1; have e2 := ew_pos p2; have f1 := ew_pos q1; have f2 := ew_pos q2
  rw [div_le_div_iff₀ e2 e1]
  have hs : (ew (m * t₂) * ew (t₁ / k)) ^ 2 ≤ (ew (m * t₁) * ew (t₂ / k)) ^ 2 := by
    rw [mul_pow, mul_pow, ew_sq q1.le, ew_sq q2.le, ew_sq p1.le, ew_sq p2.le]
    have e : ∀ t : ℝ, (t / k) ^ 2 = t ^ 2 / k ^ 2 := fun t => by ring
    rw [e, e]
    have hk2 : 0 < k ^ 2 := by positivity
    field_simp
    have T1 : k ^ 2 < t₁ ^ 2 := by nlinarith
    have T12 : t₁ ^ 2 ≤ t₂ ^ 2 := by nlinarith
    have hkm2 : 1 < k ^ 2 * m ^ 2 := by nlinarith
    -- reduces to (m²k² − 1)(T₂ − T₁) ≥ 0, times positive factors
    have key : 0 ≤ t₁ ^ 2 * t₂ ^ 2 * ((t₂ ^ 2 - t₁ ^ 2) * (m ^ 2 * k ^ 2 - 1)) :=
      mul_nonneg (by positivity) (mul_nonneg (by linarith) (by nlinarith))
    nlinarith [key]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hs

open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral in
/-- **One stationary pair, in closed form**: `StationaryCrossPairSplit`'s three pieces with the sups of Cvs.Prolate.Envelope.ProlateWeightToEdge at the ends
(`G√κ₀/m`, `(G/m)√(κ₀R)`, `√(G/(√(c²−χ) ew))`), for the modes `m` and `1/k` with `D < 0` on `[a, t_l]` and
`D > 0` on `[t_r, b]`. -/
theorem stationary_pair_le {c χ G ξ₁ Ξ k m a tl tr b : ℝ} {ψ u : ℝ → ℝ}
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk : 0 < k) (hm : 0 < m) (hkm : 1 < k * m)
    (hka : k < a) (hal : a ≤ tl) (hlr : tl ≤ tr) (hrb : tr ≤ b)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ a / k) (hlo' : ξ₁ ≤ m * a) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψ : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χ) ψ u ξ ≤ G)
    (hDL : ∀ τ ∈ Icc a tl, Dmr c χ m (1 / k) τ < 0) (hDR : ∀ τ ∈ Icc tr b, 0 < Dmr c χ m (1 / k) τ) :
    |∫ t in a..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ 2 * (-(pm m tl / Dmr c χ m (1 / k) tl) * (G * √(c / √(c ^ 2 - χ)) / m)
            + -(pm (1 / k) tl / Dmr c χ m (1 / k) tl) * (G / m * √(c / √(c ^ 2 - χ) * (ew (m * a) / ew (a / k)))))
        + (tr - tl) * (√(G / (√(c ^ 2 - χ) * ew (m * tl))) * √(G / (√(c ^ 2 - χ) * ew (tl / k))))
        + 2 * (pm m tr * (G * √(c / √(c ^ 2 - χ)) / m)
            + pm (1 / k) tr * (G / m * √(c / √(c ^ 2 - χ) * (ew (m * tr) / ew (tr / k))))) / Dmr c χ m (1 / k) tr := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hd : 0 < c ^ 2 - χ := by linarith
  have hsd : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  have hr : (0 : ℝ) < 1 / k := by positivity
  have hrm : 1 / k < m := by rw [div_lt_iff₀ hk]; linarith
  have hra : 1 < 1 / k * a := by rw [one_div_mul_eq_div, lt_div_iff₀ hk]; linarith
  set κ₀ := c / √(c ^ 2 - χ) with hκ₀
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
  -- the value-times-flux sups
  have hZ : ∀ τ ∈ Icc a b, |ψ (m * τ) * (u (1 / k * τ) / (1 / k))| ≤ G * √κ₀ / m := fun τ hτ => by
    have h := cross_env' hc hχ0 hχ (arg1 τ hτ) (arg2 τ hτ) (hG _ (in1 τ hτ)) (hG _ (in2 τ hτ))
    have hr' := ratio_le hk hm hkm (gt1 τ hτ)
    rw [← hdiv] at hr'
    have e : ψ (m * τ) * (u (1 / k * τ) / (1 / k)) = k * (ψ (m * τ) * u (1 / k * τ)) := by field_simp
    rw [e, abs_mul, abs_of_pos hk]
    calc k * |ψ (m * τ) * u (1 / k * τ)| ≤ k * (G * √(κ₀ * (ew (1 / k * τ) / ew (m * τ)))) :=
          mul_le_mul_of_nonneg_left h hk.le
      _ ≤ k * (G * √(κ₀ * (1 / (k ^ 2 * m ^ 2)))) := by
          gcongr
      _ = G * √κ₀ / m := by
          have e2 : √(κ₀ * (1 / (k ^ 2 * m ^ 2))) = √κ₀ * (1 / (k * m)) := by
            rw [sqrt_mul' _ (by positivity), show 1 / (k ^ 2 * m ^ 2) = (1 / (k * m)) ^ 2 by field_simp,
              sqrt_sq (by positivity)]
          rw [e2]; field_simp
  have hV : ∀ t₀ ∈ Icc a b, ∀ τ ∈ Icc t₀ b,
      |u (m * τ) / m * ψ (1 / k * τ)| ≤ G / m * √(κ₀ * (ew (m * t₀) / ew (t₀ / k))) := fun t₀ ht₀ τ hτ => by
    have hτ' : τ ∈ Icc a b := ⟨ht₀.1.trans hτ.1, hτ.2⟩
    have h := cross_env' hc hχ0 hχ (arg2 τ hτ') (arg1 τ hτ') (hG _ (in2 τ hτ')) (hG _ (in1 τ hτ'))
    have hR := R_anti hk hm hkm (gt1 t₀ ht₀) hτ.1
    rw [← hdiv] at hR
    have e : u (m * τ) / m * ψ (1 / k * τ) = (ψ (1 / k * τ) * u (m * τ)) / m := by ring
    rw [e, abs_div, abs_of_pos hm]
    calc |ψ (1 / k * τ) * u (m * τ)| / m ≤ G * √(κ₀ * (ew (m * τ) / ew (1 / k * τ))) / m :=
          div_le_div_of_nonneg_right h hm.le
      _ ≤ G * √(κ₀ * (ew (m * t₀) / ew (t₀ / k))) / m := by
          have hκ : 0 ≤ κ₀ := by positivity
          apply div_le_div_of_nonneg_right _ hm.le
          exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hR hκ)) hG0
      _ = G / m * √(κ₀ * (ew (m * t₀) / ew (t₀ / k))) := by ring
  -- the value sups on the window
  have hval : ∀ ξ ∈ Icc ξ₁ Ξ, ∀ η, 1 < η → η ≤ ξ → |ψ ξ| ≤ √(G / (√(c ^ 2 - χ) * ew η)) := by
    intro ξ hξ η hη hηξ
    have hξ1 : 1 < ξ := lt_of_lt_of_le hξ₁ hξ.1
    have ha := aP_pos hξ1 hc2 hχ
    have h1 := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.sq_le_energy_div (ψ := ψ) (u := u) ha
    have h2 : ψ ξ ^ 2 ≤ G / (√(c ^ 2 - χ) * ew η) := by
      refine h1.trans ?_
      have lo := le_aP' hχ0 hχ hξ1.le
      have hmono := ew_mono hη.le hηξ
      have hew := ew_pos hη
      calc energy (aP c χ) ψ u ξ / aP c χ ξ ≤ G / aP c χ ξ := div_le_div_of_nonneg_right (hG ξ hξ) ha.le
        _ ≤ G / (√(c ^ 2 - χ) * ew η) := by
            apply div_le_div_of_nonneg_left hG0 (by positivity)
            exact le_trans (mul_le_mul_of_nonneg_left hmono hsd.le) lo
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h2
  have key := Cvs.L2a.StationaryCrossPairSplit.prolate_stationary_le (c := c) (χ := χ) (m := m) (r := 1 / k)
    (f₁ := fun t => ψ (m * t)) (u₁ := fun t => u (m * t) / m)
    (f₂ := fun t => ψ (1 / k * t)) (u₂ := fun t => u (1 / k * t) / (1 / k))
    (MzL := G * √κ₀ / m) (MvL := G / m * √(κ₀ * (ew (m * a) / ew (a / k))))
    (MzR := G * √κ₀ / m) (MvR := G / m * √(κ₀ * (ew (m * tr) / ew (tr / k))))
    (F₁ := √(G / (√(c ^ 2 - χ) * ew (m * tl)))) (F₂ := √(G / (√(c ^ 2 - χ) * ew (tl / k))))
    hr hrm hra hχ hal hlr hrb hDL hDR
    (fun τ hτ => (sys m hm in1 τ hτ).1) (fun τ hτ => (sys m hm in1 τ hτ).2)
    (fun τ hτ => (sys (1 / k) hr in2 τ hτ).1) (fun τ hτ => (sys (1 / k) hr in2 τ hτ).2)
    (fun τ hτ => hZ τ ⟨hτ.1, hτ.2.trans (hlr.trans hrb)⟩)
    (fun τ hτ => hV a ⟨le_rfl, hal.trans (hlr.trans hrb)⟩ τ ⟨hτ.1, hτ.2.trans (hlr.trans hrb)⟩)
    (fun τ hτ => hZ τ ⟨hal.trans (hlr.trans hτ.1), hτ.2⟩)
    (fun τ hτ => hV tr ⟨hal.trans hlr, hrb⟩ τ hτ)
    (fun τ hτ => hval _ (in1 τ ⟨hal.trans hτ.1, hτ.2.trans hrb⟩) (m * tl)
      (arg1 tl ⟨hal, hlr.trans hrb⟩) (by nlinarith [hτ.1]))
    (fun τ hτ => by
      have := hval _ (in2 τ ⟨hal.trans hτ.1, hτ.2.trans hrb⟩) (tl / k)
        (by rw [← hdiv]; exact arg2 tl ⟨hal, hlr.trans hrb⟩)
        (by rw [hdiv]; exact div_le_div_of_nonneg_right hτ.1 hk.le)
      simpa using this)
  simpa using key

end Cvs.L2a.StationaryEnvelopeMonotone
