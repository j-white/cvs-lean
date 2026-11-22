import Mathlib
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.ProlateMassEnergyWeighted

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail and the mass of a rung against its energy at `ξ = 2`

The energy grows by at most `F(w) = (1 + w/2)/(1 − w/2) e^{w/(2−w)}` from `2` to `b` and shrinks by at most the
same factor, with `w ≤ 4/(3c)` beyond `ξ = 2` and `F(w) ≤ (1 + w/2)/(1 − w) ≤ (3c + 2)/(3c − 4)`. Hence the tail
bound beyond `b` is at most `E(2) Φ²/(c(b − 1))` and the mass on `[1, b]` is at least
`E(2)((1/Φ)(1/2 − 1/b)/(2c) − Φ/(6c²))`, `Φ = (3c + 2)/(3c − 4)`.
-/

namespace Cvs.Prolate.RungTailMassEnergyAtTwo

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower Cvs.Prolate.ProlateMassEnergyWeighted Cvs.Prolate.Gram.RungGramFloorAtInfinity

/-- The energy growth factor `F(w) = (1 + w/2)/(1 − w/2) e^{w/(2−w)}`. -/
noncomputable def Fg (w : ℝ) : ℝ := (1 + w / 2) / (1 - w / 2) * exp (w / (2 - w))

/-- The bound `Φ(c) = (3c + 2)/(3c − 4)` on `F` beyond `ξ = 2`. -/
noncomputable def Φc (c : ℝ) : ℝ := (3 * c + 2) / (3 * c - 4)

/-- `e^x ≤ 1/(1 − x)` for `x < 1`. -/
theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : exp x ≤ 1 / (1 - x) := by
  have h := Real.add_one_le_exp (-x)
  rw [le_div_iff₀ (by linarith)]
  have : exp x * exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x]

/-- `F(w) ≤ (1 + w/2)/(1 − w)` for `0 ≤ w < 1`. -/
theorem Fg_le {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 1) : Fg w ≤ (1 + w / 2) / (1 - w) := by
  unfold Fg
  have h2 : 0 < 2 - w := by linarith
  have hx : w / (2 - w) < 1 := by rw [div_lt_one h2]; linarith
  have he := exp_le_inv_one_sub hx
  have e : 1 / (1 - w / (2 - w)) = (2 - w) / (2 - 2 * w) := by
    have : 1 - w / (2 - w) = (2 - 2 * w) / (2 - w) := by
      rw [eq_div_iff h2.ne']; field_simp; ring
    rw [this, one_div_div]
  rw [e] at he
  calc (1 + w / 2) / (1 - w / 2) * exp (w / (2 - w))
      ≤ (1 + w / 2) / (1 - w / 2) * ((2 - w) / (2 - 2 * w)) :=
        mul_le_mul_of_nonneg_left he (by apply div_nonneg <;> linarith)
    _ = (1 + w / 2) / (1 - w) := by
        have h1w : (0:ℝ) < 1 - w := by linarith
        have h2w : (0:ℝ) < 2 - 2 * w := by linarith
        have hw2 : (0:ℝ) < 1 - w / 2 := by linarith
        rw [div_mul_div_comm, div_eq_div_iff (mul_pos hw2 h2w).ne' h1w.ne']; ring

/-- `F(w) ≤ Φ(c)` for `0 ≤ w ≤ 4/(3c)`, `c ≥ 2`. -/
theorem Fg_le_Φ {c w : ℝ} (hc : 2 ≤ c) (hw0 : 0 ≤ w) (hw : w ≤ 4 / (3 * c)) : Fg w ≤ Φc c := by
  have hc0 : 0 < c := by linarith
  have hw1 : w < 1 := by
    have : 4 / (3 * c) ≤ 4 / 6 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  refine (Fg_le hw0 hw1).trans ?_
  unfold Φc
  have h3 : 0 < 3 * c - 4 := by linarith
  rw [div_le_div_iff₀ (by linarith) h3]
  have hw' : w * (3 * c) ≤ 4 := by rwa [le_div_iff₀ (by positivity)] at hw
  nlinarith

theorem Φc_pos {c : ℝ} (hc : 2 ≤ c) : 0 < Φc c := by unfold Φc; apply div_pos <;> linarith

theorem Φc_le {c : ℝ} (hc : 8 ≤ c) : Φc c ≤ 13 / 10 := by
  unfold Φc; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith

/-- `w(2) ≤ 4/(3c)`. -/
theorem wP_two_le {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) : wP c χ 2 ≤ 4 / (3 * c) := by
  have := wP_le_far (ξ := 2) (by norm_num) hc hχ0 hχc
  have e : (2 : ℝ) * 2 / (c * pP 2) = 4 / (3 * c) := by unfold pP; norm_num; ring
  linarith

/-- `w(b) ≤ 4/(3c)` for `b ≥ 2`. -/
theorem wP_ge_two_le {c χ b : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hb : 2 ≤ b) :
    wP c χ b ≤ 4 / (3 * c) := by
  have h := wP_le_far (ξ := b) (by linarith) hc hχ0 hχc
  refine h.trans ?_
  unfold pP
  have hb2 : (0:ℝ) < b ^ 2 - 1 := by nlinarith
  rw [div_le_div_iff₀ (mul_pos hc hb2) (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ b - 2) (by linarith : (0:ℝ) ≤ 4 * b + 2)]

theorem energy_nonneg {c χ ξ : ℝ} {ψ u : ℝ → ℝ} (hξ : 1 < ξ) (hc : 0 < c ^ 2) (hχc : χ < c ^ 2) :
    0 ≤ energy (aP c χ) ψ u ξ := by
  unfold energy; have := aP_pos hξ hc hχc; positivity

/-- The growth factor of `Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.prolate_energy_le` is `F(w)`. -/
theorem energy_le_Fg {c χ : ℝ} {ψ u : ℝ → ℝ} {ξ₀ ξ₁ : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hc : 0 < c ^ 2) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    energy (aP c χ) ψ u ξ₁ ≤ energy (aP c χ) ψ u ξ₀ * Fg (wP c χ ξ₀) := by
  have := prolate_energy_le h1 hle hc hχ hχc hψ hu hW
  unfold Fg; linarith [this, show energy (aP c χ) ψ u ξ₀ * (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
    * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) = energy (aP c χ) ψ u ξ₀ * ((1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
    * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀))) by ring]

/-- The shrinking factor of `Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower.prolate_energy_ge` is `1/F(w)`. -/
theorem energy_ge_Fg {c χ : ℝ} {ψ u : ℝ → ℝ} {ξ₀ ξ₁ : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hc : 0 < c ^ 2) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    energy (aP c χ) ψ u ξ₀ / Fg (wP c χ ξ₀) ≤ energy (aP c χ) ψ u ξ₁ := by
  have h := prolate_energy_ge h1 hle hc hχ hχc hψ hu hW
  have hw0 : 0 < wP c χ ξ₀ := wP_pos h1 hc hχc
  have e : energy (aP c χ) ψ u ξ₀ * (1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2)
      * exp (-(wP c χ ξ₀ / (2 - wP c χ ξ₀))) = energy (aP c χ) ψ u ξ₀ / Fg (wP c χ ξ₀) := by
    unfold Fg
    rw [Real.exp_neg]
    have h2 : (0:ℝ) < 2 - wP c χ ξ₀ := by linarith
    have h1' : (0:ℝ) < 1 - wP c χ ξ₀ / 2 := by linarith
    have h1'' : (0:ℝ) < 1 + wP c χ ξ₀ / 2 := by linarith
    have he : exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  linarith [h, e]

/-- **The tail beyond `b` against the energy at `2`**: `T ≤ E(2) Φ²/(c(b − 1))` for `b ≥ 4`, `c ≥ 2`. -/
theorem tail_le_energy_two {c χ b : ℝ} {ψ u : ℝ → ℝ} (hc : 2 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hb : 4 ≤ b)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) :
    energy (aP c χ) ψ u b * (1 + wP c χ b / 2) / (1 - wP c χ b / 2) * exp (wP c χ b / (2 - wP c χ b)) / (2 * c)
        * log ((b + 1) / (b - 1))
      ≤ energy (aP c χ) ψ u 2 * Φc c ^ 2 / (c * (b - 1)) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hw₀ : (4 : ℝ) / (3 * c) < 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have hW2 : wP c χ 2 < 2 := lt_of_le_of_lt (wP_two_le hc0 hχ0 hχc) hw₀
  have hWb : wP c χ b < 2 := lt_of_le_of_lt (wP_ge_two_le hc0 hχ0 hχc (by linarith)) hw₀
  have hwb0 : 0 ≤ wP c χ b := (wP_pos (by linarith) hc2 hχc).le
  have hw20 : 0 ≤ wP c χ 2 := (wP_pos (by norm_num) hc2 hχc).le
  have hE2 : 0 ≤ energy (aP c χ) ψ u 2 := energy_nonneg (by norm_num) hc2 hχc
  have hEb := energy_le_Fg (ξ₀ := 2) (ξ₁ := b) (by norm_num) (by linarith) hc2 hχ0 hχc
    (fun t ht => hψ t (by linarith [ht.1])) (fun t _ => hu t) hW2
  have hF2 : Fg (wP c χ 2) ≤ Φc c := Fg_le_Φ hc hw20 (wP_two_le hc0 hχ0 hχc)
  have hFb : Fg (wP c χ b) ≤ Φc c := Fg_le_Φ hc hwb0 (wP_ge_two_le hc0 hχ0 hχc (by linarith))
  have hΦ := Φc_pos hc
  have hFb0 : 0 ≤ Fg (wP c χ b) := by unfold Fg; apply mul_nonneg (div_nonneg (by linarith) (by linarith)); positivity
  have hlog : log ((b + 1) / (b - 1)) ≤ 2 / (b - 1) := by
    have := Real.log_le_sub_one_of_pos (by apply div_pos <;> linarith : (0:ℝ) < (b + 1) / (b - 1))
    have hb1 : b - 1 ≠ 0 := by linarith
    have e : (b + 1) / (b - 1) - 1 = 2 / (b - 1) := by field_simp; ring
    linarith
  have hlog0 : 0 ≤ log ((b + 1) / (b - 1)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by linarith)]; linarith
  have e : energy (aP c χ) ψ u b * (1 + wP c χ b / 2) / (1 - wP c χ b / 2) * exp (wP c χ b / (2 - wP c χ b)) / (2 * c)
      * log ((b + 1) / (b - 1)) = energy (aP c χ) ψ u b * Fg (wP c χ b) * log ((b + 1) / (b - 1)) / (2 * c) := by
    unfold Fg; ring
  rw [e]
  have hEbF : energy (aP c χ) ψ u b * Fg (wP c χ b) ≤ energy (aP c χ) ψ u 2 * Φc c ^ 2 := by
    calc energy (aP c χ) ψ u b * Fg (wP c χ b) ≤ energy (aP c χ) ψ u 2 * Fg (wP c χ 2) * Fg (wP c χ b) :=
          mul_le_mul_of_nonneg_right hEb hFb0
      _ ≤ energy (aP c χ) ψ u 2 * Φc c * Φc c := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hF2 hE2) hFb hFb0 (by positivity)
      _ = energy (aP c χ) ψ u 2 * Φc c ^ 2 := by ring
  have hEbF0 : 0 ≤ energy (aP c χ) ψ u b * Fg (wP c χ b) :=
    mul_nonneg (energy_nonneg (by linarith) hc2 hχc) hFb0
  calc energy (aP c χ) ψ u b * Fg (wP c χ b) * log ((b + 1) / (b - 1)) / (2 * c)
      ≤ energy (aP c χ) ψ u 2 * Φc c ^ 2 * (2 / (b - 1)) / (2 * c) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul hEbF hlog hlog0 (by positivity)
    _ = energy (aP c χ) ψ u 2 * Φc c ^ 2 / (c * (b - 1)) := by
        have hb1 : b - 1 ≠ 0 := by linarith
        field_simp

/-- `∫₂ᵇ dt/t² = 1/2 − 1/b`. -/
theorem integral_inv_sq_two {b : ℝ} (hb : 2 ≤ b) : ∫ t in (2 : ℝ)..b, 1 / t ^ 2 = 1 / 2 - 1 / b := by
  have hd : ∀ t ∈ uIcc (2 : ℝ) b, HasDerivAt (fun t : ℝ => -(1 / t)) (1 / t ^ 2) t := fun t ht => by
    rw [uIcc_of_le hb] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h := (hasDerivAt_inv ht0).neg
    have h' : HasDerivAt (fun t : ℝ => -(1 / t)) (-(-(t ^ 2)⁻¹)) t :=
      h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp [one_div])
    exact h'.congr_deriv (by simp [one_div])
  have hi : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) MeasureTheory.volume 2 b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hb]
    exact continuousOn_const.div (continuousOn_id.pow 2) fun t ht => by
      have : (0:ℝ) < t := by linarith [ht.1]
      exact pow_ne_zero 2 this.ne'
  rw [integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- **The mass on `[1, b]` against the energy at `2`**: for `b ≥ 4`, `c ≥ 2`,
`E(2)((1/Φ)(1/2 − 1/b)/(2c) − Φ/(6c²)) ≤ ∫₁ᵇ ψ²`. -/
theorem mass_ge_energy_two {c χ b : ℝ} {ψ u : ℝ → ℝ} (hc : 2 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hb : 4 ≤ b)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hcont : Continuous ψ) :
    energy (aP c χ) ψ u 2 * (1 / Φc c * (1 / 2 - 1 / b) / (2 * c) - Φc c / (6 * c ^ 2))
      ≤ ∫ ξ in (1 : ℝ)..b, ψ ξ ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hw₀ : (4 : ℝ) / (3 * c) < 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have hW2 : wP c χ 2 < 2 := lt_of_le_of_lt (wP_two_le hc0 hχ0 hχc) hw₀
  have hw20 : 0 ≤ wP c χ 2 := (wP_pos (by norm_num) hc2 hχc).le
  have hF2 : Fg (wP c χ 2) ≤ Φc c := Fg_le_Φ hc hw20 (wP_two_le hc0 hχ0 hχc)
  have hΦ := Φc_pos hc
  have hF20 : 0 < Fg (wP c χ 2) := by
    unfold Fg; apply mul_pos (div_pos (by linarith) (by linarith)); positivity
  set E2 := energy (aP c χ) ψ u 2 with hE2def
  have hE2 : 0 ≤ E2 := energy_nonneg (by norm_num) hc2 hχc
  -- the energy on `[2, b]` lies between `E(2)/F` and `E(2) F`
  have hup : ∀ t ∈ Icc (2 : ℝ) b, energy (aP c χ) ψ u t ≤ E2 * Φc c := fun t ht => by
    have := energy_le_Fg (ξ₀ := 2) (ξ₁ := t) (by norm_num) ht.1 hc2 hχ0 hχc
      (fun r hr => hψ r (by linarith [hr.1])) (fun r _ => hu r) hW2
    exact this.trans (mul_le_mul_of_nonneg_left hF2 hE2)
  have hlow : ∀ t ∈ Icc (2 : ℝ) b, E2 / Φc c ≤ energy (aP c χ) ψ u t := fun t ht => by
    have := energy_ge_Fg (ξ₀ := 2) (ξ₁ := t) (by norm_num) ht.1 hc2 hχ0 hχc
      (fun r hr => hψ r (by linarith [hr.1])) (fun r _ => hu r) hW2
    exact (div_le_div_of_nonneg_left hE2 hF20 hF2).trans this
  -- the mass law (Cvs.Prolate.ProlateMassEnergyWeighted)
  have hmass := mass_ge_weighted (ξ₀ := 2) (ξ₁ := b) (GM := E2 * Φc c) (by norm_num) (by linarith) hc0 hχc
    (fun t ht => hψ t (by linarith [ht.1])) (fun t _ => hu t) hup
  -- the weighted integral from below
  have hpt : ∀ t ∈ Icc (2 : ℝ) b, E2 / Φc c / (2 * c) * (1 / t ^ 2) ≤ energy (aP c χ) ψ u t / (2 * aP c χ t) :=
    fun t ht => by
    have ht1 : 1 < t := by linarith [ht.1]
    have ha := aP_pos ht1 hc2 hχc
    have hale : aP c χ t ≤ c * t ^ 2 := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.aP_le hc0 hχ0 ht1.le
    have h1 : E2 / Φc c / (2 * c) * (1 / t ^ 2) = E2 / Φc c / (2 * (c * t ^ 2)) := by
      field_simp
    rw [h1]
    calc E2 / Φc c / (2 * (c * t ^ 2)) ≤ E2 / Φc c / (2 * aP c χ t) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ ≤ energy (aP c χ) ψ u t / (2 * aP c χ t) := div_le_div_of_nonneg_right (hlow t ht) (by positivity)
  have hEc : ContinuousOn (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)) (Icc 2 b) := by
    have hψc : ContinuousOn ψ (Icc 2 b) := hcont.continuousOn
    have huc : ContinuousOn u (Icc 2 b) := fun t _ => (hu t).continuousAt.continuousWithinAt
    have hac : Continuous (aP c χ) := by unfold aP pP qP; fun_prop
    have ha0 : ∀ t ∈ Icc (2:ℝ) b, aP c χ t ≠ 0 := fun t ht => (aP_pos (by linarith [ht.1]) hc2 hχc).ne'
    have hE : ContinuousOn (energy (aP c χ) ψ u) (Icc 2 b) := by
      have e : energy (aP c χ) ψ u = fun t => aP c χ t * ψ t ^ 2 + u t ^ 2 / aP c χ t := rfl
      rw [e]
      exact (hac.continuousOn.mul (hψc.pow 2)).add ((huc.pow 2).div hac.continuousOn ha0)
    exact hE.div (continuousOn_const.mul hac.continuousOn) fun t ht => by have := ha0 t ht; positivity
  have hint : E2 / Φc c / (2 * c) * (1 / 2 - 1 / b) ≤ ∫ t in (2 : ℝ)..b, energy (aP c χ) ψ u t / (2 * aP c χ t) := by
    have hb2 : (2:ℝ) ≤ b := by linarith
    rw [← integral_inv_sq_two hb2]
    rw [← integral_const_mul]
    refine integral_mono_on hb2 ?_ (hEc.intervalIntegrable_of_Icc hb2) hpt
    have hi : ContinuousOn (fun t : ℝ => E2 / Φc c / (2 * c) * (1 / t ^ 2)) (uIcc 2 b) := by
      rw [uIcc_of_le (by linarith : (2:ℝ) ≤ b)]
      exact continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 2) fun t ht => by
        have ht0 : (0:ℝ) < t := by linarith [ht.1]
        exact pow_ne_zero 2 ht0.ne')
    exact hi.intervalIntegrable
  -- `q(2) ≥ 3c²`
  have hq2 : 3 * c ^ 2 ≤ qP c χ 2 := by unfold qP; nlinarith
  have hGq : E2 * Φc c / (2 * qP c χ 2) ≤ E2 * Φc c / (6 * c ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  -- the mass on `[1, b]` is at least that on `[2, b]`
  have hsplit : ∫ ξ in (2 : ℝ)..b, ψ ξ ^ 2 ≤ ∫ ξ in (1 : ℝ)..b, ψ ξ ^ 2 := by
    have hI : ∀ s t : ℝ, IntervalIntegrable (fun ξ => ψ ξ ^ 2) MeasureTheory.volume s t := fun s t =>
      (hcont.pow 2).intervalIntegrable s t
    rw [← integral_add_adjacent_intervals (hI 1 2) (hI 2 b)]
    have : 0 ≤ ∫ ξ in (1 : ℝ)..2, ψ ξ ^ 2 := integral_nonneg (by norm_num) fun ξ _ => sq_nonneg _
    linarith
  have e : E2 * (1 / Φc c * (1 / 2 - 1 / b) / (2 * c) - Φc c / (6 * c ^ 2))
      = E2 / Φc c / (2 * c) * (1 / 2 - 1 / b) - E2 * Φc c / (6 * c ^ 2) := by ring
  rw [e]
  linarith [hmass, hint, hGq, hsplit]

end Cvs.Prolate.RungTailMassEnergyAtTwo
