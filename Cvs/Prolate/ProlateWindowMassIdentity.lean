import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window mass, the far energy and the weighted mass identity of a prolate solution

Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval/Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower with `exp x ≤ 1/(1 − x)` keep the energy within `(1 + W/2)/(1 − W)` of `E(ξ₀)`; with Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw and
`arccos(2/3) ≤ 0.842`, `arccos(5/6) ≤ 0.6` this gives `E(2)/(10c) ≤ ∫_{3/2}^2 ψ²` for `c ≥ 500` and
`E(ξ) ≤ 6c∫₁^X ψ²` on `[6/5, X]` for `c ≥ 80`, `X ≥ 2`. With `u(1) = 0`,
`∫₁^X u²/(pq) = ∫₁^X ψ² + ψ(X)u(X)/q(X) + ∫₁^X ψu q'/q²`. Rung forms via Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system.
-/

namespace Cvs.Prolate.ProlateWindowMassIdentity

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- `cos 0.842 ≤ 2/3`, by `Real.cos_bound` at a quarter of the angle and two doublings. -/
theorem cos_842_le : cos (842 / 1000) ≤ 2 / 3 := by
  set y : ℝ := 842 / 4000
  have hy : |y| ≤ 1 := by rw [abs_le]; constructor <;> norm_num [y]
  have hb := abs_le.mp (Real.cos_bound hy)
  rw [abs_of_nonneg (by norm_num [y] : (0:ℝ) ≤ y)] at hb
  have h1u : cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by linarith [hb.2]
  have h1l : 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) ≤ cos y := by linarith [hb.1]
  have h1l' : (0:ℝ) ≤ cos y := le_trans (by norm_num [y]) h1l
  have e2 : cos (2 * y) = 2 * cos y ^ 2 - 1 := cos_two_mul y
  have h2u : cos (2 * y) ≤ 2 * (1 - y ^ 2 / 2 + y ^ 4 * (5 / 96)) ^ 2 - 1 := by
    rw [e2]; nlinarith [pow_le_pow_left₀ h1l' h1u 2]
  have h2l : 2 * (1 - y ^ 2 / 2 - y ^ 4 * (5 / 96)) ^ 2 - 1 ≤ cos (2 * y) := by
    rw [e2]; nlinarith [pow_le_pow_left₀ (by norm_num [y]) h1l 2]
  have h2l' : (0:ℝ) ≤ cos (2 * y) := le_trans (by norm_num [y]) h2l
  have e4 : cos (842 / 1000) = 2 * cos (2 * y) ^ 2 - 1 := by
    rw [← cos_two_mul]; congr 1; norm_num [y]
  rw [e4]
  have := pow_le_pow_left₀ h2l' h2u 2
  have hn : 2 * (2 * (1 - y ^ 2 / 2 + y ^ 4 * (5 / 96)) ^ 2 - 1) ^ 2 - 1 ≤ 2 / 3 := by norm_num [y]
  nlinarith

/-- `arccos(1/2) − arccos(2/3) ≥ 0.205`. -/
theorem arccos_window_ge : (41 / 200 : ℝ) ≤ arccos (1 / 2) - arccos (2 / 3) := by
  have h12 : arccos (1 / 2) = π / 3 := by
    rw [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]
  have h23 : arccos (2 / 3) ≤ 842 / 1000 := by
    calc arccos (2 / 3) ≤ arccos (cos (842 / 1000)) := arccos_le_arccos cos_842_le
      _ = 842 / 1000 := arccos_cos (by norm_num) (by linarith [pi_gt_d6])
  rw [h12]; linarith [pi_gt_d6]

/-- `arccos(1/2) − arccos(5/6) ≥ 0.447`. -/
theorem arccos_far_ge : (447 / 1000 : ℝ) ≤ arccos (1 / 2) - arccos (5 / 6) := by
  have h12 : arccos (1 / 2) = π / 3 := by
    rw [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]
  have hc : cos (3 / 5) ≤ 5 / 6 := by
    have hy : |(3 / 5 : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
    have hb := (abs_le.mp (Real.cos_bound hy)).2
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3 / 5)] at hb
    norm_num at hb ⊢; linarith
  have h56 : arccos (5 / 6) ≤ 3 / 5 := by
    calc arccos (5 / 6) ≤ arccos (cos (3 / 5)) := arccos_le_arccos hc
      _ = 3 / 5 := arccos_cos (by norm_num) (by linarith [pi_gt_d6])
  rw [h12]; linarith [pi_gt_d6]

/-- **The two-sided energy window**: if `w(ξ₀) ≤ W < 1`, then on `[ξ₀, ξ₁]`
`E(ξ₀)(1 − W)/(1 + W/2) ≤ E ≤ E(ξ₀)(1 + W/2)/(1 − W)`. -/
theorem energy_window {c χ : ℝ} {ψ u : ℝ → ℝ} {ξ₀ ξ₁ W : ℝ} (h1 : 1 < ξ₀) (hc : 0 < c) (hχ : 0 ≤ χ)
    (hχc : χ < c ^ 2) (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ ≤ W) (hW1 : W < 1) :
    ∀ t ∈ Icc ξ₀ ξ₁, energy (aP c χ) ψ u ξ₀ * ((1 - W) / (1 + W / 2)) ≤ energy (aP c χ) ψ u t
      ∧ energy (aP c χ) ψ u t ≤ energy (aP c χ) ψ u ξ₀ * ((1 + W / 2) / (1 - W)) := by
  intro t ht
  have hc2 : 0 < c ^ 2 := by positivity
  set w := wP c χ ξ₀ with hw
  have hw0 : 0 < w := wP_pos h1 hc2 hχc
  have hw2 : w < 2 := by linarith
  set G₀ := energy (aP c χ) ψ u ξ₀
  have hG0 : 0 ≤ G₀ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos h1 hc2 hχc))
  have hψ' : ∀ s ∈ Icc ξ₀ t, HasDerivAt ψ (u s / pP s) s := fun s hs => hψ s ⟨hs.1, hs.2.trans ht.2⟩
  have hu' : ∀ s ∈ Icc ξ₀ t, HasDerivAt u (-(qP c χ s * ψ s)) s :=
    fun s hs => hu s ⟨hs.1, hs.2.trans ht.2⟩
  have hx0 : 0 ≤ w / (2 - w) := div_nonneg hw0.le (by linarith)
  have hx1 : w / (2 - w) < 1 := by rw [div_lt_one (by linarith)]; linarith
  constructor
  · have hge := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower.prolate_energy_ge h1 ht.1 hc2 hχ hχc hψ' hu' hw2
    have hexp : 1 - w / (2 - w) ≤ exp (-(w / (2 - w))) := by linarith [add_one_le_exp (-(w / (2 - w)))]
    have hfac : (1 - W) / (1 + W / 2) ≤ (1 - w / 2) / (1 + w / 2) * (1 - w / (2 - w)) := by
      have e : (1 - w / 2) / (1 + w / 2) * (1 - w / (2 - w)) = (1 - w) / (1 + w / 2) := by
        have : (2 : ℝ) - w ≠ 0 := by linarith
        have : (1 : ℝ) - w / (2 - w) = (2 - 2 * w) / (2 - w) := by field_simp; ring
        rw [this]; field_simp
      rw [e, div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    calc G₀ * ((1 - W) / (1 + W / 2)) ≤ G₀ * ((1 - w / 2) / (1 + w / 2) * (1 - w / (2 - w))) :=
          mul_le_mul_of_nonneg_left hfac hG0
      _ ≤ G₀ * ((1 - w / 2) / (1 + w / 2) * exp (-(w / (2 - w)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp
            (div_nonneg (by linarith) (by linarith))) hG0
      _ = G₀ * (1 - w / 2) / (1 + w / 2) * exp (-(w / (2 - w))) := by ring
      _ ≤ _ := hge
  · have hle := prolate_energy_le h1 ht.1 hc2 hχ hχc hψ' hu' hw2
    have hexp : exp (w / (2 - w)) ≤ 1 / (1 - w / (2 - w)) := exp_bound_div_one_sub_of_interval hx0 hx1
    have hfac : (1 + w / 2) / (1 - w / 2) * (1 / (1 - w / (2 - w))) ≤ (1 + W / 2) / (1 - W) := by
      have e : (1 + w / 2) / (1 - w / 2) * (1 / (1 - w / (2 - w))) = (1 + w / 2) / (1 - w) := by
        have : (1 : ℝ) - w ≠ 0 := by linarith
        have : (2 : ℝ) - w ≠ 0 := by linarith
        have : (1 : ℝ) - w / (2 - w) = (2 - 2 * w) / (2 - w) := by field_simp; ring
        rw [this]; field_simp
      rw [e, div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    calc energy (aP c χ) ψ u t ≤ G₀ * (1 + w / 2) / (1 - w / 2) * exp (w / (2 - w)) := hle
      _ = G₀ * ((1 + w / 2) / (1 - w / 2) * exp (w / (2 - w))) := by ring
      _ ≤ G₀ * ((1 + w / 2) / (1 - w / 2) * (1 / (1 - w / (2 - w)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp
            (div_nonneg (by linarith) (by linarith))) hG0
      _ ≤ G₀ * ((1 + W / 2) / (1 - W)) := mul_le_mul_of_nonneg_left hfac hG0

/-- **The window mass**: for `c ≥ 500`, `0 ≤ χ < c²` and a prolate solution on `[3/2, 2]`,
`E(2)/(10c) ≤ ∫_{3/2}^2 ψ²`. -/
theorem window_mass {c χ : ℝ} {ψ u : ℝ → ℝ} (hc : 500 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc (3 / 2 : ℝ) 2, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc (3 / 2 : ℝ) 2, HasDerivAt u (-(qP c χ t * ψ t)) t) :
    energy (aP c χ) ψ u 2 / (10 * c) ≤ ∫ ξ in (3 / 2 : ℝ)..2, ψ ξ ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have h1 : (1 : ℝ) < 3 / 2 := by norm_num
  have hW : wP c χ (3 / 2) ≤ 3 / 625 := by
    refine (Cvs.Prolate.Gram.RungGramFloorAtInfinity.wP_le_far h1 hc0 hχ0 hχ).trans ?_
    unfold pP
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hwin := energy_window h1 hc0 hχ0 hχ hψ hu hW (by norm_num)
  set G₀ := energy (aP c χ) ψ u (3 / 2)
  have hG0 : 0 ≤ G₀ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos h1 hc2 hχ))
  have hmass := (Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.prolate_mass_bounds h1 (by norm_num) hc0 hχ0 hχ hψ hu
    (fun t ht => (hwin t ht).1) (fun t ht => (hwin t ht).2)
    (mul_nonneg hG0 (by norm_num))).1
  have hΔ : (41 / 200 : ℝ) ≤ arccos (1 / 2) - arccos (1 / (3 / 2)) := by
    have := arccos_window_ge; norm_num at this ⊢; linarith
  have hq : 5 / 4 * c ^ 2 ≤ qP c χ (3 / 2) := by unfold qP; nlinarith
  have hE2 := (hwin 2 ⟨by norm_num, le_rfl⟩).2
  norm_num at hE2 hmass hΔ
  set Δ := arccos (1 / 2) - arccos (2 / 3)
  have hA : G₀ * (1244 / 1253) * (41 / 200) / (2 * c) ≤ G₀ * (1244 / 1253) * Δ / (2 * c) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ (by positivity)) (by positivity)
  have hB : G₀ * (1253 / 1244) / (2 * qP c χ (3 / 2)) ≤ G₀ * (1253 / 1244) / (1250 * c) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have hC : energy (aP c χ) ψ u 2 / (10 * c) ≤ G₀ * (1253 / 1244) / (10 * c) :=
    div_le_div_of_nonneg_right (by norm_num at hE2 ⊢; linarith) (by positivity)
  have hK : 0 ≤ G₀ / c := div_nonneg hG0 hc0.le
  have e1 : G₀ * (1253 / 1244) / (10 * c) = G₀ / c * (1253 / 12440) := by ring
  have e2 : G₀ * (1244 / 1253) * (41 / 200) / (2 * c) = G₀ / c * (1244 * 41 / (1253 * 400)) := by ring
  have e3 : G₀ * (1253 / 1244) / (1250 * c) = G₀ / c * (1253 / (1244 * 1250)) := by ring
  have hnum := mul_le_mul_of_nonneg_left
    (show (1253 / 12440 : ℝ) ≤ 1244 * 41 / (1253 * 400) - 1253 / (1244 * 1250) by norm_num) hK
  have e4 : G₀ * (1244 / 1253) * Δ / (2 * c) = G₀ * 1244 / 1253 * Δ / (2 * c) := by ring
  have e5 : G₀ * (1253 / 1244) / (2 * qP c χ (3 / 2)) = G₀ * 1253 / 1244 / (2 * qP c χ (3 / 2)) := by ring
  rw [e1] at hC; rw [e2] at hA; rw [e3] at hB
  nlinarith

/-- **The far energy against the mass**: for `c ≥ 80`, `0 ≤ χ < c²`, `X ≥ 2` and a prolate solution on
`[6/5, X]` with `ψ` continuous on `[1, X]`, `E(ξ) ≤ 6c∫₁^X ψ²` for every `ξ ∈ [6/5, X]`. -/
theorem far_energy_le {c χ X : ℝ} {ψ u : ℝ → ℝ} (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hX : 2 ≤ X)
    (hψ : ∀ t ∈ Icc (6 / 5 : ℝ) X, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc (6 / 5 : ℝ) X, HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hcont : ContinuousOn ψ (Icc 1 X)) :
    ∀ ξ ∈ Icc (6 / 5 : ℝ) X, energy (aP c χ) ψ u ξ ≤ 6 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2 := by
  intro ξ hξ
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have h1 : (1 : ℝ) < 6 / 5 := by norm_num
  have hW : wP c χ (6 / 5) ≤ 3 / 44 := by
    refine (Cvs.Prolate.Gram.RungGramFloorAtInfinity.wP_le_far h1 hc0 hχ0 hχ).trans ?_
    unfold pP
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hwin := energy_window h1 hc0 hχ0 hχ hψ hu hW (by norm_num)
  have sub : ∀ t ∈ Icc (6 / 5 : ℝ) 2, t ∈ Icc (6 / 5 : ℝ) X := fun t ht => ⟨ht.1, ht.2.trans hX⟩
  set G₀ := energy (aP c χ) ψ u (6 / 5)
  have hG0 : 0 ≤ G₀ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos h1 hc2 hχ))
  have hmass := (Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.prolate_mass_bounds h1 (by norm_num) hc0 hχ0 hχ
    (fun t ht => hψ t (sub t ht)) (fun t ht => hu t (sub t ht))
    (fun t ht => (hwin t (sub t ht)).1) (fun t ht => (hwin t (sub t ht)).2)
    (mul_nonneg hG0 (by norm_num))).1
  have hΔ : (447 / 1000 : ℝ) ≤ arccos (1 / 2) - arccos (1 / (6 / 5)) := by
    have := arccos_far_ge; norm_num at this ⊢; linarith
  have hq : 11 / 25 * c ^ 2 ≤ qP c χ (6 / 5) := by unfold qP; nlinarith
  have hEξ := (hwin ξ hξ).2
  -- the window `[6/5, 2]` inside `[1, X]`
  have hsub : ∫ t in (6 / 5 : ℝ)..2, ψ t ^ 2 ≤ ∫ t in (1 : ℝ)..X, ψ t ^ 2 :=
    intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) hX
      (Filter.Eventually.of_forall fun t => sq_nonneg (ψ t))
      ((hcont.pow 2).intervalIntegrable_of_Icc (by linarith))
  norm_num at hEξ hmass hΔ
  set Δ := arccos (1 / 2) - arccos (5 / 6)
  have hA : G₀ * (82 / 91) * (447 / 1000) / (2 * c) ≤ G₀ * (82 / 91) * Δ / (2 * c) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ (by positivity)) (by positivity)
  have hB : G₀ * (91 / 82) / (2 * qP c χ (6 / 5)) ≤ G₀ * (91 / 82) / (352 / 5 * c) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have hK : 0 ≤ G₀ / c := div_nonneg hG0 hc0.le
  have e2 : G₀ * (82 / 91) * (447 / 1000) / (2 * c) = G₀ / c * (82 * 447 / (91 * 2000)) := by ring
  have e3 : G₀ * (91 / 82) / (352 / 5 * c) = G₀ / c * (91 * 5 / (82 * 352)) := by ring
  rw [e2] at hA; rw [e3] at hB
  have e4 : G₀ * (82 / 91) * Δ / (2 * c) = G₀ * 82 / 91 * Δ / (2 * c) := by ring
  have e5 : G₀ * (91 / 82) / (2 * qP c χ (6 / 5)) = G₀ * 91 / 82 / (2 * qP c χ (6 / 5)) := by ring
  -- `G₀/c · κ ≤ ∫₁^X ψ²` with `6cκ ≥ 91/82 · c`
  have hlow : G₀ / c * (82 * 447 / (91 * 2000) - 91 * 5 / (82 * 352)) ≤ ∫ t in (1 : ℝ)..X, ψ t ^ 2 := by
    nlinarith
  have hnum := mul_le_mul_of_nonneg_left
    (show (91 / 82 : ℝ) ≤ 6 * (82 * 447 / (91 * 2000) - 91 * 5 / (82 * 352)) by norm_num) hG0
  have hcK : c * (G₀ / c) = G₀ := mul_div_cancel₀ G₀ hc0.ne'
  calc energy (aP c χ) ψ u ξ ≤ G₀ * (91 / 82) := by linarith
    _ ≤ G₀ * (6 * (82 * 447 / (91 * 2000) - 91 * 5 / (82 * 352))) := by linarith
    _ = 6 * (c * (G₀ / c)) * (82 * 447 / (91 * 2000) - 91 * 5 / (82 * 352)) := by rw [hcK]; ring
    _ = 6 * c * (G₀ / c * (82 * 447 / (91 * 2000) - 91 * 5 / (82 * 352))) := by ring
    _ ≤ 6 * c * ∫ t in (1 : ℝ)..X, ψ t ^ 2 := mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **The weighted mass identity**: for a prolate solution on `(1, X)`, continuous on `[1, X]`, with
`u(1) = 0` and `χ < c²`, `∫₁^X u²/(pq) = ∫₁^X ψ² + ψ(X)u(X)/q(X) + ∫₁^X ψu(2c²ξ)/q²`. -/
theorem integral_u_sq_eq {c χ X : ℝ} {ψ u : ℝ → ℝ} (hX : 1 ≤ X) (hχ : χ < c ^ 2)
    (hψc : ContinuousOn ψ (Icc 1 X)) (huc : ContinuousOn u (Icc 1 X))
    (hψ : ∀ t ∈ Ioo 1 X, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Ioo 1 X, HasDerivAt u (-(qP c χ t * ψ t)) t) (hu1 : u 1 = 0) :
    ∫ ξ in (1 : ℝ)..X, u ξ ^ 2 / (pP ξ * qP c χ ξ)
      = (∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2) + ψ X * u X / qP c χ X
        + ∫ ξ in (1 : ℝ)..X, ψ ξ * u ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2 := by
  have hq : ∀ t ∈ Icc 1 X, 0 < qP c χ t := fun t ht => by
    unfold qP; nlinarith [ht.1, sq_nonneg c, mul_le_mul_of_nonneg_left
      (show (1:ℝ) ≤ t ^ 2 by nlinarith [ht.1]) (sq_nonneg c)]
  have hqc : ContinuousOn (qP c χ) (Icc 1 X) := by unfold qP; fun_prop
  have hqd : ∀ t, HasDerivAt (qP c χ) (2 * c ^ 2 * t) t := fun t => by
    have h := ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).sub_const χ
    exact h.congr_deriv (by ring)
  set S : ℝ → ℝ := fun t => ψ t ^ 2 + ψ t * u t * (2 * c ^ 2 * t) / qP c χ t ^ 2 with hS
  have hTc : ContinuousOn (fun t => ψ t * u t * (2 * c ^ 2 * t) / qP c χ t ^ 2) (Icc 1 X) :=
    ((hψc.mul huc).mul (by fun_prop)).div (hqc.pow 2) fun t ht => by have := hq t ht; positivity
  have hSc : ContinuousOn S (Icc 1 X) := (hψc.pow 2).add hTc
  have hSi : IntervalIntegrable S MeasureTheory.volume 1 X := hSc.intervalIntegrable_of_Icc hX
  set H : ℝ → ℝ := fun t => ψ t * u t / qP c χ t + ∫ s in (1 : ℝ)..t, S s with hH
  have hI : uIcc 1 X = Icc 1 X := uIcc_of_le hX
  have hHc : ContinuousOn H (Icc 1 X) := by
    refine ((hψc.mul huc).div hqc fun t ht => (hq t ht).ne').add ?_
    have := intervalIntegral.continuousOn_primitive_interval' hSi (left_mem_uIcc (a := (1:ℝ)) (b := X))
    rwa [hI] at this
  have hIoo : ∀ t ∈ Ioo 1 X, t ∈ Icc 1 X := fun t ht => Ioo_subset_Icc_self ht
  have hHd : ∀ t ∈ Ioo 1 X, HasDerivAt H (u t ^ 2 / (pP t * qP c χ t)) t := by
    intro t ht
    have hp : pP t ≠ 0 := (pP_pos ht.1).ne'
    have hqt : qP c χ t ≠ 0 := (hq t (hIoo t ht)).ne'
    have hV := ((hψ t ht).mul (hu t ht)).div (hqd t) hqt
    have hnhds : Icc 1 X ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hSt : ContinuousAt S t := hSc.continuousAt hnhds
    have hP := intervalIntegral.integral_hasDerivAt_right
      ((hSc.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
      ((hSc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht) hSt
    refine (hV.add hP).congr_deriv ?_
    simp only [hS, Pi.mul_apply]
    field_simp
    ring
  have hpos : ∀ t ∈ Ioo 1 X, 0 ≤ u t ^ 2 / (pP t * qP c χ t) := fun t ht =>
    div_nonneg (sq_nonneg _) (mul_pos (pP_pos ht.1) (hq t (hIoo t ht))).le
  have hint : IntervalIntegrable (fun t => u t ^ 2 / (pP t * qP c χ t)) MeasureTheory.volume 1 X :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr
      (integrableOn_deriv_of_nonneg hHc hHd hpos)
  rw [integral_eq_sub_of_hasDerivAt_of_le hX hHc hHd hint]
  simp only [hH, hu1, mul_zero, zero_div, integral_same, add_zero, sub_zero]
  have hSint : ∫ s in (1 : ℝ)..X, S s = (∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2)
      + ∫ ξ in (1 : ℝ)..X, ψ ξ * u ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2 :=
    intervalIntegral.integral_add ((hψc.pow 2).intervalIntegrable_of_Icc hX)
      (hTc.intervalIntegrable_of_Icc hX)
  rw [hSint]
  ring

section rung

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- `window_mass` for a rung `ψ = psi c g` with `u = rungU c g`. -/
theorem window_mass_rung (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 500 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) :
    energy (aP c χ) (psi c g) (rungU c g) 2 / (10 * c) ≤ ∫ ξ in (3 / 2 : ℝ)..2, psi c g ξ ^ 2 := by
  obtain ⟨hψ, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
  exact window_mass hc hχ0 hχ (fun t ht => hψ t (by linarith [ht.1])) (fun t _ => hu t)

/-- `far_energy_le` for a rung `ψ = psi c g` with `u = rungU c g`. -/
theorem far_energy_le_rung (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {X : ℝ} (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hX : 2 ≤ X) :
    ∀ ξ ∈ Icc (6 / 5 : ℝ) X,
      energy (aP c χ) (psi c g) (rungU c g) ξ ≤ 6 * c * ∫ t in (1 : ℝ)..X, psi c g t ^ 2 := by
  obtain ⟨hψ, hu, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  exact far_energy_le hc hχ0 hχ hX (fun t ht => hψ t (by linarith [ht.1])) (fun t _ => hu t)
    hψc.continuousOn

/-- `integral_u_sq_eq` for a rung `ψ = psi c g` with `u = rungU c g`, given `u(1) = 0`. -/
theorem integral_u_sq_eq_rung (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {X : ℝ} (hX : 1 ≤ X) (hχ : χ < c ^ 2) (hu1 : rungU c g 1 = 0) :
    ∫ ξ in (1 : ℝ)..X, rungU c g ξ ^ 2 / (pP ξ * qP c χ ξ)
      = (∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2) + psi c g X * rungU c g X / qP c χ X
        + ∫ ξ in (1 : ℝ)..X, psi c g ξ * rungU c g ξ * (2 * c ^ 2 * ξ) / qP c χ ξ ^ 2 := by
  obtain ⟨hψ, hu, hψc, huc⟩ := rung_system hg hg₁ hg₂c hang
  exact integral_u_sq_eq hX hχ hψc.continuousOn huc.continuousOn (fun t ht => hψ t ht.1)
    (fun t _ => hu t) hu1

end rung

end Cvs.Prolate.ProlateWindowMassIdentity
