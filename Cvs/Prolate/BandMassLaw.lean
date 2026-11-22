import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CorrectedEnergyAntitone
import Cvs.Prolate.EdgeBesselCount
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy
import Cvs.Prolate.RungConnectionIdentity
import Cvs.Prolate.RungOrthogonalityAtInfinity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The band mass law: `cM ≥ (E∞/4)(log(1 + 2c/r₀) − 2k)` and the far fraction, `λ`-free

For `0 ≤ χ < c²`: the sign polynomial is `q² + c²y²(2c² + χ) + 2c⁴y³`, `w ≤ 2ξ/(cp)`, and the energy obeys
`E∞(1 − w/2)/(1 + w/2) ≤ E ≤ E∞/(1 − w/2)²`. Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy from `ξ₀ = 1 + r₀/c` gives the mass law and
`f(ξ)(log(1 + 2c/r₀) − 2k) ≤ ℓ(ξ)(1 + δ_c(ξ))`, `ℓ(ξ) = log((ξ + 1)/(ξ − 1))`, with `E∞` cancelled.
-/

namespace Cvs.Prolate.BandMassLaw

open Real Set Filter Topology MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-! ### The sign polynomial and the rate `w` -/

/-- **The sign-polynomial identity**: with `y = X − 1` and `q = c²X − χ`, `ProlateEnergyOutsideInterval`'s sign polynomial is
`q² + c²y²(2c² + χ) + 2c⁴y³`. -/
theorem signPoly_eq (c χ X : ℝ) :
    c ^ 4 * (2 * X ^ 3 - 3 * X ^ 2 + 2 * X) + c ^ 2 * χ * (X ^ 2 - 4 * X + 1) + χ ^ 2
      = (c ^ 2 * X - χ) ^ 2 + c ^ 2 * (X - 1) ^ 2 * (2 * c ^ 2 + χ) + 2 * c ^ 4 * (X - 1) ^ 3 := by
  ring

/-- The sign polynomial is nonnegative for `X ≥ 1` and `χ ≥ −2c²`, with no upper bound on `χ`. -/
theorem signPoly_nonneg' {c χ X : ℝ} (hX : 1 ≤ X) (hχ : -(2 * c ^ 2) ≤ χ) :
    0 ≤ c ^ 4 * (2 * X ^ 3 - 3 * X ^ 2 + 2 * X) + c ^ 2 * χ * (X ^ 2 - 4 * X + 1) + χ ^ 2 := by
  rw [signPoly_eq]
  have hy : 0 ≤ X - 1 := by linarith
  have h2 : 0 ≤ c ^ 2 * (X - 1) ^ 2 * (2 * c ^ 2 + χ) := mul_nonneg (by positivity) (by linarith)
  have h3 : 0 ≤ 2 * c ^ 4 * (X - 1) ^ 3 := by positivity
  nlinarith [sq_nonneg (c ^ 2 * X - χ)]

/-- **`w` decreases** for `ξ > 1`, `−2c² ≤ χ < c²`, by the sign-polynomial identity. -/
theorem wP'_nonpos' {c χ ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c ^ 2) (hχ : -(2 * c ^ 2) ≤ χ) (hχc : χ < c ^ 2) :
    wP' c χ ξ ≤ 0 := by
  have ha := aP_pos hξ hc hχc
  have hq := qP_pos hξ hc hχc
  have hP := signPoly_nonneg' (X := ξ ^ 2) (by nlinarith) hχ
  have ha2 := aP_sq hξ hc hχc
  unfold wP' wP
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have key : (2 * (6 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ) * (2 * qP c χ ξ * aP c χ ξ)
      - dP c χ ξ * (2 * (2 * c ^ 2 * ξ * aP c χ ξ
        + qP c χ ξ * (dP c χ ξ / (2 * qP c χ ξ * aP c χ ξ) * qP c χ ξ)))) * aP c χ ξ
      = qP c χ ξ * (-4 * (c ^ 4 * (2 * (ξ ^ 2) ^ 3 - 3 * (ξ ^ 2) ^ 2 + 2 * ξ ^ 2)
        + c ^ 2 * χ * ((ξ ^ 2) ^ 2 - 4 * ξ ^ 2 + 1) + χ ^ 2)) := by
    field_simp
    rw [ha2]
    unfold pP qP dP
    ring
  have hrhs : qP c χ ξ * (-4 * (c ^ 4 * (2 * (ξ ^ 2) ^ 3 - 3 * (ξ ^ 2) ^ 2 + 2 * ξ ^ 2)
        + c ^ 2 * χ * ((ξ ^ 2) ^ 2 - 4 * ξ ^ 2 + 1) + χ ^ 2)) ≤ 0 := by nlinarith
  by_contra hcon
  push Not at hcon
  have := mul_pos hcon ha
  linarith

/-- `w` is antitone on `(1, ∞)` for `0 ≤ χ < c²`. -/
theorem wP_antitoneOn {c χ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) :
    AntitoneOn (wP c χ) (Ioi 1) := by
  have hc2 : 0 < c ^ 2 := by positivity
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 1)
  · exact fun t ht => (hasDerivAt_wP (show 1 < t from ht) hc2 hχc).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; exact fun t ht =>
      (hasDerivAt_wP (show 1 < t from ht) hc2 hχc).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro t ht
    rw [(hasDerivAt_wP (show 1 < t from ht) hc2 hχc).deriv]
    exact wP'_nonpos' ht hc2 (by linarith) hχc

/-- The majorant `2ξ/(c(ξ² − 1))` of the rate `w`. -/
noncomputable def wUp (c ξ : ℝ) : ℝ := 2 * ξ / (c * pP ξ)

/-- `cp ≤ a` for `χ ≤ c²`. -/
theorem mul_pP_le_aP {c χ ξ : ℝ} (hc : 0 < c) (hχc : χ ≤ c ^ 2) (hξ : 1 < ξ) :
    c * pP ξ ≤ aP c χ ξ := by
  have hp := pP_pos hξ
  unfold aP
  rw [show c * pP ξ = √((c * pP ξ) ^ 2) from (sqrt_sq (by positivity)).symm]
  apply sqrt_le_sqrt
  have : c ^ 2 * pP ξ ≤ qP c χ ξ := by unfold qP pP; nlinarith
  nlinarith

/-- **`w ≤ 2ξ/(cp)`** for `ξ > 1`, `χ < c²`. -/
theorem wP_le_wUp {c χ ξ : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hξ : 1 < ξ) :
    wP c χ ξ ≤ wUp c ξ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp := pP_pos hξ
  have ha := aP_pos hξ hc2 hχc
  have hq := qP_pos hξ hc2 hχc
  have hcp := mul_pP_le_aP hc hχc.le hξ
  have hpq : c ^ 2 * pP ξ ≤ qP c χ ξ := by unfold qP pP; nlinarith
  unfold wP wUp
  have e : dP c χ ξ = 2 * ξ * (qP c χ ξ + c ^ 2 * pP ξ) := by unfold dP qP pP; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have hξ0 : 0 < ξ := by linarith
  have h1 : 2 * ξ * (qP c χ ξ + c ^ 2 * pP ξ) ≤ 2 * ξ * (2 * qP c χ ξ) := by nlinarith
  have h2 : 2 * ξ * (2 * qP c χ ξ) * (c * pP ξ) ≤ 2 * ξ * (2 * qP c χ ξ * aP c χ ξ) := by
    have : 0 ≤ 2 * ξ * (2 * qP c χ ξ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hcp this]
  nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ c * pP ξ)]

/-- `wUp` is antitone on `(1, ∞)` for `c > 0`. -/
theorem wUp_le_wUp {c ξ₀ ξ : ℝ} (hc : 0 < c) (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ) : wUp c ξ ≤ wUp c ξ₀ := by
  have hp0 := pP_pos h1
  have hp := pP_pos (lt_of_lt_of_le h1 hle)
  unfold wUp
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  unfold pP at *
  have : 0 ≤ (ξ - ξ₀) * (ξ * ξ₀ + 1) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith [mul_nonneg hc.le this]

/-- `wUp c ξ → 0` as `ξ → ∞`. -/
theorem tendsto_wUp {c : ℝ} (hc : 0 < c) : Tendsto (wUp c) atTop (𝓝 0) := by
  have h : Tendsto (fun ξ : ℝ => 4 / c * ξ⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (4 / c)
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_gt_atTop 1] with ξ hξ
    have := pP_pos hξ; unfold wUp; have : 0 < ξ := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop 2] with ξ hξ
    have hp := pP_pos (show 1 < ξ by linarith)
    unfold wUp
    rw [div_le_iff₀ (by positivity)]
    unfold pP at *
    have hξ0 : 0 < ξ := by linarith
    field_simp
    nlinarith

/-! ### The two-sided energy bracket -/

section bracket
variable {ψ u p q a w w' : ℝ → ℝ}

/-- **The mirror corrected energy is monotone**: for `w` decreasing in `[0, 2]`, `(E + wψu)(1 − w/2)` does not
decrease, since its derivative is `w'(ψu(1 − w) − E/2) ≥ 0`. -/
theorem corrected_mul_monotoneOn {t₀ t₁ : ℝ}
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Icc t₀ t₁, HasDerivAt w (w' t) t)
    (hw' : ∀ t ∈ Icc t₀ t₁, w' t ≤ 0) (hw0 : ∀ t ∈ Icc t₀ t₁, 0 ≤ w t) (hw2 : ∀ t ∈ Icc t₀ t₁, w t ≤ 2) :
    MonotoneOn (fun s => (energy a ψ u s + w s * (ψ s * u s)) * (1 - w s / 2)) (Icc t₀ t₁) := by
  set F : ℝ → ℝ := fun s => energy a ψ u s + w s * (ψ s * u s) with hFdef
  have hF : ∀ t ∈ Icc t₀ t₁, HasDerivAt F (w' t * (ψ t * u t)) t := fun t ht =>
    hasDerivAt_energy_add (ha t ht) (hp t ht) (hapq t ht) (hψ t ht) (hu t ht) (haw t ht) (hw t ht)
  have hg : ∀ t ∈ Icc t₀ t₁, HasDerivAt (fun s => 1 - w s / 2) (-(w' t / 2)) t := fun t ht =>
    ((hw t ht).div_const 2).const_sub 1
  apply monotoneOn_of_deriv_nonneg (convex_Icc t₀ t₁)
  · exact fun t ht => ((hF t ht).fun_mul (hg t ht)).continuousAt.continuousWithinAt
  · rw [interior_Icc]
    exact fun t ht => ((hF t (Ioo_subset_Icc_self ht)).fun_mul
      (hg t (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro t ht
    have ht' := Ioo_subset_Icc_self ht
    rw [((hF t ht').fun_mul (hg t ht')).deriv]
    have e : w' t * (ψ t * u t) * (1 - w t / 2) + F t * -(w' t / 2)
        = -w' t * (energy a ψ u t / 2 - (1 - w t) * (ψ t * u t)) := by simp only [hFdef]; ring
    rw [e]
    have h := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht')
    have hb : |(1 - w t) * (ψ t * u t)| ≤ energy a ψ u t / 2 := by
      rw [abs_mul]
      have : |1 - w t| ≤ 1 := abs_le.mpr ⟨by linarith [hw2 t ht'], by linarith [hw0 t ht']⟩
      have := mul_le_mul_of_nonneg_right this (abs_nonneg (ψ t * u t))
      linarith
    have := le_abs_self ((1 - w t) * (ψ t * u t))
    exact mul_nonneg (by linarith [hw' t ht']) (by linarith)

end bracket

/-- The energy of a solution is nonnegative where `a > 0`. -/
theorem energy_nonneg {a ψ u : ℝ → ℝ} {t : ℝ} (ha : 0 < a t) : 0 ≤ energy a ψ u t := by
  unfold energy; positivity

section prolate
variable {c χ Einf : ℝ} {ψ u : ℝ → ℝ}

/-- The energy limit `E∞` of a prolate solution is nonnegative. -/
theorem einf_nonneg (hc : 0 < c) (hχc : χ < c ^ 2)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) : 0 ≤ Einf := by
  refine ge_of_tendsto hE ?_
  filter_upwards [eventually_gt_atTop 1] with ξ hξ
  exact energy_nonneg (aP_pos hξ (by positivity) hχc)

/-- The corrected energy `E + wψu` of a prolate solution tends to `E∞`. -/
theorem tendsto_corrected (hc : 0 < c) (hχc : χ < c ^ 2)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) :
    Tendsto (fun ξ => energy (aP c χ) ψ u ξ + wP c χ ξ * (ψ ξ * u ξ)) atTop (𝓝 Einf) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hw : Tendsto (wP c χ) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (tendsto_wUp hc)
    · filter_upwards [eventually_gt_atTop 1] with ξ hξ using (wP_pos hξ hc2 hχc).le
    · filter_upwards [eventually_gt_atTop 1] with ξ hξ using wP_le_wUp hc hχc hξ
  have hwE : Tendsto (fun ξ => wP c χ ξ * energy (aP c χ) ψ u ξ / 2) atTop (𝓝 0) := by
    simpa using (hw.mul hE).div_const 2
  have hcross : Tendsto (fun ξ => wP c χ ξ * (ψ ξ * u ξ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hwE
    filter_upwards [eventually_gt_atTop 1] with ξ hξ
    have hw0 := (wP_pos hξ hc2 hχc).le
    have h := two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos hξ hc2 hχc)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    nlinarith [mul_le_mul_of_nonneg_left h hw0]
  simpa using hE.add hcross

/-- **The energy bracket**: for a solution on `(1, ∞)` with `E → E∞`, `0 ≤ χ < c²` and `w(ξ) < 2`,
`E∞(1 − w/2)/(1 + w/2) ≤ E(ξ) ≤ E∞/(1 − w/2)²`. -/
theorem energy_bracket {ξ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hξ : 1 < ξ)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hW : wP c χ ξ < 2) :
    Einf * (1 - wP c χ ξ / 2) / (1 + wP c χ ξ / 2) ≤ energy (aP c χ) ψ u ξ
      ∧ energy (aP c χ) ψ u ξ ≤ Einf / (1 - wP c χ ξ / 2) ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hanti := wP_antitoneOn hc hχ hχc
  set E := energy (aP c χ) ψ u
  set w := wP c χ
  set H : ℝ → ℝ := fun s => E s + w s * (ψ s * u s) with hH
  have hHlim : Tendsto H atTop (𝓝 Einf) := tendsto_corrected hc hχc hE
  have hw : Tendsto w atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (tendsto_wUp hc)
    · filter_upwards [eventually_gt_atTop 1] with t ht using (wP_pos ht hc2 hχc).le
    · filter_upwards [eventually_gt_atTop 1] with t ht using wP_le_wUp hc hχc ht
  -- the hypotheses of the two monotonicity lemmas on `[ξ, X]`
  have gt1 : ∀ X, ∀ t ∈ Icc ξ X, 1 < t := fun X t ht => lt_of_lt_of_le hξ ht.1
  have hwle : ∀ X, ∀ t ∈ Icc ξ X, w t ≤ w ξ := fun X t ht =>
    hanti (show (1 : ℝ) < ξ from hξ) (show 1 < t from gt1 X t ht) ht.1
  have hH1 : ∀ X, ξ ≤ X → H X / (1 - w X / 2) ≤ H ξ / (1 - w ξ / 2) := fun X hX =>
    Cvs.Prolate.CorrectedEnergyAntitone.corrected_antitoneOn (fun t ht => aP_pos (gt1 X t ht) hc2 hχc)
      (fun t ht => (pP_pos (gt1 X t ht)).ne') (fun t ht => aP_sq (gt1 X t ht) hc2 hχc)
      (fun t ht => hψ t (gt1 X t ht)) (fun t ht => hu t (gt1 X t ht))
      (fun t ht => hasDerivAt_aP (gt1 X t ht) hc2 hχc) (fun t ht => hasDerivAt_wP (gt1 X t ht) hc2 hχc)
      (fun t ht => wP'_nonpos (gt1 X t ht) hc2 hχ hχc) (fun t ht => lt_of_le_of_lt (hwle X t ht) hW)
      (left_mem_Icc.mpr hX) (right_mem_Icc.mpr hX) hX
  have hH2 : ∀ X, ξ ≤ X → H ξ * (1 - w ξ / 2) ≤ H X * (1 - w X / 2) := fun X hX =>
    corrected_mul_monotoneOn (fun t ht => aP_pos (gt1 X t ht) hc2 hχc)
      (fun t ht => (pP_pos (gt1 X t ht)).ne') (fun t ht => aP_sq (gt1 X t ht) hc2 hχc)
      (fun t ht => hψ t (gt1 X t ht)) (fun t ht => hu t (gt1 X t ht))
      (fun t ht => hasDerivAt_aP (gt1 X t ht) hc2 hχc) (fun t ht => hasDerivAt_wP (gt1 X t ht) hc2 hχc)
      (fun t ht => wP'_nonpos (gt1 X t ht) hc2 hχ hχc) (fun t ht => (wP_pos (gt1 X t ht) hc2 hχc).le)
      (fun t ht => (lt_of_le_of_lt (hwle X t ht) hW).le)
      (left_mem_Icc.mpr hX) (right_mem_Icc.mpr hX) hX
  have hlim1 : Tendsto (fun X => H X / (1 - w X / 2)) atTop (𝓝 Einf) := by
    have h := hHlim.div ((hw.div_const 2).const_sub 1) (by norm_num : (1 : ℝ) - 0 / 2 ≠ 0)
    rwa [zero_div, sub_zero, div_one] at h
  have hlim2 : Tendsto (fun X => H X * (1 - w X / 2)) atTop (𝓝 Einf) := by
    have h := hHlim.mul ((hw.div_const 2).const_sub 1)
    rwa [zero_div, sub_zero, mul_one] at h
  have hF : Einf ≤ H ξ / (1 - w ξ / 2) :=
    le_of_tendsto hlim1 (by filter_upwards [eventually_ge_atTop ξ] with X hX using hH1 X hX)
  have hG : H ξ * (1 - w ξ / 2) ≤ Einf :=
    ge_of_tendsto hlim2 (by filter_upwards [eventually_ge_atTop ξ] with X hX using hH2 X hX)
  have hw0 : 0 ≤ w ξ := (wP_pos hξ hc2 hχc).le
  have hpos : 0 < 1 - w ξ / 2 := by linarith
  have hEb := two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos hξ hc2 hχc)
  have hab := abs_le.mp (show |ψ ξ * u ξ| ≤ E ξ / 2 by linarith)
  have hHup : H ξ ≤ E ξ * (1 + w ξ / 2) := by
    simp only [hH]; nlinarith [mul_le_mul_of_nonneg_left hab.2 hw0]
  have hHlo : E ξ * (1 - w ξ / 2) ≤ H ξ := by
    simp only [hH]; nlinarith [mul_le_mul_of_nonneg_left hab.1 hw0]
  rw [le_div_iff₀ hpos] at hF
  constructor
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hHlo hpos.le]

end prolate

/-! ### Closed-form integrals and pointwise bounds -/

/-- `ℓ(ξ) = log((ξ + 1)/(ξ − 1))`. -/
noncomputable def ellF (ξ : ℝ) : ℝ := log ((ξ + 1) / (ξ - 1))

/-- `ℓ' = −2/(ξ² − 1)` for `ξ > 1`. -/
theorem hasDerivAt_ellF {ξ : ℝ} (hξ : 1 < ξ) : HasDerivAt ellF (-(2 / pP ξ)) ξ := by
  have h1 : (ξ - 1) ≠ 0 := by linarith
  have hf : HasDerivAt (fun t => (t + 1) / (t - 1)) ((1 * (ξ - 1) - (ξ + 1) * 1) / (ξ - 1) ^ 2) ξ :=
    ((hasDerivAt_id ξ).add_const 1).div ((hasDerivAt_id ξ).sub_const 1) h1
  have hne : (ξ + 1) / (ξ - 1) ≠ 0 := div_ne_zero (by linarith) h1
  refine (hf.log hne).congr_deriv ?_
  rw [show pP ξ = (ξ - 1) * (ξ + 1) by unfold pP; ring]
  have h2 : ξ + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `ℓ(ξ) > 0` for `ξ > 1`. -/
theorem ellF_pos {ξ : ℝ} (hξ : 1 < ξ) : 0 < ellF ξ := by
  unfold ellF
  apply Real.log_pos
  rw [one_lt_div (by linarith)]; linarith

/-- `ℓ(ξ) → 0` as `ξ → ∞`. -/
theorem tendsto_ellF : Tendsto ellF atTop (𝓝 0) := by
  have h : Tendsto (fun ξ : ℝ => 4 * ξ⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul 4
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_gt_atTop 1] with ξ hξ using (ellF_pos hξ).le
  · filter_upwards [eventually_ge_atTop 2] with ξ hξ
    have hpos : 0 < (ξ + 1) / (ξ - 1) := div_pos (by linarith) (by linarith)
    refine (Real.log_le_sub_one_of_pos hpos).trans ?_
    rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    have : 0 < ξ := by linarith
    field_simp
    nlinarith

/-- `∫_a^b 1/(ξ² − 1) = (ℓ(a) − ℓ(b))/2` for `1 < a ≤ b`. -/
theorem integral_inv_pP {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / pP t = (ellF a - ellF b) / 2 := by
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  have gt1 : ∀ t ∈ uIcc a b, 1 < t := fun t ht => lt_of_lt_of_le ha (hI ▸ ht).1
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun s => -(ellF s / 2)) (1 / pP t) t := fun t ht =>
    ((hasDerivAt_ellF (gt1 t ht)).div_const 2).neg.congr_deriv (by ring)
  have hc : ContinuousOn (fun t => 1 / pP t) (uIcc a b) :=
    continuousOn_const.div₀ (by unfold pP; fun_prop) fun t ht => (pP_pos (gt1 t ht)).ne'
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  ring

/-- `∫_a^b ξ/(ξ² − 1)² = 1/(2p(a)) − 1/(2p(b))` for `1 < a ≤ b`. -/
theorem integral_xi_div_pP_sq {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, t / pP t ^ 2 = 1 / (2 * pP a) - 1 / (2 * pP b) := by
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  have gt1 : ∀ t ∈ uIcc a b, 1 < t := fun t ht => lt_of_lt_of_le ha (hI ▸ ht).1
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun s => -(1 / (2 * pP s))) (t / pP t ^ 2) t := by
    intro t ht
    have hp := pP_pos (gt1 t ht)
    have hpd : HasDerivAt (fun s => 2 * pP s) (2 * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).sub_const 1).const_mul 2
      unfold pP; simpa using this
    have := (hpd.inv (by positivity)).neg
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · field_simp
    · filter_upwards with s; simp [one_div]
  have hc : ContinuousOn (fun t => t / pP t ^ 2) (uIcc a b) :=
    continuousOn_id.div₀ (by unfold pP; fun_prop) fun t ht => by have := pP_pos (gt1 t ht); positivity
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  ring

/-- `c/a ≥ 1/p − σ²/(2c²p²)`, `σ² = c² − χ`, for `ξ > 1`, `χ ≤ c²`. -/
theorem c_div_aP_ge {c χ ξ : ℝ} (hc : 0 < c) (hχc : χ ≤ c ^ 2) (hξ : 1 < ξ) :
    1 / pP ξ - (c ^ 2 - χ) / (2 * c ^ 2 * pP ξ ^ 2) ≤ c / aP c χ ξ := by
  have hp := pP_pos hξ
  have hq : 0 < qP c χ ξ := by
    have : 0 < c ^ 2 * pP ξ := by positivity
    unfold qP; unfold pP at this; linarith
  have ha : 0 < aP c χ ξ := sqrt_pos.mpr (mul_pos hp hq)
  have ha2 : aP c χ ξ ^ 2 = pP ξ * qP c χ ξ := sq_sqrt (mul_pos hp hq).le
  have e : 1 / pP ξ - (c ^ 2 - χ) / (2 * c ^ 2 * pP ξ ^ 2)
      = (2 * (c ^ 2 * pP ξ) - (c ^ 2 - χ)) / (2 * c ^ 2 * pP ξ ^ 2) := by field_simp
  rw [e]
  have hq' : qP c χ ξ = c ^ 2 * pP ξ + (c ^ 2 - χ) := by unfold qP pP; ring
  rcases le_or_gt (2 * (c ^ 2 * pP ξ) - (c ^ 2 - χ)) 0 with hneg | hpos
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hneg (by positivity)) (by positivity)
  rw [div_le_div_iff₀ (by positivity) ha]
  -- `(2x − y)²(x + y) = 4x³ − y²(3x − y)` with `x = c²p`, `y = c² − χ`
  have hsq : ((2 * (c ^ 2 * pP ξ) - (c ^ 2 - χ)) * aP c χ ξ) ^ 2 ≤ (c * (2 * c ^ 2 * pP ξ ^ 2)) ^ 2 := by
    rw [mul_pow, ha2, hq']
    have hy0 : 0 ≤ c ^ 2 - χ := by linarith
    have h0 : 0 ≤ (c ^ 2 - χ) ^ 2 * (3 * (c ^ 2 * pP ξ) - (c ^ 2 - χ)) * pP ξ :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hp.le
    have e2 : (c * (2 * c ^ 2 * pP ξ ^ 2)) ^ 2
        - (2 * (c ^ 2 * pP ξ) - (c ^ 2 - χ)) ^ 2 * (pP ξ * (c ^ 2 * pP ξ + (c ^ 2 - χ)))
        = (c ^ 2 - χ) ^ 2 * (3 * (c ^ 2 * pP ξ) - (c ^ 2 - χ)) * pP ξ := by ring
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq

/-- `w c/a ≤ 2ξ/(cp²)` for `ξ > 1`, `χ < c²`. -/
theorem wP_mul_c_div_aP_le {c χ ξ : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hξ : 1 < ξ) :
    wP c χ ξ * (c / aP c χ ξ) ≤ 2 * ξ / (c * pP ξ ^ 2) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp := pP_pos hξ
  have ha := aP_pos hξ hc2 hχc
  have hq := qP_pos hξ hc2 hχc
  have ha2 := aP_sq hξ hc2 hχc
  have hpq : c ^ 2 * pP ξ ≤ qP c χ ξ := by unfold qP pP; nlinarith
  have hξ0 : 0 < ξ := by linarith
  have e : wP c χ ξ * (c / aP c χ ξ) = c * ξ * (qP c χ ξ + c ^ 2 * pP ξ) / (pP ξ * qP c χ ξ ^ 2) := by
    unfold wP
    have ed : dP c χ ξ = 2 * ξ * (qP c χ ξ + c ^ 2 * pP ξ) := by unfold dP qP pP; ring
    rw [ed]
    field_simp
    rw [ha2]; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : c * ξ * (qP c χ ξ + c ^ 2 * pP ξ) ≤ c * ξ * (2 * qP c χ ξ) := by
    have : 0 ≤ c * ξ := by positivity
    nlinarith
  have h2 : 2 * ξ * (c ^ 2 * pP ξ) ≤ 2 * ξ * qP c χ ξ := by nlinarith
  have hcq : 0 ≤ c * pP ξ * qP c χ ξ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ c * pP ξ ^ 2),
    mul_le_mul_of_nonneg_left h2 hcq]

/-! ### The L² sandwich and the far mass -/

section mass
variable {c χ Einf : ℝ} {ψ u : ℝ → ℝ}

/-- `E/(2a)` is continuous on `[ξ₀, X]`, `1 < ξ₀`, for a solution of the prolate system. -/
theorem continuousOn_energy_div {ξ₀ X : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (h1 : 1 < ξ₀)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t) :
    ContinuousOn (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)) (Icc ξ₀ X) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have gt1 : ∀ t ∈ Icc ξ₀ X, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
  have ha : ∀ t ∈ Icc ξ₀ X, 0 < aP c χ t := fun t ht => aP_pos (gt1 t ht) hc2 hχc
  have hac : ContinuousOn (aP c χ) (Icc ξ₀ X) := by
    have : Continuous (aP c χ) := by unfold aP pP qP; fun_prop
    exact this.continuousOn
  have hψc : ContinuousOn ψ (Icc ξ₀ X) := fun t ht => (hψ t (gt1 t ht)).continuousAt.continuousWithinAt
  have huc : ContinuousOn u (Icc ξ₀ X) := fun t ht => (hu t (gt1 t ht)).continuousAt.continuousWithinAt
  unfold energy
  exact ((hac.mul (hψc.pow 2)).add ((huc.pow 2).div₀ hac fun t ht => (ha t ht).ne')).div
    (continuousOn_const.mul hac) fun t ht => by have := ha t ht; positivity

/-- **The L² sandwich**: on `[ξ₀, X]`, `1 < ξ₀`, `χ < c²`, with `E ≤ Es` there,
`|∫ψ² − ∫E/(2a)| ≤ Es/(2q(ξ₀))` (Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy with `|ψu| ≤ E/2`). -/
theorem abs_integral_sq_sub_le {ξ₀ X Es : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (h1 : 1 < ξ₀) (hle : ξ₀ ≤ X)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hEs : ∀ t ∈ Icc ξ₀ X, energy (aP c χ) ψ u t ≤ Es) :
    |(∫ t in ξ₀..X, ψ t ^ 2) - ∫ t in ξ₀..X, energy (aP c χ) ψ u t / (2 * aP c χ t)|
      ≤ Es / (2 * qP c χ ξ₀) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have gt1 : ∀ t ∈ Icc ξ₀ X, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
  have hq : ∀ t ∈ Icc ξ₀ X, 0 < qP c χ t := fun t ht => qP_pos (gt1 t ht) hc2 hχc
  have ha : ∀ t ∈ Icc ξ₀ X, 0 < aP c χ t := fun t ht => aP_pos (gt1 t ht) hc2 hχc
  have hqd : ∀ t ∈ Icc ξ₀ X, HasDerivAt (qP c χ) (2 * c ^ 2 * t) t := fun t _ => by
    have h := ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).sub_const χ
    exact h.congr_deriv (by ring)
  have hac : ContinuousOn (aP c χ) (Icc ξ₀ X) := by
    have : Continuous (aP c χ) := by unfold aP pP qP; fun_prop
    exact this.continuousOn
  have hpc : ContinuousOn pP (Icc ξ₀ X) := by unfold pP; fun_prop
  have hqc : ContinuousOn (qP c χ) (Icc ξ₀ X) := by unfold qP; fun_prop
  have hψc : ContinuousOn ψ (Icc ξ₀ X) := fun t ht => (hψ t (gt1 t ht)).continuousAt.continuousWithinAt
  have huc : ContinuousOn u (Icc ξ₀ X) := fun t ht => (hu t (gt1 t ht)).continuousAt.continuousWithinAt
  have hid := Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy.integral_sq_eq (q' := fun t => 2 * c ^ 2 * t) hle ha
    (fun t ht => (pP_pos (gt1 t ht)).ne') (fun t ht => (hq t ht).ne')
    (fun t ht => aP_sq (gt1 t ht) hc2 hχc) (fun t ht => hψ t (gt1 t ht)) (fun t ht => hu t (gt1 t ht)) hqd
    (by fun_prop) hac hpc
  have hEc := continuousOn_energy_div (X := X) hc hχc h1 hψ hu
  have hGc : ContinuousOn (fun t => ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)) (Icc ξ₀ X) :=
    ((hψc.mul huc).mul (by fun_prop)).div₀ (continuousOn_const.mul (hqc.pow 2))
      fun t ht => by have := hq t ht; positivity
  have hQc : ContinuousOn (fun t => 2 * c ^ 2 * t / qP c χ t ^ 2) (Icc ξ₀ X) :=
    (continuousOn_const.mul continuousOn_id).div₀ (hqc.pow 2) fun t ht => by have := hq t ht; positivity
  rw [intervalIntegral.integral_sub (hEc.intervalIntegrable_of_Icc hle)
    (hGc.intervalIntegrable_of_Icc hle)] at hid
  have hcross : ‖∫ t in ξ₀..X, ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)‖
      ≤ ∫ t in ξ₀..X, Es / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hle (Eventually.of_forall fun t ht => ?_)
      ((hQc.intervalIntegrable_of_Icc hle).const_mul _)
    have ht' : t ∈ Icc ξ₀ X := Ioc_subset_Icc_self ht
    have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht')
    have hqt := hq t ht'
    have ht0 : 0 ≤ 2 * c ^ 2 * t := by have := gt1 t ht'; positivity
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg ht0,
      abs_of_pos (by positivity : 0 < 2 * qP c χ t ^ 2), div_le_iff₀ (by positivity)]
    have : |ψ t * u t| ≤ Es / 2 := by linarith [hEs t ht']
    have e : Es / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2) * (2 * qP c χ t ^ 2) = Es / 2 * (2 * c ^ 2 * t) := by
      field_simp; ring
    rw [e]; exact mul_le_mul_of_nonneg_right this ht0
  have hI : uIcc ξ₀ X = Icc ξ₀ X := uIcc_of_le hle
  have hqq : ∫ t in ξ₀..X, Es / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2)
      = Es / 4 * (1 / qP c χ ξ₀ - 1 / qP c χ X) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hd : ∀ t ∈ uIcc ξ₀ X, HasDerivAt (fun s => -(1 / qP c χ s)) (2 * c ^ 2 * t / qP c χ t ^ 2) t :=
      fun t ht => by
        have := ((hqd t (hI ▸ ht)).inv (hq t (hI ▸ ht)).ne').neg
        refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
        filter_upwards with s; simp [one_div]
    rw [integral_eq_sub_of_hasDerivAt hd (hQc.intervalIntegrable_of_Icc hle)]
    ring
  have hm0 : ξ₀ ∈ Icc ξ₀ X := left_mem_Icc.mpr hle
  have hmX : X ∈ Icc ξ₀ X := right_mem_Icc.mpr hle
  have hb : ∀ t ∈ Icc ξ₀ X, |ψ t * u t / qP c χ t / 2| ≤ Es / (4 * qP c χ t) := fun t ht => by
    have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht)
    have hqt := hq t ht
    rw [show ψ t * u t / qP c χ t / 2 = ψ t * u t / (2 * qP c χ t) by ring, abs_div,
      abs_of_pos (by positivity : 0 < 2 * qP c χ t), show Es / (4 * qP c χ t) = Es / 2 / (2 * qP c χ t) by ring]
    exact div_le_div_of_nonneg_right (by linarith [hEs t ht]) (by positivity)
  have hbX := abs_le.mp (hb X hmX)
  have hb0 := abs_le.mp (hb ξ₀ hm0)
  rw [Real.norm_eq_abs, hqq] at hcross
  have hcr := abs_le.mp hcross
  have hq0 := hq ξ₀ hm0
  have hqX := hq X hmX
  have hsum : Es / 4 * (1 / qP c χ ξ₀ - 1 / qP c χ X) + Es / (4 * qP c χ X) + Es / (4 * qP c χ ξ₀)
      = Es / (2 * qP c χ ξ₀) := by field_simp; ring
  rw [hid, abs_le]
  constructor <;> linarith

/-- The far constant `(ℓ(ξ) + 2/(cp(ξ)))/(1 − wUp(ξ)/2)²`. -/
noncomputable def farK (c ξ : ℝ) : ℝ := (ellF ξ + 2 / (c * pP ξ)) / (1 - wUp c ξ / 2) ^ 2

/-- **The energy beyond `ξ`**: `E(t) ≤ E∞/(1 − wUp(ξ)/2)²` for `t ≥ ξ > 1` when `wUp(ξ) < 2`. -/
theorem energy_le_of_ge {ξ t : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hξ : 1 < ξ) (hξt : ξ ≤ t)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hW : wUp c ξ < 2) :
    energy (aP c χ) ψ u t ≤ Einf / (1 - wUp c ξ / 2) ^ 2 := by
  have ht : 1 < t := lt_of_lt_of_le hξ hξt
  have hwt : wP c χ t ≤ wUp c ξ := (wP_le_wUp hc hχc ht).trans (wUp_le_wUp hc hξ hξt)
  have hw0 : 0 ≤ wP c χ t := (wP_pos ht (by positivity) hχc).le
  have hE0 := einf_nonneg hc hχc hE
  refine (energy_bracket hc hχ hχc ht hψ hu hE (by linarith)).2.trans ?_
  apply div_le_div_of_nonneg_left hE0 (by nlinarith)
  nlinarith

/-- **The energy from below**: `E∞(1 − w(t)) ≤ E(t)` for `t > 1` when `w(t) < 2`. -/
theorem energy_ge {t : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (ht : 1 < t)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hW : wP c χ t < 2) :
    Einf * (1 - wP c χ t) ≤ energy (aP c χ) ψ u t := by
  have hw0 : 0 ≤ wP c χ t := (wP_pos ht (by positivity) hχc).le
  have hE0 := einf_nonneg hc hχc hE
  refine le_trans ?_ (energy_bracket hc hχ hχc ht hψ hu hE hW).1
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg hE0 (mul_nonneg hw0 hw0)]

/-- **The far mass**: for `ξ > 1` with `wUp(ξ) < 2`, `ψ² ∈ L¹(ξ, ∞)` and `c∫_ξ^∞ ψ² ≤ (E∞/4)·farK(ξ)`. -/
theorem far_mass_le {ξ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hξ : 1 < ξ)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hW : wUp c ξ < 2) :
    IntegrableOn (fun t => ψ t ^ 2) (Ioi ξ) ∧ c * ∫ t in Ioi ξ, ψ t ^ 2 ≤ Einf / 4 * farK c ξ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hE0 := einf_nonneg hc hχc hE
  have hWp : 0 < 1 - wUp c ξ / 2 := by linarith
  set Es := Einf / (1 - wUp c ξ / 2) ^ 2 with hEsdef
  have hEs0 : 0 ≤ Es := by positivity
  have hp := pP_pos hξ
  have hb : ∀ X, ξ ≤ X → c * ∫ t in ξ..X, ψ t ^ 2 ≤ Einf / 4 * farK c ξ := by
    intro X hX
    have gt1 : ∀ t ∈ Icc ξ X, 1 < t := fun t ht => lt_of_lt_of_le hξ ht.1
    have hEs : ∀ t ∈ Icc ξ X, energy (aP c χ) ψ u t ≤ Es := fun t ht =>
      energy_le_of_ge hc hχ hχc hξ ht.1 hψ hu hE hW
    have hs := (abs_le.mp (abs_integral_sq_sub_le hc hχc hξ hX hψ hu hEs)).2
    have hpp : ContinuousOn pP (Icc ξ X) := by unfold pP; fun_prop
    have hpc : ContinuousOn (fun t => Es / (2 * c) * (1 / pP t)) (Icc ξ X) :=
      continuousOn_const.mul (continuousOn_const.div₀ hpp
        fun t ht => (pP_pos (gt1 t ht)).ne')
    have hmono := integral_mono_on hX
      ((continuousOn_energy_div hc hχc hξ hψ hu).intervalIntegrable_of_Icc (μ := volume) hX)
      (hpc.intervalIntegrable_of_Icc (μ := volume) hX) (fun t ht => by
        have ha := aP_pos (gt1 t ht) hc2 hχc
        have hpt := pP_pos (gt1 t ht)
        have hcp := mul_pP_le_aP hc hχc.le (gt1 t ht)
        have hE0t := energy_nonneg (ψ := ψ) (u := u) ha
        calc energy (aP c χ) ψ u t / (2 * aP c χ t) ≤ Es / (2 * aP c χ t) :=
              div_le_div_of_nonneg_right (hEs t ht) (by positivity)
          _ ≤ Es / (2 * (c * pP t)) := div_le_div_of_nonneg_left hEs0 (by positivity) (by linarith)
          _ = Es / (2 * c) * (1 / pP t) := by field_simp)
    rw [intervalIntegral.integral_const_mul, integral_inv_pP hξ hX] at hmono
    have hellX := (ellF_pos (lt_of_lt_of_le hξ hX)).le
    have hq : c ^ 2 * pP ξ ≤ qP c χ ξ := by unfold qP pP; nlinarith
    have hqE : Es / (2 * qP c χ ξ) ≤ Es / (2 * (c ^ 2 * pP ξ)) :=
      div_le_div_of_nonneg_left hEs0 (by positivity) (by linarith)
    have key : ∫ t in ξ..X, ψ t ^ 2 ≤ Es / (2 * c) * ((ellF ξ - ellF X) / 2) + Es / (2 * (c ^ 2 * pP ξ)) := by
      linarith
    have e : Einf / 4 * farK c ξ = c * (Es / (2 * c) * (ellF ξ / 2) + Es / (2 * (c ^ 2 * pP ξ))) := by
      simp only [hEsdef, farK]; field_simp; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hc.le
    have : Es / (2 * c) * ((ellF ξ - ellF X) / 2) ≤ Es / (2 * c) * (ellF ξ / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hψc : ContinuousOn ψ (Ici ξ) := fun t ht =>
    (hψ t (lt_of_lt_of_le hξ ht)).continuousAt.continuousWithinAt
  have hInt : IntegrableOn (fun t => ψ t ^ 2) (Ioi ξ) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (l := atTop) (b := id)
      (Einf / 4 * farK c ξ / c) ξ
      (fun i => ((hψc.mono Icc_subset_Ici_self).pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      tendsto_id ?_
    filter_upwards [eventually_ge_atTop ξ] with X hX
    have e : ∫ x in ξ..id X, ‖ψ x ^ 2‖ = ∫ x in ξ..X, ψ x ^ 2 := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [norm_pow, Real.norm_eq_abs, sq_abs]
    rw [e, le_div_iff₀ hc, mul_comm]
    exact hb X hX
  refine ⟨hInt, ?_⟩
  have hlim := (intervalIntegral_tendsto_integral_Ioi ξ hInt tendsto_id).const_mul c
  exact le_of_tendsto hlim (by filter_upwards [eventually_ge_atTop ξ] with X hX using hb X hX)

/-- The log loss `κ(ξ₀) = (2(1 + (1 − wUp(ξ₀)/2)⁻²) + (c² − χ)/(2c))/(cp(ξ₀))` of the mass law. -/
noncomputable def kapLoss (c χ ξ₀ : ℝ) : ℝ :=
  (2 * (1 + 1 / (1 - wUp c ξ₀ / 2) ^ 2) + (c ^ 2 - χ) / (2 * c)) / (c * pP ξ₀)

private theorem tendsto_const_sub_mul_ellF (A B : ℝ) :
    Tendsto (fun X => A - B * ellF X) atTop (𝓝 A) := by
  simpa using tendsto_const_nhds.sub (tendsto_ellF.const_mul B)

private theorem mass_law_alg (E c χ p w L0 LX : ℝ) (hc : c ≠ 0) (hp : p ≠ 0) :
    E / 4 * (L0 - (2 * (1 + 1 / (1 - w / 2) ^ 2) + (c ^ 2 - χ) / (2 * c)) / (c * p)) - E / 4 * LX
      = c * (E / (2 * c) * ((L0 - LX) / 2 - ((c ^ 2 - χ) / (2 * c ^ 2) + 2 / c) * (1 / (2 * p)))
        - E / (1 - w / 2) ^ 2 / (2 * (c ^ 2 * p))) := by
  field_simp; ring

/-- **The `λ`-free mass law from `ξ₀`**: for `ξ₀ > 1` with `wUp(ξ₀) < 2`, `0 ≤ χ < c²`,
`(E∞/4)(ℓ(ξ₀) − κ(ξ₀)) ≤ c∫_{ξ₀}^∞ ψ²`. -/
theorem mass_law_from {ξ₀ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (h1 : 1 < ξ₀)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hW : wUp c ξ₀ < 2) :
    Einf / 4 * (ellF ξ₀ - kapLoss c χ ξ₀) ≤ c * ∫ t in Ioi ξ₀, ψ t ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  obtain ⟨hInt, -⟩ := far_mass_le hc hχ hχc h1 hψ hu hE hW
  have hE0 := einf_nonneg hc hχc hE
  have hWp : 0 < 1 - wUp c ξ₀ / 2 := by linarith
  set Es := Einf / (1 - wUp c ξ₀ / 2) ^ 2 with hEsdef
  have hEs0 : 0 ≤ Es := by positivity
  set K := (c ^ 2 - χ) / (2 * c ^ 2) + 2 / c with hKdef
  have hK0 : 0 ≤ K := by
    have : 0 ≤ c ^ 2 - χ := by linarith
    positivity
  have hp0 := pP_pos h1
  have hb : ∀ X, ξ₀ ≤ X →
      Einf / 4 * (ellF ξ₀ - kapLoss c χ ξ₀) - Einf / 4 * ellF X ≤ c * ∫ t in ξ₀..X, ψ t ^ 2 := by
    intro X hX
    have gt1 : ∀ t ∈ Icc ξ₀ X, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
    have hEs : ∀ t ∈ Icc ξ₀ X, energy (aP c χ) ψ u t ≤ Es := fun t ht =>
      energy_le_of_ge hc hχ hχc h1 ht.1 hψ hu hE hW
    have hs := (abs_le.mp (abs_integral_sq_sub_le hc hχc h1 hX hψ hu hEs)).1
    have hlc : ContinuousOn (fun t => Einf / (2 * c) * (1 / pP t - K * (t / pP t ^ 2))) (Icc ξ₀ X) := by
      have hpc : ContinuousOn pP (Icc ξ₀ X) := by unfold pP; fun_prop
      refine continuousOn_const.mul ((continuousOn_const.div₀ hpc fun t ht => (pP_pos (gt1 t ht)).ne').sub
        (continuousOn_const.mul (continuousOn_id.div₀ (hpc.pow 2) fun t ht => ?_)))
      exact pow_ne_zero 2 (pP_pos (gt1 t ht)).ne'
    have hmono := integral_mono_on hX (hlc.intervalIntegrable_of_Icc (μ := volume) hX)
      ((continuousOn_energy_div hc hχc h1 hψ hu).intervalIntegrable_of_Icc (μ := volume) hX)
      (fun t ht => by
        have ht1 := gt1 t ht
        have ha := aP_pos ht1 hc2 hχc
        have hpt := pP_pos ht1
        have hwt : wP c χ t < 2 :=
          lt_of_le_of_lt ((wP_le_wUp hc hχc ht1).trans (wUp_le_wUp hc h1 ht.1)) hW
        have hlow := energy_ge hc hχ hχc ht1 hψ hu hE hwt
        have hA := c_div_aP_ge hc hχc.le ht1
        have hwA := wP_mul_c_div_aP_le hc hχc ht1
        have hApos : 0 < c / aP c χ t := by positivity
        -- `E/(2a) = E·(c/a)/(2c) ≥ E∞(c/a − w c/a)/(2c)`
        have e : energy (aP c χ) ψ u t / (2 * aP c χ t) = energy (aP c χ) ψ u t * (c / aP c χ t) / (2 * c) := by
          field_simp
        rw [e]
        have h1' : Einf * (c / aP c χ t - wP c χ t * (c / aP c χ t))
            ≤ energy (aP c χ) ψ u t * (c / aP c χ t) := by
          have := mul_le_mul_of_nonneg_right hlow hApos.le
          linarith
        have h2' : 1 / pP t - K * (t / pP t ^ 2)
            ≤ c / aP c χ t - wP c χ t * (c / aP c χ t) := by
          have hσ : (c ^ 2 - χ) / (2 * c ^ 2 * pP t ^ 2) ≤ (c ^ 2 - χ) / (2 * c ^ 2) * (t / pP t ^ 2) := by
            rw [div_mul_div_comm]
            apply div_le_div_of_nonneg_right _ (by positivity)
            have : 0 ≤ c ^ 2 - χ := by linarith
            nlinarith
          have e2 : 2 * t / (c * pP t ^ 2) = 2 / c * (t / pP t ^ 2) := by field_simp
          simp only [hKdef]
          nlinarith
        have h3' : Einf * (1 / pP t - K * (t / pP t ^ 2))
            ≤ Einf * (c / aP c χ t - wP c χ t * (c / aP c χ t)) := mul_le_mul_of_nonneg_left h2' hE0
        rw [show Einf / (2 * c) * (1 / pP t - K * (t / pP t ^ 2))
          = Einf * (1 / pP t - K * (t / pP t ^ 2)) / (2 * c) by ring]
        exact div_le_div_of_nonneg_right (h3'.trans h1') (by positivity))
    have hpX := pP_pos (lt_of_lt_of_le h1 hX)
    have hint : ∫ t in ξ₀..X, Einf / (2 * c) * (1 / pP t - K * (t / pP t ^ 2))
        = Einf / (2 * c) * ((ellF ξ₀ - ellF X) / 2 - K * (1 / (2 * pP ξ₀) - 1 / (2 * pP X))) := by
      have gt1' : ∀ t ∈ uIcc ξ₀ X, 1 < t := fun t ht => gt1 t (uIcc_of_le hX ▸ ht)
      have i1 : IntervalIntegrable (fun t => 1 / pP t) volume ξ₀ X :=
        (continuousOn_const.div₀ (by unfold pP; fun_prop) fun t ht => (pP_pos (gt1' t ht)).ne').intervalIntegrable
      have i2 : IntervalIntegrable (fun t => t / pP t ^ 2) volume ξ₀ X :=
        (continuousOn_id.div₀ (by unfold pP; fun_prop) fun t ht => by
          have := pP_pos (gt1' t ht); positivity).intervalIntegrable
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub i1 (i2.const_mul K),
        intervalIntegral.integral_const_mul, integral_inv_pP h1 hX, integral_xi_div_pP_sq h1 hX]
    rw [hint] at hmono
    have hq : c ^ 2 * pP ξ₀ ≤ qP c χ ξ₀ := by unfold qP pP; nlinarith
    have hqE : Es / (2 * qP c χ ξ₀) ≤ Es / (2 * (c ^ 2 * pP ξ₀)) :=
      div_le_div_of_nonneg_left hEs0 (by positivity) (by linarith)
    have hKX : 0 ≤ Einf / (2 * c) * (K * (1 / (2 * pP X))) := by positivity
    have key : Einf / (2 * c) * ((ellF ξ₀ - ellF X) / 2 - K * (1 / (2 * pP ξ₀)))
        - Es / (2 * (c ^ 2 * pP ξ₀)) ≤ ∫ t in ξ₀..X, ψ t ^ 2 := by
      have e3 : Einf / (2 * c) * ((ellF ξ₀ - ellF X) / 2 - K * (1 / (2 * pP ξ₀) - 1 / (2 * pP X)))
          = Einf / (2 * c) * ((ellF ξ₀ - ellF X) / 2 - K * (1 / (2 * pP ξ₀)))
            + Einf / (2 * c) * (K * (1 / (2 * pP X))) := by ring
      linarith only [hmono, hs, hqE, hKX, e3]
    have e : Einf / 4 * (ellF ξ₀ - kapLoss c χ ξ₀) - Einf / 4 * ellF X
        = c * (Einf / (2 * c) * ((ellF ξ₀ - ellF X) / 2 - K * (1 / (2 * pP ξ₀)))
          - Es / (2 * (c ^ 2 * pP ξ₀))) := by
      rw [hEsdef, hKdef, kapLoss]
      exact mass_law_alg Einf c χ (pP ξ₀) (wUp c ξ₀) (ellF ξ₀) (ellF X) hc.ne' hp0.ne'
    rw [e]
    exact mul_le_mul_of_nonneg_left key hc.le
  have hlim : Tendsto (fun X => Einf / 4 * (ellF ξ₀ - kapLoss c χ ξ₀) - Einf / 4 * ellF X) atTop
      (𝓝 (Einf / 4 * (ellF ξ₀ - kapLoss c χ ξ₀))) := by
    exact tendsto_const_sub_mul_ellF _ _
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop ξ₀] with X hX
  refine (hb X hX).trans (mul_le_mul_of_nonneg_left ?_ hc.le)
  rw [intervalIntegral.integral_of_le hX]
  exact setIntegral_mono_set hInt (ae_of_all _ fun t => sq_nonneg _) Ioc_subset_Ioi_self.eventuallySubset

/-- **The far fraction from `ξ₀`**: for `1 < ξ₀ ≤ ξ` with `wUp(ξ₀) < 2`,
`(∫_ξ^∞ ψ²)(ℓ(ξ₀) − κ(ξ₀)) ≤ farK(ξ)·∫_{ξ₀}^∞ ψ²`; `E∞` cancels. -/
theorem far_fraction_from {ξ₀ ξ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (h1 : 1 < ξ₀)
    (hle : ξ₀ ≤ ξ)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hW : wUp c ξ₀ < 2) :
    (∫ t in Ioi ξ, ψ t ^ 2) * (ellF ξ₀ - kapLoss c χ ξ₀) ≤ farK c ξ * ∫ t in Ioi ξ₀, ψ t ^ 2 := by
  have hξ : 1 < ξ := lt_of_lt_of_le h1 hle
  have hWξ : wUp c ξ < 2 := lt_of_le_of_lt (wUp_le_wUp hc h1 hle) hW
  obtain ⟨-, hA⟩ := far_mass_le hc hχ hχc hξ hψ hu hE hWξ
  have hB := mass_law_from hc hχ hχc h1 hψ hu hE hW
  have hE0 := einf_nonneg hc hχc hE
  have hF0 : 0 ≤ farK c ξ := by
    have := ellF_pos hξ; have := pP_pos hξ; unfold farK; positivity
  have hA0 : 0 ≤ ∫ t in Ioi ξ, ψ t ^ 2 := setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  have hB0 : 0 ≤ ∫ t in Ioi ξ₀, ψ t ^ 2 := setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  set D := ellF ξ₀ - kapLoss c χ ξ₀
  rcases le_or_gt D 0 with hD | hD
  · nlinarith [mul_nonneg hF0 hB0]
  · -- `c A D ≤ (E∞/4) F D ≤ F (c B)`
    have h1' := mul_le_mul_of_nonneg_right hA hD.le
    have h2' := mul_le_mul_of_nonneg_left hB hF0
    have : c * ((∫ t in Ioi ξ, ψ t ^ 2) * D) ≤ c * (farK c ξ * ∫ t in Ioi ξ₀, ψ t ^ 2) := by
      nlinarith
    exact le_of_mul_le_mul_left this hc

end mass

/-! ### The edge point `ξ₀ = 1 + r₀/c` -/

/-- `wUp` at `1 + r₀/c`: `w̄(r₀) = 2(1 + r₀/c)/(r₀(2 + r₀/c))`. -/
noncomputable def wBar (c r₀ : ℝ) : ℝ := 2 * (1 + r₀ / c) / (r₀ * (2 + r₀ / c))

/-- The additive log loss `2k(r₀, s) = (2(1 + (1 − w̄/2)⁻²) + s/2)/(r₀(2 + r₀/c))`. -/
noncomputable def twoK (c r₀ s : ℝ) : ℝ :=
  (2 * (1 + 1 / (1 - wBar c r₀ / 2) ^ 2) + s / 2) / (r₀ * (2 + r₀ / c))

/-- The relative error `δ_c(ξ) = (1 + 2/(cp(ξ)ℓ(ξ)))/(1 − wUp(ξ)/2)² − 1` of the far fraction. -/
noncomputable def deltaC (c ξ : ℝ) : ℝ := (1 + 2 / (c * pP ξ * ellF ξ)) / (1 - wUp c ξ / 2) ^ 2 - 1

section edge
variable {c r₀ : ℝ}

/-- `c·p(1 + r₀/c) = r₀(2 + r₀/c)`. -/
theorem c_mul_pP_edge (hc : 0 < c) : c * pP (1 + r₀ / c) = r₀ * (2 + r₀ / c) := by
  unfold pP; field_simp; ring

/-- `ℓ(1 + r₀/c) = log(1 + 2c/r₀)`. -/
theorem ellF_edge (hc : 0 < c) (hr : 0 < r₀) : ellF (1 + r₀ / c) = log (1 + 2 * c / r₀) := by
  have := hr.ne'
  have := hc.ne'
  unfold ellF; congr 1
  rw [show 1 + r₀ / c - 1 = r₀ / c by ring, show 1 + r₀ / c + 1 = (2 * c + r₀) / c by field_simp; ring,
    div_div_div_cancel_right₀ this]
  field_simp
  ring

/-- `wUp(1 + r₀/c) = w̄(r₀)`. -/
theorem wUp_edge (hc : 0 < c) : wUp c (1 + r₀ / c) = wBar c r₀ := by
  unfold wUp; rw [c_mul_pP_edge hc]; rfl

/-- `κ(1 + r₀/c) = 2k(r₀, (c² − χ)/c)`. -/
theorem kapLoss_edge {χ : ℝ} (hc : 0 < c) : kapLoss c χ (1 + r₀ / c) = twoK c r₀ ((c ^ 2 - χ) / c) := by
  unfold kapLoss twoK; rw [wUp_edge hc, c_mul_pP_edge hc]; congr 1; field_simp

/-- `w̄(r₀) < 2` for `r₀ ≥ 1`. -/
theorem wBar_lt_two (hc : 0 < c) (hr : 1 ≤ r₀) : wBar c r₀ < 2 := by
  unfold wBar
  have h : 0 < r₀ / c := by positivity
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- `2k(r₀, s) ≤ (1 + (1 − w̄/2)⁻²)/r₀ + s/(4r₀)` for `r₀ > 0`, `s ≥ 0`. -/
theorem twoK_le {s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 ≤ s) :
    twoK c r₀ s ≤ (1 + 1 / (1 - wBar c r₀ / 2) ^ 2) / r₀ + s / (4 * r₀) := by
  unfold twoK
  have hN : 0 ≤ 2 * (1 + 1 / (1 - wBar c r₀ / 2) ^ 2) + s / 2 := by positivity
  have e : (1 + 1 / (1 - wBar c r₀ / 2) ^ 2) / r₀ + s / (4 * r₀)
      = (2 * (1 + 1 / (1 - wBar c r₀ / 2) ^ 2) + s / 2) / (2 * r₀) := by field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_left hN (by positivity)
  have : 0 < r₀ / c := by positivity
  nlinarith

/-- `2k(r₀, s)` is monotone in `s`. -/
theorem twoK_mono {s s' : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : s ≤ s') : twoK c r₀ s ≤ twoK c r₀ s' := by
  unfold twoK
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- `farK(ξ) = ℓ(ξ)(1 + δ_c(ξ))` for `ξ > 1`. -/
theorem farK_eq {ξ : ℝ} (hc : 0 < c) (hξ : 1 < ξ) : farK c ξ = ellF ξ * (1 + deltaC c ξ) := by
  have := ellF_pos hξ
  have := pP_pos hξ
  unfold farK deltaC
  field_simp
  ring

end edge

/-! ### The band mass law -/

section band
variable {c χ Einf r₀ : ℝ} {ψ u : ℝ → ℝ}

/-- **The band mass law**: for `0 ≤ χ < c²`, `s = (c² − χ)/c`, `r₀ > 0` with `w̄(r₀) < 2`,
`(E∞/4)(log(1 + 2c/r₀) − 2k(r₀, s)) ≤ c∫₁^∞ ψ²`. -/
theorem band_mass_law (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hr : 0 < r₀) (hW : wBar c r₀ < 2)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hInt : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1)) :
    Einf / 4 * (log (1 + 2 * c / r₀) - twoK c r₀ ((c ^ 2 - χ) / c)) ≤ c * ∫ t in Ioi 1, ψ t ^ 2 := by
  have h1 : 1 < 1 + r₀ / c := by have : 0 < r₀ / c := by positivity
                                 linarith
  have hm := mass_law_from hc hχ hχc h1 hψ hu hE (by rwa [wUp_edge hc])
  rw [ellF_edge hc hr, kapLoss_edge hc] at hm
  refine hm.trans (mul_le_mul_of_nonneg_left ?_ hc.le)
  exact setIntegral_mono_set hInt (ae_of_all _ fun t => sq_nonneg _) (Ioi_subset_Ioi h1.le).eventuallySubset

/-- **The band far fraction**: under `band_mass_law`'s hypotheses, for `ξ ≥ 1 + r₀/c`,
`(∫_ξ^∞ ψ²)(log(1 + 2c/r₀) − 2k(r₀, s)) ≤ ℓ(ξ)(1 + δ_c(ξ))·∫₁^∞ ψ²`. -/
theorem band_far_fraction {ξ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hr : 0 < r₀)
    (hW : wBar c r₀ < 2) (hξ : 1 + r₀ / c ≤ ξ)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hInt : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1)) :
    (∫ t in Ioi ξ, ψ t ^ 2) * (log (1 + 2 * c / r₀) - twoK c r₀ ((c ^ 2 - χ) / c))
      ≤ ellF ξ * (1 + deltaC c ξ) * ∫ t in Ioi 1, ψ t ^ 2 := by
  have h1 : 1 < 1 + r₀ / c := by have : 0 < r₀ / c := by positivity
                                 linarith
  have hξ1 : 1 < ξ := lt_of_lt_of_le h1 hξ
  have hf := far_fraction_from hc hχ hχc h1 hξ hψ hu hE (by rwa [wUp_edge hc])
  rw [ellF_edge hc hr, kapLoss_edge hc, farK_eq hc hξ1] at hf
  refine hf.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · exact setIntegral_mono_set hInt (ae_of_all _ fun t => sq_nonneg _) (Ioi_subset_Ioi h1.le).eventuallySubset
  · rw [← farK_eq hc hξ1]
    have := ellF_pos hξ1; have := pP_pos hξ1; unfold farK; positivity

/-- **The band mass law, uniform on the band**: for `0 < c² − χ ≤ 5c`,
`(E∞/4)(log(1 + 2c/r₀) − 2k(r₀, 5)) ≤ c∫₁^∞ ψ²`. -/
theorem band_mass_law_five (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hband : c ^ 2 - χ ≤ 5 * c)
    (hr : 0 < r₀) (hW : wBar c r₀ < 2)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hInt : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1)) :
    Einf / 4 * (log (1 + 2 * c / r₀) - twoK c r₀ 5) ≤ c * ∫ t in Ioi 1, ψ t ^ 2 := by
  have hs : (c ^ 2 - χ) / c ≤ 5 := by rw [div_le_iff₀ hc]; linarith
  refine le_trans ?_ (band_mass_law hc hχ hχc hr hW hψ hu hE hInt)
  have := einf_nonneg hc hχc hE
  exact mul_le_mul_of_nonneg_left (by linarith [twoK_mono hc hr hs]) (by positivity)

/-- **The band far fraction, uniform on the band**: for `0 < c² − χ ≤ 5c` and `ξ ≥ 1 + r₀/c`,
`(∫_ξ^∞ ψ²)(log(1 + 2c/r₀) − 2k(r₀, 5)) ≤ ℓ(ξ)(1 + δ_c(ξ))·∫₁^∞ ψ²`. -/
theorem band_far_fraction_five {ξ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hband : c ^ 2 - χ ≤ 5 * c)
    (hr : 0 < r₀) (hW : wBar c r₀ < 2) (hξ : 1 + r₀ / c ≤ ξ)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hInt : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1)) :
    (∫ t in Ioi ξ, ψ t ^ 2) * (log (1 + 2 * c / r₀) - twoK c r₀ 5)
      ≤ ellF ξ * (1 + deltaC c ξ) * ∫ t in Ioi 1, ψ t ^ 2 := by
  have hs : (c ^ 2 - χ) / c ≤ 5 := by rw [div_le_iff₀ hc]; linarith
  refine le_trans ?_ (band_far_fraction hc hχ hχc hr hW hξ hψ hu hE hInt)
  have hA0 : 0 ≤ ∫ t in Ioi ξ, ψ t ^ 2 := setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  exact mul_le_mul_of_nonneg_left (by linarith [twoK_mono hc hr hs]) hA0

/-- `ψ² ∈ L¹(1, ∞)` for a solution continuous on `[1, ∞)` with `E → E∞`, `0 ≤ χ < c²`. -/
theorem integrableOn_Ioi_one {ξ₀ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (h1 : 1 < ξ₀)
    (hW : wUp c ξ₀ < 2)
    (hψ : ∀ t, 1 < t → HasDerivAt ψ (u t / pP t) t) (hu : ∀ t, 1 < t → HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hE : Tendsto (energy (aP c χ) ψ u) atTop (𝓝 Einf)) (hψc : ContinuousOn ψ (Ici 1)) :
    IntegrableOn (fun t => ψ t ^ 2) (Ioi 1) := by
  rw [← Ioc_union_Ioi_eq_Ioi h1.le]
  exact (((hψc.mono Icc_subset_Ici_self).pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self).union
    (far_mass_le hc hχ hχc h1 hψ hu hE hW).1

end band

/-! ### Rungs -/

section rung
open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity
open scoped Interval
variable {g g₁ g₂ : ℝ → ℝ} {c χ r₀ : ℝ}

/-- **The layer sup of a rung**: `|ψ(1 + r/c) − ψ(1)| ≤ |ψ(1)|(sr/2 + r²/4)`, `s = (c² − χ)/c`, for `r ≥ 0`
(`EdgeBesselCount`'s Sonin bound in edge units). -/
theorem rung_layer_le {r : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχc : χ < c ^ 2) (hr : 0 ≤ r) :
    |psi c g (1 + r / c) - psi c g 1| ≤ |psi c g 1| * ((c ^ 2 - χ) / c * r / 2 + r ^ 2 / 4) := by
  have h0 : 0 ≤ r / c := by positivity
  have h := Cvs.Prolate.EdgeBesselCount.abs_psi_sub_psi_one_le hg hg₁ hg₂c hang hχc (ξ := 1 + r / c) (by linarith)
  have e : (c ^ 2 - χ) * (1 + r / c - 1) / 2 + c ^ 2 * (1 + r / c - 1) ^ 2 / 4
      = (c ^ 2 - χ) / c * r / 2 + r ^ 2 / 4 := by field_simp; ring
  rwa [e] at h

/-- **The band mass law for a rung**: for `0 ≤ χ < c²`, `s = (c² − χ)/c`, `r₀ > 0` with `w̄(r₀) < 2`,
`ψ² ∈ L¹(1, ∞)` and `(A²/(4c))(log(1 + 2c/r₀) − 2k(r₀, s)) ≤ c∫₁^∞ ψ²`, `A = g(1) + g(−1)`. -/
theorem rung_band_mass_law
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hr : 0 < r₀) (hW : wBar c r₀ < 2) :
    IntegrableOn (fun t => psi c g t ^ 2) (Ioi 1) ∧
      ampl g ^ 2 / c / 4 * (log (1 + 2 * c / r₀) - twoK c r₀ ((c ^ 2 - χ) / c))
        ≤ c * ∫ t in Ioi 1, psi c g t ^ 2 := by
  obtain ⟨hψ, hu, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hE := Cvs.Prolate.RungConnectionIdentity.tendsto_energy hg hg₁ hg₂c hc hχ hχc
  have h1 : 1 < 1 + r₀ / c := by have : 0 < r₀ / c := by positivity
                                 linarith
  have hInt := integrableOn_Ioi_one hc hχ hχc h1 (by rwa [wUp_edge hc]) hψ (fun t _ => hu t) hE
    hψc.continuousOn
  exact ⟨hInt, band_mass_law hc hχ hχc hr hW hψ (fun t _ => hu t) hE hInt⟩

/-- **The band far fraction for a rung**: under `rung_band_mass_law`'s hypotheses, for `ξ ≥ 1 + r₀/c`,
`(∫_ξ^∞ ψ²)(log(1 + 2c/r₀) − 2k(r₀, s)) ≤ ℓ(ξ)(1 + δ_c(ξ))·∫₁^∞ ψ²`. -/
theorem rung_band_far_fraction {ξ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hr : 0 < r₀) (hW : wBar c r₀ < 2) (hξ : 1 + r₀ / c ≤ ξ) :
    (∫ t in Ioi ξ, psi c g t ^ 2) * (log (1 + 2 * c / r₀) - twoK c r₀ ((c ^ 2 - χ) / c))
      ≤ ellF ξ * (1 + deltaC c ξ) * ∫ t in Ioi 1, psi c g t ^ 2 := by
  obtain ⟨hψ, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
  have hE := Cvs.Prolate.RungConnectionIdentity.tendsto_energy hg hg₁ hg₂c hc hχ hχc
  exact band_far_fraction hc hχ hχc hr hW hξ hψ (fun t _ => hu t) hE
    (rung_band_mass_law hg hg₁ hg₂c hang hc hχ hχc hr hW).1

end rung

end Cvs.Prolate.BandMassLaw
