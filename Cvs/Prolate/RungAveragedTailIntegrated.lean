import Mathlib
import Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungAveragedTail
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The averaged tail of a rung, integrated

With `ψ² = E/(2a) + (E/(2q))(XY)′ − (E/(2q))(ε/(1 + ε))(XY)′` (Cvs.Prolate.RungAveragedTail) on `[b, t]`, `E ≤ G`, `w ≤ W < 2`:
the first and third terms are at most `(G/(2cp))(1 + κ_W)` pointwise, `κ_W = (W/2)(1 + W/2)/(1 − W/2)`, and the
second integrates by parts against `|XY| ≤ ½`, with boundary and derivative terms at most `G/(c²(b² − 1))` in all. So
`∫_b^t ψ² ≤ (G/(4c))log((b+1)/(b−1))(1 + κ_W) + G/(c²(b² − 1))`: `RungGramFloorAtInfinity`'s tail bound halved.
-/

namespace Cvs.Prolate.RungAveragedTailIntegrated

open Real Set intervalIntegral MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.RungAveragedTail

/-- `qP ≥ c²·pP` for `χ ≤ c²`. -/
theorem qP_ge {c χ ξ : ℝ} (hχc : χ ≤ c ^ 2) : c ^ 2 * pP ξ ≤ qP c χ ξ := by
  unfold pP qP; nlinarith

theorem hasDerivAt_qP (c χ ξ : ℝ) : HasDerivAt (qP c χ) (2 * c ^ 2 * ξ) ξ := by
  have := ((hasDerivAt_pow 2 ξ).const_mul (c ^ 2)).sub_const χ
  unfold qP
  refine this.congr_deriv ?_; simp; ring

/-- `wP` is antitone beyond the edge. -/
theorem wP_le_of_le {c χ b ξ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hb : 1 < b) (hbξ : b ≤ ξ) :
    wP c χ ξ ≤ wP c χ b := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hpb0' : 0 < b ^ 2 - 1 := by nlinarith
  have hanti : AntitoneOn (wP c χ) (Icc b ξ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc b ξ)
    · exact fun x hx => (hasDerivAt_wP (lt_of_lt_of_le hb hx.1) hc2 hχc).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_wP (lt_of_lt_of_le hb (interior_subset hx).1) hc2 hχc).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hasDerivAt_wP (lt_of_lt_of_le hb hx'.1) hc2 hχc).deriv]
      exact wP'_nonpos (lt_of_lt_of_le hb hx'.1) hc2 hχ0 hχc
  exact hanti ⟨le_rfl, hbξ⟩ ⟨hbξ, le_rfl⟩ hbξ

/-- **The bound on `(E/(2q))′`**: with `|E′| ≤ wqE/a`, `q′ = 2c²ξ`, `E ≤ G`, `w ≤ 2ξ/(cp)`, `a ≥ cp`, `q ≥ c²p`:
`|(E′q − Eq′)/(2q²)| ≤ 2Gξ/(c²p²)`. -/
theorem abs_fderiv_le {E E' G a p q w c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (hE0 : 0 ≤ E) (hEG : E ≤ G) (hE' : |E'| ≤ w * q * E / a) (hw0 : 0 ≤ w) (hw : w ≤ 2 * ξ / (c * p))
    (hacp : c * p ≤ a) (hqcp : c ^ 2 * p ≤ q) :
    |(E' * q - E * (2 * c ^ 2 * ξ)) / (2 * q ^ 2)| ≤ 2 * G * ξ / (c ^ 2 * p ^ 2) := by
  have hG0 : 0 ≤ G := le_trans hE0 hEG
  have h1 : |E' * q| / (2 * q ^ 2) ≤ G * ξ / (c ^ 2 * p ^ 2) := by
    rw [abs_mul, abs_of_pos hq]
    have : |E'| * q / (2 * q ^ 2) = |E'| / (2 * q) := by field_simp
    rw [this]
    calc |E'| / (2 * q) ≤ w * q * E / a / (2 * q) := by gcongr
      _ = w * E / (2 * a) := by field_simp
      _ ≤ 2 * ξ / (c * p) * G / (2 * (c * p)) := by
          gcongr
      _ = G * ξ / (c ^ 2 * p ^ 2) := by field_simp
  have h2 : |E * (2 * c ^ 2 * ξ)| / (2 * q ^ 2) ≤ G * ξ / (c ^ 2 * p ^ 2) := by
    rw [abs_mul, abs_of_nonneg hE0, abs_of_pos (by positivity)]
    have : E * (2 * c ^ 2 * ξ) / (2 * q ^ 2) = E * c ^ 2 * ξ / q ^ 2 := by field_simp
    rw [this]
    calc E * c ^ 2 * ξ / q ^ 2 ≤ G * c ^ 2 * ξ / (c ^ 2 * p) ^ 2 := by gcongr
      _ = G * ξ / (c ^ 2 * p ^ 2) := by field_simp
  calc |(E' * q - E * (2 * c ^ 2 * ξ)) / (2 * q ^ 2)|
      ≤ (|E' * q| + |E * (2 * c ^ 2 * ξ)|) / (2 * q ^ 2) := by
        rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 * q ^ 2 by positivity)]
        exact div_le_div_of_nonneg_right (abs_sub _ _) (by positivity)
    _ = |E' * q| / (2 * q ^ 2) + |E * (2 * c ^ 2 * ξ)| / (2 * q ^ 2) := by ring
    _ ≤ G * ξ / (c ^ 2 * p ^ 2) + G * ξ / (c ^ 2 * p ^ 2) := add_le_add h1 h2
    _ = 2 * G * ξ / (c ^ 2 * p ^ 2) := by ring

/-- The antiderivative of `ξ/(ξ² − 1)²`. -/
theorem hasDerivAt_neg_inv_two {ξ : ℝ} (hξ : 1 < ξ) :
    HasDerivAt (fun x : ℝ => -1 / (2 * (x ^ 2 - 1))) (ξ / (ξ ^ 2 - 1) ^ 2) ξ := by
  have hne : 2 * (ξ ^ 2 - 1) ≠ 0 := by
    have : ξ ^ 2 - 1 ≠ 0 := by nlinarith
    exact mul_ne_zero two_ne_zero this
  have h := ((hasDerivAt_pow 2 ξ).sub_const 1).const_mul 2
  have h2 := (hasDerivAt_const ξ (-1 : ℝ)).div h hne
  refine h2.congr_deriv ?_
  field_simp
  ring

/-- The `ε`-factor is monotone in `w` on `[0, 2)`. -/
theorem kappa_mono {w W : ℝ} (hw0 : 0 ≤ w) (hwW : w ≤ W) (hW2 : W < 2) :
    w / 2 * (1 + w / 2) / (1 - w / 2) ≤ W / 2 * (1 + W / 2) / (1 - W / 2) := by
  have h1 : 0 < 1 - w / 2 := by linarith
  have h2 : 0 < 1 - W / 2 := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hwW), mul_nonneg (mul_nonneg hw0 (sub_nonneg.mpr hwW)) hw0]

set_option maxHeartbeats 800000 in
/-- **The averaged tail of a rung**: `∫_b^t ψ² ≤ (G/(4c))log((b+1)/(b−1))(1 + κ_W) + G/(c²(b² − 1))`. -/
theorem tail_mass_le_avg {c χ G W b t : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hb : 1 < b) (hbt : b ≤ t)
    (hψ : ∀ ξ ∈ Icc b t, HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ ∈ Icc b t, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hE : ∀ ξ ∈ Icc b t, 0 < energy (aP c χ) ψ u ξ) (hG : ∀ ξ ∈ Icc b t, energy (aP c χ) ψ u ξ ≤ G)
    (hW : wP c χ b ≤ W) (hW2 : W < 2) :
    ∫ ξ in b..t, ψ ξ ^ 2
      ≤ G / (4 * c) * log ((b + 1) / (b - 1)) * (1 + W / 2 * (1 + W / 2) / (1 - W / 2)) + G / (c ^ 2 * (b ^ 2 - 1)) := by
  set a := aP c χ with had
  set q := qP c χ with hqd
  set w := wP c χ with hwd
  set E := energy a ψ u with hEd
  set Z : ℝ → ℝ := fun ξ => X a ψ u ξ * Y a ψ u ξ with hZd
  set D : ℝ → ℝ := fun ξ => X a ψ u ξ ^ 2 - Y a ψ u ξ ^ 2 with hDd
  set r := rate pP a w q ψ u with hrd
  set f : ℝ → ℝ := fun ξ => E ξ / (2 * q ξ) with hfd
  set f' : ℝ → ℝ := fun ξ => (w ξ * q ξ * (ψ ξ ^ 2 - u ξ ^ 2 / a ξ ^ 2) * q ξ - E ξ * (2 * c ^ 2 * ξ)) / (2 * q ξ ^ 2)
    with hf'd
  set ε : ℝ → ℝ := fun ξ => w ξ * (u ξ * ψ ξ) / E ξ with hεd
  set κ := W / 2 * (1 + W / 2) / (1 - W / 2) with hκd
  have hc2 : 0 < c ^ 2 := by positivity
  have hpb0' : 0 < b ^ 2 - 1 := by nlinarith
  have hI : uIcc b t = Icc b t := uIcc_of_le hbt
  have hW0 : 0 ≤ W := le_trans (wP_pos hb hc2 hχc).le hW
  have hκ0 : 0 ≤ κ := by
    rw [hκd]
    have : 0 < 1 - W / 2 := by linarith
    positivity
  -- pointwise facts on `[b, t]`
  have hξ1 : ∀ ξ ∈ Icc b t, 1 < ξ := fun ξ hξ => lt_of_lt_of_le hb hξ.1
  have hne : ∀ ξ ∈ Icc b t, ξ ^ 2 - 1 ≠ 0 := fun ξ hξ => by
    have h := hξ1 ξ hξ; have : 1 < ξ ^ 2 := by nlinarith
    exact ne_of_gt (by linarith only [this])
  have hp : ∀ ξ ∈ Icc b t, 0 < pP ξ := fun ξ hξ => pP_pos (hξ1 ξ hξ)
  have hq : ∀ ξ ∈ Icc b t, 0 < q ξ := fun ξ hξ => qP_pos (hξ1 ξ hξ) hc2 hχc
  have ha : ∀ ξ ∈ Icc b t, 0 < a ξ := fun ξ hξ => aP_pos (hξ1 ξ hξ) hc2 hχc
  have hapq : ∀ ξ ∈ Icc b t, a ξ ^ 2 = pP ξ * q ξ := fun ξ hξ => aP_sq (hξ1 ξ hξ) hc2 hχc
  have hw0 : ∀ ξ ∈ Icc b t, 0 < w ξ := fun ξ hξ => wP_pos (hξ1 ξ hξ) hc2 hχc
  have hwW : ∀ ξ ∈ Icc b t, w ξ ≤ W := fun ξ hξ => (wP_le_of_le hc hχ0 hχc hb hξ.1).trans hW
  have haw : ∀ ξ ∈ Icc b t, HasDerivAt a (w ξ * q ξ) ξ := fun ξ hξ => hasDerivAt_aP (hξ1 ξ hξ) hc2 hχc
  have hε : ∀ ξ ∈ Icc b t, |ε ξ| ≤ w ξ / 2 := fun ξ hξ => abs_eps_le (ha ξ hξ) (hE ξ hξ) (hw0 ξ hξ).le
  have h1ε : ∀ ξ ∈ Icc b t, 1 + ε ξ ≠ 0 := fun ξ hξ => by
    have := hε ξ hξ; have := hwW ξ hξ; have := neg_le_abs (ε ξ); intro h; linarith
  have hrate : ∀ ξ ∈ Icc b t, r ξ = a ξ / pP ξ * (1 + ε ξ) := fun ξ hξ =>
    rate_eq (ha ξ hξ) (hp ξ hξ).ne' (hapq ξ hξ) (hE ξ hξ)
  have hD1 : ∀ ξ ∈ Icc b t, |D ξ| ≤ 1 := fun ξ hξ => by
    have h := X_sq_add_Y_sq (ψ := ψ) (u := u) (ha ξ hξ) (hE ξ hξ)
    simp only [hDd]; rw [abs_le]; constructor <;> nlinarith [sq_nonneg (X a ψ u ξ), sq_nonneg (Y a ψ u ξ)]
  have hacp : ∀ ξ ∈ Icc b t, c * pP ξ ≤ a ξ := fun ξ hξ => aP_ge_cp hχc.le (hξ1 ξ hξ).le
  have hqcp : ∀ ξ ∈ Icc b t, c ^ 2 * pP ξ ≤ q ξ := fun ξ _ => qP_ge hχc.le
  have hE0 : ∀ ξ ∈ Icc b t, 0 ≤ E ξ := fun ξ hξ => (hE ξ hξ).le
  have hG0 : 0 ≤ G := le_trans (hE0 b ⟨le_rfl, hbt⟩) (hG b ⟨le_rfl, hbt⟩)
  -- the decomposition `ψ² = g + f·Z′`, `g = E/(2a) − f(ε/(1+ε))Z′`
  have hdec : ∀ ξ ∈ Icc b t, ψ ξ ^ 2 = (E ξ / (2 * a ξ) - f ξ * (ε ξ / (1 + ε ξ)) * (r ξ * D ξ)) + f ξ * (r ξ * D ξ) :=
    fun ξ hξ => by
      have := psi_sq_decomp (p := pP) (w := w) (q := q) (ha ξ hξ) (hp ξ hξ).ne' (hq ξ hξ).ne' (hapq ξ hξ) (hE ξ hξ)
        (h1ε ξ hξ)
      simp only [hfd, hεd, hDd, hrd, hEd]; linarith
  -- derivatives of `Z` and `f`
  have hZ : ∀ ξ ∈ Icc b t, HasDerivAt Z (r ξ * D ξ) ξ := fun ξ hξ =>
    hasDerivAt_XY (ha ξ hξ) (hp ξ hξ).ne' (hapq ξ hξ) (hE ξ hξ) (hψ ξ hξ) (hu ξ hξ) (haw ξ hξ)
  have hEder : ∀ ξ ∈ Icc b t, HasDerivAt E (w ξ * q ξ * (ψ ξ ^ 2 - u ξ ^ 2 / a ξ ^ 2)) ξ := fun ξ hξ =>
    hasDerivAt_energy (ha ξ hξ) (hp ξ hξ).ne' (hapq ξ hξ) (hψ ξ hξ) (hu ξ hξ) (haw ξ hξ)
  have hf : ∀ ξ ∈ Icc b t, HasDerivAt f (f' ξ) ξ := fun ξ hξ => by
    have hq' : HasDerivAt q (2 * c ^ 2 * ξ) ξ := hasDerivAt_qP c χ ξ
    have hq0 : (2 * q ξ) ≠ 0 := (mul_pos two_pos (hq ξ hξ)).ne'
    have := (hEder ξ hξ).div (hq'.const_mul 2) hq0
    refine this.congr_deriv ?_
    simp only [hf'd]
    have := (hq ξ hξ).ne'
    field_simp
  -- continuity on `[b, t]`
  have cψ : ContinuousOn ψ (Icc b t) := fun ξ hξ => (hψ ξ hξ).continuousAt.continuousWithinAt
  have cu : ContinuousOn u (Icc b t) := fun ξ hξ => (hu ξ hξ).continuousAt.continuousWithinAt
  have ca : ContinuousOn a (Icc b t) := fun ξ hξ => (haw ξ hξ).continuousAt.continuousWithinAt
  have cE : ContinuousOn E (Icc b t) := fun ξ hξ => (hEder ξ hξ).continuousAt.continuousWithinAt
  have cq : ContinuousOn q (Icc b t) := by rw [hqd]; unfold qP; fun_prop
  have cp : ContinuousOn pP (Icc b t) := by unfold pP; fun_prop
  have cw : ContinuousOn w (Icc b t) := fun ξ hξ =>
    (hasDerivAt_wP (hξ1 ξ hξ) hc2 hχc).continuousAt.continuousWithinAt
  have cZ : ContinuousOn Z (Icc b t) := fun ξ hξ => (hZ ξ hξ).continuousAt.continuousWithinAt
  have cf : ContinuousOn f (Icc b t) := fun ξ hξ => (hf ξ hξ).continuousAt.continuousWithinAt
  have cX : ContinuousOn (X a ψ u) (Icc b t) := by
    unfold X
    exact ((ca.sqrt.mul cψ).div cE.sqrt) fun ξ hξ => (Real.sqrt_pos.mpr (hE ξ hξ)).ne'
  have cY : ContinuousOn (Y a ψ u) (Icc b t) := by
    unfold Y
    exact (cu.div (ca.sqrt.mul cE.sqrt) fun ξ hξ =>
      (mul_pos (Real.sqrt_pos.mpr (ha ξ hξ)) (Real.sqrt_pos.mpr (hE ξ hξ))).ne').neg
  have cD : ContinuousOn D (Icc b t) := (cX.pow 2).sub (cY.pow 2)
  have cr : ContinuousOn r (Icc b t) := by
    rw [hrd]; unfold rate
    refine (ca.div cp fun ξ hξ => (hp ξ hξ).ne').add
      (((cw.mul cq).mul (cu.mul cψ)).div (ca.mul cE) fun ξ hξ => (mul_pos (ha ξ hξ) (hE ξ hξ)).ne')
  have cf' : ContinuousOn f' (Icc b t) := by
    simp only [hf'd]
    refine ContinuousOn.div ?_ (continuousOn_const.mul (cq.pow 2))
      fun ξ hξ => show 2 * q ξ ^ 2 ≠ 0 from (mul_pos two_pos (pow_pos (hq ξ hξ) 2)).ne'
    refine ContinuousOn.sub (((cw.mul cq).mul ((cψ.pow 2).sub ((cu.pow 2).div (ca.pow 2)
      fun ξ hξ => show a ξ ^ 2 ≠ 0 from (pow_pos (ha ξ hξ) 2).ne'))).mul cq) (cE.mul ((continuous_const.mul continuous_id).continuousOn))
  have iZ' : IntervalIntegrable (fun ξ => r ξ * D ξ) volume b t := (cr.mul cD).intervalIntegrable_of_Icc hbt
  have if' : IntervalIntegrable f' volume b t := cf'.intervalIntegrable_of_Icc hbt
  have ifZ' : IntervalIntegrable (fun ξ => f ξ * (r ξ * D ξ)) volume b t :=
    (cf.mul (cr.mul cD)).intervalIntegrable_of_Icc hbt
  have iψ : IntervalIntegrable (fun ξ => ψ ξ ^ 2) volume b t := (cψ.pow 2).intervalIntegrable_of_Icc hbt
  set g : ℝ → ℝ := fun ξ => E ξ / (2 * a ξ) - f ξ * (ε ξ / (1 + ε ξ)) * (r ξ * D ξ) with hgd
  have ig : IntervalIntegrable g volume b t := by
    refine (iψ.sub ifZ').congr fun ξ hξ => ?_
    rw [uIoc_of_le hbt] at hξ
    have hξ' : ξ ∈ Icc b t := Ioc_subset_Icc_self hξ
    simp only [hgd]; linarith [hdec ξ hξ']
  -- split
  have hsplit : ∫ ξ in b..t, ψ ξ ^ 2 = (∫ ξ in b..t, g ξ) + ∫ ξ in b..t, f ξ * (r ξ * D ξ) := by
    rw [← integral_add ig ifZ']
    refine integral_congr fun ξ hξ => ?_
    rw [hI] at hξ
    simp only [hgd]; linarith [hdec ξ hξ]
  -- the pointwise bound on `g`
  have hgle : ∀ ξ ∈ Icc b t, g ξ ≤ G / (2 * (c * pP ξ)) * (1 + κ) := fun ξ hξ => by
    have hT3 := eps_term_le (hE ξ hξ) (ha ξ hξ) (hp ξ hξ) (hq ξ hξ) (hapq ξ hξ) (hw0 ξ hξ).le
      (by linarith [hwW ξ hξ]) (hε ξ hξ) (hD1 ξ hξ) (hrate ξ hξ)
    have hκw := kappa_mono (hw0 ξ hξ).le (hwW ξ hξ) hW2
    have hEa : E ξ / (2 * a ξ) ≤ G / (2 * (c * pP ξ)) := by
      apply div_le_div₀ hG0 (hG ξ hξ) (by have := hp ξ hξ; positivity) (by linarith [hacp ξ hξ])
    have hEa0 : 0 ≤ E ξ / (2 * a ξ) := by have := ha ξ hξ; have := hE0 ξ hξ; positivity
    have hκw0 : 0 ≤ w ξ / 2 * (1 + w ξ / 2) / (1 - w ξ / 2) := by
      have := hw0 ξ hξ; have : 0 < 1 - w ξ / 2 := by linarith [hwW ξ hξ]
      positivity
    simp only [hgd, hfd]
    calc E ξ / (2 * a ξ) - E ξ / (2 * q ξ) * (ε ξ / (1 + ε ξ)) * (r ξ * D ξ)
        ≤ E ξ / (2 * a ξ) + |E ξ / (2 * q ξ) * (ε ξ / (1 + ε ξ)) * (r ξ * D ξ)| := by
          linarith [neg_le_abs (E ξ / (2 * q ξ) * (ε ξ / (1 + ε ξ)) * (r ξ * D ξ))]
      _ ≤ E ξ / (2 * a ξ) + E ξ / (2 * a ξ) * (w ξ / 2 * (1 + w ξ / 2) / (1 - w ξ / 2)) := by linarith [hT3]
      _ = E ξ / (2 * a ξ) * (1 + w ξ / 2 * (1 + w ξ / 2) / (1 - w ξ / 2)) := by ring
      _ ≤ G / (2 * (c * pP ξ)) * (1 + κ) := by
          apply mul_le_mul hEa (by linarith) (by linarith)
            (div_nonneg hG0 (mul_pos two_pos (mul_pos hc (hp ξ hξ))).le)
  have hint1 : ∫ ξ in b..t, g ξ ≤ G / (4 * c) * log ((b + 1) / (b - 1)) * (1 + κ) := by
    have hc1 : ContinuousOn (fun ξ : ℝ => G / (2 * (c * pP ξ)) * (1 + κ)) (Icc b t) := by
      refine (continuousOn_const.div (continuousOn_const.mul (continuousOn_const.mul cp))
        fun ξ hξ => ?_).mul continuousOn_const
      exact (mul_pos two_pos (mul_pos hc (hp ξ hξ))).ne'
    have hc2' : ContinuousOn (fun ξ : ℝ => 1 / (ξ ^ 2 - 1)) (Icc b t) := by
      apply continuousOn_const.div ((continuousOn_id.pow 2).sub continuousOn_const)
      intro ξ hξ; exact hne ξ hξ
    have h1 := integral_mono_on hbt ig (hc1.intervalIntegrable_of_Icc hbt) hgle
    have h2 : ∫ ξ in b..t, G / (2 * (c * pP ξ)) * (1 + κ) = G * (1 + κ) / (2 * c) * ∫ ξ in b..t, 1 / (ξ ^ 2 - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      refine integral_congr fun ξ hξ => ?_
      rw [hI] at hξ
      have := hne ξ hξ; have := hc.ne'
      unfold pP; field_simp
    have h3 : ∫ ξ in b..t, 1 / (ξ ^ 2 - 1)
        = 1 / 2 * log ((t - 1) / (t + 1)) - 1 / 2 * log ((b - 1) / (b + 1)) :=
      integral_eq_sub_of_hasDerivAt (fun ξ hξ => hasDerivAt_half_log (hξ1 ξ (hI ▸ hξ)))
        (hc2'.intervalIntegrable_of_Icc hbt)
    have h4 : 1 / 2 * log ((t - 1) / (t + 1)) - 1 / 2 * log ((b - 1) / (b + 1)) ≤ 1 / 2 * log ((b + 1) / (b - 1)) := by
      have ht1 : 1 < t := lt_of_lt_of_le hb hbt
      have hlt : log ((t - 1) / (t + 1)) ≤ 0 := by
        apply log_nonpos (div_nonneg (by linarith) (by linarith))
        rw [div_le_one (by linarith)]; linarith
      have hlb : log ((b + 1) / (b - 1)) = -log ((b - 1) / (b + 1)) := by rw [← log_inv, inv_div]
      rw [hlb]; linarith
    have hpos : 0 ≤ G * (1 + κ) / (2 * c) := by positivity
    calc ∫ ξ in b..t, g ξ ≤ ∫ ξ in b..t, G / (2 * (c * pP ξ)) * (1 + κ) := h1
      _ = G * (1 + κ) / (2 * c) * (1 / 2 * log ((t - 1) / (t + 1)) - 1 / 2 * log ((b - 1) / (b + 1))) := by
          rw [h2, h3]
      _ ≤ G * (1 + κ) / (2 * c) * (1 / 2 * log ((b + 1) / (b - 1))) := mul_le_mul_of_nonneg_left h4 hpos
      _ = G / (4 * c) * log ((b + 1) / (b - 1)) * (1 + κ) := by ring
  -- the exact-derivative term by parts
  have hibp : ∫ ξ in b..t, f ξ * (r ξ * D ξ) = f t * Z t - f b * Z b - ∫ ξ in b..t, f' ξ * Z ξ :=
    integral_mul_deriv_eq_deriv_mul (fun ξ hξ => hf ξ (hI ▸ hξ)) (fun ξ hξ => hZ ξ (hI ▸ hξ)) if' iZ'
  have hfle : ∀ ξ ∈ Icc b t, |f ξ| ≤ G / (2 * (c ^ 2 * pP ξ)) := fun ξ hξ => by
    have hq' := hq ξ hξ
    have hf0 : 0 ≤ f ξ := by simp only [hfd]; have := hE0 ξ hξ; positivity
    rw [abs_of_nonneg hf0]
    simp only [hfd]
    apply div_le_div₀ hG0 (hG ξ hξ) (by have := hp ξ hξ; positivity) (by linarith [hqcp ξ hξ])
  have hZle : ∀ ξ ∈ Icc b t, |Z ξ| ≤ 1 / 2 := fun ξ hξ => abs_XY_le_half (ha ξ hξ) (hE ξ hξ)
  have hf'le : ∀ ξ ∈ Icc b t, |f' ξ| ≤ 2 * G * ξ / (c ^ 2 * pP ξ ^ 2) := fun ξ hξ => by
    have hξ' := hξ1 ξ hξ
    have ha' := ha ξ hξ
    have hE' : |w ξ * q ξ * (ψ ξ ^ 2 - u ξ ^ 2 / a ξ ^ 2)| ≤ w ξ * q ξ * E ξ / a ξ := by
      have hEa : E ξ / a ξ = ψ ξ ^ 2 + u ξ ^ 2 / a ξ ^ 2 := by
        simp only [hEd]; unfold energy; field_simp
      rw [abs_mul, abs_of_pos (mul_pos (hw0 ξ hξ) (hq ξ hξ)), mul_div_assoc, hEa]
      apply mul_le_mul_of_nonneg_left _ (mul_pos (hw0 ξ hξ) (hq ξ hξ)).le
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (ψ ξ), div_nonneg (sq_nonneg (u ξ)) (sq_nonneg (a ξ))]
    exact abs_fderiv_le hc (by linarith) (hp ξ hξ) (hq ξ hξ) ha' (hE0 ξ hξ) (hG ξ hξ) hE' (hw0 ξ hξ).le
      (wP_le_far hξ' hc hχ0 hχc) (hacp ξ hξ) (hqcp ξ hξ)
  have hpb : pP b = b ^ 2 - 1 := rfl
  have hpb0 : 0 < b ^ 2 - 1 := hpb0'
  have hbnd : ∀ ξ ∈ Icc b t, |f ξ * Z ξ| ≤ G / (4 * (c ^ 2 * (b ^ 2 - 1))) := fun ξ hξ => by
    have hpξ : b ^ 2 - 1 ≤ pP ξ := by unfold pP; nlinarith [hξ.1, hb]
    rw [abs_mul]
    calc |f ξ| * |Z ξ| ≤ G / (2 * (c ^ 2 * pP ξ)) * (1 / 2) :=
          mul_le_mul (hfle ξ hξ) (hZle ξ hξ) (abs_nonneg _)
            (div_nonneg hG0 (mul_pos two_pos (mul_pos hc2 (hp ξ hξ))).le)
      _ ≤ G / (2 * (c ^ 2 * (b ^ 2 - 1))) * (1 / 2) := by gcongr
      _ = G / (4 * (c ^ 2 * (b ^ 2 - 1))) := by field_simp; ring
  have hder : |∫ ξ in b..t, f' ξ * Z ξ| ≤ G / (2 * (c ^ 2 * (b ^ 2 - 1))) := by
    have hpt : ∀ ξ ∈ Icc b t, |f' ξ * Z ξ| ≤ G / c ^ 2 * (ξ / (ξ ^ 2 - 1) ^ 2) := fun ξ hξ => by
      rw [abs_mul]
      calc |f' ξ| * |Z ξ| ≤ 2 * G * ξ / (c ^ 2 * pP ξ ^ 2) * (1 / 2) :=
            mul_le_mul (hf'le ξ hξ) (hZle ξ hξ) (abs_nonneg _) (by have := hp ξ hξ; have := hξ1 ξ hξ; positivity)
        _ = G / c ^ 2 * (ξ / (ξ ^ 2 - 1) ^ 2) := by unfold pP; field_simp
    have hcq2 : ContinuousOn (fun ξ : ℝ => ξ / (ξ ^ 2 - 1) ^ 2) (Icc b t) :=
      continuousOn_id.div ((continuousOn_id.pow 2).sub continuousOn_const |>.pow 2)
        fun ξ hξ => pow_ne_zero 2 (hne ξ hξ)
    have hcb : ContinuousOn (fun ξ : ℝ => G / c ^ 2 * (ξ / (ξ ^ 2 - 1) ^ 2)) (Icc b t) :=
      continuousOn_const.mul hcq2
    have hcZ : ContinuousOn (fun ξ => |f' ξ * Z ξ|) (Icc b t) := (cf'.mul cZ).abs
    have h1 := abs_integral_le_integral_abs (μ := volume) (f := fun ξ => f' ξ * Z ξ) hbt
    have h2 := integral_mono_on hbt (hcZ.intervalIntegrable_of_Icc (μ := volume) hbt)
      (hcb.intervalIntegrable_of_Icc (μ := volume) hbt) hpt
    have h3' : ∫ ξ in b..t, ξ / (ξ ^ 2 - 1) ^ 2 = -1 / (2 * (t ^ 2 - 1)) - -1 / (2 * (b ^ 2 - 1)) :=
      integral_eq_sub_of_hasDerivAt (fun ξ hξ => hasDerivAt_neg_inv_two (hξ1 ξ (hI ▸ hξ)))
        (hcq2.intervalIntegrable_of_Icc (μ := volume) hbt)
    have h3 : ∫ ξ in b..t, G / c ^ 2 * (ξ / (ξ ^ 2 - 1) ^ 2)
        = G / c ^ 2 * (-1 / (2 * (t ^ 2 - 1)) - -1 / (2 * (b ^ 2 - 1))) := by
      rw [intervalIntegral.integral_const_mul, h3']
    have ht1 : 1 < t := lt_of_lt_of_le hb hbt
    have ht2 : 0 < t ^ 2 - 1 := by nlinarith
    have h4 : -1 / (2 * (t ^ 2 - 1)) - -1 / (2 * (b ^ 2 - 1)) ≤ 1 / (2 * (b ^ 2 - 1)) := by
      have : 0 ≤ 1 / (2 * (t ^ 2 - 1)) := by positivity
      have e : -1 / (2 * (t ^ 2 - 1)) = -(1 / (2 * (t ^ 2 - 1))) := by ring
      have e' : -1 / (2 * (b ^ 2 - 1)) = -(1 / (2 * (b ^ 2 - 1))) := by ring
      rw [e, e']; linarith only [this]
    calc |∫ ξ in b..t, f' ξ * Z ξ| ≤ ∫ ξ in b..t, |f' ξ * Z ξ| := h1
      _ ≤ ∫ ξ in b..t, G / c ^ 2 * (ξ / (ξ ^ 2 - 1) ^ 2) := h2
      _ = G / c ^ 2 * (-1 / (2 * (t ^ 2 - 1)) - -1 / (2 * (b ^ 2 - 1))) := h3
      _ ≤ G / c ^ 2 * (1 / (2 * (b ^ 2 - 1))) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = G / (2 * (c ^ 2 * (b ^ 2 - 1))) := by field_simp
  have hint2 : ∫ ξ in b..t, f ξ * (r ξ * D ξ) ≤ G / (c ^ 2 * (b ^ 2 - 1)) := by
    rw [hibp]
    have hb1 := hbnd b ⟨le_rfl, hbt⟩
    have ht1 := hbnd t ⟨hbt, le_rfl⟩
    have := neg_le_abs (∫ ξ in b..t, f' ξ * Z ξ)
    have e : G / (4 * (c ^ 2 * (b ^ 2 - 1))) + G / (4 * (c ^ 2 * (b ^ 2 - 1))) + G / (2 * (c ^ 2 * (b ^ 2 - 1)))
        = G / (c ^ 2 * (b ^ 2 - 1)) := by field_simp; ring
    linarith only [le_abs_self (f t * Z t), neg_le_abs (f b * Z b), hder, hb1, ht1, this, e]
  rw [hsplit]
  linarith only [hint1, hint2]

end Cvs.Prolate.RungAveragedTailIntegrated
