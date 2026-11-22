import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset
import Cvs.Prolate.Gram.GramFloorTailOrthogonality
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungOrthogonalityAtInfinity
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung Gram floor from orthogonality at infinity

For rungs `ψ_i = ∫ g_i cos(cξs)` with distinct angular eigenvalues `χ_i ∈ [0, c²)`, `c ≥ 1` and `b ≥ 2`,
`∫₁ᵇ (Σ a_iψ_i)² ≥ Σ_i a_i² (∫₁ᵇ ψ_i² − Σ_j T_j)`, where `T_j = (G_j/(2c)) log((b+1)/(b−1))` bounds the tail
`∫_b^∞ ψ_j²` through `ψ² ≤ G/(c(ξ² − 1))` and the energy beyond `b`, `G_j = E_j(b)(1 + W/2)/(1 − W/2) e^{W/(2−W)}`,
`W = w_j(b) ≤ 2b/(c(b² − 1))`. The pairs enter only through Cvs.Prolate.RungOrthogonalityAtInfinity, with no gap between the `χ_i`.
-/

namespace Cvs.Prolate.Gram.RungGramFloorAtInfinity

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity
open scoped Interval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **`w ≤ 2ξ/(cp)`** for `ξ > 1`, `c > 0`, `0 ≤ χ < c²`: from `c²p ≤ q` and `cp ≤ a`. -/
theorem wP_le_far {c χ ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    wP c χ ξ ≤ 2 * ξ / (c * pP ξ) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp := pP_pos hξ
  have hq := qP_pos hξ hc2 hχc
  have ha := aP_pos hξ hc2 hχc
  have ha2 := aP_sq hξ hc2 hχc
  have hX : qP c χ ξ + c ^ 2 * pP ξ ≤ 2 * qP c χ ξ := by unfold pP qP; nlinarith
  have hcp : c * pP ξ ≤ aP c χ ξ := by
    apply le_of_sq_le_sq _ ha.le
    rw [ha2, mul_pow]; unfold pP qP
    nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ ξ ^ 2 - 1) (by linarith : (0:ℝ) ≤ c ^ 2 - χ)]
  have hXY : (qP c χ ξ + c ^ 2 * pP ξ) * (c * pP ξ) ≤ 2 * qP c χ ξ * aP c χ ξ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hX) (by positivity : (0:ℝ) ≤ c * pP ξ),
      mul_nonneg (by positivity : (0:ℝ) ≤ 2 * qP c χ ξ) (sub_nonneg.mpr hcp)]
  unfold wP dP
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : 2 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ = qP c χ ξ + c ^ 2 * pP ξ := by unfold pP qP; ring
  rw [e]
  calc 2 * ξ * (qP c χ ξ + c ^ 2 * pP ξ) * (c * pP ξ)
      = 2 * ξ * ((qP c χ ξ + c ^ 2 * pP ξ) * (c * pP ξ)) := by ring
    _ ≤ 2 * ξ * (2 * qP c χ ξ * aP c χ ξ) := mul_le_mul_of_nonneg_left hXY (by positivity)

/-- **`w(b) < 2` for `b ≥ 2`, `c ≥ 1`.** -/
theorem wP_lt_two {c χ b : ℝ} (hb : 2 ≤ b) (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    wP c χ b < 2 := by
  have hb1 : 1 < b := by linarith
  refine lt_of_le_of_lt (wP_le_far hb1 (by linarith) hχ0 hχc) ?_
  have hp := pP_pos hb1
  rw [div_lt_iff₀ (by positivity)]
  unfold pP
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (by nlinarith : (0:ℝ) ≤ b ^ 2 - 1),
    mul_nonneg (sub_nonneg.mpr hb) (by linarith : (0:ℝ) ≤ b + 1)]

/-- `½ log((ξ − 1)/(ξ + 1))` is a primitive of `1/(ξ² − 1)` on `ξ > 1`. -/
theorem hasDerivAt_half_log {ξ : ℝ} (hξ : 1 < ξ) :
    HasDerivAt (fun ξ => 1 / 2 * log ((ξ - 1) / (ξ + 1))) (1 / (ξ ^ 2 - 1)) ξ := by
  have h1 : ξ + 1 ≠ 0 := by linarith
  have h2 : (ξ - 1) / (ξ + 1) ≠ 0 := div_ne_zero (by linarith) h1
  have hf := ((hasDerivAt_id' ξ).sub_const 1).fun_div ((hasDerivAt_id' ξ).add_const 1) h1
  have := (hf.log h2).const_mul (1 / 2)
  refine this.congr_deriv ?_
  have h3 : ξ - 1 ≠ 0 := by linarith
  have h4 : ξ ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

/-- **The tail beyond `b`**: for a rung with energy `≤ G` on `[b, t]`, `1 < b ≤ t`,
`∫_b^t ψ² ≤ (G/(2c)) log((b + 1)/(b − 1))`. -/
theorem tail_mass_le {c χ G b t : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hb : 1 < b) (hbt : b ≤ t)
    (hcont : ContinuousOn ψ (Icc b t)) (hG : ∀ ξ ∈ Icc b t, energy (aP c χ) ψ u ξ ≤ G) :
    ∫ ξ in b..t, ψ ξ ^ 2 ≤ G / (2 * c) * log ((b + 1) / (b - 1)) := by
  have hG0 : 0 ≤ G := by
    refine le_trans ?_ (hG b (left_mem_Icc.mpr hbt))
    unfold energy
    have := aP_pos hb (by positivity) hχc
    positivity
  have hpt : ∀ ξ ∈ Icc b t, ψ ξ ^ 2 ≤ G / (c * (ξ ^ 2 - 1)) := fun ξ hξ =>
    Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset.psi_sq_le_edge hc hχc (lt_of_lt_of_le hb hξ.1) (hG ξ hξ)
  have hne : ∀ ξ ∈ Icc b t, ξ ^ 2 - 1 ≠ 0 := fun ξ hξ => by
    have := lt_of_lt_of_le hb hξ.1; nlinarith
  have hc1 : ContinuousOn (fun ξ : ℝ => G / (c * (ξ ^ 2 - 1))) (Icc b t) := by
    apply continuousOn_const.div (continuousOn_const.mul ((continuousOn_id.pow 2).sub continuousOn_const))
    intro ξ hξ; exact mul_ne_zero hc.ne' (hne ξ hξ)
  have hc2 : ContinuousOn (fun ξ : ℝ => 1 / (ξ ^ 2 - 1)) (Icc b t) := by
    apply continuousOn_const.div ((continuousOn_id.pow 2).sub continuousOn_const)
    intro ξ hξ; exact hne ξ hξ
  have hI : uIcc b t = Icc b t := uIcc_of_le hbt
  calc ∫ ξ in b..t, ψ ξ ^ 2 ≤ ∫ ξ in b..t, G / (c * (ξ ^ 2 - 1)) :=
        integral_mono_on hbt ((hcont.pow 2).intervalIntegrable_of_Icc hbt) (hc1.intervalIntegrable_of_Icc hbt) hpt
    _ = G / c * ∫ ξ in b..t, 1 / (ξ ^ 2 - 1) := by
        rw [← integral_const_mul]
        exact integral_congr fun ξ hξ => by
          have h1 := hne ξ (hI ▸ hξ); have h2 := hc.ne'; field_simp
    _ = G / c * (1 / 2 * log ((t - 1) / (t + 1)) - 1 / 2 * log ((b - 1) / (b + 1))) := by
        rw [integral_eq_sub_of_hasDerivAt (fun ξ hξ => hasDerivAt_half_log (lt_of_lt_of_le hb (hI ▸ hξ).1))
          (hc2.intervalIntegrable_of_Icc hbt)]
    _ ≤ G / (2 * c) * log ((b + 1) / (b - 1)) := by
        have ht1 : 1 < t := lt_of_lt_of_le hb hbt
        have hlt : log ((t - 1) / (t + 1)) ≤ 0 := by
          apply log_nonpos (div_nonneg (by linarith) (by linarith))
          rw [div_le_one (by linarith)]; linarith
        have hlb : log ((b + 1) / (b - 1)) = -log ((b - 1) / (b + 1)) := by rw [← log_inv, inv_div]
        rw [hlb]
        have h0 : 0 ≤ G / c * (1 / 2 * -log ((t - 1) / (t + 1))) := by
          apply mul_nonneg (div_nonneg hG0 hc.le); linarith
        have e : G / (2 * c) * -log ((b - 1) / (b + 1)) = G / c * (-(1 / 2) * log ((b - 1) / (b + 1))) := by
          field_simp
        rw [e]; nlinarith [h0]

/-- The rung's `u = (ξ² − 1)ψ'` as a kernel integral. -/
noncomputable def rungU (c : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  pP ξ * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ

/-- **The rung as a `(ψ, u)` system** on `ξ > 1`: `ψ' = u/p`, `u' = −qψ`, and `u(1) = 0`. -/
theorem rung_system {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    (∀ ξ, 1 < ξ → HasDerivAt (psi c g) (rungU c g ξ / pP ξ) ξ)
      ∧ (∀ ξ, HasDerivAt (rungU c g) (-(qP c χ ξ * psi c g ξ)) ξ)
      ∧ Continuous (psi c g) ∧ Continuous (rungU c g) := by
  obtain ⟨hψ, hv, hode⟩ := psi_system hg hg₁ hg₂c hang
  have hp' : ∀ ξ : ℝ, HasDerivAt pP (2 * ξ) ξ := fun ξ => by
    have := (hasDerivAt_pow 2 ξ).sub_const 1; unfold pP; simpa using this
  have hpc : Continuous pP := by unfold pP; fun_prop
  refine ⟨fun ξ hξ => ?_, fun ξ => ?_, ?_, ?_⟩
  · have hp : pP ξ ≠ 0 := (pP_pos hξ).ne'
    unfold rungU; rw [mul_div_cancel_left₀ _ hp]; exact hψ ξ
  · refine ((hp' ξ).mul (hv ξ)).congr_deriv ?_
    have := hode ξ; unfold pP qP; linarith
  · exact continuous_iff_continuousAt.mpr fun ξ => (hψ ξ).continuousAt
  · exact hpc.mul (continuous_iff_continuousAt.mpr fun ξ => (hv ξ).continuousAt)

/-- The tail bound of a rung beyond `b`: `(G/(2c)) log((b + 1)/(b − 1))` with
`G = E(b)(1 + W/2)/(1 − W/2) e^{W/(2−W)}`, `W = w(b)`. -/
noncomputable def tailBound (c χ : ℝ) (g : ℝ → ℝ) (b : ℝ) : ℝ :=
  energy (aP c χ) (psi c g) (rungU c g) b * (1 + wP c χ b / 2) / (1 - wP c χ b / 2)
    * exp (wP c χ b / (2 - wP c χ b)) / (2 * c) * log ((b + 1) / (b - 1))

/-- **The rung Gram floor from orthogonality at infinity**: for rungs with distinct `χ_i ∈ [0, c²)`, `c ≥ 1`,
`b ≥ 2`, `Σ_i a_i² (∫₁ᵇ ψ_i² − Σ_j T_j) ≤ ∫₁ᵇ (Σ_i a_iψ_i)²`, `T_j` the tail bound of `ψ_j` beyond `b`. -/
theorem rung_gram_floor_tail {c b : ℝ} (hc : 1 ≤ c) (hb : 2 ≤ b)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ) :
    ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) - ∑ j, tailBound c (χ j) (g j) b)
      ≤ ∫ ξ in (1 : ℝ)..b, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hb1 : 1 < b := by linarith
  have hsys := fun i => rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)
  apply Cvs.Prolate.Gram.GramFloorTailOrthogonality.gram_floor_tail hb1.le (fun i => psi c (g i)) a
    (fun i j => wronskianConst c (g i) (g₁ i) (g₂ i) (g j) (g₁ j) (g₂ j) / |χ i - χ j|)
    (fun j => tailBound c (χ j) (g j) b)
  · exact fun i => (hsys i).2.2.1.continuousOn
  · intro i j hij t hbt
    have hχ : χ i ≠ χ j := fun e => hij (hinj e)
    rw [div_div]
    exact integral_psi_mul_le (hg i) (hg₁ i) (hg₂c i) (hang i) (hg j) (hg₁ j) (hg₂c j) (hang j) hc0 hχ
      (hb1.le.trans hbt)
  · intro j t hbt
    obtain ⟨hψu, huu, hcψ, hcu⟩ := hsys j
    have hW := wP_lt_two hb hc (hχ0 j) (hχc j)
    -- the energy beyond `b` from the energy at `b`
    have hG : ∀ ξ ∈ Icc b t, energy (aP c (χ j)) (psi c (g j)) (rungU c (g j)) ξ
        ≤ energy (aP c (χ j)) (psi c (g j)) (rungU c (g j)) b * (1 + wP c (χ j) b / 2) / (1 - wP c (χ j) b / 2)
          * exp (wP c (χ j) b / (2 - wP c (χ j) b)) := fun ξ hξ =>
      prolate_energy_le hb1 hξ.1 (by positivity) (hχ0 j) (hχc j)
        (fun r hr => hψu r (lt_of_lt_of_le hb1 hr.1)) (fun r _ => huu r) hW
    unfold tailBound
    exact tail_mass_le hc0 (hχc j) hb1 hbt hcψ.continuousOn hG

end Cvs.Prolate.Gram.RungGramFloorAtInfinity
