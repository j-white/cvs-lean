import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.AngularVirial
import Cvs.Prolate.CorrectedEnergyPairAngular
import Cvs.Prolate.ForbiddenZoneClosedForm
import Cvs.Prolate.ForbiddenZoneGrowth
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.AiryTurningPoint
import Cvs.Prolate.LiouvilleGreen.AngularRateAiryUnits
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.PlungeLawIntegral
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The plunge law P2♭: the two-zone mass sum

The radial frame `(1 − λ)c∫₀¹ψ² ≤ (11/20)(K + 1/(2S))ψ(1)²` and the two-zone lower bound
`ψ(a)²(D₁ + D₂(K − β)₊) ≤ c∫₀^aψ²` (Airy window plus transported angular virial) give
`1 − λ ≤ (11/20)max{T₁, T₂}e^{−2Φ_C(Z_tot)}`; for `5 ≤ S ≤ c/4` the ratios are at most `T̄₁, T̄₂`.
-/

namespace Cvs.Prolate.PlungeLawTwoZone

open Real Set MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.ForbiddenZoneGrowth Cvs.Prolate.PlungeLawIntegral Cvs.Prolate.ForbiddenZoneClosedForm Cvs.Prolate.LiouvilleGreen.AiryTurningPoint Cvs.Prolate.CorrectedEnergyPairAngular Cvs.Prolate.AngularVirial Cvs.Prolate.LiouvilleGreen.AngularRateAiryUnits

/-- **The radial frame**: `(1 − λ)c∫₀¹ψ² ≤ (11/20)(K + c/(2(c² − χ)))ψ(1)²` for an even rung with
`psi c g = μ g`, `c ≥ 80`, `χ ≥ 0`, `c² − χ ≥ 5c`. -/
theorem radial_frame {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hD : 5 * c ≤ c ^ 2 - χ)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    (1 - c / (2 * π) * μ ^ 2) * (c * ∫ x in (0 : ℝ)..1, psi c g x ^ 2)
      ≤ 11 / 20 * (ellK c χ + c / (2 * (c ^ 2 - χ))) * psi c g 1 ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hD0 : 0 < c ^ 2 - χ := by linarith
  have hχc : χ < c ^ 2 := by linarith
  have hgc : ContinuousOn g (Icc (-1 : ℝ) 1) := fun s hs =>
    (hg s (by rw [uIcc_of_le (by norm_num)]; exact hs)).continuousAt.continuousWithinAt
  obtain ⟨hψ, hu, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hu1 : rungU c g 1 = 0 := by unfold rungU pP; simp
  obtain ⟨-, hM⟩ := radial_mass_le hc0 hχ0 hχc hψ hu hψc hu1
    (fun ξ hξ => energy_le_sup hg hg₁ hg₂c hang hc hχ0 hD hξ)
  have hlow := one_sub_lambda_mul_le hc0 hgc heven hμ
  calc (1 - c / (2 * π) * μ ^ 2) * (c * ∫ x in (0 : ℝ)..1, psi c g x ^ 2)
      = c * ((1 - c / (2 * π) * μ ^ 2) * ∫ x in (0 : ℝ)..1, psi c g x ^ 2) := by ring
    _ ≤ c * ∫ x in Ioi 1, psi c g x ^ 2 := mul_le_mul_of_nonneg_left hlow hc0.le
    _ ≤ c * (11 / 10 * psi c g 1 ^ 2 / 2 * (∫ ξ in Ioi 1, 1 / aP c χ ξ)
          + 11 / 10 * psi c g 1 ^ 2 / (4 * (c ^ 2 - χ))) := mul_le_mul_of_nonneg_left hM hc0.le
    _ = 11 / 20 * (ellK c χ + c / (2 * (c ^ 2 - χ))) * psi c g 1 ^ 2 := by
        unfold ellK; field_simp; ring

/-- `D₂ > 0` for `0 < θ < Θ`, `θ³ < 6`, `εΘ < 1/2` and `W(θ(1 − εθ)) < 2`. -/
theorem D2f_pos {g a ε θ Θ : ℝ} (hg : 0 < g) (ha : 0 < a) (hε : 0 ≤ ε) (hθ : 0 < θ) (hθΘ : θ < Θ)
    (hθ6 : θ ^ 3 < 6) (hεΘ : ε * Θ < 1 / 2) (hW : Wair g (θ * (1 - ε * θ)) < 2) :
    0 < D2f g a ε θ Θ := by
  have hεθ : ε * θ ≤ ε * Θ := mul_le_mul_of_nonneg_left hθΘ.le hε
  have hym : 0 < θ * (1 - ε * θ) := mul_pos hθ (by linarith)
  have hyv : θ * (1 - ε * θ) ≤ Θ * (1 - ε * Θ) := by
    nlinarith [mul_pos (sub_pos.2 hθΘ) (by linarith : (0 : ℝ) < 1 - ε * Θ - ε * θ)]
  have hRm : 0 < Rcorr (Wair g (θ * (1 - ε * θ))) :=
    Rcorr_pos (by linarith [Wair_pos hg.le hym]) hW
  have hRv : 0 < Rcorr (Wair g (Θ * (1 - ε * Θ))) :=
    Rcorr_pos (by linarith [Wair_pos hg.le (hym.trans_le hyv)])
      (lt_of_le_of_lt (Wair_anti hg.le hym hyv) hW)
  have h6 : 0 < 1 - θ ^ 3 / 6 := by linarith
  unfold D2f
  exact mul_pos (mul_pos (mul_pos hRv hRm) (pow_pos h6 2))
    (mul_pos (div_pos ha hg) (sqrt_pos.2 (by positivity)))

/-- `D₁ = m(θ)/√g > 0` for `0 < θ`, `θ³ < 6`. -/
theorem D1f_pos {g θ : ℝ} (hg : 0 < g) (hθ : 0 < θ) (hθ6 : θ ^ 3 < 6) : 0 < D1f g θ := by
  have hm : 0 < mth θ := by
    unfold mth
    nlinarith [mul_pos hθ (by linarith : (0 : ℝ) < 1 - θ ^ 3 / 12), pow_pos hθ 7]
  unfold D1f
  exact div_pos hm (sqrt_pos.2 hg)

/-- **The two-zone mass**: the Airy window `[a − θl, a]` carries `D₁ψ(a)²`, and the transported
angular virial on `[0, a − Θl]` carries `D₂ψ(a)²(K − β)₊`; together at most `c∫₀^aψ²`. -/
theorem two_zone {ψ u : ℝ → ℝ} {c χ a θ Θ : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1)
    (hχ : χ = c ^ 2 * a ^ 2) (hθ : 0 < θ) (hθΘ : θ < Θ) (hθ6 : θ ^ 3 < 6)
    (hΘε : airyEps c a * Θ < 1 / 2) (hW : Wair (airyG c a) (θ * (1 - airyEps c a * θ)) < 2)
    (hψ : ∀ t ∈ Icc 0 a, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc 0 a, HasDerivAt u (-(qP c χ t * ψ t)) t) (hu0 : u 0 = 0)
    (hψa : 0 ≤ ψ a) (hua : 0 ≤ u a) :
    ψ a ^ 2 * (D1f (airyG c a) θ + D2f (airyG c a) a (airyEps c a) θ Θ
        * max 0 (ellK c χ - betaf (airyG c a) a (airyEps c a) Θ))
      ≤ c * ∫ t in (0 : ℝ)..a, ψ t ^ 2 := by
  have hl := airyL_pos hc ha ha1
  have hg := airyG_pos hc ha ha1
  have hε := airyEps_pos hc ha ha1
  have hlε : airyL c a = 2 * a * airyEps c a := by unfold airyEps; field_simp
  have hΘ : 0 < Θ := hθ.trans hθΘ
  have hεθ : airyEps c a * θ < airyEps c a * Θ := mul_lt_mul_of_pos_left hθΘ hε
  have hΘl : Θ * airyL c a < a := by
    rw [hlε]; nlinarith [mul_pos ha (sub_pos.2 hΘε)]
  have hθl : θ * airyL c a < Θ * airyL c a := mul_lt_mul_of_pos_right hθΘ hl
  have hc2 : 0 < c ^ 2 := by positivity
  have hχc : χ < c ^ 2 := by
    rw [hχ]; nlinarith [mul_pos hc2 (by nlinarith : (0 : ℝ) < 1 - a ^ 2)]
  have hpq : ∀ s, 0 ≤ s → s < a → pP s < 0 ∧ qP c χ s < 0 := fun s hs0 hsa => by
    have h2 : s ^ 2 < a ^ 2 := by nlinarith
    refine ⟨by unfold pP; nlinarith, by unfold qP; rw [hχ]; nlinarith [mul_pos hc2 (sub_pos.2 h2)]⟩
  have hsq : ∀ s, 0 ≤ s → s < a → c ^ 2 * s ^ 2 < χ := fun s hs0 hsa => by
    have := (hpq s hs0 hsa).2; unfold qP at this; linarith
  have hsub : ∀ x y : ℝ, 0 ≤ x → y ≤ a → Icc x y ⊆ Icc 0 a := fun x y hx hy => Icc_subset_Icc hx hy
  have hψc : ContinuousOn ψ (Icc 0 a) := fun t ht => (hψ t ht).continuousAt.continuousWithinAt
  have hII : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ a → IntervalIntegrable (fun t => ψ t ^ 2) volume x y :=
    fun x y hx hxy hy => ((hψc.pow 2).mono (hsub x y hx hy)).intervalIntegrable_of_Icc hxy
  have hInn : ∀ x y : ℝ, x ≤ y → 0 ≤ ∫ t in x..y, ψ t ^ 2 := fun x y hxy =>
    intervalIntegral.integral_nonneg hxy fun t _ => sq_nonneg _
  have henergy : ∀ s, 0 ≤ s → s < a →
      aP c χ s * ψ s ^ 2 ≤ energy (aP c χ) ψ u s ∧ 0 ≤ energy (aP c χ) ψ u s := by
    intro s hs0 hsa
    obtain ⟨hp, hq⟩ := hpq s hs0 hsa
    have hpos := aP_pos_of_neg hp hq
    unfold energy
    have h1 := div_nonneg (sq_nonneg (u s)) hpos.le
    have h2 := mul_nonneg hpos.le (sq_nonneg (ψ s))
    constructor <;> linarith
  -- the cut points `s_v = a − Θl < s₋ = a − θl < a`
  have hsv0 : 0 < a - Θ * airyL c a := by linarith
  have hsm0 : 0 < a - θ * airyL c a := by linarith
  have hsva : a - Θ * airyL c a < a := by linarith [mul_pos hΘ hl]
  have hsma : a - θ * airyL c a < a := by linarith [mul_pos hθ hl]
  have hθla : θ * airyL c a ≤ a := by linarith
  -- (1) the window and (2) the crossing
  have h1 := crossing_window_mass_airy hc ha ha1 hχ hθ.le hθ6.le hθla
    (fun t ht => hψ t (hsub _ _ hsm0.le le_rfl ht)) (fun t ht => hu t (hsub _ _ hsm0.le le_rfl ht)) hψa hua
  have h2 := turning_crossing_airy hc ha ha1 hχ hθ.le hθ6.le hθla
    (fun t ht => hψ t (hsub _ _ hsm0.le le_rfl ht)) (fun t ht => hu t (hsub _ _ hsm0.le le_rfl ht)) hψa hua
  have h2sq : (1 - θ ^ 3 / 6) ^ 2 * ψ a ^ 2 ≤ ψ (a - θ * airyL c a) ^ 2 := by
    have h0 : 0 ≤ (1 - θ ^ 3 / 6) * ψ a := mul_nonneg (by linarith) hψa
    have := pow_le_pow_left₀ h0 h2 2
    rwa [mul_pow] at this
  -- (3) the energy at `s₋`
  have haPm := aP_airy hc ha ha1 hχ hθ.le hθla
  obtain ⟨hEm, hEm0⟩ := henergy _ hsm0.le hsma
  obtain ⟨-, hEv0⟩ := henergy _ hsv0.le hsva
  -- (4) the rates and the transport ratios
  have hym : 0 < θ * (1 - airyEps c a * θ) := mul_pos hθ (by linarith)
  have hyv : θ * (1 - airyEps c a * θ) ≤ Θ * (1 - airyEps c a * Θ) := by
    nlinarith [mul_pos (sub_pos.2 hθΘ)
      (by linarith : (0 : ℝ) < 1 - airyEps c a * Θ - airyEps c a * θ)]
  have hwm := wP_le_Wair hc ha ha1 hχ hθ (by linarith : θ * airyL c a < a)
  have hwv := wP_le_Wair hc ha ha1 hχ hΘ hΘl
  have hWv := Wair_anti hg.le hym hyv
  obtain ⟨hpm, hqm⟩ := hpq _ hsm0.le hsma
  obtain ⟨hpv, hqv⟩ := hpq _ hsv0.le hsva
  have hw0m := wP_nonneg_of_neg hsm0.le hpm hqm
  have hw0v := wP_nonneg_of_neg hsv0.le hpv hqv
  have hRm0 : 0 < Rcorr (Wair (airyG c a) (θ * (1 - airyEps c a * θ))) :=
    Rcorr_pos (by linarith [Wair_pos hg.le hym]) hW
  have hRv0 : 0 < Rcorr (Wair (airyG c a) (Θ * (1 - airyEps c a * Θ))) :=
    Rcorr_pos (by linarith [Wair_pos hg.le (hym.trans_le hyv)]) (by linarith)
  have hRm := Rcorr_anti (by linarith) hwm
  have hRv := Rcorr_anti (by linarith) hwv
  -- (5) the transport `R₋E(s₋) ≤ E(s_v)`
  have hT := (angular_transport hc hχc hsv0.le (by linarith : a - Θ * airyL c a ≤ a - θ * airyL c a)
    (hsq _ hsm0.le hsma) (fun t ht => hψ t (hsub _ _ hsv0.le hsma.le ht))
    (fun t ht => hu t (hsub _ _ hsv0.le hsma.le ht)) (by linarith)).1
  have h5 := (mul_le_mul_of_nonneg_right hRm hEm0).trans hT
  -- (6) the angular virial on `[0, s_v]`
  have hV := angular_virial hc hχc hsv0.le (hsq _ hsv0.le hsva)
    (fun t ht => hψ t (hsub _ _ le_rfl hsva.le ht)) (fun t ht => hu t (hsub _ _ le_rfl hsva.le ht)) hu0
    (by linarith) hRv0 hRv
  have hK := ellK_sub_le hc ha ha1 hχ (mul_pos hΘ hl) hΘl.le
  rw [Lambda_airy hc ha ha1 hΘ (by linarith)] at hK
  have hQ := cQ_airy hc ha ha1 hχ hΘ (by linarith)
  have hQpos : 0 < χ - c ^ 2 * (a - Θ * airyL c a) ^ 2 := by linarith [hsq _ hsv0.le hsva]
  -- (8) the split of `∫₀^a` at `s_v` and `s₋`
  have hs1 := integral_add_adjacent_intervals (hII 0 _ le_rfl hsv0.le hsva.le)
    (hII _ _ hsv0.le (by linarith : a - Θ * airyL c a ≤ a - θ * airyL c a) hsma.le)
  have hs2 := integral_add_adjacent_intervals (hII 0 _ le_rfl hsm0.le hsma.le)
    (hII _ a hsm0.le hsma.le le_rfl)
  have hmid := hInn (a - Θ * airyL c a) (a - θ * airyL c a) (by linarith)
  have hlow := hInn 0 (a - Θ * airyL c a) hsv0.le
  -- abbreviations
  set l := airyL c a with hldef
  set g := airyG c a with hgdef
  set ε := airyEps c a with hεdef
  set sv := a - Θ * l with hsvdef
  set sm := a - θ * l with hsmdef
  set ym := θ * (1 - ε * θ) with hymdef
  set Rv := Rcorr (Wair g (Θ * (1 - ε * Θ))) with hRvdef
  set Rm := Rcorr (Wair g ym) with hRmdef
  set Q := χ - c ^ 2 * sv ^ 2 with hQdef
  set E := energy (aP c χ) ψ u with hEdef
  set Ia := ∫ t in (0 : ℝ)..sv, 1 / aP c χ t with hIadef
  have hκ : 0 < 1 - ε * Θ := by linarith
  -- (6') the bracket is at least `K − β`
  have e : c * ((1 + Rv) / (2 * Rv ^ 2 * Q))
      = (1 + Rv) * √g / (4 * a * Rv ^ 2 * (1 - ε * Θ) * Θ) := by
    rw [show c * ((1 + Rv) / (2 * Rv ^ 2 * Q)) = (1 + Rv) / (2 * Rv ^ 2) * (c / Q) by
      rw [div_mul_div_comm, mul_div_assoc', mul_comm c], hQ,
      div_mul_div_comm]
    congr 1; ring
  have hβ : betaf g a ε Θ = √(g * Θ / (1 - ε * Θ)) / a
      + (1 + Rv) * √g / (4 * a * Rv ^ 2 * (1 - ε * Θ) * Θ) := rfl
  have hbr : ellK c χ - betaf g a ε Θ ≤ c * (Ia - (1 + Rv) / (2 * Rv ^ 2 * Q)) := by
    have e7 : c * (Ia - (1 + Rv) / (2 * Rv ^ 2 * Q)) = c * Ia - c * ((1 + Rv) / (2 * Rv ^ 2 * Q)) := by
      ring
    rw [hβ, e7, e]; linarith [hK]
  have hP0 : 0 ≤ Rv * E sv / 2 := by positivity
  have h6 : Rv * E sv / 2 * (ellK c χ - betaf g a ε Θ) ≤ c * ∫ t in (0 : ℝ)..sv, ψ t ^ 2 := by
    have f1 := mul_le_mul_of_nonneg_left hbr hP0
    have f2 := mul_le_mul_of_nonneg_left hV hc.le
    have e1 : Rv * E sv / 2 * (c * (Ia - (1 + Rv) / (2 * Rv ^ 2 * Q)))
        = c * (Rv * E sv / 2 * (Ia - (1 + Rv) / (2 * Rv ^ 2 * Q))) := by ring
    linarith
  -- (7) the transported energy is at least `D₂ψ(a)²`
  have h7 : D2f g a ε θ Θ * ψ a ^ 2 ≤ Rv * E sv / 2 := by
    have hA0 : 0 ≤ a / g * √(ym * (1 + g * ym)) := by positivity
    have hD2 : D2f g a ε θ Θ = Rv * Rm * (1 - θ ^ 3 / 6) ^ 2 * (a / g * √(ym * (1 + g * ym))) := rfl
    have f1 := mul_le_mul_of_nonneg_left h2sq
      (by positivity : 0 ≤ Rv * Rm * (a / g * √(ym * (1 + g * ym))))
    have f2 := mul_le_mul_of_nonneg_left hEm (by positivity : 0 ≤ Rv * Rm / 2)
    have f3 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ Rv / 2)
    rw [haPm] at f2
    have e2 : Rv * Rm / 2 * (2 * a / g * √(ym * (1 + g * ym)) * ψ sm ^ 2)
        = Rv * Rm * (a / g * √(ym * (1 + g * ym))) * ψ sm ^ 2 := by ring
    have e3 : D2f g a ε θ Θ * ψ a ^ 2
        = Rv * Rm * (a / g * √(ym * (1 + g * ym))) * ((1 - θ ^ 3 / 6) ^ 2 * ψ a ^ 2) := by
      rw [hD2]; ring
    have e4 : Rv / 2 * (Rm * E sm) = Rv * Rm / 2 * E sm := by ring
    have e5 : Rv / 2 * E sv = Rv * E sv / 2 := by ring
    linarith
  have h8 : D2f g a ε θ Θ * ψ a ^ 2 * max 0 (ellK c χ - betaf g a ε Θ)
      ≤ c * ∫ t in (0 : ℝ)..sv, ψ t ^ 2 := by
    rcases le_total (ellK c χ - betaf g a ε Θ) 0 with h | h
    · rw [max_eq_left h, mul_zero]; exact mul_nonneg hc.le hlow
    · rw [max_eq_right h]
      exact (mul_le_mul_of_nonneg_right h7 h).trans h6
  have hD1 : D1f g θ = mth θ / √g := rfl
  have e6 : ψ a ^ 2 * (D1f g θ + D2f g a ε θ Θ * max 0 (ellK c χ - betaf g a ε Θ))
      = mth θ / √g * ψ a ^ 2 + D2f g a ε θ Θ * ψ a ^ 2 * max 0 (ellK c χ - betaf g a ε Θ) := by
    rw [hD1]; ring
  rw [e6, ← hs2, ← hs1, mul_add, mul_add]
  linarith [mul_nonneg hc.le hmid]

/-- `K + α ≤ max((α + β)/D₁, 1/D₂)·(D₁ + D₂(K − β)₊)` for `D₁, D₂ > 0`. -/
theorem add_le_max_mul {K α β D₁ D₂ : ℝ} (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) :
    K + α ≤ max ((α + β) / D₁) (1 / D₂) * (D₁ + D₂ * max 0 (K - β)) := by
  set T := max ((α + β) / D₁) (1 / D₂)
  set M := max 0 (K - β)
  have h1 : (α + β) / D₁ ≤ T := le_max_left _ _
  have h2 : 1 / D₂ ≤ T := le_max_right _ _
  have hM : 0 ≤ M := le_max_left _ _
  have hK : K - β ≤ M := le_max_right _ _
  have e1 : α + β ≤ T * D₁ := (div_le_iff₀ hD₁).mp h1
  have e2 : 1 ≤ T * D₂ := by rw [div_le_iff₀ hD₂] at h2; exact h2
  have e3 : M ≤ T * D₂ * M := le_mul_of_one_le_left hM e2
  have e4 : T * (D₁ + D₂ * M) = T * D₁ + T * D₂ * M := by ring
  linarith

/-- **Plunge law P2♭ in Airy units**: for an even rung `g ≢ 0` with `psi c g = μ g`, `c ≥ 80`,
`c² − χ ≥ 5c`, `χ = c²a²`, `1 − λ ≤ (11/20)max{T₁, T₂}e^{−2Φ_C(Z(a))}`, `S = (c² − χ)/c`. -/
theorem plunge_P2flat_airy {g g₁ g₂ : ℝ → ℝ} {c χ μ a θ Θ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hD : 5 * c ≤ c ^ 2 - χ)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s)
    (ha : 0 < a) (hχ : χ = c ^ 2 * a ^ 2) (hθ : 0 < θ) (hθΘ : θ < Θ) (hθ6 : θ ^ 3 < 6)
    (hΘε : airyEps c a * Θ < 1 / 2) (hW : Wair (airyG c a) (θ * (1 - airyEps c a * θ)) < 2) :
    1 - c / (2 * π) * μ ^ 2
      ≤ 11 / 20 * max (T1f ((c ^ 2 - χ) / c) (airyG c a) a (airyEps c a) θ Θ)
          (T2f (airyG c a) a (airyEps c a) θ Θ) * Real.exp (-(2 * PhiC (forbZ c χ a))) := by
  have hc0 : 0 < c := by linarith
  have hD0 : 0 < c ^ 2 - χ := by linarith
  have hχc : χ < c ^ 2 := by linarith
  have hχ0 : 0 ≤ χ := by rw [hχ]; positivity
  have hc2 : 0 < c ^ 2 := by positivity
  have ha1 : a < 1 := by
    have h : a ^ 2 < 1 := by
      have : c ^ 2 * a ^ 2 < c ^ 2 * 1 := by rw [← hχ]; linarith
      exact lt_of_mul_lt_mul_left this hc2.le
    nlinarith
  have hsa : √χ / c = a := by
    rw [hχ, sqrt_mul (by positivity), sqrt_sq hc0.le, sqrt_sq ha.le]; field_simp
  have hgc := airyG_pos hc0 ha ha1
  have hεc := airyEps_pos hc0 ha ha1
  obtain ⟨-, hu, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hψf := rung_system_forbidden hg hg₁ hg₂c hang
  have hu1 : rungU c g 1 = 0 := by unfold rungU pP; simp
  have hu0 := rungU_zero c g
  have h1 := psi_one_ne_zero hc0 hg hg₁ hg₂c hang heven hg0
  have hψI : ∀ t ∈ Icc 0 a, HasDerivAt (psi c g) (rungU c g t / pP t) t := fun t ht =>
    hψf t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have huI : ∀ t ∈ Icc 0 a, HasDerivAt (rungU c g) (-(qP c χ t * psi c g t)) t := fun t _ => hu t
  have hψE : ∀ s ∈ Ico a 1, HasDerivAt (psi c g) (rungU c g s / pP s) s := fun s hs =>
    hψf s ⟨by linarith [hs.1], hs.2⟩
  have huE : ∀ s ∈ Icc a 1, HasDerivAt (rungU c g) (-(qP c χ s * psi c g s)) s := fun s _ => hu s
  have hq : ∀ s ∈ Icc a 1, 0 ≤ qP c χ s := fun s hs => by
    have h2 : a ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ ha.le hs.1 2
    unfold qP; rw [hχ]; nlinarith [mul_le_mul_of_nonneg_left h2 hc2.le]
  have haI : a ∈ Icc a 1 := ⟨le_rfl, ha1.le⟩
  set B := D1f (airyG c a) θ + D2f (airyG c a) a (airyEps c a) θ Θ
    * max 0 (ellK c χ - betaf (airyG c a) a (airyEps c a) Θ) with hBdef
  -- the two-zone mass, with the sign of `ψ(1)` normalised
  have hTZ : psi c g a ^ 2 * B ≤ c * ∫ t in (0 : ℝ)..a, psi c g t ^ 2 := by
    rcases lt_or_gt_of_ne h1 with hneg | hpos
    · have hψn : ∀ s ∈ Ico a 1, HasDerivAt (fun t => -psi c g t) (-rungU c g s / pP s) s :=
        fun s hs => (hψE s hs).neg.congr_deriv (neg_div _ _).symm
      have hun : ∀ s, HasDerivAt (fun t => -rungU c g t) (-(qP c χ s * -psi c g s)) s :=
        fun s => (hu s).neg.congr_deriv (by ring)
      have hE := edge_le_of_forbidden (ψ := fun t => -psi c g t) (u := fun t => -rungU c g t)
        ha.le ha1 hψn hψc.neg.continuousOn (fun s _ => hun s) (by simp [hu1]) hq (by simpa using hneg)
        a haI
      have h := two_zone (ψ := fun t => -psi c g t) (u := fun t => -rungU c g t) hc0 ha ha1 hχ hθ hθΘ
        hθ6 hΘε hW (fun t ht => (hψI t ht).neg.congr_deriv (neg_div _ _).symm) (fun t _ => hun t)
        (by simp [hu0]) (show 0 ≤ -psi c g a by have hE1 : -psi c g 1 ≤ -psi c g a := hE.1; linarith)
        hE.2
      simp only [neg_sq] at h
      exact h
    · have hE := edge_le_of_forbidden ha.le ha1 hψE hψc.continuousOn huE hu1 hq hpos a haI
      exact two_zone hc0 ha ha1 hχ hθ hθΘ hθ6 hΘε hW hψI huI hu0 (by linarith [hE.1]) hE.2
  -- the forbidden growth `ψ(1)² ≤ ψ(a)²e^{−2Φ}`
  have hG := forbidden_growth_sq hc0 hχ0 hχc hg hg₁ hg₂c hang (s := √χ / c)
    ⟨le_rfl, by rw [hsa]; exact ha1.le⟩
  rw [hsa] at hG
  set e := Real.exp (-(2 * PhiC (forbZ c χ a))) with hedef
  have hee : Real.exp (2 * PhiC (forbZ c χ a)) * e = 1 := by
    rw [hedef, ← Real.exp_add]; simp
  have hP1 : 0 < psi c g 1 ^ 2 := by positivity
  have hG' : psi c g 1 ^ 2 ≤ psi c g a ^ 2 * e := by
    have := mul_le_mul_of_nonneg_right hG (Real.exp_pos (-(2 * PhiC (forbZ c χ a)))).le
    rw [← hedef, mul_assoc, hee, mul_one] at this
    exact this
  have hPa : 0 < psi c g a ^ 2 := lt_of_lt_of_le
    (mul_pos hP1 (Real.exp_pos _)) hG
  -- the denominators and the ratios
  have hD1 := D1f_pos hgc hθ hθ6
  have hD2 := D2f_pos hgc ha hεc.le hθ hθΘ hθ6 hΘε hW
  have hB : 0 < B := by
    have : 0 ≤ D2f (airyG c a) a (airyEps c a) θ Θ
        * max 0 (ellK c χ - betaf (airyG c a) a (airyEps c a) Θ) :=
      mul_nonneg hD2.le (le_max_left _ _)
    rw [hBdef]; linarith
  have hT1 : T1f ((c ^ 2 - χ) / c) (airyG c a) a (airyEps c a) θ Θ
      = (c / (2 * (c ^ 2 - χ)) + betaf (airyG c a) a (airyEps c a) Θ) / D1f (airyG c a) θ := by
    unfold T1f
    rw [show 1 / (2 * ((c ^ 2 - χ) / c)) = c / (2 * (c ^ 2 - χ)) by field_simp]
  have hT2 : T2f (airyG c a) a (airyEps c a) θ Θ = 1 / D2f (airyG c a) a (airyEps c a) θ Θ := rfl
  rw [hT1, hT2]
  set T := max ((c / (2 * (c ^ 2 - χ)) + betaf (airyG c a) a (airyEps c a) Θ) / D1f (airyG c a) θ)
    (1 / D2f (airyG c a) a (airyEps c a) θ Θ) with hTdef
  have hAM : ellK c χ + c / (2 * (c ^ 2 - χ)) ≤ T * B := add_le_max_mul hD1 hD2
  have hT0 : 0 < T := lt_of_lt_of_le (one_div_pos.mpr hD2) (le_max_right _ _)
  have he0 : 0 < e := Real.exp_pos _
  -- the low mass `c∫₀¹ψ² ≥ c∫₀^aψ²`
  have hψ2c : Continuous fun t => psi c g t ^ 2 := hψc.pow 2
  have hsplit := integral_add_adjacent_intervals (hψ2c.intervalIntegrable (μ := volume) 0 a)
    (hψ2c.intervalIntegrable a 1)
  have hrest : 0 ≤ ∫ t in a..1, psi c g t ^ 2 :=
    intervalIntegral.integral_nonneg ha1.le fun t _ => sq_nonneg _
  set I := c * ∫ x in (0 : ℝ)..1, psi c g x ^ 2 with hIdef
  have hIa : c * ∫ t in (0 : ℝ)..a, psi c g t ^ 2 ≤ I := by
    rw [hIdef, ← hsplit, mul_add]; linarith [mul_nonneg hc0.le hrest]
  have hI : 0 < I := lt_of_lt_of_le (mul_pos hPa hB) (hTZ.trans hIa)
  have hR := radial_frame hg hg₁ hg₂c hang hc hχ0 hD heven hμ
  rw [← hIdef] at hR
  have f1 := mul_le_mul_of_nonneg_right hAM hP1.le
  have f2 := mul_le_mul_of_nonneg_left hG' (mul_pos hT0 hB).le
  have f3 := mul_le_mul_of_nonneg_left (hTZ.trans hIa) (mul_pos hT0 he0).le
  have key : (1 - c / (2 * π) * μ ^ 2) * I ≤ (11 / 20 * T * e) * I := by
    have e1 : T * B * (psi c g a ^ 2 * e) = T * e * (psi c g a ^ 2 * B) := by ring
    nlinarith
  exact le_of_mul_le_mul_right key hI

/-- **Plunge law P2♭, uniform**: for `c ≥ 80` and `5c ≤ c² − χ ≤ c²/4`,
`1 − λ ≤ (11/20)max{T̄₁, T̄₂}e^{−2Φ_C(π(c² − χ)/(4c))}`. -/
theorem plunge_P2flat_Tbar {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hD : 5 * c ≤ c ^ 2 - χ) (hD4 : 4 * (c ^ 2 - χ) ≤ c ^ 2)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    1 - c / (2 * π) * μ ^ 2
      ≤ 11 / 20 * max T1bar T2bar * Real.exp (-(2 * PhiC (π * (c ^ 2 - χ) / (4 * c)))) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hχpos : 0 < χ := by nlinarith
  have hχc : χ < c ^ 2 := by linarith
  have hexp := exp_neg_two_PhiC_forbZ_le hc0 hχpos.le hχc
  set a := √χ / c with hadef
  have ha : 0 < a := div_pos (sqrt_pos.2 hχpos) hc0
  have hχa : χ = c ^ 2 * a ^ 2 := by
    rw [hadef, div_pow, sq_sqrt hχpos.le]; field_simp
  have ha1 : a < 1 := by
    rw [hadef, div_lt_one hc0, Real.sqrt_lt' hc0]; exact hχc
  have hS : c * (1 - a ^ 2) = (c ^ 2 - χ) / c := by
    rw [hχa]; field_simp
  have hS5 : 5 ≤ c * (1 - a ^ 2) := by
    rw [hS, le_div_iff₀ hc0]; linarith
  have hS4 : 4 * (1 - a ^ 2) ≤ 1 := by
    have e : 1 - a ^ 2 = (c ^ 2 - χ) / c ^ 2 := by rw [hχa]; field_simp
    rw [e, ← mul_div_assoc, div_le_one hc2]; linarith
  obtain ⟨hε4, hW1, hT1, hT2⟩ := airy_worst_case hc ha ha1 hS5 hS4
  have hP := plunge_P2flat_airy (θ := 1) (Θ := 4) hg hg₁ hg₂c hang hc hD heven hg0 hμ ha hχa
    one_pos (by norm_num) (by norm_num) hε4 hW1
  rw [← hS] at hP
  have hD2 := D2f_pos (airyG_pos hc0 ha ha1) ha (airyEps_pos hc0 ha ha1).le one_pos
    (by norm_num : (1 : ℝ) < 4) (by norm_num) hε4 hW1
  have hM0 : 0 ≤ max (T1f (c * (1 - a ^ 2)) (airyG c a) a (airyEps c a) 1 4)
      (T2f (airyG c a) a (airyEps c a) 1 4) :=
    le_trans (by unfold T2f; positivity) (le_max_right _ _)
  have hMM := max_le_max hT1 hT2
  refine hP.trans (mul_le_mul (mul_le_mul_of_nonneg_left hMM (by norm_num)) hexp
    (Real.exp_pos _).le (by nlinarith))

end Cvs.Prolate.PlungeLawTwoZone
