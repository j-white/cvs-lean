import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanFloorShortExplicit
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.ProlateEnergyFromFarEnd
import Cvs.Prolate.RungTailMassEnergyAtTwo

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Hilbert loss of a rung against its mass, explicitly

On `[ξ₀, b]` the energy lies between `E(b) κ₀` and `E(b) κ₁`, `κ₀ = (1 − w̄/2)/(1 + w̄/2)`, `κ₁ = 1/(1 − w̄/2)²`,
`w̄ = 2ξ₀/(c(ξ₀² − 1))` (Cvs.Prolate.ProlateEnergyFromFarEnd, Cvs.Prolate.Gram.RungGramFloorAtInfinity), so the arccos mass law (Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw) gives `∫₁ᵇ ψ² ≥ E(b)(κ₀ Δ/(2c) −
κ₁/(2c²(ξ₀² − 1)))`, `Δ = arccos(1/b) − arccos(1/ξ₀)`, and the Hilbert loss `(π/D)(b/√(b² − 1)) E(b)` is at most
`θ_H` times the mass; the prolate span floor at short `b` then has hypotheses only on the rungs.
-/

namespace Cvs.L2a.RungHilbertLossMass

open Real Finset Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.TreeBoundInverseScaling Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorPositive Cvs.Prolate.RungTailMassEnergyAtTwo Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.SpanFloorShortExplicit

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The rate bound `w̄ = 2ξ₀/(c(ξ₀² − 1))` beyond `ξ₀`. -/
noncomputable def wbar (c ξ₀ : ℝ) : ℝ := 2 * ξ₀ / (c * (ξ₀ ^ 2 - 1))
/-- The energy factors from the far end. -/
noncomputable def κ₀ (c ξ₀ : ℝ) : ℝ := (1 - wbar c ξ₀ / 2) / (1 + wbar c ξ₀ / 2)
noncomputable def κ₁ (c ξ₀ : ℝ) : ℝ := 1 / (1 - wbar c ξ₀ / 2) ^ 2
/-- The mass coefficient `κ₀ Δ/(2c) − κ₁/(2c²(ξ₀² − 1))`. -/
noncomputable def massCoeff (c b ξ₀ : ℝ) : ℝ :=
  κ₀ c ξ₀ * (arccos (1 / b) - arccos (1 / ξ₀)) / (2 * c) - κ₁ c ξ₀ / (2 * c ^ 2 * (ξ₀ ^ 2 - 1))
/-- The Hilbert loss against the mass, `θ_H = (π/D)(b/√(b² − 1))/massCoeff`. -/
noncomputable def θH (c D b ξ₀ : ℝ) : ℝ := Real.pi / D * (b / √(b ^ 2 - 1)) / massCoeff c b ξ₀

/-- `w(ξ) ≤ w̄` for `ξ ≥ ξ₀ > 1`. -/
theorem wP_le_wbar {c χ ξ₀ ξ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (h1 : 1 < ξ₀) (hξ : ξ₀ ≤ ξ) :
    wP c χ ξ ≤ wbar c ξ₀ := by
  have hξ1 : 1 < ξ := lt_of_lt_of_le h1 hξ
  refine (wP_le_far hξ1 hc hχ0 hχc).trans ?_
  unfold wbar pP
  have h0 : 0 < ξ ^ 2 - 1 := by nlinarith
  have h0' : 0 < ξ₀ ^ 2 - 1 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ξ - ξ₀) (by positivity : (0:ℝ) ≤ 1 + ξ * ξ₀)]

/-- **The energy on `[ξ₀, b]` from the far end**: `E(b) κ₀ ≤ E(ξ) ≤ E(b) κ₁`. -/
theorem energy_between {c χ ξ₀ b : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (h1 : 1 < ξ₀)
    (hb : ξ₀ ≤ b) (hw : wbar c ξ₀ < 2)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) :
    ∀ ξ ∈ Icc ξ₀ b, energy (aP c χ) ψ u b * κ₀ c ξ₀ ≤ energy (aP c χ) ψ u ξ ∧
      energy (aP c χ) ψ u ξ ≤ energy (aP c χ) ψ u b * κ₁ c ξ₀ := by
  intro ξ hξ
  have hc2 : 0 < c ^ 2 := by positivity
  have hξ1 : 1 < ξ := lt_of_lt_of_le h1 hξ.1
  have hwξ : wP c χ ξ ≤ wbar c ξ₀ := wP_le_wbar hc hχ0 hχc h1 hξ.1
  have hwξ0 : 0 ≤ wP c χ ξ := (wP_pos hξ1 hc2 hχc).le
  have hwb0 : 0 ≤ wP c χ b := (wP_pos (lt_of_lt_of_le h1 hb) hc2 hχc).le
  have hW : wP c χ ξ < 2 := lt_of_le_of_lt hwξ hw
  have hw0 : 0 ≤ wbar c ξ₀ := hwξ0.trans hwξ
  obtain ⟨hlo, hhi⟩ := Cvs.Prolate.ProlateEnergyFromFarEnd.prolate_energy_bounds_of_far (ξ₀ := ξ) (ξ₁ := b) hξ1 hξ.2 hc2 hχ0 hχc
    (fun t ht => hψ t (by linarith [ht.1])) (fun t _ => hu t) hW
  have hEb : 0 ≤ energy (aP c χ) ψ u b := energy_nonneg (lt_of_lt_of_le h1 hb) hc2 hχc
  constructor
  · -- `κ₀ ≤ (1 − w/2)/(1 + w/2)` since `w ≤ w̄`
    have hf : κ₀ c ξ₀ ≤ (1 - wP c χ ξ / 2) / (1 + wP c χ ξ / 2) := by
      unfold κ₀
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have := mul_le_mul_of_nonneg_left hf hEb
    have e : energy (aP c χ) ψ u b * (1 - wP c χ ξ / 2) / (1 + wP c χ ξ / 2)
        = energy (aP c χ) ψ u b * ((1 - wP c χ ξ / 2) / (1 + wP c χ ξ / 2)) := by ring
    linarith
  · -- `1/(1 − w/2)² ≤ κ₁` and `1 − (w(b)/2)² ≤ 1`
    have h1w : 0 < 1 - wbar c ξ₀ / 2 := by linarith
    have h2 : (1 - wbar c ξ₀ / 2) ^ 2 ≤ (1 - wP c χ ξ / 2) ^ 2 := by
      apply pow_le_pow_left₀ h1w.le; linarith
    have h3 : 1 - (wP c χ b / 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (wP c χ b / 2)]
    have hfac : (1 - (wP c χ b / 2) ^ 2) / (1 - wP c χ ξ / 2) ^ 2 ≤ κ₁ c ξ₀ := by
      unfold κ₁
      calc (1 - (wP c χ b / 2) ^ 2) / (1 - wP c χ ξ / 2) ^ 2 ≤ 1 / (1 - wP c χ ξ / 2) ^ 2 :=
            div_le_div_of_nonneg_right h3 (by positivity)
        _ ≤ 1 / (1 - wbar c ξ₀ / 2) ^ 2 := div_le_div_of_nonneg_left zero_le_one (by positivity) h2
    have := mul_le_mul_of_nonneg_left hfac hEb
    have e : energy (aP c χ) ψ u b * (1 - (wP c χ b / 2) ^ 2) / (1 - wP c χ ξ / 2) ^ 2
        = energy (aP c χ) ψ u b * ((1 - (wP c χ b / 2) ^ 2) / (1 - wP c χ ξ / 2) ^ 2) := by ring
    linarith

/-- **The mass on `[1, b]` against the energy at `b`**: `E(b) massCoeff ≤ ∫₁ᵇ ψ²`. -/
theorem mass_ge_energy_b {c χ ξ₀ b : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (h1 : 1 < ξ₀)
    (hb : ξ₀ ≤ b) (hw : wbar c ξ₀ < 2)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hcont : Continuous ψ) :
    energy (aP c χ) ψ u b * massCoeff c b ξ₀ ≤ ∫ ξ in (1 : ℝ)..b, ψ ξ ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hEb : 0 ≤ energy (aP c χ) ψ u b := energy_nonneg (lt_of_lt_of_le h1 hb) hc2 hχc
  have hbet := energy_between hc hχ0 hχc h1 hb hw hψ hu
  have hκ₀ : 0 ≤ κ₀ c ξ₀ := by
    unfold κ₀
    have hw0 : 0 ≤ wbar c ξ₀ := by
      unfold wbar; have : 0 < ξ₀ ^ 2 - 1 := by nlinarith
      positivity
    apply div_nonneg <;> linarith
  have hmass := Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.prolate_mass_bounds (Gm := energy (aP c χ) ψ u b * κ₀ c ξ₀)
    (GM := energy (aP c χ) ψ u b * κ₁ c ξ₀) h1 hb hc hχ0 hχc (fun t ht => hψ t (by linarith [ht.1]))
    (fun t _ => hu t) (fun t ht => (hbet t ht).1) (fun t ht => (hbet t ht).2) (mul_nonneg hEb hκ₀)
  have hq : c ^ 2 * (ξ₀ ^ 2 - 1) ≤ qP c χ ξ₀ := by unfold qP; nlinarith
  have hξ2 : 0 < ξ₀ ^ 2 - 1 := by nlinarith
  have hκ₁ : 0 ≤ κ₁ c ξ₀ := by unfold κ₁; positivity
  have hGq : energy (aP c χ) ψ u b * κ₁ c ξ₀ / (2 * qP c χ ξ₀)
      ≤ energy (aP c χ) ψ u b * κ₁ c ξ₀ / (2 * c ^ 2 * (ξ₀ ^ 2 - 1)) :=
    div_le_div_of_nonneg_left (mul_nonneg hEb hκ₁) (by positivity) (by linarith)
  have hsplit : ∫ ξ in ξ₀..b, ψ ξ ^ 2 ≤ ∫ ξ in (1 : ℝ)..b, ψ ξ ^ 2 := by
    have hI : ∀ s t : ℝ, IntervalIntegrable (fun ξ => ψ ξ ^ 2) MeasureTheory.volume s t := fun s t =>
      (hcont.pow 2).intervalIntegrable s t
    rw [← integral_add_adjacent_intervals (hI 1 ξ₀) (hI ξ₀ b)]
    have : 0 ≤ ∫ ξ in (1 : ℝ)..ξ₀, ψ ξ ^ 2 := integral_nonneg h1.le fun ξ _ => sq_nonneg _
    linarith
  have e : energy (aP c χ) ψ u b * massCoeff c b ξ₀
      = energy (aP c χ) ψ u b * κ₀ c ξ₀ * (arccos (1 / b) - arccos (1 / ξ₀)) / (2 * c)
        - energy (aP c χ) ψ u b * κ₁ c ξ₀ / (2 * c ^ 2 * (ξ₀ ^ 2 - 1)) := by
    unfold massCoeff; ring
  rw [e]
  linarith [hmass.1, hGq, hsplit]

/-- **The Hilbert loss against the mass**: `(π/D)(b/√(b² − 1)) E(b) ≤ θ_H ∫₁ᵇ ψ²` when `massCoeff > 0`. -/
theorem hilbert_loss_le_mass {c χ ξ₀ b D : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (h1 : 1 < ξ₀) (hb : ξ₀ ≤ b) (hw : wbar c ξ₀ < 2) (hD : 0 < D) (hden : 0 < massCoeff c b ξ₀)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hcont : Continuous ψ) :
    Real.pi / D * (b / √(b ^ 2 - 1)) * energy (aP c χ) ψ u b ≤ θH c D b ξ₀ * ∫ ξ in (1 : ℝ)..b, ψ ξ ^ 2 := by
  have hm := mass_ge_energy_b hc hχ0 hχc h1 hb hw hψ hu hcont
  have hb1 : 1 < b := lt_of_lt_of_le h1 hb
  have hπ : 0 ≤ Real.pi / D * (b / √(b ^ 2 - 1)) := by
    have : 0 < b ^ 2 - 1 := by nlinarith
    positivity
  have hθ : 0 ≤ θH c D b ξ₀ := by unfold θH; exact div_nonneg hπ hden.le
  have e : Real.pi / D * (b / √(b ^ 2 - 1)) * energy (aP c χ) ψ u b
      = θH c D b ξ₀ * (energy (aP c χ) ψ u b * massCoeff c b ξ₀) := by
    unfold θH; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hm hθ

set_option maxHeartbeats 1600000 in
/-- **The prolate span floor at short `b`, for every large `c`, with hypotheses only on the rungs**:
`∫₁ᵇ (G + Σ_{m ≤ M} G(m·))² ≥ ((1 − max(s, 5/(6s)))(1 − θ_H) − (K/c + Λ)(1 + τ)) Σ a_i² ∫₁ᵇ ψ_i²`. -/
theorem span_floor_prolate_explicit {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ : ℝ} {M : ℕ} (N : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ)
    (hM : 2 ≤ M) (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c) (hc8 : 8 ≤ c) (hs : 0 < s) (hsmax : max s (5 / (6 * s)) ≤ 1)
    (hh : 0 < h) (hh' : h ≤ 1 / 5)
    (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20) (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 4 ≤ b)
    (hbM : 3 * M / 2 ≤ b)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hMpos : ∀ i, 0 < ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
    (hN₀ : 0 < ∑ i, a i ^ 2 * massB c (χ i) (g i) b)
    (hD : 0 < D) (hgap : ∀ i j, i ≠ j → D ≤ |χ i - χ j|)
    (hξ₀ : 1 < ξ₀) (hξ₀b : ξ₀ ≤ b) (hw : wbar c ξ₀ < 2) (hden : 0 < massCoeff c b ξ₀) :
    ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b))
        * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2
      ≤ ∫ θ in (1 : ℝ)..b, (Gk a χ (fun i => psi c (g i)) 0 θ
          + ∑ m ∈ Finset.Icc 2 M, Gk a χ (fun i => psi c (g i)) 0 (m * θ)) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hsys := fun i => rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)
  have hθ0 : 0 ≤ θH c D b ξ₀ := by
    unfold θH
    have : 0 < b ^ 2 - 1 := by nlinarith
    positivity
  have ht : ∀ i, Real.pi / D * (b / √(b ^ 2 - 1)) * energy (aP c (χ i)) (psi c (g i)) (rungU c (g i)) b
      ≤ θH c D b ξ₀ * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2 := fun i => by
    obtain ⟨hψi, hui, hci, -⟩ := hsys i
    exact hilbert_loss_le_mass hc0 (hχ0 i) (hχc i) hξ₀ hξ₀b hw hD hden hψi hui hci
  exact span_floor_prolate_const (θ := θH c D b ξ₀) N g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs
    hsmax hh hh' hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hθ0 ht

end Cvs.L2a.RungHilbertLossMass
