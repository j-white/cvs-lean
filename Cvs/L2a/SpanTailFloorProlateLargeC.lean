import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorPositive
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungTailMassEnergyAtTwo

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The span tail Gram floor for the prolate rungs, for every large `c`

For rungs whose energies at `ξ = 2` are comparable, `E_j(2) ≤ κ E_i(2)`, every tail bound is at most
`κ τ(c, b)` times every mass, `τ(c, b) = (Φ²/(c(b − 1)))/((1/Φ)(1/2 − 1/b)/(2c) − Φ/(6c²))` (Cvs.Prolate.RungTailMassEnergyAtTwo); so with
`(R + 1) κ τ ≤ m₀/4` the floor of Cvs.L2a.SpanTailFloorPositive holds: `∫₁ᵇ (G + Σ_m G(m·))² ≥ (m₀/4) Σ_i a_i² ∫₁ᵇ ψ_i²` for every
`c ≥ 2K/m₀`, `c ≥ 8`, `b ≥ 4`.
-/

namespace Cvs.L2a.SpanTailFloorProlateLargeC

open Real Finset Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.TreeBoundInverseScaling Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorPositive Cvs.Prolate.RungTailMassEnergyAtTwo

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The mass coefficient `D(c, b) = (1/Φ)(1/2 − 1/b)/(2c) − Φ/(6c²)` is positive for `c ≥ 8`, `b ≥ 4`. -/
theorem Dtail_pos {c b : ℝ} (hc : 8 ≤ c) (hb : 4 ≤ b) :
    0 < 1 / Φc c * (1 / 2 - 1 / b) / (2 * c) - Φc c / (6 * c ^ 2) := by
  have hΦ := Φc_pos (by linarith : (2:ℝ) ≤ c)
  have hΦle := Φc_le hc
  have hc0 : 0 < c := by linarith
  have h1 : 10 / 13 ≤ 1 / Φc c := by rw [div_le_div_iff₀ (by norm_num) hΦ]; linarith
  have hb' : 1 / 4 ≤ 1 / 2 - 1 / b := by
    have : 1 / b ≤ 1 / 4 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hA : 5 / (52 * c) ≤ 1 / Φc c * (1 / 2 - 1 / b) / (2 * c) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul h1 hb' (by norm_num) (by positivity)
    nlinarith
  have hB : Φc c / (6 * c ^ 2) ≤ 13 / (480 * c) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have : 13 / (480 * c) < 5 / (52 * c) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  linarith

/-- The tail-to-mass quotient `τ(c, b)`. -/
noncomputable def τtail (c b : ℝ) : ℝ :=
  Φc c ^ 2 / (c * (b - 1)) / (1 / Φc c * (1 / 2 - 1 / b) / (2 * c) - Φc c / (6 * c ^ 2))

theorem τtail_nonneg {c b : ℝ} (hc : 8 ≤ c) (hb : 4 ≤ b) : 0 ≤ τtail c b := by
  unfold τtail
  have := Dtail_pos hc hb
  have hc0 : 0 < c := by linarith
  have hb1 : 0 < b - 1 := by linarith
  positivity

/-- **A tail against a mass**: for two rungs with `E_j(2) ≤ κ E_i(2)`, the tail bound of `j` is at most
`κ τ(c, b)` times the mass of `i` on `[1, b]`. -/
theorem tail_le_mass_of_energy_ratio {c χi χj b κ : ℝ} {ψi ui ψj uj : ℝ → ℝ} (hc : 8 ≤ c) (hb : 4 ≤ b)
    (hχi0 : 0 ≤ χi) (hχic : χi < c ^ 2) (hχj0 : 0 ≤ χj) (hχjc : χj < c ^ 2)
    (hψi : ∀ ξ, 1 < ξ → HasDerivAt ψi (ui ξ / pP ξ) ξ) (hui : ∀ ξ, HasDerivAt ui (-(qP c χi ξ * ψi ξ)) ξ)
    (hci : Continuous ψi)
    (hψj : ∀ ξ, 1 < ξ → HasDerivAt ψj (uj ξ / pP ξ) ξ) (huj : ∀ ξ, HasDerivAt uj (-(qP c χj ξ * ψj ξ)) ξ)
    (hκ0 : 0 ≤ κ) (hE : energy (aP c χj) ψj uj 2 ≤ κ * energy (aP c χi) ψi ui 2) :
    energy (aP c χj) ψj uj b * (1 + wP c χj b / 2) / (1 - wP c χj b / 2) * exp (wP c χj b / (2 - wP c χj b))
        / (2 * c) * log ((b + 1) / (b - 1))
      ≤ κ * τtail c b * ∫ ξ in (1 : ℝ)..b, ψi ξ ^ 2 := by
  have hc2 : (2:ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hD := Dtail_pos hc hb
  have hT := tail_le_energy_two hc2 hχj0 hχjc hb hψj huj
  have hM := mass_ge_energy_two hc2 hχi0 hχic hb hψi hui hci
  have hEi : 0 ≤ energy (aP c χi) ψi ui 2 := energy_nonneg (by norm_num) (by positivity) hχic
  set D := 1 / Φc c * (1 / 2 - 1 / b) / (2 * c) - Φc c / (6 * c ^ 2) with hDdef
  set Q := Φc c ^ 2 / (c * (b - 1)) with hQdef
  have hQ0 : 0 ≤ Q := by
    have : 0 < b - 1 := by linarith
    rw [hQdef]; positivity
  have h1 : energy (aP c χj) ψj uj 2 * Q ≤ κ * energy (aP c χi) ψi ui 2 * Q := mul_le_mul_of_nonneg_right hE hQ0
  have e : κ * energy (aP c χi) ψi ui 2 * Q = κ * (Q / D) * (energy (aP c χi) ψi ui 2 * D) := by
    field_simp
  have h2 : κ * (Q / D) * (energy (aP c χi) ψi ui 2 * D) ≤ κ * (Q / D) * ∫ ξ in (1 : ℝ)..b, ψi ξ ^ 2 :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have eτ : τtail c b = Q / D := rfl
  have e0 : energy (aP c χj) ψj uj 2 * Φc c ^ 2 / (c * (b - 1)) = energy (aP c χj) ψj uj 2 * Q := by
    rw [hQdef]; ring
  rw [eτ]
  linarith [hT, h1, e, h2, e0]

set_option maxHeartbeats 800000 in
/-- **The span tail Gram floor for the prolate rungs, for every large `c`**: with energies at `2` comparable
(`E_j(2) ≤ κ E_i(2)`), `(R + 1) κ τ(c, b) ≤ m₀/4`, `c ≥ 8`, `b ≥ 4` and `c ≥ 2K/m₀`,
`∫₁ᵇ (G + Σ_{m ≤ M} G(m·))² ≥ (m₀/4) Σ_i a_i² ∫₁ᵇ ψ_i²`. -/
theorem span_floor_positive_prolate {c c₀ h h₂ hη b s ε δ μ₁ μ₂ κ : ℝ} {M : ℕ} (N : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ)
    (hM : 2 ≤ M) (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c) (hc8 : 8 ≤ c) (hs : 0 < s) (hh : 0 < h) (hh' : h ≤ 1 / 5)
    (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20) (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 4 ≤ b)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hMpos : ∀ i, 0 < ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
    (hN₀ : 0 < ∑ i, a i ^ 2 * massB c (χ i) (g i) b)
    (hm₀ : 0 < margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N)
    (hK : 2 * Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N
      / margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N ≤ c)
    (hκ0 : 0 ≤ κ)
    (hE : ∀ i j, energy (aP c (χ j)) (psi c (g j)) (rungU c (g j)) 2
      ≤ κ * energy (aP c (χ i)) (psi c (g i)) (rungU c (g i)) 2)
    (hτ : ((Fintype.card ι : ℝ) + 1) * (κ * τtail c b)
      ≤ margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N / 4) :
    margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N / 4
        * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2
      ≤ ∫ θ in (1 : ℝ)..b, (Gk a χ (fun i => psi c (g i)) 0 θ
          + ∑ m ∈ Finset.Icc 2 M, Gk a χ (fun i => psi c (g i)) 0 (m * θ)) ^ 2 := by
  have hsys := fun i => rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)
  have hT : ∀ i j, tailBound c (χ j) (g j) b ≤ κ * τtail c b * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2 := by
    intro i j
    obtain ⟨hψi, hui, hci, -⟩ := hsys i
    obtain ⟨hψj, huj, -, -⟩ := hsys j
    unfold tailBound
    exact tail_le_mass_of_energy_ratio hc8 hb (hχ0 i) (hχc i) (hχ0 j) (hχc j) hψi hui hci hψj huj hκ0 (hE i j)
  exact span_floor_positive (τ := κ * τtail c b) N g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hs hh hh'
    hh₂ hh₂' hη0 hη' (by linarith) hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hm₀ hK (mul_nonneg hκ0 (τtail_nonneg hc8 hb)) hT hτ

end Cvs.L2a.SpanTailFloorProlateLargeC
