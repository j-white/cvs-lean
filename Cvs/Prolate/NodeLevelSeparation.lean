import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.Gram.DirichletDualFloorShifted
import Cvs.Prolate.RegularSolutionChiVariation
import Cvs.Prolate.RegularSolutionDepthBound
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RegularSolutionEnergyComparability

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Level separation: two zeros of `ν ↦ y_ν(a)` (or of `ν ↦ U_ν(0)`) are `≥ π/(8c(1 + (1 + ν')/c²))` apart

A curve `(g, f)` turning with angular speed `(f'g − fg')/(f² + g²) ∈ (0, L]` needs time `π/(2L)` between two zeros of
`f` (eq-cpb Lemma 8(ii)–(iii)); for `(U_ν(a), c y_ν(a))` the speed is `c∫_a^1 y_ν²/(U² + c²y²)`, which Cvs.Prolate.RegularSolutionEnergyComparability bounds.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC)
open Cvs.Prolate.RegularSolutionChiVariation (regDot regUDot)

namespace Cvs.Prolate.NodeLevelSeparation
open Cvs.ZeroCounting

/-! ### The quarter turn -/

/-- **A quarter turn takes time**: if `0 < f'g − fg' ≤ L(f² + g²)` on `[σ, σ']` and `f(σ) = f(σ') = 0`, then
`π/2 ≤ L(σ' − σ)`. -/
theorem quarter_turn {f g f' g' : ℝ → ℝ} {σ σ' L : ℝ} (hσ : σ < σ')
    (hf : ∀ ν ∈ Icc σ σ', HasDerivAt f (f' ν) ν) (hg : ∀ ν ∈ Icc σ σ', HasDerivAt g (g' ν) ν)
    (hW : ∀ ν ∈ Icc σ σ', 0 < f' ν * g ν - f ν * g' ν)
    (hL : ∀ ν ∈ Icc σ σ', f' ν * g ν - f ν * g' ν ≤ L * (f ν ^ 2 + g ν ^ 2))
    (h0 : f σ = 0) (h1 : f σ' = 0) : π / 2 ≤ L * (σ' - σ) := by
  have hσI : σ ∈ Icc σ σ' := ⟨le_rfl, hσ.le⟩
  have hσ'I : σ' ∈ Icc σ σ' := ⟨hσ.le, le_rfl⟩
  have hgσ : g σ ≠ 0 := fun h => by have := hW σ hσI; rw [h, h0] at this; simp at this
  have hgc : ContinuousOn g (Icc σ σ') := fun ν hν => (hg ν hν).continuousAt.continuousWithinAt
  -- `g` vanishes somewhere on `[σ, σ']`
  have hex : ∃ ν ∈ Icc σ σ', g ν = 0 := by
    by_contra hne
    push Not at hne
    have hρ : ∀ ν ∈ Icc σ σ', HasDerivAt (fun ν => f ν / g ν)
        ((f' ν * g ν - f ν * g' ν) / g ν ^ 2) ν := fun ν hν => (hf ν hν).div (hg ν hν) (hne ν hν)
    have hm : StrictMonoOn (fun ν => f ν / g ν) (Icc σ σ') :=
      strictMonoOn_of_deriv_pos (convex_Icc σ σ')
        (fun ν hν => (hρ ν hν).continuousAt.continuousWithinAt)
        (fun ν hν => by
          rw [(hρ ν (interior_subset hν)).deriv]
          have := hne ν (interior_subset hν)
          exact div_pos (hW ν (interior_subset hν)) (by positivity))
    have := hm hσI hσ'I hσ
    simp [h0, h1] at this
  -- the first zero `ν₁` of `g`
  set Z := {ν ∈ Icc σ σ' | g ν = 0} with hZ
  have hZc : IsClosed Z := hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZne : Z.Nonempty := let ⟨ν, hν, h⟩ := hex; ⟨ν, hν, h⟩
  have hZb : BddBelow Z := ⟨σ, fun ν hν => hν.1.1⟩
  set ν₁ := sInf Z with hν₁
  have hν₁Z : ν₁ ∈ Z := hZc.csInf_mem hZne hZb
  have hν₁I : ν₁ ∈ Icc σ σ' := hν₁Z.1
  have hgν₁ : g ν₁ = 0 := hν₁Z.2
  have hσν₁ : σ < ν₁ := lt_of_le_of_ne hν₁I.1 fun h => hgσ (h ▸ hgν₁)
  have hne : ∀ ν ∈ Ico σ ν₁, g ν ≠ 0 := fun ν hν h0' =>
    absurd (csInf_le hZb ⟨⟨hν.1, hν.2.le.trans hν₁I.2⟩, h0'⟩) (not_le.mpr hν.2)
  have hfν₁ : f ν₁ ≠ 0 := fun h => by have := hW ν₁ hν₁I; rw [h, hgν₁] at this; simp at this
  have hL0 : 0 < L := by
    have h1' := hW σ hσI
    have h2' := hL σ hσI
    rw [h0] at h1' h2'
    have : 0 < L * (0 ^ 2 + g σ ^ 2) := lt_of_lt_of_le h1' h2'
    exact pos_of_mul_pos_left this (by positivity)
  -- on `[σ, ν)`, `ν < ν₁`, the angle `arctan(f/g)` grows at speed at most `L`
  have hθ : ∀ ν ∈ Icc σ ν₁, ν < ν₁ → ∀ μ ∈ Icc σ ν, HasDerivAt (fun μ => arctan (f μ / g μ))
      ((f' μ * g μ - f μ * g' μ) / (f μ ^ 2 + g μ ^ 2)) μ := by
    intro ν hν hνν₁ μ hμ
    have hμI : μ ∈ Icc σ σ' := ⟨hμ.1, hμ.2.trans (hνν₁.le.trans hν₁I.2)⟩
    have hgμ := hne μ ⟨hμ.1, lt_of_le_of_lt hμ.2 hνν₁⟩
    refine ((hf μ hμI).div (hg μ hμI) hgμ).arctan.congr_deriv ?_
    have : g μ ^ 2 ≠ 0 := pow_ne_zero 2 hgμ
    have : f μ ^ 2 + g μ ^ 2 ≠ 0 := by positivity
    simp only [Pi.div_apply]
    field_simp
    ring
  have hbound : ∀ ν ∈ Ioo σ ν₁, π / 2 - arctan (g ν / f ν) ≤ L * (ν - σ) := by
    intro ν hν
    have hνI : ν ∈ Icc σ ν₁ := ⟨hν.1.le, hν.2.le⟩
    have hm := Cvs.Prolate.RegularSolutionDepthBound.monotoneOn_of_deriv (a := σ) (b := ν)
      (f := fun μ => L * (μ - σ) - arctan (f μ / g μ))
      (fun μ hμ => ((((hasDerivAt_id μ).sub_const σ).const_mul L).sub (hθ ν hνI hν.2 μ hμ)))
      (fun μ hμ => by
        have hμI : μ ∈ Icc σ σ' := ⟨hμ.1, hμ.2.trans (hν.2.le.trans hν₁I.2)⟩
        have := hL μ hμI
        have hp : 0 < f μ ^ 2 + g μ ^ 2 := by
          have := hne μ ⟨hμ.1, lt_of_le_of_lt hμ.2 hν.2⟩; positivity
        have hq : (f' μ * g μ - f μ * g' μ) / (f μ ^ 2 + g μ ^ 2) ≤ L := (div_le_iff₀ hp).mpr this
        linarith)
    have hm' := hm ⟨le_rfl, hν.1.le⟩ ⟨hν.1.le, le_rfl⟩ hν.1.le
    simp only [sub_self, mul_zero, h0, zero_div, arctan_zero] at hm'
    -- the angle is positive, so `arctan(f/g) = π/2 − arctan(g/f)`
    have hpos : 0 < f ν / g ν := by
      have hsm : StrictMonoOn (fun μ => arctan (f μ / g μ)) (Icc σ ν) :=
        strictMonoOn_of_deriv_pos (convex_Icc σ ν)
          (fun μ hμ => (hθ ν hνI hν.2 μ hμ).continuousAt.continuousWithinAt)
          (fun μ hμ => by
            have hμ' := interior_subset hμ
            rw [(hθ ν hνI hν.2 μ hμ').deriv]
            have hμI : μ ∈ Icc σ σ' := ⟨hμ'.1, hμ'.2.trans (hν.2.le.trans hν₁I.2)⟩
            have := hne μ ⟨hμ'.1, lt_of_le_of_lt hμ'.2 hν.2⟩
            exact div_pos (hW μ hμI) (by positivity))
      have := hsm ⟨le_rfl, hν.1.le⟩ ⟨hν.1.le, le_rfl⟩ hν.1
      simp only [h0, zero_div, arctan_zero] at this
      exact Real.arctan_pos.mp this
    have hinv : arctan (f ν / g ν) = π / 2 - arctan (g ν / f ν) := by
      rw [← Real.arctan_inv_of_pos (by
        have : g ν / f ν = (f ν / g ν)⁻¹ := by rw [inv_div]
        rw [this]; exact inv_pos.mpr hpos), inv_div]
    linarith
  -- pass to the limit `ν → ν₁⁻`
  have hcont : ContinuousAt (fun ν => π / 2 - arctan (g ν / f ν) - L * (ν - σ)) ν₁ := by
    have hfc : ContinuousAt f ν₁ := (hf ν₁ hν₁I).continuousAt
    have hgc' : ContinuousAt g ν₁ := (hg ν₁ hν₁I).continuousAt
    exact (continuousAt_const.sub (continuous_arctan.continuousAt.comp (hgc'.div hfc hfν₁))).sub
      (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
  have hlim := hcont.continuousWithinAt (s := Iio ν₁) |>.tendsto
  have hle : π / 2 - arctan (g ν₁ / f ν₁) - L * (ν₁ - σ) ≤ 0 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hσν₁] with ν hν
    linarith [hbound ν hν]
  rw [hgν₁, zero_div, arctan_zero] at hle
  nlinarith [hν₁I.2]

/-! ### The angular speed of `(U_ν(b), c y_ν(b))` -/

/-- `ẏU − yU̇ = ∫_b^1 y²` at `b > −1` (`RegularSolutionChiVariation`'s mass identity). -/
theorem wronskian_dot {c ν b : ℝ} (hb : -1 < b) :
    regDot (sqC c) ν b * regU (sqC c) ν b - regSol (sqC c) ν b * regUDot (sqC c) ν b =
      ∫ t in b..1, regSol (sqC c) ν t ^ 2 := by
  have := Cvs.Prolate.RegularSolutionChiVariation.mass_identity (sqC c) ν hb
  rw [intervalIntegral.integral_symm] at this
  linarith

/-- **The speed bound**: for `0 ≤ b < 1`, `c > 0` and `c²b² ≤ ν ≤ ν'`,
`c∫_b^1 y_ν² ≤ 4c(1 + (1 + ν')/c²)(c²y_ν(b)² + U_ν(b)²)`. -/
theorem speed_le {c ν ν' b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) (hb1 : b < 1) (hν : c ^ 2 * b ^ 2 ≤ ν) (hνν' : ν ≤ ν') :
    c * ∫ t in b..1, regSol (sqC c) ν t ^ 2 ≤
      4 * c * (1 + (1 + ν') / c ^ 2) * ((c * regSol (sqC c) ν b) ^ 2 + regU (sqC c) ν b ^ 2) := by
  have h7 := Cvs.Prolate.RegularSolutionEnergyComparability.integral_sq_le (c := c) (σ := ν) hb hb1 hν
  have hν0 : 0 ≤ ν := (mul_nonneg (sq_nonneg c) (sq_nonneg b)).trans hν
  have hc2 : 0 < c ^ 2 := by positivity
  set y := regSol (sqC c) ν b
  set U := regU (sqC c) ν b
  have key : U ^ 2 + (1 + ν) * y ^ 2 ≤ (1 + (1 + ν') / c ^ 2) * ((c * y) ^ 2 + U ^ 2) := by
    have e : (1 + (1 + ν') / c ^ 2) * ((c * y) ^ 2 + U ^ 2) =
        U ^ 2 + c ^ 2 * y ^ 2 + (1 + ν') * y ^ 2 + (1 + ν') / c ^ 2 * U ^ 2 := by
      field_simp; ring
    rw [e]
    have : 0 ≤ (1 + ν') / c ^ 2 * U ^ 2 := by
      have : 0 ≤ 1 + ν' := by linarith
      positivity
    nlinarith [sq_nonneg y, sq_nonneg (c * y), mul_nonneg hc2.le (sq_nonneg y)]
  calc c * ∫ t in b..1, regSol (sqC c) ν t ^ 2 ≤ c * (4 * (U ^ 2 + (1 + ν) * y ^ 2)) :=
        mul_le_mul_of_nonneg_left h7 hc.le
    _ ≤ c * (4 * ((1 + (1 + ν') / c ^ 2) * ((c * y) ^ 2 + U ^ 2))) := by gcongr
    _ = _ := by ring

/-- **Dirichlet nodes are separated** (eq-cpb Lemma 8(ii)): two nodes `σ < σ'` of `y(a) = 0`, `0 ≤ a < 1`, `c > 0`,
have `π/2 ≤ 4c(1 + (1 + σ')/c²)(σ' − σ)`. -/
theorem dirichlet_sep {c a σ σ' : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (ha1 : a < 1) (hσ : σ < σ')
    (h : regSol (sqC c) σ a = 0) (h' : regSol (sqC c) σ' a = 0) :
    π / 2 ≤ 4 * c * (1 + (1 + σ') / c ^ 2) * (σ' - σ) := by
  have hlow := Cvs.Prolate.RegularSolutionEnergyComparability.lt_of_regSol_eq_zero (c := c) ha ha1.le h
  have ha' : -1 < a := by linarith
  refine quarter_turn (f := fun ν => c * regSol (sqC c) ν a) (g := fun ν => regU (sqC c) ν a)
    (f' := fun ν => c * regDot (sqC c) ν a) (g' := fun ν => regUDot (sqC c) ν a) hσ
    (fun ν _ => (Cvs.Prolate.RegularSolutionChiVariation.hasDerivAt_regSol_regDot (sqC c) ν a).const_mul c)
    (fun ν _ => Cvs.Prolate.RegularSolutionChiVariation.hasDerivAt_regU_chi (sqC c) ν ha') (fun ν hν => ?_) (fun ν hν => ?_)
    (by simp [h]) (by simp [h'])
  · have e : c * regDot (sqC c) ν a * regU (sqC c) ν a - c * regSol (sqC c) ν a * regUDot (sqC c) ν a =
        c * ∫ t in a..1, regSol (sqC c) ν t ^ 2 := by rw [← wronskian_dot ha']; ring
    rw [e]
    exact mul_pos hc (by simpa [Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass] using Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass_pos c ν ha' ha1)
  · have e : c * regDot (sqC c) ν a * regU (sqC c) ν a - c * regSol (sqC c) ν a * regUDot (sqC c) ν a =
        c * ∫ t in a..1, regSol (sqC c) ν t ^ 2 := by rw [← wronskian_dot ha']; ring
    rw [e]
    exact speed_le hc ha ha1 (hlow.le.trans hν.1) hν.2

/-- **Even levels are separated** (eq-cpb Lemma 8(iii)): two even levels `0 ≤ χ < χ'` of `c²t²`, `c > 0`, have
`π/2 ≤ 4c(1 + (1 + χ')/c²)(χ' − χ)`. -/
theorem even_sep {c χ χ' : ℝ} (hc : 0 < c) (h0 : 0 ≤ χ) (hχ : χ < χ') (he : χ ∈ Cvs.Prolate.EdgeCentreSign.evenSpec (sqC c))
    (he' : χ' ∈ Cvs.Prolate.EdgeCentreSign.evenSpec (sqC c)) : π / 2 ≤ 4 * c * (1 + (1 + χ') / c ^ 2) * (χ' - χ) := by
  have h0' : (-1 : ℝ) < 0 := by norm_num
  have e : ∀ ν, regUDot (sqC c) ν 0 * (-c * regSol (sqC c) ν 0) - regU (sqC c) ν 0 * (-c * regDot (sqC c) ν 0) =
      c * ∫ t in (0 : ℝ)..1, regSol (sqC c) ν t ^ 2 := fun ν => by rw [← wronskian_dot h0']; ring
  refine quarter_turn (f := fun ν => regU (sqC c) ν 0) (g := fun ν => -c * regSol (sqC c) ν 0)
    (f' := fun ν => regUDot (sqC c) ν 0) (g' := fun ν => -c * regDot (sqC c) ν 0) hχ
    (fun ν _ => Cvs.Prolate.RegularSolutionChiVariation.hasDerivAt_regU_chi (sqC c) ν h0')
    (fun ν _ => (Cvs.Prolate.RegularSolutionChiVariation.hasDerivAt_regSol_regDot (sqC c) ν 0).const_mul (-c)) (fun ν hν => ?_) (fun ν hν => ?_)
    he he'
  · rw [e]
    exact mul_pos hc (by simpa [Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass] using Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass_pos c ν h0' one_pos)
  · rw [e]
    have := speed_le (b := 0) hc le_rfl one_pos (by simpa using h0.trans hν.1) hν.2
    convert this using 2
    ring

end Cvs.Prolate.NodeLevelSeparation

end
