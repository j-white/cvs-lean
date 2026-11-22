import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.MirrorConcentrationHalf
import Cvs.Prolate.ForbiddenZoneGrowth
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungEdgeCorrectedEnergy
import Cvs.Prolate.RungMirrorIdentity
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Upstream.OneSidedEdgeLimit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The plunge law P1 in integral form

For an even rung `g ≢ 0` with `psi c g = μ g` and `0 ≤ χ < c²`, the far mass `∫₁^∞ ψ²` is at most `(E/2)∫₁^∞ 1/a +
E/(4(c² − χ))` when `E ≥` the energy beyond `1` (Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy, Cvs.Upstream.OneSidedEdgeLimit), the low mass is at least `ψ(1)² J` (Cvs.Prolate.ForbiddenZoneGrowth), and `RungMirrorIdentity`'s
unitarity gives `1 − λ ≤ (e₀/2)(K + 1/(2S))/(cJ)`, `K = c∫₁^∞ 1/a`, with `e₀ = 11/10` for `c ≥ 80`, `c² − χ ≥ 5c`.
-/

namespace Cvs.Prolate.PlungeLawIntegral

open Real Set Filter Topology MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.ForbiddenZoneGrowth

/-- `K = c ∫₁^∞ dξ/a(ξ)`, `a = √((ξ² − 1)(c²ξ² − χ))`: with `ξ = 1/t`, the complete elliptic integral of the first
kind at modulus `√χ/c`. -/
noncomputable def ellK (c χ : ℝ) : ℝ := c * ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ

/-- The forbidden-zone weight `J = ∫_{√χ/c}^1 exp(2Φ_C(Z(s))) ds`. -/
noncomputable def forbJ (c χ : ℝ) : ℝ := ∫ s in (√χ / c)..1, Real.exp (2 * PhiC (forbZ c χ s))

/-- `ξ ↦ 1/(ξ√(ξ² − 1))`, the derivative of `arccos(1/ξ)`, is integrable on `(1, ∞)`. -/
theorem integrableOn_arcsec_deriv : IntegrableOn (fun ξ : ℝ => 1 / (ξ * √(ξ ^ 2 - 1))) (Ioi 1) := by
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun s => arccos (1 / s)) (l := π / 2) ?_ ?_ ?_ ?_
  · exact (Real.continuous_arccos.continuousAt.comp
      (continuousAt_const.div continuousAt_id one_ne_zero)).continuousWithinAt
  · exact fun x hx => Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.hasDerivAt_arcsec hx
  · intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    exact div_nonneg zero_le_one (mul_nonneg hx0.le (Real.sqrt_nonneg _))
  · have h : Tendsto (fun s : ℝ => 1 / s) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero
    have := (Real.continuous_arccos.tendsto 0).comp h
    rwa [Real.arccos_zero] at this

/-- `1/a` is integrable on `(1, ∞)`: `1/a ≤ 1/(√(c² − χ) ξ√(ξ² − 1))`. -/
theorem integrableOn_inv_aP {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    IntegrableOn (fun ξ => 1 / aP c χ ξ) (Ioi 1) := by
  have hσ : 0 < √(c ^ 2 - χ) := Real.sqrt_pos.mpr (by linarith)
  refine (integrableOn_arcsec_deriv.const_mul (1 / √(c ^ 2 - χ))).mono' ?_ ?_
  · have hcont : Continuous (aP c χ) := by unfold aP pP qP; fun_prop
    exact (measurable_const.div hcont.measurable).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ => ?_
    have hξ1 : 1 < ξ := hξ
    have ha := aP_pos hξ1 (by positivity) hχc
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 1 / aP c χ ξ ≤ 1 / (√(c ^ 2 - χ) * (ξ * √(ξ ^ 2 - 1))) :=
          Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.inv_a_le hξ1 hc hχ0 hχc
      _ = 1 / √(c ^ 2 - χ) * (1 / (ξ * √(ξ ^ 2 - 1))) := by rw [one_div_mul_one_div]

/-- **The radial mass up to `X`**: for `ψ' = u/p` beyond `1`, `u' = −qψ`, `u(1) = 0` and energy at most `E` beyond
`1`, `∫₁^X ψ² ≤ (E/2)∫₁^∞ 1/a + E/(4(c² − χ))`. -/
theorem radial_mass_le_interval {c χ E X : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hX : 1 ≤ X) (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) (hψc : Continuous ψ) (hu1 : u 1 = 0)
    (hE : ∀ ξ, 1 < ξ → energy (aP c χ) ψ u ξ ≤ E) :
    ∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2 ≤ E / 2 * (∫ ξ in Ioi 1, 1 / aP c χ ξ) + E / (4 * (c ^ 2 - χ)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hD : 0 < c ^ 2 - χ := by linarith
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun ξ => (hu ξ).continuousAt
  have hInt := integrableOn_inv_aP hc hχ0 hχc
  set K := ∫ ξ in Ioi 1, 1 / aP c χ ξ with hK
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun ξ hξ => by
    have := aP_pos (show 1 < ξ from hξ) hc2 hχc; positivity
  have hE0 : 0 ≤ E := by
    have ha := aP_pos one_lt_two hc2 hχc
    refine le_trans ?_ (hE 2 one_lt_two)
    unfold energy; positivity
  have hI0 : 0 ≤ E / 2 * K + E / (4 * (c ^ 2 - χ)) := by positivity
  rcases eq_or_lt_of_le hX with hX1 | hX1
  · subst hX1; rw [intervalIntegral.integral_same]; exact hI0
  have hqc' : Continuous (qP c χ) := by unfold qP; fun_prop
  have hac' : Continuous (aP c χ) := by unfold aP pP qP; fun_prop
  refine Cvs.Upstream.OneSidedEdgeLimit.le_of_edge_limit
    (S := fun x₀ => (∫ ξ in (1 : ℝ)..x₀, ψ ξ ^ 2) + ψ x₀ * u x₀ / qP c χ x₀ / 2) hX1 ?_ ?_
  · intro x₀ hx₀
    have h1 : 1 < x₀ := hx₀.1
    have hle : x₀ ≤ X := hx₀.2.le
    have gt1 : ∀ t ∈ Icc x₀ X, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
    have hq : ∀ t ∈ Icc x₀ X, 0 < qP c χ t := fun t ht => qP_pos (gt1 t ht) hc2 hχc
    have ha : ∀ t ∈ Icc x₀ X, 0 < aP c χ t := fun t ht => aP_pos (gt1 t ht) hc2 hχc
    have hqd : ∀ t ∈ Icc x₀ X, HasDerivAt (qP c χ) (2 * c ^ 2 * t) t := fun t _ => by
      have h := ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).sub_const χ
      exact h.congr_deriv (by ring)
    have hac : ContinuousOn (aP c χ) (Icc x₀ X) := hac'.continuousOn
    have hpc : ContinuousOn pP (Icc x₀ X) := by unfold pP; fun_prop
    have hqc : ContinuousOn (qP c χ) (Icc x₀ X) := hqc'.continuousOn
    have hψcI : ContinuousOn ψ (Icc x₀ X) := hψc.continuousOn
    have hucI : ContinuousOn u (Icc x₀ X) := huc.continuousOn
    have hid := Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy.integral_sq_eq (q' := fun t => 2 * c ^ 2 * t) hle ha
      (fun t ht => (pP_pos (gt1 t ht)).ne') (fun t ht => (hq t ht).ne')
      (fun t ht => aP_sq (gt1 t ht) hc2 hχc) (fun t ht => hψ t (gt1 t ht)) (fun t _ => hu t) hqd
      (by fun_prop) hac hpc
    have hcross : ∀ t ∈ Icc x₀ X, |ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)|
        ≤ E / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2) := fun t ht => by
      have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht)
      have hqt := hq t ht
      have ht0 : 0 ≤ 2 * c ^ 2 * t := by have := gt1 t ht; positivity
      rw [abs_div, abs_mul, abs_of_nonneg ht0, abs_of_pos (by positivity : 0 < 2 * qP c χ t ^ 2),
        div_le_iff₀ (by positivity)]
      have : |ψ t * u t| ≤ E / 2 := by linarith [hE t (gt1 t ht)]
      have e : E / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2) * (2 * qP c χ t ^ 2) = E / 2 * (2 * c ^ 2 * t) := by
        field_simp; ring
      rw [e]; exact mul_le_mul_of_nonneg_right this ht0
    have hmain : ∀ t ∈ Icc x₀ X, energy (aP c χ) ψ u t / (2 * aP c χ t)
        - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)
        ≤ E / 2 * (1 / aP c χ t) + E / 4 * (2 * c ^ 2 * t / qP c χ t ^ 2) := by
      intro t ht
      have hat := ha t ht
      have h1' : energy (aP c χ) ψ u t / (2 * aP c χ t) ≤ E / 2 * (1 / aP c χ t) := by
        have e : energy (aP c χ) ψ u t / (2 * aP c χ t) = energy (aP c χ) ψ u t / 2 * (1 / aP c χ t) := by
          field_simp
        rw [e]; exact mul_le_mul_of_nonneg_right (by linarith [hE t (gt1 t ht)]) (by positivity)
      have := neg_abs_le (ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2))
      linarith [hcross t ht]
    have hint1 : ContinuousOn (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)
        - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)) (Icc x₀ X) := by
      have hnz1 : ∀ t ∈ Icc x₀ X, 2 * aP c χ t ≠ 0 := fun t ht => by
        have := ha t ht; positivity
      have hnz2 : ∀ t ∈ Icc x₀ X, 2 * qP c χ t ^ 2 ≠ 0 := fun t ht => by
        have := hq t ht; positivity
      have hE1 : ContinuousOn (fun t => energy (aP c χ) ψ u t) (Icc x₀ X) := by
        unfold energy
        exact (hac.mul (hψcI.pow 2)).add ((hucI.pow 2).div₀ hac fun t ht => (ha t ht).ne')
      have hlin : ContinuousOn (fun t : ℝ => 2 * c ^ 2 * t) (Icc x₀ X) :=
        continuousOn_const.mul continuousOn_id
      exact (hE1.div₀ (continuousOn_const.mul hac) hnz1).sub
        (((hψcI.mul hucI).mul hlin).div₀ (continuousOn_const.mul (hqc.pow 2)) hnz2)
    have hainv : ContinuousOn (fun t => 1 / aP c χ t) (Icc x₀ X) :=
      continuousOn_const.div hac fun t ht => (ha t ht).ne'
    have hqq' : ContinuousOn (fun t => 2 * c ^ 2 * t / qP c χ t ^ 2) (Icc x₀ X) :=
      (continuousOn_const.mul continuousOn_id).div₀ (hqc.pow 2) fun t ht => pow_ne_zero 2 (hq t ht).ne'
    have iA := hainv.intervalIntegrable_of_Icc (μ := volume) hle
    have iQ := hqq'.intervalIntegrable_of_Icc (μ := volume) hle
    have iH := hint1.intervalIntegrable_of_Icc (μ := volume) hle
    have iU := integral_mono_on hle iH ((iA.const_mul (E / 2)).add (iQ.const_mul (E / 4))) hmain
    rw [intervalIntegral.integral_add (iA.const_mul _) (iQ.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at iU
    have hI : uIcc x₀ X = Icc x₀ X := uIcc_of_le hle
    have hqq : ∫ t in x₀..X, 2 * c ^ 2 * t / qP c χ t ^ 2 = 1 / qP c χ x₀ - 1 / qP c χ X := by
      have hd : ∀ t ∈ uIcc x₀ X, HasDerivAt (fun s => -(1 / qP c χ s))
          (2 * c ^ 2 * t / qP c χ t ^ 2) t := fun t ht => by
        have := ((hqd t (hI ▸ ht)).inv (hq t (hI ▸ ht)).ne').neg
        refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
        filter_upwards with s; simp [one_div]
      rw [integral_eq_sub_of_hasDerivAt hd iQ]
      ring
    have hAK : ∫ t in x₀..X, 1 / aP c χ t ≤ K := by
      rw [intervalIntegral.integral_of_le hle]
      refine setIntegral_mono_set hInt ?_ ?_
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have := aP_pos (show 1 < t from ht) hc2 hχc; positivity
      · exact LE.le.eventuallySubset (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi h1.le))
    have hmemX : X ∈ Icc x₀ X := right_mem_Icc.mpr hle
    have hqX := hq X hmemX
    have hqx₀ : c ^ 2 - χ ≤ qP c χ x₀ := by
      unfold qP
      have : 0 ≤ c ^ 2 * (x₀ ^ 2 - 1) := mul_nonneg hc2.le (by nlinarith)
      nlinarith
    have eX : -(ψ X * u X / qP c χ X / 2) ≤ E / (4 * qP c χ X) := by
      have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha X hmemX)
      have hab : -(ψ X * u X) ≤ E / 2 := by
        have := neg_le_abs (ψ X * u X); linarith [hE X (gt1 X hmemX)]
      rw [show -(ψ X * u X / qP c χ X / 2) = -(ψ X * u X) / (2 * qP c χ X) by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hab hqX.le]
    have hq₀ : E / (4 * qP c χ x₀) ≤ E / (4 * (c ^ 2 - χ)) :=
      div_le_div_of_nonneg_left hE0 (by positivity) (by linarith)
    have hsum : E / 4 * (1 / qP c χ x₀ - 1 / qP c χ X) + E / (4 * qP c χ X) = E / (4 * qP c χ x₀) := by
      have := hq x₀ (left_mem_Icc.mpr hle)
      field_simp; ring
    have hsplit : ∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2 = (∫ ξ in (1 : ℝ)..x₀, ψ ξ ^ 2) + ∫ ξ in x₀..X, ψ ξ ^ 2 :=
      (integral_add_adjacent_intervals ((hψc.pow 2).intervalIntegrable _ _)
        ((hψc.pow 2).intervalIntegrable _ _)).symm
    rw [hqq] at iU
    rw [hsplit, hid]
    have hKE : E / 2 * ∫ t in x₀..X, 1 / aP c χ t ≤ E / 2 * K := mul_le_mul_of_nonneg_left hAK (by positivity)
    show _ ≤ (∫ ξ in (1 : ℝ)..x₀, ψ ξ ^ 2) + ψ x₀ * u x₀ / qP c χ x₀ / 2 + (E / 2 * K + E / (4 * (c ^ 2 - χ)))
    linarith
  · have hprim : Continuous (fun x₀ => ∫ ξ in (1 : ℝ)..x₀, ψ ξ ^ 2) :=
      intervalIntegral.continuous_primitive (fun a b => (hψc.pow 2).intervalIntegrable a b) 1
    have hq1 : qP c χ 1 ≠ 0 := by unfold qP; nlinarith
    have hcont : ContinuousAt (fun x₀ => (∫ ξ in (1 : ℝ)..x₀, ψ ξ ^ 2) + ψ x₀ * u x₀ / qP c χ x₀ / 2) 1 :=
      hprim.continuousAt.add ((((hψc.mul huc).continuousAt).div hqc'.continuousAt hq1).div_const 2)
    have h0 : (∫ ξ in (1 : ℝ)..1, ψ ξ ^ 2) + ψ 1 * u 1 / qP c χ 1 / 2 = 0 := by
      simp [hu1]
    have := hcont.tendsto
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds

/-- **The radial mass**: under `radial_mass_le_interval`'s hypotheses, `ψ² ∈ L¹(1, ∞)` and
`∫₁^∞ ψ² ≤ (E/2)∫₁^∞ 1/a + E/(4(c² − χ))`. -/
theorem radial_mass_le {c χ E : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) (hψc : Continuous ψ) (hu1 : u 1 = 0)
    (hE : ∀ ξ, 1 < ξ → energy (aP c χ) ψ u ξ ≤ E) :
    IntegrableOn (fun ξ => ψ ξ ^ 2) (Ioi 1) ∧
      ∫ ξ in Ioi 1, ψ ξ ^ 2 ≤ E / 2 * (∫ ξ in Ioi 1, 1 / aP c χ ξ) + E / (4 * (c ^ 2 - χ)) := by
  have hb : ∀ X, 1 ≤ X → ∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2
      ≤ E / 2 * (∫ ξ in Ioi 1, 1 / aP c χ ξ) + E / (4 * (c ^ 2 - χ)) := fun X hX =>
    radial_mass_le_interval hc hχ0 hχc hX hψ hu hψc hu1 hE
  have hInt : IntegrableOn (fun ξ => ψ ξ ^ 2) (Ioi 1) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (l := atTop) (b := id)
      (E / 2 * (∫ ξ in Ioi 1, 1 / aP c χ ξ) + E / (4 * (c ^ 2 - χ))) 1
      (fun i => (hψc.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self) tendsto_id ?_
    filter_upwards [eventually_ge_atTop 1] with X hX
    have e : ∫ x in (1 : ℝ)..id X, ‖ψ x ^ 2‖ = ∫ x in (1 : ℝ)..X, ψ x ^ 2 := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [norm_pow, Real.norm_eq_abs, sq_abs]
    rw [e]; exact hb X hX
  refine ⟨hInt, ?_⟩
  have hlim := intervalIntegral_tendsto_integral_Ioi 1 hInt tendsto_id
  exact le_of_tendsto hlim (by filter_upwards [eventually_ge_atTop 1] with X hX using hb X hX)

/-- `∫_{Ioi 0} ψ² = ∫₀¹ ψ² + ∫₁^∞ ψ²` for an even `g` continuous on `[−1, 1]`. -/
theorem integral_Ioi_zero_split {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    ∫ x in Ioi 0, psi c g x ^ 2 = (∫ x in (0 : ℝ)..1, psi c g x ^ 2) + ∫ x in Ioi 1, psi c g x ^ 2 := by
  have hm := Cvs.Prolate.RungMirrorIdentity.memLp_psi hc hgc heven
  have hInt : IntegrableOn (fun x => psi c g x ^ 2) (Ioi 0) := by
    have := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi zero_le_one)),
    Ioc_union_Ioi_eq_Ioi zero_le_one]

/-- **The far mass is the defect**: `∫₁^∞ ψ² = (1 − λ)∫_{Ioi 0} ψ²`, `λ = (c/2π)μ²`, for an even `g` continuous on
`[−1, 1]` with `psi c g = μ g` there. -/
theorem far_mass_eq {g : ℝ → ℝ} {c μ : ℝ} (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    ∫ x in Ioi 1, psi c g x ^ 2 = (1 - c / (2 * π) * μ ^ 2) * ∫ x in Ioi 0, psi c g x ^ 2 := by
  have hsplit := integral_Ioi_zero_split hc hgc heven
  have hτ := Cvs.Prolate.RungMirrorIdentity.tau_sq_mul hc hgc heven hμ
  have hlam : (μ * √(c / (2 * π))) ^ 2 = c / (2 * π) * μ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hlam] at hτ
  linear_combination hτ - hsplit

/-- `(1 − λ)∫₀¹ ψ² ≤ ∫₁^∞ ψ²`, `λ = (c/2π)μ²`, under `far_mass_eq`'s hypotheses. -/
theorem one_sub_lambda_mul_le {g : ℝ → ℝ} {c μ : ℝ} (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    (1 - c / (2 * π) * μ ^ 2) * ∫ x in (0 : ℝ)..1, psi c g x ^ 2 ≤ ∫ x in Ioi 1, psi c g x ^ 2 := by
  have hsplit := integral_Ioi_zero_split hc hgc heven
  have hM := far_mass_eq hc hgc heven hμ
  have hM0 : 0 ≤ ∫ x in Ioi 1, psi c g x ^ 2 := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have hI0 : 0 ≤ ∫ x in (0 : ℝ)..1, psi c g x ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun x _ => sq_nonneg _
  rcases le_or_gt 0 (1 - c / (2 * π) * μ ^ 2) with h | h
  · calc (1 - c / (2 * π) * μ ^ 2) * ∫ x in (0 : ℝ)..1, psi c g x ^ 2
        ≤ (1 - c / (2 * π) * μ ^ 2) * ∫ x in Ioi 0, psi c g x ^ 2 :=
          mul_le_mul_of_nonneg_left (by linarith) h
      _ = ∫ x in Ioi 1, psi c g x ^ 2 := hM.symm
  · exact (mul_nonpos_of_nonpos_of_nonneg h.le hI0).trans hM0

/-- An even rung `g ≢ 0` has `ψ(1) ≠ 0`: `ψ = ψ(1) regSol` on `(−1, ∞)` (Cvs.Prolate.RegularSolutionEdge) and `∫_{Ioi 0} ψ² > 0` (Cvs.Prolate.RungMirrorIdentity). -/
theorem psi_one_ne_zero {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) :
    psi c g 1 ≠ 0 := by
  intro h
  have hgc : ContinuousOn g (Icc (-1 : ℝ) 1) := fun s hs =>
    (hg s (by rw [uIcc_of_le (by norm_num)]; exact hs)).continuousAt.continuousWithinAt
  have hT := Cvs.Prolate.RungMirrorIdentity.integral_psi_sq_pos hc hgc heven hg0
  have h0 : ∫ x in Ioi 0, psi c g x ^ 2 = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hx' : (-1 : ℝ) < x := by have : (0 : ℝ) < x := hx; linarith
    rw [(Cvs.Prolate.RegularSolutionEdge.psi_eq_mul_regSol hg hg₁ hg₂c hang hx').1, h]
    ring
  linarith

/-- `J > 0` for `0 ≤ χ < c²`. -/
theorem forbJ_pos {c χ : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) : 0 < forbJ c χ := by
  have ha0 : 0 ≤ √χ / c := div_nonneg (Real.sqrt_nonneg _) hc.le
  have ha1 : √χ / c < 1 := by rw [div_lt_one hc, Real.sqrt_lt' hc]; exact hχc
  have hcont : ContinuousOn (fun s => Real.exp (2 * PhiC (forbZ c χ s))) (Icc (√χ / c) 1) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_PhiC)).comp_continuousOn
      ((continuousOn_forbZ c χ).mono (Icc_subset_Icc ha0 le_rfl))
  unfold forbJ
  exact intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable_of_Icc ha1.le) (fun x _ => Real.exp_pos _) ha1

/-- **The forbidden-zone mass**: `ψ(1)² J ≤ ∫₀¹ ψ²` for a rung with `0 ≤ χ < c²` (`ForbiddenZoneGrowth`'s growth, squared). -/
theorem forbidden_mass_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    psi c g 1 ^ 2 * forbJ c χ ≤ ∫ s in (0 : ℝ)..1, psi c g s ^ 2 := by
  have ha0 : 0 ≤ √χ / c := div_nonneg (Real.sqrt_nonneg _) hc.le
  have ha1 : √χ / c < 1 := by rw [div_lt_one hc, Real.sqrt_lt' hc]; exact hχc
  have hψc := (rung_system hg hg₁ hg₂c hang).2.2.1
  have hcont : ContinuousOn (fun s => psi c g 1 ^ 2 * Real.exp (2 * PhiC (forbZ c χ s))) (Icc (√χ / c) 1) :=
    continuousOn_const.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_PhiC)).comp_continuousOn
      ((continuousOn_forbZ c χ).mono (Icc_subset_Icc ha0 le_rfl)))
  unfold forbJ
  rw [← intervalIntegral.integral_const_mul]
  calc ∫ s in (√χ / c)..1, psi c g 1 ^ 2 * Real.exp (2 * PhiC (forbZ c χ s))
      ≤ ∫ s in (√χ / c)..1, psi c g s ^ 2 :=
        intervalIntegral.integral_mono_on ha1.le (hcont.intervalIntegrable_of_Icc ha1.le)
          ((hψc.pow 2).intervalIntegrable _ _) fun s hs => forbidden_growth_sq hc hχ0 hχc hg hg₁ hg₂c hang hs
    _ ≤ ∫ s in (0 : ℝ)..1, psi c g s ^ 2 :=
        intervalIntegral.integral_mono_interval ha0 ha1.le le_rfl
          (Filter.Eventually.of_forall fun s => sq_nonneg (psi c g s)) ((hψc.pow 2).intervalIntegrable _ _)

/-- **Plunge law P1, integral form**: an even rung `g ≢ 0` with `psi c g = μ g`, `0 ≤ χ < c²` and `E ≤ e₀ψ(1)²`
beyond `1` has `1 − λ ≤ (e₀/2)(K + 1/(2S))/(cJ)`, `λ = (c/2π)μ²`, `S = (c² − χ)/c`. -/
theorem plunge_P1_of_energy {g g₁ g₂ : ℝ → ℝ} {c χ μ e₀ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s)
    (hE : ∀ ξ, 1 < ξ → energy (aP c χ) (psi c g) (rungU c g) ξ ≤ e₀ * psi c g 1 ^ 2) :
    1 - c / (2 * π) * μ ^ 2 ≤ e₀ / 2 * (ellK c χ + c / (2 * (c ^ 2 - χ))) / (c * forbJ c χ) := by
  have hgc : ContinuousOn g (Icc (-1 : ℝ) 1) := fun s hs =>
    (hg s (by rw [uIcc_of_le (by norm_num)]; exact hs)).continuousAt.continuousWithinAt
  obtain ⟨hψ, hu, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hu1 : rungU c g 1 = 0 := by unfold rungU pP; simp
  have hD : 0 < c ^ 2 - χ := by linarith
  obtain ⟨-, hM⟩ := radial_mass_le hc hχ0 hχc hψ hu hψc hu1 hE
  have hlow := one_sub_lambda_mul_le hc hgc heven hμ
  have hJ := forbidden_mass_le hc hχ0 hχc hg hg₁ hg₂c hang
  have hJ0 := forbJ_pos hc hχc
  have h1 := psi_one_ne_zero hc hg hg₁ hg₂c hang heven hg0
  have hP : 0 < psi c g 1 ^ 2 := by positivity
  set lam := c / (2 * π) * μ ^ 2 with hlam
  set J := forbJ c χ with hJdef
  set M := ∫ x in Ioi 1, psi c g x ^ 2 with hMdef
  have hM0 : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have key : (1 - lam) * (psi c g 1 ^ 2 * J) ≤ M := by
    rcases le_or_gt 0 (1 - lam) with h | h
    · exact (mul_le_mul_of_nonneg_left hJ h).trans hlow
    · exact (mul_nonpos_of_nonpos_of_nonneg h.le (by positivity)).trans hM0
  have key' : (1 - lam) * J * psi c g 1 ^ 2
      ≤ (e₀ / 2 * (∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ) + e₀ / (4 * (c ^ 2 - χ))) * psi c g 1 ^ 2 :=
    calc (1 - lam) * J * psi c g 1 ^ 2 = (1 - lam) * (psi c g 1 ^ 2 * J) := by ring
      _ ≤ M := key
      _ ≤ e₀ * psi c g 1 ^ 2 / 2 * (∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ)
          + e₀ * psi c g 1 ^ 2 / (4 * (c ^ 2 - χ)) := hM
      _ = (e₀ / 2 * (∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ) + e₀ / (4 * (c ^ 2 - χ))) * psi c g 1 ^ 2 := by
          ring
  have hfin := le_of_mul_le_mul_right key' hP
  rw [le_div_iff₀ (by positivity)]
  show (1 - lam) * (c * J) ≤ e₀ / 2 * (c * (∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ) + c / (2 * (c ^ 2 - χ)))
  calc (1 - lam) * (c * J) = c * ((1 - lam) * J) := by ring
    _ ≤ c * (e₀ / 2 * (∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ) + e₀ / (4 * (c ^ 2 - χ))) :=
        mul_le_mul_of_nonneg_left hfin hc.le
    _ = e₀ / 2 * (c * (∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ) + c / (2 * (c ^ 2 - χ))) := by
        field_simp; ring

/-- `a(ξ) ≤ 11/10` on `(1, 1 + 1/(2(c² − χ))]` for `c ≥ 80`, `c² − χ ≥ 5c`. -/
theorem aP_le_edge {c χ ξ : ℝ} (hc : 80 ≤ c) (hD : 5 * c ≤ c ^ 2 - χ) (h1 : 1 < ξ)
    (hξ : ξ ≤ 1 + 1 / (2 * (c ^ 2 - χ))) : aP c χ ξ ≤ 11 / 10 := by
  have hc0 : 0 < c := by linarith
  have hD0 : 0 < c ^ 2 - χ := by nlinarith
  set D := c ^ 2 - χ with hDdef
  set δ := ξ - 1 with hδ
  have hδ0 : 0 < δ := by linarith
  have hδD : δ * (2 * D) ≤ 1 := by
    have : δ ≤ 1 / (2 * D) := by linarith
    rwa [le_div_iff₀ (by positivity)] at this
  have hD400 : 400 ≤ D := by nlinarith
  have hδs : δ ≤ 1 / 800 := by
    have : δ * 800 ≤ δ * (2 * D) := mul_le_mul_of_nonneg_left (by linarith) hδ0.le
    linarith
  set x := δ * (2 + δ) * D with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 + 1 / 1600 := by
    have : x = δ * (2 * D) * (1 + δ / 2) := by rw [hx]; ring
    rw [this]
    calc δ * (2 * D) * (1 + δ / 2) ≤ 1 * (1 + 1 / 1600) :=
          mul_le_mul hδD (by linarith) (by positivity) zero_le_one
      _ = 1 + 1 / 1600 := one_mul _
  have ha2 : aP c χ ξ ^ 2 = x + c ^ 2 * (δ * (2 + δ)) ^ 2 := by
    rw [aP_sq h1 (by positivity) (by linarith), hx]
    unfold pP qP
    rw [hδ, hDdef]; ring
  have hcD : c ^ 2 * (δ * (2 + δ)) ^ 2 * 25 ≤ x ^ 2 := by
    have hc5 : 25 * c ^ 2 ≤ D ^ 2 := by nlinarith
    have : x ^ 2 = D ^ 2 * (δ * (2 + δ)) ^ 2 := by rw [hx]; ring
    rw [this]; nlinarith [sq_nonneg (δ * (2 + δ))]
  have hsq : aP c χ ξ ^ 2 ≤ (11 / 10) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by norm_num) two_ne_zero).mp hsq

/-- **The sup energy**: `E(ξ) ≤ (11/10)ψ(1)²` for every `ξ > 1`, for a rung with `c ≥ 80`, `χ ≥ 0`, `c² − χ ≥ 5c`. -/
theorem energy_le_sup {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hD : 5 * c ≤ c ^ 2 - χ) {ξ : ℝ} (hξ : 1 < ξ) :
    energy (aP c χ) (psi c g) (rungU c g) ξ ≤ 11 / 10 * psi c g 1 ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hχc : χ < c ^ 2 := by nlinarith
  rcases le_or_gt (1 + 1 / (2 * (c ^ 2 - χ))) ξ with h | h
  · exact Cvs.L2a.MirrorConcentrationHalf.energy_le_far hg hg₁ hg₂c hang hc hχ0 hD h
  · exact (Cvs.Prolate.RungEdgeCorrectedEnergy.energy_le_edge hc0 hχc hg hg₁ hg₂c hang hξ).trans
      (mul_le_mul_of_nonneg_right (aP_le_edge hc hD hξ h.le) (sq_nonneg _))

/-- **Plunge law P1**: for an even rung `g ≢ 0` with `psi c g = μ g`, `c ≥ 80`, `χ ≥ 0`, `c² − χ ≥ 5c`,
`1 − λ ≤ (11/20)(K + c/(2(c² − χ)))/(cJ)`, `λ = (c/2π)μ²`. -/
theorem plunge_P1 {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hD : 5 * c ≤ c ^ 2 - χ)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    1 - c / (2 * π) * μ ^ 2 ≤ 11 / 10 / 2 * (ellK c χ + c / (2 * (c ^ 2 - χ))) / (c * forbJ c χ) :=
  plunge_P1_of_energy (by linarith) hχ0 (by nlinarith) hg hg₁ hg₂c hang heven hg0 hμ
    fun _ hξ => energy_le_sup hg hg₁ hg₂c hang hc hχ0 hD hξ

end Cvs.Prolate.PlungeLawIntegral
