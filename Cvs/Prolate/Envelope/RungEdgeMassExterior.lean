import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CorrectedEnergyAntitone
import Cvs.Prolate.Envelope.EdgeValueSoninBound
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungEdgeCorrectedEnergy
import Cvs.Prolate.RungSpanBernsteinNikolskii

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge mass and the exterior derivative of a rung

For a rung `ψ = ∫ g cos(cξs)` with `χ < c²` and `D = c² − χ`: `(ξ + 1)|ψ'(ξ)| ≤ q(ξ)|ψ(1)|` on `ξ ≥ 1` (Cvs.Prolate.RungEdgeCorrectedEnergy), so
`ψ(1)² ≤ (144/49)(2D + 3c)∫₁^∞ψ²`. Past `ξ₀ > 1` with `w(ξ₀) < 2` the energy is at most `ecap c χ ξ₀ · ψ(1)²`
(Cvs.Prolate.CorrectedEnergyAntitone, Cvs.Prolate.RungEdgeCorrectedEnergy), closed form at `ξ₀ = 1 + 1/c`; an energy cap `e` past `ξ₀` bounds `∫₁^∞ψ'²` in closed form.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity
open Cvs.Prolate.RungSpanBernsteinNikolskii (psiD hasDerivAt_psi' continuous_psi continuous_psiD integrable_psi_sq integrable_psiD_sq)

namespace Cvs.Prolate.Envelope.RungEdgeMassExterior
open Cvs.ZeroCounting

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- `u = pψ'`: the rung's `u` is `pP` times the derivative of the transform. -/
theorem rungU_eq (c : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : rungU c g ξ = pP ξ * psiD c g ξ := rfl

/-- `qP c χ` is continuous. -/
theorem continuous_qP (c χ : ℝ) : Continuous (qP c χ) := by unfold qP; fun_prop

/-! ### The edge slope and the edge mass -/

/-- **The edge slope**: `(ξ + 1)|ψ'(ξ)| ≤ q(ξ)|ψ(1)|` for `ξ ≥ 1`. -/
theorem abs_psiD_mul_le (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ : ℝ} (hξ : 1 ≤ ξ) : (ξ + 1) * |psiD c g ξ| ≤ qP c χ ξ * |psi c g 1| := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have key : Ioi (1 : ℝ) ⊆ {ξ | (ξ + 1) * |psiD c g ξ| ≤ qP c χ ξ * |psi c g 1|} := by
    intro ξ hξ
    have hξ1 : 1 < ξ := hξ
    have h := (Cvs.Prolate.RungEdgeCorrectedEnergy.rung_edge_bounds hχc hg hg₁ hg₂c hang hξ1.le).2
    rw [rungU_eq, abs_mul, abs_of_pos (pP_pos hξ1)] at h
    have hp : pP ξ = (ξ - 1) * (ξ + 1) := by unfold pP; ring
    rw [hp] at h
    have h0 : 0 < ξ - 1 := by linarith
    show (ξ + 1) * |psiD c g ξ| ≤ qP c χ ξ * |psi c g 1|
    have h' : (ξ - 1) * ((ξ + 1) * |psiD c g ξ|) ≤ (ξ - 1) * (qP c χ ξ * |psi c g 1|) := by
      linarith [h]
    exact le_of_mul_le_mul_left h' h0
  have hclosed : IsClosed {ξ | (ξ + 1) * |psiD c g ξ| ≤ qP c χ ξ * |psi c g 1|} :=
    isClosed_le ((continuous_id.add continuous_const).mul (continuous_psiD hgc).abs)
      ((continuous_qP c χ).mul continuous_const)
  have hcl := hclosed.closure_subset_iff.mpr key
  rw [closure_Ioi] at hcl
  exact hcl hξ

/-- **The edge mass**: for `c ≥ 1` and `χ < c²`, `ψ(1)² ≤ (144/49)(2(c² − χ) + 3c)∫₁^∞ψ²`. -/
theorem edge_mass (hc : 1 ≤ c) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    psi c g 1 ^ 2 ≤ 144 / 49 * (2 * (c ^ 2 - χ) + 3 * c) * ∫ ξ in Ioi 1, psi c g ξ ^ 2 := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hc0 : 0 < c := by linarith
  set D := c ^ 2 - χ with hDdef
  have hD : 0 < D := by rw [hDdef]; linarith
  have hden : 0 < 2 * D + 3 * c := by positivity
  set ε := 1 / (2 * D + 3 * c) with hεdef
  have hε : 0 < ε := by positivity
  have hεden : ε * (2 * D + 3 * c) = 1 := by rw [hεdef]; field_simp
  have hεD : ε * D ≤ 1 / 2 := by nlinarith
  have hεc : 3 * c * ε ≤ 1 := by nlinarith
  have hε1 : ε ≤ 1 := by nlinarith
  set A := |psi c g 1| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  set M := qP c χ (1 + ε) * A / 2 with hM
  have hq1 : qP c χ (1 + ε) = D + c ^ 2 * (2 * ε + ε ^ 2) := by rw [qP, hDdef]; ring
  have hslope : ∀ t ∈ Icc (1 : ℝ) (1 + ε), ‖psiD c g t‖ ≤ M := by
    intro t ht
    have h := abs_psiD_mul_le hχc hg hg₁ hg₂c hang ht.1
    have hqt : qP c χ t ≤ qP c χ (1 + ε) := by
      have h2 : t ^ 2 ≤ (1 + ε) ^ 2 := pow_le_pow_left₀ (by linarith [ht.1]) ht.2 2
      unfold qP; nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg c)]
    have hq0 : 0 ≤ qP c χ t := by
      have h1 : 1 ≤ t ^ 2 := one_le_pow₀ ht.1
      unfold qP; nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg c)]
    rw [Real.norm_eq_abs, hM]
    have h2 : 2 * |psiD c g t| ≤ (t + 1) * |psiD c g t| := by
      nlinarith [abs_nonneg (psiD c g t), ht.1]
    nlinarith [mul_le_mul_of_nonneg_right hqt hA0]
  have hMε : M * ε ≤ 5 / 12 * A := by
    rw [hM, hq1]
    have h1 : c ^ 2 * ε ^ 2 * (2 + ε) ≤ 1 / 3 := by
      have : (c * ε) ^ 2 ≤ 1 / 9 := by nlinarith
      nlinarith
    have : (D + c ^ 2 * (2 * ε + ε ^ 2)) * ε ≤ 5 / 6 := by nlinarith
    nlinarith
  have hdiff : ∀ t ∈ Icc (1 : ℝ) (1 + ε), |psi c g t - psi c g 1| ≤ 5 / 12 * A := by
    intro t ht
    have h := (convex_Icc (1 : ℝ) (1 + ε)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := psi c g) (f' := psiD c g) (fun s _ => (hasDerivAt_psi' hgc s).hasDerivWithinAt) hslope
      (left_mem_Icc.mpr (by linarith)) ht
    simp only [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - 1)] at h
    have hM0 : 0 ≤ M := by
      rw [hM]
      have : 0 ≤ qP c χ (1 + ε) := by
        rw [hq1]; have : 0 ≤ c ^ 2 * (2 * ε + ε ^ 2) := by positivity
        linarith
      positivity
    calc |psi c g t - psi c g 1| ≤ M * (t - 1) := h
      _ ≤ M * ε := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hM0
      _ ≤ 5 / 12 * A := hMε
  have hlow : ∀ t ∈ Icc (1 : ℝ) (1 + ε), 49 / 144 * psi c g 1 ^ 2 ≤ psi c g t ^ 2 := by
    intro t ht
    have h := hdiff t ht
    have h1 : 7 / 12 * A ≤ |psi c g t| := by
      have := abs_sub_abs_le_abs_sub (psi c g 1) (psi c g t)
      rw [abs_sub_comm] at this; linarith
    have h2 : (7 / 12 * A) ^ 2 ≤ |psi c g t| ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    rw [sq_abs] at h2
    have : A ^ 2 = psi c g 1 ^ 2 := sq_abs _
    nlinarith
  have hint := (integrable_psi_sq hc0 hgc).integrableOn (s := Ioi (1 : ℝ))
  have hsub : ∫ ξ in Ioc 1 (1 + ε), psi c g ξ ^ 2 ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 :=
    setIntegral_mono_set hint (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ Ioc_subset_Ioi_self)
  have hlowI : ε * (49 / 144 * psi c g 1 ^ 2) ≤ ∫ ξ in Ioc 1 (1 + ε), psi c g ξ ^ 2 := by
    have hc' : ∫ ξ in Ioc 1 (1 + ε), (49 / 144 * psi c g 1 ^ 2) = ε * (49 / 144 * psi c g 1 ^ 2) := by
      rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
      ring
    rw [← hc']
    refine setIntegral_mono_on (integrableOn_const (by simp)) ((integrable_psi_sq hc0 hgc).integrableOn)
      measurableSet_Ioc fun t ht => hlow t (Ioc_subset_Icc_self ht)
  have htot : ε * (49 / 144 * psi c g 1 ^ 2) ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 := hlowI.trans hsub
  have e : psi c g 1 ^ 2 = 144 / 49 * (2 * D + 3 * c) * (ε * (49 / 144 * psi c g 1 ^ 2)) := by
    rw [hεdef]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left htot (by positivity)

/-! ### The energy cap past `ξ₀` -/

/-- The energy cap past `ξ₀`: `[(1 + d₀)a(ξ₀) − w(ξ₀)(ξ₀ − 1)q(ξ₀)]/(1 − w(ξ₀)/2)`, `d₀ = 2c²ξ₀(ξ₀ − 1)/(c² − χ)`. -/
def ecap (c χ ξ₀ : ℝ) : ℝ :=
  ((1 + 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) / (c ^ 2 - χ)) * aP c χ ξ₀ - wP c χ ξ₀ * (ξ₀ - 1) * qP c χ ξ₀)
    / (1 - wP c χ ξ₀ / 2)

/-- **The energy cap**: for a rung with `c > 0`, `0 ≤ χ < c²`, `1 < ξ₀ ≤ ξ` and `w(ξ₀) < 2`,
`E(ξ) ≤ ecap c χ ξ₀ · ψ(1)²`. -/
theorem energy_le_ecap (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ₀ ξ : ℝ} (h1 : 1 < ξ₀) (hξ : ξ₀ ≤ ξ) (hW : wP c χ ξ₀ < 2) :
    energy (aP c χ) (psi c g) (rungU c g) ξ ≤ ecap c χ ξ₀ * psi c g 1 ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  obtain ⟨hψ, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
  have hE := Cvs.Prolate.CorrectedEnergyAntitone.prolate_energy_le_corrected h1 hξ hc2 hχ0 hχc
    (fun t ht => hψ t (lt_of_lt_of_le h1 ht.1)) (fun t _ => hu t) hW
  have hH := Cvs.Prolate.RungEdgeCorrectedEnergy.edge_corrected_energy_le hc hχ0 hχc hg hg₁ hg₂c hang h1
  have hden : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
  calc energy (aP c χ) (psi c g) (rungU c g) ξ
      ≤ (energy (aP c χ) (psi c g) (rungU c g) ξ₀ + wP c χ ξ₀ * (psi c g ξ₀ * rungU c g ξ₀))
          / (1 - wP c χ ξ₀ / 2) := hE
    _ ≤ psi c g 1 ^ 2 * ((1 + 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) / (c ^ 2 - χ)) * aP c χ ξ₀
          - wP c χ ξ₀ * (ξ₀ - 1) * qP c χ ξ₀) / (1 - wP c χ ξ₀ / 2) :=
        div_le_div_of_nonneg_right hH hden.le
    _ = ecap c χ ξ₀ * psi c g 1 ^ 2 := by unfold ecap; ring

/-- **The cap at `ξ₀ = 1 + 1/c`**: for `c > 0`, `0 ≤ χ < c²`, `w(1 + 1/c) < 2` and
`ecap c χ (1 + 1/c) ≤ (1 + 2(c + 1)/(c² − χ))(2c + 1)√((2c + 1)(c² − χ + 2c + 1))/c²`. -/
theorem ecap_edge_le (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    wP c χ (1 + 1 / c) < 2 ∧ ecap c χ (1 + 1 / c)
      ≤ (1 + 2 * (c + 1) / (c ^ 2 - χ)) * ((2 * c + 1) * √((2 * c + 1) * (c ^ 2 - χ + 2 * c + 1)) / c ^ 2) := by
  set ξ₀ := 1 + 1 / c with hξ₀
  have hc2 : 0 < c ^ 2 := by positivity
  have hD : 0 < c ^ 2 - χ := by linarith
  have h1 : 1 < ξ₀ := by rw [hξ₀]; have : 0 < 1 / c := by positivity
                         linarith
  have hp : pP ξ₀ = (2 * c + 1) / c ^ 2 := by rw [pP, hξ₀]; field_simp; ring
  have hq : qP c χ ξ₀ = c ^ 2 - χ + 2 * c + 1 := by rw [qP, hξ₀]; field_simp; ring
  have hqpos : 0 < c ^ 2 - χ + 2 * c + 1 := by linarith
  have hwle := wP_le_far h1 hc hχ0 hχc
  have hw2 : 2 * ξ₀ / (c * pP ξ₀) = 2 * (c + 1) / (2 * c + 1) := by
    rw [hp, hξ₀]; field_simp
  rw [hw2] at hwle
  have hw0 := wP_pos h1 hc2 hχc
  have hwlt : 2 * (c + 1) / (2 * c + 1) < 2 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  refine ⟨lt_of_le_of_lt hwle hwlt, ?_⟩
  have hden : c / (2 * c + 1) ≤ 1 - wP c χ ξ₀ / 2 := by
    have : c / (2 * c + 1) = 1 - 2 * (c + 1) / (2 * c + 1) / 2 := by field_simp; ring
    rw [this]; linarith
  have hdpos : 0 < c / (2 * c + 1) := by positivity
  have ha : aP c χ ξ₀ = √((2 * c + 1) * (c ^ 2 - χ + 2 * c + 1)) / c := by
    unfold aP
    rw [hp, hq, div_mul_eq_mul_div, Real.sqrt_div' _ hc2.le, Real.sqrt_sq hc.le]
  have ha0 : 0 ≤ aP c χ ξ₀ := (aP_pos h1 hc2 hχc).le
  have hd₀ : 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) / (c ^ 2 - χ) = 2 * (c + 1) / (c ^ 2 - χ) := by
    rw [hξ₀]; field_simp; ring
  have hsub : 0 ≤ wP c χ ξ₀ * (ξ₀ - 1) * qP c χ ξ₀ := by
    rw [hq]; have : 0 ≤ ξ₀ - 1 := by linarith
    positivity
  have hd0 : 0 ≤ 2 * (c + 1) / (c ^ 2 - χ) := by positivity
  have hnum : ((1 + 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) / (c ^ 2 - χ)) * aP c χ ξ₀ - wP c χ ξ₀ * (ξ₀ - 1) * qP c χ ξ₀)
      ≤ (1 + 2 * (c + 1) / (c ^ 2 - χ)) * aP c χ ξ₀ := by rw [hd₀]; linarith
  have hX0 : 0 ≤ (1 + 2 * (c + 1) / (c ^ 2 - χ)) * aP c χ ξ₀ := by positivity
  unfold ecap
  calc _ ≤ (1 + 2 * (c + 1) / (c ^ 2 - χ)) * aP c χ ξ₀ / (1 - wP c χ ξ₀ / 2) :=
        div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ (1 + 2 * (c + 1) / (c ^ 2 - χ)) * aP c χ ξ₀ / (c / (2 * c + 1)) :=
        div_le_div_of_nonneg_left hX0 hdpos hden
    _ = _ := by rw [ha]; field_simp

/-! ### The exterior derivative -/

/-- `−ξ/√(ξ² − 1)` is a primitive of `1/((ξ² − 1)√(ξ² − 1))` on `ξ > 1`. -/
theorem hasDerivAt_neg_div_sqrt {ξ : ℝ} (hξ : 1 < ξ) :
    HasDerivAt (fun ξ => -(ξ / √(ξ ^ 2 - 1))) (1 / ((ξ ^ 2 - 1) * √(ξ ^ 2 - 1))) ξ := by
  have hp : 0 < ξ ^ 2 - 1 := by nlinarith
  have hs : 0 < √(ξ ^ 2 - 1) := Real.sqrt_pos.mpr hp
  have hsq : √(ξ ^ 2 - 1) ^ 2 = ξ ^ 2 - 1 := Real.sq_sqrt hp.le
  have hd : HasDerivAt (fun ξ : ℝ => ξ ^ 2 - 1) (2 * ξ) ξ := by
    simpa using (hasDerivAt_pow 2 ξ).sub_const 1
  have h := ((hasDerivAt_id' ξ).div (hd.sqrt hp.ne') hs.ne').neg
  refine h.congr_deriv ?_
  field_simp
  rw [hsq]; ring

/-- `ξ/√(ξ² − 1) → 1` as `ξ → ∞`. -/
theorem tendsto_div_sqrt : Tendsto (fun ξ : ℝ => ξ / √(ξ ^ 2 - 1)) atTop (𝓝 1) := by
  have hcont : ContinuousAt (fun t : ℝ => 1 / √(1 - t ^ 2)) 0 := by
    apply ContinuousAt.div continuousAt_const (by fun_prop); simp
  have h := hcont.tendsto.comp tendsto_inv_atTop_zero
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Real.sqrt_one, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with ξ hξ
  have hξ0 : 0 < ξ := by linarith
  have h1 : 0 ≤ 1 - ξ⁻¹ ^ 2 := by
    have : ξ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hξ.le
    nlinarith [inv_pos.mpr hξ0]
  have e : √(ξ ^ 2 - 1) = ξ * √(1 - ξ⁻¹ ^ 2) := by
    rw [← Real.sqrt_sq hξ0.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hξ0.le]
    congr 1; field_simp
  simp only [Function.comp, e]
  have hs : 0 < √(1 - ξ⁻¹ ^ 2) := by
    have : ξ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hξ
    exact Real.sqrt_pos.mpr (by nlinarith [inv_pos.mpr hξ0])
  field_simp

/-- `½ log((ξ − 1)/(ξ + 1)) → 0` as `ξ → ∞`. -/
theorem tendsto_half_log : Tendsto (fun ξ : ℝ => 1 / 2 * log ((ξ - 1) / (ξ + 1))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun ξ : ℝ => (ξ - 1) / (ξ + 1)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun ξ : ℝ => 1 - 2 * (ξ + 1)⁻¹) atTop (𝓝 (1 - 2 * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)))
    rw [mul_zero, sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ξ hξ
    have : ξ + 1 ≠ 0 := by linarith
    field_simp; ring
  have h3 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1).const_mul (1 / 2)
  simpa using h3

/-- **The exterior derivative from an energy cap**: for a rung with `c > 0`, `χ < c²`, `ξ₀ > 1` and
`E ≤ e ψ(1)²` on `[ξ₀, ∞)`, `∫₁^∞ψ'² ≤ ψ(1)²[(ξ₀ − 1)(q(ξ₀)/2)² + e(√(c² − χ)(ξ₀/√(ξ₀² − 1) − 1)
+ (c/2)log((ξ₀ + 1)/(ξ₀ − 1)))]`. -/
theorem integral_psiD_sq_le (hc : 0 < c) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ₀ e : ℝ} (h1 : 1 < ξ₀)
    (he : ∀ ξ, ξ₀ ≤ ξ → energy (aP c χ) (psi c g) (rungU c g) ξ ≤ e * psi c g 1 ^ 2) :
    ∫ ξ in Ioi 1, psiD c g ξ ^ 2 ≤ psi c g 1 ^ 2 * ((ξ₀ - 1) * (qP c χ ξ₀ / 2) ^ 2
      + e * (√(c ^ 2 - χ) * (ξ₀ / √(ξ₀ ^ 2 - 1) - 1) + c / 2 * log ((ξ₀ + 1) / (ξ₀ - 1)))) := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hc2 : 0 < c ^ 2 := by positivity
  set D := c ^ 2 - χ with hDdef
  have hD : 0 < D := by rw [hDdef]; linarith
  set A := psi c g 1 ^ 2 with hA
  have hA0 : 0 ≤ A := sq_nonneg _
  set K := e * A with hK
  have hK0 : 0 ≤ K := by
    refine le_trans ?_ (he ξ₀ le_rfl)
    unfold energy
    have := aP_pos h1 hc2 hχc
    positivity
  have hint := integrable_psiD_sq hc hgc
  -- the edge piece `(1, ξ₀]`
  have hnear : ∫ ξ in Ioc 1 ξ₀, psiD c g ξ ^ 2 ≤ (ξ₀ - 1) * (A * (qP c χ ξ₀ / 2) ^ 2) := by
    have hpt : ∀ t ∈ Ioc 1 ξ₀, psiD c g t ^ 2 ≤ A * (qP c χ ξ₀ / 2) ^ 2 := by
      intro t ht
      have h := abs_psiD_mul_le hχc hg hg₁ hg₂c hang ht.1.le
      have hqt : qP c χ t ≤ qP c χ ξ₀ := by
        have h2 : t ^ 2 ≤ ξ₀ ^ 2 := pow_le_pow_left₀ (by linarith [ht.1]) ht.2 2
        unfold qP; nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg c)]
      have hb : |psiD c g t| ≤ qP c χ ξ₀ * |psi c g 1| / 2 := by
        have h2 : 2 * |psiD c g t| ≤ (t + 1) * |psiD c g t| := by
          nlinarith [abs_nonneg (psiD c g t), ht.1]
        nlinarith [mul_le_mul_of_nonneg_right hqt (abs_nonneg (psi c g 1))]
      have h3 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [sq_abs] at h3
      calc psiD c g t ^ 2 ≤ (qP c χ ξ₀ * |psi c g 1| / 2) ^ 2 := h3
        _ = A * (qP c χ ξ₀ / 2) ^ 2 := by rw [hA, ← sq_abs (psi c g 1)]; ring
    have hc' : ∫ ξ in Ioc 1 ξ₀, A * (qP c χ ξ₀ / 2) ^ 2 = (ξ₀ - 1) * (A * (qP c χ ξ₀ / 2) ^ 2) := by
      rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    rw [← hc']
    exact setIntegral_mono_on hint.integrableOn (integrableOn_const (by simp)) measurableSet_Ioc hpt
  -- the far piece `(ξ₀, ∞)`
  set G : ℝ → ℝ := fun ξ => K * (√D * -(ξ / √(ξ ^ 2 - 1)) + c * (1 / 2 * log ((ξ - 1) / (ξ + 1)))) with hGdef
  set g' : ℝ → ℝ := fun ξ => K * (√D * (1 / ((ξ ^ 2 - 1) * √(ξ ^ 2 - 1))) + c * (1 / (ξ ^ 2 - 1))) with hg'def
  have hGd : ∀ ξ ∈ Ici ξ₀, HasDerivAt G (g' ξ) ξ := fun ξ hξ => by
    have hξ1 : 1 < ξ := lt_of_lt_of_le h1 hξ
    exact (((hasDerivAt_neg_div_sqrt hξ1).const_mul √D).add
      ((hasDerivAt_half_log hξ1).const_mul c)).const_mul K
  have hg'0 : ∀ ξ ∈ Ioi ξ₀, 0 ≤ g' ξ := fun ξ hξ => by
    have hξ1 : 1 < (ξ : ℝ) := lt_trans h1 hξ
    have hp : 0 < ξ ^ 2 - 1 := by nlinarith
    simp only [hg'def]; positivity
  have hGlim : Tendsto G atTop (𝓝 (K * (√D * -1 + c * 0))) :=
    (((tendsto_div_sqrt.neg).const_mul √D).add (tendsto_half_log.const_mul c)).const_mul K
  have hIg' := integral_Ioi_of_hasDerivAt_of_nonneg' hGd hg'0 hGlim
  have hintg' := integrableOn_Ioi_deriv_of_nonneg' hGd hg'0 hGlim
  have hfar : ∫ ξ in Ioi ξ₀, psiD c g ξ ^ 2 ≤ ∫ ξ in Ioi ξ₀, g' ξ := by
    refine setIntegral_mono_on hint.integrableOn hintg' measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := lt_trans h1 ht
    have hp : 0 < pP t := pP_pos ht1
    have ha := aP_pos ht1 hc2 hχc
    have hE := he t (le_of_lt ht)
    have hu2 : rungU c g t ^ 2 ≤ aP c χ t * K := by
      have h0 : rungU c g t ^ 2 / aP c χ t ≤ K := by
        unfold energy at hE
        have : 0 ≤ aP c χ t * psi c g t ^ 2 := by positivity
        rw [hK]; linarith
      rw [div_le_iff₀ ha] at h0; linarith
    have hsq : pP t * qP c χ t = pP t * (D + c ^ 2 * pP t) := by unfold pP qP; rw [hDdef]; ring
    have hsp : √(pP t) ^ 2 = pP t := Real.sq_sqrt hp.le
    have hsp0 : 0 < √(pP t) := Real.sqrt_pos.mpr hp
    have hsD : √D ^ 2 = D := Real.sq_sqrt hD.le
    have hsD0 : 0 ≤ √D := Real.sqrt_nonneg _
    have haB : aP c χ t ≤ √(pP t) * √D + c * pP t := by
      apply le_of_sq_le_sq _ (by positivity)
      rw [aP_sq ht1 hc2 hχc, hsq]
      nlinarith [mul_nonneg (mul_nonneg hsp0.le hsD0) (mul_nonneg hc.le hp.le)]
    have hpt : pP t = t ^ 2 - 1 := rfl
    rw [rungU_eq] at hu2
    have hψ : psiD c g t ^ 2 ≤ K * (√(pP t) * √D + c * pP t) / pP t ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc psiD c g t ^ 2 * pP t ^ 2 = (pP t * psiD c g t) ^ 2 := by ring
        _ ≤ aP c χ t * K := hu2
        _ ≤ (√(pP t) * √D + c * pP t) * K := mul_le_mul_of_nonneg_right haB hK0
        _ = K * (√(pP t) * √D + c * pP t) := by ring
    refine hψ.trans (le_of_eq ?_)
    simp only [hg'def]
    rw [← hpt]
    field_simp
    have hmm : √(pP t) * √(pP t) = pP t := Real.mul_self_sqrt hp.le
    linear_combination (K * √D) * hmm
  have hsplit : ∫ ξ in Ioi 1, psiD c g ξ ^ 2
      = (∫ ξ in Ioc 1 ξ₀, psiD c g ξ ^ 2) + ∫ ξ in Ioi ξ₀, psiD c g ξ ^ 2 := by
    rw [← Ioc_union_Ioi_eq_Ioi h1.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint.integrableOn hint.integrableOn
  have hval : ∫ ξ in Ioi ξ₀, g' ξ = K * (√D * (ξ₀ / √(ξ₀ ^ 2 - 1) - 1) + c / 2 * log ((ξ₀ + 1) / (ξ₀ - 1))) := by
    rw [hIg']
    simp only [hGdef]
    have e : (ξ₀ + 1) / (ξ₀ - 1) = ((ξ₀ - 1) / (ξ₀ + 1))⁻¹ := by rw [inv_div]
    rw [e, Real.log_inv]; ring
  rw [hsplit]
  calc _ ≤ (ξ₀ - 1) * (A * (qP c χ ξ₀ / 2) ^ 2) + ∫ ξ in Ioi ξ₀, g' ξ := add_le_add hnear hfar
    _ = _ := by rw [hval, hK]; ring

end Cvs.Prolate.Envelope.RungEdgeMassExterior
