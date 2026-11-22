import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.BandCellFloorUnconditional
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.DirichletNodeCountPotFloor
import Cvs.Prolate.Gram.PlungeLawBandCellFloor
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.TunnellingFloorSumBand
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.PlungePowerSumPolylog
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Prolate.RungsAboveLevelCount
import Cvs.Prolate.TunnellingIntegralMargin
import Cvs.Prolate.TunnellingIntegralsAgree
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Upstream.CellFloorSandwichPosDef

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tunnelling floor sum from the band floor above any level `τ < 1`

On `¾ < T_j ≤ τ` the plunge law gives `1 − λ_{4j} ≤ c^K e^{−c(1 − τ)}` (Cvs.Prolate.RungsAboveLevelCount) and Cvs.Prolate.Gram.BandCellFloorUnconditional gives `σ'_j ≥ e^{−εc}`, so
those terms are exponentially small; the band floor `σ'_j ≥ x^{−ε}` is needed only on `T_j > τ`.
-/

noncomputable section

open Real Set Filter Finset Topology
open Cvs.Prolate.EvenRungsByIndex (lev lamR)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram)
open Cvs.Route.Visibility.WindowChainCellFloors (finOfSF)
open Cvs.Prolate.TunnellingIntegralMargin (gStar)

namespace Cvs.Prolate.Gram.TunnellingFloorSumAbove
open Cvs.ZeroCounting

/-- **The band floor above `τ`**: `σ'_j ≥ x^{−ε}` on the rungs with `T_j > τ`, for every `ε > 0`. -/
def BandFloorAbove (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, τ < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    (x : ℝ) ^ (-ε) ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j)

/-- A band floor above `τ` is one above every `τ' ≥ τ`. -/
theorem BandFloorAbove.mono {τ τ' : ℝ} (h : BandFloorAbove τ) (hτ : τ ≤ τ') : BandFloorAbove τ' :=
  fun ε hε => (h ε hε).mono fun _ hx j hj => hx j (lt_of_le_of_lt hτ hj)

/-- On a rung with `W ≥ w ≥ 0`, `1 − λ ≤ c^K e^{−2cW}` and `σ' ≥ e^{−wc/2}`, the term `√((1 − λ)^p)/√σ'` is at
most `√(c^{Kp}e^{−wc/2})`. -/
theorem edge_term_le {c ω σ W K p w : ℝ} (hc : 0 < c) (hp : 1 / 2 ≤ p) (hω0 : 0 ≤ ω)
    (hω : ω ≤ c ^ K * exp (-(2 * c * W))) (hσ : exp (-(w / 2 * c)) ≤ σ) (hw : 0 ≤ w) (hW : w ≤ W) :
    √(ω ^ p) / √σ ≤ √(c ^ (K * p) * exp (-(w / 2) * c)) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le (exp_pos _) hσ
  rw [← sqrt_div' _ hσ0.le]
  refine sqrt_le_sqrt ?_
  have h1 : ω ^ p ≤ c ^ (K * p) * exp (-(2 * c * W) * p) := by
    calc ω ^ p ≤ (c ^ K * exp (-(2 * c * W))) ^ p := rpow_le_rpow hω0 hω (by linarith)
      _ = _ := by rw [mul_rpow (by positivity) (by positivity), ← rpow_mul hc.le, ← exp_mul]
  rw [div_le_iff₀ hσ0]
  calc ω ^ p ≤ c ^ (K * p) * exp (-(2 * c * W) * p) := h1
    _ ≤ c ^ (K * p) * (exp (-(w / 2) * c) * exp (-(w / 2 * c))) := by
        rw [← exp_add]
        refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity)
        have hWp : w ≤ 2 * p * W := by nlinarith
        nlinarith
    _ ≤ c ^ (K * p) * exp (-(w / 2) * c) * σ := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hσ (by positivity)

/-- `x·√(c^{Kp}e^{−gc}) ≤ 1` at `c = 2πx`, eventually in `x`, for `g > 0`. -/
theorem eventually_small (K p : ℝ) {g : ℝ} (hg : 0 < g) :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) * √((2 * π * x) ^ (K * p) * exp (-g * (2 * π * x))) ≤ 1 := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (K * p + 2) g hg
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hev := (ht.comp hc).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, eventually_ge_atTop 1] with x h hx1
  have hx : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hc0 : 0 < 2 * π * (x : ℝ) := by positivity
  have hxc : (x : ℝ) ≤ 2 * π * x := by nlinarith [pi_gt_three]
  simp only [Function.comp] at h
  have hpow : (2 * π * (x : ℝ)) ^ (K * p + 2) = (2 * π * x) ^ (K * p) * (2 * π * x) ^ 2 := by
    rw [rpow_add hc0, rpow_two]
  rw [show (x : ℝ) * √((2 * π * (x : ℝ)) ^ (K * p) * exp (-g * (2 * π * x)))
      = √((x : ℝ) ^ 2 * ((2 * π * (x : ℝ)) ^ (K * p) * exp (-g * (2 * π * x)))) by
    rw [sqrt_mul (sq_nonneg _), sqrt_sq (by linarith)], ← sqrt_one]
  refine sqrt_le_sqrt ?_
  calc (x : ℝ) ^ 2 * ((2 * π * x) ^ (K * p) * exp (-g * (2 * π * x)))
      ≤ (2 * π * x) ^ 2 * ((2 * π * x) ^ (K * p) * exp (-g * (2 * π * x))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hxc 2) (by positivity)
    _ = (2 * π * x) ^ (K * p + 2) * exp (-g * (2 * π * x)) := by rw [hpow]; ring
    _ ≤ 1 := h.le

/-- **The tunnelling floor sum from the band floor above `τ < 1`**: `ExtTunnelSum η` for every `η ≥ 0`. -/
theorem extTunnelSum_of_bandFloorAbove {τ : ℝ} (hτ1 : τ < 1) (hB0 : BandFloorAbove τ) {η : ℝ} (hη : 0 ≤ η) :
    Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η := by
  intro ε hε
  set τ' := max τ (3 / 4) with hτ'
  have hτ'1 : τ' < 1 := max_lt hτ1 (by norm_num)
  have hτ'3 : 3 / 4 ≤ τ' := le_max_right _ _
  have hB := hB0.mono (le_max_left τ (3 / 4))
  set w : ℝ := (1 - τ') / 2 with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  set g : ℝ := min (gStar / 2) (w / 2) with hg
  have hg0 : 0 < g := lt_min (by linarith [Cvs.Prolate.TunnellingIntegralMargin.gStar_pos]) (by linarith)
  obtain ⟨K, hPK⟩ := Cvs.Prolate.Gram.PlungeLawBandCellFloor.plungeLaw
  set p : ℝ := 1 / 2 + η with hpdef
  have hp : 1 / 2 ≤ p := by linarith
  have hq : 0 < p / 2 := by linarith
  obtain ⟨M, hM⟩ := Cvs.Prolate.Gram.TunnellingFloorSumBand.exists_plungePoly_le hq (by linarith : 0 < ε / 2)
  refine ⟨1 + M, ?_⟩
  have hcT : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [hPK, Cvs.Prolate.Gram.PlungeLawBandCellFloor.cPbFloor_of_deep Cvs.Prolate.Gram.DirichletNodeCountPotFloor.deepCellFloor (gStar / 2) (by linarith [Cvs.Prolate.TunnellingIntegralMargin.gStar_pos]),
    Cvs.Prolate.Gram.BandCellFloorUnconditional.bandCellFloor (w / 2) (by linarith), hB ε hε, eventually_small K p hg0, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale,
    Cvs.Prolate.PlungePowerSumPolylog.eventually_sum_rpow_le hq, hM, hcT.eventually_ge_atTop (5 / (1 - τ'))]
    with x hPx hDx hEx hBx hsmall hx hsum hMx hc5
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast Cvs.Prolate.RungSpanBernsteinNikolskii.one_le_of_scale hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith
  have hlam : ∀ j : Cvs.Approximant.SpineSubspace.SF x, 1 / 2 ≤ lamR (2 * π * x) (2 * (j : ℕ)) ∧ lamR (2 * π * x) (2 * (j : ℕ)) ≤ 1 :=
    fun j => ⟨Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx (Cvs.Approximant.SpineSubspace.SF_lt x j j.2),
      Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 ((Cvs.Prolate.RungSpanBernsteinNikolskii.spine_landau hx).1 j (Cvs.Approximant.SpineSubspace.SF_lt x j j.2))⟩
  set f : Cvs.Approximant.SpineSubspace.SF x → ℝ := fun j => √((1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ p)
    / √(Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (cellGram x) (finOfSF j)) with hf
  set Md : ℝ := √((2 * π * x) ^ (K * p) * exp (-g * (2 * π * x)))
  have hMd1 : √((2 * π * x) ^ (K * p) * exp (-(gStar / 2) * (2 * π * x))) ≤ Md := by
    refine sqrt_le_sqrt (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity))
    have := min_le_left (gStar / 2) (w / 2)
    nlinarith
  have hMd2 : √((2 * π * x) ^ (K * p) * exp (-(w / 2) * (2 * π * x))) ≤ Md := by
    refine sqrt_le_sqrt (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity))
    have := min_le_right (gStar / 2) (w / 2)
    nlinarith
  -- the rungs up to `τ'`
  have hlow : ∑ j ∈ univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j ≤ τ'), f j ≤ 1 := by
    have hterm : ∀ j ∈ univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j ≤ τ'), f j ≤ Md := by
      intro j hj
      have hT : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j ≤ τ' := (Finset.mem_filter.1 hj).2
      have hlev : lev (2 * π * x) (2 * (j : ℕ)) ≤ τ' * (2 * π * x) ^ 2 := by
        have := hT; unfold Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev at this; rwa [div_le_iff₀ (by positivity)] at this
      have h5 : 5 * (2 * π * x) ≤ (2 * π * x) ^ 2 - lev (2 * π * x) (2 * (j : ℕ)) := by
        rw [div_le_iff₀ (by linarith)] at hc5
        nlinarith
      rcases le_or_gt (Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j) (3 / 4) with hT3 | hT3
      · exact (Cvs.Prolate.Gram.TunnellingFloorSumPlunge.deep_term_le hc0 hp (by linarith [(hlam j).2]) (hPx j h5) (hDx j hT3)
          (Cvs.Prolate.TunnellingIntegralMargin.half_gStar_le hp hT3)).trans hMd1
      · have hE := hEx (finOfSF j) (by rw [← Cvs.Prolate.TunnellingIntegralsAgree.tLev_eq]; exact hT3.le)
        have hW : w ≤ Cvs.Prolate.TunnellingIntegralMargin.tunW (Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j) := by
          have := Cvs.Prolate.RungsAboveLevelCount.half_one_sub_le_tunW (T := Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j) (by linarith) (by linarith)
          rw [hw]; linarith
        exact (edge_term_le hc0 hp (by linarith [(hlam j).2]) (hPx j h5) hE hw0.le hW).trans hMd2
    have hcard : ((univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j ≤ τ')).card : ℝ) ≤ x := by
      have h1 := Finset.card_filter_le (univ : Finset (Cvs.Approximant.SpineSubspace.SF x)) (fun j => Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j ≤ τ')
      have h2 : (univ : Finset (Cvs.Approximant.SpineSubspace.SF x)).card ≤ x := by
        rw [Finset.card_univ, Fintype.card_coe]
        exact (Finset.card_filter_le _ _).trans (Finset.card_range x).le
      exact_mod_cast h1.trans h2
    calc _ ≤ ∑ _j ∈ univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j ≤ τ'), Md := Finset.sum_le_sum hterm
      _ = (univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j ≤ τ')).card * Md := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ x * Md := mul_le_mul_of_nonneg_right hcard (sqrt_nonneg _)
      _ ≤ 1 := hsmall
  -- the rungs above `τ'`
  have hband : ∑ j ∈ univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => ¬ Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j ≤ τ'), f j
      ≤ (x : ℝ) ^ (ε / 2) * (M * (x : ℝ) ^ (ε / 2)) := by
    set s := univ.filter (fun j : Cvs.Approximant.SpineSubspace.SF x => ¬ Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j ≤ τ')
    have hterm : ∀ j ∈ s, f j ≤ (x : ℝ) ^ (ε / 2) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (p / 2) := by
      intro j hj
      have hT : τ' < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j := not_le.1 (Finset.mem_filter.1 hj).2
      exact Cvs.Prolate.Gram.TunnellingFloorSumPlunge.band_term_le hx0 (by linarith [(hlam j).2]) (hBx j hT)
    have hs : ∑ j ∈ s, (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (p / 2)
        ≤ ∑ j : Cvs.Approximant.SpineSubspace.SF x, (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (p / 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun j _ _ =>
        rpow_nonneg (by linarith [(hlam j).2]) _
    calc _ ≤ ∑ j ∈ s, (x : ℝ) ^ (ε / 2) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (p / 2) :=
          Finset.sum_le_sum hterm
      _ = (x : ℝ) ^ (ε / 2) * ∑ j ∈ s, (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (p / 2) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hs.trans (hsum.trans hMx)) (by positivity)
  -- assembly
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Cvs.Approximant.SpineSubspace.SF x))
    (fun j : Cvs.Approximant.SpineSubspace.SF x => Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j ≤ τ') f
  have hxe : (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (ε / 2) = (x : ℝ) ^ ε := by
    rw [← rpow_add hx0]; ring_nf
  have hxe1 : (1 : ℝ) ≤ (x : ℝ) ^ ε := one_le_rpow hx1 hε.le
  change ∑ j : Cvs.Approximant.SpineSubspace.SF x, f j ≤ _
  rw [← hsplit]
  calc _ ≤ 1 + (x : ℝ) ^ (ε / 2) * (M * (x : ℝ) ^ (ε / 2)) := add_le_add hlow hband
    _ = 1 + M * (x : ℝ) ^ ε := by rw [← hxe]; ring
    _ ≤ (1 + M) * (x : ℝ) ^ ε := by nlinarith

end Cvs.Prolate.Gram.TunnellingFloorSumAbove

end
