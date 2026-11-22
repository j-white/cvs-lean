import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.DeepCellFloorAmplitude
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.DirichletDualFloorShifted
import Cvs.Prolate.Gram.DiscretePotentialAllRungs
import Cvs.Prolate.Gram.EndpointAmplitudeAllRungs
import Cvs.Prolate.Gram.EndpointAmplitudeFloor
import Cvs.Prolate.Gram.EquilibriumPotential
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinDualCertificate
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RegularSolutionEnergyComparability
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.CellFloorSandwichPosDef

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The band cell floor `σ'_j ≥ e^{−εc}` on `T_j ≥ ¾`, unconditionally

Above `¾` the exponent `Ag + Ψ_a` is at most `2(t_e(a) − √3/2)`, which vanishes as `a ↓ ½`; `DeepCellFloorAmplitude`'s assembly with
`EndpointAmplitudeAllRungs`'s amplitude and `DiscretePotentialAllRungs`'s potential on every rung then gives `DeepRemainderCellFloors`'s `BandCellFloor`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory Polynomial Finset
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC)
open Cvs.Prolate.Gram.EquilibriumPotential (tE wA psiA)
open Cvs.Prolate.Gram.DeepCellFloorAmplitude

namespace Cvs.Prolate.Gram.BandCellFloorUnconditional
open Cvs.ZeroCounting

/-- **`Δ_a ≤ 2(t_e − √3/2)` above `¾`**: for `½ ≤ a`, `a² ≤ 9/25` and `¾ ≤ T`,
`Ag(T, a) + Ψ_a(T) ≤ 2(t_e(a) − √3/2)`. -/
theorem agmonInt_add_psiA_le_band {a T : ℝ} (ha : 1 / 2 ≤ a) (ha2 : a ^ 2 ≤ 9 / 25) (hT3 : 3 / 4 ≤ T) :
    agmonInt T a + psiA a T ≤ 2 * (tE a - √3 / 2) := by
  have ha0 : 0 ≤ a := by linarith
  have ha2' : 2 * a ^ 2 < 1 := by linarith
  have hte := Cvs.Prolate.Gram.EquilibriumPotential.tE_lt_one ha2'
  have hte96 := tE_le ha0 ha2
  have hT0 : 0 ≤ T := by linarith
  have hs3 : (√3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs3le : √3 / 2 ≤ tE a := by
    have hmono : tE (1 / 2) ≤ tE a := by
      unfold tE
      have hsq : (2 * (1 / 2) * √(1 - (1 / 2) ^ 2)) ^ 2 ≤ (2 * a * √(1 - a ^ 2)) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by nlinarith)]
        have hq : 1 / 4 ≤ a ^ 2 := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show (0 : ℝ) ≤ 3 / 4 - a ^ 2 by linarith)]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    have h12 : tE (1 / 2) = √3 / 2 := by
      unfold tE
      rw [show (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num, show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num,
        Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num)]
      ring
    linarith
  have hsT : √3 / 2 ≤ √T := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ √3 / 2), hs3]; exact Real.sqrt_le_sqrt hT3
  have hsT2 : √T ^ 2 = T := Real.sq_sqrt hT0
  rcases le_or_gt T (tE a ^ 2) with hTe | hTe
  · rw [agmonInt_add_psiA ha0 ha2' hT0 hTe]
    have hsTe : √T ≤ tE a := by
      rw [← Real.sqrt_sq (Cvs.Prolate.Gram.EquilibriumPotential.tE_nonneg ha0)]; exact Real.sqrt_le_sqrt hTe
    have hb : ∫ t in √T..tE a, √(t ^ 2 - T) / √(1 - t ^ 2) ≤ ∫ t in √T..tE a, (4 : ℝ) := by
      refine intervalIntegral.integral_mono_on hsTe (intervalIntegrable_f (Real.sqrt_nonneg T) hsTe hte)
        intervalIntegrable_const fun t ht => ?_
      have ht1 : t ≤ 24 / 25 := ht.2.trans hte96
      have ht0 : 0 ≤ t := (Real.sqrt_nonneg T).trans ht.1
      have hp : (7 / 25 : ℝ) ≤ √(1 - t ^ 2) := by
        rw [show (7 / 25 : ℝ) = √((7 / 25) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hn : √(t ^ 2 - T) ≤ 1 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by nlinarith)
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hb
    linarith
  · have hat : a ≤ √T := (Cvs.Prolate.Gram.EquilibriumPotential.le_tE ha0 (by nlinarith)).trans (by
      rw [← Real.sqrt_sq (Cvs.Prolate.Gram.EquilibriumPotential.tE_nonneg ha0)]; exact Real.sqrt_le_sqrt hTe.le)
    have hag : agmonInt T a = 0 := by
      rw [agmonInt, intervalIntegral.integral_symm, integral_zero_of_le hat (by rw [hsT2]) ha0, neg_zero]
    have hpsi : psiA a T = 0 := by
      unfold psiA
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
      · simp
      · rw [uIcc_of_le (Cvs.Prolate.Gram.EquilibriumPotential.tE_nonneg ha0)] at ht
        simp only
        rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith [ht.1, ht.2]), mul_zero]
    rw [hag, hpsi]
    linarith

/-- **The band cell floor holds**: for every `ε > 0`, eventually every rung with `T_j ≥ ¾` has `σ'_j ≥ e^{−εc}`,
from the endpoint amplitude and the discrete potential on every rung. -/
theorem bandCellFloor : Cvs.Prolate.Gram.DeepRemainderCellFloors.BandCellFloor := by
  intro ε hε
  -- the endpoint window
  have hcont : ContinuousAt tE (1 / 2) := by unfold tE; fun_prop
  obtain ⟨ρ₀, hρ₀, hρ₀'⟩ := Metric.continuousAt_iff.mp hcont (ε / 16) (by positivity)
  set ρ := min (ρ₀ / 2) (1 / 10) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by norm_num)
  have h12 : tE (1 / 2) = √3 / 2 := by
    unfold tE
    rw [show (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num, show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num,
      Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num)]
    ring
  have htE : ∀ a ∈ Icc (1 / 2 : ℝ) (1 / 2 + ρ), tE a - √3 / 2 ≤ ε / 16 := fun a ha => by
    have hd : dist a (1 / 2) < ρ₀ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [ha.1])]
      linarith [ha.2, min_le_left (ρ₀ / 2) (1 / 10)]
    have := hρ₀' hd
    rw [Real.dist_eq, h12] at this
    linarith [le_abs_self (tE a - √3 / 2)]
  set δ := ε / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsq := eventually_sq_le_exp (η := ε / 4 * (2 * π)) (by positivity)
  filter_upwards [Cvs.Prolate.Gram.EndpointAmplitudeAllRungs.ampFloor_all ρ hρ0 δ hδ0, Cvs.Prolate.Gram.DiscretePotentialAllRungs.potFloor_all δ hδ0, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, hsq]
    with x hAx hPx hx hsqx
  intro j hj
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by linarith
  obtain ⟨a, ha, hamp⟩ := hAx j
  have ha35 : a ≤ 3 / 5 := ha.2.trans (by linarith [min_le_right (ρ₀ / 2) (1 / 10)])
  obtain ⟨S, hS, hxS, hSx, hR, hres⟩ := hPx j a ⟨ha.1, ha35⟩
  have ha1 : a < 1 := by linarith
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; exact j.elim0
    · exact h
  have hdeg : (Qj x j).degree < S.card := by
    rw [degree_Qj]
    exact_mod_cast (show x - 1 < S.card by omega)
  have hkey := Cvs.Prolate.Gram.DirichletDualFloorShifted.dirichlet_le_sigmaP hx j ha.1 ha1 S hS hdeg (fun b hb => eval_Qj_eq_zero x j hb)
  -- the levels
  have hT0 : 0 ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j := by
    unfold Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT
    exact div_nonneg (Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec _ (Cvs.Prolate.EvenRungsByIndex.lev_spec (Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx j)).1)
      (by positivity)
  set T := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j with hT
  set K := 2 * c * psiA a T + δ * c with hK
  set R := Rj x j S with hRdef
  have hR2 : 0 < R ^ 2 := by positivity
  -- the denominator
  have hg : ∀ σ ∈ S, (Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ / Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ) ^ 2 ≤ 4 * (R ^ 2 * Real.exp K) := by
    intro σ hσ
    have hg4 := Cvs.Prolate.RegularSolutionEnergyComparability.quarter_le_dirG_sq (c := c) (by linarith [ha.1]) ha1 (hS σ hσ)
    have hg0 : 0 < Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ ^ 2 := by linarith
    rw [div_pow, div_le_iff₀ hg0]
    have := hres σ hσ
    have hRe : 0 ≤ R ^ 2 * Real.exp K := by positivity
    nlinarith
  have hD : ∑ σ ∈ S, (Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ / Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ) ^ 2 ≤ S.card * (4 * (R ^ 2 * Real.exp K)) := by
    have := Finset.sum_le_sum hg
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  -- the denominator is positive: some residue is nonzero
  have hDpos : 0 < ∑ σ ∈ S, (Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ / Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ) ^ 2 := by
    have hProd : ∏ σ ∈ S, (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j - σ) ≠ 0 := by
      intro h0; apply hR; rw [hRdef, Rj, h0, div_zero]
    have hnot : ∀ σ ∈ S, Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j ≠ id σ := fun σ hσ h =>
      hProd (Finset.prod_eq_zero hσ (by rw [h]; simp))
    have hsum := Cvs.Prolate.Gram.RobinDualCertificate.sum_resid_div (Set.injOn_id (S : Set ℝ)) hdeg hnot
    obtain ⟨σ, hσ, hrσ⟩ : ∃ σ ∈ S, Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hR
      simp only [id] at hsum
      rw [hRdef, Rj, ← hsum]
      exact Finset.sum_eq_zero fun σ hσ => by rw [hall σ hσ, zero_div]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun σ _ => sq_nonneg _) hσ)
    have hgne := Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG_ne_zero (c := c) (by linarith [ha.1]) ha1 (hS σ hσ)
    positivity
  have hSpos : (0 : ℝ) < S.card := by
    have : 0 < S.card := lt_of_lt_of_le hx1 hxS
    exact_mod_cast this
  have hlow : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * Real.exp (-K) / (4 * S.card) ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x) j := by
    refine le_trans ?_ hkey
    rw [mul_pow, div_le_div_iff₀ (by positivity) hDpos]
    have hexp : Real.exp (-K) * Real.exp K = 1 := by rw [← Real.exp_add]; simp
    calc Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * Real.exp (-K) *
          ∑ σ ∈ S, (Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Qj x j) σ / Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ) ^ 2
        ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * Real.exp (-K) * (S.card * (4 * (R ^ 2 * Real.exp K))) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * R ^ 2 * (4 * S.card) * (Real.exp (-K) * Real.exp K) := by ring
      _ = _ := by rw [hexp, mul_one, hRdef, Rj]
  -- the exponent
  have hΔ := agmonInt_add_psiA_le_band ha.1 (by nlinarith [ha.1]) hj
  have htEa := htE a ha
  have hlog4 : Real.log (4 * S.card) ≤ ε / 4 * c := by
    have h1 : 4 * (S.card : ℝ) ≤ 4 * (x : ℝ) ^ 2 := by linarith
    have h2 := h1.trans hsqx
    rw [← Real.log_exp (ε / 4 * c)]
    have : ε / 4 * (2 * π) * (x : ℝ) = ε / 4 * c := by rw [hc]; ring
    rw [this] at h2
    exact Real.log_le_log (by positivity) h2
  have hfin : Real.exp (-(ε * c)) ≤
      Real.exp (-(2 * c * agmonInt T a) - δ * c) * Real.exp (-K) / (4 * S.card) := by
    rw [le_div_iff₀ (by positivity), ← Real.exp_add,
      show 4 * (S.card : ℝ) = Real.exp (Real.log (4 * S.card)) from (Real.exp_log (by positivity)).symm,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hK, hδ]
    nlinarith [mul_le_mul_of_nonneg_left hΔ hc0.le]
  calc Real.exp (-(ε * c))
      ≤ Real.exp (-(2 * c * agmonInt T a) - δ * c) * Real.exp (-K) / (4 * S.card) := hfin
    _ ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * Real.exp (-K) / (4 * S.card) := by
        gcongr
    _ ≤ _ := hlow

end Cvs.Prolate.Gram.BandCellFloorUnconditional

end
