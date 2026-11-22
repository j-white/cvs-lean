import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.DeepCellFloorAmplitude
import Cvs.Prolate.Gram.DirichletNodeCountPotFloor
import Cvs.Prolate.Gram.EquilibriumPotential
import Cvs.Prolate.Gram.PotentialFloorFromCounts
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.ResidueRatioLogSums
import Cvs.Prolate.Gram.RobinDualCertificate
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.SelectionTargetMeasure
import Cvs.Prolate.Gram.TruncatedPotentialBound
import Cvs.Prolate.Gram.WeylCountsDiscretePotential
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungWeylCount
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.GreedySelectionTarget
import Cvs.Upstream.SliceMeasurePushforward

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The discrete potential on every rung

`PotentialFloorFromCounts`'s residue-ratio bound uses `T_j ≤ ¾` only through `T_j ≤ 1`, so `RungCount ∧ DirCount` give the node sets and
residue bounds of `PotFloor` on every rung `j < x`; with `DirichletNodeCountPotFloor`'s two counts this holds unconditionally.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory Polynomial Finset
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)
open Cvs.Upstream.GreedySelectionTarget (cnt)
open Cvs.Prolate.Gram.SelectionTargetMeasure (zMeas muP muM Fcdf zcdf phiZ)
open Cvs.Prolate.Gram.PotentialFloorFromCounts

namespace Cvs.Prolate.Gram.DiscretePotentialAllRungs
open Cvs.ZeroCounting

/-- **The residue ratio at any level `T_j ≤ 1`**: for a node `σ = c²s` of the selection,
`log|r_σ| − log|R_j| ≤ cΨ_a(T_j) + cη(U) + log c²` plus the four Cvs.Upstream.DiscreteContinuousLogPotential errors. -/
theorem log_ratio_le_all {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) (hj : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ 1)
    {a U : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) (hU : 4 ≤ U)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hadd : ν + muM a U = zMeas + muP a U) (hνle : ν ≤ zMeas + muP a U)
    (hνIic : ∀ y, ν.real (Iic y) = Fcdf a U y) {S' : Finset ℝ}
    (hS' : ∀ s ∈ S', regSol (sqC (2 * π * x)) ((2 * π * x) ^ 2 * s) a = 0 ∧ a ^ 2 < s ∧ s ≤ U ^ 2 + 2)
    (hTS : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ∉ S') {ER ES : ℝ}
    (hER : ∀ u, |(cnt (rungSet x) u : ℝ) - 2 * π * x * zMeas.real (Iic u)| ≤ ER)
    (hES : ∀ u, |(cnt S' u : ℝ) - 2 * π * x * Fcdf a U u| ≤ ES) {r γ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hγ : 0 < γ) (hγr : γ ≤ r) (hγc : γ ≤ π / (8 * (3 + (U ^ 2 + 2)) * (2 * π * x) ^ 3)) {s : ℝ} (hs : s ∈ S')
    (hres : Cvs.Prolate.Gram.RobinDualCertificate.resid (S'.image ((2 * π * x) ^ 2 * ·)) id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) ((2 * π * x) ^ 2 * s) ≠ 0)
    (hR : Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j (S'.image ((2 * π * x) ^ 2 * ·)) ≠ 0) :
    log |Cvs.Prolate.Gram.RobinDualCertificate.resid (S'.image ((2 * π * x) ^ 2 * ·)) id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) ((2 * π * x) ^ 2 * s)| -
        log |Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j (S'.image ((2 * π * x) ^ 2 * ·))| ≤
      2 * π * x * Cvs.Prolate.Gram.EquilibriumPotential.psiA a (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) + 2 * π * x * Cvs.Prolate.Gram.TruncatedPotentialBound.etaU U +
        (log ((2 * π * x) ^ 2) + errU (2 * π * x) (U ^ 2 + 2) r (ER + 1) + errL (2 * π * x) (U ^ 2 + 2) r γ ER +
          errU (2 * π * x) (U ^ 2 + 2) r ES + errL (2 * π * x) (U ^ 2 + 2) r γ ES) := by
  classical
  have : Fact (a ∈ Icc (1 / 2 : ℝ) (3 / 5)) := ⟨ha⟩
  obtain ⟨h0, hat, hte, h2⟩ := Cvs.Prolate.Gram.SelectionTargetMeasure.tE_facts ha
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  set B := U ^ 2 + 2 with hB
  have hB1 : 1 ≤ B := by nlinarith
  have hB2 : B ≤ 2 * U ^ 2 := by nlinarith
  set T := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j with hT
  set Zj := rungSetErase x j with hZj
  set S := S'.image (c ^ 2 * ·) with hS
  have hinj : Function.Injective (c ^ 2 * · : ℝ → ℝ) := mul_right_injective₀ (by positivity)
  have hT0 : 0 ≤ T := levT_nonneg hx j
  have hsS := hS' s hs
  have hs0 : 0 ≤ s := (sq_nonneg a).trans hsS.2.1.le
  -- the four sums in scaled form
  have hL := Cvs.Prolate.Gram.ResidueRatioLogSums.log_resid_sub_log_Rj j S (c ^ 2 * s) hres hR
  have hQs : ∀ p ∈ Zj, p ≠ s := by
    intro p hp hps
    rw [Cvs.Prolate.Gram.ResidueRatioLogSums.resid_eq] at hres
    have h1 := left_ne_zero_of_mul hres
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.prod_ne_zero_iff.mp h1 b hb (by rw [chi_eq, hps, sub_self])
  have hZT : ∀ p ∈ Zj, p ≠ T := fun p hp hpT => by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_erase.mp hb).1 (levT_injective hx hpT)
  have e1 : ∑ b ∈ univ.erase j, log |c ^ 2 * s - Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b| =
      ((x - 1 : ℕ) : ℝ) * log (c ^ 2) + ∑ p ∈ Zj, log |s - p| := by
    rw [sum_rungs hx, sum_log_scale' hc0.ne' _ _ hQs, card_rungSetErase hx]
  have e3 : ∑ b ∈ univ.erase j, log |Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j - Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b| =
      ((x - 1 : ℕ) : ℝ) * log (c ^ 2) + ∑ p ∈ Zj, log |T - p| := by
    rw [sum_rungs hx, chi_eq, sum_log_scale' hc0.ne' _ _ hZT, card_rungSetErase hx]
  have e2 : ∑ σ' ∈ S.erase (c ^ 2 * s), log |c ^ 2 * s - σ'| =
      ((S'.card - 1 : ℕ) : ℝ) * log (c ^ 2) + ∑ p ∈ S'.erase s, log |s - p| := by
    rw [hS, ← Finset.image_erase hinj, Finset.sum_image fun p _ q _ h => hinj h,
      sum_log_scale' hc0.ne' _ _ fun p hp => Finset.ne_of_mem_erase hp, Finset.card_erase_of_mem hs]
  have e4 : ∑ σ' ∈ S, log |Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j - σ'| = (S'.card : ℝ) * log (c ^ 2) + ∑ p ∈ S', log |T - p| := by
    rw [hS, Finset.sum_image fun p _ q _ h => hinj h, chi_eq,
      sum_log_scale' hc0.ne' _ _ fun p hp hpT => hTS (by rw [hT, ← hpT]; exact hp)]
  have hcard : ((S'.card - 1 : ℕ) : ℝ) = S'.card - 1 := by
    rw [Nat.cast_sub (Finset.card_pos.mpr ⟨s, hs⟩), Nat.cast_one]
  rw [e1, e2, e3, e4, hcard] at hL
  -- the local inputs
  have hLzeta := (Cvs.Prolate.Gram.SelectionTargetMeasure.localInputs_zeta ha U).mono_right (show 1 + U ^ 2 ≤ B by linarith)
  have hLz : Cvs.Prolate.Gram.SelectionTargetMeasure.LocalInputs zMeas B := hLzeta.mono hB1 (Measure.le_add_right le_rfl)
  have hLν : Cvs.Prolate.Gram.SelectionTargetMeasure.LocalInputs ν B := hLzeta.mono hB1 hνle
  have hZB : ∀ p ∈ rungSet x, p ∈ Icc 0 B := fun p hp => by
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨levT_nonneg hx b, (levT_lt_one hx b).le.trans hB1⟩
  have hZjB : ∀ p ∈ Zj, p ∈ Icc 0 B := fun p hp => hZB p (by
    rw [hZj, rungSetErase_eq hx] at hp; exact Finset.mem_of_mem_erase hp)
  have hSB : ∀ p ∈ S', p ∈ Icc 0 B := fun p hp => by
    obtain ⟨-, h1, h2⟩ := hS' p hp; exact ⟨(sq_nonneg a).trans h1.le, h2⟩
  have hsB : s ∈ Icc 0 B := hSB s hs
  have hTB : T ∈ Icc 0 B := ⟨hT0, by linarith⟩
  have hERZ : ∀ u, |(cnt Zj u : ℝ) - c * zMeas.real (Iic u)| ≤ ER + 1 := fun u => by
    rw [hZj, rungSetErase_eq hx]
    obtain ⟨h1, h2⟩ := cnt_erase (rungSet x) T u
    have := hER u
    rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]
  have hESν : ∀ u, |(cnt S' u : ℝ) - c * ν.real (Iic u)| ≤ ES := fun u => by rw [hνIic]; exact hES u
  -- the four applications of Cvs.Upstream.DiscreteContinuousLogPotential
  have hA := Cvs.Prolate.Gram.ResidueRatioLogSums.sum_log_upper hB1 hLz Zj hZjB hc0.le hERZ hr hr1 hsB
  rw [Finset.erase_eq_of_notMem fun h => hQs s h rfl] at hA
  have hγZ : ∀ p ∈ rungSet x, p ≠ T → γ ≤ |T - p| := fun p hp hpT => by
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hp
    have hbj : b ≠ j := fun h => hpT (by rw [h])
    refine hγc.trans (le_trans ?_ (levT_sep hx hbj))
    rw [div_le_div_iff_of_pos_left Real.pi_pos (by positivity) (by positivity)]
    have h24 : (24 : ℝ) ≤ 8 * (3 + B) := by linarith
    exact mul_le_mul_of_nonneg_right h24 (pow_pos hc0 3).le
  have hBl := Cvs.Prolate.Gram.ResidueRatioLogSums.sum_log_lower hB1 hLz (rungSet x) hZB hc0.le hER hr hr1 hγ hγr hTB hγZ
  rw [← rungSetErase_eq hx] at hBl
  have hC := Cvs.Prolate.Gram.ResidueRatioLogSums.sum_log_upper hB1 hLν S' hSB hc0.le hESν hr hr1 hTB
  rw [Finset.erase_eq_of_notMem hTS] at hC
  have hγS : ∀ p ∈ S', p ≠ s → γ ≤ |s - p| := fun p hp hps =>
    hγc.trans (node_sep hc1 h0 (hat.trans_lt hte) (by positivity) hsS.1 (hS' p hp).1 hsS.2.2 (hS' p hp).2.2 hps)
  have hD := Cvs.Prolate.Gram.ResidueRatioLogSums.sum_log_lower hB1 hLν S' hSB hc0.le hESν hr hr1 hγ hγr hsB hγS
  -- the potentials
  have hsupM : muM a U (Icc 0 B)ᶜ = 0 := by
    refine Cvs.Upstream.SliceMeasurePushforward.sliceMeas_compl Cvs.Prolate.Gram.SelectionTargetMeasure.measurable_phiZ measurable_const fun t ht => ?_
    have h1 : t ≤ 1 := ht.2.trans (hat.trans hte.le)
    have h2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 h1
    show t ^ 2 + U ^ 2 ≤ B
    rw [hB]; linarith
  have : IsFiniteMeasure (Cvs.Upstream.SliceMeasurePushforward.sliceMeas phiZ (fun _ => U) 0 a) := (inferInstance : IsFiniteMeasure (muM a U))
  have hiM : ∀ y, Integrable (fun v => log |y - v|) (muM a U) := fun y =>
    Cvs.Upstream.SliceMeasurePushforward.integrable_log_sliceMeas Cvs.Prolate.Gram.SelectionTargetMeasure.measurable_phiZ measurable_const (fun t _ => Cvs.Prolate.Gram.SelectionTargetMeasure.phiZ_nonneg t)
      (Cvs.Prolate.Gram.SelectionTargetMeasure.integrableOn_phiZ_of_subset le_rfl (hat.trans hte.le)) hsupM y
  have hpot : ∀ y, (∫ v, log |y - v| ∂ν) - ∫ v, log |y - v| ∂zMeas =
      (∫ v, log |y - v| ∂(muP a U)) - ∫ v, log |y - v| ∂(muM a U) := fun y => by
    have hiz := (hLzeta.intLog y).mono_measure (Measure.le_add_right le_rfl : zMeas ≤ zMeas + muP a U)
    have hip := (hLzeta.intLog y).mono_measure (Measure.le_add_left le_rfl : muP a U ≤ zMeas + muP a U)
    have h := congrArg (fun μ => ∫ v, log |y - v| ∂μ) hadd
    rw [integral_add_measure (hLν.intLog y) (hiM y), integral_add_measure hiz hip] at h
    linarith
  have hPT := Cvs.Prolate.Gram.TruncatedPotentialBound.abs_pot_sub_psiA_le ha hU hT0 (by linarith)
  have hPs := Cvs.Prolate.Gram.TruncatedPotentialBound.abs_pot_sub_psiA_le ha hU hs0 (show s ≤ 2 * U ^ 2 by linarith [hsB.2])
  rw [← hpot] at hPT hPs
  have hψs : 0 ≤ Cvs.Prolate.Gram.EquilibriumPotential.psiA a s := Cvs.Prolate.Gram.EquilibriumPotential.psiA_nonneg h0 h2 hsS.2.1.le
  rw [abs_le] at hPT hPs
  have hPT' := mul_le_mul_of_nonneg_left (show (∫ v, log |T - v| ∂ν) - ∫ v, log |T - v| ∂zMeas ≤
    Cvs.Prolate.Gram.EquilibriumPotential.psiA a T + Cvs.Prolate.Gram.TruncatedPotentialBound.etaU U / 2 by linarith [hPT.2]) hc0.le
  have hPs' := mul_le_mul_of_nonneg_left (show Cvs.Prolate.Gram.EquilibriumPotential.psiA a s - Cvs.Prolate.Gram.TruncatedPotentialBound.etaU U / 2 ≤
    (∫ v, log |s - v| ∂ν) - ∫ v, log |s - v| ∂zMeas by linarith [hPs.1]) hc0.le
  have hψs' := mul_nonneg hc0.le hψs
  simp only [errU, errL]
  linarith

/-- **The discrete potential on every rung**: from `RungCount` and `DirCount`, for every `δ > 0`, eventually every
`j < x` and `a ∈ [½, 3/5]` have between `x` and `x²` Dirichlet nodes with `R_j ≠ 0` and `r_σ² ≤ R_j²e^{2cΨ_a + δc}`. -/
theorem potFloor_all_of_counts (hR : Cvs.Prolate.Gram.WeylCountsDiscretePotential.RungCount) (hD : Cvs.Prolate.Gram.WeylCountsDiscretePotential.DirCount) :
    ∀ δ > 0, ∀ᶠ x : ℕ in atTop, ∀ j : Fin x, ∀ a ∈ Icc (1 / 2 : ℝ) (3 / 5),
      ∃ S : Finset ℝ, (∀ σ ∈ S, regSol (sqC (2 * π * x)) σ a = 0) ∧ x ≤ S.card ∧ (S.card : ℝ) ≤ (x : ℝ) ^ 2 ∧
        Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S ≠ 0 ∧ ∀ σ ∈ S, Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) σ ^ 2 ≤
          Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S ^ 2 * Real.exp (2 * (2 * π * x) * Cvs.Prolate.Gram.EquilibriumPotential.psiA a (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) + δ * (2 * π * x)) := by
  intro δ hδ
  -- the truncation `U`
  obtain ⟨U, hη, hU4⟩ := ((Cvs.Prolate.Gram.TruncatedPotentialBound.tendsto_etaU.eventually (ge_mem_nhds (show (0 : ℝ) < δ / 8 by positivity))).and
    (eventually_ge_atTop (4 : ℝ))).exists
  have hB1 : 1 ≤ U ^ 2 + 2 := by nlinarith
  set κ := 1 / (5 * π * √(U ^ 2 + 2)) with hκ
  have hκ0 : 0 < κ := by positivity
  set ε := min (δ / 324) (κ / 8) with hεdef
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεδ : ε ≤ δ / 324 := min_le_left _ _
  have hεκ : ε ≤ κ / 8 := min_le_right _ _
  have ev1 : ∀ᶠ x : ℕ in atTop, 1 ≤ log (2 * π * x) :=
    tendsto_scale.eventually (tendsto_log_atTop.eventually_ge_atTop 1)
  have ev2 : ∀ᶠ x : ℕ in atTop, log (U ^ 2 + 2) ≤ log (2 * π * x) :=
    tendsto_scale.eventually ((eventually_ge_atTop (U ^ 2 + 2)).mono fun c hc => Real.log_le_log (by linarith) hc)
  have ev3 : ∀ᶠ x : ℕ in atTop, log (8 * (3 + (U ^ 2 + 2))) - log π ≤ log (2 * π * x) :=
    tendsto_scale.eventually (tendsto_log_atTop.eventually_ge_atTop _)
  have ev4 : ∀ᶠ x : ℕ in atTop, 4 * √(2 * π * x) + 12 * √(2 * π * x) * log (2 * π * x) +
      164 * log (2 * π * x) ≤ ε * (2 * π * x) := tendsto_scale.eventually (eventually_rem_le hε0)
  have ev5 : ∀ᶠ x : ℕ in atTop, 12 / κ ≤ 2 * π * x := tendsto_scale.eventually (eventually_ge_atTop _)
  filter_upwards [hR ε hε0, hD ε hε0 (U ^ 2 + 2), Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, ev1, ev2, ev3, ev4, ev5,
    eventually_ge_atTop 2] with x hRx hDx hx hL1 hLB hLγ hrem h6 hx2
  intro j a ha
  have hj : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ 1 := (levT_lt_one hx j).le
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  obtain ⟨h0, hat, hte, h2⟩ := Cvs.Prolate.Gram.SelectionTargetMeasure.tE_facts ha
  have ha1 : a ≤ 1 := hat.trans hte.le
  set L := log c with hLdef
  set T := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j with hT
  -- the rung discrepancy
  have hER := rung_disc hx (E := ε * c / L) (by positivity) hRx
  -- the Dirichlet nodes
  obtain ⟨hfinB, -⟩ := hDx a ha (U ^ 2 + 2) ⟨by positivity, le_rfl⟩
  obtain ⟨D, hDn, hDc⟩ := exists_nodeSet (c := c) hc0.ne' h0 ha1 hfinB
  have hE : ∀ v ∈ Icc (0 : ℝ) (U ^ 2 + 2), |(cnt D v : ℝ) - c * Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a v| ≤ ε * c / L :=
    fun v hv => by rw [hDc v hv.2]; exact (hDx a ha v hv).2
  have hbig : 4 * (ε * c / L + 1) + 2 ≤ c * (Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a (U ^ 2 + 2) - Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a (1 + U ^ 2)) := by
    have hw := dirWeyl_sub_ge (V := 1 + U ^ 2) h0 ha1 (by nlinarith)
    rw [show 1 + U ^ 2 + 1 = U ^ 2 + 2 by ring] at hw
    have hk : κ ≤ (1 - a) / (2 * π * √(U ^ 2 + 2)) := by
      rw [hκ, div_le_div_iff₀ (by positivity) (by positivity)]
      have hs : 0 < π * √(U ^ 2 + 2) := by positivity
      have : 0 ≤ π * √(U ^ 2 + 2) * (5 * (1 - a) - 2) := mul_nonneg hs.le (by linarith [ha.2])
      linarith
    have h1 : ε * c / L ≤ ε * c := div_le_self (by positivity) hL1
    have h2' : 6 ≤ κ / 2 * c := by
      rw [div_le_iff₀ hκ0] at h6; nlinarith
    have h3 : κ * c ≤ c * (Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a (U ^ 2 + 2) - Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a (1 + U ^ 2)) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hk.trans hw) hc0.le
    nlinarith
  obtain ⟨S', hS'D, hTS, hdisc, hcard1, hcard2⟩ :=
    exists_selection ha (by linarith) D (fun s hs => ⟨(hDn s hs).2.1, (hDn s hs).2.2⟩) hE T hbig
  obtain ⟨ν, hνfin, hadd, hνIic, hνle⟩ := Cvs.Prolate.Gram.SelectionTargetMeasure.exists_nu ha (by linarith : (1 : ℝ) ≤ U)
  have hinj : Function.Injective (c ^ 2 * · : ℝ → ℝ) := mul_right_injective₀ (by positivity)
  set S := S'.image (c ^ 2 * ·) with hS
  -- `R_j ≠ 0`
  have hRne : Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S ≠ 0 := by
    unfold Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj
    refine div_ne_zero ?_ ?_
    · rw [Cvs.Prolate.Gram.ResidueRatioLogSums.eval_Qj]
      refine Finset.prod_ne_zero_iff.mpr fun b hb => sub_ne_zero.mpr fun h => ?_
      exact (Finset.mem_erase.mp hb).1 ((Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lev_strictMono hx).injective h).symm
    · refine Finset.prod_ne_zero_iff.mpr fun σ hσ => sub_ne_zero.mpr fun h => ?_
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hσ
      rw [chi_eq] at h
      exact hTS (by rw [hT, hinj h]; exact hs)
  refine ⟨S, fun σ hσ => ?_, ?_, ?_, hRne, fun σ hσ => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hσ
    exact (hDn s (hS'D hs)).1
  · rw [Finset.card_image_of_injective _ hinj]; exact hcard1
  · rw [Finset.card_image_of_injective _ hinj]
    have : (S'.card : ℝ) ≤ x + 1 := by exact_mod_cast hcard2
    have hx2' : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    nlinarith
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hσ
    by_cases hres : Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) (c ^ 2 * s) = 0
    · rw [hres, zero_pow two_ne_zero]; positivity
    have hS'n : ∀ s ∈ S', regSol (sqC c) (c ^ 2 * s) a = 0 ∧ a ^ 2 < s ∧ s ≤ U ^ 2 + 2 := fun s hs => hDn s (hS'D hs)
    have hγ0 : 0 < π / (8 * (3 + (U ^ 2 + 2)) * c ^ 3) := by positivity
    have hγr : π / (8 * (3 + (U ^ 2 + 2)) * c ^ 3) ≤ 1 / c := by
      rw [div_le_div_iff₀ (by positivity) hc0, one_mul]
      have hc3 : c ≤ c ^ 3 := by simpa using pow_le_pow_right₀ hc1 (show 1 ≤ 3 by norm_num)
      have hp : π ≤ 8 * (3 + (U ^ 2 + 2)) := by linarith [Real.pi_lt_four, sq_nonneg U]
      calc π * c ≤ 8 * (3 + (U ^ 2 + 2)) * c := mul_le_mul_of_nonneg_right hp hc0.le
        _ ≤ 8 * (3 + (U ^ 2 + 2)) * c ^ 3 := mul_le_mul_of_nonneg_left hc3 (by positivity)
    have key := log_ratio_le_all hx j hj ha hU4 hadd hνle hνIic hS'n hTS hER hdisc (r := 1 / c) (by positivity)
      (by rw [div_le_one hc0]; exact hc1) hγ0 hγr le_rfl hs hres hRne
    rw [← hc, ← hS, ← hT] at key
    have herr := err_le hc1 hB1 hε0.le hL1 hLB hLγ
    rw [← hLdef] at herr
    have hcη : c * Cvs.Prolate.Gram.TruncatedPotentialBound.etaU U ≤ c * (δ / 8) := mul_le_mul_of_nonneg_left hη hc0.le
    have hlog : log |Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) (c ^ 2 * s)| ≤
        log |Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S| + (c * Cvs.Prolate.Gram.EquilibriumPotential.psiA a T + δ * c / 2) := by
      have h81 : 81 * ε * c ≤ δ * c / 4 := by
        have := mul_le_mul_of_nonneg_right hεδ hc0.le; linarith
      have hδc := mul_pos hδ hc0
      linarith
    have hr0 : 0 < |Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) (c ^ 2 * s)| := abs_pos.mpr hres
    have hR0 : 0 < |Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S| := abs_pos.mpr hRne
    have habs : |Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) (c ^ 2 * s)| ≤
        |Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S| * Real.exp (c * Cvs.Prolate.Gram.EquilibriumPotential.psiA a T + δ * c / 2) := by
      rw [← Real.exp_log hr0, ← Real.exp_log hR0, ← Real.exp_add]
      exact Real.exp_le_exp.mpr hlog
    rw [← sq_abs, ← sq_abs (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S)]
    calc |Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) (c ^ 2 * s)| ^ 2
        ≤ (|Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S| * Real.exp (c * Cvs.Prolate.Gram.EquilibriumPotential.psiA a T + δ * c / 2)) ^ 2 :=
          pow_le_pow_left₀ hr0.le habs 2
      _ = |Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S| ^ 2 * Real.exp (2 * c * Cvs.Prolate.Gram.EquilibriumPotential.psiA a T + δ * c) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring

/-- **The discrete potential on every rung**, unconditionally (`RungWeylCount`'s rung count, `DirichletNodeCountPotFloor`'s node count). -/
theorem potFloor_all : ∀ δ > 0, ∀ᶠ x : ℕ in atTop, ∀ j : Fin x, ∀ a ∈ Icc (1 / 2 : ℝ) (3 / 5),
      ∃ S : Finset ℝ, (∀ σ ∈ S, regSol (sqC (2 * π * x)) σ a = 0) ∧ x ≤ S.card ∧ (S.card : ℝ) ≤ (x : ℝ) ^ 2 ∧
        Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S ≠ 0 ∧ ∀ σ ∈ S, Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) σ ^ 2 ≤
          Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S ^ 2 * Real.exp (2 * (2 * π * x) * Cvs.Prolate.Gram.EquilibriumPotential.psiA a (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) + δ * (2 * π * x)) :=
  potFloor_all_of_counts Cvs.Prolate.RungWeylCount.rungCount Cvs.Prolate.Gram.DirichletNodeCountPotFloor.dirCount

end Cvs.Prolate.Gram.DiscretePotentialAllRungs

end
