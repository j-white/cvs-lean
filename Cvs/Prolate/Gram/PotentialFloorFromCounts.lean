import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.DeepCellFloorAmplitude
import Cvs.Prolate.Gram.EquilibriumPotential
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.ResidueRatioLogSums
import Cvs.Prolate.Gram.RobinDualCertificate
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.SelectionTargetMeasure
import Cvs.Prolate.Gram.TruncatedPotentialBound
import Cvs.Prolate.Gram.WeylCountsDiscretePotential
import Cvs.Prolate.NodeLevelSeparation
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RegularSolutionEnergyComparability
import Cvs.Prolate.SlepianEvenOrdering
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
# The discrete potential from the two Weyl counts: `RungCount ∧ DirCount → PotFloor`

Select Dirichlet nodes greedily against `c ν′ = c(z + μ_a^{(U)})`; Cvs.Upstream.DiscreteContinuousLogPotential applied four times compares the four log sums
of the residue ratio with the potentials of `z` and `ν′`, whose difference is `Ψ_a` up to `η(U)/2` (Cvs.Prolate.Gram.TruncatedPotentialBound).
-/

noncomputable section

open Real Set Filter Topology MeasureTheory Polynomial Finset
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)
open Cvs.Upstream.GreedySelectionTarget (cnt)
open Cvs.Upstream.GreedySelectionTarget renaming cnt_eq_card → cnt_eq_card'
open Cvs.Prolate.Gram.SelectionTargetMeasure (zMeas muP muM Fcdf zcdf phiZ)

namespace Cvs.Prolate.Gram.PotentialFloorFromCounts
open Cvs.ZeroCounting

/-! ### The rung levels -/

section Rungs

variable {x : ℕ}

/-- The rung levels `T_b = χ_b/c²` as a finite set. -/
def rungSet (x : ℕ) : Finset ℝ := univ.image (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x)

theorem chi_eq (x : ℕ) (b : Fin x) : Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b = (2 * π * x) ^ 2 * Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x b := by
  unfold Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT
  have hx0 : (x : ℝ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; exact b.elim0
    · exact_mod_cast h.ne'
  field_simp

theorem chi_mem (hx : 80 ≤ 2 * π * x) (b : Fin x) :
    Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (2 * (b : ℕ)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) :=
  Cvs.Prolate.EvenRungsByIndex.lev_spec (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx b)

theorem chi_nonneg (hx : 80 ≤ 2 * π * x) (b : Fin x) : 0 ≤ Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b :=
  Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec _ (chi_mem hx b).1

theorem chi_lt (hx : 80 ≤ 2 * π * x) (b : Fin x) : Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b < (2 * π * x) ^ 2 := by
  have h := Cvs.Prolate.EvenLevelIndexLemma.index_lemma hx (χ := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) (by rw [(chi_mem hx b).2]; have := b.2; omega)
  have h0 := (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow_pos_le hx).1
  linarith

theorem levT_nonneg (hx : 80 ≤ 2 * π * x) (b : Fin x) : 0 ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x b :=
  div_nonneg (chi_nonneg hx b) (by positivity)

theorem levT_lt_one (hx : 80 ≤ 2 * π * x) (b : Fin x) : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x b < 1 := by
  unfold Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT
  rw [div_lt_one (by positivity)]
  exact chi_lt hx b

theorem levT_injective (hx : 80 ≤ 2 * π * x) : Function.Injective (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x) :=
  (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT_strictMono hx).injective

theorem card_rungSet (hx : 80 ≤ 2 * π * x) : (rungSet x).card = x := by
  rw [rungSet, card_image_of_injective _ (levT_injective hx), card_univ, Fintype.card_fin]

theorem cnt_rungSet (hx : 80 ≤ 2 * π * x) (u : ℝ) :
    cnt (rungSet x) u = (univ.filter fun j : Fin x => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ u).card := by
  unfold cnt rungSet
  rw [filter_image, card_image_of_injective _ (levT_injective hx)]

/-- **The rungs are separated**: `|T_j − T_b| ≥ π/(24c³)` for `b ≠ j`. -/
theorem levT_sep (hx : 80 ≤ 2 * π * x) {j b : Fin x} (hb : b ≠ j) :
    π / (24 * (2 * π * x) ^ 3) ≤ |Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x b| := by
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by linarith
  have key : ∀ i k : Fin x, i < k → π / (24 * c ^ 3) ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x k - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x i := by
    intro i k hik
    have hlt : Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x i < Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x k := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lev_strictMono hx hik
    have h := Cvs.Prolate.NodeLevelSeparation.even_sep hc0 (chi_nonneg hx i) hlt (chi_mem hx i).1 (chi_mem hx k).1
    have hk := chi_lt hx k
    have h3 : 1 + (1 + Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x k) / c ^ 2 ≤ 3 := by
      rw [← sub_nonneg]
      have : (1 + Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x k) / c ^ 2 ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have hd : π / (24 * c) ≤ Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x k - Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x i := by
      rw [div_le_iff₀ (by positivity)]
      have hd0 : 0 ≤ Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x k - Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x i := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * c) hd0)]
    rw [chi_eq, chi_eq] at hd
    rw [← mul_sub] at hd
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hd
    nlinarith
  rcases lt_or_gt_of_ne hb with h | h
  · rw [abs_of_nonneg (by linarith [key b j h, show 0 < π / (24 * c ^ 3) by positivity])]; exact key b j h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [key j b h, show 0 < π / (24 * c ^ 3) by positivity])]
    exact key j b h

end Rungs

/-! ### The rung measure against the rung count -/

theorem zcdf_of_nonpos {u : ℝ} (hu : u ≤ 0) : zcdf u = 0 := by
  unfold zcdf
  have h : ∀ t : ℝ, √(u - t ^ 2) = 0 := fun t => Real.sqrt_eq_zero_of_nonpos (by nlinarith [sq_nonneg t])
  simp [h]

theorem zcdf_of_one_le {u : ℝ} (hu : 1 ≤ u) : zcdf u = 1 / (2 * π) := by
  unfold zcdf
  rw [intervalIntegral.integral_congr_ae (g := fun _ => 1 / (2 * π)) ?_]
  · simp
  · have hne : ∀ᵐ t ∂volume, t ≠ (1 : ℝ) := by rw [ae_iff]; simp
    filter_upwards [hne] with t h1 ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hm : min √(1 - t ^ 2) √(u - t ^ 2) = √(1 - t ^ 2) := min_eq_left (Real.sqrt_le_sqrt (by linarith))
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 h1
    rw [hm, phiZ, mul_assoc, one_div_mul_cancel (Real.sqrt_pos.mpr (by nlinarith [ht.1])).ne', mul_one]

/-- `2π z(−∞, u] = W(u)` for `u ≤ 1`. -/
theorem zcdf_eq {u : ℝ} (hu : u ≤ 1) : 2 * π * zcdf u = Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u := by
  unfold zcdf Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl
  rw [← intervalIntegral.integral_const_mul, min_eq_left hu]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hm : min √(1 - t ^ 2) √(u - t ^ 2) = √(u - t ^ 2) := min_eq_right (Real.sqrt_le_sqrt (by linarith))
  rw [hm, Real.sqrt_div' _ (by nlinarith [ht.1, ht.2] : (0 : ℝ) ≤ 1 - t ^ 2), phiZ]
  field_simp

/-- **The rung discrepancy**: the rung count bound on `[0, 1]` holds on all of `ℝ` against `c z`. -/
theorem rung_disc {x : ℕ} (hx : 80 ≤ 2 * π * x) {E : ℝ} (hE0 : 0 ≤ E)
    (hR : ∀ u ∈ Icc (0 : ℝ) 1,
      |((univ.filter fun j : Fin x => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ u).card : ℝ) - x * Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u| ≤ E) (u : ℝ) :
    |(cnt (rungSet x) u : ℝ) - 2 * π * x * zMeas.real (Iic u)| ≤ E := by
  rw [Cvs.Prolate.Gram.SelectionTargetMeasure.zMeas_real_Iic]
  rcases lt_or_ge u 0 with h0 | h0
  · have hc : cnt (rungSet x) u = 0 := by
      rw [cnt_rungSet hx, card_eq_zero, filter_eq_empty_iff]
      exact fun b _ => not_le.mpr (h0.trans_le (levT_nonneg hx b))
    rw [hc, zcdf_of_nonpos h0.le]; simpa using hE0
  rcases le_or_gt u 1 with h1 | h1
  · have := hR u ⟨h0, h1⟩
    rw [← cnt_rungSet hx] at this
    have e : 2 * π * (x : ℝ) * zcdf u = x * Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u := by rw [← zcdf_eq h1]; ring
    rwa [e]
  · have hc : cnt (rungSet x) u = x := by
      rw [cnt_eq_card' (fun p hp => ?_), card_rungSet hx]
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hp
      exact (levT_lt_one hx b).le.trans h1.le
    rw [hc, zcdf_of_one_le h1.le, show 2 * π * (x : ℝ) * (1 / (2 * π)) = x by field_simp, sub_self, abs_zero]
    exact hE0

/-! ### The Dirichlet nodes as a finite set -/

theorem dirWeyl_of_le {a v : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hv : v ≤ a ^ 2) : Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a v = 0 := by
  unfold Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
  · simp
  · refine Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le ha1] at ht
    exact Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by nlinarith [ht.1])
      (by nlinarith [ht.1, ht.2]))

/-- **The scaled node set**: the Dirichlet nodes `σ ≤ c²B` at `a`, divided by `c²`, count the nodes below every
`c²v`, `v ≤ B`, and lie in `(a², B]`. -/
theorem exists_nodeSet {c a B : ℝ} (hc : c ≠ 0) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hfin : (Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirNodes c a B).Finite) :
    ∃ D : Finset ℝ, (∀ s ∈ D, regSol (sqC c) (c ^ 2 * s) a = 0 ∧ a ^ 2 < s ∧ s ≤ B) ∧
      ∀ v ≤ B, cnt D v = (Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirNodes c a v).ncard := by
  classical
  have hc2 : 0 < c ^ 2 := by positivity
  refine ⟨hfin.toFinset.image (· / c ^ 2), fun s hs => ?_, fun v hv => ?_⟩
  · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hs
    rw [Set.Finite.mem_toFinset] at hσ
    obtain ⟨h0, h1⟩ := hσ
    have h0' : regSol (sqC c) σ a = 0 := h0
    have hlow := Cvs.Prolate.RegularSolutionEnergyComparability.lt_of_regSol_eq_zero (c := c) ha ha1 h0'
    refine ⟨by rw [mul_div_cancel₀ _ hc2.ne']; exact h0', ?_, ?_⟩
    · rw [lt_div_iff₀ hc2]; linarith
    · rw [div_le_iff₀ hc2]; linarith [mem_Iic.mp h1]
  · have hsub : Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirNodes c a v ⊆ Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirNodes c a B := fun σ hσ =>
      ⟨hσ.1, mem_Iic.mpr ((mem_Iic.mp hσ.2).trans (by nlinarith))⟩
    have hset : Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirNodes c a v = ↑(hfin.toFinset.filter (· ≤ c ^ 2 * v)) := by
      ext σ
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, mem_ofPred_eq]
      exact ⟨fun h => ⟨hsub h, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [hset, Set.ncard_coe_finset]
    unfold cnt
    rw [Finset.filter_image, Finset.card_image_of_injective _ (fun p q h => by
      simpa [div_left_inj' hc2.ne'] using h)]
    congr 1
    refine Finset.filter_congr fun σ _ => ?_
    simp only [div_le_iff₀ hc2]
    rw [mul_comm]

/-! ### The selection -/

/-- `Λ_a(B) − Λ_a(V) ≥ (1 − a)/(2π√B)` for `1 ≤ V`, `B = V + 1`, `0 ≤ a ≤ 1`. -/
theorem dirWeyl_sub_ge {a V : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hV : 1 ≤ V) :
    (1 - a) / (2 * π * √(V + 1)) ≤ Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a (V + 1) - Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a V := by
  have hB : 0 < √(V + 1) := Real.sqrt_pos.mpr (by linarith)
  rw [Cvs.Prolate.Gram.SelectionTargetMeasure.dirWeyl_eq a _ ha ha1, Cvs.Prolate.Gram.SelectionTargetMeasure.dirWeyl_eq a _ ha ha1, ← intervalIntegral.integral_sub
    ((Cvs.Prolate.Gram.SelectionTargetMeasure.intervalIntegrable_phiZ_mul ha ha1 le_rfl (by fun_prop)).const_mul 2)
    ((Cvs.Prolate.Gram.SelectionTargetMeasure.intervalIntegrable_phiZ_mul ha ha1 le_rfl (by fun_prop)).const_mul 2)]
  have hlow : ∫ t in a..1, (1 / (2 * π * √(V + 1)) : ℝ) ≤
      ∫ t in a..1, (2 * (phiZ t * √(V + 1 - t ^ 2)) - 2 * (phiZ t * √(V - t ^ 2))) := by
    refine intervalIntegral.integral_mono_ae_restrict ha1 intervalIntegrable_const
      (((Cvs.Prolate.Gram.SelectionTargetMeasure.intervalIntegrable_phiZ_mul ha ha1 le_rfl (by fun_prop)).const_mul 2).sub
      ((Cvs.Prolate.Gram.SelectionTargetMeasure.intervalIntegrable_phiZ_mul ha ha1 le_rfl (by fun_prop)).const_mul 2)) ?_
    have hne : ∀ᵐ t ∂(volume.restrict (Icc a 1)), t ≠ 1 := by
      refine ae_restrict_of_ae ?_; rw [ae_iff]; simp
    filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with t h1 ht
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 h1
    have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1]
    have hφ : 1 / (2 * π) ≤ phiZ t := by
      unfold phiZ
      have : 1 ≤ 1 / √(1 - t ^ 2) := by
        rw [le_div_iff₀ (Real.sqrt_pos.mpr hp), one_mul, Real.sqrt_le_one]; nlinarith
      nlinarith [show 0 < 1 / (2 * π) by positivity]
    set p := √(V + 1 - t ^ 2)
    set q := √(V - t ^ 2)
    have hp2 : p ^ 2 = V + 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
    have hq2 : q ^ 2 = V - t ^ 2 := Real.sq_sqrt (by nlinarith)
    have hp0 : 0 ≤ p := Real.sqrt_nonneg _
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hpB : p ≤ √(V + 1) := Real.sqrt_le_sqrt (by nlinarith)
    have hqB : q ≤ √(V + 1) := Real.sqrt_le_sqrt (by nlinarith)
    have hpq : q ≤ p := Real.sqrt_le_sqrt (by linarith)
    have hd : 1 / (2 * √(V + 1)) ≤ p - q := by
      rw [div_le_iff₀ (by positivity)]
      have e : (p - q) * (p + q) = 1 := by nlinarith
      have : (p - q) * (p + q) ≤ (p - q) * (2 * √(V + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    have hd0 : 0 ≤ p - q := (by positivity : (0 : ℝ) ≤ 1 / (2 * √(V + 1))).trans hd
    calc (1 / (2 * π * √(V + 1)) : ℝ) = 2 * (1 / (2 * π)) * (1 / (2 * √(V + 1))) := by field_simp
      _ ≤ 2 * phiZ t * (p - q) := by
          have := Cvs.Prolate.Gram.SelectionTargetMeasure.phiZ_nonneg t
          gcongr
      _ = _ := by ring
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  calc (1 - a) / (2 * π * √(V + 1)) = (1 - a) * (1 / (2 * π * √(V + 1))) := by ring
    _ ≤ _ := hlow

theorem cnt_erase (D : Finset ℝ) (T v : ℝ) :
    (cnt D v : ℝ) - 1 ≤ cnt (D.erase T) v ∧ (cnt (D.erase T) v : ℝ) ≤ cnt D v := by
  unfold cnt
  rw [Finset.filter_erase]
  have h1 := Finset.pred_card_le_card_erase (s := D.filter (· ≤ v)) (a := T)
  have h2 := Finset.card_erase_le (s := D.filter (· ≤ v)) (a := T)
  constructor
  · have : ((D.filter (· ≤ v)).card : ℝ) - 1 ≤ ((D.filter (· ≤ v)).card - 1 : ℕ) := by
      rcases Nat.eq_zero_or_pos (D.filter (· ≤ v)).card with h | h
      · rw [h]; simp
      · rw [Nat.cast_sub h]; simp
    exact this.trans (by exact_mod_cast h1)
  · exact_mod_cast h2

/-- **The selection**: from scaled nodes `D ⊆ (a², B]`, `B = U² + 2`, counting like `cΛ_a` up to `E`, greedy selection
against `cF` avoiding `T` gives `S ⊆ D ∖ {T}` counting like `cF` up to `2E + 3`, with `x ≤ |S| ≤ x + 1`. -/
theorem exists_selection {x : ℕ} {a U : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) (hU : 1 ≤ U) (D : Finset ℝ)
    (hD : ∀ s ∈ D, a ^ 2 < s ∧ s ≤ U ^ 2 + 2) {E : ℝ}
    (hE : ∀ v ∈ Icc (0 : ℝ) (U ^ 2 + 2), |(cnt D v : ℝ) - 2 * π * x * Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a v| ≤ E) (T : ℝ)
    (hbig : 4 * (E + 1) + 2 ≤ 2 * π * x * (Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a (U ^ 2 + 2) - Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a (1 + U ^ 2))) :
    ∃ S ⊆ D, T ∉ S ∧ (∀ u, |(cnt S u : ℝ) - 2 * π * x * Fcdf a U u| ≤ 2 * (E + 1) + 1) ∧
      x ≤ S.card ∧ S.card ≤ x + 1 := by
  classical
  obtain ⟨h0, hat, hte, -⟩ := Cvs.Prolate.Gram.SelectionTargetMeasure.tE_facts ha
  have ha1 : a ≤ 1 := hat.trans hte.le
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  set B := U ^ 2 + 2 with hB
  set V := 1 + U ^ 2 with hV
  have hBV : B = V + 1 := by rw [hB, hV]; ring
  set Φ : ℝ → ℝ := fun y => c * Fcdf a U y with hΦ
  have hmono : Monotone Φ := fun y₁ y₂ h => mul_le_mul_of_nonneg_left (Cvs.Prolate.Gram.SelectionTargetMeasure.Fcdf_mono ha hU h) hc0
  have hF0 : ∀ y, 0 ≤ Fcdf a U y := fun y => by
    have := Cvs.Prolate.Gram.SelectionTargetMeasure.Fcdf_mono ha hU (min_le_left y 0)
    rwa [Cvs.Prolate.Gram.SelectionTargetMeasure.Fcdf_of_nonpos (by linarith) (min_le_right y 0)] at this
  have hΦ0 : ∀ y, 0 ≤ Φ y := fun y => mul_nonneg hc0 (hF0 y)
  have hΦtop : ∀ y, V ≤ y → Φ y = x := fun y hy => by
    simp only [hΦ]; rw [Cvs.Prolate.Gram.SelectionTargetMeasure.Fcdf_of_ge ha (by linarith) hy, hc]; field_simp
  have hΦinc : ∀ y₁ y₂, y₁ ≤ y₂ → Φ y₂ - Φ y₁ ≤ c * (Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a y₂ - Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a y₁) := fun y₁ y₂ h => by
    simp only [hΦ]; rw [← mul_sub]; exact mul_le_mul_of_nonneg_left (Cvs.Prolate.Gram.SelectionTargetMeasure.Fcdf_sub_le ha hU h) hc0
  have hΦz : Φ 0 = 0 := by simp only [hΦ]; rw [Cvs.Prolate.Gram.SelectionTargetMeasure.Fcdf_of_nonpos (by linarith) le_rfl, mul_zero]
  have hΛz : Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a 0 = 0 := dirWeyl_of_le h0 ha1 (sq_nonneg a)
  have hΦΛ : ∀ v, 0 ≤ v → Φ v ≤ c * Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a v := fun v hv => by
    have := hΦinc 0 v hv
    rw [hΦz, hΛz] at this
    simpa using this
  set P := D.erase T with hP
  have hPD : P ⊆ D := Finset.erase_subset T D
  have hEP : ∀ v ∈ Icc (0 : ℝ) B, |(cnt P v : ℝ) - c * Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a v| ≤ E + 1 := fun v hv => by
    have h1 := hE v hv
    obtain ⟨h2, h3⟩ : ((cnt D v : ℝ) - 1 ≤ cnt P v ∧ (cnt P v : ℝ) ≤ cnt D v) := cnt_erase D T v
    rw [abs_le] at h1 ⊢; constructor <;> linarith [h1.1, h1.2]
  obtain ⟨S, hSP, g1, g2, g3⟩ := Cvs.Upstream.GreedySelectionTarget.exists_greedy P hmono hΦ0
  have hSD : S ⊆ D := hSP.trans hPD
  have hTS : T ∉ S := fun h => Finset.notMem_erase T D (hSP h)
  have hSB : ∀ s ∈ S, 0 ≤ s ∧ s ≤ B := fun s hs => by
    obtain ⟨h1, h2⟩ := hD s (hSD hs); exact ⟨by nlinarith, h2⟩
  have hPB : ∀ s ∈ P, 0 ≤ s ∧ s ≤ B := fun s hs => by
    obtain ⟨h1, h2⟩ := hD s (hPD hs); exact ⟨by nlinarith, h2⟩
  -- the discrepancy on `[0, B]`
  have hmain : ∀ u ∈ Icc (0 : ℝ) B, |(cnt S u : ℝ) - Φ u| ≤ 2 * (E + 1) + 1 := fun u hu => by
    have hup := g1 u
    have hE1 : 0 ≤ E + 1 := (abs_nonneg _).trans (hEP u hu)
    rw [abs_le]
    refine ⟨?_, by linarith⟩
    rcases g2 u with h | ⟨ρ, hρ, hρu, -, hb⟩
    · have := hEP u hu
      rw [h]; rw [abs_le] at this; linarith [hΦΛ u hu.1, this.1]
    · have hρB := hPB ρ hρ
      have i1 := hEP u hu
      have i2 := hEP ρ ⟨hρB.1, hρB.2⟩
      have i3 := hΦinc ρ u hρu
      rw [abs_le] at i1 i2
      linarith [i1.1, i2.2]
  have hcntlow : ∀ u, u < 0 → cnt S u = 0 := fun u hu => by
    unfold cnt; rw [card_eq_zero, filter_eq_empty_iff]; exact fun s hs => not_le.mpr (hu.trans_le (hSB s hs).1)
  have hcnttop : ∀ u, B ≤ u → cnt S u = S.card := fun u hu =>
    Cvs.Upstream.GreedySelectionTarget.cnt_eq_card fun s hs => (hSB s hs).2.trans hu
  have hdisc : ∀ u, |(cnt S u : ℝ) - Φ u| ≤ 2 * (E + 1) + 1 := fun u => by
    rcases lt_or_ge u 0 with h | h
    · rw [hcntlow u h, show Φ u = 0 by simp only [hΦ]; rw [Cvs.Prolate.Gram.SelectionTargetMeasure.Fcdf_of_nonpos (by linarith) h.le, mul_zero]]
      simp; linarith [show (0 : ℝ) ≤ E + 1 from (abs_nonneg _).trans (hEP 0 ⟨le_rfl, by positivity⟩)]
    rcases le_or_gt u B with h' | h'
    · exact hmain u ⟨h, h'⟩
    · have := hmain B ⟨by positivity, le_rfl⟩
      rwa [hcnttop u h'.le, hΦtop u (by linarith), ← hcnttop B le_rfl, ← hΦtop B (by linarith)]
  refine ⟨S, hSD, hTS, hdisc, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hfil : P.filter (fun p => ¬ p ≤ V) ⊆ S.filter (fun p => ¬ p ≤ V) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨?_, hp.2⟩
      by_contra hpS
      have h1 := g3 p hp.1 hpS
      rw [hΦtop p (le_of_lt (not_le.mp hp.2))] at h1
      have h2 : ((S.filter (· < p)).card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_filter_le _ _
      have : (S.card : ℝ) < x := by exact_mod_cast hlt
      linarith
    have hS1 := Finset.card_filter_add_card_filter_not (s := S) (p := fun p => p ≤ V)
    have hP1 := Finset.card_filter_add_card_filter_not (s := P) (p := fun p => p ≤ V)
    have hPc : cnt P B = P.card := Cvs.Upstream.GreedySelectionTarget.cnt_eq_card fun s hs => (hPB s hs).2
    have h1 := Finset.card_le_card hfil
    have hdV := hdisc V
    have hPV := hEP V ⟨by positivity, by linarith⟩
    have hPB' := hEP B ⟨by positivity, le_rfl⟩
    rw [hΦtop V le_rfl] at hdV
    rw [abs_le] at hdV hPV hPB'
    have e1 : (cnt S V : ℝ) + (S.filter (fun p => ¬ p ≤ V)).card = S.card := by exact_mod_cast hS1
    have e2 : (cnt P V : ℝ) + (P.filter (fun p => ¬ p ≤ V)).card = cnt P B := by rw [hPc]; exact_mod_cast hP1
    have h1' : ((P.filter (fun p => ¬ p ≤ V)).card : ℝ) ≤ (S.filter (fun p => ¬ p ≤ V)).card := by
      exact_mod_cast h1
    have : (S.card : ℝ) < x := by exact_mod_cast hlt
    linarith [hPV.2, hPB'.1, hdV.1]
  · have h := g1 B
    rw [hcnttop B le_rfl, hΦtop B (by linarith)] at h
    exact_mod_cast (show (S.card : ℝ) ≤ x + 1 by linarith)

/-! ### The four log sums -/

theorem sum_log_scale' {c : ℝ} (hc : c ≠ 0) (T : Finset ℝ) (q : ℝ) (hq : ∀ p ∈ T, p ≠ q) :
    ∑ p ∈ T, log |c ^ 2 * q - c ^ 2 * p| = T.card * log (c ^ 2) + ∑ p ∈ T, log |q - p| := by
  have := Cvs.Prolate.Gram.ResidueRatioLogSums.sum_log_scale hc T q hq
  simp_rw [abs_sub_comm (c ^ 2 * q), abs_sub_comm q]
  exact this

/-- The rungs other than `j`. -/
def rungSetErase (x : ℕ) (j : Fin x) : Finset ℝ := (univ.erase j).image (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x)

theorem rungSetErase_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) :
    rungSetErase x j = (rungSet x).erase (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) := by
  unfold rungSetErase rungSet
  exact Finset.image_erase (levT_injective hx) _ _

theorem card_rungSetErase {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : (rungSetErase x j).card = x - 1 := by
  unfold rungSetErase
  rw [card_image_of_injective _ (levT_injective hx), card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]

/-- The rung sums in scaled form: `Σ_{b ≠ j} log|q − χ_b| = Σ_{p ∈ Z_j} log|q − c²p|`. -/
theorem sum_rungs {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) (q : ℝ) :
    ∑ b ∈ univ.erase j, log |q - Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b| = ∑ p ∈ rungSetErase x j, log |q - (2 * π * x) ^ 2 * p| := by
  unfold rungSetErase
  rw [Finset.sum_image fun b _ b' _ h => levT_injective hx h]
  exact Finset.sum_congr rfl fun b _ => by rw [chi_eq]

/-- **Dirichlet nodes are separated** in scaled form: `|s − s′| ≥ π/(8(3 + B)c³)` for distinct nodes in `[0, B]`. -/
theorem node_sep {c a B s s' : ℝ} (hc : 1 ≤ c) (ha : 0 ≤ a) (ha1 : a < 1) (hB : 0 ≤ B)
    (hs : regSol (sqC c) (c ^ 2 * s) a = 0) (hs' : regSol (sqC c) (c ^ 2 * s') a = 0) (hsB : s ≤ B)
    (hs'B : s' ≤ B) (hne : s' ≠ s) : π / (8 * (3 + B) * c ^ 3) ≤ |s - s'| := by
  have hc0 : 0 < c := by linarith
  have key : ∀ u v : ℝ, u < v → v ≤ B → regSol (sqC c) (c ^ 2 * u) a = 0 → regSol (sqC c) (c ^ 2 * v) a = 0 →
      π / (8 * (3 + B) * c ^ 3) ≤ v - u := fun u v huv hvB hu hv => by
    have hlt : c ^ 2 * u < c ^ 2 * v := mul_lt_mul_of_pos_left huv (by positivity)
    have h := Cvs.Prolate.NodeLevelSeparation.dirichlet_sep hc0 ha ha1 hlt hu hv
    have h2 : 1 + (1 + c ^ 2 * v) / c ^ 2 ≤ 3 + B := by
      have e : (1 + c ^ 2 * v) / c ^ 2 = 1 / c ^ 2 + v := by field_simp
      have : 1 / c ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
      rw [e]; linarith
    have hd : 0 ≤ c ^ 2 * v - c ^ 2 * u := by linarith
    have h3 : π / 2 ≤ 4 * c * (3 + B) * (c ^ 2 * v - c ^ 2 * u) := h.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hd)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rcases lt_or_gt_of_ne hne with h | h
  · rw [abs_of_nonneg (by linarith [key s' s h hsB hs' hs, show 0 < π / (8 * (3 + B) * c ^ 3) by positivity])]
    exact key s' s h hsB hs' hs
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [key s s' h hs'B hs hs',
      show 0 < π / (8 * (3 + B) * c ^ 3) by positivity])]
    exact key s s' h hs'B hs hs'

/-! ### One residue -/

/-- The error of Cvs.Upstream.DiscreteContinuousLogPotential (U): `2c√r + 3(E + 1)(log B − log r) + (E + 2)|log r|`. -/
def errU (c B r E : ℝ) : ℝ := c * (2 * √r) + 3 * (E + 1) * (log B - log r) + (E + 1 + 1) * |log r|

/-- The error of Cvs.Upstream.DiscreteContinuousLogPotential (L): `3(E + 1)(log B − log r) + (E + 1)|log r| + (2c√r + 2(E + 1))(log r − log γ)`. -/
def errL (c B r γ E : ℝ) : ℝ :=
  3 * (E + 1) * (log B - log r) + (E + 1) * |log r| + (c * (2 * √r) + 2 * (E + 1)) * (log r - log γ)

/-- **The residue ratio**: for a node `σ = c²s` of the selection, `log|r_σ| − log|R_j| ≤ cΨ_a(T_j) + cη(U) + log c² +`
the four Cvs.Upstream.DiscreteContinuousLogPotential errors. -/
theorem log_ratio_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) (hj : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ 3 / 4)
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

/-! ### The error budget -/

/-- `log γ` for `γ = π/(8(3 + B)c³)`. -/
theorem log_gam {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    log (π / (8 * (3 + B) * c ^ 3)) = log π - log (8 * (3 + B)) - 3 * log c := by
  rw [Real.log_div Real.pi_pos.ne' (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast; ring

theorem errU_mono {c B r E E' : ℝ} (hBr : 0 ≤ log B - log r) (hEE : E ≤ E') : errU c B r E ≤ errU c B r E' := by
  unfold errU
  have := abs_nonneg (log r)
  nlinarith

theorem errL_mono {c B r γ E E' : ℝ} (hBr : 0 ≤ log B - log r) (hrγ : 0 ≤ log r - log γ) (hEE : E ≤ E') :
    errL c B r γ E ≤ errL c B r γ E' := by
  unfold errL
  have := abs_nonneg (log r)
  nlinarith

/-- **The error budget**: with `r = 1/c`, `γ = π/(8(3 + B)c³)`, `E = εc/log c`, and `1 ≤ log c`, `log B ≤ log c`,
`log(8(3 + B)/π) ≤ log c`, the total error is at most `80εc + 4√c + 12√c log c + 164 log c`. -/
theorem err_le {c B ε : ℝ} (hc : 1 ≤ c) (hB : 1 ≤ B) (hε : 0 ≤ ε) (hL : 1 ≤ log c) (hLB : log B ≤ log c)
    (hLγ : log (8 * (3 + B)) - log π ≤ log c) :
    log (c ^ 2) + errU c B (1 / c) (ε * c / log c + 1) + errL c B (1 / c) (π / (8 * (3 + B) * c ^ 3)) (ε * c / log c) +
        errU c B (1 / c) (2 * (ε * c / log c + 1) + 1) +
        errL c B (1 / c) (π / (8 * (3 + B) * c ^ 3)) (2 * (ε * c / log c + 1) + 1) ≤
      80 * ε * c + 4 * √c + 12 * √c * log c + 164 * log c := by
  have hc0 : 0 < c := by linarith
  set L := log c with hLdef
  have hL0 : 0 < L := by linarith
  have hlr : log (1 / c) = -L := by rw [one_div, Real.log_inv]
  have hlg := log_gam (by linarith : (0 : ℝ) ≤ B) hc0
  have hlB0 : 0 ≤ log B := Real.log_nonneg hB
  have hsr : c * (2 * √(1 / c)) = 2 * √c := by
    rw [Real.sqrt_div' _ hc0.le, Real.sqrt_one]
    have : 0 < √c := Real.sqrt_pos.mpr hc0
    field_simp
    rw [Real.sq_sqrt hc0.le]
  have hKγ : 0 ≤ log (8 * (3 + B)) - log π := by
    have := Real.log_le_log Real.pi_pos (show π ≤ 8 * (3 + B) by linarith [Real.pi_lt_four]); linarith
  set E := ε * c / L with hE
  have hE0 : 0 ≤ E := by positivity
  have hEL : E * L = ε * c := by rw [hE]; field_simp
  set Es := 2 * (E + 1) + 1 with hEs
  have hBr : 0 ≤ log B - log (1 / c) := by rw [hlr]; linarith
  have hrγ : 0 ≤ log (1 / c) - log (π / (8 * (3 + B) * c ^ 3)) := by rw [hlr, hlg]; linarith
  have u1 := errU_mono (c := c) hBr (show E + 1 ≤ Es by rw [hEs]; linarith)
  have l1 := errL_mono (c := c) (γ := π / (8 * (3 + B) * c ^ 3)) hBr hrγ (show E ≤ Es by rw [hEs]; linarith)
  have hU : errU c B (1 / c) Es ≤ 2 * √c + 14 * ε * c + 29 * L := by
    unfold errU
    rw [hsr, hlr, abs_neg, abs_of_pos hL0, hEs]
    nlinarith
  have hLl : errL c B (1 / c) (π / (8 * (3 + B) * c ^ 3)) Es ≤ 26 * ε * c + 52 * L + 6 * √c * L := by
    unfold errL
    rw [hsr, hlr, abs_neg, abs_of_pos hL0, hlg, hEs]
    have hsc : 0 ≤ √c := Real.sqrt_nonneg c
    have h3 : -L - (log π - log (8 * (3 + B)) - 3 * L) ≤ 3 * L := by linarith
    have h4 : 0 ≤ -L - (log π - log (8 * (3 + B)) - 3 * L) := by linarith
    have h5 : (2 * √c + 2 * (2 * (E + 1) + 1 + 1)) * (-L - (log π - log (8 * (3 + B)) - 3 * L)) ≤
        (2 * √c + 2 * (2 * (E + 1) + 1 + 1)) * (3 * L) := mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  have hlc2 : log (c ^ 2) = 2 * L := by rw [Real.log_pow]; push_cast; ring
  rw [hlc2]
  linarith

/-- **The remainder is `o(c)`**: eventually `4√c + 12√c log c + 164 log c ≤ Kc`, `K > 0`. -/
theorem eventually_rem_le {K : ℝ} (hK : 0 < K) :
    ∀ᶠ c : ℝ in atTop, 4 * √c + 12 * √c * log c + 164 * log c ≤ K * c := by
  have h1 : Tendsto (fun c : ℝ => c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
  have h2 : Tendsto (fun c : ℝ => log c / c ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero
  have h3 : Tendsto (fun c : ℝ => log c / c) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h := ((h1.const_mul 4).add (h2.const_mul 12)).add (h3.const_mul 164)
  simp only [mul_zero, add_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds hK), eventually_gt_atTop 0] with c hc hc0
  have hs : √c = c ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow c
  have hs0 : 0 < √c := Real.sqrt_pos.mpr hc0
  have hss : √c * √c = c := Real.mul_self_sqrt hc0.le
  have hneg : c ^ (-(1 / 2 : ℝ)) = 1 / √c := by rw [Real.rpow_neg hc0.le, ← hs, one_div]
  rw [hneg, ← hs] at hc
  have hcs : c / √c = √c := by rw [div_eq_iff hs0.ne', hss]
  have t1 : c * (4 * (1 / √c)) = 4 * √c := by
    calc c * (4 * (1 / √c)) = 4 * (c / √c) := by ring
      _ = 4 * √c := by rw [hcs]
  have t2 : c * (12 * (log c / √c)) = 12 * √c * log c := by
    calc c * (12 * (log c / √c)) = 12 * (c / √c) * log c := by ring
      _ = 12 * √c * log c := by rw [hcs]
  have t3 : c * (164 * (log c / c)) = 164 * log c := by field_simp
  have := mul_lt_mul_of_pos_left hc hc0
  rw [mul_add, mul_add, t1, t2, t3] at this
  linarith

/-- The scale `c = 2πx` tends to infinity. -/
theorem tendsto_scale : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)

/-! ### The discrete potential -/

/-- **The discrete potential from the two Weyl counts**: `RungCount` and `DirCount` give `PotFloor`. -/
theorem potFloor_of_counts (hR : Cvs.Prolate.Gram.WeylCountsDiscretePotential.RungCount) (hD : Cvs.Prolate.Gram.WeylCountsDiscretePotential.DirCount) : Cvs.Prolate.Gram.DeepCellFloorAmplitude.PotFloor := by
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
  intro j hj a ha
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
    have key := log_ratio_le hx j hj ha hU4 hadd hνle hνIic hS'n hTS hER hdisc (r := 1 / c) (by positivity)
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

end Cvs.Prolate.Gram.PotentialFloorFromCounts

end
