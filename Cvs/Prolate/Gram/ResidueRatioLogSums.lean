import Mathlib
import Cvs.Prolate.Gram.DeepCellFloorAmplitude
import Cvs.Prolate.Gram.RobinDualCertificate
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.SelectionTargetMeasure
import Cvs.Upstream.DiscreteContinuousLogPotential
import Cvs.Upstream.GreedySelectionTarget

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The residue ratio as four log sums, and Cvs.Upstream.DiscreteContinuousLogPotential in counting form

`log|r_σ| − log|R_j| = Σ_{b ≠ j} log|σ − χ_b| − Σ_{S ∖ σ} log|σ − σ′| − Σ_{b ≠ j} log|χ_j − χ_b|
+ Σ_S log|χ_j − σ′|`, and each log sum over a finite `Y ⊆ [0, B]` counting like `cν` up to `E` is bounded by Cvs.Upstream.DiscreteContinuousLogPotential
with the local inputs of Cvs.Prolate.Gram.SelectionTargetMeasure.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory Polynomial Finset
open Cvs.Upstream.GreedySelectionTarget (cnt)

namespace Cvs.Prolate.Gram.ResidueRatioLogSums
open Cvs.ZeroCounting

/-! ### The residue ratio -/

theorem eval_Qj (x : ℕ) (j : Fin x) (z : ℝ) :
    (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j).eval z = ∏ b ∈ univ.erase j, (z - Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) := by
  unfold Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj; rw [eval_prod]; simp

theorem resid_eq (x : ℕ) (j : Fin x) (S : Finset ℝ) (σ : ℝ) :
    Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) σ =
      (∏ b ∈ univ.erase j, (σ - Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b)) * ∏ σ' ∈ S.erase σ, (σ - σ')⁻¹ := by
  unfold Cvs.Prolate.Gram.RobinDualCertificate.resid Lagrange.nodalWeight; rw [eval_Qj]; rfl

theorem log_abs_prod {ι : Type*} (T : Finset ι) (f : ι → ℝ) (h : ∏ i ∈ T, f i ≠ 0) :
    log |∏ i ∈ T, f i| = ∑ i ∈ T, log |f i| := by
  rw [abs_prod, Real.log_prod]
  exact fun i hi => abs_ne_zero.mpr (Finset.prod_ne_zero_iff.mp h i hi)

/-- **The residue ratio in log sums**. -/
theorem log_resid_sub_log_Rj {x : ℕ} (j : Fin x) (S : Finset ℝ) (σ : ℝ)
    (hr : Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) σ ≠ 0) (hR : Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S ≠ 0) :
    log |Cvs.Prolate.Gram.RobinDualCertificate.resid S id (Cvs.Prolate.Gram.DeepCellFloorAmplitude.Qj x j) σ| - log |Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj x j S| =
      (∑ b ∈ univ.erase j, log |σ - Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b|) - (∑ σ' ∈ S.erase σ, log |σ - σ'|) -
        (∑ b ∈ univ.erase j, log |Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j - Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b|) + ∑ σ' ∈ S, log |Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j - σ'| := by
  rw [resid_eq] at hr ⊢
  have h1 := left_ne_zero_of_mul hr
  have h2 := right_ne_zero_of_mul hr
  unfold Cvs.Prolate.Gram.DeepCellFloorAmplitude.Rj at hR ⊢
  rw [eval_Qj] at hR ⊢
  have h3 : ∏ b ∈ univ.erase j, (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j -
      Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) ≠ 0 := by
    intro h; apply hR; rw [h, zero_div]
  have h4 : ∏ σ' ∈ S, (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j - σ') ≠ 0 := by
    intro h; apply hR; rw [h, div_zero]
  rw [abs_mul, Real.log_mul (abs_ne_zero.mpr h1) (abs_ne_zero.mpr h2), abs_div,
    Real.log_div (abs_ne_zero.mpr h3) (abs_ne_zero.mpr h4), log_abs_prod _ _ h1, log_abs_prod _ _ h2,
    log_abs_prod _ _ h3, log_abs_prod _ _ h4]
  have e : ∑ σ' ∈ S.erase σ, log |(σ - σ')⁻¹| = -∑ σ' ∈ S.erase σ, log |σ - σ'| := by
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [abs_inv, Real.log_inv]
  rw [e]; ring

/-- `Σ_T log|c²p − c²q| = |T| log c² + Σ_T log|p − q|` when no `p ∈ T` equals `q`, `c ≠ 0`. -/
theorem sum_log_scale {c : ℝ} (hc : c ≠ 0) (T : Finset ℝ) (q : ℝ) (hq : ∀ p ∈ T, p ≠ q) :
    ∑ p ∈ T, log |c ^ 2 * p - c ^ 2 * q| = T.card * log (c ^ 2) + ∑ p ∈ T, log |p - q| := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity), Real.log_mul (by positivity)
    (abs_ne_zero.mpr (sub_ne_zero.mpr (hq p hp)))]
  simp

/-! ### Cvs.Upstream.DiscreteContinuousLogPotential in counting form -/

/-- `ptMeas` of a closed half-line is the count. -/
theorem ptMeas_real_Iic (Y : Finset ℝ) (u : ℝ) : (Cvs.Upstream.DiscreteContinuousLogPotential.ptMeas Y).real (Iic u) = cnt Y u := by
  classical
  rw [Cvs.Upstream.DiscreteContinuousLogPotential.ptMeas_real Y measurableSet_Iic]; rfl

/-- The open half-line count is within `1` of the closed one. -/
theorem ptMeas_real_Iio (Y : Finset ℝ) (u : ℝ) :
    (cnt Y u : ℝ) - 1 ≤ (Cvs.Upstream.DiscreteContinuousLogPotential.ptMeas Y).real (Iio u) ∧ (Cvs.Upstream.DiscreteContinuousLogPotential.ptMeas Y).real (Iio u) ≤ cnt Y u := by
  classical
  rw [Cvs.Upstream.DiscreteContinuousLogPotential.ptMeas_real Y measurableSet_Iio]
  unfold cnt
  have hsub : Y.filter (· ∈ Iio u) ⊆ Y.filter (· ≤ u) := by
    intro p hp; simp only [Finset.mem_filter, Set.mem_Iio] at hp ⊢; exact ⟨hp.1, hp.2.le⟩
  have hsub2 : Y.filter (· ≤ u) ⊆ insert u (Y.filter (· ∈ Iio u)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_insert, Set.mem_Iio] at hp ⊢
    rcases eq_or_lt_of_le hp.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hp.1, h⟩
  have h1 := Finset.card_le_card hsub
  have h2 := (Finset.card_le_card hsub2).trans (Finset.card_insert_le _ _)
  constructor
  · have : ((Y.filter (· ≤ u)).card : ℝ) ≤ (Y.filter (· ∈ Iio u)).card + 1 := by exact_mod_cast h2
    linarith
  · exact_mod_cast h1

/-- An atomless finite measure has `ν(−∞, u) = ν(−∞, u]`. -/
theorem measureReal_Iio_eq {ν : Measure ℝ} (hν : ∀ y, ν {y} = 0) (u : ℝ) : ν.real (Iio u) = ν.real (Iic u) := by
  have h1 : ν (Iio u) ≤ ν (Iic u) := measure_mono Iio_subset_Iic_self
  have h2 : ν (Iic u) ≤ ν (Iio u) := by
    rw [← Iio_union_right]; exact (measure_union_le _ _).trans (by rw [hν u, add_zero])
  rw [measureReal_def, measureReal_def, le_antisymm h1 h2]

theorem disc_Iio {ν : Measure ℝ} (hν : ∀ y, ν {y} = 0) (Y : Finset ℝ) {c E : ℝ}
    (hE : ∀ u, |(cnt Y u : ℝ) - c * ν.real (Iic u)| ≤ E) (u : ℝ) :
    |(Cvs.Upstream.DiscreteContinuousLogPotential.ptMeas Y).real (Iio u) - c * ν.real (Iio u)| ≤ E + 1 := by
  rw [measureReal_Iio_eq hν]
  obtain ⟨h1, h2⟩ := ptMeas_real_Iio Y u
  have := hE u
  rw [abs_le] at this ⊢
  constructor <;> linarith [this.1, this.2]

/-- **Lemma 11 (U) in counting form**. -/
theorem sum_log_upper {ν : Measure ℝ} [IsFiniteMeasure ν] {B : ℝ} (hB : 1 ≤ B) (hν : Cvs.Prolate.Gram.SelectionTargetMeasure.LocalInputs ν B)
    (Y : Finset ℝ) (hY : ∀ p ∈ Y, p ∈ Icc 0 B) {c E : ℝ} (hc : 0 ≤ c)
    (hE : ∀ u, |(cnt Y u : ℝ) - c * ν.real (Iic u)| ≤ E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {y : ℝ}
    (hy : y ∈ Icc 0 B) :
    ∑ p ∈ Y.erase y, log |y - p| ≤
      c * ∫ v, log |y - v| ∂ν + c * (2 * √r) + 3 * (E + 1) * (log B - log r) + (E + 1 + 1) * |log r| := by
  refine Cvs.Upstream.DiscreteContinuousLogPotential.sum_log_le ν Y hc hB hr hr1 hy hν.supp hY (fun u => ?_) (disc_Iio hν.atom Y hE)
    (hν.intLog y) (hν.loc y r hr hr1)
  rw [ptMeas_real_Iic]; linarith [hE u]

/-- **Lemma 11 (L) in counting form**. -/
theorem sum_log_lower {ν : Measure ℝ} [IsFiniteMeasure ν] {B : ℝ} (hB : 1 ≤ B) (hν : Cvs.Prolate.Gram.SelectionTargetMeasure.LocalInputs ν B)
    (Y : Finset ℝ) (hY : ∀ p ∈ Y, p ∈ Icc 0 B) {c E : ℝ} (hc : 0 ≤ c)
    (hE : ∀ u, |(cnt Y u : ℝ) - c * ν.real (Iic u)| ≤ E) {r γ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hγ : 0 < γ)
    (hγr : γ ≤ r) {y : ℝ} (hy : y ∈ Icc 0 B) (hsep : ∀ p ∈ Y, p ≠ y → γ ≤ |y - p|) :
    c * ∫ v, log |y - v| ∂ν - 3 * (E + 1) * (log B - log r) - (E + 1) * |log r| -
        (c * (2 * √r) + 2 * (E + 1)) * (log r - log γ) ≤ ∑ p ∈ Y.erase y, log |y - p| :=
  Cvs.Upstream.DiscreteContinuousLogPotential.le_sum_log ν Y hc hB hr hr1 hy hν.supp hY (fun u => by rw [ptMeas_real_Iic]; linarith [hE u])
    (disc_Iio hν.atom Y hE) (hν.intLog y) (hν.ball y r hr.le) (hν.atom y) hγ hγr hsep

end Cvs.Prolate.Gram.ResidueRatioLogSums

end
