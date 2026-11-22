import Mathlib
import Cvs.L2a.PlateauModeWeight
import Cvs.L2a.SpanTailGramFloorBulk

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The summed diagonal of the modes under a plateau weight

For a continuous weight `σ ≤ 1` vanishing outside `(19/20, 3/2)`, the dilated square `∫ σ(θ) G(mθ)² dθ` is
`(1/m)∫ σ(u/m) G(u)² du ≤ (1/m)∫_{19m/20}^{3m/2} G²`, a switched integral over `[19/10, 3M/2]`, and the sum over
`2 ≤ m ≤ M` is at most `(5/6)∫_{19/10}^{3M/2} G²` by the plateau weight (Cvs.L2a.PlateauModeWeight): the diagonal input of the cutoff
route's edge bound.
-/

namespace Cvs.L2a.PlateauSummedDiagonal

open Real Set Finset intervalIntegral Cvs.L2a.PlateauModeWeight

/-- A switched integral over `[a, b] ⊇ [p, q]` is the integral over `[p, q]`. -/
theorem integral_ite_eq {F : ℝ → ℝ} (hF : Continuous F) {a p q b : ℝ} (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b) :
    ∫ u in a..b, (if p < u ∧ u < q then F u else 0) = ∫ u in p..q, F u := by
  have hP : MeasurableSet {u : ℝ | p < u ∧ u < q} :=
    (measurableSet_lt measurable_const measurable_id).inter (measurableSet_lt measurable_id measurable_const)
  have hI : ∀ s t : ℝ, s ≤ t → IntervalIntegrable (fun u => if p < u ∧ u < q then F u else 0)
      MeasureTheory.volume s t := fun s t hst =>
    Cvs.L2a.SpanTailGramFloorBulk.intervalIntegrable_ite (P := fun u => p < u ∧ u < q) hst hP hF.continuousOn
  rw [← integral_add_adjacent_intervals (hI a p hap) (hI p b (hpq.trans hqb)),
    ← integral_add_adjacent_intervals (hI p q hpq) (hI q b hqb)]
  have z1 : ∫ u in a..p, (if p < u ∧ u < q then F u else 0) = ∫ u in a..p, (0 : ℝ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le hap] at hu
    rw [ite_eq_right]; intro h; linarith [h.1, hu.2]
  have z3 : ∫ u in q..b, (if p < u ∧ u < q then F u else 0) = ∫ u in q..b, (0 : ℝ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le hqb] at hu
    rw [ite_eq_right]; intro h; linarith [h.2, hu.1]
  -- on `(p, q]` the switch is on except at the single point `q`
  have z2 : ∫ u in p..q, (if p < u ∧ u < q then F u else 0) = ∫ u in p..q, F u := by
    apply integral_congr_ae
    have h0 : MeasureTheory.volume ({q} : Set ℝ) = 0 := Real.volume_singleton
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h0] with u hu hmem
    rw [uIoc_of_le hpq] at hmem
    rw [ite_eq_left ⟨hmem.1, lt_of_le_of_ne hmem.2 hu⟩]
  rw [z1, z2, z3, integral_zero, integral_zero]; ring

/-- **A dilated square under the weight**: for `σ ≤ 1` vanishing outside `(19/20, 3/2)` and `2 ≤ m`,
`∫_L^R σ(θ) G(mθ)² ≤ (1/m) ∫_{19m/20}^{3m/2} G²` whenever `L ≤ 19/20`, `3/2 ≤ R`. -/
theorem dilate_sq_le {σ G : ℝ → ℝ} (hσc : Continuous σ) (hGc : Continuous G) (hσ1 : ∀ θ, σ θ ≤ 1)
    (hσ0 : ∀ θ, θ ≤ 19 / 20 ∨ 3 / 2 ≤ θ → σ θ = 0) {m : ℕ} (hm : 2 ≤ m) {L R : ℝ} (hL : L ≤ 19 / 20)
    (hR : 3 / 2 ≤ R) :
    ∫ θ in L..R, σ θ * G (m * θ) ^ 2 ≤ 1 / m * ∫ u in (19 * m / 20 : ℝ)..(3 * m / 2), G u ^ 2 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hmpos : (0 : ℝ) < m := by positivity
  have e : (fun θ => σ θ * G (m * θ) ^ 2) = fun θ => (fun u => σ (u / m) * G u ^ 2) (m * θ) := by
    funext θ; simp only; rw [mul_div_cancel_left₀ θ hm0]
  rw [e, integral_comp_mul_left (fun u => σ (u / m) * G u ^ 2) hm0, smul_eq_mul]
  have hLR : (m : ℝ) * L ≤ m * R := mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hap : (m : ℝ) * L ≤ 19 * m / 20 := by nlinarith
  have hpq : 19 * (m : ℝ) / 20 ≤ 3 * m / 2 := by linarith
  have hqb : 3 * (m : ℝ) / 2 ≤ m * R := by nlinarith
  have hpt : ∀ u ∈ Icc ((m : ℝ) * L) (m * R),
      σ (u / m) * G u ^ 2 ≤ (if 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2 then G u ^ 2 else 0) := by
    intro u _
    split_ifs with h
    · exact mul_le_of_le_one_left (sq_nonneg _) (hσ1 _)
    · have : σ (u / m) = 0 := by
        apply hσ0
        rcases not_and_or.mp h with h1 | h1
        · left; rw [div_le_iff₀ hmpos]; linarith [not_lt.mp h1]
        · right; rw [le_div_iff₀ hmpos]; linarith [not_lt.mp h1]
      rw [this, zero_mul]
  have hP : MeasurableSet {u : ℝ | 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2} := measurableSet_Ioo
  have hmono := integral_mono_on (f := fun u => σ (u / m) * G u ^ 2)
    (g := fun u => if 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2 then G u ^ 2 else 0) hLR
    ((by fun_prop : Continuous fun u => σ (u / m) * G u ^ 2).continuousOn.intervalIntegrable_of_Icc hLR)
    (Cvs.L2a.SpanTailGramFloorBulk.intervalIntegrable_ite (P := fun u => 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2) hLR hP
      (by fun_prop : Continuous fun u => G u ^ 2).continuousOn) hpt
  rw [integral_ite_eq (F := fun u => G u ^ 2) (by fun_prop) hap hpq hqb] at hmono
  have : (m : ℝ)⁻¹ = 1 / m := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **The summed diagonal under the plateau weight**: `Σ_{m=2}^{M} ∫_L^R σ(θ) G(mθ)² ≤ (5/6) ∫_{19/10}^{3M/2} G²`. -/
theorem sum_dilate_sq_le {σ G : ℝ → ℝ} (hσc : Continuous σ) (hGc : Continuous G) (hσ1 : ∀ θ, σ θ ≤ 1)
    (hσ0 : ∀ θ, θ ≤ 19 / 20 ∨ 3 / 2 ≤ θ → σ θ = 0) {M : ℕ} (hM : 2 ≤ M) {L R : ℝ} (hL : L ≤ 19 / 20)
    (hR : 3 / 2 ≤ R) :
    ∑ m ∈ Finset.Icc 2 M, ∫ θ in L..R, σ θ * G (m * θ) ^ 2 ≤ 5 / 6 * ∫ u in (19 / 10 : ℝ)..(3 * M / 2), G u ^ 2 := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hab : (19 / 10 : ℝ) ≤ 3 * M / 2 := by linarith
  have hI : ∀ m ∈ Finset.Icc 2 M, IntervalIntegrable
      (fun u => (1 : ℝ) / m * (if 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2 then G u ^ 2 else 0)) MeasureTheory.volume
      (19 / 10) (3 * M / 2) := fun m _ =>
    (Cvs.L2a.SpanTailGramFloorBulk.intervalIntegrable_ite (P := fun u => 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2) hab
      measurableSet_Ioo
      (hGc.pow 2).continuousOn).const_mul _
  have e : ∀ m ∈ Finset.Icc 2 M, ∫ θ in L..R, σ θ * G (m * θ) ^ 2
      ≤ ∫ u in (19 / 10 : ℝ)..(3 * M / 2), (1 : ℝ) / m * (if 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2 then G u ^ 2 else 0) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast hm.2
    rw [integral_const_mul, integral_ite_eq (F := fun u => G u ^ 2) (by fun_prop) (by linarith) (by linarith) (by linarith)]
    exact dilate_sq_le hσc hGc hσ1 hσ0 hm.1 hL hR
  calc ∑ m ∈ Finset.Icc 2 M, ∫ θ in L..R, σ θ * G (m * θ) ^ 2
      ≤ ∑ m ∈ Finset.Icc 2 M, ∫ u in (19 / 10 : ℝ)..(3 * M / 2),
          (1 : ℝ) / m * (if 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2 then G u ^ 2 else 0) := Finset.sum_le_sum e
    _ = ∫ u in (19 / 10 : ℝ)..(3 * M / 2), ∑ m ∈ Finset.Icc 2 M,
          (1 : ℝ) / m * (if 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2 then G u ^ 2 else 0) := (integral_finsetSum hI).symm
    _ ≤ ∫ u in (19 / 10 : ℝ)..(3 * M / 2), 5 / 6 * G u ^ 2 := by
        apply integral_mono_on hab
        · have h := IntervalIntegrable.sum (Finset.Icc 2 M) hI
          simpa only [Finset.sum_fn] using h
        · exact ((hGc.pow 2).continuousOn.intervalIntegrable_of_Icc hab).const_mul _
        · intro u hu
          have hu0 : 0 < u := by linarith [hu.1]
          have e2 : ∑ m ∈ Finset.Icc 2 M, (1 : ℝ) / m * (if 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2 then G u ^ 2 else 0)
              = (∑ m ∈ plateauModes M u, (1 : ℝ) / m) * G u ^ 2 := by
            unfold plateauModes
            rw [Finset.sum_filter, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro m _
            split_ifs <;> simp
          rw [e2]
          exact mul_le_mul_of_nonneg_right (plateau_weight_le M hu0) (sq_nonneg _)
    _ = 5 / 6 * ∫ u in (19 / 10 : ℝ)..(3 * M / 2), G u ^ 2 := integral_const_mul _ _

end Cvs.L2a.PlateauSummedDiagonal
