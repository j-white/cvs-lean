import Mathlib
import Cvs.Prolate.Hardy.CarrierBoundaryValues
import Cvs.Prolate.Hardy.CarrierNegativeFrequencies
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Upstream.PlancherelL1L2SpectralDensity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The lips `½ < |x| ≤ 3/5` cut into symmetric pieces

With `symS a b = (a, b] ∪ (−b, −a]`, `1_{(−3/5, 3/5]}H − 1_I H = 1_{symS ½ (3/5)}H` off `x = −½`, symmetric pieces
add along `a ≤ b ≤ c`, and a piece where `|A| ≤ G₀` has `‖1_{symS a b}H‖² ≤ 2G₀²(b − a)`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.Hardy.LipSymmetricPieces
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C wR)
open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI)
open Cvs.Prolate.Hardy.CarrierNegativeFrequencies (carH kC)

/-- The symmetric piece `(a, b] ∪ (−b, −a]`. -/
def symS (a b : ℝ) : Set ℝ := Ioc a b ∪ Ioc (-b) (-a)

theorem measurableSet_symS (a b : ℝ) : MeasurableSet (symS a b) := measurableSet_Ioc.union measurableSet_Ioc

theorem disjoint_sides {a b : ℝ} (ha : 0 ≤ a) : Disjoint (Ioc a b) (Ioc (-b) (-a)) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  linarith [h1.1, h2.2]

theorem indicator_symS {a b : ℝ} (ha : 0 ≤ a) (f : ℝ → ℂ) :
    (symS a b).indicator f = (Ioc a b).indicator f + (Ioc (-b) (-a)).indicator f :=
  indicator_union_of_disjoint (disjoint_sides ha) f

theorem indicator_symS_split {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (f : ℝ → ℂ) :
    (symS a c).indicator f = (symS a b).indicator f + (symS b c).indicator f := by
  rw [indicator_symS ha, indicator_symS ha, indicator_symS (ha.trans hab)]
  have h1 : (Ioc a c).indicator f = (Ioc a b).indicator f + (Ioc b c).indicator f := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hab hbc, indicator_union_of_disjoint (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
    rfl
  have h2 : (Ioc (-c) (-a)).indicator f = (Ioc (-c) (-b)).indicator f + (Ioc (-b) (-a)).indicator f := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc (by linarith : -c ≤ -b) (by linarith : -b ≤ -a),
      indicator_union_of_disjoint (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
    rfl
  rw [h1, h2]
  abel

/-- `1_{(−3/5, 3/5]}H − 1_I H = 1_{symS ½ (3/5)}H` at every `x ≠ −½`. -/
theorem kC_sub_indicator (c : ℝ) (A : ℂ → ℂ) {x : ℝ} (hx : x ≠ -(1 / 2)) :
    kC c A x - cI.indicator (carH c A) x = (symS (1 / 2) (3 / 5)).indicator (carH c A) x := by
  unfold kC symS
  by_cases hI : x ∈ cI
  · have h1 : x ∈ Ioc (-(3 / 5) : ℝ) (3 / 5) := ⟨by linarith [hI.1], by linarith [hI.2]⟩
    have h2 : x ∉ Ioc (1 / 2 : ℝ) (3 / 5) ∪ Ioc (-(3 / 5)) (-(1 / 2)) := by
      rintro (h | h)
      · linarith [h.1, hI.2]
      · exact hx (le_antisymm h.2 (by linarith [hI.1]))
    rw [indicator_of_mem h1, indicator_of_mem hI, indicator_of_notMem h2, sub_self]
  · rw [indicator_of_notMem hI, sub_zero]
    have hI' : x < -(1 / 2) ∨ 1 / 2 < x := by
      by_contra h; push Not at h; exact hI ⟨by linarith [h.1], h.2⟩
    by_cases hK : x ∈ Ioc (-(3 / 5) : ℝ) (3 / 5)
    · have : x ∈ Ioc (1 / 2 : ℝ) (3 / 5) ∪ Ioc (-(3 / 5)) (-(1 / 2)) := by
        rcases hI' with h | h
        · exact Or.inr ⟨hK.1, h.le⟩
        · exact Or.inl ⟨h, hK.2⟩
      rw [indicator_of_mem hK, indicator_of_mem this]
    · have : x ∉ Ioc (1 / 2 : ℝ) (3 / 5) ∪ Ioc (-(3 / 5)) (-(1 / 2)) := by
        rintro (h | h)
        · exact hK ⟨by linarith [h.1], h.2⟩
        · exact hK ⟨h.1, by linarith [h.2]⟩
      rw [indicator_of_notMem hK, indicator_of_notMem this]

/-- Off `I` the carrier has the modulus of its amplitude: `|H(x)| = |A(x)|`. -/
theorem norm_carH_of_half_le (c : ℝ) (A : ℂ → ℂ) {x : ℝ} (hx : 1 / 2 ≤ |x|) : ‖carH c A x‖ = ‖A x‖ := by
  unfold carH
  rw [norm_mul, norm_mul, norm_inv, Cvs.Prolate.Hardy.CarrierBoundaryValues.norm_wR_of_half_le_abs _ hx, inv_one, mul_one,
    show Complex.I * (c : ℂ) * x = ((c * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem half_le_abs_of_mem_symS {a b x : ℝ} (ha : 1 / 2 ≤ a) (hx : x ∈ symS a b) : 1 / 2 ≤ |x| := by
  rcases hx with h | h
  · rw [abs_of_pos (by linarith [h.1])]; linarith [h.1]
  · rw [abs_of_neg (by linarith [h.2])]; linarith [h.2]

theorem volume_symS {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) : volume.real (symS a b) = 2 * (b - a) := by
  unfold symS
  rw [measureReal_union (disjoint_sides ha) measurableSet_Ioc (h₁ := measure_Ioc_lt_top.ne)
    (h₂ := measure_Ioc_lt_top.ne), Real.volume_real_Ioc, Real.volume_real_Ioc,
    max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

/-- **The remainder bound** `‖1_{symS a b}H‖² ≤ 2G₀²(b − a)` when `|A| ≤ G₀` there. -/
theorem norm_sq_symS_le {c a b G₀ : ℝ} (ha : 1 / 2 ≤ a) (hab : a ≤ b) {A : ℂ → ℂ}
    (hG : ∀ x ∈ symS a b, ‖A x‖ ≤ G₀) (h2 : MemLp ((symS a b).indicator (carH c A)) 2 volume) :
    ‖h2.toLp _‖ ^ 2 ≤ G₀ ^ 2 * (2 * (b - a)) := by
  rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.norm_sq_eq_integral]
  have e : ∫ x, ‖((h2.toLp _ : L2C) : ℝ → ℂ) x‖ ^ 2 = ∫ x in symS a b, ‖carH c A x‖ ^ 2 := by
    rw [← integral_indicator (measurableSet_symS a b)]
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
    by_cases hm : x ∈ symS a b
    · rw [indicator_of_mem hm, indicator_of_mem hm]
    · rw [indicator_of_notMem hm, indicator_of_notMem hm]; simp
  rw [e]
  have hG0 : ∀ x ∈ symS a b, ‖carH c A x‖ ^ 2 ≤ G₀ ^ 2 := fun x hx => by
    rw [norm_carH_of_half_le c A (half_le_abs_of_mem_symS ha hx)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hG x hx) 2
  have hfin : volume (symS a b) ≠ ⊤ := by
    unfold symS
    exact (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨measure_Ioc_lt_top, measure_Ioc_lt_top⟩) |>.ne
  calc ∫ x in symS a b, ‖carH c A x‖ ^ 2 ≤ ∫ x in symS a b, G₀ ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
          (integrableOn_const hfin) ((ae_restrict_iff' (measurableSet_symS a b)).2
            (Filter.Eventually.of_forall hG0))
    _ = G₀ ^ 2 * (2 * (b - a)) := by
        rw [setIntegral_const, volume_symS hab (by linarith), smul_eq_mul, mul_comm]

end Cvs.Prolate.Hardy.LipSymmetricPieces

end
