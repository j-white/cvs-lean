import Mathlib
import Cvs.Route.DyadicWorstScale
import Cvs.Route.EvenBulkFloorAlongScales
import Cvs.Route.EvenFloorDownwardClosure
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.PowerLawVisibilityBulkFloor
import Cvs.Route.ScaleSelectionSets
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Worst and best scales of the dyadic windows

Lower sets of `ℝ` are linearly ordered, so every dyadic window `[2^k, 2^{k+1})` has a worst scale `Cvs.Route.DyadicWorstScale.worst k`
and a best scale `best k`. For infinite `S`, worst-scale floors give the floor along `S`, which gives best-scale
floors frequently; the last is `RiemannHypothesis`, holds at loss `(2^{k+1})^{1/2}`, gives a strip of width `θ` at
loss `(2^{k+1})^θ`, and off `RiemannHypothesis` fails at every large `k` for exponents below `topDepth`.
-/

noncomputable section

open Real Filter Set
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.Route.DyadicWorstBestScales
open Cvs.ZeroCounting

open Cvs.Route.ScaleSelectionSets (dyadic dyadic_nonempty)

/-! ### 1. A largest member of a finite family of down-closed predicates -/

/-- **A finite nonempty family of down-closed predicates on `ℝ` has a largest member.** -/
theorem exists_best {α : Type*} (W : Finset α) (hW : W.Nonempty) (F : α → ℝ → Prop)
    (hF : ∀ a b₁ b₂, b₁ ≤ b₂ → F a b₂ → F a b₁) : ∃ x ∈ W, ∀ b, (∃ y ∈ W, F y b) → F x b := by
  let S : α → LowerSet ℝ := fun a => ⟨{b | F a b}, by intro b₂ b₁ h hb; exact hF a b₁ b₂ h hb⟩
  obtain ⟨x, hx, hmax⟩ := W.exists_max_image S hW
  exact ⟨x, hx, fun b ⟨y, hy, hyb⟩ => LowerSet.coe_subset_coe.mpr (hmax y hy) hyb⟩

/-! ### 2. The best scale of a dyadic window -/

/-- A scale of a finite nonempty window carrying every floor carried by some scale of it. -/
theorem exists_best_evenBulkFloor (W : Finset ℕ) (hW : W.Nonempty) :
    ∃ x ∈ W, ∀ b, (∃ y ∈ W, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor y b) → Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b :=
  exists_best W hW Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor Cvs.Route.DyadicWorstScale.evenBulkFloor_downClosed

/-- The best scale of the dyadic window `[2^k, 2^{k+1})`. -/
def best (k : ℕ) : ℕ := (exists_best_evenBulkFloor (dyadic k) (dyadic_nonempty k)).choose

/-- `best k ∈ [2^k, 2^{k+1})`. -/
theorem best_mem (k : ℕ) : best k ∈ dyadic k :=
  (exists_best_evenBulkFloor (dyadic k) (dyadic_nonempty k)).choose_spec.1

/-- **The floor at the best scale is the floor at some scale of the window.** -/
theorem evenBulkFloor_best_iff (k : ℕ) (b : ℝ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (best k) b ↔ ∃ y ∈ dyadic k, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor y b :=
  ⟨fun h => ⟨best k, best_mem k, h⟩,
    (exists_best_evenBulkFloor (dyadic k) (dyadic_nonempty k)).choose_spec.2 b⟩

/-- **Each scale of a window lies between its worst and its best scale.** -/
theorem worst_imp_imp_best {k y : ℕ} (hy : y ∈ dyadic k) (b : ℝ) :
    (Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (Cvs.Route.DyadicWorstScale.worst k) b → Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor y b) ∧
      (Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor y b → Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (best k) b) :=
  ⟨fun h => Cvs.Route.DyadicWorstScale.evenBulkFloor_of_worst h y hy, fun h => (evenBulkFloor_best_iff k b).mpr ⟨y, hy, h⟩⟩

/-- `2^k ≤ best k`. -/
theorem two_pow_le_best (k : ℕ) : 2 ^ k ≤ best k := (Finset.mem_Ico.mp (best_mem k)).1

/-- `best k < 2^{k+1}`. -/
theorem best_lt (k : ℕ) : best k < 2 ^ (k + 1) := (Finset.mem_Ico.mp (best_mem k)).2

/-- The best scales tend to infinity. -/
theorem tendsto_best : Tendsto best atTop atTop :=
  tendsto_atTop_mono (fun k => (Nat.lt_two_pow_self).le.trans (two_pow_le_best k)) tendsto_id

/-! ### 3. Frequent floors and frequent best-scale floors -/

/-- **Frequent floors give frequent best-scale floors**: loss `x^ε` at infinitely many `x` gives loss
`(2^{k+1})^ε` at `best k` for infinitely many `k`. -/
theorem frequently_best_of_frequently {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-(x : ℝ) ^ ε)) :
    ∃ᶠ k : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (best k) (-((2 : ℝ) ^ (k + 1)) ^ ε) := by
  rw [frequently_atTop] at h ⊢
  intro K
  obtain ⟨x, hx, hfl⟩ := h (2 ^ K)
  have hx1 : 1 ≤ x := le_trans Nat.one_le_two_pow hx
  refine ⟨Nat.log 2 x, Nat.le_log_of_pow_le (by norm_num) hx, ?_⟩
  refine (evenBulkFloor_best_iff _ _).mpr ⟨x, Cvs.Route.DyadicWorstScale.mem_dyadic_log hx1, Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono ?_ hfl⟩
  have hlt : (x : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 x + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num) x).le
  have := Real.rpow_le_rpow (Nat.cast_nonneg x) hlt hε
  linarith

/-- The window loss against the best-scale loss: `C (2^{k+1})^κ ≤ (max C 0 · 2^κ) (best k)^κ` for `κ ≥ 0`. -/
theorem loss_le_best (k : ℕ) (C : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    -(max C 0 * (2 : ℝ) ^ κ) * ((best k : ℕ) : ℝ) ^ κ ≤ -C * ((2 : ℝ) ^ (k + 1)) ^ κ := by
  have hle : ((2 : ℝ) ^ k) ≤ best k := by exact_mod_cast two_pow_le_best k
  have h1 := Real.rpow_le_rpow (by positivity) hle hκ
  have hsplit : ((2 : ℝ) ^ (k + 1)) ^ κ = (2 : ℝ) ^ κ * ((2 : ℝ) ^ k) ^ κ := by
    rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num), mul_comm]
  have h0 := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) κ
  have h2 := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) κ
  have hM := le_max_right C 0
  have ha : max C 0 * (2 : ℝ) ^ κ * ((2 : ℝ) ^ k) ^ κ ≤ max C 0 * (2 : ℝ) ^ κ * ((best k : ℕ) : ℝ) ^ κ :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hM h2.le)
  have hb : C * ((2 : ℝ) ^ κ * ((2 : ℝ) ^ k) ^ κ) ≤ max C 0 * ((2 : ℝ) ^ κ * ((2 : ℝ) ^ k) ^ κ) :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) (mul_nonneg h2.le h0)
  rw [hsplit]
  nlinarith

/-- **Frequent best-scale floors give frequent floors**: loss `(2^{k+1})^ε` at `best k` for infinitely many `k`
gives loss `x^{2ε}` at infinitely many `x`. -/
theorem frequently_of_frequently_best {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∃ᶠ k : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (best k) (-((2 : ℝ) ^ (k + 1)) ^ ε)) :
    ∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-(x : ℝ) ^ (2 * ε)) := by
  have h' : ∃ᶠ k : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (best k) (-((best k : ℕ) : ℝ) ^ (2 * ε)) := by
    refine (h.and_eventually (eventually_ge_atTop 1)).mono fun k hk => Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono ?_ hk.1
    have hb : (2 : ℝ) ^ k ≤ best k := by exact_mod_cast two_pow_le_best k
    have h2 : (2 : ℝ) ^ (k + 1) ≤ ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by have := hk.2; omega)
    have h1 : (2 : ℝ) ^ (k + 1) ≤ ((best k : ℕ) : ℝ) ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      exact h2.trans (pow_le_pow_left₀ (by positivity) hb 2)
    have h3 := Real.rpow_le_rpow (by positivity) h1 hε
    rw [← Real.rpow_mul (Nat.cast_nonneg _)] at h3
    linarith
  exact tendsto_best.frequently h'

/-! ### 4. The best-scale floor and `RiemannHypothesis` -/

/-- The even bulk floor at loss `(2^{k+1})^ε` at the best scale of infinitely many dyadic windows, every `ε > 0`. -/
def BestFloor : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ᶠ k : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (best k) (-((2 : ℝ) ^ (k + 1)) ^ ε)

/-- **`RiemannHypothesis ↔ BestFloor`.** -/
theorem rh_iff_bestFloor : RiemannHypothesis ↔ BestFloor := by
  constructor
  · intro hRH ε hε
    exact frequently_best_of_frequently hε.le (Cvs.Route.PowerLawVisibilityBulkFloor.rh_iff_subpoly_evenBulkFloor.mp hRH ε hε)
  · intro h
    refine Cvs.Route.PowerLawVisibilityBulkFloor.rh_iff_subpoly_evenBulkFloor.mpr fun ε hε => ?_
    have := frequently_of_frequently_best (by positivity : (0 : ℝ) ≤ ε / 2) (h (ε / 2) (by positivity))
    have e : 2 * (ε / 2) = ε := by ring
    rwa [e] at this

/-- **`BestFloor` is the floor at some scale of infinitely many dyadic windows.** -/
theorem bestFloor_iff :
    BestFloor ↔ ∀ ε : ℝ, 0 < ε →
      ∃ᶠ k : ℕ in atTop, ∃ y ∈ dyadic k, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor y (-((2 : ℝ) ^ (k + 1)) ^ ε) :=
  forall₂_congr fun _ _ => frequently_congr (Eventually.of_forall fun k => evenBulkFloor_best_iff k _)

/-- **Worst scales, any infinite `S`, best scales**: for `ε ≥ 0`, the worst-scale floor eventually gives the floor
along `S`, which gives the best-scale floor frequently. -/
theorem worst_imp_floorAlong_imp_best {S : Set ℕ} (hS : S.Infinite) {ε : ℝ} (hε : 0 ≤ ε) :
    ((∀ᶠ k : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (Cvs.Route.DyadicWorstScale.worst k) (-((2 : ℝ) ^ k) ^ ε)) →
        Cvs.Route.EvenBulkFloorAlongScales.FloorAlong S fun x => (x : ℝ) ^ ε) ∧
      (Cvs.Route.EvenBulkFloorAlongScales.FloorAlong S (fun x => (x : ℝ) ^ ε) →
        ∃ᶠ k : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (best k) (-((2 : ℝ) ^ (k + 1)) ^ ε)) :=
  ⟨fun h => (Cvs.Route.DyadicWorstScale.eventually_evenBulkFloor_of_worst hε h).mono fun _ hx _ => hx,
    fun h => frequently_best_of_frequently hε (Cvs.Route.EvenBulkFloorAlongScales.frequently_of_eventually_mem hS h)⟩

/-- **Every scale of every window `k ≥ 1` carries the floor at loss `C₀ (2^{k+1})^{1/2}`**,
`C₀ = |archSymbol 0| + 4(log 4 + 4)`. -/
theorem evenBulkFloor_window_neg_rpow_half {k y : ℕ} (hk : 1 ≤ k) (hy : y ∈ dyadic k) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor y
      (-(|Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 4 * (Real.log 4 + 4)) * ((2 : ℝ) ^ (k + 1)) ^ (1 / 2 : ℝ)) := by
  have hmem := Finset.mem_Ico.mp hy
  have hy1 : 1 < y := lt_of_lt_of_le (Nat.one_lt_two_pow (by omega)) hmem.1
  refine Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono ?_ (Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_neg_rpow_half hy1)
  have hC : 0 ≤ |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 4 * (Real.log 4 + 4) := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    positivity
  have hle : (y : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast hmem.2.le
  have h1 := Real.rpow_le_rpow (Nat.cast_nonneg y) hle (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith

/-- **Zero-free strip from the best scales**: loss `C (2^{k+1})^θ` at `best k` for infinitely many `k`, `θ ≥ 0`,
gives `1/2 − θ ≤ Re ρ ≤ 1/2 + θ`. -/
theorem zeroFreeStrip_of_frequently_best {θ C : ℝ} (hθ : 0 ≤ θ)
    (h : ∃ᶠ k : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (best k) (-C * ((2 : ℝ) ^ (k + 1)) ^ θ))
    (ρ : nonTrivialZeroSet) : 1 / 2 - θ ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ 1 / 2 + θ := by
  have h' : ∃ᶠ k : ℕ in atTop,
      Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (best k) (-(max C 0 * (2 : ℝ) ^ θ) * ((best k : ℕ) : ℝ) ^ θ) :=
    h.mono fun k hk => Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono (loss_le_best k C hθ) hk
  exact Cvs.Route.PowerLawVisibilityBulkFloor.zeroFreeStrip_of_frequently_evenBulkFloor_neg_rpow hθ (tendsto_best.frequently h') ρ

/-- **Off `RiemannHypothesis` the best scales fail**: for `0 ≤ κ < topDepth` and every `C`, the floor at loss
`C (2^{k+1})^κ` fails at `best k` for all large `k`. -/
theorem eventually_not_best_of_not_rh (hRH : ¬ RiemannHypothesis) {κ : ℝ} (hκ : κ < Cvs.StepA.Edge.CaseInfinityJointRates.topDepth)
    (hκ0 : 0 ≤ κ) (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (best k) (-C * ((2 : ℝ) ^ (k + 1)) ^ κ) := by
  have hev := tendsto_best.eventually (Cvs.Route.PowerLawVisibilityBulkFloor.hV_lt_topDepth hRH hκ (max C 0 * (2 : ℝ) ^ κ))
  exact hev.mono fun k hk hfl => hk (Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono (loss_le_best k C hκ0) hfl)

/-! ### 5. The reflection-even floor along a set with bounded gaps -/

/-- **A growing loss passes down a gap**: for monotone `Q`, if every `x ≥ 1` has `x ≤ x' ≤ g x` with
`EvenFloor x' (−Q x')`, then `EvenFloor x (−Q (g x))` at every `x ≥ 1`. -/
theorem evenFloor_neg_of_gaps {Q : ℕ → ℝ} (hQ : Monotone Q) {g : ℕ → ℕ}
    (hS : ∀ x : ℕ, 1 ≤ x → ∃ x', x ≤ x' ∧ x' ≤ g x ∧ Cvs.Route.EvenFloorDownwardClosure.EvenFloor x' (-Q x')) {x : ℕ} (hx : 1 ≤ x) :
    Cvs.Route.EvenFloorDownwardClosure.EvenFloor x (-Q (g x)) := by
  obtain ⟨x', hxx', hxg, hfl⟩ := hS x hx
  exact Cvs.Route.EvenFloorDownwardClosure.evenFloor_mono (neg_le_neg (hQ hxg)) (Cvs.Route.EvenFloorDownwardClosure.evenFloor_of_le hx hxx' hfl)

end Cvs.Route.DyadicWorstBestScales
