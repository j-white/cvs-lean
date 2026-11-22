import Mathlib
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.PowerLawVisibilityBulkFloor
import Cvs.Route.ScaleSelectionSets
import Cvs.StepA.Edge.CaseInfinityJointRates

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The worst scale of each dyadic window

Floors at a scale form a down-set of `ℝ`, and down-sets of `ℝ` form a chain, so every finite nonempty window has a
scale whose floor implies the floor at every scale of the window. Along the worst scale `worst k` of each dyadic
window `[2^k, 2^{k+1})`, the floor at loss `(2^k)^ε` is equivalent to the floor at that loss on the whole window
and, over all `ε > 0`, to `RiemannHypothesis`.
-/

noncomputable section

open Real Filter Set

namespace Cvs.Route.DyadicWorstScale
open Cvs.ZeroCounting

open Cvs.Route.ScaleSelectionSets (dyadic dyadic_nonempty le_of_mem_dyadic)

/-! ### 1. Down-sets of `ℝ` are a chain; finite families have a smallest member -/

/-- Two down-closed predicates on `ℝ` are comparable. -/
theorem downClosed_total {P Q : ℝ → Prop} (hP : ∀ b₁ b₂, b₁ ≤ b₂ → P b₂ → P b₁)
    (hQ : ∀ b₁ b₂, b₁ ≤ b₂ → Q b₂ → Q b₁) : (∀ b, P b → Q b) ∨ (∀ b, Q b → P b) := by
  by_contra h
  push Not at h
  obtain ⟨⟨b₁, hP₁, hQ₁⟩, ⟨b₂, hQ₂, hP₂⟩⟩ := h
  rcases le_total b₁ b₂ with h12 | h21
  · exact hQ₁ (hQ b₁ b₂ h12 hQ₂)
  · exact hP₂ (hP b₂ b₁ h21 hP₁)

/-- **A finite nonempty family of down-closed predicates on `ℝ` has a smallest member.** -/
theorem exists_worst {α : Type*} (W : Finset α) (hW : W.Nonempty) (F : α → ℝ → Prop)
    (hF : ∀ a b₁ b₂, b₁ ≤ b₂ → F a b₂ → F a b₁) : ∃ x ∈ W, ∀ b, F x b → ∀ y ∈ W, F y b := by
  classical
  induction hW using Finset.Nonempty.cons_induction with
  | singleton a =>
    exact ⟨a, Finset.mem_singleton_self a, fun b hb y hy => by
      rw [Finset.mem_singleton] at hy; exact hy ▸ hb⟩
  | cons a s ha _ ih =>
    obtain ⟨m, hm, hmin⟩ := ih
    rcases downClosed_total (hF a) (hF m) with h | h
    · refine ⟨a, Finset.mem_cons_self a s, fun b hb y hy => ?_⟩
      rcases Finset.mem_cons.mp hy with rfl | hy
      · exact hb
      · exact hmin b (h b hb) y hy
    · refine ⟨m, Finset.mem_cons.mpr (Or.inr hm), fun b hb y hy => ?_⟩
      rcases Finset.mem_cons.mp hy with rfl | hy
      · exact h b hb
      · exact hmin b hb y hy

/-! ### 2. The worst scale of a dyadic window -/

/-- The even bulk floor is down-closed in the floor parameter. -/
theorem evenBulkFloor_downClosed (x : ℕ) (b₁ b₂ : ℝ) (h : b₁ ≤ b₂) (hf : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b₂) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b₁ :=
  Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono h hf

/-- A scale of a finite nonempty window whose even bulk floor implies the floor at every scale of it. -/
theorem exists_worst_evenBulkFloor (W : Finset ℕ) (hW : W.Nonempty) :
    ∃ x ∈ W, ∀ b, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b → ∀ y ∈ W, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor y b :=
  exists_worst W hW Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor evenBulkFloor_downClosed

/-- The worst scale of the dyadic window `[2^k, 2^{k+1})`. -/
def worst (k : ℕ) : ℕ := (exists_worst_evenBulkFloor (dyadic k) (dyadic_nonempty k)).choose

/-- `worst k ∈ [2^k, 2^{k+1})`. -/
theorem worst_mem (k : ℕ) : worst k ∈ dyadic k :=
  (exists_worst_evenBulkFloor (dyadic k) (dyadic_nonempty k)).choose_spec.1

/-- **The floor at the worst scale is the floor on the whole window.** -/
theorem evenBulkFloor_of_worst {k : ℕ} {b : ℝ} (h : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (worst k) b) :
    ∀ y ∈ dyadic k, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor y b :=
  (exists_worst_evenBulkFloor (dyadic k) (dyadic_nonempty k)).choose_spec.2 b h

/-- **At a window-uniform loss, the worst-scale floor is the whole-window floor.** -/
theorem evenBulkFloor_worst_iff (k : ℕ) (b : ℝ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (worst k) b ↔ ∀ y ∈ dyadic k, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor y b :=
  ⟨evenBulkFloor_of_worst, fun h => h _ (worst_mem k)⟩

/-! ### 3. The worst-scale subsequence and `RiemannHypothesis` -/

/-- Each `x ≥ 1` lies in the dyadic window `k = Nat.log 2 x`. -/
theorem mem_dyadic_log {x : ℕ} (hx : 1 ≤ x) : x ∈ dyadic (Nat.log 2 x) :=
  Finset.mem_Ico.mpr ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) x⟩

/-- **The worst-scale floors at loss `(2^k)^ε` give the floor at loss `x^ε` at every large `x`.** -/
theorem eventually_evenBulkFloor_of_worst {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ᶠ k : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (worst k) (-((2 : ℝ) ^ k) ^ ε)) :
    ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-(x : ℝ) ^ ε) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop (2 ^ K)] with x hx
  have hx1 : 1 ≤ x := le_trans Nat.one_le_two_pow hx
  have hk : K ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) hx
  have hmem := mem_dyadic_log hx1
  have hfl := evenBulkFloor_of_worst (hK _ hk) x hmem
  refine Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono ?_ hfl
  have hle : ((2 : ℝ) ^ Nat.log 2 x) ≤ x := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have := Real.rpow_le_rpow (by positivity) hle hε
  linarith

/-- **`RiemannHypothesis` ↔ the floor at loss `(2^k)^ε` at the worst scale of every large dyadic window,
for every `ε > 0`.** -/
theorem rh_iff_worst :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (worst k) (-((2 : ℝ) ^ k) ^ ε) := by
  constructor
  · intro hRH ε _
    filter_upwards [eventually_ge_atTop 1] with k hk
    have h2 : 2 ≤ worst k := le_trans (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk) (Finset.mem_Ico.mp (worst_mem k)).1
    refine Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono ?_ (Cvs.Route.EvenWindowBulkCoupling.even_floor_coupling_zero_of_rh hRH h2).2.1
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) ε
    linarith
  · intro h
    exact Cvs.Route.PowerLawVisibilityBulkFloor.rh_iff_subpoly_evenBulkFloor.mpr fun ε hε =>
      (eventually_evenBulkFloor_of_worst hε.le (h ε hε)).frequently

/-- Off `RiemannHypothesis`, for `κ < topDepth` the worst-scale floor at loss `C · (2^k)^κ` fails for all large
`k`. -/
theorem eventually_not_worst_of_not_rh (hRH : ¬ RiemannHypothesis) {κ : ℝ} (hκ : κ < Cvs.StepA.Edge.CaseInfinityJointRates.topDepth)
    (hκ0 : 0 ≤ κ) (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (worst k) (-C * ((2 : ℝ) ^ k) ^ κ) := by
  have hev := Cvs.Route.PowerLawVisibilityBulkFloor.hV_lt_topDepth hRH hκ (max C 0)
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  filter_upwards [eventually_ge_atTop X] with k hk hfl
  have hmem := Finset.mem_Ico.mp (worst_mem k)
  have hXk : X ≤ worst k := hk.trans ((Nat.lt_two_pow_self).le.trans hmem.1)
  refine hX _ hXk (Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono ?_ hfl)
  have hle : ((2 : ℝ) ^ k) ≤ worst k := by exact_mod_cast hmem.1
  have h1 := Real.rpow_le_rpow (by positivity) hle hκ0
  have h0 := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) κ
  nlinarith [le_max_left C 0, le_max_right C 0]

end Cvs.Route.DyadicWorstScale
