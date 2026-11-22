import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Route.EvenFormBelowBulk
import Cvs.Route.EvenSlotPrimeForm
import Cvs.Route.EvenSlotSpectralMinorant
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Prolate spine floor reduction for the even spectral and prime-form slots

Past `c₀W ≤ 2πx`, `Cvs.L2a.EvenSectorReflectionBound.L2a_even_R1` under `ReflBound x 1 δR` (`δR ≤ 1`) gives
`((1 − δR)/2 · b_R(x)) ‖r‖² ≤ Q_x(r)` on `R₁`. Substituting this floor into `EvenWeightedRatio`,
`EvenTameWeightedRatio`, and `SpecRatio` replaces `Q_x(r)` on `R₁` with `((1 − δR)/2 · b_R(x)) ‖r‖²`.
-/

noncomputable section

open Real Filter Finset
open scoped InnerProductSpace

namespace Cvs.Route.ProlateSpineFloorEvenSlots
open Cvs.ZeroCounting

open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.L2a.EvenSectorReflectionBound (R1 ReflBound bR)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.Route.EvenWindowBulkCoupling (EvenBulkFloor)
open Cvs.Route.EvenFormBelowBulk (EvenOperatorFloor EvenWeightedChannel EvenWeightedRatio)
open Cvs.Route.EvenSlotPrimeForm (EvenTameOperatorFloor EvenTameWeightedChannel EvenTameWeightedRatio)
open Cvs.Route.EvenSlotSpectralMinorant (SpecComparison SpecRepresentation SpecRatio)

/-! ### The explicit prolate `L²` floor on `R₁` -/

/-- **Prolate `L²` floor on `R₁`**: past `c₀W ≤ 2πx`, `ReflBound x 1 δR` (`δR ≤ 1`) gives
`((1 − δR)/2 * bR x) * ‖r‖² ≤ Qx x r` for every `r ∈ R₁ x`. -/
theorem evenRungFloor_of_reflBound {x : ℕ} (hx : c0W ≤ 2 * π * x) {δR : ℝ} (hδ : δR ≤ 1)
    (hR : ReflBound x 1 δR) {r : Dom x} (hr : r ∈ R1 x) :
    ((1 - δR) / 2 * bR x) * ‖r‖ ^ 2 ≤ Qx x r := by
  have h := Cvs.L2a.EvenSectorReflectionBound.L2a_even_R1 x hx hδ hR r hr
  have e : Cvs.L2a.EvenSectorReflectionBound.kappaE x δR * (1 - Cvs.Prolate.EvenRungsByIndex.lamR (2 * π * x) 2) = (1 - δR) / 2 * bR x := by
    unfold Cvs.L2a.EvenSectorReflectionBound.kappaE bR; ring
  rwa [e] at h

/-- **`EvenFormBelowBulk`'s `EvenWeightedRatio` from `ReflBound` and an `L²` norm bound on `κ`.** -/
theorem evenWeightedRatio_of_reflBound_norm {x : ℕ} (hx : c0W ≤ 2 * π * x) {δR : ℝ} (hδ : δR ≤ 1)
    (hR : ReflBound x 1 δR) {κ : Dom x → ℝ}
    (hκ : ∀ r ∈ R1 x, κ r ≤ ((1 - δR) / 2 * bR x) * ‖r‖ ^ 2) :
    EvenWeightedRatio x 0 κ := fun r hr => by
  rw [sub_zero, one_mul]
  exact (hκ r hr).trans (evenRungFloor_of_reflBound hx hδ hR hr)

/-- **`EvenSlotPrimeForm`'s prime-form `EvenTameWeightedRatio` from `ReflBound` and an `L²` norm bound on `κ`.** -/
theorem evenTameWeightedRatio_of_reflBound_norm {x : ℕ} (hx : c0W ≤ 2 * π * x) {δR : ℝ} (hδ : δR ≤ 1)
    (hR : ReflBound x 1 δR) {κ : (Cvs.Approximant.SpineSubspace.SF x → ℝ) → ℝ}
    (hκ : ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
      κ a ≤ ((1 - δR) / 2 * bR x) *
        ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖ ^ 2) :
    EvenTameWeightedRatio x 0 κ := fun a => by
  rw [sub_zero, one_mul]
  exact (hκ a).trans
    (evenRungFloor_of_reflBound hx hδ hR (Cvs.Route.EvenWindowBulkCoupling.evenPart_spineMap_mem_R1 x a))

/-! ### The spectral slot (`Cvs.Route.EvenSlotSpectralMinorant`) against the prolate `L²` floor -/

/-- **The spectral ratio against the prolate `L²` floor on `R₁`**:
`∑_k c_k(r)²/g_k + A(u r, u r) ≤ ((1 − δR)/2 * bR x) * ‖r‖²` for `r ∈ R₁ x`. -/
def SpecNormRatio (x : ℕ) {ι : Type*} [Fintype ι] (δR : ℝ) (g : ι → ℝ)
    (A : LinearMap.BilinForm ℝ (Dom x)) (c : Dom x → ι → ℝ) (u : Dom x → Dom x) : Prop :=
  ∀ r ∈ R1 x, ∑ k, c r k ^ 2 / g k + A (u r) (u r) ≤ ((1 - δR) / 2 * bR x) * ‖r‖ ^ 2

/-- **`SpecNormRatio` and `ReflBound` give `Cvs.Route.EvenSlotSpectralMinorant.SpecRatio`** past `c₀W ≤ 2πx`. -/
theorem specRatio_of_reflBound_norm {x : ℕ} {ι : Type*} [Fintype ι] (hx : c0W ≤ 2 * π * x)
    {δR : ℝ} (hδ : δR ≤ 1) (hR : ReflBound x 1 δR) {g : ι → ℝ}
    {A : LinearMap.BilinForm ℝ (Dom x)} {c : Dom x → ι → ℝ} {u : Dom x → Dom x}
    (hN : SpecNormRatio x δR g A c u) :
    SpecRatio x g A c u := fun r hr =>
  (hN r hr).trans (evenRungFloor_of_reflBound hx hδ hR hr)

/-- **Even window positivity at `x` from spectral data, `ReflBound`, and `SpecNormRatio`.** -/
theorem Q_nonneg_of_spec_reflBound_norm {x : ℕ} {ι : Type*} [Fintype ι] (hx : c0W ≤ 2 * π * x)
    {δR : ℝ} (hδ : δR ≤ 1) (hR : ReflBound x 1 δR)
    {φ : ι → Dom x} {g : ι → ℝ} {A : LinearMap.BilinForm ℝ (Dom x)}
    {c : Dom x → ι → ℝ} {u : Dom x → Dom x} {K : Submodule ℝ (Dom x)}
    (hg : ∀ k, 0 < g k) (hAs : A.IsSymm) (hA : ∀ v ∈ K, 0 ≤ A v v)
    (hbulk : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → w ∈ K) (hu : ∀ r ∈ R1 x, u r ∈ K)
    (hC : SpecComparison x φ g A) (hRep : SpecRepresentation x φ A c u)
    (hN : SpecNormRatio x δR g A c u) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v :=
  Cvs.Route.EvenSlotSpectralMinorant.Q_nonneg_of_spec hg hAs hA hbulk hu hC hRep (specRatio_of_reflBound_norm hx hδ hR hN)

/-- **`RiemannHypothesis` from spectral data, `ReflBound`, and `SpecNormRatio` at infinitely many `x`.** -/
theorem riemannHypothesis_of_spec_reflBound_norm
    (h : ∃ᶠ x : ℕ in atTop, ∃ (n : ℕ) (δR : ℝ) (φ : Fin n → Dom x) (g : Fin n → ℝ)
      (A : LinearMap.BilinForm ℝ (Dom x)) (c : Dom x → Fin n → ℝ) (u : Dom x → Dom x)
      (K : Submodule ℝ (Dom x)),
      δR ≤ 1 ∧ ReflBound x 1 δR ∧ (∀ k, 0 < g k) ∧ A.IsSymm ∧
      (∀ v ∈ K, 0 ≤ A v v) ∧ (∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → w ∈ K) ∧ (∀ r ∈ R1 x, u r ∈ K) ∧
      SpecComparison x φ g A ∧ SpecRepresentation x φ A c u ∧ SpecNormRatio x δR g A c u) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually Cvs.Route.WindowPositivityBulkCoupling.eventually_c0W_le).mono fun x ⟨hx', hx⟩ => ?_)
  obtain ⟨n, δR, φ, g, A, c, u, K, hδ, hRefl, hg, hAs, hA, hb, hu, hC, hRep, hN⟩ := hx'
  exact Q_nonneg_of_spec_reflBound_norm hx hδ hRefl hg hAs hA hb hu hC hRep hN

/-! ### The prime-form slot (`Cvs.Route.EvenSlotPrimeForm`) against the prolate `L²` floor -/

/-- **Even window positivity at `x` from the prime-form slot (`Cvs.Route.EvenSlotPrimeForm`), `ReflBound`, and the
prolate `L²` norm bound on `κ`.** -/
theorem Q_nonneg_of_even_tame_reflBound_norm {x : ℕ} (hx : c0W ≤ 2 * π * x) {δR : ℝ} (hδ : δR ≤ 1)
    (hRefl : ReflBound x 1 δR) {M : LinearMap.BilinForm ℝ (Dom x)} {κ : (Cvs.Approximant.SpineSubspace.SF x → ℝ) → ℝ}
    (hF : EvenTameOperatorFloor x M) (hC : EvenTameWeightedChannel x M κ)
    (hκ : ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
      κ a ≤ ((1 - δR) / 2 * bR x) *
        ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖ ^ 2) :
    ∀ φ ∈ Ev x, 0 ≤ Qx x φ :=
  Cvs.Route.EvenSlotPrimeForm.Q_nonneg_of_even_tame_weighted (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx) le_rfl one_pos hF hC
    (evenTameWeightedRatio_of_reflBound_norm hx hδ hRefl hκ)

/-- **`RiemannHypothesis` from the prime-form slot (`Cvs.Route.EvenSlotPrimeForm`), `ReflBound`, and the prolate `L²`
norm bound on `κ` at infinitely many `x`.** -/
theorem riemannHypothesis_of_even_tame_reflBound_norm
    (h : ∃ᶠ x : ℕ in atTop, ∃ (δR : ℝ) (M : LinearMap.BilinForm ℝ (Dom x))
      (κ : (Cvs.Approximant.SpineSubspace.SF x → ℝ) → ℝ),
      δR ≤ 1 ∧ ReflBound x 1 δR ∧ EvenTameOperatorFloor x M ∧ EvenTameWeightedChannel x M κ ∧
      ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
        κ a ≤ ((1 - δR) / 2 * bR x) *
          ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖ ^ 2) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually Cvs.Route.WindowPositivityBulkCoupling.eventually_c0W_le).mono fun x ⟨hx', hx⟩ => ?_)
  obtain ⟨δR, M, κ, hδ, hRefl, hF, hC, hκ⟩ := hx'
  exact Q_nonneg_of_even_tame_reflBound_norm hx hδ hRefl hF hC hκ

/-! ### The scalar bilinear norm route against the prolate `L²` floor -/

/-- **Even window positivity at `x` from `EvenBulkFloor x b`, `ReflBound x 1 δR`, a bilinear norm
bound `|Q(r, w)| ≤ L_rw ‖r‖ ‖w‖`, and `L_rw² ≤ b * ((1 − δR)/2 * bR x)`.** -/
theorem Q_nonneg_of_bilinear_norm_reflBound {x : ℕ} (hx : c0W ≤ 2 * π * x)
    {b δR L_rw : ℝ} (hb : 0 < b) (hδ : δR ≤ 1) (hRefl : ReflBound x 1 δR)
    (hF : EvenBulkFloor x b)
    (hB : ∀ r ∈ R1 x, ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
      |Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) r w| ≤ L_rw * ‖r‖ * ‖w‖)
    (hL : L_rw ^ 2 ≤ b * ((1 - δR) / 2 * bR x)) :
    ∀ φ ∈ Ev x, 0 ≤ Qx x φ := by
  have hslot := Cvs.Route.EvenFormBelowBulk.even_weighted_of_norm (x := x) (b := b) (δ := 0) (c := fun r => L_rw * ‖r‖)
    hb hF hB fun r hr => by
      rw [sub_zero, one_mul, mul_pow]
      have h1 : L_rw ^ 2 * ‖r‖ ^ 2 ≤ b * (((1 - δR) / 2 * bR x) * ‖r‖ ^ 2) := by
        calc L_rw ^ 2 * ‖r‖ ^ 2 ≤ (b * ((1 - δR) / 2 * bR x)) * ‖r‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hL (sq_nonneg ‖r‖)
          _ = b * (((1 - δR) / 2 * bR x) * ‖r‖ ^ 2) := by ring
      exact h1.trans (mul_le_mul_of_nonneg_left (evenRungFloor_of_reflBound hx hδ hRefl hr) hb.le)
  exact Cvs.Route.EvenFormBelowBulk.Q_nonneg_of_even_weighted le_rfl one_pos hslot.1 hslot.2.1 hslot.2.2

/-- **`RiemannHypothesis` from `EvenBulkFloor x b`, `ReflBound x 1 δR`, a bilinear norm bound
`|Q(r, w)| ≤ L_rw ‖r‖ ‖w‖`, and `L_rw² ≤ b * ((1 − δR)/2 * bR x)` at infinitely many `x`.** -/
theorem riemannHypothesis_of_bilinear_norm_reflBound
    (h : ∃ᶠ x : ℕ in atTop, ∃ b δR L_rw : ℝ,
      0 < b ∧ δR ≤ 1 ∧ ReflBound x 1 δR ∧ EvenBulkFloor x b ∧
      (∀ r ∈ R1 x, ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
        |Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) r w| ≤ L_rw * ‖r‖ * ‖w‖) ∧
      L_rw ^ 2 ≤ b * ((1 - δR) / 2 * bR x)) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually Cvs.Route.WindowPositivityBulkCoupling.eventually_c0W_le).mono fun x ⟨hx', hx⟩ => ?_)
  obtain ⟨b, δR, L_rw, hb, hδ, hRefl, hF, hB, hL⟩ := hx'
  exact Q_nonneg_of_bilinear_norm_reflBound hx hb hδ hRefl hF hB hL

end Cvs.Route.ProlateSpineFloorEvenSlots
