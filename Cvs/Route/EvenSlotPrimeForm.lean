import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.EvenChannelSplitPrime
import Cvs.Route.EvenTameDenseCoupling
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.CouplingCauchySchwarzBulk
import Cvs.WeilForm.CouplingFiniteSchur
import Cvs.WeilForm.CouplingPrimeForm
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even slot in prime form

Over the `u` tame on `[1/x, 1]` with `w_u` even and `⊥ R₁`: `0 ≤ M(w_u, w_u) ≤ Q(w_u)`, `κ(a) ≥ 0` with
`(Σ_n Λ(n)⟨u, τ_a(n·)⟩ − arch(τ_a, u) − pole(τ_a, u))² ≤ κ(a)·M(w_u, w_u)` (`τ_a` the tail of `spineMap x a`), and
`κ(a) ≤ (1−δ)Q(e_a)`. At `80 ≤ 2πx`, by `EvenTameDenseCoupling`'s density, `Q ≥ 0` on `Ev x` is this slot with `δ = 0` and RH is the
slot at infinitely many `x`; for every `M` under `EvenFormBelowBulk`'s floor it is `EvenFormBelowBulk`'s slot.
-/

noncomputable section

open Real Filter
open scoped InnerProductSpace

namespace Cvs.Route.EvenSlotPrimeForm
open Cvs.ZeroCounting

open Cvs.WeilForm.ThetaSpaceParseval (dil poleP poleM)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.Xi.PhysicalReciprocalReflection (reciprocal)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.WeilForm.CouplingPrimeForm (tail)

/-! ### The slot -/

/-- **The even tame operator floor at `x`**: `0 ≤ M(w_u, w_u) ≤ Q(w_u)` for every `u` tame on `[1/x, 1]` with `w_u`
even and `L²`-orthogonal to `R₁`. -/
def EvenTameOperatorFloor (x : ℕ) (M : LinearMap.BilinForm ℝ (Dom x)) : Prop :=
  ∀ (u : ℝ → ℝ) (hx0 : (0 : ℝ) < x) (hu : Tame u (1 / x) 1),
    Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ Ev x → Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ (R1 x)ᗮ →
    0 ≤ M (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) ∧ M (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) ≤ Qx x (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)

/-- **The even tame weighted channel at `x`**: `κ(a) ≥ 0` and
`(Σ_n Λ(n)⟨u, τ_a(n·)⟩ − arch(τ_a, u) − pole(τ_a, u))² ≤ κ(a)·M(w_u, w_u)`, `τ_a` the tail of `spineMap x a`, for
every `a` and every `u` tame on `[1/x, 1]` with `w_u` even and `L²`-orthogonal to `R₁`. -/
def EvenTameWeightedChannel (x : ℕ) (M : LinearMap.BilinForm ℝ (Dom x)) (κ : (Cvs.Approximant.SpineSubspace.SF x → ℝ) → ℝ) : Prop :=
  ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, 0 ≤ κ a ∧ ∀ (u : ℝ → ℝ) (hx0 : (0 : ℝ) < x) (hu : Tame u (1 / x) 1),
    Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ Ev x → Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ (R1 x)ᗮ →
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil u (tail x a) n
        - (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale (tail x a)) (Cvs.L2a.TailLogScaleTest.logScale u) t)
        - (poleP (tail x a) * poleM u + poleM (tail x a) * poleP u)) ^ 2
      ≤ κ a * M (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)

/-- **The even tame weighted ratio at `x`**: `κ(a) ≤ (1−δ)·Q(e_a)` for every `a`, `e_a` the even part of
`spineMap x a`. -/
def EvenTameWeightedRatio (x : ℕ) (δ : ℝ) (κ : (Cvs.Approximant.SpineSubspace.SF x → ℝ) → ℝ) : Prop :=
  ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, κ a ≤ (1 - δ) * Qx x (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a))

/-- **The prime-form channel is the form channel**: at `80 ≤ 2πx` the prime–arch–pole value is `Q(e_a, w_u)`. -/
theorem evenTameWeightedChannel_iff {x : ℕ} (hx : 80 ≤ 2 * π * x) (M : LinearMap.BilinForm ℝ (Dom x))
    (κ : (Cvs.Approximant.SpineSubspace.SF x → ℝ) → ℝ) :
    EvenTameWeightedChannel x M κ ↔ ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, 0 ≤ κ a ∧
      ∀ (u : ℝ → ℝ) (hx0 : (0 : ℝ) < x) (hu : Tame u (1 / x) 1),
        Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ Ev x → Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ (R1 x)ᗮ →
        Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
            (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) ^ 2
          ≤ κ a * M (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) := by
  refine forall_congr' fun a => and_congr_right' (forall_congr' fun u => forall_congr' fun hx0 =>
    forall_congr' fun hu => forall_congr' fun he => imp_congr_right fun _ => ?_)
  rw [Cvs.Route.EvenChannelSplitPrime.QWbil_evenPart_spineMap_wv_eq_channels hx a hu he]

/-- **The even tame operator floor gives the zero even bulk floor**, at `80 ≤ 2πx`. -/
theorem evenBulkFloor_zero_of_tameOperatorFloor {x : ℕ} (hx : 80 ≤ 2 * π * x) {M : LinearMap.BilinForm ℝ (Dom x)}
    (hF : EvenTameOperatorFloor x M) : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  Cvs.Route.EvenTameDenseCoupling.evenBulkFloor_of_tame hx fun u hx0 hu he hw => by
    rw [zero_mul]; exact (hF u hx0 hu he hw).1.trans (hF u hx0 hu he hw).2

/-! ### The slot gives even window positivity -/

/-- **The even tame coupling from the slot**, at `80 ≤ 2πx`. -/
theorem evenTameCoupling_of_weighted {x : ℕ} (hx : 80 ≤ 2 * π * x) {M : LinearMap.BilinForm ℝ (Dom x)}
    {κ : (Cvs.Approximant.SpineSubspace.SF x → ℝ) → ℝ} {δ : ℝ} (hF : EvenTameOperatorFloor x M) (hC : EvenTameWeightedChannel x M κ)
    (hR : EvenTameWeightedRatio x δ κ) : Cvs.Route.EvenChannelSplitPrime.EvenTameCoupling x δ := by
  intro a u hx0 hu he hw
  have hC' := (evenTameWeightedChannel_iff hx M κ).1 hC a
  have h := Cvs.WeilForm.CouplingCauchySchwarzBulk.sq_le_of_weighted (B := Bx x) (M := M)
    (r := Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) (w := Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)
    (hF u hx0 hu he hw).1 (by rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]; exact (hF u hx0 hu he hw).2) hC'.1 (hC'.2 u hx0 hu he hw)
    (by rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]; exact hR a)
  rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self, Cvs.WeilForm.CouplingFiniteSchur.Bx_self] at h
  exact h

/-- **The prime-form channel and ratio with `δ < 1` give even rung positivity.** -/
theorem evenRungPos_of_tame_weighted {x : ℕ} {M : LinearMap.BilinForm ℝ (Dom x)} {κ : (Cvs.Approximant.SpineSubspace.SF x → ℝ) → ℝ}
    {δ : ℝ} (hδ : δ < 1) (hC : EvenTameWeightedChannel x M κ) (hR : EvenTameWeightedRatio x δ κ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenRungPos x := by
  intro r hr
  obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
  exact nonneg_of_mul_nonneg_right ((hC a).1.trans (hR a)) (by linarith)

/-- **Even window positivity at `x` from the slot in prime form**, at `80 ≤ 2πx` with `0 ≤ δ < 1`. -/
theorem Q_nonneg_of_even_tame_weighted {x : ℕ} (hx : 80 ≤ 2 * π * x) {M : LinearMap.BilinForm ℝ (Dom x)}
    {κ : (Cvs.Approximant.SpineSubspace.SF x → ℝ) → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hF : EvenTameOperatorFloor x M)
    (hC : EvenTameWeightedChannel x M κ) (hR : EvenTameWeightedRatio x δ κ) : ∀ φ ∈ Ev x, 0 ≤ Qx x φ :=
  Cvs.Route.EvenWindowBulkCoupling.Q_nonneg_of_even_floor_coupling (evenRungPos_of_tame_weighted hδ1 hC hR) le_rfl hδ0
    (evenBulkFloor_zero_of_tameOperatorFloor hx hF)
    (Cvs.Route.EvenTameDenseCoupling.evenFormCoupling_of_evenTameCoupling hx (evenTameCoupling_of_weighted hx hF hC hR))

/-! ### The slot is `EvenFormBelowBulk`'s slot for every `M` -/

/-! ### Even window positivity and RH -/

end Cvs.Route.EvenSlotPrimeForm
