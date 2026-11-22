import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.EvenSlotSpectralMinorant
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.RepresenterFreeCrossBounds
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.CouplingPrimeForm
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ReflectionEvenPositivityRH
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
# Finite Even Gram Matrix Reduction of Rung Floors and Cross-Term Bounds

Reduces `EvenRungNonneg`, `ReflBound`, `EvenCrossBound`, `EvenTameCrossBound`, and `SpecCrossBound`
on `R₁` to the finite `(x − 1) × (x − 1)` matrix `Cvs.L2a.EvenSectorReflectionBound.evenGram x` on `Cvs.Approximant.SpineSubspace.SF x → ℝ`.
-/

noncomputable section

open Real Filter Finset Matrix
open scoped InnerProductSpace

namespace Cvs.Route.EvenGramRungFloors
open Cvs.ZeroCounting

open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.WeilForm.ThetaSpaceParseval (dil poleP poleM)
open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.L2a.EvenSectorReflectionBound (R1 ReflBound bR evenGram tailQ reflQ)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.CouplingPrimeForm (tail)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.Route.EvenWindowBulkCoupling (EvenRungPos)
open Cvs.Route.EvenFormBelowBulk (EvenOperatorFloor)
open Cvs.Route.EvenSlotPrimeForm (EvenTameOperatorFloor)
open Cvs.Route.EvenSlotSpectralMinorant (SpecComparison)
open Cvs.Route.ProlateSpineFloorEvenSlots (evenRungFloor_of_reflBound)
open Cvs.Route.RepresenterFreeCrossBounds (EvenPosDom EvenRungNonneg EvenChannel EvenCrossBound EvenNormCrossBound EvenTameCrossBound EvenTameNormCrossBound SpecRemRepresentation SpecCrossBound)

/-! ### Bridge between `Qx x` on `R₁` and the finite matrix `evenGram x` -/

/-- **Quadratic form of `evenGram x`**: `a ⬝ᵥ (evenGram x *ᵥ a)` equals `Qx x` evaluated on the
even part of `spineMap x a`. -/
theorem evenGram_quad_eq_Qx (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    a ⬝ᵥ (evenGram x *ᵥ a) =
      Qx x (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) :=
  Cvs.L2a.EvenSectorReflectionBound.quad_evenGram x a

/-! ### Positive semidefiniteness of `evenGram x` and `ReflBound` -/

/-- **Positive semidefiniteness of the finite even Gram matrix `evenGram x`.** -/
def EvenGramNonneg (x : ℕ) : Prop :=
  ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, 0 ≤ a ⬝ᵥ (evenGram x *ᵥ a)

/-- **`EvenRungPos x` is equivalent to `EvenGramNonneg x`.** -/
theorem evenRungPos_iff_evenGramNonneg (x : ℕ) :
    EvenRungPos x ↔ EvenGramNonneg x := by
  constructor
  · intro h a
    rw [evenGram_quad_eq_Qx]
    exact h _ (Cvs.Route.EvenWindowBulkCoupling.evenPart_spineMap_mem_R1 x a)
  · intro h r hr
    obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
    rw [← evenGram_quad_eq_Qx]
    exact h a

/-- At `80 ≤ 2πx`, `EvenGramNonneg x` is equivalent to `ReflBound x 1 1`. -/
theorem evenGramNonneg_iff_reflBound_one {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    EvenGramNonneg x ↔ ReflBound x 1 1 :=
  (evenRungPos_iff_evenGramNonneg x).symm.trans (Cvs.Route.EvenWindowBulkCoupling.evenRungPos_iff_reflBound hx)

/-- **Finite-matrix `L²` floor on `evenGram x`**:
`c * ‖evenPart(spineMap x a)‖² ≤ a ⬝ᵥ (evenGram x *ᵥ a)` for every `a : Cvs.Approximant.SpineSubspace.SF x → ℝ`. -/
def EvenGramFloor (x : ℕ) (c : ℝ) : Prop :=
  ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
    c * ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖ ^ 2
      ≤ a ⬝ᵥ (evenGram x *ᵥ a)

/-! ### Finite-matrix cross-term bounds against `evenGram x` -/

/-! ### Prime-form cross-term bound against `evenGram x` -/

/-- **Prime-form cross-term bound against the finite matrix `evenGram x`**:
the squared prime–arch–pole pairing is bounded by `(a ⬝ᵥ (evenGram x *ᵥ a)) * M w_u w_u`. -/
def EvenTameGramCrossBound (x : ℕ) (M : LinearMap.BilinForm ℝ (Dom x)) : Prop :=
  ∀ (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (u : ℝ → ℝ) (hx0 : (0 : ℝ) < x) (hu : Tame u (1 / x) 1),
    Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ Ev x → Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ (R1 x)ᗮ →
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil u (tail x a) n
        - (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale (tail x a)) (Cvs.L2a.TailLogScaleTest.logScale u) t)
        - (poleP (tail x a) * poleM u + poleM (tail x a) * poleP u)) ^ 2
      ≤ (a ⬝ᵥ (evenGram x *ᵥ a)) * M (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)

/-! ### Representer-free spectral cross-term bound against `evenGram x` -/

/-- **Representer-free spectral cross-term bound against `evenGram x`**: for `e_a = evenPart(spineMap x a)`,
`∑_k c_k(e_a)² / g_k ≤ a ⬝ᵥ (evenGram x *ᵥ a)` and
`(B_rem e_a w)² ≤ (a ⬝ᵥ (evenGram x *ᵥ a) − ∑_k c_k(e_a)² / g_k) * A w w` on the even bulk. -/
def SpecGramCrossBound (x : ℕ) {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (A : LinearMap.BilinForm ℝ (Dom x)) (c : Dom x → ι → ℝ) (B_rem : Dom x → Dom x → ℝ) : Prop :=
  ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ,
    ∑ k, c (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) k ^ 2 / g k
      ≤ a ⬝ᵥ (evenGram x *ᵥ a) ∧
    ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
      (B_rem (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) w) ^ 2
        ≤ (a ⬝ᵥ (evenGram x *ᵥ a) -
            ∑ k, c (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) k ^ 2 / g k) *
          A w w

/-- **`SpecCrossBound` is equivalent to `SpecGramCrossBound`.** -/
theorem specCrossBound_iff_specGramCrossBound (x : ℕ) {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (A : LinearMap.BilinForm ℝ (Dom x)) (c : Dom x → ι → ℝ) (B_rem : Dom x → Dom x → ℝ) :
    SpecCrossBound x g A c B_rem ↔ SpecGramCrossBound x g A c B_rem := by
  constructor
  · intro h a
    rw [evenGram_quad_eq_Qx x a]
    exact h _ (Cvs.Route.EvenWindowBulkCoupling.evenPart_spineMap_mem_R1 x a)
  · intro h r hr
    obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
    rw [← evenGram_quad_eq_Qx x a]
    exact h a

/-- **Even window positivity at `x` from `SpecComparison`, `SpecRemRepresentation`, and
`SpecGramCrossBound`.** -/
theorem Q_nonneg_of_specGram_crossBound {x : ℕ} {ι : Type*} [Fintype ι]
    {φ : ι → Dom x} {g : ι → ℝ} {A : LinearMap.BilinForm ℝ (Dom x)}
    {c : Dom x → ι → ℝ} {B_rem : Dom x → Dom x → ℝ}
    (hg : ∀ k, 0 < g k) (hA : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w)
    (hComp : SpecComparison x φ g A) (hRep : SpecRemRepresentation x φ c B_rem)
    (hCB : SpecGramCrossBound x g A c B_rem) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v :=
  Cvs.Route.RepresenterFreeCrossBounds.Q_nonneg_of_spec_crossBound hg hA hComp hRep
    ((specCrossBound_iff_specGramCrossBound x g A c B_rem).2 hCB)

/-- **`RiemannHypothesis` from `SpecComparison`, `SpecRemRepresentation`, and `SpecGramCrossBound`
at infinitely many `x`.** -/
theorem riemannHypothesis_of_specGram_crossBound
    (h : ∃ᶠ x : ℕ in atTop, ∃ (n : ℕ) (φ : Fin n → Dom x) (g : Fin n → ℝ)
      (A : LinearMap.BilinForm ℝ (Dom x)) (c : Dom x → Fin n → ℝ) (B_rem : Dom x → Dom x → ℝ),
      (∀ k, 0 < g k) ∧ (∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w) ∧
      SpecComparison x φ g A ∧ SpecRemRepresentation x φ c B_rem ∧
      SpecGramCrossBound x g A c B_rem) :
    RiemannHypothesis :=
  Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos (h.mono fun _ ⟨_, _, _, _, _, _, hg, hA, hComp, hRep, hCB⟩ =>
    Q_nonneg_of_specGram_crossBound hg hA hComp hRep hCB)

end Cvs.Route.EvenGramRungFloors
