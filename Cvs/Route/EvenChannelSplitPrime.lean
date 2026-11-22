import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.StepAFromTwoGaps
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.CouplingPrimeForm
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even channel split: the coupling of `R₁` with an even tame class in prime form

For a reflection-even `w`, `Q(o, w) = 0` for every odd part `o`, so `Q(e(v), w) = Q(v, w)`. For `u` tame on
`[1/x, 1]`, `w_u` is even iff `R_{1/x}u = u` a.e., and at `80 ≤ 2πx` then `Q(e_a, w_u) = Σ_n Λ(n)⟨u, τ_a(n·)⟩ −
arch(τ_a, u) − pole(τ_a, u)`, `τ_a` the tail of `spineMap x a` itself, `e_a` its even part: `EvenWindowBulkCoupling`'s coupling on the
even tame classes, `EvenTameCoupling x δ`, is that prime–arch–pole inequality.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped InnerProductSpace

namespace Cvs.Route.EvenChannelSplitPrime
open Cvs.ZeroCounting

open Cvs.WeilForm.ThetaSpaceParseval (dil poleP poleM)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.Xi.PhysicalReciprocalReflection (reciprocal)
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.WeilForm.CouplingPrimeForm (tail)

/-! ### Parity of the form -/

/-- **An odd part is form-orthogonal to every even class**: `Q(o(v), w) = 0` for `w` reflection-even. -/
theorem QWbil_oddPart_eq_zero {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (v : Cvs.WeilForm.FormDomain.formDomain hL)
    {w : Cvs.WeilForm.FormDomain.formDomain hL} (hw : w ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R (Cvs.WeilForm.EvenOddSplitForm.oddPart hL v) w = 0 := by
  have h := Cvs.Approximant.CosineColumnTailPairing.QWbil_reflD hL P R (Cvs.WeilForm.EvenOddSplitForm.oddPart hL v) w
  have hw' : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL w = w := hw
  rw [Cvs.WeilForm.EvenOddSplitForm.reflD_oddPart, hw'] at h
  have e : Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R (-Cvs.WeilForm.EvenOddSplitForm.oddPart hL v) w
      = -Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R (Cvs.WeilForm.EvenOddSplitForm.oddPart hL v) w :=
    LinearMap.map_neg₂ (Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R) (Cvs.WeilForm.EvenOddSplitForm.oddPart hL v) w
  linarith

/-- **Against an even class only the even part couples**: `Q(e(v), w) = Q(v, w)` for `w` reflection-even. -/
theorem QWbil_evenPart_left {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (v : Cvs.WeilForm.FormDomain.formDomain hL)
    {w : Cvs.WeilForm.FormDomain.formDomain hL} (hw : w ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R (Cvs.WeilForm.EvenOddSplitForm.evenPart hL v) w = Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R v w := by
  conv_rhs => rw [← Cvs.WeilForm.EvenOddSplitForm.evenPart_add_oddPart hL v]
  rw [map_add, LinearMap.add_apply, QWbil_oddPart_eq_zero hL P R v hw, add_zero]

/-- An even class is its own even part. -/
theorem evenPart_eq_self {L : ℝ} (hL : 0 ≤ L) {w : Cvs.WeilForm.FormDomain.formDomain hL} (hw : w ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL) :
    Cvs.WeilForm.EvenOddSplitForm.evenPart hL w = w := by
  have hw' : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL w = w := hw
  unfold Cvs.WeilForm.EvenOddSplitForm.evenPart
  rw [hw', ← two_smul ℝ w, smul_smul]
  norm_num

/-! ### The even tame classes -/

/-! ### The even channel split -/

/-- **The even coupling with an even tame class in prime form**: at `80 ≤ 2πx`, for `u` tame on `[1/x, 1]` with
`w_u` even, `Q(e_a, w_u) = Σ_n Λ(n)⟨u, τ_a(n·)⟩ − arch(τ_a, u) − pole(τ_a, u)`, `τ_a` the tail of `spineMap x a`. -/
theorem QWbil_evenPart_spineMap_wv_eq_channels {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ)
    {u : ℝ → ℝ} (hu : Tame u (1 / x) 1) (he : Cvs.Approximant.SpineCouplingTailPairing.wv (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hu ∈ Ev x) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) (Cvs.Approximant.SpineCouplingTailPairing.wv (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hu)
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil u (tail x a) n
        - (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale (tail x a)) (Cvs.L2a.TailLogScaleTest.logScale u) t)
        - (poleP (tail x a) * poleM u + poleM (tail x a) * poleP u) :=
  (QWbil_evenPart_left _ _ _ _ he).trans (Cvs.WeilForm.CouplingPrimeForm.QWbil_spineMap_wv_eq_channels hx a hu)

/-- **The even tame coupling at `x`**: `Q(e_a, w_u)² ≤ (1−δ)Q(e_a)Q(w_u)` for every `a` and every `u` tame on
`[1/x, 1]` with `w_u` even and `L²`-orthogonal to `R₁`. -/
def EvenTameCoupling (x : ℕ) (δ : ℝ) : Prop :=
  ∀ (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (u : ℝ → ℝ) (hx0 : (0 : ℝ) < x) (hu : Tame u (1 / x) 1),
    Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ Ev x → Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ (R1 x)ᗮ →
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) ^ 2
      ≤ (1 - δ) * Qx x (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a))
          * Qx x (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)

end Cvs.Route.EvenChannelSplitPrime
