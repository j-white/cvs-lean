import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.EvenFormBelowBulk
import Cvs.Route.EvenSlotPrimeForm
import Cvs.Route.EvenSlotSpectralMinorant
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.ProlateSpineFloorEvenSlots
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.CouplingFiniteSchur
import Cvs.WeilForm.CouplingGramTopEigen
import Cvs.WeilForm.CouplingPrimeForm
import Cvs.WeilForm.CouplingSchurComplement
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
# Representer-Free Cross-Term Bounds and Prolate Norm Ratios

Replaces auxiliary weights and bulk representers in `Cvs.Route.EvenFormBelowBulk`, `Cvs.Route.EvenSlotPrimeForm`, `Cvs.Route.EvenSlotSpectralMinorant`, and `Cvs.Route.ProlateSpineFloorEvenSlots`
with direct quadratic and spectral cross-term bounds against `Q_x(r)` and `b_R(x) ‖r‖²`.
-/

noncomputable section

open Real Filter Finset
open scoped InnerProductSpace

namespace Cvs.Route.RepresenterFreeCrossBounds
open Cvs.ZeroCounting

open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.WeilForm.ThetaSpaceParseval (dil poleP poleM)
open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.L2a.EvenSectorReflectionBound (R1 ReflBound bR)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.CouplingPrimeForm (tail)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.Route.EvenWindowBulkCoupling (EvenRungPos EvenBulkFloor)
open Cvs.Route.EvenFormBelowBulk (EvenOperatorFloor EvenWeightedChannel EvenWeightedRatio)
open Cvs.Route.EvenSlotPrimeForm (EvenTameOperatorFloor EvenTameWeightedChannel EvenTameWeightedRatio)
open Cvs.Route.EvenSlotSpectralMinorant (specForm specForm_self SpecComparison SpecRepresentation SpecRatio)
open Cvs.Route.ProlateSpineFloorEvenSlots (SpecNormRatio evenRungFloor_of_reflBound)

/-! ### Elementary quadratic completion -/

/-- **Quadratic completion**: `0 ≤ A`, `0 ≤ C`, and `B² ≤ A * C` give `0 ≤ A + 2 * B + C`. -/
theorem quad_nonneg_of_sq_le {A B C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : B ^ 2 ≤ A * C) :
    0 ≤ A + 2 * B + C := by
  by_cases hA0 : A = 0
  · have hB0 : B = 0 := by nlinarith [sq_nonneg B]
    linarith
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hmul : 0 ≤ A * (A + 2 * B + C) := by
      calc (0 : ℝ) ≤ (A + B) ^ 2 + (A * C - B ^ 2) :=
            add_nonneg (sq_nonneg (A + B)) (sub_nonneg.mpr hB)
        _ = A * (A + 2 * B + C) := by ring
    exact nonneg_of_mul_nonneg_right hmul hApos

/-! ### Representer-free even cross-term slot on a general subspace `P` -/

/-- **Nonnegativity of the bulk minorant `A` on `Ev x ⊓ Pᗮ`.** -/
def EvenPosDom (x : ℕ) (P : Submodule ℝ (Dom x)) (A : Dom x → Dom x → ℝ) : Prop :=
  ∀ w ∈ Ev x ⊓ Pᗮ, 0 ≤ A w w

/-- **Nonnegativity of `Qx x` on the even rung subspace `Ev x ⊓ P`.** -/
def EvenRungNonneg (x : ℕ) (P : Submodule ℝ (Dom x)) : Prop :=
  ∀ r ∈ Ev x ⊓ P, 0 ≤ Qx x r

/-- **Lower bilinear decomposition of `Qx x (r + w)` along `(Ev x ⊓ P) × (Ev x ⊓ Pᗮ)`.** -/
def EvenChannel (x : ℕ) (P : Submodule ℝ (Dom x)) (C A : Dom x → Dom x → ℝ) : Prop :=
  ∀ r ∈ Ev x ⊓ P, ∀ w ∈ Ev x ⊓ Pᗮ, Qx x r + 2 * C r w + A w w ≤ Qx x (r + w)

/-- **Representer-free cross-term bound**: `(C r w)² ≤ Qx x r * A w w` for `r ∈ Ev x ⊓ P`
and `w ∈ Ev x ⊓ Pᗮ`. -/
def EvenCrossBound (x : ℕ) (P : Submodule ℝ (Dom x)) (C A : Dom x → Dom x → ℝ) : Prop :=
  ∀ r ∈ Ev x ⊓ P, ∀ w ∈ Ev x ⊓ Pᗮ, (C r w) ^ 2 ≤ Qx x r * A w w

/-- **Pointwise sum nonnegativity**: `EvenPosDom`, `EvenRungNonneg`, `EvenCrossBound`, and
`EvenChannel` give `0 ≤ Qx x (r + w)` for `r ∈ Ev x ⊓ P` and `w ∈ Ev x ⊓ Pᗮ`. -/
theorem Q_add_nonneg_of_crossBound {x : ℕ} {P : Submodule ℝ (Dom x)} {C A : Dom x → Dom x → ℝ}
    (hPos : EvenPosDom x P A) (hRung : EvenRungNonneg x P)
    (hCross : EvenCrossBound x P C A) (hChan : EvenChannel x P C A)
    {r w : Dom x} (hr : r ∈ Ev x ⊓ P) (hw : w ∈ Ev x ⊓ Pᗮ) :
    0 ≤ Qx x (r + w) :=
  (quad_nonneg_of_sq_le (hRung r hr) (hPos w hw) (hCross r hr w hw)).trans (hChan r hr w hw)

/-- Orthogonal split in `Ev x` when `P.starProjection` preserves `Ev x`. -/
theorem exists_even_split_of_starProjection {x : ℕ} {P : Submodule ℝ (Dom x)}
    [P.HasOrthogonalProjection] (hP : ∀ v ∈ Ev x, P.starProjection v ∈ Ev x)
    {v : Dom x} (hv : v ∈ Ev x) :
    ∃ r ∈ Ev x ⊓ P, ∃ w ∈ Ev x ⊓ Pᗮ, v = r + w := by
  refine ⟨P.starProjection v, ⟨hP v hv, P.starProjection_apply_mem v⟩,
    v - P.starProjection v,
    ⟨(Ev x).sub_mem hv (hP v hv), P.sub_starProjection_mem_orthogonal v⟩, ?_⟩
  abel

/-- Orthogonal split in `Ev x` along any `P ≤ Ev x` with orthogonal projection. -/
theorem exists_even_split {x : ℕ} {P : Submodule ℝ (Dom x)} [P.HasOrthogonalProjection]
    (hP : P ≤ Ev x) {v : Dom x} (hv : v ∈ Ev x) :
    ∃ r ∈ Ev x ⊓ P, ∃ w ∈ Ev x ⊓ Pᗮ, v = r + w :=
  exists_even_split_of_starProjection (fun u _ => hP (P.starProjection_apply_mem u)) hv

/-- **Even window positivity from `EvenPosDom`, `EvenRungNonneg`, `EvenCrossBound`, and `EvenChannel`**
when `P.starProjection` preserves `Ev x`. -/
theorem Q_nonneg_of_even_crossBound_proj {x : ℕ} {P : Submodule ℝ (Dom x)}
    [P.HasOrthogonalProjection] (hP : ∀ v ∈ Ev x, P.starProjection v ∈ Ev x)
    {C A : Dom x → Dom x → ℝ} (hPos : EvenPosDom x P A) (hRung : EvenRungNonneg x P)
    (hCross : EvenCrossBound x P C A) (hChan : EvenChannel x P C A) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v := by
  intro v hv
  obtain ⟨r, hr, w, hw, rfl⟩ := exists_even_split_of_starProjection hP hv
  exact Q_add_nonneg_of_crossBound hPos hRung hCross hChan hr hw

/-- **Even window positivity from `EvenPosDom`, `EvenRungNonneg`, `EvenCrossBound`, and `EvenChannel`**
for `P ≤ Ev x`. -/
theorem Q_nonneg_of_even_crossBound {x : ℕ} {P : Submodule ℝ (Dom x)}
    [P.HasOrthogonalProjection] (hP : P ≤ Ev x) {C A : Dom x → Dom x → ℝ}
    (hPos : EvenPosDom x P A) (hRung : EvenRungNonneg x P)
    (hCross : EvenCrossBound x P C A) (hChan : EvenChannel x P C A) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v :=
  Q_nonneg_of_even_crossBound_proj (fun u _ => hP (P.starProjection_apply_mem u))
    hPos hRung hCross hChan

/-- Exact bilinear expansion `Qx x (r + w) = Qx x r + 2 * Bx x r w + Qx x w`. -/
theorem Qx_add_eq (x : ℕ) (r w : Dom x) :
    Qx x (r + w) = Qx x r + 2 * Bx x r w + Qx x w := by
  have hB : (Bx x).IsSymm := Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
  have h := Cvs.WeilForm.CouplingSchurComplement.apply_add_self hB r w
  rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self, Cvs.WeilForm.CouplingFiniteSchur.Bx_self, Cvs.WeilForm.CouplingFiniteSchur.Bx_self] at h
  linarith

/-- Any bulk minorant `A w w ≤ Qx x w` on `Ev x ⊓ Pᗮ` satisfies `EvenChannel x P (Bx x) A`. -/
theorem evenChannel_Bx_of_le_Qx {x : ℕ} {P : Submodule ℝ (Dom x)} {A : Dom x → Dom x → ℝ}
    (hA : ∀ w ∈ Ev x ⊓ Pᗮ, A w w ≤ Qx x w) :
    EvenChannel x P (fun r w => Bx x r w) A := by
  intro r _ w hw
  rw [Qx_add_eq]
  linarith [hA w hw]

/-- `Cvs.Route.EvenFormBelowBulk.EvenOperatorFloor x M` gives `EvenPosDom x (R1 x) (fun v w => M v w)` and
`EvenChannel x (R1 x) (fun r w => Bx x r w) (fun v w => M v w)`. -/
theorem evenPosDom_and_channel_of_operatorFloor {x : ℕ} {M : LinearMap.BilinForm ℝ (Dom x)}
    (hF : EvenOperatorFloor x M) :
    EvenPosDom x (R1 x) (fun v w => M v w) ∧
      EvenChannel x (R1 x) (fun r w => Bx x r w) (fun v w => M v w) :=
  ⟨fun w hw => (hF w hw.1 hw.2).1, evenChannel_Bx_of_le_Qx fun w hw => (hF w hw.1 hw.2).2⟩

/-- `EvenRungNonneg x (R1 x)` is equivalent to `Cvs.Route.EvenWindowBulkCoupling.EvenRungPos x`. -/
theorem evenRungNonneg_R1_iff (x : ℕ) :
    EvenRungNonneg x (R1 x) ↔ EvenRungPos x :=
  ⟨fun h r hr => h r ⟨Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hr, hr⟩, fun h r hr => h r hr.2⟩

/-- `Cvs.Route.EvenFormBelowBulk`'s weighted slot implies `EvenCrossBound x (R1 x) (fun r w => Bx x r w) (fun v w => M v w)`. -/
theorem evenCrossBound_of_weighted {x : ℕ} {M : LinearMap.BilinForm ℝ (Dom x)} {κ : Dom x → ℝ}
    (hF : EvenOperatorFloor x M) (hC : EvenWeightedChannel x M κ)
    (hR : EvenWeightedRatio x 0 κ) :
    EvenCrossBound x (R1 x) (fun r w => Bx x r w) (fun v w => M v w) := by
  intro r hr w hw
  have hM0 : 0 ≤ M w w := (hF w hw.1 hw.2).1
  have hκ : κ r ≤ Qx x r := by simpa using hR r hr.2
  exact ((hC r hr.2).2 w hw.1 hw.2).trans (mul_le_mul_of_nonneg_right hκ hM0)

/-- `EvenRungNonneg x (R1 x)` and `EvenCrossBound x (R1 x)` fill `Cvs.Route.EvenFormBelowBulk`'s weighted slot with `κ = Qx x`. -/
theorem evenWeighted_of_evenCrossBound {x : ℕ} {M : LinearMap.BilinForm ℝ (Dom x)}
    (hRung : EvenRungNonneg x (R1 x))
    (hCross : EvenCrossBound x (R1 x) (fun r w => Bx x r w) (fun v w => M v w)) :
    EvenWeightedChannel x M (Qx x) ∧ EvenWeightedRatio x 0 (Qx x) := by
  refine ⟨fun r hr => ⟨hRung r ⟨Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hr, hr⟩, fun w hwe hw => ?_⟩,
    fun r _ => by simp⟩
  exact hCross r ⟨Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hr, hr⟩ w ⟨hwe, hw⟩

/-- **Equivalence between even window positivity and the representer-free `EvenCrossBound` on `R1 x`.** -/
theorem evenWindowPos_iff_even_crossBound (x : ℕ) :
    (∀ v ∈ Ev x, 0 ≤ Qx x v) ↔
      ∃ M : LinearMap.BilinForm ℝ (Dom x),
        EvenOperatorFloor x M ∧ EvenRungNonneg x (R1 x) ∧
        EvenCrossBound x (R1 x) (fun r w => Bx x r w) (fun v w => M v w) := by
  constructor
  · intro h
    obtain ⟨hF, hC, hR⟩ := Cvs.Route.EvenFormBelowBulk.even_weighted_self_of_Q_nonneg h
    exact ⟨Bx x, hF, fun r hr => h r hr.1, evenCrossBound_of_weighted hF hC hR⟩
  · rintro ⟨M, hF, hRung, hCross⟩
    obtain ⟨hPos, hChan⟩ := evenPosDom_and_channel_of_operatorFloor hF
    exact Q_nonneg_of_even_crossBound (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x) hPos hRung hCross hChan

/-! ### Prolate `L²` norm cross-term bound from `Cvs.L2a.EvenSectorReflectionBound.ReflBound` -/

/-- **Prolate `L²` norm cross-term bound on `R₁`**:
`(C r w)² ≤ ((1 − δR)/2 * bR x * ‖r‖²) * A w w` for `r ∈ Ev x ⊓ R1 x` and `w ∈ Ev x ⊓ (R1 x)ᗮ`. -/
def EvenNormCrossBound (x : ℕ) (δR : ℝ) (C A : Dom x → Dom x → ℝ) : Prop :=
  ∀ r ∈ Ev x ⊓ R1 x, ∀ w ∈ Ev x ⊓ (R1 x)ᗮ,
    (C r w) ^ 2 ≤ ((1 - δR) / 2 * bR x * ‖r‖ ^ 2) * A w w

/-- Past `c₀W ≤ 2πx`, `ReflBound x 1 δR` (`δR ≤ 1`) gives `EvenRungNonneg x (R1 x)`. -/
theorem evenRungNonneg_R1_of_reflBound {x : ℕ} (hx : c0W ≤ 2 * π * x) {δR : ℝ} (hδ : δR ≤ 1)
    (hR : ReflBound x 1 δR) : EvenRungNonneg x (R1 x) :=
  (evenRungNonneg_R1_iff x).2 (Cvs.Route.EvenWindowBulkCoupling.evenRungPos_of_reflBound hx hδ hR)

/-- **Past `c₀W ≤ 2πx`, `ReflBound x 1 δR` (`δR ≤ 1`) and `EvenNormCrossBound` give `EvenCrossBound`.** -/
theorem evenCrossBound_of_reflBound_norm {x : ℕ} (hx : c0W ≤ 2 * π * x) {δR : ℝ} (hδ : δR ≤ 1)
    (hR : ReflBound x 1 δR) {C A : Dom x → Dom x → ℝ} (hPos : EvenPosDom x (R1 x) A)
    (hN : EvenNormCrossBound x δR C A) :
    EvenCrossBound x (R1 x) C A := by
  intro r hr w hw
  have hfl := evenRungFloor_of_reflBound hx hδ hR hr.2
  exact (hN r hr w hw).trans (mul_le_mul_of_nonneg_right hfl (hPos w hw))

/-- **Even window positivity at `x` from `ReflBound x 1 δR`, `EvenPosDom`, `EvenChannel`, and
`EvenNormCrossBound`.** -/
theorem Q_nonneg_of_reflBound_even_normCrossBound {x : ℕ} (hx : c0W ≤ 2 * π * x) {δR : ℝ}
    (hδ : δR ≤ 1) (hR : ReflBound x 1 δR) {C A : Dom x → Dom x → ℝ}
    (hPos : EvenPosDom x (R1 x) A) (hChan : EvenChannel x (R1 x) C A)
    (hN : EvenNormCrossBound x δR C A) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v :=
  Q_nonneg_of_even_crossBound (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x) hPos
    (evenRungNonneg_R1_of_reflBound hx hδ hR)
    (evenCrossBound_of_reflBound_norm hx hδ hR hPos hN) hChan

/-- **`RiemannHypothesis` from `ReflBound x 1 δR`, `EvenPosDom`, `EvenChannel`, and
`EvenNormCrossBound` at infinitely many `x`.** -/
theorem riemannHypothesis_of_reflBound_even_normCrossBound
    (h : ∃ᶠ x : ℕ in atTop, ∃ (δR : ℝ) (C A : Dom x → Dom x → ℝ),
      δR ≤ 1 ∧ ReflBound x 1 δR ∧ EvenPosDom x (R1 x) A ∧
      EvenChannel x (R1 x) C A ∧ EvenNormCrossBound x δR C A) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually Cvs.Route.WindowPositivityBulkCoupling.eventually_c0W_le).mono fun x ⟨hx', hx⟩ => ?_)
  obtain ⟨δR, C, A, hδ, hR, hPos, hChan, hN⟩ := hx'
  exact Q_nonneg_of_reflBound_even_normCrossBound hx hδ hR hPos hChan hN

/-- **Even window positivity from `EvenOperatorFloor x M`, `ReflBound x 1 δR`, and
`EvenNormCrossBound` for `Bx x` against `M`.** -/
theorem Q_nonneg_of_operatorFloor_reflBound_normCrossBound {x : ℕ} (hx : c0W ≤ 2 * π * x)
    {δR : ℝ} (hδ : δR ≤ 1) (hR : ReflBound x 1 δR) {M : LinearMap.BilinForm ℝ (Dom x)}
    (hF : EvenOperatorFloor x M)
    (hN : EvenNormCrossBound x δR (fun r w => Bx x r w) (fun v w => M v w)) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v := by
  obtain ⟨hPos, hChan⟩ := evenPosDom_and_channel_of_operatorFloor hF
  exact Q_nonneg_of_reflBound_even_normCrossBound hx hδ hR hPos hChan hN

/-- **`RiemannHypothesis` from `EvenOperatorFloor`, `ReflBound`, and `EvenNormCrossBound` at
infinitely many `x`.** -/
theorem riemannHypothesis_of_operatorFloor_reflBound_normCrossBound
    (h : ∃ᶠ x : ℕ in atTop, ∃ (δR : ℝ) (M : LinearMap.BilinForm ℝ (Dom x)),
      δR ≤ 1 ∧ ReflBound x 1 δR ∧ EvenOperatorFloor x M ∧
      EvenNormCrossBound x δR (fun r w => Bx x r w) (fun v w => M v w)) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually Cvs.Route.WindowPositivityBulkCoupling.eventually_c0W_le).mono fun x ⟨hx', hx⟩ => ?_)
  obtain ⟨δR, M, hδ, hR, hF, hN⟩ := hx'
  exact Q_nonneg_of_operatorFloor_reflBound_normCrossBound hx hδ hR hF hN

/-! ### Representer-free prime-form cross-term bounds (`Cvs.Route.EvenSlotPrimeForm`) -/

/-- **Representer-free prime-form cross-term bound**: the squared prime–arch–pole pairing is bounded
directly by `Qx x e_a * M w_u w_u` without an intermediate weight `κ`. -/
def EvenTameCrossBound (x : ℕ) (M : LinearMap.BilinForm ℝ (Dom x)) : Prop :=
  ∀ (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (u : ℝ → ℝ) (hx0 : (0 : ℝ) < x) (hu : Tame u (1 / x) 1),
    Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ Ev x → Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ (R1 x)ᗮ →
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil u (tail x a) n
        - (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale (tail x a)) (Cvs.L2a.TailLogScaleTest.logScale u) t)
        - (poleP (tail x a) * poleM u + poleM (tail x a) * poleP u)) ^ 2
      ≤ Qx x (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) *
          M (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)

/-- **Representer-free prime-form norm cross-term bound against `bR x * ‖e_a‖²`.** -/
def EvenTameNormCrossBound (x : ℕ) (δR : ℝ) (M : LinearMap.BilinForm ℝ (Dom x)) : Prop :=
  ∀ (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (u : ℝ → ℝ) (hx0 : (0 : ℝ) < x) (hu : Tame u (1 / x) 1),
    Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ Ev x → Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ (R1 x)ᗮ →
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil u (tail x a) n
        - (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale (tail x a)) (Cvs.L2a.TailLogScaleTest.logScale u) t)
        - (poleP (tail x a) * poleM u + poleM (tail x a) * poleP u)) ^ 2
      ≤ ((1 - δR) / 2 * bR x *
          ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖ ^ 2) *
          M (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)

/-- Past `c₀W ≤ 2πx`, `ReflBound x 1 δR` (`δR ≤ 1`) and `EvenTameNormCrossBound` give
`EvenTameCrossBound`. -/
theorem evenTameCrossBound_of_reflBound_norm {x : ℕ} (hx : c0W ≤ 2 * π * x) {δR : ℝ}
    (hδ : δR ≤ 1) (hR : ReflBound x 1 δR) {M : LinearMap.BilinForm ℝ (Dom x)}
    (hF : EvenTameOperatorFloor x M) (hN : EvenTameNormCrossBound x δR M) :
    EvenTameCrossBound x M := by
  intro a u hx0 hu he hw
  have hfl := evenRungFloor_of_reflBound hx hδ hR (Cvs.Route.EvenWindowBulkCoupling.evenPart_spineMap_mem_R1 x a)
  have hM0 : 0 ≤ M (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) := (hF u hx0 hu he hw).1
  exact (hN a u hx0 hu he hw).trans (mul_le_mul_of_nonneg_right hfl hM0)

/-- **Even window positivity at `x` from `EvenTameOperatorFloor`, `EvenRungPos`, and
`EvenTameCrossBound`**, at `80 ≤ 2πx`. -/
theorem Q_nonneg_of_even_tame_crossBound {x : ℕ} (hx : 80 ≤ 2 * π * x)
    {M : LinearMap.BilinForm ℝ (Dom x)} (hF : EvenTameOperatorFloor x M)
    (hRung : EvenRungPos x) (hC : EvenTameCrossBound x M) :
    ∀ φ ∈ Ev x, 0 ≤ Qx x φ := by
  refine Cvs.Route.EvenSlotPrimeForm.Q_nonneg_of_even_tame_weighted hx le_rfl one_pos hF
    (κ := fun a => Qx x (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)))
    (fun a => ⟨hRung _ (Cvs.Route.EvenWindowBulkCoupling.evenPart_spineMap_mem_R1 x a), fun u hx0 hu he hw => hC a u hx0 hu he hw⟩)
    (fun a => by simp)

/-- **Even window positivity at `x` from `ReflBound x 1 δR`, `EvenTameOperatorFloor`, and
`EvenTameNormCrossBound`**, past `c₀W ≤ 2πx`. -/
theorem Q_nonneg_of_even_tame_reflBound_normCrossBound {x : ℕ} (hx : c0W ≤ 2 * π * x)
    {δR : ℝ} (hδ : δR ≤ 1) (hR : ReflBound x 1 δR) {M : LinearMap.BilinForm ℝ (Dom x)}
    (hF : EvenTameOperatorFloor x M) (hN : EvenTameNormCrossBound x δR M) :
    ∀ φ ∈ Ev x, 0 ≤ Qx x φ :=
  Q_nonneg_of_even_tame_crossBound (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx) hF
    (Cvs.Route.EvenWindowBulkCoupling.evenRungPos_of_reflBound hx hδ hR)
    (evenTameCrossBound_of_reflBound_norm hx hδ hR hF hN)

/-- **`RiemannHypothesis` from `ReflBound`, `EvenTameOperatorFloor`, and `EvenTameNormCrossBound`
at infinitely many `x`.** -/
theorem riemannHypothesis_of_even_tame_reflBound_normCrossBound
    (h : ∃ᶠ x : ℕ in atTop, ∃ (δR : ℝ) (M : LinearMap.BilinForm ℝ (Dom x)),
      δR ≤ 1 ∧ ReflBound x 1 δR ∧ EvenTameOperatorFloor x M ∧ EvenTameNormCrossBound x δR M) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually Cvs.Route.WindowPositivityBulkCoupling.eventually_c0W_le).mono fun x ⟨hx', hx⟩ => ?_)
  obtain ⟨δR, M, hδ, hR, hF, hN⟩ := hx'
  exact Q_nonneg_of_even_tame_reflBound_normCrossBound hx hδ hR hF hN

/-! ### Representer-free spectral cross-term bounds (`Cvs.Route.EvenSlotSpectralMinorant`) -/

/-- **Representer-free two-band decomposition of the coupling**:
`Q(r, w) = ∑_k c_k(r) ⟪φ_k, w⟫ + B_rem(r, w)` on `R₁ × (Ev x ∩ R₁ᗮ)`, with no representer `u`. -/
def SpecRemRepresentation (x : ℕ) {ι : Type*} [Fintype ι] (φ : ι → Dom x)
    (c : Dom x → ι → ℝ) (B_rem : Dom x → Dom x → ℝ) : Prop :=
  ∀ r ∈ R1 x, ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) r w =
      ∑ k, c r k * ⟪φ k, w⟫_ℝ + B_rem r w

/-- **Representer-free spectral cross-term bound**: the mode sum `∑_k c_k(r)² / g_k ≤ Q_x(r)`
leaves a residual rung budget bounding `(B_rem r w)² ≤ (Q_x(r) − ∑_k c_k(r)² / g_k) * A(w, w)`
on the even bulk, without requiring any representer `u : Dom x → Dom x`. -/
def SpecCrossBound (x : ℕ) {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (A : LinearMap.BilinForm ℝ (Dom x)) (c : Dom x → ι → ℝ) (B_rem : Dom x → Dom x → ℝ) : Prop :=
  ∀ r ∈ R1 x, ∑ k, c r k ^ 2 / g k ≤ Qx x r ∧
    ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
      (B_rem r w) ^ 2 ≤ (Qx x r - ∑ k, c r k ^ 2 / g k) * A w w

/-- **Representer-free spectral norm cross-term bound against the prolate `L²` floor**:
`∑_k c_k(r)² / g_k ≤ ((1 − δR)/2 * bR x) * ‖r‖²` and
`(B_rem r w)² ≤ (((1 − δR)/2 * bR x) * ‖r‖² − ∑_k c_k(r)² / g_k) * A(w, w)` on the even bulk. -/
def SpecNormCrossBound (x : ℕ) {ι : Type*} [Fintype ι] (δR : ℝ) (g : ι → ℝ)
    (A : LinearMap.BilinForm ℝ (Dom x)) (c : Dom x → ι → ℝ) (B_rem : Dom x → Dom x → ℝ) : Prop :=
  ∀ r ∈ R1 x, ∑ k, c r k ^ 2 / g k ≤ ((1 - δR) / 2 * bR x) * ‖r‖ ^ 2 ∧
    ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
      (B_rem r w) ^ 2 ≤ (((1 - δR) / 2 * bR x) * ‖r‖ ^ 2 - ∑ k, c r k ^ 2 / g k) * A w w

/-- `Cvs.Route.EvenSlotSpectralMinorant.SpecRepresentation` is `SpecRemRepresentation` with `B_rem r w = A (u r) w`. -/
theorem specRemRepresentation_of_specRepresentation {x : ℕ} {ι : Type*} [Fintype ι]
    {φ : ι → Dom x} {A : LinearMap.BilinForm ℝ (Dom x)} {c : Dom x → ι → ℝ} {u : Dom x → Dom x}
    (hRep : SpecRepresentation x φ A c u) :
    SpecRemRepresentation x φ c (fun r w => A (u r) w) :=
  hRep

/-- `Cvs.Route.EvenSlotSpectralMinorant.SpecRatio` with a representer `u` implies the representer-free `SpecCrossBound`
for `B_rem r w = A (u r) w`. -/
theorem specCrossBound_of_specRatio {x : ℕ} {ι : Type*} [Fintype ι] {g : ι → ℝ}
    {A : LinearMap.BilinForm ℝ (Dom x)} {c : Dom x → ι → ℝ} {u : Dom x → Dom x}
    {K : Submodule ℝ (Dom x)} (hAs : A.IsSymm) (hA : ∀ v ∈ K, 0 ≤ A v v)
    (hbulk : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → w ∈ K) (hu : ∀ r ∈ R1 x, u r ∈ K)
    (hRatio : SpecRatio x g A c u) :
    SpecCrossBound x g A c (fun r w => A (u r) w) := by
  intro r hr
  have h1 := hRatio r hr
  have hur : 0 ≤ A (u r) (u r) := hA (u r) (hu r hr)
  refine ⟨by linarith, fun w hwe hw => ?_⟩
  have hcs := Cvs.WeilForm.CouplingGramTopEigen.sq_le_mul_of_nonneg hAs hA (hu r hr) (hbulk w hwe hw)
  have hle : A (u r) (u r) ≤ Qx x r - ∑ k, c r k ^ 2 / g k := by linarith
  exact hcs.trans (mul_le_mul_of_nonneg_right hle (hA w (hbulk w hwe hw)))

/-- `Cvs.Route.ProlateSpineFloorEvenSlots.SpecNormRatio` with a representer `u` implies the representer-free `SpecNormCrossBound`
for `B_rem r w = A (u r) w`. -/
theorem specNormCrossBound_of_specNormRatio {x : ℕ} {ι : Type*} [Fintype ι] {δR : ℝ} {g : ι → ℝ}
    {A : LinearMap.BilinForm ℝ (Dom x)} {c : Dom x → ι → ℝ} {u : Dom x → Dom x}
    {K : Submodule ℝ (Dom x)} (hAs : A.IsSymm) (hA : ∀ v ∈ K, 0 ≤ A v v)
    (hbulk : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → w ∈ K) (hu : ∀ r ∈ R1 x, u r ∈ K)
    (hN : SpecNormRatio x δR g A c u) :
    SpecNormCrossBound x δR g A c (fun r w => A (u r) w) := by
  intro r hr
  have h1 := hN r hr
  have hur : 0 ≤ A (u r) (u r) := hA (u r) (hu r hr)
  refine ⟨by linarith, fun w hwe hw => ?_⟩
  have hcs := Cvs.WeilForm.CouplingGramTopEigen.sq_le_mul_of_nonneg hAs hA (hu r hr) (hbulk w hwe hw)
  have hle : A (u r) (u r) ≤ ((1 - δR) / 2 * bR x) * ‖r‖ ^ 2 - ∑ k, c r k ^ 2 / g k := by linarith
  exact hcs.trans (mul_le_mul_of_nonneg_right hle (hA w (hbulk w hwe hw)))

/-- `SpecCrossBound` with `g > 0` forces `EvenRungNonneg x (R1 x)`. -/
theorem evenRungNonneg_of_specCrossBound {x : ℕ} {ι : Type*} [Fintype ι] {g : ι → ℝ}
    {A : LinearMap.BilinForm ℝ (Dom x)} {c : Dom x → ι → ℝ} {B_rem : Dom x → Dom x → ℝ}
    (hg : ∀ k, 0 < g k) (hCB : SpecCrossBound x g A c B_rem) :
    EvenRungNonneg x (R1 x) := by
  intro r hr
  have hsum : 0 ≤ ∑ k, c r k ^ 2 / g k :=
    sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (hg k).le
  exact hsum.trans (hCB r hr.2).1

/-- **`SpecRemRepresentation` and `SpecCrossBound` give `EvenCrossBound` against `specForm φ g A`.** -/
theorem evenCrossBound_of_specCrossBound {x : ℕ} {ι : Type*} [Fintype ι]
    {φ : ι → Dom x} {g : ι → ℝ} {A : LinearMap.BilinForm ℝ (Dom x)}
    {c : Dom x → ι → ℝ} {B_rem : Dom x → Dom x → ℝ}
    (hg : ∀ k, 0 < g k) (hA : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w)
    (hRep : SpecRemRepresentation x φ c B_rem) (hCB : SpecCrossBound x g A c B_rem) :
    EvenCrossBound x (R1 x) (fun r w => Bx x r w) (fun v w => specForm φ g A v w) := by
  intro r hr w hw
  have h1 := hRep r hr.2 w hw.1 hw.2
  have h2 := hCB r hr.2
  have hs : 0 ≤ Qx x r - ∑ k, c r k ^ 2 / g k := sub_nonneg.mpr h2.1
  have ht : 0 ≤ A w w := hA w hw.1 hw.2
  have hcs := Cvs.Route.EvenSlotSpectralMinorant.sq_add_le (c := c r) (a := fun k => ⟪φ k, w⟫_ℝ) hg hs ht (h2.2 w hw.1 hw.2)
  change (Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) r w) ^ 2 ≤
    Qx x r * specForm φ g A w w
  rw [h1, specForm_self]
  calc (∑ k, c r k * ⟪φ k, w⟫_ℝ + B_rem r w) ^ 2
      ≤ (∑ k, c r k ^ 2 / g k + (Qx x r - ∑ k, c r k ^ 2 / g k)) *
          (∑ k, g k * ⟪φ k, w⟫_ℝ ^ 2 + A w w) := hcs
    _ = Qx x r * (∑ k, g k * ⟪φ k, w⟫_ℝ ^ 2 + A w w) := by rw [add_sub_cancel]

/-- **Representer-free spectral window positivity at `x`**: `g > 0`, `A ≥ 0` on the even bulk,
`SpecComparison`, `SpecRemRepresentation`, and `SpecCrossBound` give `0 ≤ Qx x v` on `Ev x`
with no representer `u`, no ambient subspace `K`, and no symmetry assumption on `A`. -/
theorem Q_nonneg_of_spec_crossBound {x : ℕ} {ι : Type*} [Fintype ι]
    {φ : ι → Dom x} {g : ι → ℝ} {A : LinearMap.BilinForm ℝ (Dom x)}
    {c : Dom x → ι → ℝ} {B_rem : Dom x → Dom x → ℝ}
    (hg : ∀ k, 0 < g k) (hA : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w)
    (hComp : SpecComparison x φ g A) (hRep : SpecRemRepresentation x φ c B_rem)
    (hCB : SpecCrossBound x g A c B_rem) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v := by
  have hF : EvenOperatorFloor x (specForm φ g A) :=
    Cvs.Route.EvenSlotSpectralMinorant.evenOperatorFloor_specForm (fun k => (hg k).le) hA hComp
  obtain ⟨hPos, hChan⟩ := evenPosDom_and_channel_of_operatorFloor hF
  exact Q_nonneg_of_even_crossBound (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x) hPos
    (evenRungNonneg_of_specCrossBound hg hCB)
    (evenCrossBound_of_specCrossBound hg hA hRep hCB) hChan

/-- **Past `c₀W ≤ 2πx`, `ReflBound x 1 δR` (`δR ≤ 1`) and `SpecNormCrossBound` give `SpecCrossBound`.** -/
theorem specCrossBound_of_reflBound_norm {x : ℕ} {ι : Type*} [Fintype ι]
    (hx : c0W ≤ 2 * π * x) {δR : ℝ} (hδ : δR ≤ 1) (hR : ReflBound x 1 δR)
    {g : ι → ℝ} {A : LinearMap.BilinForm ℝ (Dom x)}
    {c : Dom x → ι → ℝ} {B_rem : Dom x → Dom x → ℝ}
    (hA : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w)
    (hN : SpecNormCrossBound x δR g A c B_rem) :
    SpecCrossBound x g A c B_rem := by
  intro r hr
  have hfl := evenRungFloor_of_reflBound hx hδ hR hr
  have h1 := hN r hr
  refine ⟨h1.1.trans hfl, fun w hwe hw => ?_⟩
  have hsub : ((1 - δR) / 2 * bR x) * ‖r‖ ^ 2 - ∑ k, c r k ^ 2 / g k ≤
      Qx x r - ∑ k, c r k ^ 2 / g k := sub_le_sub_right hfl _
  exact (h1.2 w hwe hw).trans (mul_le_mul_of_nonneg_right hsub (hA w hwe hw))

/-- **Representer-free spectral window positivity at `x` from `ReflBound` and `SpecNormCrossBound`.** -/
theorem Q_nonneg_of_spec_reflBound_normCrossBound {x : ℕ} {ι : Type*} [Fintype ι]
    (hx : c0W ≤ 2 * π * x) {δR : ℝ} (hδ : δR ≤ 1) (hR : ReflBound x 1 δR)
    {φ : ι → Dom x} {g : ι → ℝ} {A : LinearMap.BilinForm ℝ (Dom x)}
    {c : Dom x → ι → ℝ} {B_rem : Dom x → Dom x → ℝ}
    (hg : ∀ k, 0 < g k) (hA : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w)
    (hComp : SpecComparison x φ g A) (hRep : SpecRemRepresentation x φ c B_rem)
    (hN : SpecNormCrossBound x δR g A c B_rem) :
    ∀ v ∈ Ev x, 0 ≤ Qx x v :=
  Q_nonneg_of_spec_crossBound hg hA hComp hRep (specCrossBound_of_reflBound_norm hx hδ hR hA hN)

/-- **`RiemannHypothesis` from representer-free spectral data and `SpecNormCrossBound` at
infinitely many `x`.** -/
theorem riemannHypothesis_of_spec_reflBound_normCrossBound
    (h : ∃ᶠ x : ℕ in atTop, ∃ (n : ℕ) (δR : ℝ) (φ : Fin n → Dom x) (g : Fin n → ℝ)
      (A : LinearMap.BilinForm ℝ (Dom x)) (c : Dom x → Fin n → ℝ) (B_rem : Dom x → Dom x → ℝ),
      δR ≤ 1 ∧ ReflBound x 1 δR ∧ (∀ k, 0 < g k) ∧
      (∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w) ∧
      SpecComparison x φ g A ∧ SpecRemRepresentation x φ c B_rem ∧
      SpecNormCrossBound x δR g A c B_rem) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually Cvs.Route.WindowPositivityBulkCoupling.eventually_c0W_le).mono fun x ⟨hx', hx⟩ => ?_)
  obtain ⟨n, δR, φ, g, A, c, B_rem, hδ, hR, hg, hA, hComp, hRep, hN⟩ := hx'
  exact Q_nonneg_of_spec_reflBound_normCrossBound hx hδ hR hg hA hComp hRep hN

/-- **Equivalence between even window positivity at `x` and representer-free spectral data.** -/
theorem evenWindowPos_iff_spec_crossBound (x : ℕ) :
    (∀ v ∈ Ev x, 0 ≤ Qx x v) ↔
      ∃ (n : ℕ) (φ : Fin n → Dom x) (g : Fin n → ℝ)
        (A : LinearMap.BilinForm ℝ (Dom x)) (c : Dom x → Fin n → ℝ) (B_rem : Dom x → Dom x → ℝ),
        (∀ k, 0 < g k) ∧ (∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w) ∧
        SpecComparison x φ g A ∧ SpecRemRepresentation x φ c B_rem ∧
        SpecCrossBound x g A c B_rem := by
  constructor
  · intro h
    have hB : ∀ v ∈ Ev x, 0 ≤ Bx x v v := fun v hv => by rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]; exact h v hv
    refine ⟨0, Fin.elim0, Fin.elim0, Bx x, fun _ => Fin.elim0, fun r w => Bx x r w,
      fun k => Fin.elim0 k, fun w hwe _ => hB w hwe,
      fun w _ _ => by rw [specForm_self]; simp [Cvs.WeilForm.CouplingFiniteSchur.Bx_self],
      fun r _ w _ _ => by simp; rfl,
      fun r hr => ⟨by simp [ h r (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hr)], fun w hwe _ => ?_⟩⟩
    simp only [Fintype.sum_empty, sub_zero]
    have hcs := Cvs.WeilForm.CouplingGramTopEigen.sq_le_mul_of_nonneg (B := Bx x) (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _) hB
      (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hr) hwe
    rwa [Cvs.WeilForm.CouplingFiniteSchur.Bx_self] at hcs
  · rintro ⟨n, φ, g, A, c, B_rem, hg, hA, hComp, hRep, hCB⟩
    exact Q_nonneg_of_spec_crossBound hg hA hComp hRep hCB

/-- **`RiemannHypothesis` is equivalent to representer-free spectral data at infinitely many `x`.** -/
theorem rh_iff_frequently_spec_crossBound :
    RiemannHypothesis ↔
      ∃ᶠ x : ℕ in atTop, ∃ (n : ℕ) (φ : Fin n → Dom x) (g : Fin n → ℝ)
        (A : LinearMap.BilinForm ℝ (Dom x)) (c : Dom x → Fin n → ℝ) (B_rem : Dom x → Dom x → ℝ),
        (∀ k, 0 < g k) ∧ (∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w) ∧
        SpecComparison x φ g A ∧ SpecRemRepresentation x φ c B_rem ∧
        SpecCrossBound x g A c B_rem := by
  rw [Cvs.WeilForm.ReflectionEvenPositivityRH.rh_iff_frequently_evenWindowPos]
  exact frequently_congr (Eventually.of_forall evenWindowPos_iff_spec_crossBound)

end Cvs.Route.RepresenterFreeCrossBounds
