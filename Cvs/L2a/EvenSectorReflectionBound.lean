import Mathlib
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCoefficientMatrix
import Cvs.Approximant.SpineFloorFormDomain
import Cvs.Approximant.SpineFormOwnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullSpanReciprocalContraction
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.ReflectedSpineTame
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowFormTailLimit
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.BulkSchurIdentity
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhysicalReciprocalReflection

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Even-sector L2a on `D₀` and `R₁` from the tail reflection bound

`R₁` is the span of the even rungs `j ≥ 1`; its vectors and `D₀`'s are even parts of spine classes. The tail
reflection bound `−δ·Q(v_a) ≤ Q(v_a, Rv_a)`, both sides in `ReflectedSpineTame`'s tail form, with `FullSpanReciprocalContraction`'s budget-one floors gives
`((1−δ)/2)·b‖e‖² ≤ Q(e)` on even parts: `κ_E(1 − λ₈)` on `D₀` and `κ_E(1 − λ₄)` on `R₁`, `κ_E = (1−δ)/2·π/(8c(1 +
2c/(πλ₀)))`. The bound at level `2` is `D0FloorEvenRungShare`'s even share `(1−δ)/2`; the even Gram matrix is the tail-form `T`.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped InnerProductSpace
open Matrix

namespace Cvs.L2a.EvenSectorReflectionBound
open Cvs.ZeroCounting

open Cvs.WeilForm.ThetaSpaceParseval (weilθ)
open Cvs.L2a.WindowFormTailLimit (regProfile)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Xi.PhysicalReciprocalReflection (reciprocal)
open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx rung D0 D0idx)

/-! ### `R₁` and even parts of spine classes -/

/-- `R₁`: the span of the even rungs `1 ≤ j < x`. -/
def R1 (x : ℕ) : Submodule ℝ (Dom x) :=
  Submodule.span ℝ (Set.range (rung x))

instance R1.finiteDimensional (x : ℕ) : FiniteDimensional ℝ (R1 x) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- `D₀ ≤ R₁`. -/
theorem D0_le_R1 (x : ℕ) : D0 x ≤ R1 x :=
  Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.1, rfl⟩)

/-- **Every `r ∈ R₁` is the even part of a spine class.** -/
theorem exists_of_mem_R1 (x : ℕ) {r : Dom x} (hr : r ∈ R1 x) :
    ∃ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, r = Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hr
  refine ⟨c, ?_⟩
  show _ = Cvs.Approximant.D0FloorEvenRungShare.evenPartL (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x c)
  conv_rhs => rw [← Cvs.Approximant.SpineCoefficientMatrix.sum_single x c]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, Cvs.Approximant.D0FloorEvenRungShare.rung_eq]

/-- A coefficient vector vanishing below `1` is any coefficient vector. -/
theorem vanish_one (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ∀ j : Cvs.Approximant.SpineSubspace.SF x, (j : ℕ) < 1 → a j = 0 := by
  intro j hj
  have := (Finset.mem_filter.1 j.2).2
  omega

/-! ### The tail-form spine and reflection pairings -/

/-- The spine pairing in tail form, `−weilθ(τ_a, W_a)`. -/
def tailQ (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ :=
  -weilθ (fullTail (psi (2 * π * x) (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))))
    (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))

/-- The reflection pairing in tail form, `−weilθ(τ_a, R_{1/x}W_a)`. -/
def reflQ (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ :=
  -weilθ (fullTail (psi (2 * π * x) (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))))
    (reciprocal (1 / x) (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)))

/-- `Q(v_a) = tailQ x a` at `80 ≤ 2πx`. -/
theorem Q_spineMap_eq_tailQ {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a) = tailQ x a :=
  Cvs.Approximant.SpineFormOwnTailPairing.Q_spineMap_eq_neg_tail hx a

/-- `Q(e_a) = (tailQ x a + reflQ x a)/2` at `80 ≤ 2πx`. -/
theorem Q_evenPart_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a))
      = (tailQ x a + reflQ x a) / 2 := by
  rw [Cvs.L2a.ReflectedSpineTame.Q_evenPart_spineMap hx, tailQ, reflQ]
  ring

/-- **The tail reflection bound at level `k` with defect `δ`**: `−δ·tailQ x a ≤ reflQ x a` for every
coefficient vector vanishing on `j < k`. -/
def ReflBound (x k : ℕ) (δ : ℝ) : Prop :=
  ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, (∀ j : Cvs.Approximant.SpineSubspace.SF x, (j : ℕ) < k → a j = 0) → -δ * tailQ x a ≤ reflQ x a

/-! ### The even floor from a full floor and the reflection bound -/

/-- **The even floor**: a floor `b‖v_a‖² ≤ Q(v_a)` and the reflection bound at level `k`, `δ ≤ 1`, give
`((1−δ)/2)·b‖e_a‖² ≤ Q(e_a)` for every `a` vanishing on `j < k`, `e_a` the even part of `v_a`. -/
theorem even_floor_of_reflBound {x k : ℕ} (hx : 80 ≤ 2 * π * x) {b δ : ℝ} (hb : 0 ≤ b) (hδ : δ ≤ 1)
    (hfloor : ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, (∀ j : Cvs.Approximant.SpineSubspace.SF x, (j : ℕ) < k → a j = 0) →
      b * ‖Cvs.Approximant.SpineSubspace.spineMap x a‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a))
    (hR : ReflBound x k δ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (ha : ∀ j : Cvs.Approximant.SpineSubspace.SF x, (j : ℕ) < k → a j = 0) :
    (1 - δ) / 2 * b * ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖ ^ 2
      ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
          (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) := by
  have hv := hfloor a ha
  have hr := hR a ha
  rw [Q_spineMap_eq_tailQ hx] at hv
  rw [Q_evenPart_eq hx]
  have hn := Cvs.WeilForm.EvenOddSplitForm.norm_sq_split (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)
  have ho := sq_nonneg ‖Cvs.WeilForm.EvenOddSplitForm.oddPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖
  have hd : 0 ≤ (1 - δ) / 2 := by linarith
  have h1 : b * ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖ ^ 2 ≤ tailQ x a :=
    (mul_le_mul_of_nonneg_left (by rw [hn]; linarith) hb).trans hv
  have h2 := mul_le_mul_of_nonneg_left h1 hd
  nlinarith

/-! ### The budget-one floors on `D₀` and `R₁` -/

/-- `FullSpanReciprocalContraction`'s `R_D` floor constant at `c = 2πx`: `π(1 − λ₄)/(8c(1 + 2c/(πλ₀)))`. -/
def bR (x : ℕ) : ℝ :=
  π / (8 * (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0))) * (1 - lamR (2 * π * x) 2)

/-- `b_R(x) > 0` past `c₀W`. -/
theorem bR_pos (x : ℕ) (hx : c0W ≤ 2 * π * x) : 0 < bR x :=
  (Cvs.L2a.FullSpanReciprocalContraction.full_factors_pos x hx).2

/-- **The `R₁` spine floor**: `b_R(x)‖spineMap x a‖² ≤ Q(spineMap x a)` for every coefficient vector. -/
theorem spine_floor_R1 (x : ℕ) (hx : c0W ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    bR x * ‖Cvs.Approximant.SpineSubspace.spineMap x a‖ ^ 2
      ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a) := by
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  rw [Cvs.Approximant.SpineFloorFormDomain.norm_spineMap_sq x h80, Cvs.Approximant.SpineSubspace.Q_spineMap x h80]
  exact Cvs.L2a.FullSpanReciprocalContraction.L2a_window_full_RD x hx a

/-- The even-sector constant `κ_E(x, δ) = ((1−δ)/2)·π/(8c(1 + 2c/(πλ₀)))`, `c = 2πx`. -/
def kappaE (x : ℕ) (δ : ℝ) : ℝ :=
  (1 - δ) / 2 * (π / (8 * (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0))))

/-! ### Even-sector L2a -/

/-- **Even-sector L2a on `R₁`**: past `c₀W`, the reflection bound at level `1` with `δ ≤ 1` gives
`κ_E(x, δ)(1 − λ₄)‖r‖² ≤ Q(r)` on `R₁`. -/
theorem L2a_even_R1 (x : ℕ) (hx : c0W ≤ 2 * π * x) {δ : ℝ} (hδ : δ ≤ 1) (hR : ReflBound x 1 δ) :
    ∀ r ∈ R1 x, kappaE x δ * (1 - lamR (2 * π * x) 2) * ‖r‖ ^ 2
      ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) r := by
  intro r hr
  obtain ⟨a, rfl⟩ := exists_of_mem_R1 x hr
  have h := even_floor_of_reflBound (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx) (bR_pos x hx).le hδ
    (fun a _ => spine_floor_R1 x hx a) hR a (vanish_one x a)
  have e : kappaE x δ * (1 - lamR (2 * π * x) 2) = (1 - δ) / 2 * bR x := by
    unfold kappaE bR; ring
  rw [e]; exact h

/-! ### The even Gram matrix -/

/-- The even spine form `(a, b) ↦ Q(e_a, e_b)` on the coefficients. -/
def evenForm (x : ℕ) : LinearMap.BilinForm ℝ (Cvs.Approximant.SpineSubspace.SF x → ℝ) :=
  (Bx x).compl₁₂ ((Cvs.Approximant.D0FloorEvenRungShare.evenPartL (Real.log_natCast_nonneg x)).comp (Cvs.Approximant.SpineSubspace.spineMap x))
    ((Cvs.Approximant.D0FloorEvenRungShare.evenPartL (Real.log_natCast_nonneg x)).comp (Cvs.Approximant.SpineSubspace.spineMap x))

/-- The even rung matrix `T_ij = Q(rung i, rung j)`. -/
def evenGram (x : ℕ) : Matrix (Cvs.Approximant.SpineSubspace.SF x) (Cvs.Approximant.SpineSubspace.SF x) ℝ :=
  Cvs.WeilForm.BulkSchurIdentity.gram (evenForm x) fun j => Pi.single j 1

/-- `T_ij` is the form on the even rungs. -/
theorem evenGram_apply (x : ℕ) (i j : Cvs.Approximant.SpineSubspace.SF x) : evenGram x i j = Bx x (rung x i) (rung x j) := rfl

/-- **`aᵀTa = Q(e_a)`**: the even rung matrix is the window form on even parts of spine classes. -/
theorem quad_evenGram (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    a ⬝ᵥ (evenGram x *ᵥ a)
      = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
          (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) := by
  have hq : evenForm x a a = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) :=
    Cvs.WeilForm.SymmetricBilinearForm.QWbil_self _ _ _ _
  rw [← hq]
  conv_rhs => rw [← Cvs.Approximant.SpineCoefficientMatrix.sum_single x a]
  rw [Cvs.WeilForm.BulkSchurIdentity.apply_sum_left, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Cvs.WeilForm.BulkSchurIdentity.apply_sum_right, mulVec, dotProduct]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [evenGram, Cvs.WeilForm.BulkSchurIdentity.gram, of_apply]; ring

end Cvs.L2a.EvenSectorReflectionBound
