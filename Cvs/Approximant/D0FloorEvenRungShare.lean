import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SimpleGroundEvenOrOdd
import Cvs.WeilForm.SymmetricBilinearForm
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
# `L1FloorFromBulkD0`'s `D₀` floor from the spine floor and the even share of the rungs

Every `r ∈ D₀` is the even part `e` of a spine class `v = spineMap x a`, `a` vanishing on `j < 2`, and
`Q(e) = (Q(v) + Q(v, Rv))/2` with `R` the window reflection. The even share `κQ(v) ≤ Q(e)` with `SpineFloorFormDomain`'s
`b_D‖v‖² ≤ Q(v)` gives `κ b_D‖r‖² ≤ Q(r)` on `D₀`, and RH from F3 without a separate `D₀` floor.
-/

noncomputable section

open Real Filter
open scoped InnerProductSpace

namespace Cvs.Approximant.D0FloorEvenRungShare

open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx rung D0 D0idx)

/-! ### The even part as a linear map, and its form -/

/-- The even part, `φ ↦ (φ + reflD φ)/2`, as a linear map of the form domain. -/
def evenPartL {L : ℝ} (hL : 0 ≤ L) : Cvs.WeilForm.FormDomain.formDomain hL →ₗ[ℝ] Cvs.WeilForm.FormDomain.formDomain hL where
  toFun := Cvs.WeilForm.EvenOddSplitForm.evenPart hL
  map_add' φ ψ := by
    unfold Cvs.WeilForm.EvenOddSplitForm.evenPart
    rw [Cvs.WeilForm.EvenOddSplitForm.reflD_add, ← smul_add]
    congr 1; abel
  map_smul' t φ := by
    unfold Cvs.WeilForm.EvenOddSplitForm.evenPart
    rw [Cvs.WeilForm.SimpleGroundEvenOrOdd.reflD_smul, RingHom.id_apply, ← smul_add, smul_comm]

/-- **The form on an even part**: `Q(e) = (Q(φ) + Q(φ, Rφ))/2`. -/
theorem Q_evenPart {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (Cvs.WeilForm.EvenOddSplitForm.evenPart hL φ)
      = (Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ + Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R φ (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ)) / 2 := by
  set B := Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R with hB
  set ψ := Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ with hψ
  have hR : B ψ ψ = B φ φ := by
    rw [hB, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]; exact Cvs.WeilForm.WindowReflectionSymmetry.weilQW_reflD hL P R φ
  have hs : B ψ φ = B φ ψ := (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm hL P R).eq ψ φ
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, ← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self hL P R φ, ← hB]
  show B ((1 / 2 : ℝ) • (φ + ψ)) ((1 / 2 : ℝ) • (φ + ψ)) = _
  simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  rw [hR, hs]
  ring

/-! ### `D₀` as even parts of spine classes -/

/-- The even rung is the even part of the spine class of `single j`. -/
theorem rung_eq (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) :
    rung x j = evenPartL (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x (Pi.single j 1)) := rfl

/-! ### The even share and the `D₀` floor -/

end Cvs.Approximant.D0FloorEvenRungShare
