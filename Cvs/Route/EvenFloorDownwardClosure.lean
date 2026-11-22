import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.NestedWindowsMonotoneBottom
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.VonMangoldtMultiplier
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowCircleIsometry
import Cvs.WeilForm.WindowReflectionSymmetry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Downward closure of the reflection-even floor in the scale

The centred embedding of `Cvs.WeilForm.NestedWindowsMonotoneBottom` carries `Ev x` into `Ev X` for `x ≤ X`, keeping the norm and the window form.
A floor `μ‖w‖² ≤ Q_X(w)` on `Ev X` therefore holds on `Ev x` for every `1 ≤ x ≤ X`; at a fixed `μ` the
reflection-even floor holds frequently, along an infinite set, or at every `x ≥ 1`, all equivalently.
-/

noncomputable section

open Real Filter Set

namespace Cvs.Route.EvenFloorDownwardClosure
open Cvs.ZeroCounting

open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)

/-- The reflection-even floor at `x`: `μ‖w‖² ≤ Q_x(w)` for every `w ∈ Ev x`. -/
def EvenFloor (x : ℕ) (μ : ℝ) : Prop := ∀ w ∈ Ev x, μ * ‖w‖ ^ 2 ≤ Qx x w

/-- The centred embedding of a scale `x ≤ X` into scale `X`. -/
abbrev embedNat {x X : ℕ} (hxX : x ≤ X) (φ : Dom x) : Dom X :=
  Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD (Real.log_natCast_nonneg x) (Real.log_natCast_nonneg X) (Cvs.WeilForm.VonMangoldtMultiplier.log_natCast_le hxX) φ

/-- The centred embedding maps `Ev x` into `Ev X`. -/
theorem embedNat_mem_Ev {x X : ℕ} (hxX : x ≤ X) {φ : Dom x} (hφ : φ ∈ Ev x) : embedNat hxX φ ∈ Ev X := by
  show Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg X) (embedNat hxX φ) = embedNat hxX φ
  rw [embedNat, Cvs.WeilForm.NestedWindowsMonotoneBottom.reflD_embedD]
  exact congrArg _ hφ

/-- The centred embedding keeps the norm. -/
theorem norm_embedNat {x X : ℕ} (hxX : x ≤ X) (φ : Dom x) : ‖embedNat hxX φ‖ = ‖φ‖ :=
  Cvs.WeilForm.NestedWindowsMonotoneBottom.norm_embed (Real.log_natCast_nonneg x) (Cvs.WeilForm.VonMangoldtMultiplier.log_natCast_le hxX) φ

/-- The centred embedding keeps the window form: `Q_X(embed φ) = Q_x(φ)` for `1 ≤ x ≤ X`. -/
theorem Qx_embedNat {x X : ℕ} (hx : 1 ≤ x) (hxX : x ≤ X) (φ : Dom x) :
    Qx X (embedNat hxX φ) = Qx x φ := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  exact Cvs.WeilForm.WindowCircleIsometry.Q_embedD_eq (Real.log_natCast_nonneg x) (Real.log_natCast_nonneg X)
    (Cvs.WeilForm.VonMangoldtMultiplier.log_natCast_le hxX) hxX (Nat.clog_mono_right 2 hxX)
    (Real.exp_log hx0).le (Cvs.WeilForm.VonMangoldtMultiplier.log_le_clog_mul_log_two x) φ

/-- **Downward closure**: a reflection-even floor at `X` holds at every `1 ≤ x ≤ X`. -/
theorem evenFloor_of_le {x X : ℕ} (hx : 1 ≤ x) (hxX : x ≤ X) {μ : ℝ} (h : EvenFloor X μ) :
    EvenFloor x μ := by
  intro φ hφ
  have h1 := h _ (embedNat_mem_Ev hxX hφ)
  rwa [norm_embedNat, Qx_embedNat hx hxX] at h1

/-- The reflection-even floor is antitone in the floor parameter. -/
theorem evenFloor_mono {x : ℕ} {μ₁ μ₂ : ℝ} (hμ : μ₁ ≤ μ₂) (h : EvenFloor x μ₂) : EvenFloor x μ₁ :=
  fun w hw => (mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖w‖)).trans (h w hw)

/-- **At a fixed `μ`, frequently is everywhere**: `EvenFloor x μ` at infinitely many `x` iff at every `x ≥ 1`. -/
theorem frequently_evenFloor_iff (μ : ℝ) :
    (∃ᶠ X : ℕ in atTop, EvenFloor X μ) ↔ ∀ x : ℕ, 1 ≤ x → EvenFloor x μ := by
  constructor
  · intro h x hx
    obtain ⟨X, hX, hxX⟩ := (h.and_eventually (eventually_ge_atTop x)).exists
    exact evenFloor_of_le hx hxX hX
  · intro h
    exact ((eventually_ge_atTop 1).mono fun x hx => h x hx).frequently

/-- **Along any infinite set, at a fixed `μ`**: the even floor at every large `X ∈ S` gives it at every `x ≥ 1`. -/
theorem evenFloor_of_eventually_mem {S : Set ℕ} (hS : S.Infinite) {μ : ℝ}
    (h : ∀ᶠ X : ℕ in atTop, X ∈ S → EvenFloor X μ) (x : ℕ) (hx : 1 ≤ x) : EvenFloor x μ :=
  (frequently_evenFloor_iff μ).mp
    (((Nat.frequently_atTop_iff_infinite.mpr hS).and_eventually h).mono fun _ h' => h'.2 h'.1) x hx

/-- The reflection-even floor restricts to the even bulk floor on `Ev x ∩ (R₁ x)ᗮ`. -/
theorem evenBulkFloor_of_evenFloor {x : ℕ} {μ : ℝ} (h : EvenFloor x μ) : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x μ :=
  fun w hwE _ => h w hwE

end Cvs.Route.EvenFloorDownwardClosure
