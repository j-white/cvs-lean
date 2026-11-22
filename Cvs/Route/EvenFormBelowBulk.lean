import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.Upstream.MergedBoundSchurForm
import Cvs.WeilForm.CouplingCauchySchwarzBulk
import Cvs.WeilForm.CouplingFiniteSchur
import Cvs.WeilForm.CouplingGramTopEigen
import Cvs.WeilForm.FormDomain
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
# Even window positivity from a form below `Q` on the even bulk

With `0 ≤ M(w,w) ≤ Q(w)` on the even bulk `Ev x ∩ R₁ᗮ`, `Q(r,w)² ≤ κ(r)·M(w,w)` there and `0 ≤ κ(r) ≤ (1−δ)Q(r)`
on `R₁`, `0 ≤ δ < 1`, Cvs.Route.EvenWindowBulkCoupling gives `Q ≥ 0` on `Ev x`; the margin reduces to `δ = 0`, and `Q ≥ 0` on `Ev x` gives the
three at `M = κ = Q`: even window positivity at `x` is the existence of `(M, κ)` with `κ ≤ Q` on `R₁`, RH is their
existence at infinitely many `x`. At `M = b⟪·,·⟫` the floor is `EvenBulkFloor x b`.
-/

noncomputable section

open Real Filter
open scoped InnerProductSpace

namespace Cvs.Route.EvenFormBelowBulk
open Cvs.ZeroCounting

open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)

/-! ### The slot -/

/-- **The even operator floor at `x`**: `0 ≤ M(w,w) ≤ Q(w)` for every even class `w` `L²`-orthogonal to
`R₁`. -/
def EvenOperatorFloor (x : ℕ) (M : LinearMap.BilinForm ℝ (Dom x)) : Prop :=
  ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ M w w ∧ M w w ≤ Qx x w

/-- **The even weighted channel at `x`**: `κ(r) ≥ 0` and `Q(r,w)² ≤ κ(r)·M(w,w)` for `r ∈ R₁` and every even
class `w` `L²`-orthogonal to `R₁`. -/
def EvenWeightedChannel (x : ℕ) (M : LinearMap.BilinForm ℝ (Dom x)) (κ : Dom x → ℝ) : Prop :=
  ∀ r ∈ R1 x, 0 ≤ κ r ∧ ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) r w ^ 2 ≤ κ r * M w w

/-- **The even weighted ratio at `x`**: `κ(r) ≤ (1−δ)·Q(r)` for every `r ∈ R₁`. -/
def EvenWeightedRatio (x : ℕ) (δ : ℝ) (κ : Dom x → ℝ) : Prop :=
  ∀ r ∈ R1 x, κ r ≤ (1 - δ) * Qx x r

/-! ### The floor -/

/-- **The even operator floor gives the zero even bulk floor.** -/
theorem evenBulkFloor_zero_of_operatorFloor {x : ℕ} {M : LinearMap.BilinForm ℝ (Dom x)}
    (hF : EvenOperatorFloor x M) : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := fun w hwe hw => by
  rw [zero_mul]; exact (hF w hwe hw).1.trans (hF w hwe hw).2

/-- **The even operator floor of `b⟪·,·⟫` is the even bulk floor `b`**, for `b ≥ 0`. -/
theorem evenOperatorFloor_smul_innerₗ_iff (x : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    EvenOperatorFloor x (b • innerₗ (Dom x)) ↔ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b := by
  rw [Cvs.Route.EvenWindowBulkCoupling.evenBulkFloor_iff, Cvs.WeilForm.CouplingCauchySchwarzBulk.bulkFloor_iff_smul_innerₗ hb]
  simp only [EvenOperatorFloor, Cvs.WeilForm.CouplingFiniteSchur.Bx_self]

/-! ### The assembly -/

/-- **The even form coupling from the even operator floor, channel and ratio.** -/
theorem evenFormCoupling_of_weighted {x : ℕ} {M : LinearMap.BilinForm ℝ (Dom x)} {κ : Dom x → ℝ} {δ : ℝ}
    (hF : EvenOperatorFloor x M) (hC : EvenWeightedChannel x M κ) (hR : EvenWeightedRatio x δ κ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenFormCoupling x δ :=
  (Cvs.Route.EvenWindowBulkCoupling.evenFormCoupling_iff x δ).2 (Cvs.WeilForm.CouplingCauchySchwarzBulk.coupling_of_weighted' (B := Bx x) (M := M) (κ := κ)
    (fun w hw hwR => by rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]; exact hF w hw hwR)
    (fun r hr => (hC r hr).1) (fun r hr w hw hwR => (hC r hr).2 w hw hwR)
    (fun r hr => by rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]; exact hR r hr))

/-- **The even channel and ratio with `δ < 1` give even rung positivity.** -/
theorem evenRungPos_of_weighted {x : ℕ} {M : LinearMap.BilinForm ℝ (Dom x)} {κ : Dom x → ℝ} {δ : ℝ}
    (hδ : δ < 1) (hC : EvenWeightedChannel x M κ) (hR : EvenWeightedRatio x δ κ) : Cvs.Route.EvenWindowBulkCoupling.EvenRungPos x :=
  fun r hr => nonneg_of_mul_nonneg_right ((hC r hr).1.trans (hR r hr)) (by linarith)

/-- **Even window positivity at `x` from the even operator floor, channel and ratio**, with `0 ≤ δ < 1`. -/
theorem Q_nonneg_of_even_weighted {x : ℕ} {M : LinearMap.BilinForm ℝ (Dom x)} {κ : Dom x → ℝ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hF : EvenOperatorFloor x M) (hC : EvenWeightedChannel x M κ)
    (hR : EvenWeightedRatio x δ κ) : ∀ φ ∈ Ev x, 0 ≤ Qx x φ :=
  Cvs.Route.EvenWindowBulkCoupling.Q_nonneg_of_even_floor_coupling (evenRungPos_of_weighted hδ1 hC hR) le_rfl hδ0
    (evenBulkFloor_zero_of_operatorFloor hF) (evenFormCoupling_of_weighted hF hC hR)

/-- **Even window positivity at `x` gives the even operator floor, channel and ratio** at `M = Q`, `κ = Q`,
`δ = 0`. -/
theorem even_weighted_self_of_Q_nonneg {x : ℕ} (h : ∀ φ ∈ Ev x, 0 ≤ Qx x φ) :
    EvenOperatorFloor x (Bx x) ∧ EvenWeightedChannel x (Bx x) (Qx x) ∧ EvenWeightedRatio x 0 (Qx x) := by
  have hB : ∀ w ∈ Ev x, 0 ≤ Bx x w w := fun w hw => by rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]; exact h w hw
  refine ⟨fun w hwe _ => ⟨hB w hwe, le_of_eq (Cvs.WeilForm.CouplingFiniteSchur.Bx_self x w)⟩,
    fun r hr => ⟨h r (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hr), fun w hwe _ => ?_⟩, fun r _ => by simp⟩
  have hCS := Cvs.WeilForm.CouplingGramTopEigen.sq_le_mul_of_nonneg (B := Bx x) (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _) hB
    (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hr) hwe
  rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self x r] at hCS
  exact hCS

/-- **Even window positivity at `x` is the existence of an even operator floor, channel and ratio** with
`κ ≤ Q` on `R₁`. -/
theorem evenWindowPos_iff_even_weighted (x : ℕ) :
    (∀ φ ∈ Ev x, 0 ≤ Qx x φ) ↔ ∃ (M : LinearMap.BilinForm ℝ (Dom x)) (κ : Dom x → ℝ),
      EvenOperatorFloor x M ∧ EvenWeightedChannel x M κ ∧ EvenWeightedRatio x 0 κ :=
  ⟨fun h => ⟨_, _, even_weighted_self_of_Q_nonneg h⟩,
    fun ⟨_, _, hF, hC, hR⟩ => Q_nonneg_of_even_weighted le_rfl one_pos hF hC hR⟩

/-! ### RH -/

/-! ### The weight `M = Q` -/

/-! ### The weight `M = b⟪·,·⟫` -/

/-- **The scalar route at `M = b⟪·,·⟫`**: for `b > 0`, `EvenBulkFloor x b`, `|Q(r,w)| ≤ c(r)‖w‖` on the even
bulk and `c(r)² ≤ (1−δ)b·Q(r)` on `R₁` give the even operator floor, channel and ratio with
`κ(r) = c(r)²/b`. -/
theorem even_weighted_of_norm {x : ℕ} {b δ : ℝ} {c : Dom x → ℝ} (hb : 0 < b) (hF : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b)
    (hc : ∀ r ∈ R1 x, ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
      |Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) r w| ≤ c r * ‖w‖)
    (hr : ∀ r ∈ R1 x, c r ^ 2 ≤ (1 - δ) * b * Qx x r) :
    EvenOperatorFloor x (b • innerₗ (Dom x)) ∧
      EvenWeightedChannel x (b • innerₗ (Dom x)) (fun r => c r ^ 2 / b) ∧
        EvenWeightedRatio x δ (fun r => c r ^ 2 / b) := by
  refine ⟨(evenOperatorFloor_smul_innerₗ_iff x hb.le).2 hF,
    fun r hr => ⟨div_nonneg (sq_nonneg _) hb.le, fun w hwe hw => ?_⟩, fun r hr' => ?_⟩
  · exact Cvs.WeilForm.CouplingCauchySchwarzBulk.sq_le_smul_innerₗ (B := Bx x) hb (hc r hr w hwe hw)
  · have h := (Cvs.WeilForm.CouplingCauchySchwarzBulk.sq_div_le_iff (B := Bx x) (r := r) (c := c r) (δ := δ) hb).2
      (by rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]; exact hr r hr')
    rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self] at h
    exact h

end Cvs.Route.EvenFormBelowBulk
