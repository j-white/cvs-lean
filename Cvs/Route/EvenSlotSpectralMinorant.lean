import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenFormBelowBulk
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
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
# The even slot with a spectral minorant

`M = Σ_k g_k⟪φ_k,·⟫⟪φ_k,·⟫ + A` (`g_k > 0`, `A` symmetric and `≥ 0` on a subspace `K` holding the even bulk and
every `u(r)`) with `M ≤ Q` on the even bulk, `Q(r,w) = Σ_k c_k(r)⟪φ_k,w⟫ + A(u(r),w)` there and
`Σ_k c_k(r)²/g_k + A(u(r),u(r)) ≤ Q(r)` on `R₁` fill `EvenFormBelowBulk`'s slot. At each `x` the slot is even window positivity
(filled by `n = 0`, `A = Q`, `u = id`, `K` the even classes), and at infinitely many `x` it is RH.
-/

noncomputable section

open Real Filter Finset
open scoped InnerProductSpace

namespace Cvs.Route.EvenSlotSpectralMinorant
open Cvs.ZeroCounting

open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)

/-! ### The spectral form -/

/-- The rank-one form `(v, w) ↦ ⟪φ, v⟫⟪φ, w⟫`. -/
def rankOne {x : ℕ} (φ : Dom x) : LinearMap.BilinForm ℝ (Dom x) :=
  (innerₗ (Dom x) φ).smulRight (innerₗ (Dom x) φ)

/-- `rankOne φ v w = ⟪φ, v⟫⟪φ, w⟫`. -/
theorem rankOne_apply {x : ℕ} (φ v w : Dom x) : rankOne φ v w = ⟪φ, v⟫_ℝ * ⟪φ, w⟫_ℝ := by
  simp [rankOne, innerₗ_apply_apply]

/-- **The spectral form** `M(v,w) = Σ_k g_k⟪φ_k,v⟫⟪φ_k,w⟫ + A(v,w)`. -/
def specForm {x : ℕ} {ι : Type*} [Fintype ι] (φ : ι → Dom x) (g : ι → ℝ)
    (A : LinearMap.BilinForm ℝ (Dom x)) : LinearMap.BilinForm ℝ (Dom x) :=
  ∑ k, g k • rankOne (φ k) + A

/-- `specForm φ g A v w = Σ_k g_k⟪φ_k,v⟫⟪φ_k,w⟫ + A(v,w)`. -/
theorem specForm_apply {x : ℕ} {ι : Type*} [Fintype ι] (φ : ι → Dom x) (g : ι → ℝ)
    (A : LinearMap.BilinForm ℝ (Dom x)) (v w : Dom x) :
    specForm φ g A v w = ∑ k, g k * (⟪φ k, v⟫_ℝ * ⟪φ k, w⟫_ℝ) + A v w := by
  simp [specForm, rankOne_apply, LinearMap.sum_apply]

/-- On the diagonal the spectral form is `Σ_k g_k⟪φ_k,w⟫² + A(w,w)`. -/
theorem specForm_self {x : ℕ} {ι : Type*} [Fintype ι] (φ : ι → Dom x) (g : ι → ℝ)
    (A : LinearMap.BilinForm ℝ (Dom x)) (w : Dom x) :
    specForm φ g A w w = ∑ k, g k * ⟪φ k, w⟫_ℝ ^ 2 + A w w := by
  rw [specForm_apply]; congr 1; exact sum_congr rfl fun k _ => by ring

/-! ### The slot -/

/-- **The spectral comparison at `x`**: `Σ_k g_k⟪φ_k,w⟫² + A(w,w) ≤ Q(w)` on the even bulk. -/
def SpecComparison (x : ℕ) {ι : Type*} [Fintype ι] (φ : ι → Dom x) (g : ι → ℝ)
    (A : LinearMap.BilinForm ℝ (Dom x)) : Prop :=
  ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → specForm φ g A w w ≤ Qx x w

/-- **The two-band representation of the coupling at `x`**: `Q(r,w) = Σ_k c_k(r)⟪φ_k,w⟫ + A(u(r),w)` for
`r ∈ R₁` and `w` in the even bulk. -/
def SpecRepresentation (x : ℕ) {ι : Type*} [Fintype ι] (φ : ι → Dom x) (A : LinearMap.BilinForm ℝ (Dom x))
    (c : Dom x → ι → ℝ) (u : Dom x → Dom x) : Prop :=
  ∀ r ∈ R1 x, ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) r w = ∑ k, c r k * ⟪φ k, w⟫_ℝ + A (u r) w

/-- **The spectral ratio at `x`**: `Σ_k c_k(r)²/g_k + A(u(r),u(r)) ≤ Q(r)` on `R₁`. -/
def SpecRatio (x : ℕ) {ι : Type*} [Fintype ι] (g : ι → ℝ) (A : LinearMap.BilinForm ℝ (Dom x))
    (c : Dom x → ι → ℝ) (u : Dom x → Dom x) : Prop :=
  ∀ r ∈ R1 x, ∑ k, c r k ^ 2 / g k + A (u r) (u r) ≤ Qx x r

/-- The weight the spectral data assign to `r`: `κ(r) = Σ_k c_k(r)²/g_k + A(u(r),u(r))`. -/
def specKappa {x : ℕ} {ι : Type*} [Fintype ι] (g : ι → ℝ) (A : LinearMap.BilinForm ℝ (Dom x))
    (c : Dom x → ι → ℝ) (u : Dom x → Dom x) (r : Dom x) : ℝ :=
  ∑ k, c r k ^ 2 / g k + A (u r) (u r)

/-! ### The slot fills Cvs.Route.EvenFormBelowBulk -/

/-- **Two-band Cauchy–Schwarz**: `(Σ_k c_k a_k + β)² ≤ (Σ_k c_k²/g_k + s)(Σ_k g_k a_k² + t)` for `g_k > 0`,
`s, t ≥ 0` and `β² ≤ s t`. -/
theorem sq_add_le {ι : Type*} [Fintype ι] {g c a : ι → ℝ} (hg : ∀ k, 0 < g k) {β s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hβ : β ^ 2 ≤ s * t) :
    (∑ k, c k * a k + β) ^ 2 ≤ (∑ k, c k ^ 2 / g k + s) * (∑ k, g k * a k ^ 2 + t) := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset (Option ι))
    (r := fun o => o.elim β fun k => c k * a k) (f := fun o => o.elim s fun k => c k ^ 2 / g k)
    (g := fun o => o.elim t fun k => g k * a k ^ 2)
    (fun o _ => by cases o <;> simp [hs, div_nonneg (sq_nonneg _) (hg _).le])
    (fun o _ => by cases o <;> simp [ht, mul_nonneg (hg _).le (sq_nonneg _)])
    (fun o _ => by
      cases o with
      | none => simpa using hβ
      | some k =>
        simp only [Option.elim_some]
        have hk := (hg k).ne'
        exact le_of_eq (by field_simp))
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some] at h
  calc (∑ k, c k * a k + β) ^ 2 = (β + ∑ k, c k * a k) ^ 2 := by ring
    _ ≤ (s + ∑ k, c k ^ 2 / g k) * (t + ∑ k, g k * a k ^ 2) := h
    _ = _ := by ring

/-- **The spectral comparison gives `EvenFormBelowBulk`'s even operator floor** for `g ≥ 0` and `A ≥ 0`. -/
theorem evenOperatorFloor_specForm {x : ℕ} {ι : Type*} [Fintype ι] {φ : ι → Dom x} {g : ι → ℝ}
    {A : LinearMap.BilinForm ℝ (Dom x)} (hg : ∀ k, 0 ≤ g k) (hA : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → 0 ≤ A w w)
    (hC : SpecComparison x φ g A) : Cvs.Route.EvenFormBelowBulk.EvenOperatorFloor x (specForm φ g A) := fun w hwe hw => by
  refine ⟨?_, hC w hwe hw⟩
  rw [specForm_self]
  exact add_nonneg (sum_nonneg fun k _ => mul_nonneg (hg k) (sq_nonneg _)) (hA w hwe hw)

/-- **The two-band representation gives `EvenFormBelowBulk`'s even channel** with `κ = specKappa`, for `g > 0` and `A`
symmetric and `≥ 0` on a subspace `K` holding the even bulk and every `u(r)`. -/
theorem evenWeightedChannel_specForm {x : ℕ} {ι : Type*} [Fintype ι] {φ : ι → Dom x} {g : ι → ℝ}
    {A : LinearMap.BilinForm ℝ (Dom x)} {c : Dom x → ι → ℝ} {u : Dom x → Dom x} {K : Submodule ℝ (Dom x)}
    (hg : ∀ k, 0 < g k) (hAs : A.IsSymm) (hA : ∀ v ∈ K, 0 ≤ A v v) (hbulk : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → w ∈ K)
    (hu : ∀ r ∈ R1 x, u r ∈ K) (hR : SpecRepresentation x φ A c u) :
    Cvs.Route.EvenFormBelowBulk.EvenWeightedChannel x (specForm φ g A) (specKappa g A c u) := fun r hr => by
  refine ⟨add_nonneg (sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (hg k).le) (hA _ (hu r hr)),
    fun w hwe hw => ?_⟩
  have hβ : A (u r) w ^ 2 ≤ A (u r) (u r) * A w w :=
    Cvs.WeilForm.CouplingGramTopEigen.sq_le_mul_of_nonneg hAs hA (hu r hr) (hbulk w hwe hw)
  rw [hR r hr w hwe hw, specKappa, specForm_self]
  exact sq_add_le hg (hA _ (hu r hr)) (hA _ (hbulk w hwe hw)) hβ

/-- **The spectral ratio gives `EvenFormBelowBulk`'s even ratio** at `δ = 0`. -/
theorem evenWeightedRatio_specKappa {x : ℕ} {ι : Type*} [Fintype ι] {g : ι → ℝ}
    {A : LinearMap.BilinForm ℝ (Dom x)} {c : Dom x → ι → ℝ} {u : Dom x → Dom x} (hR : SpecRatio x g A c u) :
    Cvs.Route.EvenFormBelowBulk.EvenWeightedRatio x 0 (specKappa g A c u) := fun r hr => by
  rw [sub_zero, one_mul]; exact hR r hr

/-- **Even window positivity at `x` from spectral data**: `g > 0`, `A` symmetric and `≥ 0` on a subspace `K`
holding the even bulk and every `u(r)`, the comparison, the two-band representation and the ratio. -/
theorem Q_nonneg_of_spec {x : ℕ} {ι : Type*} [Fintype ι] {φ : ι → Dom x} {g : ι → ℝ}
    {A : LinearMap.BilinForm ℝ (Dom x)} {c : Dom x → ι → ℝ} {u : Dom x → Dom x} {K : Submodule ℝ (Dom x)}
    (hg : ∀ k, 0 < g k) (hAs : A.IsSymm) (hA : ∀ v ∈ K, 0 ≤ A v v)
    (hbulk : ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → w ∈ K) (hu : ∀ r ∈ R1 x, u r ∈ K) (hC : SpecComparison x φ g A)
    (hR : SpecRepresentation x φ A c u) (hQ : SpecRatio x g A c u) : ∀ v ∈ Ev x, 0 ≤ Qx x v :=
  (Cvs.Route.EvenFormBelowBulk.evenWindowPos_iff_even_weighted x).2
    ⟨_, _, evenOperatorFloor_specForm (fun k => (hg k).le) (fun w hwe hw => hA w (hbulk w hwe hw)) hC,
      evenWeightedChannel_specForm hg hAs hA hbulk hu hR, evenWeightedRatio_specKappa hQ⟩

end Cvs.Route.EvenSlotSpectralMinorant
