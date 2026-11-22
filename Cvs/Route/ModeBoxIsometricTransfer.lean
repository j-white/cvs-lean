import Mathlib
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.FreqThresholdModeCutoff
import Cvs.Route.HighModeTailArchFree

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Canonical `N`-Independent Mode Box `ModeBox M₀` and Isometric Rung Transfer

Isometrically embeds `modeCutoffRung N M₀` and `lowModeRung L N C` into the `N`-independent
space `ModeBox M₀ → ℝ`, transferring `A1Mat`, `ApoleMat`, and `M` floors across all `N : ℕ`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxIsometricTransfer
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.LowModeRungBulkFloor
open Cvs.Route.FreqThresholdModeCutoff
open Cvs.Route.HighModeTailArchFree

/-! ### The `N`-independent integer mode box `ModeBox M₀` -/

/-- **The `N`-independent integer mode box of radius `M₀ : ℕ`**:
`{m : ℤ // m ∈ Finset.Icc (-M₀) M₀}` of cardinality `2M₀ + 1`. -/
abbrev ModeBox (M₀ : ℕ) : Type :=
  {m : ℤ // m ∈ Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ)}

/-- The integer mode value `m.1` of `m : ModeBox M₀`. -/
def boxMode (M₀ : ℕ) (m : ModeBox M₀) : ℤ := m.1

/-- `boxMode M₀` is injective. -/
theorem boxMode_injective (M₀ : ℕ) : Function.Injective (boxMode M₀) :=
  Subtype.val_injective

/-- The negation involution `m ↦ -m` on `ModeBox M₀`. -/
def negBox (M₀ : ℕ) (m : ModeBox M₀) : ModeBox M₀ :=
  ⟨-m.1, by
    have hm := Finset.mem_Icc.mp m.2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-- `negBox M₀` is an involution on `ModeBox M₀`. -/
theorem negBox_involutive (M₀ : ℕ) : Function.Involutive (negBox M₀) :=
  fun m => Subtype.ext (neg_neg m.1)

/-- `boxMode M₀` negates under `negBox M₀`. -/
theorem boxMode_negBox (M₀ : ℕ) (m : ModeBox M₀) :
    boxMode M₀ (negBox M₀ m) = -boxMode M₀ m :=
  rfl

/-- `Cvs.Finite.SymmetricModeSet.mode N i ∈ Finset.Icc (-M₀) M₀` iff `i ∈ modeCutoffSet N M₀`. -/
theorem mem_Icc_iff_mem_modeCutoffSet {N M₀ : ℕ} (i : Cvs.Finite.SymmetricModeSet.Idx N) :
    Cvs.Finite.SymmetricModeSet.mode N i ∈ Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ) ↔ i ∈ modeCutoffSet N M₀ := by
  rw [Finset.mem_Icc]
  change (-(M₀ : ℤ) ≤ Cvs.Finite.SymmetricModeSet.mode N i ∧ Cvs.Finite.SymmetricModeSet.mode N i ≤ (M₀ : ℤ)) ↔
    (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ M₀
  omega

/-- Embedding of a cutoff mode index `i ∈ modeCutoffSet N M₀` into `ModeBox M₀`. -/
def idxToModeBox {N M₀ : ℕ} (i : Cvs.Finite.SymmetricModeSet.Idx N) (hi : i ∈ modeCutoffSet N M₀) : ModeBox M₀ :=
  ⟨Cvs.Finite.SymmetricModeSet.mode N i, (mem_Icc_iff_mem_modeCutoffSet i).2 hi⟩

/-! ### The zero-padded lifting map `toModeBox` and isometric quadratic form preservation -/

/-- **Zero-padded lifting map** from `Cvs.Finite.SymmetricModeSet.Idx N → ℝ` to the `N`-independent box `ModeBox M₀ → ℝ`. -/
def toModeBox (N M₀ : ℕ) (r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) (m : ModeBox M₀) : ℝ :=
  ∑ i : Cvs.Finite.SymmetricModeSet.Idx N, if Cvs.Finite.SymmetricModeSet.mode N i = m.1 then r i else 0

/-- **`toModeBox` maps `evenModeSub (negI N)` into `evenModeSub (negBox M₀)`.** -/
theorem toModeBox_mem_evenModeSub (N M₀ : ℕ) {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : r ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) :
    toModeBox N M₀ r ∈ evenModeSub (negBox M₀) := by
  intro m
  dsimp [toModeBox, negBox]
  refine Fintype.sum_bijective (Cvs.Finite.SymmetricModeSet.negI N) (Cvs.Finite.SymmetricModeSet.negI_involutive N).bijective _ _ fun i => ?_
  have hmode : (Cvs.Finite.SymmetricModeSet.mode N (Cvs.Finite.SymmetricModeSet.negI N i) = m.1) ↔ (Cvs.Finite.SymmetricModeSet.mode N i = -m.1) := by
    rw [Cvs.Finite.SymmetricModeSet.mode_negI N i, neg_eq_iff_eq_neg]
  simp only [hmode, hr i]

/-- On `i ∈ modeCutoffSet N M₀`, `toModeBox N M₀ r (idxToModeBox i hi) = r i`. -/
theorem toModeBox_idxToModeBox {N M₀ : ℕ} (r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ)
    {i : Cvs.Finite.SymmetricModeSet.Idx N} (hi : i ∈ modeCutoffSet N M₀) :
    toModeBox N M₀ r (idxToModeBox i hi) = r i := by
  dsimp [toModeBox, idxToModeBox]
  have hcongr : (∑ j : Cvs.Finite.SymmetricModeSet.Idx N, if Cvs.Finite.SymmetricModeSet.mode N j = Cvs.Finite.SymmetricModeSet.mode N i then r j else 0)
      = ∑ j : Cvs.Finite.SymmetricModeSet.Idx N, if j = i then r j else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [(Cvs.Finite.SymmetricModeSet.mode_injective N).eq_iff]
  rw [hcongr, Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]

/-- **Master sum-transfer identity**: for `r` supported on `modeCutoffSet N M₀` and any `g : ℤ → ℝ`,
`∑_{m : ModeBox M₀} toModeBox N M₀ r m * g(m) = ∑_{i : Idx N} r i * g(mode_N(i))`. -/
theorem sum_toModeBox_mul_eq (N M₀ : ℕ) (g : ℤ → ℝ) {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : ∀ i, i ∉ modeCutoffSet N M₀ → r i = 0) :
    (∑ m : ModeBox M₀, toModeBox N M₀ r m * g (boxMode M₀ m)) =
      ∑ i : Cvs.Finite.SymmetricModeSet.Idx N, r i * g (Cvs.Finite.SymmetricModeSet.mode N i) := by
  simp only [toModeBox, boxMode, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ modeCutoffSet N M₀
  · set m₀ : ModeBox M₀ := idxToModeBox i hi
    have hcongr : (∑ m : ModeBox M₀, (if Cvs.Finite.SymmetricModeSet.mode N i = m.1 then r i else 0) * g m.1)
        = ∑ m : ModeBox M₀, if m = m₀ then r i * g m.1 else 0 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      have heq : (Cvs.Finite.SymmetricModeSet.mode N i = m.1) ↔ (m = m₀) := by
        rw [Subtype.ext_iff]
        exact eq_comm
      by_cases hm : m = m₀
      · rw [if_pos hm, if_pos (heq.2 hm)]
      · rw [if_neg hm, if_neg (mt heq.1 hm), zero_mul]
    rw [hcongr, Finset.sum_ite_eq', if_pos (Finset.mem_univ m₀)]
    rfl
  · rw [hr i hi]
    simp

/-- **Master quadratic-form transfer identity**: for any integer-mode kernel `F : ℤ → ℤ → ℝ` and
`r` supported on `modeCutoffSet N M₀`, `toModeBox N M₀ r` has the exact same quadratic form on
`ModeBox M₀` as `r` on `Idx N`. -/
theorem toModeBox_quad_eq (N M₀ : ℕ) (F : ℤ → ℤ → ℝ) {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : ∀ i, i ∉ modeCutoffSet N M₀ → r i = 0) :
    toModeBox N M₀ r ⬝ᵥ
        (Matrix.of (fun m₁ m₂ : ModeBox M₀ => F (boxMode M₀ m₁) (boxMode M₀ m₂)) *ᵥ toModeBox N M₀ r)
      = r ⬝ᵥ (Matrix.of (fun i j : Cvs.Finite.SymmetricModeSet.Idx N => F (Cvs.Finite.SymmetricModeSet.mode N i) (Cvs.Finite.SymmetricModeSet.mode N j)) *ᵥ r) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
  have Dinner : ∀ m₁ : ModeBox M₀,
      (∑ m₂ : ModeBox M₀, F (boxMode M₀ m₁) (boxMode M₀ m₂) * toModeBox N M₀ r m₂)
        = ∑ j : Cvs.Finite.SymmetricModeSet.Idx N, F (boxMode M₀ m₁) (Cvs.Finite.SymmetricModeSet.mode N j) * r j := by
    intro m₁
    have h1 := sum_toModeBox_mul_eq N M₀ (fun z => F (boxMode M₀ m₁) z) hr
    calc (∑ m₂ : ModeBox M₀, F (boxMode M₀ m₁) (boxMode M₀ m₂) * toModeBox N M₀ r m₂)
        = ∑ m₂ : ModeBox M₀, toModeBox N M₀ r m₂ * F (boxMode M₀ m₁) (boxMode M₀ m₂) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = ∑ j : Cvs.Finite.SymmetricModeSet.Idx N, r j * F (boxMode M₀ m₁) (Cvs.Finite.SymmetricModeSet.mode N j) := h1
      _ = ∑ j : Cvs.Finite.SymmetricModeSet.Idx N, F (boxMode M₀ m₁) (Cvs.Finite.SymmetricModeSet.mode N j) * r j :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp_rw [Dinner]
  exact sum_toModeBox_mul_eq N M₀ (fun z => ∑ j : Cvs.Finite.SymmetricModeSet.Idx N, F z (Cvs.Finite.SymmetricModeSet.mode N j) * r j) hr

/-- **Isometry of `toModeBox` on vectors supported in `modeCutoffSet N M₀`**:
`toModeBox N M₀ r ⬝ᵥ toModeBox N M₀ r = r ⬝ᵥ r`. -/
theorem toModeBox_dotProduct_self (N M₀ : ℕ) {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : ∀ i, i ∉ modeCutoffSet N M₀ → r i = 0) :
    toModeBox N M₀ r ⬝ᵥ toModeBox N M₀ r = r ⬝ᵥ r := by
  have h := toModeBox_quad_eq N M₀ (fun m₁ m₂ => if m₁ = m₂ then (1 : ℝ) else 0) hr
  have h1 : Matrix.of (fun m₁ m₂ : ModeBox M₀ => if boxMode M₀ m₁ = boxMode M₀ m₂ then (1 : ℝ) else 0)
      = (1 : Matrix (ModeBox M₀) (ModeBox M₀) ℝ) := by
    ext m₁ m₂
    simp [(boxMode_injective M₀).eq_iff, Matrix.one_apply]
  have h2 : Matrix.of (fun i j : Cvs.Finite.SymmetricModeSet.Idx N => if Cvs.Finite.SymmetricModeSet.mode N i = Cvs.Finite.SymmetricModeSet.mode N j then (1 : ℝ) else 0)
      = (1 : Matrix (Cvs.Finite.SymmetricModeSet.Idx N) (Cvs.Finite.SymmetricModeSet.Idx N) ℝ) := by
    ext i j
    simp [(Cvs.Finite.SymmetricModeSet.mode_injective N).eq_iff, Matrix.one_apply]
  rw [h1, h2, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

/-! ### Exact preservation of `M`, `A1Mat`, and `ApoleMat` quadratic forms under `toModeBox` -/

/-- Integer-mode kernel of `Cvs.Finite.TruncationQuadraticForm.M P R L`. -/
def modeKernelM (P R : ℕ) (L : ℝ) (m₁ m₂ : ℤ) : ℝ :=
  if m₁ = m₂ then Cvs.Finite.PairFormDividedDifference.aval P R L m₁
  else (Cvs.Finite.PairFormDividedDifference.bval P R L m₁ - Cvs.Finite.PairFormDividedDifference.bval P R L m₂) / (2 * π * m₁ / L - 2 * π * m₂ / L)

/-- Integer-mode kernel of `Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L`. -/
def modeKernelA1 (P R : ℕ) (L : ℝ) (m₁ m₂ : ℤ) : ℝ :=
  modeKernelM P R L m₁ m₂ - 1 / L * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * m₁ / L) (2 * π * m₂ / L)

/-- For any injective `mode : ι → ℤ`, `Cvs.Finite.TruncationQuadraticForm.M P R L mode` is given by `modeKernelM`. -/
theorem M_eq_of_modeKernelM {ι : Type*} [Fintype ι] [DecidableEq ι] (P R : ℕ) (L : ℝ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) :
    Cvs.Finite.TruncationQuadraticForm.M P R L mode = Matrix.of (fun i j => modeKernelM P R L (mode i) (mode j)) := by
  ext i j
  simp [Cvs.Finite.TruncationQuadraticForm.M, Cvs.Finite.DividedDifferenceCommutator.ddMatrix, Cvs.Finite.TruncationZeroFreeOffAxes.omega, modeKernelM, hinj.eq_iff]

/-- For any injective `mode : ι → ℤ`, `Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode` is given by `modeKernelA1`. -/
theorem A1Mat_eq_of_modeKernelA1 {ι : Type*} [Fintype ι] [DecidableEq ι] (P R : ℕ) (L : ℝ)
    {mode : ι → ℤ} (hinj : Function.Injective mode) :
    Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L mode = Matrix.of (fun i j => modeKernelA1 P R L (mode i) (mode j)) := by
  ext i j
  have hM := congrFun (congrFun (M_eq_of_modeKernelM P R L hinj) i) j
  simp only [Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat, hM, Matrix.of_apply, modeKernelA1]

/-- **`toModeBox` preserves the `Cvs.Finite.TruncationQuadraticForm.M` quadratic form** for `r` supported on `modeCutoffSet N M₀`. -/
theorem toModeBox_M_quad_eq (P R N M₀ : ℕ) (L : ℝ) {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : ∀ i, i ∉ modeCutoffSet N M₀ → r i = 0) :
    toModeBox N M₀ r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ toModeBox N M₀ r)
      = r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) := by
  rw [M_eq_of_modeKernelM P R L (boxMode_injective M₀),
    M_eq_of_modeKernelM P R L (Cvs.Finite.SymmetricModeSet.mode_injective N)]
  exact toModeBox_quad_eq N M₀ (modeKernelM P R L) hr

/-- **`toModeBox` preserves the `A1Mat` quadratic form** for `r` supported on `modeCutoffSet N M₀`. -/
theorem toModeBox_A1Mat_quad_eq (P R N M₀ : ℕ) (L : ℝ) {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hr : ∀ i, i ∉ modeCutoffSet N M₀ → r i = 0) :
    toModeBox N M₀ r ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (boxMode M₀) *ᵥ toModeBox N M₀ r)
      = r ⬝ᵥ (Cvs.Route.EvenMatrixSlotPoleRestored.A1Mat P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) := by
  rw [A1Mat_eq_of_modeKernelA1 P R L (boxMode_injective M₀),
    A1Mat_eq_of_modeKernelA1 P R L (Cvs.Finite.SymmetricModeSet.mode_injective N)]
  exact toModeBox_quad_eq N M₀ (modeKernelA1 P R L) hr

/-! ### Support of `modeCutoffRung` and `N`-independent rung floor transfer -/

/-- `modeCutoffSet N M₀` is invariant under `Cvs.Finite.SymmetricModeSet.negI N`. -/
theorem negI_mem_modeCutoffSet_iff (N M₀ : ℕ) (i : Cvs.Finite.SymmetricModeSet.Idx N) :
    Cvs.Finite.SymmetricModeSet.negI N i ∈ modeCutoffSet N M₀ ↔ i ∈ modeCutoffSet N M₀ := by
  change (Cvs.Finite.SymmetricModeSet.mode N (Cvs.Finite.SymmetricModeSet.negI N i)).natAbs ≤ M₀ ↔ (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ M₀
  rw [Cvs.Finite.SymmetricModeSet.mode_negI, Int.natAbs_neg]

/-- Every vector `r ∈ modeCutoffRung N M₀` vanishes outside `modeCutoffSet N M₀`. -/
theorem apply_eq_zero_of_mem_modeCutoffRung {N M₀ : ℕ}
    {r : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hr : r ∈ modeCutoffRung N M₀)
    {i : Cvs.Finite.SymmetricModeSet.Idx N} (hi : i ∉ modeCutoffSet N M₀) :
    r i = 0 :=
  apply_eq_zero_of_mem_span_evenBasisVec (negI_mem_modeCutoffSet_iff N M₀) hr hi

/-- **Transfer of an `N`-independent `Cvs.Finite.TruncationQuadraticForm.M` floor on `ModeBox M₀` to `modeCutoffRung N M₀` for all `N`.** -/
theorem modeCutoffRung_M_floor_of_modeBox (P R N M₀ : ℕ) (L cR : ℝ)
    (hbox : ∀ η ∈ evenModeSub (negBox M₀),
      cR * (η ⬝ᵥ η) ≤ η ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (boxMode M₀) *ᵥ η)) :
    ∀ r ∈ modeCutoffRung N M₀,
      cR * (r ⬝ᵥ r) ≤ r ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ r) := by
  intro r hr
  have hsupp : ∀ i, i ∉ modeCutoffSet N M₀ → r i = 0 :=
    fun _ hi => apply_eq_zero_of_mem_modeCutoffRung hr hi
  have hev : toModeBox N M₀ r ∈ evenModeSub (negBox M₀) :=
    toModeBox_mem_evenModeSub N M₀ (modeCutoffRung_le_evenModeSub N M₀ hr)
  have h := hbox (toModeBox N M₀ r) hev
  rwa [toModeBox_dotProduct_self N M₀ hsupp, toModeBox_M_quad_eq P R N M₀ L hsupp] at h

end Cvs.Route.ModeBoxIsometricTransfer
