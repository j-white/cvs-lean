import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.EvenModeSumsFormDense
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Route.CoreSchurForm
import Cvs.Route.EvenHyperplaneFloorCompress
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.JointGapConnesFromL1
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.Upstream.MergedBoundSchurForm
import Cvs.WeilForm.CouplingFiniteSchur
import Cvs.WeilForm.CouplingFromTameDensity
import Cvs.WeilForm.CouplingGramTopEigen
import Cvs.WeilForm.CouplingPrimeForm
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.WindowOrthogonalComplement
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even bulk floor and coupling in mode matrices

At `1 < x`, `MergedBoundSchurForm`'s bulk floor and coupling on `Ev x` against a finite-dimensional `R ≤ Ev x` are their restrictions
to even mode sums `modeMap f ⊥ R`, read through `‖modeMap f‖² = log x·f⬝f` and `Q(modeMap f) = log x·f⬝M_N f`;
against `D₀` the constraint, the rung columns and the Gram are explicit matrices. A positive floor and a coupling
against `D₀` at infinitely many `x` is RH plus a positive matrix floor at infinitely many `x`.
-/

noncomputable section

open MeasureTheory Real Filter Topology Set Matrix
open scoped InnerProductSpace

namespace Cvs.Finite.EvenBulkModeMatrices
open Cvs.ZeroCounting

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Positivity on `H` gives the zero-margin coupling on `H`** against every `R ≤ H` (Cauchy–Schwarz). -/
theorem coupling_zero_of_nonneg_on {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {H R : Submodule ℝ E}
    (hRH : R ≤ H) (h : ∀ v ∈ H, 0 ≤ B v v) : Cvs.Upstream.MergedBoundSchurForm.Coupling B H R 0 := fun r hr w hw _ => by
  simpa using Cvs.WeilForm.CouplingGramTopEigen.sq_le_mul_of_nonneg hB h (hRH hr) hw

end Abstract

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx rung D0 D0idx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)

/-! ### Mode vectors against a finite-dimensional `R ≤ Ev x` -/

/-- **The `L²` pairing with a mode sum is a dot product**: `⟪η, modeMap f⟫ = normalCoeff(η) ⬝ f`. -/
theorem inner_modeMap {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) (η : Dom x) (f : Idx N → ℝ) :
    ⟪η, Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f⟫_ℝ
      = Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) η (mode N) ⬝ᵥ f := by
  rw [← Cvs.Route.EvenHyperplaneFloorCompress.ell_eq_dotProduct]
  have h : ⟪η, Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f⟫_ℝ
      = inner ℝ (η : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
          (Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) := rfl
  rw [h, Cvs.WeilForm.WindowOrthogonalComplement.inner_rep]
  unfold Cvs.Finite.DiscreteTwoGap.ell
  apply MeasureTheory.integral_congr_ae
  filter_upwards [(Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.Approximant.CosineColumnTailPairing.coe_modeClass_ae hx0 N f)] with s hs
  exact congrArg (Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) s * ·) hs

/-- **Orthogonality to a span is a set of dot-product constraints**: `modeMap f ⊥ span(range v)` iff
`normalCoeff(v j) ⬝ f = 0` for every `j`. -/
theorem modeMap_mem_orthogonal_span_iff {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) (f : Idx N → ℝ) {ι : Type*}
    (v : ι → Dom x) :
    Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f ∈ (Submodule.span ℝ (Set.range v))ᗮ ↔
      ∀ j, Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (v j) (mode N) ⬝ᵥ f = 0 := by
  constructor
  · intro h j
    rw [← inner_modeMap]
    exact (Submodule.mem_orthogonal _ _).1 h (v j) (Submodule.subset_span ⟨j, rfl⟩)
  · intro h
    refine (Submodule.mem_orthogonal _ _).2 fun r hr => ?_
    have hle : Submodule.span ℝ (Set.range v) ≤ (ℝ ∙ (Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f : Dom x))ᗮ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 ((inner_modeMap hx0 N _ f).trans (h j))
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hr)

/-- **The bulk floor against a finite-dimensional `R ≤ Ev x` is the mode-matrix floor** `b f⬝f ≤ f⬝M_N f` on even
`f` with `modeMap f ⊥ R`, at `1 < x`. -/
theorem bulkFloor_iff_matrix {x : ℕ} (hx1 : (1 : ℝ) < x) {R : Submodule ℝ (Dom x)} [FiniteDimensional ℝ R]
    (hRE : R ≤ Ev x) (b : ℝ) :
    Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) R b ↔
      ∀ (N : ℕ) (f : Idx N → ℝ), (∀ i, f (negI N i) = f i) →
        Cvs.Approximant.CosineColumnTailPairing.modeMap (zero_lt_one.trans hx1) N f ∈ Rᗮ →
        b * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ f) := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have key : ∀ (N : ℕ) (f : Idx N → ℝ), (∀ i, f (negI N i) = f i) →
      (b * ‖Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f‖ ^ 2 ≤ Bx x (Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f) (Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f) ↔
        b * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ f)) := by
    intro N f hf
    rw [Cvs.Route.JointGapConnesFromL1.norm_modeMap_sq hx0 hx1 N f hf, Cvs.WeilForm.CouplingFiniteSchur.Bx_self]
    change _ ≤ Cvs.WeilForm.InfimumAttainedSphere.Q _ x (Nat.clog 2 x) _ ↔ _
    rw [Cvs.Approximant.CosineColumnTailPairing.Q_modeMap hx0 hx1 x (Nat.clog 2 x) N f hf]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [Cvs.Finite.EvenModeSumsFormDense.bulkFloor_iff_of_dense (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _) (Cvs.WeilForm.CouplingFromTameDensity.floor_Bx x)
    (Cvs.Finite.EvenModeSumsFormDense.evenModes_le_Ev hx0) hRE (fun w hw => Cvs.Finite.EvenModeSumsFormDense.evenModeDense hx1 hw) b]
  constructor
  · intro h N f hf hperp
    exact (key N f hf).1 (h _ ⟨N, f, hf, rfl⟩ hperp)
  · rintro h _ ⟨N, f, hf, rfl⟩ hperp
    exact (key N f hf).2 (h N f hf hperp)

/-- **The coupling against a finite-dimensional `R ≤ Ev x` is the coupling against even mode sums `⊥ R`**, with
`Q(modeMap f) = log x·f⬝M_N f`, at `1 < x`. -/
theorem coupling_iff_matrix {x : ℕ} (hx1 : (1 : ℝ) < x) {R : Submodule ℝ (Dom x)} [FiniteDimensional ℝ R]
    (hRE : R ≤ Ev x) (δ : ℝ) :
    Cvs.Upstream.MergedBoundSchurForm.Coupling (Bx x) (Ev x) R δ ↔
      ∀ r ∈ R, ∀ (N : ℕ) (f : Idx N → ℝ), (∀ i, f (negI N i) = f i) →
        Cvs.Approximant.CosineColumnTailPairing.modeMap (zero_lt_one.trans hx1) N f ∈ Rᗮ →
        Bx x r (Cvs.Approximant.CosineColumnTailPairing.modeMap (zero_lt_one.trans hx1) N f) ^ 2
          ≤ (1 - δ) * Bx x r r *
            (Real.log x * (f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ f))) := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx1
  have hQ : ∀ (N : ℕ) (f : Idx N → ℝ), (∀ i, f (negI N i) = f i) →
      Bx x (Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f) (Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f)
        = Real.log x * (f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ f)) := by
    intro N f hf
    rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]
    exact Cvs.Approximant.CosineColumnTailPairing.Q_modeMap hx0 hx1 x (Nat.clog 2 x) N f hf
  rw [Cvs.Finite.EvenModeSumsFormDense.coupling_iff_of_dense (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _) (Cvs.WeilForm.CouplingFromTameDensity.floor_Bx x)
    (Cvs.Finite.EvenModeSumsFormDense.evenModes_le_Ev hx0) hRE (fun w hw => Cvs.Finite.EvenModeSumsFormDense.evenModeDense hx1 hw) δ]
  constructor
  · intro h r hr N f hf hperp
    rw [← hQ N f hf]
    exact h r hr _ ⟨N, f, hf, rfl⟩ hperp
  · rintro h r hr _ ⟨N, f, hf, rfl⟩ hperp
    rw [hQ N f hf]
    exact h r hr N f hf hperp

/-- **The even bulk floor against `R₁` is the mode-matrix floor** on even `f` with `normalCoeff(rung_j) ⬝ f = 0`
for every rung `j`, at `1 < x`. -/
theorem evenBulkFloor_iff_matrix {x : ℕ} (hx1 : (1 : ℝ) < x) (b : ℝ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b ↔
      ∀ (N : ℕ) (f : Idx N → ℝ), (∀ i, f (negI N i) = f i) →
        (∀ j : Cvs.Approximant.SpineSubspace.SF x, Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (rung x j) (mode N) ⬝ᵥ f = 0) →
        b * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ f) := by
  rw [Cvs.Route.EvenWindowBulkCoupling.evenBulkFloor_iff, bulkFloor_iff_matrix hx1 (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x)]
  exact forall_congr' fun N => forall_congr' fun f => forall_congr' fun _ =>
    imp_congr_left (modeMap_mem_orthogonal_span_iff _ N f (rung x))

/-! ### The rung matrices against `D₀` -/

/-- **The rung normals in closed form**: at `80 ≤ 2πx` the `i`-th normal coefficient of rung `j` is
`∫ k_G(e_j)·modeSum(e_i)`. -/
theorem normalCoeff_rung_eq_integral {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) (i : Idx N) :
    Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (rung x j) (mode N) i
      = ∫ s, Cvs.Approximant.SpineSubspace.kG x (Pi.single j (1 : ℝ)) s
          * Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) (Pi.single i 1) s := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have h1 := inner_modeMap hx0 N (rung x j) (Pi.single i 1)
  rw [dotProduct_single_one] at h1
  rw [← h1]
  have hsplit := Cvs.WeilForm.EvenOddSplitForm.evenPart_add_oddPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x (Pi.single j 1))
  have hodd : ⟪Cvs.WeilForm.EvenOddSplitForm.oddPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x (Pi.single j 1)),
      Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N (Pi.single i 1)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact Cvs.Route.EvenWindowBulkCoupling.inner_oddPart_eq_zero (Cvs.Approximant.CosineColumnTailPairing.reflD_modeMap hx0 N _) _
  have hsp : ⟪rung x j, Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N (Pi.single i 1)⟫_ℝ
      = ⟪Cvs.Approximant.SpineSubspace.spineMap x (Pi.single j 1), Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N (Pi.single i 1)⟫_ℝ := by
    conv_rhs => rw [← hsplit]
    rw [@inner_add_left ℝ (Dom x) _ _ _, hodd, add_zero]; rfl
  rw [hsp]
  have h : ⟪Cvs.Approximant.SpineSubspace.spineMap x (Pi.single j 1), Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N (Pi.single i 1)⟫_ℝ
      = inner ℝ (Cvs.Approximant.SpineSubspace.spineMap x (Pi.single j 1) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
          (Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N (Pi.single i 1) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) := rfl
  rw [h, Cvs.WeilForm.WindowOrthogonalComplement.inner_rep]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [(Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.Approximant.SpineSubspace.coe_spineMap_ae x hx (Pi.single j 1)),
    (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.Approximant.CosineColumnTailPairing.coe_modeClass_ae hx0 N (Pi.single i 1))] with s h1 h2
  rw [h1]; exact congrArg _ h2

/-- **The rung columns in closed form**: at `80 ≤ 2πx`, `Q(rung_j, modeMap f) = −weilθ(τ_j, modeTest f)`. -/
theorem Bx_rung_modeMap {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) (f : Idx N → ℝ) :
    Bx x (rung x j) (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)
      = -Cvs.WeilForm.ThetaSpaceParseval.weilθ (Cvs.WeilForm.CouplingPrimeForm.tail x (Pi.single j 1)) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) := by
  unfold Bx rung
  rw [← Cvs.Approximant.CosineColumnTailPairing.QWbil_modeMap_eq_evenPart (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)]
  exact Cvs.Approximant.SpineCouplingTailPairing.QWbil_spineMap_eq_neg_tail hx (Pi.single j 1)
    (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)

/-- The rung normals at order `N`: row `j` holds the normal coefficients of rung `j ≥ 2`. -/
def rungNormal (x N : ℕ) : Matrix (D0idx x) (Idx N) ℝ :=
  Matrix.of fun j i => Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (rung x j.1) (mode N) i

/-- The rung columns at order `N` in tail form: `X_{j i} = −weilθ(τ_j, modeTest e_i)` for `j ≥ 2`. -/
def rungTail (x N : ℕ) : Matrix (D0idx x) (Idx N) ℝ :=
  Matrix.of fun j i => -Cvs.WeilForm.ThetaSpaceParseval.weilθ (Cvs.WeilForm.CouplingPrimeForm.tail x (Pi.single j.1 1)) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Pi.single i 1))

/-- The form Gram of the rungs `j ≥ 2`: the `D0idx` block of `Cvs.L2a.EvenSectorReflectionBound.evenGram`. -/
def rungGram (x : ℕ) : Matrix (D0idx x) (D0idx x) ℝ :=
  (Cvs.L2a.EvenSectorReflectionBound.evenGram x).submatrix (fun j : D0idx x => j.1) (fun j => j.1)

/-- The matrix bulk floor at order `N`: `b f⬝f ≤ f⬝M_N f` for every even `f` with `rungNormal x N f = 0`. -/
def MatFloorN (x N : ℕ) (b : ℝ) : Prop :=
  ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → rungNormal x N *ᵥ f = 0 →
    b * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ f)

/-- The matrix bulk floor at `x`: `MatFloorN x N b` at every order `N`. -/
def MatFloor (x : ℕ) (b : ℝ) : Prop :=
  ∀ N, MatFloorN x N b

/-- The matrix coupling at `x` with the tail-form columns `X = rungTail x N` and `G = rungGram x`:
`(a⬝Xf)² ≤ (1−δ)(a⬝Ga)(log x·f⬝M_N f)` for every even `f` with `rungNormal x N f = 0`, every `N` and every `a`. -/
def MatCoupling (x : ℕ) (δ : ℝ) : Prop :=
  ∀ (a : D0idx x → ℝ) (N : ℕ) (f : Idx N → ℝ), (∀ i, f (negI N i) = f i) → rungNormal x N *ᵥ f = 0 →
    (a ⬝ᵥ (rungTail x N *ᵥ f)) ^ 2
      ≤ (1 - δ) * (a ⬝ᵥ (rungGram x *ᵥ a))
          * (Real.log x * (f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ f)))

/-- `modeMap f ⊥ D₀` iff `rungNormal x N f = 0`. -/
theorem modeMap_mem_orthogonal_D0_iff {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) (f : Idx N → ℝ) :
    Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f ∈ (D0 x)ᗮ ↔ rungNormal x N *ᵥ f = 0 := by
  rw [funext_iff]
  exact modeMap_mem_orthogonal_span_iff hx0 N f (fun j : D0idx x => rung x j.1)

/-- `Q(Σ a_j rung_j, modeMap f) = a ⬝ (rungTail f)` at `80 ≤ 2πx`. -/
theorem Bx_sum_rung_modeMap {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (a : D0idx x → ℝ) (f : Idx N → ℝ) :
    Bx x (∑ j, a j • rung x j.1) (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)
      = a ⬝ᵥ (rungTail x N *ᵥ f) := by
  rw [map_sum, LinearMap.sum_apply]
  unfold dotProduct
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  conv_lhs => rw [pi_eq_sum_univ' f]
  simp only [map_sum, map_smul, smul_eq_mul, Bx_rung_modeMap hx, rungTail, Matrix.mulVec, dotProduct,
    Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `Q(Σ a_j rung_j) = a ⬝ (rungGram a)`. -/
theorem Bx_sum_rung_self (x : ℕ) (a : D0idx x → ℝ) :
    Bx x (∑ j, a j • rung x j.1) (∑ j, a j • rung x j.1) = a ⬝ᵥ (rungGram x *ᵥ a) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, rungGram,
    Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Cvs.L2a.EvenSectorReflectionBound.evenGram_apply, Finset.mul_sum]
  have hs : ∀ u v : Dom x, Bx x u v = Bx x v u := fun u v => (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _).eq u v
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hs (rung x j.1)]; ring

/-- **The bulk floor against `D₀` is the matrix floor**, at `1 < x`. -/
theorem bulkFloor_iff_matFloor {x : ℕ} (hx1 : (1 : ℝ) < x) (b : ℝ) :
    Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (D0 x) b ↔ MatFloor x b := by
  rw [bulkFloor_iff_matrix hx1 (Cvs.Route.EvenWindowBulkCoupling.D0_le_Ev x) b]
  unfold MatFloor MatFloorN
  exact forall_congr' fun N => forall_congr' fun f => forall_congr' fun _ =>
    imp_congr_left (modeMap_mem_orthogonal_D0_iff _ N f)

/-- **The coupling against `D₀` is the matrix coupling**, at `80 ≤ 2πx`. -/
theorem coupling_iff_matCoupling {x : ℕ} (hx : 80 ≤ 2 * π * x) (δ : ℝ) :
    Cvs.Upstream.MergedBoundSchurForm.Coupling (Bx x) (Ev x) (D0 x) δ ↔ MatCoupling x δ := by
  rw [coupling_iff_matrix (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) (Cvs.Route.EvenWindowBulkCoupling.D0_le_Ev x) δ]
  constructor
  · intro h a N f hf hfD
    have := h (∑ j, a j • rung x j.1)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
      N f hf ((modeMap_mem_orthogonal_D0_iff _ N f).2 hfD)
    rwa [Bx_sum_rung_modeMap hx, Bx_sum_rung_self] at this
  · intro h r hr N f hf hfD
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hr
    have := h a N f hf ((modeMap_mem_orthogonal_D0_iff _ N f).1 hfD)
    rwa [← Bx_sum_rung_modeMap hx, ← Bx_sum_rung_self] at this

/-- **A positive floor and a coupling against `D₀` at infinitely many `x` is their matrix form**: `MatFloor x b`
and `MatCoupling x δ` with `b > 0`, `0 ≤ δ < 1` at infinitely many `x`. -/
theorem frequently_floor_coupling_D0_iff_matrix :
    (∃ᶠ x : ℕ in atTop, ∃ b δ : ℝ, 0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧
      Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (D0 x) b ∧ Cvs.Upstream.MergedBoundSchurForm.Coupling (Bx x) (Ev x) (D0 x) δ) ↔
    ∃ᶠ x : ℕ in atTop, ∃ b δ : ℝ, 0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧ MatFloor x b ∧ MatCoupling x δ := by
  have hev : ∀ᶠ x : ℕ in atTop, 80 ≤ 2 * π * x :=
    Cvs.Route.WindowPositivityBulkCoupling.eventually_c0W_le.mono fun _ h => Cvs.Approximant.SpineSubspace.scale80_of_c0W h
  constructor
  · intro h
    exact (h.and_eventually hev).mono fun x ⟨⟨b, δ, hb, hδ0, hδ1, hF, hC⟩, hx⟩ =>
      ⟨b, δ, hb, hδ0, hδ1, (bulkFloor_iff_matFloor (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) b).1 hF,
        (coupling_iff_matCoupling hx δ).1 hC⟩
  · intro h
    exact (h.and_eventually hev).mono fun x ⟨⟨b, δ, hb, hδ0, hδ1, hF, hC⟩, hx⟩ =>
      ⟨b, δ, hb, hδ0, hδ1, (bulkFloor_iff_matFloor (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) b).2 hF,
        (coupling_iff_matCoupling hx δ).2 hC⟩

/-! ### The collapse -/

/-- **At `x ≥ 2` a positive floor and a coupling against `D₀` is even window positivity plus a positive floor.** -/
theorem floor_coupling_D0_iff_evenPos_and_floor {x : ℕ} (hx : 2 ≤ x) :
    (∃ b δ : ℝ, 0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧
      Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (D0 x) b ∧ Cvs.Upstream.MergedBoundSchurForm.Coupling (Bx x) (Ev x) (D0 x) δ) ↔
    (∀ w ∈ Ev x, 0 ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x w) ∧ ∃ b : ℝ, 0 < b ∧ Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (D0 x) b := by
  constructor
  · rintro ⟨b, δ, hb, hδ0, hδ1, hF, hC⟩
    refine ⟨?_, b, hb, hF⟩
    obtain ⟨w, hwe, hw, hw0⟩ := Cvs.Route.EvenWindowBulkCoupling.exists_evenBulk_ne_zero hx
    have hwD : w ∈ (D0 x)ᗮ := Submodule.orthogonal_le (Cvs.L2a.EvenSectorReflectionBound.D0_le_R1 x) hw
    have hpos : 0 < Bx x w w :=
      (mul_pos hb (pow_pos (norm_pos_iff.2 hw0) 2)).trans_le (hF w hwe hwD)
    have hD := Cvs.Route.EvenWindowBulkCoupling.nonneg_on_of_coupling hδ1 hC hwe hwD hpos
    exact Cvs.Route.EvenWindowBulkCoupling.Q_nonneg_of_floor_coupling_sub (Cvs.Route.EvenWindowBulkCoupling.D0_le_Ev x)
      (fun r hr => by have := hD r hr; rwa [Cvs.WeilForm.CouplingFiniteSchur.Bx_self] at this) hb.le hδ0 hF hC
  · rintro ⟨hpos, b, hb, hF⟩
    exact ⟨b, 0, hb, le_rfl, one_pos, hF, coupling_zero_of_nonneg_on (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _)
      (Cvs.Route.EvenWindowBulkCoupling.D0_le_Ev x) fun v hv => by rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]; exact hpos v hv⟩

/-- **A positive floor and a coupling against `D₀` at infinitely many `x` is RH plus a positive floor against `D₀`
at infinitely many `x`.** -/
theorem frequently_floor_coupling_D0_iff_rh_and_floor :
    (∃ᶠ x : ℕ in atTop, ∃ b δ : ℝ, 0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧
      Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (D0 x) b ∧ Cvs.Upstream.MergedBoundSchurForm.Coupling (Bx x) (Ev x) (D0 x) δ) ↔
    RiemannHypothesis ∧
      ∃ᶠ x : ℕ in atTop, ∃ b : ℝ, 0 < b ∧ Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (D0 x) b := by
  constructor
  · intro h
    exact ⟨Cvs.Route.EvenWindowBulkCoupling.riemannHypothesis_of_floor_pos_coupling_D0 h,
      h.mono fun x ⟨b, _, hb, _, _, hF, _⟩ => ⟨b, hb, hF⟩⟩
  · rintro ⟨hRH, h⟩
    refine (h.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨hF, hx⟩ => ?_
    exact (floor_coupling_D0_iff_evenPos_and_floor hx).2 ⟨fun w _ => Cvs.Route.CoreSchurForm.nonneg_of_rh hRH x hx w, hF⟩

/-- **A positive floor and a coupling against `D₀` at infinitely many `x` is RH plus a positive matrix floor at
infinitely many `x`.** -/
theorem frequently_floor_coupling_D0_iff_rh_and_matFloor :
    (∃ᶠ x : ℕ in atTop, ∃ b δ : ℝ, 0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧
      Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (D0 x) b ∧ Cvs.Upstream.MergedBoundSchurForm.Coupling (Bx x) (Ev x) (D0 x) δ) ↔
    RiemannHypothesis ∧ ∃ᶠ x : ℕ in atTop, ∃ b : ℝ, 0 < b ∧ MatFloor x b := by
  rw [frequently_floor_coupling_D0_iff_rh_and_floor]
  have hev : ∀ᶠ x : ℕ in atTop, (1 : ℝ) < x :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 1
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · exact (h.and_eventually hev).mono fun x ⟨⟨b, hb, hF⟩, hx⟩ =>
      ⟨b, hb, (bulkFloor_iff_matFloor hx b).1 hF⟩
  · exact (h.and_eventually hev).mono fun x ⟨⟨b, hb, hF⟩, hx⟩ =>
      ⟨b, hb, (bulkFloor_iff_matFloor hx b).2 hF⟩

end Cvs.Finite.EvenBulkModeMatrices
