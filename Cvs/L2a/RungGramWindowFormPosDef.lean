import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCoefficientMatrix
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.RungSpanLowEnergy
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.BulkSchurIdentity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowGramDeterminantRatio
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Gram matrix of the window form on the windowed prolate rungs is positive definite

The rungs `e_j = spineMap x (δ_j)`, `j ∈ SF x = [1, x)`, are the `k_G` classes of the windowed profiles
`h_{4j} − α_j h₀` at `c = 2πx`; they span `R_F`, with `QWbil` Gram `G = spineGram x`, `L²` Gram `N = normGram x`.
At `80 ≤ 2πx`, `aᵀ G a = W_x(window(G_a))`, `G_a = Σ_j a_j(h_{4j} − α_j h₀)`, and the rungs are linearly
independent; at `c₀W ≤ 2πx`, `G − b_R(x)·N ⪰ 0` and `G ≻ 0`.
-/

noncomputable section

open Real Matrix

namespace Cvs.L2a.RungGramWindowFormPosDef
open Cvs.ZeroCounting

open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.WeilForm.BulkSchurIdentity (gram)
open Cvs.WeilForm.WindowGramDeterminantRatio (QW)
open Cvs.L2a.WindowChainInputsProlate (c0W)

/-- The windowed prolate rungs at scale `x`: `e_j = spineMap x (δ_j)`, `j ∈ SF x`. -/
def rungs (x : ℕ) : Cvs.Approximant.SpineSubspace.SF x → Dom x := fun j => Cvs.Approximant.SpineSubspace.spineMap x (Pi.single j 1)

/-- Each rung lies in `R_F`. -/
theorem rungs_mem_RF (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : rungs x j ∈ Cvs.Approximant.SpineSubspace.RF x :=
  LinearMap.mem_range_self _ _

/-- The rungs span `R_F`. -/
theorem span_rungs (x : ℕ) : Submodule.span ℝ (Set.range (rungs x)) = Cvs.Approximant.SpineSubspace.RF x :=
  (Cvs.Approximant.SpineSubspace.RF_eq_span x).symm

/-- `Σ_j a_j e_j = spineMap x a`. -/
theorem sum_smul_rungs (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ∑ j, a j • rungs x j = Cvs.Approximant.SpineSubspace.spineMap x a := by
  conv_rhs => rw [← Cvs.Approximant.SpineCoefficientMatrix.sum_single x a]
  simp only [map_sum, map_smul, rungs]

/-- **The rung Gram matrix of `QWbil` is the spine Gram matrix.** -/
theorem gram_rungs (x : ℕ) : gram (QW x) (rungs x) = Cvs.Approximant.SpineCoefficientMatrix.spineGram x := rfl

/-- The rung Gram matrix is symmetric. -/
theorem gram_rungs_isHermitian (x : ℕ) : (gram (QW x) (rungs x)).IsHermitian :=
  Cvs.Approximant.SpineCoefficientMatrix.spineGram_isHermitian x

/-- `aᵀ G a = Q(Σ_j a_j e_j)`. -/
theorem dot_gram_rungs (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    a ⬝ᵥ (gram (QW x) (rungs x) *ᵥ a)
      = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a) :=
  Cvs.Approximant.SpineCoefficientMatrix.quad_spineGram x a

/-- **The rung Gram matrix in prolate coordinates**: at `80 ≤ 2πx`,
`aᵀ G a = W_x(log-scaled window(2π/(2πx))(G_a))` with `G_a = Σ_j a_j(h_{4j} − α_j h₀)` at `c = 2πx`. -/
theorem dot_gram_rungs_eq_weilForm {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    a ⬝ᵥ (gram (QW x) (rungs x) *ᵥ a)
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x)
          (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))) := by
  rw [dot_gram_rungs, Cvs.Approximant.SpineSubspace.Q_spineMap x hx]

/-- The `L²` Gram matrix of the rungs is `normGram x`. -/
theorem gram_inner_rungs (x : ℕ) : gram (innerₗ (Dom x)) (rungs x) = Cvs.L2a.RungSpanLowEnergy.normGram x := rfl

/-- `aᵀ N a = ‖Σ_j a_j e_j‖²` for `N` the `L²` Gram matrix of the rungs. -/
theorem dot_gram_inner_rungs (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    a ⬝ᵥ (gram (innerₗ (Dom x)) (rungs x) *ᵥ a) = ‖Cvs.Approximant.SpineSubspace.spineMap x a‖ ^ 2 := by
  rw [gram_inner_rungs]; exact Cvs.L2a.RungSpanLowEnergy.quad_normGram x a

/-- **The rungs are linearly independent** at `80 ≤ 2πx`. -/
theorem linearIndependent_rungs {x : ℕ} (hx : 80 ≤ 2 * π * x) : LinearIndependent ℝ (rungs x) := by
  have e : rungs x = Cvs.Approximant.SpineSubspace.spineMap x ∘ Pi.basisFun ℝ (Cvs.Approximant.SpineSubspace.SF x) := by
    funext j; simp [rungs, Pi.basisFun_apply]
  rw [e]
  exact (Pi.basisFun ℝ (Cvs.Approximant.SpineSubspace.SF x)).linearIndependent.map' (Cvs.Approximant.SpineSubspace.spineMap x)
    (LinearMap.ker_eq_bot.mpr (Cvs.Approximant.SpineCoefficientMatrix.spineMap_injective hx))

/-- **The L2a floor on the rung Gram matrix**: at `c₀W ≤ 2πx`, `G − b_R(x)·N` is positive semidefinite,
`G` the `QWbil` and `N` the `L²` Gram matrix of the rungs. -/
theorem gram_rungs_sub_posSemidef {x : ℕ} (hx : c0W ≤ 2 * π * x) :
    (gram (QW x) (rungs x) - Cvs.L2a.EvenSectorReflectionBound.bR x • gram (innerₗ (Dom x)) (rungs x)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun a => ?_
  · refine (gram_rungs_isHermitian x).sub (IsHermitian.smul ?_ (IsSelfAdjoint.all _))
    exact Cvs.WeilForm.BulkSchurIdentity.gram_isHermitian ⟨fun u v => real_inner_comm v u⟩ _
  · rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul,
      dot_gram_rungs, dot_gram_inner_rungs, sub_nonneg]
    exact Cvs.L2a.EvenSectorReflectionBound.spine_floor_R1 x hx a

/-- **The rung Gram matrix of the window form is positive definite** at `c₀W ≤ 2πx`. -/
theorem gram_rungs_posDef {x : ℕ} (hx : c0W ≤ 2 * π * x) : (gram (QW x) (rungs x)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (gram_rungs_isHermitian x) fun a ha => ?_
  rw [star_trivial, dot_gram_rungs]
  exact Cvs.Approximant.SpineSubspace.RF_pos x hx _ (LinearMap.mem_range_self _ _)
    fun h => ha (Cvs.Approximant.SpineCoefficientMatrix.spineMap_injective (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx) (h.trans (map_zero _).symm))

/-- The determinant of the rung Gram matrix is a unit at `c₀W ≤ 2πx`. -/
theorem isUnit_det_gram_rungs {x : ℕ} (hx : c0W ≤ 2 * π * x) : IsUnit (gram (QW x) (rungs x)).det :=
  (gram_rungs_posDef hx).det_pos.ne'.isUnit

end Cvs.L2a.RungGramWindowFormPosDef
