import Mathlib
import Cvs.Approximant.ConnesErrorColumn
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.ResidualSymbolVariance
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapFromResidual
import Cvs.WeilForm.EvenBoundaryKernelBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The asymmetric interval bound for the actual boundary variance

The positive archimedean boundary and the signed prime boundary give an asymmetric
interval for the full boundary operator on even modes.
-/

noncomputable section

open Real Matrix Finset

namespace Cvs.Approximant.BoundaryVarianceInterval
open Cvs.ZeroCounting

section Variance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_center_sq (w v : E) (hv : ‖v‖ = 1) :
    ‖w - (inner ℝ w v) • v‖ ^ 2 = ‖w‖ ^ 2 - (inner ℝ w v) ^ 2 := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    sq_abs, hv, mul_one, real_inner_smul_right]
  ring

/-- A selfadjoint quadratic interval controls the centered energy at every unit vector. -/
theorem centered_variance_le (T : E →L[ℝ] E) (hT : T.IsSymmetric) (a b : ℝ)
    (hlo : ∀ w : E, a * ‖w‖ ^ 2 ≤ inner ℝ (T w) w)
    (hhi : ∀ w : E, inner ℝ (T w) w ≤ b * ‖w‖ ^ 2)
    (v : E) (hv : ‖v‖ = 1) :
    ‖T v - (inner ℝ (T v) v) • v‖ ^ 2 ≤
      (b - inner ℝ (T v) v) * (inner ℝ (T v) v - a) := by
  let c : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  let S : E →L[ℝ] E := T - c • ContinuousLinearMap.id ℝ E
  have hab : a ≤ b := by
    have hl := hlo v
    have hh := hhi v
    rw [hv, one_pow, mul_one] at hl hh
    exact hl.trans hh
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hS : S.IsSymmetric := by
    change (T.toLinearMap - c • LinearMap.id).IsSymmetric
    exact hT.sub (LinearMap.IsSymmetric.id.smul (by rfl))
  have hquad (w : E) : |inner ℝ (S w) w| ≤ r * ‖w‖ ^ 2 := by
    simp only [S, _root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    rw [abs_le]
    dsimp [c, r]
    constructor <;> nlinarith [hlo w, hhi w]
  have hnorm : ‖S‖ ≤ r := by
    rw [S.norm_eq_iSup_rayleighQuotient hS]
    apply ciSup_le
    intro w
    by_cases hw : w = 0
    · simp only [hw, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]
      exact hr
    · have hwpos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
      change |inner ℝ (S w) w / ‖w‖ ^ 2| ≤ r
      rw [abs_div, abs_of_pos hwpos, div_le_iff₀ hwpos]
      exact hquad w
  have happ : ‖S v‖ ≤ r := by
    have h := S.le_opNorm v
    rw [hv, mul_one] at h
    exact h.trans hnorm
  have hsquare : ‖S v‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) happ 2
  have hs : ‖S v‖ ^ 2 = ‖T v‖ ^ 2 - 2 * c * inner ℝ (T v) v + c ^ 2 := by
    simp only [S, _root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      sq_abs, hv, mul_one, real_inner_smul_right]
    ring
  have hc : ‖T v - (inner ℝ (T v) v) • v‖ ^ 2 =
      ‖T v‖ ^ 2 - (inner ℝ (T v) v) ^ 2 := norm_center_sq _ _ hv
  rw [hs] at hsquare
  rw [hc]
  dsimp [c, r] at hsquare
  nlinarith

end Variance

section Boundary

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The actual archimedean boundary form is nonnegative on even signed modes. -/
theorem arch_boundary_nonneg {L : ℝ} (hL : 0 < L) (N : ℕ) (v : Idx N → ℝ)
    (hv : ∀ i, v (negI N i) = v i) :
    0 ≤ ∑ i, ∑ j, v i * v j *
      (Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * (mode N i : ℝ) / L)
        (2 * π * (mode N j : ℝ) / L) / L) := by
  have heq : (∑ i, ∑ j, v i * v j *
      (Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * (mode N i : ℝ) / L)
        (2 * π * (mode N j : ℝ) / L) / L)) =
      Cvs.WeilForm.EvenBoundaryKernelBound.archQuad L (Cvs.WeilForm.EvenBoundaryKernelBound.positiveMode N) (v none)
        (fun k => v (some (k, true))) := by
    simp_rw [← mul_div_assoc, ← Finset.sum_div]
    rw [Cvs.Finite.WindowMatrixSymbolKernel.quadForm_kArch hL, Cvs.WeilForm.EvenBoundaryKernelBound.archQuad_eq hL]
    simp only [Cvs.WeilForm.EvenBoundaryKernelBound.idx_sum_uu L _ N v hv, Cvs.WeilForm.EvenBoundaryKernelBound.idx_sum_vv L _ N v hv,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
    unfold Cvs.WeilForm.EvenBoundaryKernelBound.evenLadderQuad Cvs.WeilForm.EvenBoundaryKernelBound.weight
    ring
  rw [heq]
  exact Cvs.WeilForm.EvenBoundaryKernelBound.archQuad_nonneg hL _ _ _

/-- The actual boundary quadratic form lies between the prime lower budget and the full upper budget. -/
theorem boundary_quadratic_interval {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (v : Idx N → ℝ) (hv : ∀ i, v (negI N i) = v i) :
    -(Cvs.WeilForm.EvenBoundaryKernelBound.primeBudget P R) * (v ⬝ᵥ v) ≤
      v ⬝ᵥ (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v) ∧
    v ⬝ᵥ (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v) ≤
      Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R L * (v ⬝ᵥ v) := by
  let qa : ℝ := ∑ i, ∑ j, v i * v j *
    (Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * (mode N i : ℝ) / L)
      (2 * π * (mode N j : ℝ) / L) / L)
  let qp : ℝ := ∑ i, ∑ j, v i * v j *
    (Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L (2 * π * (mode N i : ℝ) / L)
      (2 * π * (mode N j : ℝ) / L) / L)
  have hqa : 0 ≤ qa := arch_boundary_nonneg hL N v hv
  have ha := Cvs.WeilForm.EvenBoundaryKernelBound.idx_arch_kernel_bound hL N v hv
  have hp := Cvs.WeilForm.EvenBoundaryKernelBound.idx_prime_kernel_bound hL P R N v hv
  change |qa| ≤ Cvs.WeilForm.EvenBoundaryKernelBound.archBudget L * (∑ i, v i ^ 2) at ha
  change |qp| ≤ Cvs.WeilForm.EvenBoundaryKernelBound.primeBudget P R * (∑ i, v i ^ 2) at hp
  have hm : ∑ i, v i ^ 2 = v ⬝ᵥ v := by simp only [dotProduct, sq]
  rw [hm, abs_of_nonneg hqa] at ha
  rw [hm, abs_le] at hp
  have heq : v ⬝ᵥ (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v) = qa + qp := by
    simp only [dotProduct, Matrix.mulVec, Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix, Cvs.Finite.WindowMatrixSymbolKernel.kK,
      add_div, add_mul, mul_add, Finset.mul_sum, Finset.sum_add_distrib, qa, qp]
    congr 1 <;>
      (apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring)
  rw [heq]
  unfold Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget
  constructor <;> nlinarith

/-- The full arithmetic boundary operator restricted to the actual even coefficient space. -/
def boundaryEven (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    Cvs.Route.GroundRouteJointGap.evenSub N →ₗ[ℝ] Cvs.Route.GroundRouteJointGap.evenSub N :=
  (Matrix.toEuclideanLin (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N)).restrict fun _ hv i =>
    Cvs.Approximant.ResidualSymbolVariance.boundary_column_even hL P R N _ hv i

/-- Restriction to even coefficients preserves the actual boundary matrix action. -/
theorem ofLp_boundaryEven (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ)
    (f : Cvs.Route.GroundRouteJointGap.evenSub N) :
    WithLp.ofLp ((boundaryEven P R hL N f : Cvs.Route.GroundRouteJointGap.evenSub N) :
      EuclideanSpace ℝ (Idx N)) =
      Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ
        WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)) := rfl

/-- The actual restricted boundary operator is symmetric. -/
theorem isSymmetric_boundaryEven (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (boundaryEven P R hL N).IsSymmetric :=
  LinearMap.IsSymmetric.restrict_invariant
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.IsHermitian.ext fun i j => by
      simp [Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix_symm hL P R N j i])) _

/-- The actual even boundary operator obeys its asymmetric quadratic interval. -/
theorem boundaryEven_interval (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ)
    (f : Cvs.Route.GroundRouteJointGap.evenSub N) :
    -(Cvs.WeilForm.EvenBoundaryKernelBound.primeBudget P R) * ‖f‖ ^ 2 ≤ inner ℝ (boundaryEven P R hL N f) f ∧
    inner ℝ (boundaryEven P R hL N f) f ≤ Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R L * ‖f‖ ^ 2 := by
  rw [Cvs.Route.GroundRouteJointGap.norm_sq_evenSub, Cvs.Route.GroundRouteJointGap.inner_evenSub, ofLp_boundaryEven]
  rw [dotProduct_comm (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ _)]
  exact boundary_quadratic_interval hL P R N _ f.property

/-- The centered actual boundary column satisfies the variance bound from its asymmetric interval. -/
theorem boundary_centered_sq_le {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (v : Idx N → ℝ) (hve : ∀ i, v (negI N i) = v i) (hv : v ⬝ᵥ v = 1) :
    let β := Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v
    Cvs.Approximant.ConnesErrorColumn.center β v ⬝ᵥ Cvs.Approximant.ConnesErrorColumn.center β v ≤
      (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R L - β ⬝ᵥ v) * (β ⬝ᵥ v + Cvs.WeilForm.EvenBoundaryKernelBound.primeBudget P R) := by
  let v' : Cvs.Route.GroundRouteJointGap.evenSub N := ⟨WithLp.toLp 2 v, hve⟩
  let T : Cvs.Route.GroundRouteJointGap.evenSub N →L[ℝ] Cvs.Route.GroundRouteJointGap.evenSub N :=
    (boundaryEven P R hL N).toContinuousLinearMap
  let β := Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v
  have hvnorm : ‖v'‖ = 1 := by
    have hs : ‖v'‖ ^ 2 = 1 := by
      rw [Cvs.Route.GroundRouteJointGap.norm_sq_evenSub]
      exact hv
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (by simpa using hs)
  have hκ : inner ℝ (T v') v' = β ⬝ᵥ v := by
    change inner ℝ (boundaryEven P R hL N v') v' = _
    rw [Cvs.Route.GroundRouteJointGap.inner_evenSub, ofLp_boundaryEven]
  have hβ : ‖T v'‖ ^ 2 = β ⬝ᵥ β := by
    change ‖boundaryEven P R hL N v'‖ ^ 2 = _
    rw [Cvs.Route.GroundRouteJointGap.norm_sq_evenSub, ofLp_boundaryEven]
  have hc : ‖T v' - (inner ℝ (T v') v') • v'‖ ^ 2 =
      β ⬝ᵥ β - (β ⬝ᵥ v) ^ 2 := by
    rw [norm_center_sq _ _ hvnorm, hκ, hβ]
  have h := centered_variance_le T (isSymmetric_boundaryEven P R hL N)
    (-(Cvs.WeilForm.EvenBoundaryKernelBound.primeBudget P R)) (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R L)
    (fun f => (boundaryEven_interval P R hL N f).1)
    (fun f => (boundaryEven_interval P R hL N f).2) v' hvnorm
  rw [hc, hκ, sub_neg_eq_add] at h
  dsimp only
  rw [Cvs.Approximant.ResidualSymbolVariance.center_sq_unit β v hv]
  exact h

/-- The actual residual budget retains symbol variance and signed covariance with the sharper boundary interval. -/
theorem residual_le_asymmetric_variance {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (v : Idx N → ℝ) (hve : ∀ i, v (negI N i) = v i) (hv : v ⬝ᵥ v = 1) :
    let d := Cvs.Approximant.ResidualSymbolVariance.symbolCoefficients P R L N
    let β := Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ v
    Cvs.Route.JointGapFromResidual.residualSq P R L N v ≤
      Cvs.Approximant.ResidualSymbolVariance.symbolVariance d v +
        (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R L - β ⬝ᵥ v) * (β ⬝ᵥ v + Cvs.WeilForm.EvenBoundaryKernelBound.primeBudget P R)
        + 2 * Cvs.Approximant.ResidualSymbolVariance.signedCovariance d v β := by
  dsimp only
  have h := boundary_centered_sq_le hL P R N v hve hv
  dsimp only at h
  rw [Cvs.Approximant.ResidualSymbolVariance.center_sq_unit _ v hv] at h
  rw [Cvs.Approximant.ResidualSymbolVariance.residual_eq_variance_covariance hL P R N v hv]
  linarith

/-- The asymmetric variance budget applies to the actual Connes trial at every positive window. -/
theorem connes_residual_le_asymmetric_variance {x : ℝ} (hx : 1 < x) (P R N : ℕ) :
    let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
    let d := Cvs.Approximant.ResidualSymbolVariance.symbolCoefficients P R (Real.log x) N
    let β := Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R (Real.log x) N *ᵥ v
    Cvs.Route.JointGapFromResidual.residualSq P R (Real.log x) N v ≤
      Cvs.Approximant.ResidualSymbolVariance.symbolVariance d v +
        (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R (Real.log x) - β ⬝ᵥ v) *
          (β ⬝ᵥ v + Cvs.WeilForm.EvenBoundaryKernelBound.primeBudget P R)
        + 2 * Cvs.Approximant.ResidualSymbolVariance.signedCovariance d v β :=
  residual_le_asymmetric_variance (Real.log_pos hx) P R N _
    (Cvs.Approximant.ConnesVectorRealScale.connesVec_even (fun _ => N) x)
    (Cvs.Approximant.ConnesVectorRealScale.connesVec_dotProduct_self (fun _ => N) x)

end Boundary

end Cvs.Approximant.BoundaryVarianceInterval
