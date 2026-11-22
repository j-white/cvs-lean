import Mathlib
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.ModeSumsToMinimiser
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.SchurFloorJointGap
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowReflectionSymmetry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A continuous even hyperplane floor compresses exactly to every mode order

The continuous normal pairs with cosine coefficients through an explicit finite vector, and the
identities `Q(modeSum f) = L f⬝Mf` and `‖modeSum f‖² = L f⬝f` preserve its hyperplane floor.
-/

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace Cvs.Route.EvenHyperplaneFloorCompress
open Cvs.ZeroCounting

open Cvs.Finite.DiscreteTwoGap (ell)

section modes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pairing a continuous window class with cosine coefficients is a real linear functional. -/
def ellMap {L : ℝ} (hL : 0 ≤ L) (η : Cvs.WeilForm.FormDomain.formDomain hL)
    (md : ι → ℤ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := ell hL η md
  map_add' := fun f g => by
    have h := Cvs.Finite.DiscreteTwoGap.ell_sub hL η md (f + g) g
    rw [add_sub_cancel_right] at h
    linarith
  map_smul' := fun c f => by
    simpa only [smul_eq_mul, RingHom.id_apply] using
      Cvs.Finite.DiscreteTwoGap.ell_smul hL η md c f

/-- The coefficient normal is the pairing with each coordinate cosine. -/
def normalCoeff {L : ℝ} (hL : 0 ≤ L) (η : Cvs.WeilForm.FormDomain.formDomain hL)
    (md : ι → ℤ) : ι → ℝ := fun i => ell hL η md (Pi.single i 1)

/-- The continuous normal pairing is exactly the dot product with its coefficient normal. -/
theorem ell_eq_dotProduct {L : ℝ} (hL : 0 ≤ L) (η : Cvs.WeilForm.FormDomain.formDomain hL)
    (md : ι → ℤ) (f : ι → ℝ) : ell hL η md f = normalCoeff hL η md ⬝ᵥ f := by
  calc ell hL η md f = ellMap hL η md f := rfl
    _ = ellMap hL η md (∑ i, f i • Pi.single i 1) :=
      congrArg (ellMap hL η md) (pi_eq_sum_univ' f)
    _ = ∑ i, f i * normalCoeff hL η md i := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      rfl
    _ = normalCoeff hL η md ⬝ᵥ f := by
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- A floor on the continuous even hyperplane gives the same floor on every symmetric mode family. -/
theorem matrix_floor_of_continuous_even_hyperplane {L μ : ℝ} (hL : 0 < L) (P R : ℕ)
    (η : Cvs.WeilForm.FormDomain.formDomain hL.le)
    (hfloor : ∀ φ : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le φ = φ → ⟪η, φ⟫_ℝ = 0 →
        μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R φ)
    (md : ι → ℤ) (hmd : Function.Injective md) (neg : ι → ι)
    (hinv : Function.Involutive neg) (hneg : ∀ i, md (neg i) = -md i)
    (f : ι → ℝ) (hfe : ∀ i, f (neg i) = f i)
    (hfη : normalCoeff hL.le η md ⬝ᵥ f = 0) :
    μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L md *ᵥ f) := by
  by_cases hf0 : f = 0
  · subst f
    simp
  obtain ⟨t, ht0, ht⟩ := Cvs.Finite.DiscreteTwoGap.normalise hL hf0
  let g : ι → ℝ := t • f
  have hge : ∀ i, g (neg i) = g i := by
    intro i
    simp only [g, Pi.smul_apply, hfe]
  have hg1 : L * (g ⬝ᵥ g) = 1 := by
    dsimp only [g]
    rw [Cvs.Finite.DiscreteTwoGap.dot_smul_self]
    nlinarith [ht]
  have hg := Cvs.Finite.ModeSumFormDomain.modeSum_mem_evenWindowSet hL hmd hinv hneg hge hg1
  let φ := Cvs.Limit.ModeSumsToMinimiser.toDomain hL.le hg.1
  have hφη : ⟪η, φ⟫_ℝ = 0 := by
    rw [Cvs.Finite.DiscreteTwoGap.inner_toDomain_eq_ell]
    dsimp only [g]
    rw [Cvs.Finite.DiscreteTwoGap.ell_smul, ell_eq_dotProduct, hfη, mul_zero]
  have h := hfloor φ (Cvs.Limit.ModeSumsToMinimiser.reflD_toDomain hL.le hg) hφη
  rw [Cvs.Limit.ModeSumsToMinimiser.norm_toDomain, one_pow, mul_one,
    Cvs.Limit.ModeSumsToMinimiser.Q_toDomain,
    Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix hL P R hmd hinv hneg hge] at h
  change μ ≤ L * (g ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L md *ᵥ g)) at h
  dsimp only [g] at h
  rw [Cvs.Finite.DiscreteTwoGap.quad_smul] at h
  have htL : 0 < L * t ^ 2 := mul_pos hL (sq_pos_of_ne_zero ht0)
  have hscaled : (L * t ^ 2) * (μ * (f ⬝ᵥ f))
      ≤ (L * t ^ 2) * (f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L md *ᵥ f)) := by
    have hn : (L * t ^ 2) * (f ⬝ᵥ f) = 1 := by nlinarith [ht]
    calc (L * t ^ 2) * (μ * (f ⬝ᵥ f)) = μ := by
          calc (L * t ^ 2) * (μ * (f ⬝ᵥ f))
              = μ * ((L * t ^ 2) * (f ⬝ᵥ f)) := by ring
            _ = μ := by rw [hn, mul_one]
      _ ≤ (L * t ^ 2) * (f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L md *ᵥ f)) := by
          nlinarith [h]
  exact le_of_mul_le_mul_left hscaled htL

end modes

/-- A continuous even hyperplane floor and a bottom-loss budget give `JointGap` at every mode order. -/
theorem jointGap_of_continuous_even_hyperplane {P R N : ℕ} {L K C ε μ : ℝ}
    (hL : 0 < L) (hK : 1 ≤ K) (η : Cvs.WeilForm.FormDomain.formDomain hL.le)
    (hfloor : ∀ φ : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le φ = φ → ⟪η, φ⟫_ℝ = 0 →
        μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R φ)
    (v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ)
    (hve : ∀ i, v (Cvs.Finite.SymmetricModeSet.negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hceil : v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ v) ≤ C)
    (hlower : -ε ≤ Cvs.Limit.SpineWithoutSimplicity.groundLam P R L hL N) (hCμ : C < μ)
    (hbudget : K * C + (K - 1) * ε ≤ μ) : Cvs.Route.GroundRouteJointGap.JointGap P R L N K v := by
  refine Cvs.Route.SchurFloorJointGap.jointGap_of_floor_lower_bound hL hK v
    (normalCoeff hL.le η (Cvs.Finite.SymmetricModeSet.mode N)) hve hv1 ?_ hceil hlower hCμ hbudget
  intro f hfe hfη
  exact matrix_floor_of_continuous_even_hyperplane hL P R η hfloor
    (Cvs.Finite.SymmetricModeSet.mode N) (Cvs.Finite.SymmetricModeSet.mode_injective N)
    (Cvs.Finite.SymmetricModeSet.negI N) (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.SymmetricModeSet.mode_negI N) f hfe hfη

end Cvs.Route.EvenHyperplaneFloorCompress
