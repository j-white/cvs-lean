import Mathlib
import Cvs.Approximant.ConnesCoefficientsNonvanishing
import Cvs.Approximant.ConnesLowModeGeometry
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.ArchGreenSecondChannel
import Cvs.WeilForm.PrimeMomentVolterra
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.PrimePowerReindex
import Cvs.WeilForm.PrimeSideSharedWeights
import Cvs.WeilForm.TwoModeLowHeadDamping
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Connes endpoint geometry and mixed signed cosine entries

The actual Connes hyperplane splits into its endpoint trace and a flat residual;
mixed cosine overlaps give exact finite prime-minus-mean Volterra entries.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Real Set MeasureTheory Matrix Finset Filter
open scoped Topology
namespace Cvs.Approximant.ConnesEndpointGeometry
open Cvs.ZeroCounting
open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The common endpoint trace of an uncut signed cosine sum. -/
def endpoint (N : ℕ) (ξ : Idx N → ℝ) : ℝ := ∑ i, ξ i

/-- The actual normalized first-two-mode Connes-perpendicular direction. -/
def anchor (x : ℝ) (N : ℕ) : Idx N → ℝ :=
  Cvs.WeilForm.TwoModeLowHeadDamping.twoMode N (-(Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0))) (1/2)

/-- The scalar carrying the endpoint value along the actual two-mode direction. -/
def endpointScale (x : ℝ) (N : ℕ) (ξ : Idx N → ℝ) : ℝ :=
  endpoint N ξ/(1-Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0))

/-- The residual after removing the endpoint contribution of the two-mode direction. -/
def endpointResidual (x : ℝ) (N : ℕ) (ξ : Idx N → ℝ) : Idx N → ℝ :=
  ξ-endpointScale x N ξ • anchor x N

theorem cosineSum_zero (L : ℝ) (N : ℕ) (ξ : Idx N → ℝ) :
    Cvs.Approximant.CosineColumnTailPairing.cosineSum L N ξ 0=endpoint N ξ := by
  simp [Cvs.Approximant.CosineColumnTailPairing.cosineSum,endpoint]

theorem cosineSum_end {L : ℝ} (hL : 0<L) (N : ℕ) (ξ : Idx N → ℝ) :
    Cvs.Approximant.CosineColumnTailPairing.cosineSum L N ξ L=endpoint N ξ := by
  unfold Cvs.Approximant.CosineColumnTailPairing.cosineSum endpoint
  apply Finset.sum_congr rfl
  intro i _
  have he : Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i*L=(mode N i : ℝ)*(2*π) := by
    unfold Cvs.Finite.TruncationZeroFreeOffAxes.omega
    field_simp
  rw [he,Real.cos_int_mul_two_pi,mul_one]

theorem anchor_even (x : ℝ) (N : ℕ) (i : Idx N) :
    anchor x N (negI N i)=anchor x N i := Cvs.WeilForm.TwoModeLowHeadDamping.twoMode_even _ _ _ _

theorem anchor_orthogonal (x : ℝ) {N : ℕ} (hN : 0<N)
    (h0 : Cvs.Approximant.ConnesLowModeGeometry.coef x 0≠0) : anchor x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N=0 :=
  Cvs.Approximant.ConnesLowModeGeometry.perpendicular_coeff_orthogonal x hN h0

theorem anchor_endpoint (x : ℝ) {N : ℕ} (hN : 0<N) :
    endpoint N (anchor x N)=1-Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0) := by
  have h := Cvs.WeilForm.TwoModeLowHeadDamping.twoMode_pair hN (-(Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)))
    (1/2) (fun _ => (1 : ℝ))
  have hh : endpoint N (anchor x N)=
      -(Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0))+(1/2)*(1+1) := by
    simpa [dotProduct,endpoint,anchor] using h
  linarith

theorem endpoint_decomposition (x : ℝ) (N : ℕ) (ξ : Idx N → ℝ) :
    ξ=endpointScale x N ξ • anchor x N+endpointResidual x N ξ := by
  simp only [endpointResidual,add_sub_cancel]

theorem endpointResidual_even (x : ℝ) (N : ℕ) (ξ : Idx N → ℝ)
    (hξ : ∀ i,ξ (negI N i)=ξ i) (i : Idx N) :
    endpointResidual x N ξ (negI N i)=endpointResidual x N ξ i := by
  simp only [endpointResidual,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    hξ i,anchor_even]

theorem endpointResidual_orthogonal (x : ℝ) {N : ℕ} (hN : 0<N)
    (h0 : Cvs.Approximant.ConnesLowModeGeometry.coef x 0≠0) (ξ : Idx N → ℝ)
    (hξ : ξ ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N=0) :
    endpointResidual x N ξ ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N=0 := by
  rw [endpointResidual,sub_dotProduct,smul_dotProduct,anchor_orthogonal x hN h0,hξ]
  simp

theorem endpointResidual_flat (x : ℝ) {N : ℕ} (hN : 0<N)
    (he : 1-Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)≠0) (ξ : Idx N → ℝ) :
    endpoint N (endpointResidual x N ξ)=0 := by
  simp only [endpointResidual,endpoint,Pi.sub_apply,Finset.sum_sub_distrib,
    Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]
  change endpoint N ξ-endpointScale x N ξ*endpoint N (anchor x N)=0
  rw [anchor_endpoint x hN,endpointScale,div_mul_cancel₀ _ he,sub_self]

/-- The actual even Connes hyperplane splits into the two-mode direction and an endpoint-flat part. -/
theorem connes_hyperplane_decomposition (x : ℝ) {N : ℕ} (hN : 0<N)
    (h0 : Cvs.Approximant.ConnesLowModeGeometry.coef x 0≠0) (he : 1-Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)≠0)
    (ξ : Idx N → ℝ) (hξ : ∀ i,ξ (negI N i)=ξ i)
    (hp : ξ ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N=0) :
    ∃ t : ℝ, ∃ w : Idx N → ℝ, (∀ i,w (negI N i)=w i) ∧
      w ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N=0 ∧ endpoint N w=0 ∧ ξ=t • anchor x N+w := by
  exact ⟨endpointScale x N ξ,endpointResidual x N ξ,
    endpointResidual_even x N ξ hξ,endpointResidual_orthogonal x hN h0 ξ hp,
    endpointResidual_flat x hN he ξ,endpoint_decomposition x N ξ⟩

/-- The full matrix energy retains the signed coupling to the endpoint-flat residual. -/
theorem energy_endpoint_decomposition {L : ℝ} (hL : 0<L) (P R N : ℕ)
    (x : ℝ) (ξ : Idx N → ℝ) :
    ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ ξ)=
      (endpointScale x N ξ)^2*(anchor x N ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ anchor x N))+
      2*endpointScale x N ξ*(anchor x N ⬝ᵥ
        (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ endpointResidual x N ξ))+
      endpointResidual x N ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ endpointResidual x N ξ) := by
  have hs := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm (Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N))
    (endpointResidual x N ξ) (anchor x N)
  conv_lhs => rw [endpoint_decomposition x N ξ]
  simp only [Matrix.mulVec_add,Matrix.mulVec_smul,add_dotProduct,dotProduct_add,
    smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [hs]
  ring

/-- Completing the actual two-mode energy retains the signed endpoint-flat Schur term. -/
theorem energy_endpoint_completed_square {L : ℝ} (hL : 0<L) (P R N : ℕ)
    (x : ℝ) (ξ : Idx N → ℝ)
    (hq : anchor x N ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ anchor x N)≠0) :
    let q := anchor x N ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ anchor x N)
    let b := anchor x N ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ endpointResidual x N ξ)
    ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ ξ)=
      q*(endpointScale x N ξ+b/q)^2+
      endpointResidual x N ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ endpointResidual x N ξ)-b^2/q := by
  dsimp only
  rw [energy_endpoint_decomposition hL]
  field_simp
  ring

/-- Both scalar divisions in the endpoint decomposition are eventually nondegenerate. -/
theorem eventually_endpoint_decomposition_parameters :
    ∀ᶠ x : ℝ in atTop, Cvs.Approximant.ConnesLowModeGeometry.coef x 0≠0 ∧
      1-Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)≠0 := by
  filter_upwards [Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_connes_constantCoef_ne_zero,
    Cvs.Approximant.ConnesLowModeGeometry.tendsto_perpendicular_endpoint.eventually
      (lt_mem_nhds (by norm_num : (0 : ℝ)<2))] with x h0 he
  exact ⟨h0,(by simpa [Cvs.Approximant.ConnesLowModeGeometry.perpendicularProfile] using he :
    0<1-Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)).ne'⟩

/-- The even signed coefficients of a constant and the first two cosines. -/
def threeMode (N : ℕ) (α β γ : ℝ) : Idx N → ℝ
  | none => α
  | some (k,_) => if (k : ℕ)=0 then β else if (k : ℕ)=1 then γ else 0

/-- A coefficient vector supported on the first three unsigned cosine modes. -/
def FirstThreeSupported (N : ℕ) (ξ : Idx N → ℝ) : Prop :=
  ∀ i,2<(mode N i).natAbs → ξ i=0

theorem threeMode_even (N : ℕ) (α β γ : ℝ) (i : Idx N) :
    threeMode N α β γ (negI N i)=threeMode N α β γ i := by
  cases i <;> rfl

theorem threeMode_supported (N : ℕ) (α β γ : ℝ) :
    FirstThreeSupported N (threeMode N α β γ) := by
  rintro (_ | ⟨k,b⟩) hi
  · simp [mode] at hi
  · have hk0 : (k : ℕ)≠0 := by intro hk; cases b <;> simp [mode,hk] at hi
    have hk1 : (k : ℕ)≠1 := by intro hk; cases b <;> simp [mode,hk] at hi
    simp [threeMode,hk0,hk1]

theorem threeMode_pair {N : ℕ} (hN : 2≤N) (α β γ : ℝ) (n : Idx N → ℝ) :
    threeMode N α β γ ⬝ᵥ n=α*n none+
      β*(n (some (⟨0,by omega⟩,true))+n (some (⟨0,by omega⟩,false)))+
      γ*(n (some (⟨1,by omega⟩,true))+n (some (⟨1,by omega⟩,false))) := by
  obtain ⟨N,rfl⟩ : ∃ K,N=Nat.succ (Nat.succ K) := by
    exact ⟨N-2,by omega⟩
  simp [dotProduct,threeMode,Fintype.sum_option,Fintype.sum_prod_type,
    Fin.sum_univ_succ]
  ring

theorem threeMode_mass {N : ℕ} (hN : 2≤N) (α β γ : ℝ) :
    threeMode N α β γ ⬝ᵥ threeMode N α β γ=α^2+2*β^2+2*γ^2 := by
  rw [threeMode_pair hN]
  simp [threeMode]
  ring

theorem threeMode_endpoint {N : ℕ} (hN : 2≤N) (α β γ : ℝ) :
    endpoint N (threeMode N α β γ)=α+2*β+2*γ := by
  have h := threeMode_pair hN α β γ (fun _ => (1 : ℝ))
  have hh : endpoint N (threeMode N α β γ)=α+β*(1+1)+γ*(1+1) := by
    simpa [dotProduct,endpoint] using h
  linarith

theorem connesCoef_second (x : ℝ) {N : ℕ} (hN : 2≤N) (b : Bool) :
    Cvs.Approximant.ConnesVectorRealScale.connesCoef x N (some (⟨1,by omega⟩,b))=Cvs.Approximant.ConnesLowModeGeometry.coef x 2/2 := by
  simp [Cvs.Approximant.ConnesVectorRealScale.connesCoef,Cvs.Finite.SymmetricModeSet.coeff,Cvs.Approximant.ConnesLowModeGeometry.coef,show 2<N+1 by omega]

/-- The cross product of the actual first three Connes coefficients and endpoint evaluation. -/
def flatVector (x : ℝ) (N : ℕ) : Idx N → ℝ :=
  threeMode N (Cvs.Approximant.ConnesLowModeGeometry.coef x 2-Cvs.Approximant.ConnesLowModeGeometry.coef x 1)
    ((2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0-Cvs.Approximant.ConnesLowModeGeometry.coef x 2)/2)
    ((Cvs.Approximant.ConnesLowModeGeometry.coef x 1-2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)/2)

theorem flatVector_even (x : ℝ) (N : ℕ) (i : Idx N) :
    flatVector x N (negI N i)=flatVector x N i := threeMode_even _ _ _ _ _

theorem flatVector_supported (x : ℝ) (N : ℕ) :
    FirstThreeSupported N (flatVector x N) := threeMode_supported _ _ _ _

theorem flatVector_endpoint (x : ℝ) {N : ℕ} (hN : 2≤N) :
    endpoint N (flatVector x N)=0 := by
  rw [flatVector,threeMode_endpoint hN]
  ring

theorem flatVector_orthogonal (x : ℝ) {N : ℕ} (hN : 2≤N) :
    flatVector x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N=0 := by
  rw [flatVector,threeMode_pair hN,Cvs.Approximant.ConnesCoefficientsNonvanishing.connesCoef_none,
    Cvs.Approximant.ConnesLowModeGeometry.connesCoef_first x (by omega) true,
    Cvs.Approximant.ConnesLowModeGeometry.connesCoef_first x (by omega) false,
    connesCoef_second x hN true,connesCoef_second x hN false]
  simp only [Cvs.Approximant.ConnesLowModeGeometry.coef]
  ring

theorem flatVector_mass_pos (x : ℝ) {N : ℕ} (hN : 2≤N)
    (hC : Cvs.Approximant.ConnesLowModeGeometry.coef x 1-2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0≠0) :
    0<flatVector x N ⬝ᵥ flatVector x N := by
  rw [flatVector,threeMode_mass hN]
  have hcp := sq_pos_of_ne_zero (div_ne_zero hC two_ne_zero)
  nlinarith [sq_nonneg (Cvs.Approximant.ConnesLowModeGeometry.coef x 2-Cvs.Approximant.ConnesLowModeGeometry.coef x 1),
    sq_nonneg ((2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0-Cvs.Approximant.ConnesLowModeGeometry.coef x 2)/2)]

/-- Every sufficiently large scale has an actual nonzero endpoint-flat Connes-perpendicular vector. -/
theorem eventually_flatVector_mass_pos :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ,2≤N → 0<flatVector x N ⬝ᵥ flatVector x N := by
  filter_upwards [Cvs.Approximant.ConnesLowModeGeometry.eventually_perpendicular_endpoint_ne_zero] with x hC N hN
  exact flatVector_mass_pos x hN hC

/-- Every even vector in the first three unsigned modes has three real coordinates. -/
theorem firstThree_eq_threeMode {N : ℕ} (hN : 2≤N) (ξ : Idx N → ℝ)
    (hξ : ∀ i,ξ (negI N i)=ξ i) (hs : FirstThreeSupported N ξ) :
    ξ=threeMode N (ξ none) (ξ (some (⟨0,by omega⟩,true)))
      (ξ (some (⟨1,by omega⟩,true))) := by
  funext i
  rcases i with _ | ⟨k,b⟩
  · rfl
  · by_cases hk0 : (k : ℕ)=0
    · have hk : k=(⟨0,by omega⟩ : Fin N) := Fin.ext hk0
      rw [hk]
      cases b
      · simpa [threeMode,negI] using (hξ (some (⟨0,by omega⟩,false))).symm
      · simp [threeMode]
    · by_cases hk1 : (k : ℕ)=1
      · have hk : k=(⟨1,by omega⟩ : Fin N) := Fin.ext hk1
        rw [hk]
        cases b
        · simpa [threeMode,negI] using (hξ (some (⟨1,by omega⟩,false))).symm
        · simp [threeMode]
      · have hm : 2<(mode N (some (k,b))).natAbs := by
          cases b <;> simp [mode] <;> omega
        rw [hs _ hm]
        simp [threeMode,hk0,hk1]

/-- The actual first-three-mode Connes hyperplane has the two-mode and endpoint-flat directions as a basis. -/
theorem firstThree_connes_basis (x : ℝ) {N : ℕ} (hN : 2≤N)
    (h0 : Cvs.Approximant.ConnesLowModeGeometry.coef x 0≠0) (hC : Cvs.Approximant.ConnesLowModeGeometry.coef x 1-2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0≠0)
    (ξ : Idx N → ℝ) (hξ : ∀ i,ξ (negI N i)=ξ i)
    (hs : FirstThreeSupported N ξ) (hp : ξ ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N=0) :
    ∃ t s : ℝ,ξ=t • anchor x N+s • flatVector x N := by
  let b : ℝ := ξ (some (⟨0,by omega⟩,true))
  let c : ℝ := ξ (some (⟨1,by omega⟩,true))
  let s : ℝ := 2*c/(Cvs.Approximant.ConnesLowModeGeometry.coef x 1-2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)
  let t : ℝ := 2*b-s*(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0-Cvs.Approximant.ConnesLowModeGeometry.coef x 2)
  have hp' : ξ none*Cvs.Approximant.ConnesLowModeGeometry.coef x 0+b*Cvs.Approximant.ConnesLowModeGeometry.coef x 1+c*Cvs.Approximant.ConnesLowModeGeometry.coef x 2=0 := by
    rw [firstThree_eq_threeMode hN ξ hξ hs,threeMode_pair hN,
      Cvs.Approximant.ConnesCoefficientsNonvanishing.connesCoef_none,Cvs.Approximant.ConnesLowModeGeometry.connesCoef_first x (by omega) true,
      Cvs.Approximant.ConnesLowModeGeometry.connesCoef_first x (by omega) false,
      connesCoef_second x hN true,connesCoef_second x hN false] at hp
    change ξ none*Cvs.Approximant.ConnesLowModeGeometry.coef x 0+b*(Cvs.Approximant.ConnesLowModeGeometry.coef x 1/2+Cvs.Approximant.ConnesLowModeGeometry.coef x 1/2)+
      c*(Cvs.Approximant.ConnesLowModeGeometry.coef x 2/2+Cvs.Approximant.ConnesLowModeGeometry.coef x 2/2)=0 at hp
    nlinarith
  have hs' : s*(Cvs.Approximant.ConnesLowModeGeometry.coef x 1-2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)=2*c := by
    exact div_mul_cancel₀ _ hC
  have ha : ξ none=t*(-(Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)))+
      s*(Cvs.Approximant.ConnesLowModeGeometry.coef x 2-Cvs.Approximant.ConnesLowModeGeometry.coef x 1) := by
    dsimp only [t,s]
    field_simp [h0,hC]
    linear_combination (Cvs.Approximant.ConnesLowModeGeometry.coef x 1-2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)*hp'
  refine ⟨t,s,?_⟩
  rw [firstThree_eq_threeMode hN ξ hξ hs]
  funext i
  rcases i with _ | ⟨k,b'⟩
  · simpa [threeMode,anchor,Cvs.WeilForm.TwoModeLowHeadDamping.twoMode,flatVector,Pi.add_apply,
      Pi.smul_apply,smul_eq_mul] using ha
  · by_cases hk0 : (k : ℕ)=0
    · simp only [threeMode,hk0,ite_true,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
        anchor,Cvs.WeilForm.TwoModeLowHeadDamping.twoMode,flatVector]
      dsimp only [b,t]
      ring
    · by_cases hk1 : (k : ℕ)=1
      · simp [threeMode,hk1,anchor,Cvs.WeilForm.TwoModeLowHeadDamping.twoMode,flatVector]
        dsimp only [c] at hs'
        linarith
      · simp [threeMode,anchor,Cvs.WeilForm.TwoModeLowHeadDamping.twoMode,flatVector,hk0,hk1]

/-- The actual two-mode and endpoint-flat directions are linearly independent. -/
theorem anchor_flatVector_independent (x : ℝ) {N : ℕ} (hN : 2≤N)
    (hC : Cvs.Approximant.ConnesLowModeGeometry.coef x 1-2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0≠0) (t s : ℝ)
    (he : t • anchor x N+s • flatVector x N=0) : t=0 ∧ s=0 := by
  have h2 := congrArg (fun v : Idx N → ℝ => v (some (⟨1,by omega⟩,true))) he
  have h1 := congrArg (fun v : Idx N → ℝ => v (some (⟨0,by omega⟩,true))) he
  simp [anchor,Cvs.WeilForm.TwoModeLowHeadDamping.twoMode,flatVector,threeMode] at h2
  have hs : s=0 := h2.resolve_right hC
  simp [anchor,Cvs.WeilForm.TwoModeLowHeadDamping.twoMode,flatVector,hs] at h1
  exact ⟨h1,hs⟩

/-- The first-three-mode basis has the exact actual two-by-two matrix energy. -/
theorem energy_anchor_flatVector {L : ℝ} (hL : 0<L) (P R N : ℕ)
    (x t s : ℝ) :
    (t • anchor x N+s • flatVector x N) ⬝ᵥ
      (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ (t • anchor x N+s • flatVector x N))=
      t^2*(anchor x N ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ anchor x N))+
      2*t*s*(anchor x N ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ flatVector x N))+
      s^2*(flatVector x N ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ flatVector x N)) := by
  have hs := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm (Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N))
    (flatVector x N) (anchor x N)
  simp only [Matrix.mulVec_add,Matrix.mulVec_smul,add_dotProduct,dotProduct_add,
    smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [hs]
  ring

theorem flatVector_cosine_endpoints {L : ℝ} (hL : 0<L) (x : ℝ) {N : ℕ}
    (hN : 2≤N) : Cvs.Approximant.CosineColumnTailPairing.cosineSum L N (flatVector x N) 0=0 ∧
      Cvs.Approximant.CosineColumnTailPairing.cosineSum L N (flatVector x N) L=0 := by
  rw [cosineSum_zero,cosineSum_end hL,flatVector_endpoint x hN]
  exact ⟨rfl,rfl⟩

/-- The nonnegative lattice frequency of an unsigned cosine mode. -/
def frequency (L : ℝ) (n : ℕ) : ℝ := 2*π*n/L

/-- The reciprocal endpoint overlap of two unsigned cosine modes. -/
def cosineConv (L : ℝ) (m n : ℕ) (d : ℝ) : ℝ :=
  if m=n then if m=0 then d else
    (d*Real.cos (frequency L m*d)+Real.sin (frequency L m*d)/frequency L m)/2
  else (frequency L m*Real.sin (frequency L m*d)-
    frequency L n*Real.sin (frequency L n*d))/((frequency L m)^2-(frequency L n)^2)

/-- The first derivative of the reciprocal overlap. -/
def cosineSlope (L : ℝ) (m n : ℕ) (d : ℝ) : ℝ :=
  if m=n then if m=0 then 1 else
    Real.cos (frequency L m*d)-frequency L m*d*Real.sin (frequency L m*d)/2
  else ((frequency L m)^2*Real.cos (frequency L m*d)-
    (frequency L n)^2*Real.cos (frequency L n*d))/((frequency L m)^2-(frequency L n)^2)

/-- The reciprocal overlap curvature. -/
def cosineCurvature (L : ℝ) (m n : ℕ) (d : ℝ) : ℝ :=
  if m=n then if m=0 then 0 else
    -3*frequency L m/2*Real.sin (frequency L m*d)-
      (frequency L m)^2*d*Real.cos (frequency L m*d)/2
  else (-(frequency L m)^3*Real.sin (frequency L m*d)+
    (frequency L n)^3*Real.sin (frequency L n*d))/((frequency L m)^2-(frequency L n)^2)

theorem frequency_nonneg {L : ℝ} (hL : 0<L) (n : ℕ) : 0≤frequency L n := by
  unfold frequency
  positivity

theorem frequency_pos {L : ℝ} (hL : 0<L) {n : ℕ} (hn : 0<n) : 0<frequency L n := by
  unfold frequency
  positivity

theorem frequency_mul_length {L : ℝ} (hL : 0<L) (n : ℕ) :
    frequency L n*L=2*π*n := by
  unfold frequency
  field_simp [ne_of_gt hL]

theorem frequency_sq_ne {L : ℝ} (hL : 0<L) {m n : ℕ} (hmn : m≠n) :
    (frequency L m)^2≠(frequency L n)^2 := by
  intro h
  have he : frequency L m=frequency L n := by
    nlinarith [frequency_nonneg hL m, frequency_nonneg hL n]
  unfold frequency at he
  have hL0 := ne_of_gt hL
  have hπ := Real.pi_ne_zero
  apply hmn
  have : (m:ℝ)=(n:ℝ) := by field_simp [hL0] at he; nlinarith [Real.pi_pos]
  exact_mod_cast this

theorem continuous_cosineConv (L : ℝ) (m n : ℕ) : Continuous (cosineConv L m n) := by
  unfold cosineConv
  split_ifs <;> fun_prop

theorem continuous_cosineCurvature (L : ℝ) (m n : ℕ) :
    Continuous (cosineCurvature L m n) := by
  unfold cosineCurvature
  split_ifs <;> fun_prop

/-- The reciprocal overlap has the displayed first derivative. -/
theorem hasDerivAt_cosineConv {L : ℝ} (hL : 0<L) (m n : ℕ) (d : ℝ) :
    HasDerivAt (cosineConv L m n) (cosineSlope L m n d) d := by
  have hc (k : ℕ) := ((hasDerivAt_id d).const_mul (frequency L k)).cos
  have hs (k : ℕ) := ((hasDerivAt_id d).const_mul (frequency L k)).sin
  by_cases hmn : m=n
  · subst n
    by_cases hm : m=0
    · unfold cosineConv cosineSlope
      simp only [ite_eq_left hm]
      exact hasDerivAt_id d
    · have hω := (frequency_pos hL (Nat.pos_of_ne_zero hm)).ne'
      unfold cosineConv cosineSlope
      simp only [ite_eq_right hm]
      convert (((hasDerivAt_id d).mul (hc m)).add ((hs m).div_const (frequency L m))).div_const 2
        using 1 <;> (try funext x) <;> (try dsimp) <;>
        (try field_simp [hω]) <;> first | rfl | ring
  · unfold cosineConv cosineSlope
    simp only [ ite_eq_right hmn]
    convert (((hs m).const_mul (frequency L m)).sub
      ((hs n).const_mul (frequency L n))).div_const
      ((frequency L m)^2-(frequency L n)^2) using 1 <;>
      (try funext x) <;> (try dsimp) <;> first | rfl | ring

/-- The reciprocal overlap's first derivative has the displayed curvature. -/
theorem hasDerivAt_cosineSlope (L : ℝ) (m n : ℕ) (d : ℝ) :
    HasDerivAt (cosineSlope L m n) (cosineCurvature L m n d) d := by
  have hc (k : ℕ) := ((hasDerivAt_id d).const_mul (frequency L k)).cos
  have hs (k : ℕ) := ((hasDerivAt_id d).const_mul (frequency L k)).sin
  by_cases hmn : m=n
  · subst n
    by_cases hm : m=0
    · unfold cosineSlope cosineCurvature
      simp only [ite_eq_left hm]
      exact hasDerivAt_const d (1:ℝ)
    · unfold cosineSlope cosineCurvature
      simp only [ite_eq_right hm]
      convert (hc m).sub ((((hasDerivAt_id d).const_mul (frequency L m)).mul
        (hs m)).div_const 2) using 1 <;> (try funext x) <;>
        (try dsimp) <;> first | rfl | ring
  · unfold cosineSlope cosineCurvature
    simp only [ ite_eq_right hmn]
    convert (((hc m).const_mul ((frequency L m)^2)).sub
      ((hc n).const_mul ((frequency L n)^2))).div_const
      ((frequency L m)^2-(frequency L n)^2) using 1 <;>
      (try funext x) <;> (try dsimp) <;> first | rfl | ring

theorem cosineConv_zero (L : ℝ) (m n : ℕ) : cosineConv L m n 0=0 := by
  simp [cosineConv]

/-- Every pair of endpoint-normalized cosine modes has slope one at zero. -/
theorem cosineSlope_zero {L : ℝ} (hL : 0<L) (m n : ℕ) : cosineSlope L m n 0=1 := by
  by_cases hmn : m=n
  · simp [cosineSlope, hmn]
  · simp only [cosineSlope, ite_eq_right hmn, mul_zero, Real.cos_zero, mul_one]
    exact div_self (sub_ne_zero.mpr (frequency_sq_ne hL hmn))

private theorem sin_frequency_reflect {L : ℝ} (hL : 0<L) (n : ℕ) (v : ℝ) :
    Real.sin (frequency L n*(L-v))=-Real.sin (frequency L n*v) := by
  rw [show frequency L n*(L-v)=2*π*n-frequency L n*v by
    nlinarith [frequency_mul_length hL n]]
  simpa using Cvs.Finite.CosineModeOverlap.sin_two_pi_int_sub (n:ℤ) (frequency L n*v)

private theorem cos_frequency_reflect {L : ℝ} (hL : 0<L) (n : ℕ) (v : ℝ) :
    Real.cos (frequency L n*(L-v))=Real.cos (frequency L n*v) := by
  rw [show frequency L n*(L-v)=2*π*n-frequency L n*v by
    nlinarith [frequency_mul_length hL n]]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    Real.cos_nat_mul_two_pi_sub (frequency L n*v) n

/-- Folding the signed kernel gives the exact reciprocal cosine convolution. -/
theorem folded_K_eq_cosineConv {L : ℝ} (hL : 0<L) (m n : ℕ) (v : ℝ) :
    L/4*(Cvs.Finite.CosineModeOverlap.K L (m:ℤ) (n:ℤ) v+Cvs.Finite.CosineModeOverlap.K L (m:ℤ) (-(n:ℤ)) v)=
      cosineConv L m n (L-v) := by
  have hL0 := ne_of_gt hL
  have hπ := Real.pi_ne_zero
  by_cases hmn : m=n
  · subst n
    by_cases hm : m=0
    · subst m
      simp [Cvs.Finite.CosineModeOverlap.K, cosineConv]
      field_simp
      ring
    · have hmInt : (m:ℤ)≠0 := by exact_mod_cast hm
      have hmirror : (m:ℤ)≠-(m:ℤ) := by omega
      have hmR : (m:ℝ)≠0 := by exact_mod_cast hm
      have hω := (frequency_pos hL (Nat.pos_of_ne_zero hm)).ne'
      simp only [cosineConv, ite_eq_right hm,
        cos_frequency_reflect hL, sin_frequency_reflect hL]
      unfold Cvs.Finite.CosineModeOverlap.K
      rw [ite_eq_left rfl, ite_eq_right hmirror]
      push_cast
      rw [show 2*π*(-(m:ℝ))*v/L=-(2*π*m*v/L) by ring, Real.sin_neg]
      unfold frequency
      field_simp
      ring
  · have hmnI : (m:ℤ)≠(n:ℤ) := by exact_mod_cast hmn
    have hmirror : (m:ℤ)≠-(n:ℤ) := by omega
    have hmnR : (m:ℝ)≠(n:ℝ) := by exact_mod_cast hmn
    have hsum : (m:ℝ)+(n:ℝ)≠0 := by
      exact_mod_cast (show m+n≠0 by omega)
    have hd := sub_ne_zero.mpr (frequency_sq_ne hL hmn)
    simp only [cosineConv, ite_eq_right hmn, sin_frequency_reflect hL]
    unfold Cvs.Finite.CosineModeOverlap.K
    rw [ite_eq_right hmnI, ite_eq_right hmirror]
    push_cast
    rw [show 2*π*(-(n:ℝ))*v/L=-(2*π*n*v/L) by ring, Real.sin_neg]
    unfold frequency at hd ⊢
    have hmn' : (n:ℝ)-(m:ℝ)≠0 := sub_ne_zero.mpr hmnR.symm
    have hsum' : -(n:ℝ)-(m:ℝ)≠0 := by intro h; apply hsum; linarith
    have hsqr : (m:ℝ)^2-(n:ℝ)^2≠0 := by
      intro h
      apply hmnR
      nlinarith [Nat.cast_nonneg (α:=ℝ) m, Nat.cast_nonneg (α:=ℝ) n]
    field_simp [hsqr]
    ring

/-- The actual mixed cosine overlap is the squared-frequency convolution kernel. -/
theorem integral_cosine_overlap {L : ℝ} (hL : 0<L) (m n : ℕ) (v : ℝ) :
    (∫ s in (0:ℝ)..(L-v), Real.cos (frequency L m*s)*
      Real.cos (frequency L n*(s+v)))=cosineConv L m n (L-v) := by
  have h := Cvs.Finite.CosineModeOverlap.overlap_eq hL (m:ℤ) (n:ℤ) v
  simp only [Int.cast_natCast] at h
  change (∫ s in (0:ℝ)..(L-v), Real.cos (frequency L m*s)*
    Real.cos (frequency L n*(s+v)))=_ at h
  rw [h]
  exact folded_K_eq_cosineConv hL m n v

/-- The mixed cosine correlation at nonnegative lag. -/
def cosineCorrCut (L : ℝ) (m n : ℕ) (v : ℝ) : ℝ :=
  if v≤L then cosineConv L m n (L-v) else 0

/-- The complete endpoint and curvature producer for an unsigned cosine pair. -/
def cosineVolterra (L : ℝ) (m n : ℕ) (V : ℝ→ℝ) : ℝ :=
  V L+∫ d in (0:ℝ)..L, cosineCurvature L m n d*V (L-d)

/-- The actual finite prime moment of an unsigned cosine pair. -/
def cosinePrimeMoment (P R : ℕ) (L : ℝ) (m n : ℕ) : ℝ :=
  ∑ k∈Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
    (ArithmeticFunction.vonMangoldt k*(k:ℝ)^(-(1/2):ℝ))*cosineCorrCut L m n (Real.log k)

/-- The continuous mean moment of an unsigned cosine pair. -/
def cosineMeanMoment (L : ℝ) (m n : ℕ) : ℝ :=
  ∫ d in (0:ℝ)..L, cosineConv L m n d*Real.exp ((L-d)/2)

/-- The correlation is the exact ramp convolution of its curvature. -/
theorem cosineConv_eq_ramp_integral {L : ℝ} (hL : 0<L) (m n : ℕ) (d : ℝ) :
    cosineConv L m n d=d+∫ s in (0:ℝ)..d, (d-s)*cosineCurvature L m n s := by
  have hd (s : ℝ) : HasDerivAt
      (fun s => (d-s)*cosineSlope L m n s+cosineConv L m n s)
      ((d-s)*cosineCurvature L m n s) s := by
    convert (((hasDerivAt_const s d).sub (hasDerivAt_id s)).mul
      (hasDerivAt_cosineSlope L m n s)).add (hasDerivAt_cosineConv hL m n s) using 1 <;>
      (try funext x) <;> (try dsimp) <;> first | rfl | ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (((continuous_const.sub continuous_id).mul (continuous_cosineCurvature L m n)).intervalIntegrable 0 d)
  rw [cosineConv_zero, cosineSlope_zero hL] at hi
  linarith

/-- A positive-part ramp gives the cut mixed correlation exactly. -/
theorem cosineCorrCut_eq_volterra_ramp {L : ℝ} (hL : 0<L) (m n : ℕ) (c : ℝ) (hc : 0≤c) :
    cosineCorrCut L m n c=cosineVolterra L m n (fun t => max (t-c) 0) := by
  have hcont : Continuous (fun d : ℝ => cosineCurvature L m n d*max (L-d-c) 0) :=
    (continuous_cosineCurvature L m n).mul
      (((continuous_const.sub continuous_id).sub continuous_const).max continuous_const)
  by_cases hcL : c≤L
  · have hi1 : (∫ d in (0:ℝ)..(L-c), cosineCurvature L m n d*max (L-d-c) 0)=
        ∫ d in (0:ℝ)..(L-c), (L-c-d)*cosineCurvature L m n d := by
      apply intervalIntegral.integral_congr
      intro d hd
      have hd' : d≤L-c := (show d∈Icc 0 (L-c) from by
        simpa [uIcc_of_le (sub_nonneg.mpr hcL)] using hd).2
      dsimp only
      rw [max_eq_left (by linarith : 0≤L-d-c)]
      ring
    have hi0 : (∫ d in (L-c)..L, cosineCurvature L m n d*max (L-d-c) 0)=0 := by
      calc
        _ = ∫ d in (L-c)..L, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro d hd
          have hd' : L-c≤d := (show d∈Icc (L-c) L from by
            simpa [uIcc_of_le (by linarith : L-c≤L)] using hd).1
          simp [max_eq_right (by linarith : L-d-c≤0)]
        _ = 0 := by simp
    have hi := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      (hcont.intervalIntegrable 0 (L-c)) (hcont.intervalIntegrable (L-c) L)
    rw [hi1, hi0, add_zero] at hi
    rw [cosineCorrCut, ite_eq_left hcL, cosineVolterra,
      max_eq_left (sub_nonneg.mpr hcL), ←hi]
    exact cosineConv_eq_ramp_integral hL m n (L-c)
  · have hi : (∫ d in (0:ℝ)..L, cosineCurvature L m n d*max (L-d-c) 0)=0 := by
      calc
        _ = ∫ d in (0:ℝ)..L, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro d hd
          have hd' : 0≤d := (show d∈Icc 0 L from by simpa [uIcc_of_le hL.le] using hd).1
          simp [max_eq_right (by linarith : L-d-c≤0)]
        _ = 0 := by simp
    simp [cosineCorrCut, hcL, cosineVolterra, max_eq_right (by linarith : L-c≤0), hi]

/-- Every finite prime cosine moment has the same coupled producer. -/
theorem cosinePrimeMoment_eq_volterra {L : ℝ} (hL : 0<L) (P R m n : ℕ) :
    cosinePrimeMoment P R L m n=cosineVolterra L m n (Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R) := by
  have hi (k : ℕ) : IntervalIntegrable (fun d : ℝ =>
      (ArithmeticFunction.vonMangoldt k*(k:ℝ)^(-(1/2):ℝ))*
      (cosineCurvature L m n d*max (L-d-Real.log k) 0)) volume 0 L := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((continuous_cosineCurvature L m n).mul
      (((continuous_const.sub continuous_id).sub continuous_const).max continuous_const))
  unfold cosinePrimeMoment
  trans ∑ k∈Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
    (ArithmeticFunction.vonMangoldt k*(k:ℝ)^(-(1/2):ℝ))*
      cosineVolterra L m n (fun t => max (t-Real.log k) 0)
  · apply Finset.sum_congr rfl
    intro k hk
    rw [cosineCorrCut_eq_volterra_ramp hL m n _ (Real.log_natCast_nonneg k)]
  unfold cosineVolterra Cvs.WeilForm.PrimeMomentVolterra.primeRamp
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    _ = ∑ k∈Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, ∫ d in (0:ℝ)..L,
        (ArithmeticFunction.vonMangoldt k*(k:ℝ)^(-(1/2):ℝ))*
          (cosineCurvature L m n d*max (L-d-Real.log k) 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ d in (0:ℝ)..L, ∑ k∈Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
        (ArithmeticFunction.vonMangoldt k*(k:ℝ)^(-(1/2):ℝ))*
          (cosineCurvature L m n d*max (L-d-Real.log k) 0) := by
      symm
      exact intervalIntegral.integral_finsetSum (fun k _ => hi k)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro d hd
      dsimp only
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The actual continuous mean has the same unsigned-cosine producer. -/
theorem cosineMeanMoment_eq_volterra {L : ℝ} (hL : 0<L) (m n : ℕ) :
    cosineMeanMoment L m n=cosineVolterra L m n Cvs.WeilForm.PrimeMomentVolterra.meanRamp := by
  have hA (d : ℝ) : HasDerivAt (fun d => Cvs.WeilForm.PrimeMomentVolterra.meanRamp (L-d))
      (-(2*Real.exp ((L-d)/2)-2)) d := by
    unfold Cvs.WeilForm.PrimeMomentVolterra.meanRamp
    convert (((((hasDerivAt_const d L).sub (hasDerivAt_id d)).div_const 2).exp.const_mul 4).sub
      (((hasDerivAt_const d L).sub (hasDerivAt_id d)).const_mul 2)).sub_const 4 using 1 <;>
      (try funext x) <;> (try dsimp) <;> first | rfl | ring
  have hA' (d : ℝ) : HasDerivAt (fun d => 2*Real.exp ((L-d)/2)-2)
      (-Real.exp ((L-d)/2)) d := by
    convert (((((hasDerivAt_const d L).sub (hasDerivAt_id d)).div_const 2).exp.const_mul 2).sub_const 2)
      using 1 <;> (try funext x) <;> (try dsimp) <;> first | rfl | ring
  have hd (d : ℝ) : HasDerivAt
      (fun d => cosineSlope L m n d*Cvs.WeilForm.PrimeMomentVolterra.meanRamp (L-d)+
        cosineConv L m n d*(2*Real.exp ((L-d)/2)-2))
      (cosineCurvature L m n d*Cvs.WeilForm.PrimeMomentVolterra.meanRamp (L-d)-
        cosineConv L m n d*Real.exp ((L-d)/2)) d := by
    convert (((hasDerivAt_cosineSlope L m n d).mul (hA d)).add
      ((hasDerivAt_cosineConv hL m n d).mul (hA' d))) using 1 <;>
      (try funext x) <;> (try dsimp) <;> first | rfl | ring
  have hAC : Continuous (fun d : ℝ => Cvs.WeilForm.PrimeMomentVolterra.meanRamp (L-d)) := by
    unfold Cvs.WeilForm.PrimeMomentVolterra.meanRamp
    fun_prop
  have hEC : Continuous (fun d : ℝ => Real.exp ((L-d)/2)) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun d _ => hd d)
    ((((continuous_cosineCurvature L m n).mul hAC).sub
      ((continuous_cosineConv L m n).mul hEC)).intervalIntegrable 0 L)
  rw [intervalIntegral.integral_sub (f:=fun d => cosineCurvature L m n d*Cvs.WeilForm.PrimeMomentVolterra.meanRamp (L-d))
    (g:=fun d => cosineConv L m n d*Real.exp ((L-d)/2))
    (((continuous_cosineCurvature L m n).mul hAC).intervalIntegrable 0 L)
    (((continuous_cosineConv L m n).mul hEC).intervalIntegrable 0 L),
    cosineConv_zero, cosineSlope_zero hL] at hi
  simp only [sub_self, Cvs.WeilForm.PrimeMomentVolterra.meanRamp, zero_div, Real.exp_zero, mul_one,
    sub_zero, mul_zero, zero_mul, add_zero] at hi
  unfold cosineMeanMoment cosineVolterra
  unfold Cvs.WeilForm.PrimeMomentVolterra.meanRamp
  linarith

/-- The signed finite prime-minus-mean matrix is one actual ramp transform. -/
theorem cosineSignedMoment_eq_volterra {L : ℝ} (hL : 0<L) (P R m n : ℕ) :
    cosinePrimeMoment P R L m n-cosineMeanMoment L m n=
      cosineVolterra L m n (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t-Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) := by
  have hp : Continuous (Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R) := by
    unfold Cvs.WeilForm.PrimeMomentVolterra.primeRamp
    apply continuous_finsetSum
    intro k hk
    exact continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const)
  have hm : Continuous Cvs.WeilForm.PrimeMomentVolterra.meanRamp := by unfold Cvs.WeilForm.PrimeMomentVolterra.meanRamp; fun_prop
  rw [cosinePrimeMoment_eq_volterra hL, cosineMeanMoment_eq_volterra hL]
  unfold cosineVolterra
  rw [show (fun d => cosineCurvature L m n d*(Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R (L-d)-Cvs.WeilForm.PrimeMomentVolterra.meanRamp (L-d)))=
    (fun d => cosineCurvature L m n d*Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R (L-d)-
      cosineCurvature L m n d*Cvs.WeilForm.PrimeMomentVolterra.meanRamp (L-d)) by funext d; ring,
    intervalIntegral.integral_sub (f:=fun d => cosineCurvature L m n d*Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R (L-d))
      (g:=fun d => cosineCurvature L m n d*Cvs.WeilForm.PrimeMomentVolterra.meanRamp (L-d))
      (((continuous_cosineCurvature L m n).mul (hp.comp (continuous_const.sub continuous_id))).intervalIntegrable 0 L)
      (((continuous_cosineCurvature L m n).mul (hm.comp (continuous_const.sub continuous_id))).intervalIntegrable 0 L)]
  ring

/-- The actual ramp producer's squared-frequency generator at a lattice node. -/
def cosineGenerator (L : ℝ) (m : ℕ) (V : ℝ→ℝ) : ℝ :=
  (frequency L m)^2*V L-(frequency L m)^3*
    ∫ d in (0:ℝ)..L, Real.sin (frequency L m*d)*V (L-d)

/-- The actual cosine producer is a divided difference off the squared-frequency diagonal. -/
theorem cosineVolterra_off {L : ℝ} (hL : 0<L) {m n : ℕ} (hmn : m≠n)
    (V : ℝ→ℝ) (hV : Continuous V) :
    cosineVolterra L m n V=(cosineGenerator L m V-cosineGenerator L n V)/
      ((frequency L m)^2-(frequency L n)^2) := by
  have hi (k : ℕ) : IntervalIntegrable (fun d : ℝ =>
      Real.sin (frequency L k*d)*V (L-d)) volume 0 L := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun d : ℝ => Real.sin (frequency L k*d)).mul
      (hV.comp (continuous_const.sub continuous_id))
  have hf : (fun d => cosineCurvature L m n d*V (L-d))=
      fun d => (-(frequency L m)^3*(Real.sin (frequency L m*d)*V (L-d))+
        (frequency L n)^3*(Real.sin (frequency L n*d)*V (L-d)))/
          ((frequency L m)^2-(frequency L n)^2) := by
    funext d
    simp only [cosineCurvature, ite_eq_right hmn]
    ring
  rw [cosineVolterra, hf, intervalIntegral.integral_div,
    intervalIntegral.integral_add ((hi m).const_mul _) ((hi n).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold cosineGenerator
  field_simp [sub_ne_zero.mpr (frequency_sq_ne hL hmn)]
  ring

/-- The zero cosine has only the endpoint term. -/
theorem cosineVolterra_zero (L : ℝ) (V : ℝ→ℝ) : cosineVolterra L 0 0 V=V L := by
  simp [cosineVolterra, cosineCurvature]

/-- The diagonal retains its exact sine moment and first cosine moment. -/
theorem cosineVolterra_diag {L : ℝ} (_hL : 0<L) {m : ℕ} (hm : m≠0)
    (V : ℝ→ℝ) (hV : Continuous V) :
    cosineVolterra L m m V=V L-3*frequency L m/2*
      (∫ d in (0:ℝ)..L, Real.sin (frequency L m*d)*V (L-d))-
      (frequency L m)^2/2*(∫ d in (0:ℝ)..L, d*Real.cos (frequency L m*d)*V (L-d)) := by
  have hi : IntervalIntegrable (fun d : ℝ => Real.sin (frequency L m*d)*V (L-d)) volume 0 L := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun d : ℝ => Real.sin (frequency L m*d)).mul
      (hV.comp (continuous_const.sub continuous_id))
  have hj : IntervalIntegrable (fun d : ℝ => d*Real.cos (frequency L m*d)*V (L-d)) volume 0 L := by
    apply Continuous.intervalIntegrable
    exact (continuous_id.mul (by fun_prop : Continuous fun d : ℝ => Real.cos (frequency L m*d))).mul
      (hV.comp (continuous_const.sub continuous_id))
  have hf : (fun d => cosineCurvature L m m d*V (L-d))=
      fun d => (-3*frequency L m/2)*(Real.sin (frequency L m*d)*V (L-d))-
        ((frequency L m)^2/2)*(d*Real.cos (frequency L m*d)*V (L-d)) := by
    funext d
    simp only [cosineCurvature, ite_true, ite_eq_right hm]
    ring
  rw [cosineVolterra, hf, intervalIntegral.integral_sub (hi.const_mul _) (hj.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- The cut signed kernel folds into the actual mixed cosine correlation. -/
theorem folded_Kc_eq_cosineCorrCut {L : ℝ} (hL : 0<L) (m n : ℕ) (v : ℝ) :
    L/4*(Cvs.Finite.LevyKernelIncrement.Kc L (m:ℤ) (n:ℤ) v+Cvs.Finite.LevyKernelIncrement.Kc L (m:ℤ) (-(n:ℤ)) v)=
      cosineCorrCut L m n v := by
  by_cases hv : v≤L
  · rw [Cvs.Finite.LevyKernelIncrement.Kc_of_le hv, Cvs.Finite.LevyKernelIncrement.Kc_of_le hv, cosineCorrCut, ite_eq_left hv]
    exact folded_K_eq_cosineConv hL m n v
  · rw [Cvs.Finite.LevyKernelIncrement.Kc_of_gt (lt_of_not_ge hv), Cvs.Finite.LevyKernelIncrement.Kc_of_gt (lt_of_not_ge hv),
      cosineCorrCut, ite_eq_right hv]
    ring

/-- The finite arithmetic moment has the exact folded prime-matrix normalization. -/
theorem folded_primePair_eq_cosinePrimeMoment {L : ℝ} (hL : 0<L) (P R m n : ℕ) :
    L/8*(Cvs.Finite.ModeSumPairValues.primePair P R L (m:ℤ) (n:ℤ)+
      Cvs.Finite.ModeSumPairValues.primePair P R L (m:ℤ) (-(n:ℤ)))=cosinePrimeMoment P R L m n := by
  have himage := Cvs.WeilForm.PrimePowerReindex.sum_primePow_eq_image P R (fun k : ℕ =>
    (ArithmeticFunction.vonMangoldt k*(k:ℝ)^(-(1/2):ℝ))*
      cosineCorrCut L m n (Real.log k))
  unfold cosinePrimeMoment Cvs.WeilForm.PrimePowerIndexed.primePowIndex
  rw [←himage]
  unfold Cvs.Finite.ModeSumPairValues.primePair
  rw [←Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2
  have hj1 : 1≤j := (Finset.mem_Icc.mp hj).1
  have hlog : Real.log ((p^j:ℕ):ℝ)=(j:ℝ)*Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  have hw := Cvs.WeilForm.PrimeSideSharedWeights.weight_eq_primePowerWeight hpp hj1
  rw [hlog]
  change L/8*(Cvs.Zeta.Explicit.Weil.primePowerWeight p j*(2*Cvs.Finite.LevyKernelIncrement.Kc L (m:ℤ) (n:ℤ) (j*Real.log p))+
    Cvs.Zeta.Explicit.Weil.primePowerWeight p j*(2*Cvs.Finite.LevyKernelIncrement.Kc L (m:ℤ) (-(n:ℤ)) (j*Real.log p)))=_
  rw [Nat.cast_pow, hw, ←folded_Kc_eq_cosineCorrCut hL m n]
  ring

private theorem meanEntry_eq_interval {L : ℝ} (hL : 0<L) (m n : ℤ) :
    Cvs.WeilForm.ArchGreenSecondChannel.meanEntry L m n=∫ v in (0:ℝ)..L, Real.exp (v/2)*Cvs.Finite.CosineModeOverlap.K L m n v := by
  unfold Cvs.WeilForm.ArchGreenSecondChannel.meanEntry
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s:=Ioc (0:ℝ) L)
    measurableSet_Ioi Ioc_subset_Ioi_self (by
      intro v hv
      have hvL : L<v := by
        have hv0 : 0<v := hv.1
        have hnv : ¬v≤L := by intro h; exact hv.2 ⟨hv0,h⟩
        exact lt_of_not_ge hnv
      rw [Cvs.Finite.LevyKernelIncrement.Kc_of_gt hvL, mul_zero]),
    ←intervalIntegral.integral_of_le hL.le]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvL : v≤L := (show v∈Icc 0 L from by simpa [uIcc_of_le hL.le] using hv).2
  dsimp only
  rw [Cvs.Finite.LevyKernelIncrement.Kc_of_le hvL]

/-- The continuous dilation mean has the exact same folded cosine normalization. -/
theorem folded_meanEntry_eq_cosineMeanMoment {L : ℝ} (hL : 0<L) (m n : ℕ) :
    L/4*(Cvs.WeilForm.ArchGreenSecondChannel.meanEntry L (m:ℤ) (n:ℤ)+Cvs.WeilForm.ArchGreenSecondChannel.meanEntry L (m:ℤ) (-(n:ℤ)))=
      cosineMeanMoment L m n := by
  have hcont (j : ℤ) : Continuous (fun v : ℝ => Real.exp (v/2)*Cvs.Finite.CosineModeOverlap.K L (m:ℤ) j v) := by
    unfold Cvs.Finite.CosineModeOverlap.K
    split_ifs <;> fun_prop
  rw [meanEntry_eq_interval hL, meanEntry_eq_interval hL,
    ←intervalIntegral.integral_add ((hcont (n:ℤ)).intervalIntegrable 0 L)
      ((hcont (-(n:ℤ))).intervalIntegrable 0 L),
    ←intervalIntegral.integral_const_mul]
  have hi : (∫ v in (0:ℝ)..L, L/4*(Real.exp (v/2)*Cvs.Finite.CosineModeOverlap.K L (m:ℤ) (n:ℤ) v+
      Real.exp (v/2)*Cvs.Finite.CosineModeOverlap.K L (m:ℤ) (-(n:ℤ)) v))=
      ∫ v in (0:ℝ)..L, cosineConv L m n (L-v)*Real.exp (v/2) := by
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [←folded_K_eq_cosineConv hL m n v]
    ring
  rw [hi]
  have h := intervalIntegral.integral_comp_sub_left
    (fun d : ℝ => cosineConv L m n d*Real.exp ((L-d)/2)) L (a:=0) (b:=L)
  simp only [sub_self, sub_zero] at h
  unfold cosineMeanMoment
  rw [←h]
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only
  congr 2
  ring

/-- The actual signed discrepancy is twice the coupled prime-minus-mean producer. -/
theorem folded_discrepancyEntry_eq_signedMoment {L : ℝ} (hL : 0<L) (P R m n : ℕ) :
    L/2*(Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L (m:ℤ) (n:ℤ)+
      Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L (m:ℤ) (-(n:ℤ)))=
      2*cosineVolterra L m n (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t-Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) := by
  rw [←cosineSignedMoment_eq_volterra hL]
  have hp := folded_primePair_eq_cosinePrimeMoment hL P R m n
  have hm := folded_meanEntry_eq_cosineMeanMoment hL m n
  unfold Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry
  linarith

end Cvs.Approximant.ConnesEndpointGeometry
