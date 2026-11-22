import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ShareBesselFromExtPairing
import Cvs.Route.Visibility.SpinePairingExteriorTransform
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.LowEigenvalueCountSpine
import Cvs.StepA.LowEigenvalueCountZeros
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.TopQuadruple
import Cvs.WeilForm.EvenExplicitFormulaTameTests
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InsideFunctionTame
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.TameClassesFormDense
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.ZeroSidePolarized
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The joint share: projecting `V_σ` off `R₁ ⊔ span U_D` for a finite deep set `D`

Adding `A` to `B` costs the distance to `B` at most `(k + θ‖P_B v‖)²/(1 − θ²)`. With `A = R₁`, `B = span U_D`,
`v = V_σ`, the residue `w = V_σ − P_{R₁ ⊔ U_D}V_σ` has `Q_x(w) ≤ Σ_{ρ ∉ D} m_ρ⟪w, U_ρ⟫² − W_σ‖w‖⁴`, so a share of
`w` in `V_σ` and an off-`D` sum `o(‖V_σ‖⁴)` give `¬ EvenBulkFloor x 0` eventually, for any off-line `σ`.
-/

noncomputable section

open Real MeasureTheory Filter
open scoped InnerProductSpace
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.StepA.TopQuadruple (quadWeight)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.StepA.Edge.FiniteTopCorrectedClosing (USpan bPerp kprof)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.StepA.Edge.DeepJointShare
open Cvs.ZeroCounting

/-! ### The joint share in an inner product space -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The joint share bound**: if `‖P_B a‖ ≤ θ‖a‖` and `|⟪a, v⟫| ≤ k‖a‖` on `A`, `θ < 1`, then
`‖v − P_{A⊔B}v‖² ≥ ‖v − P_B v‖² − (k + θ‖P_B v‖)²/(1 − θ²)`. -/
theorem norm_sub_starProjection_sup_sq_ge (A B : Submodule ℝ E) [B.HasOrthogonalProjection]
    [(A ⊔ B).HasOrthogonalProjection] (v : E) {θ k : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hk : 0 ≤ k)
    (hθ : ∀ a ∈ A, ‖B.starProjection a‖ ≤ θ * ‖a‖) (hkA : ∀ a ∈ A, |⟪a, v⟫_ℝ| ≤ k * ‖a‖) :
    ‖v - B.starProjection v‖ ^ 2 - (k + θ * ‖B.starProjection v‖) ^ 2 / (1 - θ ^ 2)
      ≤ ‖v - (A ⊔ B).starProjection v‖ ^ 2 := by
  set N := A ⊔ B
  set pB := B.starProjection v
  set pN := N.starProjection v
  set q := pN - pB with hq
  have hBN : B ≤ N := le_sup_right
  have hpB : pB ∈ B := B.starProjection_apply_mem v
  have hqN : q ∈ N := N.sub_mem (N.starProjection_apply_mem v) (hBN hpB)
  have hoN : ∀ n ∈ N, ⟪v - pN, n⟫_ℝ = 0 := fun n hn => N.starProjection_inner_eq_zero v n hn
  have hoB : ∀ b ∈ B, ⟪v - pB, b⟫_ℝ = 0 := fun b hb => B.starProjection_inner_eq_zero v b hb
  have hqB : ∀ b ∈ B, ⟪q, b⟫_ℝ = 0 := by
    intro b hb
    have h1 := hoN b (hBN hb)
    have h2 := hoB b hb
    have : q = (v - pB) - (v - pN) := by rw [hq]; abel
    rw [this, inner_sub_left, h1, h2, sub_zero]
  have hpy : ‖v - pB‖ ^ 2 = ‖v - pN‖ ^ 2 + ‖q‖ ^ 2 := by
    have hsum : v - pB = (v - pN) + q := by rw [hq]; abel
    rw [hsum, sq, sq, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_real (hoN q hqN)
  obtain ⟨a, ha, b', hb', hab⟩ := Submodule.mem_sup.mp hqN
  have hqq : ‖q‖ ^ 2 = ⟪q, a⟫_ℝ := by
    calc ‖q‖ ^ 2 = ⟪q, q⟫_ℝ := (real_inner_self_eq_norm_sq q).symm
      _ = ⟪q, a + b'⟫_ℝ := by rw [hab]
      _ = ⟪q, a⟫_ℝ := by rw [inner_add_right, hqB b' hb', add_zero]
  set pa := B.starProjection a
  have hpa : pa ∈ B := B.starProjection_apply_mem a
  have hqa : ⟪q, a⟫_ℝ = ⟪a, v⟫_ℝ - ⟪pB, pa⟫_ℝ := by
    have h1 : ⟪pN, a⟫_ℝ = ⟪v, a⟫_ℝ := by
      have := hoN a (le_sup_left (b := B) ha)
      rw [inner_sub_left] at this; linarith
    have h2 : ⟪pB, a⟫_ℝ = ⟪pB, pa⟫_ℝ := by
      have h3 : ⟪a - pa, pB⟫_ℝ = 0 := B.starProjection_inner_eq_zero a pB hpB
      rw [inner_sub_left] at h3
      have c1 := real_inner_comm a pB
      have c2 := real_inner_comm pa pB
      linarith
    have c3 := real_inner_comm a v
    rw [hq, inner_sub_left, h1, h2]; linarith
  have hK : ‖q‖ ^ 2 ≤ (k + θ * ‖pB‖) * ‖a‖ := by
    rw [hqq, hqa]
    have e1 : ⟪a, v⟫_ℝ ≤ k * ‖a‖ := (le_abs_self _).trans (hkA a ha)
    have e2 : -⟪pB, pa⟫_ℝ ≤ ‖pB‖ * (θ * ‖a‖) :=
      (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hθ a ha) (norm_nonneg _)))
    nlinarith [e1, e2]
  have hlow : (1 - θ ^ 2) * ‖a‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    have hperp : ⟪a - pa, pa + b'⟫_ℝ = 0 :=
      B.starProjection_inner_eq_zero a _ (B.add_mem hpa hb')
    have hdec : q = (a - pa) + (pa + b') := by rw [← hab]; abel
    have hq2 : ‖q‖ ^ 2 = ‖a - pa‖ ^ 2 + ‖pa + b'‖ ^ 2 := by
      rw [hdec, sq, sq, sq]; exact norm_add_sq_eq_norm_sq_add_norm_sq_real hperp
    have hperp2 : ⟪pa, a - pa⟫_ℝ = 0 := by
      rw [real_inner_comm]; exact B.starProjection_inner_eq_zero a pa hpa
    have ha2 : ‖a‖ ^ 2 = ‖pa‖ ^ 2 + ‖a - pa‖ ^ 2 := by
      have : a = pa + (a - pa) := by abel
      conv_lhs => rw [this]
      rw [sq, sq, sq]; exact norm_add_sq_eq_norm_sq_add_norm_sq_real hperp2
    have hθa : ‖pa‖ ^ 2 ≤ θ ^ 2 * ‖a‖ ^ 2 := by
      have := hθ a ha
      have h0 : 0 ≤ ‖pa‖ := norm_nonneg _
      nlinarith
    nlinarith [sq_nonneg ‖pa + b'‖]
  have hθ2 : 0 < 1 - θ ^ 2 := by nlinarith
  have hKn : 0 ≤ k + θ * ‖pB‖ := by positivity
  have hq2 : ‖q‖ ^ 2 ≤ (k + θ * ‖pB‖) ^ 2 / (1 - θ ^ 2) := by
    rw [le_div_iff₀ hθ2]
    have hA0 : 0 ≤ ‖a‖ := norm_nonneg _
    have hQ0 : 0 ≤ ‖q‖ ^ 2 := sq_nonneg _
    have h4 : (‖q‖ ^ 2) ^ 2 ≤ (k + θ * ‖pB‖) ^ 2 * ‖a‖ ^ 2 := by
      have := mul_le_mul hK hK hQ0 (mul_nonneg hKn hA0)
      nlinarith [this]
    by_cases hz : ‖q‖ ^ 2 = 0
    · rw [hz, zero_mul]; positivity
    · have hpos : 0 < ‖q‖ ^ 2 := lt_of_le_of_ne hQ0 (Ne.symm hz)
      have h5 : (‖q‖ ^ 2) ^ 2 * (1 - θ ^ 2) ≤ (k + θ * ‖pB‖) ^ 2 * ‖q‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hlow (sq_nonneg (k + θ * ‖pB‖))
        nlinarith [mul_le_mul_of_nonneg_right h4 hθ2.le]
      have h6 : ‖q‖ ^ 2 * (1 - θ ^ 2) ≤ (k + θ * ‖pB‖) ^ 2 := by
        by_contra hc
        nlinarith [mul_lt_mul_of_pos_left (not_le.mp hc) hpos]
      linarith
  linarith [hpy, hq2]

/-- **The joint share in ratio form**: with `r‖v‖² ≤ ‖v − P_B v‖²`, `|⟪a, v⟫| ≤ κ‖v‖‖a‖` and `‖P_B a‖ ≤ θ‖a‖`
on `A`, `θ < 1`: `‖v − P_{A⊔B}v‖² ≥ (r − θ² − κ(κ + 2))/(1 − θ²)·‖v‖²`. -/
theorem joint_share_ge (A B : Submodule ℝ E) [B.HasOrthogonalProjection]
    [(A ⊔ B).HasOrthogonalProjection] (v : E) {r θ κ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hκ : 0 ≤ κ)
    (hr : r * ‖v‖ ^ 2 ≤ ‖v - B.starProjection v‖ ^ 2)
    (hθ : ∀ a ∈ A, ‖B.starProjection a‖ ≤ θ * ‖a‖) (hkA : ∀ a ∈ A, |⟪a, v⟫_ℝ| ≤ κ * ‖v‖ * ‖a‖) :
    (r - θ ^ 2 - κ * (κ + 2)) / (1 - θ ^ 2) * ‖v‖ ^ 2 ≤ ‖v - (A ⊔ B).starProjection v‖ ^ 2 := by
  have h := norm_sub_starProjection_sup_sq_ge A B v hθ0 hθ1 (by positivity) hθ hkA
  have hpy := B.norm_sq_eq_add_norm_sq_starProjection v
  rw [Submodule.starProjection_orthogonal_val] at hpy
  set p := ‖B.starProjection v‖
  set b := ‖v - B.starProjection v‖
  set V := ‖v‖
  have hp0 : 0 ≤ p := norm_nonneg _
  have hpV : p ≤ V := by nlinarith [norm_nonneg (v - B.starProjection v), norm_nonneg v]
  have hθ2 : 0 < 1 - θ ^ 2 := by nlinarith
  have hsq : (κ * V + θ * p) ^ 2 ≤ θ ^ 2 * p ^ 2 + κ * (κ + 2) * V ^ 2 := by
    have : θ * p ≤ V := by nlinarith [norm_nonneg v]
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hκ (norm_nonneg v))]
  have e : b ^ 2 - θ ^ 2 * p ^ 2 / (1 - θ ^ 2) = (b ^ 2 - θ ^ 2 * V ^ 2) / (1 - θ ^ 2) := by
    field_simp; nlinarith [hpy]
  have h2 : (κ * V + θ * p) ^ 2 / (1 - θ ^ 2)
      ≤ (θ ^ 2 * p ^ 2 + κ * (κ + 2) * V ^ 2) / (1 - θ ^ 2) :=
    div_le_div_of_nonneg_right hsq hθ2.le
  have h3 : (r - θ ^ 2 - κ * (κ + 2)) / (1 - θ ^ 2) * V ^ 2
      ≤ (b ^ 2 - θ ^ 2 * V ^ 2) / (1 - θ ^ 2) - κ * (κ + 2) * V ^ 2 / (1 - θ ^ 2) := by
    rw [div_mul_eq_mul_div, ← sub_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hθ2.le
  have e2 : (θ ^ 2 * p ^ 2 + κ * (κ + 2) * V ^ 2) / (1 - θ ^ 2)
      = θ ^ 2 * p ^ 2 / (1 - θ ^ 2) + κ * (κ + 2) * V ^ 2 / (1 - θ ^ 2) := add_div _ _ _
  linarith

/-- **The operator norm of a product of two orthogonal projections is symmetric**:
`‖P_B a‖ ≤ θ‖a‖` on `A` gives `‖P_A b‖ ≤ θ‖b‖` on `B`. -/
theorem norm_starProjection_le_symm (A B : Submodule ℝ E) [A.HasOrthogonalProjection]
    [B.HasOrthogonalProjection] {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ a ∈ A, ‖B.starProjection a‖ ≤ θ * ‖a‖) :
    ∀ b ∈ B, ‖A.starProjection b‖ ≤ θ * ‖b‖ := by
  intro b hb
  set a := A.starProjection b
  have ha : a ∈ A := A.starProjection_apply_mem b
  have h1 : ‖a‖ ^ 2 = ⟪a, b⟫_ℝ := by
    have : ⟪b - a, a⟫_ℝ = 0 := A.starProjection_inner_eq_zero b a ha
    rw [inner_sub_left, real_inner_comm] at this
    rw [← real_inner_self_eq_norm_sq]; linarith
  have h2 : ⟪a, b⟫_ℝ = ⟪B.starProjection a, b⟫_ℝ := by
    have : ⟪a - B.starProjection a, b⟫_ℝ = 0 := B.starProjection_inner_eq_zero a b hb
    rw [inner_sub_left] at this; linarith
  have h3 : ‖a‖ ^ 2 ≤ θ * ‖a‖ * ‖b‖ := by
    rw [h1, h2]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hθ a ha) (norm_nonneg _))
  rcases (norm_nonneg a).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

/-- `‖P_B a‖ ≤ ‖P_B P_A‖·‖a‖` for `a ∈ A`. -/
theorem norm_starProjection_le_opNorm_comp (A B : Submodule ℝ E) [A.HasOrthogonalProjection]
    [B.HasOrthogonalProjection] {a : E} (ha : a ∈ A) :
    ‖B.starProjection a‖ ≤ ‖B.starProjection ∘L A.starProjection‖ * ‖a‖ := by
  have := (B.starProjection ∘L A.starProjection).le_opNorm a
  rwa [ContinuousLinearMap.comp_apply, A.starProjection_eq_self_iff.2 ha] at this

/-- **The deep-orthogonal closing step**: for `w = v − P_N v` with `U_i ∈ N` on `S`,
`Q(w) ≤ Σ_i m_i⟪w, U_i⟫² − W⟪w, v⟫²` gives `Q(w) ≤ Σ_{i ∉ S} m_i⟪w, U_i⟫² − W‖w‖⁴`. -/
theorem Q_le_off_sub_of_joint {ι : Type*} (N : Submodule ℝ E) [N.HasOrthogonalProjection] (v : E)
    (U : ι → E) (m : ι → ℝ) (S : Set ι) (hUS : ∀ i ∈ S, U i ∈ N) (Q : E → ℝ) {W : ℝ}
    (hQ : Q (v - N.starProjection v) ≤ ∑' i, m i * ⟪v - N.starProjection v, U i⟫_ℝ ^ 2
      - W * ⟪v - N.starProjection v, v⟫_ℝ ^ 2) :
    Q (v - N.starProjection v) ≤ ∑' i : ↥(Sᶜ : Set ι), m i * ⟪v - N.starProjection v, U i⟫_ℝ ^ 2
      - W * ‖v - N.starProjection v‖ ^ 4 := by
  set w := v - N.starProjection v
  have hvan : ∀ i ∈ S, ⟪w, U i⟫_ℝ = 0 := fun i hi => N.starProjection_inner_eq_zero v (U i) (hUS i hi)
  have hA : ∑' i, m i * ⟪w, U i⟫_ℝ ^ 2 = ∑' i : ↥(Sᶜ : Set ι), m i * ⟪w, U i⟫_ℝ ^ 2 := by
    refine (tsum_subtype_eq_of_support_subset fun i hi => ?_).symm
    intro hiS
    exact hi (by simp [hvan i hiS])
  have hwv : ⟪w, v⟫_ℝ = ‖w‖ ^ 2 := (Cvs.Route.Visibility.VisibilityClosingStep.sub_starProjection_facts N v).2
  have e : (‖w‖ ^ 2) ^ 2 = ‖w‖ ^ 4 := by ring
  have h := hQ
  rw [hwv, hA, e] at h
  exact h

end Abstract

/-! ### The joint residue on the real objects -/

section Joint

/-- The joint span `R₁ ⊔ span{U_ρ : ρ ∈ D}` at `x`. -/
abbrev jointSpan {x : ℕ} (hx0 : (0 : ℝ) < x) (D : Finset nonTrivialZeroSet) : Submodule ℝ (Dom x) :=
  R1 x ⊔ USpan hx0 D

instance {x : ℕ} (hx0 : (0 : ℝ) < x) (D : Finset nonTrivialZeroSet) :
    FiniteDimensional ℝ (jointSpan hx0 D) :=
  Submodule.finiteDimensional_sup _ _

instance {x : ℕ} (hx0 : (0 : ℝ) < x) (D : Finset nonTrivialZeroSet) :
    (jointSpan hx0 D).HasOrthogonalProjection :=
  haveI : CompleteSpace (jointSpan hx0 D) := FiniteDimensional.complete ℝ _
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The joint residue `w = V_σ − P_{R₁ ⊔ U_D}V_σ`. -/
def wJoint {x : ℕ} (hx0 : (0 : ℝ) < x) (D : Finset nonTrivialZeroSet) (σ : nonTrivialZeroSet) : Dom x :=
  Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
    - (jointSpan hx0 D).starProjection (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ))

/-- **The joint residue is reflection-even and orthogonal to `R₁`**. -/
theorem wJoint_mem {x : ℕ} (hx0 : (0 : ℝ) < x) (D : Finset nonTrivialZeroSet) (σ : nonTrivialZeroSet) :
    wJoint hx0 D σ ∈ Ev x ∧ wJoint hx0 D σ ∈ (R1 x)ᗮ := by
  have hN : jointSpan hx0 D ≤ Ev x := sup_le (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x) (Cvs.StepA.Edge.FiniteTopCorrectedClosing.USpan_le_Ev hx0 D)
  refine ⟨(Ev x).sub_mem (Cvs.Route.Visibility.ZeroPairingVector.pairVec_mem_Ev hx0 _) (hN ((jointSpan hx0 D).starProjection_apply_mem _)),
    Submodule.orthogonal_le (le_sup_left : R1 x ≤ jointSpan hx0 D)
      ((jointSpan hx0 D).sub_starProjection_mem_orthogonal _)⟩

/-- **The joint residue is the class of a tame test** at `80 ≤ 2πx`. -/
theorem exists_tame_wJoint {x : ℕ} (hx : 80 ≤ 2 * π * x) (D : Finset nonTrivialZeroSet) (σ : nonTrivialZeroSet) :
    ∃ (u : ℝ → ℝ) (hu : Tame u (1 / x) 1),
      wJoint (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) D σ = Cvs.Approximant.SpineCouplingTailPairing.wv (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hu := by
  set hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  obtain ⟨r, hr, u, hu, hru⟩ :=
    Submodule.mem_sup.mp ((jointSpan hx0 D).starProjection_apply_mem (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℝ).1 hu
  obtain ⟨v', hv', hrv, -⟩ := Cvs.WeilForm.EvenExplicitFormulaTameTests.exists_tame_of_mem_R1 hx hr
  have hC : ContDiff ℝ 1 (fun s => kprof σ D c (s - Real.log x / 2)) := by
    unfold kprof Cvs.StepA.OneZeroParitySectors.ve Cvs.StepA.OneZeroParitySectors.ue; fun_prop
  have hbt := Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 hC
  have hb : Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ) - u = Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hbt := by
    apply Cvs.StepA.Edge.FiniteTopCorrectedClosing.dom_ext_ae
    rw [← hc]
    filter_upwards [Cvs.StepA.Edge.FiniteTopCorrectedClosing.toLp_comb_ae hx0 σ D c, Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 hbt] with s h1 h2
    rw [h1, h2, Cvs.Route.Visibility.ZeroPairingVector.fv_ofWin hx0]
  refine ⟨_, Cvs.WeilForm.InsideFunctionTame.tame_sub hbt hv', ?_⟩
  rw [Cvs.WeilForm.ZeroSidePolarized.wv_sub hx0 hbt hv', ← hb, ← hrv, wJoint, ← hru]
  abel

/-- **`Q_x` of the joint residue**: with the `U` sum of `w` summable,
`Q_x(w) ≤ Σ_{ρ ∉ D} m_ρ⟪w, U_ρ⟫² − W_σ‖w‖⁴`. -/
theorem Qx_wJoint_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (D : Finset nonTrivialZeroSet) (σ : nonTrivialZeroSet)
    (hS : Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪wJoint (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) D σ, ueVec (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2) :
    Qx x (wJoint (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) D σ)
      ≤ ∑' ρ : ↥((D : Set nonTrivialZeroSet)ᶜ), (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ)
          * ⟪wJoint (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) D σ,
              ueVec (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        - quadWeight σ * ‖wJoint (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) D σ‖ ^ 4 := by
  set hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  obtain ⟨u, hu, hw⟩ := exists_tame_wJoint hx D σ
  have hQ := Cvs.Route.Visibility.VisibilityClosingStep.Qx_le_tsum_ue_sub (Cvs.StepA.LowEigenvalueCountSpine.two_le hx) hx0 hu (wJoint_mem hx0 D σ).1 hw σ hS
  exact Q_le_off_sub_of_joint (jointSpan hx0 D) _ (fun ρ => ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))
    (fun ρ => (Cvs.Criterion.divisorWeight ρ : ℝ)) (D : Set nonTrivialZeroSet)
    (fun ρ hρ => (le_sup_right : USpan hx0 D ≤ jointSpan hx0 D) (Submodule.subset_span ⟨ρ, hρ, rfl⟩))
    (Qx x) hQ

/-- **The closing step for the joint residue at one `x`**: at `80 ≤ 2πx`, a summable `U` sum of `w` with
`Σ_{ρ ∉ D} m_ρ⟪w, U_ρ⟫² < W_σ‖w‖⁴` gives `¬ EvenBulkFloor x 0`. -/
theorem not_evenBulkFloor_of_joint {x : ℕ} (hx : 80 ≤ 2 * π * x) (D : Finset nonTrivialZeroSet)
    (σ : nonTrivialZeroSet)
    (hS : Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪wJoint (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) D σ, ueVec (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
    (hoff : ∑' ρ : ↥((D : Set nonTrivialZeroSet)ᶜ), (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ)
          * ⟪wJoint (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) D σ,
              ueVec (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        < quadWeight σ * ‖wJoint (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) D σ‖ ^ 4) :
    ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  have h := Qx_wJoint_le hx D σ hS
  obtain ⟨hE, hR⟩ := wJoint_mem (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) D σ
  exact (Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor.not_evenBulkFloor_zero_iff x).2 ⟨_, hE, hR, by linarith⟩

end Joint

/-! ### The rates and the joint share -/

section Rates

set_option synthInstance.maxHeartbeats 400000

/-- The pairing vector `V_σ` at `x`. -/
abbrev Vσ {x : ℕ} (hx0 : (0 : ℝ) < x) (σ : nonTrivialZeroSet) : Dom x :=
  Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)

/-- **The free share `r`** of `V_σ` off `span U_{D(x)}`: at all large `x`, `r‖V_σ‖² ≤ ‖V_σ − P_{U_{D(x)}}V_σ‖²`. -/
def FreeShare (σ : nonTrivialZeroSet) (D : ℕ → Finset nonTrivialZeroSet) (r : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x, r * ‖Vσ hx0 σ‖ ^ 2 ≤ ‖bPerp hx0 (D x) σ‖ ^ 2

/-- **The normalised pairing rate at `σ`**: for every `ε > 0`, at all large `x`, `|⟪a, V_σ⟫| ≤ ε‖V_σ‖‖a‖` on `R₁`. -/
def PairingRate (σ : nonTrivialZeroSet) : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x, ∀ a ∈ R1 x, |⟪a, Vσ hx0 σ⟫_ℝ| ≤ ε * ‖Vσ hx0 σ‖ * ‖a‖

/-- The angle cosine `θ_x = ‖P_{U_D}P_{R₁}‖` between `R₁` and `span U_D`. -/
def angle {x : ℕ} (hx0 : (0 : ℝ) < x) (D : Finset nonTrivialZeroSet) : ℝ :=
  ‖(USpan hx0 D).starProjection ∘L (R1 x).starProjection‖

/-- `‖P_{U_D}a‖ ≤ θ_x‖a‖` on `R₁`. -/
theorem norm_starProjection_le_angle {x : ℕ} (hx0 : (0 : ℝ) < x) (D : Finset nonTrivialZeroSet)
    {a : Dom x} (ha : a ∈ R1 x) : ‖(USpan hx0 D).starProjection a‖ ≤ angle hx0 D * ‖a‖ :=
  norm_starProjection_le_opNorm_comp (R1 x) (USpan hx0 D) ha

/-- **The angle bound `η`**: at all large `x`, `θ_x² ≤ η` for the deep set `D(x)`. -/
def AngleBound (D : ℕ → Finset nonTrivialZeroSet) (η : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x, angle hx0 (D x) ^ 2 ≤ η

/-- **The deep joint share**: some `s₀ > 0` has `s₀‖V_σ‖² ≤ ‖V_σ − P_{R₁ ⊔ U_{D(x)}}V_σ‖²` at all large `x`. -/
def DeepJointShare (σ : nonTrivialZeroSet) (D : ℕ → Finset nonTrivialZeroSet) : Prop :=
  ∃ s₀ > 0, ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x, s₀ * ‖Vσ hx0 σ‖ ^ 2 ≤ ‖wJoint hx0 (D x) σ‖ ^ 2

/-- **The shallow rate**: the `U` sum of the joint residue is summable and its part off `D(x)` is `o(‖V_σ‖⁴)`. -/
def ShallowRate (σ : nonTrivialZeroSet) (D : ℕ → Finset nonTrivialZeroSet) : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
    (Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪wJoint hx0 (D x) σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
    ∧ ∑' ρ : ↥((D x : Set nonTrivialZeroSet)ᶜ), (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ)
        * ⟪wJoint hx0 (D x) σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 ≤ ε * ‖Vσ hx0 σ‖ ^ 4

/-- **`DeepJointShare` from the free share, the pairing rate and the angle bound**: `η < r` gives the share
`s₀ = (r − η)/2`. -/
theorem deepJointShare_of_rates {σ : nonTrivialZeroSet} {D : ℕ → Finset nonTrivialZeroSet} {r η : ℝ}
    (hr : FreeShare σ D r) (hk : PairingRate σ) (hθ : AngleBound D η) (hηr : η < r) : DeepJointShare σ D := by
  set κ := min 1 ((r - η) / 6) with hκdef
  have hκ0 : 0 < κ := lt_min one_pos (by linarith)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκ2 : κ ≤ (r - η) / 6 := min_le_right _ _
  refine ⟨(r - η) / 2, by linarith, ?_⟩
  filter_upwards [hr, hk κ hκ0, hθ] with x h1 h2 h3 hx0
  set V := Vσ hx0 σ
  rcases (norm_nonneg V).eq_or_lt with hV0 | hVpos
  · rw [← hV0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]; positivity
  have hb := Cvs.StepA.Edge.FiniteTopCorrectedClosing.norm_bPerp_sq_le hx0 (D x) σ
  have hr1 : r ≤ 1 := by
    have := (h1 hx0).trans hb
    nlinarith [pow_pos hVpos 2]
  set θ := angle hx0 (D x)
  have hθ0 : 0 ≤ θ := norm_nonneg _
  have hθ2 : θ ^ 2 ≤ η := h3 hx0
  have hθ1 : θ < 1 := by nlinarith
  have h := joint_share_ge (R1 x) (USpan hx0 (D x)) V hθ0 hθ1 hκ0.le (h1 hx0)
    (fun a ha => norm_starProjection_le_angle hx0 (D x) ha) (h2 hx0)
  have hden : 0 < 1 - θ ^ 2 := by nlinarith
  have hnum : (r - η) / 2 ≤ r - θ ^ 2 - κ * (κ + 2) := by nlinarith
  have hq : (r - η) / 2 ≤ (r - θ ^ 2 - κ * (κ + 2)) / (1 - θ ^ 2) := by
    rw [le_div_iff₀ hden]; nlinarith [sq_nonneg θ]
  exact (mul_le_mul_of_nonneg_right hq (sq_nonneg _)).trans h

/-- `V_σ ≠ 0` for an off-line `σ` and `x > 1`. -/
theorem Vσ_ne_zero {x : ℕ} (hx0 : (0 : ℝ) < x) (hx : 1 < x) {σ : nonTrivialZeroSet}
    (hσ : Cvs.GaussKernel.del σ ≠ 0) : Vσ hx0 σ ≠ 0 := by
  refine Cvs.Route.Visibility.ZeroPairingVector.pairVec_ne_zero hx0 hx ?_ ?_
  · rw [Cvs.ZeroCounting.zPoint_re]; exact Cvs.StepA.LowEigenvalueCountZeros.im_ne_zero σ
  · rw [Cvs.ZeroCounting.zPoint_im]; exact neg_ne_zero.2 hσ

/-- **The joint share and the shallow rate close eventually**: for an off-line `σ`, `DeepJointShare σ D` and
`ShallowRate σ D` give `¬ EvenBulkFloor x 0` at all large `x`. -/
theorem eventually_not_evenBulkFloor_of_joint {σ : nonTrivialZeroSet} (hσ : Cvs.GaussKernel.del σ ≠ 0)
    {D : ℕ → Finset nonTrivialZeroSet} (hJ : DeepJointShare σ D) (hS : ShallowRate σ D) :
    ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  obtain ⟨s₀, hs₀, hJ⟩ := hJ
  filter_upwards [hJ, hS (s₀ ^ 2 / 2) (by positivity), eventually_ge_atTop 14] with x h1 h2 h14
  have hx := Cvs.Route.Visibility.VisibilityClosingStep.scale_of_ge h14
  obtain ⟨hsum, hoff⟩ := h2 (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
  refine not_evenBulkFloor_of_joint hx (D x) σ hsum (hoff.trans_lt ?_)
  generalize Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx = hx0 at h1 hsum hoff ⊢
  have hV : 0 < ‖Vσ hx0 σ‖ := norm_pos_iff.2 (Vσ_ne_zero hx0 (by omega) hσ)
  have hw := h1 hx0
  have hW : 1 ≤ quadWeight σ := Cvs.StepA.TopQuadruple.one_le_quadWeight σ
  have hV4 : 0 < ‖Vσ hx0 σ‖ ^ 4 := by positivity
  have hsq : (s₀ * ‖Vσ hx0 σ‖ ^ 2) ^ 2 ≤ (‖wJoint hx0 (D x) σ‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hw 2
  have hw4 : 0 ≤ ‖wJoint hx0 (D x) σ‖ ^ 4 := by positivity
  have e1 : (s₀ * ‖Vσ hx0 σ‖ ^ 2) ^ 2 = s₀ ^ 2 * ‖Vσ hx0 σ‖ ^ 4 := by ring
  have e2 : (‖wJoint hx0 (D x) σ‖ ^ 2) ^ 2 = ‖wJoint hx0 (D x) σ‖ ^ 4 := by ring
  rw [e1, e2] at hsq
  have hWw : ‖wJoint hx0 (D x) σ‖ ^ 4 ≤ quadWeight σ * ‖wJoint hx0 (D x) σ‖ ^ 4 := le_mul_of_one_le_left hw4 hW
  have hp : 0 < s₀ ^ 2 * ‖Vσ hx0 σ‖ ^ 4 := by positivity
  have key : s₀ ^ 2 / 2 * ‖Vσ hx0 σ‖ ^ 4 < quadWeight σ * ‖wJoint hx0 (D x) σ‖ ^ 4 := by linarith
  exact key

/-- **The pairing rate from `ShareBesselFromExtPairing`'s exterior pairing rate** and a growth `β x^δ ≤ ‖V_σ‖²`, for `σ ∈ S`. -/
theorem pairingRate_of_extPairingRate {S : Finset nonTrivialZeroSet} {δ : ℝ} {K : ℕ → ℝ}
    {σ : nonTrivialZeroSet} (hσ : σ ∈ S) (hK : Cvs.Route.Visibility.ShareBesselFromExtPairing.ExtPairingRate S δ K)
    (hV : ∃ β > 0, ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x, β * (x : ℝ) ^ δ ≤ ‖Vσ hx0 σ‖ ^ 2) :
    PairingRate σ := by
  obtain ⟨hK0, hKe, hKo⟩ := hK
  obtain ⟨β, hβ, hV⟩ := hV
  intro ε hε
  filter_upwards [hKe, hKo (ε ^ 2 * β) (by positivity), hV, eventually_ge_atTop 14]
    with x h1 h2 h3 h14 hx0 a ha
  have hx := Cvs.Route.Visibility.VisibilityClosingStep.scale_of_ge h14
  obtain ⟨c, rfl, hp⟩ := Cvs.Route.Visibility.SpinePairingExteriorTransform.inner_R1_pairVec hx hx0 ha
  have hKV : K x ≤ ε * ‖Vσ hx0 σ‖ := by
    have : K x ^ 2 ≤ (ε * ‖Vσ hx0 σ‖) ^ 2 := by
      rw [mul_pow]; nlinarith [h3 hx0]
    exact (pow_le_pow_iff_left₀ (hK0 x) (by positivity) two_ne_zero).1 this
  rw [hp σ, abs_div, abs_two]
  have := (Complex.abs_im_le_norm _).trans (h1 σ hσ c)
  have hn := norm_nonneg (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x c))
  nlinarith [mul_le_mul_of_nonneg_right hKV hn]

/-- **The pairing vector grows like `x^{|y|}`**: with `a = |Im z|`, `R = ‖z‖`, `L = log x`, for `Re z, Im z ≠ 0`,
`sinh(aL)/a − 2L − cosh(aL)/R − a/R² ≤ 4‖V_z‖²`. -/
theorem four_mul_norm_sq_pairVec_ge_abs {x : ℕ} (hx0 : (0 : ℝ) < x) {z : ℂ} (hre : z.re ≠ 0) (hy : z.im ≠ 0) :
    sinh (|z.im| * Real.log x) / |z.im| - 2 * Real.log x - cosh (|z.im| * Real.log x) / ‖z‖
        - |z.im| / ‖z‖ ^ 2 ≤ 4 * ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 z‖ ^ 2 := by
  have hL : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  have hexact := Cvs.Route.Visibility.ZeroPairingVector.norm_sq_pairVec hx0 hy
  generalize ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 z‖ ^ 2 = P at hexact ⊢
  generalize Real.log x = L at hL hexact ⊢
  set a := |z.im| with ha
  set γ := z.re
  have ha0 : 0 < a := abs_pos.2 hy
  have hR2 : ‖z‖ ^ 2 = γ ^ 2 + a ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ha, sq_abs]; ring
  have hR : 0 < ‖z‖ := norm_pos_iff.2 fun h => hre (by simp [γ, h])
  have e1 : sinh (z.im * L) / z.im = sinh (a * L) / a ∧ z.im * sinh (z.im * L) = a * sinh (a * L)
      ∧ cosh (z.im * L) = cosh (a * L) := by
    rcases abs_choice z.im with h | h <;> rw [ha, h]
    · exact ⟨rfl, rfl, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [neg_mul, Real.sinh_neg, neg_div_neg_eq]
      · rw [show -z.im * L = -(z.im * L) by ring, Real.sinh_neg]; ring
      · rw [neg_mul, Real.cosh_neg]
  obtain ⟨e1, e2, e3⟩ := e1
  have hsq : z.re ^ 2 + z.im ^ 2 = γ ^ 2 + a ^ 2 := by rw [ha, sq_abs]
  rw [e1, hsq, ← hR2] at hexact
  have hnum : z.re * sin (z.re * L) * cosh (z.im * L) + z.im * cos (z.re * L) * sinh (z.im * L)
      = (γ * sin (γ * L) + a * cos (γ * L)) * cosh (a * L) - a * cos (γ * L) * (cosh (a * L) - sinh (a * L)) := by
    rw [e3, mul_comm z.im (cos _), mul_assoc (cos _), e2]; ring
  rw [hnum] at hexact
  have hcs : γ * sin (γ * L) + a * cos (γ * L) ≤ ‖z‖ := by
    have h2 : (γ * sin (γ * L) + a * cos (γ * L)) ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [hR2]; nlinarith [sq_nonneg (γ * cos (γ * L) - a * sin (γ * L)), Real.sin_sq_add_cos_sq (γ * L)]
    exact abs_le_of_sq_le_sq' h2 hR.le |>.2
  have hch : 0 ≤ cosh (a * L) := (Real.cosh_pos _).le
  have hcs2 : cosh (a * L) - sinh (a * L) ≤ 1 := by
    rw [Real.cosh_sub_sinh]; exact Real.exp_le_one_iff.2 (by nlinarith)
  have hcs3 : 0 ≤ cosh (a * L) - sinh (a * L) := by rw [Real.cosh_sub_sinh]; exact (Real.exp_pos _).le
  have hT : (γ * sin (γ * L) + a * cos (γ * L)) * cosh (a * L) - a * cos (γ * L) * (cosh (a * L) - sinh (a * L))
      ≤ ‖z‖ * cosh (a * L) + a := by
    have h1 := mul_le_mul_of_nonneg_right hcs hch
    have h2 : -(a * cos (γ * L) * (cosh (a * L) - sinh (a * L))) ≤ a := by
      have := Real.neg_one_le_cos (γ * L)
      have := Real.cos_le_one (γ * L)
      nlinarith [mul_nonneg ha0.le hcs3]
    linarith
  have hdiv : ((γ * sin (γ * L) + a * cos (γ * L)) * cosh (a * L)
        - a * cos (γ * L) * (cosh (a * L) - sinh (a * L))) / ‖z‖ ^ 2
      ≤ cosh (a * L) / ‖z‖ + a / ‖z‖ ^ 2 := by
    rw [div_add_div _ _ hR.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hT (by positivity : 0 ≤ ‖z‖ * ‖z‖ ^ 2)
    nlinarith
  have hs : -L ≤ L * Real.sinc (γ * L) := by
    have := Real.neg_one_le_sinc (γ * L); nlinarith
  rw [hexact]
  linarith

/-- **`‖V_z‖² ≥ β x^{|Im z|}` eventually**, with `β = (1/|Im z| − 1/‖z‖)/16 > 0`, for `Re z, Im z ≠ 0`. -/
theorem exists_norm_sq_pairVec_ge {z : ℂ} (hre : z.re ≠ 0) (hy : z.im ≠ 0) :
    ∃ β > 0, ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x, β * (x : ℝ) ^ |z.im| ≤ ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 z‖ ^ 2 := by
  set a := |z.im| with ha
  have ha0 : 0 < a := abs_pos.2 hy
  have hR : 0 < ‖z‖ := norm_pos_iff.2 fun h => hre (by rw [h]; simp)
  have haR : a < ‖z‖ := Complex.abs_im_lt_norm.2 hre
  set c := (1 / a - 1 / ‖z‖) / 2 with hc
  have hc0 : 0 < c := by
    rw [hc]; have : 1 / ‖z‖ < 1 / a := one_div_lt_one_div_of_lt ha0 haR; linarith
  set C0 := 1 / (2 * a) + 1 / (2 * ‖z‖) + a / ‖z‖ ^ 2 with hC0
  have hC00 : 0 ≤ C0 := by positivity
  set L0 := max 1 (4 * (2 + C0) / (c * a ^ 2)) with hL0
  refine ⟨c / 8, by positivity, ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop L0)
  filter_upwards [hlog, eventually_gt_atTop 0] with x hxL hxpos hx0
  simp only [Function.comp_apply] at hxL
  set L := Real.log x
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hxL
  have hL2 : 4 * (2 + C0) / (c * a ^ 2) ≤ L := (le_max_right _ _).trans hxL
  have h4 := four_mul_norm_sq_pairVec_ge_abs hx0 hre hy
  set E := Real.exp (a * L) with hE
  have hxa : (x : ℝ) ^ a = E := by rw [Real.rpow_def_of_pos hx0, mul_comm]
  rw [hxa]
  have hEinv : Real.exp (-(a * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hEinv0 : 0 ≤ Real.exp (-(a * L)) := (Real.exp_pos _).le
  have hsh : sinh (a * L) / a ≥ E / (2 * a) - 1 / (2 * a) := by
    rw [Real.sinh_eq, ge_iff_le, ← sub_div, div_le_div_iff₀ (by positivity) ha0]
    nlinarith
  have hch : cosh (a * L) / ‖z‖ ≤ E / (2 * ‖z‖) + 1 / (2 * ‖z‖) := by
    rw [Real.cosh_eq, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hquad : (a * L) ^ 2 / 2 ≤ E := by
    have := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ a * L)
    nlinarith [mul_pos ha0 (by linarith : (0:ℝ) < L)]
  have hcE : c * E - C0 - 2 * L ≥ c / 2 * E := by
    have hb : 4 * (2 + C0) ≤ L * (c * a ^ 2) := by rwa [div_le_iff₀ (by positivity)] at hL2
    have : 2 + C0 ≤ c * (a * L) ^ 2 / 4 := by nlinarith
    nlinarith
  have hsplit : E / (2 * a) - E / (2 * ‖z‖) = c * E := by rw [hc]; field_simp
  have : c * E - C0 - 2 * L ≤ 4 * ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 z‖ ^ 2 := by
    have : C0 = 1 / (2 * a) + 1 / (2 * ‖z‖) + a / ‖z‖ ^ 2 := hC0
    linarith
  nlinarith

/-- **The pairing rate from `ShareBesselFromExtPairing`'s exterior pairing rate** at depth `|δ_σ|`, for an off-line `σ ∈ S`. -/
theorem pairingRate_of_extPairingRate_offLine {S : Finset nonTrivialZeroSet} {K : ℕ → ℝ} {σ : nonTrivialZeroSet}
    (hσ0 : Cvs.GaussKernel.del σ ≠ 0) (hσ : σ ∈ S) (hK : Cvs.Route.Visibility.ShareBesselFromExtPairing.ExtPairingRate S |Cvs.GaussKernel.del σ| K) :
    PairingRate σ := by
  refine pairingRate_of_extPairingRate hσ hK ?_
  have hre : (Cvs.ZeroCounting.zPoint σ).re ≠ 0 := by
    rw [Cvs.ZeroCounting.zPoint_re]; exact Cvs.StepA.LowEigenvalueCountZeros.im_ne_zero σ
  have him : (Cvs.ZeroCounting.zPoint σ).im ≠ 0 := by
    rw [Cvs.ZeroCounting.zPoint_im]; exact neg_ne_zero.2 hσ0
  have habs : |(Cvs.ZeroCounting.zPoint σ).im| = |Cvs.GaussKernel.del σ| := by
    rw [Cvs.ZeroCounting.zPoint_im, abs_neg]; rfl
  obtain ⟨β, hβ, h⟩ := exists_norm_sq_pairVec_ge hre him
  exact ⟨β, hβ, by rw [← habs]; exact h⟩

end Rates

end Cvs.StepA.Edge.DeepJointShare

end
