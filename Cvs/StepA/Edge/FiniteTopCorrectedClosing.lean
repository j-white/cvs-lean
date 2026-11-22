import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.EvenSectionContinuation
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.Edge.DampedEdgeGram
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.TwoEdgeSplit
import Cvs.StepA.LowEigenvalueCountSpine
import Cvs.StepA.LowEigenvalueCountZeros
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.TopQuadruple
import Cvs.WeilForm.EvenExplicitFormulaTameTests
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InsideFunctionTame
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.TameClassesFormDense
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.ZeroSidePolarized
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.WeightedRateLemma
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
# The closing step with the `U`-corrected pairing vector of a finite top set

For a finite top set `S` at depth `δ` and `σ ∈ S`, `b⊥ = V_σ − P_{span U_S} V_σ` is reflection-even, orthogonal to
every `U_ρ`, `ρ ∈ S`, and `V_σ = b⊥ + Σ_{r ∈ R} a_r U_r` over one zero per ordinate. The edge Gram of Cvs.StepA.Edge.DampedEdgeGram gives
`‖b⊥‖² ≥ θ‖V_σ‖²` eventually for every `θ < κ/Λ`, `‖b⊥‖² ≥ (κ/16)x^δ` and `Σ a_r² ≤ 16Λ/κ`; with a share, a
Bessel sum at `P_{R₁}b⊥` and the off-`S` rest both `o(x^{2δ})`, `EvenBulkFloor x 0` fails eventually.
-/

noncomputable section

open Real MeasureTheory Filter Set Matrix
open scoped InnerProductSpace
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.StepA.OneZeroParitySectors (ue ve)
open Cvs.StepA.TopQuadruple (quadWeight)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec ueProf)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.StepA.Edge.FiniteTopCorrectedClosing
open Cvs.ZeroCounting

/-! ### The closing step in an inner product space -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (R : Submodule ℝ E)
  [R.HasOrthogonalProjection] {ι : Type*}

/-- Weighted Cauchy–Schwarz over a finite set: `|Σ_s aᵢyᵢ| ≤ √(Σ_s aᵢ²/mᵢ)·√(Σ_s mᵢyᵢ²)` for `m > 0` on `s`. -/
theorem abs_sum_mul_le (s : Finset ι) {m a y : ι → ℝ} (hm : ∀ i ∈ s, 0 < m i) :
    |∑ i ∈ s, a i * y i| ≤ √(∑ i ∈ s, a i ^ 2 / m i) * √(∑ i ∈ s, m i * y i ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => a i / √(m i)) (fun i => √(m i) * y i)
  have e1 : ∑ i ∈ s, a i / √(m i) * (√(m i) * y i) = ∑ i ∈ s, a i * y i :=
    Finset.sum_congr rfl fun i hi => by
      have : √(m i) ≠ 0 := (Real.sqrt_pos.2 (hm i hi)).ne'
      field_simp
  have e2 : ∑ i ∈ s, (a i / √(m i)) ^ 2 = ∑ i ∈ s, a i ^ 2 / m i :=
    Finset.sum_congr rfl fun i hi => by rw [div_pow, Real.sq_sqrt (hm i hi).le]
  have e3 : ∑ i ∈ s, (√(m i) * y i) ^ 2 = ∑ i ∈ s, m i * y i ^ 2 :=
    Finset.sum_congr rfl fun i hi => by rw [mul_pow, Real.sq_sqrt (hm i hi).le]
  rw [e1, e2, e3] at hcs
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hm i hi).le),
    ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hcs

/-- **The closing step with a corrected vector, raw form**: if `V = b + Σ_s aᵢUᵢ`, `w = b − P_R b`,
`Q(w) ≤ Σ mᵢ⟪w, Uᵢ⟫² − W⟪w, V⟫²`, `‖P_R b‖² ≤ (1 − s₀)‖b‖²`, `Σ mᵢ⟪P_R b, Uᵢ⟫² ≤ C_P`, `Σ mᵢ⟪b, Uᵢ⟫² ≤ E_b`,
`Σ_s aᵢ²/mᵢ ≤ A²`, `A·X ≤ s₀‖b‖²` and `X² < W(s₀‖b‖² − A·X)²` with `X = √E_b + √C_P`, then `Q(w) < 0`. -/
theorem neg_of_perp_closing_raw {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) (U : ι → E) (s : Finset ι)
    (hms : ∀ i ∈ s, 0 < m i) (a : ι → ℝ) {V b : E} (hV : V = b + ∑ i ∈ s, a i • U i)
    {Q : E → ℝ} {W s₀ Cp Eb A : ℝ} (hW : 0 ≤ W)
    (hQ : Q (b - R.starProjection b)
      ≤ ∑' i, m i * ⟪b - R.starProjection b, U i⟫_ℝ ^ 2 - W * ⟪b - R.starProjection b, V⟫_ℝ ^ 2)
    (hshare : ‖R.starProjection b‖ ^ 2 ≤ (1 - s₀) * ‖b‖ ^ 2)
    (hpS : Summable fun i => m i * ⟪R.starProjection b, U i⟫_ℝ ^ 2)
    (hpB : ∑' i, m i * ⟪R.starProjection b, U i⟫_ℝ ^ 2 ≤ Cp)
    (hbS : Summable fun i => m i * ⟪b, U i⟫_ℝ ^ 2) (hbE : ∑' i, m i * ⟪b, U i⟫_ℝ ^ 2 ≤ Eb)
    (hA : ∑ i ∈ s, a i ^ 2 / m i ≤ A ^ 2) (hA0 : 0 ≤ A)
    (hX : A * (√Eb + √Cp) ≤ s₀ * ‖b‖ ^ 2)
    (hclose : (√Eb + √Cp) ^ 2 < W * (s₀ * ‖b‖ ^ 2 - A * (√Eb + √Cp)) ^ 2) :
    Q (b - R.starProjection b) < 0 := by
  set P := R.starProjection b with hP
  set w := b - P with hw
  set X := √Eb + √Cp with hXdef
  obtain ⟨hwS, hwT⟩ := Cvs.Route.Visibility.VisibilityClosingStep.tsum_mul_sub_sq_le (m := m)
    (a := fun i => ⟪b, U i⟫_ℝ) (c := fun i => ⟪P, U i⟫_ℝ) hm hbS hpS
  have hfun : (fun i => m i * ⟪w, U i⟫_ℝ ^ 2) = fun i => m i * (⟪b, U i⟫_ℝ - ⟪P, U i⟫_ℝ) ^ 2 :=
    funext fun i => by rw [hw, inner_sub_left]
  set T := ∑' i, m i * ⟪w, U i⟫_ℝ ^ 2 with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun i => mul_nonneg (hm i) (sq_nonneg _)
  have hTX : √T ≤ X := by
    have h1 : T ≤ (√(∑' i, m i * ⟪b, U i⟫_ℝ ^ 2) + √(∑' i, m i * ⟪P, U i⟫_ℝ ^ 2)) ^ 2 := by
      rw [hT, hfun]; exact hwT
    have h2 : √(∑' i, m i * ⟪b, U i⟫_ℝ ^ 2) ≤ √Eb := Real.sqrt_le_sqrt hbE
    have h3 : √(∑' i, m i * ⟪P, U i⟫_ℝ ^ 2) ≤ √Cp := Real.sqrt_le_sqrt hpB
    calc √T ≤ √(∑' i, m i * ⟪b, U i⟫_ℝ ^ 2) + √(∑' i, m i * ⟪P, U i⟫_ℝ ^ 2) := by
          rw [Real.sqrt_le_left (by positivity)]; exact h1
      _ ≤ X := add_le_add h2 h3
  have hX0 : 0 ≤ X := by positivity
  have hTle : T ≤ X ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg T) hTX 2
    rwa [Real.sq_sqrt hT0] at this
  obtain ⟨hnorm, hwb⟩ := Cvs.Route.Visibility.VisibilityClosingStep.sub_starProjection_facts R b
  have hwV : ⟪w, V⟫_ℝ = ‖w‖ ^ 2 + ∑ i ∈ s, a i * ⟪w, U i⟫_ℝ := by
    rw [hV, inner_add_right, inner_sum]
    simp only [inner_smul_right]
    rw [show ⟪w, b⟫_ℝ = ‖w‖ ^ 2 from hwb]
  have hcorr : |∑ i ∈ s, a i * ⟪w, U i⟫_ℝ| ≤ A * X := by
    refine (abs_sum_mul_le s hms).trans ?_
    have hwS' : Summable fun i => m i * ⟪w, U i⟫_ℝ ^ 2 := by rw [hfun]; exact hwS
    have hsT : ∑ i ∈ s, m i * ⟪w, U i⟫_ℝ ^ 2 ≤ T :=
      hwS'.sum_le_tsum s (fun i _ => mul_nonneg (hm i) (sq_nonneg _))
    exact mul_le_mul (by rw [Real.sqrt_le_left hA0]; exact hA)
        ((Real.sqrt_le_sqrt (hsT.trans hTle)).trans_eq (Real.sqrt_sq hX0)) (Real.sqrt_nonneg _) hA0
  have hlow : s₀ * ‖b‖ ^ 2 ≤ ‖w‖ ^ 2 := by rw [hnorm]; linarith
  have hpos : s₀ * ‖b‖ ^ 2 - A * X ≤ ⟪w, V⟫_ℝ := by
    rw [hwV]; linarith [neg_abs_le (∑ i ∈ s, a i * ⟪w, U i⟫_ℝ)]
  have hsq : (s₀ * ‖b‖ ^ 2 - A * X) ^ 2 ≤ ⟪w, V⟫_ℝ ^ 2 :=
    pow_le_pow_left₀ (by linarith) hpos 2
  have := mul_le_mul_of_nonneg_left hsq hW
  have hQ' : Q w ≤ T - W * ⟪w, V⟫_ℝ ^ 2 := hQ
  linarith

end Abstract

/-! ### The `ue` vectors -/

/-- The `L²` class of a form-domain element at `x`. -/
abbrev toLp {x : ℕ} (u : Dom x) : Lp ℝ 2 (volume : Measure ℝ) :=
  ((u : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))

/-- Form-domain elements with a.e. equal classes are equal. -/
theorem dom_ext_ae {x : ℕ} {u v : Dom x} (h : toLp u =ᵐ[volume] toLp v) : u = v := by
  apply Subtype.ext; apply Subtype.ext; exact Lp.ext h

/-- **The `ue` vector is reflection-even**. -/
theorem ueVec_mem_Ev {x : ℕ} (hx0 : (0 : ℝ) < x) (z : ℂ) : ueVec hx0 z ∈ Ev x := by
  show Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) (ueVec hx0 z) = ueVec hx0 z
  apply Subtype.ext; apply Subtype.ext
  show Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) (((ueVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
      : Lp ℝ 2 (volume : Measure ℝ))
    = (((ueVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))
  apply Lp.ext
  have h2 := (Measure.measurePreserving_sub_left volume (Real.log x)).quasiMeasurePreserving.ae_eq_comp
    (Cvs.Route.Visibility.VisibilityClosingStep.coe_ueVec_ae hx0 z)
  filter_upwards [Cvs.WeilForm.WindowReflectionSymmetry.refl_ae (Real.log x) _, h2, Cvs.Route.Visibility.VisibilityClosingStep.coe_ueVec_ae hx0 z,
    (Set.countable_singleton (0 : ℝ)).ae_notMem volume,
    (Set.countable_singleton (Real.log x)).ae_notMem volume] with s h1 h2 h3 h4 h5
  rw [h1, h3]
  simp only [Function.comp_apply] at h2
  rw [h2]
  have h4 : s ≠ 0 := h4
  have h5 : s ≠ Real.log x := h5
  have hmem : Real.log x - s ∈ Ico 0 (Real.log x) ↔ s ∈ Ico 0 (Real.log x) := by
    simp only [mem_Ico]
    constructor
    · rintro ⟨a, b⟩; exact ⟨by linarith, lt_of_le_of_ne (by linarith) h5⟩
    · rintro ⟨a, b⟩; exact ⟨by linarith, by
        rcases lt_or_eq_of_le a with a | a
        · linarith
        · exact absurd a.symm h4⟩
  by_cases hs : s ∈ Ico 0 (Real.log x)
  · rw [indicator_of_mem (hmem.2 hs), indicator_of_mem hs, ueProf, ueProf, ← Cvs.StepA.OneZeroParitySectors.ue_neg]
    congr 1; ring
  · rw [indicator_of_notMem (fun h => hs (hmem.1 h)), indicator_of_notMem hs]

/-- The size `|γ_ρ|` of the ordinate of a zero. -/
def ordG (ρ : nonTrivialZeroSet) : ℝ := |(ρ : ℂ).im|

/-- `ue_{z_ρ}(t) = cos(|γ_ρ|t)·cosh(|δ_ρ|t)`. -/
theorem ue_zPoint (ρ : nonTrivialZeroSet) (t : ℝ) :
    ue (Cvs.ZeroCounting.zPoint ρ) t = cos (ordG ρ * t) * cosh (|Cvs.GaussKernel.del ρ| * t) := by
  simp only [ue, Cvs.ZeroCounting.zPoint_re, Cvs.ZeroCounting.zPoint_im, ordG]
  rw [show (ρ : ℂ).re - 1 / 2 = Cvs.GaussKernel.del ρ from rfl]
  rcases abs_choice (ρ : ℂ).im with h | h <;> rcases abs_choice (Cvs.GaussKernel.del ρ) with h' | h' <;>
    rw [h, h'] <;> simp [neg_mul, Real.cos_neg, Real.cosh_neg]

/-- `ve_{z_ρ}(t) = s·sin(|γ_ρ|t)·sinh(|δ_ρ|t)` for a sign `s`. -/
theorem ve_zPoint (ρ : nonTrivialZeroSet) : ∃ s : ℝ, s ^ 2 = 1 ∧ ∀ t,
    ve (Cvs.ZeroCounting.zPoint ρ) t = s * (sin (ordG ρ * t) * sinh (|Cvs.GaussKernel.del ρ| * t)) := by
  simp only [ve, Cvs.ZeroCounting.zPoint_re, Cvs.ZeroCounting.zPoint_im, ordG]
  rw [show (ρ : ℂ).re - 1 / 2 = Cvs.GaussKernel.del ρ from rfl]
  rcases abs_choice (ρ : ℂ).im with h | h <;> rcases abs_choice (Cvs.GaussKernel.del ρ) with h' | h'
  · exact ⟨-1, by norm_num, fun t => by rw [h, h']; simp [neg_mul, Real.sinh_neg]⟩
  · exact ⟨1, by norm_num, fun t => by rw [h, h']; simp [neg_mul, Real.sinh_neg]⟩
  · exact ⟨1, by norm_num, fun t => by rw [h, h']; simp [neg_mul, Real.sin_neg, Real.sinh_neg]⟩
  · exact ⟨-1, by norm_num, fun t => by rw [h, h']; simp [neg_mul, Real.sin_neg, Real.sinh_neg]⟩

/-- Equal `ue` profiles give equal `ue` vectors. -/
theorem ueVec_congr {x : ℕ} (hx0 : (0 : ℝ) < x) {z z' : ℂ} (h : ∀ t, ue z t = ue z' t) :
    ueVec hx0 z = ueVec hx0 z' := by
  have hp : ueProf x z = ueProf x z' := funext fun s => h _
  apply dom_ext_ae
  filter_upwards [Cvs.Route.Visibility.VisibilityClosingStep.coe_ueVec_ae hx0 z, Cvs.Route.Visibility.VisibilityClosingStep.coe_ueVec_ae hx0 z'] with s h1 h2
  rw [h1, h2, hp]

/-- Zeros with the same `|γ|` and `|δ|` have the same `ue` vector. -/
theorem ueVec_eq_of_ord {x : ℕ} (hx0 : (0 : ℝ) < x) {ρ ρ' : nonTrivialZeroSet} (hg : ordG ρ = ordG ρ')
    (hd : |Cvs.GaussKernel.del ρ| = |Cvs.GaussKernel.del ρ'|) :
    ueVec hx0 (Cvs.ZeroCounting.zPoint ρ) = ueVec hx0 (Cvs.ZeroCounting.zPoint ρ') :=
  ueVec_congr hx0 fun t => by rw [ue_zPoint, ue_zPoint, hg, hd]

/-! ### One zero per ordinate -/

/-- A subset of `S` on which `|γ|` is injective with the same ordinates as `S`. -/
theorem exists_reps (S : Finset nonTrivialZeroSet) :
    ∃ R : Finset nonTrivialZeroSet, R ⊆ S ∧ Set.InjOn ordG R ∧ R.image ordG = S.image ordG := by
  classical
  obtain ⟨u, hu, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (f := ordG)
    (S : Set nonTrivialZeroSet) (S.image ordG) (by
      intro y hy
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨ρ, hρ, rfl⟩)
  exact ⟨u, Finset.coe_subset.1 hu, hinj, himg⟩

/-- One zero of `S` per ordinate `|γ|`. -/
def reps (S : Finset nonTrivialZeroSet) : Finset nonTrivialZeroSet := Classical.choose (exists_reps S)

/-- The representatives lie in `S`. -/
theorem reps_subset (S : Finset nonTrivialZeroSet) : reps S ⊆ S := (Classical.choose_spec (exists_reps S)).1

/-- `|γ|` is injective on the representatives. -/
theorem reps_injOn (S : Finset nonTrivialZeroSet) : Set.InjOn ordG (reps S) :=
  (Classical.choose_spec (exists_reps S)).2.1

/-- Every zero of `S` has a representative with the same `|γ|`. -/
theorem exists_rep_of_mem {S : Finset nonTrivialZeroSet} {ρ : nonTrivialZeroSet} (hρ : ρ ∈ S) :
    ∃ r ∈ reps S, ordG r = ordG ρ := by
  classical
  have h : ordG ρ ∈ (reps S).image ordG := by
    rw [show (reps S).image ordG = S.image ordG from (Classical.choose_spec (exists_reps S)).2.2]
    exact Finset.mem_image_of_mem _ hρ
  obtain ⟨r, hr, e⟩ := Finset.mem_image.1 h
  exact ⟨r, hr, e⟩

/-! ### The `U`-corrected pairing vector -/

/-- The span of the `ue` vectors `U_ρ`, `ρ ∈ S`. -/
def USpan {x : ℕ} (hx0 : (0 : ℝ) < x) (S : Finset nonTrivialZeroSet) : Submodule ℝ (Dom x) :=
  Submodule.span ℝ ((fun ρ => ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)) '' (S : Set nonTrivialZeroSet))

instance {x : ℕ} (hx0 : (0 : ℝ) < x) (S : Finset nonTrivialZeroSet) :
    FiniteDimensional ℝ (USpan hx0 S) :=
  FiniteDimensional.span_of_finite ℝ (S.finite_toSet.image _)

instance {x : ℕ} (hx0 : (0 : ℝ) < x) (S : Finset nonTrivialZeroSet) :
    (USpan hx0 S).HasOrthogonalProjection :=
  haveI : CompleteSpace (USpan hx0 S) := FiniteDimensional.complete ℝ _
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The `U`-corrected pairing vector `b⊥ = V_σ − P_{span U_S} V_σ`. -/
def bPerp {x : ℕ} (hx0 : (0 : ℝ) < x) (S : Finset nonTrivialZeroSet) (σ : nonTrivialZeroSet) : Dom x :=
  Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
    - (USpan hx0 S).starProjection (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ))

/-- The span of the `U_ρ` lies in the reflection-even classes. -/
theorem USpan_le_Ev {x : ℕ} (hx0 : (0 : ℝ) < x) (S : Finset nonTrivialZeroSet) : USpan hx0 S ≤ Ev x :=
  Submodule.span_le.2 fun _ ⟨_, _, e⟩ => e ▸ ueVec_mem_Ev hx0 _

/-- **`b⊥` is reflection-even**. -/
theorem bPerp_mem_Ev {x : ℕ} (hx0 : (0 : ℝ) < x) (S : Finset nonTrivialZeroSet) (σ : nonTrivialZeroSet) :
    bPerp hx0 S σ ∈ Ev x :=
  (Ev x).sub_mem (Cvs.Route.Visibility.ZeroPairingVector.pairVec_mem_Ev hx0 _)
    (USpan_le_Ev hx0 S ((USpan hx0 S).starProjection_apply_mem _))

/-- **`b⊥` is orthogonal to every `U_ρ`, `ρ ∈ S`**. -/
theorem inner_bPerp_ueVec {x : ℕ} (hx0 : (0 : ℝ) < x) {S : Finset nonTrivialZeroSet} (σ : nonTrivialZeroSet)
    {ρ : nonTrivialZeroSet} (hρ : ρ ∈ S) : ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ = 0 :=
  (USpan hx0 S).starProjection_inner_eq_zero _ _ (Submodule.subset_span ⟨ρ, hρ, rfl⟩)

/-- `‖b⊥‖ ≤ ‖V_σ‖`. -/
theorem norm_bPerp_sq_le {x : ℕ} (hx0 : (0 : ℝ) < x) (S : Finset nonTrivialZeroSet) (σ : nonTrivialZeroSet) :
    ‖bPerp hx0 S σ‖ ^ 2 ≤ ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)‖ ^ 2 := by
  have h := (Cvs.Route.Visibility.VisibilityClosingStep.sub_starProjection_facts (USpan hx0 S) (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ))).1
  rw [bPerp, h]
  linarith [sq_nonneg ‖(USpan hx0 S).starProjection (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ))‖]

/-- With `|δ|` constant on `S`, the span of the `U_ρ` over `S` is that over the representatives. -/
theorem USpan_eq_reps {x : ℕ} (hx0 : (0 : ℝ) < x) {S : Finset nonTrivialZeroSet} {δ : ℝ}
    (hS : ∀ ρ ∈ S, |Cvs.GaussKernel.del ρ| = δ) :
    USpan hx0 S = Submodule.span ℝ
      ((fun ρ => ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)) '' (reps S : Set nonTrivialZeroSet)) := by
  unfold USpan
  congr 1
  apply Set.Subset.antisymm
  · rintro _ ⟨ρ, hρ, rfl⟩
    obtain ⟨r, hr, e⟩ := exists_rep_of_mem hρ
    exact ⟨r, hr, ueVec_eq_of_ord hx0 e (by rw [hS r (reps_subset S hr), hS ρ hρ])⟩
  · exact Set.image_mono (Finset.coe_subset.2 (reps_subset S))

/-- **The `Dom` identity**: with `|δ|` constant on `S`, `V_σ = b⊥ + Σ_{r ∈ R} a_r U_r` over the
representatives `R` for some coefficients `a`. -/
theorem exists_coeff {x : ℕ} (hx0 : (0 : ℝ) < x) {S : Finset nonTrivialZeroSet} {δ : ℝ}
    (hS : ∀ ρ ∈ S, |Cvs.GaussKernel.del ρ| = δ) (σ : nonTrivialZeroSet) :
    ∃ a : nonTrivialZeroSet → ℝ, Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
      = bPerp hx0 S σ + ∑ r ∈ reps S, a r • ueVec hx0 (Cvs.ZeroCounting.zPoint r) := by
  have hmem := (USpan hx0 S).starProjection_apply_mem (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℝ).1 ((USpan_eq_reps hx0 hS).le hmem)
  refine ⟨a, ?_⟩
  rw [ha, bPerp, sub_add_cancel]

/-- The `U` sum of `b⊥` is its sum off `S`. -/
theorem tsum_bPerp_eq_off {x : ℕ} (hx0 : (0 : ℝ) < x) (S : Finset nonTrivialZeroSet) (σ : nonTrivialZeroSet) :
    ∑' ρ : ↥((S : Set nonTrivialZeroSet)ᶜ), (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ)
        * ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      = ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 := by
  refine tsum_subtype_eq_of_support_subset (s := ((S : Set nonTrivialZeroSet)ᶜ))
    (f := fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2) fun ρ hρ hS => hρ ?_
  show _ * _ = _
  rw [inner_bPerp_ueVec hx0 σ (Finset.mem_coe.1 hS)]; ring

/-! ### The edge Gram: coercivity -/

section Gram

open Cvs.StepA.Edge.DampedEdgeGram (gram gramOn comb)

variable {ι : Type*} [Fintype ι]

/-- `κ Σ yₖ² ≤ yᵀGy` for every `y`. -/
def Coercive (G : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ) (κ : ℝ) : Prop :=
  ∀ y : Fin 2 × ι → ℝ, κ * ∑ k, y k ^ 2 ≤ y ⬝ᵥ (G *ᵥ y)

/-- `yᵀGy ≤ Λ Σ yₖ²` for every `y` supported on the block of `i`. -/
def BlockBound (G : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ) (i : ι) (Λ : ℝ) : Prop :=
  ∀ y : Fin 2 × ι → ℝ, (∀ k, k.2 ≠ i → y k = 0) → y ⬝ᵥ (G *ᵥ y) ≤ Λ * ∑ k, y k ^ 2

/-- `|yᵀDy| ≤ ε' (Σ|yₖ|)²` when every entry of `D` is at most `ε'` in size. -/
theorem abs_quad_le {D : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ} {ε' : ℝ} (hD : ∀ k l, |D k l| ≤ ε')
    (y : Fin 2 × ι → ℝ) : |y ⬝ᵥ (D *ᵥ y)| ≤ ε' * (∑ k, |y k|) ^ 2 := by
  simp only [dotProduct, mulVec]
  have hk : ∀ k, |y k * ∑ l, D k l * y l| ≤ |y k| * (ε' * ∑ l, |y l|) := by
    intro k
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |∑ l, D k l * y l| ≤ ∑ l, |D k l * y l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, ε' * |y l| := Finset.sum_le_sum fun l _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hD k l) (abs_nonneg _)
      _ = ε' * ∑ l, |y l| := (Finset.mul_sum _ _ _).symm
  calc |∑ k, y k * ∑ l, D k l * y l| ≤ ∑ k, |y k * ∑ l, D k l * y l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |y k| * (ε' * ∑ l, |y l|) := Finset.sum_le_sum fun k _ => hk k
    _ = ε' * (∑ k, |y k|) ^ 2 := by rw [← Finset.sum_mul]; ring

/-- `(Σ|yₖ|)² ≤ N Σ yₖ²`, `N` the number of coordinates. -/
theorem sq_sum_abs_le (y : Fin 2 × ι → ℝ) :
    (∑ k, |y k|) ^ 2 ≤ (Fintype.card (Fin 2 × ι) : ℝ) * ∑ k, y k ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 2 × ι))) (f := fun k => |y k|)
  simpa [sq_abs] using h

/-- **The finite Gram matrices are eventually coercive**: if `gram δ g` is `κ`-coercive and `δ > 0`, then for every
`ε > 0` the Gram matrix on `[0, b]` is `(κ − ε)`-coercive for all large `b`. -/
theorem eventually_coercive_gramOn {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) {κ : ℝ}
    (hκ : Coercive (gram δ g) κ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b in atTop, Coercive (gramOn δ g b) (κ - ε) := by
  set N : ℝ := (Fintype.card (Fin 2 × ι) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set ε' := ε / (N + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hT := Cvs.StepA.Edge.DampedEdgeGram.tendsto_gramOn hδ g
  have hent : ∀ k l : Fin 2 × ι, ∀ᶠ b in atTop, |gramOn δ g b k l - gram δ g k l| < ε' := by
    intro k l
    have h := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hT k) l
    have := (Metric.tendsto_nhds.1 h) ε' hε'0
    filter_upwards [this] with b hb
    rwa [Real.dist_eq] at hb
  have hall : ∀ᶠ b in atTop, ∀ k l : Fin 2 × ι, |gramOn δ g b k l - gram δ g k l| < ε' :=
    eventually_all.2 fun k => eventually_all.2 fun l => hent k l
  filter_upwards [hall] with b hb
  intro y
  set D := gramOn δ g b - gram δ g
  have hD : ∀ k l, |D k l| ≤ ε' := fun k l => (hb k l).le
  have hsplit : y ⬝ᵥ (gramOn δ g b *ᵥ y) = y ⬝ᵥ (gram δ g *ᵥ y) + y ⬝ᵥ (D *ᵥ y) := by
    rw [show gramOn δ g b = gram δ g + D by simp [D], Matrix.add_mulVec, dotProduct_add]
  have h1 := abs_quad_le hD y
  have h2 := sq_sum_abs_le y
  have hs0 : 0 ≤ ∑ k, y k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h3 : ε' * (∑ k, |y k|) ^ 2 ≤ ε * ∑ k, y k ^ 2 := by
    calc ε' * (∑ k, |y k|) ^ 2 ≤ ε' * (N * ∑ k, y k ^ 2) := mul_le_mul_of_nonneg_left h2 hε'0.le
      _ ≤ ε * ∑ k, y k ^ 2 := by
        rw [hε', ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hs0
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  have := hκ y
  rw [hsplit]
  linarith [neg_abs_le (y ⬝ᵥ (D *ᵥ y))]

/-- **The edge Gram of distinct positive ordinates is coercive**, for `δ > 0`. -/
theorem exists_coercive_gram {δ : ℝ} (hδ : 0 < δ) {g : ι → ℝ} (hg0 : ∀ i, 0 < g i)
    (hg : Function.Injective g) : ∃ κ > 0, Coercive (gram δ g) κ := by
  have hG := Cvs.StepA.Edge.DampedEdgeGram.gram_posDef hδ hg0 hg
  have hq : Continuous fun y : Fin 2 × ι → ℝ => y ⬝ᵥ (gram δ g *ᵥ y) :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  obtain ⟨c, hc, hcoer⟩ := Cvs.Route.EvenSectionContinuation.exists_coercive (⊤ : Submodule ℝ (Fin 2 × ι → ℝ)) hq
    (fun t y => by simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring)
    (fun y _ hy => by simpa [star_trivial] using hG.dotProduct_mulVec_pos hy)
  set N : ℝ := (Fintype.card (Fin 2 × ι) : ℝ)
  refine ⟨c / (N + 1), by positivity, fun y => ?_⟩
  have h1 := hcoer y Submodule.mem_top
  have h2 : ∑ k, y k ^ 2 ≤ (N + 1) * ‖y‖ ^ 2 := by
    have : ∀ k, y k ^ 2 ≤ ‖y‖ ^ 2 := fun k => by
      have := norm_le_pi_norm y k
      rw [Real.norm_eq_abs] at this
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    calc ∑ k, y k ^ 2 ≤ ∑ _k : Fin 2 × ι, ‖y‖ ^ 2 := Finset.sum_le_sum fun k _ => this k
      _ = N * ‖y‖ ^ 2 := by simp [N]
      _ ≤ (N + 1) * ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
  have hN : 0 < N + 1 := by positivity
  calc c / (N + 1) * ∑ k, y k ^ 2 ≤ c / (N + 1) * ((N + 1) * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = c * ‖y‖ ^ 2 := by field_simp
    _ ≤ _ := h1

/-- Every Gram matrix has a block bound, `Λ = (Σ |Gₖₗ| + 1)(N + 1)`. -/
theorem exists_blockBound (G : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ) (i : ι) : ∃ Λ > 0, BlockBound G i Λ := by
  set N : ℝ := (Fintype.card (Fin 2 × ι) : ℝ)
  set c := ∑ k, ∑ l, |G k l| + 1
  have hc : 0 < c := by positivity
  refine ⟨c * (N + 1), by positivity, fun y _ => ?_⟩
  have h1 := abs_quad_le (D := G) (ε' := c) (fun k l => by
    have : |G k l| ≤ ∑ l, |G k l| := Finset.single_le_sum (f := fun l => |G k l|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
    have h' : ∑ l, |G k l| ≤ ∑ k, ∑ l, |G k l| := Finset.single_le_sum (f := fun k => ∑ l, |G k l|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    linarith) y
  have h2 := sq_sum_abs_le y
  have hs0 : 0 ≤ ∑ k, y k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  calc y ⬝ᵥ (G *ᵥ y) ≤ |y ⬝ᵥ (G *ᵥ y)| := le_abs_self _
    _ ≤ c * (N * ∑ k, y k ^ 2) := h1.trans (mul_le_mul_of_nonneg_left h2 hc.le)
    _ ≤ c * (N + 1) * ∑ k, y k ^ 2 := by nlinarith

end Gram

/-! ### Edge integrals -/

section EdgeIntegral

open Cvs.StepA.Edge.DampedEdgeGram (gram gramOn comb)

/-- `∫₀^T e^{2δ(u − T)} du = (1 − e^{−2δT})/(2δ)`. -/
theorem integral_exp_edge {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∫ u in (0 : ℝ)..T, Real.exp (2 * δ * (u - T)) = (1 - Real.exp (-(2 * δ * T))) / (2 * δ) := by
  have hd : ∀ u : ℝ, HasDerivAt (fun u => Real.exp (2 * δ * (u - T)) / (2 * δ))
      (Real.exp (2 * δ * (u - T))) u := by
    intro u
    have h := (((hasDerivAt_id u).sub_const T).const_mul (2 * δ)).exp.div_const (2 * δ)
    have h2 : (2 * δ) ≠ 0 := by positivity
    exact h.congr_deriv (by simp only [id, mul_one]; field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (2 * δ * (u - T))).intervalIntegrable _ _)]
  have e1 : 2 * δ * (T - T) = 0 := by ring
  have e2 : 2 * δ * (0 - T) = -(2 * δ * T) := by ring
  simp only [e1, e2, Real.exp_zero]
  ring

/-- `(1 − η)p² − q²/η ≤ (p + q)²` for `η > 0`. -/
theorem sq_add_ge (p q : ℝ) {η : ℝ} (hη : 0 < η) : (1 - η) * p ^ 2 - q ^ 2 / η ≤ (p + q) ^ 2 := by
  have h : (p + q) ^ 2 - ((1 - η) * p ^ 2 - q ^ 2 / η) = (η * p + q) ^ 2 / η + q ^ 2 := by
    field_simp; ring
  have : 0 ≤ (η * p + q) ^ 2 / η + q ^ 2 := by positivity
  linarith

variable {ι : Type*} [Fintype ι]

/-- **The edge integral**: if `k(T − u) = ½e^{δT}·comb y (u) + q(u)` on `[0, T]` with
`|q(u)| ≤ ½e^{−δ(T−u)}M`, then for `η > 0`, `∫₀^T k(T − u)²` lies between
`(1 − η)·¼e^{2δT}·yᵀG_T y − M²/(8δη)` and `(1 + η)·¼e^{2δT}·yᵀG_T y + (1 + 1/η)M²/(8δ)`. -/
theorem edge_int_bounds {δ T η M : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hη : 0 < η) (hM : 0 ≤ M) (g : ι → ℝ)
    (y : Fin 2 × ι → ℝ) {k : ℝ → ℝ} (hk : Continuous k)
    (hrem : ∀ u ∈ Icc 0 T, |k (T - u) - Real.exp (δ * T) / 2 * comb δ g y u|
      ≤ Real.exp (-(δ * (T - u))) / 2 * M) :
    (1 - η) * (Real.exp (δ * T) ^ 2 / 4 * (y ⬝ᵥ (gramOn δ g T *ᵥ y))) - M ^ 2 / (8 * δ * η)
        ≤ ∫ u in (0 : ℝ)..T, k (T - u) ^ 2
      ∧ ∫ u in (0 : ℝ)..T, k (T - u) ^ 2
        ≤ (1 + η) * (Real.exp (δ * T) ^ 2 / 4 * (y ⬝ᵥ (gramOn δ g T *ᵥ y))) + (1 + 1 / η) * (M ^ 2 / (8 * δ)) := by
  set p : ℝ → ℝ := fun u => Real.exp (δ * T) / 2 * comb δ g y u with hpdef
  set q : ℝ → ℝ := fun u => k (T - u) - p u with hqdef
  have hpc : Continuous p := continuous_const.mul (Cvs.StepA.Edge.DampedEdgeGram.continuous_comb δ g y)
  have hkc : Continuous fun u => k (T - u) := hk.comp (continuous_const.sub continuous_id)
  have hqc : Continuous q := hkc.sub hpc
  have hkpq : ∀ u, k (T - u) = p u + q u := fun u => by simp only [hqdef]; ring
  have hP : ∫ u in (0 : ℝ)..T, p u ^ 2 = Real.exp (δ * T) ^ 2 / 4 * (y ⬝ᵥ (gramOn δ g T *ᵥ y)) := by
    rw [Cvs.StepA.Edge.DampedEdgeGram.quad_gramOn, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hpdef]; ring
  have hQ : ∫ u in (0 : ℝ)..T, q u ^ 2 ≤ M ^ 2 / (8 * δ) := by
    have h1 : ∫ u in (0 : ℝ)..T, q u ^ 2
        ≤ ∫ u in (0 : ℝ)..T, M ^ 2 / 4 * Real.exp (2 * δ * (u - T)) := by
      refine intervalIntegral.integral_mono_on hT ((hqc.pow 2).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun u : ℝ => M ^ 2 / 4 * Real.exp (2 * δ * (u - T))).intervalIntegrable _ _)
        fun u hu => ?_
      have hb := hrem u hu
      have hb0 : 0 ≤ Real.exp (-(δ * (T - u))) / 2 * M := by positivity
      have hsq : q u ^ 2 ≤ (Real.exp (-(δ * (T - u))) / 2 * M) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have he : (Real.exp (-(δ * (T - u))) / 2 * M) ^ 2 = M ^ 2 / 4 * Real.exp (2 * δ * (u - T)) := by
        rw [div_mul_eq_mul_div, div_pow, mul_pow, sq (Real.exp _), ← Real.exp_add]
        rw [show -(δ * (T - u)) + -(δ * (T - u)) = 2 * δ * (u - T) by ring]
        ring
      exact hsq.trans he.le
    rw [intervalIntegral.integral_const_mul, integral_exp_edge hδ] at h1
    have he : 0 ≤ Real.exp (-(2 * δ * T)) := (Real.exp_pos _).le
    have : M ^ 2 / 4 * ((1 - Real.exp (-(2 * δ * T))) / (2 * δ)) ≤ M ^ 2 / (8 * δ) := by
      rw [show M ^ 2 / (8 * δ) = M ^ 2 / 4 * (1 / (2 * δ)) by field_simp; ring]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hpi : IntervalIntegrable (fun u => p u ^ 2) volume 0 T := (hpc.pow 2).intervalIntegrable _ _
  have hqi : IntervalIntegrable (fun u => q u ^ 2) volume 0 T := (hqc.pow 2).intervalIntegrable _ _
  have hki : IntervalIntegrable (fun u => k (T - u) ^ 2) volume 0 T := (hkc.pow 2).intervalIntegrable _ _
  constructor
  · have h := intervalIntegral.integral_mono_on hT ((hpi.const_mul (1 - η)).sub (hqi.div_const η)) hki
      fun u _ => by
        show (1 - η) * p u ^ 2 - q u ^ 2 / η ≤ k (T - u) ^ 2
        rw [hkpq u]; exact sq_add_ge (p u) (q u) hη
    rw [intervalIntegral.integral_sub (hpi.const_mul _) (hqi.div_const _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div, hP] at h
    have : M ^ 2 / (8 * δ * η) ≥ (∫ u in (0 : ℝ)..T, q u ^ 2) / η := by
      rw [show M ^ 2 / (8 * δ * η) = (M ^ 2 / (8 * δ)) / η by field_simp]
      exact div_le_div_of_nonneg_right hQ hη.le
    linarith
  · have h := intervalIntegral.integral_mono_on hT hki ((hpi.const_mul (1 + η)).add (hqi.const_mul (1 + 1 / η)))
      fun u _ => by
        show k (T - u) ^ 2 ≤ (1 + η) * p u ^ 2 + (1 + 1 / η) * q u ^ 2
        rw [hkpq u]
        have := Cvs.Route.Visibility.VisibilityClosingStep.sq_sub_le (p u) (-q u) hη
        rwa [sub_neg_eq_add, neg_sq] at this
    rw [intervalIntegral.integral_add (hpi.const_mul _) (hqi.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hP] at h
    have : (1 + 1 / η) * ∫ u in (0 : ℝ)..T, q u ^ 2 ≤ (1 + 1 / η) * (M ^ 2 / (8 * δ)) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    linarith

end EdgeIntegral

/-! ### The window norm of `V_σ − Σ c_r U_r` at the edge -/

section Window

open Cvs.StepA.Edge.DampedEdgeGram (gram gramOn comb edgeFn_zero edgeFn_one)

/-- The ordinates `|γ_r|` of a finite set of zeros, indexed by the set. -/
def ordF (R : Finset nonTrivialZeroSet) : ↥R → ℝ := fun i => ordG i

/-- The edge coordinates of `V_σ − Σ_r c_r U_r` at `T`: `s·(sin, −cos)(g_σT)` on the block of `σ` minus
`c_r(cos, sin)(g_rT)` on the block of `r`. -/
def edgeCoord (R : Finset nonTrivialZeroSet) (T s : ℝ) (iσ : ↥R) (c : nonTrivialZeroSet → ℝ) :
    Fin 2 × ↥R → ℝ := fun k =>
  (if k.2 = iσ then s * ![Real.sin (ordG k.2 * T), -Real.cos (ordG k.2 * T)] k.1 else 0)
    - c k.2 * ![Real.cos (ordG k.2 * T), Real.sin (ordG k.2 * T)] k.1

/-- **The edge coordinates have squared length `1 + Σ_r c_r²`**, for `s² = 1`. -/
theorem sum_sq_edgeCoord (R : Finset nonTrivialZeroSet) (T : ℝ) {s : ℝ} (hs : s ^ 2 = 1) (iσ : ↥R)
    (c : nonTrivialZeroSet → ℝ) :
    ∑ k, edgeCoord R T s iσ c k ^ 2 = 1 + ∑ r ∈ R, c r ^ 2 := by
  classical
  rw [Fintype.sum_prod_type_right]
  have hi : ∀ i : ↥R, ∑ e : Fin 2, edgeCoord R T s iσ c (e, i) ^ 2
      = (if i = iσ then 1 else 0) + c i ^ 2 := by
    intro i
    simp only [Fin.sum_univ_two, edgeCoord, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h := Real.sin_sq_add_cos_sq (ordG i * T)
    split_ifs
    · linear_combination (s ^ 2 + c i ^ 2) * h + hs
    · linear_combination c i ^ 2 * h
  rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [Finset.sum_coe_sort R (fun r => c r ^ 2)]

/-- **The edge combination of the edge coordinates**:
`comb(u) = s e^{−δu} sin(g_σ(T − u)) − Σ_r c_r e^{−δu} cos(g_r(T − u))`. -/
theorem comb_edgeCoord (δ : ℝ) (R : Finset nonTrivialZeroSet) (T s : ℝ) (iσ : ↥R)
    (c : nonTrivialZeroSet → ℝ) (u : ℝ) :
    comb δ (ordF R) (edgeCoord R T s iσ c) u
      = s * (Real.exp (-(δ * u)) * Real.sin (ordG iσ * (T - u)))
        - ∑ r ∈ R, c r * (Real.exp (-(δ * u)) * Real.cos (ordG r * (T - u))) := by
  classical
  unfold comb
  rw [Fintype.sum_prod_type_right]
  have hi : ∀ i : ↥R, ∑ e : Fin 2, edgeCoord R T s iσ c (e, i)
        * Cvs.StepA.Edge.DampedEdgeGram.edgeFn δ (ordF R (e, i).2) (e, i).1 u
      = (if i = iσ then s * (Real.exp (-(δ * u)) * Real.sin (ordG i * (T - u))) else 0)
        - c i * (Real.exp (-(δ * u)) * Real.cos (ordG i * (T - u))) := by
    intro i
    simp only [Fin.sum_univ_two, edgeCoord, Matrix.cons_val_zero, Matrix.cons_val_one, edgeFn_zero,
      edgeFn_one, ordF]
    have h1 : Real.sin (ordG i * (T - u))
        = Real.sin (ordG i * T) * Real.cos (ordG i * u) - Real.cos (ordG i * T) * Real.sin (ordG i * u) := by
      rw [mul_sub, Real.sin_sub]
    have h2 : Real.cos (ordG i * (T - u))
        = Real.cos (ordG i * T) * Real.cos (ordG i * u) + Real.sin (ordG i * T) * Real.sin (ordG i * u) := by
      rw [mul_sub, Real.cos_sub]
    rw [h1, h2]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [Finset.sum_coe_sort R (fun r => c r * (Real.exp (-(δ * u)) * Real.cos (ordG r * (T - u))))]

/-- The window profile `ve_{z_σ}(t) − Σ_{r ∈ R} c_r ue_{z_r}(t)`. -/
def kprof (σ : nonTrivialZeroSet) (R : Finset nonTrivialZeroSet) (c : nonTrivialZeroSet → ℝ) (t : ℝ) : ℝ :=
  ve (Cvs.ZeroCounting.zPoint σ) t - ∑ r ∈ R, c r * ue (Cvs.ZeroCounting.zPoint r) t

/-- The window profile is continuous. -/
theorem continuous_kprof (σ : nonTrivialZeroSet) (R : Finset nonTrivialZeroSet) (c : nonTrivialZeroSet → ℝ) :
    Continuous (kprof σ R c) := by
  unfold kprof ve ue; fun_prop

/-- The window profile is even. -/
theorem kprof_neg (σ : nonTrivialZeroSet) (R : Finset nonTrivialZeroSet) (c : nonTrivialZeroSet → ℝ) (t : ℝ) :
    kprof σ R c (-t) = kprof σ R c t := by
  simp only [kprof, Cvs.StepA.OneZeroParitySectors.ve_neg, Cvs.StepA.OneZeroParitySectors.ue_neg]

/-- **The edge decomposition**: with `|δ_r| = δ` on `R`, `|δ_σ| = δ`, `g_{iσ} = g_σ` and `ve_{z_σ} = s·sin·sinh`,
`|k(T − u) − ½e^{δT}·comb(u)| ≤ ½e^{−δ(T−u)}(1 + Σ_r |c_r|)`. -/
theorem abs_kprof_sub_comb_le {δ : ℝ} {R : Finset nonTrivialZeroSet}
    (hR : ∀ r ∈ R, |Cvs.GaussKernel.del r| = δ) {σ : nonTrivialZeroSet} (hσ : |Cvs.GaussKernel.del σ| = δ)
    {iσ : ↥R} (hiσ : ordG iσ = ordG σ) {s : ℝ} (hs2 : s ^ 2 = 1)
    (hs : ∀ t, ve (Cvs.ZeroCounting.zPoint σ) t
      = s * (Real.sin (ordG σ * t) * Real.sinh (|Cvs.GaussKernel.del σ| * t)))
    (c : nonTrivialZeroSet → ℝ) (T u : ℝ) :
    |kprof σ R c (T - u) - Real.exp (δ * T) / 2 * comb δ (ordF R) (edgeCoord R T s iσ c) u|
      ≤ Real.exp (-(δ * (T - u))) / 2 * (1 + ∑ r ∈ R, |c r|) := by
  set E := Real.exp (δ * (T - u))
  set e' := Real.exp (-(δ * (T - u)))
  set C := ∑ r ∈ R, c r * Real.cos (ordG r * (T - u))
  have hE : Real.exp (δ * T) * Real.exp (-(δ * u)) = E := by rw [← Real.exp_add]; congr 1; ring
  have h1 : ∑ r ∈ R, c r * ue (Cvs.ZeroCounting.zPoint r) (T - u) = (E + e') / 2 * C := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [ue_zPoint, hR r hr, Real.cosh_eq]; ring
  have h2 : ∑ r ∈ R, c r * (Real.exp (-(δ * u)) * Real.cos (ordG r * (T - u)))
      = Real.exp (-(δ * u)) * C := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
  have key : kprof σ R c (T - u) - Real.exp (δ * T) / 2 * comb δ (ordF R) (edgeCoord R T s iσ c) u
      = -(e' / 2) * (s * Real.sin (ordG σ * (T - u)) + C) := by
    rw [kprof, h1, comb_edgeCoord, h2, hs, hσ, hiσ, Real.sinh_eq]
    linear_combination (-(s * Real.sin (ordG σ * (T - u))) / 2 + C / 2) * hE
  rw [key, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ e' / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hs1 : |s| = 1 := by
    have : |s| ^ 2 = 1 := by rw [sq_abs]; exact hs2
    nlinarith [abs_nonneg s]
  have hsin : |s * Real.sin (ordG σ * (T - u))| ≤ 1 := by
    rw [abs_mul, hs1, one_mul]; exact Real.abs_sin_le_one _
  have hC : |C| ≤ ∑ r ∈ R, |c r| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
  exact (abs_add_le _ _).trans (add_le_add hsin hC)

/-- `(1 + Σ_r |c_r|)² ≤ (1 + #R)(1 + Σ_r c_r²)`. -/
theorem one_add_sum_abs_sq_le (R : Finset nonTrivialZeroSet) (c : nonTrivialZeroSet → ℝ) :
    (1 + ∑ r ∈ R, |c r|) ^ 2 ≤ (1 + R.card) * (1 + ∑ r ∈ R, c r ^ 2) := by
  classical
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Option ↥R)))
    (f := fun o => o.elim 1 fun i => |c i|)
  simp only [Finset.card_univ, Fintype.card_option, Fintype.sum_option, Option.elim] at h
  rw [Finset.sum_coe_sort R (fun r => |c r|)] at h
  have e : ∑ i : ↥R, |c i| ^ 2 = ∑ r ∈ R, c r ^ 2 := by
    rw [Finset.sum_coe_sort R (fun r => |c r| ^ 2)]; exact Finset.sum_congr rfl fun r _ => sq_abs _
  rw [e, Fintype.card_coe] at h
  push_cast at h
  linarith

/-- The class of `V_σ − Σ_{r ∈ R} c_r U_r` is a.e. the shifted window profile on `[0, log x)`. -/
theorem toLp_comb_ae {x : ℕ} (hx0 : (0 : ℝ) < x) (σ : nonTrivialZeroSet) (R : Finset nonTrivialZeroSet)
    (c : nonTrivialZeroSet → ℝ) :
    toLp (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
        - ∑ r ∈ R, c r • ueVec hx0 (Cvs.ZeroCounting.zPoint r))
      =ᵐ[volume] (Ico 0 (Real.log x)).indicator (fun s => kprof σ R c (s - Real.log x / 2)) := by
  have e : toLp (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
        - ∑ r ∈ R, c r • ueVec hx0 (Cvs.ZeroCounting.zPoint r))
      = toLp (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ))
        - ∑ r ∈ R, c r • toLp (ueVec hx0 (Cvs.ZeroCounting.zPoint r)) := by
    simp only [toLp, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
  rw [e]
  filter_upwards [Lp.coeFn_sub (toLp (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)))
      (∑ r ∈ R, c r • toLp (ueVec hx0 (Cvs.ZeroCounting.zPoint r))),
    Lp.coeFn_finsetSum R (fun r => c r • toLp (ueVec hx0 (Cvs.ZeroCounting.zPoint r))),
    (eventually_all_finset R).2 (fun r _ => Lp.coeFn_smul (c r) (toLp (ueVec hx0 (Cvs.ZeroCounting.zPoint r)))),
    (eventually_all_finset R).2 (fun r _ => Cvs.Route.Visibility.VisibilityClosingStep.coe_ueVec_ae hx0 (Cvs.ZeroCounting.zPoint r)),
    Cvs.Route.Visibility.ZeroPairingVector.coe_pairVec_ae hx0 (Cvs.ZeroCounting.zPoint σ)] with s h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, Finset.sum_apply, h5]
  rw [Finset.sum_congr rfl fun r hr => by rw [h3 r hr, Pi.smul_apply, h4 r hr]]
  by_cases hs : s ∈ Ico 0 (Real.log x)
  · simp only [indicator_of_mem hs, kprof, Cvs.Route.Visibility.ZeroPairingVector.pairProf, ueProf, smul_eq_mul]
  · simp [indicator_of_notMem hs]

/-- `∫_{−T}^{T} k² = 2∫₀^T k(T − u)² du` for a continuous even `k`. -/
theorem integral_sq_even {k : ℝ → ℝ} (hk : Continuous k) (heven : ∀ t, k (-t) = k t) (T : ℝ) :
    ∫ t in -T..T, k t ^ 2 = 2 * ∫ u in (0 : ℝ)..T, k (T - u) ^ 2 := by
  have h := Cvs.StepA.Edge.TwoEdgeSplit.integral_sq_even (2 * T) hk heven
  rw [show 2 * T / 2 = T by ring] at h
  rw [h]
  congr 1
  exact intervalIntegral.integral_congr fun u _ => by rw [← heven, neg_sub]

/-- **The window norm of `V_σ − Σ_r c_r U_r`**: `‖·‖² = 2∫₀^T k(T − u)² du`, `T = log x / 2`. -/
theorem norm_sq_comb_eq {x : ℕ} (hx0 : (0 : ℝ) < x) (σ : nonTrivialZeroSet) (R : Finset nonTrivialZeroSet)
    (c : nonTrivialZeroSet → ℝ) :
    ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ) - ∑ r ∈ R, c r • ueVec hx0 (Cvs.ZeroCounting.zPoint r)‖ ^ 2
      = 2 * ∫ u in (0 : ℝ)..Real.log x / 2, kprof σ R c (Real.log x / 2 - u) ^ 2 := by
  have h : ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ) - ∑ r ∈ R, c r • ueVec hx0 (Cvs.ZeroCounting.zPoint r)‖
      = ‖toLp (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
          - ∑ r ∈ R, c r • ueVec hx0 (Cvs.ZeroCounting.zPoint r))‖ := rfl
  rw [h, Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral,
    integral_congr_ae (g := (Ico 0 (Real.log x)).indicator (fun s => kprof σ R c (s - Real.log x / 2) ^ 2)),
    Cvs.Route.Visibility.ZeroPairingVector.integral_indicator_Ico_eq (Real.log_natCast_nonneg x),
    ← integral_sq_even (continuous_kprof σ R c) (kprof_neg σ R c)]
  · refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [add_sub_cancel_right]
  · filter_upwards [toLp_comb_ae hx0 σ R c] with s h2
    rw [h2]
    by_cases hs : s ∈ Ico 0 (Real.log x) <;> simp [hs]

/-- **The window norm of `V_σ − Σ_r c_r U_r` between edge-Gram bounds**: with `T = log x / 2`,
`y` the edge coordinates, `G_T` the edge Gram on `[0, T]` and `M₂ = (1 + #R)(1 + Σ c_r²)`, for `η > 0`,
`2(1 − η)·¼e^{2δT}yᵀG_T y − M₂/(4δη) ≤ ‖·‖² ≤ 2(1 + η)·¼e^{2δT}yᵀG_T y + (1 + 1/η)M₂/(4δ)`. -/
theorem norm_sq_comb_bounds {x : ℕ} (hx0 : (0 : ℝ) < x) {δ : ℝ} (hδ : 0 < δ) {R : Finset nonTrivialZeroSet}
    (hR : ∀ r ∈ R, |Cvs.GaussKernel.del r| = δ) {σ : nonTrivialZeroSet} (hσ : |Cvs.GaussKernel.del σ| = δ)
    {iσ : ↥R} (hiσ : ordG iσ = ordG σ) {s : ℝ} (hs2 : s ^ 2 = 1)
    (hs : ∀ t, ve (Cvs.ZeroCounting.zPoint σ) t
      = s * (Real.sin (ordG σ * t) * Real.sinh (|Cvs.GaussKernel.del σ| * t)))
    (c : nonTrivialZeroSet → ℝ) {η : ℝ} (hη : 0 < η) :
    2 * ((1 - η) * (Real.exp (δ * (Real.log x / 2)) ^ 2 / 4
        * (edgeCoord R (Real.log x / 2) s iσ c ⬝ᵥ
          (gramOn δ (ordF R) (Real.log x / 2) *ᵥ edgeCoord R (Real.log x / 2) s iσ c))))
        - (1 + R.card) * (1 + ∑ r ∈ R, c r ^ 2) / (4 * δ * η)
      ≤ ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
          - ∑ r ∈ R, c r • ueVec hx0 (Cvs.ZeroCounting.zPoint r)‖ ^ 2
    ∧ ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
          - ∑ r ∈ R, c r • ueVec hx0 (Cvs.ZeroCounting.zPoint r)‖ ^ 2
      ≤ 2 * ((1 + η) * (Real.exp (δ * (Real.log x / 2)) ^ 2 / 4
        * (edgeCoord R (Real.log x / 2) s iσ c ⬝ᵥ
          (gramOn δ (ordF R) (Real.log x / 2) *ᵥ edgeCoord R (Real.log x / 2) s iσ c))))
        + (1 + 1 / η) * ((1 + R.card) * (1 + ∑ r ∈ R, c r ^ 2) / (4 * δ)) := by
  set T := Real.log x / 2
  have hT : 0 ≤ T := by have := Real.log_natCast_nonneg x; positivity
  have hM : 0 ≤ 1 + ∑ r ∈ R, |c r| := by positivity
  obtain ⟨h1, h2⟩ := edge_int_bounds hδ hT hη hM (ordF R) (edgeCoord R T s iσ c) (continuous_kprof σ R c)
    (fun u _ => abs_kprof_sub_comb_le hR hσ hiσ hs2 hs c T u)
  have hMM := one_add_sum_abs_sq_le R c
  rw [norm_sq_comb_eq hx0 σ R c]
  have e1 : (1 + ∑ r ∈ R, |c r|) ^ 2 / (8 * δ * η) ≤ (1 + R.card) * (1 + ∑ r ∈ R, c r ^ 2) / (8 * δ * η) :=
    div_le_div_of_nonneg_right hMM (by positivity)
  have e2 : (1 + ∑ r ∈ R, |c r|) ^ 2 / (8 * δ) ≤ (1 + R.card) * (1 + ∑ r ∈ R, c r ^ 2) / (8 * δ) :=
    div_le_div_of_nonneg_right hMM (by positivity)
  have hη' : 0 ≤ 1 + 1 / η := by positivity
  constructor
  · have : (1 + R.card) * (1 + ∑ r ∈ R, c r ^ 2) / (4 * δ * η)
        = 2 * ((1 + R.card) * (1 + ∑ r ∈ R, c r ^ 2) / (8 * δ * η)) := by field_simp; ring
    rw [this]; linarith
  · have : (1 + R.card) * (1 + ∑ r ∈ R, c r ^ 2) / (4 * δ)
        = 2 * ((1 + R.card) * (1 + ∑ r ∈ R, c r ^ 2) / (8 * δ)) := by field_simp; ring
    rw [this]
    have := mul_le_mul_of_nonneg_left e2 hη'
    nlinarith

end Window

/-! ### Eventual bounds on `b⊥` for a finite top set -/

section Eventual

open Cvs.StepA.Edge.DampedEdgeGram (gram gramOn comb)

variable {S : Finset nonTrivialZeroSet} {δ : ℝ}

/-- On a finite top set every representative is at depth `δ`. -/
theorem reps_del (hT : FiniteTop S δ) : ∀ r ∈ reps S, |Cvs.GaussKernel.del r| = δ :=
  fun r hr => hT.2.2.1 r (reps_subset S hr)

/-- The ordinates of a finite set of zeros are positive. -/
theorem ordF_pos (R : Finset nonTrivialZeroSet) (i : ↥R) : 0 < ordF R i :=
  abs_pos.2 (Cvs.StepA.LowEigenvalueCountZeros.im_ne_zero i)

/-- The ordinates of the representatives are distinct. -/
theorem ordF_injective (S : Finset nonTrivialZeroSet) : Function.Injective (ordF (reps S)) :=
  fun i j h => Subtype.ext (reps_injOn S i.2 j.2 h)

/-- `x^δ = e^{δ log x} → ∞`. -/
theorem tendsto_exp_delta_log (hδ : 0 < δ) :
    Tendsto (fun x : ℕ => Real.exp (δ * Real.log x)) atTop atTop :=
  Real.tendsto_exp_atTop.comp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hδ)

/-- **The two edge bounds, eventually**: for a `κ`-coercive edge Gram, a block bound `Λ` at `σ`, `0 < η ≤ 1`, `ε > 0`,
at all large `x`, `(1 + Σ c_r²)((1 − η)(κ − ε)x^δ/2 − (1 + #R)/(4δη)) ≤ ‖V_σ − Σ_r c_r U_r‖²` for every `c`, and
`‖V_σ‖² ≤ (1 + η)Λx^δ/2 + (1 + 1/η)(1 + #R)/(4δ)`. -/
theorem eventually_comb_bounds (hT : FiniteTop S δ) {σ : nonTrivialZeroSet} (hσS : σ ∈ S)
    {iσ : ↥(reps S)} (hiσ : ordG iσ = ordG σ) {κ Λ : ℝ} (hκ : Coercive (gram δ (ordF (reps S))) κ)
    (hΛ : BlockBound (gram δ (ordF (reps S))) iσ Λ) {η ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      (∀ c : nonTrivialZeroSet → ℝ, (1 + ∑ r ∈ reps S, c r ^ 2)
          * ((1 - η) * (κ - ε) / 2 * Real.exp (δ * Real.log x) - (1 + (reps S).card) / (4 * δ * η))
        ≤ ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
            - ∑ r ∈ reps S, c r • ueVec hx0 (Cvs.ZeroCounting.zPoint r)‖ ^ 2)
      ∧ ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)‖ ^ 2
        ≤ (1 + η) * Λ / 2 * Real.exp (δ * Real.log x) + (1 + 1 / η) * ((1 + (reps S).card) / (4 * δ)) := by
  obtain ⟨s, hs2, hs⟩ := ve_zPoint σ
  have hσδ := hT.2.2.1 σ hσS
  have hR := reps_del hT
  have hlog : Tendsto (fun x : ℕ => Real.log x / 2) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const two_pos
  filter_upwards [hlog.eventually (eventually_coercive_gramOn hT.1 (ordF (reps S)) hκ hε)] with x hx hx0
  have hexp : Real.exp (δ * (Real.log x / 2)) ^ 2 = Real.exp (δ * Real.log x) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hT0 : 0 ≤ Real.log x / 2 := by have := Real.log_natCast_nonneg x; positivity
  have he : 0 ≤ Real.exp (δ * Real.log x) := (Real.exp_pos _).le
  set n : ℝ := ((reps S).card : ℝ)
  constructor
  · intro c
    obtain ⟨h1, -⟩ := norm_sq_comb_bounds hx0 hT.1 hR hσδ hiσ hs2 hs c hη
    have hq := hx (edgeCoord (reps S) (Real.log x / 2) s iσ c)
    rw [sum_sq_edgeCoord _ _ hs2] at hq
    rw [hexp] at h1
    have hm : (1 - η) * (Real.exp (δ * Real.log x) / 4 * ((κ - ε) * (1 + ∑ r ∈ reps S, c r ^ 2)))
        ≤ (1 - η) * (Real.exp (δ * Real.log x) / 4
          * (edgeCoord (reps S) (Real.log x / 2) s iσ c ⬝ᵥ
            (gramOn δ (ordF (reps S)) (Real.log x / 2) *ᵥ edgeCoord (reps S) (Real.log x / 2) s iσ c))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by positivity)) (by linarith)
    have e : (1 + ∑ r ∈ reps S, c r ^ 2)
          * ((1 - η) * (κ - ε) / 2 * Real.exp (δ * Real.log x) - (1 + n) / (4 * δ * η))
        = 2 * ((1 - η) * (Real.exp (δ * Real.log x) / 4 * ((κ - ε) * (1 + ∑ r ∈ reps S, c r ^ 2))))
          - (1 + n) * (1 + ∑ r ∈ reps S, c r ^ 2) / (4 * δ * η) := by
      field_simp; ring
    rw [e]
    linarith
  · obtain ⟨-, h2⟩ := norm_sq_comb_bounds hx0 hT.1 hR hσδ hiσ hs2 hs (fun _ => 0) hη
    have e0 : Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
        - ∑ r ∈ reps S, (fun _ => (0 : ℝ)) r • ueVec hx0 (Cvs.ZeroCounting.zPoint r)
        = Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ) := by
      rw [Finset.sum_eq_zero fun r _ => zero_smul ℝ (ueVec hx0 (Cvs.ZeroCounting.zPoint r)), sub_zero]
    have e1 : ∑ r ∈ reps S, (fun _ => (0 : ℝ)) r ^ 2 = 0 := Finset.sum_eq_zero fun r _ => by norm_num
    rw [e0, e1, hexp, add_zero, mul_one] at h2
    set y := edgeCoord (reps S) (Real.log x / 2) s iσ (fun _ => 0)
    have hsupp : ∀ k : Fin 2 × ↥(reps S), k.2 ≠ iσ → y k = 0 := fun k hk => by
      simp [y, edgeCoord, hk]
    have hy1 : ∑ k, y k ^ 2 = 1 := by
      rw [sum_sq_edgeCoord _ _ hs2]; simp
    have hyG : y ⬝ᵥ (gramOn δ (ordF (reps S)) (Real.log x / 2) *ᵥ y) ≤ Λ := by
      have := (Cvs.StepA.Edge.DampedEdgeGram.quad_gramOn_le hT.1 (ordF (reps S)) y hT0).trans (hΛ y hsupp)
      rwa [hy1, mul_one] at this
    have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyG (by positivity : 0 ≤ Real.exp (δ * Real.log x) / 4))
      (by linarith : 0 ≤ 1 + η)
    have e : (1 + η) * Λ / 2 * Real.exp (δ * Real.log x) = 2 * ((1 + η) * (Real.exp (δ * Real.log x) / 4 * Λ)) := by
      ring
    rw [e]
    linarith

/-- **`b⊥` is of size `x^δ` with bounded coefficients**: for a finite top set and `σ ∈ S` there are `β > 0` and
`K ≥ 0` with, at all large `x`, `β x^δ ≤ ‖b⊥‖²` and `V_σ = b⊥ + Σ_{r ∈ R} a_r U_r` with `Σ a_r² ≤ K`. -/
theorem eventually_bPerp_bounds (hT : FiniteTop S δ) {σ : nonTrivialZeroSet} (hσS : σ ∈ S) :
    ∃ β > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      β * Real.exp (δ * Real.log x) ≤ ‖bPerp hx0 S σ‖ ^ 2 ∧
      ∃ a : nonTrivialZeroSet → ℝ, Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
          = bPerp hx0 S σ + ∑ r ∈ reps S, a r • ueVec hx0 (Cvs.ZeroCounting.zPoint r)
        ∧ ∑ r ∈ reps S, a r ^ 2 ≤ K := by
  obtain ⟨r, hr, hro⟩ := exists_rep_of_mem hσS
  set iσ : ↥(reps S) := ⟨r, hr⟩
  have hδ := hT.1
  obtain ⟨κ, hκ0, hκ⟩ := exists_coercive_gram hδ (ordF_pos (reps S)) (ordF_injective S)
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_blockBound (gram δ (ordF (reps S))) iσ
  set n : ℝ := ((reps S).card : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨κ / 16, by positivity, 16 * Λ / κ, by positivity, ?_⟩
  filter_upwards [eventually_comb_bounds hT hσS (iσ := iσ) hro hκ hΛ (η := 1 / 2) (ε := κ / 2)
      (by norm_num) (by norm_num) (by positivity),
    (tendsto_exp_delta_log hδ).eventually_ge_atTop (8 * (1 + n) / (δ * κ) + 3 * (1 + n) / (δ * Λ))]
    with x h hE hx0
  obtain ⟨hlow, hup⟩ := h hx0
  obtain ⟨a, ha⟩ := exists_coeff hx0 hT.2.2.1 σ
  have hb : bPerp hx0 S σ = Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
      - ∑ r ∈ reps S, a r • ueVec hx0 (Cvs.ZeroCounting.zPoint r) := eq_sub_of_add_eq ha.symm
  have hL := hlow a
  rw [← hb] at hL
  have hbV := norm_bPerp_sq_le hx0 S σ
  set e := Real.exp (δ * Real.log x)
  have hp1 : 0 ≤ 8 * (1 + n) / (δ * κ) := div_nonneg (by linarith) (mul_pos hδ hκ0).le
  have hp2 : 0 ≤ 3 * (1 + n) / (δ * Λ) := div_nonneg (by linarith) (mul_pos hδ hΛ0).le
  have he1 : 8 * (1 + n) / (δ * κ) ≤ e := le_trans (le_add_of_nonneg_right hp2) hE
  have he2 : 3 * (1 + n) / (δ * Λ) ≤ e := le_trans (le_add_of_nonneg_left hp1) hE
  rw [div_le_iff₀ (mul_pos hδ hκ0)] at he1
  rw [div_le_iff₀ (mul_pos hδ hΛ0)] at he2
  have hbr : (1 - 1 / 2) * (κ - κ / 2) / 2 * e - (1 + n) / (4 * δ * (1 / 2)) = κ * e / 8 - (1 + n) / (2 * δ) := by
    field_simp; ring
  have hc1 : (1 + n) / (2 * δ) ≤ κ * e / 16 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hc2 : (1 + 1 / (1 / 2 : ℝ)) * ((1 + n) / (4 * δ)) ≤ Λ * e / 4 := by
    rw [show (1 + 1 / (1 / 2 : ℝ)) * ((1 + n) / (4 * δ)) = 3 * (1 + n) / (4 * δ) by field_simp; ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  rw [hbr] at hL
  have hsa : 0 ≤ ∑ r ∈ reps S, a r ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbrk : κ * e / 16 ≤ κ * e / 8 - (1 + n) / (2 * δ) := by linarith
  have hκe : 0 ≤ κ * e / 16 := by positivity
  have hL' : (1 + ∑ r ∈ reps S, a r ^ 2) * (κ * e / 16) ≤ ‖bPerp hx0 S σ‖ ^ 2 :=
    (mul_le_mul_of_nonneg_left hbrk (by positivity)).trans hL
  refine ⟨by nlinarith, a, ha, ?_⟩
  have hup' : ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)‖ ^ 2 ≤ Λ * e := by
    have : (1 + 1 / 2) * Λ / 2 * e = 3 * (Λ * e / 4) := by ring
    linarith
  have hke : 0 < κ * e := by
    have : 0 < e := Real.exp_pos _
    positivity
  have h3 : (1 + ∑ r ∈ reps S, a r ^ 2) * (κ * e) ≤ 16 * Λ * e := by nlinarith
  rw [le_div_iff₀ hκ0]
  have h4 : (∑ r ∈ reps S, a r ^ 2) * (κ * e) ≤ 16 * Λ * e := by nlinarith
  have : (∑ r ∈ reps S, a r ^ 2) * κ * e ≤ 16 * Λ * e := by linarith
  exact le_of_mul_le_mul_right (by linarith) (Real.exp_pos (δ * Real.log x))

end Eventual

/-! ### The θ bound -/

section Theta

open Cvs.StepA.Edge.DampedEdgeGram (gram)

variable {S : Finset nonTrivialZeroSet} {δ : ℝ}

end Theta

/-! ### The closing theorem for `b⊥` -/

section Closing

variable {S : Finset nonTrivialZeroSet} {δ : ℝ}

/-- **The closing step for `b⊥` at one `x`**: at `80 ≤ 2πx`, `V_σ = b⊥ + Σ_R a_r U_r`, `‖P_{R₁}b⊥‖² ≤ (1 − s₀)‖b⊥‖²`,
`Σ_ρ m_ρ⟪P_{R₁}b⊥, U_ρ⟫² ≤ C_P`, `Σ_{ρ ∉ S} m_ρ⟪b⊥, U_ρ⟫² ≤ E_b`, `Σ_R a_r²/m_r ≤ A²`, `A·X ≤ s₀‖b⊥‖²` and
`X² < W_σ(s₀‖b⊥‖² − A·X)²`, `X = √E_b + √C_P`, give `¬ EvenBulkFloor x 0`. -/
theorem not_evenBulkFloor_of_perp {x : ℕ} (hx : 80 ≤ 2 * π * x) (S : Finset nonTrivialZeroSet)
    (σ : nonTrivialZeroSet) (a : nonTrivialZeroSet → ℝ) {s₀ Cp Eb A : ℝ}
    (hV : Cvs.Route.Visibility.ZeroPairingVector.pairVec (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.ZeroCounting.zPoint σ)
      = bPerp (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) S σ
        + ∑ r ∈ reps S, a r • ueVec (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.ZeroCounting.zPoint r))
    (hshare : ‖(R1 x).starProjection (bPerp (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) S σ)‖ ^ 2
      ≤ (1 - s₀) * ‖bPerp (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) S σ‖ ^ 2)
    (hpS : Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪(R1 x).starProjection (bPerp (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) S σ),
          ueVec (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
    (hpB : ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪(R1 x).starProjection (bPerp (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) S σ),
          ueVec (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 ≤ Cp)
    (hbS : Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪bPerp (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) S σ, ueVec (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
    (hbE : ∑' ρ : ↥((S : Set nonTrivialZeroSet)ᶜ), (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ)
      * ⟪bPerp (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) S σ,
          ueVec (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 ≤ Eb)
    (hA : ∑ r ∈ reps S, a r ^ 2 / (Cvs.Criterion.divisorWeight r : ℝ) ≤ A ^ 2) (hA0 : 0 ≤ A)
    (hX : A * (√Eb + √Cp) ≤ s₀ * ‖bPerp (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) S σ‖ ^ 2)
    (hclose : (√Eb + √Cp) ^ 2
      < quadWeight σ * (s₀ * ‖bPerp (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) S σ‖ ^ 2 - A * (√Eb + √Cp)) ^ 2) :
    ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  set hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  set b := bPerp hx0 S σ with hbdef
  have hPR : (R1 x).starProjection b ∈ R1 x := (R1 x).starProjection_apply_mem b
  have hwE : b - (R1 x).starProjection b ∈ Ev x := (Ev x).sub_mem (bPerp_mem_Ev hx0 S σ) (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hPR)
  have hwR : b - (R1 x).starProjection b ∈ (R1 x)ᗮ := (R1 x).sub_starProjection_mem_orthogonal b
  obtain ⟨v', hv', hPv, -⟩ := Cvs.WeilForm.EvenExplicitFormulaTameTests.exists_tame_of_mem_R1 hx hPR
  have hC : ContDiff ℝ 1 (fun s => kprof σ (reps S) a (s - Real.log x / 2)) := by
    unfold kprof ve ue; fun_prop
  have hbt := Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 hC
  have hbwv : b = Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hbt := by
    have hb' : b = Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
        - ∑ r ∈ reps S, a r • ueVec hx0 (Cvs.ZeroCounting.zPoint r) := eq_sub_of_add_eq hV.symm
    apply dom_ext_ae
    rw [hb']
    filter_upwards [toLp_comb_ae hx0 σ (reps S) a, Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 hbt] with s h1 h2
    rw [h1, h2, Cvs.Route.Visibility.ZeroPairingVector.fv_ofWin hx0]
  have hwv : b - (R1 x).starProjection b = Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.InsideFunctionTame.tame_sub hbt hv') := by
    rw [Cvs.WeilForm.ZeroSidePolarized.wv_sub hx0 hbt hv', ← hbwv, ← hPv]
  have hm0 : ∀ ρ : nonTrivialZeroSet, 0 ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) := fun ρ => Nat.cast_nonneg _
  have hm1 : ∀ ρ : nonTrivialZeroSet, 1 ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) := fun ρ => by
    exact_mod_cast Cvs.Criterion.one_le_divisorWeight ρ
  obtain ⟨hs1, -⟩ := Cvs.Route.Visibility.VisibilityClosingStep.tsum_mul_sub_sq_le (m := fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ))
    (a := fun ρ => ⟪b, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ)
    (c := fun ρ => ⟪(R1 x).starProjection b, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ) hm0 hbS hpS
  have hwS : Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪b - (R1 x).starProjection b, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 := by
    refine hs1.congr fun ρ => ?_
    rw [Cvs.Route.Visibility.VisibilityClosingStep.inner_sub_starProjection (R1 x) b]
  have hQ := Cvs.Route.Visibility.VisibilityClosingStep.Qx_le_tsum_ue_sub (Cvs.StepA.LowEigenvalueCountSpine.two_le hx) hx0 (Cvs.WeilForm.InsideFunctionTame.tame_sub hbt hv') hwE hwv σ hwS
  have hW : 0 ≤ quadWeight σ := (lt_of_lt_of_le one_pos (Cvs.StepA.TopQuadruple.one_le_quadWeight σ)).le
  have hneg := neg_of_perp_closing_raw (R1 x) hm0 (fun ρ => ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)) (reps S)
    (fun ρ _ => lt_of_lt_of_le one_pos (hm1 ρ)) a hV (Q := Qx x) hW hQ hshare hpS hpB hbS
    (by rw [← tsum_bPerp_eq_off]; exact hbE) hA hA0 hX hclose
  exact (Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor.not_evenBulkFloor_zero_iff x).2 ⟨_, hwE, hwR, hneg⟩

/-- The closing arithmetic: with `8r(1 + A) = s₀β`, `βe ≤ B` and `E_b, C_P ≤ r²e²`, `X = √E_b + √C_P` has
`A·X ≤ s₀B` and `X² < W(s₀B − A·X)²` for `W ≥ 1`. -/
theorem closing_arith {s₀ β e r A B Cp Eb W : ℝ} (hs₀ : 0 < s₀) (hβ : 0 < β) (he : 0 < e) (hA0 : 0 ≤ A)
    (hr : 0 < r) (hrA : 8 * (r * (1 + A)) = s₀ * β) (hBe : β * e ≤ B) (hEb : Eb ≤ r ^ 2 * e ^ 2)
    (hCp : Cp ≤ r ^ 2 * e ^ 2) (hW : 1 ≤ W) :
    A * (√Eb + √Cp) ≤ s₀ * B ∧ (√Eb + √Cp) ^ 2 < W * (s₀ * B - A * (√Eb + √Cp)) ^ 2 := by
  have hsq : ∀ {Y : ℝ}, Y ≤ r ^ 2 * e ^ 2 → √Y ≤ r * e := fun {Y} hY => by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  set X := √Eb + √Cp with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXle : X ≤ 2 * (r * e) := by linarith [hsq hEb, hsq hCp]
  have hAr : 8 * (A * r) ≤ s₀ * β := by nlinarith
  have hre0 : 0 ≤ r * e := by positivity
  have hAX : A * X ≤ s₀ * β * e / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hXle hA0
    have h2 : A * (2 * (r * e)) = 2 * (A * r) * e := by ring
    have h3 : 2 * (A * r) * e ≤ s₀ * β / 4 * e := mul_le_mul_of_nonneg_right (by linarith) he.le
    linarith
  have hsB : s₀ * (β * e) ≤ s₀ * B := mul_le_mul_of_nonneg_left hBe hs₀.le
  have hsbe : 0 < s₀ * β * e := by positivity
  refine ⟨by nlinarith, ?_⟩
  have hpos : 3 / 4 * (s₀ * β * e) ≤ s₀ * B - A * X := by nlinarith
  have hX2 : X ^ 2 ≤ (2 * (r * e)) ^ 2 := pow_le_pow_left₀ hX0 hXle 2
  have hr8 : 8 * r ≤ s₀ * β := by nlinarith
  have hre : 8 * (r * e) ≤ s₀ * β * e := by nlinarith
  have h1 : (3 / 4 * (s₀ * β * e)) ^ 2 ≤ (s₀ * B - A * X) ^ 2 := pow_le_pow_left₀ (by positivity) hpos 2
  have h2 : (s₀ * B - A * X) ^ 2 ≤ W * (s₀ * B - A * X) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hW
  have h3 : (2 * (r * e)) ^ 2 ≤ (s₀ * β * e) ^ 2 / 16 := by nlinarith
  nlinarith

/-- The honest eventual rates for `b⊥` of `σ` over `S`: a share `s₀ > 0` of `b⊥` off `R₁`, summable `U` sums at
`P_{R₁}b⊥` and at `b⊥`, and the Bessel sum `Σ_ρ m_ρ⟪P_{R₁}b⊥, U_ρ⟫²` and the rest `Σ_{ρ ∉ S} m_ρ⟪b⊥, U_ρ⟫²` both
`o(x^{2δ})`. -/
def PerpRates (S : Finset nonTrivialZeroSet) (δ : ℝ) (σ : nonTrivialZeroSet) : Prop :=
  (∃ s₀ > 0, ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      ‖(R1 x).starProjection (bPerp hx0 S σ)‖ ^ 2 ≤ (1 - s₀) * ‖bPerp hx0 S σ‖ ^ 2)
  ∧ (∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      (Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪(R1 x).starProjection (bPerp hx0 S σ), ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
      ∧ Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
  ∧ ∀ ε > 0, ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
          * ⟪(R1 x).starProjection (bPerp hx0 S σ), ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ ε * (x : ℝ) ^ (2 * δ)
      ∧ ∑' ρ : ↥((S : Set nonTrivialZeroSet)ᶜ), (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ)
          * ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ ε * (x : ℝ) ^ (2 * δ)

/-- **Ties close eventually (Theorem T)**: for a finite top set `S` at depth `δ`, `σ ∈ S` and the rates
`PerpRates S δ σ`, the zero even bulk floor fails at all large `x`. -/
theorem eventually_not_evenBulkFloor_of_perpRates (hT : FiniteTop S δ) {σ : nonTrivialZeroSet} (hσS : σ ∈ S)
    (h : PerpRates S δ σ) : ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  obtain ⟨β, hβ, K, hK0, hev⟩ := eventually_bPerp_bounds hT hσS
  obtain ⟨⟨s₀, hs₀, hsh⟩, hsum, hrate⟩ := h
  set A := √K with hAdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  set r := s₀ * β / (8 * (1 + A)) with hrdef
  have hr : 0 < r := by positivity
  have hrA : 8 * (r * (1 + A)) = s₀ * β := by rw [hrdef]; field_simp
  filter_upwards [hev, hsh, hsum, hrate (r ^ 2) (by positivity), eventually_ge_atTop 14]
    with x h1 h2 h3 h4 h14
  have hx := Cvs.Route.Visibility.VisibilityClosingStep.scale_of_ge h14
  obtain ⟨hlow, a, hV, hKa⟩ := h1 (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
  obtain ⟨hp, hb⟩ := h3 (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
  obtain ⟨hCp, hEb⟩ := h4 (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
  have he : 0 < Real.exp (δ * Real.log x) := Real.exp_pos _
  have hxe : (x : ℝ) ^ (2 * δ) = Real.exp (δ * Real.log x) ^ 2 := by
    rw [Real.rpow_def_of_pos (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx), sq, ← Real.exp_add]; congr 1; ring
  rw [hxe] at hCp hEb
  have hA : ∑ r ∈ reps S, a r ^ 2 / (Cvs.Criterion.divisorWeight r : ℝ) ≤ A ^ 2 := by
    rw [hAdef, Real.sq_sqrt hK0]
    refine le_trans (Finset.sum_le_sum fun ρ _ => div_le_self (sq_nonneg _) ?_) hKa
    exact_mod_cast Cvs.Criterion.one_le_divisorWeight ρ
  obtain ⟨hX, hclose⟩ := closing_arith hs₀ hβ he hA0 hr hrA hlow hEb hCp (Cvs.StepA.TopQuadruple.one_le_quadWeight σ)
  exact not_evenBulkFloor_of_perp hx S σ a hV (h2 _) hp le_rfl hb le_rfl hA hA0 hX hclose

end Closing

end Cvs.StepA.Edge.FiniteTopCorrectedClosing

end
