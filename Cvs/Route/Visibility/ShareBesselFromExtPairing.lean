import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ProjectionShareSawtooth
import Cvs.Route.Visibility.ROneUSumSummable
import Cvs.Route.Visibility.SpinePairingExteriorTransform
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.StepA.Edge.CorrectedPairingUSums
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.LowEigenvalueCountSpine
import Cvs.StepA.OneZeroParitySectors
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The share and Bessel conjuncts from one exterior pairing bound

`⟪r_a, U_ρ⟫ = −Re Φ_ρ(a)/2` on `R₁`, so `‖Φ_ρ(a)‖ ≤ 2K‖r_a‖` gives `‖P U_ρ‖, ‖P V_ρ‖ ≤ K`; with
`‖P(V − Σ aU)‖ ≤ ‖PV‖ + √(Σa²)·√(Σ‖PU‖²)`, the rates `K² = o(x^δ)` and `Bess·K² = o(x^{2δ})` for an `R₁`
Bessel constant give `Cvs.StepA.Edge.CorrectedPairingUSums.ShareBessel` with `s₀ = ½`, the summability coming from Cvs.Route.Visibility.ROneUSumSummable.
-/

noncomputable section

open Real MeasureTheory Filter
open scoped InnerProductSpace
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec)
open Cvs.StepA.Edge.FiniteTopCorrectedClosing (bPerp reps)
open Cvs.Route.Visibility.SpinePairingExteriorTransform (extComb)
open Cvs.StepA.Edge.CorrectedPairingUSums (ShareBessel)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.Route.Visibility.ShareBesselFromExtPairing
open Cvs.ZeroCounting

/-! ### The `ue` pairing on `R₁` -/

/-- **The pairing of an even spine class with a zero's `ue` vector**: `⟪evenPart(spineMap x a), U_ρ⟫ = −Re Φ/2`. -/
theorem inner_evenPart_spineMap_ueVec {x : ℕ} (hx : 80 ≤ 2 * π * x) (hx0 : (0 : ℝ) < x)
    (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (ρ : nonTrivialZeroSet) :
    ⟪Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a),
        ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ
      = -(extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ).re / 2 := by
  rw [Cvs.StepA.LowEigenvalueCountSpine.evenPart_spineMap_eq_wv hx a,
    Cvs.Route.Visibility.VisibilityClosingStep.inner_ueVec hx0 _ _ (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (Cvs.StepA.LowEigenvalueCountSpine.tame_evenWin hx a))]
  exact (Cvs.Route.Visibility.SpinePairingExteriorTransform.integral_ue_ve_evenWin hx a ρ).1

/-- **Both projections from one bound on `Φ`**: if `‖Φ_ρ(a)‖ ≤ 2K‖evenPart(spineMap x a)‖` for every `a`, then
`‖P_{R₁}U_ρ‖ ≤ K` and `‖P_{R₁}V_ρ‖ ≤ K`. -/
theorem norm_proj_le_of_extComb {x : ℕ} (hx : 80 ≤ 2 * π * x) (hx0 : (0 : ℝ) < x) {ρ : nonTrivialZeroSet}
    {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, ‖extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ‖
      ≤ 2 * K * ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖) :
    ‖(R1 x).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ≤ K
      ∧ ‖(R1 x).starProjection (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ≤ K := by
  constructor
  · refine Cvs.Route.Visibility.ProjectionShareSawtooth.norm_starProjection_le_of_pairing (R1 x) hK fun r hr => ?_
    obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
    rw [inner_evenPart_spineMap_ueVec hx hx0 a ρ, abs_div, abs_neg, abs_two]
    have := (Complex.abs_re_le_norm (extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ)).trans (h a)
    linarith
  · refine Cvs.Route.Visibility.ProjectionShareSawtooth.norm_starProjection_le_of_pairing (R1 x) hK fun r hr => ?_
    obtain ⟨a, rfl, hp⟩ := Cvs.Route.Visibility.SpinePairingExteriorTransform.inner_R1_pairVec hx hx0 hr
    rw [hp ρ, abs_div, abs_two]
    have := (Complex.abs_im_le_norm (extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ)).trans (h a)
    linarith

/-! ### The projection of a corrected vector -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (R : Submodule ℝ E)
  [R.HasOrthogonalProjection] {ι : Type*}

/-- **The projection of a corrected vector**: `‖P(V − Σ_s aᵢUᵢ)‖ ≤ ‖PV‖ + √(Σ aᵢ²)·√(Σ ‖PUᵢ‖²)`. -/
theorem norm_proj_sub_sum_le (V : E) (s : Finset ι) (a : ι → ℝ) (U : ι → E) :
    ‖R.starProjection (V - ∑ i ∈ s, a i • U i)‖
      ≤ ‖R.starProjection V‖ + √(∑ i ∈ s, a i ^ 2) * √(∑ i ∈ s, ‖R.starProjection (U i)‖ ^ 2) := by
  rw [map_sub, map_sum]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_sum_le _ _).trans ?_
  simp only [map_smul, norm_smul, Real.norm_eq_abs]
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => |a i|) (fun i => ‖R.starProjection (U i)‖)
  simpa only [sq_abs] using h

/-- With every `‖PUᵢ‖ ≤ K` and `‖PV‖ ≤ K` on `s` of size `n`: `‖P(V − Σ aᵢUᵢ)‖ ≤ K(1 + √(A n))` for `Σ aᵢ² ≤ A`. -/
theorem norm_proj_sub_sum_le_const (V : E) (s : Finset ι) (a : ι → ℝ) (U : ι → E) {K A : ℝ} (hK : 0 ≤ K)
    (hV : ‖R.starProjection V‖ ≤ K) (hU : ∀ i ∈ s, ‖R.starProjection (U i)‖ ≤ K)
    (hA : ∑ i ∈ s, a i ^ 2 ≤ A) :
    ‖R.starProjection (V - ∑ i ∈ s, a i • U i)‖ ≤ K * (1 + √(A * s.card)) := by
  refine (norm_proj_sub_sum_le R V s a U).trans ?_
  have hS : ∑ i ∈ s, ‖R.starProjection (U i)‖ ^ 2 ≤ s.card * K ^ 2 := by
    calc ∑ i ∈ s, ‖R.starProjection (U i)‖ ^ 2 ≤ ∑ _i ∈ s, K ^ 2 :=
          Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (norm_nonneg _) (hU i hi) 2
      _ = s.card * K ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have h1 : √(∑ i ∈ s, a i ^ 2) * √(∑ i ∈ s, ‖R.starProjection (U i)‖ ^ 2)
      ≤ √A * √(s.card * K ^ 2) :=
    mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hS) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 : √A * √(s.card * K ^ 2) = K * √(A * s.card) := by
    rw [Real.sqrt_mul' _ (sq_nonneg K), Real.sqrt_sq hK, ← mul_assoc, mul_comm (√A * _) K,
      ← Real.sqrt_mul' _ (Nat.cast_nonneg _)]
  nlinarith

end Abstract

/-! ### The exterior pairing and `R₁` Bessel rates -/

/-- **The exterior pairing bound** at `x` with constant `K` for the zeros of `S`: `‖Φ_ρ(a)‖ ≤ 2K‖r_a‖`. -/
def ExtPairing (x : ℕ) (S : Finset nonTrivialZeroSet) (K : ℝ) : Prop :=
  ∀ ρ ∈ S, ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, ‖extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ‖
    ≤ 2 * K * ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖

/-- **The `R₁` Bessel bound** at `x` with constant `B`: every `r ∈ R₁` has `Σ_ρ m_ρ⟪r, U_ρ⟫² ≤ B‖r‖²`. -/
def R1Bessel (x : ℕ) (B : ℝ) : Prop :=
  ∀ hx0 : (0 : ℝ) < x, ∀ r ∈ R1 x,
    ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 ≤ B * ‖r‖ ^ 2

/-- The pairing rate for `S`: `K ≥ 0`, `ExtPairing x S (K x)` at all large `x`, and `K² = o(x^δ)`. -/
def ExtPairingRate (S : Finset nonTrivialZeroSet) (δ : ℝ) (K : ℕ → ℝ) : Prop :=
  (∀ x, 0 ≤ K x) ∧ (∀ᶠ x : ℕ in atTop, ExtPairing x S (K x))
    ∧ ∀ ε > 0, ∀ᶠ x : ℕ in atTop, K x ^ 2 ≤ ε * (x : ℝ) ^ δ

/-- The `R₁` Bessel rate against `K`: `Bess ≥ 0`, `R1Bessel x (Bess x)` at all large `x`, `Bess·K² = o(x^{2δ})`. -/
def R1BesselRate (δ : ℝ) (K Bess : ℕ → ℝ) : Prop :=
  (∀ x, 0 ≤ Bess x) ∧ (∀ᶠ x : ℕ in atTop, R1Bessel x (Bess x))
    ∧ ∀ ε > 0, ∀ᶠ x : ℕ in atTop, Bess x * K x ^ 2 ≤ ε * (x : ℝ) ^ (2 * δ)

/-- **`ShareBessel` from the pairing and Bessel rates**: for `σ` in a finite top set `S`, the pairing rate on `S`,
and an `R₁` Bessel rate against it give `ShareBessel S δ σ` with `s₀ = ½`. -/
theorem shareBessel_of_extPairing {S : Finset nonTrivialZeroSet} {δ : ℝ} (hT : FiniteTop S δ)
    {σ : nonTrivialZeroSet} (hσS : σ ∈ S) {K Bess : ℕ → ℝ} (hK : ExtPairingRate S δ K)
    (hB : R1BesselRate δ K Bess) : ShareBessel S δ σ := by
  obtain ⟨hK0, hKe, hKo⟩ := hK
  obtain ⟨hB0, hBess, hBKo⟩ := hB
  obtain ⟨β, hβ, Ka, -, hev⟩ := Cvs.StepA.Edge.FiniteTopCorrectedClosing.eventually_bPerp_bounds hT hσS
  set n : ℝ := ((reps S).card : ℝ)
  set C : ℝ := (1 + √(Ka * n)) ^ 2 with hC
  have hC1 : 1 ≤ C := by
    rw [hC]; nlinarith [Real.sqrt_nonneg (Ka * n)]
  have hC0 : 0 < C := by linarith
  have hproj : ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      β * exp (δ * Real.log x) ≤ ‖bPerp hx0 S σ‖ ^ 2
        ∧ ‖(R1 x).starProjection (bPerp hx0 S σ)‖ ^ 2 ≤ C * K x ^ 2 := by
    filter_upwards [hev, hKe, eventually_ge_atTop 14] with x h1 h2 h14 hx0
    have hx := Cvs.Route.Visibility.VisibilityClosingStep.scale_of_ge h14
    obtain ⟨hlow, a, hV, hKa⟩ := h1 hx0
    have hb : bPerp hx0 S σ = Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
        - ∑ r ∈ reps S, a r • ueVec hx0 (Cvs.ZeroCounting.zPoint r) := by
      rw [hV, add_sub_cancel_right]
    refine ⟨hlow, ?_⟩
    have hPV := (norm_proj_le_of_extComb hx hx0 (hK0 x) (h2 σ hσS)).2
    have hPU : ∀ r ∈ reps S, ‖(R1 x).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint r))‖ ≤ K x :=
      fun r hr => (norm_proj_le_of_extComb hx hx0 (hK0 x) (h2 r (Cvs.StepA.Edge.FiniteTopCorrectedClosing.reps_subset S hr))).1
    have h := norm_proj_sub_sum_le_const (R1 x) _ (reps S) a _ (hK0 x) hPV hPU hKa
    rw [← hb] at h
    refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (le_of_eq ?_)
    rw [hC]; ring
  refine ⟨⟨1 / 2, by norm_num, ?_⟩, Cvs.Route.Visibility.ROneUSumSummable.eventually_summable_bPerp S σ, ?_⟩
  · filter_upwards [hproj, hKo (β / (2 * C)) (by positivity)] with x h1 h2 hx0
    obtain ⟨hlow, hP⟩ := h1 hx0
    rw [Real.rpow_def_of_pos hx0, mul_comm (Real.log (x : ℝ)) δ] at h2
    have : C * K x ^ 2 ≤ (β / 2) * exp (δ * Real.log x) := by
      have := mul_le_mul_of_nonneg_left h2 hC0.le
      rw [show C * (β / (2 * C) * exp (δ * Real.log x)) = β / 2 * exp (δ * Real.log x) by
        field_simp] at this
      exact this
    nlinarith
  · intro ε hε
    filter_upwards [hproj, hBess, hBKo (ε / C) (by positivity)] with x h1 h2 h3 hx0
    obtain ⟨_, hP⟩ := h1 hx0
    refine (h2 hx0 _ ((R1 x).starProjection_apply_mem _)).trans ?_
    calc Bess x * ‖(R1 x).starProjection (bPerp hx0 S σ)‖ ^ 2 ≤ Bess x * (C * K x ^ 2) :=
          mul_le_mul_of_nonneg_left hP (hB0 x)
      _ = C * (Bess x * K x ^ 2) := by ring
      _ ≤ C * (ε / C * (x : ℝ) ^ (2 * δ)) := mul_le_mul_of_nonneg_left h3 hC0.le
      _ = ε * (x : ℝ) ^ (2 * δ) := by field_simp

end Cvs.Route.Visibility.ShareBesselFromExtPairing

end
