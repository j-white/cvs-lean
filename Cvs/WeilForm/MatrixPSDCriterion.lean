import Mathlib
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.OddSectorSineSums
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.ModeSumsToMinimiser
import Cvs.Route.OneCellBoxWindowForm
import Cvs.Route.OneCellCriterion
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PositivityOfRH
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormHomogeneous
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowSetNonempty

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The CvS matrix criterion: RH ⟺ the window matrix is positive semidefinite at every scale

At a complete truncation (`e^L ≤ P`, `L ≤ R log 2`) RH makes the CvS matrix `Cvs.Finite.TruncationQuadraticForm.M` positive semidefinite on
every symmetric mode set: `L·vᵀMv` is the Weil form of a cosine sum plus a sine sum, both window functions.
Its constant-mode corner is `L·M₀₀ = G(L)`, the one-cell function, so the corner alone, as `L` varies, gives RH.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix

namespace Cvs.WeilForm.MatrixPSDCriterion
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form at a unit vector is the diagonal entry. -/
theorem single_quad (A : Matrix ι ι ℝ) (i₀ : ι) :
    Pi.single i₀ (1:ℝ) ⬝ᵥ (A *ᵥ Pi.single i₀ 1) = A i₀ i₀ := by
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul]
  rfl

omit [DecidableEq ι] in
/-- The cosine sum is linear in its coefficients. -/
theorem modeSum_smul (L : ℝ) (mode : ι → ℤ) (t : ℝ) (xi : ι → ℝ) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode (t • xi) = fun y => t * Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi y := by
  funext y; simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  · ring

/-- The Weil form of the zero function vanishes. -/
theorem weilForm_zero (P R : ℕ) : Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (fun _ => (0:ℝ)) = 0 := by
  have h := Cvs.WeilForm.WeilFormHomogeneous.weilForm_smul P R 0 (fun _ => (0:ℝ))
  simpa using h

/-- A Weil form that is nonnegative after a nonzero rescaling is nonnegative. -/
theorem weilForm_nonneg_of_smul {P R : ℕ} {f : ℝ → ℝ} {t : ℝ} (ht : t ≠ 0)
    (h : 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (fun y => t * f y)) : 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  rw [Cvs.WeilForm.WeilFormHomogeneous.weilForm_smul] at h
  exact nonneg_of_mul_nonneg_right (by linarith) (pow_pos (abs_pos.2 ht) 2 |>.trans_eq (sq_abs t))

/-- **RH makes the Weil form of every window function nonnegative** at a complete truncation. -/
theorem weilForm_nonneg_of_mem (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) {P R : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) {f : ℝ → ℝ} (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  rw [← Cvs.Limit.ModeSumsToMinimiser.Q_toDomain hL.le P R hf]
  exact Cvs.WeilForm.PositivityOfRH.Q_nonneg_of_RH hRH hL hP hR _

variable {mode : ι → ℤ} {neg : ι → ι}

/-- **RH makes the Weil form of every even cosine sum nonnegative.** -/
theorem weilForm_modeSum_nonneg (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) {P R : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (hinj : Function.Injective mode)
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ}
    (hxi : ∀ i, xi (neg i) = xi i) : 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) := by
  by_cases h0 : xi = 0
  · have : Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi = fun _ => 0 := by
      funext y; simp [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, h0]
    rw [this, weilForm_zero]
  obtain ⟨t, ht, htn⟩ := Cvs.Finite.DiscreteTwoGap.normalise hL h0
  have hmem := Cvs.Finite.ModeSumFormDomain.modeSum_mem_evenWindowSet hL hinj hinv hmode (xi := t • xi)
    (fun i => by simp [hxi i]) (by rw [Cvs.Finite.DiscreteTwoGap.dot_smul_self]; linarith)
  have := weilForm_nonneg_of_mem hRH hL hP hR hmem.1
  rw [modeSum_smul] at this
  exact weilForm_nonneg_of_smul ht this

/-- **RH makes the Weil form of every odd sine sum nonnegative.** -/
theorem weilForm_sineSum_nonneg (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) {P R : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (hinj : Function.Injective mode)
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {o : ι → ℝ}
    (ho : ∀ i, o (neg i) = -o i) : 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.OddSectorSineSums.sineSum L mode o) := by
  by_cases h0 : o = 0
  · have : Cvs.Finite.OddSectorSineSums.sineSum L mode o = fun _ => 0 := by
      funext y; simp [Cvs.Finite.OddSectorSineSums.sineSum, h0]
    rw [this, weilForm_zero]
  obtain ⟨t, ht, htn⟩ := Cvs.Finite.DiscreteTwoGap.normalise hL h0
  have hmem := Cvs.Finite.ModeSumFormDomain.sineSum_mem_windowSet hL hinj hinv hmode (o := t • o)
    (fun i => by simp [ho i]) (by rw [Cvs.Finite.DiscreteTwoGap.dot_smul_self]; linarith)
  have := weilForm_nonneg_of_mem hRH hL hP hR hmem
  rw [Cvs.Finite.DiscreteTwoGap.sineSum_smul] at this
  exact weilForm_nonneg_of_smul ht this

/-- **RH makes the CvS matrix positive semidefinite** on every symmetric mode set, at a complete
truncation. -/
theorem posSemidef_of_rh (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) {P R : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (hinj : Function.Injective mode)
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) :
    (Cvs.Finite.TruncationQuadraticForm.M P R L mode).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, star_trivial]
    exact Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj j i
  · rw [star_trivial]
    have h := Cvs.Finite.TruncationQuadraticForm.quadForm_eq_weil hL P R hinj hinv hmode v
    have h1 := weilForm_modeSum_nonneg hRH hL hP hR hinj hinv hmode
      (Cvs.Finite.TruncationQuadraticForm.evenPart_even hinv v)
    have h2 := weilForm_sineSum_nonneg hRH hL hP hR hinj hinv hmode
      (Cvs.Finite.TruncationQuadraticForm.oddPart_odd hinv v)
    exact nonneg_of_mul_nonneg_right (h ▸ add_nonneg h1 h2) hL

/-! ### The constant-mode corner is the one-cell function -/

/-- The unit vector at the constant mode is its own cosine sum: the box. -/
theorem modeSum_single {L : ℝ} {i₀ : ι} (h0 : mode i₀ = 0) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode (Pi.single i₀ 1) = Cvs.WeilForm.WindowSetNonempty.flat L := by
  funext y
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, Cvs.WeilForm.WindowSetNonempty.flat, Set.indicator]
  split_ifs
  · rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
    simp [Cvs.Finite.TruncationZeroFreeOffAxes.omega, h0]
  · rfl

/-- **The corner of the CvS matrix is the one-cell function**: `L·M₀₀ = G(L)` at a complete
truncation, for any mode set containing the constant mode. -/
theorem corner_eq {L : ℝ} (hL : 0 < L) {P R : ℕ} (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2)
    (hinj : Function.Injective mode) (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {i₀ : ι} (h0 : mode i₀ = 0) :
    L * Cvs.Finite.TruncationQuadraticForm.M P R L mode i₀ i₀ = Cvs.Route.OneCellLaplaceTransform.G L := by
  have hn : neg i₀ = i₀ := hinj (by rw [hmode, h0, neg_zero])
  have hsingle : ∀ i, (Pi.single i₀ (1:ℝ) : ι → ℝ) (neg i) = (Pi.single i₀ (1:ℝ) : ι → ℝ) i := by
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [hn]
    · have : neg i ≠ i₀ := fun h => hi (by rw [← hinv i, h, hn])
      simp [hi, this]
  have he : Cvs.Finite.TruncationQuadraticForm.evenPart neg (Pi.single i₀ (1:ℝ)) = Pi.single i₀ 1 := by
    funext i; simp only [Cvs.Finite.TruncationQuadraticForm.evenPart, hsingle]; ring
  have ho : Cvs.Finite.TruncationQuadraticForm.oddPart neg (Pi.single i₀ (1:ℝ)) = 0 := by
    funext i; simp only [Cvs.Finite.TruncationQuadraticForm.oddPart, hsingle]; simp
  have h := Cvs.Finite.TruncationQuadraticForm.quadForm_eq_weil hL P R hinj hinv hmode (Pi.single i₀ 1)
  have hsine : Cvs.Finite.OddSectorSineSums.sineSum L mode 0 = fun _ => 0 := by
    funext y; simp [Cvs.Finite.OddSectorSineSums.sineSum]
  rw [he, ho, hsine, weilForm_zero, add_zero, modeSum_single h0,
    Cvs.Route.OneCellBoxWindowForm.weilForm_flat_eq hL hP hR] at h
  rw [← h, single_quad]

/-! ### The criterion -/

/-- The complete truncation at scale `L`: `P = ⌈e^L⌉`, `R = ⌈L / log 2⌉`. -/
theorem complete (L : ℝ) :
    Real.exp L ≤ (⌈Real.exp L⌉₊ : ℕ) ∧ L ≤ (⌈L / Real.log 2⌉₊ : ℕ) * Real.log 2 := by
  refine ⟨Nat.le_ceil _, ?_⟩
  have hl := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have := Nat.le_ceil (L / Real.log 2)
  rwa [div_le_iff₀ hl] at this

/-- **RH from the corner alone**: if `M₀₀ ≥ 0` at every scale, RH. -/
theorem rh_of_corner_nonneg
    (h : ∀ L : ℝ, 0 < L → 0 ≤ Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (Cvs.Finite.SymmetricModeSet.mode 0) none none) :
    RiemannHypothesis := by
  refine Cvs.Route.OneCellCriterion.riemannHypothesis_of_G_nonneg fun L hL => ?_
  rw [← corner_eq hL (complete L).1 (complete L).2 (Cvs.Finite.SymmetricModeSet.mode_injective 0) (Cvs.Finite.SymmetricModeSet.negI_involutive 0)
    (Cvs.Finite.SymmetricModeSet.mode_negI 0) (i₀ := none) rfl]
  exact mul_nonneg hL.le (h L hL)

/-- **The CvS matrix criterion**: RH iff the CvS matrix is positive semidefinite on every symmetric
mode set `Idx N` at every scale `L > 0`, with the complete truncation. -/
theorem rh_iff_posSemidef :
    RiemannHypothesis ↔ ∀ L : ℝ, 0 < L → ∀ N : ℕ,
      (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (Cvs.Finite.SymmetricModeSet.mode N)).PosSemidef := by
  refine ⟨fun hRH L hL N => posSemidef_of_rh hRH hL (complete L).1 (complete L).2
    (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N), fun h => ?_⟩
  refine rh_of_corner_nonneg fun L hL => ?_
  have := ((posSemidef_iff_dotProduct_mulVec.1 (h L hL 0)).2 (Pi.single none 1))
  rwa [star_trivial, single_quad] at this

/-- **The corner criterion**: RH iff the constant-mode corner of the CvS matrix is nonnegative at
every scale. -/
theorem rh_iff_corner_nonneg :
    RiemannHypothesis ↔ ∀ L : ℝ, 0 < L →
      0 ≤ Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (Cvs.Finite.SymmetricModeSet.mode 0) none none := by
  refine ⟨fun hRH L hL => ?_, rh_of_corner_nonneg⟩
  have := ((posSemidef_iff_dotProduct_mulVec.1 (rh_iff_posSemidef.1 hRH L hL 0)).2 (Pi.single none 1))
  rwa [star_trivial, single_quad] at this

end Cvs.WeilForm.MatrixPSDCriterion
