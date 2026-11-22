import Mathlib
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.OddSectorSineSums
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.ModeSumsToMinimiser
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowOrthogonalComplement
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# The discrete two-gap from step (a)

StepA's isolation bound reaches every odd coefficient vector (the sine sums are orthogonal to `η`),
and when the discrete bottom lies below the isolation level the even eigenspace is a line: exactly
`Cvs.Finite.TruncationZeroFreeOffAxes`'s `hQpsd`, `hxieven` and `hkerline`.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix

namespace Cvs.Finite.DiscreteTwoGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Scaling -/

omit [DecidableEq ι] in
theorem sineSum_smul (L : ℝ) (mode : ι → ℤ) (t : ℝ) (o : ι → ℝ) :
    Cvs.Finite.OddSectorSineSums.sineSum L mode (t • o)
      = fun y => t * Cvs.Finite.OddSectorSineSums.sineSum L mode o y := by
  funext y; simp only [Cvs.Finite.OddSectorSineSums.sineSum, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  · ring

omit [DecidableEq ι] in
theorem quad_smul (A : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ) :
    (t • v) ⬝ᵥ (A *ᵥ (t • v)) = t ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  rw [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

omit [DecidableEq ι] in
theorem dot_smul_self (t : ℝ) (v : ι → ℝ) : (t • v) ⬝ᵥ (t • v) = t ^ 2 * (v ⬝ᵥ v) := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

omit [DecidableEq ι] in
/-- The normalising scalar: `t² · L · (v ⬝ v) = 1`. -/
theorem normalise {L : ℝ} (hL : 0 < L) {v : ι → ℝ} (hv : v ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ t ^ 2 * (L * (v ⬝ᵥ v)) = 1 := by
  have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' v)
    (fun h => hv (dotProduct_self_eq_zero.mp h.symm))
  have hLv : 0 < L * (v ⬝ᵥ v) := mul_pos hL hpos
  refine ⟨(Real.sqrt (L * (v ⬝ᵥ v)))⁻¹, inv_ne_zero (Real.sqrt_pos.mpr hLv).ne', ?_⟩
  rw [inv_pow, Real.sq_sqrt hLv.le, inv_mul_cancel₀ hLv.ne']

/-! ### The odd gap -/

/-- **StepA's isolation bound reaches every odd coefficient vector.** -/
theorem odd_gap_of_stepA {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam mu : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (heven : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le η = η)
    (hiso : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le, (inner ℝ η v : ℝ) = 0 →
      mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    {mode : ι → ℤ} (hinj : Function.Injective mode) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i) :
    mu * (o ⬝ᵥ o) ≤ o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ o) := by
  have _ : lam = lam := rfl
  by_cases ho : o = 0
  · subst ho; simp
  obtain ⟨t, ht0, ht⟩ := normalise hL ho
  set o' : ι → ℝ := t • o with ho'
  have hodd' : ∀ i, o' (neg i) = -o' i := by
    intro i; simp only [ho', Pi.smul_apply, hodd i, smul_eq_mul]; ring
  have hn : L * (o' ⬝ᵥ o') = 1 := by rw [ho', dot_smul_self]; linarith [ht]
  have hf := Cvs.Finite.ModeSumFormDomain.sineSum_mem_windowSet hL hinj hinv hmode hodd' hn
  set v := Cvs.Limit.ModeSumsToMinimiser.toDomain hL.le hf with hv
  have hrefl : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le v = -v :=
    Cvs.Finite.ModeSumFormDomain.reflD_toDomain_odd hL.le hf
      (Cvs.Finite.ModeSumFormDomain.sineSum_reflect_ae L mode o')
  have hinner : (inner ℝ η v : ℝ) = 0 :=
    Cvs.Finite.ModeSumFormDomain.inner_eq_zero_of_even_odd hL.le heven hrefl
  have h1 := hiso v hinner
  rw [Cvs.Limit.ModeSumsToMinimiser.norm_toDomain, one_pow, mul_one] at h1
  have hQ : Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L)
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.OddSectorSineSums.sineSum L mode o') :=
    Cvs.Limit.ModeSumsToMinimiser.Q_toDomain hL.le P R hf
  rw [hQ, Cvs.Finite.OddSectorSineSums.weilForm_sineSum_eq_ddMatrix hL P R hinj hinv hmode hodd'] at h1
  change mu ≤ L * (o' ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ o')) at h1
  -- `h1 : mu ≤ L * (o' ⬝ M o')`, and `o' = t • o`
  have h2 : o' ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ o')
      = t ^ 2 * (o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ o)) := by
    rw [ho']; exact quad_smul _ t o
  rw [h2] at h1
  have ht2 : 0 < t ^ 2 := by positivity
  -- multiply `h1` by `L * (o ⬝ o) = 1 / t²`
  have hLo : L * (o ⬝ᵥ o) = (t ^ 2)⁻¹ := by
    field_simp; linarith [ht]
  have hL0 : 0 < L := hL
  have hoo : 0 ≤ o ⬝ᵥ o := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o
  have hkey : mu * (L * (o ⬝ᵥ o)) ≤ L * (o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ o)) := by
    rw [hLo]
    have := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr ht2.le)
    calc mu * (t ^ 2)⁻¹ ≤ L * (t ^ 2 * (o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ o))) * (t ^ 2)⁻¹ :=
          this
      _ = L * (o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ o)) := by field_simp
  nlinarith [hkey, hL0]

/-! ### The even eigenspace is a line -/

/-- The pairing of the minimiser's representative against a coefficient vector's cosine sum. -/
def ell {L : ℝ} (hL : 0 ≤ L) (η : Cvs.WeilForm.FormDomain.formDomain hL) (mode : ι → ℤ)
    (w : ι → ℝ) : ℝ :=
  ∫ x, Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) x
    * Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode w x

omit [DecidableEq ι] in
theorem modeSum_add (L : ℝ) (mode : ι → ℤ) (v w : ι → ℝ) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode (v + w)
      = fun y => Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode v y
        + Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode w y := by
  funext y; simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, Pi.add_apply]
  split_ifs
  · rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  · ring

omit [DecidableEq ι] in
theorem modeSum_sub (L : ℝ) (mode : ι → ℤ) (v w : ι → ℝ) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode (v - w)
      = fun y => Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode v y
        - Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode w y := by
  funext y; simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, Pi.sub_apply]
  split_ifs
  · rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  · ring

omit [DecidableEq ι] in
/-- The product of a square-integrable window class with a bounded window function is integrable. -/
theorem integrable_rep_mul_modeSum {L : ℝ} (hL : 0 ≤ L) (η : Cvs.WeilForm.FormDomain.formDomain hL)
    (mode : ι → ℤ) (w : ι → ℝ) :
    Integrable (fun x => Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) x
      * Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode w x) (volume : Measure ℝ) := by
  have hη : Integrable (Cvs.WeilForm.WindowRepresentative.rep (η : Cvs.WeilForm.WeilFormOnWindowL2.window L)) volume :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL (Cvs.WeilForm.WindowRepresentative.memLp_rep _)
      (Cvs.WeilForm.WindowRepresentative.rep_supp _)
  refine hη.mul_bdd (c := ∑ i, |w i|) ?_ ?_
  · exact (Cvs.Finite.ModeSumPairValues.measurable_modeSum L mode w).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Cvs.Finite.ModeSumPairValues.abs_modeSum_le L mode w x

omit [DecidableEq ι] in
theorem ell_smul {L : ℝ} (hL : 0 ≤ L) (η : Cvs.WeilForm.FormDomain.formDomain hL) (mode : ι → ℤ)
    (t : ℝ) (w : ι → ℝ) : ell hL η mode (t • w) = t * ell hL η mode w := by
  unfold ell
  rw [Cvs.Finite.ModeSumFormDomain.modeSum_smul, ← integral_const_mul]
  congr 1; funext x; ring

omit [DecidableEq ι] in
theorem ell_sub {L : ℝ} (hL : 0 ≤ L) (η : Cvs.WeilForm.FormDomain.formDomain hL) (mode : ι → ℤ)
    (v w : ι → ℝ) : ell hL η mode (v - w) = ell hL η mode v - ell hL η mode w := by
  unfold ell
  rw [modeSum_sub, ← integral_sub (integrable_rep_mul_modeSum hL η mode v)
    (integrable_rep_mul_modeSum hL η mode w)]
  congr 1; funext x; ring

omit [DecidableEq ι] in
/-- **The inner product of `η` with the class of a normalised cosine sum is `ell`.** -/
theorem inner_toDomain_eq_ell {L : ℝ} (hL : 0 ≤ L) (η : Cvs.WeilForm.FormDomain.formDomain hL)
    {mode : ι → ℤ} {w : ι → ℝ}
    (hf : Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode w ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    (inner ℝ η (Cvs.Limit.ModeSumsToMinimiser.toDomain hL hf) : ℝ) = ell hL η mode w := by
  have h : (inner ℝ η (Cvs.Limit.ModeSumsToMinimiser.toDomain hL hf) : ℝ)
      = inner ℝ (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) (Cvs.Limit.ModeSumsToMinimiser.toWindow hf) := rfl
  rw [h, Cvs.WeilForm.WindowOrthogonalComplement.inner_rep]
  unfold ell
  apply integral_congr_ae
  filter_upwards [Cvs.Limit.ModeSumsToMinimiser.rep_toWindow_ae hf] with x hx
  rw [hx]

/-- **An even `lamD`-eigenvector orthogonal to `η` vanishes**, when `lamD < mu`. -/
theorem eq_zero_of_even_eigen_perp {L : ℝ} (hL : 0 < L) (P R : ℕ) {mu : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (hiso : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le, (inner ℝ η v : ℝ) = 0 →
      mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    {mode : ι → ℤ} (hinj : Function.Injective mode) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {lamD : ℝ} (hlt : lamD < mu) {w : ι → ℝ} (hweven : ∀ i, w (neg i) = w i)
    (hw : Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ w = lamD • w) (hperp : ell hL.le η mode w = 0) :
    w = 0 := by
  by_contra hne
  obtain ⟨t, ht0, ht⟩ := normalise hL hne
  set w' : ι → ℝ := t • w with hw'
  have heven' : ∀ i, w' (neg i) = w' i := by
    intro i; simp only [hw', Pi.smul_apply, hweven i]
  have hn : L * (w' ⬝ᵥ w') = 1 := by rw [hw', dot_smul_self]; linarith [ht]
  have hf := Cvs.Finite.ModeSumFormDomain.modeSum_mem_evenWindowSet hL hinj hinv hmode heven' hn
  set v := Cvs.Limit.ModeSumsToMinimiser.toDomain hL.le hf.1 with hv
  have hinner : (inner ℝ η v : ℝ) = 0 := by
    rw [hv, inner_toDomain_eq_ell, hw', ell_smul, hperp, mul_zero]
  have h1 := hiso v hinner
  rw [Cvs.Limit.ModeSumsToMinimiser.norm_toDomain, one_pow, mul_one] at h1
  have hQ : Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L)
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode w') :=
    Cvs.Limit.ModeSumsToMinimiser.Q_toDomain hL.le P R hf.1
  rw [hQ, Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix hL P R hinj hinv hmode heven'] at h1
  change mu ≤ L * (w' ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ w')) at h1
  -- the eigen-equation makes the form `lamD` times the norm
  have heig : Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ w' = lamD • w' := by
    rw [hw', Matrix.mulVec_smul, hw, smul_comm]
  have hform : w' ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ w') = lamD * (w' ⬝ᵥ w') := by
    rw [heig, dotProduct_smul, smul_eq_mul]
  rw [hform, ← mul_assoc, mul_comm L lamD, mul_assoc, hn, mul_one] at h1
  linarith

/-- **The even `lamD`-eigenspace is the line through the discrete minimiser**, when `lamD < mu`. -/
theorem even_kerline_of_stepA {L : ℝ} (hL : 0 < L) (P R : ℕ) {mu : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (hiso : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le, (inner ℝ η v : ℝ) = 0 →
      mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    {mode : ι → ℤ} (hinj : Function.Injective mode) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {lamD : ℝ} (hlt : lamD < mu) {xi : ι → ℝ} (hxi1 : xi ⬝ᵥ xi = 1)
    (hxieven : ∀ i, xi (neg i) = xi i)
    (hxi : Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ xi = lamD • xi) :
    ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ v = lamD • v →
      ∃ c : ℝ, v = c • xi := by
  intro v hveven hv
  have hxi0 : xi ≠ 0 := by
    intro h; rw [h] at hxi1; simp at hxi1
  -- `ell xi ≠ 0`, else `xi` itself would vanish
  have hℓxi : ell hL.le η mode xi ≠ 0 := by
    intro h
    exact hxi0 (eq_zero_of_even_eigen_perp hL P R hiso hinj hinv hmode hlt hxieven hxi h)
  -- the combination `ell v • xi − ell xi • v` is even, an eigenvector, and orthogonal to `η`
  set w : ι → ℝ := ell hL.le η mode v • xi - ell hL.le η mode xi • v with hw
  have hweven : ∀ i, w (neg i) = w i := by
    intro i; simp only [hw, Pi.sub_apply, Pi.smul_apply, hxieven i, hveven i]
  have hweig : Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ w = lamD • w := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hxi, hv, smul_sub,
      smul_comm lamD, smul_comm lamD]
  have hwperp : ell hL.le η mode w = 0 := by
    rw [hw, ell_sub, ell_smul, ell_smul]; ring
  have hw0 := eq_zero_of_even_eigen_perp hL P R hiso hinj hinv hmode hlt hweven hweig hwperp
  refine ⟨ell hL.le η mode v / ell hL.le η mode xi, ?_⟩
  rw [hw, sub_eq_zero] at hw0
  -- `ell v • xi = ell xi • v`
  funext i
  have := congrFun hw0 i
  simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
  field_simp
  linarith

end Cvs.Finite.DiscreteTwoGap
