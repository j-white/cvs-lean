import Mathlib
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EvenBottomRealRoots
import Cvs.Finite.SecularRealRooted
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Limit.DiscreteSpine
import Cvs.Limit.OffAxesLimit
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# Tools for a zero-free even ground state without simplicity
Even minimisers of a symmetric reflection-invariant matrix exist and are eigenvectors (`exists_even_min`). Lowering
the diagonal on one reflection pair makes the even bottom simple when it drops (`evenSimple_of_drop`). A `ddMatrix`
with even diagonal and simple even bottom has a zero-free transform (`zeroFree_of_ddMatrix`). The transform at
`−ω_j` is `L·ξ_j` (`fourierLaplace_at_mode`), so a nonzero vector's transform is nowhere locally zero, and transforms
converge locally uniformly off the axes with their coefficients (`tendstoLocallyUniformlyOn_transform`).
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Matrix Filter Topology

namespace Cvs.Finite.EvenGroundStateTools
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Even minimisers -/

theorem eigen_of_even_min {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hneg : ∀ i j, A (neg i) (neg j) = A i j)
    {lam : ℝ} {xi : ι → ℝ} (hxie : ∀ i, xi (neg i) = xi i)
    (hmin : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hlev : xi ⬝ᵥ (A *ᵥ xi) = lam * (xi ⬝ᵥ xi)) : A *ᵥ xi = lam • xi := by
  set B : Matrix ι ι ℝ := A - lam • (1 : Matrix ι ι ℝ) with hB
  have hBv : ∀ v : ι → ℝ, B *ᵥ v = A *ᵥ v - lam • v := by
    intro v; rw [hB, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hBq : ∀ v : ι → ℝ, v ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (A *ᵥ v) - lam * (v ⬝ᵥ v) := by
    intro v; rw [hBv, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hBsymm : ∀ i j, B i j = B j i := by
    intro i j
    simp only [hB, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [hsymm i j]
    by_cases h : i = j
    · rw [h]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  have hBneg : ∀ i j, B (neg i) (neg j) = B i j := by
    intro i j
    simp only [hB, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hneg]
    by_cases h : i = j
    · rw [ite_eq_left (by rw [h]), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hinv.injective h')), ite_eq_right h]
  have hBpsd : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → 0 ≤ v ⬝ᵥ (B *ᵥ v) := by
    intro v hv; rw [hBq]; linarith [hmin v hv]
  have h0 : xi ⬝ᵥ (B *ᵥ xi) = 0 := by rw [hBq, hlev, sub_self]
  have hk := Cvs.Finite.EvenBottomRealRoots.mulVec_eq_zero_of_even_psd hBsymm hinv hBneg hBpsd hxie h0
  rw [hBv, sub_eq_zero] at hk
  exact hk

theorem even_quad_ge {A : Matrix ι ι ℝ} {neg : ι → ι} {lam : ℝ}
    (hmin : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → v ⬝ᵥ v = 1 → lam ≤ v ⬝ᵥ (A *ᵥ v))
    (v : ι → ℝ) (hv : ∀ i, v (neg i) = v i) : lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
  by_cases hv0 : v = 0
  · subst hv0; simp
  · have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' v)
      (fun h => hv0 (dotProduct_self_eq_zero.mp h.symm))
    set c : ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ with hc
    have hcc : c * c = (v ⬝ᵥ v)⁻¹ := by rw [hc, ← mul_inv, Real.mul_self_sqrt hpos.le]
    have h1 : (c • v) ⬝ᵥ (c • v) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hcc,
        inv_mul_cancel₀ hpos.ne']
    have h : lam ≤ (c • v) ⬝ᵥ (A *ᵥ (c • v)) := hmin _ (fun i => by simp [hv i]) h1
    rw [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hcc] at h
    calc lam * (v ⬝ᵥ v) ≤ (v ⬝ᵥ v)⁻¹ * (v ⬝ᵥ (A *ᵥ v)) * (v ⬝ᵥ v) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = v ⬝ᵥ (A *ᵥ v) := by field_simp

/-- **Even minimisers exist and are eigenvectors.** -/
theorem exists_even_min {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hneg : ∀ i j, A (neg i) (neg j) = A i j)
    {v0 : ι → ℝ} (hv0e : ∀ i, v0 (neg i) = v0 i) (hv01 : v0 ⬝ᵥ v0 = 1) :
    ∃ (lam : ℝ) (xi : ι → ℝ), (∀ i, xi (neg i) = xi i) ∧ xi ⬝ᵥ xi = 1
      ∧ (∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
      ∧ A *ᵥ xi = lam • xi := by
  set E : Set (ι → ℝ) := {v | ∀ i, v (neg i) = v i} with hE
  have hEclosed : IsClosed E := by
    have : E = ⋂ i, {v : ι → ℝ | v (neg i) = v i} := by ext v; simp [hE]
    rw [this]
    exact isClosed_iInter fun i => isClosed_eq (continuous_apply _) (continuous_apply _)
  have hK : IsCompact (Cvs.Upstream.SymmetricMatrixBottom.sphere ι ∩ E) :=
    Cvs.Upstream.SymmetricMatrixBottom.isCompact_sphere.inter_right hEclosed
  obtain ⟨xi, ⟨hxis, hxie⟩, hmin⟩ := hK.exists_isMinOn ⟨v0, hv01, hv0e⟩
    (by fun_prop : Continuous fun v : ι → ℝ => v ⬝ᵥ (A *ᵥ v)).continuousOn
  have hxi1 : xi ⬝ᵥ xi = 1 := hxis
  have hge := even_quad_ge (A := A) (neg := neg) (lam := xi ⬝ᵥ (A *ᵥ xi))
    (fun v hv hv1 => hmin (show v ∈ Cvs.Upstream.SymmetricMatrixBottom.sphere ι ∩ E from ⟨hv1, hv⟩))
  exact ⟨_, xi, hxie, hxi1, hge, eigen_of_even_min hsymm hinv hneg hxie hge (by rw [hxi1, mul_one])⟩

/-! ### Dropping one reflection pair of the diagonal -/

theorem quad_sub_diagonal (A : Matrix ι ι ℝ) (d v : ι → ℝ) :
    v ⬝ᵥ ((A - Matrix.diagonal d) *ᵥ v) = v ⬝ᵥ (A *ᵥ v) - ∑ i, d i * v i ^ 2 := by
  have hD : Matrix.diagonal d *ᵥ v = fun i => d i * v i := by
    ext i; exact Matrix.mulVec_diagonal d v i
  rw [Matrix.sub_mulVec, hD, dotProduct_sub]
  congr 1
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Dropping the diagonal on one reflection pair makes a dropped even bottom simple.** -/
theorem evenSimple_of_drop {A : Matrix ι ι ℝ} {neg : ι → ι} {d : ι → ℝ} {i0 : ι}
    (hdz : ∀ i, d i ≠ 0 → i = i0 ∨ i = neg i0) {lam mu : ℝ}
    (hA : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) (hmu : mu < lam)
    {eta : ι → ℝ} (hetae : ∀ i, eta (neg i) = eta i) (heta0 : eta ≠ 0)
    (heta : (A - Matrix.diagonal d) *ᵥ eta = mu • eta) :
    ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → (A - Matrix.diagonal d) *ᵥ v = mu • v →
      ∃ c : ℝ, v = c • eta := by
  have key : ∀ y : ι → ℝ, (∀ i, y (neg i) = y i) → y i0 = 0 →
      (A - Matrix.diagonal d) *ᵥ y = mu • y → y = 0 := by
    intro y hye hy0 hy
    have hyn : y (neg i0) = 0 := by rw [hye i0, hy0]
    have hdy : ∑ i, d i * y i ^ 2 = 0 := Finset.sum_eq_zero fun i _ => by
      by_cases hd : d i = 0
      · rw [hd, zero_mul]
      · rcases hdz i hd with h | h <;> simp [h, hy0, hyn]
    have hq := quad_sub_diagonal A d y
    rw [hy, dotProduct_smul, smul_eq_mul, hdy, sub_zero] at hq
    have h1 := hA y hye
    have hnn := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' y
    have hyy : y ⬝ᵥ y = 0 := by nlinarith
    exact dotProduct_self_eq_zero.mp hyy
  have heta_i0 : eta i0 ≠ 0 := fun h => heta0 (key eta hetae h heta)
  intro v hve hv
  refine ⟨v i0 / eta i0, ?_⟩
  have hy := key (eta i0 • v - v i0 • eta)
    (fun i => by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hve i, hetae i])
    (by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
    (by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hv, heta]
      ext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
  ext i
  have := congrFun hy i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
  rw [div_mul_eq_mul_div, eq_div_iff heta_i0]
  linear_combination this

theorem ddMatrix_sub_diag (a b pos d : ι → ℝ) :
    Cvs.Finite.DividedDifferenceCommutator.ddMatrix (a - d) b pos = Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b pos - Matrix.diagonal d := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Cvs.Finite.DividedDifferenceCommutator.ddMatrix]
  · simp [Cvs.Finite.DividedDifferenceCommutator.ddMatrix, h]

/-! ### Zero-freeness for a general even diagonal -/

theorem zeroFree_of_ddMatrix {L : ℝ} (hL : 0 < L) {mode : ι → ℤ} (hmodeinj : Function.Injective mode)
    {neg : ι → ι} (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {a b : ι → ℝ}
    (ha : ∀ i, a (neg i) = a i) (hb : ∀ i, b (neg i) = -b i) {lam : ℝ} {xi : ι → ℝ}
    (hxieven : ∀ i, xi (neg i) = xi i) (hxi0 : xi ≠ 0)
    (hmin : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) →
      lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) *ᵥ v))
    (hxi : Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) *ᵥ xi = lam • xi)
    (hker : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) →
      Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) *ᵥ v = lam • v →
        ∃ c : ℝ, v = c • xi) :
    ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi)) z ≠ 0 := by
  intro z hz hzero
  obtain ⟨hre, him⟩ := hz
  have hz0 : ∀ i, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z ≠ 0 := by
    intro i hc; exact him (by simpa using congrArg Complex.im hc)
  rw [Cvs.Finite.SecularRealRooted.fourierLaplace_eq_S hL hinv hmode hxieven hz0] at hzero
  have hpre : Complex.exp (Complex.I * z * (L : ℂ)) - 1 ≠ 0 := by
    intro hc
    have h1 : Complex.exp (Complex.I * z * (L : ℂ)) = 1 := sub_eq_zero.mp hc
    have h2 : Real.exp ((Complex.I * z * (L : ℂ)).re) = 1 := by
      rw [← Complex.norm_exp, h1, norm_one]
    have h3 : (Complex.I * z * (L : ℂ)).re = 0 := by
      have he : Real.exp ((Complex.I * z * (L : ℂ)).re) = Real.exp 0 := by rw [h2, Real.exp_zero]
      exact Real.exp_injective he
    have h4 : -(z.im * L) = 0 := by simpa [Complex.mul_re, Complex.mul_im] using h3
    exact him (by
      have : z.im * L = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (ne_of_gt hL))
  have hzne : z ≠ 0 := fun h => hre (by rw [h, Complex.zero_re])
  have hS : Cvs.Finite.UniversalFunctionPairing.S L mode xi z = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exfalso
      rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact Complex.I_ne_zero h''
        · exact hzne h''
      · exact hpre h'
    · exact h
  have hw : (z ^ 2).im ≠ 0 := by
    rw [sq, Complex.mul_im]
    have : z.re * z.im + z.im * z.re = 2 * (z.re * z.im) := by ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hre him)
  have hsec := Cvs.Finite.EvenBottomRealRoots.secular_ne_zero (a := a) (b := b)
    (ω := Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode)
    (Cvs.Finite.DisplacementIdentity.omega_injective hL hmodeinj) hinv
    (Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg hmode) hb ha hxieven hxi0 hmin hxi hker hw
  apply hsec
  rw [← hS]
  unfold Cvs.Finite.UniversalFunctionPairing.S
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]
  push_cast
  rfl

/-! ### The transform recovers the coefficients -/

/-- **The transform at `−ω_j` is `L·ξ_j`.** -/
theorem fourierLaplace_at_mode {L : ℝ} (hL : 0 < L) {mode : ι → ℤ} (hmodeinj : Function.Injective mode)
    {neg : ι → ι} (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ}
    (hxieven : ∀ i, xi (neg i) = xi i) (j : ι) :
    FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi))
      (-((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ)) = (L : ℂ) * xi j := by
  set z : ℂ := -((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ) with hzdef
  have hInd : ∀ t : ℝ, Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) t
        * Complex.exp (Complex.I * z * (t : ℂ))
      = Set.indicator (Set.Ioc (0 : ℝ) L)
          (fun t : ℝ => (∑ i, (xi i : ℂ) * Complex.exp (Complex.I
            * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z) * (t : ℂ)))) t := by
    intro t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) L
    · rw [Set.indicator_of_mem ht]
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, ite_eq_left ht]
      rw [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum_eq_exp_sum hinv hmode hxieven t, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, ← Complex.exp_add]
      ring_nf
    · rw [Set.indicator_of_notMem ht]
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, ite_eq_right ht]
      simp
  rw [FourierLaplace.fourierLaplace]
  simp only [hInd]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hL.le]
  have hint : ∀ i : ι, IntervalIntegrable
      (fun t : ℝ => (xi i : ℂ)
        * Complex.exp (Complex.I * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z) * (t : ℂ)))
      MeasureTheory.volume 0 L := fun i =>
    (continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable 0 L
  rw [intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  rw [Finset.sum_eq_single j]
  · have hj : ∀ t : ℝ, (xi j : ℂ)
        * Complex.exp (Complex.I * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ) + z) * (t : ℂ))
        = (xi j : ℂ) := by
      intro t; rw [hzdef, add_neg_cancel, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    simp only [hj, intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  · intro i _ hij
    have hω : (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) ≠ Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j :=
      fun h => hij (Cvs.Finite.DisplacementIdentity.omega_injective hL hmodeinj h)
    have hc : Complex.I * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z) ≠ 0 := by
      refine mul_ne_zero Complex.I_ne_zero ?_
      rw [hzdef, ← sub_eq_add_neg, sub_ne_zero]
      exact_mod_cast hω
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
    have hsplit : Complex.exp (Complex.I * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z) * (L : ℂ))
        = 1 := by
      rw [show Complex.I * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z) * (L : ℂ)
          = Complex.I * ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) * (L : ℂ)
            - Complex.I * ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ) * (L : ℂ) by rw [hzdef]; ring,
        Complex.exp_sub, Cvs.Finite.TruncationZeroFreeOffAxes.exp_omega_mul (ne_of_gt hL) mode i,
        Cvs.Finite.TruncationZeroFreeOffAxes.exp_omega_mul (ne_of_gt hL) mode j, div_one]
    rw [hsplit]
    simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **A nonzero even vector's transform is nowhere locally zero.** -/
theorem transform_not_eventually_zero {L : ℝ} (hL : 0 < L) {mode : ι → ℤ} (hmodeinj : Function.Injective mode)
    {neg : ι → ι} (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ}
    (hxieven : ∀ i, xi (neg i) = xi i) (hxi0 : xi ≠ 0) (z₀ : ℂ) :
    ¬ (∀ᶠ z in 𝓝 z₀, FourierLaplace.fourierLaplace
      (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi)) z = 0) := by
  intro h
  have hA : AnalyticOnNhd ℂ (FourierLaplace.fourierLaplace
      (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi))) Set.univ :=
    fun z _ => (Cvs.Limit.DiscreteSpine.differentiable_modeSum hL mode xi).analyticAt z
  have hE := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z₀) h
  apply hxi0
  funext j
  have h1 : FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi))
      (-((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ)) = 0 := hE (Set.mem_univ _)
  rw [fourierLaplace_at_mode hL hmodeinj hinv hmode hxieven j] at h1
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have : (xi j : ℂ) = 0 := (mul_eq_zero.mp h1).resolve_left hL'
  exact_mod_cast this

/-! ### Locally uniform convergence of transforms -/

theorem tendstoLocallyUniformlyOn_const' {X : Type*} [TopologicalSpace X] {s : Set X} (g : X → ℂ) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => g) g atTop s :=
  fun _ hu _ _ => ⟨s, self_mem_nhdsWithin, Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩

theorem tendstoLocallyUniformlyOn_sum {X : Type*} [TopologicalSpace X] {s : Set X}
    (c : ℕ → ι → ℂ) (c0 : ι → ℂ) (hc : ∀ i, Tendsto (fun k => c k i) atTop (𝓝 (c0 i)))
    (g : ι → X → ℂ) (hg : ∀ i, ContinuousOn (g i) s) (t : Finset ι) :
    TendstoLocallyUniformlyOn (fun k x => ∑ i ∈ t, c k i * g i x) (fun x => ∑ i ∈ t, c0 i * g i x)
      atTop s := by
  induction t using Finset.induction_on with
  | empty => simpa using tendstoLocallyUniformlyOn_const' (s := s) (fun _ : X => (0 : ℂ))
  | insert j t hj ih =>
    simp only [Finset.sum_insert hj]
    have h1 : TendstoLocallyUniformlyOn (fun k (_ : X) => c k j) (fun _ => c0 j) atTop s :=
      ((hc j).tendstoUniformlyOn_const s).tendstoLocallyUniformlyOn
    have hterm := h1.mul₀ (tendstoLocallyUniformlyOn_const' (s := s) (g j)) continuousOn_const (hg j)
    exact hterm.add ih

/-- **Transforms converge locally uniformly off the axes with their coefficients.** -/
theorem tendstoLocallyUniformlyOn_transform {L : ℝ} (hL : 0 < L) {mode : ι → ℤ} {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    (xs : ℕ → ι → ℝ) (x0 : ι → ℝ) (hxs : ∀ k i, xs k (neg i) = xs k i) (hx0 : ∀ i, x0 (neg i) = x0 i)
    (hconv : ∀ i, Tendsto (fun k => xs k i) atTop (𝓝 (x0 i))) :
    TendstoLocallyUniformlyOn
      (fun k => FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode (xs k))))
      (FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode x0)))
      atTop Cvs.Limit.OffAxesLimit.offAxes := by
  set g : ι → ℂ → ℂ := fun i z => Complex.I * z * (Complex.exp (Complex.I * z * (L : ℂ)) - 1)
    / (((2 * π * mode i / L : ℝ) : ℂ) ^ 2 - z ^ 2) with hg
  have hden : ∀ i, ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes,
      (((2 * π * mode i / L : ℝ) : ℂ) ^ 2 - z ^ 2) ≠ 0 := by
    intro i z hz h
    have hre0 : ((((2 * π * mode i / L : ℝ) : ℂ) ^ 2)).im = 0 := by
      rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
    have h' := congrArg Complex.im h
    rw [Complex.sub_im, hre0, Complex.zero_im, zero_sub, neg_eq_zero] at h'
    exact Cvs.Limit.OffAxesLimit.notMem_offAxes_of_sq_im h' hz
  have hgc : ∀ i, ContinuousOn (g i) Cvs.Limit.OffAxesLimit.offAxes := by
    intro i
    have hnum : Continuous (fun z : ℂ => Complex.I * z * (Complex.exp (Complex.I * z * (L : ℂ)) - 1)) := by
      fun_prop
    have hdc : Continuous (fun z : ℂ => ((2 * π * mode i / L : ℝ) : ℂ) ^ 2 - z ^ 2) := by
      fun_prop
    exact ContinuousOn.div (f := fun z : ℂ => Complex.I * z * (Complex.exp (Complex.I * z * (L : ℂ)) - 1))
      (g := fun z : ℂ => ((2 * π * mode i / L : ℝ) : ℂ) ^ 2 - z ^ 2) hnum.continuousOn hdc.continuousOn (hden i)
  have hform : ∀ x : ι → ℝ, (∀ i, x (neg i) = x i) → ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode x)) z
        = ∑ i, (x i : ℂ) * g i z := by
    intro x hx z hz
    have hz0 : ∀ i, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ) + z ≠ 0 := by
      intro i hc; exact hz.2 (by simpa using congrArg Complex.im hc)
    rw [Cvs.Finite.SecularRealRooted.fourierLaplace_eq_S hL hinv hmode hx hz0]
    unfold Cvs.Finite.UniversalFunctionPairing.S
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg]
    ring
  have hsum := tendstoLocallyUniformlyOn_sum (s := Cvs.Limit.OffAxesLimit.offAxes)
    (fun k i => (xs k i : ℂ)) (fun i => (x0 i : ℂ))
    (fun i => (Complex.continuous_ofReal.tendsto _).comp (hconv i)) g hgc Finset.univ
  exact (hsum.congr fun k z hz => (hform (xs k) (hxs k) z hz).symm).congr_right
    fun z hz => (hform x0 hx0 z hz).symm

end Cvs.Finite.EvenGroundStateTools
