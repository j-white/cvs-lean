import Mathlib
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.EvenBottomRealRoots
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SecularRealRooted
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Limit.DiscreteSpine
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The spine without the ordering: even-sector minimisers
The CvS matrix has a bottom on even vectors at every scale and mode count (`exists_even_bottom`, compactness of the
even unit sphere). If that bottom is simple within the even sector, the transform of its minimiser is zero-free off
the axes (`zeroFree_even`): the transform is `i z (e^{izL} − 1)·S(z²)` (`Cvs.Finite.SecularRealRooted`) and `Cvs.Finite.EvenBottomRealRoots` excludes non-real roots
of `S` in `z²`. Hence `riemannHypothesis_of_evenSector`: even-sector simplicity along a sequence of scales and
convergence of the even-sector transforms to `Ξ` give RH. No even/odd ordering, odd gap or positivity is assumed.
-/

noncomputable section

open Real Matrix Filter Topology

namespace Cvs.Finite.EvenMinimisers
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet

theorem negI_none (N : ℕ) : negI N none = none := rfl

/-- **An even-sector bottom exists** at every scale and mode count. -/
theorem exists_even_bottom {L : ℝ} (hL : 0 < L) (P R N : ℕ) :
    ∃ (lam : ℝ) (xi : Idx N → ℝ), (∀ i, xi (negI N i) = xi i) ∧ xi ⬝ᵥ xi = 1
      ∧ (∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) →
          lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
      ∧ Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xi = lam • xi := by
  set M := Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) with hM
  set E : Set (Idx N → ℝ) := {v | ∀ i, v (negI N i) = v i} with hE
  have hEclosed : IsClosed E := by
    have : E = ⋂ i, {v : Idx N → ℝ | v (negI N i) = v i} := by ext v; simp [hE]
    rw [this]
    exact isClosed_iInter fun i => isClosed_eq (continuous_apply _) (continuous_apply _)
  have hK : IsCompact (Cvs.Upstream.SymmetricMatrixBottom.sphere (Idx N) ∩ E) :=
    Cvs.Upstream.SymmetricMatrixBottom.isCompact_sphere.inter_right hEclosed
  have hne : (Cvs.Upstream.SymmetricMatrixBottom.sphere (Idx N) ∩ E).Nonempty := by
    refine ⟨Pi.single none 1, ?_, ?_⟩
    · show Pi.single none (1:ℝ) ⬝ᵥ Pi.single none 1 = 1
      simp
    · intro i
      rcases i with _ | ⟨k, b⟩
      · rfl
      · simp [negI]
  obtain ⟨xi, ⟨hxis, hxie⟩, hmin⟩ := hK.exists_isMinOn hne
    (by fun_prop : Continuous fun v : Idx N → ℝ => v ⬝ᵥ (M *ᵥ v)).continuousOn
  have hxi1 : xi ⬝ᵥ xi = 1 := hxis
  set lam := xi ⬝ᵥ (M *ᵥ xi) with hlam
  have hge : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) → lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v) := by
    intro v hv
    by_cases hv0 : v = 0
    · subst hv0; simp
    · have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' v)
        (fun h => hv0 (dotProduct_self_eq_zero.mp h.symm))
      set c : ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ with hc
      have hcc : c * c = (v ⬝ᵥ v)⁻¹ := by rw [hc, ← mul_inv, Real.mul_self_sqrt hpos.le]
      have hmem : c • v ∈ Cvs.Upstream.SymmetricMatrixBottom.sphere (Idx N) ∩ E := by
        refine ⟨?_, fun i => by simp [hv i]⟩
        show (c • v) ⬝ᵥ (c • v) = 1
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hcc,
          inv_mul_cancel₀ hpos.ne']
      have h : lam ≤ (c • v) ⬝ᵥ (M *ᵥ (c • v)) := hmin hmem
      rw [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hcc] at h
      calc lam * (v ⬝ᵥ v) ≤ (v ⬝ᵥ v)⁻¹ * (v ⬝ᵥ (M *ᵥ v)) * (v ⬝ᵥ v) :=
            mul_le_mul_of_nonneg_right h hpos.le
        _ = v ⬝ᵥ (M *ᵥ v) := by field_simp
  refine ⟨lam, xi, hxie, hxi1, hge, ?_⟩
  have hinj := mode_injective N
  have hsymm : ∀ i j, M i j = M j i := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj
  have hMneg : ∀ i j, M (negI N i) (negI N j) = M i j :=
    Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R hinj (mode_negI N)
  set A : Matrix (Idx N) (Idx N) ℝ := M - lam • (1 : Matrix (Idx N) (Idx N) ℝ) with hA
  have hAv : ∀ v : Idx N → ℝ, A *ᵥ v = M *ᵥ v - lam • v := by
    intro v; rw [hA, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hAq : ∀ v : Idx N → ℝ, v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (M *ᵥ v) - lam * (v ⬝ᵥ v) := by
    intro v; rw [hAv, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hAsymm : ∀ i j, A i j = A j i := by
    intro i j
    simp only [hA, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [hsymm i j]
    by_cases h : i = j
    · rw [h]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hAneg : ∀ i j, A (negI N i) (negI N j) = A i j := by
    intro i j
    simp only [hA, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hMneg]
    by_cases h : i = j
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (fun h' => h ((negI_involutive N).injective h')), if_neg h]
  have hApsd : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) → 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v hv; rw [hAq]; linarith [hge v hv]
  have h0 : xi ⬝ᵥ (A *ᵥ xi) = 0 := by rw [hAq, hxi1, mul_one, hlam, sub_self]
  have hk := Cvs.Finite.EvenBottomRealRoots.mulVec_eq_zero_of_even_psd hAsymm (negI_involutive N) hAneg hApsd hxie h0
  rw [hAv, sub_eq_zero] at hk
  exact hk

/-- **The even-sector minimiser's transform is zero-free off the axes**, given simplicity in the even sector. -/
theorem zeroFree_even {L : ℝ} (hL : 0 < L) (P R N : ℕ) {lam : ℝ} {xi : Idx N → ℝ}
    (hxieven : ∀ i, xi (negI N i) = xi i) (hxi0 : xi ≠ 0)
    (hmin : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) →
      lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
    (hxi : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xi = lam • xi)
    (hker : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) →
      Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v = lam • v → ∃ c : ℝ, v = c • xi) :
    ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
        (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) xi)) z ≠ 0 := by
  intro z hz hzero
  obtain ⟨hre, him⟩ := hz
  have hz0 : ∀ i, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i : ℝ) : ℂ) + z ≠ 0 := by
    intro i hc; exact him (by simpa using congrArg Complex.im hc)
  rw [Cvs.Finite.SecularRealRooted.fourierLaplace_eq_S hL (negI_involutive N) (mode_negI N) hxieven hz0] at hzero
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
  have hS : Cvs.Finite.UniversalFunctionPairing.S L (mode N) xi z = 0 := by
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
  have ha : ∀ i, Cvs.Finite.PairFormDividedDifference.aval P R L (mode N (negI N i))
      = Cvs.Finite.PairFormDividedDifference.aval P R L (mode N i) := by
    intro i
    unfold Cvs.Finite.PairFormDividedDifference.aval
    rw [mode_negI, Cvs.Finite.TruncationQuadraticForm.pairQ_neg_neg]
  have hb : ∀ i, Cvs.Finite.PairFormDividedDifference.bval P R L (mode N (negI N i))
      = -Cvs.Finite.PairFormDividedDifference.bval P R L (mode N i) := by
    intro i; rw [mode_negI, Cvs.Finite.PairFormDividedDifference.bval_neg]
  have hsec := Cvs.Finite.EvenBottomRealRoots.secular_ne_zero
    (a := fun k => Cvs.Finite.PairFormDividedDifference.aval P R L (mode N k))
    (b := fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (mode N k))
    (ω := Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N))
    (Cvs.Finite.DisplacementIdentity.omega_injective hL (mode_injective N)) (negI_involutive N)
    (Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg (mode_negI N)) hb ha hxieven hxi0 hmin hxi hker hw
  apply hsec
  rw [← hS]
  unfold Cvs.Finite.UniversalFunctionPairing.S
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]
  push_cast
  rfl

/-- The even-sector bottom and its minimiser at a scale. -/
def evLam (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) : ℝ := Classical.choose (exists_even_bottom hL P R N)
def evMin (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) : Idx N → ℝ :=
  Classical.choose (Classical.choose_spec (exists_even_bottom hL P R N))

theorem evMin_spec (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (∀ i, evMin P R L hL N (negI N i) = evMin P R L hL N i) ∧ evMin P R L hL N ⬝ᵥ evMin P R L hL N = 1
      ∧ (∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) →
          evLam P R L hL N * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
      ∧ Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ evMin P R L hL N = evLam P R L hL N • evMin P R L hL N :=
  Classical.choose_spec (Classical.choose_spec (exists_even_bottom hL P R N))

/-- **Even-sector simplicity** at a scale: the even eigenvectors at the even bottom form a line. -/
def EvenSimple (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) : Prop :=
  ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) →
    Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v = evLam P R L hL N • v → ∃ c : ℝ, v = c • evMin P R L hL N

/-- The transform of the even-sector minimiser. -/
def etransform (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) : ℂ → ℂ :=
  FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
    (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) (evMin P R L hL N)))

theorem etransform_ne_zero {P R : ℕ} {L : ℝ} (hL : 0 < L) {N : ℕ} (h : EvenSimple P R L hL N) :
    ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, etransform P R hL N z ≠ 0 := by
  obtain ⟨hev, hn, hmin, hxi⟩ := evMin_spec P R hL N
  have hne : evMin P R L hL N ≠ 0 := by
    intro h0; rw [h0] at hn; simp at hn
  exact zeroFree_even hL P R N hev hne hmin hxi h

/-- **The spine without the ordering.** Even-sector simplicity at every scale of a sequence, and a nonzero rescaling
of the even-sector transforms converging locally uniformly to `Ξ`, give RH. -/
theorem riemannHypothesis_of_evenSector {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ)
    (hsimple : ∀ n, EvenSimple (P n) (R n) (L n) (hL n) (N n))
    (hB : ∃ c : ℕ → ℂ, (∀ n, c n ≠ 0) ∧
      TendstoLocallyUniformlyOn (fun n z => c n * etransform (P n) (R n) (hL n) (N n) z)
        Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop (Set.univ : Set ℂ)) :
    RiemannHypothesis := by
  obtain ⟨c, hc, hconv⟩ := hB
  refine Cvs.Limit.ZeroFreeApproximantsRH.riemannHypothesis_of_convergence'
    (fun n z => c n * etransform (P n) (R n) (hL n) (N n) z) (fun n => ?_) (fun n z hz => ?_) hconv
  · exact (differentiable_const (c n)).mul (Cvs.Limit.DiscreteSpine.differentiable_modeSum (hL n) _ _)
  · exact mul_ne_zero (hc n) (etransform_ne_zero (hL n) (hsimple n) z hz)

end Cvs.Finite.EvenMinimisers
