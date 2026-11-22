import Mathlib
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EvenGroundStateTools
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.DiscreteSpine
import Cvs.Limit.LimitSeesXiZeros
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.Hurwitz
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The RH spine without simplicity
`exists_zeroFree_even_ground`: at every scale the CvS matrix has a unit even bottom eigenvector with transform
zero-free off the axes, simplicity not assumed: dropping the diagonal on a reflection pair makes the bottom simple
(`Cvs.Finite.EvenGroundStateTools`), and a compactness limit with Hurwitz returns to the unperturbed matrix. `riemannHypothesis_of_ground`: RH
from step (b) alone; `ground_eq_of_evenSimple`: in the simple case the ground state is `± evMin` (`Cvs.Finite.EvenMinimisers`'s spine).
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Matrix Filter Topology

namespace Cvs.Limit.SpineWithoutSimplicity
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet

/-- The indicator of the reflection pair of `i0`. -/
def pairInd (N : ℕ) (i0 : Idx N) : Idx N → ℝ := fun i => if i = i0 ∨ i = negI N i0 then 1 else 0

theorem pairInd_neg (N : ℕ) (i0 i : Idx N) : pairInd N i0 (negI N i) = pairInd N i0 i := by
  have hinv := negI_involutive N
  have hiff : (negI N i = i0 ∨ negI N i = negI N i0) ↔ (i = i0 ∨ i = negI N i0) := by
    constructor
    · rintro (h | h)
      · right; rw [← h, hinv i]
      · left; exact hinv.injective h
    · rintro (h | h)
      · right; rw [h]
      · left; rw [h, hinv i0]
  unfold pairInd
  by_cases h : i = i0 ∨ i = negI N i0
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-- **A zero-free even ground state exists at every scale**, without simplicity. -/
theorem exists_zeroFree_even_ground {L : ℝ} (hL : 0 < L) (P R N : ℕ) :
    ∃ (lam : ℝ) (xi : Idx N → ℝ), (∀ i, xi (negI N i) = xi i) ∧ xi ⬝ᵥ xi = 1
      ∧ (∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) →
          lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
      ∧ Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xi = lam • xi
      ∧ ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, FourierLaplace.fourierLaplace
          (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) xi)) z ≠ 0 := by
  set M := Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) with hM
  have hinv := negI_involutive N
  have hinj := mode_injective N
  have hsymm : ∀ i j, M i j = M j i := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj
  have hMneg : ∀ i j, M (negI N i) (negI N j) = M i j :=
    Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R hinj (mode_negI N)
  obtain ⟨lam0, xi0, hxi0e, hxi01, hmin0, hxi0⟩ := Cvs.Finite.EvenMinimisers.exists_even_bottom hL P R N
  have hxi0ne : xi0 ≠ 0 := by intro h; rw [h] at hxi01; simp at hxi01
  obtain ⟨i0, hi0⟩ : ∃ i0, xi0 i0 ≠ 0 := by
    by_contra h
    exact hxi0ne (funext fun i => by by_contra hi; exact h ⟨i, hi⟩)
  -- the perturbations
  set eps : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with heps
  have heps_pos : ∀ k, 0 < eps k := fun k => by simp only [heps]; positivity
  set d : ℕ → Idx N → ℝ := fun k => eps k • pairInd N i0 with hd
  have hdneg : ∀ k i, d k (negI N i) = d k i := by
    intro k i; simp only [hd, Pi.smul_apply, smul_eq_mul, pairInd_neg]
  set A : ℕ → Matrix (Idx N) (Idx N) ℝ := fun k => M - Matrix.diagonal (d k) with hA
  have hAsymm : ∀ k i j, A k i j = A k j i := by
    intro k i j
    simp only [hA, Matrix.sub_apply, Matrix.diagonal_apply]
    rw [hsymm i j]
    by_cases h : i = j
    · rw [h]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hAneg : ∀ k i j, A k (negI N i) (negI N j) = A k i j := by
    intro k i j
    simp only [hA, Matrix.sub_apply, Matrix.diagonal_apply]
    rw [hMneg]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_pos rfl, hdneg]
    · rw [if_neg (fun h' => h (hinv.injective h')), if_neg h]
  have hex : ∀ k, ∃ (mu : ℝ) (eta : Idx N → ℝ), (∀ i, eta (negI N i) = eta i) ∧ eta ⬝ᵥ eta = 1
      ∧ (∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) → mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A k *ᵥ v))
      ∧ A k *ᵥ eta = mu • eta :=
    fun k => Cvs.Finite.EvenGroundStateTools.exists_even_min (hAsymm k) hinv (hAneg k) hxi0e hxi01
  choose mu eta hetae heta1 hetamin heta using hex
  have hetane : ∀ k, eta k ≠ 0 := by
    intro k h; have h1 := heta1 k; rw [h] at h1; simp at h1
  have hquad : ∀ k (v : Idx N → ℝ),
      v ⬝ᵥ (A k *ᵥ v) = v ⬝ᵥ (M *ᵥ v) - eps k * ∑ i, pairInd N i0 i * v i ^ 2 := by
    intro k v
    simp only [hA]
    rw [Cvs.Finite.EvenGroundStateTools.quad_sub_diagonal, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hd, Pi.smul_apply, smul_eq_mul]; ring
  have hpairpos : 0 < ∑ i, pairInd N i0 i * xi0 i ^ 2 := by
    have hnn : ∀ i, 0 ≤ pairInd N i0 i * xi0 i ^ 2 := fun i =>
      mul_nonneg (by unfold pairInd; split_ifs <;> norm_num) (sq_nonneg _)
    have hle : pairInd N i0 i0 * xi0 i0 ^ 2 ≤ ∑ i, pairInd N i0 i * xi0 i ^ 2 :=
      Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i0)
    have h1 : pairInd N i0 i0 = 1 := by simp [pairInd]
    rw [h1, one_mul] at hle
    have h2 : 0 < xi0 i0 ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (fun h => hi0 ((pow_eq_zero_iff two_ne_zero).mp h.symm))
    linarith
  have hmu_lt : ∀ k, mu k < lam0 := by
    intro k
    have h1 := hetamin k xi0 hxi0e
    rw [hxi01, mul_one, hquad k xi0] at h1
    have h2 : xi0 ⬝ᵥ (M *ᵥ xi0) = lam0 := by rw [hxi0, dotProduct_smul, smul_eq_mul, hxi01, mul_one]
    rw [h2] at h1
    linarith [mul_pos (heps_pos k) hpairpos]
  have hsimple : ∀ k, ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) → A k *ᵥ v = mu k • v →
      ∃ c : ℝ, v = c • eta k := by
    intro k
    refine Cvs.Finite.EvenGroundStateTools.evenSimple_of_drop (A := M) (d := d k) (i0 := i0)
      (fun i hdi => ?_) hmin0 (hmu_lt k) (hetae k) (hetane k) (heta k)
    by_contra hc
    apply hdi
    simp only [hd, Pi.smul_apply, smul_eq_mul, pairInd, if_neg hc, mul_zero]
  have haval : ∀ i, Cvs.Finite.PairFormDividedDifference.aval P R L (mode N (negI N i))
      = Cvs.Finite.PairFormDividedDifference.aval P R L (mode N i) := by
    intro i
    unfold Cvs.Finite.PairFormDividedDifference.aval
    rw [mode_negI, Cvs.Finite.TruncationQuadraticForm.pairQ_neg_neg]
  have hbval : ∀ i, Cvs.Finite.PairFormDividedDifference.bval P R L (mode N (negI N i))
      = -Cvs.Finite.PairFormDividedDifference.bval P R L (mode N i) := by
    intro i; rw [mode_negI, Cvs.Finite.PairFormDividedDifference.bval_neg]
  have hzf : ∀ k, ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, FourierLaplace.fourierLaplace
      (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) (eta k))) z ≠ 0 := by
    intro k
    have hAk : A k = Cvs.Finite.DividedDifferenceCommutator.ddMatrix
        ((fun i => Cvs.Finite.PairFormDividedDifference.aval P R L (mode N i)) - d k)
        (fun i => Cvs.Finite.PairFormDividedDifference.bval P R L (mode N i)) (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N)) := by
      rw [Cvs.Finite.EvenGroundStateTools.ddMatrix_sub_diag]; rfl
    refine Cvs.Finite.EvenGroundStateTools.zeroFree_of_ddMatrix
      (a := (fun i => Cvs.Finite.PairFormDividedDifference.aval P R L (mode N i)) - d k)
      (b := fun i => Cvs.Finite.PairFormDividedDifference.bval P R L (mode N i)) (lam := mu k)
      hL hinj hinv (mode_negI N) (fun i => ?_) hbval (hetae k) (hetane k) ?_ ?_ ?_
    · simp only [Pi.sub_apply]; rw [haval i, hdneg k i]
    · rw [← hAk]; exact hetamin k
    · rw [← hAk]; exact heta k
    · rw [← hAk]; exact hsimple k
  -- the limit
  set E : Set (Idx N → ℝ) := {v | ∀ i, v (negI N i) = v i} with hE
  have hEclosed : IsClosed E := by
    have : E = ⋂ i, {v : Idx N → ℝ | v (negI N i) = v i} := by ext v; simp [hE]
    rw [this]
    exact isClosed_iInter fun i => isClosed_eq (continuous_apply _) (continuous_apply _)
  have hK : IsCompact (Cvs.Upstream.SymmetricMatrixBottom.sphere (Idx N) ∩ E) :=
    Cvs.Upstream.SymmetricMatrixBottom.isCompact_sphere.inter_right hEclosed
  obtain ⟨xs, ⟨hxs1, hxse⟩, φ, hφ, hlim⟩ :=
    hK.tendsto_subseq (x := eta) (fun k => ⟨heta1 k, hetae k⟩)
  have hxs1' : xs ⬝ᵥ xs = 1 := hxs1
  have hcoord : ∀ i, Tendsto (fun k => eta (φ k) i) atTop (𝓝 (xs i)) :=
    fun i => ((continuous_apply i).tendsto xs).comp hlim
  have heps_lim : Tendsto (fun k => eps (φ k)) atTop (𝓝 0) := by
    have h0 : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    exact h0.comp hφ.tendsto_atTop
  set lam := xs ⬝ᵥ (M *ᵥ xs) with hlam
  have hminlim : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) → lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v) := by
    intro v hv
    have hmuk : ∀ k, mu k = eta k ⬝ᵥ (A k *ᵥ eta k) := by
      intro k; rw [heta k, dotProduct_smul, smul_eq_mul, heta1 k, mul_one]
    have hleft : Tendsto (fun k => mu (φ k) * (v ⬝ᵥ v)) atTop (𝓝 (lam * (v ⬝ᵥ v))) := by
      have hq : Tendsto (fun k => eta (φ k) ⬝ᵥ (M *ᵥ eta (φ k))) atTop (𝓝 lam) :=
        ((by fun_prop : Continuous fun x : Idx N → ℝ => x ⬝ᵥ (M *ᵥ x)).tendsto xs).comp hlim
      have hp : Tendsto (fun k => ∑ i, pairInd N i0 i * eta (φ k) i ^ 2) atTop
          (𝓝 (∑ i, pairInd N i0 i * xs i ^ 2)) :=
        ((by fun_prop : Continuous fun x : Idx N → ℝ => ∑ i, pairInd N i0 i * x i ^ 2).tendsto xs).comp hlim
      have h := (hq.sub (heps_lim.mul hp)).mul_const (v ⬝ᵥ v)
      rw [zero_mul, sub_zero] at h
      have e : (fun k => mu (φ k) * (v ⬝ᵥ v)) = fun k =>
          (eta (φ k) ⬝ᵥ (M *ᵥ eta (φ k)) - eps (φ k) * ∑ i, pairInd N i0 i * eta (φ k) i ^ 2) * (v ⬝ᵥ v) :=
        funext fun k => by rw [hmuk, hquad]
      rw [e]; exact h
    have hright : Tendsto (fun k => v ⬝ᵥ (A (φ k) *ᵥ v)) atTop (𝓝 (v ⬝ᵥ (M *ᵥ v))) := by
      have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => v ⬝ᵥ (M *ᵥ v)) atTop _).sub
        (heps_lim.mul (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => ∑ i, pairInd N i0 i * v i ^ 2) atTop _))
      rw [zero_mul, sub_zero] at h
      have e : (fun k => v ⬝ᵥ (A (φ k) *ᵥ v)) = fun k =>
          v ⬝ᵥ (M *ᵥ v) - eps (φ k) * ∑ i, pairInd N i0 i * v i ^ 2 :=
        funext fun k => hquad _ _
      rw [e]; exact h
    exact le_of_tendsto_of_tendsto' hleft hright fun k => hetamin (φ k) v hv
  have hxs_eig : M *ᵥ xs = lam • xs :=
    Cvs.Finite.EvenGroundStateTools.eigen_of_even_min hsymm hinv hMneg hxse hminlim (by rw [hxs1', mul_one])
  have hxsne : xs ≠ 0 := by intro h; rw [h] at hxs1'; simp at hxs1'
  have hconvT := Cvs.Finite.EvenGroundStateTools.tendstoLocallyUniformlyOn_transform hL hinv (mode_negI N)
    (fun k => eta (φ k)) xs (fun k => hetae (φ k)) hxse hcoord
  refine ⟨lam, xs, hxse, hxs1', hminlim, hxs_eig, fun z hz => ?_⟩
  exact Cvs.Upstream.Hurwitz.ne_zero_of_zeroFree_of_tendstoLocallyUniformlyOn
    (F := fun k => FourierLaplace.fourierLaplace
      (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) (eta (φ k)))))
    Cvs.Limit.OffAxesLimit.isOpen_offAxes hz
    (fun k => (Cvs.Limit.DiscreteSpine.differentiable_modeSum hL (mode N) (eta (φ k))).differentiableOn)
    (fun k => hzf (φ k)) hconvT
    (Cvs.Finite.EvenGroundStateTools.transform_not_eventually_zero hL hinj hinv (mode_negI N) hxse hxsne z)

/-- The level of the chosen ground state. -/
def groundLam (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) : ℝ :=
  Classical.choose (exists_zeroFree_even_ground hL P R N)

/-- The chosen zero-free even ground state. -/
def ground (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) : Idx N → ℝ :=
  Classical.choose (Classical.choose_spec (exists_zeroFree_even_ground hL P R N))

theorem ground_spec (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (∀ i, ground P R L hL N (negI N i) = ground P R L hL N i) ∧ ground P R L hL N ⬝ᵥ ground P R L hL N = 1
      ∧ (∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) →
          groundLam P R L hL N * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
      ∧ Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ ground P R L hL N = groundLam P R L hL N • ground P R L hL N
      ∧ ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, FourierLaplace.fourierLaplace
          (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) (ground P R L hL N))) z ≠ 0 :=
  Classical.choose_spec (Classical.choose_spec (exists_zeroFree_even_ground hL P R N))

/-- The transform of the ground state. -/
def gtransform (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) : ℂ → ℂ :=
  FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
    (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) (ground P R L hL N)))

/-- **The RH spine on step (b) alone**, in the weak form: rescaled ground-state transforms converging locally
uniformly to a nonzero entire limit that vanishes at the off-axis zeros of `Ξ`. -/
theorem riemannHypothesis_of_ground {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ)
    (c : ℕ → ℂ) (hc : ∀ n, c n ≠ 0) (f : ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * gtransform (P n) (R n) (hL n) (N n) z) f atTop Set.univ)
    (hf0 : ∃ z₀, f z₀ ≠ 0)
    (hsees : ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, Cvs.Limit.ZeroFreeApproximantsRH.Xi z = 0 → f z = 0) :
    RiemannHypothesis :=
  Cvs.Limit.LimitSeesXiZeros.riemannHypothesis_of_limit _ f
    (fun n => (differentiable_const (c n)).mul (Cvs.Limit.DiscreteSpine.differentiable_modeSum (hL n) _ _))
    (fun n z hz => mul_ne_zero (hc n) ((ground_spec (P n) (R n) (hL n) (N n)).2.2.2.2 z hz))
    hconv hf0 hsees

/-- **The RH spine on step (b) alone**, with the limit `Ξ`. -/
theorem riemannHypothesis_of_ground_Xi {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ)
    (c : ℕ → ℂ) (hc : ∀ n, c n ≠ 0)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * gtransform (P n) (R n) (hL n) (N n) z) Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop Set.univ) :
    RiemannHypothesis :=
  riemannHypothesis_of_ground hL P R N c hc _ hconv ⟨_, Cvs.Limit.ZeroFreeApproximantsRH.Xi_half_I_ne_zero⟩
    (fun _ _ h => h)

/-- **In the simple case the ground state is `± evMin`.** -/
theorem ground_eq_of_evenSimple {P R : ℕ} {L : ℝ} (hL : 0 < L) {N : ℕ}
    (h : Cvs.Finite.EvenMinimisers.EvenSimple P R L hL N) :
    ground P R L hL N = Cvs.Finite.EvenMinimisers.evMin P R L hL N
      ∨ ground P R L hL N = -Cvs.Finite.EvenMinimisers.evMin P R L hL N := by
  obtain ⟨hge, hg1, hgmin, hgeig, _⟩ := ground_spec P R hL N
  obtain ⟨hee, he1, hemin, heeig⟩ := Cvs.Finite.EvenMinimisers.evMin_spec P R hL N
  have hlev : groundLam P R L hL N = Cvs.Finite.EvenMinimisers.evLam P R L hL N := by
    have h1 := hgmin _ hee
    have h2 := hemin _ hge
    rw [he1, mul_one, heeig, dotProduct_smul, smul_eq_mul, he1, mul_one] at h1
    rw [hg1, mul_one, hgeig, dotProduct_smul, smul_eq_mul, hg1, mul_one] at h2
    linarith
  rw [hlev] at hgeig
  obtain ⟨c, hc⟩ := h _ hge hgeig
  have hc2 : c * c = 1 := by
    have h1 := hg1
    rw [hc, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, he1, mul_one] at h1
    exact h1
  rcases mul_self_eq_one_iff.mp hc2 with h1 | h1
  · left; rw [hc, h1, one_smul]
  · right; rw [hc, h1, neg_one_smul]

end Cvs.Limit.SpineWithoutSimplicity
