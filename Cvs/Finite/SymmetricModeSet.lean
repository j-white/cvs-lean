import Mathlib
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowedModeSumDomain
import Cvs.Limit.TerminalApproximantsExist
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.WeilPositivityStatement

/-!
# The symmetric mode set of order `N`, and the discrete bottom against step (a)

`Idx N` indexes the modes `0, ±1, …, ±N`; window modes are mode sums on it; the discrete bottom
`lamD N` sits between the continuous bottom and any admissible even mode sum's form, so it
converges to `lam` from above.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix

namespace Cvs.Finite.SymmetricModeSet

/-! ### The index set -/

/-- The symmetric mode set: `none` is the zero mode, `some (k, b)` is `±(k+1)`. -/
abbrev Idx (N : ℕ) := Option (Fin N × Bool)

/-- The mode of an index. -/
def mode (N : ℕ) : Idx N → ℤ
  | none => 0
  | some (k, b) => if b then ((k : ℕ) : ℤ) + 1 else -(((k : ℕ) : ℤ) + 1)

/-- The involution: flip the sign. -/
def negI (N : ℕ) : Idx N → Idx N
  | none => none
  | some (k, b) => some (k, !b)

theorem negI_involutive (N : ℕ) : Function.Involutive (negI N) := by
  rintro (_ | ⟨k, b⟩)
  · rfl
  · simp [negI]

theorem mode_negI (N : ℕ) (i : Idx N) : mode N (negI N i) = -mode N i := by
  rcases i with _ | ⟨k, b⟩
  · simp [mode, negI]
  · cases b <;> simp [mode, negI]

theorem mode_injective (N : ℕ) : Function.Injective (mode N) := by
  rintro (_ | ⟨k, b⟩) (_ | ⟨k', b'⟩) h
  · rfl
  · exfalso
    simp only [mode] at h
    split_ifs at h <;> omega
  · exfalso
    simp only [mode] at h
    split_ifs at h <;> omega
  · simp only [mode] at h
    split_ifs at h with hb hb'
    · have hk : (k : ℕ) = k' := by omega
      rw [Fin.ext hk, hb, hb']
    · omega
    · omega
    · have hk : (k : ℕ) = k' := by omega
      rw [Fin.ext hk]
      cases b <;> cases b' <;> simp_all

instance (N : ℕ) : Nonempty (Idx N) := ⟨none⟩

/-! ### Window modes as mode sums -/

/-- The even coefficient vector carrying `windowMode L s a`. -/
def coeff (N : ℕ) (s : Finset ℕ) (a : ℕ → ℝ) : Idx N → ℝ
  | none => if 0 ∈ s then a 0 else 0
  | some (k, _) => if (k : ℕ) + 1 ∈ s then a ((k : ℕ) + 1) / 2 else 0

theorem coeff_even (N : ℕ) (s : Finset ℕ) (a : ℕ → ℝ) (i : Idx N) :
    coeff N s a (negI N i) = coeff N s a i := by
  rcases i with _ | ⟨k, b⟩ <;> rfl

/-- **A window mode on modes below `N + 1` is a mode sum on `Idx N`.** -/
theorem windowMode_eq_modeSum (L : ℝ) (N : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : s ⊆ Finset.range (N + 1)) :
    Cvs.Finite.WindowedModeSumDomain.windowMode L s a
      = Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) (coeff N s a) := by
  funext y
  simp only [Cvs.Finite.WindowedModeSumDomain.windowMode, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, Set.indicator_apply]
  split_ifs with hy
  · -- the mode sum over `Idx N`, split by the option and the sign
    rw [Fintype.sum_option, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    -- the window mode as a sum over `range (N+1)`
    have hext : Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a y
        = ∑ n ∈ Finset.range (N + 1), (if n ∈ s then a n else 0) * Real.cos (2 * π * n / L * y) := by
      unfold Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum
      rw [← Finset.sum_subset hs (fun n _ hn => by simp [hn])]
      refine Finset.sum_congr rfl fun n hn => ?_
      simp [hn]
    rw [hext, Finset.sum_range_succ', ← Fin.sum_univ_eq_sum_range
      (fun k => (if k + 1 ∈ s then a (k + 1) else 0) * Real.cos (2 * π * ((k + 1 : ℕ) : ℝ) / L * y)) N]
    simp only [coeff, mode, Cvs.Finite.TruncationZeroFreeOffAxes.omega, if_true, Bool.false_eq_true, if_false]
    push_cast
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 2 * π * -((k : ℝ) + 1) / L * y = -(2 * π * ((k : ℝ) + 1) / L * y) by ring, Real.cos_neg]
    split_ifs <;> ring
  · rfl

/-! ### The discrete bottom -/

/-- **The discrete bottom** on `Idx N`: the value produced by `Cvs.Upstream.SymmetricMatrixBottom.exists_bottom`. -/
def lamD (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) : ℝ :=
  Classical.choose (Cvs.Upstream.SymmetricMatrixBottom.exists_bottom
    (Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (mode_injective N)))

/-- **Its eigenvector.** -/
def xiD (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) : Idx N → ℝ :=
  Classical.choose (Classical.choose_spec (Cvs.Upstream.SymmetricMatrixBottom.exists_bottom
    (Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (mode_injective N))))

theorem xiD_spec (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) :
    xiD P R L hL N ⬝ᵥ xiD P R L hL N = 1
      ∧ (∀ v, lamD P R L hL N * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
      ∧ Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xiD P R L hL N = lamD P R L hL N • xiD P R L hL N :=
  Classical.choose_spec (Classical.choose_spec (Cvs.Upstream.SymmetricMatrixBottom.exists_bottom
    (Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (mode_injective N))))

/-- **The discrete bottom is at most the form of any normalised even mode sum on `Idx N`.** -/
theorem lamD_le_weilForm (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) {xi : Idx N → ℝ}
    (hxieven : ∀ i, xi (negI N i) = xi i) (hn : L * (xi ⬝ᵥ xi) = 1) :
    lamD P R L hL N ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) xi) := by
  have h := (xiD_spec P R L hL N).2.1 xi
  rw [Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix hL P R (mode_injective N)
    (negI_involutive N) (mode_negI N) hxieven]
  change _ ≤ L * (xi ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xi))
  calc lamD P R L hL N = lamD P R L hL N * (L * (xi ⬝ᵥ xi)) := by rw [hn, mul_one]
    _ = L * (lamD P R L hL N * (xi ⬝ᵥ xi)) := by ring
    _ ≤ L * (xi ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xi)) :=
        mul_le_mul_of_nonneg_left h hL.le

/-- **The continuous bottom is at most the discrete one**: the eigenvector's normalised mode sum
is an admissible even window function. -/
theorem lam_le_lamD (P R : ℕ) {L : ℝ} (hL : 0 < L) {lam : ℝ}
    (hbot : ∀ g ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L,
      lam ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g)
    (N : ℕ) (hxieven : ∀ i, xiD P R L hL N (negI N i) = xiD P R L hL N i) :
    lam ≤ lamD P R L hL N := by
  obtain ⟨hxi1, -, hxi⟩ := xiD_spec P R L hL N
  obtain ⟨t, ht0, ht⟩ := Cvs.Finite.DiscreteTwoGap.normalise hL (v := xiD P R L hL N)
    (fun h => by rw [h] at hxi1; simp at hxi1)
  set w : Idx N → ℝ := t • xiD P R L hL N with hw
  have hweven : ∀ i, w (negI N i) = w i := by
    intro i; simp only [hw, Pi.smul_apply, hxieven i]
  have hn : L * (w ⬝ᵥ w) = 1 := by rw [hw, Cvs.Finite.DiscreteTwoGap.dot_smul_self]; linarith [ht]
  have hmem := Cvs.Finite.ModeSumFormDomain.modeSum_mem_evenWindowSet hL (mode_injective N)
    (negI_involutive N) (mode_negI N) hweven hn
  have h1 := hbot _ hmem
  rw [Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix hL P R (mode_injective N)
    (negI_involutive N) (mode_negI N) hweven] at h1
  change lam ≤ L * (w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w)) at h1
  have heig : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w = lamD P R L hL N • w := by
    rw [hw, Matrix.mulVec_smul, hxi, smul_comm]
  rw [heig, dotProduct_smul, smul_eq_mul, ← mul_assoc, mul_comm L, mul_assoc, hn, mul_one] at h1
  exact h1

/-- **The discrete bottom converges to the continuous one from above**, along `N`. -/
theorem lamD_lt_of_glb (P R : ℕ) {L : ℝ} (hL : 0 < L) {lam : ℝ}
    (hlam : IsGLB (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R '' Cvs.WeilForm.EvenBottomAttained.evenWindowSet L) lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → lamD P R L hL N < lam + ε := by
  obtain ⟨s, a, hmem, hclose⟩ := Cvs.Limit.TerminalApproximantsExist.exists_modeSum_close hL P R hlam hε
  refine ⟨s.sup id, fun N hN => ?_⟩
  have hs : s ⊆ Finset.range (N + 1) := by
    intro n hn
    rw [Finset.mem_range]
    have : n ≤ s.sup id := Finset.le_sup (f := id) hn
    omega
  have heq := windowMode_eq_modeSum L N s a hs
  have hn : L * (coeff N s a ⬝ᵥ coeff N s a) = 1 := by
    have h := hmem.1.2.2.1
    rw [heq, ← Cvs.Finite.ModeSumFormDomain.selfConvolution_zero_eq,
      Cvs.Finite.PairFormDividedDifference.selfConvolution_modeSum_zero hL (mode_injective N) (negI_involutive N)
        (mode_negI N) (coeff_even N s a)] at h
    exact h
  have h1 := lamD_le_weilForm P R hL N (coeff_even N s a) hn
  rw [← heq] at h1
  have h2 := (abs_lt.mp hclose).2
  linarith

end Cvs.Finite.SymmetricModeSet
