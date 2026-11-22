import Mathlib
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# Link 3, closed: step (a) at a scale gives a zero-free transform for its minimiser

The normalised discrete minimisers form a minimising sequence, a subsequence converges in `L²` to
`±normRep η` (`Cvs.WeilForm.MinimisingSequenceConverges`), each term is zero-free off the axes (`Cvs.Finite.DisplacementIdentity`), and Hurwitz (`Cvs.Limit.OffAxesLimit`)
transfers it. Needs only `lam < aval 0`; the coefficient-sum condition is `Cvs.Finite.DisplacementIdentity`'s theorem.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix Filter Topology

namespace Cvs.Limit.StepAZeroFreeMinimiser

/-- The normalised discrete minimiser as a window function. -/
def Xi (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) : ℝ → ℝ :=
  Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (Cvs.Finite.SymmetricModeSet.mode N)
    ((Real.sqrt L)⁻¹ • Cvs.Finite.SymmetricModeSet.xiD P R L hL N)

theorem norm_coeff (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    L * (((Real.sqrt L)⁻¹ • Cvs.Finite.SymmetricModeSet.xiD P R L hL N)
      ⬝ᵥ ((Real.sqrt L)⁻¹ • Cvs.Finite.SymmetricModeSet.xiD P R L hL N)) = 1 := by
  rw [Cvs.Finite.DiscreteTwoGap.dot_smul_self, (Cvs.Finite.SymmetricModeSet.xiD_spec P R L hL N).1, mul_one,
    inv_pow, Real.sq_sqrt hL.le, mul_inv_cancel₀ hL.ne']

/-- **The normalised discrete minimiser lies in the even window set.** -/
theorem Xi_mem {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam mu : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (heven : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le η = η)
    (hiso : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le, (inner ℝ η v : ℝ) = 0 →
      mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (N : ℕ) (hlt : Cvs.Finite.SymmetricModeSet.lamD P R L hL N < mu) :
    Xi P R L hL N ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L := by
  have _ : lam = lam := rfl
  have hev := Cvs.Finite.DisplacementIdentity.xiD_even hL P R (lam := lam) heven hiso N hlt
  exact Cvs.Finite.ModeSumFormDomain.modeSum_mem_evenWindowSet hL (Cvs.Finite.SymmetricModeSet.mode_injective N)
    (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N)
    (fun i => by simp only [Pi.smul_apply, hev i]) (norm_coeff P R hL N)

/-- **Its form is the discrete bottom.** -/
theorem weilForm_Xi {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam mu : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (heven : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le η = η)
    (hiso : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le, (inner ℝ η v : ℝ) = 0 →
      mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (N : ℕ) (hlt : Cvs.Finite.SymmetricModeSet.lamD P R L hL N < mu) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Xi P R L hL N) = Cvs.Finite.SymmetricModeSet.lamD P R L hL N := by
  have _ : lam = lam := rfl
  have hev := Cvs.Finite.DisplacementIdentity.xiD_even hL P R (lam := lam) heven hiso N hlt
  obtain ⟨hxi1, -, hxi⟩ := Cvs.Finite.SymmetricModeSet.xiD_spec P R L hL N
  unfold Xi
  rw [Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix hL P R
    (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.SymmetricModeSet.mode_negI N) (fun i => by simp only [Pi.smul_apply, hev i])]
  change L * (((Real.sqrt L)⁻¹ • Cvs.Finite.SymmetricModeSet.xiD P R L hL N) ⬝ᵥ
    (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ
      ((Real.sqrt L)⁻¹ • Cvs.Finite.SymmetricModeSet.xiD P R L hL N))) = _
  rw [Cvs.Finite.DiscreteTwoGap.quad_smul, hxi, dotProduct_smul, smul_eq_mul, hxi1, mul_one, inv_pow,
    Real.sq_sqrt hL.le]
  field_simp

/-- The constant mode's diagonal entry does not depend on the order. -/
theorem M_none_none {L : ℝ} (hL : 0 < L) (P R : ℕ) (N : ℕ) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) none none
      = Cvs.Finite.PairFormDividedDifference.aval P R L 0 := by
  rw [Cvs.Finite.TruncationQuadraticForm.M_apply hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N)]
  rfl

/-- **The side conditions hold for all large orders** once the minimiser is not the constant. -/
theorem eventually_conditions {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    (hglb : IsGLB (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R '' Cvs.WeilForm.EvenBottomAttained.evenWindowSet L) lam)
    {mu : ℝ} (hmu : lam < mu) (hc : lam < Cvs.Finite.PairFormDividedDifference.aval P R L 0) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → Cvs.Finite.SymmetricModeSet.lamD P R L hL N < mu
      ∧ Cvs.Finite.SymmetricModeSet.lamD P R L hL N
        < Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) none none := by
  obtain ⟨N₀, hN₀⟩ := Cvs.Finite.SymmetricModeSet.lamD_lt_of_glb P R hL hglb
    (ε := min (mu - lam) (Cvs.Finite.PairFormDividedDifference.aval P R L 0 - lam))
    (lt_min (by linarith) (by linarith))
  refine ⟨N₀, fun N hN => ?_⟩
  have h := hN₀ N hN
  have h1 : min (mu - lam) (Cvs.Finite.PairFormDividedDifference.aval P R L 0 - lam) ≤ mu - lam := min_le_left _ _
  have h2 : min (mu - lam) (Cvs.Finite.PairFormDividedDifference.aval P R L 0 - lam)
      ≤ Cvs.Finite.PairFormDividedDifference.aval P R L 0 - lam := min_le_right _ _
  rw [M_none_none hL]
  constructor <;> linarith

end Cvs.Limit.StepAZeroFreeMinimiser
