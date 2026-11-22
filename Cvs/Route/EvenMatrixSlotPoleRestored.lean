import Mathlib
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Finite.WindowedModeSumDomain
import Cvs.Limit.ModeSumsToMinimiser
import Cvs.Limit.TerminalApproximantsExist
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.StepAFromTwoGaps
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.FormBoundedBelowInfimum
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.MatrixPSDCriterion
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The matrix even slot, the form-density bridge, and the pole-restored minorant

Continuous even window positivity on `Ev x` is equivalent to even-sector positivity of the Fourier mode matrix `Cvs.Finite.TruncationQuadraticForm.M`
across all mode cutoffs `N`, and to the matrix even slot for the pole-restored minorant `A₁ + pole` (`M` minus the
digamma ladder).
-/

noncomputable section

open Matrix Real Filter Finset

namespace Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The even slot for matrices -/

/-- The bulk of `E` against `R`: vectors in `E` dot-orthogonal to `R`. -/
def Bulk (E R : Submodule ℝ (ι → ℝ)) (w : ι → ℝ) : Prop :=
  w ∈ E ∧ ∀ r ∈ R, r ⬝ᵥ w = 0

omit [Fintype ι] [DecidableEq ι] in
/-- `0 ≤ a + 2b + c` from `0 ≤ a`, `0 ≤ c`, and `b² ≤ ac`. -/
theorem add_two_mul_add_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : b ^ 2 ≤ a * c) :
    0 ≤ a + 2 * b + c := by
  by_contra hneg
  push Not at hneg
  have h1 : a + c < -2 * b := by linarith
  have h2 : 0 ≤ a + c := by linarith
  have h3 : (a + c) ^ 2 < (-2 * b) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (a - c)]

omit [DecidableEq ι] in
/-- Every vector of `E` decomposes as a vector of `R ≤ E` plus a bulk vector. -/
theorem exists_dec {E R : Submodule ℝ (ι → ℝ)} (hRE : R ≤ E) :
    ∀ ξ ∈ E, ∃ r ∈ R, ∃ w, Bulk E R w ∧ ξ = r + w := by
  classical
  let B : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toBilin' 1
  have hB : ∀ x y, B x y = x ⬝ᵥ y := fun x y => by simp [B, Matrix.toBilin'_apply']
  have hrefl : B.IsRefl := fun x y h => by rw [hB] at h ⊢; rwa [dotProduct_comm]
  have hdis : Disjoint R (B.orthogonal R) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hx') x hx
    rw [hB] at h0
    exact dotProduct_self_eq_zero.1 h0
  have hc := (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).2 hdis
  intro ξ hξ
  have hmem : ξ ∈ R ⊔ B.orthogonal R := by rw [hc.sup_eq_top]; trivial
  obtain ⟨r, hr, w, hw, hsum⟩ := Submodule.mem_sup.1 hmem
  refine ⟨r, hr, w, ⟨?_, fun r' hr' => ?_⟩, hsum.symm⟩
  · have : w = ξ - r := by rw [← hsum]; abel
    rw [this]; exact E.sub_mem hξ (hRE hr)
  · have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hw) r' hr'
    rwa [hB] at h0

omit [DecidableEq ι] in
/-- **The even slot for matrices**: a minorant `A ≤ Q` that is `≥ 0` on the bulk, and a channel
`(rᵀQw)² ≤ κ(r)·wᵀAw` with `0 ≤ κ(r) ≤ rᵀQr`, give `Q ≥ 0` on `E`. -/
theorem nonneg_of_slot {Q A : Matrix ι ι ℝ} (hQ : Q.IsSymm) {E R : Submodule ℝ (ι → ℝ)} (hRE : R ≤ E)
    {κ : (ι → ℝ) → ℝ}
    (hfloor : ∀ w, Bulk E R w → 0 ≤ w ⬝ᵥ (A *ᵥ w))
    (hcomp : ∀ w, Bulk E R w → w ⬝ᵥ (A *ᵥ w) ≤ w ⬝ᵥ (Q *ᵥ w))
    (hchan : ∀ r ∈ R, ∀ w, Bulk E R w → (r ⬝ᵥ (Q *ᵥ w)) ^ 2 ≤ κ r * w ⬝ᵥ (A *ᵥ w))
    (hκ0 : ∀ r ∈ R, 0 ≤ κ r) (hκ : ∀ r ∈ R, κ r ≤ r ⬝ᵥ (Q *ᵥ r)) :
    ∀ ξ ∈ E, 0 ≤ ξ ⬝ᵥ (Q *ᵥ ξ) := by
  intro ξ hξ
  obtain ⟨r, hr, w, hw, rfl⟩ := exists_dec hRE ξ hξ
  have hsym : w ⬝ᵥ (Q *ᵥ r) = r ⬝ᵥ (Q *ᵥ w) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ.eq, dotProduct_comm]
  have hexp : (r + w) ⬝ᵥ (Q *ᵥ (r + w))
      = r ⬝ᵥ (Q *ᵥ r) + 2 * (r ⬝ᵥ (Q *ᵥ w)) + w ⬝ᵥ (Q *ᵥ w) := by
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    rw [hsym]; ring
  have hA := hfloor w hw
  have hb : (r ⬝ᵥ (Q *ᵥ w)) ^ 2 ≤ (r ⬝ᵥ (Q *ᵥ r)) * (w ⬝ᵥ (A *ᵥ w)) :=
    (hchan r hr w hw).trans (mul_le_mul_of_nonneg_right (hκ r hr) hA)
  have := add_two_mul_add_nonneg ((hκ0 r hr).trans (hκ r hr)) hA hb
  rw [hexp]; linarith [hcomp w hw]

/-! ### Continuous-to-discrete form-density bridge -/

/-- Even mode vectors under an involution `neg : ι → ι`. -/
def evenModeSub {ι : Type*} (neg : ι → ι) : Submodule ℝ (ι → ℝ) where
  carrier := {ξ | ∀ i, ξ (neg i) = ξ i}
  add_mem' ha hb i := by simp [ha i, hb i]
  zero_mem' _ := rfl
  smul_mem' c _ ha i := by simp [ha i]

/-- **Form-density lower bound on `evenWindowSet L`**: if `0 ≤ ξ ⬝ᵥ (M P R L (mode N) *ᵥ ξ)` on
`evenModeSub (negI N)` for every `N : ℕ`, then `0 ≤ weilForm P R g` for every `g ∈ evenWindowSet L`. -/
theorem weilForm_evenWindowSet_nonneg_of_M_even_nonneg {L : ℝ} (hL : 0 < L) (P R : ℕ)
    (hM : ∀ N : ℕ, ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ))
    {g : ℝ → ℝ} (hg : g ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L) :
    0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g := by
  obtain ⟨lam, hlam⟩ := Cvs.WeilForm.FormBoundedBelowInfimum.exists_isGLB_even hL P R
  have hle : lam ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g := hlam.1 ⟨g, hg, rfl⟩
  have hlam0 : 0 ≤ lam := by
    by_contra hlt
    push Not at hlt
    obtain ⟨s, a, _, hclose⟩ := Cvs.Limit.TerminalApproximantsExist.exists_modeSum_close hL P R hlam (neg_pos.2 hlt)
    set N := s.sup id
    have hs : s ⊆ Finset.range (N + 1) := by
      intro n hn
      rw [Finset.mem_range]
      have : n ≤ s.sup id := Finset.le_sup (f := id) hn
      omega
    have heq := Cvs.Finite.SymmetricModeSet.windowMode_eq_modeSum L N s a hs
    have hform : Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.WindowedModeSumDomain.windowMode L s a)
        = L * (Cvs.Finite.SymmetricModeSet.coeff N s a ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ Cvs.Finite.SymmetricModeSet.coeff N s a)) := by
      rw [heq, Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N)
        (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) (Cvs.Finite.SymmetricModeSet.coeff_even N s a)]
      rfl
    have hnonneg : 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.WindowedModeSumDomain.windowMode L s a) := by
      rw [hform]
      exact mul_nonneg hL.le (hM N (Cvs.Finite.SymmetricModeSet.coeff N s a) (Cvs.Finite.SymmetricModeSet.coeff_even N s a))
    have hupper := (abs_lt.mp hclose).2
    linarith
  linarith

/-- **Continuous even form positivity from discrete even matrix positivity**: if `0 ≤ ξ ⬝ᵥ (M P R L (mode N) *ᵥ ξ)`
on `evenModeSub (negI N)` for all `N : ℕ`, then `0 ≤ Q hL.le P R η` for every `η ∈ evenSub hL.le`. -/
theorem Q_evenSub_nonneg_of_M_even_nonneg {L : ℝ} (hL : 0 < L) (P R : ℕ)
    (hM : ∀ N : ℕ, ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
      0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ))
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le} (hη : η ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL.le) :
    0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R η := by
  by_cases hη0 : η = 0
  · subst hη0
    show 0 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R ((0 : Cvs.WeilForm.FormDomain.formDomain hL.le) : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    rw [Submodule.coe_zero, Cvs.WeilForm.BottomAttained.weilQW_zero]
  · have hn : 0 < ‖η‖ := by simpa using hη0
    have hmem := Cvs.Limit.ModeSumsToMinimiser.normRep_mem_evenWindowSet hL.le η hη0 hη
    have hweil := weilForm_evenWindowSet_nonneg_of_M_even_nonneg hL P R hM hmem
    have hsm : Cvs.WeilForm.WindowRepresentative.rep ((1 / ‖η‖) • (η : Cvs.WeilForm.WeilFormOnWindowL2.window L)) =ᵐ[MeasureTheory.volume] Cvs.Limit.ModeSumsToMinimiser.normRep η :=
      Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae _ _
    have h1 := Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (P := P) (R := R)
      ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep ((1 / ‖η‖) • (η : Cvs.WeilForm.WeilFormOnWindowL2.window L))).trans hsm)
    change Cvs.WeilForm.WindowRepresentative.weilQW P R ((1 / ‖η‖) • (η : Cvs.WeilForm.WeilFormOnWindowL2.window L)) = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Limit.ModeSumsToMinimiser.normRep η) at h1
    rw [Cvs.WeilForm.BottomAttained.weilQW_smul] at h1
    have hpos : 0 < (1 / ‖η‖) ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_right (by linarith [h1, hweil]) hpos

/-- **Discrete even matrix positivity from continuous even form positivity**: if `0 ≤ Q hL.le P R η`
for all `η ∈ evenSub hL.le`, then `0 ≤ ξ ⬝ᵥ (M P R L (mode N) *ᵥ ξ)` for all `N` and `ξ ∈ evenModeSub (negI N)`. -/
theorem M_even_nonneg_of_Q_evenSub_nonneg {L : ℝ} (hL : 0 < L) (P R : ℕ)
    (hQ : ∀ η ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL.le, 0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R η)
    (N : ℕ) {ξ : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (hξ : ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N)) :
    0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) := by
  by_cases h0 : ξ = 0
  · subst h0; simp
  · obtain ⟨t, ht, htn⟩ := Cvs.Finite.DiscreteTwoGap.normalise hL h0
    have hmem := Cvs.Finite.ModeSumFormDomain.modeSum_mem_evenWindowSet hL (Cvs.Finite.SymmetricModeSet.mode_injective N)
      (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) (xi := t • ξ)
      (fun i => by simp [hξ i]) (by rw [Cvs.Finite.DiscreteTwoGap.dot_smul_self]; linarith)
    have hev : Cvs.Limit.ModeSumsToMinimiser.toDomain hL.le hmem.1 ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL.le :=
      Cvs.Limit.ModeSumsToMinimiser.reflD_toDomain hL.le hmem
    have h1 := hQ _ hev
    rw [Cvs.Limit.ModeSumsToMinimiser.Q_toDomain hL.le P R hmem.1, Cvs.WeilForm.MatrixPSDCriterion.modeSum_smul] at h1
    have h2 := Cvs.WeilForm.MatrixPSDCriterion.weilForm_nonneg_of_smul ht h1
    rw [Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N)
      (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) hξ] at h2
    exact nonneg_of_mul_nonneg_right h2 hL

/-- **Equivalence between continuous even form positivity on `evenSub hL.le` and discrete even-sector
positivity of `M P R L (mode N)` across `N : ℕ`.** -/
theorem Q_evenSub_nonneg_iff_M_even_nonneg {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    (∀ η ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL.le, 0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R η) ↔
      ∀ N : ℕ, ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
        0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) :=
  ⟨M_even_nonneg_of_Q_evenSub_nonneg hL P R, fun hM _ hη => Q_evenSub_nonneg_of_M_even_nonneg hL P R hM hη⟩

/-- **Equivalence at integer scale `x ≥ 2` between `∀ w ∈ Ev x, 0 ≤ Qx x w` and even-sector positivity
of `M x (Nat.clog 2 x) (log x) (mode N)` for all `N : ℕ`.** -/
theorem Qx_Ev_nonneg_iff_M_even_nonneg {x : ℕ} (hx : 2 ≤ x) :
    (∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, 0 ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x w) ↔
      ∀ N : ℕ, ∀ ξ ∈ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N),
        0 ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ ξ) := by
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  exact Q_evenSub_nonneg_iff_M_even_nonneg hL x (Nat.clog 2 x)

/-! ### Even-sector `kArch` sum of squares and the pole-restored minorant -/

omit [DecidableEq ι] in
/-- On `evenModeSub neg`, the odd Lorentzian factor `Cvs.Finite.WindowMatrixSymbolKernel.vv a` pairs to zero with `ξ`. -/
theorem sum_even_mul_vv_eq_zero (L a : ℝ)
    {mode : ι → ℤ} {neg : ι → ι} (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {ξ : ι → ℝ} (hξ : ξ ∈ evenModeSub neg) :
    ∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.vv a (2 * π * mode i / L) = 0 := by
  have hodd : ∀ i, Cvs.Finite.WindowMatrixSymbolKernel.vv a (2 * π * mode (neg i) / L) = -Cvs.Finite.WindowMatrixSymbolKernel.vv a (2 * π * mode i / L) := by
    intro i; simp only [Cvs.Finite.WindowMatrixSymbolKernel.vv, hmode i]; push_cast; ring
  have h0 := Cvs.Finite.DividedDifferenceCommutator.sum_odd_even
    (u := fun i => Cvs.Finite.WindowMatrixSymbolKernel.vv a (2 * π * mode i / L)) (v := ξ) hinv hodd (fun i => hξ i)
  rw [← h0]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Even-sector sum-of-squares identity for `Cvs.Finite.WindowMatrixSymbolKernel.kArch`**: on `evenModeSub neg`, the odd squares
vanish and `kArch` is the rank-one pole square plus the digamma ladder of Lorentzian squares. -/
theorem quadForm_kArch_even {L : ℝ} (hL : 0 < L)
    {mode : ι → ℤ} {neg : ι → ι} (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {ξ : ι → ℝ} (hξ : ξ ∈ evenModeSub neg) :
    ∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L)
      = 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2
        + ∑' k, 2 * (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L k) *
            (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) (2 * π * mode i / L)) ^ 2 := by
  rw [Cvs.Finite.WindowMatrixSymbolKernel.quadForm_kArch hL (fun i => 2 * π * mode i / L) ξ,
    sum_even_mul_vv_eq_zero L (1 / 2) hinv hmode hξ]
  have h00 : ((0 : ℝ)) ^ 2 = 0 := by norm_num
  rw [h00, sub_zero]
  congr 1
  refine tsum_congr fun k => ?_
  rw [sum_even_mul_vv_eq_zero L (Cvs.Finite.WindowMatrixSymbolKernel.bk k) hinv hmode hξ, h00, sub_zero]

/-- On `evenModeSub neg`, the digamma ladder sum in `kArch` is nonnegative, so `kArch` dominates
the rank-one pole square `2 * poleFactor L * (∑_i ξ_i uu (1/2) (ω_i))²`. -/
theorem quadForm_kArch_even_ge_pole {L : ℝ} (hL : 0 < L)
    {mode : ι → ℤ} {neg : ι → ι} (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {ξ : ι → ℝ} (hξ : ξ ∈ evenModeSub neg) :
    2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2
      ≤ ∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L) := by
  rw [quadForm_kArch_even hL hinv hmode hξ]
  have hlad : 0 ≤ ∑' k, 2 * (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L k) *
      (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (Cvs.Finite.WindowMatrixSymbolKernel.bk k) (2 * π * mode i / L)) ^ 2 := by
    refine tsum_nonneg fun k => ?_
    have htail : Cvs.Finite.DiagonalLevySymbol.tailFactor L k ≤ 1 := by
      unfold Cvs.Finite.DiagonalLevySymbol.tailFactor
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ (1 / 4 + (k : ℝ)) * (2 * L) := by positivity
      linarith
    have h1 : 0 ≤ 1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L k := by linarith
    positivity
  linarith

/-- The pole-free minorant matrix `A₁ = M − (1/L) K_arch`. -/
def A1Mat (P R : ℕ) (L : ℝ) (mode : ι → ℤ) : Matrix ι ι ℝ :=
  fun i j => Cvs.Finite.TruncationQuadraticForm.M P R L mode i j - 1 / L * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L)

/-- The quadratic form of `A1Mat` as a double sum. -/
theorem quad_A1Mat_eq_sum (P R : ℕ) (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) :
    ξ ⬝ᵥ (A1Mat P R L mode *ᵥ ξ) =
      ∑ i, ∑ j, ξ i * ξ j *
        (Cvs.Finite.TruncationQuadraticForm.M P R L mode i j - 1 / L * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L)) := by
  simp only [dotProduct, Matrix.mulVec, A1Mat, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- On even mode vectors, `A1Mat ≤ M`. -/
theorem A1Mat_le_M {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} {neg : ι → ι} (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {ξ : ι → ℝ} (hξ : ξ ∈ evenModeSub neg) :
    ξ ⬝ᵥ (A1Mat P R L mode *ᵥ ξ) ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ ξ) := by
  have hK := Cvs.Finite.WindowMatrixSymbolKernel.quadForm_kArch_nonneg hL (fun i => 2 * π * mode i / L) ξ
    (fun a _ => sum_even_mul_vv_eq_zero L a hinv hmode hξ)
  have hM : ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ ξ) = ∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.TruncationQuadraticForm.M P R L mode i j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [quad_A1Mat_eq_sum, hM]
  have hdiff : (∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.TruncationQuadraticForm.M P R L mode i j) -
      (∑ i, ∑ j, ξ i * ξ j * (Cvs.Finite.TruncationQuadraticForm.M P R L mode i j - 1 / L * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L)))
      = 1 / L * ∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hnonneg : 0 ≤ 1 / L * ∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L) :=
    mul_nonneg (by positivity) hK
  linarith

/-- **The pole-restored minorant matrix** `ApoleMat = A₁ + (2 poleFactor L / L) u_{1/2} u_{1/2}ᵀ`
(`M` minus the digamma ladder). -/
def ApoleMat (P R : ℕ) (L : ℝ) (mode : ι → ℤ) : Matrix ι ι ℝ :=
  fun i j => A1Mat P R L mode i j
    + (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L)
      * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L) * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode j / L)

/-- The quadratic form of `ApoleMat` is `ξ ⬝ᵥ (A1Mat *ᵥ ξ)` plus the rank-one pole square. -/
theorem quad_ApoleMat_eq (P R : ℕ) (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) :
    ξ ⬝ᵥ (ApoleMat P R L mode *ᵥ ξ) =
      ξ ⬝ᵥ (A1Mat P R L mode *ᵥ ξ)
        + 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2 := by
  have hpole : ∑ i, ∑ j, ξ i * ξ j *
      ((2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L)
        * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L) * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode j / L))
      = 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [quad_A1Mat_eq_sum, ← hpole, ← Finset.sum_add_distrib]
  simp only [dotProduct, Matrix.mulVec, ApoleMat, A1Mat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- **Pole-restored comparison**: on `evenModeSub neg`, `ApoleMat ≤ M` (dropping only the nonnegative
digamma ladder). -/
theorem ApoleMat_le_M {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {mode : ι → ℤ} {neg : ι → ι} (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {ξ : ι → ℝ} (hξ : ξ ∈ evenModeSub neg) :
    ξ ⬝ᵥ (ApoleMat P R L mode *ᵥ ξ) ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ ξ) := by
  rw [quad_ApoleMat_eq]
  have hM : ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ ξ) =
      ξ ⬝ᵥ (A1Mat P R L mode *ᵥ ξ) +
        1 / L * ∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L) := by
    rw [quad_A1Mat_eq_sum]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hpole : 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2
      ≤ 1 / L * ∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * mode i / L) (2 * π * mode j / L) := by
    have h := mul_le_mul_of_nonneg_left (quadForm_kArch_even_ge_pole hL hinv hmode hξ) (by positivity : (0 : ℝ) ≤ 1 / L)
    linarith [show 1 / L * (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2)
      = 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2 by ring]
  linarith

/-! ### The pole-restored matrix slot and its equivalence to RH -/

end Cvs.Route.EvenMatrixSlotPoleRestored
