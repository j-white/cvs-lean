import Mathlib
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# Link 3, assembled at one mode order

For any order `N` whose discrete bottom lies below the isolation level and below the constant
mode's diagonal entry, and whose eigenvector has nonzero coefficient sum, `Cvs.Finite.TruncationZeroFreeOffAxes.zeroFree_offAxes`
applies to the discrete minimiser's cosine sum.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix

namespace Cvs.Finite.DisplacementIdentity

/-- The Fourier–Laplace transform scales with the function. -/
theorem fourierLaplace_cf_const_mul (c : ℝ) (f : ℝ → ℝ) (z : ℂ) :
    FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (fun x => c * f x)) z
      = (c : ℂ) * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z := by
  rw [FourierLaplace.fourierLaplace, FourierLaplace.fourierLaplace, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show ((c * f t : ℝ) : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))
    = (c : ℂ) * (((f t : ℝ) : ℂ) * Complex.exp (Complex.I * z * (t : ℂ)))
  push_cast
  ring

/-- The frequencies of an injective mode map are injective. -/
theorem omega_injective {ι : Type*} {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) : Function.Injective (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) := by
  intro i j h
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega] at h
  have hc : (2 * π / L) ≠ 0 := by positivity
  have h2 : (mode i : ℝ) = mode j := by
    apply mul_left_cancel₀ hc
    calc 2 * π / L * (mode i : ℝ) = 2 * π * (mode i) / L := by ring
      _ = 2 * π * (mode j) / L := h
      _ = 2 * π / L * (mode j : ℝ) := by ring
  exact hinj (by exact_mod_cast h2)

/-- **The discrete eigenvector is not carried by the zero mode alone**, once its bottom lies below
the constant mode's diagonal entry. -/
theorem xiD_ne {L : ℝ} (hL : 0 < L) (P R : ℕ) (N : ℕ)
    (hconst : Cvs.Finite.SymmetricModeSet.lamD P R L hL N
      < Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) none none) :
    ∃ j, Cvs.Finite.SymmetricModeSet.xiD P R L hL N j
      * Cvs.Finite.TruncationZeroFreeOffAxes.omega L (Cvs.Finite.SymmetricModeSet.mode N) j ≠ 0 := by
  obtain ⟨hxi1, -, hxi⟩ := Cvs.Finite.SymmetricModeSet.xiD_spec P R L hL N
  set M := Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) with hM
  set xi := Cvs.Finite.SymmetricModeSet.xiD P R L hL N with hxidef
  set lamD := Cvs.Finite.SymmetricModeSet.lamD P R L hL N with hlamD
  have hinj := Cvs.Finite.SymmetricModeSet.mode_injective N
  by_contra hall
  push Not at hall
  have hoff : ∀ j, j ≠ none → xi j = 0 := by
    intro j hj
    have hω : Cvs.Finite.TruncationZeroFreeOffAxes.omega L (Cvs.Finite.SymmetricModeSet.mode N) j ≠ 0 := by
      have hm : Cvs.Finite.SymmetricModeSet.mode N j ≠ 0 := fun h => hj (hinj h)
      have hm' : (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) ≠ 0 := by exact_mod_cast hm
      simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hm') hL.ne'
    exact (mul_eq_zero.mp (hall j)).resolve_right hω
  have hxi_eq : xi = xi none • Pi.single none (1:ℝ) := by
    funext j
    by_cases hj : j = none
    · subst hj; simp
    · rw [hoff j hj]; simp [hj]
  have h1 : xi ⬝ᵥ (M *ᵥ xi) = lamD := by
    rw [hxi, dotProduct_smul, smul_eq_mul, hxi1, mul_one]
  have hsingle : Pi.single none (1:ℝ) ⬝ᵥ (M *ᵥ Pi.single none (1:ℝ)) = M none none := by
    rw [single_dotProduct, one_mul]
    simp only [Matrix.mulVec, dotProduct_single, mul_one]
  have h2 : xi ⬝ᵥ (M *ᵥ xi) = xi none ^ 2 * M none none := by
    conv_lhs => rw [hxi_eq]
    rw [Cvs.Finite.DiscreteTwoGap.quad_smul, hsingle]
  have h3 : xi none ^ 2 = 1 := by
    have := hxi1
    rw [hxi_eq, Cvs.Finite.DiscreteTwoGap.dot_smul_self, single_dotProduct, one_mul,
      Pi.single_eq_same, mul_one] at this
    exact this
  rw [h2, h3, one_mul] at h1
  linarith

/-- **The discrete eigenvector is even** once its bottom lies below the isolation level. -/
theorem xiD_even {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam mu : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (heven : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le η = η)
    (hiso : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le, (inner ℝ η v : ℝ) = 0 →
      mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (N : ℕ) (hlt : Cvs.Finite.SymmetricModeSet.lamD P R L hL N < mu) :
    ∀ i, Cvs.Finite.SymmetricModeSet.xiD P R L hL N (Cvs.Finite.SymmetricModeSet.negI N i)
      = Cvs.Finite.SymmetricModeSet.xiD P R L hL N i := by
  have _hlam : lam = lam := rfl
  obtain ⟨hxi1, hge, hxi⟩ := Cvs.Finite.SymmetricModeSet.xiD_spec P R L hL N
  have hinj := Cvs.Finite.SymmetricModeSet.mode_injective N
  have hinv := Cvs.Finite.SymmetricModeSet.negI_involutive N
  have hmode := Cvs.Finite.SymmetricModeSet.mode_negI N
  have hsymm := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj
  have hA := Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R hinj hmode
  have hgap : ∀ o : Cvs.Finite.SymmetricModeSet.Idx N → ℝ,
      (∀ i, o (Cvs.Finite.SymmetricModeSet.negI N i) = -o i) → o ≠ 0 →
      Cvs.Finite.SymmetricModeSet.lamD P R L hL N * (o ⬝ᵥ o)
        < o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ o) := by
    intro o hodd hne
    have h1 := Cvs.Finite.DiscreteTwoGap.odd_gap_of_stepA hL P R (lam := lam) heven hiso hinj hinv
      hmode hodd
    have hpos : 0 < o ⬝ᵥ o := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
      (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
    calc Cvs.Finite.SymmetricModeSet.lamD P R L hL N * (o ⬝ᵥ o) < mu * (o ⬝ᵥ o) :=
          mul_lt_mul_of_pos_right hlt hpos
      _ ≤ _ := h1
  have ho := Cvs.Upstream.SymmetricMatrixBottom.oddPart_eq_zero_of_gap hsymm hinv hA hge hgap hxi
  intro i
  have := congrFun ho i
  simp only [Cvs.Finite.TruncationQuadraticForm.oddPart, Pi.zero_apply] at this
  linarith

/-! ### The displacement identity -/

/-- **`diag(pos) · A − A · diag(pos) = b 𝟙ᵀ − 𝟙 bᵀ`** for the divided-difference matrix, applied to
a vector. -/
theorem displacement {ι : Type*} [Fintype ι] [DecidableEq ι] {a b pos : ι → ℝ} (hposinj : Function.Injective pos) (v : ι → ℝ) (i : ι) :
    pos i * (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b pos *ᵥ v) i
      - (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b pos *ᵥ (fun j => pos j * v j)) i
      = b i * (∑ j, v j) - ∑ j, b j * v j := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst hij; ring
  · rw [Cvs.Finite.DividedDifferenceCommutator.ddMatrix_off hij]
    have hne : pos i - pos j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hposinj h))
    field_simp

/-- An odd vector sums to zero. -/
theorem sum_eq_zero_of_odd {ι : Type*} [Fintype ι] {neg : ι → ι} (hinv : Function.Involutive neg)
    {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i) : ∑ i, o i = 0 := by
  have h := Equiv.sum_comp (Function.Involutive.toPerm neg hinv) o
  simp only [Function.Involutive.coe_toPerm, hodd, Finset.sum_neg_distrib] at h
  linarith

/-- **The even bottom eigenvector has nonzero coefficient sum**, given the odd gap and a nonzero
frequency. -/
theorem sum_ne_zero_of_eigen {ι : Type*} [Fintype ι] [DecidableEq ι] {a b pos : ι → ℝ} (hposinj : Function.Injective pos)
    {neg : ι → ι} (hinv : Function.Involutive neg) (hpos : ∀ i, pos (neg i) = -pos i)
    {lam : ℝ}
    (hgap : ∀ o : ι → ℝ, (∀ i, o (neg i) = -o i) → o ≠ 0 →
      lam * (o ⬝ᵥ o) < o ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b pos *ᵥ o))
    {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    (hxi : Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b pos *ᵥ xi = lam • xi)
    (hne : ∃ j, xi j * pos j ≠ 0) :
    ∑ i, xi i ≠ 0 := by
  intro hsum
  set o : ι → ℝ := fun j => pos j * xi j with ho
  have hodd : ∀ i, o (neg i) = -o i := by
    intro i; simp only [ho, hpos i, hxieven i]; ring
  set c : ℝ := ∑ j, b j * xi j with hc
  -- `M o = lam • o + c • 𝟙`
  have hMo : ∀ i, (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b pos *ᵥ o) i = lam * o i + c := by
    intro i
    have h := displacement (a := a) (b := b) hposinj xi i
    rw [hsum, mul_zero, zero_sub, hxi, Pi.smul_apply, smul_eq_mul] at h
    simp only [ho]
    linarith
  -- so the form of the odd vector `o` is `lam` times its norm
  have hform : o ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b pos *ᵥ o) = lam * (o ⬝ᵥ o) := by
    simp only [dotProduct, hMo, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [← Finset.sum_mul, sum_eq_zero_of_odd hinv hodd, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- the odd gap then forces `o = 0`
  have ho0 : o = 0 := by
    by_contra hne0
    have := hgap o hodd hne0
    linarith
  obtain ⟨j, hj⟩ := hne
  apply hj
  have := congrFun ho0 j
  simp only [ho, Pi.zero_apply] at this
  linarith

/-! ### The endpoint hypothesis, discharged for the discrete minimiser -/

/-- **`∑ xiD N ≠ 0`** whenever the bottom lies below the isolation level and the constant entry. -/
theorem sum_xiD_ne_zero {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam mu : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (heven : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le η = η)
    (hiso : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le, (inner ℝ η v : ℝ) = 0 →
      mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (N : ℕ) (hlt : Cvs.Finite.SymmetricModeSet.lamD P R L hL N < mu)
    (hconst : Cvs.Finite.SymmetricModeSet.lamD P R L hL N
      < Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) none none) :
    ∑ i, Cvs.Finite.SymmetricModeSet.xiD P R L hL N i ≠ 0 := by
  have _ : lam = lam := rfl
  obtain ⟨-, -, hxi⟩ := Cvs.Finite.SymmetricModeSet.xiD_spec P R L hL N
  have hinj := Cvs.Finite.SymmetricModeSet.mode_injective N
  have hinv := Cvs.Finite.SymmetricModeSet.negI_involutive N
  have hmode := Cvs.Finite.SymmetricModeSet.mode_negI N
  have hgap : ∀ o : Cvs.Finite.SymmetricModeSet.Idx N → ℝ,
      (∀ i, o (Cvs.Finite.SymmetricModeSet.negI N i) = -o i) → o ≠ 0 →
      Cvs.Finite.SymmetricModeSet.lamD P R L hL N * (o ⬝ᵥ o)
        < o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ o) := by
    intro o hodd hne
    have h1 := Cvs.Finite.DiscreteTwoGap.odd_gap_of_stepA hL P R (lam := lam) heven hiso hinj hinv
      hmode hodd
    have hpos : 0 < o ⬝ᵥ o := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
      (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
    calc Cvs.Finite.SymmetricModeSet.lamD P R L hL N * (o ⬝ᵥ o) < mu * (o ⬝ᵥ o) :=
          mul_lt_mul_of_pos_right hlt hpos
      _ ≤ _ := h1
  exact sum_ne_zero_of_eigen (Cvs.Finite.DisplacementIdentity.omega_injective hL hinj) hinv
    (Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg hmode) hgap
    (Cvs.Finite.DisplacementIdentity.xiD_even hL P R (lam := lam) heven hiso N hlt) hxi
    (Cvs.Finite.DisplacementIdentity.xiD_ne hL P R N hconst)

end Cvs.Finite.DisplacementIdentity
