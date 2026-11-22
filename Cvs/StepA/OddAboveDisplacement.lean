import Mathlib
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.ParityDisplacementEigenspaces
import Cvs.Finite.ReducedSecularPolynomial
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Limit.MomentSpineConstantCoeff
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even sector from the odd sector, through the displacement identity

`ΩM − MΩ = b𝟙ᵀ − 𝟙bᵀ`: a second even eigenvector at the even bottom gives a fatal vector whose
`Ω`-image is an odd eigenvector there, and an even one with `ξ₀ = 0` gives the odd eigenvector `ξ/ω`.
Ward identity, `d = y² + ω²`, `a = −ωξ/d`, `c = yξ/d`: `aᵀ(M−λ)a + cᵀ(M−λ)c = (bᵀa)·∑ ξ_i/d_i`, the
secular sum at `iy`; so a strict odd gap at the even bottom leaves no secular root on `(−∞, 0]`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Matrix Filter Topology

namespace Cvs.StepA.OddAboveDisplacement
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet Cvs.Finite.OddEigenvectorResolvent Cvs.Finite.EvenMinimisers Cvs.Limit.SpineWithoutSimplicity
open Cvs.Finite.ReducedSecularPolynomial Cvs.Finite.SecularCoefficientLimits

/-! ### The displacement identity and the Ward identity, for any matrix -/

section General

variable {ι : Type*} [Fintype ι]

/-- The displacement identity applied to a vector: `ω_i (Gv)_i − (G(ωv))_i = e_i (u ⬝ v) − u_i (e ⬝ v)`. -/
theorem displacement_mulVec {om : ι → ℝ} {G : Matrix ι ι ℝ} {e u : ι → ℝ}
    (hd : Cvs.Finite.ParityDisplacementEigenspaces.Displacement om G e u) (v : ι → ℝ) (i : ι) :
    om i * (G *ᵥ v) i - (G *ᵥ fun k => om k * v k) i = e i * (u ⬝ᵥ v) - u i * (e ⬝ᵥ v) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  linear_combination (v j) * (hd i j)

/-- The odd Ward vector `a_i = −ω_i ξ_i / (y² + ω_i²)`. -/
def wardA (om : ι → ℝ) (y : ℝ) (xi : ι → ℝ) : ι → ℝ := fun i => -(om i * xi i / (y ^ 2 + om i ^ 2))

/-- The even Ward vector `c_i = y ξ_i / (y² + ω_i²)`. -/
def wardC (om : ι → ℝ) (y : ℝ) (xi : ι → ℝ) : ι → ℝ := fun i => y * xi i / (y ^ 2 + om i ^ 2)

omit [Fintype ι] in
theorem wardA_odd {om : ι → ℝ} {neg : ι → ι} (hom : ∀ i, om (neg i) = -om i) (y : ℝ) {xi : ι → ℝ}
    (hxe : ∀ i, xi (neg i) = xi i) (i : ι) : wardA om y xi (neg i) = -wardA om y xi i := by
  simp only [wardA, hom i, hxe i, neg_sq]; ring

omit [Fintype ι] in
theorem wardC_even {om : ι → ℝ} {neg : ι → ι} (hom : ∀ i, om (neg i) = -om i) (y : ℝ) {xi : ι → ℝ}
    (hxe : ∀ i, xi (neg i) = xi i) (i : ι) : wardC om y xi (neg i) = wardC om y xi i := by
  simp only [wardC, hom i, hxe i, neg_sq]

/-- **The imaginary-axis Ward identity.** For `G` with displacement `e uᵀ − u eᵀ`, an eigenvector
`ξ` at `λ` and `y ≠ 0`, the excesses of the Ward vectors add to
`(e ⬝ a)·∑ u_i ξ_i/d_i − (u ⬝ a)·∑ e_i ξ_i/d_i` with `d_i = y² + ω_i²`. -/
theorem ward {om : ι → ℝ} {G : Matrix ι ι ℝ} {e u : ι → ℝ}
    (hd : Cvs.Finite.ParityDisplacementEigenspaces.Displacement om G e u) {lam : ℝ} {xi : ι → ℝ}
    (hx : G *ᵥ xi = lam • xi) {y : ℝ} (hy : y ≠ 0) :
    (wardA om y xi ⬝ᵥ (G *ᵥ wardA om y xi) - lam * (wardA om y xi ⬝ᵥ wardA om y xi))
      + (wardC om y xi ⬝ᵥ (G *ᵥ wardC om y xi) - lam * (wardC om y xi ⬝ᵥ wardC om y xi))
      = (e ⬝ᵥ wardA om y xi) * ∑ i, u i * xi i / (y ^ 2 + om i ^ 2)
        - (u ⬝ᵥ wardA om y xi) * ∑ i, e i * xi i / (y ^ 2 + om i ^ 2) := by
  set a := wardA om y xi with ha
  set c := wardC om y xi with hc
  have hy2 : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  have hden : ∀ i, y ^ 2 + om i ^ 2 ≠ 0 := fun i => (add_pos_of_pos_of_nonneg hy2 (sq_nonneg _)).ne'
  have hωa : (fun k => om k * a k) = -xi + y • c := by
    funext k
    simp only [ha, hc, wardA, wardC, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    have := hden k
    field_simp
    ring
  have hxi : ∀ i, -(om i * a i) + y * c i = xi i := by
    intro i
    simp only [ha, hc, wardA, wardC]
    have := hden i
    field_simp
    ring
  have hrow : ∀ i, om i * ((G *ᵥ a) i - lam * a i) - y * ((G *ᵥ c) i - lam * c i)
      = e i * (u ⬝ᵥ a) - u i * (e ⬝ᵥ a) := by
    intro i
    have h := displacement_mulVec hd a i
    rw [hωa, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, hx] at h
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h
    linear_combination h + lam * hxi i
  have hper : ∀ i, a i * ((G *ᵥ a) i - lam * a i) + c i * ((G *ᵥ c) i - lam * c i)
      = -(xi i / (y ^ 2 + om i ^ 2)) * (e i * (u ⬝ᵥ a) - u i * (e ⬝ᵥ a)) := by
    intro i
    have hai : a i = -(om i * xi i / (y ^ 2 + om i ^ 2)) := rfl
    have hci : c i = y * xi i / (y ^ 2 + om i ^ 2) := rfl
    rw [← hrow i, hai, hci]
    ring
  have hq : ∀ v w : ι → ℝ, v ⬝ᵥ w - lam * (v ⬝ᵥ v) = ∑ i, v i * (w i - lam * v i) := by
    intro v w
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hq, hq, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ => hper i]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end General

/-! ### The window matrix -/

/-- **The displacement identity for the window matrix**: `(ω_i − ω_j) M_ij = b_i − b_j`, the
displacement with generators `𝟙` and `−b`. -/
theorem displacement_M {L : ℝ} (hL : 0 < L) (P R N : ℕ) :
    Cvs.Finite.ParityDisplacementEigenspaces.Displacement (om L N) (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)) 1
      (fun i => -Cvs.Finite.PairFormDividedDifference.bval P R L (mode N i)) := by
  intro i j
  by_cases hij : i = j
  · subst hij; ring
  · have hne : Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i - Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) j
        ≠ 0 :=
      sub_ne_zero.mpr fun h => hij (Cvs.Finite.DisplacementIdentity.omega_injective hL (mode_injective N) h)
    show (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i - Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) j)
        * Cvs.Finite.DividedDifferenceCommutator.ddMatrix _ _ (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N)) i j = _
    rw [Cvs.Finite.DividedDifferenceCommutator.ddMatrix_off hij, mul_div_cancel₀ _ hne]
    simp only [Pi.one_apply]
    ring

theorem M_isSymm {L : ℝ} (hL : 0 < L) (P R N : ℕ) :
    (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)).IsSymm :=
  Matrix.IsSymm.ext fun i j => Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (mode_injective N) j i

theorem om_odd (L : ℝ) (N : ℕ) (i : Idx N) : om L N (negI N i) = -om L N i :=
  Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg (mode_negI N) i

/-- The window matrix sends an odd vector to one vanishing at the constant mode. -/
theorem mulVec_none_of_odd {L : ℝ} (hL : 0 < L) (P R N : ℕ) {w : Idx N → ℝ}
    (hw : ∀ i, w (negI N i) = -w i) : (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w) none = 0 := by
  have he : ∀ i, (Pi.single none (1 : ℝ) : Idx N → ℝ) (negI N i)
      = (Pi.single none (1 : ℝ) : Idx N → ℝ) i := by
    rintro (_ | j)
    · rfl
    · simp [negI]
  have h := Cvs.Finite.TruncationQuadraticForm.dotProduct_mulVec_eq_zero (negI_involutive N)
    (Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R (mode_injective N) (mode_negI N)) he hw
  rwa [single_dotProduct, one_mul] at h

/-- The two even-bottom levels coincide. -/
theorem groundLam_eq_evLam (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    groundLam P R L hL N = evLam P R L hL N := by
  obtain ⟨hge, hg1, hgmin, hgeig, _⟩ := ground_spec P R hL N
  obtain ⟨hee, he1, hemin, heeig⟩ := evMin_spec P R hL N
  have h1 := hgmin _ hee
  have h2 := hemin _ hge
  rw [he1, mul_one, heeig, dotProduct_smul, smul_eq_mul, he1, mul_one] at h1
  rw [hg1, mul_one, hgeig, dotProduct_smul, smul_eq_mul, hg1, mul_one] at h2
  linarith

/-- **An even eigenvector vanishing at the constant mode divides into an odd eigenvector**: `ξ/ω` is
odd, nonzero, and an eigenvector at the same level. -/
theorem exists_odd_of_none_eq_zero {L : ℝ} (hL : 0 < L) (P R N : ℕ) {mu : ℝ} {xi : Idx N → ℝ}
    (hxe : ∀ i, xi (negI N i) = xi i) (hx : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xi = mu • xi)
    (hxne : xi ≠ 0) (h0 : xi none = 0) :
    ∃ w : Idx N → ℝ, (∀ i, w (negI N i) = -w i) ∧ w ≠ 0
      ∧ Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w = mu • w := by
  set M := Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) with hM
  set w : Idx N → ℝ := fun i => xi i / om L N i with hw
  have hwodd : ∀ i, w (negI N i) = -w i := by
    intro i; simp only [hw, hxe i, om_odd, div_neg]
  have hωw : (fun k => om L N k * w k) = xi := by
    funext k
    rcases k with _ | j
    · simp only [hw, om_none, zero_mul, h0]
    · simp only [hw]; field_simp [om_some_ne hL N j]
  have hsum : (1 : Idx N → ℝ) ⬝ᵥ w = 0 := by
    rw [one_dotProduct]; exact Cvs.Finite.DisplacementIdentity.sum_eq_zero_of_odd (negI_involutive N) hwodd
  have hrow : ∀ i, om L N i * (M *ᵥ w) i - mu * xi i
      = (fun i => -Cvs.Finite.PairFormDividedDifference.bval P R L (mode N i)) ⬝ᵥ w := by
    intro i
    have h := displacement_mulVec (displacement_M hL P R N) w i
    rw [hωw, hx, hsum] at h
    simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_zero, sub_zero, one_mul] at h
    linarith
  have hbw : (fun i => -Cvs.Finite.PairFormDividedDifference.bval P R L (mode N i)) ⬝ᵥ w = 0 := by
    have h := hrow none
    rw [om_none, h0] at h
    linarith
  refine ⟨w, hwodd, ?_, ?_⟩
  · intro hw0
    apply hxne
    rw [← hωw, hw0]
    funext k; simp
  · funext i
    rcases i with _ | j
    · have hw0 : w none = 0 := by
        have := hwodd none
        simp only [negI] at this
        linarith
      rw [mulVec_none_of_odd hL P R N hwodd, Pi.smul_apply, smul_eq_mul, hw0, mul_zero]
    · have h := hrow (some j)
      rw [hbw, ← congrFun hωw (some j)] at h
      have hne := om_some_ne hL N j
      have h' : om L N (some j) * ((M *ᵥ w) (some j) - mu * w (some j)) = 0 := by linarith
      rw [Pi.smul_apply, smul_eq_mul]
      linarith [(mul_eq_zero.mp h').resolve_left hne]

/-! ### No odd eigenvector at the even bottom -/

/-- No nonzero odd eigenvector of the window matrix at the even-sector bottom. -/
def NotOddEig (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) : Prop :=
  ∀ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) →
    Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o = evLam P R L hL N • o → o = 0

/-- **No odd eigenvector at the even bottom makes the even bottom simple.** -/
theorem evenSimple_of_notOddEig {P R : ℕ} {L : ℝ} {hL : 0 < L} {N : ℕ} (h : NotOddEig P R L hL N) :
    EvenSimple P R L hL N := by
  intro v hve hv
  by_contra hno
  push Not at hno
  obtain ⟨hee, he1, -, heeig⟩ := evMin_spec P R hL N
  have hxne : evMin P R L hL N ≠ 0 := by intro h0; rw [h0] at he1; simp at he1
  have hd := displacement_M hL P R N
  obtain ⟨z, hzne, hzeig, hzeven, hze, hzu⟩ :=
    Cvs.Finite.ParityDisplacementEigenspaces.exists_fatal (M_isSymm hL P R N) hd heeig hv hee hve hno hxne
  obtain ⟨hOm, hOdd⟩ := Cvs.Finite.ParityDisplacementEigenspaces.omega_odd_eigenvector (om_odd L N) hd hzeig hzeven hze hzu
  have h0 := h _ hOdd hOm
  have hsome : ∀ j, z (some j) = 0 := by
    intro j
    have := congrFun h0 (some j)
    simp only [Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (om_some_ne hL N j)
  apply hzne
  funext i
  rcases i with _ | j
  · rw [one_dotProduct, Fintype.sum_option] at hze
    simp only [hsome, Finset.sum_const_zero, add_zero] at hze
    exact hze
  · exact hsome j

/-! ### The even bottom on mean-zero even vectors -/

/-! ### A strict odd gap and the secular polynomial on the imaginary axis -/

/-- A strict gap above the even bottom on odd vectors. -/
def OddAbove (P R : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) : Prop :=
  ∀ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) → o ≠ 0 →
    evLam P R L hL N * (o ⬝ᵥ o) < o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o)

theorem notOddEig_of_oddAbove {P R : ℕ} {L : ℝ} {hL : 0 < L} {N : ℕ} (h : OddAbove P R L hL N) :
    NotOddEig P R L hL N := by
  intro o hodd hoeig
  by_contra hne
  have := h o hodd hne
  rw [hoeig, dotProduct_smul, smul_eq_mul] at this
  exact lt_irrefl _ this

/-- The secular sum at `iy` is the real sum `∑ ξ_k / (y² + ω_k²)`. -/
theorem S_I_mul (L : ℝ) (N : ℕ) (xi : Idx N → ℝ) (y : ℝ) :
    Cvs.Finite.UniversalFunctionPairing.S L (mode N) xi (Complex.I * y)
      = ((∑ k, xi k / (y ^ 2 + om L N k ^ 2) : ℝ) : ℂ) := by
  unfold Cvs.Finite.UniversalFunctionPairing.S
  simp only [om, Cvs.Finite.TruncationZeroFreeOffAxes.omega]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [mul_pow, Complex.I_sq]
  ring

/-- **On the imaginary axis the secular sum of an even bottom eigenvector with a strict odd gap is
nonzero**, by the Ward identity. -/
theorem secSum_ne_zero_of_gap {L : ℝ} (hL : 0 < L) (P R N : ℕ) {lam : ℝ} {xi : Idx N → ℝ}
    (hxe : ∀ i, xi (negI N i) = xi i) (hxne : xi ≠ 0)
    (hmin : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) →
      lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
    (hx : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xi = lam • xi)
    (hodd : ∀ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) → o ≠ 0 →
      lam * (o ⬝ᵥ o) < o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o))
    {y : ℝ} (hy : y ≠ 0) :
    ∑ k, xi k / (y ^ 2 + om L N k ^ 2) ≠ 0 := by
  set M := Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) with hM
  set a := wardA (om L N) y xi with ha
  set c := wardC (om L N) y xi with hc
  have hy2 : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  have hw := ward (displacement_M hL P R N) hx hy
  have haodd : ∀ i, a (negI N i) = -a i := wardA_odd (om_odd L N) y hxe
  have hceven : ∀ i, c (negI N i) = c i := wardC_even (om_odd L N) y hxe
  have hsa : (1 : Idx N → ℝ) ⬝ᵥ a = 0 := by
    rw [one_dotProduct]; exact Cvs.Finite.DisplacementIdentity.sum_eq_zero_of_odd (negI_involutive N) haodd
  rw [← ha, ← hc, hsa, zero_mul, zero_sub] at hw
  simp only [Pi.one_apply, one_mul] at hw
  have hcge : 0 ≤ c ⬝ᵥ (M *ᵥ c) - lam * (c ⬝ᵥ c) := by linarith [hmin c hceven]
  by_cases ha0 : a = 0
  · have hsome : ∀ j, xi (some j) = 0 := by
      intro j
      have h := congrFun ha0 (some j)
      simp only [ha, wardA, Pi.zero_apply, neg_eq_zero] at h
      have hd : y ^ 2 + om L N (some j) ^ 2 ≠ 0 :=
        (add_pos_of_pos_of_nonneg hy2 (sq_nonneg _)).ne'
      rcases mul_eq_zero.mp ((div_eq_zero_iff.mp h).resolve_right hd) with h1 | h1
      · exact absurd h1 (om_some_ne hL N j)
      · exact h1
    have hnone : xi none ≠ 0 := by
      intro h0; apply hxne; funext i; rcases i with _ | j
      · exact h0
      · exact hsome j
    rw [Fintype.sum_option]
    simp only [hsome, zero_div, Finset.sum_const_zero, add_zero, om_none]
    rw [show y ^ 2 + (0 : ℝ) ^ 2 = y ^ 2 by ring]
    exact div_ne_zero hnone hy2.ne'
  · have hapos := hodd a haodd ha0
    intro hS
    rw [hS, mul_zero, neg_zero] at hw
    linarith

/-- **An even bottom eigenvector with a strict odd gap has no secular root on `(−∞, 0]`.** -/
theorem noNonposRoot_of_gap {L : ℝ} (hL : 0 < L) (P R N : ℕ) {lam : ℝ} {xi : Idx N → ℝ}
    (hxe : ∀ i, xi (negI N i) = xi i) (hxne : xi ≠ 0)
    (hmin : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) →
      lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
    (hx : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ xi = lam • xi)
    (hodd : ∀ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) → o ≠ 0 →
      lam * (o ⬝ᵥ o) < o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o)) :
    NoNonposRoot L N xi := by
  intro t ht
  rcases ht.eq_or_lt with h0 | hneg
  · rw [h0, Complex.ofReal_zero]
    refine Cvs.Limit.MomentSpineConstantCoeff.secPoly_zero_ne_zero hL N fun hx0 => ?_
    obtain ⟨w, hwodd, hwne, hweig⟩ := exists_odd_of_none_eq_zero hL P R N hxe hx hxne hx0
    have := hodd w hwodd hwne
    rw [hweig, dotProduct_smul, smul_eq_mul] at this
    exact lt_irrefl _ this
  · set y : ℝ := Real.sqrt (-t) with hy
    have hypos : 0 < y := Real.sqrt_pos.mpr (by linarith)
    have hysq : y ^ 2 = -t := Real.sq_sqrt (by linarith)
    set z : ℂ := Complex.I * (y : ℂ) with hz
    have hzsq : z ^ 2 = (t : ℂ) := by
      rw [hz, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hysq]
      push_cast; ring
    have hzne : z ^ 2 ≠ 0 := by
      rw [hzsq]; exact Complex.ofReal_ne_zero.mpr hneg.ne
    have hq : ∀ j : Fin N, (qf L N j : ℂ) - z ^ 2 ≠ 0 := by
      intro j h
      have hre := congrArg Complex.re h
      rw [hzsq] at hre
      unfold qf at hre
      rw [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.ofReal_re, Complex.zero_re] at hre
      have : 0 ≤ (2 * π * (((j : ℕ) : ℝ) + 1) / L) ^ 2 := sq_nonneg _
      linarith
    have hS : Cvs.Finite.UniversalFunctionPairing.S L (mode N) xi z ≠ 0 := by
      rw [hz, S_I_mul]
      exact Complex.ofReal_ne_zero.mpr (secSum_ne_zero_of_gap hL P R N hxe hxne hmin hx hodd hypos.ne')
    have hprod : (-z ^ 2 * ∏ j : Fin N, ((qf L N j : ℂ) - z ^ 2)) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hzne) (Finset.prod_ne_zero_iff.mpr fun j _ => hq j)
    rw [← hzsq, ← S_mul_eq_secPoly N xi hzne hq]
    exact mul_ne_zero hS hprod

/-- **A strict odd gap at the even bottom leaves the ground state no secular root on `(−∞, 0]`.** -/
theorem noNonposRoot_of_oddAbove {P R : ℕ} {L : ℝ} {hL : 0 < L} {N : ℕ} (h : OddAbove P R L hL N) :
    NoNonposRoot L N (ground P R L hL N) := by
  obtain ⟨hge, hg1, hgmin, hgeig, -⟩ := ground_spec P R hL N
  rw [groundLam_eq_evLam] at hgmin hgeig
  exact noNonposRoot_of_gap hL P R N hge (by intro h0; rw [h0] at hg1; simp at hg1) hgmin hgeig h

end Cvs.StepA.OddAboveDisplacement
