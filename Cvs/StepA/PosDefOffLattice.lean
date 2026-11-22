import Mathlib
import Cvs.Finite.CoefficientDilation
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EvenBilinearZeroSide
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.NestedMinimiser
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.ReducedSecularPolynomial
import Cvs.Finite.SecularCoefficientLimits
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Finite.ZeroSideGramMatrix
import Cvs.StepA.EvenBelowOdd
import Cvs.StepA.OddAboveDisplacement
import Cvs.StepA.OddAboveUnderRH
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.ConcreteTestIdentification
import Cvs.WeilForm.CouplingAngle
import Cvs.WeilForm.MatrixPSDCriterion
import Cvs.WeilForm.MellinZeroSum
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.WeightedRateLemma
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Under RH the window matrix is positive definite when the zeros whose ordinate avoids `2πℤ/L` have more than `N` distinct squared ordinates

Off `2πℤ/L` an even vector's transform vanishes only where `γ²` is a root of its secular polynomial,
the secular polynomial on the pair nodes `(2πk/L)²`: degree at most `N`, nonzero for a nonzero even
vector. So the CvS matrix is positive definite under RH and that count condition, and step (a)
follows for an odd bottom eigenpair with `Ω_h` below every zero ordinate.
-/

noncomputable section

open Matrix Real Polynomial Cvs.Finite.SymmetricModeSet Cvs.Finite.OddEigenvectorResolvent Cvs.Finite.EvenMinimisers
open Cvs.Finite.ReducedSecularPolynomial Cvs.Finite.SecularCoefficientLimits Cvs.StepA.OddAboveDisplacement Cvs.Finite.ParitySectorDefect
open Cvs.StepA.EvenBelowOdd Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.StepA.PosDefOffLattice
open Cvs.ZeroCounting

variable {L : ℝ} {N : ℕ}

/-! ### The secular polynomial on the pair nodes -/

/-- **On distinct nodes a nonzero weight vector has a nonzero secular polynomial.** -/
theorem Psec_ne_zero {κ : Type*} [Fintype κ] [DecidableEq κ] {F : Type*} [Field F] {q : κ → F}
    (hq : Function.Injective q) {y : κ → F} (hy : y ≠ 0) : Cvs.Finite.CoefficientDilation.Psec q y ≠ 0 := by
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hy
  intro h
  have he := congrArg (Polynomial.eval (q m)) h
  rw [Cvs.Finite.CoefficientDilation.eval_Psec_node, eval_zero] at he
  refine mul_ne_zero hm (Finset.prod_ne_zero_iff.mpr fun l hl => sub_ne_zero.mpr fun e => ?_) he
  exact (Finset.mem_erase.mp hl).1 (hq e)

/-- The secular polynomial's nodes: the pair nodes `(2π·k)²` divided by `L²`. -/
def secNode (L : ℝ) (N : ℕ) (m : Option (Fin N)) : ℂ :=
  ((Cvs.Finite.NestedMinimiser.qr N m / L ^ 2 : ℝ) : ℂ)

theorem secNode_none (L : ℝ) (N : ℕ) : secNode L N none = 0 := by
  simp [secNode, Cvs.Finite.NestedMinimiser.qr, Cvs.Finite.NestedMinimiser.amode]

theorem secNode_some (L : ℝ) (N : ℕ) (j : Fin N) : secNode L N (some j) = qf L N j := by
  simp only [secNode, Cvs.Finite.NestedMinimiser.qr, Cvs.Finite.NestedMinimiser.amode, qf]
  push_cast
  ring

theorem secNode_injective (hL : L ≠ 0) (N : ℕ) : Function.Injective (secNode L N) := fun _ _ h =>
  Cvs.Finite.NestedMinimiser.qr_injective N
    ((div_left_inj' (pow_ne_zero 2 hL)).mp (Complex.ofReal_injective h))

/-- The secular polynomial's weights: `x₀` at the node `0` and the pair sum `x_j⁺ + x_j⁻` at
`qf L N j`. -/
def secWeight (N : ℕ) (xi : Idx N → ℝ) : Option (Fin N) → ℂ
  | none => (xi none : ℂ)
  | some j => ((xi (some (j, true)) + xi (some (j, false)) : ℝ) : ℂ)

/-- **The reduced secular polynomial is the secular polynomial on the pair nodes.** -/
theorem secPolyP_eq_Psec (L : ℝ) (N : ℕ) (xi : Idx N → ℝ) :
    secPolyP L N xi = Cvs.Finite.CoefficientDilation.Psec (secNode L N) (secWeight N xi) := by
  have h0 : (Finset.univ : Finset (Option (Fin N))).erase none
      = Finset.univ.map Function.Embedding.some := by
    ext m; rcases m with _ | j <;> simp
  have h1 : ∀ j : Fin N, (Finset.univ : Finset (Option (Fin N))).erase (some j)
      = Finset.insertNone (Finset.univ.erase j) := by
    intro j; ext m; rcases m with _ | j' <;> simp
  have hA : C (secWeight N xi none) * ∏ l ∈ Finset.univ.erase none, (C (secNode L N l) - X)
      = C (xi none : ℂ) * ∏ j, (C (qf L N j) - X) := by
    rw [h0, Finset.prod_map]
    simp only [Function.Embedding.some_apply, secNode_some]
    rfl
  have hB : ∀ j : Fin N, C (secWeight N xi (some j))
        * ∏ l ∈ Finset.univ.erase (some j), (C (secNode L N l) - X)
      = C (((xi (some (j, true)) + xi (some (j, false)) : ℝ) : ℂ)) * (-X)
        * ∏ j' ∈ Finset.univ.erase j, (C (qf L N j') - X) := by
    intro j
    rw [h1, Finset.prod_insertNone, secNode_none]
    simp only [secNode_some, map_zero, zero_sub]
    rw [← mul_assoc]
    rfl
  unfold Cvs.Finite.CoefficientDilation.Psec
  rw [Fintype.sum_option, hA, Finset.sum_congr rfl fun j _ => hB j]
  rfl

/-- **The secular polynomial has degree at most `N`.** -/
theorem natDegree_secPolyP_le (L : ℝ) (N : ℕ) (xi : Idx N → ℝ) : (secPolyP L N xi).natDegree ≤ N := by
  have h := Cvs.Finite.CoefficientDilation.natDegree_Psec_le (secNode L N) (secWeight N xi)
  rw [Fintype.card_option, Fintype.card_fin, Nat.add_sub_cancel] at h
  rw [secPolyP_eq_Psec]
  exact h

/-- **The secular polynomial of a nonzero even vector is nonzero.** -/
theorem secPolyP_ne_zero (hL : L ≠ 0) {xi : Idx N → ℝ} (hxe : ∀ i, xi (negI N i) = xi i)
    (hne : xi ≠ 0) : secPolyP L N xi ≠ 0 := by
  rw [secPolyP_eq_Psec]
  refine Psec_ne_zero (secNode_injective hL N) fun h0 => hne (funext fun i => ?_)
  have hpair : ∀ j : Fin N, xi (some (j, false)) = xi (some (j, true)) := fun j => by
    have := hxe (some (j, true)); simpa [negI] using this
  rcases i with _ | ⟨j, b⟩
  · have h := congrFun h0 none
    simp only [secWeight, Pi.zero_apply, Complex.ofReal_eq_zero] at h
    exact h
  · have h := congrFun h0 (some j)
    simp only [secWeight, Pi.zero_apply, Complex.ofReal_eq_zero, hpair j] at h
    have ht : xi (some (j, true)) = 0 := by linarith
    cases b
    · rw [Pi.zero_apply, hpair j, ht]
    · exact ht

/-! ### Off the lattice `2πℤ/L` -/

/-- Off the lattice, `γ²` differs from every squared integer frequency. -/
theorem sq_sub_sq_ne_zero (hL : 0 < L) {γ : ℝ} (hγ : ∀ k : ℤ, γ * L ≠ 2 * π * k) (m : ℤ) :
    ((2 * π * m / L : ℝ) : ℂ) ^ 2 - (γ : ℂ) ^ 2 ≠ 0 := by
  intro h
  rw [sub_eq_zero, ← Complex.ofReal_pow, ← Complex.ofReal_pow, Complex.ofReal_inj] at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
  · apply hγ m; rw [← h1]; field_simp
  · apply hγ (-m)
    have hγ' : γ = -(2 * π * m / L) := by linarith
    rw [hγ']; push_cast; field_simp

/-- **Off the lattice `2πℤ/L` an even vector's transform vanishes only at a root of its secular
polynomial.** -/
theorem secPoly_eq_zero_of_transform (hL : 0 < L) (xi : Idx N → ℝ) {γ : ℝ}
    (hγ : ∀ k : ℤ, γ * L ≠ 2 * π * k)
    (h : Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) xi)) (γ : ℂ) = 0) :
    secPoly L N xi ((γ : ℂ) ^ 2) = 0 := by
  have hgen : ∀ k, ((2 * π * mode N k / L : ℝ) : ℂ) ^ 2 - (γ : ℂ) ^ 2 ≠ 0 :=
    fun k => sq_sub_sq_ne_zero hL hγ (mode N k)
  rw [Cvs.Finite.UniversalFunctionPairing.transform_cosPoly_eq hL (mode N) xi hgen] at h
  have hγ0 : (γ : ℂ) ≠ 0 := by
    intro h0
    apply hγ 0
    rw [Complex.ofReal_eq_zero.mp h0]; simp
  have hexp : Complex.exp (-((L : ℂ) * (γ : ℂ)) * Complex.I) - 1 ≠ 0 := by
    intro h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp h1)
    have h2 : ((-(L * γ) - n * (2 * π) : ℝ) : ℂ) * Complex.I = 0 := by
      push_cast; linear_combination hn
    have h3 : -(L * γ) - n * (2 * π) = 0 :=
      Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right Complex.I_ne_zero)
    apply hγ (-n)
    push_cast
    linarith
  have hS : Cvs.Finite.UniversalFunctionPairing.S L (mode N) xi (γ : ℂ) = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exfalso
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hγ0) h''
      · exact hexp h''
    · exact h'
  have hq : ∀ j, qf L N j - (γ : ℂ) ^ 2 ≠ 0 := by
    intro j
    have := sq_sub_sq_ne_zero hL hγ ((j : ℤ) + 1)
    unfold qf
    convert this using 3
    push_cast; ring
  rw [← S_mul_eq_secPoly N xi (pow_ne_zero 2 hγ0) hq, hS, zero_mul]

/-- The squares of the zero ordinates that avoid `2πℤ/L`. -/
def offLatticeSq (L : ℝ) : Set ℝ :=
  (fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet => ((rho : ℂ).im) ^ 2) ''
    {rho | ∀ k : ℤ, (rho : ℂ).im * L ≠ 2 * π * k}

/-- **When the zeros whose ordinate avoids `2πℤ/L` have more than `N` distinct squared ordinates, one
of them has an ordinate at which the transform of a nonzero even vector is nonzero.** -/
theorem exists_offLattice_transform_ne_zero (hL : 0 < L) {xi : Idx N → ℝ}
    (hxe : ∀ i, xi (negI N i) = xi i) (hne : xi ≠ 0) (hZ : (N : ℕ∞) < (offLatticeSq L).encard) :
    ∃ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (∀ k : ℤ, (rho : ℂ).im * L ≠ 2 * π * k) ∧
      Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) xi))
        (((rho : ℂ).im : ℝ) : ℂ) ≠ 0 := by
  by_contra hall
  push Not at hall
  set p := secPolyP L N xi
  have hp0 : p ≠ 0 := secPolyP_ne_zero hL.ne' hxe hne
  have hmaps : Set.MapsTo (fun t : ℝ => (t : ℂ)) (offLatticeSq L) (p.roots.toFinset : Set ℂ) := by
    rintro t ⟨rho, hrho, rfl⟩
    have h0 := secPoly_eq_zero_of_transform hL xi hrho (hall rho hrho)
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    refine (Polynomial.mem_roots hp0).mpr ?_
    rw [Polynomial.IsRoot.def, eval_secPolyP]
    simpa using h0
  have hle := Set.encard_le_encard_of_injOn hmaps (Complex.ofReal_injective.injOn)
  rw [Set.encard_coe_eq_coe_finsetCard] at hle
  have hcard : (p.roots.toFinset.card : ℕ∞) ≤ N := by
    exact_mod_cast (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' p).trans (natDegree_secPolyP_le L N _))
  exact absurd (hZ.trans_le (hle.trans hcard)) (lt_irrefl _)

/-! ### Positivity under RH -/

/-- **Under RH a nonzero even vector has positive form** when the zeros whose ordinate avoids `2πℤ/L`
have more than `N` distinct squared ordinates. -/
theorem evenForm_pos_of_RH (hRH : RiemannHypothesis) (hL : 0 < L) {xi : Idx N → ℝ}
    (hxe : ∀ i, xi (negI N i) = xi i) (hne : xi ≠ 0) (hZ : (N : ℕ∞) < (offLatticeSq L).encard) :
    0 < xi ⬝ᵥ (MX L N *ᵥ xi) := by
  have hre := Cvs.WeilForm.CouplingAngle.re_eq_half_of_rh hRH
  obtain ⟨rho₀, -, hW⟩ := exists_offLattice_transform_ne_zero hL hxe hne hZ
  have h := Cvs.Finite.ZeroSideGramMatrix.zeroSide_eq_ddMatrix hL (mode_injective N) (negI_involutive N)
    (mode_negI N) hxe 0 0
  unfold Cvs.ZeroCounting.kernelZeroSide at h
  have hs := Cvs.Finite.EvenBilinearZeroSide.summable_zeroSide_cosPoly hL (mode N) xi
  have hnn : ∀ rho, 0 ≤ (Cvs.Criterion.divisorWeight rho : ℝ)
      * (Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) xi))
          (Cvs.ZeroCounting.zPoint rho)).re := fun rho => by
    rw [Cvs.StepA.OddAboveUnderRH.sqTerm_of_re L _ (hre rho)]; positivity
  have hw : (0 : ℝ) < (Cvs.Criterion.divisorWeight rho₀ : ℝ) := by
    exact_mod_cast Cvs.Criterion.one_le_divisorWeight rho₀
  have hpos := hs.tsum_pos hnn rho₀ (by
    rw [Cvs.StepA.OddAboveUnderRH.sqTerm_of_re L _ (hre rho₀)]
    exact mul_pos hw (pow_pos (norm_pos_iff.mpr hW) 2))
  rw [h] at hpos
  exact pos_of_mul_pos_right hpos hL.le

/-- **Under RH a nonzero odd vector has positive form** when the zeros whose ordinate avoids `2πℤ/L`
have more than `N` distinct squared ordinates. -/
theorem oddForm_pos_of_RH (hRH : RiemannHypothesis) (hL : 0 < L) {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) (hne : o ≠ 0) (hZ : (N : ℕ∞) < (offLatticeSq L).encard) :
    0 < o ⬝ᵥ (MX L N *ᵥ o) := by
  have hre := Cvs.WeilForm.CouplingAngle.re_eq_half_of_rh hRH
  obtain ⟨rho₀, hoff, hW⟩ := exists_offLattice_transform_ne_zero hL (xdiv_even hL N hodd)
    (xdiv_ne_zero hL hodd hne) hZ
  have hγ0 : (rho₀ : ℂ).im ≠ 0 := by
    intro h0; apply hoff 0; rw [h0]; simp
  have hb : ∀ rho, 0 ≤ bTerm L N o rho := fun rho => by
    rw [bTerm_of_re L N o (hre rho)]; positivity
  have hb0 : 0 < bTerm L N o rho₀ := by
    rw [bTerm_of_re L N o (hre rho₀)]
    have hw : (0 : ℝ) < (Cvs.Criterion.divisorWeight rho₀ : ℝ) := by
      exact_mod_cast Cvs.Criterion.one_le_divisorWeight rho₀
    exact mul_pos hw (mul_pos (pow_pos (abs_pos.mpr hγ0) 2 |>.trans_eq (sq_abs _))
      (pow_pos (norm_pos_iff.mpr hW) 2))
  have hpos : 0 < ∑' rho, bTerm L N o rho := (summable_odd hL hodd).tsum_pos hb rho₀ hb0
  have he : ∑' rho, bTerm L N o rho = L * (o ⬝ᵥ (MX L N *ᵥ o)) := (oddForm_zeroSide hL hodd).symm
  rw [he] at hpos
  exact pos_of_mul_pos_right hpos hL.le

/-- **Under RH the window matrix is positive definite** when the zeros whose ordinate avoids `2πℤ/L`
have more than `N` distinct squared ordinates. -/
theorem posDef_of_RH (hRH : RiemannHypothesis) (hL : 0 < L)
    (hZ : (N : ℕ∞) < (offLatticeSq L).encard) : (MX L N).PosDef := by
  have hpsd := Cvs.WeilForm.MatrixPSDCriterion.posSemidef_of_rh hRH hL (Cvs.WeilForm.ConcreteTestIdentification.le_ceil_exp L)
    (Cvs.WeilForm.ConcreteTestIdentification.le_ceil_log L) (mode_injective N) (negI_involutive N) (mode_negI N)
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hpsd.isHermitian, fun v hv => ?_⟩
  rw [star_trivial, Cvs.Finite.TruncationQuadraticForm.dotProduct_mulVec_split
    (Cvs.Finite.TruncationQuadraticForm.M_symm hL _ _ (mode_injective N)) (negI_involutive N)
    (Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL _ _ (mode_injective N) (mode_negI N)) v]
  have he0 := hpsd.dotProduct_mulVec_nonneg (Cvs.Finite.TruncationQuadraticForm.evenPart (negI N) v)
  have ho0 := hpsd.dotProduct_mulVec_nonneg (Cvs.Finite.TruncationQuadraticForm.oddPart (negI N) v)
  rw [star_trivial] at he0 ho0
  by_cases he : Cvs.Finite.TruncationQuadraticForm.evenPart (negI N) v = 0
  · have ho : Cvs.Finite.TruncationQuadraticForm.oddPart (negI N) v ≠ 0 := by
      intro h
      apply hv
      rw [← Cvs.Finite.TruncationQuadraticForm.evenPart_add_oddPart (negI N) v, he, h, add_zero]
    have := oddForm_pos_of_RH hRH hL (Cvs.Finite.TruncationQuadraticForm.oddPart_odd (negI_involutive N) v) ho hZ
    linarith
  · have := evenForm_pos_of_RH hRH hL (Cvs.Finite.TruncationQuadraticForm.evenPart_even (negI_involutive N) v) he hZ
    linarith

/-- **Under RH the even bottom is positive** when the zeros whose ordinate avoids `2πℤ/L` have more
than `N` distinct squared ordinates. -/
theorem evLam_pos_of_RH (hRH : RiemannHypothesis) (hL : 0 < L)
    (hZ : (N : ℕ∞) < (offLatticeSq L).encard) : 0 < evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  obtain ⟨-, he1, -, heeig⟩ := evMin_spec ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ hL N
  have hne : evMin ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N ≠ 0 := by
    intro h0; rw [h0] at he1; simp at he1
  have h := (posDef_of_RH hRH hL hZ).dotProduct_mulVec_pos hne
  rw [star_trivial, heeig, dotProduct_smul, smul_eq_mul, he1, mul_one] at h
  exact h

/-! ### Step (a) under RH -/

/-- **RH gives step (a)** for an odd bottom eigenpair with `Ω_h` below every zero ordinate, when the
zeros whose ordinate avoids `2πℤ/L` have more than `N` distinct squared ordinates. -/
theorem oddAbove_of_RH_offLattice (hRH : RiemannHypothesis) (hL : 0 < L)
    (hZ : (N : ℕ∞) < (offLatticeSq L).encard) {μ : ℝ} {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) (hne : o ≠ 0) (hMo : MX L N *ᵥ o = μ • o)
    (hbot : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) → μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (MX L N *ᵥ v))
    (hΩ : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, omegaSq L N o < ((rho : ℂ).im) ^ 2) :
    OddAbove ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  have ho : 0 < o ⬝ᵥ o := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
    (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
  have hpos := oddForm_pos_of_RH hRH hL hodd hne hZ
  rw [hMo, dotProduct_smul, smul_eq_mul] at hpos
  exact Cvs.StepA.OddAboveUnderRH.oddAbove_of_RH hRH hL hodd hne hMo hbot
    (pos_of_mul_pos_left hpos ho.le) hΩ

/-- **RH gives step (a) below a common gap**: every zero ordinate at least `c ≥ 0` in absolute value,
more than `N` distinct squared ordinates among the zeros whose ordinate avoids `2πℤ/L`, and an odd
bottom eigenpair with `|o|² < c²·|xdiv o|²`. -/
theorem oddAbove_of_RH_of_gap_offLattice (hRH : RiemannHypothesis) (hL : 0 < L)
    (hZ : (N : ℕ∞) < (offLatticeSq L).encard) {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, c ≤ |(rho : ℂ).im|) {μ : ℝ}
    {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) (hMo : MX L N *ᵥ o = μ • o)
    (hbot : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) → μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (MX L N *ᵥ v))
    (hΩ : o ⬝ᵥ o < c ^ 2 * (xdiv L N o ⬝ᵥ xdiv L N o)) :
    OddAbove ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N :=
  oddAbove_of_RH_offLattice hRH hL hZ hodd (Cvs.StepA.OddAboveUnderRH.ne_zero_of_lt_sq_mul hΩ) hMo hbot
    (Cvs.StepA.OddAboveUnderRH.omegaSq_lt_of_gap hL hodd hc hgap hΩ)

end Cvs.StepA.PosDefOffLattice
