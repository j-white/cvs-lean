import Mathlib
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.OddDisplacementPencil
import Cvs.Finite.OddDivisionPolynomial
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.PivotPencilRoots
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.StepA.DeflationUnderRH
import Cvs.StepA.LatticeCondition
import Cvs.StepA.OddBottomGapCriterion
import Cvs.StepA.OddSectorBottom
import Cvs.StepA.OrderedOrdinates
import Cvs.StepA.StepACountDischarged
import Cvs.StepA.StepACriterion
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Under RH, `LAT(L, N)` gives an odd bottom eigenpair with `Ω_h` below every ordinate

At the odd bottom `μ`, `G(p, q) = vecOf(p)ᵀ(M − μ)vecOf(q)` is a symmetric pencil with a pivot. Its
radical generator has real simple roots `r_i ≥ γ_i²`, its radical is zero under `Λ_Y < γ_1`, so the
pivot is a bottom eigenvector, and `Λ_h < 6.24` bounds its `Ω_h`.
-/

noncomputable section

open Matrix Real Polynomial

namespace Cvs.Finite.OddDisplacementPencil
open Cvs.ZeroCounting
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI negI_involutive mode_negI mode_injective)
open Cvs.Finite.OddEigenvectorResolvent (xdiv om)
open Cvs.Finite.ParitySectorDefect (MX)
open Cvs.StepA.OddBottomGapCriterion (OddBottomBelow)

variable {L : ℝ} {N : ℕ}

/-! ### The pencil form on polynomials -/

/-- The pencil form `G(p, q) = vecOf(p)ᵀ(M − μ)vecOf(q)`. -/
def pencilForm (L : ℝ) (N : ℕ) (μ : ℝ) : LinearMap.BilinForm ℝ ℝ[X] :=
  (Matrix.toBilin' (MX L N - μ • (1 : Matrix (Idx N) (Idx N) ℝ))).compl₁₂ (vecOf L N) (vecOf L N)

theorem pencilForm_apply (μ : ℝ) (p q : ℝ[X]) :
    pencilForm L N μ p q = vecOf L N p ⬝ᵥ ((MX L N - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ vecOf L N q) := by
  simp only [pencilForm, LinearMap.compl₁₂_apply, Matrix.toBilin'_apply']

theorem sub_smul_one_mulVec (A : Matrix (Idx N) (Idx N) ℝ) (μ : ℝ) (v : Idx N → ℝ) :
    (A - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ v = A *ᵥ v - μ • v := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem pencilForm_apply' (μ : ℝ) (p q : ℝ[X]) :
    pencilForm L N μ p q
      = vecOf L N p ⬝ᵥ (MX L N *ᵥ vecOf L N q) - μ * (vecOf L N p ⬝ᵥ vecOf L N q) := by
  rw [pencilForm_apply, sub_smul_one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem MX_symm (hL : 0 < L) (i j : Idx N) : MX L N i j = MX L N j i :=
  Cvs.Finite.TruncationQuadraticForm.M_symm hL _ _ (mode_injective N) i j

theorem MX_negI (hL : 0 < L) (i j : Idx N) : MX L N (negI N i) (negI N j) = MX L N i j :=
  Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL _ _ (mode_injective N) (mode_negI N) i j

theorem shift_symm (hL : 0 < L) (μ : ℝ) (i j : Idx N) :
    (MX L N - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) i j
      = (MX L N - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) j i := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, MX_symm hL i j]
  by_cases h : i = j
  · rw [h]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem shift_negI (hL : 0 < L) (μ : ℝ) (i j : Idx N) :
    (MX L N - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) (negI N i) (negI N j)
      = (MX L N - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, MX_negI hL i j]
  by_cases h : i = j
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun h' => h ((negI_involutive N).injective h')), if_neg h]

theorem pencilForm_symm (hL : 0 < L) (μ : ℝ) (p q : ℝ[X]) :
    pencilForm L N μ p q = pencilForm L N μ q p := by
  rw [pencilForm_apply, pencilForm_apply,
    Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm (shift_symm hL μ)]

/-- `G(Xp, q) = G(p, Xq)` on polynomials of degree `< N − 1` (the odd displacement). -/
theorem pencilForm_X_mul_comm (hL : 0 < L) (μ : ℝ) {p q : ℝ[X]} (hp : p.degree < (N - 1 : ℕ))
    (hq : q.degree < (N - 1 : ℕ)) :
    pencilForm L N μ (X * p) q = pencilForm L N μ p (X * q) := by
  rw [pencilForm_apply', pencilForm_apply', vecOf_X_mul, vecOf_X_mul]
  have hb : ∀ i, Cvs.Finite.PairFormDividedDifference.bval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode N (negI N i))
      = -Cvs.Finite.PairFormDividedDifference.bval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode N i) := fun i => by
    rw [mode_negI, Cvs.Finite.PairFormDividedDifference.bval_neg]
  have h := W2_dotProduct_mulVec_comm
    (a := fun k => Cvs.Finite.PairFormDividedDifference.aval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode N k))
    (b := fun k => Cvs.Finite.PairFormDividedDifference.bval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode N k))
    (Cvs.Finite.DisplacementIdentity.omega_injective hL (mode_injective N)) (negI_involutive N)
    (om_negI (L := L)) hb (vecOf_negI q) (om_dotProduct_vecOf_eq_zero hp)
    (om_dotProduct_vecOf_eq_zero hq)
  change (fun i => om L N i ^ 2 * vecOf L N p i) ⬝ᵥ (MX L N *ᵥ vecOf L N q)
    = vecOf L N p ⬝ᵥ (MX L N *ᵥ fun j => om L N j ^ 2 * vecOf L N q j) at h
  rw [h]
  congr 2
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `G(Xp, p) = (W²v)ᵀMv − μ (W²v)·v` for `v = vecOf p`. -/
theorem pencilForm_X_mul_self (μ : ℝ) (p : ℝ[X]) :
    pencilForm L N μ (X * p) p
      = (fun i => om L N i ^ 2 * vecOf L N p i) ⬝ᵥ (MX L N *ᵥ vecOf L N p)
        - μ * ((fun i => om L N i ^ 2 * vecOf L N p i) ⬝ᵥ vecOf L N p) := by
  rw [pencilForm_apply', vecOf_X_mul]

/-- At an odd bottom `μ`, `M − μ` is nonnegative on odd vectors. -/
theorem shift_psd {μ : ℝ}
    (hbot : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) → μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (MX L N *ᵥ v))
    (v : Idx N → ℝ) (hv : ∀ i, v (negI N i) = -v i) :
    0 ≤ v ⬝ᵥ ((MX L N - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ v) := by
  rw [sub_smul_one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  linarith [hbot v hv]

/-! ### The pivot -/

-- H_fix Step 1.3 (both pivot cases)
/-- **The pivot**: at an odd bottom `μ` some `P` of degree `N − 1` is `G`-orthogonal to all
polynomials of degree `< N − 1`, and `vecOf P` is a bottom eigenvector whenever some bottom
eigenvector `ξ` has `ω·ξ ≠ 0`. -/
theorem exists_pivot (hL : 0 < L) (hN : 0 < N) {μ : ℝ}
    (hbot : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) → μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (MX L N *ᵥ v)) :
    ∃ P : ℝ[X], P.degree < N ∧ P.degree = (N - 1 : ℕ) ∧
      (∀ q : ℝ[X], q.degree < (N - 1 : ℕ) → pencilForm L N μ P q = 0) ∧
      ((∃ ξ : Idx N → ℝ, (∀ i, ξ (negI N i) = -ξ i) ∧ MX L N *ᵥ ξ = μ • ξ ∧ om L N ⬝ᵥ ξ ≠ 0) →
        MX L N *ᵥ vecOf L N P = μ • vecOf L N P) := by
  by_cases hE : ∃ ξ : Idx N → ℝ, (∀ i, ξ (negI N i) = -ξ i) ∧ MX L N *ᵥ ξ = μ • ξ ∧ om L N ⬝ᵥ ξ ≠ 0
  · obtain ⟨ξ, hodd, hM, hη⟩ := hE
    obtain ⟨P, hPN, hPv⟩ := exists_vecOf_eq hL.ne' hodd
    refine ⟨P, hPN, degree_eq_pred_of_om_dotProduct_ne hPN (by rw [hPv]; exact hη), fun q _ => ?_,
      fun _ => by rw [hPv]; exact hM⟩
    rw [pencilForm_apply', hPv, Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm (MX_symm hL), hM,
      dotProduct_smul, smul_eq_mul, dotProduct_comm (vecOf L N q) ξ]
    ring
  · push Not at hE
    obtain ⟨w, hwodd, hAw⟩ := exists_odd_mulVec_eq (shift_symm hL μ) (negI_involutive N)
      (shift_negI hL μ) (y := om L N) om_negI fun v hv hAv =>
        hE v hv (by rw [sub_smul_one_mulVec, sub_eq_zero] at hAv; exact hAv)
    obtain ⟨P, hPN, hPv⟩ := exists_vecOf_eq hL.ne' hwodd
    have hηw : om L N ⬝ᵥ w ≠ 0 := by
      intro h0
      have h1 : w ⬝ᵥ ((MX L N - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ w) = 0 := by
        rw [hAw, dotProduct_comm]; exact h0
      have h2 := mulVec_eq_zero_of_odd_psd (shift_symm hL μ) (negI_involutive N) (shift_negI hL μ)
        (shift_psd hbot) hwodd h1
      rw [hAw] at h2
      have h3 := congrFun h2 (some (⟨0, hN⟩, true))
      rw [om_some, Pi.zero_apply] at h3
      simp [nu, hL.ne', Real.pi_ne_zero] at h3
    refine ⟨P, hPN, degree_eq_pred_of_om_dotProduct_ne hPN (by rw [hPv]; exact hηw), fun q hq => ?_,
      fun ⟨ξ, h1, h2, h3⟩ => absurd (hE ξ h1 h2) h3⟩
    rw [pencilForm_apply, hPv, Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm (shift_symm hL μ), hAw,
      dotProduct_comm]
    exact om_dotProduct_vecOf_eq_zero hq

/-! ### The theorem -/

/-- **Under RH, `LAT(L, N)` gives an odd bottom eigenpair with `Ω_h` below every zero ordinate.** -/
theorem oddBottomBelow_of_LAT (hRH : RiemannHypothesis) (hL : 0 < L) (hLAT : LAT L N) :
    OddBottomBelow L N := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · exfalso
      have h1 := hLAT.1
      simp [lamYNum, lamYDen] at h1
    · exact h
  obtain ⟨μ, ξ, hξodd, hξ1, hbot, hMξ⟩ :=
    Cvs.StepA.OddSectorBottom.exists_odd_bottom hL ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ N hN
  change ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) → μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (MX L N *ᵥ v) at hbot
  change MX L N *ᵥ ξ = μ • ξ at hMξ
  have hξne : ξ ≠ 0 := by rintro rfl; simp at hξ1
  have hμ : 0 < μ := by
    have h := (Cvs.StepA.StepACountDischarged.posDef_of_RH hRH hL N).dotProduct_mulVec_pos hξne
    rw [hMξ] at h
    simpa only [star_trivial, dotProduct_smul, smul_eq_mul, hξ1, mul_one] using h
  set G := pencilForm L N μ with hG
  set d := N - 1 with hd
  have hsymm : ∀ p q, G p q = G q p := pencilForm_symm hL μ
  have hpsd : ∀ p : ℝ[X], p.degree < d → 0 ≤ G p p := fun p _ => by
    rw [hG, pencilForm_apply]; exact shift_psd hbot _ (vecOf_negI p)
  have hcomm : ∀ p q : ℝ[X], p.degree < d → q.degree < d → G (X * p) q = G p (X * q) :=
    fun p q hp hq => pencilForm_X_mul_comm hL μ hp hq
  obtain ⟨P, hPN, hPd, hpiv, hPE⟩ := exists_pivot hL hN hbot
  obtain ⟨h, hmon, hdvd, hrad⟩ := exists_radical_generator hsymm hcomm hPd hpiv
  obtain ⟨n, r, hr, rfl⟩ :=
    exists_roots_of_radical_generator hsymm hpsd hcomm hPd hpiv hmon hdvd hrad
  have hhn : (∏ i ∈ Finset.range n, (X - C (r i))).natDegree = n := by
    rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range]
  have hP0 : P ≠ 0 := fun h0 => by
    rw [h0, degree_zero] at hPd; exact WithBot.bot_ne_coe hPd
  have hPnat : P.natDegree = d := natDegree_eq_of_degree_eq_some hPd
  have hnd : n ≤ d := by
    have := natDegree_le_of_dvd hdvd hP0
    rwa [hhn, hPnat] at this
  -- dominance `r_i ≥ γ_i²`, by the maximal violating index
  have hdom : ∀ i < n, ordSeq i ^ 2 ≤ r i := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i₀, hi₀n, hi₀⟩ := hcon
    set S := (Finset.range n).filter (fun i => r i < ordSeq i ^ 2) with hS
    have hSne : S.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi₀n, hi₀⟩⟩
    set k := S.max' hSne with hk
    have hkS : k ∈ S := S.max'_mem hSne
    rw [hS, Finset.mem_filter, Finset.mem_range] at hkS
    obtain ⟨hkn, hrk⟩ := hkS
    have habove : ∀ i, k < i → i < n → ordSeq i ^ 2 ≤ r i := fun i hki hin => by
      by_contra h'
      push Not at h'
      have := S.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin, h'⟩)
      omega
    set q : ℝ[X] := ∏ i ∈ Finset.range k, (X - C (ordSeq i ^ 2)) with hq
    have hqdeg : q.natDegree ≤ k := by
      rw [hq, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range]
    have hq0 : q ≠ 0 := (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (ordSeq i ^ 2)).ne_zero
    set g : ℝ[X] := q * ∏ i ∈ Finset.Ioo k n, (X - C (r i)) with hg
    obtain ⟨hray, hpos⟩ := rayleigh_le_of_roots hsymm hpsd hcomm hPd hpiv hr hdvd hrad hkn hqdeg
    have hGg := hpos hq0
    have hgprod : g = ∏ i ∈ Finset.range (n - 1),
        (X - C (if i < k then ordSeq i ^ 2 else r (i + 1))) := deflate_prod hkn
    have hgdeg : g.degree < (N - 1 : ℕ) := by
      rw [hgprod, degree_eq_natDegree (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _).ne_zero,
        natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range]
      exact_mod_cast (show n - 1 < N - 1 by omega)
    have hvan : ∀ ρ : nonTrivialZeroSet, (ρ : ℂ).im ^ 2 < ordSeq k ^ 2 →
        g.eval ((ρ : ℂ).im ^ 2) = 0 := by
      intro ρ hρ
      have habs : |(ρ : ℂ).im| < ordSeq k := abs_lt_of_sq_lt_sq hρ (ordSeq_pos k).le
      obtain ⟨j, hj, hjeq⟩ := exists_eq_ordSeq_of_lt k ρ habs
      have hsq : (ρ : ℂ).im ^ 2 = ordSeq j ^ 2 := by rw [← hjeq, sq_abs]
      rw [hg, eval_mul, hq, eval_prod, Finset.prod_eq_zero (Finset.mem_range.mpr hj)
        (by rw [eval_sub, eval_X, eval_C, hsq, sub_self]), zero_mul]
    have hdefl := mul_dot_le_of_eval_eq_zero hRH hL hgdeg hvan
    rw [hG, pencilForm_X_mul_self, pencilForm_apply'] at hray
    rw [hG, pencilForm_apply'] at hGg
    have hWv : ordSeq k ^ 2 * (vecOf L N g ⬝ᵥ vecOf L N g)
        < (fun i => om L N i ^ 2 * vecOf L N g i) ⬝ᵥ vecOf L N g := by
      have h1 := mul_lt_mul_of_pos_right hrk hGg
      have h2 : μ * (ordSeq k ^ 2 * (vecOf L N g ⬝ᵥ vecOf L N g))
          < μ * ((fun i => om L N i ^ 2 * vecOf L N g i) ⬝ᵥ vecOf L N g) := by
        nlinarith
      exact lt_of_mul_lt_mul_left h2 hμ.le
    have hgdom : Dominated N g := ⟨1, n - 1, fun i => if i < k then ordSeq i ^ 2 else r (i + 1),
      one_ne_zero, by omega, deflate_dominates ordSeq_sq_mono habove,
      by rw [C_1, one_mul]; exact hgprod⟩
    have henv := W2_dot_lt_of_LAT hL hLAT hgdom
    have hmono : ordSeq 0 ^ 2 ≤ ordSeq k ^ 2 := ordSeq_sq_mono (Nat.zero_le k)
    have hvv : 0 ≤ vecOf L N g ⬝ᵥ vecOf L N g := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' _
    nlinarith
  -- the radical is zero: `h` has degree `N − 1`
  have hhdeg : (∏ i ∈ Finset.range n, (X - C (r i))).natDegree = d := by
    by_contra hne
    have hlt : n < d := lt_of_le_of_ne hnd (by rw [← hhn]; exact hne)
    have hhdeg' : (∏ i ∈ Finset.range n, (X - C (r i))).degree < (d : WithBot ℕ) := by
      rw [degree_eq_natDegree hmon.ne_zero, hhn]; exact_mod_cast hlt
    have hK := (hrad _ hhdeg').mpr dvd_rfl
    have hAu : (MX L N - μ • (1 : Matrix (Idx N) (Idx N) ℝ)) *ᵥ
        vecOf L N (∏ i ∈ Finset.range n, (X - C (r i))) = 0 := by
      refine mulVec_eq_zero_of_perp (shift_symm hL μ) (negI_involutive N) (shift_negI hL μ)
        (shift_psd hbot) (y := om L N) (vecOf_negI _) (om_dotProduct_vecOf_eq_zero hhdeg')
        fun u' hu' hηu' => ?_
      obtain ⟨q', hq'N, rfl⟩ := exists_vecOf_eq hL.ne' hu'
      have hq'd := degree_lt_pred_of_om_dotProduct hL.ne' hq'N hηu'
      have h0 := hK q' hq'd
      rw [hsymm, hG, pencilForm_apply] at h0
      exact h0
    have hMu : MX L N *ᵥ vecOf L N (∏ i ∈ Finset.range n, (X - C (r i)))
        = μ • vecOf L N (∏ i ∈ Finset.range n, (X - C (r i))) := by
      rw [sub_smul_one_mulVec, sub_eq_zero] at hAu; exact hAu
    have hdefl := mul_dot_le_of_eval_eq_zero hRH hL hhdeg' (Λ := ordSeq 0 ^ 2) fun ρ hρ => by
      exfalso
      have h1 : ordSeq 0 ^ 2 ≤ (ρ : ℂ).im ^ 2 :=
        (pow_le_pow_left₀ (ordSeq_pos 0).le (ordSeq_zero_le_abs_im ρ) 2).trans_eq (sq_abs _)
      linarith
    rw [hMu, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hdefl
    have hudom : Dominated N (∏ i ∈ Finset.range n, (X - C (r i))) :=
      ⟨1, n, r, one_ne_zero, hnd, hdom, by rw [C_1, one_mul]⟩
    have henv := mul_lt_mul_of_pos_left (W2_dot_lt_of_LAT hL hLAT hudom) hμ
    nlinarith
  have hPeq : P = C P.leadingCoeff * ∏ i ∈ Finset.range n, (X - C (r i)) :=
    eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hmon hdvd (by rw [hPnat, hhdeg])
  have hPdom : Dominated N P :=
    ⟨P.leadingCoeff, n, r, leadingCoeff_ne_zero.mpr hP0, hnd, hdom, hPeq⟩
  by_cases hE : ∃ ξ' : Idx N → ℝ, (∀ i, ξ' (negI N i) = -ξ' i) ∧ MX L N *ᵥ ξ' = μ • ξ' ∧
      om L N ⬝ᵥ ξ' ≠ 0
  · have hMP := hPE hE
    have hΩ := dot_lt_of_LAT hL hLAT hPdom
    rw [← xdiv_vecOf hL.ne' hPN] at hΩ
    exact Cvs.StepA.OddBottomGapCriterion.oddBottomBelow_of_gap hL (c := 6.24) (by norm_num)
      (fun ρ => (Cvs.StepA.StepACriterion.lt_abs_im ρ).le) (vecOf_negI P) hMP hbot hΩ
  · exfalso
    have hηξ : om L N ⬝ᵥ ξ = 0 := by
      by_contra h'
      exact hE ⟨ξ, hξodd, hMξ, h'⟩
    obtain ⟨pξ, hpξN, hpξ⟩ := exists_vecOf_eq hL.ne' hξodd
    have hpξd := degree_lt_pred_of_om_dotProduct hL.ne' hpξN (by rw [hpξ]; exact hηξ)
    have hK : ∀ q : ℝ[X], q.degree < d → G pξ q = 0 := fun q _ => by
      rw [hG, pencilForm_apply', hpξ, Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm (MX_symm hL),
        hMξ, dotProduct_smul, smul_eq_mul, dotProduct_comm (vecOf L N q) ξ]
      ring
    have hdvd' := (hrad pξ hpξd).mp hK
    have hpξ0 : pξ = 0 := eq_zero_of_dvd_of_degree_lt hdvd' (by
      rw [degree_eq_natDegree hmon.ne_zero, hhdeg]; exact hpξd)
    rw [hpξ0, map_zero] at hpξ
    exact hξne hpξ.symm

end Cvs.Finite.OddDisplacementPencil
