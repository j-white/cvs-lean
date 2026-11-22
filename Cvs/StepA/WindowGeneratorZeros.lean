import Mathlib
import Cvs.Finite.CosineModeTransform
import Cvs.Finite.CosineModeTransformBounds
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EvenBilinearZeroSide
import Cvs.Finite.EvenPairCancellation
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.ModeTransformEnvelopes
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowMatrixClosedForm
import Cvs.Finite.ZeroSideGramMatrix
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
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
# The window generator over the zeros

The constant column of the window matrix is `−gen(m)/(2πm)` and its even bilinear zero side has the
term `−8 sin²(Lz/2)/(ω_m² − z²)` at every `z ∈ ℂ`, so
`gen(m) = (8πm/L)·∑_ρ m_ρ Re[sin²(L z_ρ/2)/(ω_m² − z_ρ²)]` at every integer mode, with no condition on the zeros.
-/

noncomputable section

open Real Matrix Filter Topology Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.StepA.WindowGeneratorZeros
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI negI_involutive mode_negI mode_injective)

section General

variable {ι : Type*} [Fintype ι]

/-- The window transform of a cosine polynomial is the coefficient sum of its modes' transforms. -/
theorem windowTransform_cosPoly (L : ℝ) (mode : ι → ℤ) (x : ι → ℝ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode x)) ξ
      = ∑ i, (x i : ℂ) * Cvs.Finite.ModeTransformEnvelopes.Wm L (mode i) ξ :=
  Cvs.Finite.CosineModeTransformBounds.windowTransform_sum_cf L x
    (fun i y => Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)) (fun i => by fun_prop) ξ

/-- For any `x`, `y` on any mode set, the zero series of `Re[W_x(z)W_y(−z) + W_y(z)W_x(−z)]` is
summable. -/
theorem summable_bilinear_zeroSide {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (x y : ι → ℝ) :
    Summable fun rho : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight rho : ℝ)
      * (Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode x))
            (Cvs.ZeroCounting.zPoint rho)
          * Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode y))
            (-Cvs.ZeroCounting.zPoint rho)
        + Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode y))
            (Cvs.ZeroCounting.zPoint rho)
          * Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode x))
            (-Cvs.ZeroCounting.zPoint rho)).re := by
  set W : (ι → ℝ) → ℂ → ℂ := fun v =>
    Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode v)) with hW
  have hWadd : ∀ ξ, W (x + y) ξ = W x ξ + W y ξ := by
    intro ξ
    simp only [hW, windowTransform_cosPoly, Pi.add_apply, Complex.ofReal_add, add_mul,
      Finset.sum_add_distrib]
  have hS : ∀ v : ι → ℝ, Summable fun rho : nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (W v (Cvs.ZeroCounting.zPoint rho) * W v (-Cvs.ZeroCounting.zPoint rho)).re := by
    intro v
    have h := Cvs.Finite.EvenBilinearZeroSide.summable_zeroSide_cosPoly hL mode v
    unfold Cvs.Detection.sqTransform at h
    exact h
  refine (((hS (x + y)).sub (hS x)).sub (hS y)).congr fun rho => ?_
  simp only [hWadd]
  rw [← mul_sub, ← mul_sub, ← Complex.sub_re, ← Complex.sub_re]
  congr 2
  ring

/-- For even `x`, `y` on an injective symmetric mode set, `2L·xᵀMy` is the sum over the zeros of
`m_ρ Re[W_x(z_ρ)W_y(−z_ρ) + W_y(z_ρ)W_x(−z_ρ)]`. -/
theorem two_mul_bilinear_eq_zeroSide [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {x y : ι → ℝ} (hx : ∀ i, x (neg i) = x i)
    (hy : ∀ i, y (neg i) = y i) :
    2 * L * (x ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ y))
      = ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
          * (Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode x))
                (Cvs.ZeroCounting.zPoint rho)
              * Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode y))
                (-Cvs.ZeroCounting.zPoint rho)
            + Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode y))
                (Cvs.ZeroCounting.zPoint rho)
              * Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode x))
                (-Cvs.ZeroCounting.zPoint rho)).re := by
  set M := Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode with hM
  set W : (ι → ℝ) → ℂ → ℂ := fun v =>
    Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode v)) with hW
  have hWadd : ∀ ξ, W (x + y) ξ = W x ξ + W y ξ := by
    intro ξ
    simp only [hW, windowTransform_cosPoly, Pi.add_apply, Complex.ofReal_add, add_mul,
      Finset.sum_add_distrib]
  have hQ : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) →
      ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
          * (W v (Cvs.ZeroCounting.zPoint rho) * W v (-Cvs.ZeroCounting.zPoint rho)).re
        = L * (v ⬝ᵥ (M *ᵥ v)) := by
    intro v hv
    have h := Cvs.Finite.ZeroSideGramMatrix.zeroSide_eq_ddMatrix hL hinj hinv hmode hv 0 0
    unfold Cvs.ZeroCounting.kernelZeroSide Cvs.Detection.sqTransform at h
    exact h
  have hS : ∀ v : ι → ℝ, Summable fun rho : nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (W v (Cvs.ZeroCounting.zPoint rho) * W v (-Cvs.ZeroCounting.zPoint rho)).re := by
    intro v
    have h := Cvs.Finite.EvenBilinearZeroSide.summable_zeroSide_cosPoly hL mode v
    unfold Cvs.Detection.sqTransform at h
    exact h
  have hxy : ∀ i, (x + y) (neg i) = (x + y) i := fun i => by simp [hx, hy]
  have hsymm : y ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (M *ᵥ y) := by
    have hMT : Mᵀ = M := by
      ext i j; rw [Matrix.transpose_apply, hM]; exact Cvs.Finite.TruncationQuadraticForm.M_symm hL _ _ hinj j i
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hMT, dotProduct_comm]
  have hexp : (x + y) ⬝ᵥ (M *ᵥ (x + y))
      = x ⬝ᵥ (M *ᵥ x) + y ⬝ᵥ (M *ᵥ y) + 2 * (x ⬝ᵥ (M *ᵥ y)) := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsymm]; ring
  have hpt : ∀ rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
      * (W x (Cvs.ZeroCounting.zPoint rho) * W y (-Cvs.ZeroCounting.zPoint rho)
        + W y (Cvs.ZeroCounting.zPoint rho) * W x (-Cvs.ZeroCounting.zPoint rho)).re
      = (Cvs.Criterion.divisorWeight rho : ℝ)
          * (W (x + y) (Cvs.ZeroCounting.zPoint rho) * W (x + y) (-Cvs.ZeroCounting.zPoint rho)).re
        - (Cvs.Criterion.divisorWeight rho : ℝ)
          * (W x (Cvs.ZeroCounting.zPoint rho) * W x (-Cvs.ZeroCounting.zPoint rho)).re
        - (Cvs.Criterion.divisorWeight rho : ℝ)
          * (W y (Cvs.ZeroCounting.zPoint rho) * W y (-Cvs.ZeroCounting.zPoint rho)).re := by
    intro rho
    rw [hWadd, hWadd, ← mul_sub, ← mul_sub, ← Complex.sub_re, ← Complex.sub_re]
    congr 2
    ring
  rw [tsum_congr hpt, ((hS (x + y)).sub (hS x)).tsum_sub (hS y),
    (hS (x + y)).tsum_sub (hS x), hQ _ hxy, hQ x hx, hQ y hy, hexp]
  ring

end General

/-- A cosine mode's window transform is even in the mode. -/
theorem Wm_neg (L : ℝ) (m : ℤ) (ξ : ℂ) :
    Cvs.Finite.ModeTransformEnvelopes.Wm L (-m) ξ = Cvs.Finite.ModeTransformEnvelopes.Wm L m ξ := by
  unfold Cvs.Finite.ModeTransformEnvelopes.Wm
  have hf : (fun y : ℝ => Real.cos (2 * π * ((-m : ℤ) : ℝ) / L * y))
      = fun y : ℝ => Real.cos (2 * π * (m : ℝ) / L * y) := by
    funext y
    rw [Int.cast_neg, show 2 * π * -(m : ℝ) / L * y = -(2 * π * m / L * y) by ring, Real.cos_neg]
  rw [hf]

/-- Away from the origin the constant mode's window transform is `−iz(e^{−iLz} − 1)/(−z²)`. -/
theorem Wm_zero_eq {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z ≠ 0) :
    Cvs.Finite.ModeTransformEnvelopes.Wm L 0 z
      = -Complex.I * z * (Complex.exp (-((L : ℂ) * z) * Complex.I) - 1) / (-(z ^ 2)) := by
  have hξ : ((2 * π * ((0 : ℤ) : ℝ) / L : ℝ) : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
    simp only [Int.cast_zero, mul_zero, zero_div, Complex.ofReal_zero]
    simpa using pow_ne_zero 2 hz
  have h := Cvs.Finite.CosineModeTransform.windowTransform_cos_eq_of_int hL 0 hξ
  unfold Cvs.Finite.ModeTransformEnvelopes.Wm
  rw [h]
  simp

/-- For `m ≠ 0` and every `z ∈ ℂ`, `W_m(z)W_0(−z) + W_0(z)W_m(−z) = −8 sin²(Lz/2)/(ω_m² − z²)`. -/
theorem Wm_cross_eq {L : ℝ} (hL : 0 < L) {m : ℤ} (hm : m ≠ 0) (z : ℂ) :
    Cvs.Finite.ModeTransformEnvelopes.Wm L m z * Cvs.Finite.ModeTransformEnvelopes.Wm L 0 (-z)
        + Cvs.Finite.ModeTransformEnvelopes.Wm L 0 z * Cvs.Finite.ModeTransformEnvelopes.Wm L m (-z)
      = -8 * Complex.sin ((L : ℂ) * z / 2) ^ 2
          / (((2 * π * m / L : ℝ) : ℂ) ^ 2 - z ^ 2) := by
  set ω : ℝ := 2 * π * m / L with hω
  have hω0 : ω ≠ 0 := by
    rw [hω]
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have := Real.pi_pos
    positivity
  have hLω : Complex.exp (-((L : ℂ) * (ω : ℂ)) * Complex.I) = 1 := by
    have : -((L : ℂ) * (ω : ℂ)) * Complex.I = ((-m : ℤ) : ℂ) * (2 * π * Complex.I) := by
      have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      rw [hω]; push_cast; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hW0 : ∀ ξ : ℂ, ξ ≠ 0 → Cvs.Finite.ModeTransformEnvelopes.Wm L 0 ξ
      = -Complex.I * ξ * (Complex.exp (-((L : ℂ) * ξ) * Complex.I) - 1) / (-(ξ ^ 2)) :=
    fun ξ hξ => Wm_zero_eq hL hξ
  rcases eq_or_ne z 0 with rfl | hz
  · have hm0 : ((ω : ℝ) : ℂ) ^ 2 - (0 : ℂ) ^ 2 ≠ 0 := by
      simpa using pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hω0)
    have h := Cvs.Finite.CosineModeTransform.windowTransform_cos_eq_of_int hL m hm0
    have hWm : Cvs.Finite.ModeTransformEnvelopes.Wm L m 0 = 0 := by
      unfold Cvs.Finite.ModeTransformEnvelopes.Wm; rw [h]; simp
    simp [hWm]
  rcases eq_or_ne (((ω : ℝ) : ℂ) ^ 2 - z ^ 2) 0 with hres | hres
  · rw [hres, div_zero]
    have hz2 : z = (ω : ℂ) ∨ z = -(ω : ℂ) := by
      have : ((ω : ℂ) - z) * ((ω : ℂ) + z) = 0 := by rw [← hres]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (sub_eq_zero.mp h).symm
      · exact Or.inr (by linear_combination h)
    have hexp1 : Complex.exp (-((L : ℂ) * z) * Complex.I) = 1 := by
      rcases hz2 with rfl | rfl
      · exact hLω
      · have : -((L : ℂ) * -(ω : ℂ)) * Complex.I = -(-((L : ℂ) * (ω : ℂ)) * Complex.I) := by ring
        rw [this, Complex.exp_neg, hLω, inv_one]
    have hexp2 : Complex.exp (-((L : ℂ) * -z) * Complex.I) = 1 := by
      have : -((L : ℂ) * -z) * Complex.I = -(-((L : ℂ) * z) * Complex.I) := by ring
      rw [this, Complex.exp_neg, hexp1, inv_one]
    rw [hW0 z hz, hW0 (-z) (neg_ne_zero.mpr hz), hexp1, hexp2]
    simp
  · have hres' : ((ω : ℝ) : ℂ) ^ 2 - (-z) ^ 2 ≠ 0 := by rwa [neg_sq]
    have h1 := Cvs.Finite.CosineModeTransform.windowTransform_cos_eq_of_int hL m hres
    have h2 := Cvs.Finite.CosineModeTransform.windowTransform_cos_eq_of_int hL m hres'
    have hz' : -z ≠ 0 := neg_ne_zero.mpr hz
    unfold Cvs.Finite.ModeTransformEnvelopes.Wm at *
    rw [h1, h2, hW0 z hz, hW0 (-z) hz']
    set A := Complex.exp (-((L : ℂ) * z) * Complex.I) with hA
    have hB : Complex.exp (-((L : ℂ) * -z) * Complex.I) = Complex.exp (((L : ℂ) * z) * Complex.I) := by
      ring_nf
    rw [hB]
    set B := Complex.exp (((L : ℂ) * z) * Complex.I) with hBdef
    have hAB : (A - 1) * (B - 1) = 4 * Complex.sin ((L : ℂ) * z / 2) ^ 2 := by
      have hprod : A * B = 1 := by
        rw [hA, hBdef, ← Complex.exp_add]; ring_nf; exact Complex.exp_zero
      have hcos : A + B = 2 * Complex.cos ((L : ℂ) * z) := by
        rw [hA, hBdef, Complex.two_cos]; ring_nf
      have hsin : Complex.cos ((L : ℂ) * z) = 1 - 2 * Complex.sin ((L : ℂ) * z / 2) ^ 2 := by
        have := Complex.cos_two_mul ((L : ℂ) * z / 2)
        rw [show 2 * ((L : ℂ) * z / 2) = (L : ℂ) * z by ring] at this
        rw [this, Complex.cos_sq']
        ring
      have e1 : (A - 1) * (B - 1) = A * B - (A + B) + 1 := by ring
      rw [e1, hprod, hcos, hsin]
      ring
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
    have hres2 : ((2 * π * m / L : ℝ) : ℂ) ^ 2 - z ^ 2 ≠ 0 := hres
    rw [show -8 * Complex.sin ((L : ℂ) * z / 2) ^ 2 = -2 * (4 * Complex.sin ((L : ℂ) * z / 2) ^ 2)
      by ring, ← hAB, neg_sq]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    have hnz : -(z ^ 2) ≠ 0 := neg_ne_zero.mpr hz2
    have key1 : ∀ a b D : ℂ, D ≠ 0 →
        (-Complex.I * z * a / D) * (-Complex.I * -z * b / -(z ^ 2)) = -(a * b) / D := by
      intro a b D hD
      rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hD hnz) hD]
      linear_combination (-z ^ 2 * a * b * D) * hI
    have key2 : ∀ a b D : ℂ, D ≠ 0 →
        (-Complex.I * z * a / -(z ^ 2)) * (-Complex.I * -z * b / D) = -(a * b) / D := by
      intro a b D hD
      rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hnz hD) hD]
      linear_combination (-z ^ 2 * a * b * D) * hI
    rw [key1 _ _ _ hres2, key2 _ _ _ hres2]
    ring

/-- The index of the mode `m ≥ 1` in `Idx m`. -/
def topIdx (m : ℕ) (hm : 0 < m) : Idx m := some (⟨m - 1, by omega⟩, true)

/-- The mode at `topIdx m` is `m`. -/
theorem mode_topIdx (m : ℕ) (hm : 0 < m) : mode m (topIdx m hm) = m := by
  simp only [topIdx, Cvs.Finite.SymmetricModeSet.mode, ite_true]
  push_cast [Nat.cast_sub hm]
  ring

/-- `∑ₖ [k = i]·f k = f i`, through the real-to-complex cast. -/
theorem sum_single_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (i : κ) (f : κ → ℂ) :
    ∑ k, (((Pi.single i (1 : ℝ) : κ → ℝ) k : ℝ) : ℂ) * f k = f i := by
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- A unit vector plus its mirror image is even. -/
theorem single_add_single_even {κ : Type*} [DecidableEq κ] {neg : κ → κ}
    (hinv : Function.Involutive neg) (i k : κ) :
    (Pi.single i (1 : ℝ) + Pi.single (neg i) (1 : ℝ) : κ → ℝ) (neg k)
      = (Pi.single i (1 : ℝ) + Pi.single (neg i) (1 : ℝ) : κ → ℝ) k := by
  have hiff : ∀ j, neg k = j ↔ k = neg j :=
    fun j => ⟨fun h => by rw [← h, hinv], fun h => by rw [h, hinv]⟩
  simp only [Pi.add_apply, Pi.single_apply, hiff, hinv i]
  ring

/-- For `m ≠ 0`, the zero series `∑_ρ m_ρ Re[sin²(L z_ρ/2)/(ω_m² − z_ρ²)]` is summable. -/
theorem summable_genTerm {L : ℝ} (hL : 0 < L) {m : ℤ} (hm : m ≠ 0) :
    Summable fun rho : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight rho : ℝ)
      * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2
          / (((2 * π * m / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re := by
  set md : Bool → ℤ := fun b => if b then m else 0 with hmd
  have h := summable_bilinear_zeroSide hL md (Pi.single true 1) (Pi.single false 1)
  have hx : ∀ ξ, Cvs.Detection.windowTransform L
      (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L md (Pi.single true 1))) ξ
        = Cvs.Finite.ModeTransformEnvelopes.Wm L m ξ := by
    intro ξ
    rw [windowTransform_cosPoly, sum_single_mul]
    rfl
  have hy : ∀ ξ, Cvs.Detection.windowTransform L
      (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L md (Pi.single false 1))) ξ
        = Cvs.Finite.ModeTransformEnvelopes.Wm L 0 ξ := by
    intro ξ
    rw [windowTransform_cosPoly, sum_single_mul]
    rfl
  simp only [hx, hy, Wm_cross_eq hL hm] at h
  refine (h.mul_left (-1 / 8)).congr fun rho => ?_
  rw [mul_div_assoc, show (-8 : ℂ) = ((-8 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  ring

/-- **The window generator over the zeros**: for `m ≥ 1`,
`gen(m) = (8πm/L)·∑_ρ m_ρ Re[sin²(L z_ρ/2)/(ω_m² − z_ρ²)]`. -/
theorem gen_eq_zeroSide {L : ℝ} (hL : 0 < L) {m : ℕ} (hm : 0 < m) :
    Cvs.Finite.WindowMatrixClosedForm.gen ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L m
      = 8 * π * m / L * ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
          * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2
              / (((2 * π * m / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re := by
  set i := topIdx m hm with hi
  set e : Idx m → ℝ := Pi.single i 1 + Pi.single (negI m i) 1 with he
  set e0 : Idx m → ℝ := Pi.single none 1 with he0
  have hinv := negI_involutive m
  have heven : ∀ k, e (negI m k) = e k := single_add_single_even hinv i
  have heven0 : ∀ k, e0 (negI m k) = e0 k := by
    intro k
    have hiff : negI m k = none ↔ k = none := by
      constructor
      · intro h; rw [← hinv k, h]; rfl
      · rintro rfl; rfl
    simp only [he0, Pi.single_apply, hiff]
  have hmi : mode m i = m := mode_topIdx m hm
  have hmi' : mode m (negI m i) = -m := by rw [mode_negI, hmi]
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmat : e ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode m) *ᵥ e0)
      = -Cvs.Finite.WindowMatrixClosedForm.gen ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L m / (π * m) := by
    rw [he0, Matrix.mulVec_single_one, he, add_dotProduct, single_one_dotProduct,
      single_one_dotProduct]
    simp only [Matrix.col_apply]
    rw [Cvs.Finite.EvenPairCancellation.M_apply_none_closed hL _ _ m (by rw [hmi]; exact hm0),
      Cvs.Finite.EvenPairCancellation.M_apply_none_closed hL _ _ m (by rw [hmi']; exact neg_ne_zero.mpr hm0),
      hmi, hmi', Cvs.Finite.EvenPairCancellation.gen_neg]
    have hπ : π ≠ 0 := Real.pi_ne_zero
    have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
    ring
  have hWe : ∀ ξ, Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode m) e)) ξ
      = 2 * Cvs.Finite.ModeTransformEnvelopes.Wm L m ξ := by
    intro ξ
    rw [windowTransform_cosPoly, he]
    simp only [Pi.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, sum_single_mul,
      hmi, hmi', Wm_neg]
    ring
  have hWe0 : ∀ ξ, Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode m) e0)) ξ
      = Cvs.Finite.ModeTransformEnvelopes.Wm L 0 ξ := by
    intro ξ
    rw [windowTransform_cosPoly, he0, sum_single_mul]
    rfl
  have hB := two_mul_bilinear_eq_zeroSide hL (mode_injective m) hinv (mode_negI m) heven heven0
  rw [hmat] at hB
  simp only [hWe, hWe0] at hB
  have hpt : ∀ rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
      * (2 * Cvs.Finite.ModeTransformEnvelopes.Wm L m (Cvs.ZeroCounting.zPoint rho)
            * Cvs.Finite.ModeTransformEnvelopes.Wm L 0 (-Cvs.ZeroCounting.zPoint rho)
          + Cvs.Finite.ModeTransformEnvelopes.Wm L 0 (Cvs.ZeroCounting.zPoint rho)
            * (2 * Cvs.Finite.ModeTransformEnvelopes.Wm L m (-Cvs.ZeroCounting.zPoint rho))).re
      = -16 * ((Cvs.Criterion.divisorWeight rho : ℝ)
          * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2
              / (((2 * π * m / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) := by
    intro rho
    have hc := Wm_cross_eq hL hm0 (Cvs.ZeroCounting.zPoint rho)
    push_cast at hc ⊢
    rw [show 2 * Cvs.Finite.ModeTransformEnvelopes.Wm L m (Cvs.ZeroCounting.zPoint rho)
            * Cvs.Finite.ModeTransformEnvelopes.Wm L 0 (-Cvs.ZeroCounting.zPoint rho)
          + Cvs.Finite.ModeTransformEnvelopes.Wm L 0 (Cvs.ZeroCounting.zPoint rho)
            * (2 * Cvs.Finite.ModeTransformEnvelopes.Wm L m (-Cvs.ZeroCounting.zPoint rho))
        = 2 * (Cvs.Finite.ModeTransformEnvelopes.Wm L m (Cvs.ZeroCounting.zPoint rho)
            * Cvs.Finite.ModeTransformEnvelopes.Wm L 0 (-Cvs.ZeroCounting.zPoint rho)
          + Cvs.Finite.ModeTransformEnvelopes.Wm L 0 (Cvs.ZeroCounting.zPoint rho)
            * Cvs.Finite.ModeTransformEnvelopes.Wm L m (-Cvs.ZeroCounting.zPoint rho)) by ring, hc]
    rw [show (2 : ℂ) * (-8 * Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2
          / ((2 * (π : ℂ) * (m : ℂ) / (L : ℂ)) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2))
        = ((-16 : ℝ) : ℂ) * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2
          / ((2 * (π : ℂ) * (m : ℂ) / (L : ℂ)) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) by
        push_cast; ring, Complex.re_ofReal_mul]
    ring
  rw [tsum_congr hpt, tsum_mul_left] at hB
  have hL0 : L ≠ 0 := hL.ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp at hB ⊢
  linarith

/-- **The window generator over the zeros, at every integer mode**:
`gen(m) = (8πm/L)·∑_ρ m_ρ Re[sin²(L z_ρ/2)/(ω_m² − z_ρ²)]`. -/
theorem gen_eq_zeroSide_int {L : ℝ} (hL : 0 < L) (m : ℤ) :
    Cvs.Finite.WindowMatrixClosedForm.gen ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L m
      = 8 * π * m / L * ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
          * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2
              / (((2 * π * m / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Cvs.Finite.EvenPairCancellation.gen_zero]
    · exact_mod_cast gen_eq_zeroSide hL hn
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Cvs.Finite.EvenPairCancellation.gen_zero]
    · rw [Cvs.Finite.EvenPairCancellation.gen_neg, gen_eq_zeroSide hL hn]
      have hsq : (((2 * π * ((-(n : ℤ) : ℤ) : ℝ) / L : ℝ) : ℂ)) ^ 2
          = (((2 * π * (n : ℝ) / L : ℝ) : ℂ)) ^ 2 := by push_cast; ring
      simp only [hsq]
      push_cast
      ring

end Cvs.StepA.WindowGeneratorZeros
