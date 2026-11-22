import Mathlib
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.OneZeroSectorBottoms
import Cvs.StepA.SineModeOddTrial
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
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
# A top gap at a finite top set refutes step (a)

For zeros `S` at distance `δ` from the line, all others strictly closer, the sector bottoms of the
top block `∑_S m_ρ((∫ f u_ρ)² − (∫ f v_ρ)²)` sandwich `evLam` and the odd form up to `o(e^{δL})` at
`N = ⌈ΩL/2π⌉₊`; an odd bottom below the even one by `c·n^δ` at infinitely many `L = log n` refutes
step (a) at all large scales, and with it RH is equivalent to step (a).
-/

noncomputable section

open Real MeasureTheory Matrix Filter Topology Asymptotics

namespace Cvs.StepA.Edge.FiniteTopGap
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI mode_injective negI_involutive mode_negI)
open Cvs.StepA.OneZeroParitySectors (ue ve uo vo continuous_ue continuous_ve continuous_uo continuous_vo)
open Cvs.StepA.OneZeroSectorBottoms (lamO sigO)
open Cvs.StepA.SineModeOddTrial (trialBound sinCoef projDefect)

/-! ### A finite weighted block of rank-two terms -/

section Block

variable {ι : Type*} (L : ℝ) (s : Finset ι) (w : ι → ℝ) (z : ι → ℂ)

/-- The even form of a finite weighted block: `∑_{i ∈ s} wᵢ ((∫ f ue_{zᵢ})² − (∫ f ve_{zᵢ})²)`. -/
def blockE (f : ℝ → ℝ) : ℝ :=
  ∑ i ∈ s, w i * ((∫ t in -(L / 2)..L / 2, f t * ue (z i) t) ^ 2
    - (∫ t in -(L / 2)..L / 2, f t * ve (z i) t) ^ 2)

/-- The odd form of a finite weighted block: `∑_{i ∈ s} wᵢ ((∫ f uo_{zᵢ})² − (∫ f vo_{zᵢ})²)`. -/
def blockO (f : ℝ → ℝ) : ℝ :=
  ∑ i ∈ s, w i * ((∫ t in -(L / 2)..L / 2, f t * uo (z i) t) ^ 2
    - (∫ t in -(L / 2)..L / 2, f t * vo (z i) t) ^ 2)

/-- The Rayleigh quotients of the even block over even continuous profiles. -/
def rayE : Set ℝ :=
  {r | ∃ f : ℝ → ℝ, Continuous f ∧ (∀ t, f (-t) = f t) ∧ 0 < ∫ t in -(L / 2)..L / 2, f t ^ 2 ∧
    r = blockE L s w z f / ∫ t in -(L / 2)..L / 2, f t ^ 2}

/-- The Rayleigh quotients of the odd block over odd continuous profiles. -/
def rayO : Set ℝ :=
  {r | ∃ f : ℝ → ℝ, Continuous f ∧ (∀ t, f (-t) = -f t) ∧ 0 < ∫ t in -(L / 2)..L / 2, f t ^ 2 ∧
    r = blockO L s w z f / ∫ t in -(L / 2)..L / 2, f t ^ 2}

/-- The even bottom of the block. -/
def botE : ℝ := sInf (rayE L s w z)

/-- The odd bottom of the block. -/
def botO : ℝ := sInf (rayO L s w z)

variable {L s w z}

/-- Cauchy–Schwarz on the window, for continuous functions. -/
theorem window_sq_integral_mul_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ t in -(L / 2)..L / 2, f t * g t) ^ 2
      ≤ (∫ t in -(L / 2)..L / 2, f t ^ 2) * ∫ t in -(L / 2)..L / 2, g t ^ 2 := by
  have h := Cvs.StepA.OneZeroSectorBottoms.winForm_sq_le L ⟨f, hf⟩ ⟨g, hg⟩
  rw [Cvs.StepA.OneZeroParitySectors.winForm_sq, Cvs.StepA.OneZeroParitySectors.winForm_sq,
    Cvs.StepA.OneZeroParitySectors.winForm_apply] at h
  simpa only [ContinuousMap.coe_mk] using h

/-- The even block is at least `−(∑ wᵢ ∫ ve²)·∫ f²` for nonnegative weights. -/
theorem neg_mul_le_blockE (hw : ∀ i ∈ s, 0 ≤ w i) {f : ℝ → ℝ} (hf : Continuous f) :
    -((∑ i ∈ s, w i * ∫ t in -(L / 2)..L / 2, ve (z i) t ^ 2) * ∫ t in -(L / 2)..L / 2, f t ^ 2)
      ≤ blockE L s w z f := by
  unfold blockE
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have h := window_sq_integral_mul_le (L := L) hf (continuous_ve (z i))
  have hwi := hw i hi
  have h2 := mul_le_mul_of_nonneg_left h hwi
  nlinarith [mul_nonneg hwi (sq_nonneg (∫ t in -(L / 2)..L / 2, f t * ue (z i) t))]

/-- The odd block is at least `−(∑ wᵢ ∫ vo²)·∫ f²` for nonnegative weights. -/
theorem neg_mul_le_blockO (hw : ∀ i ∈ s, 0 ≤ w i) {f : ℝ → ℝ} (hf : Continuous f) :
    -((∑ i ∈ s, w i * ∫ t in -(L / 2)..L / 2, vo (z i) t ^ 2) * ∫ t in -(L / 2)..L / 2, f t ^ 2)
      ≤ blockO L s w z f := by
  unfold blockO
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have h := window_sq_integral_mul_le (L := L) hf (continuous_vo (z i))
  have hwi := hw i hi
  have h2 := mul_le_mul_of_nonneg_left h hwi
  nlinarith [mul_nonneg hwi (sq_nonneg (∫ t in -(L / 2)..L / 2, f t * uo (z i) t))]

/-- The even Rayleigh quotients of a block with nonnegative weights are bounded below. -/
theorem bddBelow_rayE (hw : ∀ i ∈ s, 0 ≤ w i) : BddBelow (rayE L s w z) := by
  refine ⟨-(∑ i ∈ s, w i * ∫ t in -(L / 2)..L / 2, ve (z i) t ^ 2), ?_⟩
  rintro r ⟨f, hf, -, hpos, rfl⟩
  rw [le_div_iff₀ hpos]
  have := neg_mul_le_blockE (L := L) (z := z) hw hf
  linarith

/-- The odd Rayleigh quotients of a block with nonnegative weights are bounded below. -/
theorem bddBelow_rayO (hw : ∀ i ∈ s, 0 ≤ w i) : BddBelow (rayO L s w z) := by
  refine ⟨-(∑ i ∈ s, w i * ∫ t in -(L / 2)..L / 2, vo (z i) t ^ 2), ?_⟩
  rintro r ⟨f, hf, -, hpos, rfl⟩
  rw [le_div_iff₀ hpos]
  have := neg_mul_le_blockO (L := L) (z := z) hw hf
  linarith

/-- For `L > 0` the even Rayleigh quotients are nonempty. -/
theorem nonempty_rayE (hL : 0 < L) : (rayE L s w z).Nonempty :=
  ⟨_, fun _ => 1, continuous_const, fun _ => rfl,
    Cvs.StepA.OneZeroSectorBottoms.integral_sq_pos hL continuous_const (t₀ := 0)
      ⟨by linarith, by linarith⟩ one_ne_zero, rfl⟩

/-- For `L > 0` the odd Rayleigh quotients are nonempty. -/
theorem nonempty_rayO (hL : 0 < L) : (rayO L s w z).Nonempty :=
  ⟨_, fun t => t, continuous_id, fun _ => rfl,
    Cvs.StepA.OneZeroSectorBottoms.integral_sq_pos hL continuous_id (t₀ := L / 4)
      ⟨by linarith, by linarith⟩ (by positivity), rfl⟩

/-- Above the odd bottom there is an odd continuous profile with a smaller quotient. -/
theorem exists_odd_lt (hL : 0 < L) {b : ℝ} (h : botO L s w z < b) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ t, f (-t) = -f t) ∧ 0 < ∫ t in -(L / 2)..L / 2, f t ^ 2 ∧
      blockO L s w z f < b * ∫ t in -(L / 2)..L / 2, f t ^ 2 := by
  obtain ⟨r, ⟨f, hf, hodd, hpos, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (nonempty_rayO hL) h
  exact ⟨f, hf, hodd, hpos, (div_lt_iff₀ hpos).mp hr⟩

/-! ### The even bottom of a block is nonpositive -/

/-- Some nonzero even polynomial of degree at most `2·#κ` is orthogonal on the window to `#κ` given
continuous functions. -/
theorem exists_even_poly_orth {κ : Type*} [Fintype κ] (L : ℝ) (g : κ → ℝ → ℝ)
    (hg : ∀ q, Continuous (g q)) :
    ∃ c : Fin (Fintype.card κ + 1) → ℝ, c ≠ 0 ∧
      ∀ q, ∫ t in -(L / 2)..L / 2, (∑ j, c j * t ^ (2 * (j : ℕ))) * g q t = 0 := by
  set A : Matrix κ (Fin (Fintype.card κ + 1)) ℝ :=
    fun q j => ∫ t in -(L / 2)..L / 2, t ^ (2 * (j : ℕ)) * g q t with hA
  have hker : LinearMap.ker (Matrix.mulVecLin A) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨c, hc0, fun q => ?_⟩
  have hq := congrFun (LinearMap.mem_ker.mp hc) q
  rw [Matrix.mulVecLin_apply, Pi.zero_apply, Matrix.mulVec, dotProduct] at hq
  simp_rw [Finset.sum_mul]
  rw [← hq, intervalIntegral.integral_finsetSum fun j _ =>
    ((by fun_prop : Continuous fun t => c j * t ^ (2 * (j : ℕ)) * g q t).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hA, mul_assoc]
  rw [intervalIntegral.integral_const_mul, mul_comm]

/-- A nonzero even polynomial is nonzero somewhere in every open interval. -/
theorem exists_mem_Ioo_evenPoly_ne_zero {n : ℕ} {c : Fin (n + 1) → ℝ} (hc : c ≠ 0) {a b : ℝ}
    (hab : a < b) : ∃ t ∈ Set.Ioo a b, ∑ j, c j * t ^ (2 * (j : ℕ)) ≠ 0 := by
  set P : Polynomial ℝ := ∑ j, Polynomial.C (c j) * Polynomial.X ^ (2 * (j : ℕ)) with hPdef
  have hP : ∀ t, P.eval t = ∑ j, c j * t ^ (2 * (j : ℕ)) := by
    intro t; simp [hPdef, Polynomial.eval_finsetSum]
  have hP0 : P ≠ 0 := by
    obtain ⟨j₀, hj₀⟩ : ∃ j, c j ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (funext h)
    intro h0
    have h1 := congrArg (fun p : Polynomial ℝ => p.coeff (2 * (j₀ : ℕ))) h0
    simp only [hPdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single j₀ (fun j _ hj => by
      rw [ite_eq_right]
      intro h2
      exact hj (Fin.ext (by omega))) (fun h => absurd (Finset.mem_univ j₀) h), ite_eq_left rfl] at h1
    exact hj₀ h1
  by_contra h
  push Not at h
  apply hP0
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono (fun t ht => ?_) (Set.Ioo_infinite hab)
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hP]
  exact h t ht

/-- **The even bottom of a block with nonnegative weights is nonpositive**, for `L > 0`. -/
theorem botE_nonpos (hL : 0 < L) (hw : ∀ i ∈ s, 0 ≤ w i) : botE L s w z ≤ 0 := by
  obtain ⟨c, hc, horth⟩ := exists_even_poly_orth L (fun i : s => ue (z i))
    (fun i => continuous_ue _)
  set f : ℝ → ℝ := fun t => ∑ j, c j * t ^ (2 * (j : ℕ)) with hfdef
  have hf : Continuous f := by rw [hfdef]; fun_prop
  have heven : ∀ t, f (-t) = f t := fun t => by
    simp only [hfdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_mul, pow_mul, neg_sq]
  obtain ⟨t₀, ht₀, hne⟩ :=
    exists_mem_Ioo_evenPoly_ne_zero hc (a := -(L / 2)) (b := L / 2) (by linarith)
  have hpos := Cvs.StepA.OneZeroSectorBottoms.integral_sq_pos hL hf ht₀ hne
  refine (csInf_le (bddBelow_rayE hw) ⟨f, hf, heven, hpos, rfl⟩).trans ?_
  refine div_nonpos_of_nonpos_of_nonneg ?_ hpos.le
  unfold blockE
  refine Finset.sum_nonpos fun i hi => ?_
  have h0 : ∫ t in -(L / 2)..L / 2, f t * ue (z i) t = 0 := horth ⟨i, hi⟩
  rw [h0]
  exact mul_nonpos_of_nonneg_of_nonpos (hw i hi)
    (by nlinarith [sq_nonneg (∫ t in -(L / 2)..L / 2, f t * ve (z i) t)])

/-! ### The odd trial for a block -/

/-- **The odd trial for a block**: for `L ≥ 0`, nonnegative weights and a continuous `φ` with
`∫ φ² > 0` and `blockO φ ≤ μ ∫ φ²`, some odd `o` has `L ‖o‖² ≤ 1` and
`blockO(sg o) ≤ μ + ∑ wᵢ (trialBound − lamO)(zᵢ)`. -/
theorem exists_odd_trial_block (hL : 0 ≤ L) (N : ℕ) (hw : ∀ i ∈ s, 0 ≤ w i) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hn : 0 < ∫ t in -(L / 2)..L / 2, φ t ^ 2) {μ : ℝ}
    (hμ : blockO L s w z φ ≤ μ * ∫ t in -(L / 2)..L / 2, φ t ^ 2) :
    ∃ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) ∧ L * (o ⬝ᵥ o) ≤ 1 ∧
      blockO L s w z (fun t => Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (t + L / 2))
        ≤ μ + ∑ i ∈ s, w i * (trialBound L N (z i) - lamO L (z i)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c ^ 2 * ∫ t in -(L / 2)..L / 2, φ t ^ 2 = 1 :=
    ⟨(√(∫ t in -(L / 2)..L / 2, φ t ^ 2))⁻¹, by
      rw [inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']⟩
  have hψc : Continuous fun t => c * φ t := continuous_const.mul hφ
  have hψn : ∫ t in -(L / 2)..L / 2, (c * φ t) ^ 2 = 1 := by
    simp only [mul_pow]
    rw [intervalIntegral.integral_const_mul, hc]
  have hpair : ∀ g : ℝ → ℝ,
      ∫ t in -(L / 2)..L / 2, c * φ t * g t = c * ∫ t in -(L / 2)..L / 2, φ t * g t := by
    intro g
    simp only [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
  refine ⟨sinCoef L N fun t => c * φ t, Cvs.StepA.SineModeOddTrial.sinCoef_odd L N _, ?_, ?_⟩
  · have h1 := Cvs.StepA.SineModeOddTrial.projDefect_nonneg hL N hψc
    rw [projDefect, hψn] at h1
    linarith
  · have hterm : ∀ i ∈ s,
        w i * ((∫ t in -(L / 2)..L / 2, Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N)
              (sinCoef L N fun t => c * φ t) (t + L / 2) * uo (z i) t) ^ 2
          - (∫ t in -(L / 2)..L / 2, Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N)
              (sinCoef L N fun t => c * φ t) (t + L / 2) * vo (z i) t) ^ 2)
        ≤ c ^ 2 * (w i * ((∫ t in -(L / 2)..L / 2, φ t * uo (z i) t) ^ 2
            - (∫ t in -(L / 2)..L / 2, φ t * vo (z i) t) ^ 2))
          + w i * (trialBound L N (z i) - lamO L (z i)) := by
      intro i hi
      have h := Cvs.StepA.SineModeOddTrial.sq_sub_sq_sinCoef_le hL N hψc (continuous_uo (z i))
        (continuous_vo (z i))
      rw [hψn, one_mul, hpair, hpair] at h
      have herr : 2 * √(((∫ t in -(L / 2)..L / 2, uo (z i) t ^ 2)
            + ∫ t in -(L / 2)..L / 2, vo (z i) t ^ 2)
            * (projDefect L N (uo (z i)) + projDefect L N (vo (z i))))
          + (projDefect L N (uo (z i)) + projDefect L N (vo (z i)))
          = trialBound L N (z i) - lamO L (z i) := by
        unfold trialBound sigO
        ring
      rw [herr] at h
      have h2 := mul_le_mul_of_nonneg_left h (hw i hi)
      nlinarith
    calc blockO L s w z (fun t => Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N)
            (sinCoef L N fun t => c * φ t) (t + L / 2))
        ≤ ∑ i ∈ s, (c ^ 2 * (w i * ((∫ t in -(L / 2)..L / 2, φ t * uo (z i) t) ^ 2
            - (∫ t in -(L / 2)..L / 2, φ t * vo (z i) t) ^ 2))
          + w i * (trialBound L N (z i) - lamO L (z i))) := Finset.sum_le_sum hterm
      _ = c ^ 2 * blockO L s w z φ + ∑ i ∈ s, w i * (trialBound L N (z i) - lamO L (z i)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
      _ ≤ μ + ∑ i ∈ s, w i * (trialBound L N (z i) - lamO L (z i)) := by
          have h3 := mul_le_mul_of_nonneg_left hμ (sq_nonneg c)
          have h4 : c ^ 2 * (μ * ∫ t in -(L / 2)..L / 2, φ t ^ 2) = μ := by
            rw [show c ^ 2 * (μ * ∫ t in -(L / 2)..L / 2, φ t ^ 2)
              = μ * (c ^ 2 * ∫ t in -(L / 2)..L / 2, φ t ^ 2) by ring, hc, mul_one]
          linarith

end Block

/-! ### The top block of a finite set of zeros -/

/-- The multiplicity of a nontrivial zero, as a real weight. -/
abbrev mult (ρ : nonTrivialZeroSet) : ℝ := (Cvs.Criterion.divisorWeight ρ : ℝ)

/-- The multiplicities are nonnegative. -/
theorem mult_nonneg (ρ : nonTrivialZeroSet) : 0 ≤ mult ρ := Nat.cast_nonneg _

/-- The even bottom of the top block of a finite set `S` of zeros at scale `L`. -/
def topBotE (L : ℝ) (S : Finset nonTrivialZeroSet) : ℝ := botE L S mult Cvs.ZeroCounting.zPoint

/-- The odd bottom of the top block of a finite set `S` of zeros at scale `L`. -/
def topBotO (L : ℝ) (S : Finset nonTrivialZeroSet) : ℝ := botO L S mult Cvs.ZeroCounting.zPoint

/-- A finite top set: every zero in `S` at distance `δ > 0` from the line, every other strictly
closer. -/
def FiniteTop (S : Finset nonTrivialZeroSet) (δ : ℝ) : Prop :=
  0 < δ ∧ S.Nonempty ∧ (∀ ρ ∈ S, |Cvs.GaussKernel.del ρ| = δ) ∧
    ∀ ρ, ρ ∉ S → |Cvs.GaussKernel.del ρ| < δ

/-- The even bottom of the top block is nonpositive for `L > 0`. -/
theorem topBotE_nonpos {L : ℝ} (hL : 0 < L) (S : Finset nonTrivialZeroSet) : topBotE L S ≤ 0 :=
  botE_nonpos hL fun ρ _ => mult_nonneg ρ

/-! ### Frequently no step (a) -/

/-! ### No step (a) at all large scales, and the criterion -/

end Cvs.StepA.Edge.FiniteTopGap
