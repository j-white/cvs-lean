import Mathlib
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.ModePolynomialFarEnvelope
import Cvs.StepA.OddAboveDisplacement
import Cvs.StepA.OddSectorBottom
import Cvs.StepA.OddTrialEnvelope
import Cvs.StepA.OddTrialErrorBudget
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.QuadrupleParitySectors
import Cvs.StepA.RestEnvelopeSmall
import Cvs.StepA.RestZerosEnvelope
import Cvs.StepA.StepACriterion
import Cvs.StepA.TopQuadruple
import Cvs.Upstream.SymmetricMatrixBottom
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
# Step (a) as an RH criterion at a top set of any size

A set `S` of zeros at the top distance `δ`, finite or not, whose odd band bottom over the window's
`N`-mode vectors lies below its even band bottom by `c·n^δ` at `L = log n` for infinitely many `n`
refutes step (a), so RH is equivalent to step (a) given such a set off RH and odd eigenpairs on RH.
-/

noncomputable section

open Real Matrix Filter Topology Asymptotics

namespace Cvs.StepA.Edge.TopSetCriterion
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI mode_injective negI_involutive mode_negI)
open Cvs.StepA.OddAboveDisplacement (OddAbove)
open Cvs.StepA.OddBottomGapCriterion (OddBottomBelow)
open Cvs.StepA.TopQuadruple (offLine pairE pairO)
open Cvs.StepA.OddTrialEnvelope (onLineBound)
open Cvs.StepA.ModePolynomialFarEnvelope (envE envO)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg FiniteTop)

/-! ### Top sets -/

/-- A top set at distance `δ > 0`: every zero of `S` at distance `δ` from the critical line, every
other zero strictly closer; `S` may be infinite. -/
def TopSet (S : Set nonTrivialZeroSet) (δ : ℝ) : Prop :=
  0 < δ ∧ S.Nonempty ∧ (∀ ρ ∈ S, |Cvs.GaussKernel.del ρ| = δ) ∧
    ∀ ρ, ρ ∉ S → |Cvs.GaussKernel.del ρ| < δ

/-- Zeros at a common distance `δ > 0` from the critical line lie off it. -/
theorem subset_offLine_of_depth {S : Set nonTrivialZeroSet} {δ : ℝ} (hδ : 0 < δ)
    (hSδ : ∀ ρ ∈ S, |Cvs.GaussKernel.del ρ| = δ) : S ⊆ offLine := by
  intro ρ hρ
  show (ρ : ℂ).re ≠ 1 / 2
  rw [← Cvs.GaussKernel.del_ne_zero_iff, ← abs_ne_zero, hSδ ρ hρ]
  exact hδ.ne'

/-- A top set lies off the critical line. -/
theorem TopSet.subset_offLine {S : Set nonTrivialZeroSet} {δ : ℝ} (h : TopSet S δ) :
    S ⊆ offLine :=
  subset_offLine_of_depth h.1 h.2.2.1

/-- The zeros off the line outside a top set lie strictly closer than `δ`. -/
theorem TopSet.rest_lt {S : Set nonTrivialZeroSet} {δ : ℝ} (h : TopSet S δ) :
    ∀ ρ ∈ offLine \ S, |Cvs.GaussKernel.del ρ| < δ :=
  fun ρ hρ => h.2.2.2 ρ hρ.2

/-- A finite top set is a top set. -/
theorem topSet_of_finiteTop {S : Finset nonTrivialZeroSet} {δ : ℝ} (h : FiniteTop S δ) :
    TopSet (S : Set nonTrivialZeroSet) δ :=
  ⟨h.1, Finset.coe_nonempty.mpr h.2.1, fun ρ hρ => h.2.2.1 ρ hρ, fun ρ hρ => h.2.2.2 ρ hρ⟩

/-! ### Splitting a sum along sets -/

/-- For `S₀ ⊆ S`, a summable family splits over `S` as `S₀`, then `S ∖ S₀`. -/
theorem tsum_split_two {β : Type*} {f : β → ℝ} (hf : Summable f) {S₀ S : Set β} (h : S₀ ⊆ S) :
    ∑' x : S, f x = ∑' x : S₀, f x + ∑' x : ↥(S \ S₀), f x := by
  simp only [tsum_subtype]
  rw [← (hf.indicator _).tsum_add (hf.indicator _)]
  refine tsum_congr fun x => ?_
  by_cases hS : x ∈ S
  · by_cases h0 : x ∈ S₀
    · simp [Set.indicator, hS, h0]
    · simp [Set.indicator, hS, h0]
  · have h0 : x ∉ S₀ := fun h' => hS (h h')
    simp [Set.indicator, hS, h0]

/-- For `S ⊆ T`, a summable family splits as `S`, then `T ∖ S`, then `Tᶜ`. -/
theorem tsum_split_three {β : Type*} {f : β → ℝ} (hf : Summable f) {S T : Set β} (hST : S ⊆ T) :
    ∑' x, f x = ∑' x : S, f x + ∑' x : ↥(T \ S), f x + ∑' x : ↥Tᶜ, f x := by
  rw [← hf.tsum_subtype_add_tsum_subtype_compl T, tsum_split_two hf hST]

/-- The even form `L ξᵀ M_L ξ` splits along a set `S` of zeros off the line into `S`, the other
zeros off the line, and the zeros on it. -/
theorem evenForm_split_set {L : ℝ} (hL : 0 < L) (N : ℕ) {S : Set nonTrivialZeroSet}
    (hS : S ⊆ offLine) {ξ : Idx N → ℝ} (hξ : ∀ i, ξ (negI N i) = ξ i) :
    L * (ξ ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ ξ))
      = ∑' ρ : S, mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ)
        + ∑' ρ : ↥(offLine \ S), mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ)
        + ∑' ρ : ↥offLineᶜ, mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) := by
  rw [Cvs.StepA.OneZeroParitySectors.quadForm_even_eq_pairings hL (mode_injective N) (negI_involutive N)
    (mode_negI N) hξ]
  exact tsum_split_three (Cvs.StepA.QuadrupleParitySectors.summable_pairE hL N ξ) hS

/-- The odd form `L oᵀ M_L o` splits along a set `S` of zeros off the line into `S`, the other
zeros off the line, and the zeros on it. -/
theorem oddForm_split_set {L : ℝ} (hL : 0 < L) (N : ℕ) {S : Set nonTrivialZeroSet}
    (hS : S ⊆ offLine) {o : Idx N → ℝ} (ho : ∀ i, o (negI N i) = -o i) :
    L * (o ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ o))
      = ∑' ρ : S, mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ)
        + ∑' ρ : ↥(offLine \ S), mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ)
        + ∑' ρ : ↥offLineᶜ, mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ) := by
  rw [Cvs.StepA.OneZeroParitySectors.quadForm_odd_eq_pairings hL (mode_injective N) (negI_involutive N)
    (mode_negI N) ho]
  exact tsum_split_three (Cvs.StepA.QuadrupleParitySectors.summable_pairO hL N o) hS

/-- The zeros on the line add a nonnegative amount to the even form. -/
theorem onLine_even_nonneg {L : ℝ} (N : ℕ) (ξ : Idx N → ℝ) :
    0 ≤ ∑' ρ : ↥offLineᶜ, mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) := by
  refine tsum_nonneg fun ρ => mul_nonneg (mult_nonneg _) ?_
  have hre : ((ρ : nonTrivialZeroSet) : ℂ).re = 1 / 2 := not_not.mp ρ.2
  have hv : ∀ t, Cvs.StepA.OneZeroParitySectors.ve (Cvs.ZeroCounting.zPoint (ρ : nonTrivialZeroSet)) t = 0 :=
    Cvs.StepA.OneZeroParitySectors.ve_eq_zero (Or.inr (Cvs.StepA.OneZeroParitySectors.zPoint_im_eq_zero hre))
  simp only [pairE, hv, mul_zero, intervalIntegral.integral_zero]
  nlinarith [sq_nonneg (∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ
    (t + L / 2) * Cvs.StepA.OneZeroParitySectors.ue (Cvs.ZeroCounting.zPoint (ρ : nonTrivialZeroSet)) t)]

/-- The zeros on the line add at most `onLineBound · L‖o‖²` to the odd form. -/
theorem onLine_odd_le {L : ℝ} (hL : 0 < L) (N : ℕ) {o : Idx N → ℝ}
    (ho : ∀ i, o (negI N i) = -o i) :
    ∑' ρ : ↥offLineᶜ, mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ)
      ≤ onLineBound L N * (L * (o ⬝ᵥ o)) :=
  Cvs.StepA.OddTrialEnvelope.tsum_onLine_le hL N ho fun _ hρ => not_not.mp hρ

/-! ### The band bottoms of a set of zeros -/

/-- The Rayleigh quotients of `∑'_{ρ ∈ S} m_ρ pairE(·, z_ρ)` over the nonzero even `N`-mode
vectors. -/
def bandRayE (L : ℝ) (N : ℕ) (S : Set nonTrivialZeroSet) : Set ℝ :=
  {r | ∃ ξ : Idx N → ℝ, (∀ i, ξ (negI N i) = ξ i) ∧ ξ ≠ 0 ∧
    r = (∑' ρ : S, mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ)) / (L * (ξ ⬝ᵥ ξ))}

/-- The Rayleigh quotients of `∑'_{ρ ∈ S} m_ρ pairO(·, z_ρ)` over the nonzero odd `N`-mode
vectors. -/
def bandRayO (L : ℝ) (N : ℕ) (S : Set nonTrivialZeroSet) : Set ℝ :=
  {r | ∃ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) ∧ o ≠ 0 ∧
    r = (∑' ρ : S, mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ)) / (L * (o ⬝ᵥ o))}

/-- The even band bottom of a set of zeros. -/
def bandBotE (L : ℝ) (N : ℕ) (S : Set nonTrivialZeroSet) : ℝ := sInf (bandRayE L N S)

/-- The odd band bottom of a set of zeros. -/
def bandBotO (L : ℝ) (N : ℕ) (S : Set nonTrivialZeroSet) : ℝ := sInf (bandRayO L N S)

/-- A nonzero vector has `L ‖v‖² > 0` for `L > 0`. -/
theorem mul_dot_pos {L : ℝ} (hL : 0 < L) {N : ℕ} {v : Idx N → ℝ} (hv : v ≠ 0) :
    0 < L * (v ⬝ᵥ v) :=
  mul_pos hL (lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' v)
    (fun h0 => hv (dotProduct_self_eq_zero.mp h0.symm)))

/-- For `L > 0` the even band quotients are nonempty. -/
theorem bandRayE_nonempty {L : ℝ} (hL : 0 < L) (N : ℕ) (S : Set nonTrivialZeroSet) :
    (bandRayE L N S).Nonempty := by
  obtain ⟨heven, hnorm, -, -⟩ := Cvs.Finite.EvenMinimisers.evMin_spec 0 0 hL N
  exact ⟨_, _, heven, fun h0 => by rw [h0] at hnorm; simp at hnorm, rfl⟩

/-- For `L > 0` and a mode pair the odd band quotients are nonempty. -/
theorem bandRayO_nonempty {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 0 < N) (S : Set nonTrivialZeroSet) :
    (bandRayO L N S).Nonempty := by
  obtain ⟨-, o, ho, hnorm, -, -⟩ := Cvs.StepA.OddSectorBottom.exists_odd_bottom hL 0 0 N hN
  exact ⟨_, o, ho, fun h0 => by rw [h0] at hnorm; simp at hnorm, rfl⟩

/-- The even band quotients are bounded below by minus the envelope sum over `S`. -/
theorem bddBelow_bandRayE {L : ℝ} (hL : 0 < L) (N : ℕ) (S : Set nonTrivialZeroSet) :
    BddBelow (bandRayE L N S) := by
  refine ⟨-(∑' ρ : S, mult ρ * envE L N (Cvs.ZeroCounting.zPoint ρ)), ?_⟩
  rintro r ⟨ξ, -, hne, rfl⟩
  rw [le_div_iff₀ (mul_dot_pos hL hne)]
  have h := Cvs.StepA.RestZerosEnvelope.neg_tsum_envE_mul_le hL N ξ S
  linarith

/-- The odd band quotients of a set of zeros off the line are bounded below. -/
theorem bddBelow_bandRayO {L : ℝ} (hL : 0 < L) (N : ℕ) {S : Set nonTrivialZeroSet}
    (hS : S ⊆ offLine) : BddBelow (bandRayO L N S) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨0, ?_⟩
    rintro r ⟨o, ho, hne, -⟩
    exact absurd (Cvs.StepA.StepACriterion.eq_zero_of_odd_zero ho) hne
  obtain ⟨lam, -, -, -, hbot, -⟩ :=
    Cvs.StepA.OddSectorBottom.exists_odd_bottom hL ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ N hN
  refine ⟨lam - ((∑' ρ : ↥(offLine \ S), mult ρ * envO L N (Cvs.ZeroCounting.zPoint ρ))
    + onLineBound L N), ?_⟩
  rintro r ⟨o, ho, hne, rfl⟩
  have hp := mul_dot_pos hL hne
  rw [le_div_iff₀ hp]
  have hsplit := oddForm_split_set hL N hS ho
  have hrest := Cvs.StepA.RestZerosEnvelope.tsum_pairO_le_tsum_envO_mul hL N o (offLine \ S)
  have hon := onLine_odd_le hL N ho
  have hb := mul_le_mul_of_nonneg_left (hbot o ho) hL.le
  have e : L * (lam * (o ⬝ᵥ o)) = lam * (L * (o ⬝ᵥ o)) := by ring
  rw [e] at hb
  have hM : L * (o ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ o))
      = L * (o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode N) *ᵥ o)) :=
    rfl
  nlinarith

/-- The even band bottom bounds `∑'_{ρ ∈ S} m_ρ pairE` from below at every nonzero even vector. -/
theorem bandBotE_mul_le {L : ℝ} (hL : 0 < L) (N : ℕ) (S : Set nonTrivialZeroSet)
    {ξ : Idx N → ℝ} (hξ : ∀ i, ξ (negI N i) = ξ i) (hne : ξ ≠ 0) :
    bandBotE L N S * (L * (ξ ⬝ᵥ ξ))
      ≤ ∑' ρ : S, mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) := by
  have h := csInf_le (bddBelow_bandRayE hL N S) ⟨ξ, hξ, hne, rfl⟩
  rwa [le_div_iff₀ (mul_dot_pos hL hne)] at h

/-- Above the odd band bottom there is a nonzero odd vector whose quotient lies below. -/
theorem exists_odd_lt_band {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 0 < N) (S : Set nonTrivialZeroSet)
    {b : ℝ} (h : bandBotO L N S < b) :
    ∃ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) ∧ o ≠ 0 ∧
      ∑' ρ : S, mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ) < b * (L * (o ⬝ᵥ o)) := by
  obtain ⟨r, ⟨o, ho, hne, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (bandRayO_nonempty hL hN S) h
  exact ⟨o, ho, hne, (div_lt_iff₀ (mul_dot_pos hL hne)).mp hr⟩

/-! ### One scale -/

/-- The even rest of a set: `∑'_{off line ∖ S} m_ρ envE(L, N, z_ρ)`. -/
def restE (L : ℝ) (N : ℕ) (S : Set nonTrivialZeroSet) : ℝ :=
  ∑' ρ : ↥(offLine \ S), mult ρ * envE L N (Cvs.ZeroCounting.zPoint ρ)

/-- The odd rest of a set: `∑'_{off line ∖ S} m_ρ envO(L, N, z_ρ)`. -/
def restO (L : ℝ) (N : ℕ) (S : Set nonTrivialZeroSet) : ℝ :=
  ∑' ρ : ↥(offLine \ S), mult ρ * envO L N (Cvs.ZeroCounting.zPoint ρ)

/-- For a set `S` of zeros off the line, `bandBotE − restE ≤ evLam` at `(⌈e^L⌉₊, ⌈L/log 2⌉₊)`. -/
theorem evLam_ge_band {L : ℝ} (hL : 0 < L) (N : ℕ) {S : Set nonTrivialZeroSet}
    (hS : S ⊆ offLine) :
    bandBotE L N S - restE L N S
      ≤ Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  obtain ⟨heven, hnorm, -, heig⟩ :=
    Cvs.Finite.EvenMinimisers.evMin_spec ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ hL N
  set ξ := Cvs.Finite.EvenMinimisers.evMin ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N
  set lam := Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N
  have hne : ξ ≠ 0 := fun h0 => by rw [h0] at hnorm; simp at hnorm
  have hsplit := evenForm_split_set hL N hS heven
  have hlhs : L * (ξ ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ ξ)) = L * lam := by
    rw [Cvs.Finite.ParitySectorDefect.MX, heig, dotProduct_smul, hnorm, smul_eq_mul, mul_one]
  have htop := bandBotE_mul_le hL N S heven hne
  rw [hnorm, mul_one] at htop
  have hrest := Cvs.StepA.RestZerosEnvelope.neg_tsum_envE_mul_le hL N ξ (offLine \ S)
  rw [hnorm, mul_one] at hrest
  have hon := onLine_even_nonneg (L := L) N ξ
  refine le_of_mul_le_mul_left ?_ hL
  have e : L * (bandBotE L N S - restE L N S) = bandBotE L N S * L - restE L N S * L := by ring
  rw [e]
  unfold restE
  nlinarith

/-- For a set `S` of zeros off the line and odd `o`,
`L oᵀ M_L o ≤ ∑'_{ρ ∈ S} m_ρ pairO + (restO + onLineBound) L ‖o‖²`. -/
theorem oddForm_le_band {L : ℝ} (hL : 0 < L) (N : ℕ) {S : Set nonTrivialZeroSet}
    (hS : S ⊆ offLine) {o : Idx N → ℝ} (ho : ∀ i, o (negI N i) = -o i) :
    L * (o ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ o))
      ≤ ∑' ρ : S, mult ρ * pairO L N o (Cvs.ZeroCounting.zPoint ρ)
        + (restO L N S + onLineBound L N) * (L * (o ⬝ᵥ o)) := by
  have hsplit := oddForm_split_set hL N hS ho
  have hrest := Cvs.StepA.RestZerosEnvelope.tsum_pairO_le_tsum_envO_mul hL N o (offLine \ S)
  have hon := onLine_odd_le hL N ho
  unfold restO
  rw [hsplit]
  nlinarith

/-- **One scale where step (a) fails around a set of zeros off the line**: with a mode pair,
`bandBotO + restO + restE + onLineBound < bandBotE` refutes `OddAbove` at `(⌈e^L⌉₊, ⌈L/log 2⌉₊)`. -/
theorem not_oddAbove_of_band {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 0 < N)
    {S : Set nonTrivialZeroSet} (hS : S ⊆ offLine)
    (h : bandBotO L N S + restO L N S + restE L N S + onLineBound L N < bandBotE L N S) :
    ¬ OddAbove ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  intro hA
  set b := bandBotE L N S - restO L N S - restE L N S - onLineBound L N with hb
  obtain ⟨o, ho, hne, hle⟩ := exists_odd_lt_band hL hN S (b := b) (by rw [hb]; linarith)
  have hp := mul_dot_pos hL hne
  have hodd := oddForm_le_band hL N hS ho
  have h2 : (bandBotE L N S - restE L N S) * (L * (o ⬝ᵥ o))
      ≤ Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N * (L * (o ⬝ᵥ o)) :=
    mul_le_mul_of_nonneg_right (evLam_ge_band hL N hS) hp.le
  have h3 : L * (Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N * (o ⬝ᵥ o))
      < L * (o ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX L N *ᵥ o)) := mul_lt_mul_of_pos_left (hA o ho hne) hL
  have e : b * (L * (o ⬝ᵥ o)) + (restO L N S + onLineBound L N) * (L * (o ⬝ᵥ o))
      = (bandBotE L N S - restE L N S) * (L * (o ⬝ᵥ o)) := by rw [hb]; ring
  nlinarith

/-! ### The band gap along a mode count -/

/-- **The band gap of `S` along a mode count `M`**: for some `c > 0` and infinitely many `n`, at
`L = log n` and `N = M L`, the odd band bottom of `S` lies below its even band bottom by `c·n^δ`. -/
def BandGap (S : Set nonTrivialZeroSet) (δ : ℝ) (M : ℝ → ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop,
    bandBotO (Real.log n) (M (Real.log n)) S + c * Real.exp (δ * Real.log n)
      ≤ bandBotE (Real.log n) (M (Real.log n)) S

/-- **The band top gap at bandwidth `Ω`**: the band gap along `N = ⌈ΩL/2π⌉₊`. -/
def BandTopGap (S : Set nonTrivialZeroSet) (δ Ω : ℝ) : Prop :=
  BandGap S δ fun L => ⌈Ω * L / (2 * π)⌉₊

/-- For a top set, an eventually positive mode count `M = O(L)`, `c > 0` and `φ → ∞` with
`bandBotO + c e^{δφ} ≤ bandBotE` at `(φ a, M (φ a))` frequently, `OddAbove` fails there
frequently. -/
theorem frequently_not_oddAbove_of_bandGap {S : Set nonTrivialZeroSet} {δ : ℝ}
    (hS : TopSet S δ) {M : ℝ → ℕ} (hM : (fun L => (M L : ℝ)) =O[atTop] fun L => L)
    (hM0 : ∀ᶠ L in atTop, 0 < M L) {c : ℝ} (hc : 0 < c) {α : Type*} {l : Filter α}
    {φ : α → ℝ} (hφ : Tendsto φ l atTop)
    (hg : ∃ᶠ a in l, bandBotO (φ a) (M (φ a)) S + c * Real.exp (δ * φ a)
      ≤ bandBotE (φ a) (M (φ a)) S) :
    ∃ᶠ a in l, ∀ hL : 0 < φ a,
      ¬ OddAbove ⌈Real.exp (φ a)⌉₊ ⌈φ a / Real.log 2⌉₊ (φ a) hL (M (φ a)) := by
  have hδ : 0 < δ := hS.1
  have h1 := (isLittleO_iff_tendsto fun _ h => absurd h (Real.exp_pos _).ne').mpr
    (Cvs.StepA.RestEnvelopeSmall.tendsto_tsum_envE_div_exp hS.rest_lt hM)
  have h2 := (isLittleO_iff_tendsto fun _ h => absurd h (Real.exp_pos _).ne').mpr
    (Cvs.StepA.RestEnvelopeSmall.tendsto_tsum_envO_div_exp hS.rest_lt hM)
  have h3 : (fun L => onLineBound L (M L)) =o[atTop] fun L => Real.exp (δ * L) :=
    Cvs.StepA.OddTrialErrorBudget.isLittleO_onLineBound_of_isBigO (k := 1)
      (by simpa only [pow_one] using hM) hδ
  have hR := (h1.add h2).add h3
  have hev : ∀ᶠ L in atTop, 0 < L ∧ 0 < M L ∧
      restE L (M L) S + restO L (M L) S + onLineBound L (M L) ≤ c / 2 * Real.exp (δ * L) := by
    filter_upwards [hR.bound (by positivity : (0 : ℝ) < c / 2), eventually_gt_atTop 0, hM0]
      with L h hL hML
    refine ⟨hL, hML, ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    exact (le_abs_self _).trans h
  refine (hg.and_eventually (hφ.eventually hev)).mono fun a ⟨hgap, _, hMa, hrest⟩ hL => ?_
  refine not_oddAbove_of_band hL hMa hS.subset_offLine ?_
  have hE := Real.exp_pos (δ * φ a)
  unfold restE restO at hrest
  unfold restE restO
  nlinarith

/-- `⌈ΩL/2π⌉₊ → ∞` as `L → ∞`, for `Ω > 0`. -/
theorem tendsto_natCeil {Ω : ℝ} (hΩ : 0 < Ω) :
    Tendsto (fun L : ℝ => ⌈Ω * L / (2 * π)⌉₊) atTop atTop :=
  tendsto_nat_ceil_atTop.comp ((tendsto_id.const_mul_atTop hΩ).atTop_div_const (by positivity))

end Cvs.StepA.Edge.TopSetCriterion
