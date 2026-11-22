import Mathlib
import Cvs.Zeta.GaussKernel.AdmissibleKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The bump algebra, and where the many-body structure actually lives

Three exact facts about the offset kernel, none of them estimates.
-/

namespace Cvs.GaussKernel

open Complex Finset

/-- **The three bumps collapse to one.**  The cross term never dominates, and
the two outer bumps are exchanged by `γ ↦ -γ`, so the whole rate is the single
two-body rate in `|γ|`. -/
theorem ampRate_eq_abs {a : ℝ} (ha : 0 ≤ a) (γ δ : ℝ) :
    Cvs.Zeta.GaussKernel.AdmissibleKernel.ampRate a γ δ = δ ^ 2 - (|γ| - a) ^ 2 := by
  rw [Cvs.Zeta.GaussKernel.AdmissibleKernel.ampRate_def]
  rcases le_or_gt 0 γ with h | h
  · rw [abs_of_nonneg h]
    have h12 : δ ^ 2 - (γ + a) ^ 2 ≤ δ ^ 2 - (γ - a) ^ 2 := by
      nlinarith [mul_nonneg ha h]
    have h13 : δ ^ 2 - γ ^ 2 - a ^ 2 ≤ δ ^ 2 - (γ - a) ^ 2 := by
      nlinarith [mul_nonneg ha h]
    rw [max_eq_left h12, max_eq_left h13]
  · rw [abs_of_neg h]
    have hga : 0 ≤ a * (-γ) := mul_nonneg ha (le_of_lt (neg_pos.mpr h))
    have h21 : δ ^ 2 - (γ - a) ^ 2 ≤ δ ^ 2 - (γ + a) ^ 2 := by nlinarith
    have h23 : δ ^ 2 - γ ^ 2 - a ^ 2 ≤ δ ^ 2 - (γ + a) ^ 2 := by nlinarith
    rw [max_eq_right h21, max_eq_left h23]
    ring

/-! ## The exact competition condition, and what it makes free

With the rate collapsed, "does the target beat this competitor" is an identity,
not an estimate. -/

/-- **The competition condition, exactly.**  No inequality is discarded here. -/
theorem ampRate_lt_iff {a : ℝ} (ha : 0 ≤ a) (γ δ δ₀ ε : ℝ) :
    Cvs.Zeta.GaussKernel.AdmissibleKernel.ampRate a γ δ < δ₀ ^ 2 - ε ^ 2
      ↔ δ ^ 2 - δ₀ ^ 2 < (|γ| - a) ^ 2 - ε ^ 2 := by
  rw [ampRate_eq_abs ha]
  constructor <;> intro h <;> linarith

/-- **Competitors half a unit above the target are beaten outright.** With `a = γ₀ - ε` a
competitor at `|γ| ≥ γ₀ + 1/2` has margin at least `1/4 + ε`, and `δ² - δ₀² ≤ 1/4` in the
strip — so no hypothesis about its deviation is needed at all. -/
theorem ampRate_lt_of_far_above {γ₀ δ δ₀ ε γ : ℝ} (hε : 0 < ε)
    (ha : 0 ≤ γ₀ - ε) (hδ : δ ^ 2 ≤ 1 / 4)
    (hfar : γ₀ + 1 / 2 ≤ |γ|) :
    Cvs.Zeta.GaussKernel.AdmissibleKernel.ampRate (γ₀ - ε) γ δ < δ₀ ^ 2 - ε ^ 2 := by
  rw [ampRate_lt_iff ha]
  have h1 : (1 : ℝ) / 2 + ε ≤ |γ| - (γ₀ - ε) := by linarith
  have h2 : (0 : ℝ) ≤ 1 / 2 + ε := by linarith
  nlinarith [mul_le_mul h1 h1 h2 (by linarith : (0:ℝ) ≤ |γ| - (γ₀ - ε))]

/-- The strip bound in the form `ampRate_lt_of_far_above` consumes. -/
theorem sq_le_quarter_of_abs_le {δ : ℝ} (h : |δ| ≤ 1 / 2) : δ ^ 2 ≤ 1 / 4 := by
  nlinarith [abs_nonneg δ, sq_abs δ]

/-! ### What a defeat costs -/

/-- **A defeat above the target costs the square of the distance.** If the target does not beat a
competitor at `|γ| ≥ γ₀`, then that competitor's off-line distance exceeds the target's by at
least `(|γ| - γ₀)²`. -/
theorem sq_dist_le_gain {γ₀ δ₀ ε γ δ : ℝ} (hε : 0 < ε) (ha : 0 ≤ γ₀ - ε)
    (habove : γ₀ ≤ |γ|)
    (hnot : (δ₀ : ℝ) ^ 2 - ε ^ 2 ≤ Cvs.Zeta.GaussKernel.AdmissibleKernel.ampRate (γ₀ - ε) γ δ) :
    (|γ| - γ₀) ^ 2 ≤ δ ^ 2 - δ₀ ^ 2 := by
  rw [ampRate_eq_abs ha] at hnot
  nlinarith [hnot, hε, sub_nonneg.mpr habove]

/-! ### What a chain of defeats costs -/

/-- **Cauchy–Schwarz on the increments.**  A chain whose squared steps are
bounded by `1/4` can only advance `√n/2` in `n` steps. -/
theorem sum_sq_le_card_div_four {n : ℕ} (u : ℕ → ℝ)
    (hsq : ∑ k ∈ Finset.range n, (u k) ^ 2 ≤ 1 / 4) :
    (∑ k ∈ Finset.range n, u k) ^ 2 ≤ (n : ℝ) / 4 := by
  refine (sq_sum_le_card_mul_sum_sq).trans ?_
  rw [Finset.card_range]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [hsq, hn]

/-- **The advance is at most `√n / 2`.**  Stated as the bound the counting law
is confronted with: reaching height `H` above the start needs `n ≥ 4H²` steps,
where the counting law allows only `O(H log H)` zeros below that height. -/
theorem card_ge_four_mul_sq {n : ℕ} (u : ℕ → ℝ) (H : ℝ)
    (hsq : ∑ k ∈ Finset.range n, (u k) ^ 2 ≤ 1 / 4)
    (hH : H ≤ ∑ k ∈ Finset.range n, u k) (hH0 : 0 ≤ H) :
    4 * H ^ 2 ≤ (n : ℝ) := by
  have h := sum_sq_le_card_div_four u hsq
  nlinarith [h, hH, hH0]

/-!
## The chain a failure would have to sustain

Everything above says what one target needs.
-/

variable {ι : Type*} (γ δ : ι → ℝ)

/-- `i` is a record: it maximises `δ²` over everything at its own height or
below. -/
def IsRecord (i : ι) : Prop := ∀ i', |γ i'| ≤ |γ i| → (δ i') ^ 2 ≤ (δ i) ^ 2

/-- The step a failure supplies: a record is beaten by something above it, and
the beating costs the square of the distance (`sq_dist_le_gain`). -/
def StepUp (P : ι → Prop) (i j : ι) (u : ℝ) : Prop :=
  0 < u ∧ |γ j| ≤ |γ i| + u ∧ (δ i) ^ 2 + u ^ 2 ≤ (δ j) ^ 2 ∧ P j

/-- **The chain.**  If every record is beaten, iterate. -/
noncomputable def chain (P : ι → Prop)
    (hstep : ∀ i, P i → ∃ j u, StepUp γ δ P i j u)
    (i₀ : ι) (h₀ : P i₀) : ℕ → {i : ι // P i}
  | 0 => ⟨i₀, h₀⟩
  | n + 1 =>
      let p := chain P hstep i₀ h₀ n
      ⟨(hstep p.1 p.2).choose, ((hstep p.1 p.2).choose_spec.choose_spec).2.2.2⟩

/-- The step size at stage `n`. -/
noncomputable def step (P : ι → Prop)
    (hstep : ∀ i, P i → ∃ j u, StepUp γ δ P i j u)
    (i₀ : ι) (h₀ : P i₀) (n : ℕ) : ℝ :=
  let p := chain γ δ P hstep i₀ h₀ n
  (hstep p.1 p.2).choose_spec.choose

variable (P : ι → Prop)
  (hstep : ∀ i, P i → ∃ j u, StepUp γ δ P i j u) (i₀ : ι) (h₀ : P i₀)

theorem chain_spec (n : ℕ) :
    StepUp γ δ P (chain γ δ P hstep i₀ h₀ n).1 (chain γ δ P hstep i₀ h₀ (n + 1)).1
      (step γ δ P hstep i₀ h₀ n) :=
  (hstep (chain γ δ P hstep i₀ h₀ n).1
    (chain γ δ P hstep i₀ h₀ n).2).choose_spec.choose_spec

theorem step_pos (n : ℕ) : 0 < step γ δ P hstep i₀ h₀ n :=
  (chain_spec γ δ P hstep i₀ h₀ n).1

/-- Heights advance by at most the step. -/
theorem height_le (n : ℕ) :
    |γ (chain γ δ P hstep i₀ h₀ n).1|
      ≤ |γ i₀| + ∑ k ∈ Finset.range n, step γ δ P hstep i₀ h₀ k := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
      have h := (chain_spec γ δ P hstep i₀ h₀ n).2.1
      rw [Finset.sum_range_succ]
      linarith

/-- Deviations gain at least the squared step. -/
theorem gain_le (n : ℕ) :
    (δ i₀) ^ 2 + ∑ k ∈ Finset.range n, (step γ δ P hstep i₀ h₀ k) ^ 2
      ≤ (δ (chain γ δ P hstep i₀ h₀ n).1) ^ 2 := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
      have h := (chain_spec γ δ P hstep i₀ h₀ n).2.2.1
      rw [Finset.sum_range_succ]
      linarith

/-- **The budget.**  In the strip the gains cannot exceed `1/4`. -/
theorem sum_step_sq_le (hbd : ∀ i, |δ i| ≤ 1 / 2) (n : ℕ) :
    ∑ k ∈ Finset.range n, (step γ δ P hstep i₀ h₀ k) ^ 2 ≤ 1 / 4 := by
  have h := gain_le γ δ P hstep i₀ h₀ n
  have h1 : (δ (chain γ δ P hstep i₀ h₀ n).1) ^ 2 ≤ 1 / 4 :=
    sq_le_quarter_of_abs_le (hbd _)
  nlinarith [sq_nonneg (δ i₀)]

/-- The gains are strictly increasing, so the chain never revisits a zero. -/
theorem strictMono_chain :
    StrictMono fun n => (δ (chain γ δ P hstep i₀ h₀ n).1) ^ 2 := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h := (chain_spec γ δ P hstep i₀ h₀ n).2.2.1
  have hu := step_pos γ δ P hstep i₀ h₀ n
  nlinarith

theorem chain_injective :
    Function.Injective fun n => (chain γ δ P hstep i₀ h₀ n).1 := by
  intro m n hmn
  exact (strictMono_chain γ δ P hstep i₀ h₀).injective (by simp only [hmn])

/-- **The chain's total advance is at most `√n / 2`.**  Cauchy–Schwarz against
the `1/4` budget: `n` steps buy `√n / 2` of height, not `n`. -/
theorem sum_step_le_sqrt (hbd : ∀ i, |δ i| ≤ 1 / 2) (n : ℕ) :
    ∑ k ∈ Finset.range n, step γ δ P hstep i₀ h₀ k ≤ Real.sqrt n / 2 := by
  have hsq := sum_step_sq_le γ δ P hstep i₀ h₀ hbd n
  have hnn : 0 ≤ ∑ k ∈ Finset.range n, step γ δ P hstep i₀ h₀ k :=
    Finset.sum_nonneg fun k _ => (step_pos γ δ P hstep i₀ h₀ k).le
  have h4 := card_ge_four_mul_sq (step γ δ P hstep i₀ h₀)
    (∑ k ∈ Finset.range n, step γ δ P hstep i₀ h₀ k) hsq (le_refl _) hnn
  have hle : (2 * ∑ k ∈ Finset.range n, step γ δ P hstep i₀ h₀ k) ≤ Real.sqrt n := by
    have h2 : (0 : ℝ) ≤ 2 * ∑ k ∈ Finset.range n, step γ δ P hstep i₀ h₀ k := by
      linarith
    refine (Real.le_sqrt h2 (Nat.cast_nonneg n)).mpr ?_
    nlinarith [h4]
  linarith

/-- **Every chain member below stage `n` sits inside a window of radius
`√n / 2`.**  This is the shape the counting law is confronted with: `n` distinct
zeros at height at most `|γ i₀| + √n / 2`. -/
theorem chain_mem_window (hbd : ∀ i, |δ i| ≤ 1 / 2) {n m : ℕ} (hm : m ≤ n) :
    |γ (chain γ δ P hstep i₀ h₀ m).1| ≤ |γ i₀| + Real.sqrt n / 2 := by
  refine (height_le γ δ P hstep i₀ h₀ m).trans ?_
  have hmono : ∑ k ∈ Finset.range m, step γ δ P hstep i₀ h₀ k
      ≤ ∑ k ∈ Finset.range n, step γ δ P hstep i₀ h₀ k :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hm) (fun k _ _ => (step_pos γ δ P hstep i₀ h₀ k).le)
  have := sum_step_le_sqrt γ δ P hstep i₀ h₀ hbd n
  linarith

include hstep h₀ in
/-- **The chain's cost, as a counting statement.** If every record is beaten, then for every `n`
there are `n` distinct indices inside the window of radius `|γ i₀| + √n / 2`. -/
theorem chain_card_le (hfin : ∀ M : ℝ, {i | |γ i| ≤ M}.Finite)
    (hbd : ∀ i, |δ i| ≤ 1 / 2) (n : ℕ) :
    n ≤ ((hfin (|γ i₀| + Real.sqrt n / 2)).toFinset).card := by
  classical
  have hmaps : ∀ m ∈ Finset.range n, (chain γ δ P hstep i₀ h₀ m).1
      ∈ (hfin (|γ i₀| + Real.sqrt n / 2)).toFinset := by
    intro m hm
    rw [Set.Finite.mem_toFinset]
    exact chain_mem_window γ δ P hstep i₀ h₀ hbd (le_of_lt (Finset.mem_range.mp hm))
  have hinj : Set.InjOn (fun m => (chain γ δ P hstep i₀ h₀ m).1) (Finset.range n) :=
    Function.Injective.injOn (chain_injective γ δ P hstep i₀ h₀)
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simpa using this

/-!
## Why `ε` costs nothing

`ε` never needs to be fixed before the target.
-/

/-- **A record is never defeated from below.** If the competitor is dominated (which a record
guarantees) and sits strictly below the target by more than `2ε`, its margin `v(v - 2ε)` is
positive while its deficit is not — so it loses, with no further hypothesis. -/
theorem ampRate_lt_of_below {γ₀ δ₀ ε γ δ : ℝ} (hε : 0 < ε) (ha : 0 ≤ γ₀ - ε)
    (hrec : δ ^ 2 ≤ δ₀ ^ 2) (hgap : 2 * ε < γ₀ - |γ|) :
    Cvs.Zeta.GaussKernel.AdmissibleKernel.ampRate (γ₀ - ε) γ δ < δ₀ ^ 2 - ε ^ 2 := by
  rw [ampRate_lt_iff ha]
  nlinarith [hgap, hε, hrec]

/-- The two orbit gaps `exists_eps_bounds_abs` supplies control the one gap the
rate needs: `abs (|γ| - γ₀)` is whichever of `|γ - γ₀|`, `|γ + γ₀|` is smaller. -/
theorem two_mul_lt_abs_abs_sub {γ γ₀ ε : ℝ}
    (h1 : 2 * ε < |γ - γ₀|) (h2 : 2 * ε < |γ + γ₀|) :
    2 * ε < abs (|γ| - γ₀) := by
  rcases le_or_gt 0 γ with h | h
  · rwa [abs_of_nonneg h]
  · rw [abs_of_neg h, show -γ - γ₀ = -(γ + γ₀) by ring, abs_neg]
    exact h2

/-- **The dichotomy the chain step needs.**  A competitor off the target's orbit
either sits at or above the target's height, or strictly more than `2ε` below
it — there is no middle. -/
theorem above_or_far_below {γ γ₀ ε : ℝ}
    (h1 : 2 * ε < |γ - γ₀|) (h2 : 2 * ε < |γ + γ₀|) :
    γ₀ ≤ |γ| ∨ |γ| < γ₀ - 2 * ε := by
  have h := two_mul_lt_abs_abs_sub h1 h2
  rcases le_or_gt γ₀ |γ| with hle | hlt
  · exact Or.inl hle
  · refine Or.inr ?_
    rw [abs_of_neg (by linarith : |γ| - γ₀ < 0)] at h
    linarith

/-!
## `hstep`, supplied

The previous section left `hstep` as a hypothesis.
-/

/-- Every index is dominated by a record at or below its own height. -/
theorem exists_record_ge {ι : Type*} (γ δ : ι → ℝ)
    (hfin : ∀ M : ℝ, {i | |γ i| ≤ M}.Finite) (j : ι) :
    ∃ j', IsRecord γ δ j' ∧ |γ j'| ≤ |γ j| ∧ (δ j) ^ 2 ≤ (δ j') ^ 2 := by
  classical
  have hmem : ∀ (M : ℝ) (a : ι), a ∈ (hfin M).toFinset ↔ |γ a| ≤ M := by
    intro M a
    rw [Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hjmem : j ∈ (hfin |γ j|).toFinset := (hmem _ j).mpr (le_refl _)
  obtain ⟨j', hj'mem, hj'max⟩ := Cvs.Zeta.GaussKernel.AdmissibleKernel.exists_max_sq ⟨j, hjmem⟩ δ
  have hj'le : |γ j'| ≤ |γ j| := (hmem _ j').mp hj'mem
  refine ⟨j', fun i hi => ?_, hj'le, hj'max j hjmem⟩
  exact hj'max i ((hmem _ i).mpr (le_trans hi hj'le))

/-!
## The chain, carrying positivity

`chain` needs every stage to be a record *at positive ordinate with non-zero deviation*.
-/

/-- A record at positive ordinate with non-zero deviation — what every stage of
the chain has to be. -/
def GoodRecord {ι : Type*} (γ δ : ι → ℝ) (i : ι) : Prop :=
  IsRecord γ δ i ∧ 0 < γ i ∧ δ i ≠ 0

/-- The family reflects: anything off the line has a partner at positive
ordinate with the same `|γ|` and the same `δ²`.  For `ζ` this is conjugation
together with the absence of a real off-line zero. -/
def HasMirror {ι : Type*} (γ δ : ι → ℝ) : Prop :=
  ∀ i, δ i ≠ 0 → ∃ i', 0 < γ i' ∧ |γ i'| = |γ i| ∧ (δ i') ^ 2 = (δ i) ^ 2

/-- `IsRecord` depends on `i` only through `|γ i|` and `δ i²`, so the mirror
carries it. -/
theorem goodRecord_of_record (hm : HasMirror γ δ) {i : ι}
    (hrec : IsRecord γ δ i) (hδ : δ i ≠ 0) :
    ∃ i', GoodRecord γ δ i' ∧ |γ i'| = |γ i| ∧ (δ i') ^ 2 = (δ i) ^ 2 := by
  obtain ⟨i', hpos, habs, hsq⟩ := hm i hδ
  have hδ' : δ i' ≠ 0 := by
    intro h
    rw [h] at hsq
    exact hδ (by nlinarith [hsq, sq_nonneg (δ i)])
  exact ⟨i', ⟨fun k hk => by rw [hsq]; exact hrec k (by rwa [← habs]), hpos, hδ'⟩,
    habs, hsq⟩

-- prose-lint-allow: R3 'cannot fail everywhere' is this theorem's statement, not a dead end

/-! ## Sanity: the machinery has content

`chain_card_le` would say nothing if `StepUp` were satisfiable for free.  It is
not: a step demands `0 < u` and a gain of `u²`, so it strictly increases `δ²`,
and the conclusion already fails over a finite index. -/

/-!
## The rate is a Lorentzian interval

`ampRate_eq_abs` gives `δ² − (|γ| − a)²`, a *difference* of two squares.
-/

end Cvs.GaussKernel
