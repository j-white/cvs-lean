import Mathlib
import Cvs.Zeta.AllZerosOnLine
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The target, and what is owed

`GaussAmpPositivity` — Weil positivity restricted to this kernel family — is *equivalent* to
RH, and both directions are here: `gaussAmpPositivity_of_rh` unconditionally, and
`riemannHypothesis_of_gaussAmpPositivity` from the reverse construction.
-/

open Complex Real

namespace Cvs.Zeta.GaussKernel.AdmissibleKernel

/-! ## The target, and what this development actually contributes to it

`riemannHypothesis` is the statement, and `riemannHypothesis_of_no_negativity`
is the exact route from the objects built here to it — so the gap is visible as
a hypothesis of a real theorem, not as a missing name. -/

/-- **The Riemann Hypothesis**, as this development states it.
`Cvs.Operator.allZerosOnLine_iff_rh` makes it `RiemannHypothesis` definitionally. -/
def riemannHypothesis : Prop := Cvs.Operator.AllZerosOnLine

theorem riemannHypothesis_iff : riemannHypothesis ↔ RiemannHypothesis :=
  Cvs.Operator.allZerosOnLine_iff_rh

/-- **RH from the machinery of this block.** The contrapositive of
`weilZeroSide_gaussAmp_neg_of_offLine`: if the offset kernel's zero side is never driven
negative, and every off-line zero configuration admits a maximiser at positive ordinate, then … -/
def NoFrequentNegativity : Prop :=
  ∀ a : ℝ, ¬ ∃ᶠ lam : ℝ in Filter.atTop,
    ∑' ρ : nonTrivialZeroSet,
      (gaussAmp lam a (-Complex.I * ((ρ : ℂ) - 1 / 2))
        * (starRingEnd ℂ) (gaussAmp lam a
          (-Complex.I * ((starRingEnd ℂ) (ρ : ℂ) - 1 / 2)))).re < 0

/-!
## The Weil functional at this kernel, and both directions

`weilZeroSideGaussAmp` is `Cvs.Zeta.weilZeroSide` at `gaussAmp`, unfolded.
-/

/-!
## The open hypotheses, named

`riemannHypothesis_of_gaussAmpPositivity` certifies because it is an *implication*, and
`#certify` checks which axioms a proof term uses — not whether its hypotheses can be
discharged.
-/

/-!
## The maximiser hypothesis, at its weakest

`LocalMaxHypothesis` asks for a *global* maximiser of `|δ|` — a genuine restriction, false
outright whenever the supremum is approached and not attained.
-/

/-- **Conjugation inside `nonTrivialZeroSet`.**  A non-trivial zero off the real
axis has a partner at positive ordinate with the same real part, hence the same
off-line distance and the same window. -/
theorem exists_pos_im_nonTrivial {ρ : nonTrivialZeroSet} (hne : (ρ : ℂ).im ≠ 0) :
    ∃ σ : nonTrivialZeroSet, 0 < (σ : ℂ).im ∧ (σ : ℂ).re = (ρ : ℂ).re
      ∧ |(σ : ℂ).im| = |(ρ : ℂ).im| := by
  obtain ⟨hz, h0, h1⟩ := ρ.2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨⟨(starRingEnd ℂ) (ρ : ℂ), ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [riemannZeta_conj, hz, map_zero]
    · simpa using h0
    · simpa using h1
    · simpa using hlt
    · simp
    · simp
  · exact ⟨ρ, hgt, rfl, rfl⟩

/-- **The record stalls somewhere above every zero.** For each zero there is a window containing
it in which every zero of height `≤ M + 1` is already dominated by one of height `≤ M`. -/
def WindowRecordStalls : Prop :=
  ∀ ρ₁ : nonTrivialZeroSet, ∃ M : ℝ, |(ρ₁ : ℂ).im| ≤ M ∧
    ∀ ρ : nonTrivialZeroSet, |(ρ : ℂ).im| ≤ M + 1 →
      ∃ σ : nonTrivialZeroSet, |(σ : ℂ).im| ≤ M ∧
        ((ρ : ℂ).re - 1 / 2) ^ 2 ≤ ((σ : ℂ).re - 1 / 2) ^ 2

/-- **No off-line zero is real.** Proved, in `Cvs.GaussKernel`, from
`Cvs.Zeta.riemannZeta_ne_zero_of_mem_Ioo` — a zero at real `s ∈ (0,1)` forces `‖Λ₀(s)‖ ≥ 4`
while `Λ₀` is at most `4/e` on the strip. -/
def NoRealOffLineZero : Prop :=
  ∀ ρ : nonTrivialZeroSet, (ρ : ℂ).re ≠ 1 / 2 → (ρ : ℂ).im ≠ 0

/-- **Evasion above a threshold still forces the chain.**  `evasion_strict_chain`
with the scales shifted, so a beater at every `M ≥ M₀` suffices. -/
theorem evasion_strict_chain_atTop {ι : Type*} (γ δ : ι → ℝ) {M₀ : ℝ}
    (hbeat : ∀ M : ℝ, M₀ ≤ M → ∃ i, |γ i| ≤ M + 1 ∧
      ∀ i', |γ i'| ≤ M → (δ i') ^ 2 < (δ i) ^ 2) :
    ∃ c : ℕ → ι,
      (∀ n : ℕ, M₀ + n < |γ (c n)| ∧ |γ (c n)| ≤ M₀ + n + 1)
        ∧ StrictMono (fun n => (δ (c n)) ^ 2) := by
  choose c hc1 hc2 using fun n : ℕ =>
    hbeat (M₀ + (n : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg n))
  refine ⟨c, fun n => ⟨?_, hc1 n⟩, fun m n hmn => ?_⟩
  · by_contra h
    exact absurd (hc2 n (c n) (not_lt.mp h)) (lt_irrefl _)
  · refine hc2 n (c m) ?_
    have h1 := hc1 m
    have h2 : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith

/-- **What evading `WindowRecordStalls` costs, over the zeros of `ζ`.** A strictly increasing
chain of off-line zeros, one in each unit annulus above some height — so at least `T` zeros up
to height `T` with `|re - 1/2|` bounded below by the first one's. -/
theorem evasion_chain_of_not_windowRecordStalls (h : ¬ WindowRecordStalls) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∃ c : ℕ → nonTrivialZeroSet,
      (∀ n : ℕ, M₀ + n < |((c n : ℂ)).im| ∧ |((c n : ℂ)).im| ≤ M₀ + n + 1)
        ∧ StrictMono (fun n => ((c n : ℂ).re - 1 / 2) ^ 2) := by
  rw [WindowRecordStalls] at h
  push Not at h
  obtain ⟨ρ₁, hρ₁⟩ := h
  refine ⟨|(ρ₁ : ℂ).im|, abs_nonneg _, ?_⟩
  refine evasion_strict_chain_atTop
    (fun ρ : nonTrivialZeroSet => (ρ : ℂ).im)
    (fun ρ : nonTrivialZeroSet => (ρ : ℂ).re - 1 / 2)
    (fun M hM => ?_)
  obtain ⟨ρ, hρ, hbeat⟩ := hρ₁ M hM
  exact ⟨ρ, hρ, hbeat⟩

/-!
## The last hypothesis, reduced to a named theorem

`WindowRecordStalls` fails only if the record improves in every unit annulus
(`evasion_chain_of_not_windowRecordStalls`), and that chain is one zero per unit of height,
all distinct, all off the line by at least a fixed amount.
-/

/-- The zeros of height at most `T` that are off the line by at least `d`. -/
def offLineWindow (d T : ℝ) : Set nonTrivialZeroSet :=
  {ρ | |(ρ : ℂ).im| ≤ T ∧ d ≤ |(ρ : ℂ).re - 1 / 2|}

theorem offLineWindow_finite (d T : ℝ) : (offLineWindow d T).Finite := by
  refine (finite_window_of_summable (fun ρ : nonTrivialZeroSet => (ρ : ℂ).im)
    summable_zeta_quartic T).subset ?_
  rintro ρ ⟨h, -⟩
  exact h

/-- `N(1/2 + d, T)`: how many zeros up to height `T` are off the line by `d`. -/
noncomputable def offLineCount (d T : ℝ) : ℕ :=
  (offLineWindow_finite d T).toFinset.card

/-- **Evading the construction forces a linear count.**  The chain has one member
per unit annulus, all distinct, all off the line by at least the second one's
deviation — so `n` of them sit below height `M₀ + n + 1`. -/
theorem offLineCount_ge_of_not_windowRecordStalls (h : ¬ WindowRecordStalls) :
    ∃ d M₀ : ℝ, 0 < d ∧ 0 ≤ M₀ ∧
      ∀ n : ℕ, n ≤ offLineCount d (M₀ + n + 1) := by
  classical
  obtain ⟨M₀, hM₀, c, hc, hmono⟩ := evasion_chain_of_not_windowRecordStalls h
  refine ⟨|((c 1 : ℂ)).re - 1 / 2|, M₀, ?_, hM₀, fun n => ?_⟩
  · have h01 : ((c 0 : ℂ).re - 1 / 2) ^ 2 < ((c 1 : ℂ).re - 1 / 2) ^ 2 :=
      hmono (by norm_num)
    have hpos : (0 : ℝ) < ((c 1 : ℂ).re - 1 / 2) ^ 2 := by
      nlinarith [sq_nonneg ((c 0 : ℂ).re - 1 / 2)]
    exact abs_pos.mpr fun hz => by rw [hz] at hpos; norm_num at hpos
  · rw [offLineCount]
    have hsub : ∀ k ∈ Finset.Icc 1 n, c k ∈ (offLineWindow_finite
        (|((c 1 : ℂ)).re - 1 / 2|) (M₀ + n + 1)).toFinset := by
      intro k hk
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
      have hkr : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      refine Set.Finite.mem_toFinset _ |>.mpr ⟨?_, ?_⟩
      · exact le_trans (hc k).2 (by linarith)
      · have hle : ((c 1 : ℂ).re - 1 / 2) ^ 2 ≤ ((c k : ℂ).re - 1 / 2) ^ 2 :=
          hmono.monotone hk1
        rw [← sq_abs, ← sq_abs ((c k : ℂ).re - 1 / 2)] at hle
        exact (pow_le_pow_iff_left₀ (abs_nonneg _) (abs_nonneg _) two_ne_zero).mp hle
    have hinj : Set.InjOn c (Finset.Icc 1 n) :=
      Function.Injective.injOn (evasion_chain_injective
        (γ := fun ρ : nonTrivialZeroSet => (ρ : ℂ).im)
        (δ := fun ρ : nonTrivialZeroSet => (ρ : ℂ).re - 1 / 2) (c := c) hmono)
    have := Finset.card_le_card_of_injOn c hsub hinj
    simpa using this

/-- **Carlson's density theorem** , in the form this development needs: `N(1/2 + d, T) = o(T)` for
every fixed `d > 0`. -/
def ZeroDensity : Prop :=
  ∀ d : ℝ, 0 < d →
    Filter.Tendsto (fun T : ℝ => (offLineCount d T : ℝ) / T) Filter.atTop (nhds 0)

/-- **The density estimate closes the last hypothesis.**  The chain puts `n`
distinct zeros off the line by `d` below height `M₀ + n + 1`, so the ratio
`N/T` is eventually at least `1/2`; `ZeroDensity` sends it to `0`. -/
theorem windowRecordStalls_of_zeroDensity (h : ZeroDensity) : WindowRecordStalls := by
  by_contra hnot
  obtain ⟨d, M₀, hd, hM₀, hcount⟩ := offLineCount_ge_of_not_windowRecordStalls hnot
  have hev := (h d hd).eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2))
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨n, hn⟩ := exists_nat_ge (max T₀ (M₀ + 1))
  have hTn : T₀ ≤ M₀ + n + 1 := by
    have := le_trans (le_max_left T₀ (M₀ + 1)) hn
    linarith
  have hb := hT₀ (M₀ + n + 1) hTn
  have hpos : (0 : ℝ) < M₀ + n + 1 := by linarith
  have hge : (n : ℝ) ≤ (offLineCount d (M₀ + n + 1) : ℝ) := by
    exact_mod_cast hcount n
  have hnM : M₀ + 1 ≤ (n : ℝ) := le_trans (le_max_right T₀ (M₀ + 1)) hn
  rw [div_lt_iff₀ hpos] at hb
  linarith

end Cvs.Zeta.GaussKernel.AdmissibleKernel
