import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The minimisation principle, with compactness only on bounded-form sequences

    bounded-form sequences in `S` have convergent subsequences with limit in `S`,
    `Q` is lower semicontinuous and bounded below on `S`   ⟹   `Q` attains its infimum on `S`

which is what a form whose sublevel sets are compact, on a sphere that is not, can offer.
-/

noncomputable section

open Filter Topology

namespace Cvs.WeilForm.MinimisationPrincipleLsc

variable {E : Type*} [NormedAddCommGroup E]

/-- **A lower semicontinuous form with compact sublevel sets attains its infimum.** -/
theorem exists_min_of_lsc {S : Set E} {Q : E → ℝ} {lam : ℝ}
    (hne : S.Nonempty)
    (hbot : ∀ v ∈ S, lam ≤ Q v)
    (hinf : ∀ ε > 0, ∃ v ∈ S, Q v < lam + ε)
    (hsub : ∀ (c : ℝ) (x : ℕ → E), (∀ n, x n ∈ S) → (∀ n, Q (x n) ≤ c) →
      ∃ (φ : ℕ → ℕ) (y : E), StrictMono φ ∧ y ∈ S ∧
        Tendsto (fun k => ‖x (φ k) - y‖) atTop (𝓝 0))
    (hlsc : ∀ (x : ℕ → E) (y : E), (∀ n, x n ∈ S) → y ∈ S →
      Tendsto (fun k => ‖x k - y‖) atTop (𝓝 0) →
      ∀ c : ℝ, (∀ k, Q (x k) ≤ c) → Q y ≤ c) :
    ∃ η ∈ S, Q η = lam := by
  classical
  have hchoice : ∀ n : ℕ, ∃ v ∈ S, Q v < lam + 1 / (n + 1 : ℝ) := fun n =>
    hinf (1 / (n + 1 : ℝ)) (by positivity)
  choose x hxS hxQ using hchoice
  have hbdd : ∀ n, Q (x n) ≤ lam + 1 := fun n => by
    have h := hxQ n
    have : 1 / (n + 1 : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  obtain ⟨φ, y, hmono, hyS, hconv⟩ := hsub (lam + 1) x hxS hbdd
  refine ⟨y, hyS, le_antisymm ?_ (hbot y hyS)⟩
  -- every tail of the subsequence sits below `lam + 1/(n+1)`, so `Q y` does too, for every `n`
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hcut : ∀ k, Q (x (φ (k + n))) ≤ lam + 1 / (n + 1 : ℝ) := by
    intro k
    refine le_of_lt (lt_of_lt_of_le (hxQ _) ?_)
    have hn_le : n ≤ φ (k + n) := le_trans (Nat.le_add_left n k) hmono.le_apply
    have hle : (n : ℝ) + 1 ≤ (φ (k + n) : ℝ) + 1 := by
      have : (n : ℝ) ≤ (φ (k + n) : ℝ) := by exact_mod_cast hn_le
      linarith
    have hpos : (0:ℝ) < (n : ℝ) + 1 := by positivity
    gcongr
  have hlim := hlsc (fun k => x (φ (k + n))) y (fun k => hxS _) hyS
    (hconv.comp (tendsto_add_atTop_nat n)) _ hcut
  linarith

end Cvs.WeilForm.MinimisationPrincipleLsc
