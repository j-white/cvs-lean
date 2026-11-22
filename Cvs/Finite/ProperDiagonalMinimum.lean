import Mathlib
import Cvs.Finite.SecularSeriesConverges

/-!
# A proper diagonal attains its minimum on any nonempty set

Only finitely many modes sit below any level, so a nonempty set of them has a smallest level.
Applied to the modes other than the bottom one, this names the second level the isolation
argument compares against.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.Finite.ProperDiagonalMinimum

variable {ι : Type*} [DecidableEq ι]

/-- **The minimum is attained.** -/
theorem exists_min_on {D : ι → ℝ} (hproper : ∀ M : ℝ, {n : ι | D n < M}.Finite)
    {S : Set ι} (hS : S.Nonempty) : ∃ m ∈ S, ∀ n ∈ S, D m ≤ D n := by
  classical
  obtain ⟨n₀, hn₀⟩ := hS
  set T : Finset ι := (hproper (D n₀ + 1)).toFinset.filter (· ∈ S) with hT
  have hn₀T : n₀ ∈ T := by
    rw [hT, Finset.mem_filter]
    refine ⟨?_, hn₀⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    linarith
  obtain ⟨m, hmT, hmin⟩ := T.exists_min_image D ⟨n₀, hn₀T⟩
  have hmS : m ∈ S := by
    rw [hT, Finset.mem_filter] at hmT
    exact hmT.2
  refine ⟨m, hmS, fun n hn => ?_⟩
  by_cases hlow : D n < D n₀ + 1
  · refine hmin n ?_
    rw [hT, Finset.mem_filter]
    exact ⟨by simpa using hlow, hn⟩
  · have hmn₀ : D m ≤ D n₀ := hmin n₀ hn₀T
    push_neg at hlow
    linarith

/-- **The second level**, as the smallest among the modes other than the bottom one. -/
theorem exists_second {D : ι → ℝ} (hproper : ∀ M : ℝ, {n : ι | D n < M}.Finite)
    {n₀ : ι} (hS : ({n : ι | n ≠ n₀}).Nonempty) :
    ∃ m : ι, m ≠ n₀ ∧ ∀ n : ι, n ≠ n₀ → D m ≤ D n := by
  obtain ⟨m, hmS, hmin⟩ := exists_min_on hproper hS
  exact ⟨m, hmS, fun n hn => hmin n hn⟩

/-! ### Isolation, assembled -/

/-- Every level is the bottom one or at least the second. -/
theorem levels_split {D : ι → ℝ} {n₀ m₁ : ι} (hD₁ : ∀ n : ι, n ≠ n₀ → D m₁ ≤ D n) (n : ι) :
    D n = D n₀ ∨ D m₁ ≤ D n := by
  by_cases h : n = n₀
  · exact Or.inl (by rw [h])
  · exact Or.inr (hD₁ n h)

/-- **Two eigenvalues cannot share the gap.**  With the bottom level simple and the second
named, the secular equation has at most one root strictly between them. -/
theorem unique_eigen_in_gap {D v : ι → ℝ} {c : ℝ} (hc : 0 < c)
    (hproper : ∀ M : ℝ, {n : ι | D n < M}.Finite)
    (hvsum : Summable fun n : ι => (v n) ^ 2) {mv : ι} (hvm : v mv ≠ 0)
    {n₀ m₁ : ι} (hD₁ : ∀ n : ι, n ≠ n₀ → D m₁ ≤ D n)
    {lam₁ lam₂ : ℝ} (hlt : lam₁ < lam₂)
    (hlo₁ : D n₀ < lam₁) (hhi₂ : lam₂ < D m₁)
    (hsec₁ : c * (∑' n : ι, (v n) ^ 2 / (lam₁ - D n)) = 1)
    (hsec₂ : c * (∑' n : ι, (v n) ^ 2 / (lam₂ - D n)) = 1) : False :=
  Cvs.Finite.SecularSeriesConverges.unique_in_gap hc (levels_split hD₁) hvsum
    (hproper (lam₁ + 1)) (hproper (lam₂ + 1)) hvm hlo₁ hhi₂ hlt hsec₁ hsec₂

end Cvs.Finite.ProperDiagonalMinimum
