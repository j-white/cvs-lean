import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A backward comparison principle and Riccati barriers

A function continuous on `[a, b]` whose derivative is positive in `(a, b)` wherever the function is positive, and
which is `≤ 0` at `b`, is `≤ 0` on all of `[a, b]`; no derivative is assumed at the endpoints. As a corollary, a
solution of `U' = U²/p − q` lies below any nonnegative supersolution-in-reverse `W' ≤ W²/p − q` that dominates it at `b`.
-/

noncomputable section
open Real Set Filter Topology
namespace Cvs.Upstream.BackwardComparisonRiccati

/-- A function continuous on `[a, b]`, with positive derivative in `(a, b)` wherever it is positive, and `≤ 0` at
`b`, is `≤ 0` on `[a, b]`. -/
theorem nonpos_of_deriv_pos {D D' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn D (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt D (D' x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < D x → 0 < D' x) (hb : D b ≤ 0) :
    ∀ x ∈ Icc a b, D x ≤ 0 := by
  intro s hs
  by_contra hDs
  push Not at hDs
  have hsb : s < b := lt_of_le_of_ne hs.2 (by rintro rfl; linarith)
  set S : Set ℝ := Icc s b ∩ D ⁻¹' Iic (D s / 2) with hS
  have hSc : IsClosed S :=
    (hc.mono (Icc_subset_Icc hs.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hbS : b ∈ S := ⟨⟨hsb.le, le_rfl⟩, by simp only [mem_preimage, mem_Iic]; linarith⟩
  have hSne : S.Nonempty := ⟨b, hbS⟩
  have hSbdd : BddBelow S := ⟨s, fun y hy => hy.1.1⟩
  obtain ⟨t, ht⟩ : ∃ t, t = sInf S := ⟨_, rfl⟩
  have htS : t ∈ S := ht ▸ hSc.csInf_mem hSne hSbdd
  have hst : s ≤ t := htS.1.1
  have htb : t ≤ b := htS.1.2
  have hDt : D t ≤ D s / 2 := htS.2
  have hst' : s < t := lt_of_le_of_ne hst (by rintro rfl; linarith)
  -- `D > D s / 2 > 0` on `[s, t)`
  have hlow : ∀ y ∈ Ico s t, D s / 2 < D y := by
    intro y hy
    by_contra h
    push Not at h
    have : y ∈ S := ⟨⟨hy.1, hy.2.le.trans htb⟩, h⟩
    exact absurd (ht ▸ csInf_le hSbdd this) (not_le.mpr hy.2)
  have hmono : MonotoneOn D (Icc s t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := D') (convex_Icc s t)
      (hc.mono (Icc_subset_Icc hs.1 htb))
    · intro y hy
      rw [interior_Icc] at hy
      exact (hd y ⟨lt_of_le_of_lt hs.1 hy.1, lt_of_lt_of_le hy.2 htb⟩).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyab : y ∈ Ioo a b := ⟨lt_of_le_of_lt hs.1 hy.1, lt_of_lt_of_le hy.2 htb⟩
      exact (hpos y hyab (by linarith [hlow y ⟨hy.1.le, hy.2⟩])).le
  have := hmono ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  linarith

/-- If `U' = U²/p − q` and `W' ≤ W²/p − q` with `p > 0`, `W ≥ 0` inside, and `U ≤ W` at `b`, then `U ≤ W` on
`[a, b]`. -/
theorem le_of_riccati {U U' W W' p q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hUc : ContinuousOn U (Icc a b)) (hWc : ContinuousOn W (Icc a b))
    (hU : ∀ x ∈ Ioo a b, HasDerivAt U (U' x) x) (hW : ∀ x ∈ Ioo a b, HasDerivAt W (W' x) x)
    (hp : ∀ x ∈ Ioo a b, 0 < p x) (hW0 : ∀ x ∈ Ioo a b, 0 ≤ W x)
    (hUeq : ∀ x ∈ Ioo a b, U' x = U x ^ 2 / p x - q x)
    (hWle : ∀ x ∈ Ioo a b, W' x ≤ W x ^ 2 / p x - q x) (hb : U b ≤ W b) :
    ∀ x ∈ Icc a b, U x ≤ W x := by
  intro x hx
  have h := nonpos_of_deriv_pos (D := fun y => U y - W y) (D' := fun y => U' y - W' y) hab
    (hUc.sub hWc) (fun y hy => (hU y hy).sub (hW y hy)) ?_ (show U b - W b ≤ 0 by linarith) x hx
  · have h' : U x - W x ≤ 0 := h
    linarith
  · intro y hy hD
    change 0 < U y - W y at hD
    show 0 < U' y - W' y
    have hpy := hp y hy
    have hWy := hW0 y hy
    have hsq : W y ^ 2 < U y ^ 2 := by nlinarith
    have : W y ^ 2 / p y < U y ^ 2 / p y := div_lt_div_of_pos_right hsq hpy
    linarith [hUeq y hy, hWle y hy]

end Cvs.Upstream.BackwardComparisonRiccati
