import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open scoped BigOperators

namespace Cvs.Operator

open Real Finset Int

variable {K : ℕ}

/-- The box index of `m`: which of the `Q` sub-intervals each coordinate's
fractional part falls into.  `fract < 1` keeps it below `Q`, so no clamping. -/
private noncomputable def box (u : Fin K → ℝ) (Q : ℕ) (m : ℕ) (i : Fin K) : ℕ :=
  (⌊Int.fract (u i * m) * Q⌋).toNat

private lemma box_lt (u : Fin K → ℝ) {Q : ℕ} (hQ : 0 < Q) (m : ℕ) (i : Fin K) :
    box u Q m i < Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h1 : Int.fract (u i * m) * Q < Q := by
    have := Int.fract_lt_one (u i * m)
    nlinarith
  have h2 : (⌊Int.fract (u i * m) * Q⌋ : ℤ) < (Q : ℤ) := by
    exact_mod_cast Int.floor_lt.mpr (by exact_mod_cast h1)
  have h3 : (0 : ℤ) ≤ ⌊Int.fract (u i * m) * Q⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  unfold box
  omega

/-- Two modes in the same box give a difference that is uniformly close to the
integers. -/
private lemma approx_of_collide (u : Fin K → ℝ) {Q : ℕ} (hQ : 0 < Q) {a b : ℕ}
    (hab : a < b) (hb : b ≤ Q ^ K) (h : box u Q a = box u Q b) :
    ∃ n : ℕ, 0 < n ∧ n ≤ Q ^ K ∧
      ∀ i, ‖((u i * n : ℝ) : UnitAddCircle)‖ ≤ 1 / Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨b - a, by omega, by omega, fun i => ?_⟩
  have hfloor : ⌊Int.fract (u i * a) * Q⌋ = ⌊Int.fract (u i * b) * Q⌋ := by
    have := congrFun h i
    unfold box at this
    have h1 : (0 : ℤ) ≤ ⌊Int.fract (u i * a) * Q⌋ :=
      Int.floor_nonneg.mpr (by positivity)
    have h2 : (0 : ℤ) ≤ ⌊Int.fract (u i * b) * Q⌋ :=
      Int.floor_nonneg.mpr (by positivity)
    omega
  -- the two fractional parts differ by less than `1/Q`
  have hclose : |Int.fract (u i * b) - Int.fract (u i * a)| < 1 / Q := by
    have h1 : |Int.fract (u i * b) * Q - Int.fract (u i * a) * Q| < 1 :=
      abs_sub_lt_one_of_floor_eq_floor hfloor.symm
    rw [← sub_mul, abs_mul, abs_of_pos hQ'] at h1
    rw [lt_div_iff₀ hQ']
    linarith
  -- and that difference is `u i * (b - a)` up to an integer
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := by
    push_cast [Nat.cast_sub hab.le]; ring
  have hint : u i * ((b - a : ℕ) : ℝ) - ((⌊u i * b⌋ - ⌊u i * a⌋ : ℤ) : ℝ)
      = Int.fract (u i * b) - Int.fract (u i * a) := by
    rw [hcast, Int.fract, Int.fract]; push_cast; ring
  rw [UnitAddCircle.norm_eq]
  calc |u i * ((b - a : ℕ) : ℝ) - round (u i * ((b - a : ℕ) : ℝ))|
      ≤ |u i * ((b - a : ℕ) : ℝ) - ((⌊u i * b⌋ - ⌊u i * a⌋ : ℤ) : ℝ)| :=
        round_le _ _
    _ = |Int.fract (u i * b) - Int.fract (u i * a)| := by rw [hint]
    _ ≤ 1 / Q := hclose.le

/-- **Simultaneous Dirichlet.**  For any `u : Fin K → ℝ` and `Q > 0` there is a
mode `n` with `0 < n ≤ Q ^ K` putting every `u i * n` within `1/Q` of an
integer. -/
theorem exists_simultaneous_approx (u : Fin K → ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ n : ℕ, 0 < n ∧ n ≤ Q ^ K ∧
      ∀ i, ‖((u i * n : ℝ) : UnitAddCircle)‖ ≤ 1 / Q := by
  classical
  set F : ℕ → (Fin K → Fin Q) :=
    fun m i => ⟨box u Q m i, box_lt u hQ m i⟩ with hF
  have hcard : (Finset.univ : Finset (Fin K → Fin Q)).card
      < (Finset.range (Q ^ K + 1)).card := by
    simp
  obtain ⟨a, ha, b, hb, hab, hFab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (fun m _ => Finset.mem_univ (F m))
  have hbox : ∀ {x y : ℕ}, F x = F y → box u Q x = box u Q y := by
    intro x y hxy
    funext i
    have := congrFun hxy i
    simpa [hF] using congrArg Fin.val this
  rcases lt_or_gt_of_ne hab with h | h
  · exact approx_of_collide u hQ h
      (by have := Finset.mem_range.mp hb; omega) (hbox hFab)
  · exact approx_of_collide u hQ h
      (by have := Finset.mem_range.mp ha; omega) (hbox hFab.symm)

end Cvs.Operator
