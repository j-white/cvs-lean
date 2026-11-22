import Mathlib
import Cvs.Prolate.ConverseLevelCount
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SturmPolyGaussComparison

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The quintic comparison: no even level of index three or more below `11γ² + 10`

`z = ξ(ξ⁴ + bξ² + d)e^{−Gξ²/2}` solves `((1 − ξ²)z')' = Tz` with `T` a quartic once `b` and `d`
satisfy two polynomial conditions, which a root `bG ∈ [−5, 0]` of a cubic supplies for `G > 1/2`.
With `G² + 13G = c²`, `c²ξ² − T` exceeds `11G + 30 + 4bG ≥ 11G + 10` on `(0, 1)`, so every even
level of index at least three lies at or above `11γ² + 10`, which is at least `19c/2` for `c ≥ 41`.
-/

noncomputable section

open Real Set Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EvenLevelIndexLemma Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Prolate.QuinticLevelComparison

/-! ### The comparison function and its zeros -/

/-- `ξ(ξ⁴ + bξ² + d)` has at most two zeros in `(0, 1)`. -/
theorem encard_zeros_le (b d : ℝ) :
    {t | t ∈ Ioo (0 : ℝ) 1 ∧ t ^ 5 + b * t ^ 3 + d * t = 0}.encard ≤ 2 := by
  set S := {t | t ∈ Ioo (0 : ℝ) 1 ∧ t ^ 5 + b * t ^ 3 + d * t = 0} with hS
  have hq : ∀ t ∈ S, t ^ 4 + b * t ^ 2 + d = 0 := fun t ht => by
    have h : t * (t ^ 4 + b * t ^ 2 + d) = 0 := by linear_combination ht.2
    exact (mul_eq_zero.mp h).resolve_left ht.1.1.ne'
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h, Set.encard_empty]; norm_num
  have hsub : S ⊆ {x, √(-b - x ^ 2)} := by
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff]
    by_cases hyx : y = x
    · exact Or.inl hyx
    right
    have hx0 := hx.1.1
    have hy0 := hy.1.1
    have hm : (y ^ 2 - x ^ 2) * (y ^ 2 + x ^ 2 + b) = 0 := by
      linear_combination hq y hy - hq x hx
    rcases mul_eq_zero.mp hm with h | h
    · exfalso
      have h' : (y - x) * (y + x) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact hyx (by linarith)
      · linarith
    · have hy2 : y ^ 2 = -b - x ^ 2 := by linarith
      rw [← hy2, Real.sqrt_sq hy0.le]
  calc S.encard ≤ ({x, √(-b - x ^ 2)} : Set ℝ).encard := Set.encard_le_encard hsub
    _ ≤ 2 := (Set.encard_insert_le _ _).trans (by rw [Set.encard_singleton]; rfl)

/-- The potential `(G² + 13G)ξ² − G²ξ⁴ − (11G + 30 + 4bG)` of the quintic comparison function. -/
def potThree (G b : ℝ) : C(ℝ, ℝ) :=
  ⟨fun s => (G ^ 2 + 13 * G) * s ^ 2 - G ^ 2 * s ^ 4 - (11 * G + 30 + 4 * b * G), by fun_prop⟩

/-- **The quintic comparison**: for `G ≠ 0` with `G² + 13G = c²`, coefficients `b, d` solving the
two conditions and `Λ ≤ 11G + 30 + 4bG`, `regSol (sqC c) Λ` has no three zeros in `(0, 1)`. -/
theorem not_hasZeros_three_of_sq {c G b d Λ : ℝ} (hG : G ≠ 0) (hc : G ^ 2 + 13 * G = c ^ 2)
    (h1 : 2 * b ^ 2 * G + 2 * b * G + 9 * b - 4 * d * G + 10 = 0)
    (h2 : 2 * b * d * G + 3 * b + 4 * d * G + 14 * d = 0)
    (hΛ : Λ ≤ 11 * G + 30 + 4 * b * G) : ¬HasZeros (sqC c) Λ 3 := by
  have hP : ∀ s : ℝ, HasDerivAt (fun s => s ^ 5 + b * s ^ 3 + d * s)
      (5 * s ^ 4 + 3 * b * s ^ 2 + d) s := fun s =>
    (((hasDerivAt_pow 5 s).add ((hasDerivAt_pow 3 s).const_mul b)).add
      ((hasDerivAt_id' s).const_mul d)).congr_deriv (by push_cast; ring)
  have hP₁ : ∀ s : ℝ, HasDerivAt (fun s => 5 * s ^ 4 + 3 * b * s ^ 2 + d)
      (20 * s ^ 3 + 6 * b * s) s := fun s =>
    (((hasDerivAt_pow 4 s).const_mul 5).add
      ((hasDerivAt_pow 2 s).const_mul (3 * b))).add_const d |>.congr_deriv (by push_cast; ring)
  refine Cvs.Prolate.SturmPolyGaussComparison.not_hasZeros_of_polyGauss (m := 2) (Q := potThree G b) (χ := 0) (G := G)
    (fun s _ => hP s) (fun s _ => hP₁ s) (fun s _ => ?_) (fun t ht => ?_)
    ((encard_zeros_le b d).trans le_rfl)
  · simp only [potThree, ContinuousMap.coe_mk]
    linear_combination (2 * s ^ 3) * h1 + (2 * s) * h2
  · have h4 : 0 < G ^ 2 * t ^ 4 := by have := ht.1; positivity
    have hct : c ^ 2 * t ^ 2 = (G ^ 2 + 13 * G) * t ^ 2 := by rw [hc]
    simp only [potThree, sqC, ContinuousMap.coe_mk]
    linarith

/-! ### The coefficients from a root of the cubic -/

/-- The cubic `2B³ + (6G + 23)B² + (4G² + 48G + 63)B + 20G² + 70G` in `B = bG`. -/
def cubic (G B : ℝ) : ℝ :=
  2 * B ^ 3 + (6 * G + 23) * B ^ 2 + (4 * G ^ 2 + 48 * G + 63) * B + 20 * G ^ 2 + 70 * G

/-- **The cubic has a root in `[−5, 0]`** for `G > 1/2`: it is `10 − 20G` at `−5` and
`20G² + 70G` at `0`. -/
theorem exists_cubic_eq_zero {G : ℝ} (hG : 1 / 2 < G) : ∃ B ∈ Icc (-5 : ℝ) 0, cubic G B = 0 := by
  have hcont : ContinuousOn (cubic G) (Icc (-5) 0) := by unfold cubic; fun_prop
  have hm : cubic G (-5) ≤ 0 := by unfold cubic; nlinarith
  have hp : 0 ≤ cubic G 0 := by unfold cubic; nlinarith
  exact intermediate_value_Icc (by norm_num) hcont ⟨hm, hp⟩

/-- **Coefficients of the quintic comparison**: for `G > 1/2` there are `b, d` solving the two
conditions with `bG ∈ [−5, 0]`. -/
theorem exists_coeffs {G : ℝ} (hG : 1 / 2 < G) : ∃ b d : ℝ,
    2 * b ^ 2 * G + 2 * b * G + 9 * b - 4 * d * G + 10 = 0 ∧
    2 * b * d * G + 3 * b + 4 * d * G + 14 * d = 0 ∧ -5 ≤ b * G ∧ b * G ≤ 0 := by
  obtain ⟨B, hB, hF⟩ := exists_cubic_eq_zero hG
  have hG0 : G ≠ 0 := by linarith
  have hbG : B / G * G = B := div_mul_cancel₀ B hG0
  refine ⟨B / G, (2 * B ^ 2 + 2 * B * G + 9 * B + 10 * G) / (4 * G ^ 2), ?_, ?_, ?_, ?_⟩
  · field_simp; ring
  · have h : 2 * (B / G) * ((2 * B ^ 2 + 2 * B * G + 9 * B + 10 * G) / (4 * G ^ 2)) * G
        + 3 * (B / G) + 4 * ((2 * B ^ 2 + 2 * B * G + 9 * B + 10 * G) / (4 * G ^ 2)) * G
        + 14 * ((2 * B ^ 2 + 2 * B * G + 9 * B + 10 * G) / (4 * G ^ 2))
        = cubic G B / (2 * G ^ 2) := by
      unfold cubic; field_simp; ring
    rw [h, hF, zero_div]
  · rw [hbG]; exact hB.1
  · rw [hbG]; exact hB.2

/-! ### The scale `G² + 13G = c²` -/

/-- The positive root `G = (√(169 + 4c²) − 13)/2` of `G² + 13G = c²`. -/
def gThree (c : ℝ) : ℝ := (√(169 + 4 * c ^ 2) - 13) / 2

/-- `gThree c` solves `G² + 13G = c²`. -/
theorem gThree_sq_add (c : ℝ) : gThree c ^ 2 + 13 * gThree c = c ^ 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 169 + 4 * c ^ 2 by positivity)
  unfold gThree
  linear_combination h / 4

/-- `gThree c > 1/2` for `c² > 27/4`. -/
theorem half_lt_gThree {c : ℝ} (hc : 27 / 4 < c ^ 2) : 1 / 2 < gThree c := by
  have h : (14 : ℝ) < √(169 + 4 * c ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  unfold gThree
  linarith

/-- `gThree c ≥ |c| − 13/2`. -/
theorem abs_sub_le_gThree (c : ℝ) : |c| - 13 / 2 ≤ gThree c := by
  have h : 2 * |c| ≤ √(169 + 4 * c ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity), mul_pow, sq_abs]
    linarith
  unfold gThree
  linarith

/-! ### Levels of index three and above -/

/-- **No three zeros below `11γ² + 10`**: for `c² > 27/4` and `Λ ≤ 11 gThree c + 10`,
`regSol (sqC c) Λ` has no three zeros in `(0, 1)`. -/
theorem not_hasZeros_three {c Λ : ℝ} (hc : 27 / 4 < c ^ 2) (hΛ : Λ ≤ 11 * gThree c + 10) :
    ¬HasZeros (sqC c) Λ 3 := by
  have hG := half_lt_gThree hc
  obtain ⟨b, d, h1, h2, hb, -⟩ := exists_coeffs hG
  exact not_hasZeros_three_of_sq (by linarith : (0 : ℝ) < gThree c).ne' (gThree_sq_add c) h1 h2
    (by linarith)

/-- **Every even level of index at least three lies at or above `11γ² + 10`**, `γ² = gThree c`,
for `c² > 27/4`. -/
theorem le_of_isLevelIdx_three_le {c χ : ℝ} {j : ℕ} (hc : 27 / 4 < c ^ 2)
    (hχ : IsLevelIdx c j χ) (hj : 3 ≤ j) : 11 * gThree c + 10 ≤ χ :=
  Cvs.Prolate.ConverseLevelCount.le_of_not_hasZeros (k := 2) (not_hasZeros_three hc le_rfl) hχ hj

end Cvs.Prolate.QuinticLevelComparison
