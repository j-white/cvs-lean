import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.SepticLevelComparison
import Cvs.Prolate.SturmFromCentre

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even octic comparison: no even level of index four or more below `17γ² + 16`

`y = (ξ⁸ + aξ⁶ + bξ⁴ + dξ² + e)e^{−Gξ²/2}` solves `((1 − ξ²)y')' = Ty` with `T` a quartic once `a, b, d, e` satisfy
four polynomial conditions, which a root `aG ∈ [−14, 0]` of a quintic supplies for `G ≥ 5`. With `G² + 19G = c²`,
`c²ξ² − T ≥ 17G + 72 + 4aG ≥ 17G + 16` on `(0, 1)` and `y'(0) = 0`, so by Cvs.Prolate.SturmFromCentre every even level of index at least
four lies at or above `17γ² + 16`, which is at least `17c − 291/2`.
-/

noncomputable section

open Real Set Polynomial Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EvenLevelIndexLemma Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Prolate.EvenOcticLevelComparison

/-! ### The comparison function and its zeros -/

/-- `ξ⁸ + aξ⁶ + bξ⁴ + dξ² + e` has at most four zeros in `(0, 1)`. -/
theorem encard_zeros_le (a b d e : ℝ) :
    {t | t ∈ Ioo (0 : ℝ) 1 ∧ t ^ 8 + a * t ^ 6 + b * t ^ 4 + d * t ^ 2 + e = 0}.encard ≤ 4 := by
  set S := {t | t ∈ Ioo (0 : ℝ) 1 ∧ t ^ 8 + a * t ^ 6 + b * t ^ 4 + d * t ^ 2 + e = 0} with hS
  set p : ℝ[X] := X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C d * X + C e with hp
  have hp0 : p ≠ 0 := fun h => by
    have := congrArg (fun q : ℝ[X] => q.coeff 4) h
    simp [hp] at this
  have hinj : InjOn (fun t : ℝ => t ^ 2) S := fun x hx y hy hxy =>
    (pow_left_inj₀ hx.1.1.le hy.1.1.le two_ne_zero).mp hxy
  have hsub : (fun t : ℝ => t ^ 2) '' S ⊆ (p.roots.toFinset : Set ℝ) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp0, IsRoot, hp]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination ht.2
  have hdeg : p.natDegree ≤ 4 := by rw [hp]; compute_degree
  calc S.encard = ((fun t : ℝ => t ^ 2) '' S).encard := (hinj.encard_image).symm
    _ ≤ (p.roots.toFinset : Set ℝ).encard := Set.encard_le_encard hsub
    _ = (p.roots.toFinset.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ 4 := by
      have h1 := Multiset.toFinset_card_le p.roots
      have h2 := card_roots' p
      exact_mod_cast h1.trans (h2.trans hdeg)

/-- The potential `(G² + 19G)ξ² − G²ξ⁴ − (17G + 72 + 4aG)` of the octic comparison function. -/
def potEight (G a : ℝ) : C(ℝ, ℝ) :=
  ⟨fun s => (G ^ 2 + 19 * G) * s ^ 2 - G ^ 2 * s ^ 4 - (17 * G + 72 + 4 * a * G), by fun_prop⟩

/-- **The octic comparison**: for `G² + 19G = c²`, coefficients `a, b, d, e` solving the four conditions and
`Λ ≤ 17G + 72 + 4aG`, every even level of index at least four lies at or above `Λ`. -/
theorem le_of_isLevelIdx_of_sq {c G a b d e Λ χ : ℝ} {j : ℕ} (hc : G ^ 2 + 19 * G = c ^ 2)
    (h6 : 4 * G * a ^ 2 + 4 * G * a + 30 * a - 8 * G * b + 56 = 0)
    (h4 : 4 * G * a * b + 8 * G * b + 52 * b - 12 * G * d + 30 * a = 0)
    (h2 : 4 * G * a * d + 12 * G * d + 66 * d - 16 * G * e + 12 * b = 0)
    (h0 : 4 * G * a * e + 16 * G * e + 72 * e + 2 * d = 0)
    (hΛ : Λ ≤ 17 * G + 72 + 4 * a * G) (hχ : IsLevelIdx c j χ) (hj : 4 ≤ j) : Λ ≤ χ := by
  have hP : ∀ s : ℝ, HasDerivAt (fun s => s ^ 8 + a * s ^ 6 + b * s ^ 4 + d * s ^ 2 + e)
      (8 * s ^ 7 + 6 * a * s ^ 5 + 4 * b * s ^ 3 + 2 * d * s) s := fun s =>
    (((((hasDerivAt_pow 8 s).add ((hasDerivAt_pow 6 s).const_mul a)).add
      ((hasDerivAt_pow 4 s).const_mul b)).add
      ((hasDerivAt_pow 2 s).const_mul d)).add_const e).congr_deriv (by push_cast; ring)
  have hP₁ : ∀ s : ℝ, HasDerivAt (fun s => 8 * s ^ 7 + 6 * a * s ^ 5 + 4 * b * s ^ 3 + 2 * d * s)
      (56 * s ^ 6 + 30 * a * s ^ 4 + 12 * b * s ^ 2 + 2 * d) s := fun s =>
    ((((hasDerivAt_pow 7 s).const_mul 8).add ((hasDerivAt_pow 5 s).const_mul (6 * a))).add
      ((hasDerivAt_pow 3 s).const_mul (4 * b))).add
      ((hasDerivAt_id' s).const_mul (2 * d)) |>.congr_deriv (by push_cast; ring)
  refine Cvs.Prolate.SturmFromCentre.le_of_polyGauss_even (k := 3) (Q' := potEight G a) (χ' := 0) (G := G)
    (fun s _ => hP s) (fun s _ => hP₁ s) (fun s _ => ?_) (by ring) (fun t ht => ?_)
    ((encard_zeros_le a b d e).trans le_rfl) hχ hj
  · simp only [potEight, ContinuousMap.coe_mk]
    linear_combination s ^ 6 * h6 + s ^ 4 * h4 + s ^ 2 * h2 + h0
  · have h4' : 0 ≤ G ^ 2 * t ^ 4 := by positivity
    have hct : c ^ 2 * t ^ 2 = (G ^ 2 + 19 * G) * t ^ 2 := by rw [hc]
    simp only [potEight, ContinuousMap.coe_mk]
    linarith

/-! ### The coefficients from a root of the quintic -/

/-- The quintic in `A = aG` whose roots give the octic coefficients. -/
def quintic (G A : ℝ) : ℝ :=
  4 * A ^ 5 + (40 * G + 220) * A ^ 4 + (140 * G ^ 2 + 1740 * G + 4407) * A ^ 3
    + (200 * G ^ 3 + 4612 * G ^ 2 + 25810 * G + 37809) * A ^ 2
    + (96 * G ^ 4 + 4640 * G ^ 3 + 46064 * G ^ 2 + 145272 * G + 115830) * A
    + 1344 * G ^ 4 + 24416 * G ^ 3 + 131152 * G ^ 2 + 216216 * G

/-- **The quintic has a root in `[−14, 0]`** for `G ≥ 5`: it is `−56(24G³ − 108G² − 58G + 65)` at `−14`
and `56G(24G³ + 436G² + 2342G + 3861)` at `0`. -/
theorem exists_quintic_eq_zero {G : ℝ} (hG : 5 ≤ G) :
    ∃ A ∈ Icc (-14 : ℝ) 0, quintic G A = 0 := by
  have hcont : ContinuousOn (quintic G) (Icc (-14) 0) := by unfold quintic; fun_prop
  have hm : quintic G (-14) ≤ 0 := by
    have : quintic G (-14) = -56 * (24 * G ^ 3 - 108 * G ^ 2 - 58 * G + 65) := by
      unfold quintic; ring
    rw [this]
    have h1 : 0 ≤ G ^ 2 * (G - 5) := by have : 0 ≤ G - 5 := by linarith
                                        positivity
    nlinarith
  have hp : 0 ≤ quintic G 0 := by
    have : quintic G 0 = 56 * G * (24 * G ^ 3 + 436 * G ^ 2 + 2342 * G + 3861) := by
      unfold quintic; ring
    rw [this]
    have : 0 ≤ G := by linarith
    positivity
  exact intermediate_value_Icc (by norm_num) hcont ⟨hm, hp⟩

/-- **Coefficients of the octic comparison**: for `G ≥ 5` there are `a, b, d, e` solving the four conditions
with `aG ∈ [−14, 0]`. -/
theorem exists_coeffs {G : ℝ} (hG : 5 ≤ G) : ∃ a b d e : ℝ,
    4 * G * a ^ 2 + 4 * G * a + 30 * a - 8 * G * b + 56 = 0 ∧
    4 * G * a * b + 8 * G * b + 52 * b - 12 * G * d + 30 * a = 0 ∧
    4 * G * a * d + 12 * G * d + 66 * d - 16 * G * e + 12 * b = 0 ∧
    4 * G * a * e + 16 * G * e + 72 * e + 2 * d = 0 ∧ -14 ≤ a * G ∧ a * G ≤ 0 := by
  obtain ⟨A, hA, hF⟩ := exists_quintic_eq_zero hG
  have hG0 : G ≠ 0 := by linarith
  set B := (4 * A ^ 2 + (4 * G + 30) * A + 56 * G) / 8 with hB
  set D := (B * (4 * A + 8 * G + 52) + 30 * A * G) / 12 with hD
  set E := (D * (4 * A + 12 * G + 66) + 12 * B * G) / 16 with hE
  have haG : A / G * G = A := div_mul_cancel₀ A hG0
  refine ⟨A / G, B / G ^ 2, D / G ^ 3, E / G ^ 4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB]; field_simp; ring
  · rw [hD]; field_simp; ring
  · rw [hE]; field_simp; ring
  · have h : 4 * G * (A / G) * (E / G ^ 4) + 16 * G * (E / G ^ 4) + 72 * (E / G ^ 4)
        + 2 * (D / G ^ 3) = quintic G A / (24 * G ^ 4) := by
      rw [hE, hD, hB]; unfold quintic; field_simp; ring
    rw [h, hF, zero_div]
  · rw [haG]; exact hA.1
  · rw [haG]; exact hA.2

/-! ### The scale `G² + 19G = c²` -/

/-- The positive root `G = (√(361 + 4c²) − 19)/2` of `G² + 19G = c²`. -/
def gEight (c : ℝ) : ℝ := (√(361 + 4 * c ^ 2) - 19) / 2

/-- `gEight c` solves `G² + 19G = c²`. -/
theorem gEight_sq_add (c : ℝ) : gEight c ^ 2 + 19 * gEight c = c ^ 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 361 + 4 * c ^ 2 by positivity)
  unfold gEight
  linear_combination h / 4

/-- `gEight c ≥ 5` for `c² ≥ 120`. -/
theorem five_le_gEight {c : ℝ} (hc : 120 ≤ c ^ 2) : 5 ≤ gEight c := by
  have h : (29 : ℝ) ≤ √(361 + 4 * c ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  unfold gEight
  linarith

/-- `gEight c ≥ |c| − 19/2`. -/
theorem abs_sub_le_gEight (c : ℝ) : |c| - 19 / 2 ≤ gEight c := by
  have h : 2 * |c| ≤ √(361 + 4 * c ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity), mul_pow, sq_abs]
    linarith
  unfold gEight
  linarith

/-! ### Levels of index four and above -/

/-- **Every even level of index at least four lies at or above `17γ² + 16`**, `γ² = gEight c`,
for `c² ≥ 120`. -/
theorem le_of_isLevelIdx_four_le {c χ : ℝ} {j : ℕ} (hc : 120 ≤ c ^ 2)
    (hχ : IsLevelIdx c j χ) (hj : 4 ≤ j) : 17 * gEight c + 16 ≤ χ := by
  obtain ⟨a, b, d, e, h6, h4, h2, h0, ha, -⟩ := exists_coeffs (five_le_gEight hc)
  exact le_of_isLevelIdx_of_sq (gEight_sq_add c) h6 h4 h2 h0 (by linarith) hχ hj

/-- **The level of index four lies at or above `17γ² + 16`** for `5π + 1 ≤ c`. -/
theorem le_lev_four {c : ℝ} (hc : 5 * π + 1 ≤ c) : 17 * gEight c + 16 ≤ lev c 4 := by
  have hc16 : 16 ≤ c := by linarith [Real.pi_gt_three]
  exact le_of_isLevelIdx_four_le (by nlinarith)
    (lev_spec (Cvs.Prolate.SepticLevelComparison.exists_isLevelIdx_of_le_four hc le_rfl)) le_rfl

/-- **The level of index four lies at or above `17c − 291/2`** for `5π + 1 ≤ c`. -/
theorem seventeen_mul_sub_le_lev_four {c : ℝ} (hc : 5 * π + 1 ≤ c) :
    17 * c - 291 / 2 ≤ lev c 4 := by
  have h := abs_sub_le_gEight c
  rw [abs_of_nonneg (by linarith [Real.pi_pos])] at h
  linarith [le_lev_four hc]

end Cvs.Prolate.EvenOcticLevelComparison
