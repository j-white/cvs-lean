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
# The septic comparison: no even level of index four or more below `15γ² + 14`

`z = ξ(ξ⁶ + aξ⁴ + bξ² + d)e^{−Gξ²/2}` solves `((1 − ξ²)z')' = Tz` with `T` a quartic once `a, b, d`
satisfy three polynomial conditions, which a root `aG ∈ [−21/2, 0]` of a quartic supplies for `G ≥ 4`.
With `G² + 17G = c²`, `c²ξ² − T` exceeds `15G + 56 + 4aG ≥ 15G + 14` on `(0, 1)`, so every even level
of index at least four lies at or above `15γ² + 14`, which is at least `15c − 241/2`.
-/

noncomputable section

open Real Set Polynomial Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EvenLevelIndexLemma Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Prolate.SepticLevelComparison

/-! ### The comparison function and its zeros -/

/-- `ξ(ξ⁶ + aξ⁴ + bξ² + d)` has at most three zeros in `(0, 1)`. -/
theorem encard_zeros_le (a b d : ℝ) :
    {t | t ∈ Ioo (0 : ℝ) 1 ∧ t ^ 7 + a * t ^ 5 + b * t ^ 3 + d * t = 0}.encard ≤ 3 := by
  set S := {t | t ∈ Ioo (0 : ℝ) 1 ∧ t ^ 7 + a * t ^ 5 + b * t ^ 3 + d * t = 0} with hS
  set p : ℝ[X] := C 1 * X ^ 3 + C a * X ^ 2 + C b * X + C d with hp
  have hp0 : p ≠ 0 := fun h => by
    have := congrArg (fun q : ℝ[X] => q.coeff 3) h
    simp [hp] at this
  have hinj : InjOn (fun t : ℝ => t ^ 2) S := fun x hx y hy hxy =>
    (pow_left_inj₀ hx.1.1.le hy.1.1.le two_ne_zero).mp hxy
  have hsub : (fun t : ℝ => t ^ 2) '' S ⊆ (p.roots.toFinset : Set ℝ) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp0, IsRoot, hp]
    have h : t * ((t ^ 2) ^ 3 + a * (t ^ 2) ^ 2 + b * t ^ 2 + d) = 0 := by
      linear_combination ht.2
    have h' := (mul_eq_zero.mp h).resolve_left ht.1.1.ne'
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linarith
  calc S.encard = ((fun t : ℝ => t ^ 2) '' S).encard := (hinj.encard_image).symm
    _ ≤ (p.roots.toFinset : Set ℝ).encard := Set.encard_le_encard hsub
    _ = (p.roots.toFinset.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ 3 := by
      have h1 := Multiset.toFinset_card_le p.roots
      have h2 := card_roots' p
      have h3 : p.natDegree ≤ 3 := natDegree_cubic_le
      exact_mod_cast h1.trans (h2.trans h3)

/-- The potential `(G² + 17G)ξ² − G²ξ⁴ − (15G + 56 + 4aG)` of the septic comparison function. -/
def potFour (G a : ℝ) : C(ℝ, ℝ) :=
  ⟨fun s => (G ^ 2 + 17 * G) * s ^ 2 - G ^ 2 * s ^ 4 - (15 * G + 56 + 4 * a * G), by fun_prop⟩

/-- **The septic comparison**: for `G ≠ 0` with `G² + 17G = c²`, coefficients `a, b, d` solving the
three conditions and `Λ ≤ 15G + 56 + 4aG`, `regSol (sqC c) Λ` has no four zeros in `(0, 1)`. -/
theorem not_hasZeros_four_of_sq {c G a b d Λ : ℝ} (hG : G ≠ 0) (hc : G ^ 2 + 17 * G = c ^ 2)
    (h5 : 4 * G * a ^ 2 + 4 * G * a + 26 * a - 8 * G * b + 42 = 0)
    (h3 : 4 * G * a * b + 8 * G * b + 44 * b - 12 * G * d + 20 * a = 0)
    (h1 : 4 * G * a * d + 12 * G * d + 54 * d + 6 * b = 0)
    (hΛ : Λ ≤ 15 * G + 56 + 4 * a * G) : ¬HasZeros (sqC c) Λ 4 := by
  have hP : ∀ s : ℝ, HasDerivAt (fun s => s ^ 7 + a * s ^ 5 + b * s ^ 3 + d * s)
      (7 * s ^ 6 + 5 * a * s ^ 4 + 3 * b * s ^ 2 + d) s := fun s =>
    ((((hasDerivAt_pow 7 s).add ((hasDerivAt_pow 5 s).const_mul a)).add
      ((hasDerivAt_pow 3 s).const_mul b)).add
      ((hasDerivAt_id' s).const_mul d)).congr_deriv (by push_cast; ring)
  have hP₁ : ∀ s : ℝ, HasDerivAt (fun s => 7 * s ^ 6 + 5 * a * s ^ 4 + 3 * b * s ^ 2 + d)
      (42 * s ^ 5 + 20 * a * s ^ 3 + 6 * b * s) s := fun s =>
    ((((hasDerivAt_pow 6 s).const_mul 7).add ((hasDerivAt_pow 4 s).const_mul (5 * a))).add
      ((hasDerivAt_pow 2 s).const_mul (3 * b))).add_const d |>.congr_deriv (by push_cast; ring)
  refine Cvs.Prolate.SturmPolyGaussComparison.not_hasZeros_of_polyGauss (m := 3) (Q := potFour G a) (χ := 0) (G := G)
    (fun s _ => hP s) (fun s _ => hP₁ s) (fun s _ => ?_) (fun t ht => ?_)
    ((encard_zeros_le a b d).trans le_rfl)
  · simp only [potFour, ContinuousMap.coe_mk]
    linear_combination s ^ 5 * h5 + s ^ 3 * h3 + s * h1
  · have h4 : 0 < G ^ 2 * t ^ 4 := by have := ht.1; positivity
    have hct : c ^ 2 * t ^ 2 = (G ^ 2 + 17 * G) * t ^ 2 := by rw [hc]
    simp only [potFour, sqC, ContinuousMap.coe_mk]
    linarith

/-! ### The coefficients from a root of the quartic -/

/-- The quartic in `A = aG` whose roots give the septic coefficients. -/
def quartic (G A : ℝ) : ℝ :=
  4 * A ^ 4 + (24 * G + 124) * A ^ 3 + (44 * G ^ 2 + 568 * G + 1231) * A ^ 2
    + (24 * G ^ 3 + 744 * G ^ 2 + 3840 * G + 3861) * A + 252 * G ^ 3 + 2709 * G ^ 2 + 6237 * G

/-- **The quartic has a root in `[−21/2, 0]`** for `G ≥ 4`: it is `−252(G² − 3G − 1)` at `−21/2`
and `252G³ + 2709G² + 6237G` at `0`. -/
theorem exists_quartic_eq_zero {G : ℝ} (hG : 4 ≤ G) :
    ∃ A ∈ Icc (-21 / 2 : ℝ) 0, quartic G A = 0 := by
  have hcont : ContinuousOn (quartic G) (Icc (-21 / 2) 0) := by unfold quartic; fun_prop
  have hm : quartic G (-21 / 2) ≤ 0 := by
    have : quartic G (-21 / 2) = -252 * (G ^ 2 - 3 * G - 1) := by unfold quartic; ring
    rw [this]; nlinarith
  have hp : 0 ≤ quartic G 0 := by unfold quartic; nlinarith
  exact intermediate_value_Icc (by norm_num) hcont ⟨hm, hp⟩

/-- **Coefficients of the septic comparison**: for `G ≥ 4` there are `a, b, d` solving the three
conditions with `aG ∈ [−21/2, 0]`. -/
theorem exists_coeffs {G : ℝ} (hG : 4 ≤ G) : ∃ a b d : ℝ,
    4 * G * a ^ 2 + 4 * G * a + 26 * a - 8 * G * b + 42 = 0 ∧
    4 * G * a * b + 8 * G * b + 44 * b - 12 * G * d + 20 * a = 0 ∧
    4 * G * a * d + 12 * G * d + 54 * d + 6 * b = 0 ∧ -21 / 2 ≤ a * G ∧ a * G ≤ 0 := by
  obtain ⟨A, hA, hF⟩ := exists_quartic_eq_zero hG
  have hG0 : G ≠ 0 := by linarith
  set B := (4 * A ^ 2 + (4 * G + 26) * A + 42 * G) / 8 with hB
  set D := (B * (8 * G + 44 + 4 * A) + 20 * A * G) / 12 with hD
  have haG : A / G * G = A := div_mul_cancel₀ A hG0
  refine ⟨A / G, B / G ^ 2, D / G ^ 3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB]; field_simp; ring
  · rw [hD]; field_simp; ring
  · have h : 4 * G * (A / G) * (D / G ^ 3) + 12 * G * (D / G ^ 3) + 54 * (D / G ^ 3)
        + 6 * (B / G ^ 2) = quartic G A / (6 * G ^ 3) := by
      rw [hD, hB]; unfold quartic; field_simp; ring
    rw [h, hF, zero_div]
  · rw [haG]; exact hA.1
  · rw [haG]; exact hA.2

/-! ### The scale `G² + 17G = c²` -/

/-- The positive root `G = (√(289 + 4c²) − 17)/2` of `G² + 17G = c²`. -/
def gFour (c : ℝ) : ℝ := (√(289 + 4 * c ^ 2) - 17) / 2

/-- `gFour c` solves `G² + 17G = c²`. -/
theorem gFour_sq_add (c : ℝ) : gFour c ^ 2 + 17 * gFour c = c ^ 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 289 + 4 * c ^ 2 by positivity)
  unfold gFour
  linear_combination h / 4

/-- `gFour c ≥ 4` for `c² ≥ 84`. -/
theorem four_le_gFour {c : ℝ} (hc : 84 ≤ c ^ 2) : 4 ≤ gFour c := by
  have h : (25 : ℝ) ≤ √(289 + 4 * c ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  unfold gFour
  linarith

/-- `gFour c ≥ |c| − 17/2`. -/
theorem abs_sub_le_gFour (c : ℝ) : |c| - 17 / 2 ≤ gFour c := by
  have h : 2 * |c| ≤ √(289 + 4 * c ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity), mul_pow, sq_abs]
    linarith
  unfold gFour
  linarith

/-! ### Levels of index four and above -/

/-- **No four zeros below `15γ² + 14`**: for `c² ≥ 84` and `Λ ≤ 15 gFour c + 14`,
`regSol (sqC c) Λ` has no four zeros in `(0, 1)`. -/
theorem not_hasZeros_four {c Λ : ℝ} (hc : 84 ≤ c ^ 2) (hΛ : Λ ≤ 15 * gFour c + 14) :
    ¬HasZeros (sqC c) Λ 4 := by
  have hG := four_le_gFour hc
  obtain ⟨a, b, d, h5, h3, h1, ha, -⟩ := exists_coeffs hG
  exact not_hasZeros_four_of_sq (by linarith : (0 : ℝ) < gFour c).ne' (gFour_sq_add c) h5 h3 h1
    (by linarith)

/-- **Every even level of index at least four lies at or above `15γ² + 14`**, `γ² = gFour c`,
for `c² ≥ 84`. -/
theorem le_of_isLevelIdx_four_le {c χ : ℝ} {j : ℕ} (hc : 84 ≤ c ^ 2)
    (hχ : IsLevelIdx c j χ) (hj : 4 ≤ j) : 15 * gFour c + 14 ≤ χ :=
  Cvs.Prolate.ConverseLevelCount.le_of_not_hasZeros (k := 3) (not_hasZeros_four hc le_rfl) hχ hj

/-- **The levels of index `0` to `4` exist** for `5π + 1 ≤ c`. -/
theorem exists_isLevelIdx_of_le_four {c : ℝ} (hc : 5 * π + 1 ≤ c) {k : ℕ} (hk : k ≤ 4) :
    ∃ χ, IsLevelIdx c k χ := by
  have hk' : ((k : ℝ) + 1) * π + 1 ≤ c := by
    have : (k : ℝ) ≤ 4 := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  obtain ⟨χ, -, h⟩ := Cvs.Prolate.ConverseLevelCount.exists_isLevelIdx hk'
  exact ⟨χ, h⟩

/-- **The level of index four lies at or above `15γ² + 14`** for `5π + 1 ≤ c`. -/
theorem le_lev_four {c : ℝ} (hc : 5 * π + 1 ≤ c) : 15 * gFour c + 14 ≤ lev c 4 := by
  have hc10 : 10 ≤ c := by linarith [Real.pi_gt_three]
  exact le_of_isLevelIdx_four_le (by nlinarith)
    (lev_spec (exists_isLevelIdx_of_le_four hc le_rfl)) le_rfl

/-- **The level of index four lies at or above `15c − 241/2`** for `5π + 1 ≤ c`. -/
theorem fifteen_mul_sub_le_lev_four {c : ℝ} (hc : 5 * π + 1 ≤ c) :
    15 * c - 241 / 2 ≤ lev c 4 := by
  have h := abs_sub_le_gFour c
  rw [abs_of_nonneg (by linarith [Real.pi_pos])] at h
  linarith [le_lev_four hc]

end Cvs.Prolate.SepticLevelComparison
