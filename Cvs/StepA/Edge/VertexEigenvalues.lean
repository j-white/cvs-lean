import Mathlib
import Cvs.StepA.Edge.ComplexWeightDiscriminant
import Cvs.StepA.Edge.EdgePencil
import Cvs.StepA.Edge.EdgePencilOperators
import Cvs.StepA.Edge.EdgeSpace
import Cvs.StepA.Edge.InteractionFrame
import Cvs.StepA.Edge.VertexChains
import Cvs.Upstream.RayleighQuotientExtremes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The extreme eigenvalues near a vertex, through the frame

Near `(x, y) = (0, 0)` the scaled extreme eigenvalues `e^{δx} λ_max/min A(flow x y z)` are pinned by
the frame functions of extreme eigenvectors: every unit `w ∈ E₊` bounds `λ_max` from below and some
unit `w ∈ E₊` bounds it from above by `σ(1 + F_w(x)/2) + y⟪A_ζ w, w⟫` up to `O(|x||F_w(x)| + y² +
|y||x|)`, and likewise for `λ_min` on `E₋` (odd-chains Theorem A, Steps 2, 6, 7 and Theorem B).
-/

noncomputable section

open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : EdgeData ι) (z : ι → ℂ)

/-- The frame pencil splits as `⟪B_f w, w⟫ = ⟪B(x) w, w⟫ + y ⟪A_ζ w, w⟫ + ⟪R w, w⟫`. -/
theorem inner_frameBf_split (x y : ℝ) (w : EdgeV P) :
    ⟪frameBf P z x y w, w⟫ = ⟪frameB P z x w, w⟫ + y * ⟪opAzeta P z w, w⟫ +
      ⟪(frameBf P z x y - frameB P z x - y • opAzeta P z) w, w⟫ := by
  simp only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left]
  ring

/-- The frame pencil at a unit eigenvector `Au = μu`: on `|x|, |y| ≤ 1`,
`|⟪B_f u, u⟫ − μ(1 + F_u/2) − y⟪A_ζ u, u⟫| ≤ c(|x||F_u| + y² + |y||x|)`. -/
theorem inner_frameBf_eig :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → ∀ (μ : ℝ) (u : EdgeV P),
      opA P z u = μ • u → ‖u‖ = 1 →
      |⟪frameBf P z x y u, u⟫ - μ * (1 + fInt P u x / 2) - y * ⟪opAzeta P z u, u⟫|
        ≤ c * |x| * |fInt P u x| + c * (y ^ 2 + |y| * |x|) := by
  obtain ⟨ca, ha⟩ := inner_frameB_eig P z
  obtain ⟨Ce, he⟩ := frameBf_expansion P z
  refine ⟨|ca| + |Ce|, by positivity, fun x y hx hy μ u hu hu1 => ?_⟩
  have h1 := ha x hx μ u hu hu1
  have h2 : |⟪(frameBf P z x y - frameB P z x - y • opAzeta P z) u, u⟫|
      ≤ Ce * (y ^ 2 + |y| * |x|) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := he x y hx hy u
    rw [hu1, mul_one] at this ⊢
    exact this
  rw [inner_frameBf_split]
  have hF : 0 ≤ |x| * |fInt P u x| := by positivity
  have hY : 0 ≤ y ^ 2 + |y| * |x| := by positivity
  have k1 : ca * |x| * |fInt P u x| ≤ (|ca| + |Ce|) * |x| * |fInt P u x| := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right ((le_abs_self ca).trans (by linarith [abs_nonneg Ce])) hF
  have k2 : Ce * (y ^ 2 + |y| * |x|) ≤ (|ca| + |Ce|) * (y ^ 2 + |y| * |x|) :=
    mul_le_mul_of_nonneg_right ((le_abs_self Ce).trans (by linarith [abs_nonneg ca])) hY
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Top trial**: every unit `w ∈ E₊` bounds `e^{δx} λ_max` from below. -/
theorem top_trial :
    ∃ c : ℝ, ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → ∀ w ∈ Eplus P z, ‖w‖ = 1 →
      sig P z * (1 + fInt P w x / 2) - c * |x| * |fInt P w x| + y * ⟪opAzeta P z w, w⟫
          - c * (y ^ 2 + |y| * |x|)
        ≤ Real.exp (P.δ * x) * lamMax (opA P (flow P.g x y z)) := by
  obtain ⟨c, -, hc⟩ := inner_frameBf_eig P z
  refine ⟨c, fun x y hx hy w hw hw1 => ?_⟩
  have h := (abs_le.mp (hc x y hx hy _ w (mem_Eplus.mp hw) hw1)).1
  rw [← lamMax_frameBf]
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  refine le_lamMax_of hw0 ?_
  rw [hw1, one_pow, mul_one]
  linarith

/-- **Bottom trial**: every unit `v ∈ E₋` bounds `e^{δx} λ_min` from above. -/
theorem bottom_trial :
    ∃ c : ℝ, ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → ∀ v ∈ Eminus P z, ‖v‖ = 1 →
      Real.exp (P.δ * x) * lamMin (opA P (flow P.g x y z))
        ≤ -sig P z * (1 + fInt P v x / 2) + c * |x| * |fInt P v x| + y * ⟪opAzeta P z v, v⟫
          + c * (y ^ 2 + |y| * |x|) := by
  obtain ⟨c, -, hc⟩ := inner_frameBf_eig P z
  refine ⟨c, fun x y hx hy v hv hv1 => ?_⟩
  have h := (abs_le.mp (hc x y hx hy _ v (mem_Eminus.mp hv) hv1)).2
  rw [← lamMin_frameBf]
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  refine lamMin_le_of hv0 ?_
  rw [hv1, one_pow, mul_one]
  linarith

/-- The perturbation `B_f(x, y) − A` at a unit eigenvector `Au = μu`: on `|x|, |y| ≤ 1`,
`‖(B_f − A)u‖² ≤ c(|x||F_u| + y²)`. -/
theorem norm_frameBf_sub_eig :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → ∀ (μ : ℝ) (u : EdgeV P),
      opA P z u = μ • u → ‖u‖ = 1 →
      ‖(frameBf P z x y - opA P z) u‖ ^ 2 ≤ c * |x| * |fInt P u x| + c * y ^ 2 := by
  obtain ⟨cb, hb⟩ := norm_frameB_sub_eig P z
  obtain ⟨Ce, he⟩ := frameBf_expansion P z
  set M := ‖opAzeta P z‖
  refine ⟨3 * |cb| + 3 * (4 * Ce ^ 2 + M ^ 2), by positivity,
    fun x y hx hy μ u hu hu1 => ?_⟩
  have e : (frameBf P z x y - opA P z) u = (frameB P z x - opA P z) u
      + (frameBf P z x y - frameB P z x - y • opAzeta P z) u + y • opAzeta P z u := by
    simp only [sub_apply, smul_apply]
    abel
  set a := ‖(frameB P z x - opA P z) u‖
  set b := ‖(frameBf P z x y - frameB P z x - y • opAzeta P z) u‖
  set d := ‖y • opAzeta P z u‖
  have hn : ‖(frameBf P z x y - opA P z) u‖ ≤ a + b + d := by
    rw [e]
    have h1 := norm_add_le ((frameB P z x - opA P z) u
      + (frameBf P z x y - frameB P z x - y • opAzeta P z) u) (y • opAzeta P z u)
    have h2 := norm_add_le ((frameB P z x - opA P z) u)
      ((frameBf P z x y - frameB P z x - y • opAzeta P z) u)
    linarith
  have ha : a ^ 2 ≤ |cb| * |x| * |fInt P u x| := by
    refine (hb x hx μ u hu hu1).trans ?_
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self cb) (by positivity)
  have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
  have hbb : b ≤ 2 * |Ce| * |y| := by
    have h1 := he x y hx hy u
    rw [hu1, mul_one] at h1
    have h2 : y ^ 2 + |y| * |x| ≤ 2 * |y| := by
      nlinarith [abs_nonneg y, abs_nonneg x]
    calc b ≤ Ce * (y ^ 2 + |y| * |x|) := h1
      _ ≤ |Ce| * (y ^ 2 + |y| * |x|) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Ce| * (2 * |y|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = 2 * |Ce| * |y| := by ring
  have hd : d ≤ M * |y| := by
    show ‖y • opAzeta P z u‖ ≤ M * |y|
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    have := (opAzeta P z).le_opNorm u
    rw [hu1, mul_one] at this
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hb0 : 0 ≤ b := norm_nonneg _
  have hd0 : 0 ≤ d := norm_nonneg _
  have hsq : ‖(frameBf P z x y - opA P z) u‖ ^ 2 ≤ (a + b + d) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h3 : (a + b + d) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - d), sq_nonneg (b - d)]
  have hb2 : b ^ 2 ≤ 4 * Ce ^ 2 * y ^ 2 := by
    have := mul_le_mul hbb hbb hb0 (by positivity)
    have e2 : 2 * |Ce| * |y| * (2 * |Ce| * |y|) = 4 * Ce ^ 2 * y ^ 2 := by
      rw [← sq_abs Ce, ← hy2]; ring
    nlinarith
  have hd2 : d ^ 2 ≤ M ^ 2 * y ^ 2 := by
    have := mul_le_mul hd hd hd0 (by positivity)
    have e2 : M * |y| * (M * |y|) = M ^ 2 * y ^ 2 := by rw [← hy2]; ring
    nlinarith
  have hF : 0 ≤ |x| * |fInt P u x| := by positivity
  have k1 : 3 * |cb| * (|x| * |fInt P u x|) + 3 * (4 * Ce ^ 2 + M ^ 2) * y ^ 2
      ≤ (3 * |cb| + 3 * (4 * Ce ^ 2 + M ^ 2)) * (|x| * |fInt P u x|)
        + (3 * |cb| + 3 * (4 * Ce ^ 2 + M ^ 2)) * y ^ 2 := by
    nlinarith [sq_nonneg y, sq_nonneg Ce, sq_nonneg M, abs_nonneg cb]
  have e3 : (3 * |cb| + 3 * (4 * Ce ^ 2 + M ^ 2)) * |x| * |fInt P u x|
      = (3 * |cb| + 3 * (4 * Ce ^ 2 + M ^ 2)) * (|x| * |fInt P u x|) := by ring
  rw [e3]
  have ha' : a ^ 2 ≤ |cb| * (|x| * |fInt P u x|) := by rw [← mul_assoc]; exact ha
  nlinarith

variable [Nonempty ι]

-- odd-chains Theorem A Step 6
/-- **Top bound**: some unit `w ∈ E₊` bounds `e^{δx} λ_max` from
above. -/
theorem top_bound :
    ∃ c r : ℝ, 0 < r ∧ ∀ x y : ℝ, |x| < r → |y| < r → ∃ w ∈ Eplus P z, ‖w‖ = 1 ∧
      Real.exp (P.δ * x) * lamMax (opA P (flow P.g x y z))
        ≤ sig P z * (1 + fInt P w x / 2) + c * |x| * |fInt P w x| + y * ⟪opAzeta P z w, w⟫
          + c * (y ^ 2 + |y| * |x|) := by
  obtain ⟨g, hg, hgap⟩ := gap_top P z
  obtain ⟨r₀, hr₀, hnear⟩ := frameBf_near P z (g / 4) (by positivity)
  obtain ⟨c₁, hc₁0, hc₁⟩ := inner_frameBf_eig P z
  obtain ⟨c₂, hc₂0, hc₂⟩ := norm_frameBf_sub_eig P z
  refine ⟨c₁ + 2 / g * c₂, min r₀ 1, lt_min hr₀ one_pos, fun x y hx hy => ?_⟩
  have hx1 : |x| ≤ 1 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  have hy1 : |y| ≤ 1 := (lt_of_lt_of_le hy (min_le_right _ _)).le
  obtain ⟨w, hw, hw1, hle⟩ := schur_upper (A₀ := opA P z) (Ep := frameBf P z x y - opA P z)
    (opA_isSelfAdjoint P z) ((frameBf_isSelfAdjoint P z x y).sub (opA_isSelfAdjoint P z))
    (Eplus_ne_bot P z) (σ := sig P z) (g := g) (ε := g / 4) (fun u hu => mem_Eplus.mp hu)
    hgap hg (hnear x y (lt_of_lt_of_le hx (min_le_left _ _)) (lt_of_lt_of_le hy (min_le_left _ _)))
    (by linarith)
  refine ⟨w, hw, hw1, ?_⟩
  rw [← lamMax_frameBf]
  have hsum : opA P z + (frameBf P z x y - opA P z) = frameBf P z x y := by abel
  rw [hsum] at hle
  have h1 := (abs_le.mp (hc₁ x y hx1 hy1 _ w (mem_Eplus.mp hw) hw1)).2
  have h2 := hc₂ x y hx1 hy1 _ w (mem_Eplus.mp hw) hw1
  have h3 : 2 / g * ‖(frameBf P z x y - opA P z) w‖ ^ 2
      ≤ 2 / g * (c₂ * |x| * |fInt P w x| + c₂ * y ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hY : y ^ 2 ≤ y ^ 2 + |y| * |x| := le_add_of_nonneg_right (by positivity)
  have h4 : 2 / g * c₂ * y ^ 2 ≤ 2 / g * c₂ * (y ^ 2 + |y| * |x|) :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  have e1 : 2 / g * (c₂ * |x| * |fInt P w x| + c₂ * y ^ 2)
      = 2 / g * c₂ * |x| * |fInt P w x| + 2 / g * c₂ * y ^ 2 := by ring
  have e2 : (c₁ + 2 / g * c₂) * |x| * |fInt P w x| + (c₁ + 2 / g * c₂) * (y ^ 2 + |y| * |x|)
      = c₁ * |x| * |fInt P w x| + c₁ * (y ^ 2 + |y| * |x|)
        + (2 / g * c₂ * |x| * |fInt P w x| + 2 / g * c₂ * (y ^ 2 + |y| * |x|)) := by ring
  linarith

-- odd-chains Theorem B, Schur on the bottom cluster
/-- **Bottom bound**: at a vertex some unit
`v ∈ E₋` bounds `e^{δx} λ_min` from below. -/
theorem bottom_bound (hv : IsVertex P z) :
    ∃ c r : ℝ, 0 < r ∧ ∀ x y : ℝ, |x| < r → |y| < r → ∃ v ∈ Eminus P z, ‖v‖ = 1 ∧
      -sig P z * (1 + fInt P v x / 2) - c * |x| * |fInt P v x| + y * ⟪opAzeta P z v, v⟫
          - c * (y ^ 2 + |y| * |x|)
        ≤ Real.exp (P.δ * x) * lamMin (opA P (flow P.g x y z)) := by
  obtain ⟨g, hg, hgap⟩ := hv.gap_bottom
  obtain ⟨r₀, hr₀, hnear⟩ := frameBf_near P z (g / 4) (by positivity)
  obtain ⟨c₁, hc₁0, hc₁⟩ := inner_frameBf_eig P z
  obtain ⟨c₂, hc₂0, hc₂⟩ := norm_frameBf_sub_eig P z
  refine ⟨c₁ + 2 / g * c₂, min r₀ 1, lt_min hr₀ one_pos, fun x y hx hy => ?_⟩
  have hx1 : |x| ≤ 1 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  have hy1 : |y| ≤ 1 := (lt_of_lt_of_le hy (min_le_right _ _)).le
  obtain ⟨v, hvW, hv1, hle⟩ := schur_lower_cluster (A₀ := opA P z)
    (Ep := frameBf P z x y - opA P z)
    (opA_isSelfAdjoint P z) ((frameBf_isSelfAdjoint P z x y).sub (opA_isSelfAdjoint P z))
    hv.Eminus_ne_bot (σ := sig P z) (g := g) (ε := g / 4) (fun u hu => mem_Eminus.mp hu)
    hgap hg (hnear x y (lt_of_lt_of_le hx (min_le_left _ _)) (lt_of_lt_of_le hy (min_le_left _ _)))
    (by linarith)
  refine ⟨v, hvW, hv1, ?_⟩
  rw [← lamMin_frameBf]
  have hsum : opA P z + (frameBf P z x y - opA P z) = frameBf P z x y := by abel
  rw [hsum] at hle
  have h1 := (abs_le.mp (hc₁ x y hx1 hy1 _ v (mem_Eminus.mp hvW) hv1)).1
  have h2 := hc₂ x y hx1 hy1 _ v (mem_Eminus.mp hvW) hv1
  have h3 : 2 / g * ‖(frameBf P z x y - opA P z) v‖ ^ 2
      ≤ 2 / g * (c₂ * |x| * |fInt P v x| + c₂ * y ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hY : y ^ 2 ≤ y ^ 2 + |y| * |x| := le_add_of_nonneg_right (by positivity)
  have h4 : 2 / g * c₂ * y ^ 2 ≤ 2 / g * c₂ * (y ^ 2 + |y| * |x|) :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  have e1 : 2 / g * (c₂ * |x| * |fInt P v x| + c₂ * y ^ 2)
      = 2 / g * c₂ * |x| * |fInt P v x| + 2 / g * c₂ * y ^ 2 := by ring
  have e2 : (c₁ + 2 / g * c₂) * |x| * |fInt P v x| + (c₁ + 2 / g * c₂) * (y ^ 2 + |y| * |x|)
      = c₁ * |x| * |fInt P v x| + c₁ * (y ^ 2 + |y| * |x|)
        + (2 / g * c₂ * |x| * |fInt P v x| + 2 / g * c₂ * (y ^ 2 + |y| * |x|)) := by ring
  linarith

end Cvs.StepA.Edge.PlanarBoxLemma
