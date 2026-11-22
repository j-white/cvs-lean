import Mathlib
import Cvs.StepA.Edge.ComplexWeightDiscriminant
import Cvs.StepA.Edge.EdgePencil
import Cvs.StepA.Edge.EdgePencilOperators
import Cvs.StepA.Edge.EdgeSpace
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
# The interaction frame

`Z = D − κκ*/2` is skew and `U_t = exp(tZ/2)` orthogonal; in the frame `B(x) = G_x A G_x*`,
`G_x = U_x* e^{xD/2}`, a unit eigenvector `u` of `A` with eigenvalue `μ` has
`⟪B(x)u, u⟫ = μ(1 + F_u(x)/2) + O(|x| F_u(x))` with `F_u(x) = ∫₀ˣ κ(U_t u)²`, and the heat
derivative at a vertex is `A_ζ`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : EdgeData ι)

/-- `Z = D − κκ*/2`, the skew part of `D`. -/
def opZ : EdgeV P →L[ℝ] EdgeV P := opD P - (1 / 2 : ℝ) • rk P

/-- `Z` is skew: `⟪Zx, y⟫ = −⟪x, Zy⟫`. -/
theorem inner_opZ (x y : EdgeV P) : ⟪opZ P x, y⟫ = -⟪x, opZ P y⟫ := by
  simp only [opZ, sub_apply, smul_apply, rk_apply,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm (kap P) x]
  linear_combination inner_opD_add P x y

/-- The frame `U_t = exp(tZ/2)`. -/
def frameU (t : ℝ) : EdgeV P →L[ℝ] EdgeV P := NormedSpace.exp ((t / 2) • opZ P)

/-- `e^{tD}`. -/
def expD (t : ℝ) : EdgeV P →L[ℝ] EdgeV P := NormedSpace.exp (t • opD P)

/-- `G_t = U_t* e^{tD/2}`. -/
def frameG (t : ℝ) : EdgeV P →L[ℝ] EdgeV P :=
  ContinuousLinearMap.adjoint (frameU P t) ∘L expD P (t / 2)

/-- `f_u(t) = κ(U_t u) = ⟪κ_t, u⟫`. -/
def fW (u : EdgeV P) (t : ℝ) : ℝ := ⟪kap P, frameU P t u⟫

/-- `F_u(x) = ∫₀ˣ f_u²` (negative for `x < 0`). -/
def fInt (u : EdgeV P) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, fW P u t ^ 2

/-- The orbit pencil in the frame, `B(x) = G_x A(z) G_x*`. -/
def frameB (z : ι → ℂ) (x : ℝ) : EdgeV P →L[ℝ] EdgeV P :=
  frameG P x ∘L opA P z ∘L ContinuousLinearMap.adjoint (frameG P x)

/-- The pencil in the frame, `B_f(x, y) = e^{δx} U_x* A(flow x y z) U_x`. -/
def frameBf (z : ι → ℂ) (x y : ℝ) : EdgeV P →L[ℝ] EdgeV P :=
  Real.exp (P.δ * x) • (ContinuousLinearMap.adjoint (frameU P x) ∘L opA P (flow P.g x y z) ∘L
    frameU P x)

/-! ### The frame is orthogonal -/

/-- `Z* = −Z`. -/
private theorem adjoint_opZ : ContinuousLinearMap.adjoint (opZ P) = -opZ P := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (-opZ P) (opZ P)).mpr fun x y => ?_).symm
  rw [neg_apply, inner_neg_left, inner_opZ, neg_neg]

omit [DecidableEq ι] in
/-- `exp (X + Y) = exp X exp Y` for commuting operators on the edge space. -/
private theorem exp_add_comm {X Y : EdgeV P →L[ℝ] EdgeV P} (h : Commute X Y) :
    NormedSpace.exp (X + Y) = NormedSpace.exp X * NormedSpace.exp Y :=
  NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    ((NormedSpace.expSeries_radius_eq_top ℝ (EdgeV P →L[ℝ] EdgeV P)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℝ (EdgeV P →L[ℝ] EdgeV P)).symm ▸ edist_lt_top _ _)

omit [DecidableEq ι] in
/-- `U_{s+t} = U_s U_t`. -/
private theorem frameU_add (s t : ℝ) : frameU P (s + t) = frameU P s * frameU P t := by
  rw [frameU, frameU, frameU, ← exp_add_comm P
    (((Commute.refl (opZ P)).smul_left (s / 2)).smul_right (t / 2)), ← add_smul, add_div]

omit [DecidableEq ι] in
/-- `U_0 = 1`. -/
private theorem frameU_zero : frameU P 0 = 1 := by
  simp [frameU]

/-- `U_t* = U_{−t}`. -/
private theorem adjoint_frameU (t : ℝ) :
    ContinuousLinearMap.adjoint (frameU P t) = frameU P (-t) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, frameU, NormedSpace.star_exp, star_smul,
    ContinuousLinearMap.star_eq_adjoint, adjoint_opZ, star_trivial, smul_neg, ← neg_smul, frameU,
    neg_div]

omit [DecidableEq ι] in
/-- `U_{−t} U_t x = x`. -/
private theorem frameU_neg_apply (t : ℝ) (x : EdgeV P) : frameU P (-t) (frameU P t x) = x := by
  rw [← mul_apply_eq_comp, ← frameU_add, neg_add_cancel, frameU_zero, one_apply_eq_self]

omit [DecidableEq ι] in
/-- `U_t U_{−t} x = x`. -/
private theorem frameU_apply_neg (t : ℝ) (x : EdgeV P) : frameU P t (frameU P (-t) x) = x := by
  simpa using frameU_neg_apply P (-t) x

-- odd-chains Theorem A Step 1 (`Z` skew)
/-- `U_t` preserves norms. -/
theorem norm_frameU_apply (t : ℝ) (x : EdgeV P) : ‖frameU P t x‖ = ‖x‖ := by
  have h : ⟪frameU P t x, frameU P t x⟫ = ⟪x, x⟫ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_frameU, frameU_neg_apply]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

-- `U_{−t} U_t = 1` (`exp` of commuting summands)
/-- `U_t` is onto. -/
theorem frameU_surjective (t : ℝ) : Function.Surjective (frameU P t) := by
  exact fun y => ⟨frameU P (-t) y, frameU_apply_neg P t y⟩

/-- The frame pencil is self-adjoint. -/
theorem frameBf_isSelfAdjoint (z : ι → ℂ) (x y : ℝ) : IsSelfAdjoint (frameBf P z x y) :=
  (IsSelfAdjoint.all (Real.exp (P.δ * x))).smul
    ((opA_isSelfAdjoint P (flow P.g x y z)).adjoint_conj (frameU P x))

/-- The frame has the scaled extreme eigenvalues: `λ_max B_f(x, y) = e^{δx} λ_max A(flow x y z)`. -/
theorem lamMax_frameBf (z : ι → ℂ) (x y : ℝ) :
    lamMax (frameBf P z x y) = Real.exp (P.δ * x) * lamMax (opA P (flow P.g x y z)) := by
  rw [frameBf, lamMax_smul (Real.exp_pos _).le,
    lamMax_conj (norm_frameU_apply P x) (frameU_surjective P x)]

/-- The frame has the scaled extreme eigenvalues: `λ_min B_f(x, y) = e^{δx} λ_min A(flow x y z)`. -/
theorem lamMin_frameBf (z : ι → ℂ) (x y : ℝ) :
    lamMin (frameBf P z x y) = Real.exp (P.δ * x) * lamMin (opA P (flow P.g x y z)) := by
  rw [frameBf, lamMin_smul (Real.exp_pos _).le,
    lamMin_conj (norm_frameU_apply P x) (frameU_surjective P x)]

/-! ### The frame functions `f_u` and `F_u` -/

omit [DecidableEq ι] in
/-- `f_u(0) = u(0)`. -/
theorem fW_zero (u : EdgeV P) : fW P u 0 = ⟪kap P, u⟫ := by
  simp [fW, frameU, NormedSpace.exp_zero]

omit [DecidableEq ι] in
/-- `f_{cu} = c f_u`. -/
theorem fW_smul (c : ℝ) (u : EdgeV P) (t : ℝ) : fW P (c • u) t = c * fW P u t := by
  simp [fW, map_smul, real_inner_smul_right]

omit [DecidableEq ι] in
/-- `F_{cu} = c² F_u`. -/
theorem fInt_smul (c : ℝ) (u : EdgeV P) (x : ℝ) : fInt P (c • u) x = c ^ 2 * fInt P u x := by
  simp only [fInt, fW_smul, mul_pow, intervalIntegral.integral_const_mul]

omit [DecidableEq ι] in
/-- `F_u(x) ≥ 0` for `x ≥ 0`. -/
theorem fInt_nonneg (u : EdgeV P) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ fInt P u x :=
  intervalIntegral.integral_nonneg hx fun _ _ => sq_nonneg _

omit [DecidableEq ι] in
/-- `F_u(x) ≤ 0` for `x ≤ 0`. -/
theorem fInt_nonpos (u : EdgeV P) {x : ℝ} (hx : x ≤ 0) : fInt P u x ≤ 0 := by
  rw [fInt, intervalIntegral.integral_symm]
  exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hx fun _ _ => sq_nonneg _)

omit [DecidableEq ι] in
/-- `d/dt e^{(t/2)X} = e^{(t/2)X} (X/2)`. -/
private theorem hasDerivAt_exp_half (X : EdgeV P →L[ℝ] EdgeV P) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s / 2) • X))
      (NormedSpace.exp ((t / 2) • X) * ((1 / 2 : ℝ) • X)) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) ((1 / 2 : ℝ) • X) t
  have e : ∀ s : ℝ, s • ((1 / 2 : ℝ) • X) = (s / 2) • X := fun s => by
    rw [smul_smul]; ring_nf
  simp only [e] at h
  exact h

omit [DecidableEq ι] in
/-- `d/dt U_t = U_t (Z/2)`. -/
private theorem hasDerivAt_frameU (t : ℝ) :
    HasDerivAt (frameU P) (frameU P t * ((1 / 2 : ℝ) • opZ P)) t :=
  hasDerivAt_exp_half P (opZ P) t

omit [DecidableEq ι] in
/-- `t ↦ U_t` is continuous. -/
private theorem continuous_frameU : Continuous (frameU P) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_frameU P t).continuousAt

-- odd-chains Theorem A Steps 1, 3: `d/dt U_t = (Z/2) U_t`
/-- `f_u' = f_{Zu}/2`. -/
theorem hasDerivAt_fW (u : EdgeV P) (t : ℝ) :
    HasDerivAt (fW P u) ((1 / 2) * fW P (opZ P u) t) t := by
  have h1 := (hasDerivAt_frameU P t).clm_apply (hasDerivAt_const t u)
  rw [map_zero, add_zero] at h1
  have h2 := HasDerivAt.inner ℝ (hasDerivAt_const t (kap P)) h1
  rw [mul_apply_eq_comp, smul_apply, map_smul, real_inner_smul_right, inner_zero_left,
    add_zero] at h2
  exact h2

/-- `f_u` is continuous. -/
private theorem continuous_fW (u : EdgeV P) : Continuous (fW P u) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_fW P u t).continuousAt

/-- `|f_v(t)| ≤ ‖κ‖ ‖v‖`. -/
private theorem abs_fW_le (v : EdgeV P) (t : ℝ) : |fW P v t| ≤ ‖kap P‖ * ‖v‖ := by
  have h := abs_real_inner_le_norm (kap P) (frameU P t v)
  rwa [norm_frameU_apply] at h

/-- `|f_u(t) − f_u(0)| ≤ (‖κ‖ ‖Z‖ / 2) ‖u‖ |t|`. -/
private theorem abs_fW_sub_le (u : EdgeV P) (t : ℝ) :
    |fW P u t - fW P u 0| ≤ ‖kap P‖ * ‖opZ P‖ / 2 * ‖u‖ * |t| := by
  have hb : ∀ s ∈ (Set.univ : Set ℝ),
      ‖(1 / 2) * fW P (opZ P u) s‖ ≤ ‖kap P‖ * ‖opZ P‖ / 2 * ‖u‖ := by
    intro s _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h1 := abs_fW_le P (opZ P u) s
    have h2 := (opZ P).le_opNorm u
    have hk := norm_nonneg (kap P)
    have h3 : ‖kap P‖ * ‖opZ P u‖ ≤ ‖kap P‖ * (‖opZ P‖ * ‖u‖) := mul_le_mul_of_nonneg_left h2 hk
    linarith
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fW P u)
    (fun s _ => (hasDerivAt_fW P u s).hasDerivWithinAt) hb convex_univ (Set.mem_univ 0)
    (Set.mem_univ t)
  simpa [Real.norm_eq_abs] using h

/-- **Interval Cauchy–Schwarz**: `(∫ₐᵇ f)² ≤ (b − a) ∫ₐᵇ f²` for `a ≤ b`. -/
private theorem sq_integral_le {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, f s) ^ 2 ≤ (b - a) * ∫ s in a..b, f s ^ 2 := by
  set I := ∫ s in a..b, f s
  set S := ∫ s in a..b, f s ^ 2
  have h0 : 0 ≤ ∫ s in a..b, ((b - a) * f s - I) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
  have e : (fun s => ((b - a) * f s - I) ^ 2)
      = fun s => ((b - a) ^ 2 * f s ^ 2 - 2 * (b - a) * I * f s) + I ^ 2 := by
    funext s; ring
  have hi1 : IntervalIntegrable (fun s => (b - a) ^ 2 * f s ^ 2) MeasureTheory.volume a b :=
    ((hf.pow 2).const_mul _).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s => 2 * (b - a) * I * f s) MeasureTheory.volume a b :=
    (hf.const_mul _).intervalIntegrable _ _
  rw [e, intervalIntegral.integral_add (hi1.sub hi2) intervalIntegrable_const,
    intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at h0
  rcases hab.eq_or_lt with h | h
  · subst h
    simp [I]
  · have hba : 0 < b - a := sub_pos.mpr h
    nlinarith

-- one-endpoint Wirtinger with any constant (merged lean_plan `EdgePencilOperators`)
/-- **One-endpoint Wirtinger**: `F(0) = 0` and `F' = f` continuous give
`|∫₀ˣ F²| ≤ (x²/2) |∫₀ˣ f²|`. -/
theorem wirtinger {F f : ℝ → ℝ} (hF : ∀ t, HasDerivAt F (f t) t) (hf : Continuous f)
    (h0 : F 0 = 0) (x : ℝ) :
    |∫ t in (0 : ℝ)..x, F t ^ 2| ≤ x ^ 2 / 2 * |∫ t in (0 : ℝ)..x, f t ^ 2| := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt
  have hFint : ∀ a b, ∫ s in a..b, f s = F b - F a := fun a b =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) (hf.intervalIntegrable _ _)
  have hf2 : Continuous fun s => f s ^ 2 := hf.pow 2
  have hF2 : Continuous fun s => F s ^ 2 := hFc.pow 2
  rcases le_total 0 x with hx | hx
  · set K := ∫ t in (0 : ℝ)..x, f t ^ 2
    have hK : 0 ≤ K := intervalIntegral.integral_nonneg hx fun _ _ => sq_nonneg _
    have hpt : ∀ t ∈ Set.Icc 0 x, F t ^ 2 ≤ t * K := by
      rintro t ⟨ht0, htx⟩
      have h1 := sq_integral_le hf ht0
      rw [hFint, h0, sub_zero, sub_zero] at h1
      have h2 : ∫ s in (0 : ℝ)..t, f s ^ 2 ≤ K := by
        have h3 := intervalIntegral.integral_add_adjacent_intervals
          (hf2.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
          (hf2.intervalIntegrable (μ := MeasureTheory.volume) t x)
        have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) htx
          (fun s _ => sq_nonneg (f s))
        linarith
      nlinarith
    have hmono := intervalIntegral.integral_mono_on hx
      (hF2.intervalIntegrable (μ := MeasureTheory.volume) 0 x)
      ((by fun_prop : Continuous fun t : ℝ => t * K).intervalIntegrable
        (μ := MeasureTheory.volume) 0 x) hpt
    rw [intervalIntegral.integral_mul_const, integral_id] at hmono
    rw [abs_of_nonneg (intervalIntegral.integral_nonneg hx fun _ _ => sq_nonneg _),
      abs_of_nonneg hK]
    nlinarith
  · set K := ∫ t in x..(0 : ℝ), f t ^ 2
    have hK : 0 ≤ K := intervalIntegral.integral_nonneg hx fun _ _ => sq_nonneg _
    have hpt : ∀ t ∈ Set.Icc x 0, F t ^ 2 ≤ -t * K := by
      rintro t ⟨htx, ht0⟩
      have h1 := sq_integral_le hf ht0
      rw [hFint, h0, zero_sub, zero_sub, neg_sq] at h1
      have h2 : ∫ s in t..(0 : ℝ), f s ^ 2 ≤ K := by
        have h3 := intervalIntegral.integral_add_adjacent_intervals
          (hf2.intervalIntegrable (μ := MeasureTheory.volume) x t)
          (hf2.intervalIntegrable (μ := MeasureTheory.volume) t 0)
        have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) htx
          (fun s _ => sq_nonneg (f s))
        linarith
      nlinarith
    have hmono := intervalIntegral.integral_mono_on hx
      (hF2.intervalIntegrable (μ := MeasureTheory.volume) x 0)
      ((by fun_prop : Continuous fun t : ℝ => -t * K).intervalIntegrable
        (μ := MeasureTheory.volume) x 0) hpt
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg, integral_id] at hmono
    rw [intervalIntegral.integral_symm, abs_neg,
      intervalIntegral.integral_symm (f := fun t => f t ^ 2),
      abs_neg, abs_of_nonneg (intervalIntegral.integral_nonneg hx fun _ _ => sq_nonneg _),
      abs_of_nonneg hK]
    nlinarith

-- odd-chains Theorem A Step 3 (Hardy transfer): `f_{D⁻¹w} = (1/2) ∫ f_w` when `κ(D⁻¹w) = 0`
/-- **Hardy transfer**: `κ(D⁻¹w) = 0` gives `|F_{D⁻¹w}(x)| ≤ (x²/8) |F_w(x)|`. -/
theorem hardy {w : EdgeV P} (hw : ⟪kap P, opDinv P w⟫ = 0) (x : ℝ) :
    |fInt P (opDinv P w) x| ≤ x ^ 2 / 8 * |fInt P w x| := by
  have hZ : opZ P (opDinv P w) = w := by
    simp only [opZ, sub_apply, smul_apply, rk_apply, hw, zero_smul, smul_zero, sub_zero,
      opD_opDinv]
  have hd : ∀ t, HasDerivAt (fW P (opDinv P w)) ((fun s => 1 / 2 * fW P w s) t) t := fun t => by
    simpa only [hZ] using hasDerivAt_fW P (opDinv P w) t
  have h := wirtinger hd ((continuous_fW P w).const_mul _) (by rw [fW_zero, hw]) x
  have e : ∫ t in (0 : ℝ)..x, (1 / 2 * fW P w t) ^ 2 = 1 / 4 * fInt P w x := by
    rw [fInt, ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h
  rw [fInt]
  linarith

-- odd-chains Theorem A Step 8 (`f_w(0) = 0` gives `F_w = O(x³)`)
/-- `F_u(x) = O(‖u‖² |x|³)` uniformly when `u(0) = 0`. -/
theorem fInt_le_cube :
    ∃ C : ℝ, ∀ u : EdgeV P, ⟪kap P, u⟫ = 0 → ∀ x : ℝ, |x| ≤ 1 →
      |fInt P u x| ≤ C * ‖u‖ ^ 2 * |x| ^ 3 := by
  set c := ‖kap P‖ * ‖opZ P‖ / 2
  have hc : 0 ≤ c := by positivity
  refine ⟨c ^ 2, fun u hu x _ => ?_⟩
  have hpt : ∀ t ∈ Set.uIoc 0 x, ‖fW P u t ^ 2‖ ≤ c ^ 2 * ‖u‖ ^ 2 * x ^ 2 := by
    intro t ht
    have h1 := abs_fW_sub_le P u t
    rw [fW_zero, hu, sub_zero] at h1
    have htx : |t| ≤ |x| := by
      rw [abs_le]
      rcases Set.mem_uIoc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;>
        linarith [neg_abs_le x, le_abs_self x, abs_nonneg x]
    have h2 : |fW P u t| ≤ c * ‖u‖ * |x| :=
      h1.trans (mul_le_mul_of_nonneg_left htx (by positivity))
    rw [Real.norm_eq_abs, abs_pow]
    calc |fW P u t| ^ 2 ≤ (c * ‖u‖ * |x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = c ^ 2 * ‖u‖ ^ 2 * x ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, sub_zero] at h
  rw [fInt]
  calc |∫ t in (0 : ℝ)..x, fW P u t ^ 2| ≤ c ^ 2 * ‖u‖ ^ 2 * x ^ 2 * |x| := h
    _ = c ^ 2 * ‖u‖ ^ 2 * |x| ^ 3 := by rw [← sq_abs x]; ring

-- even-chains forward rule, odd-chains Theorem A Step 8(ii)
/-- `F_u(x) ≥ u(0)² x − C ‖u‖² x²` uniformly on `0 ≤ x ≤ 1`. -/
theorem fInt_ge_linear :
    ∃ C : ℝ, ∀ u : EdgeV P, ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ⟪kap P, u⟫ ^ 2 * x - C * ‖u‖ ^ 2 * x ^ 2 ≤ fInt P u x := by
  set c := ‖kap P‖ * ‖opZ P‖ / 2
  have hc : 0 ≤ c := by positivity
  refine ⟨2 * ‖kap P‖ * c, fun u x hx _ => ?_⟩
  have ha : |⟪kap P, u⟫| ≤ ‖kap P‖ * ‖u‖ := abs_real_inner_le_norm _ _
  have hpt : ∀ t ∈ Set.Icc 0 x,
      ⟪kap P, u⟫ ^ 2 - 2 * ‖kap P‖ * c * ‖u‖ ^ 2 * x ≤ fW P u t ^ 2 := by
    rintro t ⟨ht0, htx⟩
    have h1 := abs_fW_sub_le P u t
    rw [fW_zero] at h1
    have he : |fW P u t - ⟪kap P, u⟫| ≤ c * ‖u‖ * x :=
      h1.trans (by rw [abs_of_nonneg ht0]; exact mul_le_mul_of_nonneg_left htx (by positivity))
    have hp := mul_le_mul ha he (abs_nonneg _) (by positivity)
    have hn := neg_abs_le (⟪kap P, u⟫ * (fW P u t - ⟪kap P, u⟫))
    rw [abs_mul] at hn
    nlinarith [sq_nonneg (fW P u t - ⟪kap P, u⟫)]
  have h := intervalIntegral.integral_mono_on hx intervalIntegrable_const
    (((continuous_fW P u).pow 2).intervalIntegrable (μ := MeasureTheory.volume) 0 x) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  simp only [Pi.pow_apply] at h
  rw [fInt]
  linarith

-- odd-chains Theorem A Step 9, for every `u ≠ 0`: `f_u` is a nonzero exponential polynomial,
-- since `κ(Zⁿu) = 0` for all `n` would give a `D`-invariant subspace in `ker κ`
-- (`eq_bot_of_invariant_le_ker`)
/-- **Nondegeneracy**: `u ≠ 0` and `x ≠ 0` give `F_u(x) ≠ 0`. -/
theorem fInt_ne_zero {u : EdgeV P} (hu : u ≠ 0) {x : ℝ} (hx : x ≠ 0) : fInt P u x ≠ 0 := by
  intro hF
  set U := Set.Ioo (min 0 x) (max 0 x)
  have hUo : IsOpen U := isOpen_Ioo
  have hz : ∀ t ∈ U, fW P u t = 0 := by
    have hcont : Continuous fun t => fW P u t ^ 2 := (continuous_fW P u).pow 2
    have hae := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
      (MeasureTheory.ae_of_all _ fun t => sq_nonneg (fW P u t))
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 x)).mp hF
    have hsub : U ⊆ Set.Ioc 0 x ∪ Set.Ioc x 0 := by
      rintro t ⟨h1, h2⟩
      rcases le_total 0 x with h | h
      · rw [min_eq_left h] at h1
        rw [max_eq_right h] at h2
        exact Or.inl ⟨h1, h2.le⟩
      · rw [min_eq_right h] at h1
        rw [max_eq_left h] at h2
        exact Or.inr ⟨h1, h2.le⟩
    have hU := MeasureTheory.Measure.eqOn_open_of_ae_eq
      (MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hae) hUo hcont.continuousOn
      continuousOn_const
    intro t ht
    exact (pow_eq_zero_iff two_ne_zero).mp (by simpa using hU ht)
  have hall : ∀ n : ℕ, ∀ t ∈ U, fW P ((opZ P ^ n) u) t = 0 := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
      intro t ht
      have h1 := hasDerivAt_fW P ((opZ P ^ n) u) t
      have h2 : HasDerivAt (fW P ((opZ P ^ n) u)) 0 t :=
        (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
          (Filter.eventually_of_mem (hUo.mem_nhds ht) fun s hs => ih s hs)
      have h3 := h1.unique h2
      rw [pow_succ', mul_apply_eq_comp]
      linarith
  have ht0 : x / 2 ∈ U := by
    rcases lt_or_gt_of_ne hx with h | h
    · rw [Set.mem_Ioo, min_eq_right h.le, max_eq_left h.le]
      constructor <;> linarith
    · rw [Set.mem_Ioo, min_eq_left h.le, max_eq_right h.le]
      constructor <;> linarith
  have hcomm : ∀ n : ℕ, frameU P (x / 2) ((opZ P ^ n) u) = (opZ P ^ n) (frameU P (x / 2) u) := by
    intro n
    have hc : Commute (opZ P ^ n) (frameU P (x / 2)) :=
      (((Commute.refl (opZ P)).pow_left n).smul_right (x / 2 / 2)).exp_right
    have := congrArg (fun T => T u) hc.eq
    simp only [mul_apply_eq_comp] at this
    exact this.symm
  set v := frameU P (x / 2) u
  have hv : ∀ n : ℕ, ⟪kap P, (opZ P ^ n) v⟫ = 0 := fun n => by
    rw [← hcomm]
    exact hall n _ ht0
  let W : Submodule ℝ (EdgeV P) :=
    { carrier := {w | ∀ n : ℕ, ⟪kap P, (opZ P ^ n) w⟫ = 0}
      add_mem' := fun {a b} ha hb n => by
        rw [map_add, inner_add_right, ha n, hb n, add_zero]
      zero_mem' := fun n => by rw [map_zero, inner_zero_right]
      smul_mem' := fun c w hw n => by rw [map_smul, real_inner_smul_right, hw n, mul_zero] }
  have hDZ : ∀ w ∈ W, opD P w = opZ P w := by
    intro w hw
    have h0 : ⟪kap P, w⟫ = 0 := by simpa using hw 0
    simp [opZ, rk_apply, h0]
  have hWbot : W = ⊥ := eq_bot_of_invariant_le_ker
    (fun w hw => by
      rw [hDZ w hw]
      intro n
      have := hw (n + 1)
      rwa [pow_succ, mul_apply_eq_comp] at this)
    (fun w hw => Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (by simpa using hw 0))
  have hv0 : v = 0 := by
    have hvW : v ∈ W := hv
    rw [hWbot] at hvW
    exact (Submodule.mem_bot ℝ).mp hvW
  apply hu
  have := norm_frameU_apply P (x / 2) u
  rw [← norm_eq_zero, ← this]
  exact norm_eq_zero.mpr hv0

/-! ### The frame expansion at a vertex (odd-chains Theorem A, Steps 1-2) -/

/-- `A` as a continuous real-linear map of the weights. -/
private def opAL : (ι → ℂ) →L[ℝ] (EdgeV P →L[ℝ] EdgeV P) :=
  LinearMap.toContinuousLinearMap
    { toFun := opA P
      map_add' := opA_add P
      map_smul' := fun r w => by
        rw [RingHom.id_apply, ← opA_real_smul]
        congr 1 }

/-- `opAL` evaluates to `A`. -/
private theorem opAL_apply (w : ι → ℂ) : opAL P w = opA P w := rfl

/-- `(D − δ)ⁿ A(w) = A((i gᵢ)ⁿ wᵢ)`. -/
private theorem opDδ_pow_mul_opA (n : ℕ) (w : ι → ℂ) :
    opDδ P ^ n * opA P w = opA P (fun i => ((P.g i : ℂ) * Complex.I) ^ n * w i) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, ContinuousLinearMap.mul_def (opDδ P), ← opAxi, ← opA_mul_I_g, ih]
    congr 1
    funext i
    ring

/-- `e^{t(D − δ)} A(w) = A(flow t 0 w)`: the orbit flow of the weights. -/
private theorem exp_opDδ_mul_opA (t : ℝ) (w : ι → ℂ) :
    NormedSpace.exp (t • opDδ P) * opA P w = opA P (flow P.g t 0 w) := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • opDδ P)).mul_right (opA P w)
  have e1 : ∀ n : ℕ, ((n.factorial : ℝ)⁻¹ • (t • opDδ P) ^ n) * opA P w
      = opAL P (fun i => (((n.factorial : ℝ)⁻¹ * t ^ n : ℝ) : ℂ)
          * (((P.g i : ℂ) * Complex.I) ^ n * w i)) := by
    intro n
    rw [smul_pow, smul_mul_assoc, smul_mul_assoc, opDδ_pow_mul_opA, smul_smul, opAL_apply]
    exact (opA_real_smul P _ (fun i => ((P.g i : ℂ) * Complex.I) ^ n * w i)).symm
  have h2 : HasSum (fun n : ℕ => fun i => (((n.factorial : ℝ)⁻¹ * t ^ n : ℝ) : ℂ)
      * (((P.g i : ℂ) * Complex.I) ^ n * w i)) (flow P.g t 0 w) := by
    refine Pi.hasSum.mpr fun i => ?_
    have h := (NormedSpace.expSeries_div_hasSum_exp ((t : ℂ) * ((P.g i : ℂ) * Complex.I))).mul_left
      (w i)
    rw [← Complex.exp_eq_exp_ℂ] at h
    have e2 : (fun n : ℕ => (((n.factorial : ℝ)⁻¹ * t ^ n : ℝ) : ℂ)
        * (((P.g i : ℂ) * Complex.I) ^ n * w i))
        = fun n : ℕ => w i * (((t : ℂ) * ((P.g i : ℂ) * Complex.I)) ^ n / (n.factorial : ℂ)) := by
      funext n
      push_cast
      ring
    have hv : flow P.g t 0 w i = w i * Complex.exp ((t : ℂ) * ((P.g i : ℂ) * Complex.I)) := by
      unfold flow
      simp only [mul_zero, Complex.ofReal_zero, sub_zero]
      congr 2
      push_cast
      ring
    show HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹ * t ^ n : ℝ) : ℂ)
        * (((P.g i : ℂ) * Complex.I) ^ n * w i)) (flow P.g t 0 w i)
    rw [e2, hv]
    exact h
  have h3 := (opAL P).hasSum h2
  simp only [← e1] at h3
  exact h1.unique h3

/-- `e^{tD} A(w) = e^{δt} A(flow t 0 w)`. -/
private theorem exp_opD_mul_opA (t : ℝ) (w : ι → ℂ) :
    NormedSpace.exp (t • opD P) * opA P w = Real.exp (P.δ * t) • opA P (flow P.g t 0 w) := by
  have hsplit : t • opD P
      = t • opDδ P + algebraMap ℝ (EdgeV P →L[ℝ] EdgeV P) (P.δ * t) := by
    rw [Algebra.algebraMap_eq_smul_one, opDδ]
    ext v
    simp only [smul_apply, sub_apply, add_apply, ContinuousLinearMap.id_apply,
      one_apply_eq_self]
    module
  rw [hsplit, exp_add_comm P (Algebra.commute_algebraMap_right _ _),
    ← NormedSpace.algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one,
    mul_smul_one, smul_mul_assoc, exp_opDδ_mul_opA]

omit [DecidableEq ι] in
/-- `(e^{sD})* = e^{sD*}`. -/
private theorem adjoint_expD (s : ℝ) :
    ContinuousLinearMap.adjoint (expD P s)
      = NormedSpace.exp (s • ContinuousLinearMap.adjoint (opD P)) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, expD, NormedSpace.star_exp, star_smul, star_trivial,
    ContinuousLinearMap.star_eq_adjoint]

/-- `A e^{sD*} = e^{sD} A`, from `DA = AD*`. -/
private theorem opA_mul_exp_adjoint (s : ℝ) (w : ι → ℂ) :
    opA P w * NormedSpace.exp (s • ContinuousLinearMap.adjoint (opD P))
      = NormedSpace.exp (s • opD P) * opA P w := by
  let _ : NormedAlgebra ℚ (EdgeV P →L[ℝ] EdgeV P) := NormedAlgebra.restrictScalars ℚ ℝ _
  have h : SemiconjBy (opA P w) (s • ContinuousLinearMap.adjoint (opD P)) (s • opD P) := by
    unfold SemiconjBy
    rw [mul_smul_comm, smul_mul_assoc, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
      opD_comp_opA]
  exact h.exp_right

variable (z : ι → ℂ)

-- odd-chains Theorem A Step 1 (`e^{δx}A(x, 0) = e^{xD/2} A e^{xD*/2}`, the orbit congruence)
/-- Along the orbit the frame pencil is `B(x)`. -/
theorem frameBf_zero (x : ℝ) : frameBf P z x 0 = frameB P z x := by
  have key : expD P (x / 2) * opA P z * ContinuousLinearMap.adjoint (expD P (x / 2))
      = Real.exp (P.δ * x) • opA P (flow P.g x 0 z) := by
    rw [mul_assoc, adjoint_expD, opA_mul_exp_adjoint, ← mul_assoc, expD,
      ← exp_add_comm P (Commute.refl _), ← add_smul, add_halves, exp_opD_mul_opA]
  rw [frameB, frameG, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    frameBf]
  ext v
  have hk := congrArg (fun T => T (frameU P x v)) key
  simp only [mul_apply_eq_comp, smul_apply] at hk
  simp only [ContinuousLinearMap.comp_apply, smul_apply, hk, map_smul]

/-- `‖U_t v − v‖ ≤ (‖Z‖/2) ‖v‖ |t|`. -/
private theorem norm_frameU_sub_le (t : ℝ) (v : EdgeV P) :
    ‖frameU P t v - v‖ ≤ ‖opZ P‖ / 2 * ‖v‖ * |t| := by
  have hd : ∀ s ∈ (Set.univ : Set ℝ), HasDerivWithinAt (fun s => frameU P s v)
      ((frameU P s * ((1 / 2 : ℝ) • opZ P)) v) Set.univ s := by
    intro s _
    have h := (hasDerivAt_frameU P s).clm_apply (hasDerivAt_const s v)
    rw [map_zero, add_zero] at h
    exact h.hasDerivWithinAt
  have hb : ∀ s ∈ (Set.univ : Set ℝ),
      ‖(frameU P s * ((1 / 2 : ℝ) • opZ P)) v‖ ≤ ‖opZ P‖ / 2 * ‖v‖ := by
    intro s _
    rw [mul_apply_eq_comp, norm_frameU_apply, smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := (opZ P).le_opNorm v
    linarith
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb convex_univ (Set.mem_univ 0)
    (Set.mem_univ t)
  simpa [frameU_zero, Real.norm_eq_abs] using h

/-- `‖e^{s} − 1‖ ≤ ‖s‖ e^{‖s‖}` for complex `s`. -/
private theorem norm_cexp_sub_one_le (s : ℂ) : ‖Complex.exp s - 1‖ ≤ ‖s‖ * Real.exp ‖s‖ := by
  simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp s 1

/-- `‖e^{s} − 1 − s‖ ≤ ‖s‖² e^{‖s‖}` for complex `s`. -/
private theorem norm_cexp_sub_one_sub_le (s : ℂ) :
    ‖Complex.exp s - 1 - s‖ ≤ ‖s‖ ^ 2 * Real.exp ‖s‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp s 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, div_one, zero_add] at h
  rwa [sub_add_eq_sub_sub] at h

/-- `|e^{s} − 1| ≤ |s| e^{|s|}` for real `s`. -/
private theorem abs_rexp_sub_one_le (s : ℝ) : |Real.exp s - 1| ≤ |s| * Real.exp |s| := by
  have h := norm_cexp_sub_one_le (s : ℂ)
  rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

-- odd-chains Theorem A Step 1 (heat term `B₁(x) = (Z + K_x − δ)B(x)(−Z + K_x − δ)`,
-- `B₁(0) = A_ζ`, remainder `O(y²)`)
/-- **The heat expansion**: on `|x|, |y| ≤ 1`, `‖B_f(x, y) − B(x) − y A_ζ‖ ≤ C (y² + |y||x|)`. -/
theorem frameBf_expansion :
    ∃ C : ℝ, ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → ∀ v : EdgeV P,
      ‖(frameBf P z x y - frameB P z x - y • opAzeta P z) v‖ ≤ C * (y ^ 2 + |y| * |x|) * ‖v‖ := by
  have hδ := P.hδ
  set q0 : ι → ℂ := fun i => -((P.g i : ℂ) ^ 2) * z i with hq0
  set M1 : ℝ := ∑ i, ‖z i‖ * (P.g i ^ 4 * Real.exp (P.g i ^ 2)) with hM1d
  set M2 : ℝ := ∑ i, ‖z i‖ * (P.g i ^ 3 * Real.exp (P.g i)) with hM2d
  set a0 : ℝ := ‖opA P q0‖ with ha0d
  set kz : ℝ := ‖opZ P‖ with hkzd
  have hM1 : 0 ≤ M1 := Finset.sum_nonneg fun i _ => by positivity
  have hM2 : 0 ≤ M2 := Finset.sum_nonneg fun i _ =>
    mul_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg (P.hg0 i).le 3) (Real.exp_pos _).le)
  have ha0 : 0 ≤ a0 := norm_nonneg _
  have hkz : 0 ≤ kz := norm_nonneg _
  set C1 : ℝ := Real.exp P.δ * (M1 / (2 * P.δ)) with hC1d
  set C2 : ℝ := Real.exp P.δ * (M2 / (2 * P.δ)) + P.δ * Real.exp P.δ * a0 + a0 * (kz / 2)
    + kz / 2 * a0 with hC2d
  have hC1 : 0 ≤ C1 := by positivity
  have hC2 : 0 ≤ C2 := by positivity
  refine ⟨C1 + C2, fun x y hx hy v => ?_⟩
  set w : ι → ℂ := flow P.g x 0 z with hw
  set r : ι → ℂ := fun i =>
    w i * (Complex.exp (-(((P.g i ^ 2 * y : ℝ)) : ℂ)) - 1 + ((P.g i ^ 2 * y : ℝ) : ℂ)) with hrd
  set q : ι → ℂ := fun i => -((P.g i : ℂ) ^ 2) * w i with hqd
  set d : ι → ℂ := fun i => -((P.g i : ℂ) ^ 2) * (w i - z i) with hdd
  have hwi : ∀ i, w i = z i * Complex.exp (((P.g i * x : ℝ) : ℂ) * Complex.I) := by
    intro i
    simp only [hw, flow, mul_zero, Complex.ofReal_zero, sub_zero]
  have hnw : ∀ i, ‖w i‖ = ‖z i‖ := by
    intro i
    rw [hwi, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hflow : flow P.g x y z = w + r + fun i => (y : ℂ) * q i := by
    funext i
    have hexp : Complex.exp (((P.g i * x : ℝ) : ℂ) * Complex.I - ((P.g i ^ 2 * y : ℝ) : ℂ))
        = Complex.exp (((P.g i * x : ℝ) : ℂ) * Complex.I)
          * Complex.exp (-(((P.g i ^ 2 * y : ℝ)) : ℂ)) := by
      rw [sub_eq_add_neg, Complex.exp_add]
    show z i * Complex.exp (((P.g i * x : ℝ) : ℂ) * Complex.I - ((P.g i ^ 2 * y : ℝ) : ℂ))
      = w i + r i + (y : ℂ) * q i
    rw [hexp]
    simp only [hrd, hqd, hwi]
    push_cast
    ring
  have hA : opA P (flow P.g x y z) = opA P w + opA P r + y • opA P q := by
    rw [hflow, opA_add, opA_add, opA_real_smul]
  have hB : frameB P z x = Real.exp (P.δ * x) •
      (ContinuousLinearMap.adjoint (frameU P x) ∘L opA P w ∘L frameU P x) := by
    rw [← frameBf_zero]
    rfl
  have hZ : opAzeta P z = opA P q0 := (opA_neg_g_sq P z).symm
  have hqq : opA P q = opA P q0 + opA P d := by
    rw [← opA_add]
    congr 1
    funext i
    simp only [hqd, hq0, hdd, Pi.add_apply]
    ring
  -- the decomposition
  have hid : (frameBf P z x y - frameB P z x - y • opAzeta P z) v
      = Real.exp (P.δ * x) • frameU P (-x) (opA P r (frameU P x v))
        + y • (Real.exp (P.δ * x) • frameU P (-x) (opA P q (frameU P x v)) - opA P q0 v) := by
    rw [hB, hZ, frameBf, hA, adjoint_frameU]
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, add_apply, map_add,
      map_smul]
    module
  have hid2 : Real.exp (P.δ * x) • frameU P (-x) (opA P q (frameU P x v)) - opA P q0 v
      = Real.exp (P.δ * x) • frameU P (-x) (opA P d (frameU P x v))
        + (Real.exp (P.δ * x) - 1) • frameU P (-x) (opA P q0 (frameU P x v))
        + frameU P (-x) (opA P q0 (frameU P x v - v))
        + (frameU P (-x) (opA P q0 v) - opA P q0 v) := by
    rw [hqq, add_apply, map_sub, map_sub, map_add]
    module
  -- elementary bounds
  have hxδ : P.δ * x ≤ P.δ := by
    have := le_trans (le_abs_self x) hx
    nlinarith
  have he0 : 0 < Real.exp (P.δ * x) := Real.exp_pos _
  have he : Real.exp (P.δ * x) ≤ Real.exp P.δ := Real.exp_le_exp.mpr hxδ
  have he1 : |Real.exp (P.δ * x) - 1| ≤ P.δ * Real.exp P.δ * |x| := by
    have h := abs_rexp_sub_one_le (P.δ * x)
    have h1 : |P.δ * x| = P.δ * |x| := by rw [abs_mul, abs_of_pos hδ]
    have h2 : Real.exp |P.δ * x| ≤ Real.exp P.δ := by
      rw [h1]
      exact Real.exp_le_exp.mpr (mul_le_of_le_one_right hδ.le hx)
    rw [h1] at h
    calc |Real.exp (P.δ * x) - 1| ≤ P.δ * |x| * Real.exp |P.δ * x| := by rwa [← h1] at h ⊢
      _ ≤ P.δ * |x| * Real.exp P.δ := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = P.δ * Real.exp P.δ * |x| := by ring
  have hUv : ‖frameU P x v‖ = ‖v‖ := norm_frameU_apply P x v
  -- the second-order heat remainder
  have hr : ∀ i, ‖r i‖ ≤ ‖z i‖ * (P.g i ^ 4 * Real.exp (P.g i ^ 2)) * y ^ 2 := by
    intro i
    have hs := norm_cexp_sub_one_sub_le (-(((P.g i ^ 2 * y : ℝ)) : ℂ))
    rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hs
    have habs : |P.g i ^ 2 * y| ≤ P.g i ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (sq_nonneg _) hy
    have hs2 : ‖Complex.exp (-(((P.g i ^ 2 * y : ℝ)) : ℂ)) - 1 + ((P.g i ^ 2 * y : ℝ) : ℂ)‖
        ≤ P.g i ^ 4 * Real.exp (P.g i ^ 2) * y ^ 2 := by
      refine hs.trans ?_
      calc |P.g i ^ 2 * y| ^ 2 * Real.exp |P.g i ^ 2 * y|
          = (P.g i ^ 4 * y ^ 2) * Real.exp |P.g i ^ 2 * y| := by rw [sq_abs]; ring
        _ ≤ (P.g i ^ 4 * y ^ 2) * Real.exp (P.g i ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr habs) (by positivity)
        _ = P.g i ^ 4 * Real.exp (P.g i ^ 2) * y ^ 2 := by ring
    simp only [hrd]
    rw [norm_mul, hnw]
    calc ‖z i‖ * ‖Complex.exp (-(((P.g i ^ 2 * y : ℝ)) : ℂ)) - 1 + ((P.g i ^ 2 * y : ℝ) : ℂ)‖
        ≤ ‖z i‖ * (P.g i ^ 4 * Real.exp (P.g i ^ 2) * y ^ 2) :=
          mul_le_mul_of_nonneg_left hs2 (norm_nonneg _)
      _ = ‖z i‖ * (P.g i ^ 4 * Real.exp (P.g i ^ 2)) * y ^ 2 := by ring
  have hrsum : ∑ i, ‖r i‖ ≤ M1 * y ^ 2 := by
    rw [hM1d, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hr i
  -- the orbit increment of the heat weights
  have hd : ∀ i, ‖d i‖ ≤ ‖z i‖ * (P.g i ^ 3 * Real.exp (P.g i)) * |x| := by
    intro i
    have hg := P.hg0 i
    have hs := norm_cexp_sub_one_le (((P.g i * x : ℝ) : ℂ) * Complex.I)
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hs
    have habs : |P.g i * x| = P.g i * |x| := by rw [abs_mul, abs_of_pos hg]
    rw [habs] at hs
    have hs2 : ‖Complex.exp (((P.g i * x : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ P.g i * Real.exp (P.g i) * |x| := by
      refine hs.trans ?_
      calc P.g i * |x| * Real.exp (P.g i * |x|) ≤ P.g i * |x| * Real.exp (P.g i) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_of_le_one_right hg.le hx))
              (by positivity)
        _ = P.g i * Real.exp (P.g i) * |x| := by ring
    have hwz : w i - z i = z i * (Complex.exp (((P.g i * x : ℝ) : ℂ) * Complex.I) - 1) := by
      rw [hwi]; ring
    simp only [hdd]
    rw [norm_mul, hwz, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hg]
    calc P.g i ^ 2 * (‖z i‖ * ‖Complex.exp (((P.g i * x : ℝ) : ℂ) * Complex.I) - 1‖)
        ≤ P.g i ^ 2 * (‖z i‖ * (P.g i * Real.exp (P.g i) * |x|)) := by gcongr
      _ = ‖z i‖ * (P.g i ^ 3 * Real.exp (P.g i)) * |x| := by ring
  have hdsum : ∑ i, ‖d i‖ ≤ M2 * |x| := by
    rw [hM2d, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hd i
  -- the two pieces
  have hT1 : ‖Real.exp (P.δ * x) • frameU P (-x) (opA P r (frameU P x v))‖
      ≤ C1 * y ^ 2 * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos he0, norm_frameU_apply]
    have h1 := norm_opA_apply_le P r (frameU P x v)
    rw [hUv] at h1
    have h2 : (∑ i, ‖r i‖) / (2 * P.δ) * ‖v‖ ≤ M1 * y ^ 2 / (2 * P.δ) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hrsum (by positivity)) (norm_nonneg _)
    calc Real.exp (P.δ * x) * ‖opA P r (frameU P x v)‖
        ≤ Real.exp P.δ * (M1 * y ^ 2 / (2 * P.δ) * ‖v‖) :=
          mul_le_mul he (h1.trans h2) (norm_nonneg _) (Real.exp_pos _).le
      _ = C1 * y ^ 2 * ‖v‖ := by rw [hC1d]; ring
  have hT2 : ‖Real.exp (P.δ * x) • frameU P (-x) (opA P q (frameU P x v)) - opA P q0 v‖
      ≤ C2 * |x| * ‖v‖ := by
    rw [hid2]
    have hb1 : ‖Real.exp (P.δ * x) • frameU P (-x) (opA P d (frameU P x v))‖
        ≤ Real.exp P.δ * (M2 / (2 * P.δ)) * |x| * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos he0, norm_frameU_apply]
      have h1 := norm_opA_apply_le P d (frameU P x v)
      rw [hUv] at h1
      have h2 : (∑ i, ‖d i‖) / (2 * P.δ) * ‖v‖ ≤ M2 * |x| / (2 * P.δ) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hdsum (by positivity))
          (norm_nonneg _)
      calc Real.exp (P.δ * x) * ‖opA P d (frameU P x v)‖
          ≤ Real.exp P.δ * (M2 * |x| / (2 * P.δ) * ‖v‖) :=
            mul_le_mul he (h1.trans h2) (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp P.δ * (M2 / (2 * P.δ)) * |x| * ‖v‖ := by ring
    have hb2 : ‖(Real.exp (P.δ * x) - 1) • frameU P (-x) (opA P q0 (frameU P x v))‖
        ≤ P.δ * Real.exp P.δ * a0 * |x| * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, norm_frameU_apply]
      have h1 := (opA P q0).le_opNorm (frameU P x v)
      rw [hUv] at h1
      calc |Real.exp (P.δ * x) - 1| * ‖opA P q0 (frameU P x v)‖
          ≤ (P.δ * Real.exp P.δ * |x|) * (a0 * ‖v‖) :=
            mul_le_mul he1 h1 (norm_nonneg _) (by positivity)
        _ = P.δ * Real.exp P.δ * a0 * |x| * ‖v‖ := by ring
    have hb3 : ‖frameU P (-x) (opA P q0 (frameU P x v - v))‖ ≤ a0 * (kz / 2) * |x| * ‖v‖ := by
      rw [norm_frameU_apply]
      have h1 := (opA P q0).le_opNorm (frameU P x v - v)
      have h2 := norm_frameU_sub_le P x v
      calc ‖opA P q0 (frameU P x v - v)‖ ≤ a0 * ‖frameU P x v - v‖ := h1
        _ ≤ a0 * (kz / 2 * ‖v‖ * |x|) := mul_le_mul_of_nonneg_left h2 ha0
        _ = a0 * (kz / 2) * |x| * ‖v‖ := by ring
    have hb4 : ‖frameU P (-x) (opA P q0 v) - opA P q0 v‖ ≤ kz / 2 * a0 * |x| * ‖v‖ := by
      have h1 := norm_frameU_sub_le P (-x) (opA P q0 v)
      have h2 := (opA P q0).le_opNorm v
      rw [abs_neg] at h1
      calc ‖frameU P (-x) (opA P q0 v) - opA P q0 v‖ ≤ kz / 2 * ‖opA P q0 v‖ * |x| := h1
        _ ≤ kz / 2 * (a0 * ‖v‖) * |x| := by gcongr
        _ = kz / 2 * a0 * |x| * ‖v‖ := by ring
    refine norm_add₄_le.trans ?_
    rw [hC2d]
    linarith
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul y, Real.norm_eq_abs y]
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have h3 : |y| * ‖Real.exp (P.δ * x) • frameU P (-x) (opA P q (frameU P x v)) - opA P q0 v‖
      ≤ |y| * (C2 * |x| * ‖v‖) := mul_le_mul_of_nonneg_left hT2 hy0
  have h4 : 0 ≤ C1 * (|y| * |x|) * ‖v‖ := by positivity
  have h5 : 0 ≤ C2 * y ^ 2 * ‖v‖ := by positivity
  linarith

-- continuity of the entire family `B_f` at `(0, 0)`
/-- `B_f(x, y) → A(z)` in operator norm as `(x, y) → 0`. -/
theorem frameBf_near (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∀ x y : ℝ, |x| < r → |y| < r → ∀ v : EdgeV P,
      ‖(frameBf P z x y - opA P z) v‖ ≤ ε * ‖v‖ := by
  have hcont : Continuous fun p : ℝ × ℝ => frameBf P z p.1 p.2 := by
    unfold frameBf
    refine (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).smul ?_
    refine (ContinuousLinearMap.adjoint.continuous.comp
      ((continuous_frameU P).comp continuous_fst)).clm_comp ?_
    exact ((opAL P).continuous.comp ((continuous_flow P.g).comp
      (continuous_id.prodMk continuous_const))).clm_comp ((continuous_frameU P).comp continuous_fst)
  have h00 : frameBf P z 0 0 = opA P z := by
    rw [frameBf, adjoint_frameU, neg_zero, frameU_zero]
    ext v
    simp
  obtain ⟨r, hr, h⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := ((0 : ℝ), (0 : ℝ))))
    ε hε
  refine ⟨r, hr, fun x y hx hy v => ?_⟩
  have hd : dist (x, y) ((0 : ℝ), (0 : ℝ)) < r := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
    exact max_lt hx hy
  have h1 := h hd
  simp only [h00, dist_eq_norm] at h1
  exact ((frameBf P z x y - opA P z).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right h1.le (norm_nonneg v))

omit [DecidableEq ι] in
/-- `U_t Z = Z U_t`. -/
private theorem frameU_opZ (t : ℝ) (v : EdgeV P) :
    frameU P t (opZ P v) = opZ P (frameU P t v) := by
  have hc : Commute (opZ P) (frameU P t) :=
    ((Commute.refl (opZ P)).smul_right (t / 2)).exp_right
  have := congrArg (fun T => T v) hc.eq
  simp only [mul_apply_eq_comp] at this
  exact this.symm

omit [DecidableEq ι] in
/-- `d/dt (e^{(t/2)X} U_t u) = ½ e^{(t/2)X} (X + Z) U_t u`. -/
private theorem hasDerivAt_exp_frameU (X : EdgeV P →L[ℝ] EdgeV P) (u : EdgeV P) (t : ℝ) :
    HasDerivAt (fun s => NormedSpace.exp ((s / 2) • X) (frameU P s u))
      ((1 / 2 : ℝ) • NormedSpace.exp ((t / 2) • X) ((X + opZ P) (frameU P t u))) t := by
  have h1 := (hasDerivAt_frameU P t).clm_apply (hasDerivAt_const t u)
  rw [map_zero, add_zero] at h1
  have h := (hasDerivAt_exp_half P X t).clm_apply h1
  refine h.congr_deriv ?_
  simp only [mul_apply_eq_comp, smul_apply, add_apply, map_smul, map_add, frameU_opZ, smul_add]

/-- `0 ≤ f ≤ g` between `0` and `x` gives `|∫₀ˣ f| ≤ |∫₀ˣ g|`. -/
private theorem abs_integral_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {x : ℝ}
    (h0 : ∀ t ∈ Set.uIcc 0 x, 0 ≤ f t) (hfg : ∀ t ∈ Set.uIcc 0 x, f t ≤ g t) :
    |∫ t in (0 : ℝ)..x, f t| ≤ |∫ t in (0 : ℝ)..x, g t| := by
  rcases le_total 0 x with hx | hx
  · rw [Set.uIcc_of_le hx] at h0 hfg
    have h1 : 0 ≤ ∫ t in (0 : ℝ)..x, f t := intervalIntegral.integral_nonneg hx h0
    have h2 := intervalIntegral.integral_mono_on hx
      (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 x)
      (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 x) hfg
    rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2
  · rw [Set.uIcc_of_ge hx] at h0 hfg
    have h1 : 0 ≤ ∫ t in x..(0 : ℝ), f t := intervalIntegral.integral_nonneg hx h0
    have h2 := intervalIntegral.integral_mono_on hx
      (hf.intervalIntegrable (μ := MeasureTheory.volume) x 0)
      (hg.intervalIntegrable (μ := MeasureTheory.volume) x 0) hfg
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_symm (f := g), abs_neg, abs_neg,
      abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2

/-- **Integral mean value bound**: `φ' = h • ζ` with `‖ζ‖ ≤ M` between `0` and `x` gives
`‖φ(x) − φ(0)‖ ≤ M |∫₀ˣ |h||`. -/
private theorem norm_sub_le_of_hasDerivAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {φ ζ : ℝ → V} {h : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (h t • ζ t) t)
    (hh : Continuous h) (hζ : Continuous ζ) {M x : ℝ} (hM : ∀ t ∈ Set.uIcc 0 x, ‖ζ t‖ ≤ M) :
    ‖φ x - φ 0‖ ≤ M * |∫ t in (0 : ℝ)..x, (|h t|)| := by
  have hc : Continuous fun t => h t • ζ t := hh.smul hζ
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hφ t)
    (hc.intervalIntegrable 0 x)]
  refine intervalIntegral.norm_integral_le_abs_integral_norm.trans ?_
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 Set.left_mem_uIcc)
  have hmono := abs_integral_mono (f := fun t => ‖h t • ζ t‖) (g := fun t => M * |h t|) hc.norm
    (continuous_const.mul hh.abs) (fun t _ => norm_nonneg _) (fun t ht => by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM t ht) (abs_nonneg _))
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hM0]

/-- `t` between `0` and `x` has `|t| ≤ |x|`. -/
private theorem abs_le_abs_of_mem_uIcc {x t : ℝ} (ht : t ∈ Set.uIcc 0 x) : |t| ≤ |x| := by
  rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [abs_le] <;> constructor <;>
    linarith [neg_abs_le x, le_abs_self x, abs_nonneg x]

/-- For `g ≥ 0` and `t` between `0` and `x`, `|∫₀ᵗ g| ≤ |∫₀ˣ g|`. -/
private theorem abs_integral_le_of_mem_uIcc {g : ℝ → ℝ} (hg : Continuous g) (h0 : ∀ t, 0 ≤ g t)
    {x t : ℝ} (ht : t ∈ Set.uIcc 0 x) :
    |∫ s in (0 : ℝ)..t, g s| ≤ |∫ s in (0 : ℝ)..x, g s| := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    (hg.intervalIntegrable (μ := MeasureTheory.volume) t x)
  rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a1 : 0 ≤ ∫ s in (0 : ℝ)..t, g s := intervalIntegral.integral_nonneg h1 fun s _ => h0 s
    have a2 : 0 ≤ ∫ s in t..x, g s := intervalIntegral.integral_nonneg h2 fun s _ => h0 s
    rw [abs_of_nonneg a1, abs_of_nonneg (by linarith)]
    linarith
  · have a1 : 0 ≤ ∫ s in t..(0 : ℝ), g s := intervalIntegral.integral_nonneg h2 fun s _ => h0 s
    have a2 : 0 ≤ ∫ s in x..t, g s := intervalIntegral.integral_nonneg h1 fun s _ => h0 s
    have b1 : ∫ s in (0 : ℝ)..t, g s = -∫ s in t..(0 : ℝ), g s := intervalIntegral.integral_symm _ _
    have b2 : ∫ s in t..x, g s = -∫ s in x..t, g s := intervalIntegral.integral_symm _ _
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- **Interval Cauchy–Schwarz**, signed form: `(∫₀ˣ |f|)² ≤ |x| |∫₀ˣ f²|`. -/
private theorem sq_abs_integral_abs_le {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    |∫ t in (0 : ℝ)..x, (|f t|)| ^ 2 ≤ |x| * |∫ t in (0 : ℝ)..x, f t ^ 2| := by
  have hfa : Continuous fun t => |f t| := hf.abs
  have e : ∀ a b : ℝ, ∫ t in a..b, |f t| ^ 2 = ∫ t in a..b, f t ^ 2 := fun a b => by
    simp_rw [sq_abs]
  rcases le_total 0 x with hx | hx
  · have h := sq_integral_le hfa hx
    rw [e, sub_zero] at h
    rw [sq_abs, abs_of_nonneg hx,
      abs_of_nonneg (intervalIntegral.integral_nonneg hx fun t _ => sq_nonneg (f t))]
    exact h
  · have h := sq_integral_le hfa hx
    rw [e, zero_sub] at h
    rw [sq_abs, abs_of_nonpos hx, intervalIntegral.integral_symm, neg_sq,
      intervalIntegral.integral_symm (f := fun t => f t ^ 2), abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg hx fun t _ => sq_nonneg (f t))]
    exact h

/-- **Step 2 core**: for `|x| ≤ 1` and a unit eigenvector `Au = μu`, with `a = |∫₀ˣ |f_u||`,
`|⟪B(x)u, u⟫ − μ(1 + F_u(x)/2)| ≤ c a²` and `‖(B(x) − A)u‖ ≤ c a`. -/
private theorem frameB_eig_core :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, |x| ≤ 1 → ∀ (μ : ℝ) (u : EdgeV P), opA P z u = μ • u → ‖u‖ = 1 →
      |⟪frameB P z x u, u⟫ - μ * (1 + fInt P u x / 2)|
          ≤ c * |∫ t in (0 : ℝ)..x, (|fW P u t|)| ^ 2 ∧
        ‖(frameB P z x - opA P z) u‖ ≤ c * |∫ t in (0 : ℝ)..x, (|fW P u t|)| := by
  have hcE : ∀ X : EdgeV P →L[ℝ] EdgeV P,
      Continuous fun s : ℝ => NormedSpace.exp ((s / 2) • X) :=
    fun X => continuous_iff_continuousAt.mpr fun t => (hasDerivAt_exp_half P X t).continuousAt
  have hc1 : Continuous fun s : ℝ =>
      NormedSpace.exp ((s / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P) :=
    (hcE (ContinuousLinearMap.adjoint (opD P))).clm_apply continuous_const
  have hc2 : Continuous fun s : ℝ => NormedSpace.exp ((s / 2) • (-opD P)) (kap P) :=
    (hcE (-opD P)).clm_apply continuous_const
  obtain ⟨K1, hK1⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc1.continuousOn
  obtain ⟨K2, hK2⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc2.continuousOn
  obtain ⟨KE, hKE⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hcE (opD P)).continuousOn
  have h0I : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hK10 : 0 ≤ K1 := (norm_nonneg _).trans (hK1 0 h0I)
  have hK20 : 0 ≤ K2 := (norm_nonneg _).trans (hK2 0 h0I)
  have hKE0 : 0 ≤ KE := (norm_nonneg _).trans (hKE 0 h0I)
  have hKA0 : 0 ≤ ‖opA P z‖ := norm_nonneg _
  have hKk0 : 0 ≤ ‖kap P‖ := norm_nonneg _
  set cb : ℝ := KE * ‖opA P z‖ * (K1 / 4) + ‖opA P z‖ * (KE * (K2 / 4)) with hcbd
  set ca : ℝ := 1 / 2 * (‖opA P z‖ * (K1 / 4) * K1 + ‖opA P z‖ * (‖kap P‖ * (KE * (K2 / 4))))
    with hcad
  have hcb : 0 ≤ cb := by positivity
  have hca : 0 ≤ ca := by positivity
  refine ⟨ca + cb, by positivity, fun x hx μ u hu hu1 => ?_⟩
  set a := |∫ t in (0 : ℝ)..x, (|fW P u t|)| with had
  have ha0 : 0 ≤ a := abs_nonneg _
  have hfc : Continuous (fW P u) := continuous_fW P u
  have hat : ∀ t ∈ Set.uIcc 0 x, |∫ s in (0 : ℝ)..t, (|fW P u s|)| ≤ a := fun t ht =>
    abs_integral_le_of_mem_uIcc hfc.abs (fun _ => abs_nonneg _) ht
  have hIcc : ∀ t ∈ Set.uIcc 0 x, t ∈ Set.Icc (-1 : ℝ) 1 := fun t ht =>
    abs_le.mp ((abs_le_abs_of_mem_uIcc ht).trans hx)
  have hIcc' : ∀ t ∈ Set.uIcc 0 x, ∀ s ∈ Set.uIcc 0 t, s ∈ Set.Icc (-1 : ℝ) 1 := fun t ht s hs =>
    abs_le.mp (((abs_le_abs_of_mem_uIcc hs).trans (abs_le_abs_of_mem_uIcc ht)).trans hx)
  have hμ : |μ| ≤ ‖opA P z‖ := by
    have h := (opA P z).le_opNorm u
    rw [hu, norm_smul, Real.norm_eq_abs, hu1, mul_one, mul_one] at h
    exact h
  -- the two trajectories `φ(t) = G_t* u` and `ψ(t) = e^{−tD/2} U_t u`
  obtain ⟨φ, hφd⟩ : ∃ φ : ℝ → EdgeV P, φ = fun t =>
      NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (frameU P t u) := ⟨_, rfl⟩
  obtain ⟨ψ, hψd⟩ : ∃ ψ : ℝ → EdgeV P, ψ = fun t =>
      NormedSpace.exp ((t / 2) • (-opD P)) (frameU P t u) := ⟨_, rfl⟩
  have hφ' : ∀ t, HasDerivAt φ (fW P u t • ((1 / 4 : ℝ) •
      NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P))) t := by
    intro t
    rw [hφd]
    refine (hasDerivAt_exp_frameU P (ContinuousLinearMap.adjoint (opD P)) u t).congr_deriv ?_
    have e : (ContinuousLinearMap.adjoint (opD P) + opZ P) (frameU P t u)
        = (1 / 2 : ℝ) • (fW P u t • kap P) := by
      rw [adjoint_opD]
      simp only [add_apply, sub_apply, rk_apply, opZ, smul_apply, fW]
      module
    rw [e, map_smul, map_smul]
    module
  have hψ' : ∀ t, HasDerivAt ψ (fW P u t • ((-1 / 4 : ℝ) •
      NormedSpace.exp ((t / 2) • (-opD P)) (kap P))) t := by
    intro t
    rw [hψd]
    refine (hasDerivAt_exp_frameU P (-opD P) u t).congr_deriv ?_
    have e : (-opD P + opZ P) (frameU P t u) = (-1 / 2 : ℝ) • (fW P u t • kap P) := by
      simp only [add_apply, neg_apply, sub_apply, rk_apply, opZ, smul_apply, fW]
      module
    rw [e, map_smul, map_smul]
    module
  have hφ0 : φ 0 = u := by simp [hφd, frameU_zero]
  have hψ0 : ψ 0 = u := by simp [hψd, frameU_zero]
  have hL1 : ∀ t ∈ Set.uIcc 0 x, ‖φ t - u‖ ≤ K1 / 4 * a := by
    intro t ht
    have h := norm_sub_le_of_hasDerivAt (φ := φ) (x := t) (M := K1 / 4) hφ' hfc
      (hc1.const_smul (1 / 4 : ℝ)) (fun s hs => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        have := hK1 s (hIcc' t ht s hs)
        linarith)
    rw [hφ0] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hat t ht) (by positivity))
  have hL2 : ∀ t ∈ Set.uIcc 0 x, ‖ψ t - u‖ ≤ K2 / 4 * a := by
    intro t ht
    have h := norm_sub_le_of_hasDerivAt (φ := ψ) (x := t) (M := K2 / 4) hψ' hfc
      (hc2.const_smul (-1 / 4 : ℝ)) (fun s hs => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_neg (by norm_num : (-1 / 4 : ℝ) < 0)]
        have := hK2 s (hIcc' t ht s hs)
        linarith)
    rw [hψ0] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hat t ht) (by positivity))
  have hEψ : ∀ t, expD P (t / 2) (ψ t) = frameU P t u := by
    intro t
    have h1 : expD P (t / 2) * NormedSpace.exp ((t / 2) • (-opD P)) = 1 := by
      rw [expD, ← exp_add_comm P (((Commute.refl (opD P)).neg_right.smul_left (t / 2)).smul_right
        (t / 2)), smul_neg, add_neg_cancel, NormedSpace.exp_zero]
    have h2 := congrArg (fun T => T (frameU P t u)) h1
    simp only [mul_apply_eq_comp, one_apply_eq_self] at h2
    rw [hψd]
    exact h2
  have hEn : ∀ t ∈ Set.uIcc 0 x, ‖expD P (t / 2) (u - ψ t)‖ ≤ KE * (K2 / 4 * a) := by
    intro t ht
    have hEt : ‖expD P (t / 2)‖ ≤ KE := hKE t (hIcc t ht)
    refine ((expD P (t / 2)).le_opNorm _).trans (mul_le_mul hEt ?_ (norm_nonneg _) hKE0)
    rw [norm_sub_rev]
    exact hL2 t ht
  have hG : ∀ t ∈ Set.uIcc 0 x, ‖frameG P t u - u‖ ≤ KE * (K2 / 4 * a) := by
    intro t ht
    have e : frameG P t u - u = frameU P (-t) (expD P (t / 2) (u - ψ t)) := by
      rw [map_sub, hEψ, map_sub, frameU_neg_apply, frameG, ContinuousLinearMap.comp_apply,
        adjoint_frameU]
    rw [e, norm_frameU_apply]
    exact hEn t ht
  have hκE : ∀ t ∈ Set.uIcc 0 x,
      |⟪kap P, expD P (t / 2) u⟫ - fW P u t| ≤ ‖kap P‖ * (KE * (K2 / 4 * a)) := by
    intro t ht
    have e : ⟪kap P, expD P (t / 2) u⟫ - fW P u t = ⟪kap P, expD P (t / 2) (u - ψ t)⟫ := by
      rw [map_sub, hEψ, inner_sub_right, fW]
    rw [e]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hEn t ht) hKk0)
  have hGadj : ∀ t, ContinuousLinearMap.adjoint (frameG P t) u = φ t := by
    intro t
    rw [frameG, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply, adjoint_expD, hφd]
  have hxI : x ∈ Set.uIcc 0 x := Set.right_mem_uIcc
  -- (b)
  have hb : ‖(frameB P z x - opA P z) u‖ ≤ cb * a := by
    have e : (frameB P z x - opA P z) u
        = frameG P x (opA P z (φ x - u)) + μ • (frameG P x u - u) := by
      simp only [sub_apply, frameB, ContinuousLinearMap.comp_apply, hGadj, map_sub, hu, map_smul]
      module
    have hGn : ∀ w, ‖frameG P x w‖ ≤ KE * ‖w‖ := by
      intro w
      rw [frameG, ContinuousLinearMap.comp_apply, adjoint_frameU, norm_frameU_apply]
      exact ((expD P (x / 2)).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right (hKE x (hIcc x hxI)) (norm_nonneg _))
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖frameG P x (opA P z (φ x - u))‖ ≤ KE * (‖opA P z‖ * (K1 / 4 * a)) :=
      (hGn _).trans (mul_le_mul_of_nonneg_left (((opA P z).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hL1 x hxI) hKA0)) hKE0)
    have h2 : ‖μ • (frameG P x u - u)‖ ≤ ‖opA P z‖ * (KE * (K2 / 4 * a)) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hμ (hG x hxI) (norm_nonneg _) hKA0
    rw [hcbd]
    linarith
  -- (a)
  have ha : |⟪frameB P z x u, u⟫ - μ * (1 + fInt P u x / 2)| ≤ ca * a ^ 2 := by
    have hinner : ⟪frameB P z x u, u⟫ = ⟪opA P z (φ x), φ x⟫ := by
      rw [frameB, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_right, hGadj]
    obtain ⟨Q, hQd⟩ : ∃ Q : ℝ → ℝ, Q = fun t => ⟪opA P z (φ t), φ t⟫ - μ / 2 * fInt P u t :=
      ⟨_, rfl⟩
    have hQ' : ∀ t, HasDerivAt Q (fW P u t • (1 / 2 * (⟪opA P z (φ t),
        NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P)⟫
          - μ * fW P u t))) t := by
      intro t
      have hA := (opA P z).hasFDerivAt.comp_hasDerivAt t (hφ' t)
      have hin := HasDerivAt.inner ℝ hA (hφ' t)
      have hF := (Continuous.integral_hasStrictDerivAt ((continuous_fW P u).pow 2) 0 t).hasDerivAt
      have hsum := hin.sub (hF.const_mul (μ / 2))
      rw [hQd]
      refine hsum.congr_deriv ?_
      have hc : ⟪opA P z (NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P)),
          φ t⟫ = ⟪opA P z (φ t),
            NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P)⟫ := by
        rw [inner_opA_comm, real_inner_comm]
      simp only [Function.comp_apply, map_smul, real_inner_smul_left, real_inner_smul_right,
        smul_eq_mul, hc, Pi.pow_apply]
      ring
    have hζb : ∀ t ∈ Set.uIcc 0 x, ‖1 / 2 * (⟪opA P z (φ t),
        NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P)⟫
          - μ * fW P u t)‖ ≤ ca * a := by
      intro t ht
      have e : ⟪opA P z (φ t),
          NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P)⟫ - μ * fW P u t
          = ⟪opA P z (φ t - u),
              NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P)⟫
            + μ * (⟪kap P, expD P (t / 2) u⟫ - fW P u t) := by
        have h1 : ⟪u, NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P)⟫
            = ⟪kap P, expD P (t / 2) u⟫ := by
          rw [← adjoint_expD, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
        rw [map_sub, inner_sub_left, hu, real_inner_smul_left, h1]
        ring
      rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have h1 : |⟪opA P z (φ t - u),
          NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P)⟫|
          ≤ ‖opA P z‖ * (K1 / 4 * a) * K1 := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        have hA := ((opA P z).le_opNorm (φ t - u)).trans
          (mul_le_mul_of_nonneg_left (hL1 t ht) hKA0)
        exact mul_le_mul hA (hK1 t (hIcc t ht)) (norm_nonneg _) (by positivity)
      have h2 : |μ * (⟪kap P, expD P (t / 2) u⟫ - fW P u t)|
          ≤ ‖opA P z‖ * (‖kap P‖ * (KE * (K2 / 4 * a))) := by
        rw [abs_mul]
        exact mul_le_mul hμ (hκE t ht) (abs_nonneg _) hKA0
      have h3 := abs_add_le (⟪opA P z (φ t - u),
          NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P)⟫)
        (μ * (⟪kap P, expD P (t / 2) u⟫ - fW P u t))
      rw [hcad]
      linarith
    have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun t => (hφ' t).continuousAt
    have hcont : Continuous fun t => 1 / 2 * (⟪opA P z (φ t),
        NormedSpace.exp ((t / 2) • ContinuousLinearMap.adjoint (opD P)) (kap P)⟫
          - μ * fW P u t) :=
      continuous_const.mul ((((opA P z).continuous.comp hφc).inner hc1).sub
        (continuous_const.mul hfc))
    have hmain := norm_sub_le_of_hasDerivAt (V := ℝ) (φ := Q) (x := x) (M := ca * a) hQ' hfc
      hcont hζb
    have hQx : Q x = ⟪frameB P z x u, u⟫ - μ / 2 * fInt P u x := by rw [hQd, hinner]
    have hQ0 : Q 0 = μ := by
      rw [hQd]
      simp only [hφ0, hu, real_inner_smul_left, real_inner_self_eq_norm_sq, hu1, fInt,
        intervalIntegral.integral_same]
      ring
    rw [hQx, hQ0, Real.norm_eq_abs] at hmain
    have e : ⟪frameB P z x u, u⟫ - μ * (1 + fInt P u x / 2)
        = ⟪frameB P z x u, u⟫ - μ / 2 * fInt P u x - μ := by ring
    rw [e]
    calc _ ≤ ca * a * a := hmain
      _ = ca * a ^ 2 := by ring
  refine ⟨ha.trans ?_, hb.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · exact mul_le_mul_of_nonneg_right (by linarith) ha0

-- odd-chains Theorem A Step 2(a) (Gronwall on `G' = κ_x κ_x* G/4`)
/-- **Graded expansion (a)**: a unit eigenvector `Au = μu` has
`|⟪B(x)u, u⟫ − μ(1 + F_u(x)/2)| ≤ c |x| |F_u(x)|` on `|x| ≤ 1`. -/
theorem inner_frameB_eig :
    ∃ c : ℝ, ∀ x : ℝ, |x| ≤ 1 → ∀ (μ : ℝ) (u : EdgeV P), opA P z u = μ • u → ‖u‖ = 1 →
      |⟪frameB P z x u, u⟫ - μ * (1 + fInt P u x / 2)| ≤ c * |x| * |fInt P u x| := by
  obtain ⟨c, hc0, hc⟩ := frameB_eig_core P z
  refine ⟨c, fun x hx μ u hu hu1 => ?_⟩
  have h := (hc x hx μ u hu hu1).1
  have hcs := sq_abs_integral_abs_le (continuous_fW P u) x
  calc _ ≤ c * |∫ t in (0 : ℝ)..x, (|fW P u t|)| ^ 2 := h
    _ ≤ c * (|x| * |fInt P u x|) := mul_le_mul_of_nonneg_left hcs hc0
    _ = c * |x| * |fInt P u x| := by ring

-- odd-chains Theorem A Step 2(b)
/-- **Graded expansion (b)**: a unit eigenvector `Au = μu` has
`‖(B(x) − A)u‖² ≤ c |x| |F_u(x)|` on `|x| ≤ 1`. -/
theorem norm_frameB_sub_eig :
    ∃ c : ℝ, ∀ x : ℝ, |x| ≤ 1 → ∀ (μ : ℝ) (u : EdgeV P), opA P z u = μ • u → ‖u‖ = 1 →
      ‖(frameB P z x - opA P z) u‖ ^ 2 ≤ c * |x| * |fInt P u x| := by
  obtain ⟨c, hc0, hc⟩ := frameB_eig_core P z
  refine ⟨c ^ 2, fun x hx μ u hu hu1 => ?_⟩
  have h := (hc x hx μ u hu hu1).2
  have hcs := sq_abs_integral_abs_le (continuous_fW P u) x
  calc _ ≤ (c * |∫ t in (0 : ℝ)..x, (|fW P u t|)|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = c ^ 2 * |∫ t in (0 : ℝ)..x, (|fW P u t|)| ^ 2 := by ring
    _ ≤ c ^ 2 * (|x| * |fInt P u x|) := mul_le_mul_of_nonneg_left hcs (sq_nonneg c)
    _ = c ^ 2 * |x| * |fInt P u x| := by ring

end Cvs.StepA.Edge.PlanarBoxLemma
