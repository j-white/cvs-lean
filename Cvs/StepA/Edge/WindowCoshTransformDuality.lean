import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.PlaneCorrelationL2
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.StepA.Edge.DeepJointShare
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.SectorGramBoxTransform
import Cvs.Upstream.ProjectionInterpolantSplit
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cosh transform of a window class, and duality against the deep span

For a window class `v`, `L = log x`, `F_v(w) = ∫_{−L/2}^{L/2} v(t + L/2) cosh(wt) dt` has `Re F_v(w_ρ) = ⟪v, U_ρ⟫`
and `−Im F_v(w_ρ) = ⟪v, V_ρ⟫`. A class reproducing `⟪f, U_ρ⟫` on `D` bounds `‖P_{U_D} f‖`, such classes for all of
`R₁` bound `θ_x(D)`, and a class with `Re F_v = 0` on `D` bounds `dist(V_σ, U_D)` from below. `Transplant` and
`PointInterp` state the window interpolation of the ∂̄ method.
-/

noncomputable section

open Real MeasureTheory Filter Set
open scoped InnerProductSpace ComplexConjugate
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec)
open Cvs.StepA.Edge.FiniteTopCorrectedClosing (USpan bPerp)
open Cvs.StepA.OneZeroParitySectors (ue ve)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.StepA.Edge.WindowCoshTransformDuality
open Cvs.ZeroCounting

/-! ### The cosh transform -/

/-- The centred representative `t ↦ v(t + L/2)` of a window class, `L = log x`. -/
def rep (x : ℕ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) (t : ℝ) : ℝ :=
  ((v : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) (t + Real.log x / 2)

/-- The centred representative is integrable on the centred window. -/
theorem intervalIntegrable_rep (x : ℕ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) :
    IntervalIntegrable (rep x v) volume (-(Real.log x / 2)) (Real.log x / 2) := by
  have hL := Real.log_natCast_nonneg x
  have h : IntervalIntegrable ((v : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) volume 0 (Real.log x) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL]
    exact ((Lp.memLp (v : Lp ℝ 2 (volume : Measure ℝ))).restrict _).integrable one_le_two
  have := h.comp_add_right (Real.log x / 2) (by simp)
  rwa [zero_sub, show Real.log x - Real.log x / 2 = Real.log x / 2 by ring] at this

/-- **The cosh transform** `F_v(w) = ∫_{−L/2}^{L/2} v(t + L/2) cosh(wt) dt` of a window class, `L = log x`. -/
def coshT (x : ℕ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) (w : ℂ) : ℂ :=
  ∫ t in -(Real.log x / 2)..Real.log x / 2, (rep x v t : ℂ) * Complex.cosh (w * t)

/-- `F_v(−w) = F_v(w)`. -/
theorem coshT_neg (x : ℕ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) (w : ℂ) : coshT x v (-w) = coshT x v w := by
  unfold coshT
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [neg_mul, Complex.cosh_neg]

/-- `F_v(w̄) = conj F_v(w)`: the class is real. -/
theorem coshT_conj (x : ℕ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) (w : ℂ) : coshT x v (conj w) = conj (coshT x v w) := by
  have hL : -(Real.log x / 2) ≤ Real.log x / 2 := by linarith [Real.log_natCast_nonneg x]
  unfold coshT
  rw [intervalIntegral.integral_of_le hL, intervalIntegral.integral_of_le hL, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [map_mul, Complex.conj_ofReal, ← Complex.cosh_conj, map_mul, Complex.conj_ofReal]

/-- `cosh(i z t) = ue_z(t) − i ve_z(t)`. -/
theorem cosh_I_mul (z : ℂ) (t : ℝ) : Complex.cosh (Complex.I * z * t) = (ue z t : ℂ) - Complex.I * (ve z t : ℂ) := by
  have e : Complex.I * z * t = ((-(z.im * t) : ℝ) : ℂ) + ((z.re * t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [e, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [ue, ve, Real.cosh_neg, Real.sinh_neg]
  push_cast; ring

/-- **The transform at `i z` splits into the `ue` and `ve` pairings**:
`F_v(iz) = ∫ v(t + L/2) ue_z(t) dt − i ∫ v(t + L/2) ve_z(t) dt`. -/
theorem coshT_I_mul (x : ℕ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) (z : ℂ) :
    coshT x v (Complex.I * z)
      = ((∫ t in -(Real.log x / 2)..Real.log x / 2, rep x v t * ue z t : ℝ) : ℂ)
        - Complex.I * ((∫ t in -(Real.log x / 2)..Real.log x / 2, rep x v t * ve z t : ℝ) : ℂ) := by
  have hg := intervalIntegrable_rep x v
  have hu : IntervalIntegrable (fun t => ((rep x v t * ue z t : ℝ) : ℂ)) volume
      (-(Real.log x / 2)) (Real.log x / 2) := by
    have h := hg.mul_continuousOn (Cvs.StepA.OneZeroParitySectors.continuous_ue z).continuousOn
    exact ⟨h.1.ofReal, h.2.ofReal⟩
  have hv : IntervalIntegrable (fun t => Complex.I * ((rep x v t * ve z t : ℝ) : ℂ)) volume
      (-(Real.log x / 2)) (Real.log x / 2) := by
    have h := hg.mul_continuousOn (Cvs.StepA.OneZeroParitySectors.continuous_ve z).continuousOn
    exact (IntervalIntegrable.const_mul ⟨h.1.ofReal, h.2.ofReal⟩ _)
  unfold coshT
  rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hu hv]
  congr 1; ext t
  rw [cosh_I_mul]
  push_cast; ring

/-! ### Pairings with the zero vectors -/

/-- The inclusion of the form domain into the window's `L²`. -/
abbrev emb (x : ℕ) : Dom x →ₗᵢ[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x) :=
  (Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)).subtypeₗᵢ

/-- **`⟪v, U_z⟫ = ∫ v(t + L/2) ue_z(t) dt`** for a window class `v`. -/
theorem inner_emb_ueVec {x : ℕ} (hx0 : (0 : ℝ) < x) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) (z : ℂ) :
    ⟪v, emb x (ueVec hx0 z)⟫_ℝ = ∫ t in -(Real.log x / 2)..Real.log x / 2, rep x v t * ue z t := by
  have h : ⟪v, emb x (ueVec hx0 z)⟫_ℝ
      = ⟪(v : Lp ℝ 2 (volume : Measure ℝ)),
          (((ueVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))⟫_ℝ := rfl
  rw [h, Cvs.L2a.PlaneCorrelationL2.inner_eq_integral,
    integral_congr_ae (g := (Ico 0 (Real.log x)).indicator
      (fun s => ((v : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) s * Cvs.Route.Visibility.VisibilityClosingStep.ueProf x z s)),
    Cvs.Route.Visibility.ZeroPairingVector.integral_indicator_Ico_eq (Real.log_natCast_nonneg x)]
  · refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [rep, Cvs.Route.Visibility.VisibilityClosingStep.ueProf, add_sub_cancel_right]
  · filter_upwards [Cvs.Route.Visibility.VisibilityClosingStep.coe_ueVec_ae hx0 z] with s h2
    rw [h2]
    by_cases hs : s ∈ Ico 0 (Real.log x) <;> simp [hs]

/-- **`⟪v, V_z⟫ = ∫ v(t + L/2) ve_z(t) dt`** for a window class `v`. -/
theorem inner_emb_pairVec {x : ℕ} (hx0 : (0 : ℝ) < x) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) (z : ℂ) :
    ⟪v, emb x (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 z)⟫_ℝ = ∫ t in -(Real.log x / 2)..Real.log x / 2, rep x v t * ve z t := by
  have h : ⟪v, emb x (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 z)⟫_ℝ
      = ⟪(v : Lp ℝ 2 (volume : Measure ℝ)),
          (((Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 z : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))⟫_ℝ := rfl
  rw [h, Cvs.L2a.PlaneCorrelationL2.inner_eq_integral,
    integral_congr_ae (g := (Ico 0 (Real.log x)).indicator
      (fun s => ((v : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) s * Cvs.Route.Visibility.ZeroPairingVector.pairProf x z s)),
    Cvs.Route.Visibility.ZeroPairingVector.integral_indicator_Ico_eq (Real.log_natCast_nonneg x)]
  · refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [rep, Cvs.Route.Visibility.ZeroPairingVector.pairProf, add_sub_cancel_right]
  · filter_upwards [Cvs.Route.Visibility.ZeroPairingVector.coe_pairVec_ae hx0 z] with s h2
    rw [h2]
    by_cases hs : s ∈ Ico 0 (Real.log x) <;> simp [hs]

/-- The point `ρ − ½` turned into the right half-plane: `w_ρ = ρ − ½` if `δ_ρ ≥ 0`, else `½ − ρ`. -/
def wR (ρ : nonTrivialZeroSet) : ℂ := if 0 ≤ Cvs.GaussKernel.del ρ then (ρ : ℂ) - 1 / 2 else 1 / 2 - (ρ : ℂ)

/-- `Re w_ρ = |δ_ρ|`. -/
theorem wR_re (ρ : nonTrivialZeroSet) : (wR ρ).re = |Cvs.GaussKernel.del ρ| := by
  have hd : (ρ : ℂ).re - 1 / 2 = Cvs.GaussKernel.del ρ := rfl
  unfold wR
  split_ifs with h
  · rw [abs_of_nonneg h, ← hd]; simp
  · rw [abs_of_neg (not_le.1 h), ← hd]; simp

/-- `|Im w_ρ| = |γ_ρ|`. -/
theorem abs_wR_im (ρ : nonTrivialZeroSet) : |(wR ρ).im| = |(ρ : ℂ).im| := by
  unfold wR
  split_ifs <;> simp [abs_neg]

/-- `i·z_ρ = ρ − ½`. -/
theorem I_mul_zPoint (ρ : nonTrivialZeroSet) : Complex.I * Cvs.ZeroCounting.zPoint ρ = (ρ : ℂ) - 1 / 2 := by
  unfold Cvs.ZeroCounting.zPoint
  rw [← mul_assoc, show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_mul]

/-- `F_v(w_ρ) = F_v(i z_ρ)`. -/
theorem coshT_wR (x : ℕ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) (ρ : nonTrivialZeroSet) :
    coshT x v (wR ρ) = coshT x v (Complex.I * Cvs.ZeroCounting.zPoint ρ) := by
  rw [I_mul_zPoint]
  unfold wR
  split_ifs
  · rfl
  · rw [← coshT_neg]; congr 1; ring

/-- **`⟪v, U_ρ⟫ = Re F_v(w_ρ)`**. -/
theorem inner_emb_ueVec_eq_re {x : ℕ} (hx0 : (0 : ℝ) < x) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
    (ρ : nonTrivialZeroSet) :
    ⟪v, emb x (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))⟫_ℝ = (coshT x v (wR ρ)).re := by
  rw [coshT_wR, coshT_I_mul, inner_emb_ueVec]
  simp

/-- **`⟪v, V_ρ⟫ = −Im F_v(w_ρ)`**. -/
theorem inner_emb_pairVec_eq_im {x : ℕ} (hx0 : (0 : ℝ) < x) (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
    (ρ : nonTrivialZeroSet) :
    ⟪v, emb x (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint ρ))⟫_ℝ = -(coshT x v (wR ρ)).im := by
  rw [coshT_wR, coshT_I_mul, inner_emb_pairVec]
  simp

/-! ### Duality against the deep span -/

/-- **Pairings on the generators give pairings on the span**: if `Re F_v(w_ρ) = ⟪f, U_ρ⟫` on `D`, then
`⟪u, v⟫ = ⟪u, f⟫` for every `u ∈ span U_D`. -/
theorem inner_emb_eq_of_mem_USpan {x : ℕ} (hx0 : (0 : ℝ) < x) {D : Finset nonTrivialZeroSet} (f : Dom x)
    (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
    (h : ∀ ρ ∈ D, (coshT x v (wR ρ)).re = ⟪f, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ) :
    ∀ u ∈ USpan hx0 D, ⟪emb x u, v⟫_ℝ = ⟪u, f⟫_ℝ := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ρ, hρ, rfl⟩ := hy
    rw [real_inner_comm, inner_emb_ueVec_eq_re, h ρ hρ, real_inner_comm]
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, inner_add_left, hy, hz]
    exact (inner_add_left (𝕜 := ℝ) y z f).symm
  | smul a y _ hy =>
    have e : ⟪emb x (a • y), v⟫_ℝ = a * ⟪emb x y, v⟫_ℝ := by
      show ⟪((a • y : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)), v⟫_ℝ = _
      rw [Submodule.coe_smul]
      exact real_inner_smul_left _ _ _
    rw [e, hy, real_inner_smul_left]

/-- **A window interpolant bounds the projection on the deep span**: `Re F_v(w_ρ) = ⟪f, U_ρ⟫` on `D` gives
`‖P_{U_D} f‖ ≤ ‖v‖`. -/
theorem norm_proj_USpan_le {x : ℕ} (hx0 : (0 : ℝ) < x) {D : Finset nonTrivialZeroSet} (f : Dom x)
    (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
    (h : ∀ ρ ∈ D, (coshT x v (wR ρ)).re = ⟪f, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ) :
    ‖(USpan hx0 D).starProjection f‖ ≤ ‖v‖ :=
  Cvs.Upstream.ProjectionInterpolantSplit.norm_starProjection_le_of_inner_eq (emb x) _ f v (inner_emb_eq_of_mem_USpan hx0 f v h)

/-- **The angle from window interpolants** (Theorem 4 (f)): if every `r ∈ R₁` has a window class `v` with
`Re F_v(w_ρ) = ⟪r, U_ρ⟫` on `D` and `‖v‖ ≤ C‖r‖`, then `θ_x(D) ≤ C`. -/
theorem angle_le_of_interp {x : ℕ} (hx0 : (0 : ℝ) < x) {D : Finset nonTrivialZeroSet} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ r ∈ R1 x, ∃ v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x),
      (∀ ρ ∈ D, (coshT x v (wR ρ)).re = ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ) ∧ ‖v‖ ≤ C * ‖r‖) :
    Cvs.StepA.Edge.DeepJointShare.angle hx0 D ≤ C :=
  Cvs.Upstream.ProjectionInterpolantSplit.opNorm_comp_le_of_interp (emb x) (R1 x) (USpan hx0 D) hC fun r hr => by
    obtain ⟨v, hv, hn⟩ := h r hr
    exact ⟨v, inner_emb_eq_of_mem_USpan hx0 r v hv, hn⟩

/-- **A dual window class bounds the distance to the deep span** (Theorem F (i)): `Re F_v(w_ρ) = 0` on `D` gives
`(Im F_v(w_σ))² ≤ ‖v‖²‖V_σ − P_{U_D}V_σ‖²`. -/
theorem sq_im_le_of_dual {x : ℕ} (hx0 : (0 : ℝ) < x) {D : Finset nonTrivialZeroSet} (σ : nonTrivialZeroSet)
    (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) (h : ∀ ρ ∈ D, (coshT x v (wR ρ)).re = 0) :
    (coshT x v (wR σ)).im ^ 2 ≤ ‖v‖ ^ 2 * ‖bPerp hx0 D σ‖ ^ 2 := by
  have hv : ∀ u ∈ USpan hx0 D, ⟪emb x u, v⟫_ℝ = 0 := fun u hu => by
    rw [inner_emb_eq_of_mem_USpan hx0 0 v (fun ρ hρ => by rw [h ρ hρ]; simp) u hu]
    simp
  have h2 := Cvs.Upstream.ProjectionInterpolantSplit.sq_inner_le_of_dual (emb x) (USpan hx0 D) (Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)) v hv
  rw [real_inner_comm, inner_emb_pairVec_eq_im, neg_sq] at h2
  exact h2

/-! ### The interpolation statements -/

/-- **The ∂̄-transplant on the window** at `x` for points `Λ`, holomorphy domain `Ω` and transition set `T`:
for `d` holomorphic on `Ω` and conjugate-symmetric there with `‖d‖ ≤ M` on `T`, and real `c`, some window class
has `F_v(w) = x^{w/2}(d(w) + c/(w − ½))` on `Λ` and `‖v‖ ≤ K M + K_p|c|`. -/
def Transplant (x : ℕ) (Λ Ω T : Set ℂ) (K Kp : ℝ) : Prop :=
  ∀ (d : ℂ → ℂ) (M c : ℝ), DifferentiableOn ℂ d Ω → (∀ w ∈ Ω, d (conj w) = conj (d w)) →
    (∀ w ∈ T, ‖d w‖ ≤ M) → ∃ v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x),
      (∀ w ∈ Λ, coshT x v w = (x : ℂ) ^ (w / 2) * (d w + c / (w - 1 / 2))) ∧ ‖v‖ ≤ K * M + Kp * |c|

/-- **Point interpolation on the window** at `x`: a window class with `F_v = 0` on `Λ ∖ {w, w̄}`, `F_v(w) = i` and
`‖v‖² ≤ B`. -/
def PointInterp (x : ℕ) (Λ : Set ℂ) (w : ℂ) (B : ℝ) : Prop :=
  ∃ v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x), (∀ ζ ∈ Λ, ζ ≠ w → ζ ≠ conj w → coshT x v ζ = 0)
    ∧ coshT x v w = Complex.I ∧ ‖v‖ ^ 2 ≤ B

/-- **The free share from point interpolation** (Theorem F (i)–(iii)): `PointInterp` at `w_σ` for the points of `D`
gives `1 ≤ B‖V_σ − P_{U_D}V_σ‖²`. -/
theorem one_le_mul_norm_bPerp_sq {x : ℕ} (hx0 : (0 : ℝ) < x) {D : Finset nonTrivialZeroSet}
    (σ : nonTrivialZeroSet) {B : ℝ} (h : PointInterp x (wR '' (D : Set nonTrivialZeroSet)) (wR σ) B) :
    1 ≤ B * ‖bPerp hx0 D σ‖ ^ 2 := by
  obtain ⟨v, hz, hI, hB⟩ := h
  have hre : ∀ ρ ∈ D, (coshT x v (wR ρ)).re = 0 := by
    intro ρ hρ
    by_cases h1 : wR ρ = wR σ
    · rw [h1, hI, Complex.I_re]
    by_cases h2 : wR ρ = conj (wR σ)
    · rw [h2, coshT_conj, hI, Complex.conj_re, Complex.I_re]
    · rw [hz _ ⟨ρ, hρ, rfl⟩ h1 h2, Complex.zero_re]
  have h := sq_im_le_of_dual hx0 σ v hre
  rw [hI, Complex.I_im, one_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_right hB (sq_nonneg _))

/-! ### The size of the pairing vector -/

/-- **`‖V_z‖² ≤ e^{|y|L}/(4|y|)`** for `y = Im z ≠ 0`, `L = log x`. -/
theorem norm_sq_pairVec_le {x : ℕ} (hx0 : (0 : ℝ) < x) {z : ℂ} (hy : z.im ≠ 0) :
    ‖Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 z‖ ^ 2 ≤ Real.exp (|z.im| * Real.log x) / (4 * |z.im|) := by
  set L := Real.log x
  have hL : 0 ≤ L := Real.log_natCast_nonneg x
  have hL2 : -(L / 2) ≤ L / 2 := by linarith
  have ha : 0 < |z.im| := abs_pos.2 hy
  have hpt : ∀ t ∈ Icc (-(L / 2)) (L / 2), ve z t ^ 2 ≤ (cosh (2 * z.im * t) - 1) / 2 := by
    intro t _
    have hs : sin (z.re * t) ^ 2 ≤ 1 := sin_sq_le_one _
    have hc : (cosh (2 * z.im * t) - 1) / 2 = sinh (z.im * t) ^ 2 := by
      rw [show 2 * z.im * t = 2 * (z.im * t) by ring, Real.cosh_two_mul, Real.cosh_sq]; ring
    rw [hc, ve, mul_pow]
    nlinarith [sq_nonneg (sinh (z.im * t))]
  have hcc : Continuous fun t : ℝ => cosh (2 * z.im * t) := by fun_prop
  have hint : ∫ t in -(L / 2)..L / 2, ve z t ^ 2 ≤ ∫ t in -(L / 2)..L / 2, (cosh (2 * z.im * t) - 1) / 2 :=
    intervalIntegral.integral_mono_on hL2
      (((Cvs.StepA.OneZeroParitySectors.continuous_ve z).pow 2).intervalIntegrable (μ := volume) _ _)
      (((hcc.sub continuous_const).div_const 2).intervalIntegrable (μ := volume) _ _) hpt
  have hc := Cvs.StepA.SectorGramBoxTransform.mul_integral_cosh_two_mul L z.im
  have hC : ∫ t in -(L / 2)..L / 2, cosh (2 * z.im * t) = sinh (z.im * L) / z.im := by
    rw [eq_div_iff hy, mul_comm]; exact hc
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (hcc.intervalIntegrable (μ := volume) _ _) intervalIntegrable_const, hC,
    intervalIntegral.integral_const, smul_eq_mul] at hint
  rw [Cvs.Route.Visibility.ZeroPairingVector.norm_sq_pairVec_eq_integral]
  refine hint.trans ?_
  have hsa : sinh (z.im * L) / z.im = sinh (|z.im| * L) / |z.im| := by
    rcases abs_choice z.im with h | h <;> rw [h]
    rw [neg_mul, Real.sinh_neg, neg_div_neg_eq]
  have hsh : sinh (|z.im| * L) ≤ Real.exp (|z.im| * L) / 2 := by
    rw [Real.sinh_eq]; linarith [Real.exp_pos (-(|z.im| * L))]
  rw [hsa]
  have : sinh (|z.im| * L) / |z.im| ≤ Real.exp (|z.im| * L) / (2 * |z.im|) := by
    rw [div_le_div_iff₀ ha (by positivity)]; nlinarith
  have hLL : 0 ≤ L / 2 - -(L / 2) := by linarith
  have : (sinh (|z.im| * L) / |z.im| - (L / 2 - -(L / 2)) * 1) / 2 ≤ sinh (|z.im| * L) / |z.im| / 2 := by
    linarith
  calc _ ≤ sinh (|z.im| * L) / |z.im| / 2 := this
    _ ≤ Real.exp (|z.im| * L) / (2 * |z.im|) / 2 := by linarith
    _ = Real.exp (|z.im| * L) / (4 * |z.im|) := by field_simp; ring

/-- **`‖V_σ‖² ≤ x^{|δ_σ|}/(4|δ_σ|)`** for an off-line zero `σ`. -/
theorem norm_sq_Vσ_le {x : ℕ} (hx0 : (0 : ℝ) < x) {σ : nonTrivialZeroSet} (hσ : Cvs.GaussKernel.del σ ≠ 0) :
    ‖Cvs.StepA.Edge.DeepJointShare.Vσ hx0 σ‖ ^ 2 ≤ (x : ℝ) ^ |Cvs.GaussKernel.del σ| / (4 * |Cvs.GaussKernel.del σ|) := by
  have him : (Cvs.ZeroCounting.zPoint σ).im ≠ 0 := by
    rw [Cvs.ZeroCounting.zPoint_im]; exact neg_ne_zero.2 hσ
  have habs : |(Cvs.ZeroCounting.zPoint σ).im| = |Cvs.GaussKernel.del σ| := by
    rw [Cvs.ZeroCounting.zPoint_im, abs_neg]; rfl
  have h := norm_sq_pairVec_le hx0 him
  rw [habs, mul_comm, ← Real.rpow_def_of_pos hx0] at h
  exact h

end Cvs.StepA.Edge.WindowCoshTransformDuality

end
