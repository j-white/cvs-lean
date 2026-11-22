import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Limit.CriticalStripOffAxes
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Route.EigenvectorCoordinateCompression
import Cvs.Route.GroundConnesAngle
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapAtConnesVectors
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.OneCellBoxWindowForm
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.StepAFromTwoGaps
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.HodgeIndexPoleForm
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.WeilForm.WindowSetNonempty

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Centered Minkowski / Hodge-Index Decomposition on the Window and `FloorPerp → RH`

Centers the pole functionals `Vc, Uc` at the window midpoint `L/2` so `poleTerm = 2 Vc² − 2 Uc²`,
`Uc = 0` on `evenSub`, and `RH` reduces to `0 ≤ N` on `ker Vc ∩ Ev` plus slice, or `FloorPerp` at Connes' vectors.
-/

noncomputable section

open MeasureTheory Real Set Filter Matrix
open scoped InnerProductSpace

namespace Cvs.WeilForm.CentredHodgeIndexWindow
open Cvs.ZeroCounting

open Cvs.WeilForm.PoleArchPrimeProblem (Mplus Mminus poleTerm archTerm primeTerm Q_eq_split)
open Cvs.WeilForm.HodgeIndexPoleForm (momentFunctional nonneg_add_sq_iff N)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev boxD coe_boxD_ae reflD_boxD)
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Route.GroundRouteJointGap (Meven)
open Cvs.Route.EigenvectorCoordinateCompression (schurVec evenVec sinSqClose_of_floorPerp)

variable {L : ℝ}

/-! ### Part 1: Midpoint-Centered Pole Functionals `Vc` and `Uc` on the Form Domain -/

theorem abs_cosh_centered_le {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) L) :
    |Real.cosh ((s - L / 2) / 2)| ≤ Real.cosh (L / 2) := by
  rw [abs_of_pos (Real.cosh_pos _)]
  have hL0 : 0 ≤ L / 2 := by linarith [hs.1, hs.2]
  refine Real.cosh_le_cosh.mpr ?_
  rw [abs_of_nonneg hL0, abs_le]
  constructor <;> linarith [hs.1, hs.2]

theorem abs_sinh_le_cosh (t : ℝ) : |Real.sinh t| ≤ Real.cosh t := by
  rw [abs_le]
  have h1 : 0 < Real.cosh t + Real.sinh t := by rw [Real.cosh_add_sinh]; exact Real.exp_pos t
  have h2 : 0 < Real.cosh t - Real.sinh t := by rw [Real.cosh_sub_sinh]; exact Real.exp_pos (-t)
  constructor <;> linarith

theorem abs_sinh_centered_le {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) L) :
    |Real.sinh ((s - L / 2) / 2)| ≤ Real.cosh (L / 2) :=
  (abs_sinh_le_cosh _).trans ((le_abs_self _).trans (abs_cosh_centered_le hs))

theorem integrable_rep_sinh_centered (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Integrable (fun s => Cvs.WeilForm.WindowRepresentative.rep φ s * Real.sinh ((s - L / 2) / 2)) :=
  Cvs.WeilForm.HodgeIndexPoleForm.integrable_rep_mul hL φ (by fun_prop) fun _ hs => abs_sinh_centered_le hs

theorem integrable_rep_cosh_centered (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Integrable (fun s => Cvs.WeilForm.WindowRepresentative.rep φ s * Real.cosh ((s - L / 2) / 2)) :=
  Cvs.WeilForm.HodgeIndexPoleForm.integrable_rep_mul hL φ (by fun_prop) fun _ hs => abs_cosh_centered_le hs

/-- Midpoint-centered odd pole functional `Uc φ = ∫ rep φ(s) sinh((s − L/2)/2) ds`. -/
def Uc (hL : 0 ≤ L) : Cvs.WeilForm.FormDomain.formDomain hL →ₗ[ℝ] ℝ :=
  momentFunctional hL (fun s => Real.sinh ((s - L / 2) / 2)) (by fun_prop)
    fun _ hs => abs_sinh_centered_le hs

/-- Midpoint-centered even pole functional `Vc φ = ∫ rep φ(s) cosh((s − L/2)/2) ds`. -/
def Vc (hL : 0 ≤ L) : Cvs.WeilForm.FormDomain.formDomain hL →ₗ[ℝ] ℝ :=
  momentFunctional hL (fun s => Real.cosh ((s - L / 2) / 2)) (by fun_prop)
    fun _ hs => abs_cosh_centered_le hs

theorem Uc_apply (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Uc hL φ = ∫ s, Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) s * Real.sinh ((s - L / 2) / 2) := rfl

theorem Vc_apply (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Vc hL φ = ∫ s, Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) s * Real.cosh ((s - L / 2) / 2) := rfl

/-! ### Part 2: Centered Minkowski Identity `poleTerm = 2 Vc² − 2 Uc²` -/

/-- `Vc φ + Uc φ = e^{−L/4} M₊(rep φ)`. -/
theorem Vc_add_Uc (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Vc hL φ + Uc hL φ = Real.exp (-(L / 4)) * Mplus (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  rw [Vc_apply, Uc_apply, Mplus,
    ← integral_add (integrable_rep_cosh_centered hL _) (integrable_rep_sinh_centered hL _),
    ← integral_const_mul]
  congr 1; funext s
  rw [← mul_add, Real.cosh_add_sinh, show (s - L / 2) / 2 = -(L / 4) + s / 2 by ring, Real.exp_add]
  ring

/-- `Vc φ − Uc φ = e^{L/4} M₋(rep φ)`. -/
theorem Vc_sub_Uc (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Vc hL φ - Uc hL φ = Real.exp (L / 4) * Mminus (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  rw [Vc_apply, Uc_apply, Mminus,
    ← integral_sub (integrable_rep_cosh_centered hL _) (integrable_rep_sinh_centered hL _),
    ← integral_const_mul]
  congr 1; funext s
  rw [← mul_sub, Real.cosh_sub_sinh, show -((s - L / 2) / 2) = L / 4 + -(s / 2) by ring, Real.exp_add]
  ring

/-- **Centered Minkowski decomposition of the pole term**: `poleTerm(rep φ) = 2 Vc(φ)² − 2 Uc(φ)²`. -/
theorem poleTerm_rep_centered (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) = 2 * Vc hL φ ^ 2 - 2 * Uc hL φ ^ 2 := by
  have h1 := Vc_add_Uc hL φ
  have h2 := Vc_sub_Uc hL φ
  have hexp : Real.exp (-(L / 4)) * Real.exp (L / 4) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      = 2 * (Real.exp (-(L / 4)) * Real.exp (L / 4))
          * Mplus (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) * Mminus (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
        rw [hexp, mul_one]; rfl
    _ = 2 * (Real.exp (-(L / 4)) * Mplus (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)))
          * (Real.exp (L / 4) * Mminus (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))) := by ring
    _ = 2 * (Vc hL φ + Uc hL φ) * (Vc hL φ - Uc hL φ) := by rw [← h1, ← h2]
    _ = 2 * Vc hL φ ^ 2 - 2 * Uc hL φ ^ 2 := by ring

/-- Centered decomposition of `Cvs.WeilForm.InfimumAttainedSphere.Q` on the form domain at scale `x`:
`Q_x(φ) = N_x(φ) + 2 Vc(φ)² − 2 Uc(φ)²`. -/
theorem Q_eq_N_centered (x : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ
      = N x φ + 2 * Vc _ φ ^ 2 - 2 * Uc _ φ ^ 2 := by
  rw [Q_eq_split, N, poleTerm_rep_centered]; ring

/-! ### Part 3: Reflection Parity — `Uc` Vanishes Identically on `evenSub` and `Vc` Vanishes on Odd Classes -/

/-- `Vc` is invariant under window reflection `reflD`: `Vc(reflD φ) = Vc(φ)`. -/
theorem Vc_reflD (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Vc hL (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ) = Vc hL φ := by
  rw [Vc_apply, Vc_apply]
  have hae : (fun s => Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.WindowReflectionSymmetry.reflW (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) s * Real.cosh ((s - L / 2) / 2))
      =ᵐ[volume] fun s => Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (L - s)
        * Real.cosh (((L - s) - L / 2) / 2) := by
    filter_upwards [Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)] with s hs
    rw [hs, show (s - L / 2) / 2 = -(((L - s) - L / 2) / 2) by ring, Real.cosh_neg]
  change (∫ s, Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.WindowReflectionSymmetry.reflW (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) s * Real.cosh ((s - L / 2) / 2)) = _
  rw [integral_congr_ae hae]
  exact integral_sub_left_eq_self
    (fun s => Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) s * Real.cosh ((s - L / 2) / 2)) volume L

/-- `Uc` is anti-invariant under window reflection `reflD`: `Uc(reflD φ) = −Uc(φ)`. -/
theorem Uc_reflD (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Uc hL (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ) = -Uc hL φ := by
  rw [Uc_apply, Uc_apply, ← integral_neg]
  have hae : (fun s => Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.WindowReflectionSymmetry.reflW (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) s * Real.sinh ((s - L / 2) / 2))
      =ᵐ[volume] fun s => -(Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (L - s)
        * Real.sinh (((L - s) - L / 2) / 2)) := by
    filter_upwards [Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)] with s hs
    rw [hs, show (s - L / 2) / 2 = -(((L - s) - L / 2) / 2) by ring, Real.sinh_neg, mul_neg]
  change (∫ s, Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.WindowReflectionSymmetry.reflW (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) s * Real.sinh ((s - L / 2) / 2)) = _
  rw [integral_congr_ae hae]
  exact integral_sub_left_eq_self
    (fun s => -(Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) s * Real.sinh ((s - L / 2) / 2))) volume L

/-- **Key Elimination Theorem**: on the reflection-even subspace `evenSub hL`, the negative-signature pole
functional `Uc` vanishes identically (`Uc φ = 0`). -/
theorem Uc_eq_zero_of_mem_evenSub (hL : 0 ≤ L) {φ : Cvs.WeilForm.FormDomain.formDomain hL}
    (hφ : φ ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL) : Uc hL φ = 0 := by
  have h1 : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ = φ := hφ
  have h2 := Uc_reflD hL φ
  rw [h1] at h2
  linarith

/-- On any reflection-odd class (`reflD φ = −φ`), the positive-signature pole functional `Vc` vanishes. -/
theorem Vc_eq_zero_of_odd (hL : 0 ≤ L) {φ : Cvs.WeilForm.FormDomain.formDomain hL}
    (hφ : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL φ = -φ) : Vc hL φ = 0 := by
  have h2 := Vc_reflD hL φ
  rw [hφ] at h2
  have h3 : Vc hL (-φ) = -Vc hL φ := (Vc hL).map_neg φ
  linarith

/-- On `evenSub hL`, the pole term is a pure nonnegative square: `poleTerm(rep φ) = 2 Vc(φ)² ≥ 0`. -/
theorem poleTerm_rep_of_mem_evenSub (hL : 0 ≤ L) {φ : Cvs.WeilForm.FormDomain.formDomain hL}
    (hφ : φ ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL) :
    poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) = 2 * Vc hL φ ^ 2 := by
  rw [poleTerm_rep_centered, Uc_eq_zero_of_mem_evenSub hL hφ]
  ring

/-- On `evenSub hL`, `0 ≤ poleTerm(rep φ)` holds unconditionally. -/
theorem poleTerm_rep_nonneg_of_mem_evenSub (hL : 0 ≤ L) {φ : Cvs.WeilForm.FormDomain.formDomain hL}
    (hφ : φ ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL) :
    0 ≤ poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  rw [poleTerm_rep_of_mem_evenSub hL hφ]
  positivity

/-- On `evenSub hL`, the single linear condition `Vc φ = 0` is equivalent to `Mplus(rep φ) = 0`. -/
theorem Vc_eq_zero_iff_Mplus_eq_zero_of_mem_evenSub (hL : 0 ≤ L) {φ : Cvs.WeilForm.FormDomain.formDomain hL}
    (hφ : φ ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL) :
    Vc hL φ = 0 ↔ Mplus (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) = 0 := by
  have h := Vc_add_Uc hL φ
  rw [Uc_eq_zero_of_mem_evenSub hL hφ, add_zero] at h
  rw [h, mul_eq_zero, or_iff_right (Real.exp_ne_zero _)]

/-- On `evenSub hL`, the single linear condition `Vc φ = 0` is equivalent to `Mminus(rep φ) = 0`. -/
theorem Vc_eq_zero_iff_Mminus_eq_zero_of_mem_evenSub (hL : 0 ≤ L) {φ : Cvs.WeilForm.FormDomain.formDomain hL}
    (hφ : φ ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hL) :
    Vc hL φ = 0 ↔ Mminus (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) = 0 := by
  have h := Vc_sub_Uc hL φ
  rw [Uc_eq_zero_of_mem_evenSub hL hφ, sub_zero] at h
  rw [h, mul_eq_zero, or_iff_right (Real.exp_ne_zero _)]

/-- On the reflection-even subspace `Ev x`, `Q_x(φ) = N_x(φ) + 2 Vc(φ)²` with no `−2 U²` term. -/
theorem Q_eq_N_add_two_Vc_sq_of_mem_Ev (x : ℕ) {φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)}
    (hφ : φ ∈ Ev x) :
    Qx x φ = N x φ + 2 * Vc _ φ ^ 2 := by
  unfold Qx
  rw [Q_eq_N_centered, Uc_eq_zero_of_mem_evenSub _ hφ]
  ring

/-! ### Part 4: Normalized Box Anchor in `evenSub` and Centered Hodge-Index Equivalence for `RH` -/

/-- The midpoint-centered moment of the indicator box `boxD hl` is `4 sinh(l/4)`. -/
theorem Vc_boxD {l : ℝ} (hl : 0 < l) :
    Vc hl.le (boxD hl) = 4 * Real.sinh (l / 4) := by
  have hU : Uc hl.le (boxD hl) = 0 := Uc_eq_zero_of_mem_evenSub hl.le (reflD_boxD hl)
  have hadd := Vc_add_Uc hl.le (boxD hl)
  rw [hU, add_zero] at hadd
  have hrep : Cvs.WeilForm.WindowRepresentative.rep ((boxD hl : Cvs.WeilForm.FormDomain.formDomain hl.le) : Cvs.WeilForm.WeilFormOnWindowL2.window l) =ᵐ[volume] Cvs.WeilForm.WindowSetNonempty.flat l :=
    (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (coe_boxD_ae hl)
  have hM : Mplus (Cvs.WeilForm.WindowRepresentative.rep ((boxD hl : Cvs.WeilForm.FormDomain.formDomain hl.le) : Cvs.WeilForm.WeilFormOnWindowL2.window l))
      = (Real.exp (1 / 2 * l) - 1) / (1 / 2) := by
    unfold Mplus
    rw [integral_congr_ae (hrep.mono fun s hs => by rw [hs, show s / 2 = 1 / 2 * s by ring])]
    exact Cvs.Route.OneCellBoxWindowForm.integral_flat_exp hl.le (by norm_num)
  rw [hM] at hadd
  rw [Real.sinh_eq]
  have hexp : Real.exp (-(l / 4)) * Real.exp (1 / 2 * l) = Real.exp (l / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Vc hl.le (boxD hl)
      = 2 * (Real.exp (-(l / 4)) * Real.exp (1 / 2 * l) - Real.exp (-(l / 4))) := by linarith
    _ = 4 * ((Real.exp (l / 4) - Real.exp (-(l / 4))) / 2) := by rw [hexp]; ring

theorem Vc_boxD_pos {l : ℝ} (hl : 0 < l) : 0 < Vc hl.le (boxD hl) := by
  rw [Vc_boxD hl]
  exact mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (by linarith))

/-- The normalized box anchor `(4 sinh(l/4))⁻¹ • 1_{(0, l]}` in `formDomain hl.le`. -/
def normBoxD {l : ℝ} (hl : 0 < l) : Cvs.WeilForm.FormDomain.formDomain hl.le :=
  (4 * Real.sinh (l / 4))⁻¹ • boxD hl

theorem normBoxD_mem_evenSub {l : ℝ} (hl : 0 < l) :
    normBoxD hl ∈ Cvs.StepA.StepAFromTwoGaps.evenSub hl.le :=
  Submodule.smul_mem _ _ (reflD_boxD hl)

theorem Vc_normBoxD {l : ℝ} (hl : 0 < l) :
    Vc hl.le (normBoxD hl) = 1 := by
  unfold normBoxD
  rw [map_smul, smul_eq_mul, Vc_boxD hl]
  have hne : 4 * Real.sinh (l / 4) ≠ 0 := by
    have := Vc_boxD_pos hl; rw [Vc_boxD hl] at this; exact this.ne'
  exact inv_mul_cancel₀ hne

/-- The Toeplitz bilinear form `QWbil − 2 Vc ⊗ Vc` restricted to `Ev x`. -/
def NbilEv (x : ℕ) : LinearMap.BilinForm ℝ (Ev x) :=
  (Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
    - (2 : ℝ) • LinearMap.smulRight (Vc (Real.log_natCast_nonneg x)) (Vc (Real.log_natCast_nonneg x))).restrict
      (Ev x)

theorem NbilEv_self (x : ℕ) (φ : Ev x) :
    NbilEv x φ φ = N x (φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) := by
  simp only [NbilEv, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul,
    Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]
  have hQ := Q_eq_N_add_two_Vc_sq_of_mem_Ev x φ.2
  unfold Qx at hQ
  linarith

/-- **Centered Hodge-Index Equivalence on `Ev x`**: for any `f₀ ∈ Ev x` with `Vc f₀ = 1`, even window
positivity `∀ φ ∈ Ev x, 0 ≤ Q_x(φ)` holds iff `0 ≤ N_x(g)` on the pole-free even hyperplane
`{g ∈ Ev x : Vc g = 0}` (with no `−2 U²` term) and `0 ≤ Q_x(f₀ + g)` on the slice `f₀ + ker Vc`. -/
theorem evenWindowPos_iff_centered_hodge (x : ℕ)
    {f₀ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)} (hf₀ : f₀ ∈ Ev x) (h₀ : Vc _ f₀ = 1) :
    (∀ φ ∈ Ev x, 0 ≤ Qx x φ) ↔
      (∀ g ∈ Ev x, Vc _ g = 0 → 0 ≤ N x g) ∧
      (∀ g ∈ Ev x, Vc _ g = 0 → 0 ≤ Qx x (f₀ + g)) := by
  let vEv : Ev x →ₗ[ℝ] ℝ := (Vc (Real.log_natCast_nonneg x)).domRestrict (Ev x)
  have h₀' : vEv ⟨f₀, hf₀⟩ = 1 := h₀
  have key := nonneg_add_sq_iff (NbilEv x) vEv (c := 2) h₀'
  have hQ : ∀ φ : Ev x, Qx x φ.1 = NbilEv x φ φ + 2 * vEv φ ^ 2 := by
    intro φ
    rw [NbilEv_self, Q_eq_N_add_two_Vc_sq_of_mem_Ev x φ.2]
    rfl
  constructor
  · intro h
    have hSub : ∀ φ : Ev x, 0 ≤ NbilEv x φ φ + 2 * vEv φ ^ 2 := fun φ => by
      rw [← hQ φ]; exact h φ.1 φ.2
    obtain ⟨h1, h2⟩ := key.mp hSub
    refine ⟨fun g hgE hg0 => ?_, fun g hgE hg0 => ?_⟩
    · have := h1 ⟨g, hgE⟩ hg0
      rwa [NbilEv_self] at this
    · have := h2 ⟨g, hgE⟩ hg0
      rw [NbilEv_self, Submodule.coe_add] at this
      have hfg : f₀ + g ∈ Ev x := Submodule.add_mem _ hf₀ hgE
      have hvfg : Vc _ (f₀ + g) = 1 := by rw [map_add, h₀, hg0, add_zero]
      rw [Q_eq_N_add_two_Vc_sq_of_mem_Ev x hfg, hvfg]
      linarith
  · rintro ⟨h1, h2⟩ φ hφ
    have hSub : ∀ ψ : Ev x, 0 ≤ NbilEv x ψ ψ + 2 * vEv ψ ^ 2 := by
      refine key.mpr ⟨fun g hg0 => ?_, fun g hg0 => ?_⟩
      · rw [NbilEv_self]; exact h1 g.1 g.2 hg0
      · rw [NbilEv_self, Submodule.coe_add]
        have := h2 g.1 g.2 hg0
        have hfg : f₀ + g.1 ∈ Ev x := Submodule.add_mem _ hf₀ g.2
        have hvfg : Vc _ (f₀ + g.1) = 1 := by
          rw [map_add, h₀, show Vc _ g.1 = 0 from hg0, add_zero]
        rw [Q_eq_N_add_two_Vc_sq_of_mem_Ev x hfg, hvfg] at this
        linarith
    have := hSub ⟨φ, hφ⟩
    rwa [← hQ ⟨φ, hφ⟩] at this

/-- **Unconditional Centered Hodge-Index Characterization of `RiemannHypothesis`**: `RH` holds iff
frequently in `x`, `0 ≤ N_x(g)` on `{g ∈ Ev x : Vc g = 0}` and `0 ≤ Q_x(normBoxD + g)` on the box slice. -/
theorem rh_iff_frequently_centered_even_hodge :
    RiemannHypothesis ↔
      ∃ᶠ x : ℕ in atTop, ∃ hx2 : 2 ≤ x,
        (∀ g ∈ Ev x, Vc _ g = 0 → 0 ≤ N x g) ∧
        (∀ g ∈ Ev x, Vc _ g = 0 →
          0 ≤ Qx x (normBoxD (Real.log_pos (by exact_mod_cast hx2)) + g)) := by
  rw [Cvs.WeilForm.ReflectionEvenPositivityRH.rh_iff_frequently_evenWindowPos]
  constructor
  · intro h
    refine (h.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨hx, hx2⟩ => ?_
    have hl : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
    exact ⟨hx2, (evenWindowPos_iff_centered_hodge x (normBoxD_mem_evenSub hl) (Vc_normBoxD hl)).mp hx⟩
  · intro h
    refine h.mono fun x ⟨hx2, h1, h2⟩ => ?_
    have hl : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2)
    exact (evenWindowPos_iff_centered_hodge x (normBoxD_mem_evenSub hl) (Vc_normBoxD hl)).mpr ⟨h1, h2⟩

/-! ### Part 5: Open Problem 9.3 (`op:direct`) — `Cvs.Route.EigenvectorCoordinateCompression.sinSqClose_of_floorPerp` at Connes' Vectors Implies `RH` -/

/-- **Corollary B.3 (`cor:floorperp` at Connes' vectors)**: if for arbitrarily large `x`, `Meven` has a floor
`μ > q` on `(connesVec N x)ᗮ` with compressed-resolvent norm `‖(C − q)⁻¹ r‖² ≤ ε / (1 − ε)` at
`ε = 2 / (√x log x)`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_frequently_floorPerp_connes (P R : ℝ → ℕ)
    (hFP : ∃ N : ℝ → ℕ, (∀ᶠ x in atTop, Cvs.Route.JointGapAtConnesVectors.connesThreshold x ≤ N x) ∧
      ∃ᶠ x in atTop, ∃ (hL : 0 < Real.log x) (μ : ℝ)
        (hve : ∀ i, Cvs.Approximant.ConnesVectorRealScale.connesVec N x (negI (N x) i)
          = Cvs.Approximant.ConnesVectorRealScale.connesVec N x i),
        (∀ f : Idx (N x) → ℝ, (∀ i, f (negI (N x) i) = f i) →
          Cvs.Approximant.ConnesVectorRealScale.connesVec N x ⬝ᵥ f = 0 →
          μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M (P x) (R x) (Real.log x) (mode (N x)) *ᵥ f)) ∧
        Cvs.Approximant.ConnesVectorRealScale.connesVec N x
          ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M (P x) (R x) (Real.log x) (mode (N x))
            *ᵥ Cvs.Approximant.ConnesVectorRealScale.connesVec N x) < μ ∧
        ‖schurVec (Meven (P x) (R x) hL (N x)) (evenVec hve)
          (Cvs.Approximant.ConnesVectorRealScale.connesVec N x
            ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M (P x) (R x) (Real.log x) (mode (N x))
              *ᵥ Cvs.Approximant.ConnesVectorRealScale.connesVec N x))‖ ^ 2
          ≤ (2 / (√x * Real.log x)) / (1 - 2 / (√x * Real.log x))) :
    RiemannHypothesis := by
  obtain ⟨N, hN, hfreq⟩ := hFP
  obtain ⟨_, hv1, -⟩ := Cvs.Route.JointGapAtConnesVectors.stripApproximable_connesVec_of_threshold_le N hN
  refine Cvs.Route.GroundConnesAngle.riemannHypothesis_of_frequently_sinSq_connes_two_div P R ⟨N, hN, ?_⟩
  have hev : ∀ᶠ x : ℝ in atTop, 2 / (√x * Real.log x) < 1 := by
    filter_upwards [eventually_ge_atTop (Real.exp 3)] with x hx
    have hexp3 : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
    have hsqrt : 1 ≤ √x := Real.one_le_sqrt.mpr (hexp3.trans hx)
    have hlog : 3 ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos 3) hx
      rwa [Real.log_exp] at this
    rw [div_lt_one (by nlinarith)]
    nlinarith
  refine (hfreq.and_eventually hev).mono fun x ⟨⟨hL, μ, hve, hfloor, hqμ, hfp⟩, hx1⟩ => ?_
  exact sinSqClose_of_floorPerp hL hve (hv1 x) hfloor hqμ hx1 hfp

end Cvs.WeilForm.CentredHodgeIndexWindow
