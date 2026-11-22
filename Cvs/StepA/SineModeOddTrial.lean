import Mathlib
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.OneZeroSectorBottoms
import Cvs.StepA.SectorBottomsLowerBound
import Cvs.Upstream.SymmetricMatrixBottom

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The first `N` sine modes on the centred window: projection and the odd trial

With `sg(o)(t) = sinePoly(o)(t + L/2)`: `∫ sg(o) h = L (o ⬝ sinCoef h)`, `sinCoef (sg o) = o` for odd
`o`, and `projDefect h = ∫ h² − L ‖sinCoef h‖² = ∫ (h − sg(sinCoef h))²`. Projection raises
`(∫ φu)² − (∫ φv)²` by at most `∫ φ² (2√((∫ u² + ∫ v²) τ) + τ)`, so for every `L > 0`, `N`, `z` some odd
`o` has `L ‖o‖² ≤ 1` and `(∫ sg(o) uo)² − (∫ sg(o) vo)² ≤ lamO + 2√(sigO τ) + τ`.
-/

noncomputable section

open Real MeasureTheory Matrix

namespace Cvs.StepA.SineModeOddTrial
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI mode_negI mode_injective)
open Cvs.Finite.TruncationZeroFreeOffAxes (omega)
open Cvs.Finite.OddSectorZeroSide (sinePoly)
open Cvs.StepA.OneZeroParitySectors (uo vo continuous_uo continuous_vo winForm_apply)
open Cvs.StepA.OneZeroSectorBottoms (lamO sigO)
open Cvs.StepA.RankTwoBottom (lamMinus)

/-! ### The sine coefficients -/

/-- The coefficients of `h` against the first `N` sine modes on the centred window,
`L⁻¹ ∫ h(t) sin(ωᵢ(t + L/2))`. -/
def sinCoef (L : ℝ) (N : ℕ) (h : ℝ → ℝ) : Idx N → ℝ := fun i =>
  L⁻¹ * ∫ t in -(L / 2)..L / 2, h t * Real.sin (omega L (mode N) i * (t + L / 2))

/-- The sine coefficients are odd under the index involution. -/
theorem sinCoef_odd (L : ℝ) (N : ℕ) (h : ℝ → ℝ) (i : Idx N) :
    sinCoef L N h (negI N i) = -sinCoef L N h i := by
  unfold sinCoef
  rw [Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg (mode_negI N) i]
  simp only [neg_mul, Real.sin_neg, mul_neg, intervalIntegral.integral_neg]

/-- The centred sine polynomial of a coefficient vector is continuous. -/
theorem continuous_sinePoly_centred (L : ℝ) (N : ℕ) (o : Idx N → ℝ) :
    Continuous fun t => sinePoly L (mode N) o (t + L / 2) :=
  (Cvs.Finite.OddSectorZeroSide.continuous_sinePoly L (mode N) o).comp (continuous_add_const _)

/-- Against one sine mode, a centred sine polynomial integrates to `(L/2)(oᵢ − o_{−i})` when `L ≠ 0`. -/
theorem integral_sinePoly_mul_sin {L : ℝ} (hL : L ≠ 0) (N : ℕ) (o : Idx N → ℝ) (i : Idx N) :
    ∫ t in -(L / 2)..L / 2,
        sinePoly L (mode N) o (t + L / 2) * Real.sin (omega L (mode N) i * (t + L / 2))
      = L / 2 * (o i - o (negI N i)) := by
  classical
  rw [intervalIntegral.integral_comp_add_right
      (fun s => sinePoly L (mode N) o s * Real.sin (omega L (mode N) i * s)),
    show -(L / 2) + L / 2 = 0 by ring, show L / 2 + L / 2 = L by ring]
  have hpt : ∀ s, sinePoly L (mode N) o s * Real.sin (omega L (mode N) i * s)
      = ∑ j, o j * (Real.sin (omega L (mode N) i * s) * Real.sin (omega L (mode N) j * s)) := by
    intro s
    unfold sinePoly
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun j _ => (by fun_prop : Continuous fun s =>
    o j * (Real.sin (omega L (mode N) i * s) * Real.sin (omega L (mode N) j * s))).intervalIntegrable _ _]
  simp_rw [intervalIntegral.integral_const_mul,
    Cvs.StepA.SectorBottomsLowerBound.integral_sin_mul_sin hL (mode_injective N) (mode_negI N) i]
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

/-- **The sine coefficients invert the centred sine polynomial** on odd coefficient vectors, `L ≠ 0`. -/
theorem sinCoef_sinePoly {L : ℝ} (hL : L ≠ 0) (N : ℕ) {o : Idx N → ℝ}
    (ho : ∀ i, o (negI N i) = -o i) :
    sinCoef L N (fun t => sinePoly L (mode N) o (t + L / 2)) = o := by
  funext i
  simp only [sinCoef]
  rw [integral_sinePoly_mul_sin hL N o i, ho i]
  field_simp
  ring

/-- **A centred sine polynomial pairs with `h` through the sine coefficients**:
`∫ sg(o) h = L (o ⬝ sinCoef h)`. -/
theorem integral_sinePoly_mul (L : ℝ) (N : ℕ) (o : Idx N → ℝ) {h : ℝ → ℝ} (hh : Continuous h) :
    ∫ t in -(L / 2)..L / 2, sinePoly L (mode N) o (t + L / 2) * h t
      = L * (o ⬝ᵥ sinCoef L N h) := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  have hpt : ∀ t, sinePoly L (mode N) o (t + L / 2) * h t
      = ∑ i, o i * (h t * Real.sin (omega L (mode N) i * (t + L / 2))) := by
    intro t
    unfold sinePoly
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun i _ => (by fun_prop : Continuous fun t =>
    o i * (h t * Real.sin (omega L (mode N) i * (t + L / 2)))).intervalIntegrable _ _]
  simp only [dotProduct, sinCoef, Finset.mul_sum, intervalIntegral.integral_const_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  generalize (∫ t in -(L / 2)..L / 2, h t * Real.sin (omega L (mode N) i * (t + L / 2))) = X
  field_simp

/-! ### The Bessel defect -/

/-- The Bessel defect of `h` against the first `N` sine modes: `∫ h² − L ‖sinCoef h‖²`. -/
def projDefect (L : ℝ) (N : ℕ) (h : ℝ → ℝ) : ℝ :=
  (∫ t in -(L / 2)..L / 2, h t ^ 2) - L * (sinCoef L N h ⬝ᵥ sinCoef L N h)

/-- **The residuals of two projections pair to the defect form**:
`∫ (h₁ − sg(sinCoef h₁))(h₂ − sg(sinCoef h₂)) = ∫ h₁ h₂ − L (sinCoef h₁ ⬝ sinCoef h₂)`. -/
theorem integral_sub_mul_sub (L : ℝ) (N : ℕ) {h₁ h₂ : ℝ → ℝ} (h₁c : Continuous h₁)
    (h₂c : Continuous h₂) :
    ∫ t in -(L / 2)..L / 2, (h₁ t - sinePoly L (mode N) (sinCoef L N h₁) (t + L / 2))
        * (h₂ t - sinePoly L (mode N) (sinCoef L N h₂) (t + L / 2))
      = (∫ t in -(L / 2)..L / 2, h₁ t * h₂ t) - L * (sinCoef L N h₁ ⬝ᵥ sinCoef L N h₂) := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  have hs₁ := continuous_sinePoly_centred L N (sinCoef L N h₁)
  have hs₂ := continuous_sinePoly_centred L N (sinCoef L N h₂)
  have e₁₂ := integral_sinePoly_mul L N (sinCoef L N h₂) h₁c
  have e₂₁ := integral_sinePoly_mul L N (sinCoef L N h₁) h₂c
  have e₁₁ := integral_sinePoly_mul L N (sinCoef L N h₁) hs₂
  rw [sinCoef_sinePoly hL N (sinCoef_odd L N h₂)] at e₁₁
  have i1 : IntervalIntegrable (fun t => h₁ t * h₂ t) volume (-(L / 2)) (L / 2) :=
    (h₁c.mul h₂c).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => sinePoly L (mode N) (sinCoef L N h₂) (t + L / 2) * h₁ t)
      volume (-(L / 2)) (L / 2) := (hs₂.mul h₁c).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t => sinePoly L (mode N) (sinCoef L N h₁) (t + L / 2) * h₂ t)
      volume (-(L / 2)) (L / 2) := (hs₁.mul h₂c).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun t => sinePoly L (mode N) (sinCoef L N h₁) (t + L / 2)
      * sinePoly L (mode N) (sinCoef L N h₂) (t + L / 2)) volume (-(L / 2)) (L / 2) :=
    (hs₁.mul hs₂).intervalIntegrable _ _
  have hexp : ∀ t, (h₁ t - sinePoly L (mode N) (sinCoef L N h₁) (t + L / 2))
        * (h₂ t - sinePoly L (mode N) (sinCoef L N h₂) (t + L / 2))
      = h₁ t * h₂ t - sinePoly L (mode N) (sinCoef L N h₂) (t + L / 2) * h₁ t
        - sinePoly L (mode N) (sinCoef L N h₁) (t + L / 2) * h₂ t
        + sinePoly L (mode N) (sinCoef L N h₁) (t + L / 2)
          * sinePoly L (mode N) (sinCoef L N h₂) (t + L / 2) := fun t => by ring
  rw [intervalIntegral.integral_congr fun t _ => hexp t,
    intervalIntegral.integral_add ((i1.sub i2).sub i3) i4,
    intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    e₁₂, e₂₁, e₁₁, dotProduct_comm (sinCoef L N h₂) (sinCoef L N h₁)]
  ring

/-- The Bessel defect is the energy of the residual: `projDefect h = ∫ (h − sg(sinCoef h))²`. -/
theorem projDefect_eq_integral_sq (L : ℝ) (N : ℕ) {h : ℝ → ℝ} (hc : Continuous h) :
    projDefect L N h
      = ∫ t in -(L / 2)..L / 2, (h t - sinePoly L (mode N) (sinCoef L N h) (t + L / 2)) ^ 2 := by
  simp only [sq]
  rw [integral_sub_mul_sub L N hc hc, projDefect]
  simp only [sq]

/-- The Bessel defect is nonnegative for `L ≥ 0`. -/
theorem projDefect_nonneg {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {h : ℝ → ℝ} (hc : Continuous h) :
    0 ≤ projDefect L N h := by
  rw [projDefect_eq_integral_sq L N hc]
  exact intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _

/-- The Bessel defect is at most the energy `∫ h²` for `L ≥ 0`. -/
theorem projDefect_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (h : ℝ → ℝ) :
    projDefect L N h ≤ ∫ t in -(L / 2)..L / 2, h t ^ 2 := by
  have := mul_nonneg hL (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' (sinCoef L N h))
  unfold projDefect
  linarith

/-- A sine coefficient of a nonzero mode is `±L⁻¹ ∫ h(t) sin(2π(k+1)t/L)`, so its square is that of the
latter. -/
theorem sinCoef_some_sq {L : ℝ} (hL : L ≠ 0) (N : ℕ) (h : ℝ → ℝ) (k : Fin N) (b : Bool) :
    sinCoef L N h (some (k, b)) * sinCoef L N h (some (k, b))
      = (L⁻¹ * ∫ t in -(L / 2)..L / 2,
          h t * Real.sin (2 * π * (((k : ℕ) : ℝ) + 1) / L * t)) ^ 2 := by
  set ε : ℝ := (if b then 1 else -1) * (-1) ^ ((k : ℕ) + 1) with hε
  have hε2 : ε * ε = 1 := by
    have hs : (if b then (1 : ℝ) else -1) * (if b then 1 else -1) = 1 := by cases b <;> norm_num
    have hp : ((-1 : ℝ) ^ ((k : ℕ) + 1)) * (-1) ^ ((k : ℕ) + 1) = 1 := by
      rw [← mul_pow]; norm_num
    calc ε * ε = ((if b then (1 : ℝ) else -1) * (if b then 1 else -1))
          * (((-1 : ℝ) ^ ((k : ℕ) + 1)) * (-1) ^ ((k : ℕ) + 1)) := by rw [hε]; ring
      _ = 1 := by rw [hs, hp, one_mul]
  have hang : ∀ t, Real.sin (omega L (mode N) (some (k, b)) * (t + L / 2))
      = ε * Real.sin (2 * π * (((k : ℕ) : ℝ) + 1) / L * t) := by
    intro t
    have harg : 2 * π * (((k : ℕ) : ℝ) + 1) / L * (t + L / 2)
        = 2 * π * (((k : ℕ) : ℝ) + 1) / L * t + (((k : ℕ) + 1 : ℕ) : ℝ) * π := by
      push_cast; field_simp
    rw [hε]
    rcases Bool.eq_false_or_eq_true b with rfl | rfl
    · simp only [omega, mode, if_true]
      push_cast
      rw [harg, Real.sin_add_nat_mul_pi]
      ring
    · simp only [omega, mode, Bool.false_eq_true, if_false]
      push_cast
      rw [show 2 * π * -(((k : ℕ) : ℝ) + 1) / L * (t + L / 2)
          = -(2 * π * (((k : ℕ) : ℝ) + 1) / L * (t + L / 2)) by ring, Real.sin_neg, harg,
        Real.sin_add_nat_mul_pi]
      ring
  have hcoef : sinCoef L N h (some (k, b))
      = ε * (L⁻¹ * ∫ t in -(L / 2)..L / 2,
          h t * Real.sin (2 * π * (((k : ℕ) : ℝ) + 1) / L * t)) := by
    simp only [sinCoef, hang]
    rw [show (fun t => h t * (ε * Real.sin (2 * π * (((k : ℕ) : ℝ) + 1) / L * t)))
        = fun t => ε * (h t * Real.sin (2 * π * (((k : ℕ) : ℝ) + 1) / L * t)) from
        funext fun t => by ring, intervalIntegral.integral_const_mul]
    ring
  rw [hcoef]
  linear_combination (L⁻¹ * ∫ t in -(L / 2)..L / 2,
    h t * Real.sin (2 * π * (((k : ℕ) : ℝ) + 1) / L * t)) ^ 2 * hε2

/-- **The projection energy as a sum over the first `N` sine frequencies**:
`L ‖sinCoef h‖² = ∑_{k<N} (2/L) (∫ h(t) sin(2π(k+1)t/L))²`. -/
theorem mul_dotProduct_sinCoef_self (L : ℝ) (N : ℕ) (h : ℝ → ℝ) :
    L * (sinCoef L N h ⬝ᵥ sinCoef L N h)
      = ∑ k ∈ Finset.range N,
          2 / L * (∫ t in -(L / 2)..L / 2, h t * Real.sin (2 * π * (k + 1) / L * t)) ^ 2 := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  have h0 : sinCoef L N h none = 0 := by simp [sinCoef, omega, mode]
  simp only [dotProduct, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool, h0,
    mul_zero, zero_add, sinCoef_some_sq hL N h]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (L⁻¹ * ∫ t in -(L / 2)..L / 2,
      h t * Real.sin (2 * π * ((k : ℝ) + 1) / L * t)) ^ 2 + (L⁻¹ * ∫ t in -(L / 2)..L / 2,
      h t * Real.sin (2 * π * ((k : ℝ) + 1) / L * t)) ^ 2) N, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  ring

/-- The Bessel defect as the energy minus the first `N` sine frequencies' squared overlaps. -/
theorem projDefect_eq_sub_sum (L : ℝ) (N : ℕ) (h : ℝ → ℝ) :
    projDefect L N h = (∫ t in -(L / 2)..L / 2, h t ^ 2)
      - ∑ k ∈ Finset.range N,
          2 / L * (∫ t in -(L / 2)..L / 2, h t * Real.sin (2 * π * (k + 1) / L * t)) ^ 2 := by
  rw [projDefect, mul_dotProduct_sinCoef_self]

/-! ### The perturbation inequality -/

/-- **A difference of squares under nearby arguments**: if `a² ≤ P`, `b² ≤ Q`, `(a' − a)² ≤ τu` and
`(b' − b)² ≤ τv`, then `a'² − b'² ≤ a² − b² + 2√((P + Q)(τu + τv)) + (τu + τv)`. -/
theorem sq_sub_sq_le_of_near {a b a' b' P Q τu τv : ℝ} (ha : a ^ 2 ≤ P) (hb : b ^ 2 ≤ Q)
    (hu : (a' - a) ^ 2 ≤ τu) (hv : (b' - b) ^ 2 ≤ τv) :
    a' ^ 2 - b' ^ 2 ≤ a ^ 2 - b ^ 2 + 2 * √((P + Q) * (τu + τv)) + (τu + τv) := by
  have hCS : (a * (a' - a) - b * (b' - b)) ^ 2 ≤ (P + Q) * (τu + τv) := by
    have h1 : (a * (a' - a) - b * (b' - b)) ^ 2
        ≤ (a ^ 2 + b ^ 2) * ((a' - a) ^ 2 + (b' - b) ^ 2) := by
      nlinarith [sq_nonneg (a * (b' - b) + b * (a' - a))]
    have h2 : (a ^ 2 + b ^ 2) * ((a' - a) ^ 2 + (b' - b) ^ 2) ≤ (P + Q) * (τu + τv) :=
      mul_le_mul (by linarith) (by linarith) (by positivity)
        (by linarith [sq_nonneg a, sq_nonneg b])
    linarith
  have hs : a * (a' - a) - b * (b' - b) ≤ √((P + Q) * (τu + τv)) :=
    (le_abs_self _).trans (Real.abs_le_sqrt hCS)
  nlinarith [sq_nonneg (b' - b)]

/-- **Projection perturbs a pairing difference by a defect term**: for `L ≥ 0` and continuous `φ, u, v`,
with `τ` the sum of the defects of `u` and `v`, `(∫ sg(sinCoef φ) u)² − (∫ sg(sinCoef φ) v)²` is at most
`(∫ φu)² − (∫ φv)² + ∫ φ² · (2√((∫ u² + ∫ v²) τ) + τ)`. -/
theorem sq_sub_sq_sinCoef_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {φ u v : ℝ → ℝ} (hφ : Continuous φ)
    (hu : Continuous u) (hv : Continuous v) :
    (∫ t in -(L / 2)..L / 2, sinePoly L (mode N) (sinCoef L N φ) (t + L / 2) * u t) ^ 2
        - (∫ t in -(L / 2)..L / 2, sinePoly L (mode N) (sinCoef L N φ) (t + L / 2) * v t) ^ 2
      ≤ (∫ t in -(L / 2)..L / 2, φ t * u t) ^ 2 - (∫ t in -(L / 2)..L / 2, φ t * v t) ^ 2
        + (∫ t in -(L / 2)..L / 2, φ t ^ 2)
          * (2 * √(((∫ t in -(L / 2)..L / 2, u t ^ 2) + ∫ t in -(L / 2)..L / 2, v t ^ 2)
              * (projDefect L N u + projDefect L N v))
            + (projDefect L N u + projDefect L N v)) := by
  have hI0 : 0 ≤ ∫ t in -(L / 2)..L / 2, φ t ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _
  have cs : ∀ f g : ℝ → ℝ, Continuous f → Continuous g →
      (∫ t in -(L / 2)..L / 2, f t * g t) ^ 2
        ≤ (∫ t in -(L / 2)..L / 2, f t ^ 2) * ∫ t in -(L / 2)..L / 2, g t ^ 2 := by
    intro f g hf hg
    have h := Cvs.StepA.OneZeroSectorBottoms.winForm_sq_le L ⟨f, hf⟩ ⟨g, hg⟩
    simp only [winForm_apply, ContinuousMap.coe_mk] at h
    simpa only [sq] using h
  have hres : ∀ h : ℝ → ℝ, Continuous h →
      Continuous fun t => h t - sinePoly L (mode N) (sinCoef L N h) (t + L / 2) := fun h hc =>
    hc.sub (continuous_sinePoly_centred L N _)
  have near : ∀ w : ℝ → ℝ, Continuous w →
      ((∫ t in -(L / 2)..L / 2, sinePoly L (mode N) (sinCoef L N φ) (t + L / 2) * w t)
          - ∫ t in -(L / 2)..L / 2, φ t * w t) ^ 2
        ≤ (∫ t in -(L / 2)..L / 2, φ t ^ 2) * projDefect L N w := by
    intro w hw
    have hdiff : (∫ t in -(L / 2)..L / 2, sinePoly L (mode N) (sinCoef L N φ) (t + L / 2) * w t)
          - ∫ t in -(L / 2)..L / 2, φ t * w t
        = -∫ t in -(L / 2)..L / 2, (φ t - sinePoly L (mode N) (sinCoef L N φ) (t + L / 2))
            * (w t - sinePoly L (mode N) (sinCoef L N w) (t + L / 2)) := by
      rw [integral_sub_mul_sub L N hφ hw, integral_sinePoly_mul L N _ hw]
      ring
    rw [hdiff, neg_sq]
    refine (cs _ _ (hres φ hφ) (hres w hw)).trans ?_
    rw [← projDefect_eq_integral_sq L N hφ, ← projDefect_eq_integral_sq L N hw]
    exact mul_le_mul_of_nonneg_right (projDefect_le hL N φ) (projDefect_nonneg hL N hw)
  have key := sq_sub_sq_le_of_near (cs φ u hφ hu) (cs φ v hφ hv) (near u hu) (near v hv)
  have hsqrt : ∀ I A B p q : ℝ, 0 ≤ I →
      √((I * A + I * B) * (I * p + I * q)) = I * √((A + B) * (p + q)) := by
    intro I A B p q hI
    rw [show (I * A + I * B) * (I * p + I * q) = I ^ 2 * ((A + B) * (p + q)) by ring,
      Real.sqrt_mul (sq_nonneg I), Real.sqrt_sq hI]
  rw [hsqrt _ _ _ _ _ hI0] at key
  refine key.trans (le_of_eq ?_)
  ring

/-! ### The odd trial -/

/-- The odd trial bound at `z`: `lamO + 2√(sigO τ) + τ`, with `τ` the sum of the Bessel defects of `uo z`
and `vo z`. -/
def trialBound (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  lamO L z + 2 * √(sigO L z * (projDefect L N (uo z) + projDefect L N (vo z)))
    + (projDefect L N (uo z) + projDefect L N (vo z))

end Cvs.StepA.SineModeOddTrial
