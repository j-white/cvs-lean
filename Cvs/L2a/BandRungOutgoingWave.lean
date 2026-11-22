import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.BandTransferKernelForm
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.CutKernelSimplified
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.QIdentityCutPoint
import Cvs.L2a.ScaledBandTransfer
import Cvs.Prolate.BandMassLaw
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The outgoing wave of a band rung and the E-coupling bound

`V(y) = ∫ g(s)e^{ic(y+s)}/(y+s) ds` solves the radial equation on `(1, ∞)`, with Wronskian `c(A² + B²)` and
`(y² − 1)|V|² ≤ (A² + B²)Λ̂`, `Λ̂ = Λ + √(Λ² − 1)`, `Λ = (1 − w/2)⁻²`. LBT-h at the cuts, collar charged to the windows:
`|⟨ψ_j, dilSum(Φ, M)⟩| ≤ [√(ψ_j(1)²Λ̂₀C_E/c) + ‖g_j‖₁√(54(π²/12 − 11/16)/(πc³)) + K₀√(cK_col) + K_bτ̄√(8(1+1/t)J)
+ T + η]√P` with no constant depending on `M`; `C_E = (1/π)Σ_{m≥2} L_m ≤ 0.017211`.
-/
namespace Cvs.L2a.BandRungOutgoingWave

open Real Set Filter Topology MeasureTheory intervalIntegral
open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation
open scoped Interval

/-! ### Differentiation under the integral near a point -/

/-- **Differentiation under the integral** for a kernel regular on a ball about `y₀` and on `s ∈ [−1, 1]`. -/
theorem hasDerivAt_kint_near {g : ℝ → ℝ} {k k' : ℝ → ℝ → ℝ} {y₀ δ C : ℝ} (hδ : 0 < δ)
    (hg : ContinuousOn g (Icc (-1) 1)) (hkc : ∀ y ∈ Metric.ball y₀ δ, ContinuousOn (k y) (Icc (-1) 1))
    (hk'c : ContinuousOn (k' y₀) (Icc (-1) 1))
    (hd : ∀ y ∈ Metric.ball y₀ δ, ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun y => k y s) (k' y s) y)
    (hb : ∀ y ∈ Metric.ball y₀ δ, ∀ s ∈ Icc (-1 : ℝ) 1, |k' y s| ≤ C) :
    HasDerivAt (kint g k) (kint g k' y₀) y₀ := by
  have hu : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hI : ∀ s ∈ Ι (-1 : ℝ) 1, s ∈ Icc (-1 : ℝ) 1 := by
    intro s hs
    rw [uIoc_of_le (by norm_num)] at hs
    exact ⟨hs.1.le, hs.2⟩
  have hint : ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) →
      IntervalIntegrable (fun s => g s * f s) volume (-1) 1 := fun f hf => by
    apply ContinuousOn.intervalIntegrable
    rw [hu]; exact hg.mul hf
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := -1) (b := 1) (F := fun y s => g s * k y s) (F' := fun y s => g s * k' y s) (x₀ := y₀)
    (bound := fun s => |g s| * C) (s := Metric.ball y₀ δ) (Metric.ball_mem_nhds y₀ hδ)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds y₀ hδ) fun y hy =>
      ((hint _ (hkc y hy)).def').aestronglyMeasurable)
    (hint _ (hkc y₀ (Metric.mem_ball_self hδ)))
    ((hint _ hk'c).def').aestronglyMeasurable
    (Filter.Eventually.of_forall fun s hs y hy => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hb y hy s (hI s hs)) (abs_nonneg _))
    (by
      apply ContinuousOn.intervalIntegrable
      rw [hu]; exact hg.abs.mul continuousOn_const)
    (Filter.Eventually.of_forall fun s hs y hy => (hd y hy s (hI s hs)).const_mul (g s))
  exact key.2

/-! ### A kernel transform `∫ g(s) h(y + s) ds` is radial when `(z²h')' + c²z²h = 0` -/

section kernel
variable {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ : ℝ}

/-- The kernel identity behind the shift transform: `L_y h(y+s) − (−L_s h(y+s)) = ((y−s)/z)·[(z²h')' + c²z²h]`. -/
theorem shift_kernel_sym {y s z H H₁ H₂ : ℝ} (hz : z = y + s)
    (hode : z * H₂ + 2 * H₁ + c ^ 2 * z * H = 0) :
    (y ^ 2 - 1) * H₂ + 2 * y * H₁ + c ^ 2 * y ^ 2 * H
      = -((1 - s ^ 2) * H₂ - 2 * s * H₁) + c ^ 2 * s ^ 2 * H := by
  subst hz
  linear_combination (y - s) * hode

/-- The shift transform `y ↦ ∫_{−1}^{1} g(s) h(y + s) ds`. -/
noncomputable def shiftT (g h : ℝ → ℝ) (y : ℝ) : ℝ := kint g (fun y s => h (y + s)) y

/-- `h` is continuous on `(0, ∞)` when it is differentiable there. -/
theorem continuousOn_of_deriv (hh : ∀ z, 0 < z → HasDerivAt h (h₁ z) z) : ContinuousOn h (Ioi 0) :=
  fun z hz => (hh z hz).continuousAt.continuousWithinAt

/-- The shift of `h` is continuous on `[−1, 1]` for `y > 1`. -/
theorem continuousOn_shift (hh : ContinuousOn h (Ioi 0)) {y : ℝ} (hy : 1 < y) :
    ContinuousOn (fun s => h (y + s)) (Icc (-1) 1) := by
  refine hh.comp (continuousOn_const.add continuousOn_id) fun s hs => ?_
  show 0 < y + s
  linarith [hs.1]

/-- **Differentiating the shift transform**: `d/dy ∫ g h(y + s) = ∫ g h'(y + s)` for `y > 1`. -/
theorem hasDerivAt_shiftT (hg : ContinuousOn g (Icc (-1) 1)) (hh : ∀ z, 0 < z → HasDerivAt h (h₁ z) z)
    (hh₁ : ContinuousOn h₁ (Ioi 0)) {y : ℝ} (hy : 1 < y) :
    HasDerivAt (shiftT g h) (shiftT g h₁ y) y := by
  set δ := (y - 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hball : ∀ x ∈ Metric.ball y δ, 1 < x ∧ x < y + δ ∧ y - δ < x := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    refine ⟨?_, ?_, ?_⟩ <;> linarith [hx.1, hx.2]
  -- a bound for `h₁` on the compact range of `x + s`
  have hK : IsCompact (Icc ((y - 1) / 2) (y + δ + 1)) := isCompact_Icc
  have hsub : Icc ((y - 1) / 2) (y + δ + 1) ⊆ Ioi 0 := fun z hz => by
    show 0 < z; linarith [hz.1]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hh₁.mono hsub)
  apply hasDerivAt_kint_near (C := C) hδ0 hg
  · intro x hx
    exact continuousOn_shift (continuousOn_of_deriv hh) (hball x hx).1
  · exact continuousOn_shift hh₁ hy
  · intro x hx s hs
    have hz : 0 < x + s := by linarith [(hball x hx).1, hs.1]
    exact (hh (x + s) hz).comp_add_const
  · intro x hx s hs
    have h1 := hball x hx
    have hz : x + s ∈ Icc ((y - 1) / 2) (y + δ + 1) := by
      constructor
      · rw [hδ] at h1; linarith [h1.2.2, hs.1]
      · linarith [h1.2.1, hs.2]
    simpa [Real.norm_eq_abs] using hC (x + s) hz

/-- **The shift transform is radial**: if `zh'' + 2h' + c²zh = 0` on `z > 0` and `g` solves the angular equation,
`(y² − 1)Y'' + 2yY' + (c²y² − χ)Y = 0` on `y > 1`. -/
theorem radial_shiftT (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hh : ∀ z, 0 < z → HasDerivAt h (h₁ z) z) (hh₁ : ∀ z, 0 < z → HasDerivAt h₁ (h₂ z) z)
    (hh₂ : ContinuousOn h₂ (Ioi 0)) (hode : ∀ z, 0 < z → z * h₂ z + 2 * h₁ z + c ^ 2 * z * h z = 0)
    {y : ℝ} (hy : 1 < y) :
    (y ^ 2 - 1) * shiftT g h₂ y + 2 * y * shiftT g h₁ y + (c ^ 2 * y ^ 2 - χ) * shiftT g h y = 0 := by
  have hu : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hpos : ∀ s ∈ uIcc (-1 : ℝ) 1, 0 < y + s := fun s hs => by
    rw [hu] at hs; linarith [hs.1]
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  have hK : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => h (y + s)) (h₁ (y + s)) s := fun s hs => by
    exact (hh (y + s) (hpos s hs)).comp_const_add
  have hK₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => h₁ (y + s)) (h₂ (y + s)) s := fun s hs => by
    exact (hh₁ (y + s) (hpos s hs)).comp_const_add
  have hcs : ∀ f : ℝ → ℝ, ContinuousOn f (Ioi 0) → ContinuousOn (fun s => f (y + s)) (uIcc (-1) 1) :=
    fun f hf => by rw [hu]; exact continuousOn_shift hf hy
  have hK₂c := hcs h₂ hh₂
  have ibp := ibp_weighted hg hg₁ hK hK₁ hg₂c hK₂c
  have hhc := hcs h (continuousOn_of_deriv hh)
  have hh₁c := hcs h₁ (continuousOn_of_deriv hh₁)
  unfold shiftT kint
  have e : ∀ s ∈ uIcc (-1 : ℝ) 1,
      (y ^ 2 - 1) * (g s * h₂ (y + s)) + 2 * y * (g s * h₁ (y + s)) + (c ^ 2 * y ^ 2 - χ) * (g s * h (y + s))
      = -(g s * ((1 - s ^ 2) * h₂ (y + s) - 2 * s * h₁ (y + s)))
        + ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) * h (y + s) := by
    intro s hs
    have hk := shift_kernel_sym (c := c) (rfl : y + s = y + s) (hode (y + s) (hpos s hs))
    have ha := hang s hs
    have : ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) = c ^ 2 * s ^ 2 * g s - χ * g s := by linarith
    rw [this]
    linear_combination (g s) * hk
  have hi : ∀ f : ℝ → ℝ, ContinuousOn f (uIcc (-1) 1) →
      IntervalIntegrable (fun s => g s * f s) volume (-1) 1 :=
    fun f hf => (hgc.mul hf).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add, ← intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_congr e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_neg, ibp]
    · ring
    · exact (hgc.mul (((continuousOn_const.sub (continuousOn_id.pow 2)).mul hK₂c).sub
        ((continuousOn_const.mul continuousOn_id).mul hh₁c))).neg.intervalIntegrable
    · exact ((((continuousOn_const.sub (continuousOn_id.pow 2)).mul hg₂c).sub
        ((continuousOn_const.mul continuousOn_id).mul hg₁c)).mul hhc).intervalIntegrable
  · exact ((hi _ hK₂c).const_mul _).add ((hi _ hh₁c).const_mul _)
  · exact (hi _ hhc).const_mul _
  · exact (hi _ hK₂c).const_mul _
  · exact (hi _ hh₁c).const_mul _

/-- **The shift transform as a radial system**: `Y' = U/p`, `U' = −qY` on `y > 1`, with `U = pY'`. -/
theorem shiftT_system (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hh : ∀ z, 0 < z → HasDerivAt h (h₁ z) z) (hh₁ : ∀ z, 0 < z → HasDerivAt h₁ (h₂ z) z)
    (hh₂ : ContinuousOn h₂ (Ioi 0)) (hode : ∀ z, 0 < z → z * h₂ z + 2 * h₁ z + c ^ 2 * z * h z = 0) :
    (∀ y, 1 < y → HasDerivAt (shiftT g h) ((fun y => pP y * shiftT g h₁ y) y / pP y) y)
      ∧ ∀ y, 1 < y → HasDerivAt (fun y => pP y * shiftT g h₁ y) (-(qP c χ y * shiftT g h y)) y := by
  have hu : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc : ContinuousOn g (Icc (-1) 1) := by
    rw [← hu]; exact fun s hs => (hg s hs).continuousAt.continuousWithinAt
  constructor
  · intro y hy
    have hp := (pP_pos hy).ne'
    have := hasDerivAt_shiftT hgc hh (continuousOn_of_deriv hh₁) hy
    refine this.congr_deriv ?_
    field_simp
  · intro y hy
    have h1 := hasDerivAt_shiftT hgc hh (continuousOn_of_deriv hh₁) hy
    have h2 := hasDerivAt_shiftT hgc hh₁ hh₂ hy
    have hp : HasDerivAt pP (2 * y) y := by
      unfold pP; simpa using (hasDerivAt_pow 2 y).sub_const 1
    have := hp.mul h2
    refine this.congr_deriv ?_
    have hr := radial_shiftT hg hg₁ hg₂c hang hh hh₁ hh₂ hode hy (χ := χ)
    unfold pP qP at *
    linarith

end kernel

/-! ### The two real parts of the outgoing wave -/

/-- `cos(cz)/z`. -/
noncomputable def hC (c z : ℝ) : ℝ := cos (c * z) / z

/-- `(cos(cz)/z)' = −c sin(cz)/z − cos(cz)/z²`. -/
noncomputable def hC₁ (c z : ℝ) : ℝ := -(c * sin (c * z)) / z - cos (c * z) / z ^ 2

/-- `(cos(cz)/z)'' = −c² cos(cz)/z + 2c sin(cz)/z² + 2cos(cz)/z³`. -/
noncomputable def hC₂ (c z : ℝ) : ℝ :=
  -(c ^ 2 * cos (c * z)) / z + 2 * c * sin (c * z) / z ^ 2 + 2 * cos (c * z) / z ^ 3

/-- `sin(cz)/z`. -/
noncomputable def hS (c z : ℝ) : ℝ := sin (c * z) / z

/-- `(sin(cz)/z)' = c cos(cz)/z − sin(cz)/z²`. -/
noncomputable def hS₁ (c z : ℝ) : ℝ := c * cos (c * z) / z - sin (c * z) / z ^ 2

/-- `(sin(cz)/z)'' = −c² sin(cz)/z − 2c cos(cz)/z² + 2 sin(cz)/z³`. -/
noncomputable def hS₂ (c z : ℝ) : ℝ :=
  -(c ^ 2 * sin (c * z)) / z - 2 * c * cos (c * z) / z ^ 2 + 2 * sin (c * z) / z ^ 3

section kernels
variable {c z : ℝ}

theorem hasDerivAt_cos_mul (c z : ℝ) : HasDerivAt (fun z => cos (c * z)) (-(c * sin (c * z))) z := by
  have := ((hasDerivAt_id z).const_mul c).cos
  refine this.congr_deriv ?_; simp; ring

theorem hasDerivAt_sin_mul (c z : ℝ) : HasDerivAt (fun z => sin (c * z)) (c * cos (c * z)) z := by
  have := ((hasDerivAt_id z).const_mul c).sin
  refine this.congr_deriv ?_; simp; ring

theorem hasDerivAt_hC (hz : 0 < z) : HasDerivAt (hC c) (hC₁ c z) z := by
  have := (hasDerivAt_cos_mul c z).div (hasDerivAt_id z) hz.ne'
  refine this.congr_deriv ?_
  unfold hC₁; simp only [id]; field_simp

theorem hasDerivAt_hC₁ (hz : 0 < z) : HasDerivAt (hC₁ c) (hC₂ c z) z := by
  have h1 := ((hasDerivAt_sin_mul c z).const_mul c).neg.div (hasDerivAt_id z) hz.ne'
  have h2 := (hasDerivAt_cos_mul c z).div ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz.ne')
  have := h1.sub h2
  refine this.congr_deriv ?_
  unfold hC₂; simp only [id, Pi.neg_apply, Pi.pow_apply]; field_simp; ring

theorem hasDerivAt_hS (hz : 0 < z) : HasDerivAt (hS c) (hS₁ c z) z := by
  have := (hasDerivAt_sin_mul c z).div (hasDerivAt_id z) hz.ne'
  refine this.congr_deriv ?_
  unfold hS₁; simp only [id]; field_simp

theorem hasDerivAt_hS₁ (hz : 0 < z) : HasDerivAt (hS₁ c) (hS₂ c z) z := by
  have h1 := ((hasDerivAt_cos_mul c z).const_mul c).div (hasDerivAt_id z) hz.ne'
  have h2 := (hasDerivAt_sin_mul c z).div ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz.ne')
  have := h1.sub h2
  refine this.congr_deriv ?_
  unfold hS₂; simp only [id, Pi.pow_apply]; field_simp; ring

theorem continuousOn_hC₂ : ContinuousOn (hC₂ c) (Ioi 0) := fun z hz => by
  have hz' : z ≠ 0 := ne_of_gt hz
  unfold hC₂
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp [hz'])

theorem continuousOn_hS₂ : ContinuousOn (hS₂ c) (Ioi 0) := fun z hz => by
  have hz' : z ≠ 0 := ne_of_gt hz
  unfold hS₂
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp [hz'])

theorem ode_hC (hz : 0 < z) : z * hC₂ c z + 2 * hC₁ c z + c ^ 2 * z * hC c z = 0 := by
  unfold hC hC₁ hC₂; field_simp; ring

theorem ode_hS (hz : 0 < z) : z * hS₂ c z + 2 * hS₁ c z + c ^ 2 * z * hS c z = 0 := by
  unfold hS hS₁ hS₂; field_simp; ring

end kernels

/-- `Re V(y) = ∫ g(s) cos(c(y+s))/(y+s) ds`. -/
noncomputable def vC (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := shiftT g (hC c) y

/-- `Im V(y) = ∫ g(s) sin(c(y+s))/(y+s) ds`. -/
noncomputable def vS (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := shiftT g (hS c) y

/-- `p·(Re V)'`. -/
noncomputable def uC (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := pP y * shiftT g (hC₁ c) y

/-- `p·(Im V)'`. -/
noncomputable def uS (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := pP y * shiftT g (hS₁ c) y

section wave
variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- **`Re V` is a radial solution** on `(1, ∞)`. -/
theorem vC_system (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    (∀ y, 1 < y → HasDerivAt (vC c g) (uC c g y / pP y) y)
      ∧ ∀ y, 1 < y → HasDerivAt (uC c g) (-(qP c χ y * vC c g y)) y :=
  shiftT_system hg hg₁ hg₂c hang (fun _ hz => hasDerivAt_hC hz) (fun _ hz => hasDerivAt_hC₁ hz)
    continuousOn_hC₂ (fun _ hz => ode_hC hz)

/-- **`Im V` is a radial solution** on `(1, ∞)`. -/
theorem vS_system (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    (∀ y, 1 < y → HasDerivAt (vS c g) (uS c g y / pP y) y)
      ∧ ∀ y, 1 < y → HasDerivAt (uS c g) (-(qP c χ y * vS c g y)) y :=
  shiftT_system hg hg₁ hg₂c hang (fun _ hz => hasDerivAt_hS hz) (fun _ hz => hasDerivAt_hS₁ hz)
    continuousOn_hS₂ (fun _ hz => ode_hS hz)

end wave

/-! ### Asymptotics at `y → ∞` -/

/-- `‖g‖₁ = ∫_{−1}^{1} |g|`. -/
noncomputable def gL1 (g : ℝ → ℝ) : ℝ := ∫ s in (-1 : ℝ)..1, |g s|

/-- `A = ∫ g(s) cos(cs) ds`, the real part of `∫ g e^{ics}`. -/
noncomputable def cA (c : ℝ) (g : ℝ → ℝ) : ℝ := ∫ s in (-1 : ℝ)..1, g s * cos (c * s)

/-- `B = ∫ g(s) sin(cs) ds`, the imaginary part of `∫ g e^{ics}`. -/
noncomputable def cB (c : ℝ) (g : ℝ → ℝ) : ℝ := ∫ s in (-1 : ℝ)..1, g s * sin (c * s)

section asymp
variable {g : ℝ → ℝ} {c : ℝ}

theorem uIcc_neg_one_one : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)

theorem ii_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    IntervalIntegrable f volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable; rw [uIcc_neg_one_one]; exact hf

/-- `|∫ g k| ≤ ‖g‖₁ K` when `|k| ≤ K` on `[−1, 1]`. -/
theorem abs_int_le {k : ℝ → ℝ} {K : ℝ} (hgc : ContinuousOn g (Icc (-1) 1))
    (hk : ∀ s ∈ Icc (-1 : ℝ) 1, |k s| ≤ K) : |∫ s in (-1 : ℝ)..1, g s * k s| ≤ gL1 g * K := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := fun s => g s * k s)
    (g := fun s => |g s| * K) (by norm_num : (-1 : ℝ) ≤ 1)
    (ae_of_all _ fun s hs => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hk s ⟨hs.1.le, hs.2⟩) (abs_nonneg _))
    (ii_of_continuousOn (hgc.abs.mul continuousOn_const))
  rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const] at h
  exact h

theorem gL1_nonneg : 0 ≤ gL1 g :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _

/-- `A cos(cy) − B sin(cy) = ∫ g(s) cos(c(y + s)) ds`. -/
theorem cos_shift_eq (hgc : ContinuousOn g (Icc (-1) 1)) (y : ℝ) :
    cA c g * cos (c * y) - cB c g * sin (c * y) = ∫ s in (-1 : ℝ)..1, g s * cos (c * (y + s)) := by
  unfold cA cB
  rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const,
    ← intervalIntegral.integral_sub (ii_of_continuousOn (by fun_prop)) (ii_of_continuousOn (by fun_prop))]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [mul_add, cos_add]; ring

/-- `A sin(cy) + B cos(cy) = ∫ g(s) sin(c(y + s)) ds`. -/
theorem sin_shift_eq (hgc : ContinuousOn g (Icc (-1) 1)) (y : ℝ) :
    cA c g * sin (c * y) + cB c g * cos (c * y) = ∫ s in (-1 : ℝ)..1, g s * sin (c * (y + s)) := by
  unfold cA cB
  rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const,
    ← intervalIntegral.integral_add (ii_of_continuousOn (by fun_prop)) (ii_of_continuousOn (by fun_prop))]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [mul_add, sin_add]; ring

theorem pos_of_mem {y s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) : y - 1 ≤ y + s := by linarith [hs.1]

theorem continuousOn_shift' {h h₁ : ℝ → ℝ} (hh : ∀ z, 0 < z → HasDerivAt h (h₁ z) z) {y : ℝ} (hy : 1 < y) :
    ContinuousOn (fun s => h (y + s)) (Icc (-1) 1) :=
  continuousOn_shift (continuousOn_of_deriv hh) hy

/-- A kernel difference `y·∫ g h(y + s) − ∫ g k(y + s)` as one integral. -/
theorem mul_shiftT_sub {h h₁ k : ℝ → ℝ} (hgc : ContinuousOn g (Icc (-1) 1))
    (hh : ∀ z, 0 < z → HasDerivAt h (h₁ z) z) (hk : Continuous k) {y : ℝ} (hy : 1 < y) :
    y * shiftT g h y - ∫ s in (-1 : ℝ)..1, g s * k (y + s)
      = ∫ s in (-1 : ℝ)..1, g s * (y * h (y + s) - k (y + s)) := by
  unfold shiftT kint
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr fun s _ => ?_
    simp only; ring
  · exact ii_of_continuousOn (continuousOn_const.mul (hgc.mul (continuousOn_shift' hh hy)))
  · exact ii_of_continuousOn (hgc.mul (by fun_prop))

theorem abs_div_shift_le {y s : ℝ} (hy : 1 < y) (hs : s ∈ Icc (-1 : ℝ) 1) : |s| / (y + s) ≤ 1 / (y - 1) := by
  have h1 := pos_of_mem (y := y) hs
  have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2⟩
  have hp : 0 < y - 1 := by linarith
  rw [div_le_div_iff₀ (by linarith) hp]
  nlinarith [abs_nonneg s]

theorem inv_sq_shift_le {y s : ℝ} (hy : 1 < y) (hs : s ∈ Icc (-1 : ℝ) 1) : 1 / (y + s) ^ 2 ≤ 1 / (y - 1) ^ 2 := by
  have h1 := pos_of_mem (y := y) hs
  have hp : 0 < y - 1 := by linarith
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp.le h1 2)

/-- **`yRe V ≈ A cos(cy) − B sin(cy)`** with error `‖g‖₁/(y − 1)`. -/
theorem abs_vC_sub_le (hgc : ContinuousOn g (Icc (-1) 1)) {y : ℝ} (hy : 1 < y) :
    |y * vC c g y - (cA c g * cos (c * y) - cB c g * sin (c * y))| ≤ gL1 g * (1 / (y - 1)) := by
  have hm := mul_shiftT_sub (k := fun z => cos (c * z)) hgc (fun _ hz => hasDerivAt_hC (c := c) hz) (by fun_prop) hy
  beta_reduce at hm
  rw [cos_shift_eq hgc, vC, hm]
  apply abs_int_le hgc
  intro s hs
  have h1 := pos_of_mem (y := y) hs
  have hz : 0 < y + s := by linarith
  have e : y * hC c (y + s) - cos (c * (y + s)) = -s * cos (c * (y + s)) / (y + s) := by
    unfold hC; field_simp; ring
  rw [e, abs_div, abs_mul, abs_neg, abs_of_pos hz]
  calc |s| * |cos (c * (y + s))| / (y + s) ≤ |s| * 1 / (y + s) := by
        gcongr; exact abs_cos_le_one _
    _ ≤ 1 / (y - 1) := by rw [mul_one]; exact abs_div_shift_le hy hs

/-- **`yIm V ≈ A sin(cy) + B cos(cy)`** with error `‖g‖₁/(y − 1)`. -/
theorem abs_vS_sub_le (hgc : ContinuousOn g (Icc (-1) 1)) {y : ℝ} (hy : 1 < y) :
    |y * vS c g y - (cA c g * sin (c * y) + cB c g * cos (c * y))| ≤ gL1 g * (1 / (y - 1)) := by
  have hm := mul_shiftT_sub (k := fun z => sin (c * z)) hgc (fun _ hz => hasDerivAt_hS (c := c) hz) (by fun_prop) hy
  beta_reduce at hm
  rw [sin_shift_eq hgc, vS, hm]
  apply abs_int_le hgc
  intro s hs
  have h1 := pos_of_mem (y := y) hs
  have hz : 0 < y + s := by linarith
  have e : y * hS c (y + s) - sin (c * (y + s)) = -s * sin (c * (y + s)) / (y + s) := by
    unfold hS; field_simp; ring
  rw [e, abs_div, abs_mul, abs_neg, abs_of_pos hz]
  calc |s| * |sin (c * (y + s))| / (y + s) ≤ |s| * 1 / (y + s) := by
        gcongr; exact abs_sin_le_one _
    _ ≤ 1 / (y - 1) := by rw [mul_one]; exact abs_div_shift_le hy hs

/-- The pointwise bound on the derivative kernels. -/
theorem deriv_kernel_le {y s : ℝ} (hc : 0 ≤ c) (hy : 2 ≤ y) (hs : s ∈ Icc (-1 : ℝ) 1) (u v : ℝ)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) : |c * s * u / (y + s) - y * v / (y + s) ^ 2| ≤ (c + 2) / (y - 1) := by
  have hy1 : 1 < y := by linarith
  have h1 := pos_of_mem (y := y) hs
  have hz : 0 < y + s := by linarith
  have hp : 0 < y - 1 := by linarith
  have ha : |c * s * u / (y + s)| ≤ c / (y - 1) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_pos hz]
    have := abs_div_shift_le hy1 hs
    have hsu : |s| * |u| ≤ |s| := by nlinarith [abs_nonneg s, abs_nonneg u]
    calc c * |s| * |u| / (y + s) ≤ c * (|s| / (y + s)) := by
          rw [mul_assoc, mul_div_assoc]; gcongr
      _ ≤ c * (1 / (y - 1)) := by gcongr
      _ = c / (y - 1) := by ring
  have hb : |y * v / (y + s) ^ 2| ≤ 2 / (y - 1) := by
    rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < y), abs_of_pos (pow_pos hz 2)]
    have h2 := inv_sq_shift_le hy1 hs
    calc y * |v| / (y + s) ^ 2 ≤ y * 1 / (y + s) ^ 2 := by gcongr
      _ = y * (1 / (y + s) ^ 2) := by ring
      _ ≤ y * (1 / (y - 1) ^ 2) := by gcongr
      _ ≤ 2 / (y - 1) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hp]; nlinarith
  calc _ ≤ |c * s * u / (y + s)| + |y * v / (y + s) ^ 2| := abs_sub _ _
    _ ≤ c / (y - 1) + 2 / (y - 1) := add_le_add ha hb
    _ = (c + 2) / (y - 1) := by ring

/-- **`y(Re V)' ≈ −c(A sin(cy) + B cos(cy))`** with error `‖g‖₁(c + 2)/(y − 1)`, `y ≥ 2`. -/
theorem abs_vC₁_sub_le (hc : 0 ≤ c) (hgc : ContinuousOn g (Icc (-1) 1)) {y : ℝ} (hy : 2 ≤ y) :
    |y * shiftT g (hC₁ c) y - c * -(cA c g * sin (c * y) + cB c g * cos (c * y))|
      ≤ gL1 g * ((c + 2) / (y - 1)) := by
  have hy1 : 1 < y := by linarith
  have e0 : c * -(cA c g * sin (c * y) + cB c g * cos (c * y))
      = ∫ s in (-1 : ℝ)..1, g s * (-(c * sin (c * (y + s)))) := by
    rw [sin_shift_eq hgc, ← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  have hm := mul_shiftT_sub (k := fun z => -(c * sin (c * z))) hgc (fun _ hz => hasDerivAt_hC₁ (c := c) hz)
    (by fun_prop) hy1
  beta_reduce at hm
  rw [e0, hm]
  apply abs_int_le hgc
  intro s hs
  have hz : 0 < y + s := by linarith [pos_of_mem (y := y) hs]
  have e : y * hC₁ c (y + s) - -(c * sin (c * (y + s)))
      = c * s * sin (c * (y + s)) / (y + s) - y * cos (c * (y + s)) / (y + s) ^ 2 := by
    unfold hC₁; field_simp; ring
  rw [e]
  exact deriv_kernel_le hc hy hs _ _ (abs_sin_le_one _) (abs_cos_le_one _)

/-- **`y(Im V)' ≈ c(A cos(cy) − B sin(cy))`** with error `‖g‖₁(c + 2)/(y − 1)`, `y ≥ 2`. -/
theorem abs_vS₁_sub_le (hc : 0 ≤ c) (hgc : ContinuousOn g (Icc (-1) 1)) {y : ℝ} (hy : 2 ≤ y) :
    |y * shiftT g (hS₁ c) y - c * (cA c g * cos (c * y) - cB c g * sin (c * y))|
      ≤ gL1 g * ((c + 2) / (y - 1)) := by
  have hy1 : 1 < y := by linarith
  have e0 : c * (cA c g * cos (c * y) - cB c g * sin (c * y))
      = ∫ s in (-1 : ℝ)..1, g s * (c * cos (c * (y + s))) := by
    rw [cos_shift_eq hgc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  have hm := mul_shiftT_sub (k := fun z => c * cos (c * z)) hgc (fun _ hz => hasDerivAt_hS₁ (c := c) hz)
    (by fun_prop) hy1
  beta_reduce at hm
  rw [e0, hm]
  apply abs_int_le hgc
  intro s hs
  have hz : 0 < y + s := by linarith [pos_of_mem (y := y) hs]
  have e : y * hS₁ c (y + s) - c * cos (c * (y + s))
      = c * s * (-cos (c * (y + s))) / (y + s) - y * sin (c * (y + s)) / (y + s) ^ 2 := by
    unfold hS₁; field_simp; ring
  rw [e]
  exact deriv_kernel_le hc hy hs _ _ (by rw [abs_neg]; exact abs_cos_le_one _) (abs_sin_le_one _)

end asymp

/-! ### The energy limits and the Wronskian -/

section limits

/-- `rρ² − r₀α² → 0` when `r → r₀`, `ρ − α → 0` and `|α| ≤ M`. -/
theorem tendsto_r_sq_sub {r ρ α : ℝ → ℝ} {r₀ M : ℝ} (hr : Tendsto r atTop (𝓝 r₀))
    (he : Tendsto (fun y => ρ y - α y) atTop (𝓝 0)) (hα : ∀ y, |α y| ≤ M) :
    Tendsto (fun y => r y * ρ y ^ 2 - r₀ * α y ^ 2) atTop (𝓝 0) := by
  have hb : ∀ y, ‖r y * ρ y ^ 2 - r₀ * α y ^ 2‖
      ≤ |r y - r₀| * (M + |ρ y - α y|) ^ 2 + |r₀| * (|ρ y - α y| * (2 * M + |ρ y - α y|)) := by
    intro y
    rw [Real.norm_eq_abs]
    have e : r y * ρ y ^ 2 - r₀ * α y ^ 2
        = (r y - r₀) * ρ y ^ 2 + r₀ * ((ρ y - α y) * (ρ y + α y)) := by ring
    have h1 : |ρ y| ≤ M + |ρ y - α y| := by
      have := abs_sub_abs_le_abs_sub (ρ y) (α y); linarith [hα y]
    have h2 : |ρ y + α y| ≤ 2 * M + |ρ y - α y| := by
      have e2 : ρ y + α y = (ρ y - α y) + 2 * α y := by ring
      rw [e2]
      calc _ ≤ |ρ y - α y| + |2 * α y| := abs_add_le _ _
        _ = |ρ y - α y| + 2 * |α y| := by rw [abs_mul]; norm_num
        _ ≤ _ := by linarith [hα y]
    rw [e]
    calc _ ≤ |(r y - r₀) * ρ y ^ 2| + |r₀ * ((ρ y - α y) * (ρ y + α y))| := abs_add_le _ _
      _ = |r y - r₀| * |ρ y| ^ 2 + |r₀| * (|ρ y - α y| * |ρ y + α y|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_pow]
      _ ≤ _ := by gcongr
  have h1 : Tendsto (fun y => |r y - r₀|) atTop (𝓝 0) := by simpa using (hr.sub_const r₀).abs
  have h2 : Tendsto (fun y => |ρ y - α y|) atTop (𝓝 0) := by simpa using he.abs
  have hl := (h1.mul (((tendsto_const_nhds (x := M)).add h2).pow 2)).add
    ((tendsto_const_nhds (x := |r₀|)).mul (h2.mul ((tendsto_const_nhds (x := 2 * M)).add h2)))
  rw [zero_mul, zero_mul, mul_zero, add_zero] at hl
  exact squeeze_zero_norm hb hl

/-- `XY − x₀y₀ → 0` when `X − x₀ → 0`, `Y − y₀ → 0` and `x₀, y₀` are bounded. -/
theorem tendsto_mul_sub_mul {X Y x₀ y₀ : ℝ → ℝ} {M N : ℝ} (hX : Tendsto (fun y => X y - x₀ y) atTop (𝓝 0))
    (hY : Tendsto (fun y => Y y - y₀ y) atTop (𝓝 0)) (hx : ∀ y, |x₀ y| ≤ M) (hy : ∀ y, |y₀ y| ≤ N) :
    Tendsto (fun y => X y * Y y - x₀ y * y₀ y) atTop (𝓝 0) := by
  have hb : ∀ y, ‖X y * Y y - x₀ y * y₀ y‖ ≤ |X y - x₀ y| * (N + |Y y - y₀ y|) + M * |Y y - y₀ y| := by
    intro y
    rw [Real.norm_eq_abs]
    have e : X y * Y y - x₀ y * y₀ y = (X y - x₀ y) * Y y + x₀ y * (Y y - y₀ y) := by ring
    have hYb : |Y y| ≤ N + |Y y - y₀ y| := by
      have := abs_sub_abs_le_abs_sub (Y y) (y₀ y); linarith [hy y]
    rw [e]
    calc _ ≤ |(X y - x₀ y) * Y y| + |x₀ y * (Y y - y₀ y)| := abs_add_le _ _
      _ = |X y - x₀ y| * |Y y| + |x₀ y| * |Y y - y₀ y| := by rw [abs_mul, abs_mul]
      _ ≤ _ := by gcongr; exact hx y
  have h1 : Tendsto (fun y => |X y - x₀ y|) atTop (𝓝 0) := by simpa using hX.abs
  have h2 : Tendsto (fun y => |Y y - y₀ y|) atTop (𝓝 0) := by simpa using hY.abs
  have hl := (h1.mul ((tendsto_const_nhds (x := N)).add h2)).add ((tendsto_const_nhds (x := M)).mul h2)
  rw [zero_mul, mul_zero, add_zero] at hl
  exact squeeze_zero_norm hb hl

variable {c χ : ℝ}

/-- `a(y)/y² → c`. -/
theorem tendsto_aP_div_sq (hc : 0 < c) :
    Tendsto (fun y => aP c χ y / y ^ 2) atTop (𝓝 c) := by
  have hy : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub (hy.pow 2)).mul
    ((tendsto_const_nhds (x := c ^ 2)).sub ((tendsto_const_nhds (x := χ)).mul (hy.pow 2)))).sqrt
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, one_mul, mul_zero] at h
  rw [Real.sqrt_sq hc.le] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with y hy1
  have hy0 : y ≠ 0 := by positivity
  have e : pP y * qP c χ y = ((1 - y⁻¹ ^ 2) * (c ^ 2 - χ * y⁻¹ ^ 2)) * (y ^ 2) ^ 2 := by
    unfold pP qP; field_simp
  have ha : aP c χ y = √((1 - y⁻¹ ^ 2) * (c ^ 2 - χ * y⁻¹ ^ 2)) * y ^ 2 := by
    unfold aP
    rw [e, Real.sqrt_mul' _ (by positivity : (0 : ℝ) ≤ (y ^ 2) ^ 2), Real.sqrt_sq (by positivity)]
  rw [ha]
  field_simp

/-- `p(y)²/(a(y)y²) → 1/c`. -/
theorem tendsto_pP_sq_div (hc : 0 < c) (hχc : χ < c ^ 2) :
    Tendsto (fun y => pP y ^ 2 / (aP c χ y * y ^ 2)) atTop (𝓝 c⁻¹) := by
  have hy : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hp : Tendsto (fun y : ℝ => 1 - y⁻¹ ^ 2) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hy.pow 2)
  have h := (hp.pow 2).div (tendsto_aP_div_sq (χ := χ) hc) hc.ne'
  rw [one_pow, one_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with y hy1
  have hy0 : y ≠ 0 := by positivity
  have ha := (aP_pos hy1 (by positivity : (0 : ℝ) < c ^ 2) hχc).ne'
  simp only [Pi.div_apply]
  unfold pP
  field_simp

/-- `p(y)/y² → 1`. -/
theorem tendsto_pP_div_sq : Tendsto (fun y => pP y / y ^ 2) atTop (𝓝 1) := by
  have hy : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hp : Tendsto (fun y : ℝ => 1 - y⁻¹ ^ 2) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hy.pow 2)
  refine hp.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with y hy1
  have hy0 : y ≠ 0 := by positivity
  unfold pP; field_simp

/-- **The energy limit from the far asymptotics**: if `yf ≈ α`, `yf₁ ≈ cβ` with `α² + β² = K`, then the
energy of `(f, pf₁)` tends to `cK`. -/
theorem tendsto_energy_of_asymp {K : ℝ} {f f₁ α β ε₁ ε₂ : ℝ → ℝ} (hc : 0 < c) (hχc : χ < c ^ 2)
    (hK : ∀ y, α y ^ 2 + β y ^ 2 = K)
    (h1 : ∀ᶠ y in atTop, |y * f y - α y| ≤ ε₁ y) (h2 : ∀ᶠ y in atTop, |y * f₁ y - c * β y| ≤ ε₂ y)
    (hε₁ : Tendsto ε₁ atTop (𝓝 0)) (hε₂ : Tendsto ε₂ atTop (𝓝 0)) :
    Tendsto (energy (aP c χ) f (fun y => pP y * f₁ y)) atTop (𝓝 (c * K)) := by
  have hα : ∀ y, |α y| ≤ √K := fun y => Real.abs_le_sqrt (by nlinarith [hK y, sq_nonneg (β y)])
  have hβ : ∀ y, |c * β y| ≤ c * √K := fun y => by
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (Real.abs_le_sqrt (by nlinarith [hK y, sq_nonneg (α y)])) hc.le
  have he1 : Tendsto (fun y => y * f y - α y) atTop (𝓝 0) :=
    squeeze_zero_norm' (h1.mono fun y hy => by rwa [Real.norm_eq_abs]) hε₁
  have he2 : Tendsto (fun y => y * f₁ y - c * β y) atTop (𝓝 0) :=
    squeeze_zero_norm' (h2.mono fun y hy => by rwa [Real.norm_eq_abs]) hε₂
  have t := (tendsto_r_sq_sub (tendsto_aP_div_sq (χ := χ) hc) he1 hα).add
    (tendsto_r_sq_sub (tendsto_pP_sq_div hc hχc) he2 hβ)
  rw [add_zero] at t
  have hc2 : 0 < c ^ 2 := by positivity
  refine tendsto_sub_nhds_zero_iff.mp (t.congr' ?_)
  filter_upwards [eventually_gt_atTop 1] with y hy
  have ha := (aP_pos hy hc2 hχc).ne'
  have hy0 : y ≠ 0 := by positivity
  unfold energy
  rw [← hK y]
  field_simp
  ring

/-- `K/(y − 1) → 0`. -/
theorem tendsto_div_sub_one (K : ℝ) : Tendsto (fun y : ℝ => K / (y - 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => y - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
  exact tendsto_const_nhds.div_atTop h

theorem sq_add_sq_trig (A B t : ℝ) :
    (A * cos t - B * sin t) ^ 2 + (A * sin t + B * cos t) ^ 2 = A ^ 2 + B ^ 2 := by
  linear_combination (A ^ 2 + B ^ 2) * sin_sq_add_cos_sq t

variable {g g₁ g₂ : ℝ → ℝ}

/-- **The energy of `Re V` tends to `c(A² + B²)`**. -/
theorem tendsto_energy_vC (hgc : ContinuousOn g (Icc (-1) 1)) (hc : 0 < c) (hχc : χ < c ^ 2) :
    Tendsto (energy (aP c χ) (vC c g) (uC c g)) atTop (𝓝 (c * (cA c g ^ 2 + cB c g ^ 2))) := by
  refine tendsto_energy_of_asymp (f₁ := shiftT g (hC₁ c))
    (α := fun y => cA c g * cos (c * y) - cB c g * sin (c * y))
    (β := fun y => -(cA c g * sin (c * y) + cB c g * cos (c * y)))
    (ε₁ := fun y => gL1 g * (1 / (y - 1))) (ε₂ := fun y => gL1 g * ((c + 2) / (y - 1))) hc hχc
    (fun y => by simp only [neg_sq]; exact sq_add_sq_trig _ _ _) ?_ ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with y hy using abs_vC_sub_le hgc hy
  · filter_upwards [eventually_ge_atTop 2] with y hy using abs_vC₁_sub_le hc.le hgc hy
  · simpa using (tendsto_div_sub_one 1).const_mul (gL1 g)
  · simpa using (tendsto_div_sub_one (c + 2)).const_mul (gL1 g)

/-- **The energy of `Im V` tends to `c(A² + B²)`**. -/
theorem tendsto_energy_vS (hgc : ContinuousOn g (Icc (-1) 1)) (hc : 0 < c) (hχc : χ < c ^ 2) :
    Tendsto (energy (aP c χ) (vS c g) (uS c g)) atTop (𝓝 (c * (cA c g ^ 2 + cB c g ^ 2))) := by
  refine tendsto_energy_of_asymp (f₁ := shiftT g (hS₁ c))
    (α := fun y => cA c g * sin (c * y) + cB c g * cos (c * y))
    (β := fun y => cA c g * cos (c * y) - cB c g * sin (c * y))
    (ε₁ := fun y => gL1 g * (1 / (y - 1))) (ε₂ := fun y => gL1 g * ((c + 2) / (y - 1))) hc hχc
    (fun y => by rw [add_comm]; exact sq_add_sq_trig _ _ _) ?_ ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with y hy using abs_vS_sub_le hgc hy
  · filter_upwards [eventually_ge_atTop 2] with y hy using abs_vS₁_sub_le hc.le hgc hy
  · simpa using (tendsto_div_sub_one 1).const_mul (gL1 g)
  · simpa using (tendsto_div_sub_one (c + 2)).const_mul (gL1 g)

theorem continuousOn_of_hasDerivAt {g g₁ : ℝ → ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) :
    ContinuousOn g (Icc (-1) 1) := by
  rw [← uIcc_neg_one_one]; exact fun s hs => (hg s hs).continuousAt.continuousWithinAt

/-- The Wronskian `Re V·p(Im V)' − Im V·p(Re V)'` has derivative `0` on `(1, ∞)`. -/
theorem hasDerivAt_wronskian (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {y : ℝ} (hy : 1 < y) :
    HasDerivAt (fun y => vC c g y * uS c g y - vS c g y * uC c g y) 0 y := by
  obtain ⟨hC1, hC2⟩ := vC_system hg hg₁ hg₂c hang
  obtain ⟨hS1, hS2⟩ := vS_system hg hg₁ hg₂c hang
  have := ((hC1 y hy).mul (hS2 y hy)).sub ((hS1 y hy).mul (hC2 y hy))
  refine this.congr_deriv ?_
  have hp := (pP_pos hy).ne'
  field_simp
  ring

/-- **The Wronskian of the outgoing wave**: `Re V·p(Im V)' − Im V·p(Re V)' = c(A² + B²)` on `(1, ∞)`. -/
theorem wronskian_eq (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) {y : ℝ} (hy : 1 < y) :
    vC c g y * uS c g y - vS c g y * uC c g y = c * (cA c g ^ 2 + cB c g ^ 2) := by
  set W : ℝ → ℝ := fun y => vC c g y * uS c g y - vS c g y * uC c g y with hWdef
  have hgc := continuousOn_of_hasDerivAt hg
  have hW' : ∀ t, 1 < t → HasDerivAt W 0 t := fun t ht => hasDerivAt_wronskian hg hg₁ hg₂c hang ht
  have hconst : ∀ y₁ y₂, 1 < y₁ → y₁ < y₂ → W y₁ = W y₂ := by
    intro y₁ y₂ h1 h12
    obtain ⟨ξ, -, hd⟩ := exists_hasDerivAt_eq_slope W (fun _ => 0) h12
      (fun t ht => (hW' t (by linarith [ht.1])).continuousAt.continuousWithinAt)
      (fun t ht => hW' t (by linarith [ht.1]))
    have hne : y₂ - y₁ ≠ 0 := by linarith
    rw [eq_div_iff hne, zero_mul] at hd
    linarith
  set K := cA c g ^ 2 + cB c g ^ 2 with hK
  set P : ℝ → ℝ := fun t => cA c g * cos (c * t) - cB c g * sin (c * t)
  set Q : ℝ → ℝ := fun t => cA c g * sin (c * t) + cB c g * cos (c * t)
  have hPQ : ∀ t, P t ^ 2 + Q t ^ 2 = K := fun t => sq_add_sq_trig _ _ _
  have hPb : ∀ t, |P t| ≤ √K := fun t => Real.abs_le_sqrt (by nlinarith [hPQ t, sq_nonneg (Q t)])
  have hQb : ∀ t, |Q t| ≤ √K := fun t => Real.abs_le_sqrt (by nlinarith [hPQ t, sq_nonneg (P t)])
  have hcPb : ∀ t, |c * P t| ≤ c * √K := fun t => by
    rw [abs_mul, abs_of_pos hc]; exact mul_le_mul_of_nonneg_left (hPb t) hc.le
  have hcQb : ∀ t, |c * -Q t| ≤ c * √K := fun t => by
    rw [abs_mul, abs_of_pos hc, abs_neg]; exact mul_le_mul_of_nonneg_left (hQb t) hc.le
  have sq0 : ∀ {ε : ℝ → ℝ} {F G : ℝ → ℝ}, (∀ᶠ t in atTop, |F t - G t| ≤ ε t) → Tendsto ε atTop (𝓝 0) →
      Tendsto (fun t => F t - G t) atTop (𝓝 0) := fun h he =>
    squeeze_zero_norm' (h.mono fun t ht => by rwa [Real.norm_eq_abs]) he
  have e1 := sq0 (F := fun t => t * vC c g t) (G := P) (ε := fun y => gL1 g * (1 / (y - 1)))
    (by filter_upwards [eventually_gt_atTop 1] with t ht using abs_vC_sub_le hgc ht)
    (by simpa using (tendsto_div_sub_one 1).const_mul (gL1 g))
  have e2 := sq0 (F := fun t => t * vS c g t) (G := Q) (ε := fun y => gL1 g * (1 / (y - 1)))
    (by filter_upwards [eventually_gt_atTop 1] with t ht using abs_vS_sub_le hgc ht)
    (by simpa using (tendsto_div_sub_one 1).const_mul (gL1 g))
  have e3 := sq0 (F := fun t => t * shiftT g (hC₁ c) t) (G := fun t => c * -Q t)
    (ε := fun y => gL1 g * ((c + 2) / (y - 1)))
    (by filter_upwards [eventually_ge_atTop 2] with t ht using abs_vC₁_sub_le hc.le hgc ht)
    (by simpa using (tendsto_div_sub_one (c + 2)).const_mul (gL1 g))
  have e4 := sq0 (F := fun t => t * shiftT g (hS₁ c) t) (G := fun t => c * P t)
    (ε := fun y => gL1 g * ((c + 2) / (y - 1)))
    (by filter_upwards [eventually_ge_atTop 2] with t ht using abs_vS₁_sub_le hc.le hgc ht)
    (by simpa using (tendsto_div_sub_one (c + 2)).const_mul (gL1 g))
  have t1 := tendsto_mul_sub_mul e1 e4 hPb hcPb
  have t2 := tendsto_mul_sub_mul e2 e3 hQb hcQb
  have t3 := ((t1.sub t2).add (tendsto_const_nhds (x := c * K)))
  rw [sub_zero, zero_add] at t3
  have hlim : Tendsto W atTop (𝓝 (c * K)) := by
    have t4 := tendsto_pP_div_sq.mul t3
    rw [one_mul] at t4
    refine t4.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    have ht0 : t ≠ 0 := by positivity
    have hk : c * K = P t * (c * P t) - Q t * (c * -Q t) := by rw [← hPQ t]; ring
    simp only [hWdef, uS, uC]
    rw [hk]
    field_simp
    ring
  have hev : (fun _ => W y) =ᶠ[atTop] W := by
    filter_upwards [eventually_gt_atTop y] with t ht
    exact hconst y t hy ht
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hlim

end limits

/-! ### The envelope of the outgoing wave -/

/-- `Λ = (1 − w/2)⁻²`. -/
noncomputable def lamB (w : ℝ) : ℝ := 1 / (1 - w / 2) ^ 2

/-- `Λ̂ = Λ + √(Λ² − 1)`. -/
noncomputable def lamHat (w : ℝ) : ℝ := lamB w + √(lamB w ^ 2 - 1)

theorem lamB_nonneg (w : ℝ) : 0 ≤ lamB w := by unfold lamB; positivity

theorem lamHat_nonneg (w : ℝ) : 0 ≤ lamHat w := by
  unfold lamHat; have := lamB_nonneg w; positivity

/-- **The envelope inequality**: `x + z ≤ 2DΛ` and `xz ≥ D²` give `x ≤ D(Λ + √(Λ² − 1))`. -/
theorem env_alg {x z D Λ : ℝ} (hx : 0 ≤ x) (hsum : x + z ≤ 2 * D * Λ) (hprod : D ^ 2 ≤ x * z) (hD : 0 ≤ D) :
    x ≤ D * (Λ + √(Λ ^ 2 - 1)) := by
  have hz : z ≤ 2 * D * Λ - x := by linarith
  have h1 : (x - D * Λ) ^ 2 ≤ D ^ 2 * (Λ ^ 2 - 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hz hx]
  have h2 : x - D * Λ ≤ D * √(Λ ^ 2 - 1) := by
    calc x - D * Λ ≤ |x - D * Λ| := le_abs_self _
      _ = √((x - D * Λ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √(D ^ 2 * (Λ ^ 2 - 1)) := Real.sqrt_le_sqrt h1
      _ = D * √(Λ ^ 2 - 1) := by rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD]
  linarith

section envelope
variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- **The envelope of the outgoing wave**: `a(Re V² + Im V²) ≤ c(A² + B²)·Λ̂(w̄)`, `w̄ = 2y/(c(y² − 1)) < 2`. -/
theorem aP_mul_sq_add_sq_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) {y : ℝ} (hy : 1 < y) (hW : Cvs.Prolate.BandMassLaw.wUp c y < 2) :
    aP c χ y * (vC c g y ^ 2 + vS c g y ^ 2) ≤ c * (cA c g ^ 2 + cB c g ^ 2) * lamHat (Cvs.Prolate.BandMassLaw.wUp c y) := by
  have hgc := continuousOn_of_hasDerivAt hg
  set K := cA c g ^ 2 + cB c g ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨hC1, hC2⟩ := vC_system hg hg₁ hg₂c hang
  obtain ⟨hS1, hS2⟩ := vS_system hg hg₁ hg₂c hang
  have hEC := Cvs.Prolate.BandMassLaw.energy_le_of_ge hc hχ hχc hy le_rfl hC1 hC2 (tendsto_energy_vC hgc hc hχc) hW
  have hES := Cvs.Prolate.BandMassLaw.energy_le_of_ge hc hχ hχc hy le_rfl hS1 hS2 (tendsto_energy_vS hgc hc hχc) hW
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos hy hc2 hχc
  have hWr := wronskian_eq hg hg₁ hg₂c hang hc hy
  have hsum : aP c χ y * (vC c g y ^ 2 + vS c g y ^ 2) + (uC c g y ^ 2 + uS c g y ^ 2) / aP c χ y
      ≤ 2 * (c * K) * lamB (Cvs.Prolate.BandMassLaw.wUp c y) := by
    have e : aP c χ y * (vC c g y ^ 2 + vS c g y ^ 2) + (uC c g y ^ 2 + uS c g y ^ 2) / aP c χ y
        = energy (aP c χ) (vC c g) (uC c g) y + energy (aP c χ) (vS c g) (uS c g) y := by
      unfold energy; ring
    rw [e]
    have e2 : c * K / (1 - Cvs.Prolate.BandMassLaw.wUp c y / 2) ^ 2 = c * K * lamB (Cvs.Prolate.BandMassLaw.wUp c y) := by
      unfold lamB; ring
    linarith
  have hprod : (c * K) ^ 2
      ≤ aP c χ y * (vC c g y ^ 2 + vS c g y ^ 2) * ((uC c g y ^ 2 + uS c g y ^ 2) / aP c χ y) := by
    have e : aP c χ y * (vC c g y ^ 2 + vS c g y ^ 2) * ((uC c g y ^ 2 + uS c g y ^ 2) / aP c χ y)
        = (vC c g y * uS c g y - vS c g y * uC c g y) ^ 2 + (vC c g y * uC c g y + vS c g y * uS c g y) ^ 2 := by
      field_simp; ring
    rw [e, hWr]
    nlinarith [sq_nonneg (vC c g y * uC c g y + vS c g y * uS c g y)]
  have := env_alg (by positivity) hsum hprod (by positivity)
  unfold lamHat
  linarith

/-- **The Stieltjes envelope**: `Re V² + Im V² ≤ (A² + B²)·Λ̂(w̄)/(y² − 1)` on `y > 1` with `w̄ < 2`. -/
theorem sq_add_sq_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) {y : ℝ} (hy : 1 < y) (hW : Cvs.Prolate.BandMassLaw.wUp c y < 2) :
    vC c g y ^ 2 + vS c g y ^ 2 ≤ (cA c g ^ 2 + cB c g ^ 2) * lamHat (Cvs.Prolate.BandMassLaw.wUp c y) / pP y := by
  have h := aP_mul_sq_add_sq_le hg hg₁ hg₂c hang hc hχ hχc hy hW
  have hcp := Cvs.Prolate.BandMassLaw.mul_pP_le_aP hc hχc.le hy
  have hp := pP_pos hy
  have hL := lamHat_nonneg (Cvs.Prolate.BandMassLaw.wUp c y)
  rw [le_div_iff₀ hp]
  have h2 : c * pP y * (vC c g y ^ 2 + vS c g y ^ 2) ≤ aP c χ y * (vC c g y ^ 2 + vS c g y ^ 2) :=
    mul_le_mul_of_nonneg_right hcp (by positivity)
  have h3 : c * (pP y * (vC c g y ^ 2 + vS c g y ^ 2)) ≤ c * ((cA c g ^ 2 + cB c g ^ 2) * lamHat (Cvs.Prolate.BandMassLaw.wUp c y)) := by
    nlinarith
  have := le_of_mul_le_mul_left h3 hc
  linarith

end envelope

/-! ### Even rungs and the complex Stieltjes transform -/

section stieltjes
variable {g : ℝ → ℝ} {c : ℝ}

/-- For an even `g`, `B = ∫ g(s) sin(cs) ds = 0`. -/
theorem cB_eq_zero (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) : cB c g = 0 := by
  unfold cB
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) (fun s => g s * sin (c * s))
  simp only [neg_neg] at h
  have h2 : ∫ x in (-1 : ℝ)..1, g (-x) * sin (c * -x) = -∫ x in (-1 : ℝ)..1, g x * sin (c * x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_neg_one_one] at hx
    simp only [heven x hx, mul_neg, sin_neg]
  rw [h2] at h
  linarith

/-- `A = ∫ g(s) cos(cs) ds = ψ(1)`. -/
theorem cA_eq_psi : cA c g = Cvs.L2a.AngularProlateTailPositive.psi c g 1 := by
  unfold cA Cvs.L2a.AngularProlateTailPositive.psi kint; simp only [mul_one]

/-- The Stieltjes transform `F(y) = ∫ g(s) e^{ics}/(y + s) ds`, so that `V = e^{icy}F`. -/
noncomputable def fStil (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ s in (-1 : ℝ)..1, (g s : ℂ) * Complex.exp (((c * s : ℝ) : ℂ) * Complex.I) / ((y + s : ℝ) : ℂ)

/-- The mirrored transform `∫ g(s) e^{−ics}/(y + s) ds`. -/
noncomputable def fStilN (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ s in (-1 : ℝ)..1, (g s : ℂ) * Complex.exp (((-(c * s)) : ℝ) * Complex.I) / ((y + s : ℝ) : ℂ)

theorem ii_ofReal {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    IntervalIntegrable (fun s => (f s : ℂ)) volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_neg_one_one]
  exact Complex.continuous_ofReal.comp_continuousOn hf

theorem continuousOn_hC_shift {y : ℝ} (hy : 1 < y) : ContinuousOn (fun s => hC c (y + s)) (Icc (-1) 1) :=
  continuousOn_shift' (fun _ hz => hasDerivAt_hC hz) hy

theorem continuousOn_hS_shift {y : ℝ} (hy : 1 < y) : ContinuousOn (fun s => hS c (y + s)) (Icc (-1) 1) :=
  continuousOn_shift' (fun _ hz => hasDerivAt_hS hz) hy

/-- **`V = e^{icy}F = Re V + i Im V`**. -/
theorem exp_mul_fStil (hgc : ContinuousOn g (Icc (-1) 1)) {y : ℝ} (hy : 1 < y) :
    Complex.exp (((c * y : ℝ) : ℂ) * Complex.I) * fStil c g y = (vC c g y : ℂ) + (vS c g y : ℂ) * Complex.I := by
  unfold fStil vC vS shiftT kint
  have i1 : IntervalIntegrable (fun x => ((g x * hC c (y + x) : ℝ) : ℂ)) volume (-1) 1 :=
    ii_ofReal (hgc.mul (continuousOn_hC_shift hy))
  have i2 : IntervalIntegrable (fun x => ((g x * hS c (y + x) : ℝ) : ℂ) * Complex.I) volume (-1) 1 :=
    (ii_ofReal (hgc.mul (continuousOn_hS_shift hy))).mul_const _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_ofReal,
    ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const]
  beta_reduce
  rw [← intervalIntegral.integral_add i1 i2]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_neg_one_one] at hs
  have hz : ((y + s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show y + s ≠ 0 by linarith [hs.1])
  have he : ((c * y : ℝ) : ℂ) * Complex.I + ((c * s : ℝ) : ℂ) * Complex.I = ((c * (y + s) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hexp : Complex.exp (((c * y : ℝ) : ℂ) * Complex.I) * Complex.exp (((c * s : ℝ) : ℂ) * Complex.I)
      = ((cos (c * (y + s)) : ℝ) : ℂ) + ((sin (c * (y + s)) : ℝ) : ℂ) * Complex.I := by
    rw [← Complex.exp_add, he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  unfold hC hS
  calc Complex.exp (((c * y : ℝ) : ℂ) * Complex.I)
        * ((g s : ℂ) * Complex.exp (((c * s : ℝ) : ℂ) * Complex.I) / ((y + s : ℝ) : ℂ))
      = (g s : ℂ) * (Complex.exp (((c * y : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((c * s : ℝ) : ℂ) * Complex.I)) / ((y + s : ℝ) : ℂ) := by ring
    _ = _ := by
      rw [hexp]; push_cast; field_simp

/-- **The mirrored wave**: `e^{−icy}∫ g e^{−ics}/(y + s) = Re V − i Im V`. -/
theorem exp_mul_fStilN (hgc : ContinuousOn g (Icc (-1) 1)) {y : ℝ} (hy : 1 < y) :
    Complex.exp (((-(c * y)) : ℝ) * Complex.I) * fStilN c g y
      = (vC c g y : ℂ) + ((-vS c g y : ℝ) : ℂ) * Complex.I := by
  unfold fStilN vC vS shiftT kint
  have i1 : IntervalIntegrable (fun x => ((g x * hC c (y + x) : ℝ) : ℂ)) volume (-1) 1 :=
    ii_ofReal (hgc.mul (continuousOn_hC_shift hy))
  have i2 : IntervalIntegrable (fun x => ((-(g x * hS c (y + x)) : ℝ) : ℂ) * Complex.I) volume (-1) 1 :=
    (ii_ofReal (hgc.mul (continuousOn_hS_shift hy)).neg).mul_const _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_ofReal,
    ← intervalIntegral.integral_neg, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const]
  beta_reduce
  rw [← intervalIntegral.integral_add i1 i2]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_neg_one_one] at hs
  have hz : ((y + s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show y + s ≠ 0 by linarith [hs.1])
  have he : (((-(c * y)) : ℝ) : ℂ) * Complex.I + (((-(c * s)) : ℝ) : ℂ) * Complex.I
      = (((-(c * (y + s))) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hexp : Complex.exp ((((-(c * y)) : ℝ) : ℂ) * Complex.I) * Complex.exp ((((-(c * s)) : ℝ) : ℂ) * Complex.I)
      = ((cos (c * (y + s)) : ℝ) : ℂ) - ((sin (c * (y + s)) : ℝ) : ℂ) * Complex.I := by
    rw [← Complex.exp_add, he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast; ring
  unfold hC hS
  calc Complex.exp ((((-(c * y)) : ℝ) : ℂ) * Complex.I)
        * ((g s : ℂ) * Complex.exp ((((-(c * s)) : ℝ) : ℂ) * Complex.I) / ((y + s : ℝ) : ℂ))
      = (g s : ℂ) * (Complex.exp ((((-(c * y)) : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((((-(c * s)) : ℝ) : ℂ) * Complex.I)) / ((y + s : ℝ) : ℂ) := by ring
    _ = _ := by
      rw [hexp]; push_cast; field_simp; ring

/-- **`|F(y)|² = Re V² + Im V²`** for `y > 1`. -/
theorem norm_fStil_sq (hgc : ContinuousOn g (Icc (-1) 1)) {y : ℝ} (hy : 1 < y) :
    ‖fStil c g y‖ ^ 2 = vC c g y ^ 2 + vS c g y ^ 2 := by
  have h := congrArg (‖·‖) (exp_mul_fStil (c := c) hgc hy)
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_add_mul_I] at h
  rw [h, Real.sq_sqrt (by positivity)]

/-- `|∫ g e^{−ics}/(y + s)|² = Re V² + Im V²` for `y > 1`. -/
theorem norm_fStilN_sq (hgc : ContinuousOn g (Icc (-1) 1)) {y : ℝ} (hy : 1 < y) :
    ‖fStilN c g y‖ ^ 2 = vC c g y ^ 2 + vS c g y ^ 2 := by
  have h := congrArg (‖·‖) (exp_mul_fStilN (c := c) hgc hy)
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_add_mul_I, neg_sq] at h
  rw [h, Real.sq_sqrt (by positivity)]

/-- The `si` part of the cut multiplier, `ν^si(ξ) = (1/m) ∫ g(s) μ_si(c, s/m, m, ξ) ds`. -/
noncomputable def nuSi (c : ℝ) (g : ℝ → ℝ) (m ξ : ℝ) : ℂ :=
  ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (g s : ℂ) * Cvs.L2a.CutKernelSimplified.muSi c (s / m) m ξ

/-- `ν^si(ξ) = −i ∫ g(s) e^{ics}/(cs + mξ) ds`. -/
theorem nuSi_eq {m : ℝ} (hm : m ≠ 0) (ξ : ℝ) :
    nuSi c g m ξ = -Complex.I * ∫ s in (-1 : ℝ)..1,
      (g s : ℂ) * Complex.exp (((c * s : ℝ) : ℂ) * Complex.I) / ((c * s + m * ξ : ℝ) : ℂ) := by
  unfold nuSi
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  unfold Cvs.L2a.CutKernelSimplified.muSi Cvs.L2a.FarIntegrationByParts.eF
  have h1 : c * (s / m) * m = c * s := by field_simp
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have h2 : ((c * s + m * ξ : ℝ) : ℂ) = (m : ℂ) * ((c * (s / m) + ξ : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [h1, h2, Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- **The `si` multiplier is the Stieltjes transform**: `|ν^si(ξ)|² = (Re V² + Im V²)(m|ξ|/c)/c²` for
`m|ξ| > c`, `g` even. -/
theorem norm_nuSi_sq (hgc : ContinuousOn g (Icc (-1) 1)) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hc : 0 < c) {m : ℝ} (hm : 0 < m) {ξ : ℝ} (hξ : c < m * |ξ|) :
    ‖nuSi c g m ξ‖ ^ 2 = (vC c g (m * |ξ| / c) ^ 2 + vS c g (m * |ξ| / c) ^ 2) / c ^ 2 := by
  have hY : 1 < m * |ξ| / c := by rw [lt_div_iff₀ hc]; linarith
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [nuSi_eq hm.ne']
  rcases le_or_gt 0 ξ with h0 | h0
  · -- `ξ ≥ 0`: `ν^si = −(i/c) F(mξ/c)`
    have hξa : |ξ| = ξ := abs_of_nonneg h0
    rw [hξa] at hY ⊢
    have e : (∫ s in (-1 : ℝ)..1, (g s : ℂ) * Complex.exp (((c * s : ℝ) : ℂ) * Complex.I)
        / ((c * s + m * ξ : ℝ) : ℂ)) = (1 / c : ℂ) * fStil c g (m * ξ / c) := by
      unfold fStil
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      have : ((c * s + m * ξ : ℝ) : ℂ) = (c : ℂ) * ((m * ξ / c + s : ℝ) : ℂ) := by
        push_cast; field_simp; ring
      rw [this]
      field_simp
    rw [e, norm_mul, norm_mul, mul_pow, mul_pow, norm_fStil_sq hgc hY]
    simp only [norm_neg, Complex.norm_I, one_pow, one_mul, norm_div, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc]
    field_simp
  · -- `ξ < 0`: `ν^si = (i/c) ∫ g e^{−ics}/(m|ξ|/c + s)` by `s ↦ −s`
    have hξa : |ξ| = -ξ := abs_of_neg h0
    rw [hξa] at hY ⊢
    have e : (∫ s in (-1 : ℝ)..1, (g s : ℂ) * Complex.exp (((c * s : ℝ) : ℂ) * Complex.I)
        / ((c * s + m * ξ : ℝ) : ℂ)) = (-1 / c : ℂ) * fStilN c g (m * -ξ / c) := by
      have hn := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
        (fun s => (g s : ℂ) * Complex.exp (((c * s : ℝ) : ℂ) * Complex.I) / ((c * s + m * ξ : ℝ) : ℂ))
      simp only [neg_neg] at hn
      rw [← hn]
      unfold fStilN
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_neg_one_one] at hs
      have : ((c * -s + m * ξ : ℝ) : ℂ) = -(c : ℂ) * ((m * -ξ / c + s : ℝ) : ℂ) := by
        push_cast; field_simp; ring
      rw [this, heven s hs, show c * -s = -(c * s) by ring]
      field_simp
    rw [e, norm_mul, norm_mul, mul_pow, mul_pow, norm_fStilN_sq hgc hY]
    simp only [norm_neg, Complex.norm_I, one_pow, one_mul, norm_div, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc]
    field_simp

end stieltjes

/-! ### The bottom main term in closed form -/

/-- `L_m = ∫_1^{Y(m)} dη/(m²η² − 1)`, `Y(m) = m/√(m² − 1)`. -/
noncomputable def lM (m : ℝ) : ℝ := ∫ η in (1 : ℝ)..Cvs.L2a.OrbitGapIntegerM.Ymax m, 1 / (m ^ 2 * η ^ 2 - 1)

/-- The two-sided band `{ξ : c ≤ |ξ| ≤ cY}`. -/
def bandB (c Y : ℝ) : Set ℝ := Icc (-(c * Y)) (-c) ∪ Icc c (c * Y)

section mainterm

theorem sub_one_le_sq_mul_sq {m η : ℝ} (hη : 1 ≤ η) : m ^ 2 - 1 ≤ m ^ 2 * η ^ 2 - 1 := by
  have h1 : 1 ≤ η ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg m)]

theorem sq_sub_one_pos {m : ℝ} (hm : 1 < m) : 0 < m ^ 2 - 1 := by nlinarith

theorem one_le_Ymax {m : ℝ} (hm : 1 < m) : 1 ≤ Cvs.L2a.OrbitGapIntegerM.Ymax m := by
  unfold Cvs.L2a.OrbitGapIntegerM.Ymax
  have hp : 0 < m ^ 2 - 1 := by nlinarith
  rw [le_div_iff₀ (Real.sqrt_pos.2 hp), one_mul]
  calc √(m ^ 2 - 1) ≤ √(m ^ 2) := Real.sqrt_le_sqrt (by linarith)
    _ = m := Real.sqrt_sq (by linarith)

/-- `Y(m) − 1 ≤ 1/(2(m² − 1))`. -/
theorem Ymax_sub_one_le {m : ℝ} (hm : 1 < m) : Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 ≤ 1 / (2 * (m ^ 2 - 1)) := by
  unfold Cvs.L2a.OrbitGapIntegerM.Ymax
  have hp : 0 < m ^ 2 - 1 := by nlinarith
  set r := √(m ^ 2 - 1) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hp
  have hr2 : r ^ 2 = m ^ 2 - 1 := Real.sq_sqrt hp.le
  rw [← hr2, div_sub_one hr0.ne', div_le_div_iff₀ hr0 (by positivity)]
  nlinarith [sq_nonneg (m - r)]

/-- **The antiderivative**: `d/dη [log((mη − 1)/(mη + 1))/(2m)] = 1/(m²η² − 1)` for `mη > 1`. -/
theorem hasDerivAt_logRatio {m η : ℝ} (hm : 0 < m) (hη : 1 < m * η) :
    HasDerivAt (fun η => Real.log ((m * η - 1) / (m * η + 1)) / (2 * m)) (1 / (m ^ 2 * η ^ 2 - 1)) η := by
  have h1 : HasDerivAt (fun η => m * η - 1) m η := by simpa using ((hasDerivAt_id η).const_mul m).sub_const 1
  have h2 : HasDerivAt (fun η => m * η + 1) m η := by simpa using ((hasDerivAt_id η).const_mul m).add_const 1
  have hq := h1.div h2 (by linarith)
  have hne : (m * η - 1) / (m * η + 1) ≠ 0 := div_ne_zero (by linarith) (by linarith)
  have := (hq.log hne).div_const (2 * m)
  refine this.congr_deriv ?_
  have a1 : m * η - 1 ≠ 0 := by linarith
  have a2 : m * η + 1 ≠ 0 := by linarith
  have a3 : m ^ 2 * η ^ 2 - 1 ≠ 0 := by
    have : m ^ 2 * η ^ 2 - 1 = (m * η - 1) * (m * η + 1) := by ring
    rw [this]; exact mul_ne_zero a1 a2
  simp only [Pi.div_apply]
  field_simp
  ring

/-- **`L_m` in closed form**: `L_m = [log((mY − 1)/(mY + 1)) − log((m − 1)/(m + 1))]/(2m)`. -/
theorem lM_eq {m : ℝ} (hm : 1 < m) :
    lM m = (Real.log ((m * Cvs.L2a.OrbitGapIntegerM.Ymax m - 1) / (m * Cvs.L2a.OrbitGapIntegerM.Ymax m + 1))
      - Real.log ((m - 1) / (m + 1))) / (2 * m) := by
  have hY := one_le_Ymax hm
  have hm0 : 0 < m := by linarith
  unfold lM
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun η => Real.log ((m * η - 1) / (m * η + 1)) / (2 * m))]
  · simp only [mul_one]; ring
  · intro η hη
    rw [uIcc_of_le hY] at hη
    exact hasDerivAt_logRatio hm0 (by nlinarith [hη.1])
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hY]
    refine ContinuousOn.div₀ continuousOn_const (by fun_prop) fun η hη => ?_
    have := sub_one_le_sq_mul_sq (m := m) hη.1
    have := sq_sub_one_pos hm
    linarith

theorem lM_nonneg {m : ℝ} (hm : 1 < m) : 0 ≤ lM m := by
  unfold lM
  refine intervalIntegral.integral_nonneg (one_le_Ymax hm) fun η hη => ?_
  have := sub_one_le_sq_mul_sq (m := m) hη.1
  have := sq_sub_one_pos hm
  have : 0 < m ^ 2 * η ^ 2 - 1 := by linarith
  positivity

/-- **`L_m ≤ 1/(2(m² − 1)²)`**. -/
theorem lM_le {m : ℝ} (hm : 1 < m) : lM m ≤ 1 / (2 * (m ^ 2 - 1) ^ 2) := by
  have hY := one_le_Ymax hm
  have hp : 0 < m ^ 2 - 1 := by nlinarith
  have h1 : lM m ≤ ∫ η in (1 : ℝ)..Cvs.L2a.OrbitGapIntegerM.Ymax m, 1 / (m ^ 2 - 1) := by
    unfold lM
    refine intervalIntegral.integral_mono_on hY ?_ (by simp) fun η hη => ?_
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hY]
      refine ContinuousOn.div₀ continuousOn_const (by fun_prop) fun η hη => ?_
      have := sub_one_le_sq_mul_sq (m := m) hη.1
      linarith
    · exact one_div_le_one_div_of_le hp (sub_one_le_sq_mul_sq (m := m) hη.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  have h2 := Ymax_sub_one_le hm
  calc lM m ≤ (Cvs.L2a.OrbitGapIntegerM.Ymax m - 1) * (1 / (m ^ 2 - 1)) := h1
    _ ≤ 1 / (2 * (m ^ 2 - 1)) * (1 / (m ^ 2 - 1)) := by gcongr
    _ = 1 / (2 * (m ^ 2 - 1) ^ 2) := by field_simp

/-- **The band integral of an even function**: `∫_{c ≤ |ξ| ≤ cY} f = 2∫_c^{cY} f`. -/
theorem integral_bandB {f : ℝ → ℝ} {c Y : ℝ} (hc : 0 < c) (hY : 1 ≤ Y) (hf : ContinuousOn f (Icc c (c * Y)))
    (heven : ∀ ξ, f (-ξ) = f ξ) : ∫ ξ in bandB c Y, f ξ = 2 * ∫ ξ in c..c * Y, f ξ := by
  have hcY : c ≤ c * Y := by nlinarith
  have hf' : ContinuousOn f (Icc (-(c * Y)) (-c)) := by
    have h := hf.comp (continuousOn_neg (s := Icc (-(c * Y)) (-c)))
      (fun ξ (hξ : ξ ∈ Icc (-(c * Y)) (-c)) => (⟨by linarith [hξ.2], by linarith [hξ.1]⟩ : -ξ ∈ Icc c (c * Y)))
    refine h.congr fun ξ _ => ?_
    simp [heven]
  have hdis : Disjoint (Icc (-(c * Y)) (-c)) (Icc c (c * Y)) := by
    rw [Set.disjoint_left]; intro ξ h1 h2; linarith [h1.2, h2.1]
  unfold bandB
  rw [setIntegral_union hdis measurableSet_Icc (hf'.integrableOn_compact isCompact_Icc)
    (hf.integrableOn_compact isCompact_Icc), integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le hcY]
  have hn := intervalIntegral.integral_comp_neg (a := c) (b := c * Y) f
  simp only [heven] at hn
  rw [← hn]
  ring

theorem lamB_mono {w w' : ℝ} (hww : w ≤ w') (hw' : w' < 2) : lamB w ≤ lamB w' := by
  unfold lamB
  have h1 : 0 < 1 - w' / 2 := by linarith
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h1.le (by linarith) 2)

theorem lamHat_mono {w w' : ℝ} (hww : w ≤ w') (hw' : w' < 2) : lamHat w ≤ lamHat w' := by
  have h := lamB_mono hww hw'
  have h0 := lamB_nonneg w
  unfold lamHat
  have : lamB w ^ 2 - 1 ≤ lamB w' ^ 2 - 1 := by nlinarith
  linarith [Real.sqrt_le_sqrt this]

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- **The even Stieltjes envelope**: `Re V² + Im V² ≤ ψ(1)²Λ̂(w̄)/(y² − 1)` for an even rung. -/
theorem sq_add_sq_le_even (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) {y : ℝ} (hy : 1 < y) (hW : Cvs.Prolate.BandMassLaw.wUp c y < 2) :
    vC c g y ^ 2 + vS c g y ^ 2
      ≤ Cvs.L2a.AngularProlateTailPositive.psi c g 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c y) / pP y := by
  have h := sq_add_sq_le hg hg₁ hg₂c hang hc hχ hχc hy hW
  rwa [cB_eq_zero heven, cA_eq_psi, zero_pow two_ne_zero, add_zero] at h

theorem mem_bandB_abs {c Y ξ : ℝ} (hc : 0 < c) (hξ : ξ ∈ bandB c Y) : c ≤ |ξ| ∧ |ξ| ≤ c * Y := by
  rcases hξ with h | h
  · rw [abs_of_neg (by linarith [h.2])]; constructor <;> linarith [h.1, h.2]
  · rw [abs_of_pos (by linarith [h.1])]; exact h

theorem den_ge {c m ξ : ℝ} (hc : 0 < c) (hm : 2 ≤ m) (hξ : c ≤ |ξ|) : 3 * c ^ 2 ≤ m ^ 2 * ξ ^ 2 - c ^ 2 := by
  have h1 : c ^ 2 ≤ ξ ^ 2 := by rw [← sq_abs ξ]; exact pow_le_pow_left₀ hc.le hξ 2
  have h2 : 4 ≤ m ^ 2 := by nlinarith
  nlinarith

/-- **The `si` multiplier on the band, pointwise**: `|ν^si(ξ)|² ≤ ψ(1)²Λ̂(w̄(m))/(m²ξ² − c²)` for `|ξ| ≥ c`. -/
theorem norm_nuSi_sq_le_band (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) {m : ℝ} (hm : 2 ≤ m) (hW : Cvs.Prolate.BandMassLaw.wUp c m < 2)
    {ξ : ℝ} (hξc : c ≤ |ξ|) :
    ‖nuSi c g m ξ‖ ^ 2
      ≤ Cvs.L2a.AngularProlateTailPositive.psi c g 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c m) / (m ^ 2 * ξ ^ 2 - c ^ 2) := by
  have hgc := continuousOn_of_hasDerivAt hg
  have hmξ : c < m * |ξ| := by nlinarith
  set Y' := m * |ξ| / c with hY'
  have hY'1 : 1 < Y' := by rw [hY', lt_div_iff₀ hc]; linarith
  have hmY' : m ≤ Y' := by rw [hY', le_div_iff₀ hc]; nlinarith
  have hwle : Cvs.Prolate.BandMassLaw.wUp c Y' ≤ Cvs.Prolate.BandMassLaw.wUp c m := Cvs.Prolate.BandMassLaw.wUp_le_wUp hc (by linarith) hmY'
  have hW' : Cvs.Prolate.BandMassLaw.wUp c Y' < 2 := lt_of_le_of_lt hwle hW
  rw [norm_nuSi_sq hgc heven hc (by linarith) hmξ]
  have he := sq_add_sq_le_even hg hg₁ hg₂c hang heven hc hχ hχc hY'1 hW'
  have hmono := lamHat_mono hwle hW
  have hpY : pP Y' = (m ^ 2 * ξ ^ 2 - c ^ 2) / c ^ 2 := by
    rw [hY']; unfold pP; rw [div_pow, mul_pow, sq_abs]; field_simp
  have hd3 := den_ge hc hm hξc
  have hc2 : 0 < c ^ 2 := by positivity
  have hpos : 0 < m ^ 2 * ξ ^ 2 - c ^ 2 := by linarith
  rw [hpY] at he
  rw [div_le_div_iff₀ hc2 hpos]
  have h1 : (vC c g Y' ^ 2 + vS c g Y' ^ 2) * (m ^ 2 * ξ ^ 2 - c ^ 2)
      ≤ Cvs.L2a.AngularProlateTailPositive.psi c g 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c Y') * c ^ 2 := by
    rwa [div_div_eq_mul_div, le_div_iff₀ hpos] at he
  have h2 : Cvs.L2a.AngularProlateTailPositive.psi c g 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c Y')
      ≤ Cvs.L2a.AngularProlateTailPositive.psi c g 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c m) :=
    mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
  nlinarith

/-- **The band integral of `D/(m²ξ² − c²)`** is `(2/c)·D·L_m`. -/
theorem integral_band_inv {c m : ℝ} (D : ℝ) (hc : 0 < c) (hm : 2 ≤ m) :
    IntegrableOn (fun ξ => D / (m ^ 2 * ξ ^ 2 - c ^ 2)) (bandB c (Cvs.L2a.OrbitGapIntegerM.Ymax m))
      ∧ ∫ ξ in bandB c (Cvs.L2a.OrbitGapIntegerM.Ymax m), D / (m ^ 2 * ξ ^ 2 - c ^ 2) = 2 / c * D * lM m := by
  set Y := Cvs.L2a.OrbitGapIntegerM.Ymax m with hYdef
  have hY : 1 ≤ Y := one_le_Ymax (by linarith)
  set H : ℝ → ℝ := fun ξ => D / (m ^ 2 * ξ ^ 2 - c ^ 2) with hH
  have hc2 : 0 < c ^ 2 := by positivity
  have hHc : ContinuousOn H (Icc c (c * Y)) := by
    refine ContinuousOn.div₀ continuousOn_const (by fun_prop) fun ξ hξ => ?_
    have := den_ge (ξ := ξ) hc hm (by rw [abs_of_pos (by linarith [hξ.1])]; exact hξ.1)
    linarith
  constructor
  · refine ContinuousOn.integrableOn_compact (isCompact_Icc.union isCompact_Icc) ?_
    refine ContinuousOn.div₀ continuousOn_const (by fun_prop) fun ξ hξ => ?_
    have := den_ge hc hm (mem_bandB_abs hc hξ).1
    linarith
  have hev : ∀ ξ, H (-ξ) = H ξ := fun ξ => by simp only [hH, neg_sq]
  rw [integral_bandB hc hY hHc hev]
  have hsub : ∫ ξ in c..c * Y, H ξ = c * ∫ η in (1 : ℝ)..Y, H (c * η) := by
    have := intervalIntegral.integral_comp_mul_left (a := 1) (b := Y) H hc.ne'
    rw [this, mul_one, smul_eq_mul]; field_simp
  have hcη : ∫ η in (1 : ℝ)..Y, H (c * η) = D / c ^ 2 * lM m := by
    unfold lM
    rw [← hYdef, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun η hη => ?_
    rw [uIcc_of_le hY] at hη
    have := sub_one_le_sq_mul_sq (m := m) hη.1
    have := sq_sub_one_pos (by linarith : (1 : ℝ) < m)
    have h4 : 0 < m ^ 2 * η ^ 2 - 1 := by linarith
    simp only [hH]
    field_simp
  rw [hsub, hcη]
  field_simp

/-- The band integral of a constant: `∫_{c ≤ |ξ| ≤ cY} k = 2c(Y − 1)k`. -/
theorem integral_band_const {c Y : ℝ} (k : ℝ) (hc : 0 < c) (hY : 1 ≤ Y) :
    IntegrableOn (fun _ => k) (bandB c Y) ∧ ∫ _ in bandB c Y, k = 2 * c * (Y - 1) * k := by
  constructor
  · exact continuousOn_const.integrableOn_compact (isCompact_Icc.union isCompact_Icc)
  · rw [integral_bandB hc hY continuousOn_const (fun _ => rfl), intervalIntegral.integral_const, smul_eq_mul]
    ring

end mainterm

/-! ### The constant `C_E = (1/π) Σ_{m ≥ 2} L_m` -/

section constant

/-- `1/((n + 2)² − 1)²`. -/
noncomputable def sqInv (n : ℕ) : ℝ := 1 / (((n : ℝ) + 2) ^ 2 - 1) ^ 2

theorem hasSum_inv_sq_one : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
  exact h

theorem hasSum_inv_sq_three : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 3) ^ 2) (π ^ 2 / 6 - 5 / 4) := by
  have h := (hasSum_nat_add_iff' 3).mpr hasSum_zeta_two
  have e : ∑ i ∈ Finset.range 3, (1 : ℝ) / (i : ℝ) ^ 2 = 5 / 4 := by
    simp [Finset.sum_range_succ]; norm_num
  rw [e] at h
  simpa using h

/-- `Σ_{n ≥ 0} (1/(n + 1) − 1/(n + 3)) = 3/2`. -/
theorem hasSum_tele : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 3)) (3 / 2) := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 3) := fun n => by
    have : 1 / ((n : ℝ) + 3) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hps : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 3))
      = 3 / 2 - 1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2) := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring
  simp_rw [hps]
  have h1 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 2)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by positivity) (fun N => ?_) h1
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have := ((tendsto_const_nhds (x := (3 / 2 : ℝ))).sub h1).sub h2
  simpa using this

/-- **`Σ_{m ≥ 2} 1/(m² − 1)² = π²/12 − 11/16`**. -/
theorem hasSum_sqInv : HasSum sqInv (π ^ 2 / 12 - 11 / 16) := by
  have h := ((hasSum_inv_sq_one.add hasSum_inv_sq_three).mul_left (1 / 4)).sub (hasSum_tele.mul_left (1 / 4))
  have hfun : sqInv = fun n : ℕ => 1 / 4 * (1 / ((n : ℝ) + 1) ^ 2 + 1 / ((n : ℝ) + 3) ^ 2)
      - 1 / 4 * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 3)) := by
    funext n
    unfold sqInv
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : ((n : ℝ) + 2) ^ 2 - 1 = ((n : ℝ) + 1) * ((n : ℝ) + 3) := by ring
    rw [h3]
    field_simp
    ring
  rw [hfun, show π ^ 2 / 12 - 11 / 16 = 1 / 4 * (π ^ 2 / 6 + (π ^ 2 / 6 - 5 / 4)) - 1 / 4 * (3 / 2) by ring]
  exact h

theorem lM_le_sqInv (n : ℕ) : lM ((n : ℝ) + 2) ≤ 1 / 2 * sqInv n := by
  have h := lM_le (m := (n : ℝ) + 2) (by linarith [n.cast_nonneg (α := ℝ)])
  unfold sqInv
  rwa [one_div_mul_one_div]

theorem lM_nonneg' (n : ℕ) : 0 ≤ lM ((n : ℝ) + 2) := lM_nonneg (by linarith [n.cast_nonneg (α := ℝ)])

theorem summable_lM : Summable fun n : ℕ => lM ((n : ℝ) + 2) :=
  Summable.of_nonneg_of_le lM_nonneg' lM_le_sqInv (hasSum_sqInv.summable.mul_left (1 / 2))

/-- **`C_E = (1/π) Σ_{m ≥ 2} L_m`**, the E-coupling's main constant. -/
noncomputable def cE : ℝ := (∑' n : ℕ, lM ((n : ℝ) + 2)) / π

theorem cE_nonneg : 0 ≤ cE := div_nonneg (tsum_nonneg lM_nonneg') pi_pos.le

/-- **Every finite sum of cuts is below `πC_E`**, uniformly in the cut set. -/
theorem sum_lM_le (S : Finset ℕ) : ∑ n ∈ S, lM ((n : ℝ) + 2) ≤ π * cE := by
  rw [cE, mul_div_cancel₀ _ pi_ne_zero]
  exact summable_lM.sum_le_tsum S (fun i _ => lM_nonneg' i)

/-- **`C_E` in closed form, bounded**: `πC_E ≤ L₂ + L₃ + (π²/12 − 11/16 − 1/9 − 1/64)/2`. -/
theorem pi_mul_cE_le : π * cE ≤ lM 2 + lM 3 + (π ^ 2 / 12 - 11 / 16 - 1 / 9 - 1 / 64) / 2 := by
  rw [cE, mul_div_cancel₀ _ pi_ne_zero, ← summable_lM.sum_add_tsum_nat_add 2]
  have hs : HasSum (fun n : ℕ => sqInv (n + 2)) (π ^ 2 / 12 - 11 / 16 - 1 / 9 - 1 / 64) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_sqInv
    have e : ∑ i ∈ Finset.range 2, sqInv i = 1 / 9 + 1 / 64 := by
      simp [Finset.sum_range_succ, sqInv]; norm_num
    rw [e] at h
    rw [show π ^ 2 / 12 - 11 / 16 - 1 / 9 - 1 / 64 = π ^ 2 / 12 - 11 / 16 - (1 / 9 + 1 / 64) by ring]
    exact h
  have hle : ∑' n : ℕ, lM (((n + 2 : ℕ) : ℝ) + 2) ≤ ∑' n : ℕ, 1 / 2 * sqInv (n + 2) :=
    ((summable_nat_add_iff 2).2 summable_lM).tsum_le_tsum (fun n => lM_le_sqInv (n + 2))
      (hs.summable.mul_left _)
  rw [tsum_mul_left, hs.tsum_eq] at hle
  have e2 : ∑ i ∈ Finset.range 2, lM ((i : ℝ) + 2) = lM 2 + lM 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  rw [e2]
  linarith

/-- `L₂ = log(3(19 − 8√3)/13)/4`. -/
theorem lM_two : lM 2 = Real.log (3 * (19 - 8 * √3) / 13) / 4 := by
  rw [lM_eq (by norm_num)]
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hY : Cvs.L2a.OrbitGapIntegerM.Ymax 2 = 2 / √3 := by
    unfold Cvs.L2a.OrbitGapIntegerM.Ymax; norm_num
  have hlt : √3 < 2 := by nlinarith
  have e : (2 * (2 / √3) - 1) / (2 * (2 / √3) + 1) = (19 - 8 * √3) / 13 := by
    field_simp; nlinarith
  have hpos : 0 < (19 - 8 * √3) / 13 := by
    have : √3 < 19 / 8 := by nlinarith
    apply div_pos <;> linarith
  rw [hY, e, show ((2 : ℝ) - 1) / (2 + 1) = 1 / 3 by norm_num, ← Real.log_div hpos.ne' (by norm_num)]
  congr 1
  · congr 1; field_simp
  · norm_num

/-- `L₃ = log(2(89 − 36√2)/73)/6`. -/
theorem lM_three : lM 3 = Real.log (2 * (89 - 36 * √2) / 73) / 6 := by
  rw [lM_eq (by norm_num)]
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h8 : √8 = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hY : Cvs.L2a.OrbitGapIntegerM.Ymax 3 = 3 / (2 * √2) := by
    unfold Cvs.L2a.OrbitGapIntegerM.Ymax; norm_num; exact h8 ▸ rfl
  have hlt : √2 < 3 / 2 := by nlinarith
  have e : (3 * (3 / (2 * √2)) - 1) / (3 * (3 / (2 * √2)) + 1) = (89 - 36 * √2) / 73 := by
    field_simp; nlinarith
  have hpos : 0 < (89 - 36 * √2) / 73 := by apply div_pos <;> nlinarith
  rw [hY, e, show ((3 : ℝ) - 1) / (3 + 1) = 1 / 2 by norm_num, ← Real.log_div hpos.ne' (by norm_num)]
  congr 1
  · congr 1; field_simp
  · norm_num

end constant

/-! ### Certified rational bounds on `C_E` -/

section certified

/-- **A log upper bound from the series**: `log x ≤ Σ_{i<n} U^{i+1}/(i+1) + U^{n+1}/(1 − U)` for `1 − 1/x ≤ U < 1`. -/
theorem log_le_series {x U : ℝ} (hx : 1 ≤ x) (hU : 1 - 1 / x ≤ U) (hU1 : U < 1) (n : ℕ) :
    Real.log x ≤ ∑ i ∈ Finset.range n, U ^ (i + 1) / (i + 1) + U ^ (n + 1) / (1 - U) := by
  set u := 1 - 1 / x with hu
  have hx0 : 0 < x := by linarith
  have hu0 : 0 ≤ u := by rw [hu, sub_nonneg, div_le_one hx0]; exact hx
  have hu1 : u < 1 := by
    have : 0 < 1 / x := by positivity
    linarith
  have habs : |u| < 1 := by rw [abs_of_nonneg hu0]; exact hu1
  have h := Real.abs_log_sub_add_sum_range_le habs n
  rw [abs_of_nonneg hu0] at h
  have hlog : Real.log x = -Real.log (1 - u) := by
    rw [hu, sub_sub_cancel, one_div, Real.log_inv, neg_neg]
  have h1 : Real.log x ≤ ∑ i ∈ Finset.range n, u ^ (i + 1) / (i + 1) + u ^ (n + 1) / (1 - u) := by
    rw [hlog]; linarith [(abs_le.mp h).1]
  have hs : ∑ i ∈ Finset.range n, u ^ (i + 1) / (i + 1) ≤ ∑ i ∈ Finset.range n, U ^ (i + 1) / (i + 1) :=
    Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (pow_le_pow_left₀ hu0 hU _) (by positivity)
  have ht : u ^ (n + 1) / (1 - u) ≤ U ^ (n + 1) / (1 - U) :=
    div_le_div₀ (pow_nonneg (hu0.trans hU) _) (pow_le_pow_left₀ hu0 hU _) (by linarith) (by linarith)
  linarith

theorem sqrt_three_ge : (17320508 / 10 ^ 7 : ℝ) ≤ √3 :=
  (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)

theorem sqrt_two_ge : (14142135 / 10 ^ 7 : ℝ) ≤ √2 :=
  (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)

/-- **`L₂ ≤ 0.04285391`**. -/
theorem lM_two_le : lM 2 ≤ 4285391 / 10 ^ 8 := by
  rw [lM_two]
  have hs := sqrt_three_ge
  have hs2 : √3 ≤ 7 / 4 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  set x := 3 * (19 - 8 * √3) / 13 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  have hxX : x ≤ 3 * (19 - 8 * (17320508 / 10 ^ 7)) / 13 := by rw [hx]; linarith
  have hU : 1 - 1 / x ≤ 15752859 / 10 ^ 8 := by
    have : 1 / (3 * (19 - 8 * (17320508 / 10 ^ 7)) / 13 : ℝ) ≤ 1 / x :=
      one_div_le_one_div_of_le (by linarith) hxX
    have h2 : (1 : ℝ) - 1 / (3 * (19 - 8 * (17320508 / 10 ^ 7)) / 13) ≤ 15752859 / 10 ^ 8 := by norm_num
    linarith
  have h := log_le_series hx1 hU (by norm_num) 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

/-- **`L₃ ≤ 0.00709927`**. -/
theorem lM_three_le : lM 3 ≤ 709927 / 10 ^ 8 := by
  rw [lM_three]
  have hs := sqrt_two_ge
  have hs2 : √2 ≤ 71 / 50 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  set x := 2 * (89 - 36 * √2) / 73 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  have hxX : x ≤ 2 * (89 - 36 * (14142135 / 10 ^ 7)) / 73 := by rw [hx]; linarith
  have hU : 1 - 1 / x ≤ 4170113 / 10 ^ 8 := by
    have : 1 / (2 * (89 - 36 * (14142135 / 10 ^ 7)) / 73 : ℝ) ≤ 1 / x :=
      one_div_le_one_div_of_le (by linarith) hxX
    have h2 : (1 : ℝ) - 1 / (2 * (89 - 36 * (14142135 / 10 ^ 7)) / 73) ≤ 4170113 / 10 ^ 8 := by norm_num
    linarith
  have h := log_le_series hx1 hU (by norm_num) 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

/-- **`πC_E ≤ 0.05406874`**. -/
theorem pi_mul_cE_le_decimal : π * cE ≤ 5406874 / 10 ^ 8 := by
  have h := pi_mul_cE_le
  have h2 := lM_two_le
  have h3 := lM_three_le
  have hp := Real.pi_lt_d6
  have hp2 : π ^ 2 ≤ 3.141593 ^ 2 := pow_le_pow_left₀ pi_pos.le hp.le 2
  have hT : (π ^ 2 / 12 - 11 / 16 - 1 / 9 - 1 / 64) / 2 ≤ 411556 / 10 ^ 8 := by
    have : (3.141593 ^ 2 / 12 - 11 / 16 - 1 / 9 - 1 / 64 : ℝ) / 2 ≤ 411556 / 10 ^ 8 := by norm_num
    linarith
  linarith

/-- **`C_E ≤ 0.017211`**. -/
theorem cE_le_decimal : cE ≤ 17211 / 10 ^ 6 := by
  have h := pi_mul_cE_le_decimal
  have hp := Real.pi_gt_d6
  have hc := cE_nonneg
  nlinarith

end certified

/-! ### Summing the cuts -/

section sums

/-- **The optimised two-term bound**: `A ≤ (1 + t)a + (1 + 1/t)b` for all `t > 0` gives `A ≤ (√a + √b)²`. -/
theorem le_sq_add_of_forall {A a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t > 0, A ≤ (1 + t) * a + (1 + 1 / t) * b) : A ≤ (√a + √b) ^ 2 := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  rcases ha.eq_or_lt with ha0 | ha0
  · rw [← ha0, Real.sqrt_zero, zero_add, hsb]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := h ((b + 1) / ε) (by positivity)
    rw [← ha0, mul_zero, zero_add] at this
    calc A ≤ (1 + 1 / ((b + 1) / ε)) * b := this
      _ = b + ε * (b / (b + 1)) := by field_simp
      _ ≤ b + ε * 1 := by gcongr; rw [div_le_one (by positivity)]; linarith
      _ = b + ε := by ring
  rcases hb.eq_or_lt with hb0 | hb0
  · rw [← hb0, Real.sqrt_zero, add_zero, hsa]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := h (ε / (a + 1)) (by positivity)
    rw [← hb0, mul_zero, add_zero] at this
    calc A ≤ (1 + ε / (a + 1)) * a := this
      _ = a + ε * (a / (a + 1)) := by ring
      _ ≤ a + ε * 1 := by gcongr; rw [div_le_one (by positivity)]; linarith
      _ = a + ε := by ring
  · set x := √a with hx
    set y := √b with hy
    have hx0 : 0 < x := Real.sqrt_pos.2 ha0
    have hy0 : 0 < y := Real.sqrt_pos.2 hb0
    have := h (y / x) (by positivity)
    rw [← hsa, ← hsb] at this
    calc A ≤ _ := this
      _ = (x + y) ^ 2 := by field_simp; ring

/-- **Minkowski for a finite sum**: `Σ(√aₘ + √bₘ)² ≤ (√Σa + √Σb)²`. -/
theorem sum_sq_add_le {ι : Type*} (S : Finset ι) {a b : ι → ℝ} (ha : ∀ i ∈ S, 0 ≤ a i)
    (hb : ∀ i ∈ S, 0 ≤ b i) :
    ∑ i ∈ S, (√(a i) + √(b i)) ^ 2 ≤ (√(∑ i ∈ S, a i) + √(∑ i ∈ S, b i)) ^ 2 := by
  have e1 : ∑ i ∈ S, (√(a i) + √(b i)) ^ 2
      = ∑ i ∈ S, a i + ∑ i ∈ S, b i + 2 * ∑ i ∈ S, √(a i) * √(b i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [add_sq, Real.sq_sqrt (ha i hi), Real.sq_sqrt (hb i hi)]; ring
  have hA : 0 ≤ ∑ i ∈ S, a i := Finset.sum_nonneg ha
  have hB : 0 ≤ ∑ i ∈ S, b i := Finset.sum_nonneg hb
  have e2 : (√(∑ i ∈ S, a i) + √(∑ i ∈ S, b i)) ^ 2
      = ∑ i ∈ S, a i + ∑ i ∈ S, b i + 2 * (√(∑ i ∈ S, a i) * √(∑ i ∈ S, b i)) := by
    rw [add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]; ring
  rw [e1, e2]
  have := Real.sum_mul_le_sqrt_mul_sqrt S (fun i => √(a i)) (fun i => √(b i))
  rw [Finset.sum_congr rfl fun i hi => Real.sq_sqrt (ha i hi),
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hb i hi)] at this
  linarith

/-- **The cut sum**: `‖Sₘ‖² ≤ AₘWₘ + rₘQ` with `ΣWₘ ≤ Q` gives `Σ‖Sₘ‖ ≤ (√ΣA + Σ√r)√Q`. -/
theorem sum_le_of_cuts {ι : Type*} (S : Finset ι) {x A W r : ι → ℝ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hA : ∀ i ∈ S, 0 ≤ A i) (hW : ∀ i ∈ S, 0 ≤ W i) (hr : ∀ i ∈ S, 0 ≤ r i) (hx : ∀ i ∈ S, 0 ≤ x i)
    (hcut : ∀ i ∈ S, x i ^ 2 ≤ A i * W i + r i * Q) (hWQ : ∑ i ∈ S, W i ≤ Q) :
    ∑ i ∈ S, x i ≤ (√(∑ i ∈ S, A i) + ∑ i ∈ S, √(r i)) * √Q := by
  have h1 : ∀ i ∈ S, x i ≤ √(A i) * √(W i) + √(r i) * √Q := by
    intro i hi
    have hAW : 0 ≤ A i * W i := mul_nonneg (hA i hi) (hW i hi)
    have hrQ : 0 ≤ r i * Q := mul_nonneg (hr i hi) hQ
    calc x i = √(x i ^ 2) := (Real.sqrt_sq (hx i hi)).symm
      _ ≤ √(A i * W i + r i * Q) := Real.sqrt_le_sqrt (hcut i hi)
      _ ≤ √(A i * W i) + √(r i * Q) := by
        rw [Real.sqrt_le_left (by positivity)]
        rw [add_sq, Real.sq_sqrt hAW, Real.sq_sqrt hrQ]
        nlinarith [Real.sqrt_nonneg (A i * W i), Real.sqrt_nonneg (r i * Q)]
      _ = √(A i) * √(W i) + √(r i) * √Q := by rw [Real.sqrt_mul (hA i hi), Real.sqrt_mul (hr i hi)]
  have h2 : ∑ i ∈ S, √(A i) * √(W i) ≤ √(∑ i ∈ S, A i) * √(∑ i ∈ S, W i) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt S (fun i => √(A i)) (fun i => √(W i))
    rwa [Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hA i hi),
      Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hW i hi)] at this
  have h3 : √(∑ i ∈ S, W i) ≤ √Q := Real.sqrt_le_sqrt hWQ
  calc ∑ i ∈ S, x i ≤ ∑ i ∈ S, (√(A i) * √(W i) + √(r i) * √Q) := Finset.sum_le_sum h1
    _ = ∑ i ∈ S, √(A i) * √(W i) + (∑ i ∈ S, √(r i)) * √Q := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ √(∑ i ∈ S, A i) * √Q + (∑ i ∈ S, √(r i)) * √Q := by
      gcongr
      exact h2.trans (mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _))
    _ = _ := by ring

theorem window_eq {d t : ℝ} (hd : d ≤ 1 / 2) {m m' : ℕ} (h : t ∈ Ioc ((m : ℝ) - d) (m + d))
    (h' : t ∈ Ioc ((m' : ℝ) - d) (m' + d)) : m = m' := by
  have a1 : (m : ℝ) < m' + 1 := by linarith [h.1, h'.2]
  have a2 : (m' : ℝ) < m + 1 := by linarith [h'.1, h.2]
  have b1 : m < m' + 1 := by exact_mod_cast a1
  have b2 : m' < m + 1 := by exact_mod_cast a2
  omega

/-- At most one window covers a point. -/
theorem sum_indicator_window_le {d t : ℝ} {f : ℝ → ℝ} (hd : d ≤ 1 / 2) (hf : 0 ≤ f t) (S : Finset ℕ) :
    ∑ m ∈ S, (Ioc ((m : ℝ) - d) (m + d)).indicator f t ≤ f t := by
  by_cases h : ∃ m ∈ S, t ∈ Ioc ((m : ℝ) - d) (m + d)
  · obtain ⟨m₀, hm₀, ht⟩ := h
    rw [Finset.sum_eq_single_of_mem m₀ hm₀ fun m _ hne => indicator_of_notMem
      (fun hm => hne (window_eq hd hm ht)) _, indicator_of_mem ht]
  · simp only [not_exists, not_and] at h
    rw [Finset.sum_eq_zero fun m hm => indicator_of_notMem (h m hm) _]
    exact hf

/-- **Disjoint windows**: `Σₘ ∫_{m−d}^{m+d} Φ² ≤ ∫₁^∞ Φ²` for `d ≤ 1/2` and cuts `m ≥ 2`. -/
theorem sum_window_le {Φ : ℝ → ℝ} (hΦ : IntegrableOn (fun t => Φ t ^ 2) (Ioi 1)) {d : ℝ} (hd0 : 0 < d)
    (hd : d ≤ 1 / 2) (S : Finset ℕ) (hS : ∀ m ∈ S, 2 ≤ m) :
    ∑ m ∈ S, ∫ x in ((m : ℝ) - d)..(m + d), Φ x ^ 2 ≤ ∫ t in Ioi 1, Φ t ^ 2 := by
  have e3 : ∀ m ∈ S, ∫ x in ((m : ℝ) - d)..(m + d), Φ x ^ 2
      = ∫ t in Ioi 1, (Ioc ((m : ℝ) - d) (m + d)).indicator (fun t => Φ t ^ 2) t := fun m hm => by
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hS m hm
    have hsub : Ioc ((m : ℝ) - d) (m + d) ⊆ Ioi (1 : ℝ) := fun t ht => mem_Ioi.2 (by linarith [ht.1])
    rw [intervalIntegral.integral_of_le (by linarith), setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.2 hsub]
  rw [Finset.sum_congr rfl e3, ← integral_finsetSum S fun m _ => hΦ.indicator measurableSet_Ioc]
  refine integral_mono_of_nonneg (ae_of_all _ fun t => Finset.sum_nonneg fun m _ =>
    indicator_nonneg (fun _ _ => sq_nonneg _) _) hΦ (ae_of_all _ fun t => ?_)
  exact sum_indicator_window_le (f := fun t => Φ t ^ 2) hd (sq_nonneg (Φ t)) S

end sums

/-! ### THEOREM E: the E-coupling of a band rung, per cut and summed -/

/-- The cut multiplier `ν(ξ) = (1/m) ∫ g(s) μ_cut(c, s/m, x₀, ξ) ds`. -/
noncomputable def nuCut (c : ℝ) (g : ℝ → ℝ) (m x₀ ξ : ℝ) : ℂ :=
  ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (g s : ℂ) * Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x₀ ξ

/-- The top multiplier `ν^top(ξ) = Σ_{2 ≤ m < M} ν_m(ξ)`, cut at `x₀ = M`. -/
noncomputable def nuTop (c : ℝ) (g : ℝ → ℝ) (M : ℕ) (ξ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ico 2 M, nuCut c g m M ξ

section theoremE
variable {ι : Type} [Fintype ι]

/-- The bottom sample `Σᵢ aᵢ Sᵢ[ν_m](m)` of the cut at `m`. -/
noncomputable def botS (c : ℝ) (gj : ℝ → ℝ) (a χ : ι → ℝ) (g : ι → ℝ → ℝ) (m : ℕ) : ℂ :=
  ∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (nuCut c gj m m) c (χ i) (g i) m

/-- The top sample `Re Σᵢ aᵢ Sᵢ[ν^top](M)`. -/
noncomputable def topE (c : ℝ) (gj : ℝ → ℝ) (a χ : ι → ℝ) (g : ι → ℝ → ℝ) (M : ℕ) : ℝ :=
  (∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (nuTop c gj M) c (χ i) (g i) M).re

/-- The E-coupling `⟨ψ_j, dilSum(Φ, M)⟩_{L²(1,∞)}`, `Φ = Σᵢ aᵢψᵢ`. -/
noncomputable def eCoup (c : ℝ) (gj : ℝ → ℝ) (a : ι → ℝ) (g : ι → ℝ → ℝ) (M : ℕ) : ℝ :=
  ∫ x in Ioi 1, Cvs.L2a.AngularProlateTailPositive.psi c gj x
    * Cvs.L2a.CoreArmIdentity.dilSum (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) M x

/-- The bulk `⟨ψ_j, dilSum⟩ + Σₘ Re(bottom) − top`: what the per-cut identity leaves. -/
noncomputable def bulkE (c : ℝ) (gj : ℝ → ℝ) (a χ : ι → ℝ) (g : ι → ℝ → ℝ) (M : ℕ) : ℝ :=
  eCoup c gj a g M + ∑ m ∈ Finset.Ico 2 M, (botS c gj a χ g m).re - topE c gj a χ g M

theorem eCoup_eq (c : ℝ) (gj : ℝ → ℝ) (a χ : ι → ℝ) (g : ι → ℝ → ℝ) (M : ℕ) :
    eCoup c gj a g M = -∑ m ∈ Finset.Ico 2 M, (botS c gj a χ g m).re + topE c gj a χ g M
      + bulkE c gj a χ g M := by
  unfold bulkE; ring

end theoremE

section cut
variable {gj gj₁ gj₂ : ℝ → ℝ} {c χj : ℝ}

/-- **The band integral of one cut multiplier**: with `|ν − ν^si| ≤ k` on the band,
`∫_{c ≤ |ξ| ≤ cY(m)} |ν|² ≤ (√((2/c)ψ(1)²Λ̂(w̄(m))L_m) + √(2c(Y(m) − 1)k²))²`. -/
theorem integral_nuCut_sq_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hg₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, gj (-s) = gj s)
    (hc : 0 < c) (hχ : 0 ≤ χj) (hχc : χj < c ^ 2) {m : ℝ} (hm : 2 ≤ m) (hW : Cvs.Prolate.BandMassLaw.wUp c m < 2) {k : ℝ}
    (hk : ∀ ξ ∈ bandB c (Cvs.L2a.OrbitGapIntegerM.Ymax m), ‖nuCut c gj m m ξ - nuSi c gj m ξ‖ ≤ k) :
    ∫ ξ in bandB c (Cvs.L2a.OrbitGapIntegerM.Ymax m), ‖nuCut c gj m m ξ‖ ^ 2
      ≤ (√(2 / c * (Cvs.L2a.AngularProlateTailPositive.psi c gj 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c m)) * lM m)
        + √(2 * c * (Cvs.L2a.OrbitGapIntegerM.Ymax m - 1) * k ^ 2)) ^ 2 := by
  set Y := Cvs.L2a.OrbitGapIntegerM.Ymax m with hYdef
  have hY : 1 ≤ Y := one_le_Ymax (by linarith)
  set D := Cvs.L2a.AngularProlateTailPositive.psi c gj 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c m) with hD
  have hD0 : 0 ≤ D := mul_nonneg (sq_nonneg _) (lamHat_nonneg _)
  have hL0 : 0 ≤ lM m := lM_nonneg (by linarith)
  obtain ⟨hi, he⟩ := integral_band_inv D hc hm
  obtain ⟨hic, hec⟩ := integral_band_const (k ^ 2) hc hY
  have hmeas : MeasurableSet (bandB c Y) := measurableSet_Icc.union measurableSet_Icc
  refine le_sq_add_of_forall (by positivity) (mul_nonneg (by nlinarith) (sq_nonneg k)) fun t ht => ?_
  have hint := (hi.const_mul (1 + t)).add (hic.const_mul (1 + 1 / t))
  have hle : ∫ ξ in bandB c Y, ‖nuCut c gj m m ξ‖ ^ 2
      ≤ ∫ ξ in bandB c Y, ((1 + t) * (D / (m ^ 2 * ξ ^ 2 - c ^ 2)) + (1 + 1 / t) * k ^ 2) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hint ?_
    filter_upwards [ae_restrict_mem hmeas] with ξ hξ
    have hsi := norm_nuSi_sq_le_band hg hg₁ hg₂c hang heven hc hχ hχc hm hW (mem_bandB_abs hc hξ).1
    have htri : ‖nuCut c gj m m ξ‖ ≤ ‖nuSi c gj m ξ‖ + k :=
      (norm_le_norm_add_norm_sub' _ _).trans (by linarith [hk ξ hξ])
    set x := ‖nuSi c gj m ξ‖ with hx
    have hx0 : 0 ≤ x := norm_nonneg _
    have hsq : ‖nuCut c gj m m ξ‖ ^ 2 ≤ (x + k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hamgm : 2 * x * k ≤ t * x ^ 2 + k ^ 2 / t := by
      rw [← sub_nonneg]
      have : t * x ^ 2 + k ^ 2 / t - 2 * x * k = (t * x - k) ^ 2 / t := by field_simp; ring
      rw [this]; positivity
    have : (x + k) ^ 2 ≤ (1 + t) * x ^ 2 + (1 + 1 / t) * k ^ 2 := by
      have e : (1 + 1 / t) * k ^ 2 = k ^ 2 + k ^ 2 / t := by ring
      nlinarith
    have : (1 + t) * x ^ 2 ≤ (1 + t) * (D / (m ^ 2 * ξ ^ 2 - c ^ 2)) :=
      mul_le_mul_of_nonneg_left hsi (by linarith)
    linarith
  rw [integral_add (hi.const_mul (1 + t)) (hic.const_mul (1 + 1 / t)), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, he, hec] at hle
  linarith

end cut

/-- The main-term arithmetic: `ΣA ≤ (2π)⁻¹(√Σa + √Σb)²`, `Σa ≤ (2/c)D·πE`, `Σb ≤ cK` give
`√ΣA ≤ √(DE/c) + √((c/2π)K)`. -/
theorem sqrt_main_le {SA Sa Sb D E c K : ℝ} (hc : 0 < c)
    (hSA : SA ≤ (2 * π)⁻¹ * (√Sa + √Sb) ^ 2) (hSa : Sa ≤ 2 / c * D * (π * E)) (hSb : Sb ≤ c * K) :
    √SA ≤ √(D * E / c) + √(c / (2 * π) * K) := by
  have hpi := pi_pos
  calc √SA ≤ √((2 * π)⁻¹ * (√Sa + √Sb) ^ 2) := Real.sqrt_le_sqrt hSA
    _ = √((2 * π)⁻¹) * (√Sa + √Sb) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ = √((2 * π)⁻¹ * Sa) + √((2 * π)⁻¹ * Sb) := by
        rw [mul_add, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    _ ≤ √(D * E / c) + √(c / (2 * π) * K) := by
        apply add_le_add
        · apply Real.sqrt_le_sqrt
          calc (2 * π)⁻¹ * Sa ≤ (2 * π)⁻¹ * (2 / c * D * (π * E)) :=
                mul_le_mul_of_nonneg_left hSa (by positivity)
            _ = D * E / c := by field_simp
        · apply Real.sqrt_le_sqrt
          calc (2 * π)⁻¹ * Sb ≤ (2 * π)⁻¹ * (c * K) := mul_le_mul_of_nonneg_left hSb (by positivity)
            _ = c / (2 * π) * K := by ring

/-! ### The `co` part of a cut multiplier, `|ν − ν^si| = O(‖g‖₁/(c²m))` -/

section co
open scoped ComplexConjugate

theorem eF_neg_y (c y x : ℝ) : Cvs.L2a.FarIntegrationByParts.eF c (-y) x = conj (Cvs.L2a.FarIntegrationByParts.eF c y x) := by
  unfold Cvs.L2a.FarIntegrationByParts.eF
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

theorem qQk_neg_y (c y x ξ : ℝ) :
    Cvs.L2a.QIdentityCutPoint.qQk c (-y) x ξ = conj (Cvs.L2a.QIdentityCutPoint.qQk c y x ξ) := by
  unfold Cvs.L2a.QIdentityCutPoint.qQk
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

theorem qQ₁_neg_y (c y x : ℝ) : Cvs.L2a.FarIntegrationByParts.qQ₁ c (-y) x = conj (Cvs.L2a.FarIntegrationByParts.qQ₁ c y x) := by
  unfold Cvs.L2a.FarIntegrationByParts.qQ₁
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- **The cut multiplier's reflection**: `μ_cut(c, −y, x, −ξ) = conj μ_cut(c, y, x, ξ)`. -/
theorem muCut_neg (c y x ξ : ℝ) :
    Cvs.L2a.QIdentityCutPoint.muCut c (-y) x (-ξ) = conj (Cvs.L2a.QIdentityCutPoint.muCut c y x ξ) := by
  unfold Cvs.L2a.QIdentityCutPoint.muCut Cvs.L2a.QIdentityCutPoint.muQ
  rw [Cvs.L2a.QIdentityCutPoint.qQk_neg, qQk_neg_y, qQ₁_neg_y, eF_neg_y]
  simp only [map_mul, map_add, map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- `μ_si(c, −y, x, −ξ) = conj μ_si(c, y, x, ξ)`. -/
theorem muSi_neg (c y x ξ : ℝ) :
    Cvs.L2a.CutKernelSimplified.muSi c (-y) x (-ξ) = conj (Cvs.L2a.CutKernelSimplified.muSi c y x ξ) := by
  unfold Cvs.L2a.CutKernelSimplified.muSi
  rw [eF_neg_y, show ((c * -y + -ξ : ℝ) : ℂ) = -((c * y + ξ : ℝ) : ℂ) by push_cast; ring]
  simp only [map_mul, map_div₀, map_neg, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem norm_muSi_eq {c y x η : ℝ} (hc : 0 < c) :
    ‖Cvs.L2a.CutKernelSimplified.muSi c y x (c * η)‖ = 1 / (c * |y + η|) := by
  unfold Cvs.L2a.CutKernelSimplified.muSi
  rw [norm_div, norm_mul, norm_neg, Complex.norm_I, (Cvs.L2a.FarIntegrationByParts.continuous_eF c y).2,
    Complex.norm_real, Real.norm_eq_abs, ← mul_add, abs_mul, abs_of_pos hc, one_mul]

theorem kNear_nonneg {c x y₀ Y : ℝ} (hc : 0 < c) (hx : 1 < x) (hy₀ : 0 ≤ y₀) (hy₁ : y₀ < 1) (hY : 0 ≤ Y) :
    0 ≤ Cvs.L2a.CutKernelSimplified.kNear c x y₀ Y := by
  have hp : 0 < pP x := pP_pos hx
  have h1 : 0 < 1 - y₀ ^ 2 := by nlinarith
  have hx0 : 0 < x := by linarith
  unfold Cvs.L2a.CutKernelSimplified.kNear
  positivity

/-- **The pointwise `co` bound**: for `0 < |y| ≤ y₀ < 1 ≤ |η| ≤ Y`,
`|μ_cut − μ_si|(c, y, x, cη) ≤ K_near(c, x, y₀, Y)/(c²(1 − y₀))`. -/
theorem norm_muCut_sub_muSi_le {c x y₀ Y y η : ℝ} (hc : 0 < c) (hx : 1 < x) (hy₀ : y₀ < 1) (hy : y ≠ 0)
    (hyy : |y| ≤ y₀) (hη1 : 1 ≤ |η|) (hηY : |η| ≤ Y) :
    ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * η) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * η)‖
      ≤ Cvs.L2a.CutKernelSimplified.kNear c x y₀ Y / (c ^ 2 * (1 - y₀)) := by
  -- the positive case
  have hpos : ∀ {y η : ℝ}, 0 < y → y ≤ y₀ → 1 ≤ |η| → |η| ≤ Y →
      ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * η) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * η)‖
        ≤ Cvs.L2a.CutKernelSimplified.kNear c x y₀ Y / (c ^ 2 * (1 - y₀)) := by
    intro y η hy hyy hη1 hηY
    have hy01 : 0 < 1 - y₀ := by linarith
    have hyη : 1 - y₀ ≤ |y + η| := by
      have := abs_sub_abs_le_abs_sub η (-y)
      rw [abs_neg, abs_of_pos hy, sub_neg_eq_add, add_comm] at this
      linarith
    have hne : y + η ≠ 0 := fun h => by rw [h, abs_zero] at hyη; linarith
    have hD : y ^ 2 ≠ η ^ 2 := by
      intro h
      have : |y| = |η| := by rw [← Real.sqrt_sq_eq_abs, h, Real.sqrt_sq_eq_abs]
      rw [abs_of_pos hy] at this
      linarith
    have h := Cvs.L2a.CutKernelSimplified.mul_norm_muCut_sub_muSi_le hc hx hy hne hD
    have hk := Cvs.L2a.CutKernelSimplified.kCmp_le_near hc hx hy hyy hy₀ hη1 hηY
    have hk0 := kNear_nonneg (Y := Y) hc hx (hy.le.trans hyy) hy₀ (by linarith [abs_nonneg η])
    rw [norm_muSi_eq hc] at h
    have hs : 1 / (c * |y + η|) ≤ 1 / (c * (1 - y₀)) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hyη hc.le)
    have hkc : 0 ≤ Cvs.L2a.CutKernelSimplified.kCmp c x y η := by
      have hp : 0 < pP x := pP_pos hx
      have hx0 : 0 < x := by linarith
      unfold Cvs.L2a.CutKernelSimplified.kCmp
      positivity
    have h2 : Cvs.L2a.CutKernelSimplified.kCmp c x y η * (1 / (c * |y + η|))
        ≤ Cvs.L2a.CutKernelSimplified.kNear c x y₀ Y * (1 / (c * (1 - y₀))) :=
      mul_le_mul hk hs (by positivity) hk0
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at *
    have h3 : c * ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * η) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * η)‖
        ≤ Cvs.L2a.CutKernelSimplified.kNear c x y₀ Y / (c * (1 - y₀)) := by
      calc _ ≤ _ := h
        _ ≤ _ := h2
        _ = _ := by ring
    rw [le_div_iff₀ (by positivity)] at h3 ⊢
    nlinarith
  rcases lt_or_gt_of_ne hy with hneg | hpos'
  · have e : Cvs.L2a.QIdentityCutPoint.muCut c y x (c * η) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * η)
        = conj (Cvs.L2a.QIdentityCutPoint.muCut c (-y) x (c * -η) - Cvs.L2a.CutKernelSimplified.muSi c (-y) x (c * -η)) := by
      have h1 := muCut_neg c (-y) x (c * -η)
      have h2 := muSi_neg c (-y) x (c * -η)
      rw [neg_neg, show -(c * -η) = c * η by ring] at h1 h2
      rw [map_sub, ← h1, ← h2]
    rw [e, Complex.norm_conj]
    exact hpos (by linarith) (by rw [abs_of_neg hneg] at hyy; linarith) (by rwa [abs_neg])
      (by rwa [abs_neg])
  · exact hpos hpos' (by rwa [abs_of_pos hpos'] at hyy) hη1 hηY

theorem qQk_ne_zero {c y x ξ : ℝ} (hx : 1 < x) (h : c ^ 2 * y ^ 2 < ξ ^ 2) :
    Cvs.L2a.QIdentityCutPoint.qQk c y x ξ ≠ 0 := by
  intro h0
  have hre := congrArg Complex.re h0
  simp only [Cvs.L2a.QIdentityCutPoint.qQk, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.zero_re] at hre
  have hp := pP_pos hx
  nlinarith

/-- On the band the cut multiplier is continuous in `s`. -/
theorem continuousOn_muCut_s {c m ξ : ℝ} (hc : 0 < c) (hm : 2 ≤ m) (hξ : c ≤ |ξ|) :
    ContinuousOn (fun s => Cvs.L2a.QIdentityCutPoint.muCut c (s / m) m ξ) (Icc (-1) 1) := by
  intro s hs
  have hm0 : 0 < m := by linarith
  have hlt : c ^ 2 * (s / m) ^ 2 < ξ ^ 2 := by
    have hs1 : (s / m) ^ 2 ≤ 1 / 4 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      have : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
      nlinarith
    have hξ2 : c ^ 2 ≤ ξ ^ 2 := by rw [← sq_abs ξ]; exact pow_le_pow_left₀ hc.le hξ 2
    nlinarith [sq_nonneg c]
  have hQ := qQk_ne_zero (c := c) (x := m) (by linarith) hlt
  have hq : Continuous fun s : ℝ => Cvs.L2a.QIdentityCutPoint.qQk c (s / m) m ξ := by
    unfold Cvs.L2a.QIdentityCutPoint.qQk; fun_prop
  have hq1 : Continuous fun s : ℝ => Cvs.L2a.FarIntegrationByParts.qQ₁ c (s / m) m := by
    unfold Cvs.L2a.FarIntegrationByParts.qQ₁; fun_prop
  have he : Continuous fun s : ℝ => Cvs.L2a.FarIntegrationByParts.eF c (s / m) m := by
    unfold Cvs.L2a.FarIntegrationByParts.eF; fun_prop
  have hl : Continuous fun s : ℝ => Complex.I * ((ξ - c * (s / m) : ℝ) : ℂ) := by fun_prop
  apply ContinuousAt.continuousWithinAt
  unfold Cvs.L2a.QIdentityCutPoint.muCut Cvs.L2a.QIdentityCutPoint.muQ
  exact he.continuousAt.mul (continuousAt_const.mul ((hl.continuousAt.div hq.continuousAt hQ).add
    (hq1.continuousAt.div (hq.continuousAt.pow 2) (pow_ne_zero 2 hQ))))

/-- On the band the `si` kernel is continuous in `s`. -/
theorem continuousOn_muSi_s {c m ξ : ℝ} (hc : 0 < c) (hm : 2 ≤ m) (hξ : c ≤ |ξ|) :
    ContinuousOn (fun s => Cvs.L2a.CutKernelSimplified.muSi c (s / m) m ξ) (Icc (-1) 1) := by
  intro s hs
  have hm0 : 0 < m := by linarith
  have hne : ((c * (s / m) + ξ : ℝ) : ℂ) ≠ 0 := by
    have h1 : |c * (s / m)| ≤ c / 2 := by
      rw [abs_mul, abs_of_pos hc, abs_div, abs_of_pos hm0]
      have : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
      calc c * (|s| / m) ≤ c * (1 / 2) := by gcongr
        _ = c / 2 := by ring
    have h2 : 0 < |c * (s / m) + ξ| := by
      have := abs_sub_abs_le_abs_sub ξ (-(c * (s / m)))
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      linarith
    exact_mod_cast abs_pos.1 h2
  have he : Continuous fun s : ℝ => Cvs.L2a.FarIntegrationByParts.eF c (s / m) m := by
    unfold Cvs.L2a.FarIntegrationByParts.eF; fun_prop
  have hd : Continuous fun s : ℝ => ((c * (s / m) + ξ : ℝ) : ℂ) := by fun_prop
  apply ContinuousAt.continuousWithinAt
  unfold Cvs.L2a.CutKernelSimplified.muSi
  exact (continuousAt_const.mul he.continuousAt).div hd.continuousAt hne

/-- **The `co` part of a cut multiplier**: on `c ≤ |ξ| ≤ cY(m)`,
`|ν_m − ν_m^si| ≤ ‖g‖₁·K_near(c, m, 1/m, Y(m))/(c²(m − 1))`. -/
theorem norm_nuCut_sub_nuSi_le {g : ℝ → ℝ} {c m ξ : ℝ} (hgc : ContinuousOn g (Icc (-1) 1)) (hc : 0 < c)
    (hm : 2 ≤ m) (hξ1 : c ≤ |ξ|) (hξY : |ξ| ≤ c * Cvs.L2a.OrbitGapIntegerM.Ymax m) :
    ‖nuCut c g m m ξ - nuSi c g m ξ‖
      ≤ gL1 g * (Cvs.L2a.CutKernelSimplified.kNear c m (1 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) / (c ^ 2 * (m - 1))) := by
  have hm0 : 0 < m := by linarith
  set K := Cvs.L2a.CutKernelSimplified.kNear c m (1 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) / (c ^ 2 * (1 - 1 / m)) with hK
  have hcont : ∀ {f : ℝ → ℂ}, ContinuousOn f (Icc (-1) 1) →
      IntervalIntegrable (fun s => (g s : ℂ) * f s) volume (-1) 1 := fun hf => by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_neg_one_one]
    exact (Complex.continuous_ofReal.comp_continuousOn hgc).mul hf
  have i1 := hcont (continuousOn_muCut_s hc hm hξ1)
  have i2 := hcont (continuousOn_muSi_s hc hm hξ1)
  have e : nuCut c g m m ξ - nuSi c g m ξ
      = ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (g s : ℂ)
        * (Cvs.L2a.QIdentityCutPoint.muCut c (s / m) m ξ - Cvs.L2a.CutKernelSimplified.muSi c (s / m) m ξ) := by
    unfold nuCut nuSi
    rw [← mul_sub, ← intervalIntegral.integral_sub i1 i2]
    refine congrArg (((1 / m : ℝ) : ℂ) * ·) (intervalIntegral.integral_congr fun s _ => ?_)
    ring
  have hη1 : 1 ≤ |ξ / c| := by rw [abs_div, abs_of_pos hc, le_div_iff₀ hc]; linarith
  have hηY : |ξ / c| ≤ Cvs.L2a.OrbitGapIntegerM.Ymax m := by
    rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]; linarith
  have hb : ‖∫ s in (-1 : ℝ)..1, (g s : ℂ)
        * (Cvs.L2a.QIdentityCutPoint.muCut c (s / m) m ξ - Cvs.L2a.CutKernelSimplified.muSi c (s / m) m ξ)‖
      ≤ ∫ s in (-1 : ℝ)..1, |g s| * K := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_
      (ii_of_continuousOn (hgc.abs.mul continuousOn_const))
    filter_upwards [volume.ae_ne 0] with s hs0 hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hsI : |s| ≤ 1 := abs_le.2 ⟨hs.1.le, hs.2⟩
    have hy : |s / m| ≤ 1 / m := by
      rw [abs_div, abs_of_pos hm0]; exact div_le_div_of_nonneg_right hsI hm0.le
    have h := norm_muCut_sub_muSi_le (x := m) (y₀ := 1 / m) (Y := Cvs.L2a.OrbitGapIntegerM.Ymax m) (y := s / m)
      (η := ξ / c) hc (by linarith) (by rw [div_lt_one hm0]; linarith) (div_ne_zero hs0 hm0.ne') hy hη1 hηY
    rwa [mul_div_cancel₀ _ hc.ne'] at h
  rw [e, norm_mul, intervalIntegral.integral_mul_const] at *
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hgl := gL1_nonneg (g := g)
  have hKe : 1 / m * (gL1 g * K)
      = gL1 g * (Cvs.L2a.CutKernelSimplified.kNear c m (1 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) / (c ^ 2 * (m - 1))) := by
    rw [hK]
    have : m - 1 ≠ 0 := by linarith
    field_simp
  rw [← hKe]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end co

section cosum

theorem Ymax_le_seven_sixths {m : ℝ} (hm : 2 ≤ m) : Cvs.L2a.OrbitGapIntegerM.Ymax m ≤ 7 / 6 := by
  unfold Cvs.L2a.OrbitGapIntegerM.Ymax
  have hp : 0 < m ^ 2 - 1 := by nlinarith
  rw [div_le_iff₀ (Real.sqrt_pos.2 hp)]
  have h : (6 * m / 7) ^ 2 ≤ m ^ 2 - 1 := by nlinarith
  have := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (by positivity)] at this
  linarith

/-- **`K_near` at a cut**: `K_near(c, m, 1/m, Y(m)) ≤ 9m/(m² − 1)` for `m ≥ 2`, `c ≥ 1`. -/
theorem kNear_cut_le {c m : ℝ} (hc : 1 ≤ c) (hm : 2 ≤ m) :
    Cvs.L2a.CutKernelSimplified.kNear c m (1 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) ≤ 9 * m / (m ^ 2 - 1) := by
  have hm0 : 0 < m := by linarith
  have hp : 0 < m ^ 2 - 1 := by nlinarith
  have hY := Ymax_le_seven_sixths hm
  have hY0 : 0 ≤ Cvs.L2a.OrbitGapIntegerM.Ymax m := le_trans zero_le_one (one_le_Ymax (by linarith))
  have e1 : 1 - (1 / m) ^ 2 = (m ^ 2 - 1) / m ^ 2 := by field_simp
  unfold Cvs.L2a.CutKernelSimplified.kNear pP
  rw [e1]
  have t1 : 2 * m * (1 / m) / ((m ^ 2 - 1) * ((m ^ 2 - 1) / m ^ 2)) ≤ 8 / 3 / (m ^ 2 - 1) := by
    rw [div_le_div_iff₀ (by positivity) hp]
    field_simp
    nlinarith
  have hA : m + 1 / m / c ≤ 5 / 4 * m := by
    have : 1 / m / c ≤ 1 / 2 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hB : 1 / m + Cvs.L2a.OrbitGapIntegerM.Ymax m ≤ 5 / 3 := by
    have : 1 / m ≤ 1 / 2 := by rw [div_le_div_iff₀ hm0 (by norm_num)]; linarith
    linarith
  have hA0 : 0 ≤ m + 1 / m / c := by positivity
  have hB0 : 0 ≤ 1 / m + Cvs.L2a.OrbitGapIntegerM.Ymax m := by positivity
  have t2 : 2 * (m + 1 / m / c) * (1 / m + Cvs.L2a.OrbitGapIntegerM.Ymax m) / ((m ^ 2 - 1) * ((m ^ 2 - 1) / m ^ 2) ^ 2)
      ≤ 200 / 27 * m / (m ^ 2 - 1) := by
    have hnum : 2 * (m + 1 / m / c) * (1 / m + Cvs.L2a.OrbitGapIntegerM.Ymax m) ≤ 2 * (5 / 4 * m) * (5 / 3) := by
      have := mul_le_mul hA hB hB0 (by positivity)
      linarith
    have hden : 0 < (m ^ 2 - 1) * ((m ^ 2 - 1) / m ^ 2) ^ 2 := by positivity
    calc _ ≤ 2 * (5 / 4 * m) * (5 / 3) / ((m ^ 2 - 1) * ((m ^ 2 - 1) / m ^ 2) ^ 2) :=
          div_le_div_of_nonneg_right hnum hden.le
      _ ≤ 200 / 27 * m / (m ^ 2 - 1) := by
          rw [div_le_div_iff₀ hden hp]
          field_simp
          have h5 : 3 * m ^ 2 ≤ 4 * (m ^ 2 - 1) := by nlinarith
          have h4 : 16 * (m ^ 2 - 1) ^ 2 ≥ 9 * m ^ 4 := by
            nlinarith [mul_le_mul h5 h5 (by positivity) (by nlinarith)]
          nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2000 * m * (m ^ 2 - 1))]
  have t3 : 8 / 3 / (m ^ 2 - 1) ≤ 4 / 3 * m / (m ^ 2 - 1) :=
    div_le_div_of_nonneg_right (by linarith) hp.le
  calc _ ≤ 8 / 3 / (m ^ 2 - 1) + 200 / 27 * m / (m ^ 2 - 1) := add_le_add t1 t2
    _ ≤ 4 / 3 * m / (m ^ 2 - 1) + 200 / 27 * m / (m ^ 2 - 1) := by linarith
    _ ≤ 9 * m / (m ^ 2 - 1) := by
        rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hp.le

/-- **One cut's `co` term**: `k_m²/(m² − 1) ≤ 108‖g‖₁²/(c⁴(m² − 1)²)`, `k_m = ‖g‖₁K_near/(c²(m − 1))`. -/
theorem co_term_le {c G m : ℝ} (hc : 1 ≤ c) (hG : 0 ≤ G) (hm : 2 ≤ m) :
    (G * (Cvs.L2a.CutKernelSimplified.kNear c m (1 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) / (c ^ 2 * (m - 1)))) ^ 2
        / (m ^ 2 - 1)
      ≤ 108 * G ^ 2 / c ^ 4 * (1 / (m ^ 2 - 1) ^ 2) := by
  have hm0 : 0 < m := by linarith
  have hp : 0 < m ^ 2 - 1 := by nlinarith
  have hm1 : 0 < m - 1 := by linarith
  have hk := kNear_cut_le hc hm
  have hk0 := kNear_nonneg (y₀ := 1 / m) (Y := Cvs.L2a.OrbitGapIntegerM.Ymax m) (by linarith : (0 : ℝ) < c)
    (by linarith : (1 : ℝ) < m) (by positivity) (by rw [div_lt_one hm0]; linarith)
    (le_trans zero_le_one (one_le_Ymax (by linarith)))
  have hc0 : 0 < c := by linarith
  have h1 : G * (Cvs.L2a.CutKernelSimplified.kNear c m (1 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) / (c ^ 2 * (m - 1)))
      ≤ G * (9 * m / (m ^ 2 - 1) / (c ^ 2 * (m - 1))) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hk (by positivity)) hG
  have h0 : 0 ≤ G * (Cvs.L2a.CutKernelSimplified.kNear c m (1 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) / (c ^ 2 * (m - 1))) := by
    positivity
  have h2 := pow_le_pow_left₀ h0 h1 2
  calc _ ≤ (G * (9 * m / (m ^ 2 - 1) / (c ^ 2 * (m - 1)))) ^ 2 / (m ^ 2 - 1) :=
        div_le_div_of_nonneg_right h2 hp.le
    _ ≤ 108 * G ^ 2 / c ^ 4 * (1 / (m ^ 2 - 1) ^ 2) := by
        rw [div_le_iff₀ hp]
        field_simp
        have hmm : 3 * m ^ 2 ≤ 4 * (m ^ 2 - 1) := by nlinarith
        have hm11 : 1 ≤ (m - 1) ^ 2 := by nlinarith
        have hprod : 3 * m ^ 2 ≤ 4 * (m ^ 2 - 1) * (m - 1) ^ 2 := by
          nlinarith [mul_le_mul hmm hm11 (by norm_num) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 27 * G ^ 2)]

/-- **The `co` sum is uniform in `M`**: `Σ_{2 ≤ m < M} k_m²/(m² − 1) ≤ 108‖g‖₁²(π²/12 − 11/16)/c⁴`. -/
theorem co_sum_le {c G : ℝ} (hc : 1 ≤ c) (hG : 0 ≤ G) (M : ℕ) :
    ∑ m ∈ Finset.Ico 2 M,
        (G * (Cvs.L2a.CutKernelSimplified.kNear c m (1 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) / (c ^ 2 * ((m : ℝ) - 1))))
          ^ 2 / ((m : ℝ) ^ 2 - 1)
      ≤ 108 * G ^ 2 / c ^ 4 * (π ^ 2 / 12 - 11 / 16) := by
  have h1 : ∀ m ∈ Finset.Ico 2 M,
      (G * (Cvs.L2a.CutKernelSimplified.kNear c m (1 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) / (c ^ 2 * ((m : ℝ) - 1))))
          ^ 2 / ((m : ℝ) ^ 2 - 1)
        ≤ 108 * G ^ 2 / c ^ 4 * (1 / ((m : ℝ) ^ 2 - 1) ^ 2) := fun m hm =>
    co_term_le hc hG (by exact_mod_cast (Finset.mem_Ico.1 hm).1)
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have hc4 : 0 ≤ 108 * G ^ 2 / c ^ 4 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hc4
  rw [Finset.sum_Ico_eq_sum_range]
  have hs := hasSum_sqInv.summable.sum_le_tsum (Finset.range (M - 2)) (fun n _ => by unfold sqInv; positivity)
  rw [hasSum_sqInv.tsum_eq] at hs
  refine le_of_eq_of_le (Finset.sum_congr rfl fun n _ => ?_) hs
  unfold sqInv
  congr 1; push_cast; ring

end cosum

/-! ### Uniform sums over the cuts -/

section unifsums

/-- `Σ_{2 ≤ m < M} 1/m² ≤ 1`, by `1/m² ≤ 1/(m − 1) − 1/m`. -/
theorem sum_inv_sq_le_one (M : ℕ) : ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) ^ 2 ≤ 1 := by
  rw [Finset.sum_Ico_eq_sum_range]
  set f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hf
  have h : ∀ n ∈ Finset.range (M - 2), 1 / (((2 + n : ℕ) : ℝ)) ^ 2 ≤ f n - f (n + 1) := by
    intro n _
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    simp only [hf]
    push_cast
    rw [show 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + 1) = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) by
      field_simp; ring]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_range_sub' f]
  have : 0 ≤ f (M - 2) := by simp only [hf]; positivity
  simp only [hf, Nat.cast_zero, zero_add, div_one] at this ⊢
  linarith

/-- `u/(u² − 1)` decreases on `u > 1`. -/
theorem div_sq_sub_one_anti {u u₀ : ℝ} (h1 : 1 < u₀) (h : u₀ ≤ u) : u / (u ^ 2 - 1) ≤ u₀ / (u₀ ^ 2 - 1) := by
  have a1 : 0 < u₀ ^ 2 - 1 := by nlinarith
  have a2 : 0 < u ^ 2 - 1 := by nlinarith
  rw [div_le_div_iff₀ a2 a1]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u - u₀) (by nlinarith : (0 : ℝ) ≤ u * u₀ + 1)]

theorem betaW_le_two {x d : ℝ} (hd2 : d ≤ 1 / 2) (hx : 2 ≤ x) :
    Cvs.L2a.BandTransferKernelForm.betaW x d ≤ Cvs.L2a.BandTransferKernelForm.betaW 2 d := by
  unfold Cvs.L2a.BandTransferKernelForm.betaW
  exact div_sq_sub_one_anti (by linarith) (by linarith)

theorem chirpW_le_two {x d : ℝ} (hd2 : d ≤ 1 / 2) (hx : 2 ≤ x) :
    Cvs.L2a.BandTransferKernelForm.chirpW x d ≤ Cvs.L2a.BandTransferKernelForm.chirpW 2 d := by
  unfold Cvs.L2a.BandTransferKernelForm.chirpW
  set v := x - d / 2
  set v₀ := 2 - d / 2
  have h1 : 1 < v₀ := by simp only [v₀]; linarith
  have h : v₀ ≤ v := by simp only [v, v₀]; linarith
  have a1 : 0 < v₀ ^ 2 - 1 := by nlinarith
  have a2 : 0 < v ^ 2 - 1 := by nlinarith
  have k1 := div_sq_sub_one_anti h1 h
  have k2 : 1 / (v ^ 2 - 1) ≤ 1 / (v₀ ^ 2 - 1) := one_div_le_one_div_of_le a1 (by nlinarith)
  calc v / (v ^ 2 - 1) ^ 2 = v / (v ^ 2 - 1) * (1 / (v ^ 2 - 1)) := by field_simp
    _ ≤ v₀ / (v₀ ^ 2 - 1) * (1 / (v₀ ^ 2 - 1)) :=
        mul_le_mul k1 k2 (by positivity) (div_nonneg (by linarith) a1.le)
    _ = v₀ / (v₀ ^ 2 - 1) ^ 2 := by field_simp

theorem Ymax_le_two {x : ℝ} (hx : 2 ≤ x) : Cvs.L2a.OrbitGapIntegerM.Ymax x ≤ Cvs.L2a.OrbitGapIntegerM.Ymax 2 := by
  unfold Cvs.L2a.OrbitGapIntegerM.Ymax
  have a1 : 0 < √((2 : ℝ) ^ 2 - 1) := Real.sqrt_pos.2 (by norm_num)
  have a2 : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith)
  rw [div_le_div_iff₀ a2 a1]
  have hsq : (x * √((2 : ℝ) ^ 2 - 1)) ^ 2 ≤ (2 * √(x ^ 2 - 1)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by nlinarith)]
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

theorem sigmaB_le_dY {dY dY' δ : ℝ} {N : ℕ → ℝ} {j : ℕ} (hN : 0 ≤ N j) (h : dY ≤ dY') :
    Cvs.L2a.BandTransferBandForm.sigmaB dY δ N j ≤ Cvs.L2a.BandTransferBandForm.sigmaB dY' δ N j := by
  unfold Cvs.L2a.BandTransferBandForm.sigmaB
  have := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (show 2 * dY ≤ 2 * dY' by linarith)) hN
  linarith

/-- **`τ̂` is largest at the first cut**: `τ̂(c, x₀, d, δ; N) ≤ τ̂(c, 2, d, δ; N)` for `x₀ ≥ 2`, `d ≤ 1/2`. -/
theorem tauHat_le_two {c x d δ : ℝ} {N : ℕ → ℝ} (hc : 0 < c) (hd : 0 < d) (hd2 : d ≤ 1 / 2) (hx : 2 ≤ x)
    (hδ : 0 ≤ δ) (h0 : ∀ j ≤ 3, 0 ≤ N j) :
    Cvs.L2a.BandTransferBandForm.tauHat c x d δ N ≤ Cvs.L2a.BandTransferBandForm.tauHat c 2 d δ N := by
  have hb := betaW_le_two hd2 hx
  have hb0 := Cvs.L2a.BandTransferKernelForm.betaW_nonneg (show 1 < x - d by linarith)
  have hch := chirpW_le_two hd2 hx
  have hch0 := Cvs.L2a.BandTransferKernelForm.chirpW_nonneg hd.le (show 1 < x - d by linarith)
  have hb20 := hb0.trans hb
  have hch20 := hch0.trans hch
  have hY := Ymax_le_two hx
  have hY0 : 0 ≤ Cvs.L2a.OrbitGapIntegerM.Ymax x - 1 := by
    linarith [Cvs.L2a.BandTransferBandForm.one_le_Ymax (show 1 < x by linarith)]
  have hs : ∀ j ≤ 3, 0 ≤ Cvs.L2a.BandTransferBandForm.sigmaB (Cvs.L2a.OrbitGapIntegerM.Ymax x - 1) δ N j
      ∧ Cvs.L2a.BandTransferBandForm.sigmaB (Cvs.L2a.OrbitGapIntegerM.Ymax x - 1) δ N j
        ≤ Cvs.L2a.BandTransferBandForm.sigmaB (Cvs.L2a.OrbitGapIntegerM.Ymax 2 - 1) δ N j := fun j hj =>
    ⟨Cvs.L2a.ScaledBandTransfer.sigmaB_nonneg hδ fun i hi => h0 i (hi.trans hj),
      sigmaB_le_dY (h0 j hj) (by linarith)⟩
  obtain ⟨a1, b1⟩ := hs 1 (by norm_num)
  obtain ⟨a2, b2⟩ := hs 2 (by norm_num)
  obtain ⟨a3, b3⟩ := hs 3 le_rfl
  have := a1.trans b1
  have := a2.trans b2
  have := a3.trans b3
  unfold Cvs.L2a.BandTransferBandForm.tauHat
  gcongr

end unifsums

/-! ### LBT-h with the collar charged to the window -/

section cutgen

/-- **The cross term by AM-GM**: from `x² ≤ AW + c(κN²W + 2Nτ√(sG)√(WP) + τ²GP)` with `P ≤ Q` and `t > 0`,
`x² ≤ (A + c(κ + ts)N²)W + (1 + 1/t)cτ²G·Q`. -/
theorem sq_le_of_cross {x A W P Q c κ N τ s G t : ℝ} (hc : 0 ≤ c) (hW : 0 ≤ W) (hP : 0 ≤ P) (hPQ : P ≤ Q)
    (hs : 0 ≤ s) (hG : 0 ≤ G) (ht : 0 < t)
    (h : x ^ 2 ≤ A * W + c * (κ * N ^ 2 * W + 2 * N * τ * √(s * G) * √(W * P) + τ ^ 2 * G * P)) :
    x ^ 2 ≤ (A + c * (κ + t * s) * N ^ 2) * W + (1 + 1 / t) * c * τ ^ 2 * G * Q := by
  have hu2 : (N * √s * √W) ^ 2 = N ^ 2 * s * W := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hs, Real.sq_sqrt hW]
  have hv2 : (τ * √G * √P) ^ 2 = τ ^ 2 * G * P := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hG, Real.sq_sqrt hP]
  have hcross : 2 * N * τ * √(s * G) * √(W * P) = 2 * (N * √s * √W) * (τ * √G * √P) := by
    rw [Real.sqrt_mul hs, Real.sqrt_mul hW]; ring
  have hamgm : ∀ u v : ℝ, 2 * u * v ≤ t * u ^ 2 + v ^ 2 / t := fun u v => by
    rw [← sub_nonneg]
    have : t * u ^ 2 + v ^ 2 / t - 2 * u * v = (t * u - v) ^ 2 / t := by field_simp; ring
    rw [this]; positivity
  have h1 := hamgm (N * √s * √W) (τ * √G * √P)
  rw [hu2, hv2, ← hcross] at h1
  have hPQ' : τ ^ 2 * G * P ≤ τ ^ 2 * G * Q := mul_le_mul_of_nonneg_left hPQ (by positivity)
  have hPQt : τ ^ 2 * G * P / t ≤ τ ^ 2 * G * Q / t := div_le_div_of_nonneg_right hPQ' ht.le
  have hin : κ * N ^ 2 * W + 2 * N * τ * √(s * G) * √(W * P) + τ ^ 2 * G * P
      ≤ κ * N ^ 2 * W + (t * (N ^ 2 * s * W) + τ ^ 2 * G * Q / t) + τ ^ 2 * G * Q := by linarith
  have h2 := mul_le_mul_of_nonneg_left hin hc
  calc x ^ 2 ≤ _ := h
    _ ≤ A * W + c * (κ * N ^ 2 * W + (t * (N ^ 2 * s * W) + τ ^ 2 * G * Q / t) + τ ^ 2 * G * Q) := by
        linarith
    _ = _ := by ring

end cutgen

section theoremE
variable {ι : Type} [Fintype ι]

/-- **One bottom cut, collar against the window**: LBT-h (`Cvs.L2a.BandTransferBandForm.lbt_band_gen`) at `x₀ = m`, weight `t > 0`
on the cross term; the window `(m − d, m + d)` carries the main and collar terms, `∫₁^∞Φ²` the transfer. -/
theorem botS_sq_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {gj : ℝ → ℝ} {M m : ℕ}
    {d δ t : ℝ} {μ₁ μ₂ μ₃ : ℝ → ℂ} {N : ℕ → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, Cvs.L2a.AngularProlateTailPositive.psi c (g i) t ^ 2)
    (hm : m ∈ Finset.Ico 2 M) (hd : 0 < d) (hd2 : d ≤ 1 / 2) (hδ : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t)
    (hμ : Cvs.L2a.BandTransferBandForm.IsBandMult (fun η => nuCut c gj m m (c * η)) μ₁ μ₂ μ₃ δ
      (Cvs.L2a.OrbitGapIntegerM.Ymax m) N) :
    ‖botS c gj a χ g m‖ ^ 2
      ≤ ((2 * π)⁻¹ * (∫ ξ in bandB c (Cvs.L2a.OrbitGapIntegerM.Ymax m), ‖nuCut c gj m m ξ‖ ^ 2)
          + c * (2 * (181 / 462) / π * δ
            + t * ((Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π)) * N 0 ^ 2)
          * (∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x) ^ 2)
        + (1 + 1 / t) * c * Cvs.L2a.BandTransferBandForm.tauHat c m d δ N ^ 2
          * (6 * (Fintype.card ι : ℝ) / (c * ((m : ℝ) ^ 2 - 1)))
          * ∫ x in Ioi 1, (∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hm' := Finset.mem_Ico.1 hm
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm'.1
  have hmM : (m : ℝ) + 1 ≤ M := by exact_mod_cast hm'.2
  set Y := Cvs.L2a.OrbitGapIntegerM.Ymax m with hYdef
  have hY1 : 1 ≤ Y := one_le_Ymax (by linarith)
  have hBc : ∀ ξ, |ξ| ∈ Icc c (c * Y) → ξ ∈ bandB c Y := by
    intro ξ hξ
    rcases le_or_gt 0 ξ with h0 | h0
    · right; rwa [abs_of_nonneg h0] at hξ
    · left; rw [abs_of_neg h0] at hξ; constructor <;> linarith [hξ.1, hξ.2]
  have hBi : IntegrableOn (fun ξ => ‖(fun η => nuCut c gj m m (c * η)) (ξ / c)‖ ^ 2) (bandB c Y) := by
    refine ContinuousOn.integrableOn_compact (isCompact_Icc.union isCompact_Icc) fun ξ hξ => ?_
    have hab := mem_bandB_abs hc0 hξ
    have hη : ξ / c ∈ Cvs.L2a.BandTransferBandForm.bandRg δ Y := by
      show |ξ / c| ∈ Icc (1 - δ) (Y + δ)
      rw [abs_div, abs_of_pos hc0]
      constructor
      · rw [le_div_iff₀ hc0]; nlinarith [hab.1]
      · rw [div_le_iff₀ hc0]; nlinarith [hab.2]
    have hdiv : ContinuousAt (fun x : ℝ => x / c) ξ := continuousAt_id.div_const c
    have hca : ContinuousAt (fun x : ℝ => nuCut c gj m m (c * (x / c))) ξ :=
      (hμ.d0 (ξ / c) hη).continuousAt.comp (f := fun x : ℝ => x / c) (x := ξ) hdiv
    exact (hca.norm.pow 2).continuousWithinAt
  have h := Cvs.L2a.BandTransferBandForm.lbt_band_gen a hg hg₁ hg₂c hang hc hχ0 hχc
    (X := (M : ℝ)) (x₀ := (m : ℝ)) (B := bandB c Y) (by linarith) hmass
    ⟨by linarith, by linarith⟩ hd (by linarith) hδ hδ1.le hμ (measurableSet_Icc.union measurableSet_Icc)
    hBc hBi
  have hcc : ∀ ξ : ℝ, c * (ξ / c) = ξ := fun ξ => by field_simp
  simp only [hcc] at h
  -- `P ≤ Q` by orthogonality on `(1, ∞)`
  have hψ2 : ∀ i, IntegrableOn (fun x => Cvs.L2a.AngularProlateTailPositive.psi c (g i) x ^ 2) (Ioi 1) := fun i =>
    (memLp_two_iff_integrable_sq ((Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i)
      (hang i)).2.2.1.aestronglyMeasurable)).mp (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i)
      (hang i) hc0)
  have hPQ : ∑ i, a i ^ 2 * (∫ t in (1 : ℝ)..M, Cvs.L2a.AngularProlateTailPositive.psi c (g i) t ^ 2)
      ≤ ∫ x in Ioi 1, (∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x) ^ 2 := by
    rw [Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc0 hχi]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set (hψ2 i) (ae_of_all _ fun x => sq_nonneg _)
      (ae_of_all _ fun x hx => show 1 < x from hx.1)
  have hP : 0 ≤ ∑ i, a i ^ 2 * (∫ t in (1 : ℝ)..M, Cvs.L2a.AngularProlateTailPositive.psi c (g i) t ^ 2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
      (intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _)
  have hW : 0 ≤ ∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hs : 0 ≤ (Y - 1 + 2 * (181 / 462) * δ) / π := by
    have := Real.pi_pos; apply div_nonneg _ this.le; linarith
  have hG : 0 ≤ 6 * (Fintype.card ι : ℝ) / (c * ((m : ℝ) ^ 2 - 1)) := by
    have : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  rw [show (Y - 1 + 2 * (181 / 462) * δ) * (6 * (Fintype.card ι : ℝ) / (c * ((m : ℝ) ^ 2 - 1))) / π
      = (Y - 1 + 2 * (181 / 462) * δ) / π * (6 * (Fintype.card ι : ℝ) / (c * ((m : ℝ) ^ 2 - 1))) by ring] at h
  exact sq_le_of_cross hc0.le hW hP hPQ hs hG ht h

/-- **THEOREM E, cut by cut**: with the collar charged to the windows and AM-GM weight `t > 0`,
`|⟨ψ_j, dilSum(Φ, M)⟩| ≤ [√(ψ_j(1)²Λ̂C_E/c) + ‖g_j‖₁√(54(π²/12 − 11/16)/(πc³)) + √(Σ_m E_m) + Σ_m √r_m + T + η]√P`,
`E_m = c(2κ_Sδ/π + t(ΔY_m + 2κ_Sδ)/π)N_{m,0}²`, `r_m = (1 + 1/t)c τ̂_m²·6J/(c(m² − 1))`. -/
theorem ecoupling_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {gj gj₁ gj₂ : ℝ → ℝ} {χj : ℝ} {M : ℕ} {d δ t T ηB : ℝ} {μ₁ μ₂ μ₃ : ℕ → ℝ → ℂ} {N : ℕ → ℕ → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hgj : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hgj₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hgj₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hangj : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (hevenj : ∀ s ∈ Icc (-1 : ℝ) 1, gj (-s) = gj s) (hχj0 : 0 ≤ χj) (hχjc : χj < c ^ 2)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, Cvs.L2a.AngularProlateTailPositive.psi c (g i) t ^ 2)
    (hd : 0 < d) (hd2 : d ≤ 1 / 2) (hδ : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t)
    (hμ : ∀ m ∈ Finset.Ico 2 M, Cvs.L2a.BandTransferBandForm.IsBandMult (fun η => nuCut c gj m m (c * η))
      (μ₁ m) (μ₂ m) (μ₃ m) δ (Cvs.L2a.OrbitGapIntegerM.Ymax m) (N m))
    (htop : |topE c gj a χ g M|
      ≤ T * √(∫ x in Ioi 1, (∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x) ^ 2))
    (hbulk : |bulkE c gj a χ g M|
      ≤ ηB * √(∫ x in Ioi 1, (∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x) ^ 2)) :
    |eCoup c gj a g M|
      ≤ (√(Cvs.L2a.AngularProlateTailPositive.psi c gj 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c 2) * cE / c)
          + gL1 gj * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3))
          + √(∑ m ∈ Finset.Ico 2 M, c * (2 * (181 / 462) / π * δ
              + t * ((Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π)) * N m 0 ^ 2)
          + ∑ m ∈ Finset.Ico 2 M, √((1 + 1 / t) * c * Cvs.L2a.BandTransferBandForm.tauHat c m d δ (N m) ^ 2
              * (6 * (Fintype.card ι : ℝ) / (c * ((m : ℝ) ^ 2 - 1))))
          + T + ηB) * √(∫ x in Ioi 1, (∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x) ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hgc := continuousOn_of_hasDerivAt hgj
  set Φ : ℝ → ℝ := fun x => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x with hΦ
  set Q := ∫ x in Ioi 1, Φ x ^ 2 with hQ
  set cuts := Finset.Ico 2 M with hcuts
  have hQ0 : 0 ≤ Q := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have hcm : ∀ m ∈ cuts, (2 : ℝ) ≤ m ∧ (m : ℝ) + 1 ≤ M := by
    intro m hm
    rw [hcuts, Finset.mem_Ico] at hm
    exact ⟨by exact_mod_cast hm.1, by exact_mod_cast hm.2⟩
  have hW2 : Cvs.Prolate.BandMassLaw.wUp c 2 < 2 := by
    unfold Cvs.Prolate.BandMassLaw.wUp pP
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hwm : ∀ m ∈ cuts, Cvs.Prolate.BandMassLaw.wUp c m ≤ Cvs.Prolate.BandMassLaw.wUp c 2 := fun m hm =>
    Cvs.Prolate.BandMassLaw.wUp_le_wUp hc0 (by norm_num) (hcm m hm).1
  have hWm : ∀ m ∈ cuts, Cvs.Prolate.BandMassLaw.wUp c m < 2 := fun m hm => lt_of_le_of_lt (hwm m hm) hW2
  have hΦ2 : IntegrableOn (fun x => Φ x ^ 2) (Ioi 1) := by
    have hm : MemLp Φ 2 (volume.restrict (Ioi 1)) := by
      have := memLp_finsetSum' Finset.univ fun i _ =>
        (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc0).const_mul (a i)
      refine this.ae_eq (ae_of_all _ fun x => ?_)
      simp [hΦ, Finset.sum_apply]
    exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
  -- the per-cut objects
  set A : ℕ → ℝ := fun m => (2 * π)⁻¹ * ∫ ξ in bandB c (Cvs.L2a.OrbitGapIntegerM.Ymax m),
    ‖nuCut c gj m m ξ‖ ^ 2 with hAdef
  set E : ℕ → ℝ := fun m => c * (2 * (181 / 462) / π * δ
    + t * ((Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π)) * N m 0 ^ 2 with hEdef
  set W : ℕ → ℝ := fun m => ∫ x in ((m : ℝ) - d)..(m + d), Φ x ^ 2 with hWdef
  set r : ℕ → ℝ := fun m => (1 + 1 / t) * c * Cvs.L2a.BandTransferBandForm.tauHat c m d δ (N m) ^ 2
    * (6 * (Fintype.card ι : ℝ) / (c * ((m : ℝ) ^ 2 - 1))) with hrdef
  have hA0 : ∀ m ∈ cuts, 0 ≤ A m := fun m _ =>
    mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  have hE0 : ∀ m ∈ cuts, 0 ≤ E m := by
    intro m hm
    have hY := one_le_Ymax (m := (m : ℝ)) (by linarith [(hcm m hm).1])
    have hpi := Real.pi_pos
    have : 0 ≤ (Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π :=
      div_nonneg (by linarith) hpi.le
    simp only [hEdef]
    positivity
  have hAE0 : ∀ m ∈ cuts, 0 ≤ A m + E m := fun m hm => add_nonneg (hA0 m hm) (hE0 m hm)
  have hW0 : ∀ m ∈ cuts, 0 ≤ W m := fun m _ =>
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hr0 : ∀ m ∈ cuts, 0 ≤ r m := by
    intro m hm
    have : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith [(hcm m hm).1]
    simp only [hrdef]
    positivity
  -- LBT-h at each cut
  have hcut : ∀ m ∈ cuts, ‖botS c gj a χ g m‖ ^ 2 ≤ (A m + E m) * W m + r m * Q := by
    intro m hm
    have h := botS_sq_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi hmass hm hd hd2 hδ hδ1 ht (hμ m hm)
    exact h
  have hWsum : ∑ m ∈ cuts, W m ≤ Q :=
    sum_window_le hΦ2 hd hd2 cuts fun m hm => (Finset.mem_Ico.1 hm).1
  have hsum := sum_le_of_cuts cuts (x := fun m => ‖botS c gj a χ g m‖) hQ0 hAE0 hW0 hr0
    (fun m _ => norm_nonneg _) hcut hWsum
  -- `√Σ(A + E) ≤ √ΣA + √ΣE`
  have hSA0 : 0 ≤ ∑ m ∈ cuts, A m := Finset.sum_nonneg hA0
  have hSE0 : 0 ≤ ∑ m ∈ cuts, E m := Finset.sum_nonneg hE0
  have hsplit : √(∑ m ∈ cuts, (A m + E m)) ≤ √(∑ m ∈ cuts, A m) + √(∑ m ∈ cuts, E m) := by
    rw [Finset.sum_add_distrib, Real.sqrt_le_left (by positivity), add_sq, Real.sq_sqrt hSA0,
      Real.sq_sqrt hSE0]
    nlinarith [Real.sqrt_nonneg (∑ m ∈ cuts, A m), Real.sqrt_nonneg (∑ m ∈ cuts, E m)]
  -- the `co` part of each cut
  set G := gL1 gj with hG
  have hG0 : 0 ≤ G := gL1_nonneg
  set k : ℕ → ℝ := fun m => G * (Cvs.L2a.CutKernelSimplified.kNear c m (1 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m)
    / (c ^ 2 * ((m : ℝ) - 1))) with hk
  have hco : ∀ m ∈ cuts, ∀ ξ ∈ bandB c (Cvs.L2a.OrbitGapIntegerM.Ymax m),
      ‖nuCut c gj m m ξ - nuSi c gj m ξ‖ ≤ k m := fun m hm ξ hξ => by
    have hab := mem_bandB_abs hc0 hξ
    exact norm_nuCut_sub_nuSi_le hgc hc0 (hcm m hm).1 hab.1 hab.2
  -- the main term
  set D₀ := Cvs.L2a.AngularProlateTailPositive.psi c gj 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c 2) with hD₀
  set am : ℕ → ℝ := fun m => 2 / c * (Cvs.L2a.AngularProlateTailPositive.psi c gj 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c m))
    * lM m with ham
  set bm : ℕ → ℝ := fun m => 2 * c * (Cvs.L2a.OrbitGapIntegerM.Ymax m - 1) * k m ^ 2 with hbm
  have ham0 : ∀ m ∈ cuts, 0 ≤ am m := fun m hm =>
    mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (lamHat_nonneg _)))
      (lM_nonneg (by linarith [(hcm m hm).1]))
  have hbm0 : ∀ m ∈ cuts, 0 ≤ bm m := fun m hm => by
    have := one_le_Ymax (m := (m : ℝ)) (by linarith [(hcm m hm).1])
    have hY0 : 0 ≤ Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc0.le) hY0) (sq_nonneg _)
  have hAle : ∀ m ∈ cuts, A m ≤ (2 * π)⁻¹ * (√(am m) + √(bm m)) ^ 2 := fun m hm =>
    mul_le_mul_of_nonneg_left (integral_nuCut_sq_le hgj hgj₁ hgj₂c hangj hevenj hc0 hχj0 hχjc
      (hcm m hm).1 (hWm m hm) (hco m hm)) (by positivity)
  have hSA : ∑ m ∈ cuts, A m ≤ (2 * π)⁻¹ * (√(∑ m ∈ cuts, am m) + √(∑ m ∈ cuts, bm m)) ^ 2 := by
    calc ∑ m ∈ cuts, A m ≤ ∑ m ∈ cuts, (2 * π)⁻¹ * (√(am m) + √(bm m)) ^ 2 := Finset.sum_le_sum hAle
      _ = (2 * π)⁻¹ * ∑ m ∈ cuts, (√(am m) + √(bm m)) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_sq_add_le cuts ham0 hbm0) (by positivity)
  have hSa : ∑ m ∈ cuts, am m ≤ 2 / c * D₀ * (π * cE) := by
    have h1 : ∑ m ∈ cuts, am m ≤ ∑ m ∈ cuts, 2 / c * D₀ * lM m := by
      refine Finset.sum_le_sum fun m hm => ?_
      have hl := lM_nonneg (m := (m : ℝ)) (by linarith [(hcm m hm).1])
      have hL := lamHat_mono (hwm m hm) hW2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hL (sq_nonneg _)) (by positivity)) hl
    have h2 : ∑ m ∈ cuts, lM (m : ℝ) ≤ π * cE := by
      rw [hcuts, Finset.sum_Ico_eq_sum_range]
      have := sum_lM_le (Finset.range (M - 2))
      refine le_of_eq_of_le (Finset.sum_congr rfl fun n _ => ?_) this
      congr 1; push_cast; ring
    rw [← Finset.mul_sum] at h1
    have : 0 ≤ 2 / c * D₀ := mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (lamHat_nonneg _))
    exact h1.trans (mul_le_mul_of_nonneg_left h2 this)
  have hSb : ∑ m ∈ cuts, bm m ≤ c * ∑ m ∈ cuts, k m ^ 2 / ((m : ℝ) ^ 2 - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : (1 : ℝ) < m := by linarith [(hcm m hm).1]
    have hY := Ymax_sub_one_le hm1
    have hp := sq_sub_one_pos hm1
    have hk2 := sq_nonneg (k m)
    simp only [hbm]
    calc 2 * c * (Cvs.L2a.OrbitGapIntegerM.Ymax m - 1) * k m ^ 2
        ≤ 2 * c * (1 / (2 * ((m : ℝ) ^ 2 - 1))) * k m ^ 2 := by gcongr
      _ = c * (k m ^ 2 / ((m : ℝ) ^ 2 - 1)) := by field_simp
  have hmain : √(∑ m ∈ cuts, A m)
      ≤ √(D₀ * cE / c) + √(c / (2 * π) * ∑ m ∈ cuts, k m ^ 2 / ((m : ℝ) ^ 2 - 1)) :=
    sqrt_main_le hc0 hSA hSa hSb
  have hS : 0 ≤ π ^ 2 / 12 - 11 / 16 := by nlinarith [Real.pi_gt_three]
  have hcosum := co_sum_le (c := c) (by linarith) hG0 M
  have hco_le : √(c / (2 * π) * ∑ m ∈ cuts, k m ^ 2 / ((m : ℝ) ^ 2 - 1))
      ≤ G * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3)) := by
    have hpi := pi_pos
    calc √(c / (2 * π) * ∑ m ∈ cuts, k m ^ 2 / ((m : ℝ) ^ 2 - 1))
        ≤ √(c / (2 * π) * (108 * G ^ 2 / c ^ 4 * (π ^ 2 / 12 - 11 / 16))) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcosum (by positivity))
      _ = √(G ^ 2 * (54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3))) := by
          congr 1; field_simp; ring
      _ = G * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3)) := by
          rw [Real.sqrt_mul (sq_nonneg G), Real.sqrt_sq hG0]
  -- assembly
  have hre : |∑ m ∈ cuts, (botS c gj a χ g m).re| ≤ ∑ m ∈ cuts, ‖botS c gj a χ g m‖ :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => Complex.abs_re_le_norm _)
  rw [eCoup_eq c gj a χ g M]
  have hsQ := Real.sqrt_nonneg Q
  have h1 : |-∑ m ∈ cuts, (botS c gj a χ g m).re + topE c gj a χ g M + bulkE c gj a χ g M|
      ≤ |∑ m ∈ cuts, (botS c gj a χ g m).re| + |topE c gj a χ g M| + |bulkE c gj a χ g M| := by
    have e1 := abs_add_le (-∑ m ∈ cuts, (botS c gj a χ g m).re + topE c gj a χ g M) (bulkE c gj a χ g M)
    have e2 := abs_add_le (-∑ m ∈ cuts, (botS c gj a χ g m).re) (topE c gj a χ g M)
    rw [abs_neg] at e2
    linarith
  have h2 : √(∑ m ∈ cuts, (A m + E m)) * √Q
      ≤ (√(D₀ * cE / c) + G * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3)) + √(∑ m ∈ cuts, E m)) * √Q :=
    mul_le_mul_of_nonneg_right (by linarith) hsQ
  calc _ ≤ _ := h1
    _ ≤ (√(∑ m ∈ cuts, (A m + E m)) + ∑ m ∈ cuts, √(r m)) * √Q + T * √Q + ηB * √Q := by
        linarith
    _ = √(∑ m ∈ cuts, (A m + E m)) * √Q + (∑ m ∈ cuts, √(r m)) * √Q + T * √Q + ηB * √Q := by ring
    _ ≤ (√(D₀ * cE / c) + G * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3)) + √(∑ m ∈ cuts, E m)) * √Q
          + (∑ m ∈ cuts, √(r m)) * √Q + T * √Q + ηB * √Q := by linarith
    _ = _ := by ring

/-- `τ̄(c, d, δ, r) = τ̂(c, 2, d, δ; j ↦ j!/r^j)`: the r-scaled transfer constant at the first cut. -/
noncomputable def tauBar (c d δ r : ℝ) : ℝ :=
  Cvs.L2a.BandTransferBandForm.tauHat c 2 d δ (fun j => (j.factorial : ℝ) / r ^ j)

/-- The collar constant `K_col(δ, t) = (2κ_Sδ + t(1/6 + 2κ_Sδ))/π`, `κ_S = 181/462`. -/
noncomputable def collarK (δ t : ℝ) : ℝ := (2 * (181 / 462) * δ + t * (1 / 6 + 2 * (181 / 462) * δ)) / π

/-- **THEOREM E, uniform in `M`**: if every cut multiplier has `N_{m,0} ≤ K₀/m` and `N_{m,j} ≤ (K_b/m)j!/r^j`
(`j ≤ 3`), then `|⟨ψ_j, dilSum(Φ, M)⟩| ≤ [√(ψ_j(1)²Λ̂C_E/c) + ‖g_j‖₁√(54(π²/12 − 11/16)/(πc³))
+ K₀√(cK_col(δ, t)) + K_b τ̄√(8(1 + 1/t)J) + T + η]√P`; no constant depends on `M`. -/
theorem ecoupling_le_unif {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {gj gj₁ gj₂ : ℝ → ℝ} {χj : ℝ} {M : ℕ} {d δ t r K0 Kb T ηB : ℝ} {μ₁ μ₂ μ₃ : ℕ → ℝ → ℂ}
    {N : ℕ → ℕ → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hgj : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hgj₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hgj₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hangj : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (hevenj : ∀ s ∈ Icc (-1 : ℝ) 1, gj (-s) = gj s) (hχj0 : 0 ≤ χj) (hχjc : χj < c ^ 2)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, Cvs.L2a.AngularProlateTailPositive.psi c (g i) t ^ 2)
    (hd : 0 < d) (hd2 : d ≤ 1 / 2) (hδ : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) (hr : 0 < r)
    (hK0 : 0 ≤ K0) (hKb : 0 ≤ Kb)
    (hμ : ∀ m ∈ Finset.Ico 2 M, Cvs.L2a.BandTransferBandForm.IsBandMult (fun η => nuCut c gj m m (c * η))
      (μ₁ m) (μ₂ m) (μ₃ m) δ (Cvs.L2a.OrbitGapIntegerM.Ymax m) (N m))
    (hN0 : ∀ m ∈ Finset.Ico 2 M, N m 0 ≤ K0 / m)
    (hN : ∀ m ∈ Finset.Ico 2 M, ∀ j ≤ 3, N m j ≤ Kb / m * ((j.factorial : ℝ) / r ^ j))
    (htop : |topE c gj a χ g M|
      ≤ T * √(∫ x in Ioi 1, (∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x) ^ 2))
    (hbulk : |bulkE c gj a χ g M|
      ≤ ηB * √(∫ x in Ioi 1, (∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x) ^ 2)) :
    |eCoup c gj a g M|
      ≤ (√(Cvs.L2a.AngularProlateTailPositive.psi c gj 1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c 2) * cE / c)
          + gL1 gj * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3))
          + K0 * √(c * collarK δ t)
          + Kb * tauBar c d δ r * √(8 * (1 + 1 / t) * (Fintype.card ι : ℝ))
          + T + ηB) * √(∫ x in Ioi 1, (∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) x) ^ 2) := by
  have hc0 : 0 < c := by linarith
  have h := ecoupling_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi hgj hgj₁ hgj₂c hangj hevenj hχj0 hχjc hmass
    hd hd2 hδ hδ1 ht hμ htop hbulk
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have hpi := Real.pi_pos
  have hm2 : ∀ m ∈ Finset.Ico 2 M, (2 : ℝ) ≤ m := fun m hm => by exact_mod_cast (Finset.mem_Ico.1 hm).1
  have hNn : ∀ m ∈ Finset.Ico 2 M, ∀ j ≤ 3, 0 ≤ N m j := fun m hm j hj => by
    obtain ⟨n0, n1, n2, n3⟩ := Cvs.L2a.BandTransferBandForm.N_nonneg hδ (one_le_Ymax (by linarith [hm2 m hm]))
      (hμ m hm)
    interval_cases j
    exacts [n0, n1, n2, n3]
  have hinv := sum_inv_sq_le_one M
  have hinv0 : 0 ≤ ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) ^ 2 := Finset.sum_nonneg fun m _ => by positivity
  -- the collar sum
  have hK : 0 ≤ collarK δ t := by unfold collarK; positivity
  have hE : ∑ m ∈ Finset.Ico 2 M, c * (2 * (181 / 462) / π * δ
        + t * ((Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π)) * N m 0 ^ 2
      ≤ c * collarK δ t * K0 ^ 2 := by
    have h1 : ∀ m ∈ Finset.Ico 2 M, c * (2 * (181 / 462) / π * δ
          + t * ((Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π)) * N m 0 ^ 2
        ≤ c * collarK δ t * K0 ^ 2 * (1 / (m : ℝ) ^ 2) := by
      intro m hm
      have hm2' := hm2 m hm
      have hY := Ymax_sub_one_le (m := (m : ℝ)) (by linarith)
      have hY0 := one_le_Ymax (m := (m : ℝ)) (by linarith)
      have hp : (1 : ℝ) / (2 * ((m : ℝ) ^ 2 - 1)) ≤ 1 / 6 := by
        rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
      have hb : 2 * (181 / 462) / π * δ + t * ((Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π)
          ≤ collarK δ t := by
        unfold collarK
        rw [show 2 * (181 / 462) / π * δ + t * ((Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π)
          = (2 * (181 / 462) * δ + t * (Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ)) / π by ring]
        apply div_le_div_of_nonneg_right _ hpi.le
        nlinarith
      have hb0 : 0 ≤ 2 * (181 / 462) / π * δ
          + t * ((Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π) := by
        have : 0 ≤ (Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π :=
          div_nonneg (by linarith) hpi.le
        positivity
      have hn0 := hNn m hm 0 (by norm_num)
      have hn2 : N m 0 ^ 2 ≤ K0 ^ 2 * (1 / (m : ℝ) ^ 2) := by
        have := pow_le_pow_left₀ hn0 (hN0 m hm) 2
        rw [div_pow] at this
        rw [mul_one_div]; exact this
      calc c * (2 * (181 / 462) / π * δ
            + t * ((Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π)) * N m 0 ^ 2
          ≤ c * collarK δ t * (K0 ^ 2 * (1 / (m : ℝ) ^ 2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hb hc0.le) hn2 (sq_nonneg _) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    calc c * collarK δ t * K0 ^ 2 * ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) ^ 2
        ≤ c * collarK δ t * K0 ^ 2 * 1 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hEs : √(∑ m ∈ Finset.Ico 2 M, c * (2 * (181 / 462) / π * δ
        + t * ((Cvs.L2a.OrbitGapIntegerM.Ymax m - 1 + 2 * (181 / 462) * δ) / π)) * N m 0 ^ 2)
      ≤ K0 * √(c * collarK δ t) := by
    calc _ ≤ √(c * collarK δ t * K0 ^ 2) := Real.sqrt_le_sqrt hE
      _ = K0 * √(c * collarK δ t) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK0]; ring
  -- the transfer sum
  set J : ℝ := (Fintype.card ι : ℝ) with hJ
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  set τb := tauBar c d δ r with hτb
  have hNr : ∀ j ≤ 3, 0 ≤ (j.factorial : ℝ) / r ^ j := fun j _ => by positivity
  have hτb0 : 0 ≤ τb := Cvs.L2a.ScaledBandTransfer.tauHat_nonneg hc0.le hd.le (by linarith) hδ.le hNr
  have hR : ∀ m ∈ Finset.Ico 2 M, √((1 + 1 / t) * c * Cvs.L2a.BandTransferBandForm.tauHat c m d δ (N m) ^ 2
        * (6 * J / (c * ((m : ℝ) ^ 2 - 1))))
      ≤ Kb * τb * √(8 * (1 + 1 / t) * J) * (1 / (m : ℝ) ^ 2) := by
    intro m hm
    have hm2' := hm2 m hm
    have hm0 : 0 < (m : ℝ) := by linarith
    have hp : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
    have hxd : 1 < (m : ℝ) - d := by linarith
    have hτ0 := Cvs.L2a.ScaledBandTransfer.tauHat_nonneg hc0.le hd.le hxd hδ.le (hNn m hm)
    have hτ1 := Cvs.L2a.ScaledBandTransfer.tauHat_le_scaled hc0.le hd.le hxd hδ.le (hNn m hm) (hN m hm)
    have hτ2 := tauHat_le_two hc0 hd hd2 hm2' hδ.le hNr
    have hτ : Cvs.L2a.BandTransferBandForm.tauHat c m d δ (N m) ≤ Kb / m * τb :=
      hτ1.trans (mul_le_mul_of_nonneg_left hτ2 (by positivity))
    have hτsq := pow_le_pow_left₀ hτ0 hτ 2
    have hG : 6 * J / (c * ((m : ℝ) ^ 2 - 1)) ≤ 8 * J / (c * (m : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 6 * (m : ℝ) ^ 2 ≤ 8 * ((m : ℝ) ^ 2 - 1) := by nlinarith
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ J * c)
      linarith
    have hle : (1 + 1 / t) * c * Cvs.L2a.BandTransferBandForm.tauHat c m d δ (N m) ^ 2
          * (6 * J / (c * ((m : ℝ) ^ 2 - 1)))
        ≤ (Kb * τb * √(8 * (1 + 1 / t) * J) * (1 / (m : ℝ) ^ 2)) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      calc (1 + 1 / t) * c * Cvs.L2a.BandTransferBandForm.tauHat c m d δ (N m) ^ 2
            * (6 * J / (c * ((m : ℝ) ^ 2 - 1)))
          ≤ (1 + 1 / t) * c * (Kb / m * τb) ^ 2 * (8 * J / (c * (m : ℝ) ^ 2)) := by
            have a1 := mul_le_mul_of_nonneg_left hτsq (by positivity : (0 : ℝ) ≤ (1 + 1 / t) * c)
            exact mul_le_mul a1 hG (by positivity) (by positivity)
        _ = _ := by field_simp
    calc _ ≤ √((Kb * τb * √(8 * (1 + 1 / t) * J) * (1 / (m : ℝ) ^ 2)) ^ 2) := Real.sqrt_le_sqrt hle
      _ = _ := Real.sqrt_sq (by positivity)
  have hRs : ∑ m ∈ Finset.Ico 2 M, √((1 + 1 / t) * c * Cvs.L2a.BandTransferBandForm.tauHat c m d δ (N m) ^ 2
        * (6 * J / (c * ((m : ℝ) ^ 2 - 1))))
      ≤ Kb * τb * √(8 * (1 + 1 / t) * J) := by
    refine (Finset.sum_le_sum hR).trans ?_
    rw [← Finset.mul_sum]
    calc Kb * τb * √(8 * (1 + 1 / t) * J) * ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) ^ 2
        ≤ Kb * τb * √(8 * (1 + 1 / t) * J) * 1 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  linarith

/-! ### The sharp part of `N_{m,0}` on the collar -/

/-- **The `si` multiplier on the collar**: for `m ≥ 2`, `δ ≤ 1/4`, `|η| ≥ 1 − δ`, `c ≥ 80`, an even rung has
`|ν_m^si(cη)| ≤ (4|ψ(1)|√Λ̂(w̄(3/2))/(√5 c))/m`, the `si` half of `N_{m,0} ≤ K₀/m`. -/
theorem norm_nuSi_le_collar {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    {m δ η : ℝ} (hm : 2 ≤ m) (hδ4 : δ ≤ 1 / 4) (hη : 1 - δ ≤ |η|) :
    ‖nuSi c g m (c * η)‖
      ≤ 4 * |Cvs.L2a.AngularProlateTailPositive.psi c g 1| * √(lamHat (Cvs.Prolate.BandMassLaw.wUp c (3 / 2))) / (√5 * c) / m := by
  have hc0 : 0 < c := by linarith
  have hgc := continuousOn_of_hasDerivAt hg
  have hm0 : 0 < m := by linarith
  have hη34 : (3 : ℝ) / 4 ≤ |η| := by linarith
  have hy34 : 3 / 4 * m ≤ m * |η| := by nlinarith
  have hy32 : (3 : ℝ) / 2 ≤ m * |η| := by linarith
  have hmξ : c < m * |c * η| := by rw [abs_mul, abs_of_pos hc0]; nlinarith
  have e1 : m * |c * η| / c = m * |η| := by rw [abs_mul, abs_of_pos hc0]; field_simp
  have hsq := norm_nuSi_sq (c := c) hgc heven hc0 hm0 hmξ
  rw [e1] at hsq
  have hW32 : Cvs.Prolate.BandMassLaw.wUp c (3 / 2) < 2 := by
    unfold Cvs.Prolate.BandMassLaw.wUp pP; rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hwle : Cvs.Prolate.BandMassLaw.wUp c (m * |η|) ≤ Cvs.Prolate.BandMassLaw.wUp c (3 / 2) := Cvs.Prolate.BandMassLaw.wUp_le_wUp hc0 (by norm_num) hy32
  have he := sq_add_sq_le_even hg hg₁ hg₂c hang heven hc0 hχ hχc (by linarith) (lt_of_le_of_lt hwle hW32)
  have hL := lamHat_mono hwle hW32
  have hp : 5 / 16 * m ^ 2 ≤ pP (m * |η|) := by unfold pP; nlinarith
  have hpos : 0 < pP (m * |η|) := by nlinarith
  set L := lamHat (Cvs.Prolate.BandMassLaw.wUp c (3 / 2)) with hLdef
  have hL0 : 0 ≤ L := lamHat_nonneg _
  set ψ1 := Cvs.L2a.AngularProlateTailPositive.psi c g 1 with hψ1
  have h1 : vC c g (m * |η|) ^ 2 + vS c g (m * |η|) ^ 2 ≤ ψ1 ^ 2 * L / (5 / 16 * m ^ 2) := by
    refine he.trans ?_
    calc ψ1 ^ 2 * lamHat (Cvs.Prolate.BandMassLaw.wUp c (m * |η|)) / pP (m * |η|) ≤ ψ1 ^ 2 * L / pP (m * |η|) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL (sq_nonneg _)) hpos.le
      _ ≤ ψ1 ^ 2 * L / (5 / 16 * m ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hp
  have hb : ‖nuSi c g m (c * η)‖ ^ 2 ≤ (4 * |ψ1| * √L / (√5 * c) / m) ^ 2 := by
    rw [hsq]
    have hr : (4 * |ψ1| * √L / (√5 * c) / m) ^ 2 = ψ1 ^ 2 * L / (5 / 16 * m ^ 2) / c ^ 2 := by
      rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hL0, Real.sq_sqrt (by norm_num), sq_abs]
      field_simp; ring
    rw [hr]
    exact div_le_div_of_nonneg_right h1 (sq_nonneg c)
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hb

end theoremE

end Cvs.L2a.BandRungOutgoingWave
