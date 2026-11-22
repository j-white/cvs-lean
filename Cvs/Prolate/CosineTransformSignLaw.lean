import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.AngularEdgeValueNonzero
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sign law of the finite cosine transform

For an even angular solution `g ≢ 0` with `c > 0`, `χ ≥ 0`, `Φ(y) = ∫_{−1}^{1} g(s) cosh(cys) ds` solves
`(1 + y²)Φ'' + 2yΦ' = (c²y² + χ)Φ`, so `Φ²` is nondecreasing on `[0, ∞)` and `Φ` far out has the sign of `g(1)`:
`0 < g(1) ψ(0)`, hence `0 < μ g(0) g(1)` and `0 < ψ(1) g(1) ↔ 0 < g(0) g(1)`, the form `MirrorConcentrationHalf`'s `tau_ge_of_sign` consumes.
-/

namespace Cvs.Prolate.CosineTransformSignLaw

open Real Set Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive

/-- **Differentiation under the integral** for a kernel whose `y`-derivative is bounded on a ball. -/
theorem hasDerivAt_kint_loc {g : ℝ → ℝ} {k k' : ℝ → ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1))
    (hkc : ∀ y, Continuous (k y)) (hk'c : ∀ y, Continuous (k' y))
    (hd : ∀ y s, HasDerivAt (fun y => k y s) (k' y s) y) (y₀ C : ℝ)
    (hb : ∀ y ∈ Metric.ball y₀ 1, ∀ s, |s| ≤ 1 → |k' y s| ≤ C) :
    HasDerivAt (kint g k) (kint g k' y₀) y₀ := by
  have hgi : IntervalIntegrable g MeasureTheory.volume (-1) 1 := hg.intervalIntegrable
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (a := -1) (b := 1) (F := fun y s => g s * k y s) (F' := fun y s => g s * k' y s) (x₀ := y₀)
    (bound := fun s => |g s| * C) (s := Metric.ball y₀ 1) (Metric.ball_mem_nhds y₀ one_pos)
    (Filter.Eventually.of_forall fun y => ((hgi.mul_continuousOn (hkc y).continuousOn).def').aestronglyMeasurable)
    (hgi.mul_continuousOn (hkc y₀).continuousOn)
    ((hgi.mul_continuousOn (hk'c y₀).continuousOn).def').aestronglyMeasurable
    (Filter.Eventually.of_forall fun s hs y hy => by
      have hs1 : |s| ≤ 1 := by
        rw [uIoc_of_le (by norm_num)] at hs; exact abs_le.mpr ⟨hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hb y hy s hs1) (abs_nonneg _))
    (hgi.abs.mul_const C)
    (Filter.Eventually.of_forall fun s _ y _ => (hd y s).const_mul (g s))
  exact key.2

/-- On the ball of radius `1` about `y₀` and for `|s| ≤ 1`, `cosh(cys) ≤ cosh(|c|(|y₀| + 1))`. -/
theorem cosh_le_ball {c y₀ y s : ℝ} (hy : y ∈ Metric.ball y₀ 1) (hs : |s| ≤ 1) :
    cosh (c * y * s) ≤ cosh (|c| * (|y₀| + 1)) := by
  rw [Real.cosh_le_cosh]
  have hy' : |y| ≤ |y₀| + 1 := by
    have := abs_sub_abs_le_abs_sub y y₀
    rw [Metric.mem_ball, Real.dist_eq] at hy
    linarith
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |c| * (|y₀| + 1))]
  calc |c| * |y| * |s| ≤ |c| * (|y₀| + 1) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hy' (abs_nonneg c)) hs (abs_nonneg s) (by positivity)
    _ = |c| * (|y₀| + 1) := mul_one _

/-- `|sinh x| ≤ cosh x`. -/
theorem abs_sinh_le_cosh (x : ℝ) : |sinh x| ≤ cosh x := by
  rw [Real.abs_sinh, ← Real.cosh_abs x]; exact (Real.sinh_lt_cosh _).le

/-- `Φ(y) = ∫_{−1}^{1} g(s) cosh(cys) ds`, the cosine transform on the imaginary axis. -/
noncomputable def phiI (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := kint g (fun y s => cosh (c * y * s)) y

/-- `Φ'(y) = ∫ g(s) cs sinh(cys) ds`. -/
noncomputable def phiI₁ (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := kint g (fun y s => c * s * sinh (c * y * s)) y

/-- `Φ''(y) = ∫ g(s) c²s² cosh(cys) ds`. -/
noncomputable def phiI₂ (c : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := kint g (fun y s => c ^ 2 * s ^ 2 * cosh (c * y * s)) y

/-- **The derivatives of `Φ`** as kernel integrals. -/
theorem phiI_deriv {g : ℝ → ℝ} (c : ℝ) (hg : ContinuousOn g (uIcc (-1) 1)) (y : ℝ) :
    HasDerivAt (phiI c g) (phiI₁ c g y) y ∧ HasDerivAt (phiI₁ c g) (phiI₂ c g y) y := by
  constructor
  · apply hasDerivAt_kint_loc hg (fun _ => by fun_prop) (fun _ => by fun_prop)
      (fun y s => by
        have := (((hasDerivAt_id y).const_mul c).mul_const s).cosh
        refine this.congr_deriv ?_; simp; ring) y (|c| * cosh (|c| * (|y| + 1)))
    intro z hz s hs
    rw [abs_mul, abs_mul]
    calc |c| * |s| * |sinh (c * z * s)| ≤ |c| * 1 * cosh (|c| * (|y| + 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs (abs_nonneg c))
            ((abs_sinh_le_cosh _).trans (cosh_le_ball hz hs)) (abs_nonneg _) (by positivity)
      _ = |c| * cosh (|c| * (|y| + 1)) := by ring
  · apply hasDerivAt_kint_loc hg (fun _ => by fun_prop) (fun _ => by fun_prop)
      (fun y s => by
        have := ((((hasDerivAt_id y).const_mul c).mul_const s).sinh.const_mul (c * s))
        refine this.congr_deriv ?_; simp; ring) y (c ^ 2 * cosh (|c| * (|y| + 1)))
    intro z hz s hs
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c), abs_of_nonneg (sq_nonneg s),
      abs_of_nonneg (Real.cosh_pos _).le]
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [abs_nonneg s, sq_abs s]
    calc c ^ 2 * s ^ 2 * cosh (c * z * s) ≤ c ^ 2 * 1 * cosh (|c| * (|y| + 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs2 (sq_nonneg c)) (cosh_le_ball hz hs) (Real.cosh_pos _).le
            (by positivity)
      _ = c ^ 2 * cosh (|c| * (|y| + 1)) := by ring

/-- **The imaginary-axis equation** `(1 + y²)Φ'' + 2yΦ' − (c²y² + χ)Φ = 0`: the kernel `cosh(cys)` has
`L_s cosh(cys) = −M_y cosh(cys)` with `M_y = ∂_y(1 + y²)∂_y − c²y²`, and `SlepianCommutingRelation`'s weighted integration by parts moves
`L_s` onto `g`. -/
theorem imag_ode {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (y : ℝ) :
    (1 + y ^ 2) * phiI₂ c g y + 2 * y * phiI₁ c g y - (c ^ 2 * y ^ 2 + χ) * phiI c g y = 0 := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  unfold phiI phiI₁ phiI₂ kint
  have hK : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => cosh (c * y * s)) (c * y * sinh (c * y * s)) s := by
    intro s _
    have := ((hasDerivAt_id s).const_mul (c * y)).cosh
    refine this.congr_deriv ?_; simp; ring
  have hK₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => c * y * sinh (c * y * s))
      (c ^ 2 * y ^ 2 * cosh (c * y * s)) s := by
    intro s _
    have := ((hasDerivAt_id s).const_mul (c * y)).sinh.const_mul (c * y)
    refine this.congr_deriv ?_; simp; ring
  have ibp := ibp_weighted hg hg₁ hK hK₁ hg₂c (by fun_prop)
  have hi : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable (fun s => g s * f s) MeasureTheory.volume (-1) 1 :=
    fun f hf => hgc.intervalIntegrable.mul_continuousOn hf.continuousOn
  have e : ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 + y ^ 2) * (g s * (c ^ 2 * s ^ 2 * cosh (c * y * s))) + 2 * y * (g s * (c * s * sinh (c * y * s)))
        - (c ^ 2 * y ^ 2 + χ) * (g s * cosh (c * y * s))
      = -(g s * ((1 - s ^ 2) * (c ^ 2 * y ^ 2 * cosh (c * y * s)) - 2 * s * (c * y * sinh (c * y * s))))
        + ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) * cosh (c * y * s) := by
    intro s hs
    have h := hang s hs
    have : ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) = c ^ 2 * s ^ 2 * g s - χ * g s := by linarith
    rw [this]; ring
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add, ← intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_congr e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_neg, ibp]
    · ring
    · exact (hgc.mul (by fun_prop)).neg.intervalIntegrable
    · exact ((((continuousOn_const.sub (continuousOn_id.pow 2)).mul hg₂c).sub
        ((continuousOn_const.mul continuousOn_id).mul hg₁c)).mul (by fun_prop)).intervalIntegrable
  · exact ((hi _ (by fun_prop)).const_mul _).add ((hi _ (by fun_prop)).const_mul _)
  · exact (hi _ (by fun_prop)).const_mul _
  · exact (hi _ (by fun_prop)).const_mul _
  · exact (hi _ (by fun_prop)).const_mul _

/-- `Φ'(0) = 0`. -/
theorem phiI₁_zero (c : ℝ) (g : ℝ → ℝ) : phiI₁ c g 0 = 0 := by
  unfold phiI₁ kint; simp

/-- `Φ(0) = ∫ g = ψ(0)`. -/
theorem phiI_zero (c : ℝ) (g : ℝ → ℝ) : phiI c g 0 = psi c g 0 := by
  unfold phiI psi kint; simp

/-- **`Φ²` is nondecreasing on `[0, ∞)`**: for a solution of `(1 + y²)Φ'' + 2yΦ' = (c²y² + χ)Φ` with `χ ≥ 0` and
`Φ'(0) = 0`, `W = (1 + y²)ΦΦ'` has `W' = (1 + y²)Φ'² + (c²y² + χ)Φ² ≥ 0` and `W(0) = 0`. -/
theorem sq_monotoneOn {Φ Φ₁ Φ₂ : ℝ → ℝ} {c χ : ℝ} (hχ : 0 ≤ χ)
    (h1 : ∀ y, HasDerivAt Φ (Φ₁ y) y) (h2 : ∀ y, HasDerivAt Φ₁ (Φ₂ y) y)
    (hode : ∀ y, (1 + y ^ 2) * Φ₂ y + 2 * y * Φ₁ y - (c ^ 2 * y ^ 2 + χ) * Φ y = 0) (h10 : Φ₁ 0 = 0) :
    MonotoneOn (fun y => Φ y ^ 2) (Ici 0) := by
  -- the monotone flux product
  have hW : ∀ y, HasDerivAt (fun y => (1 + y ^ 2) * Φ y * Φ₁ y)
      ((1 + y ^ 2) * Φ₁ y ^ 2 + (c ^ 2 * y ^ 2 + χ) * Φ y ^ 2) y := by
    intro y
    have hp : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * y) y := by
      simpa using ((hasDerivAt_pow 2 y).const_add 1)
    have := (hp.mul (h1 y)).mul (h2 y)
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply]
    linear_combination Φ y * hode y
  have hWmono : Monotone (fun y => (1 + y ^ 2) * Φ y * Φ₁ y) :=
    monotone_of_hasDerivAt_nonneg hW (fun y => by positivity)
  have hW0 : ∀ y, 0 ≤ y → 0 ≤ Φ y * Φ₁ y := by
    intro y hy
    have hm := hWmono hy
    simp only [h10, mul_zero] at hm
    have hp : 0 < 1 + y ^ 2 := by positivity
    have : 0 ≤ (1 + y ^ 2) * (Φ y * Φ₁ y) := by rw [← mul_assoc]; exact hm
    exact (mul_nonneg_iff_of_pos_left hp).mp this
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => 2 * Φ y * Φ₁ y) (convex_Ici 0)
    (fun y _ => ((h1 y).continuousAt.pow 2).continuousWithinAt) (fun y _ => ?_) (fun y hy => ?_)
  · have := (h1 y).pow 2
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp
  · rw [interior_Ici] at hy
    have := hW0 y (le_of_lt hy)
    linarith

/-- **Zero data at `0` force `Φ = 0` on `[0, Y]`**: `E = Φ² + (1 + y²)Φ'²` has `E' ≤ (1 + c²Y² + χ)E` there, so
`E·e^{−(1 + c²Y² + χ)y}` is antitone from `E(0) = 0`. -/
theorem eq_zero_of_zero_data {Φ Φ₁ Φ₂ : ℝ → ℝ} {c χ : ℝ} (hχ : 0 ≤ χ)
    (h1 : ∀ y, HasDerivAt Φ (Φ₁ y) y) (h2 : ∀ y, HasDerivAt Φ₁ (Φ₂ y) y)
    (hode : ∀ y, (1 + y ^ 2) * Φ₂ y + 2 * y * Φ₁ y - (c ^ 2 * y ^ 2 + χ) * Φ y = 0)
    (h0 : Φ 0 = 0) (h10 : Φ₁ 0 = 0) {Y : ℝ} : ∀ y ∈ Icc 0 Y, Φ y = 0 := by
  set K := 1 + c ^ 2 * Y ^ 2 + χ with hK
  set F : ℝ → ℝ := fun y => (Φ y ^ 2 + (1 + y ^ 2) * Φ₁ y ^ 2) * exp (-(K * y)) with hF
  set F' : ℝ → ℝ := fun y => (2 * Φ y * Φ₁ y * (1 + c ^ 2 * y ^ 2 + χ) - 2 * y * Φ₁ y ^ 2
      - K * (Φ y ^ 2 + (1 + y ^ 2) * Φ₁ y ^ 2)) * exp (-(K * y)) with hF'
  have hFd : ∀ y, HasDerivAt F (F' y) y := by
    intro y
    have hp : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * y) y := by
      simpa using ((hasDerivAt_pow 2 y).const_add 1)
    have hE := ((h1 y).pow 2).add (hp.mul ((h2 y).pow 2))
    have hx : HasDerivAt (fun y => exp (-(K * y))) (exp (-(K * y)) * (-K)) y := by
      have := ((hasDerivAt_id y).const_mul K).neg.exp
      refine this.congr_deriv ?_; simp
    refine (hE.mul hx).congr_deriv ?_
    simp only [hF', Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    linear_combination (2 * Φ₁ y * exp (-(K * y))) * hode y
  have hanti : AntitoneOn F (Icc 0 Y) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := F') (convex_Icc 0 Y)
      (fun y _ => (hFd y).continuousAt.continuousWithinAt) (fun y _ => (hFd y).hasDerivWithinAt) (fun y hy => ?_)
    rw [interior_Icc] at hy
    have hy0 : 0 ≤ y := hy.1.le
    have hyY : y ≤ Y := hy.2.le
    have hcy : c ^ 2 * y ^ 2 ≤ c ^ 2 * Y ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg c); nlinarith
    have hM : 0 ≤ 1 + c ^ 2 * y ^ 2 + χ := by positivity
    have hcs : 2 * Φ y * Φ₁ y ≤ Φ y ^ 2 + Φ₁ y ^ 2 := by nlinarith [sq_nonneg (Φ y - Φ₁ y)]
    have hb : 2 * Φ y * Φ₁ y * (1 + c ^ 2 * y ^ 2 + χ) ≤ (Φ y ^ 2 + Φ₁ y ^ 2) * K := by
      calc 2 * Φ y * Φ₁ y * (1 + c ^ 2 * y ^ 2 + χ) ≤ (Φ y ^ 2 + Φ₁ y ^ 2) * (1 + c ^ 2 * y ^ 2 + χ) :=
            mul_le_mul_of_nonneg_right hcs hM
        _ ≤ (Φ y ^ 2 + Φ₁ y ^ 2) * K := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); rw [hK]; linarith
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have : 2 * Φ y * Φ₁ y * (1 + c ^ 2 * y ^ 2 + χ) - 2 * y * Φ₁ y ^ 2
        - K * (Φ y ^ 2 + (1 + y ^ 2) * Φ₁ y ^ 2) ≤ 0 := by
      nlinarith [mul_nonneg hK0 (mul_nonneg (sq_nonneg y) (sq_nonneg (Φ₁ y))), mul_nonneg hy0 (sq_nonneg (Φ₁ y))]
    simp only [hF']
    exact mul_nonpos_of_nonpos_of_nonneg this (exp_pos _).le
  intro y hy
  have hle := hanti ⟨le_rfl, hy.1.trans hy.2⟩ hy hy.1
  simp only [hF, h0, h10, mul_zero, neg_zero, exp_zero, mul_one] at hle
  have hpos : 0 < exp (-(K * y)) := exp_pos _
  have h2 : Φ y ^ 2 * exp (-(K * y)) ≤ 0 := by
    have : 0 ≤ (1 + y ^ 2) * Φ₁ y ^ 2 * exp (-(K * y)) := by positivity
    nlinarith
  have : Φ y ^ 2 ≤ 0 := by
    by_contra hc
    nlinarith [mul_pos (lt_of_not_ge hc) hpos]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))

/-- **The edge pins the far imaginary axis**: for `g(−1) = g(1)`, `|g'| ≤ G` on `[−1, 1]` and `a = cy > 0`,
`|Φ(y) − 2g(1) sinh a/a| ≤ 2G sinh a/a²` (one integration by parts, then `|sinh| ≤ cosh`). -/
theorem phiI_edge {g g₁ : ℝ → ℝ} {c G y : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁c : ContinuousOn g₁ (uIcc (-1) 1))
    (hev : g (-1) = g 1) (hG : ∀ s ∈ uIcc (-1 : ℝ) 1, |g₁ s| ≤ G) (ha : 0 < c * y) :
    |phiI c g y - 2 * g 1 * sinh (c * y) / (c * y)| ≤ 2 * G * sinh (c * y) / (c * y) ^ 2 := by
  have hphi : phiI c g y = ∫ s in (-1 : ℝ)..1, g s * cosh (c * y * s) := rfl
  rw [hphi]
  set a := c * y with ha_def
  have ha0 : a ≠ 0 := ha.ne'
  have hv : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => sinh (a * s) / a) (cosh (a * s)) s := by
    intro s _
    have := (((hasDerivAt_id s).const_mul a).sinh).div_const a
    refine this.congr_deriv ?_
    field_simp
    simp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg hv hg₁c.intervalIntegrable
    ((by fun_prop : Continuous fun s => cosh (a * s)).intervalIntegrable (-1) 1)
  rw [hibp]
  simp only [mul_one, mul_neg, Real.sinh_neg, hev]
  have hbound : |∫ s in (-1 : ℝ)..1, g₁ s * (sinh (a * s) / a)| ≤ 2 * G * sinh a / a ^ 2 := by
    have h1 : ‖∫ s in (-1 : ℝ)..1, g₁ s * (sinh (a * s) / a)‖ ≤ ∫ s in (-1 : ℝ)..1, G * cosh (a * s) / a := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      · refine Filter.Eventually.of_forall fun s hs => ?_
        have hs' : s ∈ uIcc (-1 : ℝ) 1 := by rw [uIcc_of_le (by norm_num)]; exact ⟨hs.1.le, hs.2⟩
        rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos ha]
        have hGs := hG s hs'
        have h2 := abs_sinh_le_cosh (a * s)
        calc |g₁ s| * (|sinh (a * s)| / a) ≤ G * (cosh (a * s) / a) :=
              mul_le_mul hGs (div_le_div_of_nonneg_right h2 ha.le) (by positivity) ((abs_nonneg _).trans hGs)
          _ = G * cosh (a * s) / a := by ring
      · exact (by fun_prop : Continuous fun s => G * cosh (a * s) / a).intervalIntegrable _ _
    have h3 : ∫ s in (-1 : ℝ)..1, G * cosh (a * s) / a = 2 * G * sinh a / a ^ 2 := by
      have hd : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => G * sinh (a * s) / a ^ 2) (G * cosh (a * s) / a) s := by
        intro s _
        have := ((((hasDerivAt_id s).const_mul a).sinh).const_mul G).div_const (a ^ 2)
        refine this.congr_deriv ?_
        field_simp
        simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((by fun_prop : Continuous fun s => G * cosh (a * s) / a).intervalIntegrable _ _)]
      simp only [mul_one, mul_neg, Real.sinh_neg]
      ring
    rw [← Real.norm_eq_abs]; linarith
  set I := ∫ s in (-1 : ℝ)..1, g₁ s * (sinh (a * s) / a) with hI
  have heq : g 1 * (sinh a / a) - g 1 * (-sinh a / a) - I - 2 * g 1 * sinh a / a = -I := by ring
  rw [heq, abs_neg]
  exact hbound

/-- **The sign law**: for an even angular solution `g ≢ 0` with `c > 0` and `χ ≥ 0`, the cosine transform at the
center has the sign of the edge value: `0 < g(1) ψ(0)`, i.e. `0 < g(1) ∫_{−1}^{1} g`. -/
theorem sign_law {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) :
    0 < g 1 * psi c g 0 := by
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg0
  have hg1 : g 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hang hs₀ hgs₀
  have hev : g (-1) = g 1 := heven 1 ⟨by norm_num, le_rfl⟩
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  obtain ⟨G, hG⟩ := (isCompact_uIcc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hg₁c
  have hG' : ∀ s ∈ uIcc (-1 : ℝ) 1, |g₁ s| ≤ G := fun s hs => by
    have := hG s hs; rwa [Real.norm_eq_abs] at this
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG' 1 (by simp))
  set A := |g 1| with hA
  have hA0 : 0 < A := abs_pos.mpr hg1
  set ystar := (G / A + 1) / c with hys
  have hys0 : 0 < ystar := by positivity
  have hays : c * ystar = G / A + 1 := by rw [hys]; field_simp
  have hapos : 0 < c * ystar := by rw [hays]; positivity
  have hedge := phiI_edge hg hg₁c hev hG' hapos
  -- `g(1) Φ(y*) > 0`
  have hpos : 0 < g 1 * phiI c g ystar := by
    set a := c * ystar with ha_def
    have hsinh : 0 < sinh a := Real.sinh_pos_iff.mpr hapos
    set Φs := phiI c g ystar
    have hT := (abs_le.mp hedge)
    have hAa : G < A * a := by
      rw [hays, mul_add, mul_one, mul_div_cancel₀ _ hA0.ne']; linarith
    have hg1sq : g 1 * g 1 = A * A := by rw [hA, ← abs_mul_abs_self]
    -- g1 Φs = g1 (Φs − T) + g1 T with T = 2 g1 sinh a/a; |g1 (Φs − T)| ≤ A B, B = 2G sinh a/a²
    have hB : |g 1 * (Φs - 2 * g 1 * sinh a / a)| ≤ A * (2 * G * sinh a / a ^ 2) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hedge hA0.le
    have hgT : g 1 * (2 * g 1 * sinh a / a) = 2 * (A * A) * sinh a / a := by
      rw [← hg1sq]; ring
    have hkey : A * (2 * G * sinh a / a ^ 2) < 2 * (A * A) * sinh a / a := by
      have h2 : A * (2 * G * sinh a / a ^ 2) = (2 * sinh a / a ^ 2) * (A * G) := by ring
      have h3 : 2 * (A * A) * sinh a / a = (2 * sinh a / a ^ 2) * (A * (A * a)) := by
        field_simp
      rw [h2, h3]
      exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hAa hA0) (by positivity)
    have := (abs_le.mp hB).1
    have hsplit : g 1 * Φs = g 1 * (Φs - 2 * g 1 * sinh a / a) + g 1 * (2 * g 1 * sinh a / a) := by ring
    rw [hsplit, hgT]
    linarith
  have hd := fun y => phiI_deriv c hgc y
  have hode := imag_ode hg hg₁ hg₂c hang
  rw [← phiI_zero]
  by_cases h0 : phiI c g 0 = 0
  · exfalso
    have hz := eq_zero_of_zero_data hχ (fun y => (hd y).1) (fun y => (hd y).2) hode h0 (phiI₁_zero c g)
      ystar ⟨hys0.le, le_rfl⟩
    rw [hz, mul_zero] at hpos
    exact lt_irrefl _ hpos
  · have hmono := sq_monotoneOn hχ (fun y => (hd y).1) (fun y => (hd y).2) hode (phiI₁_zero c g)
    have hne : ∀ y ∈ Icc 0 ystar, phiI c g y ≠ 0 := by
      intro y hy hz
      have hm := hmono (Set.mem_Ici.mpr le_rfl) hy.1 hy.1
      simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hm
      exact h0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hm (sq_nonneg _)))
    have hsame : 0 < phiI c g 0 * phiI c g ystar := by
      by_contra hneg
      have hle : phiI c g 0 * phiI c g ystar ≤ 0 := le_of_not_gt hneg
      have hcont : ContinuousOn (phiI c g) (uIcc 0 ystar) :=
        fun y _ => (hd y).1.continuousAt.continuousWithinAt
      have h0mem : (0 : ℝ) ∈ uIcc (phiI c g 0) (phiI c g ystar) := by
        rw [Set.mem_uIcc]
        rcases lt_or_gt_of_ne h0 with hlt | hgt
        · left; exact ⟨hlt.le, by nlinarith⟩
        · right; exact ⟨by nlinarith, hgt.le⟩
      obtain ⟨y, hy, hy0⟩ := intermediate_value_uIcc hcont h0mem
      rw [uIcc_of_le hys0.le] at hy
      exact hne y hy hy0
    have hsq : 0 < phiI c g ystar ^ 2 := by
      have := hne ystar ⟨hys0.le, le_rfl⟩
      positivity
    have hprod : 0 < (g 1 * phiI c g 0) * phiI c g ystar ^ 2 := by
      have := mul_pos hpos hsame
      calc (0 : ℝ) < g 1 * phiI c g ystar * (phiI c g 0 * phiI c g ystar) := this
        _ = (g 1 * phiI c g 0) * phiI c g ystar ^ 2 := by ring
    exact (pos_iff_pos_of_mul_pos hprod).mpr hsq

/-- **The sign of the eigenvalue**: with `ψ = μg` on `[−1, 1]`, `0 < μ g(0) g(1)`. -/
theorem mu_sign {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    0 < μ * (g 0 * g 1) := by
  have h := sign_law hc hχ hg hg₁ hg₂c hang heven hg0
  rw [hμ 0 ⟨by norm_num, by norm_num⟩] at h
  linarith [show g 1 * (μ * g 0) = μ * (g 0 * g 1) by ring]

/-- **`hsign` is the edge-center condition**: for such `g` with `ψ = μg`, `0 < ψ(1) g(1) ↔ 0 < g(0) g(1)`. The right
side is a property of `g` alone: `g(0)g(1) > 0` iff `g` has an even number of zeros in `(0, 1)`, i.e. `n ≡ 0 mod 4`
for the `n`-th eigenfunction. -/
theorem hsign_iff {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    0 < psi c g 1 * g 1 ↔ 0 < g 0 * g 1 := by
  have hm := mu_sign hc hχ hg hg₁ hg₂c hang heven hg0 hμ
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg0
  have hg1 : g 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hang hs₀ hgs₀
  have hg1sq : 0 < g 1 * g 1 := mul_self_pos.mpr hg1
  rw [hμ 1 ⟨by norm_num, le_rfl⟩, mul_assoc]
  rw [← pos_iff_pos_of_mul_pos hm]
  constructor
  · intro h; exact (pos_iff_pos_of_mul_pos h).mpr hg1sq
  · intro h; exact mul_pos h hg1sq

/-- **`hsign` from the edge-center sign**, rung by rung, in the form Cvs.L2a.MirrorConcentrationHalf–an earlier result consume. -/
theorem hsign_of_edge {ι : Type*} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ} (hc : 0 < c)
    (hχ0 : ∀ i, 0 ≤ χ i)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hedge : ∀ i, 0 < g i 0 * g i 1) :
    ∀ i, 0 < psi c (g i) 1 * g i 1 := fun i =>
  (hsign_iff hc (hχ0 i) (hg i) (hg₁ i) (hg₂c i) (hang i) (heven i) (hg0 i) (hμ i)).mpr (hedge i)

end Cvs.Prolate.CosineTransformSignLaw
