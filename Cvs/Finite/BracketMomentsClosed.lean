import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.LevyExpMoments
import Cvs.Finite.LevyKernelIncrement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exponential moments of the bracket, in closed form

A decaying exponential against a cosine, a sine, or the lag times a cosine has an elementary
antiderivative, and at twice the window the lattice cosine returns to one; beyond it the cut
kernel is zero and only the exponential's own tail remains, so each moment of the bracket is a
rational function of the pole and the frequency times one exponential factor.
-/

noncomputable section

open Real MeasureTheory Set

namespace Cvs.Finite.BracketMomentsClosed

open Cvs.Finite.CosineModeOverlap Cvs.Finite.LevyKernelIncrement Cvs.Finite.LevyExpMoments

/-! ### Three antiderivatives -/

/-- Antiderivative of `exp (−a u) cos (b u)`. -/
def expCos (a b : ℝ) : ℝ → ℝ := fun u =>
  Real.exp (-(a * u)) * (-a * Real.cos (b * u) + b * Real.sin (b * u)) / (a ^ 2 + b ^ 2)

/-- Antiderivative of `exp (−a u) sin (b u)`. -/
def expSin (a b : ℝ) : ℝ → ℝ := fun u =>
  Real.exp (-(a * u)) * (-a * Real.sin (b * u) - b * Real.cos (b * u)) / (a ^ 2 + b ^ 2)

/-- Antiderivative of `u exp (−a u) cos (b u)`. -/
def uExpCos (a b : ℝ) : ℝ → ℝ := fun u =>
  u * expCos a b u
    - Real.exp (-(a * u)) * ((a ^ 2 - b ^ 2) * Real.cos (b * u) - 2 * a * b * Real.sin (b * u))
      / (a ^ 2 + b ^ 2) ^ 2

theorem hasDerivAt_expCos {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) (u : ℝ) :
    HasDerivAt (expCos a b) (Real.exp (-(a * u)) * Real.cos (b * u)) u := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-(a * t))) (Real.exp (-(a * u)) * (-a)) u := by
    have := (((hasDerivAt_id u).const_mul a).neg).exp
    simpa using this
  have hb : HasDerivAt (fun t : ℝ => b * t) b u := by simpa using (hasDerivAt_id u).const_mul b
  have hin : HasDerivAt (fun t : ℝ => -a * Real.cos (b * t) + b * Real.sin (b * t))
      (-a * (-Real.sin (b * u) * b) + b * (Real.cos (b * u) * b)) u :=
    (hb.cos.const_mul (-a)).add (hb.sin.const_mul b)
  have hd : (Real.exp (-(a * u)) * (-a) * (-a * Real.cos (b * u) + b * Real.sin (b * u))
        + Real.exp (-(a * u)) * (-a * (-Real.sin (b * u) * b) + b * (Real.cos (b * u) * b)))
        / (a ^ 2 + b ^ 2) = Real.exp (-(a * u)) * Real.cos (b * u) := by
    rw [div_eq_iff h]; ring
  rw [← hd]
  exact (he.mul hin).div_const _

theorem hasDerivAt_expSin {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) (u : ℝ) :
    HasDerivAt (expSin a b) (Real.exp (-(a * u)) * Real.sin (b * u)) u := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-(a * t))) (Real.exp (-(a * u)) * (-a)) u := by
    have := (((hasDerivAt_id u).const_mul a).neg).exp
    simpa using this
  have hb : HasDerivAt (fun t : ℝ => b * t) b u := by simpa using (hasDerivAt_id u).const_mul b
  have hin : HasDerivAt (fun t : ℝ => -a * Real.sin (b * t) - b * Real.cos (b * t))
      (-a * (Real.cos (b * u) * b) - b * (-Real.sin (b * u) * b)) u :=
    (hb.sin.const_mul (-a)).sub (hb.cos.const_mul b)
  have hd : (Real.exp (-(a * u)) * (-a) * (-a * Real.sin (b * u) - b * Real.cos (b * u))
        + Real.exp (-(a * u)) * (-a * (Real.cos (b * u) * b) - b * (-Real.sin (b * u) * b)))
        / (a ^ 2 + b ^ 2) = Real.exp (-(a * u)) * Real.sin (b * u) := by
    rw [div_eq_iff h]; ring
  rw [← hd]
  exact (he.mul hin).div_const _

theorem hasDerivAt_uExpCos {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) (u : ℝ) :
    HasDerivAt (uExpCos a b) (u * (Real.exp (-(a * u)) * Real.cos (b * u))) u := by
  have h1 : HasDerivAt (fun t : ℝ => t * expCos a b t)
      (1 * expCos a b u + u * (Real.exp (-(a * u)) * Real.cos (b * u))) u :=
    (hasDerivAt_id u).mul (hasDerivAt_expCos h u)
  have he : HasDerivAt (fun t : ℝ => Real.exp (-(a * t))) (Real.exp (-(a * u)) * (-a)) u := by
    have := (((hasDerivAt_id u).const_mul a).neg).exp
    simpa using this
  have hb : HasDerivAt (fun t : ℝ => b * t) b u := by simpa using (hasDerivAt_id u).const_mul b
  have hin : HasDerivAt (fun t : ℝ => (a ^ 2 - b ^ 2) * Real.cos (b * t) - 2 * a * b * Real.sin (b * t))
      ((a ^ 2 - b ^ 2) * (-Real.sin (b * u) * b) - 2 * a * b * (Real.cos (b * u) * b)) u :=
    (hb.cos.const_mul _).sub (hb.sin.const_mul _)
  have h2 := (he.mul hin).div_const ((a ^ 2 + b ^ 2) ^ 2)
  have hsum := h1.sub h2
  have hd : 1 * expCos a b u + u * (Real.exp (-(a * u)) * Real.cos (b * u))
      - (Real.exp (-(a * u)) * (-a) * ((a ^ 2 - b ^ 2) * Real.cos (b * u) - 2 * a * b * Real.sin (b * u))
        + Real.exp (-(a * u)) * ((a ^ 2 - b ^ 2) * (-Real.sin (b * u) * b) - 2 * a * b * (Real.cos (b * u) * b)))
        / (a ^ 2 + b ^ 2) ^ 2
      = u * (Real.exp (-(a * u)) * Real.cos (b * u)) := by
    unfold expCos
    have h2' : (a ^ 2 + b ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h
    field_simp
    ring
  rw [← hd]
  exact hsum

/-! ### Their integrals over the window at a lattice frequency -/

theorem cos_lattice {L : ℝ} (hL : L ≠ 0) (m : ℤ) : Real.cos (π * m / L * (2 * L)) = 1 := by
  rw [show π * m / L * (2 * L) = (m : ℤ) * (2 * π) by field_simp, Real.cos_int_mul_two_pi]

theorem sin_lattice {L : ℝ} (hL : L ≠ 0) (m : ℤ) : Real.sin (π * m / L * (2 * L)) = 0 := by
  rw [show π * m / L * (2 * L) = ((2 * m : ℤ) : ℝ) * π by field_simp; push_cast; ring,
    Real.sin_int_mul_pi]

theorem integral_exp_cos_lattice {a L : ℝ} (ha : 0 < a) (hL : 0 < L) (m : ℤ) :
    (∫ u in (0:ℝ)..(2 * L), Real.exp (-(a * u)) * Real.cos (π * m / L * u))
      = a * (1 - Real.exp (-(a * (2 * L)))) / (a ^ 2 + (π * m / L) ^ 2) := by
  have h : a ^ 2 + (π * m / L) ^ 2 ≠ 0 := by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_expCos h u)
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(a * u)) * Real.cos (π * m / L * u))
      |>.intervalIntegrable _ _)]
  unfold expCos
  rw [cos_lattice hL.ne', sin_lattice hL.ne']
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, mul_one, add_zero,
    one_mul]
  field_simp
  ring

theorem integral_exp_sin_lattice {a L : ℝ} (ha : 0 < a) (hL : 0 < L) (m : ℤ) :
    (∫ u in (0:ℝ)..(2 * L), Real.exp (-(a * u)) * Real.sin (π * m / L * u))
      = (π * m / L) * (1 - Real.exp (-(a * (2 * L)))) / (a ^ 2 + (π * m / L) ^ 2) := by
  have h : a ^ 2 + (π * m / L) ^ 2 ≠ 0 := by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_expSin h u)
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(a * u)) * Real.sin (π * m / L * u))
      |>.intervalIntegrable _ _)]
  unfold expSin
  rw [cos_lattice hL.ne', sin_lattice hL.ne']
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, mul_one, one_mul,
    zero_sub]
  field_simp
  ring

theorem integral_mul_exp_cos_lattice {a L : ℝ} (ha : 0 < a) (hL : 0 < L) (m : ℤ) :
    (∫ u in (0:ℝ)..(2 * L), u * (Real.exp (-(a * u)) * Real.cos (π * m / L * u)))
      = (a ^ 2 - (π * m / L) ^ 2) * (1 - Real.exp (-(a * (2 * L)))) / (a ^ 2 + (π * m / L) ^ 2) ^ 2
        - 2 * L * a * Real.exp (-(a * (2 * L))) / (a ^ 2 + (π * m / L) ^ 2) := by
  have h : a ^ 2 + (π * m / L) ^ 2 ≠ 0 := by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_uExpCos h u)
    ((by fun_prop : Continuous fun u : ℝ => u * (Real.exp (-(a * u)) * Real.cos (π * m / L * u)))
      |>.intervalIntegrable _ _)]
  unfold uExpCos expCos
  rw [cos_lattice hL.ne', sin_lattice hL.ne']
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, mul_one, add_zero,
    one_mul, zero_mul, zero_sub, sub_zero]
  field_simp
  ring

/-! ### The tail beyond twice the window, and the split -/

theorem integral_exp_neg_Ioi_scaled {a T : ℝ} (ha : 0 < a) :
    ∫ u in Ioi T, Real.exp (-(a * u)) = Real.exp (-(a * T)) / a := by
  have := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) T ha
  rw [integral_exp_neg_Ioi] at this
  rw [this, smul_eq_mul, div_eq_inv_mul]

theorem integrableOn_exp_neg_mul_Ioi {a T : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => Real.exp (-(a * u))) (Ioi T) volume := by
  have := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x)) T ha).mpr
    (integrableOn_exp_neg_Ioi (a * T))
  exact this

/-- The kernel's branch at a fixed pair is continuous in the lag. -/
theorem continuous_K (L : ℝ) (m n : ℤ) : Continuous (K L m n) := by
  unfold K
  split_ifs <;> fun_prop

/-- **The moment splits at twice the window**: the window part against the kernel, plus the
constant's own exponential tail. -/
theorem moment_split {L : ℝ} (hL : 0 < L) (m n : ℤ) (k : ℕ) :
    Cvs.Finite.LevyExpMoments.moment L m n k
      = (∫ u in (0:ℝ)..(2 * L), Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - K L m n (u / 2)))
        + K L m n 0 * (Real.exp (-((1 / 4 + (k : ℝ)) * (2 * L))) / (1 / 4 + (k : ℝ))) := by
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by positivity
  unfold Cvs.Finite.LevyExpMoments.moment
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : (0:ℝ) ≤ 2 * L)]
  have hdisj : Disjoint (Ioc (0:ℝ) (2 * L)) (Ioi (2 * L)) := by
    rw [Set.disjoint_left]; intro u hu hu'; exact absurd hu.2 (not_le.mpr hu')
  have hf1 : ∀ u ∈ Ioc (0:ℝ) (2 * L),
      Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - Kc L m n (u / 2))
        = Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - K L m n (u / 2)) := by
    intro u hu; rw [Kc_of_le (by linarith [hu.2])]
  have hf2 : ∀ u ∈ Ioi (2 * L),
      Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - Kc L m n (u / 2))
        = K L m n 0 * Real.exp (-((1 / 4 + (k : ℝ)) * u)) := by
    intro u hu
    have : (2 * L : ℝ) < u := hu
    rw [Kc_of_gt (by linarith), sub_zero]; ring
  have hi1 : IntegrableOn (fun u : ℝ => Real.exp (-((1 / 4 + (k : ℝ)) * u))
      * (K L m n 0 - Kc L m n (u / 2))) (Ioc 0 (2 * L)) volume := by
    refine IntegrableOn.congr_fun ?_ (fun u hu => (hf1 u hu).symm) measurableSet_Ioc
    have hc : Continuous fun u : ℝ => Real.exp (-((1 / 4 + (k : ℝ)) * u))
        * (K L m n 0 - K L m n (u / 2)) :=
      (by fun_prop : Continuous fun u : ℝ => Real.exp (-((1 / 4 + (k : ℝ)) * u))).mul
        (continuous_const.sub ((continuous_K L m n).comp (continuous_id.div_const 2)))
    exact hc.integrableOn_Ioc
  have hi2 : IntegrableOn (fun u : ℝ => Real.exp (-((1 / 4 + (k : ℝ)) * u))
      * (K L m n 0 - Kc L m n (u / 2))) (Ioi (2 * L)) volume := by
    refine IntegrableOn.congr_fun ?_ (fun u hu => (hf2 u hu).symm) measurableSet_Ioi
    exact (integrableOn_exp_neg_mul_Ioi ha).const_mul _
  rw [setIntegral_union hdisj measurableSet_Ioi hi1 hi2,
    setIntegral_congr_fun measurableSet_Ioc hf1, setIntegral_congr_fun measurableSet_Ioi hf2,
    ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 2 * L),
    integral_const_mul, integral_exp_neg_Ioi_scaled ha]

/-! ### The two branches -/

theorem integral_exp_lattice {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    (∫ u in (0:ℝ)..(2 * L), Real.exp (-(a * u))) = (1 - Real.exp (-(a * (2 * L)))) / a := by
  have h := integral_exp_cos_lattice ha hL 0
  simp only [Int.cast_zero, mul_zero, zero_div, zero_mul, Real.cos_zero, mul_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  rw [h]
  field_simp

/-- **The diagonal moment**, with `b = π m / L`. -/
theorem moment_diag {L : ℝ} (hL : 0 < L) (m : ℤ) (k : ℕ) :
    Cvs.Finite.LevyExpMoments.moment L m m k
      = 2 * (π * m / L) ^ 2 / ((1 / 4 + (k : ℝ)) * ((1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2))
        + ((1 / 4 + (k : ℝ)) ^ 2 - (π * m / L) ^ 2)
            * (1 - Real.exp (-((1 / 4 + (k : ℝ)) * (2 * L))))
            / (L * ((1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2) ^ 2) := by
  rw [moment_split hL m m k]
  have hK0 : K L m m 0 = 2 := by
    simp only [K, if_true, mul_zero, zero_div, sub_zero, mul_one, Real.cos_zero]
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by positivity
  have hI1 := integral_exp_lattice ha hL
  have hI2 := integral_exp_cos_lattice ha hL m
  have hI3 := integral_mul_exp_cos_lattice ha hL m
  have hpt : ∀ u : ℝ, Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m m 0 - K L m m (u / 2))
      = 2 * Real.exp (-((1 / 4 + (k : ℝ)) * u))
        - 2 * (Real.exp (-((1 / 4 + (k : ℝ)) * u)) * Real.cos (π * m / L * u))
        + (1 / L) * (u * (Real.exp (-((1 / 4 + (k : ℝ)) * u)) * Real.cos (π * m / L * u))) := by
    intro u
    rw [hK0]
    simp only [K, if_true]
    have e : 2 * π * m * (u / 2) / L = π * m / L * u := by ring
    rw [e]
    field_simp
    ring
  rw [intervalIntegral.integral_congr (fun u _ => hpt u), intervalIntegral.integral_add,
    intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI1, hI2, hI3, hK0]
  · generalize hadef : (1 / 4 + (k : ℝ)) = a at ha ⊢
    generalize hbdef : (π * m / L) = b
    have h : a ^ 2 + b ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

/-- **The off-diagonal moment.** -/
theorem moment_off {L : ℝ} (hL : 0 < L) {m n : ℤ} (hmn : m ≠ n) (k : ℕ) :
    Cvs.Finite.LevyExpMoments.moment L m n k
      = -((1 - Real.exp (-((1 / 4 + (k : ℝ)) * (2 * L))))
          * ((π * m / L) / ((1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2)
            - (π * n / L) / ((1 / 4 + (k : ℝ)) ^ 2 + (π * n / L) ^ 2)))
        / (π * ((n : ℝ) - m)) := by
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by positivity
  rw [moment_split hL m n k]
  have hK0 : K L m n 0 = 0 := by
    simp only [K, if_neg hmn, mul_zero, zero_div, Real.sin_zero, sub_zero]
  have hnm : ((n : ℝ) - m) ≠ 0 := by
    have : (n : ℝ) ≠ m := by exact_mod_cast hmn.symm
    exact sub_ne_zero.mpr this
  have hpt : ∀ u : ℝ, Real.exp (-((1 / 4 + (k : ℝ)) * u)) * (K L m n 0 - K L m n (u / 2))
      = -(1 / (π * ((n : ℝ) - m)))
        * (Real.exp (-((1 / 4 + (k : ℝ)) * u)) * Real.sin (π * m / L * u)
          - Real.exp (-((1 / 4 + (k : ℝ)) * u)) * Real.sin (π * n / L * u)) := by
    intro u
    rw [hK0]
    simp only [K, if_neg hmn]
    have e1 : 2 * π * m * (u / 2) / L = π * m / L * u := by ring
    have e2 : 2 * π * n * (u / 2) / L = π * n / L * u := by ring
    rw [e1, e2]
    field_simp
    ring
  rw [intervalIntegral.integral_congr (fun u _ => hpt u), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub, integral_exp_sin_lattice ha hL m,
    integral_exp_sin_lattice ha hL n, hK0]
  · generalize hadef : (1 / 4 + (k : ℝ)) = a at ha ⊢
    field_simp
    ring
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

end Cvs.Finite.BracketMomentsClosed
