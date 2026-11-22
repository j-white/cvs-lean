/-
The Single-Atom Path Law — groundwork for the real Fourier basis.

The one remaining input, `exists_maskedRotationModel`, needs a *real* Hilbert
basis of `L²(𝕋)` indexed by `ℤ`. Mathlib's `fourierBasis` is `ℂ`-valued and
stated for `haarAddCircle` rather than `volume`, so it does not apply; the
real trigonometric system has to be built.

This file starts that construction with the two integrals every
orthogonality relation reduces to:

    ∫₀¹ cos(2πk x) dx = 0    and    ∫₀¹ sin(2πk x) dx = 0    (k ≠ 0),

together with the product-to-sum reductions that express
`cos·cos`, `sin·sin` and `cos·sin` in terms of them.

Blocks leaned on: `intervalIntegral.mul_integral_comp_mul_left`,
`integral_cos` / `integral_sin`, `Real.sin_int_mul_pi`,
`Real.cos_int_mul_two_pi`.
-/
import Cvs.PathLaw.Weight

open MeasureTheory Real intervalIntegral

namespace Cvs.PathLaw

/-! ### The two base integrals -/

/-- `∫₀¹ cos(2πk x) dx = 0` for `k ≠ 0`. -/
theorem integral_cos_two_pi (k : ℤ) (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * k * x) = 0 := by
  set c : ℝ := 2 * π * k with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    positivity
  have hmul := mul_integral_comp_mul_left (f := fun x => Real.cos x) (c := c)
    (a := (0 : ℝ)) (b := 1)
  rw [mul_zero, mul_one, integral_cos] at hmul
  have hsin : Real.sin c = 0 := by
    rw [hc, show (2 : ℝ) * π * k = (2 * k : ℤ) * π by push_cast; ring]
    exact Real.sin_int_mul_pi (2 * k)
  rw [hsin, Real.sin_zero, sub_zero] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left hcne

/-- `∫₀¹ sin(2πk x) dx = 0` for `k ≠ 0`. -/
theorem integral_sin_two_pi (k : ℤ) (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * π * k * x) = 0 := by
  set c : ℝ := 2 * π * k with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    positivity
  have hmul := mul_integral_comp_mul_left (f := fun x => Real.sin x) (c := c)
    (a := (0 : ℝ)) (b := 1)
  rw [mul_zero, mul_one, integral_sin] at hmul
  have hcos : Real.cos c = 1 := by
    rw [hc, show (2 : ℝ) * π * k = (k : ℤ) * (2 * π) by ring]
    exact Real.cos_int_mul_two_pi k
  rw [hcos, Real.cos_zero, sub_self] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left hcne

/-! ### Product-to-sum

Every orthogonality relation for the real system follows from the two
integrals above after rewriting a product of trigonometric functions as a
sum. -/

theorem cos_mul_cos_eq (a b : ℝ) :
    Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

theorem sin_mul_sin_eq (a b : ℝ) :
    Real.sin a * Real.sin b = (Real.cos (a - b) - Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

theorem cos_mul_sin_eq (a b : ℝ) :
    Real.cos a * Real.sin b = (Real.sin (a + b) - Real.sin (a - b)) / 2 := by
  rw [Real.sin_add, Real.sin_sub]
  ring

/-! ### Orthogonality of the real trigonometric system -/

/-- The sine integral vanishes for every `k`, including `k = 0`. -/
theorem integral_sin_two_pi' (k : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * π * k * x) = 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · exact integral_sin_two_pi k hk

/-- The cosine integral is `1` at `k = 0` and `0` otherwise. -/
theorem integral_cos_two_pi' (k : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * k * x) = if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [if_neg hk]
    exact integral_cos_two_pi k hk

private lemma intIntegrable_cos (k : ℤ) :
    IntervalIntegrable (fun x => Real.cos (2 * π * k * x)) volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

private lemma intIntegrable_sin (k : ℤ) :
    IntervalIntegrable (fun x => Real.sin (2 * π * k * x)) volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- **Cosine–cosine orthogonality.** -/
theorem integral_cos_mul_cos (m n : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * m * x) * Real.cos (2 * π * n * x)
      = ((if m - n = 0 then 1 else 0) + (if m + n = 0 then 1 else 0)) / 2 := by
  have hpt : ∀ x : ℝ, Real.cos (2 * π * m * x) * Real.cos (2 * π * n * x)
      = (Real.cos (2 * π * ((m - n : ℤ) : ℝ) * x)
          + Real.cos (2 * π * ((m + n : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have h1 : 2 * π * ((m - n : ℤ) : ℝ) * x = 2 * π * m * x - 2 * π * n * x := by
      push_cast; ring
    have h2 : 2 * π * ((m + n : ℤ) : ℝ) * x = 2 * π * m * x + 2 * π * n * x := by
      push_cast; ring
    rw [h1, h2]
    exact cos_mul_cos_eq _ _
  rw [integral_congr (fun x _ => hpt x)]
  rw [intervalIntegral.integral_div, integral_add (intIntegrable_cos (m - n)) (intIntegrable_cos (m + n)),
    integral_cos_two_pi' (m - n), integral_cos_two_pi' (m + n)]

/-- **Sine–sine orthogonality.** -/
theorem integral_sin_mul_sin (m n : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * π * m * x) * Real.sin (2 * π * n * x)
      = ((if m - n = 0 then 1 else 0) - (if m + n = 0 then 1 else 0)) / 2 := by
  have hpt : ∀ x : ℝ, Real.sin (2 * π * m * x) * Real.sin (2 * π * n * x)
      = (Real.cos (2 * π * ((m - n : ℤ) : ℝ) * x)
          - Real.cos (2 * π * ((m + n : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have h1 : 2 * π * ((m - n : ℤ) : ℝ) * x = 2 * π * m * x - 2 * π * n * x := by
      push_cast; ring
    have h2 : 2 * π * ((m + n : ℤ) : ℝ) * x = 2 * π * m * x + 2 * π * n * x := by
      push_cast; ring
    rw [h1, h2]
    exact sin_mul_sin_eq _ _
  rw [integral_congr (fun x _ => hpt x)]
  rw [intervalIntegral.integral_div, integral_sub (intIntegrable_cos (m - n)) (intIntegrable_cos (m + n)),
    integral_cos_two_pi' (m - n), integral_cos_two_pi' (m + n)]

/-- **Cosine–sine orthogonality**: always zero. -/
theorem integral_cos_mul_sin (m n : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * m * x) * Real.sin (2 * π * n * x) = 0 := by
  have hpt : ∀ x : ℝ, Real.cos (2 * π * m * x) * Real.sin (2 * π * n * x)
      = (Real.sin (2 * π * ((m + n : ℤ) : ℝ) * x)
          - Real.sin (2 * π * ((m - n : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have h1 : 2 * π * ((m - n : ℤ) : ℝ) * x = 2 * π * m * x - 2 * π * n * x := by
      push_cast; ring
    have h2 : 2 * π * ((m + n : ℤ) : ℝ) * x = 2 * π * m * x + 2 * π * n * x := by
      push_cast; ring
    rw [h1, h2]
    exact cos_mul_sin_eq _ _
  rw [integral_congr (fun x _ => hpt x)]
  rw [intervalIntegral.integral_div, integral_sub (intIntegrable_sin (m + n)) (intIntegrable_sin (m - n)),
    integral_sin_two_pi' (m + n), integral_sin_two_pi' (m - n)]
  norm_num

/-! ### The trigonometric system on the circle

`cos(2πnx)` and `sin(2πnx)` are `1`-periodic, so they descend to
`AddCircle 1` via `Function.Periodic.lift`. Orthogonality then transfers from
the interval by `AddCircle.integral_preimage`. -/

theorem periodic_cos_two_pi (n : ℤ) :
    Function.Periodic (fun x : ℝ => Real.cos (2 * π * n * x)) 1 := by
  intro x
  show Real.cos (2 * π * (n : ℝ) * (x + 1)) = Real.cos (2 * π * (n : ℝ) * x)
  have h : 2 * π * (n : ℝ) * (x + 1) = 2 * π * n * x + (n : ℤ) * (2 * π) := by
    ring
  rw [h, Real.cos_add_int_mul_two_pi]

theorem periodic_sin_two_pi (n : ℤ) :
    Function.Periodic (fun x : ℝ => Real.sin (2 * π * n * x)) 1 := by
  intro x
  show Real.sin (2 * π * (n : ℝ) * (x + 1)) = Real.sin (2 * π * (n : ℝ) * x)
  have h : 2 * π * (n : ℝ) * (x + 1) = 2 * π * n * x + (n : ℤ) * (2 * π) := by
    ring
  rw [h, Real.sin_add_int_mul_two_pi]

/-- `cos(2πn·)` as a function on the circle. -/
noncomputable def rCos (n : ℤ) : AddCircle (1 : ℝ) → ℝ := (periodic_cos_two_pi n).lift

/-- `sin(2πn·)` as a function on the circle. -/
noncomputable def rSin (n : ℤ) : AddCircle (1 : ℝ) → ℝ := (periodic_sin_two_pi n).lift

@[simp] theorem rCos_coe (n : ℤ) (x : ℝ) :
    rCos n ((x : ℝ) : AddCircle (1 : ℝ)) = Real.cos (2 * π * n * x) :=
  (periodic_cos_two_pi n).lift_coe x

@[simp] theorem rSin_coe (n : ℤ) (x : ℝ) :
    rSin n ((x : ℝ) : AddCircle (1 : ℝ)) = Real.sin (2 * π * n * x) :=
  (periodic_sin_two_pi n).lift_coe x

/-- Transfer an integral over the circle to the unit interval. -/
theorem integral_circle_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AddCircle (1 : ℝ) → E) :
    ∫ z : AddCircle (1 : ℝ), f z
      = ∫ x in (0 : ℝ)..1, f ((x : ℝ) : AddCircle (1 : ℝ)) := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← AddCircle.integral_preimage (1 : ℝ) 0 f]
  simp

/-! ### Orthogonality on the circle -/

theorem integral_rCos_rCos (m n : ℤ) :
    ∫ z : AddCircle (1 : ℝ), rCos m z * rCos n z
      = ((if m - n = 0 then 1 else 0) + (if m + n = 0 then 1 else 0)) / 2 := by
  rw [integral_circle_eq]
  simp only [rCos_coe]
  exact integral_cos_mul_cos m n

theorem integral_rSin_rSin (m n : ℤ) :
    ∫ z : AddCircle (1 : ℝ), rSin m z * rSin n z
      = ((if m - n = 0 then 1 else 0) - (if m + n = 0 then 1 else 0)) / 2 := by
  rw [integral_circle_eq]
  simp only [rSin_coe]
  exact integral_sin_mul_sin m n

theorem integral_rCos_rSin (m n : ℤ) :
    ∫ z : AddCircle (1 : ℝ), rCos m z * rSin n z = 0 := by
  rw [integral_circle_eq]
  simp only [rCos_coe, rSin_coe]
  exact integral_cos_mul_sin m n

/-! ### First moments and the normalised system -/

theorem integral_rCos (n : ℤ) :
    ∫ z : AddCircle (1 : ℝ), rCos n z = if n = 0 then 1 else 0 := by
  rw [integral_circle_eq]
  simp only [rCos_coe]
  exact integral_cos_two_pi' n

theorem integral_rSin (n : ℤ) :
    ∫ z : AddCircle (1 : ℝ), rSin n z = 0 := by
  rw [integral_circle_eq]
  simp only [rSin_coe]
  exact integral_sin_two_pi' n

/-- The circle has total mass one, so the constant `1` is already normalised. -/
theorem integral_one_circle :
    ∫ _z : AddCircle (1 : ℝ), (1 : ℝ) = 1 := by
  rw [integral_circle_eq]
  simp

/-- The real trigonometric system, indexed by `ℤ`: the constant at `0`,
cosines at positive indices, sines at negative ones, each normalised. -/
noncomputable def trigFun (n : ℤ) : AddCircle (1 : ℝ) → ℝ :=
  if n = 0 then (fun _ => 1)
  else if 0 < n then (fun z => Real.sqrt 2 * rCos n z)
  else (fun z => Real.sqrt 2 * rSin (-n) z)

theorem trigFun_zero : trigFun 0 = fun _ => 1 := by
  unfold trigFun; simp

theorem trigFun_pos {n : ℤ} (hn : 0 < n) :
    trigFun n = fun z => Real.sqrt 2 * rCos n z := by
  unfold trigFun
  rw [if_neg (ne_of_gt hn), if_pos hn]

theorem trigFun_neg {n : ℤ} (hn : n < 0) :
    trigFun n = fun z => Real.sqrt 2 * rSin (-n) z := by
  unfold trigFun
  rw [if_neg (ne_of_lt hn), if_neg (not_lt.mpr hn.le)]

/-- Pointwise description through the canonical representative. -/
theorem rCos_eq_rep (n : ℤ) (z : AddCircle (1 : ℝ)) :
    rCos n z = Real.cos (2 * π * n * rep z) := by
  conv_lhs => rw [← coe_rep z]
  exact rCos_coe n (rep z)

theorem rSin_eq_rep (n : ℤ) (z : AddCircle (1 : ℝ)) :
    rSin n z = Real.sin (2 * π * n * rep z) := by
  conv_lhs => rw [← coe_rep z]
  exact rSin_coe n (rep z)

theorem measurable_rCos (n : ℤ) : Measurable (rCos n) := by
  have h : rCos n = fun z => Real.cos (2 * π * (n : ℝ) * rep z) :=
    funext (rCos_eq_rep n)
  rw [h]
  exact Real.continuous_cos.measurable.comp (measurable_rep.const_mul _)

theorem measurable_rSin (n : ℤ) : Measurable (rSin n) := by
  have h : rSin n = fun z => Real.sin (2 * π * (n : ℝ) * rep z) :=
    funext (rSin_eq_rep n)
  rw [h]
  exact Real.continuous_sin.measurable.comp (measurable_rep.const_mul _)

theorem measurable_trigFun (n : ℤ) : Measurable (trigFun n) := by
  unfold trigFun
  split_ifs
  · exact measurable_const
  · exact (measurable_rCos n).const_mul _
  · exact (measurable_rSin (-n)).const_mul _

/-- Every member is bounded by `√2`. -/
theorem abs_trigFun_le (n : ℤ) (z : AddCircle (1 : ℝ)) :
    |trigFun n z| ≤ Real.sqrt 2 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold trigFun
  split_ifs
  · simp
  · rw [abs_mul, abs_of_nonneg hs2]
    have : |rCos n z| ≤ 1 := by
      rw [rCos_eq_rep]
      exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    nlinarith
  · rw [abs_mul, abs_of_nonneg hs2]
    have : |rSin (-n) z| ≤ 1 := by
      rw [rSin_eq_rep]
      exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    nlinarith

theorem memLp_trigFun (n : ℤ) :
    MemLp (trigFun n) 2 (volume : Measure (AddCircle (1 : ℝ))) := by
  refine MemLp.of_bound (measurable_trigFun n).aestronglyMeasurable (Real.sqrt 2) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  exact abs_trigFun_le n z

/-- The trigonometric system as elements of `L²(𝕋)`. -/
noncomputable def trigLp (n : ℤ) : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ))) :=
  MemLp.toLp _ (memLp_trigFun n)

theorem coeFn_trigLp (n : ℤ) :
    (trigLp n : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] trigFun n :=
  MemLp.coeFn_toLp _

/-! ### Orthonormality

The nine sign cases of the pair `(m, n)`. In every mixed case the integral
vanishes; in the matching cases the `√2` normalisation is exactly what turns
the value `1/2` into `1`. -/

theorem integral_trigFun_mul (m n : ℤ) :
    ∫ z : AddCircle (1 : ℝ), trigFun m z * trigFun n z
      = if m = n then 1 else 0 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rcases lt_trichotomy m 0 with hm | hm | hm <;>
    rcases lt_trichotomy n 0 with hn | hn | hn
  -- m < 0, n < 0
  · rw [trigFun_neg hm, trigFun_neg hn]
    have hpt : ∀ z : AddCircle (1 : ℝ),
        (Real.sqrt 2 * rSin (-m) z) * (Real.sqrt 2 * rSin (-n) z)
          = 2 * (rSin (-m) z * rSin (-n) z) := by
      intro z
      calc (Real.sqrt 2 * rSin (-m) z) * (Real.sqrt 2 * rSin (-n) z)
          = (Real.sqrt 2 * Real.sqrt 2) * (rSin (-m) z * rSin (-n) z) := by ring
        _ = 2 * (rSin (-m) z * rSin (-n) z) := by rw [hs]
    simp only [hpt]
    rw [MeasureTheory.integral_const_mul, integral_rSin_rSin, if_neg (by omega : ¬(-m + -n = 0))]
    by_cases hmn : m = n
    · rw [if_pos hmn, if_pos (by omega : -m - -n = 0)]; ring
    · rw [if_neg hmn, if_neg (by omega : ¬(-m - -n = 0))]; ring
  -- m < 0, n = 0
  · subst hn
    rw [trigFun_neg hm, trigFun_zero, if_neg (by omega : ¬(m = 0))]
    simp only [mul_one]
    rw [MeasureTheory.integral_const_mul, integral_rSin, mul_zero]
  -- m < 0, n > 0
  · rw [trigFun_neg hm, trigFun_pos hn, if_neg (by omega : ¬(m = n))]
    have hpt : ∀ z : AddCircle (1 : ℝ),
        (Real.sqrt 2 * rSin (-m) z) * (Real.sqrt 2 * rCos n z)
          = 2 * (rCos n z * rSin (-m) z) := by
      intro z
      calc (Real.sqrt 2 * rSin (-m) z) * (Real.sqrt 2 * rCos n z)
          = (Real.sqrt 2 * Real.sqrt 2) * (rCos n z * rSin (-m) z) := by ring
        _ = 2 * (rCos n z * rSin (-m) z) := by rw [hs]
    simp only [hpt]
    rw [MeasureTheory.integral_const_mul, integral_rCos_rSin, mul_zero]
  -- m = 0, n < 0
  · subst hm
    rw [trigFun_zero, trigFun_neg hn, if_neg (by omega : ¬((0 : ℤ) = n))]
    simp only [one_mul]
    rw [MeasureTheory.integral_const_mul, integral_rSin, mul_zero]
  -- m = 0, n = 0
  · subst hm; subst hn
    rw [trigFun_zero, if_pos rfl]
    simpa using integral_one_circle
  -- m = 0, n > 0
  · subst hm
    rw [trigFun_zero, trigFun_pos hn, if_neg (by omega : ¬((0 : ℤ) = n))]
    simp only [one_mul]
    rw [MeasureTheory.integral_const_mul, integral_rCos, if_neg (by omega : ¬(n = 0)), mul_zero]
  -- m > 0, n < 0
  · rw [trigFun_pos hm, trigFun_neg hn, if_neg (by omega : ¬(m = n))]
    have hpt : ∀ z : AddCircle (1 : ℝ),
        (Real.sqrt 2 * rCos m z) * (Real.sqrt 2 * rSin (-n) z)
          = 2 * (rCos m z * rSin (-n) z) := by
      intro z
      calc (Real.sqrt 2 * rCos m z) * (Real.sqrt 2 * rSin (-n) z)
          = (Real.sqrt 2 * Real.sqrt 2) * (rCos m z * rSin (-n) z) := by ring
        _ = 2 * (rCos m z * rSin (-n) z) := by rw [hs]
    simp only [hpt]
    rw [MeasureTheory.integral_const_mul, integral_rCos_rSin, mul_zero]
  -- m > 0, n = 0
  · subst hn
    rw [trigFun_pos hm, trigFun_zero, if_neg (by omega : ¬(m = 0))]
    simp only [mul_one]
    rw [MeasureTheory.integral_const_mul, integral_rCos, if_neg (by omega : ¬(m = 0)), mul_zero]
  -- m > 0, n > 0
  · rw [trigFun_pos hm, trigFun_pos hn]
    have hpt : ∀ z : AddCircle (1 : ℝ),
        (Real.sqrt 2 * rCos m z) * (Real.sqrt 2 * rCos n z)
          = 2 * (rCos m z * rCos n z) := by
      intro z
      calc (Real.sqrt 2 * rCos m z) * (Real.sqrt 2 * rCos n z)
          = (Real.sqrt 2 * Real.sqrt 2) * (rCos m z * rCos n z) := by ring
        _ = 2 * (rCos m z * rCos n z) := by rw [hs]
    simp only [hpt]
    rw [MeasureTheory.integral_const_mul, integral_rCos_rCos, if_neg (by omega : ¬(m + n = 0))]
    by_cases hmn : m = n
    · rw [if_pos hmn, if_pos (by omega : m - n = 0)]; ring
    · rw [if_neg hmn, if_neg (by omega : ¬(m - n = 0))]; ring

/-- The `L²` inner product of two members of the system. -/
theorem inner_trigLp (m n : ℤ) :
    inner ℝ (trigLp m) (trigLp n) = if m = n then 1 else 0 := by
  rw [L2.inner_def]
  have hcongr : ∫ z, inner ℝ ((trigLp m : AddCircle (1 : ℝ) → ℝ) z)
        ((trigLp n : AddCircle (1 : ℝ) → ℝ) z)
      = ∫ z, trigFun m z * trigFun n z := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_trigLp m, coeFn_trigLp n] with z h1 h2
    rw [RCLike.inner_apply, h1, h2, starRingEnd_apply, star_trivial]
    ring
  rw [hcongr, integral_trigFun_mul]

/-- **The real trigonometric system is orthonormal in `L²(𝕋)`.** -/
theorem orthonormal_trigLp : Orthonormal ℝ trigLp := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_trigLp]

/-! ### Toward completeness

A `HilbertBasis` needs orthonormality (above) plus density of the span.
Density will come from Mathlib's complex Fourier basis. Two mismatches have
to be bridged: the scalars (`ℝ` vs `ℂ`) and the measure (`volume` vs
`haarAddCircle`). The second is not really a mismatch at all — at period `1`
the two measures coincide. -/

/-- At period `1` the circle's volume *is* the normalised Haar measure. -/
theorem volume_eq_haar :
    (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  norm_num

/-- A real `L²` function, viewed as a complex one, is still `L²`. -/
theorem memLp_ofReal (f : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))) :
    MemLp (fun z => ((f : AddCircle (1 : ℝ) → ℝ) z : ℂ)) 2
      (volume : Measure (AddCircle (1 : ℝ))) := by
  have h := Lp.memLp (Complex.ofRealCLM.compLp (p := 2)
    (μ := (volume : Measure (AddCircle (1 : ℝ)))) f)
  refine h.ae_eq ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLp' (Complex.ofRealCLM) f] with z hz
  rw [hz]
  rfl

/-- The same statement with respect to the Haar measure. -/
theorem memLp_ofReal_haar (f : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))) :
    MemLp (fun z => ((f : AddCircle (1 : ℝ) → ℝ) z : ℂ)) 2
      (AddCircle.haarAddCircle (T := (1 : ℝ))) := by
  rw [← volume_eq_haar]
  exact memLp_ofReal f

/-- The complexification of a real `L²` element, as an element of the complex
`L²` space that Mathlib's Fourier basis lives in. -/
noncomputable def toC (f : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  MemLp.toLp _ (memLp_ofReal_haar f)

theorem coeFn_toC (f : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))) :
    (toC f : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z => ((f : AddCircle (1 : ℝ) → ℝ) z : ℂ) :=
  MemLp.coeFn_toLp _

/-! ### Fourier monomials in terms of the real system -/

/-- The conjugate Fourier monomial, expanded into real trigonometric parts. -/
theorem fourier_neg_eq (n : ℤ) (t : AddCircle (1 : ℝ)) :
    fourier (-n) t = (rCos n t : ℂ) - Complex.I * (rSin n t : ℂ) := by
  conv_lhs => rw [← coe_rep t]
  rw [fourier_coe_apply, rCos_eq_rep, rSin_eq_rep]
  have harg : (2 * (π : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * ((rep t : ℝ) : ℂ)
        / ((1 : ℝ) : ℂ))
      = ((-(2 * π * (n : ℝ) * rep t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-! ### Parity -/

theorem rCos_neg (n : ℤ) (t : AddCircle (1 : ℝ)) : rCos (-n) t = rCos n t := by
  rw [rCos_eq_rep, rCos_eq_rep]
  rw [show 2 * π * ((-n : ℤ) : ℝ) * rep t = -(2 * π * (n : ℝ) * rep t) by push_cast; ring]
  exact Real.cos_neg _

theorem rSin_neg (n : ℤ) (t : AddCircle (1 : ℝ)) : rSin (-n) t = -rSin n t := by
  rw [rSin_eq_rep, rSin_eq_rep]
  rw [show 2 * π * ((-n : ℤ) : ℝ) * rep t = -(2 * π * (n : ℝ) * rep t) by push_cast; ring]
  exact Real.sin_neg _

theorem rCos_zero (t : AddCircle (1 : ℝ)) : rCos 0 t = 1 := by
  rw [rCos_eq_rep]
  norm_num

theorem rSin_zero (t : AddCircle (1 : ℝ)) : rSin 0 t = 0 := by
  rw [rSin_eq_rep]
  norm_num

/-! ### Orthogonality as vanishing real integrals -/

variable {f : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))}

/-- Orthogonality to `trigLp k`, restated as an integral. -/
theorem integral_trigFun_mul_f (h : ∀ k : ℤ, inner ℝ (trigLp k) f = 0) (k : ℤ) :
    ∫ t, trigFun k t * (f : AddCircle (1 : ℝ) → ℝ) t = 0 := by
  have hk := h k
  rw [L2.inner_def] at hk
  rw [← hk]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_trigLp k] with t ht
  rw [RCLike.inner_apply, ht, starRingEnd_apply, star_trivial]
  ring

private lemma cancel_sqrt2 {a : ℝ} (h : Real.sqrt 2 * a = 0) : a = 0 := by
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp h).resolve_left hs2

theorem integral_rCos_mul (h : ∀ k : ℤ, inner ℝ (trigLp k) f = 0) (n : ℤ) :
    ∫ t, rCos n t * (f : AddCircle (1 : ℝ) → ℝ) t = 0 := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hb := integral_trigFun_mul_f h (-n)
    rw [trigFun_pos (by omega : 0 < -n)] at hb
    simp only [] at hb
    have hre : ∀ t : AddCircle (1 : ℝ),
        Real.sqrt 2 * rCos (-n) t * (f : AddCircle (1 : ℝ) → ℝ) t
          = Real.sqrt 2 * (rCos n t * (f : AddCircle (1 : ℝ) → ℝ) t) := by
      intro t; rw [rCos_neg]; ring
    simp only [hre] at hb
    rw [MeasureTheory.integral_const_mul] at hb
    exact cancel_sqrt2 hb
  · subst hn
    have hb := integral_trigFun_mul_f h 0
    rw [trigFun_zero] at hb
    simp only [one_mul] at hb
    rw [← hb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show rCos 0 t * (f : AddCircle (1 : ℝ) → ℝ) t = (f : AddCircle (1 : ℝ) → ℝ) t
    rw [rCos_zero, one_mul]
  · have hb := integral_trigFun_mul_f h n
    rw [trigFun_pos hn] at hb
    simp only [] at hb
    have hre : ∀ t : AddCircle (1 : ℝ),
        Real.sqrt 2 * rCos n t * (f : AddCircle (1 : ℝ) → ℝ) t
          = Real.sqrt 2 * (rCos n t * (f : AddCircle (1 : ℝ) → ℝ) t) := by
      intro t; ring
    simp only [hre] at hb
    rw [MeasureTheory.integral_const_mul] at hb
    exact cancel_sqrt2 hb

theorem integral_rSin_mul (h : ∀ k : ℤ, inner ℝ (trigLp k) f = 0) (n : ℤ) :
    ∫ t, rSin n t * (f : AddCircle (1 : ℝ) → ℝ) t = 0 := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hb := integral_trigFun_mul_f h n
    rw [trigFun_neg hn] at hb
    simp only [] at hb
    have hre : ∀ t : AddCircle (1 : ℝ),
        Real.sqrt 2 * rSin (-n) t * (f : AddCircle (1 : ℝ) → ℝ) t
          = Real.sqrt 2 * (-(rSin n t * (f : AddCircle (1 : ℝ) → ℝ) t)) := by
      intro t; rw [rSin_neg]; ring
    simp only [hre] at hb
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_neg] at hb
    have := cancel_sqrt2 hb
    linarith
  · subst hn
    simp only [rSin_zero, zero_mul]
    simp
  · have hb := integral_trigFun_mul_f h (-n)
    rw [trigFun_neg (by omega : -n < 0)] at hb
    simp only [neg_neg] at hb
    have hre : ∀ t : AddCircle (1 : ℝ),
        Real.sqrt 2 * rSin n t * (f : AddCircle (1 : ℝ) → ℝ) t
          = Real.sqrt 2 * (rSin n t * (f : AddCircle (1 : ℝ) → ℝ) t) := by
      intro t; ring
    simp only [hre] at hb
    rw [MeasureTheory.integral_const_mul] at hb
    exact cancel_sqrt2 hb

/-! ### The Fourier coefficients of the complexification -/

theorem integrable_rCos_mul (g : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ))))
    (n : ℤ) :
    Integrable (fun t => rCos n t * (g : AddCircle (1 : ℝ) → ℝ) t) volume := by
  have hg : Integrable (g : AddCircle (1 : ℝ) → ℝ) volume :=
    (Lp.memLp g).integrable (by norm_num)
  refine hg.bdd_mul (measurable_rCos n).aestronglyMeasurable (c := 1) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, rCos_eq_rep]
  exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem integrable_rSin_mul (g : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ))))
    (n : ℤ) :
    Integrable (fun t => rSin n t * (g : AddCircle (1 : ℝ) → ℝ) t) volume := by
  have hg : Integrable (g : AddCircle (1 : ℝ) → ℝ) volume :=
    (Lp.memLp g).integrable (by norm_num)
  refine hg.bdd_mul (measurable_rSin n).aestronglyMeasurable (c := 1) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, rSin_eq_rep]
  exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- **All Fourier coefficients of the complexification vanish.** -/
theorem fourierCoeff_toC_eq_zero (h : ∀ k : ℤ, inner ℝ (trigLp k) f = 0) (n : ℤ) :
    fourierCoeff (toC f : AddCircle (1 : ℝ) → ℂ) n = 0 := by
  unfold fourierCoeff
  -- first rewrite the integrand, still against the Haar measure
  have hcongr : ∫ t, fourier (-n) t • (toC f : AddCircle (1 : ℝ) → ℂ) t
        ∂AddCircle.haarAddCircle
      = ∫ t, (((rCos n t * (f : AddCircle (1 : ℝ) → ℝ) t : ℝ) : ℂ)
          - Complex.I * ((rSin n t * (f : AddCircle (1 : ℝ) → ℝ) t : ℝ) : ℂ))
          ∂AddCircle.haarAddCircle := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toC f] with t ht
    rw [smul_eq_mul, ht, fourier_neg_eq]
    push_cast
    ring
  rw [hcongr]
  -- integrability and vanishing, transported to the Haar measure
  have hA : Integrable
      (fun t => ((rCos n t * (f : AddCircle (1 : ℝ) → ℝ) t : ℝ) : ℂ))
      AddCircle.haarAddCircle := by
    rw [← volume_eq_haar]
    exact (integrable_rCos_mul f n).ofReal
  have hB : Integrable
      (fun t => Complex.I * ((rSin n t * (f : AddCircle (1 : ℝ) → ℝ) t : ℝ) : ℂ))
      AddCircle.haarAddCircle := by
    rw [← volume_eq_haar]
    exact ((integrable_rSin_mul f n).ofReal).const_mul Complex.I
  have hR : ∫ t, rCos n t * (f : AddCircle (1 : ℝ) → ℝ) t
      ∂AddCircle.haarAddCircle = 0 := by
    rw [← volume_eq_haar]
    exact integral_rCos_mul h n
  have hS : ∫ t, rSin n t * (f : AddCircle (1 : ℝ) → ℝ) t
      ∂AddCircle.haarAddCircle = 0 := by
    rw [← volume_eq_haar]
    exact integral_rSin_mul h n
  rw [integral_sub hA hB, MeasureTheory.integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, hR, hS]
  simp

/-! ### Completeness -/

theorem toC_eq_zero (h : ∀ k : ℤ, inner ℝ (trigLp k) f = 0) : toC f = 0 := by
  have hrepr : (fourierBasis (T := (1 : ℝ))).repr (toC f) = 0 := by
    ext n
    rw [fourierBasis_repr]
    simpa using fourierCoeff_toC_eq_zero h n
  have hb := congrArg (fourierBasis (T := (1 : ℝ))).repr.symm hrepr
  rwa [LinearIsometryEquiv.symm_apply_apply, map_zero] at hb

/-- **A vector orthogonal to the whole trigonometric system is zero.** -/
theorem eq_zero_of_orthogonal_trigLp
    (h : ∀ k : ℤ, inner ℝ (trigLp k) f = 0) : f = 0 := by
  have h0 := toC_eq_zero h
  have h1 := coeFn_toC f
  rw [h0] at h1
  have h2 : (fun z => ((f : AddCircle (1 : ℝ) → ℝ) z : ℂ))
      =ᵐ[AddCircle.haarAddCircle] 0 :=
    h1.symm.trans (Lp.coeFn_zero ℂ 2 _)
  have h3 : (fun z => ((f : AddCircle (1 : ℝ) → ℝ) z : ℂ)) =ᵐ[volume] 0 := by
    rw [← volume_eq_haar] at h2
    exact h2
  have hae : (f : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] 0 := by
    filter_upwards [h3] with z hz
    show (f : AddCircle (1 : ℝ) → ℝ) z = 0
    have hz' : ((f : AddCircle (1 : ℝ) → ℝ) z : ℂ) = 0 := hz
    exact_mod_cast hz'
  exact Lp.ext (hae.trans (Lp.coeFn_zero ℝ 2 _).symm)

/-- **The real trigonometric Hilbert basis of `L²(𝕋)`, indexed by `ℤ`.**

This is the object Mathlib does not provide: its `fourierBasis` is
`ℂ`-valued. With it, the DTFT needed by `exists_maskedRotationModel` becomes
available over the reals. -/
noncomputable def trigBasis :
    HilbertBasis ℤ ℝ (Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_trigLp (by
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine eq_zero_of_orthogonal_trigLp (fun k => ?_)
    exact hx (trigLp k) (Submodule.subset_span ⟨k, rfl⟩))

@[simp] theorem coe_trigBasis : ⇑trigBasis = trigLp :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

end Cvs.PathLaw
