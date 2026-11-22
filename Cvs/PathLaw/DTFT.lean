/-
The Single-Atom Path Law — the DTFT matrix computation.

In the Fourier basis, the matrix of the masked rotation is the Loewner
divided-difference matrix: the Fourier-side form of Lemma 2.1 of the paper.

In the normalisation used here the circle has circumference `1`, the rotation
step is `β = y/L`, and the Fourier monomials are `fourier n z = e^{2πinφ}`.
The paper's angle is `α = 2π(1-β)`, and `sin(αm) = -sin(2πβm)`, which is why
the signs work out.

This file builds the exponential integrals the computation reduces to.
-/
import Cvs.PathLaw.Complexify

open MeasureTheory Real intervalIntegral

namespace Cvs.PathLaw

/-! ### Exponential integrals over an interval -/

/-- The frequency constant is nonzero for a nonzero index. -/
theorem two_pi_I_mul_ne_zero {k : ℤ} (hk : k ≠ 0) :
    (2 * (π : ℂ) * Complex.I * (k : ℂ)) ≠ 0 := by
  have h1 : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have h2 : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨⟨⟨two_ne_zero, h1⟩, Complex.I_ne_zero⟩, h2⟩

/-- `∫_a^b e^{2πikφ} dφ` in closed form, for `k ≠ 0`. -/
theorem integral_expc (k : ℤ) (hk : k ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))
      = (Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (b : ℂ))
          - Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (a : ℂ)))
        / (2 * (π : ℂ) * Complex.I * (k : ℂ)) :=
  integral_exp_mul_complex (two_pi_I_mul_ne_zero hk)

/-- At `k = 0` the integrand is constant. -/
theorem integral_expc_zero (a b : ℝ) :
    (∫ x in a..b, Complex.exp (2 * (π : ℂ) * Complex.I * ((0 : ℤ) : ℂ) * (x : ℂ)))
      = ((b - a : ℝ) : ℂ) := by
  simp

/-- A Fourier monomial, in exponential form on the unit circle. -/
theorem fourier_eq_exp (n : ℤ) (x : ℝ) :
    fourier n ((x : ℝ) : AddCircle (1 : ℝ))
      = Complex.exp (2 * (π : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) := by
  rw [fourier_coe_apply]
  norm_num

/-- `e^{2πik}` is `1`. -/
theorem exp_two_pi_I_int (k : ℤ) :
    Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ)) = 1 := by
  rw [show 2 * (π : ℂ) * Complex.I * (k : ℂ) = (k : ℂ) * (2 * (π : ℂ) * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-! ### The two masked intervals

The forward mask is `[0, 1-β)` and the backward mask is `[β, 1)` in the
normalised coordinate, so the matrix element is a sum of two exponential
integrals over those intervals. -/

theorem integral_expc_fwd (k : ℤ) (hk : k ≠ 0) (β : ℝ) :
    (∫ x in (0 : ℝ)..(1 - β),
        Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))
      = (Complex.exp (-(2 * (π : ℂ) * Complex.I * (k : ℂ) * (β : ℂ))) - 1)
        / (2 * (π : ℂ) * Complex.I * (k : ℂ)) := by
  rw [integral_expc k hk]
  congr 1
  · congr 1
    · rw [show (2 * (π : ℂ) * Complex.I * (k : ℂ) * ((1 - β : ℝ) : ℂ))
          = 2 * (π : ℂ) * Complex.I * (k : ℂ)
            + -(2 * (π : ℂ) * Complex.I * (k : ℂ) * (β : ℂ)) by push_cast; ring,
        Complex.exp_add, exp_two_pi_I_int, one_mul]
    · simp

theorem integral_expc_bwd (k : ℤ) (hk : k ≠ 0) (β : ℝ) :
    (∫ x in (β : ℝ)..1,
        Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))
      = (1 - Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (β : ℂ)))
        / (2 * (π : ℂ) * Complex.I * (k : ℂ)) := by
  rw [integral_expc k hk]
  congr 1
  congr 1
  rw [show (2 * (π : ℂ) * Complex.I * (k : ℂ) * ((1 : ℝ) : ℂ))
      = 2 * (π : ℂ) * Complex.I * (k : ℂ) by push_cast; ring, exp_two_pi_I_int]

/-! ### Euler -/

/-- `e^{iθ} - e^{-iθ} = 2i sin θ` for real `θ`. -/
theorem exp_sub_exp_neg (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp (-((θ : ℂ) * Complex.I))
      = 2 * Complex.I * ((Real.sin θ : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, show -((θ : ℂ) * Complex.I) = (-(θ : ℂ)) * Complex.I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  push_cast
  ring

/-! ### Fourier algebra -/

/-- The Fourier monomial is a homomorphism in its *argument*. -/
theorem fourier_arg_add (m : ℤ) (x y : AddCircle (1 : ℝ)) :
    fourier m (x + y) = fourier m x * fourier m y := by
  simp_rw [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- `e_m · conj e_n = e_{m-n}`. -/
theorem fourier_mul_conj (m n : ℤ) (x : AddCircle (1 : ℝ)) :
    fourier m x * (starRingEnd ℂ) (fourier n x) = fourier (m - n) x := by
  rw [sub_eq_add_neg, fourier_add, fourier_neg]

/-! ### Integrals of a Fourier monomial over the two masks -/

private lemma ae_ne_one : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
  rw [MeasureTheory.ae_iff]
  simp

/-- `∫ 1_{maskFwd} · e_k` over the circle equals `∫₀^{1-β} e^{2πikφ} dφ`. -/
theorem integral_maskFwd_fourier (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℤ) :
    (∫ z : AddCircle (1 : ℝ), (maskFwd β).indicator (fun w => fourier k w) z)
      = ∫ x in (0 : ℝ)..(1 - β),
          Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)) := by
  rw [integral_circle_eq, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 1 - β)]
  have hcongr : (∫ x in Set.Ioc (0 : ℝ) 1,
        (maskFwd β).indicator (fun w => fourier k w) ((x : ℝ) : AddCircle (1 : ℝ)))
      = ∫ x in Set.Ioc (0 : ℝ) 1, (Set.Iio (1 - β)).indicator
          (fun y => Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (y : ℂ))) x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae ae_ne_one] with x hx hx1
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    by_cases hc : x < 1 - β
    · have hmem : ((x : ℝ) : AddCircle (1 : ℝ)) ∈ maskFwd β := by
        show rep ((x : ℝ) : AddCircle (1 : ℝ)) + β < 1
        rw [rep_coe x hx0 hxlt]
        linarith
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (Set.mem_Iio.mpr hc),
        fourier_eq_exp]
    · have hnm : ((x : ℝ) : AddCircle (1 : ℝ)) ∉ maskFwd β := by
        show ¬(rep ((x : ℝ) : AddCircle (1 : ℝ)) + β < 1)
        rw [rep_coe x hx0 hxlt]
        push Not
        push Not at hc
        linarith
      rw [Set.indicator_of_notMem hnm,
        Set.indicator_of_notMem (by simpa using hc)]
  rw [hcongr, MeasureTheory.integral_indicator measurableSet_Iio,
    MeasureTheory.Measure.restrict_restrict measurableSet_Iio,
    show Set.Iio (1 - β) ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioo (0 : ℝ) (1 - β) by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, by linarith⟩,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- `∫ 1_{maskBwd} · e_k` over the circle equals `∫_β^1 e^{2πikφ} dφ`. -/
theorem integral_maskBwd_fourier (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℤ) :
    (∫ z : AddCircle (1 : ℝ), (maskBwd β).indicator (fun w => fourier k w) z)
      = ∫ x in (β : ℝ)..1,
          Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)) := by
  rw [integral_circle_eq, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by linarith : (β : ℝ) ≤ 1)]
  have hcongr : (∫ x in Set.Ioc (0 : ℝ) 1,
        (maskBwd β).indicator (fun w => fourier k w) ((x : ℝ) : AddCircle (1 : ℝ)))
      = ∫ x in Set.Ioc (0 : ℝ) 1, (Set.Ici β).indicator
          (fun y => Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (y : ℂ))) x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae ae_ne_one] with x hx hx1
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    by_cases hc : β ≤ x
    · have hmem : ((x : ℝ) : AddCircle (1 : ℝ)) ∈ maskBwd β := by
        show β ≤ rep ((x : ℝ) : AddCircle (1 : ℝ))
        rw [rep_coe x hx0 hxlt]
        exact hc
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (Set.mem_Ici.mpr hc),
        fourier_eq_exp]
    · have hnm : ((x : ℝ) : AddCircle (1 : ℝ)) ∉ maskBwd β := by
        show ¬(β ≤ rep ((x : ℝ) : AddCircle (1 : ℝ)))
        rw [rep_coe x hx0 hxlt]
        exact hc
      rw [Set.indicator_of_notMem hnm,
        Set.indicator_of_notMem (by simpa using hc)]
  rw [hcongr, MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ici,
    show Set.Ici β ∩ Set.Ioc (0 : ℝ) 1 = Set.Icc β 1 by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by linarith, h2⟩,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]


/-! ### Reduction of the matrix element -/

private lemma indicator_mul {α : Type*} (s : Set α) (f g : α → ℂ) (z : α) :
    s.indicator f z * g z = s.indicator (fun w => f w * g w) z := by
  by_cases h : z ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

private lemma const_mul_indicator {α : Type*} (s : Set α) (c : ℂ) (f : α → ℂ) (z : α) :
    s.indicator (fun w => c * f w) z = c * s.indicator f z := by
  by_cases h : z ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

theorem norm_fourier_eq_one (k : ℤ) (z : AddCircle (1 : ℝ)) :
    ‖fourier k z‖ = 1 := Circle.norm_coe _

theorem integrable_indicator_fourier (s : Set (AddCircle (1 : ℝ)))
    (hs : MeasurableSet s) (k : ℤ) :
    Integrable (s.indicator (fun w => fourier k w))
      (volume : Measure (AddCircle (1 : ℝ))) := by
  refine (MemLp.of_bound (p := 1) ?_ 1 ?_).integrable le_rfl
  · exact (((map_continuous (fourier k)).measurable).indicator hs).aestronglyMeasurable
  · filter_upwards with z
    by_cases h : z ∈ s
    · rw [Set.indicator_of_mem h, norm_fourier_eq_one]
    · rw [Set.indicator_of_notMem h, norm_zero]
      norm_num

/-- **The matrix element, reduced to two exponential integrals.** -/
theorem integral_maskedRotation_fourier (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (m n : ℤ) :
    (∫ z : AddCircle (1 : ℝ),
        ((maskFwd β).indicator
            (fun w => fourier m (w + ((β : ℝ) : AddCircle (1 : ℝ)))) z
          + (maskBwd β).indicator
            (fun w => fourier m (w + -((β : ℝ) : AddCircle (1 : ℝ)))) z)
        * (starRingEnd ℂ) (fourier n z))
      = fourier m ((β : ℝ) : AddCircle (1 : ℝ))
          * (∫ x in (0 : ℝ)..(1 - β),
              Complex.exp (2 * (π : ℂ) * Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ)))
        + fourier m (-((β : ℝ) : AddCircle (1 : ℝ)))
          * (∫ x in (β : ℝ)..1,
              Complex.exp (2 * (π : ℂ) * Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ))) := by
  set bc := ((β : ℝ) : AddCircle (1 : ℝ)) with hbc
  have hpt : ∀ z : AddCircle (1 : ℝ),
      ((maskFwd β).indicator (fun w => fourier m (w + bc)) z
        + (maskBwd β).indicator (fun w => fourier m (w + -bc)) z)
        * (starRingEnd ℂ) (fourier n z)
      = fourier m bc * (maskFwd β).indicator (fun w => fourier (m - n) w) z
        + fourier m (-bc) * (maskBwd β).indicator (fun w => fourier (m - n) w) z := by
    intro z
    rw [add_mul,
      indicator_mul (maskFwd β) (fun w => fourier m (w + bc))
        (fun w => (starRingEnd ℂ) (fourier n w)) z,
      indicator_mul (maskBwd β) (fun w => fourier m (w + -bc))
        (fun w => (starRingEnd ℂ) (fourier n w)) z]
    congr 1
    · rw [← const_mul_indicator]
      congr 1
      funext w
      rw [fourier_arg_add, mul_comm (fourier m w) (fourier m bc), mul_assoc,
        fourier_mul_conj]
    · rw [← const_mul_indicator]
      congr 1
      funext w
      rw [fourier_arg_add, mul_comm (fourier m w) (fourier m (-bc)), mul_assoc,
        fourier_mul_conj]
  simp only [hpt]
  rw [MeasureTheory.integral_add
      ((integrable_indicator_fourier _ (measurableSet_maskFwd β) (m - n)).const_mul _)
      ((integrable_indicator_fourier _ (measurableSet_maskBwd β) (m - n)).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_maskFwd_fourier β hβ0 hβ1, integral_maskBwd_fourier β hβ0 hβ1]

/-! ### Evaluating the matrix element -/

/-- The rotation phase, in exponential form. -/
theorem fourier_beta (m : ℤ) (β : ℝ) :
    fourier m ((β : ℝ) : AddCircle (1 : ℝ))
      = Complex.exp (((2 * π * (m : ℝ) * β : ℝ) : ℂ) * Complex.I) := by
  rw [fourier_eq_exp]
  congr 1
  push_cast
  ring

theorem fourier_neg_beta (m : ℤ) (β : ℝ) :
    fourier m (-((β : ℝ) : AddCircle (1 : ℝ)))
      = Complex.exp (-(((2 * π * (m : ℝ) * β : ℝ) : ℂ) * Complex.I)) := by
  rw [show -((β : ℝ) : AddCircle (1 : ℝ)) = ((-β : ℝ) : AddCircle (1 : ℝ)) by
      rw [AddCircle.coe_neg], fourier_eq_exp]
  congr 1
  push_cast
  ring

/-- The exponentials appearing in the two interval integrals, in the same form. -/
theorem expc_beta (k : ℤ) (β : ℝ) :
    Complex.exp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (β : ℂ))
      = Complex.exp (((2 * π * (k : ℝ) * β : ℝ) : ℂ) * Complex.I) := by
  congr 1
  push_cast
  ring

theorem expc_neg_beta (k : ℤ) (β : ℝ) :
    Complex.exp (-(2 * (π : ℂ) * Complex.I * (k : ℂ) * (β : ℂ)))
      = Complex.exp (-(((2 * π * (k : ℝ) * β : ℝ) : ℂ) * Complex.I)) := by
  congr 1
  push_cast
  ring

/-- **The off-diagonal matrix element** is the Loewner divided difference. -/
theorem matrix_element_offdiag (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (m n : ℤ)
    (hmn : m ≠ n) :
    (∫ z : AddCircle (1 : ℝ),
        ((maskFwd β).indicator
            (fun w => fourier m (w + ((β : ℝ) : AddCircle (1 : ℝ)))) z
          + (maskBwd β).indicator
            (fun w => fourier m (w + -((β : ℝ) : AddCircle (1 : ℝ)))) z)
        * (starRingEnd ℂ) (fourier n z))
      = (((Real.sin (2 * π * (n : ℝ) * β) - Real.sin (2 * π * (m : ℝ) * β))
            / (π * ((m : ℝ) - (n : ℝ))) : ℝ) : ℂ) := by
  have hk : (m - n : ℤ) ≠ 0 := sub_ne_zero.mpr hmn
  have hmnC : ((m - n : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hD : (2 * (π : ℂ) * Complex.I * ((m - n : ℤ) : ℂ)) ≠ 0 :=
    two_pi_I_mul_ne_zero hk
  rw [integral_maskedRotation_fourier β hβ0 hβ1, integral_expc_fwd _ hk,
    integral_expc_bwd _ hk, fourier_beta, fourier_neg_beta, expc_beta, expc_neg_beta]
  -- combine the exponentials
  have e1 : Complex.exp (((2 * π * (m : ℝ) * β : ℝ) : ℂ) * Complex.I)
      * Complex.exp (-(((2 * π * ((m - n : ℤ) : ℝ) * β : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((2 * π * (n : ℝ) * β : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : Complex.exp (-(((2 * π * (m : ℝ) * β : ℝ) : ℂ) * Complex.I))
      * Complex.exp (((2 * π * ((m - n : ℤ) : ℝ) * β : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-(((2 * π * (n : ℝ) * β : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- combine over the common denominator, then apply Euler
  have hnum : Complex.exp (((2 * π * (m : ℝ) * β : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (-(((2 * π * ((m - n : ℤ) : ℝ) * β : ℝ) : ℂ) * Complex.I)) - 1)
      + Complex.exp (-(((2 * π * (m : ℝ) * β : ℝ) : ℂ) * Complex.I))
        * (1 - Complex.exp (((2 * π * ((m - n : ℤ) : ℝ) * β : ℝ) : ℂ) * Complex.I))
      = (Complex.exp (((2 * π * (n : ℝ) * β : ℝ) : ℂ) * Complex.I)
          - Complex.exp (-(((2 * π * (n : ℝ) * β : ℝ) : ℂ) * Complex.I)))
        - (Complex.exp (((2 * π * (m : ℝ) * β : ℝ) : ℂ) * Complex.I)
          - Complex.exp (-(((2 * π * (m : ℝ) * β : ℝ) : ℂ) * Complex.I))) := by
    linear_combination e1 - e2
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, hnum, exp_sub_exp_neg,
    exp_sub_exp_neg]
  push_cast
  field_simp

/-- `e^{iθ} + e^{-iθ} = 2 cos θ` for real `θ`. -/
theorem exp_add_exp_neg (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (-((θ : ℂ) * Complex.I))
      = 2 * ((Real.cos θ : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, show -((θ : ℂ) * Complex.I) = (-(θ : ℂ)) * Complex.I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  push_cast
  ring

/-- **The diagonal matrix element.** -/
theorem matrix_element_diag (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (m : ℤ) :
    (∫ z : AddCircle (1 : ℝ),
        ((maskFwd β).indicator
            (fun w => fourier m (w + ((β : ℝ) : AddCircle (1 : ℝ)))) z
          + (maskBwd β).indicator
            (fun w => fourier m (w + -((β : ℝ) : AddCircle (1 : ℝ)))) z)
        * (starRingEnd ℂ) (fourier m z))
      = ((2 * (1 - β) * Real.cos (2 * π * (m : ℝ) * β) : ℝ) : ℂ) := by
  rw [integral_maskedRotation_fourier β hβ0 hβ1, sub_self, integral_expc_zero,
    integral_expc_zero, fourier_beta, fourier_neg_beta]
  have hc := exp_add_exp_neg (2 * π * (m : ℝ) * β)
  push_cast
  push_cast at hc
  linear_combination ((1 : ℂ) - (β : ℂ)) * hc

/-! ### The paper's angle `α = 2π(1-β)` -/

theorem cos_alpha (β : ℝ) (m : ℤ) :
    Real.cos (2 * π * (1 - β) * (m : ℝ)) = Real.cos (2 * π * (m : ℝ) * β) := by
  rw [show 2 * π * (1 - β) * (m : ℝ) = (m : ℤ) * (2 * π) - 2 * π * (m : ℝ) * β by
    ring]
  exact Real.cos_int_mul_two_pi_sub _ m

theorem sin_alpha (β : ℝ) (m : ℤ) :
    Real.sin (2 * π * (1 - β) * (m : ℝ)) = -Real.sin (2 * π * (m : ℝ) * β) := by
  rw [show 2 * π * (1 - β) * (m : ℝ) = (m : ℤ) * (2 * π) - 2 * π * (m : ℝ) * β by
    ring]
  exact Real.sin_int_mul_two_pi_sub _ m

/-! ### The matrix element is the Loewner entry -/

/-- `atomEntry` rewritten in terms of the normalised step `β = log q / log c`,
using `cos(α·) = cos(2π·β)` and `sin(α·) = -sin(2π·β)` for `α = 2π(1-β)`. -/
theorem atomEntry_eq (q c : ℕ) (m n : ℤ) :
    atomEntry q c n m
      = weight q * (if n = m then
            2 * (1 - Real.log q / Real.log c)
              * Real.cos (2 * π * (n : ℝ) * (Real.log q / Real.log c))
          else (Real.sin (2 * π * (n : ℝ) * (Real.log q / Real.log c))
              - Real.sin (2 * π * (m : ℝ) * (Real.log q / Real.log c)))
            / (π * ((m : ℝ) - (n : ℝ)))) := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  unfold atomEntry
  simp only []
  by_cases hmn : n = m
  · subst hmn
    rw [if_pos rfl, if_pos rfl, cos_alpha]
    congr 1
    field_simp
  · rw [if_neg hmn, if_neg hmn, sin_alpha, sin_alpha]
    congr 1
    ring

/-- **The DTFT matrix element of the masked rotation is the Loewner entry.**
In the Fourier basis the weighted masked rotation *is* the divided-difference
matrix `atomEntry` (the Fourier-side form of the paper's Lemma 2.1). -/
theorem matrix_element_atomEntry (q c : ℕ) (m n : ℤ)
    (hβ0 : 0 < Real.log q / Real.log c) (hβ1 : Real.log q / Real.log c < 1) :
    ((weight q : ℝ) : ℂ) *
      (∫ z : AddCircle (1 : ℝ),
        ((maskFwd (Real.log q / Real.log c)).indicator
            (fun w => fourier m
              (w + ((Real.log q / Real.log c : ℝ) : AddCircle (1 : ℝ)))) z
          + (maskBwd (Real.log q / Real.log c)).indicator
            (fun w => fourier m
              (w + -((Real.log q / Real.log c : ℝ) : AddCircle (1 : ℝ)))) z)
        * (starRingEnd ℂ) (fourier n z))
      = ((atomEntry q c n m : ℝ) : ℂ) := by
  rw [atomEntry_eq, Complex.ofReal_mul]
  congr 1
  by_cases hmn : n = m
  · subst hmn
    rw [if_pos rfl]
    exact matrix_element_diag _ hβ0 hβ1 n
  · rw [if_neg hmn]
    exact matrix_element_offdiag _ hβ0 hβ1 m n (Ne.symm hmn)

end Cvs.PathLaw
