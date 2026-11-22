import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The Riccati witness is a tangent

    `w y = t · tan (t (y − c))`   satisfies   `w' = t² + w²`

wherever the cosine does not vanish, and `w 0 = −b` when `c = arctan (b/t)/t`.
-/

noncomputable section

namespace Cvs.Upstream.RiccatiTangentWitness

/-- The witness. -/
def wit (t c : ℝ) : ℝ → ℝ := fun y => t * Real.tan (t * (y - c))

/-- **The Riccati equation.**  `sec² = 1 + tan²` is the whole of it. -/
theorem hasDerivAt_wit {t c x : ℝ} (hcos : Real.cos (t * (x - c)) ≠ 0) :
    HasDerivAt (wit t c) (t ^ 2 + (wit t c x) ^ 2) x := by
  have hin : HasDerivAt (fun y : ℝ => t * (y - c)) t x := by
    simpa using ((hasDerivAt_id x).sub_const c).const_mul t
  have htan : HasDerivAt (fun y : ℝ => Real.tan (t * (y - c)))
      (1 / Real.cos (t * (x - c)) ^ 2 * t) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_tan hcos).comp x hin
  have h := htan.const_mul t
  have hid : (1 + Real.tan (t * (x - c)) ^ 2) * Real.cos (t * (x - c)) ^ 2 = 1 :=
    Real.one_add_tan_sq_mul_cos_sq_eq_one hcos
  have hc2 : Real.cos (t * (x - c)) ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  have hval : t * (1 / Real.cos (t * (x - c)) ^ 2 * t)
      = t ^ 2 + (wit t c x) ^ 2 := by
    unfold wit
    field_simp
    nlinarith [hid]
  rw [hval] at h
  exact h

/-- **The value at the left endpoint.**  With `c = arctan (b/t)/t` the witness starts at `−b`,
so the Robin constant is matched exactly rather than estimated. -/
theorem wit_zero {t b : ℝ} (ht : 0 < t) :
    wit t (Real.arctan (b / t) / t) 0 = -b := by
  unfold wit
  rw [zero_sub, mul_neg, mul_div_cancel₀ _ (ne_of_gt ht), Real.tan_neg, Real.tan_arctan]
  field_simp

end Cvs.Upstream.RiccatiTangentWitness
