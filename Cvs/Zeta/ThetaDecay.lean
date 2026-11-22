import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.MellinSplit

/-
**Explicit exponential decay of the theta kernel.**

Rung 2 needs a growth bound on `Λ₀ = completedRiemannZeta₀`, which is a Mellin
transform of the theta kernel.  `Cvs.Zeta.GammaBound` supplies the estimate for
the resulting integral; what is still needed is the *decay* of the kernel, with
explicit constants.

Mathlib has the decay, but only as an `IsBigO`:

    `isBigO_atTop_evenKernel_sub 0 : ∃ p > 0, (evenKernel 0 · − 1) =O[atTop] e^{−p·}`.

That is genuine exponential decay — much stronger than the `O(x^r)`-for-every-`r`
carried by the abstract `WeakFEPair` interface, which has no uniform constants and
cannot bound a Mellin transform at all.  This file unpacks it into the explicit
form `|θ(t) − 1| ≤ C·e^{−vt}` for `t ≥ T`, which is what an integral estimate can
consume.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Filter Asymptotics

/-- **The theta kernel decays exponentially, with explicit constants.** -/
theorem exists_evenKernel_sub_one_bound :
    ∃ C v T : ℝ, 0 < C ∧ 0 < v ∧ 1 ≤ T ∧
      ∀ t : ℝ, T ≤ t → |HurwitzZeta.evenKernel 0 t - 1| ≤ C * Real.exp (-v * t) := by
  obtain ⟨p, hp, hO⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub 0
  simp only [↓reduceIte] at hO
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hc
  refine ⟨max c 1, p, max T₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hp,
    le_max_right _ _, fun t ht => ?_⟩
  have h1 := hT₀ t (le_trans (le_max_left _ _) ht)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- **The cosine kernel decays exponentially too**, with explicit constants.
This is the other half of the Mellin integrand: `hf_modif_FE` sends the `(0,1)`
end of `Λ₀`'s integral to a `[1,∞)` integral against `cosKernel − 1`. -/
theorem exists_cosKernel_sub_one_bound :
    ∃ C v T : ℝ, 0 < C ∧ 0 < v ∧ 1 ≤ T ∧
      ∀ t : ℝ, T ≤ t → |HurwitzZeta.cosKernel 0 t - 1| ≤ C * Real.exp (-v * t) := by
  obtain ⟨p, hp, hO⟩ := HurwitzZeta.isBigO_atTop_cosKernel_sub 0
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hc
  refine ⟨max c 1, p, max T₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hp,
    le_max_right _ _, fun t ht => ?_⟩
  have h1 := hT₀ t (le_trans (le_max_left _ _) ht)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- **Both ends of `Λ₀`'s Mellin integrand, with one set of constants.**  Taking
the larger `C`, `T` and the smaller rate `v` makes a single triple work for both
kernels — the form the two tail estimates consume. -/
theorem exists_kernel_bounds :
    ∃ C v T : ℝ, 0 < C ∧ 0 < v ∧ 1 ≤ T ∧
      (∀ t : ℝ, T ≤ t → |HurwitzZeta.evenKernel 0 t - 1| ≤ C * Real.exp (-v * t)) ∧
      (∀ t : ℝ, T ≤ t → |HurwitzZeta.cosKernel 0 t - 1| ≤ C * Real.exp (-v * t)) := by
  obtain ⟨C₁, v₁, T₁, hC₁, hv₁, hT₁, hb₁⟩ := exists_evenKernel_sub_one_bound
  obtain ⟨C₂, v₂, T₂, hC₂, hv₂, hT₂, hb₂⟩ := exists_cosKernel_sub_one_bound
  refine ⟨max C₁ C₂, min v₁ v₂, max T₁ T₂, lt_of_lt_of_le hC₁ (le_max_left _ _),
    lt_min hv₁ hv₂, le_trans hT₁ (le_max_left _ _), fun t ht => ?_, fun t ht => ?_⟩
  · refine (hb₁ t (le_trans (le_max_left _ _) ht)).trans ?_
    have hmono : Real.exp (-v₁ * t) ≤ Real.exp (-(min v₁ v₂) * t) := by
      have ht0 : (0 : ℝ) ≤ t := by
        have : (1 : ℝ) ≤ t := le_trans (le_trans hT₁ (le_max_left _ _)) ht
        linarith
      exact Real.exp_le_exp.mpr (by nlinarith [min_le_left v₁ v₂])
    exact mul_le_mul (le_max_left _ _) hmono (Real.exp_pos _).le
      (le_trans hC₁.le (le_max_left _ _))
  · refine (hb₂ t (le_trans (le_max_right _ _) ht)).trans ?_
    have hmono : Real.exp (-v₂ * t) ≤ Real.exp (-(min v₁ v₂) * t) := by
      have ht0 : (0 : ℝ) ≤ t := by
        have : (1 : ℝ) ≤ t := le_trans (le_trans hT₁ (le_max_left _ _)) ht
        linarith
      exact Real.exp_le_exp.mpr (by nlinarith [min_le_right v₁ v₂])
    exact mul_le_mul (le_max_right _ _) hmono (Real.exp_pos _).le
      (le_trans hC₂.le (le_max_right _ _))

/-! ### Convergence of `Λ₀`'s outer half, for the zeta pair

`Lambda0_eq_tail_add_tail` carries two convergence hypotheses.  The outer one is
now discharged: the integrand `θ(t) − 1` is continuous on `(0, ∞)` and
exponentially small, which is exactly `integrableOn_Ioi_one_of_exp_bound`. -/

theorem mellinConvergent_zeta_outer (s : ℂ) :
    MellinConvergent ((Set.Ioi 1).indicator
      (fun t : ℝ => ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1)) s := by
  obtain ⟨C, v, T, hC, hv, hT, hb⟩ := exists_evenKernel_sub_one_bound
  rw [mellinConvergent_indicator_Ioi_iff zero_le_one]
  refine integrableOn_Ioi_one_of_exp_bound ?_ hT hC.le hv (fun t ht => ?_)
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (HurwitzZeta.continuousOn_evenKernel 0)).sub continuousOn_const
  · have hnorm : ‖((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1‖
        = |HurwitzZeta.evenKernel 0 t - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    exact hb t ht

/-- **The inner convergence hypothesis, for the zeta pair.**  Same construction
as the outer one, run against the cosine kernel — which is where the reflection
sends the `(0,1)` half. -/
theorem mellinConvergent_zeta_inner (s : ℂ) :
    MellinConvergent ((Set.Ioo 0 1).indicator
      (fun t : ℝ => (HurwitzZeta.hurwitzEvenFEPair 0).f t
        - ((HurwitzZeta.hurwitzEvenFEPair 0).ε
            * ((t ^ (-(HurwitzZeta.hurwitzEvenFEPair 0).k) : ℝ) : ℂ))
          • (HurwitzZeta.hurwitzEvenFEPair 0).g₀)) s := by
  obtain ⟨C, v, T, hC, hv, hT, hb⟩ := exists_cosKernel_sub_one_bound
  refine mellinConvergent_inner_of_exp_bound _ ?_ hT hC.le hv (fun t ht => ?_)
  · have : (fun t : ℝ => (HurwitzZeta.hurwitzEvenFEPair 0).ε
        • ((HurwitzZeta.hurwitzEvenFEPair 0).g t - (HurwitzZeta.hurwitzEvenFEPair 0).g₀))
        = fun t : ℝ => ((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1 := by
      funext t
      simp [HurwitzZeta.hurwitzEvenFEPair]
    rw [this]
    exact (Complex.continuous_ofReal.comp_continuousOn
      (HurwitzZeta.continuousOn_cosKernel 0)).sub continuousOn_const
  · have hval : (HurwitzZeta.hurwitzEvenFEPair 0).ε
        • ((HurwitzZeta.hurwitzEvenFEPair 0).g t - (HurwitzZeta.hurwitzEvenFEPair 0).g₀)
        = ((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1 := by
      simp [HurwitzZeta.hurwitzEvenFEPair]
    rw [hval, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact hb t ht

/-! ### `Λ₀` for the zeta pair, as two tails

Both hypotheses of `Lambda0_eq_tail_add_tail'` are now available, so the
decomposition specialises. -/

theorem Lambda0_zeta_eq_tails (s : ℂ) :
    (HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ s
      = (∫ t in Set.Ioi (1:ℝ),
          (t : ℂ) ^ (s - 1) • (((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1))
        + ∫ t in Set.Ioi (1:ℝ),
            (t : ℂ) ^ (((1/2 : ℝ) : ℂ) - s - 1)
              • (((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1) := by
  have houter : (fun t : ℝ => (HurwitzZeta.hurwitzEvenFEPair 0).f t
      - (HurwitzZeta.hurwitzEvenFEPair 0).f₀)
      = fun t : ℝ => ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1 := by
    funext t; simp [HurwitzZeta.hurwitzEvenFEPair]
  have hconvA := mellinConvergent_zeta_outer (s := s)
  rw [← houter] at hconvA
  have hmain := Lambda0_eq_tail_add_tail' (HurwitzZeta.hurwitzEvenFEPair 0)
    hconvA (mellinConvergent_zeta_inner s)
  rw [hmain]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    have hf : (HurwitzZeta.hurwitzEvenFEPair 0).f t
        - (HurwitzZeta.hurwitzEvenFEPair 0).f₀
        = ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1 := by
      simp [HurwitzZeta.hurwitzEvenFEPair]
    rw [hf]
  · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    have hk : ((HurwitzZeta.hurwitzEvenFEPair 0).k : ℂ) = ((1/2 : ℝ) : ℂ) := by
      norm_num [HurwitzZeta.hurwitzEvenFEPair]
    have hg : (HurwitzZeta.hurwitzEvenFEPair 0).ε
        • ((HurwitzZeta.hurwitzEvenFEPair 0).g t - (HurwitzZeta.hurwitzEvenFEPair 0).g₀)
        = ((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1 := by
      simp [HurwitzZeta.hurwitzEvenFEPair]
    rw [hk, hg]

/-! ### Rung 2: the growth bound on `Λ₀`

Both tails of `Lambda0_zeta_eq_tails` are Mellin tails of explicitly decaying,
continuous kernels, so `norm_integral_Ioi_one_le` bounds each. -/

theorem exists_norm_Lambda0_zeta_le :
    ∃ M C v T : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ 0 < v ∧ 1 ≤ T ∧ ∀ s : ℂ,
      ‖(HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ s‖
        ≤ tailBound M C v T (max s.re 1)
          + tailBound M C v T (max ((1/2 : ℝ) - s.re) 1) := by
  obtain ⟨C, v, T, hC, hv, hT, hbe, hbc⟩ := exists_kernel_bounds
  have hcontE : ContinuousOn (fun t : ℝ => ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1)
      (Set.Ioi (0:ℝ)) :=
    (Complex.continuous_ofReal.comp_continuousOn
      (HurwitzZeta.continuousOn_evenKernel 0)).sub continuousOn_const
  have hcontC : ContinuousOn (fun t : ℝ => ((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1)
      (Set.Ioi (0:ℝ)) :=
    (Complex.continuous_ofReal.comp_continuousOn
      (HurwitzZeta.continuousOn_cosKernel 0)).sub continuousOn_const
  have hnormE : ∀ t : ℝ, T ≤ t →
      ‖((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1‖ ≤ C * Real.exp (-v * t) := by
    intro t ht
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hbe t ht
  have hnormC : ∀ t : ℝ, T ≤ t →
      ‖((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1‖ ≤ C * Real.exp (-v * t) := by
    intro t ht
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hbc t ht
  obtain ⟨M₁, hM₁0, hM₁⟩ := norm_integral_Ioi_one_le hcontE hC.le hv hT hnormE
  obtain ⟨M₂, hM₂0, hM₂⟩ := norm_integral_Ioi_one_le hcontC hC.le hv hT hnormC
  refine ⟨max M₁ M₂, C, v, T, le_trans hM₁0 (le_max_left _ _), hC.le, hv, hT, fun s => ?_⟩
  have hmono : ∀ (M M' x : ℝ), M ≤ M' → 0 ≤ T ^ x →
      tailBound M C v T x ≤ tailBound M' C v T x := by
    intro M M' x hMM hTx
    unfold tailBound
    exact add_le_add (mul_le_mul_of_nonneg_right hMM hTx) le_rfl
  have hTx1 : (0:ℝ) ≤ T ^ (max s.re 1) :=
    Real.rpow_nonneg (le_trans zero_le_one hT) _
  have hTx2 : (0:ℝ) ≤ T ^ (max ((1/2 : ℝ) - s.re) 1) :=
    Real.rpow_nonneg (le_trans zero_le_one hT) _
  rw [Lambda0_zeta_eq_tails s]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · exact le_trans (hM₁ s) (hmono M₁ (max M₁ M₂) _ (le_max_left _ _) hTx1)
  · have hre : ((((1/2 : ℝ) : ℂ) - s).re) = (1/2 : ℝ) - s.re := by
      simp
    have := hM₂ (((1/2 : ℝ) : ℂ) - s)
    rw [hre] at this
    exact le_trans this (hmono M₂ (max M₁ M₂) _ (le_max_right _ _) hTx2)

/-! ### Transfer to `completedRiemannZeta₀`

Mathlib's `Λ₀` for `ζ` is the FE-pair's `Λ₀` at half the argument, halved:
`completedRiemannZeta₀ s = (P.Λ₀ (s/2))/2`.  Both are definitional. -/

theorem completedRiemannZeta₀_eq_Lambda0 (s : ℂ) :
    completedRiemannZeta₀ s = ((HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (s / 2)) / 2 := rfl

/-- **The growth bound, on Mathlib's `Λ₀`.**  Order 1, maximal type. -/
theorem exists_norm_completedRiemannZeta₀_le :
    ∃ M C v T : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ 0 < v ∧ 1 ≤ T ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖
        ≤ (tailBound M C v T (max (s.re / 2) 1)
            + tailBound M C v T (max ((1/2 : ℝ) - s.re / 2) 1)) / 2 := by
  obtain ⟨M, C, v, T, hM, hC, hv, hT, hb⟩ := exists_norm_Lambda0_zeta_le
  refine ⟨M, C, v, T, hM, hC, hv, hT, fun s => ?_⟩
  rw [completedRiemannZeta₀_eq_Lambda0, norm_div]
  have hre : (s / 2).re = s.re / 2 := by simp
  have h := hb (s / 2)
  rw [hre] at h
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  exact div_le_div_of_nonneg_right h (by norm_num) |>.trans_eq rfl

/-! ### Rung 2, in the form rungs 1+4 consume

`summable_inv_norm_sq_zeroSeq_of_growth_rlogr` wants
`‖f z‖ ≤ C·exp(A·‖z‖·(1 + log‖z‖))`.  The bound above is stated at
`max (Re s/2) 1` and `max (½ − Re s/2) 1`; both are `≤ max ‖s‖ 1`, and
`max_one_mul_one_add_log_le` trades that for `‖s‖` at the cost of `e^{2A}`. -/

theorem exists_growth_bound_completedRiemannZeta₀ :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖
        ≤ C * Real.exp (A * (‖s‖ * (1 + Real.log ‖s‖))) := by
  obtain ⟨M, C, v, T, hM, hC, hv, hT, hb⟩ := exists_norm_completedRiemannZeta₀_le
  set A : ℝ := max (max (Real.log T) |Real.log v|) 1 with hA
  have hA1 : (1:ℝ) ≤ A := le_max_right _ _
  have hA0 : (0:ℝ) ≤ A := by linarith
  refine ⟨(M + C) * Real.exp (2 * A), A, by positivity, hA0, fun s => ?_⟩
  set y : ℝ := max ‖s‖ 1 with hy
  have hy1 : (1:ℝ) ≤ y := le_max_right _ _
  have hsn : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
  have hre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  -- both exponents are at most `y`
  have hx1 : max (s.re / 2) 1 ≤ y := by
    refine max_le ?_ hy1
    refine le_trans ?_ (le_max_left _ _)
    have : s.re ≤ ‖s‖ := le_trans (le_abs_self _) hre
    linarith
  have hx2 : max ((1/2 : ℝ) - s.re / 2) 1 ≤ y := by
    refine max_le ?_ hy1
    rcases lt_or_ge ‖s‖ 1 with h | h
    · refine le_trans ?_ hy1
      have : -s.re ≤ ‖s‖ := le_trans (neg_le_abs _) hre
      linarith
    · refine le_trans ?_ (le_max_left _ _)
      have : -s.re ≤ ‖s‖ := le_trans (neg_le_abs _) hre
      linarith
  -- convert each tail bound
  have hstep : ∀ x : ℝ, 1 ≤ x → x ≤ y →
      tailBound M C v T x ≤ (M + C) * Real.exp (A * (y * (1 + Real.log y))) := by
    intro x hx hxy
    refine le_trans (tailBound_le_exp hM hC hv hT hx) ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
    exact mul_le_mul_of_nonneg_left (mul_one_add_log_mono hx hxy) hA0
  have hb' := hb s
  have h1 := hstep _ (le_max_right _ _) hx1
  have h2 := hstep _ (le_max_right _ _) hx2
  have hcomb : (tailBound M C v T (max (s.re / 2) 1)
      + tailBound M C v T (max ((1/2 : ℝ) - s.re / 2) 1)) / 2
      ≤ (M + C) * Real.exp (A * (y * (1 + Real.log y))) := by linarith
  refine le_trans hb' (le_trans hcomb ?_)
  -- trade `y` for `‖s‖`
  have hbridge : y * (1 + Real.log y) ≤ ‖s‖ * (1 + Real.log ‖s‖) + 2 :=
    max_one_mul_one_add_log_le hsn
  have hexp : Real.exp (A * (y * (1 + Real.log y)))
      ≤ Real.exp (2 * A) * Real.exp (A * (‖s‖ * (1 + Real.log ‖s‖))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hbridge, hA0]
  calc (M + C) * Real.exp (A * (y * (1 + Real.log y)))
      ≤ (M + C) * (Real.exp (2 * A) * Real.exp (A * (‖s‖ * (1 + Real.log ‖s‖)))) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
    _ = (M + C) * Real.exp (2 * A) * Real.exp (A * (‖s‖ * (1 + Real.log ‖s‖))) := by
        ring

end Cvs.Zeta
