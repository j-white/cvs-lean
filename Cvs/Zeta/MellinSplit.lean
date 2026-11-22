import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Cvs.Zeta.GammaBound

/-
**Splitting `Λ₀` into two tail integrals.**

Rung 2 needs a growth bound on `Λ₀ = completedRiemannZeta₀`.  Every analytic
ingredient is now proved — `Cvs.Zeta.GammaBound` (the `Γ` bound, the scaled
integrability, and the tail estimate) and `Cvs.Zeta.ThetaDecay` (exponential decay
of both kernels, with explicit constants).  What is missing is *structural*:
Mathlib defines

    `Λ₀ = mellin f_modif`,   `f_modif = 𝟙_{(1,∞)}·(f − f₀) + 𝟙_{(0,1)}·(f − ε·x^{−k}·g₀)`

as a **single** Mellin transform over `(0, ∞)` and never splits it.  The tail
estimates only see integrals over `[T, ∞)`, so the classical decomposition

    `Λ₀(s) = ∫₁^∞ (f(t) − f₀)·t^{s−1} dt + ε·∫₁^∞ (g(t) − g₀)·t^{k−s−1} dt`

has to be built.  The `(0,1)` half becomes a `[1,∞)` integral by `t ↦ 1/t`, for
which `mellin_comp_inv` is exactly right: `mellin (f ∘ (·⁻¹)) s = mellin f (−s)`,
with no side conditions.  Combined with the pair's own functional equation
`h_feq`, the reflected integrand is `ε·t^k·(g(t) − g₀)`.

This file builds the pieces bottom-up.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open MeasureTheory Set

/-- A Mellin transform of a function supported on `[a, ∞)` is a tail integral. -/
theorem mellin_indicator_Ioi {F : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (s : ℂ) :
    mellin ((Set.Ioi a).indicator F) s
      = ∫ t in Set.Ioi a, (t : ℂ) ^ (s - 1) • F t := by
  have hfun : (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Set.Ioi a).indicator F t)
      = (Set.Ioi a).indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) := by
    funext t
    by_cases h : t ∈ Set.Ioi a
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, smul_zero]
  rw [mellin, hfun, MeasureTheory.integral_indicator measurableSet_Ioi,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_self_of_subset_left (Set.Ioi_subset_Ioi ha)]

/-- **The reflection.**  Inverting the variable turns a `(0,1)`-supported Mellin
integral into an `[1,∞)`-supported one.  `mellin_comp_inv` does the substitution;
the content here is that `t⁻¹ ∈ (0,1) ↔ t ∈ (1,∞)`. -/
theorem indicator_Ioo_comp_inv (F : ℝ → ℂ) :
    (fun t : ℝ => (Set.Ioo (0:ℝ) 1).indicator F t⁻¹)
      = (Set.Ioi (1:ℝ)).indicator (fun t => F t⁻¹) := by
  funext t
  by_cases h : t ∈ Set.Ioi (1:ℝ)
  · have h1 : (1:ℝ) < t := h
    have ht0 : (0:ℝ) < t := lt_trans zero_lt_one h1
    have hmem : t⁻¹ ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨inv_pos.mpr ht0, inv_lt_one_of_one_lt₀ h1⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h]
  · have h1 : ¬ (1:ℝ) < t := h
    have hnot : t⁻¹ ∉ Set.Ioo (0:ℝ) 1 := by
      rintro ⟨hpos, hlt⟩
      have ht0 : (0:ℝ) < t := inv_pos.mp hpos
      rcases inv_lt_one_iff₀.mp hlt with hc | hc
      · linarith
      · exact h1 hc
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem h]

/-- **A `(0,1)`-supported Mellin integral is a tail integral of the reflected
function.**  This is the step Mathlib does not take: `Λ₀`'s inner half becomes an
integral over `[1, ∞)`, where the tail estimates apply. -/
theorem mellin_indicator_Ioo_eq_tail (F : ℝ → ℂ) (s : ℂ) :
    mellin ((Set.Ioo (0:ℝ) 1).indicator F) s
      = ∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (-s - 1) • F t⁻¹ := by
  have h := mellin_comp_inv ((Set.Ioo (0:ℝ) 1).indicator F) (-s)
  rw [neg_neg] at h
  rw [← h, indicator_Ioo_comp_inv, mellin_indicator_Ioi zero_le_one]

/-! ### The two halves of `f_modif` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `f_modif` is by definition the sum of its two indicator pieces. -/
theorem f_modif_eq_add (P : WeakFEPair E) :
    P.f_modif
      = (Set.Ioi 1).indicator (fun t => P.f t - P.f₀)
        + (Set.Ioo 0 1).indicator
            (fun t => P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀) := rfl

/-- **The reflected inner integrand.**  On `(1, ∞)` the pair's functional
equation turns `f(1/t) − ε·t^k·g₀` into `ε·t^k·(g(t) − g₀)` — the cosine-kernel
tail, which decays exponentially. -/
theorem inner_integrand_comp_inv (P : WeakFEPair E) {t : ℝ} (ht : 0 < t) :
    P.f t⁻¹ - (P.ε * ((t⁻¹ ^ (-P.k) : ℝ) : ℂ)) • P.g₀
      = (P.ε * ((t ^ P.k : ℝ) : ℂ)) • (P.g t - P.g₀) := by
  have hinv : (1 : ℝ) / t = t⁻¹ := one_div t
  have hfe := P.h_feq t ht
  rw [hinv] at hfe
  rw [hfe, Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv, smul_sub]

/-! ### Adding the two halves -/

/-- Mellin transforms add, given convergence of each piece. -/
theorem mellin_add_of_convergent {F G : ℝ → ℂ} {s : ℂ}
    (hF : MellinConvergent F s) (hG : MellinConvergent G s) :
    mellin (F + G) s = mellin F s + mellin G s := by
  simp only [mellin, Pi.add_apply, smul_add]
  exact MeasureTheory.integral_add hF hG

/-- **The decomposition.** `Λ₀` is the sum of two integrals over `[1, ∞)`: the outer half as it
stands, and the inner half reflected by `t ↦ 1/t`, whose integrand the pair's functional
equation turns into `ε·t^k·(g(t) − g₀)`. -/
theorem Lambda0_eq_tail_add_tail (P : WeakFEPair ℂ) {s : ℂ}
    (hA : MellinConvergent ((Set.Ioi 1).indicator (fun t => P.f t - P.f₀)) s)
    (hB : MellinConvergent ((Set.Ioo 0 1).indicator
      (fun t => P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀)) s) :
    P.Λ₀ s
      = (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (s - 1) • (P.f t - P.f₀))
        + ∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (-s - 1) •
            ((P.ε * ((t ^ P.k : ℝ) : ℂ)) • (P.g t - P.g₀)) := by
  have hsplit : P.Λ₀ s
      = mellin ((Set.Ioi 1).indicator (fun t => P.f t - P.f₀)) s
        + mellin ((Set.Ioo 0 1).indicator
            (fun t => P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀)) s := by
    show mellin P.f_modif s = _
    rw [f_modif_eq_add P, mellin_add_of_convergent hA hB]
  rw [hsplit, mellin_indicator_Ioi zero_le_one, mellin_indicator_Ioo_eq_tail]
  refine congrArg₂ (· + ·) rfl ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  rw [inner_integrand_comp_inv P ht0]

/-! ### Reducing convergence to tail integrability

`Lambda0_eq_tail_add_tail` carries two `MellinConvergent` hypotheses.  Each is
about an integral over `(0, ∞)` of an indicator-supported integrand, so each
collapses to plain integrability on the support — which is where the exponential
majorants of `Cvs.Zeta.GammaBound` apply. -/

theorem mellinConvergent_indicator_Ioi_iff {F : ℝ → ℂ} {s : ℂ} {a : ℝ}
    (ha : 0 ≤ a) :
    MellinConvergent ((Set.Ioi a).indicator F) s
      ↔ MeasureTheory.IntegrableOn
          (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) (Set.Ioi a) := by
  have hfun : (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Set.Ioi a).indicator F t)
      = (Set.Ioi a).indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) := by
    funext t
    by_cases h : t ∈ Set.Ioi a
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, smul_zero]
  unfold MellinConvergent
  rw [hfun, MeasureTheory.IntegrableOn,
    MeasureTheory.integrable_indicator_iff measurableSet_Ioi,
    MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_self_of_subset_left (Set.Ioi_subset_Ioi ha)]
  exact Iff.rfl

/-!
### Discharging convergence from exponential decay

The two tail integrands are continuous on `(0, ∞)` and exponentially small past some `T`.
-/

theorem integrableOn_Ioi_one_of_exp_bound {F : ℝ → ℂ} {s : ℂ} {C v T : ℝ}
    (hcont : ContinuousOn F (Set.Ioi (0:ℝ))) (hT : 1 ≤ T) (hC : 0 ≤ C) (hv : 0 < v)
    (hbd : ∀ t : ℝ, T ≤ t → ‖F t‖ ≤ C * Real.exp (-v * t)) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) (Set.Ioi (1:ℝ)) := by
  set x : ℝ := max s.re 1 with hx
  have hx1 : (1:ℝ) ≤ x := le_max_right _ _
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  -- the integrand is continuous on `(0, ∞)`
  have hcpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Set.Ioi (0:ℝ)) :=
    continuousOn_of_forall_continuousAt fun t ht =>
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
  have hcontI : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) (Set.Ioi (0:ℝ)) := by
    simp only [smul_eq_mul]
    exact hcpow.mul hcont
  -- split at `T`
  have hsplit : Set.Ioi (1:ℝ) = Set.Ioc 1 T ∪ Set.Ioi T := (Set.Ioc_union_Ioi_eq_Ioi hT).symm
  rw [hsplit, MeasureTheory.integrableOn_union]
  constructor
  · -- compact piece
    have hIcc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) (Set.Icc 1 T) := by
      refine hcontI.mono fun t ht => ?_
      exact lt_of_lt_of_le zero_lt_one ht.1
    exact (hIcc.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  · -- tail piece, dominated
    have hmaj : MeasureTheory.IntegrableOn
        (fun t : ℝ => C * (t ^ (x - 1) * Real.exp (-v * t))) (Set.Ioi T) :=
      (integrableOn_exp_mul_rpow_Ioi hv hxpos hTpos.le).const_mul C
    refine MeasureTheory.Integrable.mono' hmaj
      ((hcontI.mono (Set.Ioi_subset_Ioi hTpos.le)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := lt_trans hTpos ht
    have ht1 : (1:ℝ) ≤ t := le_trans hT ht.le
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
    have hexp : t ^ (s.re - 1) ≤ t ^ (x - 1) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by simp [hx])
    have hFb := hbd t ht.le
    calc t ^ (s.re - 1) * ‖F t‖
        ≤ t ^ (x - 1) * (C * Real.exp (-v * t)) := by
          exact mul_le_mul hexp hFb (norm_nonneg _) (Real.rpow_pos_of_pos ht0 _).le
      _ = C * (t ^ (x - 1) * Real.exp (-v * t)) := by ring

/-!
### Absorbing the weight into the exponent

The reflected integrand carries a factor `t^k`.
-/

theorem tail_integrand_eq (P : WeakFEPair ℂ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (-s - 1) • ((P.ε * ((t ^ P.k : ℝ) : ℂ)) • (P.g t - P.g₀))
      = (t : ℂ) ^ ((P.k : ℂ) - s - 1) • (P.ε • (P.g t - P.g₀)) := by
  have hne : (t : ℂ) ≠ 0 := by
    simpa using ne_of_gt ht
  rw [Complex.ofReal_cpow ht.le, smul_smul, smul_smul, ← mul_assoc]
  congr 1
  rw [mul_comm ((t : ℂ) ^ (-s - 1)) _, mul_assoc, ← Complex.cpow_add _ _ hne]
  ring_nf

/-- **Both halves, one shape.**  `Λ₀(s)` is the outer tail at `s` plus `ε` times
the outer-shaped tail at `k − s`. -/
theorem Lambda0_eq_tail_add_tail' (P : WeakFEPair ℂ) {s : ℂ}
    (hA : MellinConvergent ((Set.Ioi 1).indicator (fun t => P.f t - P.f₀)) s)
    (hB : MellinConvergent ((Set.Ioo 0 1).indicator
      (fun t => P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀)) s) :
    P.Λ₀ s
      = (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (s - 1) • (P.f t - P.f₀))
        + ∫ t in Set.Ioi (1:ℝ),
            (t : ℂ) ^ ((P.k : ℂ) - s - 1) • (P.ε • (P.g t - P.g₀)) := by
  rw [Lambda0_eq_tail_add_tail P hA hB]
  refine congrArg₂ (· + ·) rfl ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  exact tail_integrand_eq P s (lt_trans zero_lt_one ht)

/-! ### Convergence of the inner half, by reflection

`MellinConvergent.comp_rpow` at `a = −1` reflects convergence just as
`mellin_comp_inv` reflected the value.  Combined with `indicator_Ioo_comp_inv`,
the inner hypothesis becomes an outer one at `−s`. -/

theorem mellinConvergent_indicator_Ioo_iff_tail {F : ℝ → ℂ} {s : ℂ} :
    MellinConvergent ((Set.Ioo (0:ℝ) 1).indicator F) s
      ↔ MellinConvergent ((Set.Ioi (1:ℝ)).indicator (fun t => F t⁻¹)) (-s) := by
  have h := MellinConvergent.comp_rpow
    (f := (Set.Ioo (0:ℝ) 1).indicator F) (s := -s) (a := -1)
    (by norm_num)
  have hfun : (fun t : ℝ => (Set.Ioo (0:ℝ) 1).indicator F (t ^ (-1 : ℝ)))
      = (Set.Ioi (1:ℝ)).indicator (fun t => F t⁻¹) := by
    simp only [Real.rpow_neg_one]
    exact indicator_Ioo_comp_inv F
  rw [hfun] at h
  rw [h]
  norm_num

/-- **The inner convergence hypothesis, from decay of `g`.** Reflecting turns it into an outer
one; `tail_integrand_eq` puts the weight `t^k` into the exponent, so the decaying factor is
just `ε·(g − g₀)` and no polynomial-times-exponential estimate is needed. -/
theorem mellinConvergent_inner_of_exp_bound (P : WeakFEPair ℂ) {s : ℂ} {C v T : ℝ}
    (hcont : ContinuousOn (fun t : ℝ => P.ε • (P.g t - P.g₀)) (Set.Ioi (0:ℝ)))
    (hT : 1 ≤ T) (hC : 0 ≤ C) (hv : 0 < v)
    (hbd : ∀ t : ℝ, T ≤ t → ‖P.ε • (P.g t - P.g₀)‖ ≤ C * Real.exp (-v * t)) :
    MellinConvergent ((Set.Ioo 0 1).indicator
      (fun t => P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀)) s := by
  rw [mellinConvergent_indicator_Ioo_iff_tail,
    mellinConvergent_indicator_Ioi_iff zero_le_one]
  have hcongr : Set.EqOn
      (fun t : ℝ => (t : ℂ) ^ (-s - 1) •
        (P.f t⁻¹ - (P.ε * ((t⁻¹ ^ (-P.k) : ℝ) : ℂ)) • P.g₀))
      (fun t : ℝ => (t : ℂ) ^ ((P.k : ℂ) - s - 1) • (P.ε • (P.g t - P.g₀)))
      (Set.Ioi (1:ℝ)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
    dsimp only
    rw [inner_integrand_comp_inv P ht0, tail_integrand_eq P s ht0]
  refine (MeasureTheory.integrableOn_congr_fun hcongr measurableSet_Ioi).mpr ?_
  exact integrableOn_Ioi_one_of_exp_bound (s := (P.k : ℂ) - s) hcont hT hC hv hbd

/-! ### The tail estimate, complex-valued

`abs_integral_Ioi_le_of_exp_bound` is real-valued; the tails of `Λ₀` are
`(t:ℂ)^{s−1} • F t`.  Same argument, with `‖(t:ℂ)^{s−1}‖ = t^{Re s − 1}` and the
exponent run at `x = max (Re s) 1` so the majorant lemma applies. -/

theorem norm_integral_Ioi_le_of_exp_bound {F : ℝ → ℂ} {s : ℂ} {C v T : ℝ}
    (hC : 0 ≤ C) (hv : 0 < v) (hT : 1 ≤ T)
    (hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) (Set.Ioi T))
    (hbd : ∀ t : ℝ, T ≤ t → ‖F t‖ ≤ C * Real.exp (-v * t)) :
    ‖∫ t in Set.Ioi T, (t : ℂ) ^ (s - 1) • F t‖
      ≤ C * (v ^ (-(max s.re 1)) * Real.exp (max s.re 1 * Real.log (max s.re 1))) := by
  set x : ℝ := max s.re 1 with hx
  have hx1 : (1:ℝ) ≤ x := le_max_right _ _
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => C * (t ^ (x - 1) * Real.exp (-v * t))) (Set.Ioi T) :=
    (integrableOn_exp_mul_rpow_Ioi hv hxpos hTpos.le).const_mul C
  calc ‖∫ t in Set.Ioi T, (t : ℂ) ^ (s - 1) • F t‖
      ≤ ∫ t in Set.Ioi T, ‖(t : ℂ) ^ (s - 1) • F t‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi T, C * (t ^ (x - 1) * Real.exp (-v * t)) := by
        refine MeasureTheory.setIntegral_mono_on hint.norm hmaj measurableSet_Ioi
          (fun t ht => ?_)
        have ht0 : (0:ℝ) < t := lt_trans hTpos ht
        have ht1 : (1:ℝ) ≤ t := le_trans hT ht.le
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re,
          Complex.one_re]
        have hexp : t ^ (s.re - 1) ≤ t ^ (x - 1) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by simp [hx])
        calc t ^ (s.re - 1) * ‖F t‖
            ≤ t ^ (x - 1) * (C * Real.exp (-v * t)) :=
              mul_le_mul hexp (hbd t ht.le) (norm_nonneg _)
                (Real.rpow_pos_of_pos ht0 _).le
          _ = C * (t ^ (x - 1) * Real.exp (-v * t)) := by ring
    _ ≤ C * (v ^ (-x) * Real.exp (x * Real.log x)) := by
        rw [MeasureTheory.integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ hC
        refine le_trans ?_ (integral_Ioi_rpow_mul_exp_le hv hx1)
        refine MeasureTheory.setIntegral_mono_set (integrableOn_exp_mul_rpow hv hxpos)
          ?_ (LE.le.eventuallySubset (Set.Ioi_subset_Ioi hTpos.le))
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0:ℝ) < t := ht
        positivity

/-- **The full tail bound on `(1, ∞)`.** The decay hypothesis only holds past `T`, so the integral
is split at `T`: on the compact head `(1, T]` the integrand is bounded by `M·T^{x−1}` and the
interval has length `≤ T`, giving `M·T^x`; past `T` the previous estimate applies. -/
theorem norm_integral_Ioi_one_le_of_exp_bound {F : ℝ → ℂ} {s : ℂ} {C v T M : ℝ}
    (hC : 0 ≤ C) (hv : 0 < v) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hMb : ∀ t ∈ Set.Ioc (1:ℝ) T, ‖F t‖ ≤ M)
    (hintH : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) (Set.Ioc 1 T))
    (hintT : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) (Set.Ioi T))
    (hbd : ∀ t : ℝ, T ≤ t → ‖F t‖ ≤ C * Real.exp (-v * t)) :
    ‖∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (s - 1) • F t‖
      ≤ M * T ^ (max s.re 1)
        + C * (v ^ (-(max s.re 1)) * Real.exp (max s.re 1 * Real.log (max s.re 1))) := by
  set x : ℝ := max s.re 1 with hx
  have hx1 : (1:ℝ) ≤ x := le_max_right _ _
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  -- split at `T`
  have hunion : Set.Ioc (1:ℝ) T ∪ Set.Ioi T = Set.Ioi (1:ℝ) := Set.Ioc_union_Ioi_eq_Ioi hT
  have hdisj : Disjoint (Set.Ioc (1:ℝ) T) (Set.Ioi T) :=
    Set.Ioc_disjoint_Ioi le_rfl
  have hsplit : (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (s - 1) • F t)
      = (∫ t in Set.Ioc (1:ℝ) T, (t : ℂ) ^ (s - 1) • F t)
        + ∫ t in Set.Ioi T, (t : ℂ) ^ (s - 1) • F t := by
    rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hintH hintT]
  rw [hsplit]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · -- the head
    have hbound : ∀ t ∈ Set.Ioc (1:ℝ) T, ‖(t : ℂ) ^ (s - 1) • F t‖ ≤ T ^ (x - 1) * M := by
      intro t ht
      have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht.1
      have ht1 : (1:ℝ) ≤ t := ht.1.le
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re,
        Complex.one_re]
      have h1 : t ^ (s.re - 1) ≤ t ^ (x - 1) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by simp [hx])
      have h2 : t ^ (x - 1) ≤ T ^ (x - 1) :=
        Real.rpow_le_rpow (by linarith) ht.2 (by linarith)
      exact mul_le_mul (le_trans h1 h2) (hMb t ht) (norm_nonneg _)
        (Real.rpow_nonneg hTpos.le _)
    have hmeas : MeasureTheory.volume (Set.Ioc (1:ℝ) T) ≠ ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    refine le_trans (MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) hbound) ?_
    rw [Real.volume_real_Ioc_of_le hT]
    have hTx : T ^ (x - 1) * T = T ^ x := by
      have hadd := Real.rpow_add hTpos (x - 1) 1
      rw [Real.rpow_one] at hadd
      rw [← hadd]
      congr 1
      ring
    calc T ^ (x - 1) * M * (T - 1) ≤ T ^ (x - 1) * M * T := by
          have : (0:ℝ) ≤ T ^ (x - 1) * M := mul_nonneg (Real.rpow_nonneg hTpos.le _) hM
          nlinarith
      _ = M * (T ^ (x - 1) * T) := by ring
      _ = M * T ^ x := by rw [hTx]
  · exact norm_integral_Ioi_le_of_exp_bound hC hv hT hintT hbd

/-- A continuous function on `(0, ∞)` is bounded on the compact head `(1, T]`. -/
theorem exists_bound_on_Ioc {F : ℝ → ℂ} {T : ℝ} (hT : 1 ≤ T)
    (hcont : ContinuousOn F (Set.Ioi (0:ℝ))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Ioc (1:ℝ) T, ‖F t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1:ℝ)) (b := T)).exists_bound_of_continuousOn
    (hcont.mono (fun t ht => lt_of_lt_of_le zero_lt_one ht.1))
  exact ⟨max M 0, le_max_right _ _,
    fun t ht => le_trans (hM t ⟨ht.1.le, ht.2⟩) (le_max_left _ _)⟩

/-- The shape of the bound: `M·T^x + C·v^{−x}·xˣ`. -/
noncomputable def tailBound (M C v T x : ℝ) : ℝ :=
  M * T ^ x + C * (v ^ (-x) * Real.exp (x * Real.log x))

/-- **The tail bound, packaged.**  Continuity on `(0,∞)` plus exponential decay
past `T` bound the whole `(1,∞)` Mellin tail by `tailBound`. -/
theorem norm_integral_Ioi_one_le {F : ℝ → ℂ} {C v T : ℝ}
    (hcont : ContinuousOn F (Set.Ioi (0:ℝ)))
    (hC : 0 ≤ C) (hv : 0 < v) (hT : 1 ≤ T)
    (hbd : ∀ t : ℝ, T ≤ t → ‖F t‖ ≤ C * Real.exp (-v * t)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ,
      ‖∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (s - 1) • F t‖
        ≤ tailBound M C v T (max s.re 1) := by
  obtain ⟨M, hM0, hMb⟩ := exists_bound_on_Ioc hT hcont
  refine ⟨M, hM0, fun s => ?_⟩
  have hall := integrableOn_Ioi_one_of_exp_bound (s := s) hcont hT hC hv hbd
  exact norm_integral_Ioi_one_le_of_exp_bound hC hv hT hM0 hMb
    (hall.mono_set Set.Ioc_subset_Ioi_self)
    (hall.mono_set (fun t ht => lt_of_le_of_lt hT ht)) hbd

/-! ### `tailBound` is order-1, maximal type

`summable_inv_norm_sq_zeroSeq_of_growth_rlogr` consumes the shape
`C·exp(A·y·(1 + log y))`.  Each piece of `tailBound` is of that form: `T^x`,
`v^{−x}` and `xˣ` are all `exp` of something at most `A·x·(1 + log x)`, with
`A = max(max(log T, |log v|), 1)`. -/

theorem tailBound_le_exp {M C v T x : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hv : 0 < v)
    (hT : 1 ≤ T) (hx : 1 ≤ x) :
    tailBound M C v T x
      ≤ (M + C)
        * Real.exp (max (max (Real.log T) |Real.log v|) 1 * (x * (1 + Real.log x))) := by
  set A : ℝ := max (max (Real.log T) |Real.log v|) 1 with hA
  have hA1 : (1:ℝ) ≤ A := le_max_right _ _
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hlogx : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hterm1 : T ^ x ≤ Real.exp (A * (x * (1 + Real.log x))) := by
    rw [Real.rpow_def_of_pos hTpos]
    refine Real.exp_le_exp.mpr ?_
    have hlogT : Real.log T ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
    have hxle : x ≤ x * (1 + Real.log x) := by nlinarith [hlogx, hxpos.le]
    calc Real.log T * x ≤ A * x := mul_le_mul_of_nonneg_right hlogT hxpos.le
      _ ≤ A * (x * (1 + Real.log x)) :=
          mul_le_mul_of_nonneg_left hxle (by linarith)
  have hterm2 : v ^ (-x) * Real.exp (x * Real.log x)
      ≤ Real.exp (A * (x * (1 + Real.log x))) := by
    rw [Real.rpow_def_of_pos hv, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hlogv : |Real.log v| ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
    have h1 : -Real.log v ≤ |Real.log v| := neg_le_abs _
    have h2 : Real.log v * (-x) ≤ A * x := by
      have hstep : -Real.log v * x ≤ A * x :=
        mul_le_mul_of_nonneg_right (le_trans h1 hlogv) hxpos.le
      linarith [hstep]
    have h3 : x * Real.log x ≤ A * (x * Real.log x) := by
      nlinarith [mul_nonneg hxpos.le hlogx, hA1]
    calc Real.log v * (-x) + x * Real.log x
        ≤ A * x + A * (x * Real.log x) := by linarith
      _ = A * (x * (1 + Real.log x)) := by ring
  unfold tailBound
  calc M * T ^ x + C * (v ^ (-x) * Real.exp (x * Real.log x))
      ≤ M * Real.exp (A * (x * (1 + Real.log x)))
        + C * Real.exp (A * (x * (1 + Real.log x))) :=
        add_le_add (mul_le_mul_of_nonneg_left hterm1 hM)
          (mul_le_mul_of_nonneg_left hterm2 hC)
    _ = (M + C) * Real.exp (A * (x * (1 + Real.log x))) := by ring

/-! ### From `max ‖s‖ 1` to `‖s‖`

The bound comes out at `max ‖s‖ 1`, while the consumer wants `‖s‖`.  The two
differ by at most an additive `2` in the exponent, because `t·(1 + log t) ≥ −1`
on `[0,1]` — which follows from `log t ≥ 1 − 1/t`, i.e. `t·log t ≥ t − 1`. -/

theorem mul_one_add_log_ge_neg_one {t : ℝ} (ht : 0 ≤ t) :
    -1 ≤ t * (1 + Real.log t) := by
  rcases eq_or_lt_of_le ht with rfl | ht0
  · simp
  · have hinv : Real.log (1 / t) ≤ 1 / t - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [one_div, Real.log_inv] at hinv
    have hlog : 1 - 1 / t ≤ Real.log t := by
      rw [one_div]; linarith
    have hmul : t * (1 - 1 / t) ≤ t * Real.log t :=
      mul_le_mul_of_nonneg_left hlog ht0.le
    have hsimp : t * (1 - 1 / t) = t - 1 := by field_simp
    rw [hsimp] at hmul
    nlinarith [hmul, ht0.le]

theorem max_one_mul_one_add_log_le {t : ℝ} (ht : 0 ≤ t) :
    max t 1 * (1 + Real.log (max t 1)) ≤ t * (1 + Real.log t) + 2 := by
  rcases lt_or_ge t 1 with h | h
  · rw [max_eq_right h.le, Real.log_one]
    have := mul_one_add_log_ge_neg_one ht
    linarith
  · rw [max_eq_left h]; linarith

/-- `x ↦ x(1 + log x)` is monotone on `[1, ∞)`. -/
theorem mul_one_add_log_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x * (1 + Real.log x) ≤ y * (1 + Real.log y) := by
  have hy : (1:ℝ) ≤ y := le_trans hx hxy
  have hlx : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ Real.log y :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hx) hxy
  nlinarith [hlx, hlog, hx, hxy]

end Cvs.Zeta
