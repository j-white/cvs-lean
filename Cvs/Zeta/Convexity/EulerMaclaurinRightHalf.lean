import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Convexity.EulerMaclaurinKernel
import Cvs.Zeta.Convexity.EulerMaclaurinPieces

/-!
# The Euler–Maclaurin identity for `σ > 1`

ζ(s) = s/(s-1) - s·∫₁^∞ {x}·x^{-s-1} dx for `1 < Re s`.
-/

open Complex MeasureTheory Set Filter

namespace Cvs.ZetaGrowth

/-- The real analogue of `EulerMaclaurinPieces.integral_indicator_term`, for the dominating norms. -/
theorem integral_norm_indicator_term {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ x in Ioi (1 : ℝ), ‖(if ((n : ℝ) + 1) ≤ x then (x : ℂ) ^ (-s - 1) else 0)‖)
      = ((n : ℝ) + 1) ^ (-s.re) / s.re := by
  have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hapos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hnorm : ∀ x ∈ Ioi (1 : ℝ),
      ‖(if ((n : ℝ) + 1) ≤ x then (x : ℂ) ^ (-s - 1) else 0)‖
        = Set.indicator (Ici ((n : ℝ) + 1)) (fun y : ℝ => y ^ (-s.re - 1)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    by_cases hc : ((n : ℝ) + 1) ≤ x
    · rw [if_pos hc, Set.indicator_of_mem (Set.mem_Ici.mpr hc),
        Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      congr 1
    · rw [if_neg hc, Set.indicator_of_notMem (by simpa using hc), norm_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hnorm,
    MeasureTheory.setIntegral_indicator measurableSet_Ici]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hset : Ioi (1 : ℝ) ∩ Ici (((0 : ℕ) : ℝ) + 1) = Ioi (1 : ℝ) := by
      rw [Set.inter_eq_left]; simpa using Set.Ioi_subset_Ici_self
    rw [hset, integral_Ioi_rpow_of_lt (by linarith) one_pos]
    rw [show (-s.re - 1 + 1) = -s.re by ring, Real.one_rpow]
    norm_num
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1a : (1 : ℝ) < (n : ℝ) + 1 := by linarith
    have hset : Ioi (1 : ℝ) ∩ Ici ((n : ℝ) + 1) = Ici ((n : ℝ) + 1) := by
      rw [Set.inter_eq_right]; intro x hx; exact lt_of_lt_of_le h1a hx
    rw [hset, MeasureTheory.integral_Ici_eq_integral_Ioi,
      integral_Ioi_rpow_of_lt (by linarith) hapos]
    rw [show (-s.re - 1 + 1) = -s.re by ring]
    field_simp

/-- **`∫₁^∞ ⌊x⌋·x^{-s-1} dx = ζ(s)/s` for `σ > 1`.**  The floor is a sum of indicators, and
each indicator integrates to `(n+1)^{-s}/s`. -/
theorem integral_floor_eq {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) = riemannZeta s / s := by
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 0 := by intro h; rw [h] at hs0; simp at hs0
  have hre : (-s - 1).re < -1 := by simp; linarith
  have hfint : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hre one_pos
  -- the indicator family
  set F : ℕ → ℝ → ℂ := fun n x => if ((n : ℝ) + 1) ≤ x then (x : ℂ) ^ (-s - 1) else 0 with hF
  have hFint : ∀ n, IntegrableOn (F n) (Ioi (1 : ℝ)) := by
    intro n
    have hind : F n = Set.indicator (Ici ((n : ℝ) + 1)) (fun y : ℝ => (y : ℂ) ^ (-s - 1)) := by
      funext x
      by_cases hc : ((n : ℝ) + 1) ≤ x
      · rw [hF]; simp only; rw [if_pos hc, Set.indicator_of_mem (Set.mem_Ici.mpr hc)]
      · rw [hF]; simp only; rw [if_neg hc, Set.indicator_of_notMem (by simpa using hc)]
    rw [hind]
    exact hfint.indicator measurableSet_Ici
  have hFsum : Summable (fun n : ℕ => ∫ x in Ioi (1 : ℝ), ‖F n x‖) := by
    have hval : ∀ n : ℕ, (∫ x in Ioi (1 : ℝ), ‖F n x‖) = ((n : ℝ) + 1) ^ (-s.re) / s.re :=
      fun n => integral_norm_indicator_term hs0 n
    refine Summable.congr ?_ (fun n => (hval n).symm)
    have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re)) := by
      have := Real.summable_one_div_nat_rpow (p := s.re)
      have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s.re) := by
        have hshift := (summable_nat_add_iff 1).mpr (this.mpr hs)
        refine hshift.congr (fun n => ?_)
        push_cast; ring_nf
      refine h2.congr (fun n => ?_)
      rw [Real.rpow_neg (by positivity), one_div]
    exact hsum.div_const _
  -- the pointwise expansion
  have hptwise : ∀ x ∈ Ioi (1 : ℝ), (∑' n : ℕ, F n x) = ((⌊x⌋ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one hx)
    exact Cvs.ZetaGrowth.tsum_indicator_eq_floor hx0 _
  calc (∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      = ∫ x in Ioi (1 : ℝ), ∑' n : ℕ, F n x := by
        exact (setIntegral_congr_fun measurableSet_Ioi hptwise).symm
    _ = ∑' n : ℕ, ∫ x in Ioi (1 : ℝ), F n x :=
        (MeasureTheory.integral_tsum_of_summable_integral_norm hFint hFsum).symm
    _ = ∑' n : ℕ, ((n : ℂ) + 1) ^ (-s) / s := by
        exact tsum_congr (fun n => Cvs.ZetaGrowth.integral_indicator_term hs0 n)
    _ = riemannZeta s / s := by
        rw [tsum_div_const]
        congr 1
        rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
        exact tsum_congr (fun n => by rw [Complex.cpow_neg, one_div])

/-- **The Euler–Maclaurin identity, for `σ > 1`.** ζ(s) = s/(s-1) - s·∫₁^∞ {x}·x^{-s-1} dx The
right-hand side makes sense for `σ > 0` (`EulerMaclaurinKernel`), which is what makes this the closed form
that continues `ζ` past `σ = 1`; the continuation itself is a separate step. -/
theorem euler_maclaurin {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * ∫ x in Ioi (1 : ℝ), Cvs.ZetaGrowth.emKernel s x := by
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 0 := by intro h; rw [h] at hs0; simp at hs0
  have hs1ne : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination h
    rw [this] at hs; simp at hs
  have hrex : (-s).re < -1 := by simp; linarith
  have hxsint : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hrex one_pos
  have hemint := Cvs.ZetaGrowth.integrableOn_emKernel hs0
  -- `{x}·x^{-s-1} = x^{-s} - ⌊x⌋·x^{-s-1}`, rearranged
  have hsplit : ∀ x ∈ Ioi (1 : ℝ), ((⌊x⌋ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      = (x : ℂ) ^ (-s) - Cvs.ZetaGrowth.emKernel s x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hxne : (x : ℂ) ≠ 0 := by
      simpa using ne_of_gt hx0
    have hpow : (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
      have hadd := Complex.cpow_add (1 : ℂ) (-s - 1) hxne
      rw [Complex.cpow_one, show (1 : ℂ) + (-s - 1) = -s by ring] at hadd
      exact hadd.symm
    have hfr : ((Int.fract x : ℝ) : ℂ) = (x : ℂ) - ((⌊x⌋ : ℝ) : ℂ) := by
      rw [Int.fract]
      push_cast
      ring
    rw [Cvs.ZetaGrowth.emKernel, hfr]
    linear_combination hpow
  have hflint : IntegrableOn (fun x : ℝ => ((⌊x⌋ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) :=
    (hxsint.sub hemint).congr_fun (fun x hx => (hsplit x hx).symm) measurableSet_Ioi
  have hxint : (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt hrex one_pos, Complex.ofReal_one,
      show (-s) + 1 = 1 - s by ring, Complex.one_cpow]
    field_simp
    rw [show (1 : ℂ) - s = -(s - 1) by ring, div_neg, div_self hs1ne]
    norm_num
  have hcalc : riemannZeta s / s = 1 / (s - 1) - ∫ x in Ioi (1 : ℝ), Cvs.ZetaGrowth.emKernel s x := by
    rw [← integral_floor_eq hs, setIntegral_congr_fun measurableSet_Ioi hsplit,
      MeasureTheory.integral_sub hxsint hemint, hxint]
  field_simp at hcalc
  field_simp
  linear_combination hcalc

end Cvs.ZetaGrowth
