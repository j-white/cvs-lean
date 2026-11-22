import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Convexity.EulerMaclaurinKernel
import Cvs.Zeta.Convexity.EulerMaclaurinPositive

/-!
# The truncated Euler–Maclaurin identity

ζ₀(s) = ∑_{n≤N} n^{-s} + (N^{1-s} - 1)/(s-1) - s·∫_N^∞ {x}·x^{-s-1} dx
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral

namespace Cvs.ZetaGrowth

variable {s : ℂ}

/-- On `(N, N+1)` the fractional part is `x - N`. -/
theorem fract_on_unit {N : ℕ} {x : ℝ} (hx : x ∈ Ioo ((N : ℝ)) ((N : ℝ) + 1)) :
    (Int.fract x : ℝ) = x - N := by
  have hfl : ⌊x⌋ = (N : ℤ) := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · push_cast; exact le_of_lt hx.1
    · push_cast; exact hx.2
  rw [Int.fract, hfl]
  push_cast
  ring

/-- **The unit-interval integral.** -/
theorem integral_unit (hs0 : s ≠ 0) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in ((N : ℝ))..((N : ℝ) + 1), Cvs.ZetaGrowth.emKernel s x)
      = (((N : ℂ) + 1) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)
        - (N : ℂ) * ((N : ℂ) ^ (-s) - ((N : ℂ) + 1) ^ (-s)) / s := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc ((N : ℝ)) ((N : ℝ) + 1) := by
    rw [Set.uIcc_of_le hle]
    intro hc
    exact absurd hc.1 (by linarith)
  have hcpow : ∀ (w : ℂ), ContinuousOn (fun x : ℝ => (x : ℂ) ^ w)
      (Set.uIcc ((N : ℝ)) ((N : ℝ) + 1)) := by
    intro w x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hN0 hx.1
    exact (Complex.continuousAt_ofReal_cpow_const x w
      (Or.inr (ne_of_gt hx0))).continuousWithinAt
  have hint1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume
      ((N : ℝ)) ((N : ℝ) + 1) := (hcpow (-s)).intervalIntegrable
  have hint2 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) MeasureTheory.volume
      ((N : ℝ)) ((N : ℝ) + 1) := (hcpow (-s - 1)).intervalIntegrable
  -- rewrite the integrand a.e.
  have hae : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc ((N : ℝ)) ((N : ℝ) + 1) →
      Cvs.ZetaGrowth.emKernel s x = ((x : ℂ) - (N : ℂ)) * (x : ℂ) ^ (-s - 1) := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
      (Real.volume_singleton (a := (N : ℝ) + 1))] with x hx hmem
    rw [Set.uIoc_of_le hle] at hmem
    have hxne : x ≠ (N : ℝ) + 1 := by simpa using hx
    have hxo : x ∈ Ioo ((N : ℝ)) ((N : ℝ) + 1) :=
      ⟨hmem.1, lt_of_le_of_ne hmem.2 hxne⟩
    rw [Cvs.ZetaGrowth.emKernel, fract_on_unit hxo]
    push_cast
    ring
  rw [intervalIntegral.integral_congr_ae hae]
  have hpt : ∀ x ∈ Set.uIcc ((N : ℝ)) ((N : ℝ) + 1),
      ((x : ℂ) - (N : ℂ)) * (x : ℂ) ^ (-s - 1)
        = (x : ℂ) ^ (-s) - (N : ℂ) * (x : ℂ) ^ (-s - 1) := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hN0 hx.1
    have hxne : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx0
    have hpow : (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
      have hadd := Complex.cpow_add (1 : ℂ) (-s - 1) hxne
      rw [Complex.cpow_one, show (1 : ℂ) + (-s - 1) = -s by ring] at hadd
      exact hadd.symm
    linear_combination hpow
  have hsplit : (∫ x in ((N : ℝ))..((N : ℝ) + 1), ((x : ℂ) - (N : ℂ)) * (x : ℂ) ^ (-s - 1))
      = (∫ x in ((N : ℝ))..((N : ℝ) + 1), (x : ℂ) ^ (-s))
        - (N : ℂ) * ∫ x in ((N : ℝ))..((N : ℝ) + 1), (x : ℂ) ^ (-s - 1) := by
    rw [intervalIntegral.integral_congr hpt,
      intervalIntegral.integral_sub hint1 (hint2.const_mul _),
      intervalIntegral.integral_const_mul]
  rw [hsplit]
  rw [integral_cpow (Or.inr ⟨by
        intro hc
        apply hs1
        have : s = 1 := by linear_combination -hc
        exact this, hzero⟩),
    integral_cpow (Or.inr ⟨by
        intro hc
        apply hs0
        linear_combination -hc, hzero⟩)]
  push_cast
  rw [show (-s) + 1 = 1 - s by ring, show (-s - 1) + 1 = -s by ring]
  field_simp
  ring

theorem intervalIntegrable_emKernel (hs : 0 < s.re) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (Cvs.ZetaGrowth.emKernel s) MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine (Cvs.ZetaGrowth.integrableOn_emKernel hs).mono_set ?_
  intro x hx
  exact lt_of_le_of_lt ha hx.1

/-- `x^{1-s} = x·x^{-s}` for `x ≠ 0`. -/
theorem cpow_one_sub {x : ℂ} (hx : x ≠ 0) : x ^ (1 - s) = x * x ^ (-s) := by
  have hadd := Complex.cpow_add (1 : ℂ) (-s) hx
  rw [Complex.cpow_one, show (1 : ℂ) + (-s) = 1 - s by ring] at hadd
  exact hadd

/-- **The finite Euler–Maclaurin identity.**  Everything here is a finite integral and a finite
sum, so it is an induction on `N` with `integral_unit` as the step. -/
theorem finite_identity (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∀ N : ℕ, 1 ≤ N →
      s * ∫ x in (1 : ℝ)..((N : ℝ)), Cvs.ZetaGrowth.emKernel s x
        = 1 - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - ((N : ℂ) ^ (1 - s) - 1) / (s - 1) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs1
  intro N
  induction N with
  | zero => intro h; omega
  | succ M ih =>
    intro _
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · have h0 : (((0 : ℕ) + 1 : ℕ) : ℝ) = 1 := by norm_num
      rw [h0, intervalIntegral.integral_same, mul_zero]
      norm_num [Finset.Icc_self, Finset.sum_singleton, Complex.one_cpow]
    · have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hMne : ((M : ℂ)) ≠ 0 := by
        intro hc
        have hre : ((M : ℂ)).re = 0 := by rw [hc]; simp
        simp only [Complex.natCast_re] at hre
        linarith
      have hM1ne : ((M : ℂ) + 1) ≠ 0 := by
        intro hc
        have hre : (((M : ℂ) + 1)).re = 0 := by rw [hc]; simp
        simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at hre
        linarith
      have hadj : (∫ x in (1 : ℝ)..((M : ℝ)), Cvs.ZetaGrowth.emKernel s x)
          + (∫ x in ((M : ℝ))..((M : ℝ) + 1), Cvs.ZetaGrowth.emKernel s x)
          = ∫ x in (1 : ℝ)..((M : ℝ) + 1), Cvs.ZetaGrowth.emKernel s x :=
        intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_emKernel hs le_rfl hM1)
          (intervalIntegrable_emKernel hs hM1 (by linarith))
      have hstep := integral_unit (s := s) hs0 hs1 hM
      have hsum : (∑ n ∈ Finset.Icc 1 (M + 1), (n : ℂ) ^ (-s))
          = (∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s)) + ((M : ℂ) + 1) ^ (-s) := by
        rw [Finset.sum_Icc_succ_top (by omega)]
        push_cast
        ring
      have hprev := ih hM
      have hcast : (((M + 1 : ℕ) : ℝ)) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast, hsum, ← hadj, mul_add, hprev, hstep]
      have e1 : ((M : ℂ)) ^ (1 - s) = (M : ℂ) * (M : ℂ) ^ (-s) := cpow_one_sub hMne
      have e2 : (((M : ℕ) : ℂ) + 1) ^ (1 - s) = ((M : ℂ) + 1) * ((M : ℂ) + 1) ^ (-s) :=
        cpow_one_sub hM1ne
      push_cast
      rw [e1, e2]
      field_simp
      ring

/-- **The truncated Euler–Maclaurin identity.** ζ₀(s) = ∑_{n≤N} n^{-s} + (N^{1-s} - 1)/(s-1) -
s·∫_N^∞ {x}·x^{-s-1} dx for `σ > 0`, `s ≠ 1`, `N ≥ 1`. -/
theorem euler_maclaurin_trunc (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta₀ s = (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
      + ((N : ℂ) ^ (1 - s) - 1) / (s - 1)
      - s * ∫ x in Ioi ((N : ℝ)), Cvs.ZetaGrowth.emKernel s x := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hun : Ioi (1 : ℝ) = Ioc (1 : ℝ) ((N : ℝ)) ∪ Ioi ((N : ℝ)) := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro hx
      rcases le_or_gt x (N : ℝ) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h)
      · exact h1
      · linarith
  have hdisj : Disjoint (Ioc (1 : ℝ) ((N : ℝ))) (Ioi ((N : ℝ))) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    exact absurd hx.2 (by simpa using hx2)
  have hI1 : MeasureTheory.IntegrableOn (Cvs.ZetaGrowth.emKernel s) (Ioc (1 : ℝ) ((N : ℝ))) :=
    (Cvs.ZetaGrowth.integrableOn_emKernel hs).mono_set (fun x hx => hx.1)
  have hI2 : MeasureTheory.IntegrableOn (Cvs.ZetaGrowth.emKernel s) (Ioi ((N : ℝ))) :=
    (Cvs.ZetaGrowth.integrableOn_emKernel hs).mono_set
      (fun x hx => lt_of_le_of_lt hN1 hx)
  have hsplit : (∫ x in Ioi (1 : ℝ), Cvs.ZetaGrowth.emKernel s x)
      = (∫ x in (1 : ℝ)..((N : ℝ)), Cvs.ZetaGrowth.emKernel s x)
        + ∫ x in Ioi ((N : ℝ)), Cvs.ZetaGrowth.emKernel s x := by
    rw [hun, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hI1 hI2,
      intervalIntegral.integral_of_le hN1]
  rw [Cvs.ZetaGrowth.zeta₀_em hs, hsplit, mul_add, finite_identity hs hs1 N hN]
  ring

end Cvs.ZetaGrowth
