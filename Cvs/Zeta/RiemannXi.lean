import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Hadamard
import Cvs.Zeta.MellinSplit
import Cvs.Zeta.ThetaDecay
import Cvs.Zeta.Weierstrass

/-
**The completed zeta function `ξ`, and its order-1 growth.**

`Cvs.Zeta.ThetaDecay` proves the growth bound for `Λ₀ = completedRiemannZeta₀`.
That is *not* the function the ladder wants.  `Λ₀ = Λ + 1/s + 1/(1−s)` differs
from `Λ = π^{−s/2}Γ(s/2)ζ(s)` by the two pole terms, so at a nontrivial zero `ρ`
one has `Λ(ρ) = 0` but `Λ₀(ρ) = 1/ρ + 1/(1−ρ) ≠ 0`: **the zeros of `Λ₀` are not
the zeros of `ζ`.**

The function whose zeros *are* the nontrivial zeros of `ζ` is

    `ξ(s) = ½·s·(s−1)·Λ(s)`,

and eliminating `Λ` in favour of the entire `Λ₀` gives

    `ξ(s) = ½·s·(s−1)·Λ₀(s) + ½`,

since `½s(s−1)·(−1/s) = −½(s−1)` and `½s(s−1)·(−1/(1−s)) = ½s`, which sum to `½`.
Taking that as the definition makes `ξ` manifestly entire and gives `ξ(0) = ½`
outright — the nonvanishing at the origin that Jensen's formula needs, and which
`Λ₀` supplies only as `(γ − log 4π)/2 + 1 ≈ 0.023`, awkward to bound away from `0`.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex

/-- The completed zeta function `ξ(s) = ½·s·(s−1)·Λ(s)`, written via the entire
`Λ₀` so that entirety is definitional. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s / 2 + 1 / 2

/-- `ξ` is entire. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  intro z
  refine DifferentiableAt.add ?_ (differentiableAt_const _)
  refine DifferentiableAt.div_const ?_ _
  exact ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
    (differentiable_completedZeta₀ z))

/-- **`ξ(0) = ½`.**  The pole terms of `Λ₀` cancel the `s(s−1)` factor exactly. -/
@[simp] theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  simp [riemannXi]

theorem riemannXi_zero_ne_zero : riemannXi 0 ≠ 0 := by
  rw [riemannXi_zero]
  norm_num

/-- `ξ` is analytic on all of `ℂ`, in the form the zero-counting machinery
consumes. -/
theorem analyticOnNhd_riemannXi : AnalyticOnNhd ℂ riemannXi Set.univ :=
  fun z _ => differentiable_riemannXi.analyticAt z

/-! ### `ξ` has order 1, maximal type

`ThetaDecay`'s bound on `Λ₀` transfers: the extra factor `½·s·(s−1)` is
polynomial, and `(t+1)² ≤ e^{2t}` absorbs it into the exponential.  The additive
`½` is absorbed too, using `t·(1 + log t) ≥ −1` to bound `exp` from below. -/

theorem norm_le_mul_one_add_log_add_two {t : ℝ} (ht : 0 ≤ t) :
    t ≤ t * (1 + Real.log t) + 2 := by
  rcases lt_or_ge t 1 with h | h
  · have := mul_one_add_log_ge_neg_one ht
    linarith
  · have hlog : (0:ℝ) ≤ Real.log t := Real.log_nonneg h
    nlinarith [ht, hlog]

/-- **Rung 2, for `ξ`.**  Exactly the hypothesis of
`summable_inv_norm_sq_zeroSeq_of_growth_rlogr`. -/
theorem exists_growth_bound_riemannXi :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ,
      ‖riemannXi s‖ ≤ C * Real.exp (A * (‖s‖ * (1 + Real.log ‖s‖))) := by
  obtain ⟨C, A, hC, hA, hb⟩ := exists_growth_bound_completedRiemannZeta₀
  refine ⟨max (C * Real.exp 4 / 2 + Real.exp (A + 2) / 2) 1, A + 2,
    le_max_right _ _, by linarith, fun s => ?_⟩
  set t : ℝ := ‖s‖ with ht
  set u : ℝ := t * (1 + Real.log t) with hu
  have ht0 : (0:ℝ) ≤ t := norm_nonneg s
  have hu1 : (-1:ℝ) ≤ u := mul_one_add_log_ge_neg_one ht0
  have htu : t ≤ u + 2 := norm_le_mul_one_add_log_add_two ht0
  -- the polynomial factor
  have hpoly : t * (t + 1) / 2 ≤ Real.exp (2 * t) / 2 := by
    have h1 : t + 1 ≤ Real.exp t := by
      have := Real.add_one_le_exp t; linarith
    have hexp : Real.exp (2 * t) = Real.exp t * Real.exp t := by
      rw [show (2:ℝ) * t = t + t by ring, Real.exp_add]
    have h2 : (t + 1) * (t + 1) ≤ Real.exp t * Real.exp t :=
      mul_le_mul h1 h1 (by linarith) (Real.exp_pos t).le
    rw [hexp]
    nlinarith [h2, ht0]
  have hexp2t : Real.exp (2 * t) ≤ Real.exp 4 * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  -- the main term
  have hmain : ‖riemannXi s‖ ≤ t * (t + 1) / 2 * (C * Real.exp (A * u)) + 1 / 2 := by
    unfold riemannXi
    refine le_trans (norm_add_le _ _) (add_le_add ?_ (by norm_num))
    rw [norm_div, norm_mul, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have hs1 : ‖s - 1‖ ≤ t + 1 := by
      refine le_trans (norm_sub_le _ _) ?_
      simp [ht]
    have hL := hb s
    rw [← ht, ← hu] at hL
    have hprod : ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖
        ≤ (t * (t + 1)) * (C * Real.exp (A * u)) := by
      refine mul_le_mul ?_ hL (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hs1 ht0
    calc ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ / 2
        ≤ (t * (t + 1)) * (C * Real.exp (A * u)) / 2 := by linarith [hprod]
      _ = t * (t + 1) / 2 * (C * Real.exp (A * u)) := by ring
  refine le_trans hmain ?_
  have hEpos : (0:ℝ) < Real.exp ((A + 2) * u) := Real.exp_pos _
  have hterm1 : t * (t + 1) / 2 * (C * Real.exp (A * u))
      ≤ C * Real.exp 4 / 2 * Real.exp ((A + 2) * u) := by
    have hstep : t * (t + 1) / 2 * (C * Real.exp (A * u))
        ≤ Real.exp 4 * Real.exp (2 * u) / 2 * (C * Real.exp (A * u)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith [hpoly, hexp2t]
    refine le_trans hstep (le_of_eq ?_)
    have hcomb : Real.exp (2 * u) * Real.exp (A * u) = Real.exp ((A + 2) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp 4 * Real.exp (2 * u) / 2 * (C * Real.exp (A * u))
        = C * Real.exp 4 / 2 * (Real.exp (2 * u) * Real.exp (A * u)) := by ring
      _ = C * Real.exp 4 / 2 * Real.exp ((A + 2) * u) := by rw [hcomb]
  have hterm2 : (1:ℝ) / 2 ≤ Real.exp (A + 2) / 2 * Real.exp ((A + 2) * u) := by
    have hlow : Real.exp (-(A + 2)) ≤ Real.exp ((A + 2) * u) :=
      Real.exp_le_exp.mpr (by nlinarith [hu1, hA])
    have : Real.exp (A + 2) * Real.exp (-(A + 2)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [hlow, Real.exp_pos (A + 2)]
  have hsum : C * Real.exp 4 / 2 * Real.exp ((A + 2) * u)
      + Real.exp (A + 2) / 2 * Real.exp ((A + 2) * u)
      ≤ max (C * Real.exp 4 / 2 + Real.exp (A + 2) / 2) 1 * Real.exp ((A + 2) * u) := by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hEpos.le
  linarith

/-! ### The ladder reaches `ζ`

`ξ` is entire (`analyticOnNhd_riemannXi`), nonzero at the origin
(`riemannXi_zero_ne_zero`), and of order 1 with maximal type
(`exists_growth_bound_riemannXi`).  Those are exactly the three hypotheses of
`summable_inv_norm_sq_zeroSeq_of_growth_rlogr`, so rungs 1, 2 and 4 compose. -/

/-- **`Σ_ρ |ρ|⁻² < ∞` for the zeros of `ξ`.**  The zeros of modulus `≥ 1`,
counted with multiplicity, are square-summable. -/
theorem summable_inv_norm_sq_riemannXi :
    Summable fun n : zeroIndex riemannXi => ‖zeroSeq riemannXi n‖⁻¹ ^ 2 := by
  obtain ⟨C, A, hC, hA, hb⟩ := exists_growth_bound_riemannXi
  exact summable_inv_norm_sq_zeroSeq_of_growth_rlogr analyticOnNhd_riemannXi
    riemannXi_zero_ne_zero hC hA hb

/-- **It is entire.** -/
theorem differentiable_tprod_riemannXi :
    Differentiable ℂ fun z : ℂ =>
      ∏' n : zeroIndex riemannXi, weierstrassE1 (z / zeroSeq riemannXi n) :=
  differentiable_tprod_weierstrassE1_div summable_inv_norm_sq_riemannXi

/-! ### `ξ` is the classical completed zeta

The definition above is `½s(s−1)Λ₀(s) + ½`.  Mathlib's `completedRiemannZeta_eq`
says `Λ = Λ₀ − 1/s − 1/(1−s)`, and the two pole terms contribute
`½s(s−1)·(−1/s) = −½(s−1)` and `½s(s−1)·(−1/(1−s)) = ½s`, summing to `½`.  So
away from `s = 0, 1` the definition agrees with `½·s·(s−1)·Λ(s)`. -/

theorem riemannXi_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h
    exact hs1 (by linear_combination -h)
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp
  ring

/-- **The zeros of `ξ` away from `0` and `1` are the zeros of `Λ`.**  Since
`Λ = π^{−s/2}·Γ(s/2)·ζ(s)` and neither `π^{−s/2}` nor `1/Γ(s/2)` vanishes, these
are exactly the nontrivial zeros of `ζ`. -/
theorem riemannXi_eq_zero_iff {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = 0 ↔ completedRiemannZeta s = 0 := by
  rw [riemannXi_eq hs0 hs1]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  constructor
  · intro h
    have := div_eq_zero_iff.mp h
    rcases this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · rcases mul_eq_zero.mp h'' with h₃ | h₃
        · exact absurd h₃ hs0
        · exact absurd h₃ hsub
      · exact h''
    · exact absurd h' (by norm_num)
  · intro h
    rw [h]
    ring

/-- **`ξ`'s zeros in the right half-plane are exactly `ζ`'s.** For `Re s > 0`, `s ≠ 1`, Mathlib's
`riemannZeta_def_of_ne_zero` gives `ζ = Λ / Γ_ℝ`, and `Gammaℝ_ne_zero_of_re_pos` says the
denominator does not vanish there. -/
theorem riemannXi_eq_zero_iff_riemannZeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  rw [riemannXi_eq_zero_iff hs0 hs1, riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff]
  constructor
  · exact fun h => Or.inl h
  · rintro (h | h)
    · exact h
    · exact absurd h (Complex.Gammaℝ_ne_zero_of_re_pos hs)

/-! ### `ξ` is nowhere locally zero

Mathlib's finite-divisor factorisation `MeromorphicOn.extract_zeros_poles`
requires the order to be finite at every point — i.e. the function must not
vanish identically near any point.  For `ξ` this follows from the identity
theorem: `ℂ` is preconnected and `ξ(0) = ½ ≠ 0`. -/

theorem analyticOrderAt_riemannXi_ne_top (u : ℂ) :
    analyticOrderAt riemannXi u ≠ ⊤ := by
  intro htop
  have hev : riemannXi =ᶠ[nhds u] 0 := analyticOrderAt_eq_top.mp htop
  have hall : Set.EqOn riemannXi 0 Set.univ :=
    analyticOnNhd_riemannXi.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ u) hev
  have h0 : riemannXi 0 = 0 := hall (Set.mem_univ 0)
  rw [riemannXi_zero] at h0
  norm_num at h0

/-!
### Local Hadamard for `ξ`, from Mathlib

`MeromorphicOn.extract_zeros_poles` needs three things: meromorphy, finite divisor support,
and finite order everywhere.
-/

theorem meromorphicOrderAt_riemannXi_ne_top (u : ℂ) :
    meromorphicOrderAt riemannXi u ≠ ⊤ := by
  have hA : AnalyticAt ℂ riemannXi u := differentiable_riemannXi.analyticAt u
  rw [hA.meromorphicOrderAt_eq]
  simpa using analyticOrderAt_riemannXi_ne_top u

/-! ### Hadamard's factorisation of `ξ`

Everything is in place: `Q·P` has the same divisor as `ξ`
(`divisor_finiteFactor_mul_tprod`), both have finite order everywhere, and
`eq_mul_exp_of_divisor_eq'` turns that into a pointwise identity. -/

/-- The zeros of `ξ` strictly inside the unit disc — finitely many. -/
theorem finite_xiSmallZeros :
    {u : ℂ | ‖u‖ < 1 ∧ (MeromorphicOn.divisor riemannXi Set.univ u : ℤ) ≠ 0}.Finite :=
  (finite_setOf_divisor_ne_zero analyticOnNhd_riemannXi 1).subset
    (fun u hu => ⟨hu.1.le, hu.2⟩)

/-- **Hadamard's factorisation of `ξ`.** -/
theorem hadamard_riemannXi :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z : ℂ,
      riemannXi z
        = finiteFactor finite_xiSmallZeros.toFinset
            (fun u => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat) z
          * (∏' n : zeroIndex riemannXi, weierstrassE1 (z / zeroSeq riemannXi n))
          * Complex.exp (h z) := by
  classical
  set S : Finset ℂ := finite_xiSmallZeros.toFinset with hSdef
  set m : ℂ → ℕ :=
    fun u => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat with hmdef
  set φ : ℂ → ℂ := fun z : ℂ => finiteFactor S m z
    * ∏' n : zeroIndex riemannXi, weierstrassE1 (z / zeroSeq riemannXi n) with hφdef
  have hS : ∀ u ∈ S, ‖u‖ < 1 := by
    intro u hu
    rw [hSdef, Set.Finite.mem_toFinset] at hu
    exact hu.1
  have hSall : ∀ u : ℂ, ‖u‖ < 1 →
      (MeromorphicOn.divisor riemannXi Set.univ u : ℤ) ≠ 0 → u ∈ S := by
    intro u h1 h2
    rw [hSdef, Set.Finite.mem_toFinset]
    exact ⟨h1, h2⟩
  have hφana : AnalyticOnNhd ℂ φ Set.univ := by
    intro z _
    exact ((differentiable_finiteFactor S m).mul
      (differentiable_tprod_weierstrassE1_div summable_inv_norm_sq_riemannXi)).analyticAt z
  have hdiv : MeromorphicOn.divisor φ Set.univ
      = MeromorphicOn.divisor riemannXi Set.univ :=
    divisor_finiteFactor_mul_tprod analyticOnNhd_riemannXi
      summable_inv_norm_sq_riemannXi hS (fun u _ => rfl) hSall
      analyticOrderAt_riemannXi_ne_top
  have hfinφ : ∀ z : ℂ, meromorphicOrderAt φ z ≠ ⊤ := by
    intro z
    rw [(hφana z (Set.mem_univ z)).meromorphicOrderAt_eq,
      analyticOrderAt_finiteFactor_mul_tprod summable_inv_norm_sq_riemannXi
        hS (fun u _ => rfl) hSall z]
    simp
  obtain ⟨h, hhdiff, hh⟩ := eq_mul_exp_of_divisor_eq' analyticOnNhd_riemannXi hφana
    meromorphicOrderAt_riemannXi_ne_top hfinφ hdiv
  refine ⟨h, hhdiff, fun z => ?_⟩
  rw [hh z, hφdef]

/-!
### The logarithmic derivative

Guinand–Weil consumes `ξ'/ξ`, not `ξ`.
-/

end Cvs.Zeta
