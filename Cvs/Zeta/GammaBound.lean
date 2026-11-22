import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-
**An upper bound on `Γ`.**

Pinned Mathlib has no upper bound on the Gamma function at all — no Stirling, no
monotonicity, nothing in `Analysis/SpecialFunctions/Gamma/`.  That is the missing
analytic ingredient for every order-of-growth argument, rung 2 of the
Guinand–Weil ladder included: `Λ₀`'s Mellin integral is controlled by
`∫₁^∞ e^{−πt}t^{σ}dt`, which is a Gamma value, and bounding it is what turns
"entire" into "order 1".

The proof needs no asymptotics.  Mathlib *does* have log-convexity
(`Real.convexOn_log_Gamma`, the heart of Bohr–Mollerup), and a convex function on
`[n, n+1]` is bounded by the larger of its endpoint values.  At integer points
`Γ` is a factorial, so on `[n, n+1]`

    `Γ(x) ≤ max((n−1)!, n!) = n! ≤ nⁿ ≤ xˣ`.

Hence `Γ(x) ≤ xˣ = exp(x·log x)` for `x ≥ 1`.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Real

/-- **`Γ` is bounded by the factorial of `⌊x⌋`.**  Log-convexity plus the maximum
principle on `[n, n+1]`, where both endpoint values are factorials. -/
theorem Gamma_le_factorial_floor {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ (Nat.factorial ⌊x⌋₊ : ℝ) := by
  set n : ℕ := ⌊x⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn : x ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  -- endpoint values are factorials
  have hΓn : Real.Gamma (n : ℝ) = (Nat.factorial (n - 1) : ℝ) := by
    have : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have : (1 : ℕ) ≤ n := hn1
      push_cast [Nat.cast_sub this]
      ring
    rw [← this, Real.Gamma_nat_eq_factorial]
  have hΓn1 : Real.Gamma ((n : ℝ) + 1) = (Nat.factorial n : ℝ) :=
    Real.Gamma_nat_eq_factorial n
  -- the maximum principle for `log ∘ Γ`
  have hmem : x ∈ Set.Icc ((n : ℝ)) ((n : ℝ) + 1) := ⟨hnx, hxn⟩
  have hmax := Real.convexOn_log_Gamma.le_max_of_mem_Icc
    (Set.mem_Ioi.mpr hnpos) (Set.mem_Ioi.mpr (by linarith)) hmem
  simp only [Function.comp_apply, hΓn, hΓn1] at hmax
  -- `(n−1)! ≤ n!`, so the max is `log n!`
  have hfac : (Nat.factorial (n - 1) : ℝ) ≤ (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.sub_le n 1)
  have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hfacpos' : (0 : ℝ) < (Nat.factorial (n - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 1)
  have hmax' : Real.log (Real.Gamma x) ≤ Real.log (Nat.factorial n : ℝ) := by
    refine hmax.trans ?_
    rw [max_le_iff]
    exact ⟨Real.log_le_log hfacpos' hfac, le_rfl⟩
  -- undo the logarithm
  have hΓpos : (0 : ℝ) < Real.Gamma x := Real.Gamma_pos_of_pos (by linarith)
  exact (Real.log_le_log_iff hΓpos hfacpos).mp hmax'

/-- **`Γ(x) ≤ xˣ`.**  The bound absent from Mathlib. -/
theorem Gamma_le_rpow_self {x : ℝ} (hx : 1 ≤ x) : Real.Gamma x ≤ x ^ x := by
  set n : ℕ := ⌊x⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  refine (Gamma_le_factorial_floor hx).trans ?_
  -- `n! ≤ nⁿ ≤ xⁿ ≤ xˣ`
  have h1 : (Nat.factorial n : ℝ) ≤ ((n : ℝ)) ^ (n : ℕ) := by
    exact_mod_cast Nat.factorial_le_pow n
  have h2 : ((n : ℝ)) ^ (n : ℕ) ≤ x ^ (n : ℕ) := pow_le_pow_left₀ hnpos hnx n
  have h3 : x ^ (n : ℕ) = x ^ ((n : ℕ) : ℝ) := (Real.rpow_natCast x n).symm
  have h4 : x ^ ((n : ℕ) : ℝ) ≤ x ^ x :=
    Real.rpow_le_rpow_of_exponent_le hx hnx
  linarith [h1, h2, h3 ▸ h4]

/-- The exponential form, as growth arguments consume it. -/
theorem Gamma_le_exp_mul_log {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ Real.exp (x * Real.log x) := by
  refine (Gamma_le_rpow_self hx).trans (le_of_eq ?_)
  rw [Real.rpow_def_of_pos (by linarith)]
  ring_nf

/-!
### The Mellin estimate

What order-of-growth arguments actually consume is not `Γ(x)` but the integral `∫₀^∞
t^{x−1}e^{−vt}dt`, which is `Γ(x)/vˣ`.
-/

/-- **The scaled Gamma integral, bounded.**  `∫₀^∞ t^{x−1}e^{−vt}dt ≤ v^{−x}·xˣ`. -/
theorem integral_Ioi_rpow_mul_exp_le {v x : ℝ} (hv : 0 < v) (hx : 1 ≤ x) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (x - 1) * Real.exp (-v * t))
      ≤ v ^ (-x) * Real.exp (x * Real.log x) := by
  have hq : (-1 : ℝ) < x - 1 := by linarith
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := x - 1) (b := v)
    one_pos hq hv
  simp only [Real.rpow_one, div_one, sub_add_cancel, one_div, inv_one, mul_one] at h
  rw [h]
  have hvpos : (0 : ℝ) < v ^ (-x) := Real.rpow_pos_of_pos hv _
  have hxpos : (0 : ℝ) < x := by linarith
  calc v ^ (-x) * Real.Gamma x
      ≤ v ^ (-x) * Real.exp (x * Real.log x) := by
        exact mul_le_mul_of_nonneg_left (Gamma_le_exp_mul_log hx) hvpos.le

/-! ### Integrability of the scaled Gamma integrand

Mathlib proves `Real.GammaIntegral_convergent` only at scale `v = 1`.  The scaled
version follows by the change of variables `u = v·t`
(`integrableOn_Ioi_comp_mul_left_iff`), which turns `(v·t)^{x−1}` into
`v^{x−1}·t^{x−1}` — a constant the integrability is insensitive to. -/

theorem integrableOn_exp_mul_rpow {v x : ℝ} (hv : 0 < v) (hx : 0 < x) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (x - 1) * Real.exp (-v * t)) (Set.Ioi 0) := by
  have hG := Real.GammaIntegral_convergent hx
  have h := (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => Real.exp (-u) * u ^ (x - 1)) 0 hv).mpr (by simpa using hG)
  have h' := h.const_mul ((v ^ (x - 1))⁻¹)
  refine MeasureTheory.IntegrableOn.congr_fun h' (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  have hvx : (v : ℝ) ^ (x - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hv _)
  rw [Real.mul_rpow hv.le ht0.le]
  field_simp

/-- The same, restricted to a tail. -/
theorem integrableOn_exp_mul_rpow_Ioi {v x T : ℝ} (hv : 0 < v) (hx : 0 < x)
    (hT : 0 ≤ T) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (x - 1) * Real.exp (-v * t)) (Set.Ioi T) :=
  (integrableOn_exp_mul_rpow hv hx).mono_set (Set.Ioi_subset_Ioi hT)

end Cvs.Zeta
