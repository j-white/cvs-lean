import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Upstream.EntireNonvanishingExpLog
import Cvs.Zeta.CanonicalProductDivisor
import Cvs.Zeta.LinearCountInverseSquareSum
import Cvs.Zeta.Weierstrass

/-
**Rungs 1 and 4 of the Guinand–Weil ladder, joined.**

`Cvs.Zeta.LinearCountInverseSquareSum` (rung 4) turns a growth bound `‖f z‖ ≤ C·e^{A‖z‖}` into

    `Σ_ρ  ord_ρ(f) · ‖ρ‖⁻²  < ∞`,

a sum over the **divisor** of `f` — points weighted by the order of vanishing.
`Cvs.Zeta.Weierstrass` (rung 1) turns `Σ_n ‖aₙ‖⁻² < ∞` into convergence of the
canonical product `Π E₁(z/aₙ)` — a sum over a **sequence**.

The two do not compose directly: one is indexed by points-with-weights, the
other by a list.  This file supplies the bridge, which is to enumerate each zero
as many times as its order,

    `zeroIndex f = Σ (ρ : ‖ρ‖ ≥ 1), Fin (ord_ρ f)`,

so that `Σ_{zeroIndex} ‖ρ‖⁻²` is literally rung 4's weighted sum regrouped by
fibre.  Zeros of modulus `< 1` are excluded: there are finitely many and they
cannot affect summability, which is the only thing rung 1 needs.

With that, the canonical product over the zeros of an order-1 entire function
converges, is nonzero off the zeros, and converges locally uniformly — Hadamard's
product, built.

Scope: the canonical product and its zero set. Matching multiplicities
(`f/P` entire, vanishing to exactly `ord_ρ(f)`) and the Borel–Carathéodory
bound pinning the exponential factor to degree `1` are separate results; see
the project notes for what is proved.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open MeromorphicOn

/-- The zeros of `f` of modulus `≥ 1`, indexed **with multiplicity**: one index
per zero per unit of vanishing order. -/
abbrev zeroIndex (f : ℂ → ℂ) : Type :=
  Σ u : {u : ℂ // 1 ≤ ‖u‖},
    Fin ((MeromorphicOn.divisor f Set.univ (u : ℂ) : ℤ)).toNat

/-- The enumeration: each zero repeated as often as its order. -/
def zeroSeq (f : ℂ → ℂ) : zeroIndex f → ℂ := fun p => (p.1 : ℂ)

theorem one_le_norm_zeroSeq {f : ℂ → ℂ} (n : zeroIndex f) : 1 ≤ ‖zeroSeq f n‖ :=
  n.1.2

theorem zeroSeq_ne_zero {f : ℂ → ℂ} (n : zeroIndex f) : zeroSeq f n ≠ 0 := by
  intro h
  have := one_le_norm_zeroSeq n
  rw [h, norm_zero] at this
  linarith

/-- **The bridge.** Rung 4's weighted sum over the divisor, regrouped by fibre, is rung 1's
hypothesis for the enumeration-with-multiplicity. -/
theorem summable_inv_norm_sq_zeroSeq_of_divisor {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hmain : Summable fun u : {u : ℂ // 1 ≤ ‖u‖} =>
      ((MeromorphicOn.divisor f Set.univ (u : ℂ) : ℤ) : ℝ) * ‖(u : ℂ)‖⁻¹ ^ 2) :
    Summable fun n : zeroIndex f => ‖zeroSeq f n‖⁻¹ ^ 2 := by
  rw [summable_sigma_of_nonneg (fun n => by positivity)]
  refine ⟨fun u => Summable.of_finite, ?_⟩
  refine hmain.congr fun u => ?_
  have hdiv : (0 : ℤ) ≤ (MeromorphicOn.divisor f Set.univ (u : ℂ) : ℤ) := by
    exact_mod_cast hf.divisor_nonneg (u : ℂ)
  rw [tsum_fintype]
  simp only [zeroSeq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hdiv).symm

/-! ### The canonical product over the zeros -/

/-!
### With the general counting bound

`ZeroCounting.summable_weight_mul_inv_norm_sq_of_counting` replaced the linear hypothesis
`n(r) ≤ K·r` by an arbitrary `N` whose dyadic blocks are summable.
-/

/-- **Counting bound ⟹ the canonical product's hypothesis**, for any admissible
counting function `N`. -/
theorem summable_inv_norm_sq_zeroSeq_of_counting {f : ℂ → ℂ} {N : ℝ → ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hcount : ∀ r : ℝ, 1 ≤ r → ∀ S : Finset {u : ℂ // 1 ≤ ‖u‖},
      (∀ u ∈ S, ‖(u : ℂ)‖ ≤ r) →
      ∑ u ∈ S, ((MeromorphicOn.divisor f Set.univ (u : ℂ) : ℤ) : ℝ) ≤ N r)
    (hN : Summable fun k : ℕ =>
      N ((2 : ℝ) ^ (k + 1)) * (((2 : ℝ)⁻¹) ^ k) ^ 2) :
    Summable fun n : zeroIndex f => ‖zeroSeq f n‖⁻¹ ^ 2 :=
  summable_inv_norm_sq_zeroSeq_of_divisor hf
    (summable_weight_mul_inv_norm_sq_of_counting
      (fun u => by exact_mod_cast hf.divisor_nonneg (u : ℂ))
      (fun u => u.2) hcount hN)

/-- **`ξ`'s counting law suffices.**  With `n(r) ≤ K·r·(1 + log r)` — the shape
Riemann–von Mangoldt gives, and the one exponential type excludes — the canonical
product over the zeros still converges. -/
theorem summable_inv_norm_sq_zeroSeq_of_rlogr {f : ℂ → ℂ} {K : ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hcount : ∀ r : ℝ, 1 ≤ r → ∀ S : Finset {u : ℂ // 1 ≤ ‖u‖},
      (∀ u ∈ S, ‖(u : ℂ)‖ ≤ r) →
      ∑ u ∈ S, ((MeromorphicOn.divisor f Set.univ (u : ℂ) : ℤ) : ℝ)
        ≤ K * r * (1 + Real.log r)) :
    Summable fun n : zeroIndex f => ‖zeroSeq f n‖⁻¹ ^ 2 :=
  summable_inv_norm_sq_zeroSeq_of_counting hf hcount (summable_dyadic_rlogr K)

/-!
### Growth ⟹ counting, for an arbitrary majorant

`ZeroCounting.sum_divisor_le_of_exp_bound` runs Jensen against the *exponential type* majorant
`C·e^{A r}`, which `ξ` does not satisfy.
-/

/-- **Jensen's counting bound with an arbitrary majorant.** -/
theorem sum_divisor_le_of_growth {f : ℂ → ℂ} {M : ℝ → ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ M ‖z‖) {r : ℝ} (hr : 0 < r) (hM : 1 ≤ M (2 * r)) :
    ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) u
      ≤ (Real.log (M (2 * r)) - Real.log ‖f 0‖) / Real.log 2 := by
  have hr2 : (0 : ℝ) < 2 * r := by linarith
  have habsr : |r| = r := abs_of_pos hr
  have habs2r : |(2 * r)| = 2 * r := abs_of_pos hr2
  have hMpos : (0 : ℝ) < M (2 * r) := lt_of_lt_of_le zero_lt_one hM
  have hf0norm : (0 : ℝ) < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hkey := AnalyticOnNhd.sum_divisor_le (c := 0) (r := r) (R := 2 * r)
    (M := M (2 * r))
    (by rw [habsr]; exact hr)
    (by rw [habsr, habs2r]; linarith)
    hM
    (hf.mono (Set.subset_univ _))
    hf0
    (fun z hz => by
      rw [habs2r, mem_sphere_zero_iff_norm] at hz
      calc ‖f z‖ ≤ M ‖z‖ := hbound z
        _ = M (2 * r) := by rw [hz])
  rw [habsr] at hkey
  refine hkey.trans (le_of_eq ?_)
  have hratio : Real.log (2 * r / r) = Real.log 2 := by
    rw [mul_div_assoc, div_self (ne_of_gt hr), mul_one]
  rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hf0norm), hratio]

/-- **The seam, growth-agnostic.**  A partial `Finset` sum of the divisor over
points of modulus `≤ r` is dominated by the `finsum` of the divisor on the closed
disc of radius `r`.  Nothing about growth enters. -/
theorem finset_sum_divisor_le_finsum {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) {r : ℝ}
    (S : Finset ℂ) (hS : ∀ u ∈ S, ‖u‖ ≤ r) :
    ∑ u ∈ S, MeromorphicOn.divisor f Set.univ u
      ≤ ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) u := by
  classical
  have hfb : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) r) :=
    hf.mono (Set.subset_univ _)
  set Dr := MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) with hDr
  have hagree : ∀ u : ℂ, u ∈ Metric.closedBall (0 : ℂ) r →
      MeromorphicOn.divisor f Set.univ u = Dr u := by
    intro u hu
    rw [hDr, MeromorphicOn.divisor_apply hf.meromorphicOn (Set.mem_univ u),
      MeromorphicOn.divisor_apply hfb.meromorphicOn hu]
  have hmem : ∀ u ∈ S, u ∈ Metric.closedBall (0 : ℂ) r := by
    intro u hu
    simpa [Metric.mem_closedBall, dist_zero_right] using hS u hu
  have hnn : ∀ u : ℂ, 0 ≤ Dr u := fun u => hfb.divisor_nonneg u
  have hfins : (Function.support (Dr : ℂ → ℤ)).Finite :=
    Dr.finiteSupport (isCompact_closedBall _ _)
  have hSsum : ∑ u ∈ S, MeromorphicOn.divisor f Set.univ u = ∑ u ∈ S, Dr u :=
    Finset.sum_congr rfl fun u hu => hagree u (hmem u hu)
  have hzero : ∀ x ∈ S, x ∉ S.filter (fun u => Dr u ≠ 0) → Dr x = 0 := by
    intro x hx hnx
    by_contra h
    exact hnx (Finset.mem_filter.mpr ⟨hx, h⟩)
  have heq : ∑ u ∈ S.filter (fun u => Dr u ≠ 0), Dr u = ∑ u ∈ S, Dr u :=
    Finset.sum_subset (Finset.filter_subset _ _) hzero
  have hsub2 : S.filter (fun u => Dr u ≠ 0) ⊆ hfins.toFinset := by
    intro u hu
    rw [Finset.mem_filter] at hu
    simpa [Set.Finite.mem_toFinset, Function.mem_support] using hu.2
  rw [hSsum, ← heq]
  calc ∑ u ∈ S.filter (fun u => Dr u ≠ 0), Dr u
      ≤ ∑ u ∈ hfins.toFinset, Dr u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun u _ _ => hnn u)
    _ = ∑ᶠ u, Dr u :=
        (finsum_eq_finsetSum_of_support_subset (Dr : ℂ → ℤ) (by simp)).symm

/-- **Growth ⟹ counting**, in the `Finset` form the engine consumes. -/
theorem finset_sum_divisor_le_of_growth {f : ℂ → ℂ} {M : ℝ → ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ M ‖z‖) {r : ℝ} (hr : 0 < r) (hM : 1 ≤ M (2 * r))
    (S : Finset ℂ) (hS : ∀ u ∈ S, ‖u‖ ≤ r) :
    ∑ u ∈ S, ((MeromorphicOn.divisor f Set.univ u : ℤ) : ℝ)
      ≤ (Real.log (M (2 * r)) - Real.log ‖f 0‖) / Real.log 2 := by
  calc ∑ u ∈ S, ((MeromorphicOn.divisor f Set.univ u : ℤ) : ℝ)
      = ((∑ u ∈ S, MeromorphicOn.divisor f Set.univ u : ℤ) : ℝ) := by push_cast; ring
    _ ≤ ((∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) u : ℤ) : ℝ) := by
        exact_mod_cast finset_sum_divisor_le_finsum hf S hS
    _ ≤ (Real.log (M (2 * r)) - Real.log ‖f 0‖) / Real.log 2 :=
        sum_divisor_le_of_growth hf hf0 hbound hr hM

/-! ### End to end, at `ξ`'s growth shape -/

/-- **The whole plumbing, in one statement.** For an entire `f` with `f(0) ≠ 0` and `‖f z‖ ≤
C·exp(A·‖z‖·(1 + log‖z‖))` — order 1, *maximal* type allowed — the canonical product over the
zeros of `f` converges. -/
theorem summable_inv_norm_sq_zeroSeq_of_growth_rlogr {f : ℂ → ℂ} {C A : ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * (‖z‖ * (1 + Real.log ‖z‖)))) :
    Summable fun n : zeroIndex f => ‖zeroSeq f n‖⁻¹ ^ 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hf0norm : (0 : ℝ) < ‖f 0‖ := norm_pos_iff.mpr hf0
  set M : ℝ → ℝ := fun t => C * Real.exp (A * (t * (1 + Real.log t))) with hM
  set K : ℝ :=
    (max (Real.log C - Real.log ‖f 0‖) 0 + 2 * A * (1 + Real.log 2)) / Real.log 2 with hK
  refine summable_inv_norm_sq_zeroSeq_of_rlogr (K := K) hf ?_
  intro r hr S hS
  -- transport the `Finset` from the subtype to `ℂ`
  have hinj : ∀ a ∈ S, ∀ b ∈ S, (a : ℂ) = (b : ℂ) → a = b :=
    fun a _ b _ h => Subtype.ext h
  have himg : ∀ u ∈ S.image Subtype.val, ‖u‖ ≤ r := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact hS v hv
  have hsum : ∑ u ∈ S, ((MeromorphicOn.divisor f Set.univ (u : ℂ) : ℤ) : ℝ)
      = ∑ u ∈ S.image Subtype.val,
          ((MeromorphicOn.divisor f Set.univ u : ℤ) : ℝ) := by
    rw [Finset.sum_image hinj]
  -- Jensen at radius `r`
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hlogr : (0 : ℝ) ≤ Real.log r := Real.log_nonneg hr
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hMge : 1 ≤ M (2 * r) := by
    rw [hM]
    have hnn : (0 : ℝ) ≤ A * ((2 * r) * (1 + Real.log (2 * r))) := by
      have : (0 : ℝ) ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
      positivity
    nlinarith [Real.one_le_exp hnn, Real.exp_pos (A * ((2 * r) * (1 + Real.log (2 * r))))]
  have hjensen := finset_sum_divisor_le_of_growth hf hf0
    (fun z => by rw [hM]; exact hbound z) hrpos hMge
    (S.image Subtype.val) himg
  rw [hsum]
  refine hjensen.trans ?_
  -- the algebra: `(log M(2r) − log‖f 0‖)/log 2 ≤ K·r·(1 + log r)` for `r ≥ 1`
  have hlogM : Real.log (M (2 * r))
      = Real.log C + A * ((2 * r) * (1 + Real.log (2 * r))) := by
    rw [hM, Real.log_mul (by linarith) (Real.exp_ne_zero _), Real.log_exp]
  have hlog2r : Real.log (2 * r) = Real.log 2 + Real.log r :=
    Real.log_mul (by norm_num) (ne_of_gt hrpos)
  have hbase : (1 : ℝ) ≤ r * (1 + Real.log r) := by nlinarith
  have hconst : max (Real.log C - Real.log ‖f 0‖) 0
      ≤ max (Real.log C - Real.log ‖f 0‖) 0 * (r * (1 + Real.log r)) := by
    nlinarith [le_max_right (Real.log C - Real.log ‖f 0‖) 0]
  have hmain : Real.log C - Real.log ‖f 0‖ + A * ((2 * r) * (1 + Real.log (2 * r)))
      ≤ (max (Real.log C - Real.log ‖f 0‖) 0 + 2 * A * (1 + Real.log 2))
        * (r * (1 + Real.log r)) := by
    have h1 : Real.log C - Real.log ‖f 0‖ ≤ max (Real.log C - Real.log ‖f 0‖) 0 :=
      le_max_left _ _
    have hlogL : (0 : ℝ) ≤ Real.log 2 := hlog2.le
    have h2 : A * ((2 * r) * (1 + Real.log (2 * r)))
        ≤ 2 * A * (1 + Real.log 2) * (r * (1 + Real.log r)) := by
      rw [hlog2r]
      have hdiff : 2 * A * (1 + Real.log 2) * (r * (1 + Real.log r))
          - A * ((2 * r) * (1 + (Real.log 2 + Real.log r)))
          = 2 * A * r * (Real.log 2 * Real.log r) := by ring
      have hnn : (0 : ℝ) ≤ 2 * A * r * (Real.log 2 * Real.log r) :=
        mul_nonneg (mul_nonneg (by linarith) hrpos.le) (mul_nonneg hlogL hlogr)
      linarith
    linarith [hconst, h1, h2]
  have hKmul : K * r * (1 + Real.log r)
      = ((max (Real.log C - Real.log ‖f 0‖) 0 + 2 * A * (1 + Real.log 2))
          * (r * (1 + Real.log r))) / Real.log 2 := by
    rw [hK]; field_simp
  rw [hlogM, hKmul]
  gcongr
  linarith [hmain]

/-!
### The canonical product is entire

`hasProdLocallyUniformlyOn_weierstrassE1_div`'s docstring says the product is "hence entire",
but that conclusion is never drawn: the file stops at local uniform convergence.
-/

theorem differentiable_weierstrassE1 : Differentiable ℂ weierstrassE1 :=
  fun w => (hasDerivAt_weierstrassE1 w).differentiableAt

variable {ι : Type*} {a : ι → ℂ}

theorem differentiable_weierstrassE1_div (i : ι) :
    Differentiable ℂ fun z : ℂ => weierstrassE1 (z / a i) :=
  differentiable_weierstrassE1.comp (differentiable_id.div_const (a i))

/-- The canonical product is holomorphic on every ball. -/
theorem differentiableOn_tprod_weierstrassE1_div
    (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (R : ℝ) :
    DifferentiableOn ℂ (fun z : ℂ => ∏' n, weierstrassE1 (z / a n))
      (Metric.ball (0 : ℂ) R) := by
  refine (hasProdLocallyUniformlyOn_weierstrassE1_div ha R).differentiableOn
    (.of_forall fun s => ?_) Metric.isOpen_ball
  exact fun z _ => (DifferentiableAt.fun_finsetProd fun i _ =>
    (differentiable_weierstrassE1_div i) z).differentiableWithinAt

/-- **The canonical product is entire.** -/
theorem differentiable_tprod_weierstrassE1_div
    (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) :
    Differentiable ℂ fun z : ℂ => ∏' n, weierstrassE1 (z / a n) := by
  intro z
  refine (differentiableOn_tprod_weierstrassE1_div ha (‖z‖ + 1)).differentiableAt ?_
  refine Metric.isOpen_ball.mem_nhds ?_
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

/-!
### Multiplicity matching: the fibre count *is* the divisor

`CanonicalDivisor.tprod_eq_pow_mul_tprod_compl` gives the order of the canonical product at
`w` as `Nat.card {n | aₙ = w}`.
-/

/-- The fibre of `zeroSeq f` over a point of modulus `≥ 1` has exactly
`ord_ρ(f)` elements. -/
theorem card_fibre_zeroSeq {f : ℂ → ℂ} {ρ : ℂ} (hρ : 1 ≤ ‖ρ‖) :
    Nat.card {n : zeroIndex f // zeroSeq f n = ρ}
      = ((MeromorphicOn.divisor f Set.univ ρ : ℤ)).toNat := by
  classical
  haveI : Unique {u : {u : ℂ // 1 ≤ ‖u‖} // (u : ℂ) = ρ} :=
    { default := ⟨⟨ρ, hρ⟩, rfl⟩
      uniq := by
        rintro ⟨⟨u, hu⟩, h⟩
        exact Subtype.ext (Subtype.ext h) }
  have e₁ : {n : zeroIndex f // zeroSeq f n = ρ}
      ≃ Σ x : {u : {u : ℂ // 1 ≤ ‖u‖} // (u : ℂ) = ρ},
          Fin ((MeromorphicOn.divisor f Set.univ ((x : {u : ℂ // 1 ≤ ‖u‖}) : ℂ) : ℤ)).toNat :=
    Equiv.subtypeSigmaEquiv
      (fun u : {u : ℂ // 1 ≤ ‖u‖} =>
        Fin ((MeromorphicOn.divisor f Set.univ (u : ℂ) : ℤ)).toNat)
      (fun u : {u : ℂ // 1 ≤ ‖u‖} => (u : ℂ) = ρ)
  rw [Nat.card_congr e₁, Nat.card_sigma, Finset.univ_unique, Finset.sum_singleton,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [(default : {u : {u : ℂ // 1 ≤ ‖u‖} // (u : ℂ) = ρ}).2]

/-! ### The atom: `E₁(z/w)` vanishes simply at `w`

Multiplicity matching rests on each factor contributing exactly `1` to the order.
`E₁(z/w) = (1 − z/w)·e^{z/w}` has derivative `−(z/w²)·e^{z/w}`, which at `z = w`
is `−e/w ≠ 0`. -/

theorem hasDerivAt_weierstrassE1_div (w : ℂ) (z : ℂ) :
    HasDerivAt (fun u : ℂ => weierstrassE1 (u / w))
      (-((z / w) * Complex.exp (z / w)) * (1 / w)) z := by
  have hinner : HasDerivAt (fun u : ℂ => u / w) (1 / w) z := by
    simpa using (hasDerivAt_id z).div_const w
  exact (hasDerivAt_weierstrassE1 (z / w)).comp z hinner

/-- **Each factor is a simple zero.** -/
theorem analyticOrderAt_weierstrassE1_div {w : ℂ} (hw : w ≠ 0) :
    analyticOrderAt (fun u : ℂ => weierstrassE1 (u / w)) w = 1 := by
  have hd := hasDerivAt_weierstrassE1_div w w
  have hanalytic : AnalyticAt ℂ (fun u : ℂ => weierstrassE1 (u / w)) w :=
    (differentiable_weierstrassE1_div (a := fun _ : Unit => w) ()).analyticAt w
  refine hanalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
  · rw [div_self hw, weierstrassE1_eq_zero_iff]
  · rw [hd.deriv, div_self hw]
    have he : Complex.exp 1 ≠ 0 := Complex.exp_ne_zero 1
    have hwinv : (1 : ℂ) / w ≠ 0 := one_div_ne_zero hw
    simp only [one_mul]
    exact mul_ne_zero (neg_ne_zero.mpr he) hwinv

/-! ### The zeros inside the unit disc are finite

`zeroSeq` enumerates only the zeros of modulus `≥ 1`, so `f/P` retains whatever
zeros `f` has inside the unit disc.  There are finitely many: the divisor of an
analytic function has finite support on a compact set, and the divisor on the
closed unit ball agrees with the divisor on `ℂ` at points of that ball. -/

/-- The divisor on a ball agrees with the divisor on `ℂ` at points of the ball. -/
theorem divisor_eq_divisor_of_mem {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    {U : Set ℂ} {u : ℂ} (hu : u ∈ U) :
    MeromorphicOn.divisor f Set.univ u = MeromorphicOn.divisor f U u := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn (Set.mem_univ u),
    MeromorphicOn.divisor_apply (hf.mono (Set.subset_univ _)).meromorphicOn hu]

theorem divisor_eq_divisor_ball {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    {r : ℝ} {u : ℂ} (hu : u ∈ Metric.closedBall (0:ℂ) r) :
    MeromorphicOn.divisor f Set.univ u
      = MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r) u :=
  divisor_eq_divisor_of_mem hf hu

/-- **Finitely many zeros in any closed ball.** -/
theorem finite_setOf_divisor_ne_zero {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (r : ℝ) :
    {u : ℂ | ‖u‖ ≤ r ∧ (MeromorphicOn.divisor f Set.univ u : ℤ) ≠ 0}.Finite := by
  have hfin : (Function.support
      (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r) : ℂ → ℤ)).Finite :=
    (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r)).finiteSupport
      (isCompact_closedBall _ _)
  refine hfin.subset ?_
  rintro u ⟨hur, hne⟩
  have hu : u ∈ Metric.closedBall (0:ℂ) r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hur
  simpa [Function.mem_support, ← divisor_eq_divisor_ball hf hu] using hne

/-! ### The polynomial factor over the small zeros

Hadamard's statement is `f = Q·e^g·P` with `Q` a finite product over the zeros
the canonical product omits.  `Q` is built abstractly from a `Finset` and a
multiplicity function, so it is independent of how the zeros were found. -/

/-- `Q(z) = ∏_{u ∈ S} (z − u)^{m u}`. -/
noncomputable def finiteFactor (S : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) : ℂ :=
  ∏ u ∈ S, (z - u) ^ m u

theorem differentiable_finiteFactor (S : Finset ℂ) (m : ℂ → ℕ) :
    Differentiable ℂ (finiteFactor S m) := by
  intro z
  refine DifferentiableAt.fun_finsetProd fun u _ => ?_
  exact (differentiableAt_id.sub_const u).pow _

/-- `Q` vanishes only on `S`. -/
theorem finiteFactor_ne_zero {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : z ∉ S) :
    finiteFactor S m z ≠ 0 := by
  rw [finiteFactor, Finset.prod_ne_zero_iff]
  intro u hu
  refine pow_ne_zero _ ?_
  intro h
  exact hz (by rwa [sub_eq_zero.mp h])

/-- Splitting off one factor: `Q(z) = (z − ρ)^{m ρ} · Q'(z)` with `Q'` the product
over `S \ {ρ}`, which does not vanish at `ρ`. -/
theorem finiteFactor_eq_pow_mul {S : Finset ℂ} {m : ℂ → ℕ} {ρ : ℂ} (hρ : ρ ∈ S)
    (z : ℂ) :
    finiteFactor S m z = (z - ρ) ^ m ρ * finiteFactor (S.erase ρ) m z := by
  rw [finiteFactor, finiteFactor, ← Finset.prod_erase_mul _ _ hρ]
  ring

theorem finiteFactor_erase_ne_zero {S : Finset ℂ} {m : ℂ → ℕ} {ρ : ℂ} :
    finiteFactor (S.erase ρ) m ρ ≠ 0 :=
  finiteFactor_ne_zero (Finset.notMem_erase ρ S)

/-- The order of `(z − ρ)^k` at `ρ` is `k`.  `z − ρ` vanishes simply there
(derivative `1`), and `analyticOrderAt_pow` multiplies. -/
theorem analyticOrderAt_sub_pow (ρ : ℂ) (k : ℕ) :
    analyticOrderAt (fun z : ℂ => (z - ρ) ^ k) ρ = k := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => z - ρ) ρ :=
    (differentiable_id.sub_const ρ).analyticAt ρ
  have hone : analyticOrderAt (fun z : ℂ => z - ρ) ρ = 1 := by
    refine hlin.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) ?_
    have hd : HasDerivAt (fun z : ℂ => z - ρ) 1 ρ := by
      simpa using (hasDerivAt_id ρ).sub_const ρ
    rw [hd.deriv]
    exact one_ne_zero
  have h := analyticOrderAt_pow (f := fun z : ℂ => z - ρ) (z₀ := ρ) hlin (n := k)
  rw [hone, show (k : ℕ) • (1 : ℕ∞) = (k : ℕ∞) by simp] at h
  exact h

/-- **The polynomial factor has the prescribed multiplicities.** -/
theorem analyticOrderAt_finiteFactor {S : Finset ℂ} {m : ℂ → ℕ} {ρ : ℂ}
    (hρ : ρ ∈ S) :
    analyticOrderAt (finiteFactor S m) ρ = m ρ := by
  have hsplit : finiteFactor S m
      = (fun z : ℂ => (z - ρ) ^ m ρ) * finiteFactor (S.erase ρ) m := by
    funext z
    exact finiteFactor_eq_pow_mul hρ z
  have h1 : AnalyticAt ℂ (fun z : ℂ => (z - ρ) ^ m ρ) ρ :=
    ((differentiable_id.sub_const ρ).pow _).analyticAt ρ
  have h2 : AnalyticAt ℂ (finiteFactor (S.erase ρ) m) ρ :=
    (differentiable_finiteFactor _ _).analyticAt ρ
  rw [hsplit, analyticOrderAt_mul h1 h2, analyticOrderAt_sub_pow]
  have hz : analyticOrderAt (finiteFactor (S.erase ρ) m) ρ = 0 := by
    rw [analyticOrderAt_eq_zero]
    exact Or.inr finiteFactor_erase_ne_zero
  rw [hz, add_zero]

/-!
### The canonical product's order *is* the divisor

Assembling: `tprod_eq_pow_mul_tprod_compl` splits the product at `ρ` into `E₁(z/ρ)^m` times a
factor not vanishing there; `analyticOrderAt_weierstrassE1_div` gives each `E₁` a simple zero,
so the head contributes exactly `m`; and `card_fibre_zeroSeq` identifies `m` with `ord_ρ(f)`.
-/

theorem analyticOrderAt_tprod_zeroSeq {f : ℂ → ℂ}
    (hsum : Summable fun n : zeroIndex f => ‖zeroSeq f n‖⁻¹ ^ 2)
    {ρ : ℂ} (hρ : 1 ≤ ‖ρ‖) :
    analyticOrderAt
        (fun z : ℂ => ∏' n : zeroIndex f, weierstrassE1 (z / zeroSeq f n)) ρ
      = ((MeromorphicOn.divisor f Set.univ ρ : ℤ)).toNat := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hρ
    linarith
  set m : ℕ := Nat.card {n : zeroIndex f | zeroSeq f n = ρ} with hm
  -- split the product
  have hsplit : (fun z : ℂ => ∏' n : zeroIndex f, weierstrassE1 (z / zeroSeq f n))
      = (fun z : ℂ => weierstrassE1 (z / ρ) ^ m)
        * fun z : ℂ =>
            ∏' n : ↥({n : zeroIndex f | zeroSeq f n = ρ}ᶜ),
              weierstrassE1 (z / zeroSeq f (n : zeroIndex f)) := by
    funext z
    exact tprod_eq_pow_mul_tprod_compl hsum hρ0 z
  have h1 : AnalyticAt ℂ (fun z : ℂ => weierstrassE1 (z / ρ) ^ m) ρ :=
    (((differentiable_weierstrassE1_div (a := fun _ : Unit => ρ) ())).pow _).analyticAt ρ
  have h2 : AnalyticAt ℂ
      (fun z : ℂ => ∏' n : ↥({n : zeroIndex f | zeroSeq f n = ρ}ᶜ),
        weierstrassE1 (z / zeroSeq f (n : zeroIndex f))) ρ :=
    (differentiable_tprod_weierstrassE1_div
      (hsum.subtype (fun n => n ∈ {n : zeroIndex f | zeroSeq f n = ρ}ᶜ))).analyticAt ρ
  rw [hsplit, analyticOrderAt_mul h1 h2]
  -- the tail contributes nothing
  have htail : analyticOrderAt
      (fun z : ℂ => ∏' n : ↥({n : zeroIndex f | zeroSeq f n = ρ}ᶜ),
        weierstrassE1 (z / zeroSeq f (n : zeroIndex f))) ρ = 0 := by
    rw [analyticOrderAt_eq_zero]
    exact Or.inr (tprod_compl_ne_zero_at hsum ρ)
  -- the head contributes `m`
  have hhead : analyticOrderAt (fun z : ℂ => weierstrassE1 (z / ρ) ^ m) ρ = m := by
    have hbase : AnalyticAt ℂ (fun z : ℂ => weierstrassE1 (z / ρ)) ρ :=
      (differentiable_weierstrassE1_div (a := fun _ : Unit => ρ) ()).analyticAt ρ
    have h := analyticOrderAt_pow (f := fun z : ℂ => weierstrassE1 (z / ρ))
      (z₀ := ρ) hbase (n := m)
    rw [analyticOrderAt_weierstrassE1_div hρ0,
      show (m : ℕ) • (1 : ℕ∞) = (m : ℕ∞) by simp] at h
    exact h
  rw [hhead, htail, add_zero, hm]
  exact_mod_cast card_fibre_zeroSeq (f := f) hρ

/-- **The canonical product is zero-free inside the unit disc.** Every `aₙ` has modulus `≥ 1`, so
no factor can vanish at a point of modulus `< 1`. -/
theorem analyticOrderAt_tprod_zeroSeq_of_lt_one {f : ℂ → ℂ}
    (hsum : Summable fun n : zeroIndex f => ‖zeroSeq f n‖⁻¹ ^ 2)
    {ρ : ℂ} (hρ : ‖ρ‖ < 1) :
    analyticOrderAt
        (fun z : ℂ => ∏' n : zeroIndex f, weierstrassE1 (z / zeroSeq f n)) ρ = 0 := by
  rw [analyticOrderAt_eq_zero]
  refine Or.inr ?_
  refine tprod_weierstrassE1_div_ne_zero hsum (fun n hEq => ?_)
  have hn : 1 ≤ ‖zeroSeq f n‖ := one_le_norm_zeroSeq n
  rw [← hEq] at hn
  linarith

/-! ### The orders match everywhere

`Q·P` has the same order as `f` at every point: outside the unit disc `P` carries
it and `Q` is inert; inside, `Q` carries it and `P` is inert.  This is the
hypothesis `f/(Q·P)` analytic and zero-free rests on. -/

theorem analyticOrderAt_finiteFactor_mul_tprod {f : ℂ → ℂ}
    (hsum : Summable fun n : zeroIndex f => ‖zeroSeq f n‖⁻¹ ^ 2)
    {S : Finset ℂ} {m : ℂ → ℕ}
    (hS : ∀ u ∈ S, ‖u‖ < 1)
    (hm : ∀ u ∈ S, m u = ((MeromorphicOn.divisor f Set.univ u : ℤ)).toNat)
    (hSall : ∀ u : ℂ, ‖u‖ < 1 → (MeromorphicOn.divisor f Set.univ u : ℤ) ≠ 0 → u ∈ S)
    (ρ : ℂ) :
    analyticOrderAt (fun z : ℂ => finiteFactor S m z
        * ∏' n : zeroIndex f, weierstrassE1 (z / zeroSeq f n)) ρ
      = ((MeromorphicOn.divisor f Set.univ ρ : ℤ)).toNat := by
  have hQ : AnalyticAt ℂ (finiteFactor S m) ρ :=
    (differentiable_finiteFactor S m).analyticAt ρ
  have hP : AnalyticAt ℂ
      (fun z : ℂ => ∏' n : zeroIndex f, weierstrassE1 (z / zeroSeq f n)) ρ :=
    (differentiable_tprod_weierstrassE1_div hsum).analyticAt ρ
  have hmul : (fun z : ℂ => finiteFactor S m z
      * ∏' n : zeroIndex f, weierstrassE1 (z / zeroSeq f n))
      = finiteFactor S m
        * fun z : ℂ => ∏' n : zeroIndex f, weierstrassE1 (z / zeroSeq f n) := rfl
  rw [hmul, analyticOrderAt_mul hQ hP]
  rcases lt_or_ge ‖ρ‖ 1 with hlt | hge
  · -- inside the unit disc: `P` is inert
    rw [analyticOrderAt_tprod_zeroSeq_of_lt_one hsum hlt, add_zero]
    by_cases hmem : ρ ∈ S
    · rw [analyticOrderAt_finiteFactor hmem, hm ρ hmem]
    · have hd : (MeromorphicOn.divisor f Set.univ ρ : ℤ) = 0 := by
        by_contra hc
        exact hmem (hSall ρ hlt hc)
      rw [hd]
      simp only [Int.toNat_zero, Nat.cast_zero]
      rw [analyticOrderAt_eq_zero]
      exact Or.inr (finiteFactor_ne_zero hmem)
  · -- outside: `Q` is inert
    have hnot : ρ ∉ S := fun hmem => absurd (hS ρ hmem) (by linarith)
    have hQ0 : analyticOrderAt (finiteFactor S m) ρ = 0 := by
      rw [analyticOrderAt_eq_zero]
      exact Or.inr (finiteFactor_ne_zero hnot)
    rw [hQ0, zero_add, analyticOrderAt_tprod_zeroSeq hsum hge]

/-! ### From matching orders to equal divisors

`AnalyticOnNhd.divisor_apply` reads the divisor off the analytic order, so
pointwise equality of orders gives equality of divisors — the form
`MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd` consumes. -/

theorem divisor_eq_of_analyticOrderAt_eq {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (h : ∀ ρ : ℂ, analyticOrderAt f ρ = analyticOrderAt g ρ) :
    MeromorphicOn.divisor f Set.univ = MeromorphicOn.divisor g Set.univ := by
  ext ρ
  rw [hf.divisor_apply (Set.mem_univ ρ), hg.divisor_apply (Set.mem_univ ρ), h ρ]

/-- **`Q·P` and `f` have the same divisor.**  The Hadamard matching, in the form
the quotient argument needs. -/
theorem divisor_finiteFactor_mul_tprod {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hsum : Summable fun n : zeroIndex f => ‖zeroSeq f n‖⁻¹ ^ 2)
    {S : Finset ℂ} {m : ℂ → ℕ}
    (hS : ∀ u ∈ S, ‖u‖ < 1)
    (hm : ∀ u ∈ S, m u = ((MeromorphicOn.divisor f Set.univ u : ℤ)).toNat)
    (hSall : ∀ u : ℂ, ‖u‖ < 1 → (MeromorphicOn.divisor f Set.univ u : ℤ) ≠ 0 → u ∈ S)
    (hfin : ∀ ρ : ℂ, analyticOrderAt f ρ ≠ ⊤) :
    MeromorphicOn.divisor (fun z : ℂ => finiteFactor S m z
        * ∏' n : zeroIndex f, weierstrassE1 (z / zeroSeq f n)) Set.univ
      = MeromorphicOn.divisor f Set.univ := by
  have hQP : AnalyticOnNhd ℂ (fun z : ℂ => finiteFactor S m z
      * ∏' n : zeroIndex f, weierstrassE1 (z / zeroSeq f n)) Set.univ := by
    intro z _
    exact ((differentiable_finiteFactor S m).mul
      (differentiable_tprod_weierstrassE1_div hsum)).analyticAt z
  refine divisor_eq_of_analyticOrderAt_eq hQP hf (fun ρ => ?_)
  rw [analyticOrderAt_finiteFactor_mul_tprod hsum hS hm hSall ρ,
    hf.divisor_apply (Set.mem_univ ρ)]
  -- `((ord).map ↑).untop₀.toNat = ord` when the order is finite
  cases hcase : analyticOrderAt f ρ with
  | top => exact absurd hcase (hfin ρ)
  | coe k => simp

/-! ### Order-finiteness through the normalisation

The quotient step needs `ord_z g ≠ ⊤` carried *separately* from `divisor g = 0`,
because `untop₀ ⊤ = 0`: a divisor reads `0` both when the order is `0` and when it
is `⊤`.  Normalising does not change the order off `z`, so the order of
`toMeromorphicNFOn (φ⁻¹ • f)` is `−ord φ + ord f`, finite when both are. -/

theorem meromorphicOrderAt_toMeromorphicNFOn_inv_smul {f φ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : AnalyticOnNhd ℂ φ Set.univ) (z : ℂ) :
    meromorphicOrderAt (toMeromorphicNFOn (φ⁻¹ • f) Set.univ) z
      = -meromorphicOrderAt φ z + meromorphicOrderAt f z := by
  have hfm : MeromorphicOn f Set.univ := hf.meromorphicOn
  have hφm : MeromorphicOn φ Set.univ := hφ.meromorphicOn
  have hcongr := (hφm.inv.smul hfm).toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  rw [meromorphicOrderAt_congr hcongr,
    meromorphicOrderAt_smul (hφm z (Set.mem_univ z)).inv (hfm z (Set.mem_univ z)),
    meromorphicOrderAt_inv]

/-- **The normalised quotient has finite order.**  This is what `divisor g = 0`
cannot supply on its own. -/
theorem meromorphicOrderAt_toMeromorphicNFOn_inv_smul_ne_top {f φ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : AnalyticOnNhd ℂ φ Set.univ)
    (hfinf : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤)
    (hfinφ : ∀ z : ℂ, meromorphicOrderAt φ z ≠ ⊤) (z : ℂ) :
    meromorphicOrderAt (toMeromorphicNFOn (φ⁻¹ • f) Set.univ) z ≠ ⊤ := by
  rw [meromorphicOrderAt_toMeromorphicNFOn_inv_smul hf hφ z]
  lift meromorphicOrderAt f z to ℤ using hfinf z with a ha
  lift meromorphicOrderAt φ z to ℤ using hfinφ z with b hb
  simp [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]

/-! ### The quotient is analytic and zero-free

With equal divisors and finite orders, the normalised quotient `g = φ⁻¹ · f` has
zero divisor *and* finite order at every point, so its order is genuinely `0`
everywhere — hence `g` is analytic and never vanishes.  This is the factor
Hadamard writes as `e^h`. -/

theorem analyticOnNhd_and_ne_zero_of_divisor_eq {f φ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : AnalyticOnNhd ℂ φ Set.univ)
    (hfinf : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤)
    (hfinφ : ∀ z : ℂ, meromorphicOrderAt φ z ≠ ⊤)
    (hdiv : MeromorphicOn.divisor φ Set.univ = MeromorphicOn.divisor f Set.univ) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn (φ⁻¹ • f) Set.univ) Set.univ ∧
      ∀ z : ℂ, toMeromorphicNFOn (φ⁻¹ • f) Set.univ z ≠ 0 := by
  have hfm : MeromorphicOn f Set.univ := hf.meromorphicOn
  have hφm : MeromorphicOn φ Set.univ := hφ.meromorphicOn
  have hinvm : MeromorphicOn φ⁻¹ Set.univ := hφm.inv
  have hfinInv : ∀ z ∈ Set.univ, meromorphicOrderAt φ⁻¹ z ≠ ⊤ := by
    intro z _
    simpa [meromorphicOrderAt_inv] using hfinφ z
  set g : ℂ → ℂ := toMeromorphicNFOn (φ⁻¹ • f) Set.univ with hgdef
  have hgNF : MeromorphicNFOn g Set.univ := meromorphicNFOn_toMeromorphicNFOn _ _
  -- the divisor vanishes
  have hdivg : MeromorphicOn.divisor g Set.univ = 0 := by
    rw [hgdef, MeromorphicOn.divisor_of_toMeromorphicNFOn (hinvm.smul hfm),
      MeromorphicOn.divisor_smul hinvm hfm hfinInv (fun z _ => hfinf z),
      MeromorphicOn.divisor_inv, hdiv, neg_add_cancel]
  -- and the order is finite, so the order really is `0`
  have hord : ∀ z : ℂ, meromorphicOrderAt g z = 0 := by
    intro z
    have hne : meromorphicOrderAt g z ≠ ⊤ :=
      meromorphicOrderAt_toMeromorphicNFOn_inv_smul_ne_top hf hφ hfinf hfinφ z
    have hz : MeromorphicOn.divisor g Set.univ z = 0 := by rw [hdivg]; rfl
    rw [MeromorphicOn.divisor_apply hgNF.meromorphicOn (Set.mem_univ z)] at hz
    lift meromorphicOrderAt g z to ℤ using hne with a ha
    simpa using hz
  refine ⟨?_, fun z => ?_⟩
  · rw [← hgNF.divisor_nonneg_iff_analyticOnNhd, hdivg]
  · exact (hgNF (Set.mem_univ z)).meromorphicOrderAt_eq_zero_iff.mp (hord z)

/-! ### Hadamard's exponential factor

`g` is entire and zero-free, so it is `e^h` with `h` entire — the last named
piece.  Combined with `CauchyDegree.exists_affine_of_growth`, `h` is affine once
`g`'s growth is controlled, which is Hadamard's genus-1 statement. -/

theorem exists_exp_of_divisor_eq {f φ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : AnalyticOnNhd ℂ φ Set.univ)
    (hfinf : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤)
    (hfinφ : ∀ z : ℂ, meromorphicOrderAt φ z ≠ ⊤)
    (hdiv : MeromorphicOn.divisor φ Set.univ = MeromorphicOn.divisor f Set.univ) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ z : ℂ, toMeromorphicNFOn (φ⁻¹ • f) Set.univ z = Complex.exp (h z) := by
  obtain ⟨hana, hne⟩ := analyticOnNhd_and_ne_zero_of_divisor_eq hf hφ hfinf hfinφ hdiv
  exact exists_differentiable_exp_eq
    (fun z => (hana z (Set.mem_univ z)).differentiableAt) hne

/-! ### From the normalisation back to a pointwise identity

Normalisation changes the value only on a discrete set — at a point where the
function is already analytic it does nothing.  Since `φ⁻¹ · f` is analytic
wherever `φ ≠ 0`, the factorisation is a genuine pointwise identity there. -/

theorem toMeromorphicNFOn_apply_of_analyticAt {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) {z : ℂ} (hz : AnalyticAt ℂ F z) :
    toMeromorphicNFOn F Set.univ z = F z := by
  simp [toMeromorphicNFOn, hF, ← (toMeromorphicNFAt_eq_self.2 hz.meromorphicNFAt).symm]

theorem toMeromorphicNFOn_inv_smul_apply {f φ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : AnalyticOnNhd ℂ φ Set.univ)
    {z : ℂ} (hz : φ z ≠ 0) :
    toMeromorphicNFOn (φ⁻¹ • f) Set.univ z = (φ z)⁻¹ * f z := by
  have hana : AnalyticAt ℂ (φ⁻¹ • f) z :=
    ((hφ z (Set.mem_univ z)).inv hz).smul (hf z (Set.mem_univ z))
  rw [toMeromorphicNFOn_apply_of_analyticAt
    (hφ.meromorphicOn.inv.smul hf.meromorphicOn) hana]
  simp

/-- **Hadamard's factorisation, pointwise off the zeros of `φ`.** -/
theorem eq_mul_exp_of_divisor_eq {f φ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : AnalyticOnNhd ℂ φ Set.univ)
    (hfinf : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤)
    (hfinφ : ∀ z : ℂ, meromorphicOrderAt φ z ≠ ⊤)
    (hdiv : MeromorphicOn.divisor φ Set.univ = MeromorphicOn.divisor f Set.univ) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ z : ℂ, φ z ≠ 0 → f z = φ z * Complex.exp (h z) := by
  obtain ⟨h, hhdiff, hh⟩ := exists_exp_of_divisor_eq hf hφ hfinf hfinφ hdiv
  refine ⟨h, hhdiff, fun z hz => ?_⟩
  have hval := hh z
  rw [toMeromorphicNFOn_inv_smul_apply hf hφ hz] at hval
  field_simp at hval
  linear_combination hval

/-!
### Extending the identity across the zeros

The identity above holds only where `φ ≠ 0`, which is unsatisfying: it is exactly at the zeros
that a factorisation theorem should say something.
-/

theorem dense_ne_zero {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ Set.univ)
    (hfinφ : ∀ z : ℂ, meromorphicOrderAt φ z ≠ ⊤) :
    Dense {z : ℂ | φ z ≠ 0} := by
  intro z
  rcases (hφ z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exact absurd (meromorphicOrderAt_eq_top_iff.mpr (hzero.filter_mono nhdsWithin_le_nhds))
      (hfinφ z)
  · refine mem_closure_iff_nhdsWithin_neBot.mpr ?_
    have hle : nhdsWithin z {z}ᶜ ≤ nhdsWithin z {w : ℂ | φ w ≠ 0} :=
      le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr hne)
    exact Filter.NeBot.mono inferInstance hle

/-- **Hadamard's factorisation, everywhere.** For any entire `φ` with the same divisor as `f` and
finite orders, `f z = φ z · e^{h z}` for **all** `z`, with `h` entire. -/
theorem eq_mul_exp_of_divisor_eq' {f φ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : AnalyticOnNhd ℂ φ Set.univ)
    (hfinf : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤)
    (hfinφ : ∀ z : ℂ, meromorphicOrderAt φ z ≠ ⊤)
    (hdiv : MeromorphicOn.divisor φ Set.univ = MeromorphicOn.divisor f Set.univ) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ z : ℂ, f z = φ z * Complex.exp (h z) := by
  obtain ⟨h, hhdiff, hoff⟩ := eq_mul_exp_of_divisor_eq hf hφ hfinf hfinφ hdiv
  refine ⟨h, hhdiff, ?_⟩
  have hcf : Continuous f := by
    have : Differentiable ℂ f := fun z => (hf z (Set.mem_univ z)).differentiableAt
    exact this.continuous
  have hcφ : Continuous φ := by
    have : Differentiable ℂ φ := fun z => (hφ z (Set.mem_univ z)).differentiableAt
    exact this.continuous
  have hcr : Continuous fun z : ℂ => φ z * Complex.exp (h z) :=
    hcφ.mul (Complex.continuous_exp.comp hhdiff.continuous)
  exact congrFun (Continuous.ext_on (dense_ne_zero hφ hfinφ) hcf hcr
    (fun w hw => hoff w hw))

/-!
### `Σ_ρ (z − ρ)⁻²` converges

The explicit formula works with `(log ξ)'' = −Σ_ρ (z − ρ)^{−2} + h''`, so convergence of `Σ_ρ
(z − ρ)^{−2}` is a prerequisite.
-/

/-!
### Minimum modulus: the lower bound for a single factor

Pinning Hadamard's exponential factor to degree `1` needs a *lower* bound on `|Q·P|`, which is
the minimum-modulus theorem.
-/

end Cvs.Zeta
