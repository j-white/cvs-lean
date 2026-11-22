import Mathlib.Analysis.Complex.JensenFormula

/-
Rung 4 of the Guinand–Weil ladder: zero counting for entire functions of order 1.

`Cvs.Zeta.Weierstrass` (rung 1) proves that the genus-1 canonical product
`Π E₁(z/aₙ)` converges, is entire, and vanishes exactly at the `aₙ` — under the
single hypothesis `Summable fun n => ‖aₙ‖⁻¹ ^ 2`.  This file is the other half:
where that hypothesis comes from.

Mathlib turns out to have Jensen's inequality in exactly the counting form
needed, `AnalyticOnNhd.sum_divisor_le` (`Analysis/Complex/JensenFormula.lean`):
for `f` analytic on `closedBall c |R|` with `f c ≠ 0` and `‖f‖ ≤ M` on the
sphere,

    `∑ᶠ u, divisor f (closedBall c |r|) u ≤ log (M / ‖f c‖) / log (R / r)`.

Feeding an order-1 growth bound `‖f z‖ ≤ C·exp(A‖z‖)` at `R = 2r` collapses the
right-hand side to `(log C + 2Ar − log ‖f 0‖) / log 2`, i.e. **`n(r) = O(r)`**.

This is independent of the growth bound for `ξ` itself (rung 2): that supplies
the hypothesis, this consumes it.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex MeromorphicOn Metric Real Set

/-! ### From `n(r) = O(r)` to `Σ ‖ρ‖⁻² < ∞`

The dyadic step.  A point with `‖x i‖ ∈ [2^k, 2^{k+1})` contributes at most
`(2⁻¹)^{2k}`, and the counting hypothesis caps the total weight at that level by
`K·2^{k+1}`, so the level-`k` block contributes `≤ 2K·(2⁻¹)^k`.  Summing the
geometric series bounds every partial sum by `4K`. -/

/-!
### The seam: Jensen's bound in `Finset` form

`sum_divisor_le_of_exp_bound` produces a `finsum` over the divisor of `f` on a closed ball;
`summable_weight_mul_inv_norm_sq` consumes a `Finset` sum.
-/

/-! ### End to end

Jensen ⟹ counting ⟹ square-summability, for the genuine divisor of an entire
function of order 1. -/

/-!
### Finite order, not merely exponential type

`summable_weight_mul_inv_norm_sq` assumes `n(r) ≤ K·r`, which comes from a bound `‖f z‖ ≤
C·exp(A‖z‖)` — *exponential type*.
-/

/-- **Dyadic counting implies square-summability, general counting bound.** `N` bounds the total
weight in a disc of radius `r`; the only requirement is that the dyadic blocks
`N(2^{k+1})·4^{-k}` are summable. -/
theorem summable_weight_mul_inv_norm_sq_of_counting {ι : Type*} {x : ι → ℂ}
    {w : ι → ℝ} {N : ℝ → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 1 ≤ ‖x i‖)
    (hcount : ∀ r : ℝ, 1 ≤ r → ∀ S : Finset ι, (∀ i ∈ S, ‖x i‖ ≤ r) →
      ∑ i ∈ S, w i ≤ N r)
    (hN : Summable fun k : ℕ => N ((2 : ℝ) ^ (k + 1)) * (((2 : ℝ)⁻¹) ^ k) ^ 2) :
    Summable fun i => w i * ‖x i‖⁻¹ ^ 2 := by
  classical
  have hone : ∀ k : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := fun k => one_le_pow₀ (by norm_num)
  have hNnn : ∀ k : ℕ, 0 ≤ N ((2 : ℝ) ^ (k + 1)) := by
    intro k
    simpa using hcount ((2 : ℝ) ^ (k + 1)) (hone k) ∅ (by simp)
  refine summable_of_sum_le (fun i => mul_nonneg (hw i) (by positivity))
    (c := ∑' k : ℕ, N ((2 : ℝ) ^ (k + 1)) * (((2 : ℝ)⁻¹) ^ k) ^ 2) ?_
  intro S
  set n : ι → ℕ := fun i => Nat.log 2 ⌊‖x i‖⌋₊ with hndef
  have hfl : ∀ i, ⌊‖x i‖⌋₊ ≠ 0 := by
    intro i
    have : 1 ≤ ⌊‖x i‖⌋₊ := Nat.le_floor (by exact_mod_cast hx i)
    omega
  have hlow : ∀ i, (2 : ℝ) ^ n i ≤ ‖x i‖ := by
    intro i
    calc (2 : ℝ) ^ n i = ((2 ^ n i : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊‖x i‖⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (hfl i)
      _ ≤ ‖x i‖ := Nat.floor_le (norm_nonneg _)
  have hhigh : ∀ i, ‖x i‖ ≤ (2 : ℝ) ^ (n i + 1) := by
    intro i
    have h1 : ⌊‖x i‖⌋₊ + 1 ≤ 2 ^ (n i + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    calc ‖x i‖ ≤ (⌊‖x i‖⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
      _ = ((⌊‖x i‖⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ (n i + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (2 : ℝ) ^ (n i + 1) := by push_cast; ring
  have hterm : ∀ i, w i * ‖x i‖⁻¹ ^ 2 ≤ w i * (((2 : ℝ)⁻¹) ^ n i) ^ 2 := by
    intro i
    have hxi : (0 : ℝ) < ‖x i‖ := lt_of_lt_of_le zero_lt_one (hx i)
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n i := by positivity
    have hinv : ‖x i‖⁻¹ ≤ ((2 : ℝ)⁻¹) ^ n i := by
      rw [inv_pow]
      exact (inv_le_inv₀ hxi h2).mpr (hlow i)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hinv 2) (hw i)
  have hmaps : ∀ i ∈ S, n i ∈ S.image n := fun i hi => Finset.mem_image_of_mem n hi
  have hblock : ∀ k ∈ S.image n,
      ∑ i ∈ S.filter (fun i => n i = k), w i * (((2 : ℝ)⁻¹) ^ n i) ^ 2
        ≤ N ((2 : ℝ) ^ (k + 1)) * (((2 : ℝ)⁻¹) ^ k) ^ 2 := by
    intro k _
    have hin : ∀ i ∈ S.filter (fun i => n i = k), ‖x i‖ ≤ (2 : ℝ) ^ (k + 1) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      exact hi.2 ▸ hhigh i
    have hcnt := hcount ((2 : ℝ) ^ (k + 1)) (hone k) _ hin
    have hrw : ∑ i ∈ S.filter (fun i => n i = k), w i * (((2 : ℝ)⁻¹) ^ n i) ^ 2
        = (∑ i ∈ S.filter (fun i => n i = k), w i) * (((2 : ℝ)⁻¹) ^ k) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [hi.2]
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hcnt (by positivity)
  calc ∑ i ∈ S, w i * ‖x i‖⁻¹ ^ 2
      ≤ ∑ i ∈ S, w i * (((2 : ℝ)⁻¹) ^ n i) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ k ∈ S.image n, ∑ i ∈ S.filter (fun i => n i = k),
          w i * (((2 : ℝ)⁻¹) ^ n i) ^ 2 := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ S.image n, N ((2 : ℝ) ^ (k + 1)) * (((2 : ℝ)⁻¹) ^ k) ^ 2 :=
        Finset.sum_le_sum hblock
    _ ≤ ∑' k : ℕ, N ((2 : ℝ) ^ (k + 1)) * (((2 : ℝ)⁻¹) ^ k) ^ 2 :=
        sum_le_hasSum _ (fun k _ => mul_nonneg (hNnn k) (by positivity)) hN.hasSum

/-- **The `r·(1 + log r)` counting bound is admissible.** This is the shape `ξ` actually satisfies
— order `1` of *maximal* type — and it is exactly what the exponential-type hypothesis
excludes. -/
theorem summable_dyadic_rlogr (K : ℝ) :
    Summable fun k : ℕ =>
      (K * (2 : ℝ) ^ (k + 1) * (1 + Real.log ((2 : ℝ) ^ (k + 1))))
        * (((2 : ℝ)⁻¹) ^ k) ^ 2 := by
  have hr : ‖((2 : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  have hgeom : Summable fun k : ℕ => ((2 : ℝ)⁻¹) ^ k :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hlin : Summable fun k : ℕ => (k : ℝ) * ((2 : ℝ)⁻¹) ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have hcomb : Summable fun k : ℕ =>
      (2 * K * (1 + Real.log 2)) * ((2 : ℝ)⁻¹) ^ k
        + (2 * K * Real.log 2) * ((k : ℝ) * ((2 : ℝ)⁻¹) ^ k) :=
    (hgeom.mul_left _).add (hlin.mul_left _)
  refine hcomb.congr fun k => ?_
  have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  rw [Real.log_pow]
  push_cast
  simp only [inv_pow]
  rw [pow_succ]
  field_simp
  ring

end Cvs.Zeta
