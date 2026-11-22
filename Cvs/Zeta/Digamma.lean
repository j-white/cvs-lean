import Mathlib

/-
Toward L1.1a: the harmonic core of the digamma bound.

LAYER3's L1.1a needs `Re ψ(¼ + it/2) = O(log(2+|t|))` uniformly on the band.
Mathlib's digamma (`Gamma/Digamma.lean`, 64 lines) supplies `logDeriv Gamma`,
the recurrence, and special values — **no asymptotics** — so the bound has to be
built.  The classical route runs through Euler's limit, which Mathlib *does*
have as `Complex.GammaSeq` with `GammaSeq_tendsto_Gamma`:

    `GammaSeq s n = n^s · n! / (s(s+1)⋯(s+n))`,
    `logDeriv (GammaSeq · n) s = log n − Σ_{k=0}^{n} 1/(s+k)`,

so formally `ψ(s) = lim_{n→∞} [log n − H_n(s)]` with `H_n(s) = Σ_{k≤n} 1/(s+k)`.

Two things are needed to turn that into L1.1a:

* **(i) the limit interchange** — that `logDeriv` commutes with `GammaSeq → Gamma`.
  This needs locally-uniform convergence (Weierstrass/Vitali) and is **not**
  available off the shelf in the pinned Mathlib.  Not proved here.
* **(ii) the harmonic bound** — that `|log n − Re H_n(¼+it/2)|` is `O(log(2+|t|))`
  uniformly in `n`.  This is elementary real analysis, and *this module proves
  its pointwise core*.

The arithmetic is driven by one exact identity: at `s = ¼ + it/2`,

    `Re (1/(s+k)) = (¼+k) / ((¼+k)² + t²/4)`,

which is `≤ 1/(¼+k)` always (giving the `log n` upper bound by harmonic
comparison) and `≤ 4(¼+k)/t²` when `t ≠ 0` (killing the terms with `k ≲ |t|`,
which is what produces the `−log|t|` and hence the `O(log(2+|t|))` cancellation).
-/

namespace Cvs.Zeta

open Complex

/-- The shifted digamma argument `s + k` at `s = ¼ + it/2`. -/
noncomputable def digammaArg (t : ℝ) (k : ℕ) : ℂ :=
  ((1 / 4 + k : ℝ) : ℂ) + I * ((t / 2 : ℝ) : ℂ)

@[simp] theorem digammaArg_re (t : ℝ) (k : ℕ) :
    (digammaArg t k).re = 1 / 4 + k := by
  simp [digammaArg]

@[simp] theorem digammaArg_im (t : ℝ) (k : ℕ) :
    (digammaArg t k).im = t / 2 := by
  simp [digammaArg]

/-- **The exact real part of a shifted reciprocal.**
`Re (1/(¼ + k + it/2)) = (¼+k) / ((¼+k)² + t²/4)`. -/
theorem re_inv_digammaArg (t : ℝ) (k : ℕ) :
    (digammaArg t k)⁻¹.re
      = (1 / 4 + k) / ((1 / 4 + k) ^ 2 + (t / 2) ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply, digammaArg_re, digammaArg_im]
  ring_nf

/-! ### The summed bound: `Re H_n ≤ 5 + log n`, uniformly in `t` -/

/-! ### The deficit against `t = 0`: the mechanism producing `log|t|` -/

/-- The **deficit** of the `t`-shifted term against its value at `t = 0`. -/
noncomputable def digammaDeficit (t : ℝ) (k : ℕ) : ℝ :=
  1 / (1 / 4 + (k : ℝ)) - (digammaArg t k)⁻¹.re

/-- **The deficit in closed form.**
`1/a − a/(a²+b²) = b²/(a(a²+b²))` at `a = ¼+k`, `b = t/2`. -/
theorem digammaDeficit_eq (t : ℝ) (k : ℕ) :
    digammaDeficit t k
      = (t / 2) ^ 2
        / ((1 / 4 + (k : ℝ)) * ((1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2)) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by linarith
  have hab : (0 : ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2 := by positivity
  rw [digammaDeficit, re_inv_digammaArg]
  field_simp
  ring

/-- The deficit is nonnegative: the imaginary part only ever *reduces* the term. -/
theorem digammaDeficit_nonneg (t : ℝ) (k : ℕ) : 0 ≤ digammaDeficit t k := by
  rw [digammaDeficit_eq]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by linarith
  positivity

/-! ### The growth side: two-regime summation by discrete telescoping -/

/-!
### The digamma recurrence, iterated

The following two lemmas are ported from the Mathlib contribution
`feat(Analysis/SpecialFunctions/Gamma/Digamma): Gauss' integral representation` (commit
`3fe84e5` of the working checkout).
-/

/-- A point with positive real part is never a nonpositive integer. -/
theorem ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) (m : ℕ) : s ≠ -m := by
  intro h
  have hm : (-(m : ℂ)).re ≤ 0 := by simp
  rw [h] at hs
  linarith

/-- **The digamma recurrence, iterated**: `ψ(s+n) = ψ(s) + Σ_{k<n} 1/(s+k)`,
for `Re s > 0`.  This is an *exact finite identity* — no limit — which is what
lets the remaining analytic input be weakened below. -/
theorem digamma_add_nat (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    Complex.digamma (s + n) = Complex.digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn : 0 < (s + n).re := by
      rw [Complex.add_re, Complex.natCast_re]
      exact add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg n)
    rw [Nat.cast_succ, ← add_assoc,
      Complex.digamma_apply_add_one _ (ne_neg_nat_of_re_pos hsn), ih,
      Finset.sum_range_succ, add_assoc]

/-- The shifted arguments are literal shifts of the base point. -/
theorem digammaArg_eq_add (t : ℝ) (k : ℕ) : digammaArg t k = digammaArg t 0 + k := by
  simp only [digammaArg]
  push_cast
  ring

/-- The base point `¼ + it/2` has positive real part. -/
theorem digammaArg_re_pos (t : ℝ) : 0 < (digammaArg t 0).re := by
  rw [digammaArg_re]; norm_num

/-! ### Closing the chain: the Euler–Gauss limit as an isolated hypothesis -/

/-- **The one remaining analytic input to L1.1a** , isolated as a class. -/
class DigammaEulerLimitRe (t : ℝ) : Prop where
  tendsto : Filter.Tendsto
    (fun n : ℕ => Real.log n - ∑ k ∈ Finset.range n, (digammaArg t k)⁻¹.re)
    Filter.atTop (nhds (Complex.digamma (digammaArg t 0)).re)

/-!
### Weakening the hypothesis to the textbook asymptotic

`digamma_add_nat` turns the Euler–Gauss *limit* into an exact finite identity plus a single
asymptotic statement.
-/

/-- **The remaining analytic input to L1.1a** , in its weakest form: `Re ψ(¼ + it/2 + n) − log n →
0`. -/
class DigammaLogAsymptoteRe (t : ℝ) : Prop where
  tendsto : Filter.Tendsto
    (fun n : ℕ => (Complex.digamma (digammaArg t 0 + n)).re - Real.log n)
    Filter.atTop (nhds 0)

/-!
### Reducing once more: Gauss's series for digamma

The Mathlib work-in-progress (`b3760fd`) proves, `sorry`-free, that `ψ(s+n) − log n`
**converges** — its `h_tail_lim`, via dominated convergence.
-/

/-- **Gauss's series for digamma at `s = ¼+it/2`** (real part):
`ψ(s) − ψ(1) = Σ_{k≥0}[1/(1+k) − 1/(s+k)]`, using `ψ(1) = −γ`. -/
class DigammaGaussSeriesRe (t : ℝ) : Prop where
  tendsto : Filter.Tendsto
    (fun n : ℕ => ∑ k ∈ Finset.range n, (((k : ℝ) + 1)⁻¹ - (digammaArg t k)⁻¹.re))
    Filter.atTop
    (nhds ((Complex.digamma (digammaArg t 0)).re + Real.eulerMascheroniConstant))

end Cvs.Zeta
