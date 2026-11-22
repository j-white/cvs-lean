import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.SymbolPartialFraction
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaEulerLimitInstance

/-!
# The truncation approaches the symbol from below

    Ω_N(t) = c_N − ∑_{n<N} 2bₙ/(t² + bₙ²)  ↑  Re ψ(¼+it/2) − log π

`Cvs.WeilForm.Archimedean.SymbolPartialFraction`'s remainder is the tail of `Cvs.Zeta`'s deficit series, so the retained channels never
overshoot the symbol and exhaust it in the limit.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Filter Topology

namespace Cvs.WeilForm.Archimedean.TruncationBelowSymbol

open Cvs.WeilForm.Archimedean.OffWindowDefect (bIdx)

/-- The symbol with only the first `N` Lévy poles retained. -/
def truncSymbol (N : ℕ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N
    - ∑ n ∈ Finset.range N, 2 * bIdx n / (t ^ 2 + (bIdx n) ^ 2)

/-- **A retained channel's gap is the digamma deficit.**  The `n`-th term of the constant is the
`n`-th pole's peak, so what the channel leaves on the table is exactly `Cvs.Zeta`'s deficit. -/
theorem gap_eq_deficit (t : ℝ) (k : ℕ) :
    1 / ((k : ℝ) + 1 / 4) - 2 * bIdx k / (t ^ 2 + (bIdx k) ^ 2)
      = Cvs.Zeta.digammaDeficit t k := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha : (0 : ℝ) < (k : ℝ) + 1 / 4 := by linarith
  have hb : (0 : ℝ) < t ^ 2 + (bIdx k) ^ 2 := by
    have : (0:ℝ) < bIdx k := by unfold bIdx; linarith
    positivity
  have hab : (0 : ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2 := by positivity
  rw [Cvs.Zeta.digammaDeficit_eq]
  unfold bIdx
  field_simp
  ring

/-- **The value at zero frequency.**  Each pole's peak is the constant's term. -/
theorem peak_eq (k : ℕ) : 2 * bIdx k / ((0:ℝ) ^ 2 + (bIdx k) ^ 2) = 1 / ((k : ℝ) + 1 / 4) := by
  have : (0:ℝ) < bIdx k := by unfold bIdx; positivity
  unfold bIdx
  field_simp
  ring

/-- **The deficit series' tail, in closed form.** -/
theorem tail_eq (t : ℝ) (N : ℕ) :
    ∑' k : ℕ, Cvs.Zeta.digammaDeficit t (k + N)
      = (∑' k : ℕ, Cvs.Zeta.digammaDeficit t k)
        - ∑ n ∈ Finset.range N, Cvs.Zeta.digammaDeficit t n := by
  have h := (Cvs.Transform.summable_digammaDeficit t).sum_add_tsum_nat_add (f := Cvs.Zeta.digammaDeficit t) N
  linarith [h]

/-- **The remainder of `Cvs.WeilForm.Archimedean.SymbolPartialFraction`'s split is the deficit series' tail.** -/
theorem remainder_eq (t : ℝ) (N : ℕ) :
    (Complex.digamma (Cvs.Zeta.digammaArg t N)).re
        - (Complex.digamma (Cvs.Zeta.digammaArg 0 N)).re
      = ∑' k : ℕ, Cvs.Zeta.digammaDeficit t (k + N) := by
  have hst := Cvs.WeilForm.Archimedean.SymbolPartialFraction.re_digamma_shift t N
  have hs0 := Cvs.WeilForm.Archimedean.SymbolPartialFraction.re_digamma_shift 0 N
  have htot := Cvs.Transform.tsum_digammaDeficit t
  have hfin : ∑ n ∈ Finset.range N, 2 * bIdx n / ((0:ℝ) ^ 2 + (bIdx n) ^ 2)
      = ∑ n ∈ Finset.range N, Cvs.Zeta.digammaDeficit t n
        + ∑ n ∈ Finset.range N, 2 * bIdx n / (t ^ 2 + (bIdx n) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [peak_eq, ← gap_eq_deficit t k]
    ring
  rw [tail_eq]
  rw [hfin] at hs0
  linarith [hst, hs0, htot]

/-- **The remainder is nonnegative.**  A tail of a series of nonnegative terms. -/
theorem remainder_nonneg (t : ℝ) (N : ℕ) :
    0 ≤ (Complex.digamma (Cvs.Zeta.digammaArg t N)).re
        - (Complex.digamma (Cvs.Zeta.digammaArg 0 N)).re := by
  rw [remainder_eq]
  exact tsum_nonneg fun k => Cvs.Zeta.digammaDeficit_nonneg t (k + N)

/-- **The truncation never overshoots.**  At every order and every frequency the retained channels
fall short of the symbol, by exactly the deficit the discarded poles carry. -/
theorem truncSymbol_le (N : ℕ) (t : ℝ) :
    truncSymbol N t ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t := by
  rw [Cvs.WeilForm.Archimedean.SymbolPartialFraction.archSymbol_split t N]
  have := remainder_nonneg t N
  unfold truncSymbol
  linarith

end Cvs.WeilForm.Archimedean.TruncationBelowSymbol
