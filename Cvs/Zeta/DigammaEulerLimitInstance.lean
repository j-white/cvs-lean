import Mathlib
import Cvs.WeilForm.Archimedean.HighResonancesClosed
import Cvs.Zeta.Digamma
import Cvs.Zeta.Weierstrass

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The filter bank sums to the weight, unconditionally
-/

namespace Cvs.Transform

open Filter Topology

/-- On the real axis the shifted argument is real, so its reciprocal's real part
is the plain reciprocal. -/
theorem re_inv_digammaArg_zero (k : ℕ) :
    (Cvs.Zeta.digammaArg 0 k)⁻¹.re = 1 / (1 / 4 + (k : ℝ)) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by linarith
  rw [Cvs.Zeta.re_inv_digammaArg]
  field_simp
  ring

/-- **The Euler–Gauss limit for `Re ψ`, unconditionally.**  Supplies the class
`Cvs.Zeta.Digamma` left open. -/
instance instDigammaEulerLimitRe (t : ℝ) : Cvs.Zeta.DigammaEulerLimitRe t := by
  refine ⟨?_⟩
  have hx : 0 < (Cvs.Zeta.digammaArg t 0).re := Cvs.Zeta.digammaArg_re_pos t
  have h := (Complex.continuous_re.tendsto _).comp (Cvs.Zeta.tendsto_euler_digamma hx)
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Complex.sub_re, Complex.ofReal_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Cvs.Zeta.digammaArg_eq_add t k]

/-- The deficit sums are the difference of two Euler–Gauss limits: the `log n`
cancels and the terms are the deficits. -/
theorem tendsto_sum_digammaDeficit (t : ℝ) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, Cvs.Zeta.digammaDeficit t k) atTop
      (𝓝 ((Complex.digamma (Cvs.Zeta.digammaArg t 0)).re
            - (Complex.digamma (Cvs.Zeta.digammaArg 0 0)).re)) := by
  have ht := (instDigammaEulerLimitRe t).tendsto
  have h0 := (instDigammaEulerLimitRe 0).tendsto
  refine (ht.sub h0).congr fun n => ?_
  have hd : ∀ k : ℕ, Cvs.Zeta.digammaDeficit t k
      = (Cvs.Zeta.digammaArg 0 k)⁻¹.re - (Cvs.Zeta.digammaArg t k)⁻¹.re := fun k => by
    rw [Cvs.Zeta.digammaDeficit, re_inv_digammaArg_zero]
  simp only [hd, Finset.sum_sub_distrib]
  ring

/-- Summability, from `HighResonancesClosed`'s majorant. -/
theorem summable_digammaDeficit (t : ℝ) : Summable (Cvs.Zeta.digammaDeficit t) := by
  have h := Cvs.Transform.summable_bankTerm t
  exact h.congr fun k => Cvs.Transform.bankTerm_eq_deficit k t

/-- **The bank sums to twice the weight.** -/
theorem tsum_digammaDeficit (t : ℝ) :
    ∑' k : ℕ, Cvs.Zeta.digammaDeficit t k
      = (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re
          - (Complex.digamma (Cvs.Zeta.digammaArg 0 0)).re :=
  tendsto_nhds_unique (summable_digammaDeficit t).hasSum.tendsto_sum_nat
    (tendsto_sum_digammaDeficit t)

/-- **`HighResonancesClosed`'s bound is a bound on the weight itself**, not merely on a
resembling series: `Re ψ(¼+iu/2) − ψ(¼) ≤ 16.166·u²`. -/
theorem re_digamma_sub_le (u : ℝ) :
    (Complex.digamma (Cvs.Zeta.digammaArg u 0)).re
        - (Complex.digamma (Cvs.Zeta.digammaArg 0 0)).re
      ≤ u ^ 2 * ∑' k : ℕ, 1 / (4 * (1 / 4 + (k : ℝ)) ^ 3) := by
  rw [← tsum_digammaDeficit u]
  refine le_trans (le_of_eq ?_) (Cvs.Transform.tsum_bankTerm_le u)
  exact tsum_congr fun k => (Cvs.Transform.bankTerm_eq_deficit k u).symm

end Cvs.Transform
