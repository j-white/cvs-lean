import Mathlib.Analysis.Calculus.LogDeriv
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
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Hadamard

/-
The argument principle.

Mathlib gap #6 of `MATHLIB.md`, which unblocks ladder rung 5 — the contour shift
in the derivation of the explicit formula.  Mathlib has Cauchy's theorem for
circles and `Meromorphic` with orders, but neither the residue theorem nor the
argument principle.

The statement, for a zero of order `m` at the centre:

    `(2πi)⁻¹ ∮_{C(a,R)} f'/f = m`.

The proof is the same decomposition `Cvs.Zeta.CauchyD` uses for `H(z)/z`: write
`f z = (z − a)^m · g z` with `g` zero-free, so that

    `f'/f = m/(z − a) + g'/g`

pointwise off `a`.  The first term integrates to `2πi·m`
(`circleIntegral.integral_sub_center_inv`), and the second vanishes because
`g'/g` is holomorphic on the whole disc — no pole to catch
(`DiffContOnCl.circleIntegral_eq_zero`).

The factorisation is taken as a hypothesis rather than derived: Mathlib's
`AnalyticAt.analyticOrderAt_eq_natCast` supplies it only *locally* (`∀ᶠ z in 𝓝 a`),
while the contour needs it on the whole disc.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex Metric

/-! ### Several zeros

The form ladder rung 5 actually needs: a *count* of zeros inside the contour,
not one at the centre.  The factor is `Cvs.Zeta.finiteFactor` — the same finite
product `Cvs.Zeta.Hadamard` splits off the small zeros with — so this composes
directly with `exists_logDeriv_riemannXi`. -/

/-- `logDeriv ((· − u)^k) = k/(z − u)`. -/
theorem logDeriv_sub_pow (u : ℂ) (k : ℕ) {z : ℂ} (hz : z ≠ u) :
    logDeriv (fun w : ℂ => (w - u) ^ k) z = (k : ℂ) / (z - u) := by
  have hsub : z - u ≠ 0 := sub_ne_zero.mpr hz
  have hd : HasDerivAt (fun w : ℂ => (w - u) ^ k) ((k : ℂ) * (z - u) ^ (k - 1)) z := by
    simpa using ((hasDerivAt_id z).sub_const u).fun_pow k
  rw [logDeriv_apply, hd.deriv]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have hsplit : (z - u) ^ k = (z - u) * (z - u) ^ (k - 1) := by
      conv_lhs => rw [show k = 1 + (k - 1) by omega]
      rw [pow_add, pow_one]
    rw [hsplit]
    field_simp

/-- **The log-derivative of `finiteFactor` is its sum of simple poles.** -/
theorem logDeriv_finiteFactor {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : z ∉ S) :
    logDeriv (finiteFactor S m) z = ∑ u ∈ S, (m u : ℂ) / (z - u) := by
  have hne : ∀ u ∈ S, z ≠ u := fun u hu hcon => hz (hcon ▸ hu)
  have hdiff : ∀ u ∈ S, DifferentiableAt ℂ (fun y : ℂ => (y - u) ^ m u) z :=
    fun u _ => (differentiableAt_id.sub_const u).fun_pow (m u)
  have hprod := logDeriv_fun_prod (s := S) (f := fun u => fun y : ℂ => (y - u) ^ m u)
    (x := z) (fun u hu => pow_ne_zero _ (sub_ne_zero.mpr (hne u hu))) hdiff
  have hfF : finiteFactor S m = fun w : ℂ => ∏ u ∈ S, (fun y : ℂ => (y - u) ^ m u) w := rfl
  rw [hfF, hprod]
  exact Finset.sum_congr rfl (fun u hu => logDeriv_sub_pow u (m u) (hne u hu))

/-! ### Indexed form

`Cvs.Zeta.exists_linear_mul_of_finset` hands over `∏_{n∈F} (z − bₙ)` — a product
over an *index* set, where a zero of multiplicity `k` appears as `k` separate
indices.  That is the form the canonical product naturally produces, and it makes
the count `F.card` with no multiplicity function to carry. -/

/-- `logDeriv (∏_{n∈F} (· − bₙ)) = Σ_{n∈F} 1/(z − bₙ)`. -/
theorem logDeriv_prod_linear {ι : Type*} (F : Finset ι) (b : ι → ℂ) {z : ℂ}
    (hz : ∀ n ∈ F, z ≠ b n) :
    logDeriv (fun w : ℂ => ∏ n ∈ F, (w - b n)) z = ∑ n ∈ F, 1 / (z - b n) := by
  have hprod := logDeriv_fun_prod (s := F) (f := fun n => fun w : ℂ => w - b n) (x := z)
    (fun n hn => sub_ne_zero.mpr (hz n hn))
    (fun n _ => differentiableAt_id.sub_const (b n))
  rw [hprod]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [logDeriv_apply]
  simp

/-!
### Mixed form

Hadamard's factorisation carries **two** finite products — `finiteFactor` over the zeros of
modulus `< 1`, and the in-disc factors split off the canonical product — and for a general
contour both can lie inside.
-/

end Cvs.Zeta
