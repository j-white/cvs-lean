import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Weierstrass

/-
The zero structure of the genus-1 canonical product.

Rung 1 (`Cvs.Zeta.Weierstrass`) shows `P z = ∏' n, E₁(z/aₙ)` converges, is
locally uniformly convergent, and is *nonzero off* `{aₙ}`.  Hadamard needs the
converse and, beyond that, the multiplicities: `f / P` is entire and zero-free
precisely because `P` vanishes at each `aₙ` to the order with which it occurs in
the family.

This file supplies the structural half.  At any `w ≠ 0` the product splits as

    `P z = (∏_{n ∈ F} E₁(z/aₙ)) · (∏'_{n ∉ F} E₁(z/aₙ))`,   `F = {n | aₙ = w}`,

where `F` is *finite* (summability of `‖aₙ‖⁻²` forces it) and the tail factor is
**nonzero at `w`** — so all of the vanishing of `P` at `w` is carried by the
explicit finite product, each of whose factors has a simple zero there.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex

variable {ι : Type*} {a : ι → ℂ}

/-- **Only finitely many `aₙ` can equal a given `w ≠ 0`.**
Summability of `‖aₙ‖⁻²` leaves no room for a value to repeat infinitely often. -/
theorem finite_setOf_eq (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) {w : ℂ} (hw : w ≠ 0) :
    {n | a n = w}.Finite := by
  have hpos : (0 : ℝ) < ‖w‖⁻¹ ^ 2 := by
    have : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    positivity
  have hev : ∀ᶠ n in Filter.cofinite, ‖a n‖⁻¹ ^ 2 < ‖w‖⁻¹ ^ 2 :=
    ha.tendsto_cofinite_zero.eventually (gt_mem_nhds hpos)
  refine (Filter.eventually_cofinite.mp hev).subset ?_
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  rw [hn]
  exact lt_irrefl _

/-- **The tail of the product, omitting every index with `aₙ = w`, is nonzero
at `w`.**  All the vanishing of `P` at `w` is carried by the head. -/
theorem tprod_compl_ne_zero_at (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (w : ℂ) :
    (∏' n : ↥({n | a n = w}ᶜ), weierstrassE1 (w / a (n : ι))) ≠ 0 :=
  tprod_weierstrassE1_div_ne_zero
    (a := fun n : ↥({n | a n = w}ᶜ) => a (n : ι))
    (ha.subtype (fun n => n ∈ {n | a n = w}ᶜ))
    (fun n hEq => n.2 hEq.symm)

/-- **The canonical product splits at `w`**: the indices with `aₙ = w`, and the
rest.  With `tprod_compl_ne_zero_at`, all vanishing at `w` sits in the head. -/
theorem tprod_split_at (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (w z : ℂ) :
    (∏' n : ↥{n | a n = w}, weierstrassE1 (z / a (n : ι)))
        * ∏' n : ↥({n | a n = w}ᶜ), weierstrassE1 (z / a (n : ι))
      = ∏' n, weierstrassE1 (z / a n) :=
  Multipliable.tprod_mul_tprod_compl
    (f := fun n => weierstrassE1 (z / a n))
    (multipliable_weierstrassE1_div (ha.subtype (fun n => n ∈ {n | a n = w})) z)
    (multipliable_weierstrassE1_div (ha.subtype (fun n => n ∈ {n | a n = w}ᶜ)) z)

/-- **The head is an explicit power.** Every index in the head has `aₙ = w`, so the head is
`E₁(z/w)` raised to the multiplicity of `w` in the family. -/
theorem tprod_head_eq_pow (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) {w : ℂ} (hw : w ≠ 0)
    (z : ℂ) :
    (∏' n : ↥{n | a n = w}, weierstrassE1 (z / a (n : ι)))
      = weierstrassE1 (z / w) ^ Nat.card ↥{n | a n = w} := by
  have hfin : Finite ↥{n | a n = w} := (finite_setOf_eq ha hw).to_subtype
  have hfty : Fintype ↥{n | a n = w} := Fintype.ofFinite _
  have hconst : ∀ n : ↥{n | a n = w}, weierstrassE1 (z / a (n : ι))
      = weierstrassE1 (z / w) := fun n => by rw [n.2]
  rw [tprod_congr hconst,
    tprod_eq_prod (s := (Finset.univ : Finset ↥{n | a n = w}))
      (fun b hb => absurd (Finset.mem_univ b) hb),
    Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **The order of vanishing of the canonical product at `w ≠ 0`.** `P z = E₁(z/w)^m · Q z`, `Q w
≠ 0`, `m` = multiplicity of `w` in `(aₙ)`. -/
theorem tprod_eq_pow_mul_tprod_compl (ha : Summable fun n => ‖a n‖⁻¹ ^ 2)
    {w : ℂ} (hw : w ≠ 0) (z : ℂ) :
    ∏' n, weierstrassE1 (z / a n)
      = weierstrassE1 (z / w) ^ Nat.card ↥{n | a n = w}
        * ∏' n : ↥({n | a n = w}ᶜ), weierstrassE1 (z / a (n : ι)) := by
  rw [← tprod_split_at ha w z, tprod_head_eq_pow ha hw z]

end Cvs.Zeta
