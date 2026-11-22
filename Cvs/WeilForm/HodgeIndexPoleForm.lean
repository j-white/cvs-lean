import Mathlib
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Hodge-index form of the problem: the pole is `2V² − 2U²`

With `U φ = ∫ rep φ · sinh(s/2)` and `V φ = ∫ rep φ · cosh(s/2)`, linear on the form domain, the pole term is
`2V² − 2U²` (`poleTerm_rep`): a rank-one positive part and a rank-one negative part.  `nonneg_add_sq_iff`: a form plus
`c·v²` is nonnegative iff it is nonnegative on `ker v` and on one affine slice `v = 1`.  `problem_iff_hodge`: the
problem is `2U² ≤ arch − prime` on the cosh-null hyperplane together with `0 ≤ Q` on the slice through any `f₀`.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.WeilForm.HodgeIndexPoleForm
open Cvs.ZeroCounting

open Cvs.WeilForm.PoleArchPrimeProblem (Mplus Mminus poleTerm archTerm primeTerm Problem Q_eq_split)

/-! ### The abstract Hodge-index lemma -/

section abstract
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **A form plus a rank-one square** is nonnegative iff it is nonnegative on the kernel of the functional and on
one affine slice `v = 1`. -/
theorem nonneg_add_sq_iff (B : LinearMap.BilinForm ℝ V) (v : V →ₗ[ℝ] ℝ) {c : ℝ}
    {f₀ : V} (h₀ : v f₀ = 1) :
    (∀ f, 0 ≤ B f f + c * v f ^ 2) ↔
      (∀ g, v g = 0 → 0 ≤ B g g) ∧ (∀ g, v g = 0 → -c ≤ B (f₀ + g) (f₀ + g)) := by
  constructor
  · intro h
    refine ⟨fun g hg => by simpa [hg] using h g, fun g hg => ?_⟩
    have := h (f₀ + g)
    have hv : v (f₀ + g) = 1 := by rw [map_add, h₀, hg, add_zero]
    rw [hv] at this
    linarith
  · rintro ⟨h1, h2⟩ f
    by_cases ht : v f = 0
    · simpa [ht] using h1 f ht
    · set t : ℝ := v f with htdef
      set g : V := f - t • f₀ with hgdef
      have hg : v g = 0 := by simp [hgdef, map_sub, map_smul, h₀, htdef]
      set k : V := f₀ + t⁻¹ • g with hkdef
      have hk : v k = 1 := by simp [hkdef, map_add, map_smul, h₀, hg]
      have hfk : f = t • k := by
        rw [hkdef, smul_add, smul_smul, mul_inv_cancel₀ ht, one_smul, hgdef]; abel
      have hB : B f f = t * t * B k k := by
        rw [hfk]; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
      have hv : v f = t := rfl
      have h2k := h2 (t⁻¹ • g) (by rw [map_smul, hg, smul_zero])
      rw [hB]
      calc (0:ℝ) ≤ t * t * (B k k + c) := mul_nonneg (mul_self_nonneg t) (by linarith)
        _ = t * t * B k k + c * t ^ 2 := by ring
end abstract

/-! ### The two moment functionals on the form domain -/

variable {L : ℝ}

theorem integrable_rep_mul (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {w : ℝ → ℝ} (hw : Continuous w)
    {C : ℝ} (hC : ∀ s ∈ Ioc (0:ℝ) L, |w s| ≤ C) :
    Integrable (fun s => Cvs.WeilForm.WindowRepresentative.rep φ s * w s) := by
  have hrep := Cvs.WeilForm.LevyDomainSpectral.integrable_rep hL φ
  refine (hrep.norm.const_mul C).mono'
    (hrep.aestronglyMeasurable.mul hw.aestronglyMeasurable) (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  by_cases hs : s ∈ Ioc (0:ℝ) L
  · have := hC s hs
    have h0 := abs_nonneg (Cvs.WeilForm.WindowRepresentative.rep φ s)
    calc |Cvs.WeilForm.WindowRepresentative.rep φ s| * |w s| ≤ |Cvs.WeilForm.WindowRepresentative.rep φ s| * C := mul_le_mul_of_nonneg_left this h0
      _ = C * |Cvs.WeilForm.WindowRepresentative.rep φ s| := by ring
  · simp [Cvs.WeilForm.WindowRepresentative.rep_supp φ s hs]

/-- A continuous weight gives a linear functional on the form domain through the representative. -/
def momentFunctional (hL : 0 ≤ L) (w : ℝ → ℝ) (hw : Continuous w) {C : ℝ}
    (hC : ∀ s ∈ Ioc (0:ℝ) L, |w s| ≤ C) : Cvs.WeilForm.FormDomain.formDomain hL →ₗ[ℝ] ℝ where
  toFun φ := ∫ s, Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) s * w s
  map_add' φ ψ := by
    have h := Cvs.WeilForm.LevyDomainSpectral.rep_add_ae (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) ψ
    rw [show ((φ + ψ : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) = (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) + ψ from rfl]
    rw [integral_congr_ae (h.mono fun s hs => by rw [hs])]
    simp only [Pi.add_apply, add_mul]
    exact integral_add (integrable_rep_mul hL _ hw hC) (integrable_rep_mul hL _ hw hC)
  map_smul' c φ := by
    have h := Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae c (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    rw [show ((c • φ : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) = c • (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) from rfl]
    rw [integral_congr_ae (h.mono fun s hs => by rw [hs])]
    simp only [mul_assoc, integral_const_mul, RingHom.id_apply, smul_eq_mul]

/-! ### The pole is `2V² − 2U²` -/

/-! ### The problem in Hodge-index form -/

/-- The Toeplitz part of the form on a class: `arch − prime` of the representative. -/
def N (x : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) : ℝ :=
  archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
    - primeTerm x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))

end Cvs.WeilForm.HodgeIndexPoleForm
