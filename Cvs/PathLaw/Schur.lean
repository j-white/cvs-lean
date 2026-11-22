/-
The Single-Atom Path Law — the Schur/Rayleigh hinge for the chain
bound.

The chain argument bounds `‖W‖` by exhibiting a positive weight
along each chain (the sine eigenvector of `Cvs.PathLaw.Spectrum`) and
running a weighted AM-GM on the quadratic form. This file proves the
*operator-theoretic* half of that route, once and for all: a symmetric
operator whose quadratic form is bounded by `K` has norm at most `K`.

With this in hand, the remaining content of the chain clause of
`MaskedRotationModel` is purely a quadratic-form estimate — no operator
theory left.

Blocks leaned on:
* `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` — for symmetric
  operators, the norm is the supremum of `|Rayleigh quotient|`;
* `ContinuousLinearMap.bddAbove_rayleighQuotient`, `ciSup_le`.

Proved here (no `sorry`):
* `opNorm_le_of_quadratic_form_le` — the hinge, in any real inner product
  space;
* `norm_maskedRotation_le_of_quadratic_form_le` — its specialization to the
  masked rotation on `L²(𝕋)`, which is exactly the shape the chain
  weighted AM-GM produces;
* `pathLaw_of_quadratic_form` — the Single-Atom Path Law reduced to a
  two-sided quadratic-form statement about `W`.
-/
import Cvs.PathLaw.Statement

open MeasureTheory Real RCLike
open scoped RealInnerProductSpace

namespace Cvs.PathLaw

/-! ### The hinge -/

section Hinge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Quadratic form bound ⟹ operator norm bound.** If `S` is symmetric and
`|⟪S x, x⟫| ≤ K ‖x‖²` for every `x`, then `‖S‖ ≤ K`.

This is the step that turns the chain weighted AM-GM estimate into
a statement about the operator norm. -/
theorem opNorm_le_of_quadratic_form_le (S : E →L[ℝ] E)
    (hsymm : (S : E →ₗ[ℝ] E).IsSymmetric) {K : ℝ} (hK : 0 ≤ K)
    (hquad : ∀ x : E, |⟪S x, x⟫| ≤ K * ‖x‖ ^ 2) : ‖S‖ ≤ K := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient S hsymm]
  refine ciSup_le fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using hK
  · have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_of_pos hx2,
      div_le_iff₀ hx2]
    refine le_trans ?_ (hquad x)
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact le_of_eq rfl

/-- **Quadratic form lower bound ⟹ operator norm lower bound.** A single test
vector with a large Rayleigh quotient forces the norm up. This is the mirror
of `opNorm_le_of_quadratic_form_le`, and it is what turns an eigenvector into
attainment. -/
theorem le_opNorm_of_quadratic_form (S : E →L[ℝ] E) {K : ℝ} (x : E) (hx : x ≠ 0)
    (hquad : K * ‖x‖ ^ 2 ≤ inner ℝ (S x) x) : K ≤ ‖S‖ := by
  have h1 : inner ℝ (S x) x ≤ ‖S x‖ * ‖x‖ := real_inner_le_norm _ _
  have h2 : ‖S x‖ ≤ ‖S‖ * ‖x‖ := S.le_opNorm x
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h3 : ‖S x‖ * ‖x‖ ≤ ‖S‖ * ‖x‖ * ‖x‖ :=
    mul_le_mul_of_nonneg_right h2 (norm_nonneg x)
  have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  nlinarith [h1, h3, hquad, hx2]

end Hinge

/-! ### Specialization to the masked rotation -/

variable {P : ℝ} [Fact (0 < P)]

/-- The chain estimate, in the form it is actually used: if
the masked rotation is symmetric and its quadratic form is bounded by
`chebFactor m`, then `‖W‖ ≤ chebFactor m`.

Combined with `Cvs.PathLaw.Transfer.single_atom_path_law_le_of`, this gives the
Path Law's upper bound from a purely pointwise (AM-GM) estimate. -/
theorem norm_maskedRotation_le_of_quadratic_form_le
    (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) (m : ℕ) (hm : 0 < m)
    (hsymm : ((maskedRotation a s₁ s₂ h₁ h₂ :
        Lp ℝ 2 (volume : Measure (AddCircle P)) →L[ℝ]
          Lp ℝ 2 (volume : Measure (AddCircle P))) :
        Lp ℝ 2 (volume : Measure (AddCircle P)) →ₗ[ℝ]
          Lp ℝ 2 (volume : Measure (AddCircle P))).IsSymmetric)
    (hquad : ∀ f : Lp ℝ 2 (volume : Measure (AddCircle P)),
      |⟪maskedRotation a s₁ s₂ h₁ h₂ f, f⟫| ≤ chebFactor m * ‖f‖ ^ 2) :
    ‖maskedRotation a s₁ s₂ h₁ h₂‖ ≤ chebFactor m :=
  opNorm_le_of_quadratic_form_le _ hsymm (chebFactor_nonneg m hm) hquad

/-- **The Path Law from a quadratic-form estimate.** Combining the hinge with
the transfer principle: an atom that transfers to a weighted masked rotation
whose quadratic form obeys the Chebyshev bound satisfies the Path Law bound
`‖T‖ ≤ pathLawNorm q c`.

Every remaining hypothesis here is either a pointwise inequality (`hquad`,
supplied by the chain weighted AM-GM) or a structural identity
(`hsymm`, `htransfer`). -/
theorem pathLaw_le_of_quadratic_form (q c : ℕ)
    (T : AtomSpace →L[ℝ] AtomSpace)
    (e : AtomSpace ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (AddCircle P)))
    (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (hcap : 0 < capacity (Real.log c) (Real.log q))
    (htransfer : ∀ x, (weight q • maskedRotation a s₁ s₂ h₁ h₂) (e x) = e (T x))
    (hsymm : ((maskedRotation a s₁ s₂ h₁ h₂ :
        Lp ℝ 2 (volume : Measure (AddCircle P)) →L[ℝ]
          Lp ℝ 2 (volume : Measure (AddCircle P))) :
        Lp ℝ 2 (volume : Measure (AddCircle P)) →ₗ[ℝ]
          Lp ℝ 2 (volume : Measure (AddCircle P))).IsSymmetric)
    (hquad : ∀ f : Lp ℝ 2 (volume : Measure (AddCircle P)),
      |⟪maskedRotation a s₁ s₂ h₁ h₂ f, f⟫|
        ≤ chebFactor (capacity (Real.log c) (Real.log q)) * ‖f‖ ^ 2) :
    ‖T‖ ≤ pathLawNorm q c :=
  single_atom_path_law_le_of q c T e a s₁ s₂ h₁ h₂ htransfer
    (norm_maskedRotation_le_of_quadratic_form_le a s₁ s₂ h₁ h₂ _ hcap hsymm hquad)

/-! ### The pointwise AM-GM behind the chain estimate -/

/-- **Weighted AM-GM.** For any positive weight `t`,
`2|uv| ≤ t u² + v²/t`. This is the pointwise inequality the chain
argument applies along each chain, with `t` built from the sine
eigenvector of `Cvs.PathLaw.Spectrum`. -/
theorem two_abs_mul_le {t : ℝ} (ht : 0 < t) (u v : ℝ) :
    2 * |u * v| ≤ t * u ^ 2 + v ^ 2 / t := by
  rw [abs_mul, ← sub_nonneg]
  have h : t * u ^ 2 + v ^ 2 / t - 2 * (|u| * |v|) = (t * |u| - |v|) ^ 2 / t := by
    field_simp
    nlinarith [sq_abs u, sq_abs v]
  rw [h]
  positivity

/-! ### The `L²` norm as an integral -/

variable {P : ℝ} [Fact (0 < P)]

/-- `‖f‖² = ∫ f²` on `L²(𝕋)`. -/
theorem norm_sq_eq_integral (f : Lp ℝ 2 (volume : Measure (AddCircle P))) :
    ‖f‖ ^ 2 = ∫ x, (f : AddCircle P → ℝ) x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

/-! ### The Schur test in operator form

The chain estimate is a weighted AM-GM. Carried out at the level of
operators rather than integrals, it becomes Cauchy-Schwarz applied to a
*factorization* of the atom half `A = C^* B` — which needs no measure theory
at all, and so avoids every integrability side condition. -/

/-- **Operator-form Schur test.** If `⟪A x, x⟫ = ⟪B x, C x⟫` for all `x`
(i.e. `A = C^* B`), then `2|⟪A f, f⟫| ≤ ‖B f‖² + ‖C f‖²`.

Taking `B = M_{√w} M_{s₁} K_α` and `C = M_{1/√w} M_{s₁}` for a positive
weight `w` recovers exactly the weighted AM-GM of the chain
argument, with the weight now carried by the two factors. -/
theorem two_abs_inner_le_of_factorization {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →L[ℝ] E) (B C : E →L[ℝ] F)
    (hfac : ∀ x : E, inner ℝ (A x) x = inner ℝ (B x) (C x)) (f : E) :
    2 * |inner ℝ (A f) f| ≤ ‖B f‖ ^ 2 + ‖C f‖ ^ 2 := by
  rw [hfac]
  have h1 : |inner ℝ (B f) (C f)| ≤ ‖B f‖ * ‖C f‖ := abs_real_inner_le_norm _ _
  nlinarith [sq_nonneg (‖B f‖ - ‖C f‖)]

end Cvs.PathLaw
