/-
The Single-Atom Path Law — symmetry of the masked rotation.

The Schur/Rayleigh hinge of `Cvs.PathLaw.Schur` needs `W` to be symmetric. This
file proves it, under exactly the paper's mask condition `s₂ = s₁ + α`
(with `s₁ = [-α, 0]`, `s₂ = [0, α]`, this is an identity).

Consequently the `hsymm` hypothesis of `norm_maskedRotation_le_of_quadratic_form_le`
and `pathLaw_le_of_quadratic_form` is DISCHARGED for the paper's operator:
what stands between the formalization and the Path Law's upper bound is now
a single pointwise (AM-GM) estimate on the quadratic form.

Blocks leaned on:
* `MeasureTheory.L2.inner_def` — the `L²` inner product as an integral;
* `MeasureTheory.MeasurePreserving.integral_comp` +
  `MeasurableEquiv.addRight` — translation change of variables;
* `MeasureTheory.Lp.coeFn_compMeasurePreserving`, `MemLp.coeFn_toLp` — the
  a.e. descriptions of the Koopman and mask operators.

Proved here (no `sorry`):
* `inner_maskCLM_left` — the mask operator is symmetric;
* `inner_koopman_left` — `⟪K_a f, g⟫ = ⟪f, K_{-a} g⟫`;
* `koopman_maskCLM` — the mask/rotation commutation under `s₂ = s₁ + α`;
* `isSymmetric_maskedRotation` — `W` is symmetric;
* `norm_maskedRotation_le_of_quadratic_form_le'` and
  `pathLaw_le_of_quadratic_form'` — the Schur route with `hsymm` discharged.
-/
import Cvs.PathLaw.Schur

open MeasureTheory Real

namespace Cvs.PathLaw

variable {P : ℝ} [Fact (0 < P)]

local notation "L2" => Lp ℝ 2 (volume : Measure (AddCircle P))

/-! ### The mask operator is symmetric -/

theorem inner_maskCLM_left (s : Set (AddCircle P)) (hs : MeasurableSet s)
    (f g : L2) :
    inner ℝ (maskCLM volume s hs f) g = inner ℝ f (maskCLM volume s hs g) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_maskFun volume s hs f, coeFn_maskFun volume s hs g]
    with x h1 h2
  have e1 : (maskCLM volume s hs f : AddCircle P → ℝ) x = s.indicator (f : AddCircle P → ℝ) x := h1
  have e2 : (maskCLM volume s hs g : AddCircle P → ℝ) x = s.indicator (g : AddCircle P → ℝ) x := h2
  rw [RCLike.inner_apply, RCLike.inner_apply, e1, e2]
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-! ### The Koopman operator's adjoint is the reverse rotation -/

/-- The a.e. description of the Koopman operator: `(K_a f)(x) = f(x + a)`. -/
lemma koopman_ae (a : AddCircle P) (f : L2) :
    ∀ᵐ x ∂(volume : Measure (AddCircle P)),
      (koopman a f : AddCircle P → ℝ) x = (f : AddCircle P → ℝ) (x + a) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume a)]
    with x hx using hx

theorem inner_koopman_left (a : AddCircle P) (f g : L2) :
    inner ℝ (koopman a f) g = inner ℝ f (koopman (-a) g) := by
  rw [L2.inner_def, L2.inner_def]
  have hmp : MeasurePreserving (fun x : AddCircle P => x + a) volume volume :=
    measurePreserving_add_right volume a
  have hcov := hmp.integral_comp (MeasurableEquiv.addRight a).measurableEmbedding
    (fun psi : AddCircle P =>
      inner ℝ ((f : AddCircle P → ℝ) psi) ((g : AddCircle P → ℝ) (psi + -a)))
  calc ∫ x, inner ℝ ((koopman a f : AddCircle P → ℝ) x) ((g : AddCircle P → ℝ) x)
      = ∫ x, inner ℝ ((f : AddCircle P → ℝ) (x + a))
              ((g : AddCircle P → ℝ) (x + a + -a)) := by
        refine integral_congr_ae ?_
        filter_upwards [koopman_ae a f] with x hx
        rw [hx, add_neg_cancel_right]
    _ = ∫ psi, inner ℝ ((f : AddCircle P → ℝ) psi)
              ((g : AddCircle P → ℝ) (psi + -a)) := hcov
    _ = ∫ x, inner ℝ ((f : AddCircle P → ℝ) x)
              ((koopman (-a) g : AddCircle P → ℝ) x) := by
        refine integral_congr_ae ?_
        filter_upwards [koopman_ae (-a) g] with x hx
        rw [hx]

/-! ### Transporting a.e. statements along a rotation -/

/-- A rotation is measure preserving, so an a.e. statement pulls back along
it. -/
lemma ae_translate {β : Type*} {F H : AddCircle P → β} (b : AddCircle P)
    (h : F =ᵐ[(volume : Measure (AddCircle P))] H) :
    ∀ᵐ x ∂(volume : Measure (AddCircle P)), F (x + b) = H (x + b) := by
  have hmp : MeasurePreserving (fun x : AddCircle P => x + b) volume volume :=
    measurePreserving_add_right volume b
  exact hmp.quasiMeasurePreserving.ae_eq_comp h

/-! ### The mask/rotation commutation -/

/-- The paper's mask condition: `s₂` is `s₁` translated by the rotation
angle. For `s₁ = [-α, 0]` and `s₂ = [0, α]` this holds. -/
def MaskShift (a : AddCircle P) (s₁ s₂ : Set (AddCircle P)) : Prop :=
  s₂ = (fun x => x + -a) ⁻¹' s₁

/-- Under the mask condition, the reverse rotation carries the `s₁`-mask to
the `s₂`-mask. -/
theorem koopman_maskCLM (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (hmask : MaskShift a s₁ s₂) (g : L2) :
    koopman (-a) (maskCLM volume s₁ h₁ g)
      = maskCLM volume s₂ h₂ (koopman (-a) g) := by
  apply Lp.ext
  filter_upwards [koopman_ae (-a) (maskCLM volume s₁ h₁ g),
    ae_translate (-a) (coeFn_maskCLM volume s₁ h₁ g),
    coeFn_maskCLM volume s₂ h₂ (koopman (-a) g),
    koopman_ae (-a) g] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3, hmask]
  by_cases hxs : x + -a ∈ s₁
  · rw [Set.indicator_of_mem hxs,
      Set.indicator_of_mem (show x ∈ (fun y : AddCircle P => y + -a) ⁻¹' s₁ from hxs), hx4]
  · rw [Set.indicator_of_notMem hxs,
      Set.indicator_of_notMem (show x ∉ (fun y : AddCircle P => y + -a) ⁻¹' s₁ from hxs)]

/-- The forward direction of the same commutation. -/
theorem koopman_maskCLM' (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (hmask : MaskShift a s₁ s₂) (g : L2) :
    koopman a (maskCLM volume s₂ h₂ g)
      = maskCLM volume s₁ h₁ (koopman a g) := by
  apply Lp.ext
  filter_upwards [koopman_ae a (maskCLM volume s₂ h₂ g),
    ae_translate a (coeFn_maskCLM volume s₂ h₂ g),
    coeFn_maskCLM volume s₁ h₁ (koopman a g),
    koopman_ae a g] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3, hmask]
  have hcancel : x + a + -a = x := by abel
  by_cases hxs : x ∈ s₁
  · rw [Set.indicator_of_mem
        (show x + a ∈ (fun y : AddCircle P => y + -a) ⁻¹' s₁ by
          simp only [Set.mem_preimage, hcancel]; exact hxs),
      Set.indicator_of_mem hxs, hx4]
  · rw [Set.indicator_of_notMem
        (show x + a ∉ (fun y : AddCircle P => y + -a) ⁻¹' s₁ by
          simp only [Set.mem_preimage, hcancel]; exact hxs),
      Set.indicator_of_notMem hxs]

/-! ### Symmetry of the masked rotation -/

/-- Pointwise description of `W`. -/
private lemma maskedRotation_apply (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) (u : L2) :
    maskedRotation a s₁ s₂ h₁ h₂ u
      = maskCLM volume s₁ h₁ (koopman a u)
        + maskCLM volume s₂ h₂ (koopman (-a) u) := rfl

/-- **The masked rotation is symmetric** under the paper's mask condition
`s₂ = s₁ + α`. This discharges the `hsymm` hypothesis of the Schur hinge. -/
theorem isSymmetric_maskedRotation (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (hmask : MaskShift a s₁ s₂) :
    ((maskedRotation a s₁ s₂ h₁ h₂ : L2 →L[ℝ] L2) : L2 →ₗ[ℝ] L2).IsSymmetric := by
  intro f g
  show inner ℝ (maskedRotation a s₁ s₂ h₁ h₂ f) g
      = inner ℝ f (maskedRotation a s₁ s₂ h₁ h₂ g)
  rw [maskedRotation_apply, maskedRotation_apply, inner_add_left, inner_add_right,
    inner_maskCLM_left, inner_maskCLM_left, inner_koopman_left, inner_koopman_left,
    neg_neg, koopman_maskCLM a s₁ s₂ h₁ h₂ hmask g,
    koopman_maskCLM' a s₁ s₂ h₁ h₂ hmask g, add_comm]

/-! ### The Schur route with `hsymm` discharged -/

/-- The chain estimate, now needing only the quadratic-form
bound: symmetry is supplied by `isSymmetric_maskedRotation`. -/
theorem norm_maskedRotation_le_of_quad (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) (hmask : MaskShift a s₁ s₂)
    (m : ℕ) (hm : 0 < m)
    (hquad : ∀ f : L2, |inner ℝ (maskedRotation a s₁ s₂ h₁ h₂ f) f|
      ≤ chebFactor m * ‖f‖ ^ 2) :
    ‖maskedRotation a s₁ s₂ h₁ h₂‖ ≤ chebFactor m :=
  opNorm_le_of_quadratic_form_le _ (isSymmetric_maskedRotation a s₁ s₂ h₁ h₂ hmask)
    (chebFactor_nonneg m hm) hquad

/-- **The Path Law's upper bound from a pointwise estimate.** With symmetry
discharged, an atom transferring to the paper's masked rotation satisfies
`‖T‖ ≤ pathLawNorm q c` as soon as the quadratic form obeys the Chebyshev
bound — a purely pointwise (AM-GM) hypothesis. -/
theorem pathLaw_le_of_quad (q c : ℕ) (T : AtomSpace →L[ℝ] AtomSpace)
    (e : AtomSpace ≃ₗᵢ[ℝ] L2) (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) (hmask : MaskShift a s₁ s₂)
    (hcap : 0 < capacity (Real.log c) (Real.log q))
    (htransfer : ∀ x, (weight q • maskedRotation a s₁ s₂ h₁ h₂) (e x) = e (T x))
    (hquad : ∀ f : L2, |inner ℝ (maskedRotation a s₁ s₂ h₁ h₂ f) f|
      ≤ chebFactor (capacity (Real.log c) (Real.log q)) * ‖f‖ ^ 2) :
    ‖T‖ ≤ pathLawNorm q c :=
  single_atom_path_law_le_of q c T e a s₁ s₂ h₁ h₂ htransfer
    (norm_maskedRotation_le_of_quad a s₁ s₂ h₁ h₂ hmask _ hcap hquad)

/-! ### The quadratic form of the masked rotation -/

/-- **The quadratic form collapses to a single term.** Under the mask
condition the two halves of `W` contribute equally:
`⟪W f, f⟫ = 2 ⟪M_{s₁} K_α f, f⟫`.

Proved purely from the adjoint lemmas above — no new integral computation. -/
theorem inner_maskedRotation_self (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (hmask : MaskShift a s₁ s₂) (f : L2) :
    inner ℝ (maskedRotation a s₁ s₂ h₁ h₂ f) f
      = 2 * inner ℝ (maskCLM volume s₁ h₁ (koopman a f)) f := by
  rw [maskedRotation_apply, inner_add_left]
  have h : inner ℝ (maskCLM volume s₂ h₂ (koopman (-a) f)) f
      = inner ℝ (maskCLM volume s₁ h₁ (koopman a f)) f := by
    rw [inner_maskCLM_left, inner_koopman_left, neg_neg,
      koopman_maskCLM' a s₁ s₂ h₁ h₂ hmask f]
    exact real_inner_comm _ _
  rw [h]
  ring

/-- The surviving half of the quadratic form, as an integral:
`⟪M_{s₁} K_α f, f⟫ = ∫ 1_{s₁}(x) f(x+α) f(x) dx`. -/
theorem inner_maskCLM_koopman_eq_integral (a : AddCircle P) (s₁ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (f : L2) :
    inner ℝ (maskCLM volume s₁ h₁ (koopman a f)) f
      = ∫ x, s₁.indicator (fun y => (f : AddCircle P → ℝ) (y + a)) x
              * (f : AddCircle P → ℝ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_maskCLM volume s₁ h₁ (koopman a f), koopman_ae a f]
    with x h1 h2
  rw [RCLike.inner_apply, h1]
  by_cases hx : x ∈ s₁
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h2]
    simp [mul_comm]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- **The full quadratic form as an integral.** Combining the two results:
`⟪W f, f⟫ = 2 ∫ 1_{s₁}(x) f(x+α) f(x) dx`. This is the exact expression the
chain weighted AM-GM estimates. -/
theorem inner_maskedRotation_self_eq_integral (a : AddCircle P)
    (s₁ s₂ : Set (AddCircle P)) (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (hmask : MaskShift a s₁ s₂) (f : L2) :
    inner ℝ (maskedRotation a s₁ s₂ h₁ h₂ f) f
      = 2 * ∫ x, s₁.indicator (fun y => (f : AddCircle P → ℝ) (y + a)) x
                  * (f : AddCircle P → ℝ) x := by
  rw [inner_maskedRotation_self a s₁ s₂ h₁ h₂ hmask f,
    inner_maskCLM_koopman_eq_integral a s₁ h₁ f]

/-! ### The chain step reduced to a factorization -/

/-- The atom half `A = M_{s} K_a`, of which `W` is `A + A^*`. -/
noncomputable def atomHalf (a : AddCircle P) (s : Set (AddCircle P))
    (hs : MeasurableSet s) : L2 →L[ℝ] L2 :=
  (maskCLM volume s hs).comp (koopman a).toContinuousLinearMap

@[simp] lemma atomHalf_apply (a : AddCircle P) (s : Set (AddCircle P))
    (hs : MeasurableSet s) (u : L2) :
    atomHalf a s hs u = maskCLM volume s hs (koopman a u) := rfl

/-- **The quadratic form bound from a factorization.** If the atom half
factors as `A = C^* B`, then the quadratic form of `W` is controlled by
`‖B f‖² + ‖C f‖²`. -/
theorem abs_inner_maskedRotation_self_le (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) (hmask : MaskShift a s₁ s₂)
    (B C : L2 →L[ℝ] L2)
    (hfac : ∀ x : L2, inner ℝ (atomHalf a s₁ h₁ x) x = inner ℝ (B x) (C x))
    (f : L2) :
    |inner ℝ (maskedRotation a s₁ s₂ h₁ h₂ f) f| ≤ ‖B f‖ ^ 2 + ‖C f‖ ^ 2 := by
  have h := two_abs_inner_le_of_factorization (atomHalf a s₁ h₁) B C hfac f
  rw [inner_maskedRotation_self a s₁ s₂ h₁ h₂ hmask f, abs_mul, abs_two]
  exact h

/-- **The chain bound from a factorization.** Exhibiting a factorization of
the atom half with `‖B f‖² + ‖C f‖² ≤ K ‖f‖²` bounds the masked rotation's
operator norm by `K`.

This is the chain step, stripped to its irreducible content: no
operator theory, no measure theory, no integrability — only the construction
of the two weighted factors, which the chain decomposition supplies
(`Cvs.PathLaw.Weight`). -/
theorem norm_maskedRotation_le_of_factorization (a : AddCircle P)
    (s₁ s₂ : Set (AddCircle P)) (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (hmask : MaskShift a s₁ s₂) {K : ℝ} (hK : 0 ≤ K) (B C : L2 →L[ℝ] L2)
    (hfac : ∀ x : L2, inner ℝ (atomHalf a s₁ h₁ x) x = inner ℝ (B x) (C x))
    (hbound : ∀ f : L2, ‖B f‖ ^ 2 + ‖C f‖ ^ 2 ≤ K * ‖f‖ ^ 2) :
    ‖maskedRotation a s₁ s₂ h₁ h₂‖ ≤ K :=
  opNorm_le_of_quadratic_form_le _
    (isSymmetric_maskedRotation a s₁ s₂ h₁ h₂ hmask) hK
    (fun f => le_trans
      (abs_inner_maskedRotation_self_le a s₁ s₂ h₁ h₂ hmask B C hfac f) (hbound f))

/-- **The Path Law's upper bound from a factorization.** The complete
reduction: an atom transferring to the paper's masked rotation satisfies
`‖T‖ ≤ pathLawNorm q c` as soon as its half factors as `C^* B` with
`‖B f‖² + ‖C f‖² ≤ 2cos(π/(m+1)) ‖f‖²`. -/
theorem pathLaw_le_of_factorization (q c : ℕ) (T : AtomSpace →L[ℝ] AtomSpace)
    (e : AtomSpace ≃ₗᵢ[ℝ] L2) (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) (hmask : MaskShift a s₁ s₂)
    (hcap : 0 < capacity (Real.log c) (Real.log q))
    (htransfer : ∀ x, (weight q • maskedRotation a s₁ s₂ h₁ h₂) (e x) = e (T x))
    (B C : L2 →L[ℝ] L2)
    (hfac : ∀ x : L2, inner ℝ (atomHalf a s₁ h₁ x) x = inner ℝ (B x) (C x))
    (hbound : ∀ f : L2, ‖B f‖ ^ 2 + ‖C f‖ ^ 2
      ≤ chebFactor (capacity (Real.log c) (Real.log q)) * ‖f‖ ^ 2) :
    ‖T‖ ≤ pathLawNorm q c :=
  single_atom_path_law_le_of q c T e a s₁ s₂ h₁ h₂ htransfer
    (norm_maskedRotation_le_of_factorization a s₁ s₂ h₁ h₂ hmask
      (chebFactor_nonneg _ hcap) B C hfac hbound)

end Cvs.PathLaw
