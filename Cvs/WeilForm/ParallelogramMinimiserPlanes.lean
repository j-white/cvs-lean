import Mathlib
import Cvs.WeilForm.BottomLineFromLowerForm

/-!
# Minimisers of a parallelogram form span planes of minimisers

    `Q(x+y) + Q(x−y) = 2Q(x) + 2Q(y)`, `Q(c x) = c² Q(x)`, `lam ‖·‖² ≤ Q`
        ⟹   minimisers are closed under sums and scalars,

so a form beneath `Q` with second min–max above `lam` on planes of minimisers forces simplicity.
-/

noncomputable section

namespace Cvs.WeilForm.ParallelogramMinimiserPlanes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Minimisers add.** -/
theorem min_add {Q : E → ℝ} {lam : ℝ}
    (hpar : ∀ x y : E, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hbot : ∀ v : E, lam * ‖v‖ ^ 2 ≤ Q v) {x y : E}
    (hx : Q x = lam * ‖x‖ ^ 2) (hy : Q y = lam * ‖y‖ ^ 2) : Q (x + y) = lam * ‖x + y‖ ^ 2 := by
  have h1 := hpar x y
  have h2 := hbot (x + y)
  have h3 := hbot (x - y)
  have h4 := parallelogram_law_with_norm ℝ x y
  have h5 : lam * ‖x + y‖ ^ 2 + lam * ‖x - y‖ ^ 2 = 2 * (lam * ‖x‖ ^ 2) + 2 * (lam * ‖y‖ ^ 2) := by
    linear_combination lam * h4
  linarith

/-- **Minimisers scale.** -/
theorem min_smul {Q : E → ℝ} {lam : ℝ} (hsmul : ∀ (c : ℝ) (x : E), Q (c • x) = c ^ 2 * Q x)
    {x : E} (hx : Q x = lam * ‖x‖ ^ 2) (c : ℝ) : Q (c • x) = lam * ‖c • x‖ ^ 2 := by
  rw [hsmul, hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring

/-- **Minimisers are closed under linear combinations.** -/
theorem min_comb {Q : E → ℝ} {lam : ℝ}
    (hpar : ∀ x y : E, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hsmul : ∀ (c : ℝ) (x : E), Q (c • x) = c ^ 2 * Q x)
    (hbot : ∀ v : E, lam * ‖v‖ ^ 2 ≤ Q v) {x y : E}
    (hx : Q x = lam * ‖x‖ ^ 2) (hy : Q y = lam * ‖y‖ ^ 2) (a b : ℝ) :
    Q (a • x + b • y) = lam * ‖a • x + b • y‖ ^ 2 :=
  min_add hpar hbot (min_smul hsmul hx a) (min_smul hsmul hy b)

/-- **Simplicity from a plane gap of a form beneath**, on a subspace holding every minimiser. -/
theorem simple_of_plane_gap {Q Qt : E → ℝ} {lam mu2 : ℝ}
    (hpar : ∀ x y : E, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hsmul : ∀ (c : ℝ) (x : E), Q (c • x) = c ^ 2 * Q x)
    (hbot : ∀ v : E, lam * ‖v‖ ^ 2 ≤ Q v)
    {W : Submodule ℝ E} (hW : ∀ v : E, Q v = lam * ‖v‖ ^ 2 → v ∈ W)
    (hle : ∀ v ∈ W, Qt v ≤ Q v) (hgap : lam < mu2)
    (hplane : ∀ V : Submodule ℝ E, Module.finrank ℝ V = 2 → V ≤ W →
      ∃ v ∈ V, v ≠ 0 ∧ mu2 * ‖v‖ ^ 2 ≤ Qt v) :
    ∀ v w : E, Q v = lam * ‖v‖ ^ 2 → Q w = lam * ‖w‖ ^ 2 → v ≠ 0 → ∃ c : ℝ, w = c • v := by
  intro v w hv hw hv0
  by_contra hnot
  push Not at hnot
  -- `v, w` are linearly independent
  have hli : LinearIndependent ℝ ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hv0, rfl⟩
    · exfalso
      apply hnot (-s / t)
      have : w = (-s / t) • v := by
        have h1 : t • w = -(s • v) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
        calc w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (-(s • v)) := by rw [h1]
          _ = (-s / t) • v := by rw [smul_neg, smul_smul, neg_div, neg_smul, mul_comm, div_eq_mul_inv]
      exact this
  -- their span is a plane inside `W`, and consists of minimisers
  set V : Submodule ℝ E := Submodule.span ℝ {v, w} with hV
  have hdim : Module.finrank ℝ V = 2 := by
    have := finrank_span_eq_card (R := ℝ) hli
    rw [Cvs.WeilForm.BottomLineFromLowerForm.range_pair] at this
    simpa using this
  have hVW : V ≤ W := by
    rw [hV, Submodule.span_le]
    rintro z (rfl | rfl)
    · exact hW _ hv
    · exact hW _ hw
  obtain ⟨u, huV, hu0, hu⟩ := hplane V hdim hVW
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp huV
  have hmin := min_comb hpar hsmul hbot hv hw a b
  have hQ := hle _ (hVW huV)
  have hpos : 0 < ‖a • v + b • w‖ ^ 2 := by
    have : ‖a • v + b • w‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    positivity
  have : mu2 * ‖a • v + b • w‖ ^ 2 ≤ lam * ‖a • v + b • w‖ ^ 2 := by linarith
  have := le_of_mul_le_mul_right this hpos
  linarith

end Cvs.WeilForm.ParallelogramMinimiserPlanes
