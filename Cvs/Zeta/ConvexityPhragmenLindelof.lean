import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Cvs.Zeta.ConvexityAuxDifferentiable
import Cvs.Zeta.ConvexityEvenBranch

/-!
# The Phragmén–Lindelöf application

The convexity argument's Layer 4, assembled.
-/

open Complex

namespace Cvs.ArchScore

/-- **The modulus of the even-branch auxiliary.** for `evenLog`. -/
theorem norm_aux_even (f : ℂ → ℂ) (c K a' b' : ℝ) (s : ℂ) :
    ‖Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b' s‖
      = ‖f s‖ * Real.exp (-(a' + b' * s.re) * (Cvs.ArchScore.evenLog c K s).re
          + b' * s.im * (Cvs.ArchScore.evenLog c K s).im) := by
  rw [Cvs.Zeta.ConvexityAuxDifferentiable.aux, norm_mul, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Undoing the damping.**  A bound on the auxiliary is a bound on `f` with the damping
factor restored — and the restored factor carries the interpolated exponent. -/
theorem norm_le_of_norm_aux_le {f : ℂ → ℂ} {c K a' b' C : ℝ} {s : ℂ}
    (h : ‖Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b' s‖ ≤ C) :
    ‖f s‖ ≤ C * Real.exp ((a' + b' * s.re) * (Cvs.ArchScore.evenLog c K s).re
      - b' * s.im * (Cvs.ArchScore.evenLog c K s).im) := by
  rw [norm_aux_even] at h
  set E : ℝ := Real.exp (-(a' + b' * s.re) * (Cvs.ArchScore.evenLog c K s).re
    + b' * s.im * (Cvs.ArchScore.evenLog c K s).im) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hinv : Real.exp ((a' + b' * s.re) * (Cvs.ArchScore.evenLog c K s).re
      - b' * s.im * (Cvs.ArchScore.evenLog c K s).im) = E⁻¹ := by
    rw [hE, ← Real.exp_neg]
    congr 1
    ring
  rw [hinv, ← le_div_iff₀ hEpos] at *
  rw [div_eq_mul_inv] at *
  linarith [h]

/-- **The application.** With's structural hypothesis and constant edge bounds on both sides —
which `ConvexityEvenBranch` made possible — `PhragmenLindelof.vertical_strip` bounds the auxiliary throughout
the strip. -/
theorem norm_aux_le_of_edges {f : ℂ → ℂ} {c K α β a' b' C : ℝ}
    (hd : DiffContOnCl ℂ (Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b') (Cvs.Zeta.ConvexityAuxDifferentiable.strip α β))
    (hgrow : ∃ e < Real.pi / (β - α), ∃ B,
      (Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b') =O[Filter.comap (fun z : ℂ => |z.im|) Filter.atTop
        ⊓ Filter.principal (Cvs.Zeta.ConvexityAuxDifferentiable.strip α β)]
        fun z : ℂ => Real.exp (B * Real.exp (e * |z.im|)))
    (hea : ∀ z : ℂ, z.re = α → ‖Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b' z‖ ≤ C)
    (heb : ∀ z : ℂ, z.re = β → ‖Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b' z‖ ≤ C)
    {s : ℂ} (h1 : α ≤ s.re) (h2 : s.re ≤ β) :
    ‖Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b' s‖ ≤ C :=
  PhragmenLindelof.vertical_strip hd hgrow hea heb h1 h2

end Cvs.ArchScore
