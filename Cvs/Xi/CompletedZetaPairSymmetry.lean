import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Xi.FoldIntervalOntoRay

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The completed zeta's pair is its own symmetry

Swapping the two members of a pair exchanges their modified functions, and at the origin the even
kernel's pair is its own swap. The two integrals from one are therefore integrals of the same
function, against the two exponents the functional equation exchanges.
-/

noncomputable section

open Set MeasureTheory Complex HurwitzZeta

namespace Cvs.Xi.CompletedZetaPairSymmetry

/-- **Swapping exchanges the modified functions.** -/
theorem g_modif_eq_symm_f_modif (P : WeakFEPair ℂ) : P.g_modif = P.symm.f_modif := rfl

/-- **At the origin the two modified functions agree.** -/
theorem zero_g_modif_eq_f_modif :
    (hurwitzEvenFEPair 0).g_modif = (hurwitzEvenFEPair 0).f_modif := by
  rw [g_modif_eq_symm_f_modif, hurwitzEvenFEPair_zero_symm]

theorem zero_eps : (hurwitzEvenFEPair 0).ε = 1 := rfl

theorem zero_k : (hurwitzEvenFEPair 0).k = 1 / 2 := rfl

/-- **The modified kernel beyond one is the kernel less its limit.** -/
theorem f_modif_of_one_lt {x : ℝ} (hx : 1 < x) :
    (hurwitzEvenFEPair 0).f_modif x = ((evenKernel 0 x : ℝ) : ℂ) - 1 := by
  have h1 : x ∈ Ioi (1 : ℝ) := hx
  have h2 : x ∉ Ioo (0 : ℝ) 1 := fun h => absurd h.2 (not_lt.mpr hx.le)
  simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_mem h1,
    Set.indicator_of_notMem h2, add_zero]
  simp [hurwitzEvenFEPair]

/-- **`Λ₀` for the completed zeta, as two integrals from one.** -/
theorem Λ₀_zero_eq (w : ℂ) :
    (hurwitzEvenFEPair 0).Λ₀ w
      = (∫ x in Ioi (1 : ℝ),
            ((x : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - w - 1) • (hurwitzEvenFEPair 0).f_modif x)
        + ∫ t in Ici (1 : ℝ), (t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif t := by
  rw [Cvs.Xi.FoldIntervalOntoRay.Λ₀_eq_integral_Ioi, zero_g_modif_eq_f_modif, zero_eps, zero_k,
    one_smul]
  norm_num

end Cvs.Xi.CompletedZetaPairSymmetry
