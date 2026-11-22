import Mathlib
import Cvs.Finite.ExponentialKernelLocalises

/-!
# The reflection symmetry of the channel Green's function under an odd source

    `f (L − s) = −f s`   ⟹   `convSplit b L f (L − s) = −convSplit b L f s` on `[0, L]`,

and the resulting midpoint vanishing, endpoint symmetry, and halving of the energy integrals.
-/

noncomputable section

open MeasureTheory Set

namespace Cvs.WeilForm.ChannelGreenOddReflection

variable {f : ℝ → ℝ} {L b : ℝ}

/-- **Reflection of the Green's function under an odd source**, for `s ∈ [0, L]`. -/
theorem convSplit_reflect (hf : Continuous f) (hodd : ∀ s, f (L - s) = -f s)
    {s : ℝ} (hs0 : 0 ≤ s) (hsL : s ≤ L) :
    Cvs.Finite.ExponentialKernelLocalises.convSplit b L f (L - s) = -Cvs.Finite.ExponentialKernelLocalises.convSplit b L f s := by
  have hLs0 : 0 ≤ L - s := by linarith
  have hLsL : L - s ≤ L := by linarith
  rw [Cvs.Finite.ExponentialKernelLocalises.convSplit_eq hLs0 hLsL hf, Cvs.Finite.ExponentialKernelLocalises.convSplit_eq hs0 hsL hf]
  have hsub : (∫ u in (0:ℝ)..L, Real.exp (-b * |L - s - u|) * f u)
      = ∫ x in (0:ℝ)..L, Real.exp (-b * |L - s - (L - x)|) * f (L - x) := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := L)
      (fun u => Real.exp (-b * |L - s - u|) * f u) L
    simp only [sub_self, sub_zero] at h
    exact h.symm
  rw [hsub, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [hodd x, show L - s - (L - x) = x - s by ring, abs_sub_comm x s]
  ring

/-- **The midpoint value vanishes.** -/
theorem convSplit_mid (hf : Continuous f) (hodd : ∀ s, f (L - s) = -f s) (hL : 0 ≤ L) :
    Cvs.Finite.ExponentialKernelLocalises.convSplit b L f (L / 2) = 0 := by
  have h := convSplit_reflect hf hodd (b := b) (s := L / 2) (by linarith) (by linarith)
  rw [show L - L / 2 = L / 2 by ring] at h
  linarith

/-- **The endpoints have equal square.** -/
theorem convSplit_endpoints (hf : Continuous f) (hodd : ∀ s, f (L - s) = -f s) (hL : 0 ≤ L) :
    Cvs.Finite.ExponentialKernelLocalises.convSplit b L f L ^ 2 = Cvs.Finite.ExponentialKernelLocalises.convSplit b L f 0 ^ 2 := by
  have h := convSplit_reflect hf hodd (b := b) (s := L) (hL) (le_rfl)
  rw [show L - L = (0:ℝ) by ring] at h
  rw [h]; ring

/-- Reflection of the derivative, from differentiating the reflection identity on `(0, L)`. -/
theorem convDeriv_reflect (hf : Continuous f) (hodd : ∀ s, f (L - s) = -f s)
    {s : ℝ} (hs0 : 0 < s) (hsL : s < L) :
    Cvs.Finite.ExponentialKernelLocalises.convDeriv b L f (L - s) = Cvs.Finite.ExponentialKernelLocalises.convDeriv b L f s := by
  -- both `x ↦ K(L−x)` and `x ↦ −K x` have matching derivatives at `s`
  have h1 := (Cvs.Finite.ExponentialKernelLocalises.hasDerivAt_convSplit (b := b) (L := L) hf (L - s)).comp s
    ((hasDerivAt_id s).const_sub L)
  have h2 := (Cvs.Finite.ExponentialKernelLocalises.hasDerivAt_convSplit (b := b) (L := L) hf s).neg
  have heq : (Cvs.Finite.ExponentialKernelLocalises.convSplit b L f ∘ fun x => L - x)
      =ᶠ[nhds s] fun x => -Cvs.Finite.ExponentialKernelLocalises.convSplit b L f x := by
    filter_upwards [Ioo_mem_nhds hs0 hsL] with x hx
    exact convSplit_reflect hf hodd (le_of_lt hx.1) (le_of_lt hx.2)
  have hu := h1.unique (heq.hasDerivAt_iff.mpr h2)
  simp only [mul_neg, mul_one] at hu
  linarith

end Cvs.WeilForm.ChannelGreenOddReflection
