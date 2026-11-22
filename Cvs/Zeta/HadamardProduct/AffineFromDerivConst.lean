import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The endgame of rung 3, and a correction about what it needs
-/

open Complex Filter Topology

namespace Cvs.ZeroFree

/-- If `h'` is constant then `h` is affine. -/
theorem affine_of_deriv_const {h : ℂ → ℂ} {a : ℂ} (hh : Differentiable ℂ h)
    (hd : ∀ z, deriv h z = a) : ∀ z, h z = a * z + h 0 := by
  intro z
  set k : ℂ → ℂ := fun w => h w - a * w with hk
  have hkdiff : Differentiable ℂ k := hh.sub (differentiable_id.const_mul _)
  have hkderiv : ∀ w : ℂ, deriv k w = 0 := by
    intro w
    have h1 : HasDerivAt h (deriv h w) w := (hh w).hasDerivAt
    have h2 : HasDerivAt (fun u : ℂ => a * u) a w := by
      have hmc := hasDerivAt_mul_const (c := a) (x := w)
      have heq : (fun u : ℂ => u * a) = fun u : ℂ => a * u := by funext u; ring
      rwa [heq] at hmc
    have h3 : HasDerivAt k (deriv h w - a) w := h1.sub h2
    rw [h3.deriv, hd w, sub_self]
  have hkc : k z = k 0 := is_const_of_deriv_eq_zero hkdiff hkderiv z 0
  rw [hk] at hkc
  simp only [mul_zero, sub_zero] at hkc
  linear_combination hkc

/-- **`h'' ≡ 0` and entire ⟹ affine.** The form the Landau route produces, as opposed to's growth
form. -/
theorem exists_affine_of_deriv_deriv_eq_zero {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (h2 : ∀ z, deriv (deriv h) z = 0) : ∃ a b : ℂ, ∀ z, h z = a * z + b := by
  have hderivDiff : Differentiable ℂ (deriv h) := by
    have hana : AnalyticOnNhd ℂ h Set.univ := hh.differentiableOn.analyticOnNhd isOpen_univ
    intro z
    exact ((hana.deriv_of_isOpen isOpen_univ) z (Set.mem_univ z)).differentiableAt
  have hconst : ∀ z : ℂ, deriv h z = deriv h 0 :=
    fun z => is_const_of_deriv_eq_zero hderivDiff h2 z 0
  exact ⟨deriv h 0, h 0, affine_of_deriv_const hh hconst⟩

end Cvs.ZeroFree
