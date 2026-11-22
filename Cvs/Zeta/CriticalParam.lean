import Mathlib

/-!
# The classical parameterisation, and where the `n^{−1/2}` went

`Cvs.Zeta.GuinandWeilFourier` has the prime side as `Σ_n Λ(n)·n^{−2}·φ̂(log n)`.
-/

open Complex

namespace Cvs.Zeta

/-- The classical parameterisation: a test function on the critical line, transported to a
test function of `s`.  If `ρ = ½ + iγ` then `ofCritical h ρ = h γ`. -/
noncomputable def ofCritical (h : ℂ → ℂ) (s : ℂ) : ℂ := h (-I * (s - 1 / 2))

@[simp] theorem ofCritical_critical (h : ℂ → ℂ) (γ : ℂ) :
    ofCritical h (1 / 2 + γ * I) = h γ := by
  unfold ofCritical
  congr 1
  have : (1 : ℂ) / 2 + γ * I - 1 / 2 = γ * I := by ring
  rw [this]
  linear_combination (-γ) * Complex.I_sq

/-- **The symmetry hypothesis is exactly "`h` is even".**  `φ(1−s) = φ(s)` for
`φ = ofCritical h` iff `h(−w) = h(w)` — the hypothesis Guinand–Weil is classically stated
with. -/
theorem ofCritical_symm_iff (h : ℂ → ℂ) :
    (∀ s : ℂ, ofCritical h (1 - s) = ofCritical h s) ↔ ∀ w : ℂ, h (-w) = h w := by
  constructor
  · intro hs w
    have := hs (1 / 2 + w * I)
    rwa [ofCritical_critical, show (1 : ℂ) - (1 / 2 + w * I) = 1 / 2 + (-w) * I by ring,
      ofCritical_critical] at this
  · intro hh s
    unfold ofCritical
    have : -I * (1 - s - 1 / 2) = -(-I * (s - 1 / 2)) := by ring
    rw [this, hh]

/-- `ofCritical h` is entire when `h` is. -/
theorem differentiable_ofCritical {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    Differentiable ℂ (ofCritical h) := by
  unfold ofCritical
  fun_prop

end Cvs.Zeta
