import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiVertical
import Cvs.Zeta.ZetaZeroWindows

/-!
# The `RiemannVonMangoldt` / venue bridge

`RiemannVonMangoldt` counts `Cvs.Zeta.riemannXi` zeros by `MeromorphicOn.divisor`; the bucket machinery
counts `CompletedZetaZeroIndex` by `analyticOrderNatAt riemannZeta`.  `sum_eq_count` is the
identification.  RH.md §3.20 carries the route and the two things worth knowing about it.
-/

set_option maxHeartbeats 1600000

noncomputable section

set_option maxHeartbeats 1600000
set_option autoImplicit false

noncomputable section
open Complex

namespace Cvs.Zeta.XiZeroStripBridge

/-- `ξ` does not vanish on `Re s ≥ 1`. -/
theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : Cvs.Zeta.riemannXi s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1]
    simp [Cvs.Zeta.riemannXi]
  · have hpos : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
    intro hz
    exact riemannZeta_ne_zero_of_one_le_re hs
      ((Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta hpos h1).mp hz)

/-- **`ξ`'s zeros lie in the open critical strip.**  `Re ≥ 1` is Mathlib's non-vanishing;
`Re ≤ 0` reflects there by the functional equation. -/
theorem riemannXi_mem_strip {s : ℂ} (h : Cvs.Zeta.riemannXi s = 0) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hcon
    push_neg at hcon
    have hre : 1 ≤ (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact riemannXi_ne_zero_of_one_le_re hre (by rw [Cvs.Zeta.riemannXi_one_sub]; exact h)
  · by_contra hcon
    push_neg at hcon
    exact riemannXi_ne_zero_of_one_le_re hcon h

/-- A `ξ`-zero is a nontrivial zeta zero. -/
noncomputable def toVenue {u : ℂ} (h : Cvs.Zeta.riemannXi u = 0) :
    Cvs.Zeta.Explicit.Venue.nontrivialRiemannZetaZeros := by
  refine ⟨⟨u, ?_⟩, (riemannXi_mem_strip h).1, (riemannXi_mem_strip h).2⟩
  have hstrip := riemannXi_mem_strip h
  have hne1 : u ≠ 1 := by
    intro hu
    rw [hu] at hstrip
    simp at hstrip
  simpa [riemannZetaZeros] using
    (Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta hstrip.1 hne1).mp h

@[simp] theorem toVenue_value {u : ℂ} (h : Cvs.Zeta.riemannXi u = 0) :
    Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue (toVenue h) = u := rfl

end Cvs.Zeta.XiZeroStripBridge
