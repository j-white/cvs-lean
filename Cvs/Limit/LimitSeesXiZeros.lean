import Mathlib
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Upstream.Hurwitz

/-!
# Step (b) weakened: the limit only has to see the zeros of `Ξ`
Hurwitz needs less than convergence to `Ξ`. If entire approximants zero-free off the axes converge locally uniformly
to some entire `f ≢ 0`, then `f` is zero-free off the axes; so RH follows as soon as `f` vanishes at every off-axis
zero of `Ξ` (`riemannHypothesis_of_limit`), e.g. when `f = G·Ξ` (`sees_of_factor`). On the even sector:
`riemannHypothesis_of_evenLimit`.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Limit.LimitSeesXiZeros

open Cvs.Limit.OffAxesLimit Cvs.Limit.ZeroFreeApproximantsRH

/-- **RH from a nonzero limit that sees the zeros of `Ξ`.** -/
theorem riemannHypothesis_of_limit (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hFd : ∀ n, Differentiable ℂ (F n))
    (hFne : ∀ n, ∀ z ∈ offAxes, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F f atTop (Set.univ : Set ℂ))
    (hf0 : ∃ z₀, f z₀ ≠ 0)
    (hsees : ∀ z ∈ offAxes, Xi z = 0 → f z = 0) :
    RiemannHypothesis := by
  have hfd' : DifferentiableOn ℂ f Set.univ :=
    hconv.differentiableOn (Eventually.of_forall fun n => (hFd n).differentiableOn) isOpen_univ
  have hfd : Differentiable ℂ f := fun z =>
    (hfd' z (Set.mem_univ z)).differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ z))
  have hnot : ∀ z₀, ¬ (∀ᶠ z in 𝓝 z₀, f z = 0) := by
    intro z₀ h
    obtain ⟨z1, hz1⟩ := hf0
    have hA : AnalyticOnNhd ℂ f Set.univ := fun z _ => hfd.analyticAt z
    exact hz1 (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z₀) h (Set.mem_univ z1))
  have hXi : ∀ z ∈ offAxes, Xi z ≠ 0 := fun z hz hX =>
    Cvs.Upstream.Hurwitz.ne_zero_of_zeroFree_of_tendstoLocallyUniformlyOn isOpen_offAxes hz
      (fun n => (hFd n).differentiableOn) hFne (hconv.mono (Set.subset_univ _)) (hnot z) (hsees z hz hX)
  intro s hs hnt hs1
  by_cases hstrip : 0 < s.re ∧ s.re < 1
  · exact re_eq_half_of_offAxes hXi hs hstrip.1 hstrip.2
  · exact absurd (trivial_of_zero_off_strip hs hstrip hs1) hnt

end Cvs.Limit.LimitSeesXiZeros
