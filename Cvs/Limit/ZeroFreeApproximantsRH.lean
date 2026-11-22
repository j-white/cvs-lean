import Mathlib
import Cvs.Limit.OffAxesLimit
import Cvs.Upstream.Hurwitz
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ZeroFreeHeightFive

/-!
# The Riemann Hypothesis from zero-free approximants of `Ξ`

Entire approximants that are zero-free off the two coordinate axes and converge locally
uniformly to `Ξ(z) = ξ(1/2 + i z)` force every critical-strip zero of `ζ` onto the line, and
the zeros off the open strip are the trivial ones, so the Riemann Hypothesis follows.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Limit.ZeroFreeApproximantsRH
/-- **Riemann's `Ξ`**, as a function of `z`: `Ξ(z) = ξ(1/2 + i z)`. -/
def Xi (z : ℂ) : ℂ := Cvs.Zeta.riemannXi (1 / 2 + I * z)

/-- `Ξ` is entire. -/
theorem differentiable_Xi : Differentiable ℂ Xi :=
  Cvs.Zeta.differentiable_riemannXi.comp
    ((differentiable_const _).add ((differentiable_const _).mul differentiable_id))

/-- `Ξ(i/2) = ξ(0) = 1/2 ≠ 0`, so `Ξ` is not the zero function. -/
theorem Xi_half_I_ne_zero : Xi (I / 2) ≠ 0 := by
  have h : (1 / 2 : ℂ) + I * (I / 2) = 0 := by
    have : I * I = -1 := I_mul_I
    linear_combination (1 / 2 : ℂ) * this
  unfold Xi
  rw [h]
  exact Cvs.Zeta.riemannXi_zero_ne_zero

/-- **`Ξ` is nowhere locally zero**: an entire function that is not identically zero. -/
theorem not_eventually_zero (z₀ : ℂ) : ¬ (∀ᶠ z in 𝓝 z₀, Xi z = 0) := by
  intro h
  have hA : AnalyticOnNhd ℂ Xi Set.univ := fun z _ => differentiable_Xi.analyticAt z
  have hE : Set.EqOn Xi 0 Set.univ :=
    hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z₀) h
  exact Xi_half_I_ne_zero (hE (Set.mem_univ _))

/-- **Hurwitz, at `Ξ`.**  If entire approximants are zero-free off the two axes and converge to
`Ξ` locally uniformly, then `Ξ` is zero-free off the two axes. -/
theorem Xi_ne_zero_offAxes (F : ℕ → ℂ → ℂ)
    (hFd : ∀ n, Differentiable ℂ (F n))
    (hFne : ∀ n, ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F Xi atTop (Set.univ : Set ℂ)) :
    ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, Xi z ≠ 0 :=
  fun z hz =>
    Cvs.Upstream.Hurwitz.ne_zero_of_zeroFree_of_tendstoLocallyUniformlyOn
      Cvs.Limit.OffAxesLimit.isOpen_offAxes hz (fun n => (hFd n).differentiableOn) hFne
      (hconv.mono (Set.subset_univ _)) (not_eventually_zero z)

/-- The point of `Ξ` that a zero `ρ` of `ξ` maps to. -/
def zOf (ρ : ℂ) : ℂ := -I * (ρ - 1 / 2)

theorem half_add_I_mul_zOf (ρ : ℂ) : (1 / 2 : ℂ) + I * zOf ρ = ρ := by
  unfold zOf
  have : I * I = -1 := I_mul_I
  linear_combination (-(ρ - 1 / 2)) * this

theorem zOf_re (ρ : ℂ) : (zOf ρ).re = ρ.im := by
  unfold zOf; simp [Complex.mul_re]

theorem zOf_im (ρ : ℂ) : (zOf ρ).im = -(ρ.re - 1 / 2) := by
  unfold zOf; simp [Complex.mul_im]

/-- **A strip zero of `ζ` lies on the line**, once `Ξ` is zero-free off the axes.  The real axis
of `z` is `Re ρ = 1/2`; the imaginary axis would be a real zero of `ξ`, excluded by `ZeroFreeHeightFive`. -/
theorem re_eq_half_of_offAxes (hXi : ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, Xi z ≠ 0)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.re = 1 / 2 := by
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hξ : Cvs.Zeta.riemannXi ρ = 0 :=
    (Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta h0 hρ1).mpr hρ
  have hXz : Xi (zOf ρ) = 0 := by
    unfold Xi; rw [half_add_I_mul_zOf]; exact hξ
  have hnot : zOf ρ ∉ Cvs.Limit.OffAxesLimit.offAxes := fun hin => hXi _ hin hXz
  have hor : (zOf ρ).re = 0 ∨ (zOf ρ).im = 0 := by
    by_contra hc
    push Not at hc
    exact hnot ⟨hc.1, hc.2⟩
  rcases hor with hre | him
  · -- a real zero of `ξ`: excluded
    rw [zOf_re] at hre
    have := Cvs.ZeroFree.abs_im_gt_five_of_riemannXi_eq_zero hξ
    rw [hre] at this
    simp at this
    linarith
  · rw [zOf_im] at him
    linarith

/-- **Every strip zero is on the line**, given the approximants. -/
theorem re_eq_half_of_convergence (F : ℕ → ℂ → ℂ)
    (hFd : ∀ n, Differentiable ℂ (F n))
    (hFne : ∀ n, ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F Xi atTop (Set.univ : Set ℂ))
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.re = 1 / 2 :=
  re_eq_half_of_offAxes (Xi_ne_zero_offAxes F hFd hFne hconv) hρ h0 h1

/-- **The quarantine theorem.**  Mathlib's `RiemannHypothesis` quantifies over every zero of `ζ`
that is neither `1` nor a trivial zero; those outside the open strip are classified by
`htriv`, a classical statement independent of the analytic hypotheses. -/
theorem riemannHypothesis_of_convergence (F : ℕ → ℂ → ℂ)
    (hFd : ∀ n, Differentiable ℂ (F n))
    (hFne : ∀ n, ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F Xi atTop (Set.univ : Set ℂ))
    (htriv : ∀ s : ℂ, riemannZeta s = 0 → ¬ (0 < s.re ∧ s.re < 1) → s ≠ 1 →
      ∃ n : ℕ, s = -2 * (n + 1)) :
    RiemannHypothesis := by
  intro s hs hnt hs1
  by_cases hstrip : 0 < s.re ∧ s.re < 1
  · exact re_eq_half_of_convergence F hFd hFne hconv hs hstrip.1 hstrip.2
  · exact absurd (htriv s hs hstrip hs1) hnt

/-! ### The finite-scale layer

At each scale the family member is the transform of the even-sector minimiser, and its
zero-freeness off the axes follows from that of its own approximants by `Cvs.Limit.OffAxesLimit`, with no sign
hypothesis.  This is the shape in which step (a) feeds the quarantine theorem. -/

/-! ### The classical classification of the zeros off the strip -/

/-- **Even Bernoulli numbers do not vanish**, because `ζ(2m) ≠ 0` for `m ≥ 1`. -/
theorem bernoulli_two_mul_ne_zero {m : ℕ} (hm : m ≠ 0) : bernoulli (2 * m) ≠ 0 := by
  intro hB
  have hz : riemannZeta (2 * m) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    simp; linarith
  apply hz
  rw [riemannZeta_two_mul_nat hm, hB]
  simp

/-- **`ζ` does not vanish at a negative odd integer.** -/
theorem riemannZeta_neg_odd_ne_zero (m : ℕ) : riemannZeta (-((2 * m + 1 : ℕ) : ℂ)) ≠ 0 := by
  rw [riemannZeta_neg_nat_eq_bernoulli]
  have hB : (bernoulli (2 * m + 1 + 1) : ℂ) ≠ 0 := by
    have : bernoulli (2 * (m + 1)) ≠ 0 := bernoulli_two_mul_ne_zero (Nat.succ_ne_zero m)
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
    exact_mod_cast this
  have hden : ((2 * m + 1 : ℕ) : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (2 * m + 1)
  have hsign : ((-1 : ℂ) ^ (2 * m + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact div_ne_zero (mul_ne_zero hsign hB) hden

/-- **A zero of `ζ` off the open strip, other than `1`, is a trivial zero.** -/
theorem trivial_of_zero_off_strip {s : ℂ} (hs : riemannZeta s = 0)
    (hstrip : ¬ (0 < s.re ∧ s.re < 1)) (hs1 : s ≠ 1) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  -- `Re s ≥ 1` is excluded outright
  have hre : s.re ≤ 0 := by
    by_contra h
    push Not at h
    have h1 : s.re < 1 := by
      by_contra h1
      push Not at h1
      exact riemannZeta_ne_zero_of_one_le_re h1 hs
    exact hstrip ⟨h, h1⟩
  by_cases hint : ∃ k : ℕ, s = -k
  · obtain ⟨k, rfl⟩ := hint
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- `k = m + m`
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        simp [hm] at hs
        exact absurd hs (by rw [riemannZeta_zero]; norm_num)
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hmpos)
        refine ⟨n, ?_⟩
        rw [hm]; push_cast; ring
    · -- `k = 2m + 1`
      exact absurd hs (by rw [hm]; exact riemannZeta_neg_odd_ne_zero m)
  · -- the functional equation
    push Not at hint
    have hfe := riemannZeta_one_sub hint hs1
    rw [hs, mul_zero] at hfe
    have hre' : 1 ≤ (1 - s).re := by simp; linarith
    exact absurd hfe (riemannZeta_ne_zero_of_one_le_re hre')

/-- **The quarantine theorem, with the classical part discharged.** -/
theorem riemannHypothesis_of_convergence' (F : ℕ → ℂ → ℂ)
    (hFd : ∀ n, Differentiable ℂ (F n))
    (hFne : ∀ n, ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F Xi atTop (Set.univ : Set ℂ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_convergence F hFd hFne hconv
    (fun _ hs hstrip hs1 => trivial_of_zero_off_strip hs hstrip hs1)

end Cvs.Limit.ZeroFreeApproximantsRH
