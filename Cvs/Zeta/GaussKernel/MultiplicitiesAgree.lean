import Mathlib
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.RiemannXi

/-!
# The two multiplicities agree

The explicit formula weights its finite zero sum by `MeromorphicOn.divisor riemannXi
Set.univ`.
-/

namespace Cvs.Criterion

open Complex

/-- The critical strip, as an open set. -/
def strip : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

theorem isOpen_strip : IsOpen strip := by
  rw [strip, Set.ofPred_and]
  exact (isOpen_lt (continuous_const (y := (0:ℝ))) Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re (continuous_const (y := (1:ℝ))))

theorem ne_zero_of_mem_strip {s : ℂ} (hs : s ∈ strip) : s ≠ 0 := by
  intro h
  have h0 := hs.1
  rw [h, Complex.zero_re] at h0
  exact lt_irrefl 0 h0

theorem ne_one_of_mem_strip {s : ℂ} (hs : s ∈ strip) : s ≠ 1 := by
  intro h
  have h1 := hs.2
  rw [h, Complex.one_re] at h1
  exact lt_irrefl 1 h1

/-- The analytic, nonvanishing factor carrying `ξ` to `ζ` on the strip. -/
noncomputable def multiplier (s : ℂ) : ℂ := (2 / (s * (s - 1))) * (Gammaℝ s)⁻¹

theorem zeta_eq_xi_mul {s : ℂ} (hs : s ∈ strip) :
    riemannZeta s = Cvs.Zeta.riemannXi s * multiplier s := by
  have hs0 : s ≠ 0 := ne_zero_of_mem_strip hs
  have hs1 : s ≠ 1 := ne_one_of_mem_strip hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs.1
  rw [riemannZeta_def_of_ne_zero hs0, Cvs.Zeta.riemannXi_eq hs0 hs1, multiplier]
  field_simp

theorem analyticAt_multiplier {u : ℂ} (hu : u ∈ strip) : AnalyticAt ℂ multiplier u := by
  have hs0 : u ≠ 0 := ne_zero_of_mem_strip hu
  have hsub : u - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_mem_strip hu)
  have h1 : AnalyticAt ℂ (fun s : ℂ => 2 / (s * (s - 1))) u :=
    (analyticAt_const (v := (2:ℂ))).div
      ((analyticAt_id (𝕜 := ℂ)).mul ((analyticAt_id (𝕜 := ℂ)).sub (analyticAt_const (v := (1:ℂ)))))
      (mul_ne_zero hs0 hsub)
  have h2 : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) u := differentiable_Gammaℝ_inv.analyticAt u
  exact h1.mul h2

theorem multiplier_ne_zero {u : ℂ} (hu : u ∈ strip) : multiplier u ≠ 0 := by
  have hs0 : u ≠ 0 := ne_zero_of_mem_strip hu
  have hsub : u - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_mem_strip hu)
  have hG : Gammaℝ u ≠ 0 := Gammaℝ_ne_zero_of_re_pos hu.1
  exact mul_ne_zero (div_ne_zero two_ne_zero (mul_ne_zero hs0 hsub)) (inv_ne_zero hG)

/-- **The orders agree on the strip.** -/
theorem analyticOrderAt_zeta_eq_xi {u : ℂ} (hu : u ∈ strip) :
    analyticOrderAt riemannZeta u = analyticOrderAt Cvs.Zeta.riemannXi u := by
  have hev : riemannZeta =ᶠ[nhds u] (Cvs.Zeta.riemannXi * multiplier) := by
    filter_upwards [isOpen_strip.mem_nhds hu] with s hs
    exact zeta_eq_xi_mul hs
  rw [analyticOrderAt_congr hev,
    analyticOrderAt_mul (Cvs.Zeta.differentiable_riemannXi.analyticAt u)
      (analyticAt_multiplier hu),
    (analyticAt_multiplier hu).analyticOrderAt_eq_zero.mpr (multiplier_ne_zero hu),
    add_zero]

/-! ### From the order to the formula's multiplicity -/

theorem untop₀_map_toNat (x : ℕ∞) :
    ((x.map (Nat.cast : ℕ → ℤ)).untop₀) = (x.toNat : ℤ) := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/-- **`ξ`'s divisor is `ζ`'s multiplicity on the strip.**  The formula's weight and the
venue's index weight are the same natural number. -/
theorem divisor_eq_multiplicity {u : ℂ} (hu : u ∈ strip) :
    MeromorphicOn.divisor Cvs.Zeta.riemannXi Set.univ u
      = (analyticOrderNatAt riemannZeta u : ℤ) := by
  have hxi : AnalyticAt ℂ Cvs.Zeta.riemannXi u := Cvs.Zeta.differentiable_riemannXi.analyticAt u
  rw [MeromorphicOn.divisor_apply (fun z _ => (Cvs.Zeta.differentiable_riemannXi.analyticAt z).meromorphicAt) (Set.mem_univ u),
    hxi.meromorphicOrderAt_eq, untop₀_map_toNat, analyticOrderNatAt,
    analyticOrderAt_zeta_eq_xi hu]

/-- Every nontrivial zero lies in the strip. -/
theorem mem_strip_of_zero (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) : (rho : ℂ) ∈ strip :=
  ⟨rho.2.2.1, rho.2.2.2⟩

theorem divisor_eq_divisorWeight (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    MeromorphicOn.divisor Cvs.Zeta.riemannXi Set.univ (rho : ℂ)
      = (Cvs.Criterion.divisorWeight rho : ℤ) :=
  divisor_eq_multiplicity (mem_strip_of_zero rho)

/-- **The formula's weight is the criterion's weight.**  Any `m` the explicit formula hands
back agrees with `DivisorWeightCoordinates.divisorWeight` at every nontrivial zero. -/
theorem formula_weight_eq {m : ℂ → ℕ}
    (hm : ∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor Cvs.Zeta.riemannXi Set.univ u)
    (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) : m (rho : ℂ) = Cvs.Criterion.divisorWeight rho := by
  have h := hm (rho : ℂ)
  rw [divisor_eq_divisorWeight rho] at h
  exact_mod_cast h

end Cvs.Criterion
