import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Landau's cancellation step: dividing out the inner zeros

Rung 6 needs `ξ'/ξ` bounded on horizontal lines, and the naive route to that runs through
Hadamard: write `ξ = (canonical product)·e^h`, show `h` is affine so that `h'` is constant.
-/

open Complex Set Metric Finset

namespace Cvs.Zeta

/-- **The estimate that makes Landau's lemma work without a minimum-modulus theorem.** -/
theorem one_le_norm_one_sub_div {ρ z : ℂ} {r : ℝ} (hρ0 : ρ ≠ 0) (hρ : ‖ρ‖ ≤ r)
    (hz : ‖z‖ = 2 * r) : 1 ≤ ‖1 - z / ρ‖ := by
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hrewrite : (1 : ℂ) - z / ρ = (ρ - z) / ρ := by field_simp
  rw [hrewrite, norm_div, le_div_iff₀ hρpos]
  have h1 : ‖z‖ - ‖ρ‖ ≤ ‖ρ - z‖ := by
    rw [← norm_neg (ρ - z), neg_sub]
    exact norm_sub_norm_le z ρ
  rw [hz] at h1
  linarith

/-- The same for a finite product of such factors, with multiplicities. -/
theorem one_le_norm_prod_one_sub_div {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} {r : ℝ}
    (hS : ∀ ρ ∈ S, ρ ≠ 0 ∧ ‖ρ‖ ≤ r) (hz : ‖z‖ = 2 * r) :
    1 ≤ ‖∏ ρ ∈ S, (1 - z / ρ) ^ m ρ‖ := by
  rw [norm_prod]
  calc (1 : ℝ) = ∏ _ρ ∈ S, (1 : ℝ) := by simp
    _ ≤ ∏ ρ ∈ S, ‖(1 - z / ρ) ^ m ρ‖ := by
        refine Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun ρ hρ => ?_
        rw [norm_pow]
        exact one_le_pow₀ (one_le_norm_one_sub_div (hS ρ hρ).1 (hS ρ hρ).2 hz)

/-- **Dividing out the inner zeros costs nothing.** Let `f = g · P` on the disc of radius `2r`,
where `P` is the product of the linear factors of `f`'s zeros in the *inner* disc `‖ρ‖ ≤ r`. -/
theorem norm_le_of_divide_out_inner_zeros {f g : ℂ → ℂ} {S : Finset ℂ} {m : ℂ → ℕ}
    {r M : ℝ} (hr : 0 < r)
    (hfg : ∀ z, f z = g z * ∏ ρ ∈ S, (1 - z / ρ) ^ m ρ)
    (hS : ∀ ρ ∈ S, ρ ≠ 0 ∧ ‖ρ‖ ≤ r)
    (hgd : DiffContOnCl ℂ g (ball 0 (2 * r)))
    (hM : ∀ z : ℂ, ‖z‖ = 2 * r → ‖f z‖ ≤ M) :
    ∀ z ∈ closedBall (0 : ℂ) (2 * r), ‖g z‖ ≤ M := by
  intro z hz
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hgd ?_ ?_
  · intro w hw
    rw [frontier_ball _ (by positivity : (2 : ℝ) * r ≠ 0), mem_sphere_iff_norm, sub_zero] at hw
    have hP : 1 ≤ ‖∏ ρ ∈ S, (1 - w / ρ) ^ m ρ‖ := one_le_norm_prod_one_sub_div hS hw
    have hfw : ‖f w‖ ≤ M := hM w hw
    rw [hfg w, norm_mul] at hfw
    nlinarith [norm_nonneg (g w), hfw, hP]
  · rwa [closure_ball _ (by positivity : (2 : ℝ) * r ≠ 0)]

/-! ### The logarithm on the inner disc -/

/-- **A zero-free analytic function on a disc is `exp` of an analytic function.** The entire
version is `Cvs.Zeta.exists_differentiable_exp_eq`; this is the local one, which is what
Landau's route needs — the quotient there is zero-free only on the inner disc. -/
theorem exists_differentiableOn_exp_eq_ball {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hg0 : ∀ z ∈ ball c r, g z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c r) ∧
      ∀ z ∈ ball c r, g z = Complex.exp (h z) := by
  have hopen : IsOpen (ball c r) := isOpen_ball
  have hcmem : c ∈ ball c r := mem_ball_self hr
  -- `g` is analytic on the ball, so `deriv g` is differentiable there
  have hana : AnalyticOnNhd ℂ g (ball c r) := hg.analyticOnNhd hopen
  have hderiv : DifferentiableOn ℂ (deriv g) (ball c r) :=
    fun z hz => ((hana z hz).deriv).differentiableAt.differentiableWithinAt
  have hld : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c r) := by
    intro z hz
    exact ((hderiv z hz).div (hg z hz) (hg0 z hz))
  obtain ⟨H, hH⟩ := hld.isExactOn_ball
  set h : ℂ → ℂ := fun z => H z + (Complex.log (g c) - H c) with hhdef
  have hHd : DifferentiableOn ℂ H (ball c r) :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  have hhd : DifferentiableOn ℂ h (ball c r) := hHd.add_const _
  refine ⟨h, hhd, ?_⟩
  -- `F := g · exp (-h)` has vanishing derivative on the ball
  set F : ℂ → ℂ := fun z => g z * Complex.exp (-h z) with hFdef
  have hFderiv : ∀ z ∈ ball c r, HasDerivAt F 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z :=
      ((hana z hz).differentiableAt).hasDerivAt
    have hhz : HasDerivAt h (deriv g z / g z) z := by
      have := (hH z hz)
      simpa [hhdef] using this.add_const (Complex.log (g c) - H c)
    have hexp : HasDerivAt (fun w => Complex.exp (-h w))
        (-(Complex.exp (-h z) * (deriv g z / g z))) z := by
      simpa using (hhz.neg).cexp
    have hmul := hgz.mul hexp
    have hgne : g z ≠ 0 := hg0 z hz
    have hval : deriv g z * Complex.exp (-h z)
        + g z * -(Complex.exp (-h z) * (deriv g z / g z)) = 0 := by
      field_simp
      ring
    rwa [hval] at hmul
  have hconst : ∀ z ∈ ball c r, F z = F c := by
    intro z hz
    refine (convex_ball c r).is_const_of_fderivWithin_eq_zero
      (fun w hw => (hFderiv w hw).differentiableAt.differentiableWithinAt) ?_ hz hcmem
    intro w hw
    have hF0 : HasFDerivAt F (0 : ℂ →L[ℂ] ℂ) w := by
      simpa using (hFderiv w hw).hasFDerivAt
    rw [fderivWithin_of_isOpen hopen hw, hF0.fderiv]
  -- `F c = 1`, so `g = exp h` throughout
  have hFc : F c = 1 := by
    have hgc : g c ≠ 0 := hg0 c hcmem
    simp only [hFdef, hhdef]
    rw [show -(H c + (Complex.log (g c) - H c)) = -Complex.log (g c) by ring,
      Complex.exp_neg, Complex.exp_log hgc]
    field_simp
  intro z hz
  have := hconst z hz
  rw [hFc] at this
  simp only [hFdef] at this
  rw [Complex.exp_neg] at this
  field_simp at this
  exact this

/-! ### Borel–Carathéodory and the Cauchy estimate -/

/-- **Landau, step 4: the logarithm is bounded on a smaller disc.** If `g` is analytic, zero-free
and bounded by `M` on `ball 0 R`, write `g = exp h` (`exists_differentiableOn_exp_eq_ball`). -/
theorem exists_log_bound_of_bounded {g : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hg0 : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hM : ∀ z ∈ ball 0 R, ‖g z‖ ≤ M) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball 0 R) ∧
      (∀ z ∈ ball 0 R, g z = Complex.exp (h z)) ∧
      ∀ z : ℂ, ‖z‖ ≤ R / 2 →
        ‖h z - h 0‖ ≤ 2 * (Real.log M - Real.log ‖g 0‖ + 1) := by
  obtain ⟨h, hhd, hexp⟩ := exists_differentiableOn_exp_eq_ball hR hg hg0
  refine ⟨h, hhd, hexp, ?_⟩
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hg00 : g 0 ≠ 0 := hg0 0 h0mem
  have hgn0 : (0 : ℝ) < ‖g 0‖ := norm_pos_iff.mpr hg00
  -- `Re h = log ‖g‖`
  have hre : ∀ w ∈ ball (0 : ℂ) R, (h w).re = Real.log ‖g w‖ := by
    intro w hw
    rw [hexp w hw, Complex.norm_exp, Real.log_exp]
  set B : ℝ := Real.log M - Real.log ‖g 0‖ + 1 with hB
  have hBpos : 0 < B := by
    have : Real.log ‖g 0‖ ≤ Real.log M :=
      Real.log_le_log hgn0 (hM 0 h0mem)
    rw [hB]; linarith
  -- the shifted logarithm has real part `≤ B` and vanishes at `0`
  set φ : ℂ → ℂ := fun w => h w - h 0 with hφ
  have hφd : DifferentiableOn ℂ φ (ball 0 R) := hhd.sub_const _
  have hφ0 : φ 0 = 0 := by simp [hφ]
  have hmaps : MapsTo φ (ball (0 : ℂ) R) {w : ℂ | w.re ≤ B} := by
    intro w hw
    have h1 : (h w).re = Real.log ‖g w‖ := hre w hw
    have h2 : (h 0).re = Real.log ‖g 0‖ := hre 0 h0mem
    have h3 : Real.log ‖g w‖ ≤ Real.log M :=
      Real.log_le_log (norm_pos_iff.mpr (hg0 w hw)) (hM w hw)
    simp only [Set.mem_ofPred_eq, hφ, Complex.sub_re, h1, h2]
    rw [hB]; linarith
  intro z hz
  have hzR : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; linarith
  have hbc := Complex.borelCaratheodory hBpos hφd hmaps hR hzR
  rw [hφ0, norm_zero] at hbc
  simp only [zero_mul, zero_div, add_zero] at hbc
  have hden : 0 < R - ‖z‖ := by linarith
  have hfin : 2 * B * ‖z‖ / (R - ‖z‖) ≤ 2 * B := by
    rw [div_le_iff₀ hden]
    nlinarith [hBpos, norm_nonneg z]
  exact le_trans hbc hfin

/-- **Landau, step 5: the logarithmic derivative is bounded.** A Cauchy estimate at radius `R/4`
turns the bound on `h - h 0` into a bound on `h'`, and `h' = g'/g` because `g = exp h`. -/
theorem norm_logDeriv_le_of_bounded {g : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hg0 : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hM : ∀ z ∈ ball 0 R, ‖g z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ R / 4) :
    ‖deriv g z / g z‖ ≤ 8 * (Real.log M - Real.log ‖g 0‖ + 1) / R := by
  obtain ⟨h, hhd, hexp, hbound⟩ := exists_log_bound_of_bounded hR hg hg0 hM
  set B : ℝ := Real.log M - Real.log ‖g 0‖ + 1 with hB
  set φ : ℂ → ℂ := fun w => h w - h 0 with hφ
  have hopen : IsOpen (ball (0 : ℂ) R) := isOpen_ball
  -- the closed disc of radius `R/4` about `z` sits inside `ball 0 (R/2)`
  have hsub : closedBall z (R / 4) ⊆ ball (0 : ℂ) R := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ = ‖z + (w - z)‖ := by congr 1; ring
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ ≤ R / 4 + R / 4 := by linarith
      _ < R := by linarith
  have hφd : DiffContOnCl ℂ φ (ball z (R / 4)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ (by positivity : R / 4 ≠ 0)]
    exact fun w hw => ((hhd.sub_const (h 0)) w (hsub hw)).mono hsub
  have hC : ∀ w ∈ sphere z (R / 4), ‖φ w‖ ≤ 2 * B := by
    intro w hw
    rw [mem_sphere_iff_norm] at hw
    refine hbound w ?_
    calc ‖w‖ = ‖z + (w - z)‖ := by congr 1; ring
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ ≤ R / 4 + R / 4 := by rw [hw]; linarith
      _ = R / 2 := by ring
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
    (by positivity : (0:ℝ) < R / 4) hφd hC
  rw [iteratedDeriv_one] at hcau
  -- `deriv φ = deriv h`, and `h' = g'/g`
  have hzmem : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; linarith
  have hderivφ : deriv φ z = deriv h z := by
    simp [hφ, deriv_sub_const]
  have hhz : DifferentiableAt ℂ h z := (hhd.differentiableAt (hopen.mem_nhds hzmem))
  have hgz : g =ᶠ[nhds z] fun w => Complex.exp (h w) := by
    filter_upwards [hopen.mem_nhds hzmem] with w hw using hexp w hw
  have hdg : deriv g z = Complex.exp (h z) * deriv h z := by
    rw [hgz.deriv_eq]
    exact (hhz.hasDerivAt.cexp).deriv
  have hgnz : g z ≠ 0 := hg0 z hzmem
  have hquot : deriv g z / g z = deriv h z := by
    rw [hdg, hexp z hzmem]
    field_simp
  rw [hquot, ← hderivφ]
  refine le_trans hcau (le_of_eq ?_)
  simp only [Nat.factorial_one, Nat.cast_one, pow_one]
  field_simp
  ring

end Cvs.Zeta
