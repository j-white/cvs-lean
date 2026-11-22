import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Hurwitz's theorem, via the maximum modulus principle

If each `F n` is zero-free on a closed disc and `F n → f` uniformly there, then `1/F n` is
holomorphic, so the maximum modulus principle bounds it inside by its bound on the circle,
where the uniform limit keeps `‖F n‖` away from `0`.  No contour integral of `f'/f`.
-/

noncomputable section

open Complex Metric Filter Topology Set

namespace Cvs.Upstream.Hurwitz

variable {z₀ : ℂ} {r : ℝ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}

/-- **The circle keeps the limit away from zero.**  A continuous nonvanishing function on the
sphere is bounded below there. -/
theorem exists_pos_le_norm_on_sphere (hr : 0 < r)
    (hfc : ContinuousOn f (sphere z₀ r)) (hfne : ∀ z ∈ sphere z₀ r, f z ≠ 0) :
    ∃ c > 0, ∀ z ∈ sphere z₀ r, c ≤ ‖f z‖ := by
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hfc.norm
  refine ⟨‖f w‖, norm_pos_iff.mpr (hfne w hw), fun z hz => hmin hz⟩

/-- **Local Hurwitz.**  A uniform limit of functions with no zeros on a closed disc has no
zero at its centre. -/
theorem ne_zero_of_tendstoUniformlyOn (hr : 0 < r)
    (hFd : ∀ n, DiffContOnCl ℂ (F n) (ball z₀ r))
    (hFne : ∀ n, ∀ z ∈ closedBall z₀ r, F n z ≠ 0)
    (hunif : TendstoUniformlyOn F f atTop (closedBall z₀ r))
    (hfc : ContinuousOn f (closedBall z₀ r))
    (hfne : ∀ z ∈ sphere z₀ r, f z ≠ 0) :
    f z₀ ≠ 0 := by
  obtain ⟨c, hc, hcle⟩ :=
    exists_pos_le_norm_on_sphere hr (hfc.mono sphere_subset_closedBall) hfne
  set B : ℝ := c / 2 with hBdef
  have hB : 0 < B := by rw [hBdef]; linarith
  -- eventually `‖F n‖ ≥ B` on the circle
  have hev : ∀ᶠ n in atTop, ∀ z ∈ sphere z₀ r, B ≤ ‖F n z‖ := by
    have hmet := Metric.tendstoUniformlyOn_iff.mp hunif B hB
    filter_upwards [hmet] with n hn z hz
    have hz' : z ∈ closedBall z₀ r := sphere_subset_closedBall hz
    have hd : dist (f z) (F n z) < B := hn z hz'
    rw [dist_eq_norm] at hd
    have hsub : ‖f z‖ - ‖F n z‖ ≤ ‖f z - F n z‖ := norm_sub_norm_le _ _
    have hfz := hcle z hz
    rw [hBdef] at *
    linarith
  -- the maximum modulus principle applied to `1/F n`
  have hbound : ∀ᶠ n in atTop, B ≤ ‖F n z₀‖ := by
    filter_upwards [hev] with n hn
    have hinvd : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball z₀ r) := by
      refine ⟨(hFd n).differentiableOn.inv fun z hz => hFne n z (ball_subset_closedBall hz), ?_⟩
      refine (hFd n).continuousOn.inv₀ ?_
      intro z hz
      rw [closure_ball z₀ (ne_of_gt hr)] at hz
      exact hFne n z hz
    have hfront : ∀ z ∈ frontier (ball z₀ r), ‖(F n z)⁻¹‖ ≤ B⁻¹ := by
      intro z hz
      rw [frontier_ball z₀ (ne_of_gt hr)] at hz
      have hge := hn z hz
      have hpz : 0 < ‖F n z‖ := lt_of_lt_of_le hB hge
      rw [norm_inv]
      exact (inv_le_inv₀ hpz hB).mpr hge
    have hz₀mem : z₀ ∈ closure (ball z₀ r) := by
      rw [closure_ball z₀ (ne_of_gt hr)]; exact mem_closedBall_self hr.le
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hinvd hfront hz₀mem
    rw [norm_inv] at hmax
    have hFz : F n z₀ ≠ 0 := hFne n z₀ (mem_closedBall_self hr.le)
    have hpos : 0 < ‖F n z₀‖ := norm_pos_iff.mpr hFz
    exact (inv_le_inv₀ hpos hB).mp hmax
  -- pass to the limit
  have hlim : Tendsto (fun n => F n z₀) atTop (𝓝 (f z₀)) :=
    hunif.tendsto_at (mem_closedBall_self hr.le)
  have hnorm : Tendsto (fun n => ‖F n z₀‖) atTop (𝓝 ‖f z₀‖) := hlim.norm
  have hfin : B ≤ ‖f z₀‖ := ge_of_tendsto hnorm hbound
  intro h
  rw [h, norm_zero] at hfin
  linarith

/-! ### The real-zeros form -/

/-- A closed disc centred off the real axis, of radius smaller than the centre's height,
misses the real axis. -/
theorem im_ne_zero_of_mem_closedBall (him : r < |z₀.im|) {z : ℂ}
    (hz : z ∈ closedBall z₀ r) : z.im ≠ 0 := by
  intro h
  have hd : ‖z - z₀‖ ≤ r := by rwa [← dist_eq_norm, ← Metric.mem_closedBall]
  have hle : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, h, zero_sub, abs_neg] at hle
  linarith

/-- **Hurwitz, real-zeros form.**  If every `F n` has only real zeros and `F n → f` uniformly
on a closed disc centred off the real axis, then `f` does not vanish at the centre. -/
theorem ne_zero_of_realZeros (hr : 0 < r) (him : r < |z₀.im|)
    (hFd : ∀ n, DiffContOnCl ℂ (F n) (ball z₀ r))
    (hFreal : ∀ n, ∀ z ∈ closedBall z₀ r, F n z = 0 → z.im = 0)
    (hunif : TendstoUniformlyOn F f atTop (closedBall z₀ r))
    (hfc : ContinuousOn f (closedBall z₀ r))
    (hfne : ∀ z ∈ sphere z₀ r, f z ≠ 0) :
    f z₀ ≠ 0 :=
  ne_zero_of_tendstoUniformlyOn hr hFd
    (fun n z hz hzero => im_ne_zero_of_mem_closedBall him hz (hFreal n z hz hzero))
    hunif hfc hfne

/-! ### The usable form: locally uniform convergence on an open set -/

/-- **Hurwitz, for real zeros.**  If each `F n` is holomorphic on an open `U` with only real
zeros there and `F n → f` locally uniformly with `f` not identically zero near `z₀ ∈ U`, then
every zero of `f` in `U` is real. -/
theorem im_eq_zero_of_tendstoLocallyUniformlyOn
    {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hFd : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFreal : ∀ n, ∀ z ∈ U, F n z = 0 → z.im = 0)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hnot : ¬ (∀ᶠ z in 𝓝 z₀, f z = 0))
    (hz : f z₀ = 0) : z₀.im = 0 := by
  by_contra him0
  -- `f` is holomorphic on `U`, hence analytic at `z₀`, hence its zeros are isolated
  have hfd : DifferentiableOn ℂ f U :=
    hconv.differentiableOn (Filter.Eventually.of_forall hFd) hU
  have hfa : AnalyticAt ℂ f z₀ := hfd.analyticAt (hU.mem_nhds hz₀)
  have hiso : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 :=
    (hfa.eventually_eq_zero_or_eventually_ne_zero).resolve_left hnot
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hiso
  obtain ⟨e1, he1, hiso'⟩ := hiso
  -- a closed disc inside `U`
  obtain ⟨e2, he2, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  -- and small enough to miss the real axis
  have himpos : 0 < |z₀.im| := abs_pos.mpr him0
  set r : ℝ := min (min (e1 / 2) (e2 / 2)) (|z₀.im| / 2) with hrdef
  have hr : 0 < r := by
    rw [hrdef]; exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hre1 : r < e1 := lt_of_le_of_lt (min_le_of_left_le (min_le_left _ _)) (by linarith)
  have hre2 : r < e2 := lt_of_le_of_lt (min_le_of_left_le (min_le_right _ _)) (by linarith)
  have him : r < |z₀.im| := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcballU : closedBall z₀ r ⊆ U := fun z hz =>
    hball (by rw [Metric.mem_closedBall] at hz; exact Metric.mem_ball.mpr (lt_of_le_of_lt hz hre2))
  have hballU : ball z₀ r ⊆ U := (ball_subset_closedBall).trans hcballU
  -- the hypotheses of the disc version
  have hFdc : ∀ n, DiffContOnCl ℂ (F n) (ball z₀ r) := by
    intro n
    refine ⟨(hFd n).mono hballU, ?_⟩
    rw [closure_ball z₀ (ne_of_gt hr)]
    exact ((hFd n).mono hcballU).continuousOn
  have hunif : TendstoUniformlyOn F f atTop (closedBall z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv _ hcballU
      (isCompact_closedBall z₀ r)
  have hfc : ContinuousOn f (closedBall z₀ r) := (hfd.mono hcballU).continuousOn
  have hfne : ∀ z ∈ sphere z₀ r, f z ≠ 0 := by
    intro z hz
    rw [Metric.mem_sphere] at hz
    refine hiso' (by rw [hz]; exact hre1) ?_
    intro hzz
    rw [hzz] at hz
    simp at hz
    linarith
  exact ne_zero_of_realZeros hr him hFdc
    (fun n z hz' hzero => hFreal n z (hcballU hz') hzero) hunif hfc hfne hz

/-- **Hurwitz's theorem, classical form.**  A locally uniform limit of zero-free holomorphic
functions is itself zero-free, unless it vanishes identically near the point. -/
theorem ne_zero_of_zeroFree_of_tendstoLocallyUniformlyOn
    {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hFd : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFne : ∀ n, ∀ z ∈ U, F n z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hnot : ¬ (∀ᶠ z in 𝓝 z₀, f z = 0)) :
    f z₀ ≠ 0 := by
  have hfd : DifferentiableOn ℂ f U :=
    hconv.differentiableOn (Filter.Eventually.of_forall hFd) hU
  have hfa : AnalyticAt ℂ f z₀ := hfd.analyticAt (hU.mem_nhds hz₀)
  have hiso : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 :=
    (hfa.eventually_eq_zero_or_eventually_ne_zero).resolve_left hnot
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hiso
  obtain ⟨e1, he1, hiso'⟩ := hiso
  obtain ⟨e2, he2, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  set r : ℝ := min (e1 / 2) (e2 / 2) with hrdef
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hre1 : r < e1 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hre2 : r < e2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcballU : closedBall z₀ r ⊆ U := fun z hz =>
    hball (by rw [Metric.mem_closedBall] at hz; exact Metric.mem_ball.mpr (lt_of_le_of_lt hz hre2))
  have hballU : ball z₀ r ⊆ U := (ball_subset_closedBall).trans hcballU
  have hFdc : ∀ n, DiffContOnCl ℂ (F n) (ball z₀ r) := by
    intro n
    refine ⟨(hFd n).mono hballU, ?_⟩
    rw [closure_ball z₀ (ne_of_gt hr)]
    exact ((hFd n).mono hcballU).continuousOn
  have hunif : TendstoUniformlyOn F f atTop (closedBall z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv _ hcballU
      (isCompact_closedBall z₀ r)
  have hfc : ContinuousOn f (closedBall z₀ r) := (hfd.mono hcballU).continuousOn
  have hfne : ∀ z ∈ sphere z₀ r, f z ≠ 0 := by
    intro z hz
    rw [Metric.mem_sphere] at hz
    refine hiso' (by rw [hz]; exact hre1) ?_
    intro hzz
    rw [hzz] at hz
    simp at hz
    linarith
  exact ne_zero_of_tendstoUniformlyOn hr hFdc
    (fun n z hz => hFne n z (hcballU hz)) hunif hfc hfne

end Cvs.Upstream.Hurwitz
