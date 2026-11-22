import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Cvs.Upstream.Hurwitz

/-!
# The window transform, and reality of its zeros in the limit

`transform L g z = ∫₀^L g x · e^{-i z x}` is entire in `z`, and locally uniform convergence
carries reality of the zeros through to the limit — which is where Hurwitz enters, and the
last analytic step of `CvS`'s theorem.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex MeasureTheory Filter Topology Set intervalIntegral

namespace Cvs.Limit.WindowTransformRealZeros

/-- The transform on the window `[0, L]`. -/
def transform (L : ℝ) (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x in (0:ℝ)..L, g x * Complex.exp (-Complex.I * z * (x : ℂ))

/-- The modulus of the kernel is `e^{x·Im z}`. -/
theorem norm_kernel (z : ℂ) (x : ℝ) :
    ‖Complex.exp (-Complex.I * z * (x : ℂ))‖ = Real.exp (x * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- **On the strip the kernel is bounded**, uniformly in `z`. -/
theorem norm_kernel_le {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) {z : ℂ} (hz : |z.im| ≤ M)
    {x : ℝ} (hx : x ∈ Set.uIcc (0:ℝ) L) :
    ‖Complex.exp (-Complex.I * z * (x : ℂ))‖ ≤ Real.exp (L * M) := by
  rw [norm_kernel]
  refine Real.exp_le_exp.mpr ?_
  rw [Set.uIcc_of_le hL] at hx
  have hx0 : 0 ≤ x := hx.1
  have hxL : x ≤ L := hx.2
  have him : z.im ≤ M := (abs_le.mp hz).2
  nlinarith [hx0, hxL, him, hM]

/-- **The transforms differ by at most `e^{LM}` times the `L¹` distance.** -/
theorem norm_transform_sub_le {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    {g G : ℝ → ℂ} (hg : Continuous g) (hG : Continuous G)
    {z : ℂ} (hz : |z.im| ≤ M) :
    ‖transform L g z - transform L G z‖
      ≤ Real.exp (L * M) * ∫ x in (0:ℝ)..L, ‖g x - G x‖ := by
  have hig : IntervalIntegrable (fun x => g x * Complex.exp (-Complex.I * z * (x : ℂ)))
      volume 0 L := (by fun_prop : Continuous _).intervalIntegrable 0 L
  have hiG : IntervalIntegrable (fun x => G x * Complex.exp (-Complex.I * z * (x : ℂ)))
      volume 0 L := (by fun_prop : Continuous _).intervalIntegrable 0 L
  have hsub : transform L g z - transform L G z
      = ∫ x in (0:ℝ)..L, (g x - G x) * Complex.exp (-Complex.I * z * (x : ℂ)) := by
    unfold transform
    rw [← intervalIntegral.integral_sub hig hiG]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [hsub]
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun x => (g x - G x) * Complex.exp (-Complex.I * z * (x : ℂ))) hL
  refine hnorm.trans ?_
  have hmono : ∫ x in (0:ℝ)..L, ‖(g x - G x) * Complex.exp (-Complex.I * z * (x : ℂ))‖
      ≤ ∫ x in (0:ℝ)..L, ‖g x - G x‖ * Real.exp (L * M) := by
    refine intervalIntegral.integral_mono_on hL
      ((by fun_prop : Continuous _).intervalIntegrable 0 L)
      ((by fun_prop : Continuous _).intervalIntegrable 0 L) ?_
    intro x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_kernel_le hL hM hz (Set.mem_uIcc_of_le hx.1 hx.2)) (norm_nonneg _)
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const, mul_comm]

/-! ### Uniform on strips, hence locally uniform on `ℂ` -/

/-- **Uniform convergence on every horizontal strip.** -/
theorem tendstoUniformlyOn_transform {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    {g : ℕ → ℝ → ℂ} {G : ℝ → ℂ}
    (hg : ∀ n, Continuous (g n)) (hG : Continuous G)
    (hconv : Tendsto (fun n => ∫ x in (0:ℝ)..L, ‖g n x - G x‖) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => transform L (g n)) (transform L G) atTop
      {z : ℂ | |z.im| ≤ M} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hC : (0:ℝ) < Real.exp (L * M) := Real.exp_pos _
  have hev : ∀ᶠ n in atTop, (∫ x in (0:ℝ)..L, ‖g n x - G x‖) < ε / Real.exp (L * M) := by
    have := hconv.eventually (gt_mem_nhds (show (0:ℝ) < ε / Real.exp (L * M) by positivity))
    simpa using this
  filter_upwards [hev] with n hn z hz
  have hzim : |z.im| ≤ M := hz
  have hbd := norm_transform_sub_le hL hM (hg n) hG hzim
  rw [dist_eq_norm, ← norm_neg]
  have hneg : -(transform L G z - transform L (g n) z)
      = transform L (g n) z - transform L G z := by ring
  rw [hneg]
  calc ‖transform L (g n) z - transform L G z‖
      ≤ Real.exp (L * M) * ∫ x in (0:ℝ)..L, ‖g n x - G x‖ := hbd
    _ < Real.exp (L * M) * (ε / Real.exp (L * M)) := by
        exact mul_lt_mul_of_pos_left hn hC
    _ = ε := by field_simp

/-- **Hence locally uniform convergence on all of `ℂ`** — the hypothesis Hurwitz consumes. -/
theorem tendstoLocallyUniformlyOn_transform {L : ℝ} (hL : 0 ≤ L)
    {g : ℕ → ℝ → ℂ} {G : ℝ → ℂ}
    (hg : ∀ n, Continuous (g n)) (hG : Continuous G)
    (hconv : Tendsto (fun n => ∫ x in (0:ℝ)..L, ‖g n x - G x‖) atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun n => transform L (g n)) (transform L G) atTop
      (Set.univ : Set ℂ) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine (tendstoUniformlyOn_transform hL (le_max_right R 0) hg hG hconv).mono ?_
  intro z hz
  have hzR : ‖z‖ ≤ R := by
    have := hR hz
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  exact le_trans (le_trans (Complex.abs_im_le_norm z) hzR) (le_max_left R 0)

/-! ### Step 5's conclusion, given the spectral inputs -/

-- The tail of CvS's Theorem `main`: `finmain` supplies `hreal`, the min-max argument
-- supplies `hconv`, and `hnot` is the nondegeneracy of the limit.
/-- **The zeros of the limit transform are real.**  Given truncations whose transforms are
entire with only real zeros and converge to `G` in `L¹` on the window, every zero of `Ĝ` is
real — provided `Ĝ` is not identically zero near it. -/
theorem im_eq_zero_of_realZeros {L : ℝ} (hL : 0 ≤ L)
    {g : ℕ → ℝ → ℂ} {G : ℝ → ℂ}
    (hg : ∀ n, Continuous (g n)) (hG : Continuous G)
    (hent : ∀ n, Differentiable ℂ (transform L (g n)))
    (hconv : Tendsto (fun n => ∫ x in (0:ℝ)..L, ‖g n x - G x‖) atTop (𝓝 0))
    (hreal : ∀ n, ∀ z : ℂ, transform L (g n) z = 0 → z.im = 0)
    {z₀ : ℂ} (hnot : ¬ (∀ᶠ z in 𝓝 z₀, transform L G z = 0))
    (hz : transform L G z₀ = 0) : z₀.im = 0 :=
  Cvs.Upstream.Hurwitz.im_eq_zero_of_tendstoLocallyUniformlyOn isOpen_univ (Set.mem_univ z₀)
    (fun n => (hent n).differentiableOn)
    (fun n z _ hzero => hreal n z hzero)
    (tendstoLocallyUniformlyOn_transform hL hg hG hconv) hnot hz

end Cvs.Limit.WindowTransformRealZeros
