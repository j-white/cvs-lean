import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Cvs.Upstream.DigammaBounds
import Cvs.Zeta.Digamma.WeierstrassGammaSeq

/-!
# The Euler–Gauss limit for the digamma function

    ψ(s) = lim_n (log n − ∑_{k<n} 1/(s+k))    for `0 < re s`

Mathlib has `GammaSeq_tendsto_Gamma` pointwise; this is its logarithmic-derivative form.
-/

noncomputable section

open Filter Topology Complex Real

namespace Cvs.Upstream.GammaEulerLimit

/-- The `k`-th term of the Gauss series, `1/(k+1) − 1/(s+k)` in closed form. -/
def gaussTerm (s : ℂ) (k : ℕ) : ℂ := (s - 1) / ((k + 1) * (s + k))

/-- The half-plane the series is summed on. -/
def rightHalf : Set ℂ := {s : ℂ | 0 < s.re}

theorem isOpen_rightHalf : IsOpen rightHalf :=
  isOpen_lt continuous_const Complex.continuous_re

/-- On the right half-plane `s + k` never vanishes. -/
theorem add_natCast_ne_zero {s : ℂ} (hs : 0 < s.re) (k : ℕ) : s + (k : ℂ) ≠ 0 := by
  intro h
  have hre : (s + (k : ℂ)).re = s.re + k := by simp
  rw [h] at hre
  simp only [Complex.zero_re] at hre
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- **The term is the difference it abbreviates.** -/
theorem gaussTerm_eq {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    gaussTerm s k = ((k : ℂ) + 1)⁻¹ - (s + (k : ℂ))⁻¹ := by
  have h1 : ((k : ℂ) + 1) ≠ 0 := by
    intro h
    have : ((k : ℝ) + 1) = 0 := by exact_mod_cast congrArg Complex.re h
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have h2 : s + (k : ℂ) ≠ 0 := add_natCast_ne_zero hs k
  simp only [gaussTerm]
  field_simp
  ring

/-- **The partial sums, rearranged.**  The Euler–Gauss sequence is the harmonic deficit plus
a partial sum of `gaussTerm`. -/
theorem partial_eq {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (Real.log n : ℂ) - ∑ k ∈ Finset.range n, (s + (k : ℂ))⁻¹
      = ((Real.log n : ℂ) - ∑ k ∈ Finset.range n, ((k : ℂ) + 1)⁻¹)
        + ∑ k ∈ Finset.range n, gaussTerm s k := by
  rw [Finset.sum_congr rfl (fun k _ => gaussTerm_eq hs k), Finset.sum_sub_distrib]
  ring

/-! ### The series converges, locally uniformly -/

/-- **The term is `O(k⁻²)`**, uniformly on any set where `re s ≥ a` and `‖s − 1‖ ≤ M`. -/
theorem norm_gaussTerm_le {s : ℂ} {a M : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hsa : a ≤ s.re)
    (hM : ‖s - 1‖ ≤ M) (k : ℕ) :
    ‖gaussTerm s k‖ ≤ M / (a * ((k : ℝ) + 1) ^ 2) := by
  have hk1 : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hre : (k : ℝ) + a ≤ ‖s + (k : ℂ)‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hpos : 0 < ‖s + (k : ℂ)‖ := lt_of_lt_of_le (by positivity) hre
  have hlow : a * ((k : ℝ) + 1) ≤ ‖s + (k : ℂ)‖ := by
    refine le_trans ?_ hre
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) hM
  have h2 : a * ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) * ‖s + (k : ℂ)‖ := by
    have := mul_le_mul_of_nonneg_left hlow (by positivity : (0:ℝ) ≤ (k : ℝ) + 1)
    nlinarith [this]
  rw [gaussTerm, norm_div, norm_mul, hk1]
  calc ‖s - 1‖ / (((k : ℝ) + 1) * ‖s + (k : ℂ)‖)
      ≤ M / (((k : ℝ) + 1) * ‖s + (k : ℂ)‖) := by gcongr
    _ ≤ M / (a * ((k : ℝ) + 1) ^ 2) := by gcongr

theorem summable_inv_sq_shift (a M : ℝ) (ha : 0 < a) :
    Summable fun k : ℕ => M / (a * ((k : ℝ) + 1) ^ 2) := by
  have h : Summable fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by
    simpa using (summable_nat_add_iff 1).2 ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two)
  have := h.mul_left (M / a)
  refine this.congr fun k => ?_
  field_simp

/-- The Gauss series is summable at every point of the right half-plane. -/
theorem summable_gaussTerm {s : ℂ} (hs : 0 < s.re) : Summable (gaussTerm s) := by
  set a : ℝ := min s.re 1 with ha_def
  have ha : 0 < a := lt_min hs one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have hsa : a ≤ s.re := min_le_left _ _
  refine Summable.of_norm_bounded (summable_inv_sq_shift a ‖s - 1‖ ha) fun k => ?_
  exact norm_gaussTerm_le ha ha1 hsa le_rfl k

/-- **The Euler–Gauss function**: the Gauss series against `−γ`. -/
def gaussFun (s : ℂ) : ℂ := -(Real.eulerMascheroniConstant : ℂ) + ∑' k : ℕ, gaussTerm s k

/-! ### The Euler–Gauss sequence converges to it -/

theorem sum_inv_natCast_add_one (n : ℕ) :
    ∑ k ∈ Finset.range n, ((k : ℂ) + 1)⁻¹ = ((harmonic n : ℚ) : ℂ) := by
  rw [harmonic]
  push_cast
  rfl

/-- **The Euler–Gauss limit exists**, and is `gaussFun`. -/
theorem tendsto_gaussFun {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => (Real.log n : ℂ) - ∑ k ∈ Finset.range n, (s + (k : ℂ))⁻¹)
      atTop (𝓝 (gaussFun s)) := by
  have hharm : Tendsto
      (fun n : ℕ => ((Real.log n : ℂ) - ∑ k ∈ Finset.range n, ((k : ℂ) + 1)⁻¹))
      atTop (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    have h := Real.tendsto_harmonic_sub_log.neg
    have hc : Tendsto (fun n : ℕ => ((-((harmonic n : ℝ) - Real.log n) : ℝ) : ℂ)) atTop
        (𝓝 ((-Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp h
    rw [show (-(Real.eulerMascheroniConstant : ℂ))
        = (((-Real.eulerMascheroniConstant : ℝ) : ℂ)) by push_cast; ring]
    refine hc.congr fun n => ?_
    rw [sum_inv_natCast_add_one]
    push_cast
    ring
  have hser : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, gaussTerm s k) atTop
      (𝓝 (∑' k : ℕ, gaussTerm s k)) := (summable_gaussTerm hs).hasSum.tendsto_sum_nat
  have := hharm.add hser
  refine this.congr fun n => ?_
  rw [← partial_eq hs n]

/-! ### `gaussFun` is holomorphic on the right half-plane -/

theorem differentiableOn_gaussTerm (k : ℕ) {U : Set ℂ} (hU : U ⊆ rightHalf) :
    DifferentiableOn ℂ (fun s => gaussTerm s k) U := by
  intro s hs
  have hne : s + (k : ℂ) ≠ 0 := add_natCast_ne_zero (hU hs) k
  have hk1 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hden : ((k : ℂ) + 1) * (s + (k : ℂ)) ≠ 0 := mul_ne_zero hk1 hne
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold gaussTerm
  have h1 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s := (differentiableAt_id.sub_const 1)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => ((k : ℂ) + 1) * (s + (k : ℂ))) s :=
    (differentiableAt_id.add_const _).const_mul _
  exact h1.div h2 hden

theorem differentiableAt_gaussFun {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ gaussFun z := by
  have hr : 0 < z.re / 2 := by positivity
  have hUopen : IsOpen (Metric.ball z (z.re / 2)) := Metric.isOpen_ball
  have hre_of_mem : ∀ w ∈ Metric.ball z (z.re / 2), z.re / 2 ≤ w.re := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    have h2 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have h3 := abs_lt.mp (lt_of_le_of_lt h2 hw)
    simp only [Complex.sub_re] at h3
    linarith [h3.1]
  have hUsub : Metric.ball z (z.re / 2) ⊆ rightHalf := by
    intro w hw
    exact lt_of_lt_of_le hr (hre_of_mem w hw)
  have ha : 0 < min (z.re / 2) 1 := lt_min hr one_pos
  have ha1 : min (z.re / 2) 1 ≤ 1 := min_le_right _ _
  have hbound : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball z (z.re / 2) →
      ‖gaussTerm w k‖ ≤ (‖z - 1‖ + z.re / 2) / (min (z.re / 2) 1 * ((k : ℝ) + 1) ^ 2) := by
    intro k w hw
    have hwre : min (z.re / 2) 1 ≤ w.re := le_trans (min_le_left _ _) (hre_of_mem w hw)
    have hd : ‖w - z‖ < z.re / 2 := by rwa [Metric.mem_ball, Complex.dist_eq] at hw
    have hwM : ‖w - 1‖ ≤ ‖z - 1‖ + z.re / 2 := by
      have hsplit : w - 1 = (w - z) + (z - 1) := by ring
      calc ‖w - 1‖ = ‖(w - z) + (z - 1)‖ := by rw [hsplit]
        _ ≤ ‖w - z‖ + ‖z - 1‖ := norm_add_le _ _
        _ ≤ ‖z - 1‖ + z.re / 2 := by linarith
    exact norm_gaussTerm_le ha ha1 hwre hwM k
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' k : ℕ, gaussTerm w k)
      (Metric.ball z (z.re / 2)) :=
    differentiableOn_tsum_of_summable_norm
      (summable_inv_sq_shift (min (z.re / 2) 1) (‖z - 1‖ + z.re / 2) ha)
      (fun k => differentiableOn_gaussTerm k hUsub) hUopen hbound
  have hz' : z ∈ Metric.ball z (z.re / 2) := Metric.mem_ball_self hr
  have hda : DifferentiableAt ℂ (fun w : ℂ => ∑' k : ℕ, gaussTerm w k) z :=
    (hdiff z hz').differentiableAt (hUopen.mem_nhds hz')
  have : DifferentiableAt ℂ (fun w : ℂ => -(Real.eulerMascheroniConstant : ℂ)
      + ∑' k : ℕ, gaussTerm w k) z := hda.const_add _
  exact this

theorem differentiableOn_gaussFun : DifferentiableOn ℂ gaussFun rightHalf :=
  fun _ hz => (differentiableAt_gaussFun hz).differentiableWithinAt

/-! ### The recurrence, and the values at the naturals -/

theorem tendsto_inv_add_natCast (s : ℂ) :
    Tendsto (fun n : ℕ => (s + (n : ℂ))⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  refine Filter.Tendsto.inv_tendsto_atTop ?_
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_atTop_add_const_left _ (-‖s‖)
    (tendsto_natCast_atTop_atTop (R := ℝ)))
  have : ‖(n : ℂ)‖ - ‖s‖ ≤ ‖s + (n : ℂ)‖ := by
    have := norm_sub_norm_le ((n : ℂ)) (-s)
    simpa [sub_neg_eq_add, add_comm] using this
  simp only [Complex.norm_natCast] at this
  change -‖s‖ + (n : ℝ) ≤ ‖s + (n : ℂ)‖
  linarith [this]

/-- **The recurrence.**  The same one `ψ` satisfies. -/
theorem gaussFun_add_one {s : ℂ} (hs : 0 < s.re) :
    gaussFun (s + 1) = gaussFun s + s⁻¹ := by
  have hs1 : 0 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hsplit : ∀ n : ℕ, (Real.log n : ℂ) - ∑ k ∈ Finset.range n, (s + 1 + (k : ℂ))⁻¹
      = ((Real.log n : ℂ) - ∑ k ∈ Finset.range n, (s + (k : ℂ))⁻¹) + s⁻¹ - (s + (n : ℂ))⁻¹ := by
    intro n
    have hshift : ∑ k ∈ Finset.range n, (s + 1 + (k : ℂ))⁻¹
        = ∑ k ∈ Finset.range n, (s + (k : ℂ))⁻¹ + (s + (n : ℂ))⁻¹ - (s + (0 : ℕ))⁻¹ := by
      have h := Finset.sum_range_succ' (fun k : ℕ => (s + (k : ℂ))⁻¹) n
      have h2 := Finset.sum_range_succ (fun k : ℕ => (s + (k : ℂ))⁻¹) n
      have hcongr : ∑ k ∈ Finset.range n, (s + 1 + (k : ℂ))⁻¹
          = ∑ k ∈ Finset.range n, (s + ((k + 1 : ℕ) : ℂ))⁻¹ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        ring_nf
      rw [hcongr]
      rw [h] at h2
      linear_combination h2
    rw [hshift]
    push_cast
    ring
  have hlim : Tendsto (fun n : ℕ => (Real.log n : ℂ) - ∑ k ∈ Finset.range n, (s + 1 + (k : ℂ))⁻¹)
      atTop (𝓝 (gaussFun s + s⁻¹)) := by
    have := ((tendsto_gaussFun hs).add_const s⁻¹).sub (tendsto_inv_add_natCast s)
    simp only [sub_zero] at this
    refine this.congr fun n => ?_
    rw [hsplit n]
  have hlim2 := tendsto_gaussFun hs1
  have hcongr : ∀ n : ℕ, (Real.log n : ℂ) - ∑ k ∈ Finset.range n, (s + 1 + (k : ℂ))⁻¹
      = (Real.log n : ℂ) - ∑ k ∈ Finset.range n, (s + 1 + (k : ℂ))⁻¹ := fun _ => rfl
  exact tendsto_nhds_unique hlim2 hlim

theorem gaussFun_one : gaussFun 1 = -(Real.eulerMascheroniConstant : ℂ) := by
  have : ∀ k : ℕ, gaussTerm 1 k = 0 := by
    intro k
    simp [gaussTerm]
  simp [gaussFun, this]

/-- **The value at `n + 1`** — the same as `ψ`'s. -/
theorem gaussFun_natCast_add_one (n : ℕ) :
    gaussFun ((n : ℂ) + 1) = -(Real.eulerMascheroniConstant : ℂ) + (harmonic n : ℂ) := by
  induction n with
  | zero => simpa using gaussFun_one
  | succ m ih =>
    have hre : 0 < ((m : ℂ) + 1).re := by
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
      positivity
    have h := gaussFun_add_one hre
    rw [show ((m : ℂ) + 1 + 1) = (((m + 1 : ℕ) : ℂ) + 1) by push_cast; ring] at h
    rw [h, ih, harmonic_succ]
    push_cast
    ring

/-! ### `digamma` at a real point is the real logarithmic derivative -/

theorem gamma_deriv_real {x : ℝ} (hx : 0 < x) :
    deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hne : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℕ) := by
    intro m hc
    have : x = -(m : ℝ) := by exact_mod_cast congrArg Complex.re hc
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hdiff : DifferentiableAt ℂ Complex.Gamma (x : ℂ) := Complex.differentiableAt_Gamma _ hne
  have hderiv : HasDerivAt Complex.Gamma (deriv Complex.Gamma (x : ℂ)) (x : ℂ) := hdiff.hasDerivAt
  have hre := hderiv.real_of_complex
  have him : HasDerivAt (fun t : ℝ => ((-Complex.I) * Complex.Gamma (t : ℂ)).re)
      ((-Complex.I * deriv Complex.Gamma (x : ℂ)).re) x :=
    (hderiv.const_mul (-Complex.I)).real_of_complex
  have hzero : (fun t : ℝ => ((-Complex.I) * Complex.Gamma (t : ℂ)).re) = fun _ => (0 : ℝ) := by
    funext t
    rw [Complex.Gamma_ofReal]
    simp
  rw [hzero] at him
  have himval : (deriv Complex.Gamma (x : ℂ)).im = 0 := by
    have h0 := ((hasDerivAt_const x (0 : ℝ)).unique him).symm
    simpa using h0
  have hreval : deriv Real.Gamma x = (deriv Complex.Gamma (x : ℂ)).re := by
    have hEq : (fun t : ℝ => (Complex.Gamma (t : ℂ)).re) = Real.Gamma := by
      funext t
      rw [Complex.Gamma_ofReal]
      simp
    rw [hEq] at hre
    exact hre.deriv
  apply Complex.ext <;> simp [hreval, himval]

/-- **`ψ` at a positive real point is real**, and is the real logarithmic derivative. -/
theorem digamma_ofReal {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((logDeriv Real.Gamma x : ℝ) : ℂ) := by
  have hG : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  rw [Complex.digamma_def, logDeriv_apply, gamma_deriv_real hx, Complex.Gamma_ofReal,
    logDeriv_apply]
  push_cast
  ring

/-! ### Both functions are monotone along the positive reals -/

theorem gaussFun_re_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (gaussFun (x : ℂ)).re ≤ (gaussFun (y : ℂ)).re := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hxc : 0 < ((x : ℂ)).re := by simpa using hx
  have hyc : 0 < ((y : ℂ)).re := by simpa using hy
  have hlim : Tendsto (fun n : ℕ => (((Real.log n : ℂ)
        - ∑ k ∈ Finset.range n, ((y : ℂ) + (k : ℂ))⁻¹)
      - ((Real.log n : ℂ) - ∑ k ∈ Finset.range n, ((x : ℂ) + (k : ℂ))⁻¹)).re) atTop
      (𝓝 ((gaussFun (y : ℂ) - gaussFun (x : ℂ)).re)) :=
    (Complex.continuous_re.tendsto _).comp ((tendsto_gaussFun hyc).sub (tendsto_gaussFun hxc))
  have hnn : 0 ≤ (gaussFun (y : ℂ) - gaussFun (x : ℂ)).re := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
    filter_upwards with n
    have hterm : ∀ k ∈ Finset.range n,
      (0 : ℝ) ≤ (((x : ℂ) + (k : ℂ))⁻¹ - ((y : ℂ) + (k : ℂ))⁻¹).re := by
      intro k _
      have hxk : (0 : ℝ) < x + k := by positivity
      have hyk : (0 : ℝ) < y + k := by positivity
      have h1 : ((x : ℂ) + (k : ℂ))⁻¹ = (((x + k : ℝ))⁻¹ : ℝ) := by push_cast; ring
      have h2 : ((y : ℂ) + (k : ℂ))⁻¹ = (((y + k : ℝ))⁻¹ : ℝ) := by push_cast; ring
      rw [h1, h2]
      simp only [← Complex.ofReal_sub, Complex.ofReal_re, sub_nonneg]
      have := one_div_le_one_div_of_le hxk (by linarith : x + (k:ℝ) ≤ y + (k:ℝ))
      simpa [one_div] using this
    have : (((Real.log n : ℂ) - ∑ k ∈ Finset.range n, ((y : ℂ) + (k : ℂ))⁻¹)
        - ((Real.log n : ℂ) - ∑ k ∈ Finset.range n, ((x : ℂ) + (k : ℂ))⁻¹)).re
        = ∑ k ∈ Finset.range n, (((x : ℂ) + (k : ℂ))⁻¹ - ((y : ℂ) + (k : ℂ))⁻¹).re := by
      rw [← Complex.re_sum]
      congr 1
      rw [Finset.sum_sub_distrib]
      ring
    rw [this]
    exact Finset.sum_nonneg hterm
  rw [Complex.sub_re] at hnn
  linarith

theorem digamma_re_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (Complex.digamma (x : ℂ)).re ≤ (Complex.digamma (y : ℂ)).re := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [digamma_ofReal hx, digamma_ofReal hy, Complex.ofReal_re, Complex.ofReal_re]
  exact Real.monotoneOn_logDeriv_Gamma (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) hxy

/-! ### Both are real on the reals, and both satisfy the same iterated recurrence -/

theorem gaussFun_im_eq_zero {x : ℝ} (hx : 0 < x) : (gaussFun (x : ℂ)).im = 0 := by
  have hxc : 0 < ((x : ℂ)).re := by simpa using hx
  have hlim : Tendsto (fun n : ℕ => ((Real.log n : ℂ)
      - ∑ k ∈ Finset.range n, ((x : ℂ) + (k : ℂ))⁻¹).im) atTop (𝓝 (gaussFun (x : ℂ)).im) :=
    (Complex.continuous_im.tendsto _).comp (tendsto_gaussFun hxc)
  have hzero : ∀ n : ℕ, ((Real.log n : ℂ)
      - ∑ k ∈ Finset.range n, ((x : ℂ) + (k : ℂ))⁻¹).im = 0 := by
    intro n
    have hsum : ∑ k ∈ Finset.range n, ((x : ℂ) + (k : ℂ))⁻¹
        = ((∑ k ∈ Finset.range n, ((x + k : ℝ))⁻¹ : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [hsum, ← Complex.ofReal_sub]
    exact Complex.ofReal_im _
  exact tendsto_nhds_unique (hlim.congr hzero) tendsto_const_nhds

theorem gaussFun_add_natCast {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    gaussFun (s + (n : ℂ)) = gaussFun s + ∑ k ∈ Finset.range n, (s + (k : ℂ))⁻¹ := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hm : 0 < (s + (m : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have h := gaussFun_add_one hm
    rw [show (s + ((m + 1 : ℕ) : ℂ)) = (s + (m : ℂ)) + 1 by push_cast; ring, h, ih,
      Finset.sum_range_succ]
    ring

theorem digamma_add_natCast {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Complex.digamma (s + (n : ℂ))
      = Complex.digamma s + ∑ k ∈ Finset.range n, (s + (k : ℂ))⁻¹ := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hm : 0 < (s + (m : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hne : ∀ j : ℕ, (s + (m : ℂ)) ≠ -(j : ℕ) := by
      intro j hc
      have : (s + (m : ℂ)).re = -(j : ℝ) := by rw [hc]; simp
      nlinarith [Nat.cast_nonneg (α := ℝ) j, this, hm]
    have h := Complex.digamma_apply_add_one (s + (m : ℂ)) hne
    rw [show (s + ((m + 1 : ℕ) : ℂ)) = (s + (m : ℂ)) + 1 by push_cast; ring, h, ih,
      Finset.sum_range_succ]
    ring

/-! ### They agree, first on the reals and then everywhere -/

theorem re_val (n : ℕ) :
    (gaussFun ((n : ℂ) + 1)).re = -Real.eulerMascheroniConstant + (harmonic n : ℝ)
      ∧ (Complex.digamma ((n : ℂ) + 1)).re
        = -Real.eulerMascheroniConstant + (harmonic n : ℝ) := by
  constructor
  · rw [gaussFun_natCast_add_one n]; simp
  · rw [Complex.digamma_natCast_add_one n]; simp

theorem re_eq_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    (gaussFun (x : ℂ)).re = (Complex.digamma (x : ℂ)).re := by
  have hx : (0:ℝ) < x := by linarith
  have hxc : 0 < ((x : ℂ)).re := by simpa using hx
  have key : ∀ n : ℕ, |(gaussFun (x : ℂ)).re - (Complex.digamma (x : ℂ)).re|
      ≤ (harmonic (n + 1) : ℝ) - (harmonic n : ℝ) := by
    intro n
    have hn0 : (0:ℝ) < 1 + n := by positivity
    have hgs := gaussFun_add_natCast hxc n
    have hps := digamma_add_natCast hxc n
    have hshift : (gaussFun ((x : ℂ) + (n : ℂ))).re
        - (Complex.digamma ((x : ℂ) + (n : ℂ))).re
        = (gaussFun (x : ℂ)).re - (Complex.digamma (x : ℂ)).re := by
      rw [hgs, hps, Complex.add_re, Complex.add_re]
      ring
    have hcast : ((x : ℂ) + (n : ℂ)) = (((x + n : ℝ)) : ℂ) := by push_cast; ring
    have hc1 : (((1 + n : ℝ)) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
    have hc2 : (((2 + n : ℝ)) : ℂ) = ((n + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
    obtain ⟨hgv, hpv⟩ := re_val n
    obtain ⟨hgv', hpv'⟩ := re_val (n + 1)
    have hgl : -Real.eulerMascheroniConstant + (harmonic n : ℝ)
        ≤ (gaussFun (((x + n : ℝ)) : ℂ)).re := by
      have := gaussFun_re_mono hn0 (by linarith : (1 : ℝ) + n ≤ x + n)
      rwa [hc1, hgv] at this
    have hgu : (gaussFun (((x + n : ℝ)) : ℂ)).re
        ≤ -Real.eulerMascheroniConstant + (harmonic (n + 1) : ℝ) := by
      have := gaussFun_re_mono (by positivity : (0:ℝ) < x + n)
        (by linarith : x + (n:ℝ) ≤ 2 + n)
      rwa [hc2, hgv'] at this
    have hpl : -Real.eulerMascheroniConstant + (harmonic n : ℝ)
        ≤ (Complex.digamma (((x + n : ℝ)) : ℂ)).re := by
      have := digamma_re_mono hn0 (by linarith : (1 : ℝ) + n ≤ x + n)
      rwa [hc1, hpv] at this
    have hpu : (Complex.digamma (((x + n : ℝ)) : ℂ)).re
        ≤ -Real.eulerMascheroniConstant + (harmonic (n + 1) : ℝ) := by
      have := digamma_re_mono (by positivity : (0:ℝ) < x + n)
        (by linarith : x + (n:ℝ) ≤ 2 + n)
      rwa [hc2, hpv'] at this
    rw [← hshift, hcast]
    rw [abs_le]
    constructor <;> linarith
  have hlim : Tendsto (fun n : ℕ => (harmonic (n + 1) : ℝ) - (harmonic n : ℝ)) atTop (𝓝 0) := by
    have : ∀ n : ℕ, (harmonic (n + 1) : ℝ) - (harmonic n : ℝ) = 1 / ((n : ℝ) + 1) := by
      intro n
      rw [harmonic_succ]
      push_cast
      ring
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h0.congr fun n => (this n).symm
  have : |(gaussFun (x : ℂ)).re - (Complex.digamma (x : ℂ)).re| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall key)
  have := abs_nonpos_iff.mp this
  linarith

theorem eq_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    gaussFun (x : ℂ) = Complex.digamma (x : ℂ) := by
  have hx : (0:ℝ) < x := by linarith
  refine Complex.ext (re_eq_of_mem_Icc h1 h2) ?_
  rw [gaussFun_im_eq_zero hx, digamma_ofReal hx, Complex.ofReal_im]

/-! ### The identity, and the Euler–Gauss limit -/

theorem ne_neg_natCast_of_mem {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -(m : ℕ) := by
  intro m hc
  have : z.re = -(m : ℝ) := by rw [hc]; simp
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem analyticOnNhd_gaussFun : AnalyticOnNhd ℂ gaussFun rightHalf :=
  differentiableOn_gaussFun.analyticOnNhd isOpen_rightHalf

theorem analyticOnNhd_digamma : AnalyticOnNhd ℂ Complex.digamma rightHalf := by
  have hG : DifferentiableOn ℂ Complex.Gamma rightHalf := fun z hz =>
    (Complex.differentiableAt_Gamma _ (ne_neg_natCast_of_mem hz)).differentiableWithinAt
  have hA : AnalyticOnNhd ℂ Complex.Gamma rightHalf := hG.analyticOnNhd isOpen_rightHalf
  have hA' : AnalyticOnNhd ℂ (deriv Complex.Gamma) rightHalf := hA.deriv
  have hEq : Complex.digamma = fun z => deriv Complex.Gamma z / Complex.Gamma z := by
    funext z
    rw [Complex.digamma_def, logDeriv_apply]
  rw [hEq]
  exact hA'.div hA fun z hz => Complex.Gamma_ne_zero (ne_neg_natCast_of_mem hz)

theorem isPreconnected_rightHalf : IsPreconnected rightHalf :=
  (convex_halfSpace_re_gt 0).isPreconnected

/-- **The Gauss series is the digamma function** on the right half-plane. -/
theorem gaussFun_eq_digamma {s : ℂ} (hs : 0 < s.re) : gaussFun s = Complex.digamma s := by
  have h1 : (1 : ℂ) ∈ rightHalf := by
    show (0:ℝ) < (1 : ℂ).re
    simp
  have hten : Tendsto (fun j : ℕ => (((1 + 1 / ((j : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun j : ℕ => (((1 + 1 / ((j : ℝ) + 1)) : ℝ) : ℂ)) ?_ ?_
    · have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hr : Tendsto (fun j : ℕ => (1 : ℝ) + 1 / ((j : ℝ) + 1)) atTop (𝓝 ((1 : ℝ) + 0)) :=
        tendsto_const_nhds.add h0
      have hc := (Complex.continuous_ofReal.tendsto ((1 : ℝ) + 0)).comp hr
      have hc' : Tendsto (fun j : ℕ => (((1 + 1 / ((j : ℝ) + 1)) : ℝ) : ℂ)) atTop
          (𝓝 ((((1 : ℝ) + 0 : ℝ)) : ℂ)) := hc
      simpa using hc'
    · filter_upwards with j
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      have : (1 : ℝ) + 1 / ((j : ℝ) + 1) = 1 := by exact_mod_cast congrArg Complex.re hc
      have hj : (0:ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), gaussFun z = Complex.digamma z := by
    refine hten.frequently (Filter.Eventually.frequently ?_)
    filter_upwards with j
    have hj : (0:ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hle : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      simp only [le_add_iff_nonneg_left]
      positivity
    exact eq_of_mem_Icc (by linarith) (by linarith)
  exact analyticOnNhd_gaussFun.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_digamma
    isPreconnected_rightHalf h1 hfreq hs

/-- **The Euler–Gauss limit**, with no hypothesis. -/
theorem tendsto_digamma {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => (Real.log n : ℂ) - ∑ k ∈ Finset.range n, (s + (k : ℂ))⁻¹) atTop
      (𝓝 (Complex.digamma s)) := by
  rw [← gaussFun_eq_digamma hs]
  exact tendsto_gaussFun hs

/-- The real-part form. -/
theorem tendsto_re_digamma {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => Real.log n - ∑ k ∈ Finset.range n, (s + (k : ℂ))⁻¹.re) atTop
      (𝓝 (Complex.digamma s).re) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_digamma hs)
  refine h.congr fun n => ?_
  rw [Function.comp_apply, Complex.sub_re, Complex.re_sum, Complex.ofReal_re]

end Cvs.Upstream.GammaEulerLimit
