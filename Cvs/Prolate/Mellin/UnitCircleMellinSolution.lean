import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The unit-circle Mellin transform of a solution of the prolate equation

With `Φ₀ = H(z)`, `Φ₁ = zH′`, `Φ₂ = z²H″` at `z = e^{−is}` and `L[f](p) = ∫_0^∞ f e^{−ips}`, `Im p < 0`, the
equation `(1 − z²)H″ − 2zH′ + (χ − Cz²)H = 0` and `L[f′] = −f(0) + ipL[f]` give, for `M = iL[Φ₀]`,
`(p − 1)(p − 2)M(p − 2) = (p(p − 1) − χ)M(p) + CM(p + 2)` with no boundary term.
-/

noncomputable section

open Real Set MeasureTheory Complex Filter Topology

namespace Cvs.Prolate.Mellin.UnitCircleMellinSolution

/-- The unit-circle point `e^{−is}`. -/
def zc (s : ℝ) : ℂ := Complex.exp (-(s * I))

/-- `|e^{−is}| = 1`. -/
theorem norm_zc (s : ℝ) : ‖zc s‖ = 1 := by
  unfold zc; rw [Complex.norm_exp]; simp

theorem zc_zero : zc 0 = 1 := by simp [zc]

theorem continuous_zc : Continuous zc := by unfold zc; fun_prop

theorem hasDerivAt_zc (s : ℝ) : HasDerivAt zc (-I * zc s) s := by
  unfold zc
  have h : HasDerivAt (fun t : ℝ => -((t : ℂ) * I)) (-((1 : ℂ) * I)) s :=
    ((hasDerivAt_id s).ofReal_comp.mul_const I).neg
  convert h.cexp using 1
  ring

/-- `Φ₀(s) = H(e^{−is})`. -/
def Φ0 (H : ℂ → ℂ) (s : ℝ) : ℂ := H (zc s)

/-- `Φ₁(s) = zH′(z)` at `z = e^{−is}`. -/
def Φ1 (H : ℂ → ℂ) (s : ℝ) : ℂ := zc s * deriv H (zc s)

/-- `Φ₂(s) = z²H″(z)` at `z = e^{−is}`. -/
def Φ2 (H : ℂ → ℂ) (s : ℝ) : ℂ := zc s ^ 2 * deriv (deriv H) (zc s)

/-- The one-sided transform `L[f](p) = ∫_0^∞ f(s)e^{−ips} ds`. -/
def lap (f : ℝ → ℂ) (p : ℂ) : ℂ := ∫ s in Ioi (0 : ℝ), f s * Complex.exp (-(I * p * s))

/-- **The unit-circle Mellin transform** `M(p) = i∫_0^∞ H(e^{−is})e^{−ips} ds`. -/
def circM (H : ℂ → ℂ) (p : ℂ) : ℂ := I * lap (Φ0 H) p

section entire

variable {H : ℂ → ℂ}

theorem deriv_differentiable (hH : Differentiable ℂ H) : Differentiable ℂ (deriv H) := fun w =>
  ((hH.differentiableOn.deriv isOpen_univ) w (mem_univ w)).differentiableAt (isOpen_univ.mem_nhds (mem_univ w))

theorem hasDerivAt_Φ0 (hH : Differentiable ℂ H) (s : ℝ) : HasDerivAt (Φ0 H) (-I * Φ1 H s) s := by
  have h := (hH (zc s)).hasDerivAt.comp s (hasDerivAt_zc s)
  exact h.congr_deriv (by unfold Φ1; ring)

theorem hasDerivAt_Φ1 (hH : Differentiable ℂ H) (s : ℝ) :
    HasDerivAt (Φ1 H) (-I * (Φ1 H s + Φ2 H s)) s := by
  have h2 := ((deriv_differentiable hH) (zc s)).hasDerivAt.comp s (hasDerivAt_zc s)
  have h := (hasDerivAt_zc s).mul h2
  exact h.congr_deriv (by unfold Φ1 Φ2; simp only [Function.comp_apply]; ring)

theorem continuous_Φ0 (hH : Differentiable ℂ H) : Continuous (Φ0 H) := hH.continuous.comp continuous_zc

theorem continuous_Φ1 (hH : Differentiable ℂ H) : Continuous (Φ1 H) :=
  continuous_zc.mul ((deriv_differentiable hH).continuous.comp continuous_zc)

theorem continuous_Φ2 (hH : Differentiable ℂ H) : Continuous (Φ2 H) :=
  (continuous_zc.pow 2).mul ((deriv_differentiable (deriv_differentiable hH)).continuous.comp continuous_zc)

/-- A continuous function is bounded on the unit circle `{e^{−is}}`. -/
theorem exists_bound_circle {F : ℂ → ℂ} (hF : Continuous F) : ∃ M, ∀ s : ℝ, ‖F (zc s)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hF.continuousOn
  exact ⟨M, fun s => hM _ (by simp [norm_zc])⟩

theorem exists_bound_Φ0 (hH : Differentiable ℂ H) : ∃ M, ∀ s, ‖Φ0 H s‖ ≤ M := exists_bound_circle hH.continuous

theorem exists_bound_Φ1 (hH : Differentiable ℂ H) : ∃ M, ∀ s, ‖Φ1 H s‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_circle (deriv_differentiable hH).continuous
  exact ⟨M, fun s => by unfold Φ1; rw [norm_mul, norm_zc, one_mul]; exact hM s⟩

theorem exists_bound_Φ2 (hH : Differentiable ℂ H) : ∃ M, ∀ s, ‖Φ2 H s‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_circle (deriv_differentiable (deriv_differentiable hH)).continuous
  exact ⟨M, fun s => by unfold Φ2; rw [norm_mul, norm_pow, norm_zc, one_pow, one_mul]; exact hM s⟩

end entire

/-! ### The one-sided transform -/

/-- `|e^{−ips}| = e^{s Im p}`. -/
theorem norm_kernel (p : ℂ) (s : ℝ) : ‖Complex.exp (-(I * p * s))‖ = Real.exp (p.im * s) := by
  rw [Complex.norm_exp]; congr 1; simp

theorem kernel_eq (p : ℂ) (s : ℝ) : Complex.exp (-(I * p * s)) = Complex.exp ((-I * p) * s) := by
  congr 1; ring

theorem integrableOn_kernel_mul {f : ℝ → ℂ} (hf : Continuous f) {M : ℝ} (hM : ∀ s, ‖f s‖ ≤ M) {p : ℂ}
    (hp : p.im < 0) : IntegrableOn (fun s => f s * Complex.exp (-(I * p * s))) (Ioi 0) := by
  have hexp : IntegrableOn (fun s : ℝ => M * Real.exp (p.im * s)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi hp 0).const_mul M
  refine hexp.mono' ((hf.mul (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun s => ?_)
  rw [norm_mul, norm_kernel]
  exact mul_le_mul_of_nonneg_right (hM s) (Real.exp_pos _).le

/-- `‖L[f](p)‖ ≤ M/(−Im p)` for `‖f‖ ≤ M`. -/
theorem norm_lap_le {f : ℝ → ℂ} {M : ℝ} (hM : ∀ s, ‖f s‖ ≤ M) {p : ℂ} (hp : p.im < 0) :
    ‖lap f p‖ ≤ M / (-p.im) := by
  have hexp : IntegrableOn (fun s : ℝ => M * Real.exp (p.im * s)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi hp 0).const_mul M
  unfold lap
  refine (norm_integral_le_of_norm_le hexp (Eventually.of_forall fun s => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, norm_kernel]
    exact mul_le_mul_of_nonneg_right (hM s) (Real.exp_pos _).le
  · rw [integral_const_mul, integral_exp_mul_Ioi hp 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp

/-- **Integration by parts**: `L[f′](p) = −f(0) + ipL[f](p)` for bounded continuous `f, f′`, `Im p < 0`. -/
theorem lap_deriv {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s) (hf'c : Continuous f') {M M' : ℝ}
    (hM : ∀ s, ‖f s‖ ≤ M) (hM' : ∀ s, ‖f' s‖ ≤ M') {p : ℂ} (hp : p.im < 0) :
    lap f' p = -f 0 + I * p * lap f p := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun s => (hf s).continuousAt
  set v : ℝ → ℂ := fun s => Complex.exp (-(I * p * s)) with hvd
  have hv : ∀ s, HasDerivAt v (-(I * p) * v s) s := fun s => by
    have h : HasDerivAt (fun t : ℝ => -(I * p * (t : ℂ))) (-(I * p * 1)) s :=
      ((hasDerivAt_id s).ofReal_comp.const_mul (I * p)).neg
    convert h.cexp using 1
    simp only [hvd]; ring
  have i1 := integrableOn_kernel_mul hfc hM hp
  have i2 := integrableOn_kernel_mul hf'c hM' hp
  have huv' : IntegrableOn (f * fun s => -(I * p) * v s) (Ioi 0) := by
    have : IntegrableOn (fun s => -(I * p) * (f s * Complex.exp (-(I * p * s)))) (Ioi 0) := i1.const_mul _
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, hvd]; ring
  have hu'v : IntegrableOn (f' * v) (Ioi 0) := i2
  have h0 : Tendsto (f * v) (𝓝[>] 0) (𝓝 (f 0)) := by
    have hc : Continuous (f * v) := hfc.mul (by simp only [hvd]; fun_prop)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [hvd] using this
  have hinf : Tendsto (f * v) atTop (𝓝 0) := by
    have hexp : Tendsto (fun s : ℝ => M * Real.exp (p.im * s)) atTop (𝓝 (M * 0)) :=
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hp)).const_mul M
    rw [mul_zero] at hexp
    refine squeeze_zero_norm (fun s => ?_) hexp
    simp only [Pi.mul_apply, hvd]
    rw [norm_mul, norm_kernel]
    exact mul_le_mul_of_nonneg_right (hM s) (Real.exp_pos _).le
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (fun s _ => hf s) (fun s _ => hv s) huv' hu'v h0 hinf
  have e1 : ∫ s in Ioi (0 : ℝ), f s * (-(I * p) * v s) = -(I * p) * lap f p := by
    unfold lap
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hvd]; ring
  have e2 : ∫ s in Ioi (0 : ℝ), f' s * v s = lap f' p := rfl
  rw [e1, e2] at key
  linear_combination key

theorem lap_const_mul (a : ℂ) (f : ℝ → ℂ) (p : ℂ) : lap (fun s => a * f s) p = a * lap f p := by
  unfold lap; rw [← integral_const_mul]; congr 1; funext s; ring

theorem lap_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) {M N : ℝ} (hM : ∀ s, ‖f s‖ ≤ M)
    (hN : ∀ s, ‖g s‖ ≤ N) {p : ℂ} (hp : p.im < 0) : lap (fun s => f s + g s) p = lap f p + lap g p := by
  unfold lap
  rw [← integral_add (integrableOn_kernel_mul hf hM hp) (integrableOn_kernel_mul hg hN hp)]
  congr 1; funext s; ring

/-- `L[e^{2is}f](p) = L[f](p − 2)`. -/
theorem lap_shift_down (f : ℝ → ℂ) (p : ℂ) :
    lap (fun s => Complex.exp (2 * (s * I)) * f s) p = lap f (p - 2) := by
  unfold lap; refine congrArg _ (funext fun s => ?_)
  simp only
  rw [show Complex.exp (2 * (s * I)) * f s * Complex.exp (-(I * p * s))
    = f s * (Complex.exp (2 * (s * I)) * Complex.exp (-(I * p * s))) by ring, ← Complex.exp_add]
  congr 2; ring

/-- `L[z²f](p) = L[f](p + 2)` at `z = e^{−is}`. -/
theorem lap_shift_up (f : ℝ → ℂ) (p : ℂ) : lap (fun s => zc s ^ 2 * f s) p = lap f (p + 2) := by
  unfold lap zc; refine congrArg _ (funext fun s => ?_)
  simp only
  rw [← Complex.exp_nat_mul, show Complex.exp (((2 : ℕ) : ℂ) * -(s * I)) * f s * Complex.exp (-(I * p * s))
    = f s * (Complex.exp (((2 : ℕ) : ℂ) * -(s * I)) * Complex.exp (-(I * p * s))) by ring, ← Complex.exp_add]
  congr 2; push_cast; ring

section recurrence

variable {H : ℂ → ℂ}

/-- `−iL[Φ₁](p) = −H(1) + ipL[Φ₀](p)`. -/
theorem lap_rel_one (hH : Differentiable ℂ H) {p : ℂ} (hp : p.im < 0) :
    -I * lap (Φ1 H) p = -Φ0 H 0 + I * p * lap (Φ0 H) p := by
  obtain ⟨M0, hM0⟩ := exists_bound_Φ0 hH
  obtain ⟨M1, hM1⟩ := exists_bound_Φ1 hH
  have h := lap_deriv (hasDerivAt_Φ0 hH) (continuous_const.mul (continuous_Φ1 hH)) hM0
    (fun s => by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]; exact hM1 s) hp
  rw [lap_const_mul] at h
  exact h

/-- `−i(L[Φ₁] + L[Φ₂])(p) = −Φ₁(0) + ipL[Φ₁](p)`. -/
theorem lap_rel_two (hH : Differentiable ℂ H) {p : ℂ} (hp : p.im < 0) :
    -I * (lap (Φ1 H) p + lap (Φ2 H) p) = -Φ1 H 0 + I * p * lap (Φ1 H) p := by
  obtain ⟨M1, hM1⟩ := exists_bound_Φ1 hH
  obtain ⟨M2, hM2⟩ := exists_bound_Φ2 hH
  have h := lap_deriv (hasDerivAt_Φ1 hH) (continuous_const.mul ((continuous_Φ1 hH).add (continuous_Φ2 hH))) hM1
    (fun s => by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      exact (norm_add_le _ _).trans (add_le_add (hM1 s) (hM2 s))) hp
  rw [lap_const_mul, lap_add (continuous_Φ1 hH) (continuous_Φ2 hH) hM1 hM2 hp] at h
  exact h

/-- **The three-term recurrence** for `M = iL[Φ₀]`:
`(p − 1)(p − 2)M(p − 2) = (p(p − 1) − χ)M(p) + CM(p + 2)` for `Im p < 0`. -/
theorem recurrence (hH : Differentiable ℂ H) {χ C : ℂ}
    (hode : ∀ z, (1 - z ^ 2) * deriv (deriv H) z - 2 * z * deriv H z + (χ - C * z ^ 2) * H z = 0)
    {p : ℂ} (hp : p.im < 0) :
    (p - 1) * (p - 2) * circM H (p - 2) = (p * (p - 1) - χ) * circM H p + C * circM H (p + 2) := by
  have hpm : (p - 2).im < 0 := by simpa using hp
  have hpp : (p + 2).im < 0 := by simpa using hp
  obtain ⟨M0, hM0⟩ := exists_bound_Φ0 hH
  obtain ⟨M1, hM1⟩ := exists_bound_Φ1 hH
  obtain ⟨M2, hM2⟩ := exists_bound_Φ2 hH
  have c0 := continuous_Φ0 hH
  have c1 := continuous_Φ1 hH
  have c2 := continuous_Φ2 hH
  -- the equation on the circle
  have hpt : ∀ s : ℝ, Complex.exp (2 * (s * I)) * Φ2 H s - Φ2 H s - 2 * Φ1 H s + χ * Φ0 H s
      - C * (zc s ^ 2 * Φ0 H s) = 0 := fun s => by
    have hw : Complex.exp (2 * (s * I)) * zc s ^ 2 = 1 := by
      unfold zc; rw [← Complex.exp_nat_mul, ← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
    have e := hode (zc s)
    unfold Φ0 Φ1 Φ2
    linear_combination e + (deriv (deriv H) (zc s)) * hw
  -- its transform
  have i2m := integrableOn_kernel_mul c2 hM2 hpm
  have hE3 : lap (Φ2 H) (p - 2) - lap (Φ2 H) p - 2 * lap (Φ1 H) p + χ * lap (Φ0 H) p
      - C * lap (Φ0 H) (p + 2) = 0 := by
    rw [← lap_shift_down, ← lap_shift_up, ← lap_const_mul 2, ← lap_const_mul χ, ← lap_const_mul C]
    have hz : lap (fun s => Complex.exp (2 * (s * I)) * Φ2 H s - Φ2 H s - 2 * Φ1 H s + χ * Φ0 H s
        - C * (zc s ^ 2 * Φ0 H s)) p = 0 := by
      simp only [hpt]; unfold lap; simp
    have iA : IntegrableOn (fun s : ℝ => Complex.exp (2 * ((s : ℂ) * I)) * Φ2 H s * Complex.exp (-(I * p * s)))
        (Ioi 0) :=
      i2m.congr_fun (fun s _ => by
        simp only
        rw [show Complex.exp (2 * ((s : ℂ) * I)) * Φ2 H s * Complex.exp (-(I * p * s))
          = Φ2 H s * (Complex.exp (2 * ((s : ℂ) * I)) * Complex.exp (-(I * p * s))) by ring, ← Complex.exp_add]
        congr 2; ring) measurableSet_Ioi
    have iB := integrableOn_kernel_mul c2 hM2 hp
    have iC : IntegrableOn (fun s : ℝ => 2 * Φ1 H s * Complex.exp (-(I * p * s))) (Ioi 0) := by
      have h : IntegrableOn (fun s : ℝ => 2 * (Φ1 H s * Complex.exp (-(I * p * s)))) (Ioi 0) :=
        (integrableOn_kernel_mul c1 hM1 hp).const_mul 2
      exact h.congr_fun (fun s _ => by ring) measurableSet_Ioi
    have iD : IntegrableOn (fun s : ℝ => χ * Φ0 H s * Complex.exp (-(I * p * s))) (Ioi 0) := by
      have h : IntegrableOn (fun s : ℝ => χ * (Φ0 H s * Complex.exp (-(I * p * s)))) (Ioi 0) :=
        (integrableOn_kernel_mul c0 hM0 hp).const_mul χ
      exact h.congr_fun (fun s _ => by ring) measurableSet_Ioi
    have iE : IntegrableOn (fun s : ℝ => C * (zc s ^ 2 * Φ0 H s) * Complex.exp (-(I * p * s))) (Ioi 0) := by
      have h : IntegrableOn (fun s : ℝ => C * (Φ0 H s * Complex.exp (-(I * (p + 2) * s)))) (Ioi 0) :=
        (integrableOn_kernel_mul c0 hM0 hpp).const_mul C
      refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
      unfold zc
      rw [← Complex.exp_nat_mul, show C * (Complex.exp (((2 : ℕ) : ℂ) * -(s * I)) * Φ0 H s)
        * Complex.exp (-(I * p * s)) = C * (Φ0 H s * (Complex.exp (((2 : ℕ) : ℂ) * -(s * I))
        * Complex.exp (-(I * p * s)))) by ring, ← Complex.exp_add]
      push_cast; ring_nf
    have k1 := integral_sub iA iB
    have k2 := integral_sub (iA.sub iB) iC
    have k3 := integral_add ((iA.sub iB).sub iC) iD
    have k4 := integral_sub (((iA.sub iB).sub iC).add iD) iE
    simp only [Pi.sub_apply, Pi.add_apply] at k1 k2 k3 k4
    have k5 : lap (fun s => Complex.exp (2 * (s * I)) * Φ2 H s - Φ2 H s - 2 * Φ1 H s + χ * Φ0 H s
        - C * (zc s ^ 2 * Φ0 H s)) p = ∫ s in Ioi (0 : ℝ), (Complex.exp (2 * ((s : ℂ) * I)) * Φ2 H s
          * Complex.exp (-(I * p * s)) - Φ2 H s * Complex.exp (-(I * p * s))
          - 2 * Φ1 H s * Complex.exp (-(I * p * s)) + χ * Φ0 H s * Complex.exp (-(I * p * s))
          - C * (zc s ^ 2 * Φ0 H s) * Complex.exp (-(I * p * s))) := by
      unfold lap; congr 1; funext s; ring
    simp only [lap] at hz k5 ⊢
    rw [k5, k4, k3, k2, k1] at hz
    linear_combination hz
  have E1p := lap_rel_one hH hp
  have E1m := lap_rel_one hH hpm
  have E2p := lap_rel_two hH hp
  have E2m := lap_rel_two hH hpm
  unfold circM
  linear_combination I * hE3 + E2m - E2p - (p - 1) * E1m + (p - 1) * E1p

/-- `pM(p) = H(1) − iL[Φ₁](p)`. -/
theorem mul_circM (hH : Differentiable ℂ H) {p : ℂ} (hp : p.im < 0) :
    p * circM H p = H 1 - I * lap (Φ1 H) p := by
  have E1 := lap_rel_one hH hp
  have h0 : Φ0 H 0 = H 1 := by simp [Φ0, zc_zero]
  rw [h0] at E1
  unfold circM
  linear_combination -E1

/-- `(p + 1)L[Φ₁](p) = −iΦ₁(0) − L[Φ₂](p)`. -/
theorem lap_Φ1_eq (hH : Differentiable ℂ H) {p : ℂ} (hp : p.im < 0) :
    (p + 1) * lap (Φ1 H) p = -I * Φ1 H 0 - lap (Φ2 H) p := by
  have E2 := lap_rel_two hH hp
  linear_combination I * E2 + ((p + 1) * lap (Φ1 H) p + lap (Φ2 H) p) * Complex.I_sq

/-- **The edge limit along a horizontal ray**: `(p₀ + 2m)M(p₀ + 2m) → H(1)` for `Im p₀ < 0`. -/
theorem tendsto_mul_circM (hH : Differentiable ℂ H) {p₀ : ℂ} (hp : p₀.im < 0) :
    Tendsto (fun m : ℕ => (p₀ + 2 * m) * circM H (p₀ + 2 * m)) atTop (𝓝 (H 1)) := by
  obtain ⟨M2, hM2⟩ := exists_bound_Φ2 hH
  have him : ∀ m : ℕ, (p₀ + 2 * m).im = p₀.im := fun m => by simp
  set K := ‖Φ1 H 0‖ + M2 / (-p₀.im) with hK
  have hbound : ∀ m : ℕ, 0 < ‖p₀ + 2 * m + 1‖ →
      ‖(p₀ + 2 * m) * circM H (p₀ + 2 * m) - H 1‖ ≤ K / ‖p₀ + 2 * m + 1‖ := fun m hpos => by
    have hpm : (p₀ + 2 * m).im < 0 := by rw [him]; exact hp
    rw [mul_circM hH hpm, show H 1 - I * lap (Φ1 H) (p₀ + 2 * m) - H 1 = -I * lap (Φ1 H) (p₀ + 2 * m) by ring,
      norm_mul, norm_neg, Complex.norm_I, one_mul, le_div_iff₀ hpos, mul_comm, ← norm_mul, lap_Φ1_eq hH hpm]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    have := norm_lap_le hM2 hpm
    rw [him] at this
    linarith
  have hgrow : Tendsto (fun m : ℕ => ‖p₀ + 2 * m + 1‖) atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    have h2 : Tendsto (fun m : ℕ => p₀.re + 2 * (m : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_atTop_add_const_left _ p₀.re h)
    refine tendsto_atTop_mono (fun m => ?_) h2
    have := Complex.re_le_norm (p₀ + 2 * m + 1)
    simpa using this
  have hK0 : Tendsto (fun m : ℕ => K / ‖p₀ + 2 * m + 1‖) atTop (𝓝 0) := hgrow.const_div_atTop K
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK0
  filter_upwards [hgrow.eventually_gt_atTop 0] with m hm
  exact hbound m hm

end recurrence

end Cvs.Prolate.Mellin.UnitCircleMellinSolution

end
