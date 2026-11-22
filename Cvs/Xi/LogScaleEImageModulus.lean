import Mathlib
import Cvs.Prolate.Mellin.TailMellinPlancherel
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `L²` modulus of the log-scale E-image

For `|G| ≤ M`, `G` `L`-Lipschitz on `[0, 1]`, `P(θ) = θE_G(θ)` moves under `θ ↦ θ' ≥ θ` by at most
`L(1 − θ/θ')(θ + a)/2 + aM(⌊θ'/a⌋ − ⌊θ/a⌋)`. With `|P| ≤ K`, `φ(u) = 1_{u>0} e^{σu} E_G(e^u)` has
`‖φ(· + h) − φ‖₂² ≤ (K²(1 + 5/b) + 4K(L + 4M)/(1 − b))·h^b` for `0 ≤ σ ≤ 1 − b`, `0 < a ≤ 1`, `0 < h ≤ ½`.
-/

noncomputable section

open MeasureTheory Set Real Filter
open Cvs.Xi.EImageWindowPoisson (eimage)

namespace Cvs.Xi.LogScaleEImageModulus

variable {a L M : ℝ} {G : ℝ → ℝ}

/-! ### The Riemann sum under a dilation -/

/-- `θE_G(θ) = a Σ_{n < ⌊θ/a⌋} G((n + 1)a/θ)` for `θ ≠ 0`. -/
theorem mul_eimage_eq {θ : ℝ} (hθ : θ ≠ 0) (a : ℝ) (G : ℝ → ℝ) :
    θ * eimage a G θ = a * ∑ n ∈ Finset.range ⌊θ / a⌋₊, G ((n + 1) * a / θ) := by
  rw [Cvs.Xi.EImageMellin.eimage_eq_sum_range, ← mul_assoc, mul_div_cancel₀ _ hθ]

/-- **The dilation step of `θE_G(θ)`**: for `0 < θ ≤ θ'`, with `|G| ≤ M` and `G` `L`-Lipschitz on `[0, 1]`,
`|θ'E(θ') − θE(θ)| ≤ L(1 − θ/θ')(θ + a)/2 + aM(⌊θ'/a⌋ − ⌊θ/a⌋)`. -/
theorem abs_mul_eimage_sub_le (ha : 0 < a) (hL : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |G t - G s| ≤ L * |t - s|)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, |G t| ≤ M) {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') :
    |θ' * eimage a G θ' - θ * eimage a G θ|
      ≤ L * (1 - θ / θ') * (θ + a) / 2 + a * M * ((⌊θ' / a⌋₊ : ℝ) - ⌊θ / a⌋₊) := by
  have hθ' : 0 < θ' := hθ.trans_le hθθ'
  set N := ⌊θ / a⌋₊ with hN
  set N' := ⌊θ' / a⌋₊ with hN'
  have hNN' : N ≤ N' := Nat.floor_le_floor (div_le_div_of_nonneg_right hθθ' ha.le)
  have hNa : (N : ℝ) * a ≤ θ := by
    have := Nat.floor_le (div_nonneg hθ.le ha.le); rw [← hN, le_div_iff₀ ha] at this; exact this
  have hN'a : (N' : ℝ) * a ≤ θ' := by
    have := Nat.floor_le (div_nonneg hθ'.le ha.le); rw [← hN', le_div_iff₀ ha] at this; exact this
  rw [mul_eimage_eq hθ'.ne', mul_eimage_eq hθ.ne', ← hN, ← hN', ← Finset.sum_range_add_sum_Ico _ hNN', mul_add,
    add_sub_right_comm, ← mul_sub, ← Finset.sum_sub_distrib]
  have hL0 : 0 ≤ L := by
    have := hL 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    simp at this; exact (abs_nonneg _).trans this
  -- the moved samples
  have h1 : |a * ∑ n ∈ Finset.range N, (G ((n + 1) * a / θ') - G ((n + 1) * a / θ))|
      ≤ L * (1 - θ / θ') * (θ + a) / 2 := by
    rw [abs_mul, abs_of_pos ha]
    have hterm : ∀ n ∈ Finset.range N, |G ((n + 1) * a / θ') - G ((n + 1) * a / θ)|
        ≤ L * (1 - θ / θ') * a / θ * (n + 1) := fun n hn => by
      have hn' : ((n : ℝ) + 1) ≤ N := by exact_mod_cast Finset.mem_range.1 hn
      have hp : ((n : ℝ) + 1) * a / θ ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, by rw [div_le_one hθ]; nlinarith⟩
      have hp' : ((n : ℝ) + 1) * a / θ' ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, (div_le_div_of_nonneg_left (by positivity) hθ hθθ').trans hp.2⟩
      refine (hL _ hp _ hp').trans (le_of_eq ?_)
      rw [abs_sub_comm, abs_of_nonneg (by rw [sub_nonneg]; exact div_le_div_of_nonneg_left (by positivity) hθ hθθ')]
      field_simp
    calc a * |∑ n ∈ Finset.range N, (G ((n + 1) * a / θ') - G ((n + 1) * a / θ))|
        ≤ a * ∑ n ∈ Finset.range N, L * (1 - θ / θ') * a / θ * (n + 1) :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)) ha.le
      _ = L * (1 - θ / θ') * a ^ 2 / θ * ∑ n ∈ Finset.range N, ((n : ℝ) + 1) := by
          rw [← Finset.mul_sum]; ring
      _ = L * (1 - θ / θ') * a ^ 2 / θ * ((N : ℝ) * (N + 1) / 2) := by
          congr 1
          induction N with
          | zero => simp
          | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
      _ ≤ L * (1 - θ / θ') * (θ + a) / 2 := by
          have hc : 0 ≤ L * (1 - θ / θ') := mul_nonneg hL0 (by rw [sub_nonneg, div_le_one hθ']; exact hθθ')
          have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          have key : a ^ 2 * ((N : ℝ) * (N + 1)) ≤ θ * (θ + a) := by
            have := mul_le_mul hNa (add_le_add_right hNa a) (by positivity) hθ.le
            nlinarith
          rw [show L * (1 - θ / θ') * a ^ 2 / θ * ((N : ℝ) * (N + 1) / 2)
              = L * (1 - θ / θ') * (a ^ 2 * ((N : ℝ) * (N + 1))) / θ / 2 by ring,
            show L * (1 - θ / θ') * (θ + a) / 2 = L * (1 - θ / θ') * (θ * (θ + a)) / θ / 2 by field_simp]
          gcongr
  -- the new samples
  have h2 : |a * ∑ n ∈ Finset.Ico N N', G ((n + 1) * a / θ')| ≤ a * M * ((N' : ℝ) - N) := by
    rw [abs_mul, abs_of_pos ha, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) ha.le
    calc ∑ n ∈ Finset.Ico N N', |G ((n + 1) * a / θ')| ≤ ∑ n ∈ Finset.Ico N N', M :=
          Finset.sum_le_sum fun n hn => hM _ ⟨by positivity, by
            have hn' : ((n : ℝ) + 1) ≤ N' := by exact_mod_cast (Finset.mem_Ico.1 hn).2
            rw [div_le_one hθ']; nlinarith⟩
      _ = M * ((N' : ℝ) - N) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hNN']; ring
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-! ### Exponential and jump-count integrals -/

/-- `e^t ≤ 1 + 2t` on `[0, 1]`. -/
theorem exp_le_one_add_two_mul' {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t ≤ 1 + 2 * t := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (by linarith : (0 : ℝ) ≤ 1 - t) h0
    (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at h
  have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  nlinarith

/-- `∫_α^β e^{cv} dv = (e^{cβ} − e^{cα})/c` for `c ≠ 0`. -/
theorem integral_exp_mul_eq {c : ℝ} (hc : c ≠ 0) (α β : ℝ) :
    ∫ v in α..β, Real.exp (c * v) = (Real.exp (c * β) - Real.exp (c * α)) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun v => Real.exp v) hc, integral_exp, smul_eq_mul]
  field_simp

/-- `∫₀^U e^{(1−b)u} du ≤ e^{(1−b)U}/(1 − b)` for `b < 1`. -/
theorem integral_exp_one_sub_le {b : ℝ} (hb : b < 1) (α U : ℝ) :
    ∫ u in α..U, Real.exp ((1 - b) * u) ≤ Real.exp ((1 - b) * U) / (1 - b) := by
  rw [integral_exp_mul_eq (by linarith : (1 - b) ≠ 0)]
  have : 0 < 1 - b := by linarith
  gcongr
  linarith [Real.exp_pos ((1 - b) * α)]

/-- The jump count `N(v) = ⌊e^v/a⌋₊`. -/
def jumpN (a v : ℝ) : ℝ := (⌊Real.exp v / a⌋₊ : ℝ)

theorem jumpN_nonneg (a v : ℝ) : 0 ≤ jumpN a v := Nat.cast_nonneg _

theorem jumpN_le (ha : 0 < a) (v : ℝ) : jumpN a v ≤ Real.exp v / a :=
  Nat.floor_le (by positivity)

theorem jumpN_mono (ha : 0 < a) : Monotone (jumpN a) := fun _ _ h =>
  Nat.cast_le.2 (Nat.floor_le_floor (div_le_div_of_nonneg_right (Real.exp_le_exp.2 h) ha.le))

theorem intervalIntegrable_exp_mul_jumpN (ha : 0 < a) (c d : ℝ) (α β : ℝ) :
    IntervalIntegrable (fun u => Real.exp (c * u) * jumpN a (u + d)) volume α β :=
  (((jumpN_mono ha).comp (monotone_id.add_const d)).intervalIntegrable).continuousOn_mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn

/-- **The jump-count integral**: for `0 < h ≤ ½ ≤ ...`, `h ≤ U`, `0 < b < 1`,
`∫₀^U e^{−bu}(N(u + h) − N(u)) du ≤ 4h e^{(1−b)U}/(a(1 − b))`. -/
theorem integral_jump_le (ha : 0 < a) {b h U : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hU : h ≤ U) :
    ∫ u in (0 : ℝ)..U, Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u)
      ≤ 4 * h * Real.exp ((1 - b) * U) / (a * (1 - b)) := by
  have h1b : 0 < 1 - b := by linarith
  have hU0 : 0 ≤ U := hh0.le.trans hU
  have iI := fun (c d α β : ℝ) => intervalIntegrable_exp_mul_jumpN ha c d α β
  have e0 : ∀ u, jumpN a (u + 0) = jumpN a u := fun u => by rw [add_zero]
  -- split the difference
  have hsplit : ∫ u in (0 : ℝ)..U, Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u)
      = (∫ u in (0 : ℝ)..U, Real.exp (-b * u) * jumpN a (u + h))
        - ∫ u in (0 : ℝ)..U, Real.exp (-b * u) * jumpN a u := by
    rw [← intervalIntegral.integral_sub (iI _ _ _ _) (by simpa only [e0] using iI (-b) 0 0 U)]
    congr 1; funext u; ring
  -- the shifted integral
  have hshift : ∫ u in (0 : ℝ)..U, Real.exp (-b * u) * jumpN a (u + h)
      = ∫ v in h..U + h, Real.exp (-b * (v - h)) * jumpN a v := by
    have := intervalIntegral.integral_comp_add_right (fun v => Real.exp (-b * (v - h)) * jumpN a v) h
      (a := 0) (b := U)
    simp only [add_sub_cancel_right, zero_add] at this
    exact this
  have iS : ∀ α β : ℝ, IntervalIntegrable (fun v => Real.exp (-b * (v - h)) * jumpN a v) volume α β := fun α β => by
    have := iI (-b) 0 α β
    refine (this.const_mul (Real.exp (b * h))).congr fun v _ => ?_
    simp only [add_zero]
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  have iJ : ∀ α β : ℝ, IntervalIntegrable (fun v => Real.exp (-b * v) * jumpN a v) volume α β := fun α β => by
    simpa only [e0] using iI (-b) 0 α β
  rw [hsplit, hshift, ← intervalIntegral.integral_add_adjacent_intervals (iS h U) (iS U (U + h)),
    ← intervalIntegral.integral_add_adjacent_intervals (iJ 0 h) (iJ h U)]
  have hfirst : (∫ v in h..U, Real.exp (-b * (v - h)) * jumpN a v) - ∫ v in h..U, Real.exp (-b * v) * jumpN a v
      ≤ 2 * h * Real.exp ((1 - b) * U) / (a * (1 - b)) := by
    rw [← intervalIntegral.integral_sub (iS h U) (iJ h U)]
    have hbd : ∀ v ∈ Icc h U, Real.exp (-b * (v - h)) * jumpN a v - Real.exp (-b * v) * jumpN a v
        ≤ 2 * h / a * Real.exp ((1 - b) * v) := fun v hv => by
      have hbh : Real.exp (b * h) - 1 ≤ 2 * h := by
        have := exp_le_one_add_two_mul' (t := b * h) (by positivity) (by nlinarith)
        nlinarith
      have e : Real.exp (-b * (v - h)) * jumpN a v - Real.exp (-b * v) * jumpN a v
          = (Real.exp (b * h) - 1) * (Real.exp (-b * v) * jumpN a v) := by
        rw [show -b * (v - h) = b * h + -b * v by ring, Real.exp_add]; ring
      rw [e]
      have hN := jumpN_le ha v
      have hN0 := jumpN_nonneg a v
      have hpos : 0 ≤ Real.exp (b * h) - 1 := by
        have := Real.one_le_exp (by positivity : 0 ≤ b * h); linarith
      calc (Real.exp (b * h) - 1) * (Real.exp (-b * v) * jumpN a v)
          ≤ (2 * h) * (Real.exp (-b * v) * (Real.exp v / a)) :=
            mul_le_mul hbh (mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le) (by positivity) (by positivity)
        _ = 2 * h / a * Real.exp ((1 - b) * v) := by
            rw [show (1 - b) * v = -b * v + v by ring, Real.exp_add]; field_simp
    calc _ ≤ ∫ v in h..U, 2 * h / a * Real.exp ((1 - b) * v) :=
          intervalIntegral.integral_mono_on hU ((iS h U).sub (iJ h U))
            ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
              |>.const_mul _) hbd
      _ = 2 * h / a * ∫ v in h..U, Real.exp ((1 - b) * v) := intervalIntegral.integral_const_mul _ _
      _ ≤ 2 * h / a * (Real.exp ((1 - b) * U) / (1 - b)) :=
          mul_le_mul_of_nonneg_left (integral_exp_one_sub_le hb1 h U) (by positivity)
      _ = _ := by field_simp
  have hsecond : ∫ v in U..U + h, Real.exp (-b * (v - h)) * jumpN a v ≤ 2 * h * Real.exp ((1 - b) * U) / a := by
    have hbd : ∀ v ∈ Icc U (U + h), Real.exp (-b * (v - h)) * jumpN a v ≤ 2 * Real.exp ((1 - b) * U) / a :=
      fun v hv => by
        have hN := jumpN_le ha v
        calc Real.exp (-b * (v - h)) * jumpN a v ≤ Real.exp (-b * (v - h)) * (Real.exp v / a) :=
              mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le
          _ = Real.exp ((1 - b) * U) * Real.exp ((1 - b) * (v - U) + b * h) / a := by
              rw [← mul_div_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
          _ ≤ Real.exp ((1 - b) * U) * 2 / a := by
              gcongr
              have h2 : (1 - b) * (v - U) + b * h ≤ 1 / 2 := by nlinarith [hv.1, hv.2]
              have h3 : 0 ≤ (1 - b) * (v - U) + b * h := by nlinarith [hv.1, hv.2]
              have := exp_le_one_add_two_mul' h3 (by linarith)
              linarith
          _ = 2 * Real.exp ((1 - b) * U) / a := by ring
    calc _ ≤ ∫ v in U..U + h, 2 * Real.exp ((1 - b) * U) / a :=
          intervalIntegral.integral_mono_on (by linarith) (iS U (U + h)) intervalIntegrable_const hbd
      _ = 2 * h * Real.exp ((1 - b) * U) / a := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hthird : 0 ≤ ∫ v in (0 : ℝ)..h, Real.exp (-b * v) * jumpN a v :=
    intervalIntegral.integral_nonneg hh0.le fun v _ => mul_nonneg (Real.exp_pos _).le (jumpN_nonneg a v)
  have hfin : 2 * h * Real.exp ((1 - b) * U) / (a * (1 - b)) + 2 * h * Real.exp ((1 - b) * U) / a
      ≤ 4 * h * Real.exp ((1 - b) * U) / (a * (1 - b)) := by
    have hE : 0 ≤ 2 * h * Real.exp ((1 - b) * U) := by positivity
    have : 2 * h * Real.exp ((1 - b) * U) / a ≤ 2 * h * Real.exp ((1 - b) * U) / (a * (1 - b)) :=
      div_le_div_of_nonneg_left hE (by positivity) (mul_le_of_le_one_right ha.le (by linarith))
    rw [show 4 * h * Real.exp ((1 - b) * U) / (a * (1 - b))
        = 2 * h * Real.exp ((1 - b) * U) / (a * (1 - b)) + 2 * h * Real.exp ((1 - b) * U) / (a * (1 - b)) by ring]
    linarith
  linarith

/-! ### The log-scale E-image -/

/-- The log-scale E-image `φ(u) = 1_{u>0} e^{u/2} E_G(e^u) e^{u(σ−½)}`. -/
def phiE (a σ : ℝ) (G : ℝ → ℝ) : ℝ → ℂ :=
  Cvs.Prolate.Mellin.TailMellinPlancherel.logTail fun w => eimage a G w * w ^ (σ - 1 / 2)

theorem phiE_of_pos (a σ : ℝ) (G : ℝ → ℝ) {u : ℝ} (hu : 0 < u) :
    phiE a σ G u = ((Real.exp ((σ - 1) * u) * (Real.exp u * eimage a G (Real.exp u)) : ℝ) : ℂ) := by
  unfold phiE Cvs.Prolate.Mellin.TailMellinPlancherel.logTail
  rw [indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
  congr 1
  dsimp only
  rw [← Real.exp_mul]
  have e : Real.exp (u / 2) * (eimage a G (Real.exp u) * Real.exp (u * (σ - 1 / 2)))
      = (Real.exp (u / 2) * Real.exp (u * (σ - 1 / 2))) * eimage a G (Real.exp u) := by ring
  rw [e, ← Real.exp_add, show (σ - 1) * u = u / 2 + u * (σ - 1 / 2) - u by ring, Real.exp_sub]
  field_simp

theorem phiE_of_nonpos (a σ : ℝ) (G : ℝ → ℝ) {u : ℝ} (hu : u ≤ 0) : phiE a σ G u = 0 := by
  unfold phiE Cvs.Prolate.Mellin.TailMellinPlancherel.logTail
  rw [indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from not_lt.2 hu)]

/-- `‖φ(u)‖ ≤ 1_{u>0} K e^{(σ−1)u}` when `|θE_G(θ)| ≤ K`. -/
theorem norm_phiE_le {σ K : ℝ} (hK : ∀ θ, 0 < θ → |θ * eimage a G θ| ≤ K) (u : ℝ) :
    ‖phiE a σ G u‖ ≤ (Ioi (0 : ℝ)).indicator (fun u => K * Real.exp ((σ - 1) * u)) u := by
  by_cases hu : 0 < u
  · rw [phiE_of_pos a σ G hu, indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu), Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hK _ (Real.exp_pos u)) (Real.exp_pos _).le
  · rw [phiE_of_nonpos a σ G (not_lt.1 hu), indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu), norm_zero]

theorem measurable_phiE (ha : 0 < a) (hGc : ContinuousOn G (Icc 0 1)) (σ : ℝ) : Measurable (phiE a σ G) :=
  Cvs.Prolate.Mellin.TailMellinPlancherel.measurable_logTail
    ((Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc).mul (measurable_id.pow_const _))

/-- For `σ < 1`, `φ` is integrable. -/
theorem integrable_phiE (ha : 0 < a) (hGc : ContinuousOn G (Icc 0 1)) {σ K : ℝ} (hσ : σ < 1)
    (hK : ∀ θ, 0 < θ → |θ * eimage a G θ| ≤ K) : Integrable (phiE a σ G) := by
  refine (integrable_indicator_iff measurableSet_Ioi |>.2
    ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < 1 - σ)).const_mul K)).mono'
    (measurable_phiE ha hGc σ).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  refine (norm_phiE_le hK u).trans (le_of_eq ?_)
  congr 1; funext u; congr 2; ring

/-- For `σ < 1`, `φ ∈ L²`. -/
theorem memLp_phiE (ha : 0 < a) (hGc : ContinuousOn G (Icc 0 1)) {σ K : ℝ} (hσ : σ < 1)
    (hK : ∀ θ, 0 < θ → |θ * eimage a G θ| ≤ K) : MemLp (phiE a σ G) 2 volume := by
  have hm := (measurable_phiE ha hGc σ).aestronglyMeasurable (μ := volume)
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine (integrable_indicator_iff measurableSet_Ioi |>.2
    ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < 2 * (1 - σ))).const_mul (K ^ 2))).mono'
    ((measurable_phiE ha hGc σ).norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := norm_phiE_le (σ := σ) hK u
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hu] at h ⊢
    calc ‖phiE a σ G u‖ ^ 2 ≤ (K * Real.exp ((σ - 1) * u)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = K ^ 2 * Real.exp (-(2 * (1 - σ)) * u) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  · rw [indicator_of_notMem hu] at h ⊢
    have : ‖phiE a σ G u‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this]; norm_num

/-! ### The pointwise bound -/

/-- The four-piece majorant of `‖φ(u + h) − φ(u)‖²`, split at `U = log(1/h)`. -/
def modBound (a L M K b h : ℝ) (u : ℝ) : ℝ :=
  (Ioc (-h) 0).indicator (fun _ => K ^ 2) u
    + (Ioi 0).indicator (fun u => 2 * h ^ 2 * K ^ 2 * Real.exp (-(2 * b) * u)) u
    + (Ioi (Real.log (1 / h))).indicator (fun u => 8 * K ^ 2 * Real.exp (-(2 * b) * u)) u
    + (Ioc 0 (Real.log (1 / h))).indicator (fun u => 4 * K * (L * h * Real.exp ((1 - b) * u)
        + a * M * (Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u)))) u

theorem modBound_nonneg (ha : 0 < a) {L M K b h : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 0 ≤ K) (hh : 0 ≤ h) (u : ℝ) :
    0 ≤ modBound a L M K b h u := by
  have hn : ∀ v, 0 ≤ jumpN a (v + h) - jumpN a v := fun v => sub_nonneg.2 (jumpN_mono ha (by linarith))
  unfold modBound
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
  · exact indicator_nonneg (fun _ _ => by positivity) _
  · exact indicator_nonneg (fun _ _ => by positivity) _
  · exact indicator_nonneg (fun _ _ => by positivity) _
  · exact indicator_nonneg (fun v _ => by have := hn v; positivity) _

/-- The bulk arithmetic: `(Aq(P₁ − P₀) + A(q − 1)P₀)² ≤ 2h²K²E + 4KS·E` for `A² ≤ E`, `0 ≤ q ≤ 1`, `1 − q ≤ h`,
`|P₀| ≤ K`, `|P₁ − P₀| ≤ 2K` and `|P₁ − P₀| ≤ S`. -/
theorem sq_bulk_le {A q P0 P1 K h E S : ℝ} (hA2 : A ^ 2 ≤ E) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h1q : 1 - q ≤ h)
    (hP0 : |P0| ≤ K) (hP2 : |P1 - P0| ≤ 2 * K) (hS : |P1 - P0| ≤ S) :
    (A * q * (P1 - P0) + A * (q - 1) * P0) ^ 2 ≤ 2 * h ^ 2 * K ^ 2 * E + 4 * K * S * E := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans hP0
  have hE0 : 0 ≤ E := (sq_nonneg A).trans hA2
  have e1 : (A * q * (P1 - P0) + A * (q - 1) * P0) ^ 2
      ≤ 2 * (A * q * (P1 - P0)) ^ 2 + 2 * (A * (q - 1) * P0) ^ 2 := by
    nlinarith [sq_nonneg (A * q * (P1 - P0) - A * (q - 1) * P0)]
  have hX : (P1 - P0) ^ 2 ≤ 2 * K * S := by
    rw [← sq_abs, sq]; exact mul_le_mul hP2 hS (abs_nonneg _) (by positivity)
  have e2 : (A * q * (P1 - P0)) ^ 2 ≤ E * (2 * K * S) := by
    rw [mul_pow, mul_pow]
    have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
    calc A ^ 2 * q ^ 2 * (P1 - P0) ^ 2 ≤ E * 1 * (2 * K * S) :=
          mul_le_mul (mul_le_mul hA2 hq2 (sq_nonneg _) hE0) hX (sq_nonneg _) (by positivity)
      _ = E * (2 * K * S) := by ring
  have e3 : (A * (q - 1) * P0) ^ 2 ≤ E * h ^ 2 * K ^ 2 := by
    rw [mul_pow, mul_pow]
    have a1 : (q - 1) ^ 2 ≤ h ^ 2 := by nlinarith
    have a2 : P0 ^ 2 ≤ K ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hP0 2
    exact mul_le_mul (mul_le_mul hA2 a1 (sq_nonneg _) hE0) a2 (sq_nonneg _) (by positivity)
  nlinarith

/-- **The pointwise majorant**: under the Lipschitz, sup and `|θE_G(θ)| ≤ K` bounds, for `0 < a ≤ 1`, `b > 0`,
`0 ≤ σ ≤ 1 − b` and `h > 0`, `‖φ(u + h) − φ(u)‖² ≤ modBound a L M K b h u`. -/
theorem sq_norm_phiE_sub_le (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hL : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |G t - G s| ≤ L * |t - s|)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, |G t| ≤ M) {K : ℝ} (hK : ∀ θ, 0 < θ → |θ * eimage a G θ| ≤ K)
    {b σ h : ℝ} (hb0 : 0 < b) (hσ0 : 0 ≤ σ) (hσb : σ ≤ 1 - b) (hh0 : 0 < h) (u : ℝ) :
    ‖phiE a σ G (u + h) - phiE a σ G u‖ ^ 2 ≤ modBound a L M K b h u := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 1 one_pos)
  have hL0 : 0 ≤ L := by
    have := hL 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    simp at this; exact (abs_nonneg _).trans this
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hB0 := modBound_nonneg (b := b) ha0 hL0 hM0 hK0 hh0.le u
  have hn : 0 ≤ jumpN a (u + h) - jumpN a u := sub_nonneg.2 (jumpN_mono ha0 (by linarith))
  have hBdef : modBound a L M K b h u = (Ioc (-h) 0).indicator (fun _ => K ^ 2) u
      + (Ioi 0).indicator (fun u => 2 * h ^ 2 * K ^ 2 * Real.exp (-(2 * b) * u)) u
      + (Ioi (Real.log (1 / h))).indicator (fun u => 8 * K ^ 2 * Real.exp (-(2 * b) * u)) u
      + (Ioc 0 (Real.log (1 / h))).indicator (fun u => 4 * K * (L * h * Real.exp ((1 - b) * u)
        + a * M * (Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u)))) u := rfl
  have p1 : 0 ≤ (Ioc (-h) 0).indicator (fun _ => K ^ 2) u := indicator_nonneg (fun _ _ => by positivity) _
  have p2 : 0 ≤ (Ioi 0).indicator (fun u => 2 * h ^ 2 * K ^ 2 * Real.exp (-(2 * b) * u)) u :=
    indicator_nonneg (fun _ _ => by positivity) _
  have p3 : 0 ≤ (Ioi (Real.log (1 / h))).indicator (fun u => 8 * K ^ 2 * Real.exp (-(2 * b) * u)) u :=
    indicator_nonneg (fun _ _ => by positivity) _
  have p4 : 0 ≤ (Ioc 0 (Real.log (1 / h))).indicator (fun u => 4 * K * (L * h * Real.exp ((1 - b) * u)
        + a * M * (Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u)))) u :=
    indicator_nonneg (fun v _ => by
      have := sub_nonneg.2 (jumpN_mono ha0 (by linarith : v ≤ v + h)); positivity) _
  rw [hBdef]
  rcases le_or_gt u 0 with hu | hu
  · rw [phiE_of_nonpos a σ G hu, sub_zero]
    rcases le_or_gt (u + h) 0 with huh | huh
    · rw [phiE_of_nonpos a σ G huh, norm_zero]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]; linarith
    · -- the boundary layer `−h < u ≤ 0`
      have hmem : u ∈ Ioc (-h) 0 := ⟨by linarith, hu⟩
      rw [phiE_of_pos a σ G huh, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hq : Real.exp ((σ - 1) * (u + h)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have hP := hK _ (Real.exp_pos (u + h))
      have h1 : (Real.exp ((σ - 1) * (u + h)) * (Real.exp (u + h) * eimage a G (Real.exp (u + h)))) ^ 2
          ≤ K ^ 2 := by
        rw [mul_pow]
        calc Real.exp ((σ - 1) * (u + h)) ^ 2 * (Real.exp (u + h) * eimage a G (Real.exp (u + h))) ^ 2
            ≤ 1 * K ^ 2 := by
              refine mul_le_mul (pow_le_one₀ (Real.exp_pos _).le hq) ?_ (sq_nonneg _) zero_le_one
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hP 2
          _ = K ^ 2 := one_mul _
      have hp1 : (Ioc (-h) 0).indicator (fun _ => K ^ 2) u = K ^ 2 := indicator_of_mem hmem _
      linarith
  -- the bulk `u > 0`
  have hAb : Real.exp (-(2 * b) * u) ≤ Real.exp (-b * u) := Real.exp_le_exp.2 (by
    have := mul_pos hb0 hu; linarith)
  have hq0 : 0 < Real.exp ((σ - 1) * h) := Real.exp_pos _
  have hq1 : Real.exp ((σ - 1) * h) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h1q : 1 - Real.exp ((σ - 1) * h) ≤ h := by
    have := Real.one_sub_le_exp_neg ((1 - σ) * h)
    rw [show -((1 - σ) * h) = (σ - 1) * h by ring] at this
    nlinarith
  have hA2 : Real.exp ((σ - 1) * u) ^ 2 ≤ Real.exp (-(2 * b) * u) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; nlinarith)
  have hP0K : |Real.exp u * eimage a G (Real.exp u)| ≤ K := hK _ (Real.exp_pos u)
  have hP1K : |Real.exp (u + h) * eimage a G (Real.exp (u + h))| ≤ K := hK _ (Real.exp_pos (u + h))
  have hP2 : |Real.exp (u + h) * eimage a G (Real.exp (u + h)) - Real.exp u * eimage a G (Real.exp u)| ≤ 2 * K :=
    (abs_sub _ _).trans (by linarith)
  have hΔ : phiE a σ G (u + h) - phiE a σ G u
      = ((Real.exp ((σ - 1) * u) * Real.exp ((σ - 1) * h)
          * (Real.exp (u + h) * eimage a G (Real.exp (u + h)) - Real.exp u * eimage a G (Real.exp u))
        + Real.exp ((σ - 1) * u) * (Real.exp ((σ - 1) * h) - 1) * (Real.exp u * eimage a G (Real.exp u)) : ℝ) : ℂ) := by
    rw [phiE_of_pos a σ G (by linarith), phiE_of_pos a σ G hu, ← Complex.ofReal_sub]
    congr 1
    rw [show (σ - 1) * (u + h) = (σ - 1) * u + (σ - 1) * h by ring, Real.exp_add]
    ring
  rw [hΔ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hp2 : (Ioi 0).indicator (fun u => 2 * h ^ 2 * K ^ 2 * Real.exp (-(2 * b) * u)) u
      = 2 * h ^ 2 * K ^ 2 * Real.exp (-(2 * b) * u) := indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu) _
  rcases lt_or_ge (Real.log (1 / h)) u with hUu | hUu
  · -- far: `|ΔP| ≤ 2K`
    have hp3 : (Ioi (Real.log (1 / h))).indicator (fun u => 8 * K ^ 2 * Real.exp (-(2 * b) * u)) u
        = 8 * K ^ 2 * Real.exp (-(2 * b) * u) := indicator_of_mem (show u ∈ Ioi (Real.log (1 / h)) from hUu) _
    have := sq_bulk_le hA2 hq0.le hq1 h1q hP0K hP2 hP2
    nlinarith
  · -- near: the dilation step
    have hp4 : (Ioc 0 (Real.log (1 / h))).indicator (fun u => 4 * K * (L * h * Real.exp ((1 - b) * u)
        + a * M * (Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u)))) u
        = 4 * K * (L * h * Real.exp ((1 - b) * u)
        + a * M * (Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u))) :=
      indicator_of_mem (show u ∈ Ioc 0 (Real.log (1 / h)) from ⟨hu, hUu⟩) _
    have hstep := abs_mul_eimage_sub_le ha0 hL hM (Real.exp_pos u)
      (Real.exp_le_exp.2 (by linarith : u ≤ u + h))
    have hratio : 1 - Real.exp u / Real.exp (u + h) ≤ h := by
      rw [Real.exp_add, div_mul_cancel_left₀ (Real.exp_pos u).ne', ← Real.exp_neg]
      linarith [Real.one_sub_le_exp_neg h]
    have hθa : Real.exp u + a ≤ 2 * Real.exp u := by linarith [Real.one_lt_exp_iff.2 hu]
    have hstep' : |Real.exp (u + h) * eimage a G (Real.exp (u + h)) - Real.exp u * eimage a G (Real.exp u)|
        ≤ L * h * Real.exp u + a * M * (jumpN a (u + h) - jumpN a u) := by
      refine hstep.trans ?_
      have hr0 : 0 ≤ 1 - Real.exp u / Real.exp (u + h) := by
        rw [sub_nonneg, div_le_one (Real.exp_pos _)]; exact Real.exp_le_exp.2 (by linarith)
      have h3 : L * (1 - Real.exp u / Real.exp (u + h)) * (Real.exp u + a) / 2 ≤ L * h * Real.exp u := by
        have h1 := mul_le_mul hratio hθa (by positivity) hh0.le
        calc L * (1 - Real.exp u / Real.exp (u + h)) * (Real.exp u + a) / 2
            = L * ((1 - Real.exp u / Real.exp (u + h)) * (Real.exp u + a)) / 2 := by ring
          _ ≤ L * (h * (2 * Real.exp u)) / 2 := by gcongr
          _ = L * h * Real.exp u := by ring
      exact add_le_add h3 le_rfl
    have hb := sq_bulk_le hA2 hq0.le hq1 h1q hP0K hP2 hstep'
    have hS0 : 0 ≤ L * h * Real.exp u + a * M * (jumpN a (u + h) - jumpN a u) :=
      add_nonneg (mul_nonneg (mul_nonneg hL0 hh0.le) (Real.exp_pos u).le) (mul_nonneg (mul_nonneg ha0.le hM0) hn)
    have e : 4 * K * (L * h * Real.exp ((1 - b) * u) + a * M * (Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u)))
        = 4 * K * (L * h * Real.exp u + a * M * (jumpN a (u + h) - jumpN a u)) * Real.exp (-b * u) := by
      rw [show (1 - b) * u = -b * u + u by ring, Real.exp_add]; ring
    have hmono : 4 * K * (L * h * Real.exp u + a * M * (jumpN a (u + h) - jumpN a u)) * Real.exp (-(2 * b) * u)
        ≤ 4 * K * (L * h * Real.exp u + a * M * (jumpN a (u + h) - jumpN a u)) * Real.exp (-b * u) :=
      mul_le_mul_of_nonneg_left hAb (by positivity)
    linarith

/-! ### Integrating the majorant -/

theorem integral_exp_Ioi_eq {c : ℝ} (hc : 0 < c) (U : ℝ) :
    ∫ u in Ioi U, Real.exp (-c * u) = Real.exp (-c * U) / c := by
  rw [integral_exp_mul_Ioi (by linarith : -c < 0) U]; field_simp

/-- `e^{c·log(1/h)} = h^{−c}` for `h > 0`. -/
theorem exp_mul_log_inv {h : ℝ} (hh : 0 < h) (c : ℝ) : Real.exp (c * Real.log (1 / h)) = h ^ (-c) := by
  rw [mul_comm, Real.exp_mul, Real.exp_log (by positivity), one_div, Real.inv_rpow hh.le, Real.rpow_neg hh.le]

/-- **The `L²` modulus of the log-scale E-image**: for `0 < a ≤ 1`, `|G| ≤ M` and `G` `L`-Lipschitz on `[0, 1]`,
`|θE_G(θ)| ≤ K`, `0 < b < 1`, `0 ≤ σ ≤ 1 − b` and `0 < h ≤ ½`,
`‖φ(· + h) − φ‖₂² ≤ (K²(1 + 5/b) + 4K(L + 4M)/(1 − b))·h^b`. -/
theorem integral_norm_phiE_sub_sq_le (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hL : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |G t - G s| ≤ L * |t - s|)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, |G t| ≤ M) {K : ℝ} (hK : ∀ θ, 0 < θ → |θ * eimage a G θ| ≤ K)
    {b σ h : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hσ0 : 0 ≤ σ) (hσb : σ ≤ 1 - b) (hh0 : 0 < h) (hh : h ≤ 1 / 2) :
    ∫ u, ‖phiE a σ G (u + h) - phiE a σ G u‖ ^ 2 ≤ (K ^ 2 * (1 + 5 / b) + 4 * K * (L + 4 * M) / (1 - b)) * h ^ b := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 1 one_pos)
  have hL0 : 0 ≤ L := by
    have := hL 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    simp at this; exact (abs_nonneg _).trans this
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  set U := Real.log (1 / h) with hU
  have hhU : h ≤ U := by
    have := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < 1 / h)
    rw [one_div, inv_inv] at this
    rw [hU, one_div]; linarith
  have hU0 : 0 ≤ U := hh0.le.trans hhU
  have h1b : 0 < 1 - b := by linarith
  -- the four pieces
  set f1 : ℝ → ℝ := (Ioc (-h) 0).indicator (fun _ => K ^ 2) with hf1
  set f2 : ℝ → ℝ := (Ioi 0).indicator (fun u => 2 * h ^ 2 * K ^ 2 * Real.exp (-(2 * b) * u)) with hf2
  set f3 : ℝ → ℝ := (Ioi U).indicator (fun u => 8 * K ^ 2 * Real.exp (-(2 * b) * u)) with hf3
  set g4 : ℝ → ℝ := fun u => 4 * K * (L * h * Real.exp ((1 - b) * u)
        + a * M * (Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u))) with hg4
  set f4 : ℝ → ℝ := (Ioc 0 U).indicator g4 with hf4
  have hb2 : 0 < 2 * b := by linarith
  have i1 : Integrable f1 := (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
  have i2 : Integrable f2 := (integrable_indicator_iff measurableSet_Ioi).2
    ((integrableOn_exp_mul_Ioi (by linarith : -(2 * b) < 0) 0).const_mul _)
  have i3 : Integrable f3 := (integrable_indicator_iff measurableSet_Ioi).2
    ((integrableOn_exp_mul_Ioi (by linarith : -(2 * b) < 0) U).const_mul _)
  have iE : ∀ c : ℝ, IntervalIntegrable (fun u => Real.exp (c * u)) volume 0 U := fun c =>
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have e0 : ∀ u, jumpN a (u + 0) = jumpN a u := fun u => by rw [add_zero]
  have iN : IntervalIntegrable (fun u => Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u)) volume 0 U := by
    have h1 := intervalIntegrable_exp_mul_jumpN ha0 (-b) h 0 U
    have h2 := intervalIntegrable_exp_mul_jumpN ha0 (-b) 0 0 U
    simp only [e0] at h2
    exact (h1.sub h2).congr fun u _ => (mul_sub _ _ _).symm
  have ig4 : IntervalIntegrable g4 volume 0 U :=
    (((iE (1 - b)).const_mul (L * h)).add (iN.const_mul (a * M))).const_mul (4 * K)
  have i4 : Integrable f4 :=
    (integrable_indicator_iff measurableSet_Ioc).2 ((intervalIntegrable_iff_integrableOn_Ioc_of_le hU0).1 ig4)
  -- the integrals
  have I1 : ∫ u, f1 u = K ^ 2 * h := by
    rw [hf1, integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul]
    ring
  have I2 : ∫ u, f2 u = h ^ 2 * K ^ 2 / b := by
    rw [hf2, integral_indicator measurableSet_Ioi, integral_const_mul, integral_exp_Ioi_eq hb2, mul_zero,
      Real.exp_zero]
    field_simp
  have I3 : ∫ u, f3 u = 4 * K ^ 2 * h ^ (2 * b) / b := by
    rw [hf3, integral_indicator measurableSet_Ioi, integral_const_mul, integral_exp_Ioi_eq hb2,
      show -(2 * b) * U = (-(2 * b)) * Real.log (1 / h) from rfl, exp_mul_log_inv hh0, neg_neg]
    field_simp
    ring
  have I4 : ∫ u, f4 u ≤ 4 * K * (L + 4 * M) * h ^ b / (1 - b) := by
    rw [hf4, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hU0, hg4,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add ((iE (1 - b)).const_mul (L * h))
        (iN.const_mul (a * M)), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hs := integral_exp_one_sub_le hb1 0 U
    have hj := integral_jump_le ha0 hb0 hb1 hh0 hh hhU
    have hE : Real.exp ((1 - b) * U) = h ^ (b - 1) := by
      rw [hU, exp_mul_log_inv hh0]; congr 1; ring
    rw [hE] at hs hj
    have hhb : h * h ^ (b - 1) = h ^ b := by
      rw [← Real.rpow_one_add' hh0.le (by linarith)]; congr 1; ring
    calc 4 * K * (L * h * (∫ u in (0 : ℝ)..U, Real.exp ((1 - b) * u))
          + a * M * ∫ u in (0 : ℝ)..U, Real.exp (-b * u) * (jumpN a (u + h) - jumpN a u))
        ≤ 4 * K * (L * h * (h ^ (b - 1) / (1 - b)) + a * M * (4 * h * h ^ (b - 1) / (a * (1 - b)))) := by
          gcongr
      _ = 4 * K * (L + 4 * M) * (h * h ^ (b - 1)) / (1 - b) := by field_simp
      _ = 4 * K * (L + 4 * M) * h ^ b / (1 - b) := by rw [hhb]
  -- compare with the majorant
  have hle : ∫ u, ‖phiE a σ G (u + h) - phiE a σ G u‖ ^ 2 ≤ ∫ u, (f1 u + f2 u + f3 u + f4 u) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity) (((i1.add i2).add i3).add i4)
      (Eventually.of_forall fun u => ?_)
    exact sq_norm_phiE_sub_le ha0 ha1 hL hM hK hb0 hσ0 hσb hh0 u
  have hsum : ∫ u, (f1 u + f2 u + f3 u + f4 u) = (∫ u, f1 u) + (∫ u, f2 u) + (∫ u, f3 u) + ∫ u, f4 u := by
    rw [integral_add (f := fun u => f1 u + f2 u + f3 u) ((i1.add i2).add i3) i4,
      integral_add (f := fun u => f1 u + f2 u) (i1.add i2) i3, integral_add i1 i2]
  rw [hsum, I1, I2, I3] at hle
  -- powers of `h`
  have hh1 : h ≤ 1 := by linarith
  have p1 : h ≤ h ^ b := by
    calc h = h ^ (1 : ℝ) := (Real.rpow_one h).symm
      _ ≤ h ^ b := Real.rpow_le_rpow_of_exponent_ge hh0 hh1 hb1.le
  have p2 : h ^ 2 ≤ h ^ b := by
    calc h ^ 2 = h ^ (2 : ℝ) := by norm_cast
      _ ≤ h ^ b := Real.rpow_le_rpow_of_exponent_ge hh0 hh1 (by linarith)
  have p3 : h ^ (2 * b) ≤ h ^ b := Real.rpow_le_rpow_of_exponent_ge hh0 hh1 (by linarith)
  have hfin : K ^ 2 * h + h ^ 2 * K ^ 2 / b + 4 * K ^ 2 * h ^ (2 * b) / b + 4 * K * (L + 4 * M) * h ^ b / (1 - b)
      ≤ (K ^ 2 * (1 + 5 / b) + 4 * K * (L + 4 * M) / (1 - b)) * h ^ b := by
    have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
    have q1 : K ^ 2 * h ≤ K ^ 2 * h ^ b := mul_le_mul_of_nonneg_left p1 hK2
    have q2 : h ^ 2 * K ^ 2 / b ≤ h ^ b * K ^ 2 / b := by gcongr
    have q3 : 4 * K ^ 2 * h ^ (2 * b) / b ≤ 4 * K ^ 2 * h ^ b / b := by gcongr
    have e : (K ^ 2 * (1 + 5 / b) + 4 * K * (L + 4 * M) / (1 - b)) * h ^ b
        = K ^ 2 * h ^ b + h ^ b * K ^ 2 / b + 4 * K ^ 2 * h ^ b / b + 4 * K * (L + 4 * M) * h ^ b / (1 - b) := by
      field_simp; ring
    rw [e]; linarith
  linarith

end Cvs.Xi.LogScaleEImageModulus

end
