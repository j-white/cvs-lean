import Mathlib
import Cvs.L2a.CutEstimateFrameFloor
import Cvs.L2a.CutGap
import Cvs.L2a.CutPointCountForm
import Cvs.L2a.FirstStepRemainderCount
import Cvs.L2a.RampCutSumsUniform
import Cvs.Upstream.SineSquaredRamp

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The remainder density on the cut range, and the rows `m ≥ 2` of `κ(X)`

`FirstStepRemainderCount`'s density obeys `ρ_mn ≤ g_mn(θ)(|ω'| + |log m − ω|A_mn(θ))`, `A_mn = 2α(mθ)/θ + 2(α(mθ)² + α(nθ)²)/(θ³Γ_mn)`;
for `m ≥ 2` the exact integrals of `ω'/θ²` and `|log m − ω|/θ^{j+1}` give `2∫₁^b ρ_mn ≤ 2g_mn(1)Φ̄_m` for every
`b ≥ 1`, so each row of `kapCount` is at most `2σ_mΦ̄_m`; with the cell majorants on the ramp and the logarithmic tail.
-/

namespace Cvs.L2a.CutRemainderDensity

open Real Set Cvs.L2a.CutGap Cvs.L2a.CutPointCountForm Cvs.L2a.FirstStepRemainderCount Cvs.L2a.CutEstimateFrameFloor Cvs.L2a.RampCutSumsUniform

/-- `A_mn(θ) = 2m²θ/(m²θ² − 1) + cutDeltaBound/Γ = 2α(mθ)/θ + 2(α(mθ)² + α(nθ)²)/(θ³Γ_mn)`. -/
noncomputable def cutA (m n θ : ℝ) : ℝ :=
  2 * m ^ 2 * θ / (m ^ 2 * θ ^ 2 - 1) + cutDeltaBound m n θ / cutGamma m n θ

/-- `L₃(x) = (2 log x + 1)/(4x²)`, so `∫_a^b log θ/θ³ = L₃(a) − L₃(b)`. -/
noncomputable def L3 (x : ℝ) : ℝ := (2 * Real.log x + 1) / (4 * x ^ 2)

/-- `L_j(x) = (j log x + 1)/(j²xʲ)`, so `∫_a^b log θ/θ^{j+1} = L_j(a) − L_j(b)`. -/
noncomputable def logPowAnti (j : ℕ) (x : ℝ) : ℝ := ((j : ℝ) * Real.log x + 1) / ((j : ℝ) ^ 2 * x ^ j)

/-- `J̄₁ = (16/25)(log(5/4) + 1/2)`. -/
noncomputable def J1bar : ℝ := 16 / 25 * (Real.log (5 / 4) + 1 / 2)

/-- `ε₀ = (2/9)log(3/2) + 1/9`. -/
noncomputable def eps0 : ℝ := 2 / 9 * Real.log (3 / 2) + 1 / 9

/-- `ε₃ = (4/81)log(3/2) + 1/81`. -/
noncomputable def eps3 : ℝ := 4 / 81 * Real.log (3 / 2) + 1 / 81

/-- `φ₀ = J̄₁ − 2ε₀`. -/
noncomputable def phi0 : ℝ := J1bar - 2 * eps0

/-- `C_m = 2/(m² − 1) + 4α_m²/(2m + 1 − α_m)`. -/
noncomputable def CM (m : ℕ) : ℝ := 2 / ((m : ℝ) ^ 2 - 1) + 4 * aU m ^ 2 / (2 * m + 1 - aU m)

/-- `Φ̄_m = log m + φ₀ + 1/m² + C_m(log m/4 − ε₃ + 1/(8m⁴))`. -/
noncomputable def PhiBar (m : ℕ) : ℝ :=
  Real.log m + phi0 + 1 / (m : ℝ) ^ 2 + CM m * (Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4))

/-- `κ̄_{≥2} = 2Σ_{m≥2} σ_mΦ̄_m`. -/
noncomputable def kappaBar2 : ℝ := 2 * ∑' m : ℕ, if 2 ≤ m then sigma m * PhiBar m else 0

theorem nsRamp'_nonneg {θ : ℝ} (hθ : 1 ≤ θ) : 0 ≤ nsRamp' θ := by
  unfold nsRamp'
  have h0 : 0 < θ := by linarith
  have hr := Cvs.Upstream.SineSquaredRamp.ramp_nonneg (5 / 4) (1 / 4) θ
  have hl := Real.log_nonneg hθ
  have hr' : 0 ≤ Cvs.Upstream.SineSquaredRamp.ramp' (5 / 4) (1 / 4) θ := by
    unfold Cvs.Upstream.SineSquaredRamp.ramp'
    split_ifs with h1 h2
    · exact le_rfl
    · apply mul_nonneg (by positivity)
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · apply div_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (by norm_num)
      · rw [div_le_iff₀ (by norm_num)]
        have : θ - 5 / 4 ≤ 1 / 4 := by linarith
        nlinarith [Real.pi_pos]
    · exact le_rfl
  positivity

theorem nsRamp'_of_le {θ : ℝ} (hθ : θ ≤ 5 / 4) : nsRamp' θ = 0 := by
  unfold nsRamp'
  rw [Cvs.Upstream.SineSquaredRamp.ramp_of_le hθ, Cvs.Upstream.SineSquaredRamp.ramp'_of_le hθ]
  simp

theorem nsRamp'_of_ge {θ : ℝ} (hθ : 3 / 2 ≤ θ) : nsRamp' θ = 1 / θ := by
  unfold nsRamp'
  rw [Cvs.Upstream.SineSquaredRamp.ramp_of_ge (by norm_num) (by linarith),
    Cvs.Upstream.SineSquaredRamp.ramp'_of_ge (by norm_num) (by linarith), mul_zero, add_zero]

theorem continuousOn_nsRamp : ContinuousOn nsRamp (Ioi 0) := fun _ hθ =>
  (hasDerivAt_nsRamp hθ).continuousAt.continuousWithinAt

theorem nsRamp_monotoneOn : MonotoneOn nsRamp (Ici 1) := by
  have hd : ∀ θ ∈ interior (Ici (1 : ℝ)), 0 ≤ deriv nsRamp θ := by
    intro θ hθ
    rw [interior_Ici] at hθ
    rw [(hasDerivAt_nsRamp (by linarith [mem_Ioi.mp hθ])).deriv]
    exact nsRamp'_nonneg (le_of_lt (mem_Ioi.mp hθ))
  refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ hd
  · exact fun θ hθ => (hasDerivAt_nsRamp (by linarith [mem_Ici.mp hθ])).continuousAt.continuousWithinAt
  · intro θ hθ
    rw [interior_Ici] at hθ
    exact (hasDerivAt_nsRamp (by linarith [mem_Ioi.mp hθ])).differentiableAt.differentiableWithinAt

/-- `FirstStepRemainderCount`'s density is continuous where `p_m`, `p_n` and `Γ_mn` are positive. -/
theorem continuousOn_remDensity {ω ω₁ : ℝ → ℝ} {m n : ℝ} {s : Set ℝ} (hω : ContinuousOn ω s)
    (hω₁ : ContinuousOn ω₁ s) (hpm : ∀ θ ∈ s, 0 < m ^ 2 * θ ^ 2 - 1) (hpn : ∀ θ ∈ s, 0 < n ^ 2 * θ ^ 2 - 1)
    (hΓ : ∀ θ ∈ s, 0 < cutGamma m n θ) : ContinuousOn (fun θ => remDensity ω ω₁ m n θ) s := by
  intro θ hθ
  have hw : ContinuousWithinAt (fun θ => |Real.log m - ω θ|) s θ := (continuousWithinAt_const.sub (hω θ hθ)).abs
  have hw₁ : ContinuousWithinAt (fun θ => |ω₁ θ|) s θ := (hω₁ θ hθ).abs
  have hpmc : ContinuousAt (fun θ => m ^ 2 * θ ^ 2 - 1) θ := by fun_prop
  have hpnc : ContinuousAt (fun θ => n ^ 2 * θ ^ 2 - 1) θ := by fun_prop
  have hΓc : ContinuousAt (fun θ => cutGamma m n θ) θ := by
    unfold cutGamma
    exact continuousAt_const.sub ((by fun_prop : ContinuousAt (fun t => m ^ 4 * t ^ 2) θ).div hpmc (hpm θ hθ).ne')
  have hBc : ContinuousAt (fun θ => cutDeltaBound m n θ) θ := by
    unfold cutDeltaBound
    exact ((by fun_prop : ContinuousAt (fun t => 2 * n ^ 4 * t) θ).div (hpnc.pow 2)
      (pow_ne_zero 2 (hpn θ hθ).ne')).add ((by fun_prop : ContinuousAt (fun t => 2 * m ^ 4 * t) θ).div
      (hpmc.pow 2) (pow_ne_zero 2 (hpm θ hθ).ne'))
  have hQ : ∀ k : ℝ, 0 < k ^ 2 * θ ^ 2 - 1 → ContinuousAt (fun θ => k ^ 2 * θ ^ 2 - 1) θ →
      ContinuousWithinAt (fun θ => (k ^ 2 * θ / √(k ^ 2 * θ ^ 2 - 1)) * (|ω₁ θ| / cutGamma m n θ
        + |Real.log m - ω θ| * (cutDeltaBound m n θ / cutGamma m n θ ^ 2
          + 2 * k ^ 2 * θ / (cutGamma m n θ * (k ^ 2 * θ ^ 2 - 1))))) s θ := by
    intro k hk hkc
    exact (((by fun_prop : ContinuousAt (fun t => k ^ 2 * t) θ).div hkc.sqrt
      (Real.sqrt_ne_zero'.2 hk)).continuousWithinAt).mul ((hw₁.div hΓc.continuousWithinAt (hΓ θ hθ).ne').add
      (hw.mul (((hBc.div (hΓc.pow 2) (pow_ne_zero 2 (hΓ θ hθ).ne')).add
        ((by fun_prop : ContinuousAt (fun t => 2 * k ^ 2 * t) θ).div (hΓc.mul hkc)
          (mul_ne_zero (hΓ θ hθ).ne' hk.ne'))).continuousWithinAt)))
  unfold remDensity
  exact ((hQ n (hpn θ hθ) hpnc).add (hQ m (hpm θ hθ) hpmc)).div (hpmc.mul hpnc).sqrt.continuousWithinAt
    (Real.sqrt_ne_zero'.2 (mul_pos (hpm θ hθ) (hpn θ hθ)))

/-- **The density against the kernel**: `ρ_mn ≤ g_mn(θ)(|ω'| + |log m − ω|A_mn(θ))` for `m ≤ n`. -/
theorem remDensity_le_cutG_mul {ω ω₁ : ℝ → ℝ} {m n θ : ℝ} (hm : 0 < m) (hmn : m ≤ n) (hmθ : 1 < m * θ)
    (hΓ : 0 < cutGamma m n θ) :
    remDensity ω ω₁ m n θ ≤ cutG m n θ * (|ω₁ θ| + |Real.log m - ω θ| * cutA m n θ) := by
  have hθ : 0 < θ := by by_contra h; push Not at h; nlinarith
  have hn : 0 < n := by linarith
  have hnθ : 1 < n * θ := lt_of_lt_of_le hmθ (mul_le_mul_of_nonneg_right hmn hθ.le)
  have hpm : 0 < m ^ 2 * θ ^ 2 - 1 := by nlinarith
  have hpn : 0 < n ^ 2 * θ ^ 2 - 1 := by nlinarith
  have hmono : n ^ 2 * θ / (n ^ 2 * θ ^ 2 - 1) ≤ m ^ 2 * θ / (m ^ 2 * θ ^ 2 - 1) := by
    rw [div_le_div_iff₀ hpn hpm]; nlinarith [mul_le_mul hmn hmn hm.le hn.le]
  unfold remDensity cutG cutA cutK
  rw [Real.sqrt_mul hpm.le]
  set pm := m ^ 2 * θ ^ 2 - 1 with hpmdef
  set pn := n ^ 2 * θ ^ 2 - 1 with hpndef
  set sm := √pm with hsm
  set sn := √pn with hsn
  set Γ := cutGamma m n θ with hΓdef
  set B := cutDeltaBound m n θ with hB
  set W1 := |ω₁ θ| with hW1
  set Wv := |Real.log m - ω θ| with hWv
  have hsm0 : 0 < sm := Real.sqrt_pos.2 hpm
  have hsn0 : 0 < sn := Real.sqrt_pos.2 hpn
  have hW0 : 0 ≤ Wv := abs_nonneg _
  rw [← sub_nonneg]
  have hX : 0 ≤ Wv * (n ^ 2 * θ / sn) * (2 / Γ) * (m ^ 2 * θ / pm - n ^ 2 * θ / pn) / (sm * sn) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by positivity) (sub_nonneg.2 hmono)
  convert hX using 1
  field_simp
  ring

theorem CM_nonneg {m : ℕ} (hm : 2 ≤ m) : 0 ≤ CM m := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : aU m ≤ aU 2 := aU_anti (by norm_num) hm2
  have ha2 : aU 2 = 4 / 3 := by unfold aU; norm_num
  have hp : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
  unfold CM
  have : 0 < 2 * (m : ℝ) + 1 - aU m := by linarith
  positivity

theorem CM_le {m : ℕ} (hm : 2 ≤ m) : CM m ≤ 86 / 33 := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : aU m ≤ aU 2 := aU_anti (by norm_num) hm2
  have ha2 : aU 2 = 4 / 3 := by unfold aU; norm_num
  have ha0 : 0 ≤ aU m := by
    unfold aU
    have : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hp : 3 ≤ (m : ℝ) ^ 2 - 1 := by nlinarith
  unfold CM
  have h1 : 2 / ((m : ℝ) ^ 2 - 1) ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
  have hden : 11 / 3 ≤ 2 * (m : ℝ) + 1 - aU m := by linarith
  have h2 : 4 * aU m ^ 2 / (2 * m + 1 - aU m) ≤ 4 * (4 / 3) ^ 2 / (11 / 3) := by
    apply div_le_div₀ (by positivity) _ (by norm_num) hden
    gcongr
    linarith
  norm_num at h2
  linarith

/-- `A_mn(θ) ≤ 2/θ + C_m/θ³` for `2 ≤ m < n`, `θ ≥ 1`. -/
theorem cutA_le {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) {θ : ℝ} (hθ : 1 ≤ θ) :
    cutA m n θ ≤ 2 / θ + CM m / θ ^ 3 := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  have hθ0 : 0 < θ := by linarith
  have hmθ : (m : ℝ) ≤ m * θ := le_mul_of_one_le_right (by linarith) hθ
  have hnθ : (m : ℝ) ≤ n * θ := by nlinarith
  have hp1 : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
  have hpm : (m : ℝ) ^ 2 * θ ^ 2 - 1 ≥ ((m : ℝ) ^ 2 - 1) * θ ^ 2 := by nlinarith
  have hpm0 : 0 < (m : ℝ) ^ 2 * θ ^ 2 - 1 := by nlinarith
  have hpn0 : 0 < (n : ℝ) ^ 2 * θ ^ 2 - 1 := by nlinarith
  have hΓ := cutGamma_ge_of_two_le hm2 hmn' hθ
  have haU : aU m = 1 + 1 / ((m : ℝ) ^ 2 - 1) := by unfold aU; field_simp; ring
  have hden : 0 < 2 * (m : ℝ) + 1 - aU m := by
    have := CM_nonneg hm
    rw [haU]
    have : 1 / ((m : ℝ) ^ 2 - 1) ≤ 1 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
    linarith
  have hΓ' : 2 * (m : ℝ) + 1 - aU m ≤ cutGamma m n θ := by rw [haU]; linarith
  -- the two pieces of cutDeltaBound
  have hαm : aU (m * θ) ≤ aU m := aU_anti (by linarith) hmθ
  have hαn : aU (n * θ) ≤ aU m := aU_anti (by linarith) hnθ
  have hα0m : 0 ≤ aU (m * θ) := by
    unfold aU
    have : 0 < ((m : ℝ) * θ) ^ 2 - 1 := by nlinarith
    positivity
  have hα0n : 0 ≤ aU (n * θ) := by
    unfold aU
    have : 0 < ((n : ℝ) * θ) ^ 2 - 1 := by nlinarith
    positivity
  have hBe : cutDeltaBound m n θ = 2 * (aU (n * θ) ^ 2 + aU (m * θ) ^ 2) / θ ^ 3 := by
    unfold cutDeltaBound aU
    rw [mul_pow, mul_pow]
    field_simp
  have hB : cutDeltaBound m n θ ≤ 4 * aU m ^ 2 / θ ^ 3 := by
    rw [hBe]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [pow_le_pow_left₀ hα0m hαm 2, pow_le_pow_left₀ hα0n hαn 2]
  have hB0 : 0 ≤ cutDeltaBound m n θ := by unfold cutDeltaBound; positivity
  have hΓ0 : 0 < cutGamma m n θ := lt_of_lt_of_le hden hΓ'
  have h1 : 2 * (m : ℝ) ^ 2 * θ / ((m : ℝ) ^ 2 * θ ^ 2 - 1) ≤ 2 / θ + 2 / ((m : ℝ) ^ 2 - 1) / θ ^ 3 := by
    have e : 2 * (m : ℝ) ^ 2 * θ / ((m : ℝ) ^ 2 * θ ^ 2 - 1) = 2 / θ + 2 / (θ * ((m : ℝ) ^ 2 * θ ^ 2 - 1)) := by
      field_simp; ring
    rw [e]
    have : 2 / (θ * ((m : ℝ) ^ 2 * θ ^ 2 - 1)) ≤ 2 / ((m : ℝ) ^ 2 - 1) / θ ^ 3 := by
      rw [div_div]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    linarith
  have h2 : cutDeltaBound m n θ / cutGamma m n θ ≤ 4 * aU m ^ 2 / (2 * m + 1 - aU m) / θ ^ 3 := by
    calc cutDeltaBound m n θ / cutGamma m n θ ≤ (4 * aU m ^ 2 / θ ^ 3) / (2 * m + 1 - aU m) :=
          div_le_div₀ (by positivity) hB hden hΓ'
      _ = 4 * aU m ^ 2 / (2 * m + 1 - aU m) / θ ^ 3 := by ring
  unfold cutA CM
  rw [add_div]
  linarith

theorem hasDerivAt_neg_logPowAnti {j : ℕ} (hj : 1 ≤ j) {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt (fun x => -logPowAnti j x) (Real.log θ / θ ^ (j + 1)) θ := by
  unfold logPowAnti
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (j : ℝ) ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x => (j : ℝ) * Real.log x + 1) ((j : ℝ) * θ⁻¹) θ := by
    simpa using ((Real.hasDerivAt_log hθ.ne').const_mul (j : ℝ)).add_const 1
  have h2 : HasDerivAt (fun x : ℝ => (j : ℝ) ^ 2 * x ^ j) ((j : ℝ) ^ 2 * ((j : ℝ) * θ ^ (j - 1))) θ := by
    simpa using (hasDerivAt_pow j θ).const_mul ((j : ℝ) ^ 2)
  have h3 := (h1.div h2 (by positivity)).neg
  refine h3.congr_deriv ?_
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- `∫_a^b log θ/θ^{j+1} = L_j(a) − L_j(b)`. -/
theorem integral_log_div_pow {j : ℕ} (hj : 1 ≤ j) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ θ in a..b, Real.log θ / θ ^ (j + 1) = logPowAnti j a - logPowAnti j b := by
  have hcont : ContinuousOn (fun θ : ℝ => Real.log θ / θ ^ (j + 1)) (uIcc a b) := by
    intro θ hθ
    rw [uIcc_of_le hab] at hθ
    have h0 : 0 < θ := lt_of_lt_of_le ha hθ.1
    exact ((Real.continuousAt_log h0.ne').div (continuousAt_id.pow _) (pow_ne_zero _ h0.ne')).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => -logPowAnti j x)
    (fun θ hθ => hasDerivAt_neg_logPowAnti hj (lt_of_lt_of_le ha (by rw [uIcc_of_le hab] at hθ; exact hθ.1)))
    (hcont.intervalIntegrable)]
  ring

/-- `∫_a^b θ^{-(j+1)} = (a^{-j} − b^{-j})/j`. -/
theorem integral_inv_pow {j : ℕ} (hj : 1 ≤ j) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ θ in a..b, 1 / θ ^ (j + 1) = (1 / a ^ j - 1 / b ^ j) / j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (j : ℝ) ≠ 0 := by linarith
  have hpos : ∀ θ ∈ uIcc a b, 0 < θ := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ; linarith [hθ.1]
  have hd : ∀ θ ∈ uIcc a b, HasDerivAt (fun x : ℝ => -(1 / ((j : ℝ) * x ^ j))) (1 / θ ^ (j + 1)) θ := by
    intro θ hθ
    have h0 := hpos θ hθ
    have h := ((hasDerivAt_const θ (1 : ℝ)).div ((hasDerivAt_pow j θ).const_mul (j : ℝ))
      (mul_ne_zero hj0 (pow_ne_zero _ h0.ne'))).neg
    refine h.congr_deriv ?_
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hc : ContinuousOn (fun θ : ℝ => 1 / θ ^ (j + 1)) (uIcc a b) := fun θ hθ =>
    (continuousAt_const.div (continuousAt_id.pow _) (pow_ne_zero _ (hpos θ hθ).ne')).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  field_simp
  ring

theorem hasDerivAt_neg_L3 {θ : ℝ} (hθ : 0 < θ) : HasDerivAt (fun x => -L3 x) (Real.log θ / θ ^ 3) θ := by
  unfold L3
  have h1 : HasDerivAt (fun x => 2 * Real.log x + 1) (2 * θ⁻¹) θ := by
    simpa using ((Real.hasDerivAt_log hθ.ne').const_mul 2).add_const 1
  have h2 : HasDerivAt (fun x : ℝ => 4 * x ^ 2) (4 * (2 * θ)) θ := by
    simpa using ((hasDerivAt_pow 2 θ).const_mul 4)
  have h3 := (h1.div h2 (mul_ne_zero (by norm_num) (pow_ne_zero 2 hθ.ne'))).neg
  refine h3.congr_deriv ?_
  field_simp
  ring

theorem integral_log_div_pow3 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ θ in a..b, Real.log θ / θ ^ 3 = L3 a - L3 b := by
  have hcont : ContinuousOn (fun θ : ℝ => Real.log θ / θ ^ 3) (uIcc a b) := by
    intro θ hθ
    rw [uIcc_of_le hab] at hθ
    have h0 : 0 < θ := lt_of_lt_of_le ha hθ.1
    exact ((Real.continuousAt_log h0.ne').div (continuousAt_id.pow 3) (pow_ne_zero 3 h0.ne')).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => -L3 x)
    (fun θ hθ => hasDerivAt_neg_L3 (lt_of_lt_of_le ha (by rw [uIcc_of_le hab] at hθ; exact hθ.1)))
    (hcont.intervalIntegrable)]
  ring

theorem L3_anti {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : L3 b ≤ L3 a := by
  have h := integral_log_div_pow3 (by linarith : (0 : ℝ) < a) hab
  have hn : 0 ≤ ∫ θ in a..b, Real.log θ / θ ^ 3 :=
    intervalIntegral.integral_nonneg hab fun θ hθ => by
      have : 1 ≤ θ := le_trans ha hθ.1
      have := Real.log_nonneg this
      positivity
  linarith

theorem L3_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ L3 x := by
  unfold L3
  have := Real.log_nonneg hx
  positivity

theorem logPowAnti_three_halves_two : logPowAnti 2 (3 / 2) = eps0 := by
  unfold logPowAnti eps0; norm_num; ring

theorem logPowAnti_three_halves_four : logPowAnti 4 (3 / 2) = eps3 := by
  unfold logPowAnti eps3; norm_num; ring

/-- `∫₁^b |log m − ω|/θ^{j+1} ≤ log m/j − L_j(3/2) + 2/(j²mʲ)` for `m ≥ 2` and every `b ≥ 1`. -/
theorem integral_abs_log_sub_div_pow_le {j : ℕ} (hj : 1 ≤ j) {m : ℕ} (hm : 2 ≤ m) {b : ℝ} (hb : 1 ≤ b) :
    ∫ θ in (1 : ℝ)..b, |Real.log m - nsRamp θ| / θ ^ (j + 1)
      ≤ Real.log m / j - logPowAnti j (3 / 2) + 2 / ((j : ℝ) ^ 2 * (m : ℝ) ^ j) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  set f := fun θ : ℝ => |Real.log m - nsRamp θ| / θ ^ (j + 1) with hf
  have hfi : ∀ u v, 1 ≤ u → u ≤ v → IntervalIntegrable f MeasureTheory.volume u v := by
    intro u v hu huv
    apply ContinuousOn.intervalIntegrable
    intro θ hθ
    rw [uIcc_of_le huv] at hθ
    have h0 : 0 < θ := by linarith [hθ.1]
    exact ((continuousAt_const.sub (continuousOn_nsRamp.continuousAt (Ioi_mem_nhds h0))).abs.div
      (continuousAt_id.pow _) (pow_ne_zero _ h0.ne')).continuousWithinAt
  have hci : ∀ u v, 0 < u → u ≤ v → IntervalIntegrable (fun θ : ℝ => 1 / θ ^ (j + 1)) MeasureTheory.volume u v := by
    intro u v hu huv
    apply ContinuousOn.intervalIntegrable
    intro θ hθ
    rw [uIcc_of_le huv] at hθ
    have h0 : 0 < θ := by linarith [hθ.1]
    exact (continuousAt_const.div (continuousAt_id.pow _) (pow_ne_zero _ h0.ne')).continuousWithinAt
  have hcl : ∀ u v, 0 < u → u ≤ v →
      IntervalIntegrable (fun θ : ℝ => Real.log θ / θ ^ (j + 1)) MeasureTheory.volume u v := by
    intro u v hu huv
    apply ContinuousOn.intervalIntegrable
    intro θ hθ
    rw [uIcc_of_le huv] at hθ
    have h0 : 0 < θ := by linarith [hθ.1]
    exact ((Real.continuousAt_log h0.ne').div (continuousAt_id.pow _) (pow_ne_zero _ h0.ne')).continuousWithinAt
  set B' := max b m with hB'
  have hB'm : (m : ℝ) ≤ B' := le_max_right _ _
  have hbB' : b ≤ B' := le_max_left _ _
  have h1 : ∫ θ in (1 : ℝ)..b, f θ ≤ ∫ θ in (1 : ℝ)..B', f θ :=
    intervalIntegral.integral_mono_interval le_rfl hb hbB'
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun θ hθ => by
        simp only [hf]; have : 0 < θ := by linarith [hθ.1]
        positivity)
      (hfi 1 B' le_rfl (by linarith))
  have hsplit : ∫ θ in (1 : ℝ)..B', f θ
      = (∫ θ in (1 : ℝ)..3 / 2, f θ) + (∫ θ in (3 / 2 : ℝ)..m, f θ) + ∫ θ in (m : ℝ)..B', f θ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hfi _ _ le_rfl (by norm_num))
        (hfi _ _ (by norm_num) (by linarith)),
      intervalIntegral.integral_add_adjacent_intervals (hfi _ _ le_rfl (by linarith)) (hfi _ _ (by linarith) hB'm)]
  have p1 : ∫ θ in (1 : ℝ)..3 / 2, f θ ≤ Real.log m * ((1 / (1 : ℝ) ^ j - 1 / (3 / 2 : ℝ) ^ j) / j) := by
    rw [← integral_inv_pow hj one_pos (by norm_num), ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num) (hfi _ _ le_rfl (by norm_num))
      ((hci 1 (3 / 2) one_pos (by norm_num)).const_mul _)
    intro θ hθ
    simp only [hf]
    have h0 : 0 < θ := by linarith [hθ.1]
    have hw0 := nsRamp_nonneg hθ.1
    have hwl := nsRamp_le_log hθ.1
    have hlθ : Real.log θ ≤ Real.log m := Real.log_le_log h0 (by linarith [hθ.2])
    rw [abs_of_nonneg (by linarith), mul_one_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have p2 : ∫ θ in (3 / 2 : ℝ)..m, f θ = Real.log m * ((1 / (3 / 2 : ℝ) ^ j - 1 / (m : ℝ) ^ j) / j)
      - (logPowAnti j (3 / 2) - logPowAnti j m) := by
    rw [← integral_inv_pow hj (by norm_num) (by linarith), ← integral_log_div_pow hj (by norm_num) (by linarith),
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hci _ _ (by norm_num) (by linarith)).const_mul _)
        (hcl _ _ (by norm_num) (by linarith))]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le (by linarith)] at hθ
    simp only [hf]
    have h0 : 0 < θ := by linarith [hθ.1]
    rw [nsRamp_of_ge hθ.1, abs_of_nonneg (sub_nonneg.2 (Real.log_le_log h0 hθ.2))]
    field_simp
  have p3 : ∫ θ in (m : ℝ)..B', f θ = (logPowAnti j m - logPowAnti j B')
      - Real.log m * ((1 / (m : ℝ) ^ j - 1 / B' ^ j) / j) := by
    rw [← integral_inv_pow hj hm0 hB'm, ← integral_log_div_pow hj hm0 hB'm,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hcl _ _ hm0 hB'm) ((hci _ _ hm0 hB'm).const_mul _)]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hB'm] at hθ
    simp only [hf]
    have h0 : 0 < θ := by linarith [hθ.1]
    rw [nsRamp_of_ge (by linarith [hθ.1]), abs_of_nonpos (sub_nonpos.2 (Real.log_le_log hm0 hθ.1))]
    field_simp
    ring
  have hLm : logPowAnti j m = Real.log m / (j * (m : ℝ) ^ j) + 1 / ((j : ℝ) ^ 2 * (m : ℝ) ^ j) := by
    unfold logPowAnti; field_simp
  have hB'0 : 0 < B' := by linarith
  have hLB : Real.log m / (j * B' ^ j) ≤ logPowAnti j B' := by
    unfold logPowAnti
    rw [show Real.log m / (j * B' ^ j) = (j * Real.log m) / ((j : ℝ) ^ 2 * B' ^ j) by field_simp]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := Real.log_le_log hm0 hB'm
    nlinarith
  have e1 : Real.log m * ((1 / (1 : ℝ) ^ j - 1 / (3 / 2 : ℝ) ^ j) / j)
      + (Real.log m * ((1 / (3 / 2 : ℝ) ^ j - 1 / (m : ℝ) ^ j) / j) - (logPowAnti j (3 / 2) - logPowAnti j m))
      + ((logPowAnti j m - logPowAnti j B') - Real.log m * ((1 / (m : ℝ) ^ j - 1 / B' ^ j) / j))
      = Real.log m / j - logPowAnti j (3 / 2) + 2 / ((j : ℝ) ^ 2 * (m : ℝ) ^ j)
        + (Real.log m / (j * B' ^ j) - logPowAnti j B') := by
    rw [hLm]; field_simp; ring
  linarith [h1, hsplit, p1, p2, p3, e1, hLB]

/-- `∫₁^b |log m − ω|/θ³ ≤ log m/2 − ε₀ + 1/(2m²)`. -/
theorem integral_abs_div_pow3_le {m : ℕ} (hm : 2 ≤ m) {b : ℝ} (hb : 1 ≤ b) :
    ∫ θ in (1 : ℝ)..b, |Real.log m - nsRamp θ| / θ ^ 3 ≤ Real.log m / 2 - eps0 + 1 / (2 * (m : ℝ) ^ 2) := by
  have h := integral_abs_log_sub_div_pow_le (j := 2) (by norm_num) hm hb
  rw [logPowAnti_three_halves_two] at h
  norm_num at h ⊢
  convert h using 2
  ring

/-- `∫₁^b |log m − ω|/θ⁵ ≤ log m/4 − ε₃ + 1/(8m⁴)`. -/
theorem integral_abs_div_pow5_le {m : ℕ} (hm : 2 ≤ m) {b : ℝ} (hb : 1 ≤ b) :
    ∫ θ in (1 : ℝ)..b, |Real.log m - nsRamp θ| / θ ^ 5 ≤ Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4) := by
  have h := integral_abs_log_sub_div_pow_le (j := 4) (by norm_num) hm hb
  rw [logPowAnti_three_halves_four] at h
  norm_num at h ⊢
  convert h using 2
  ring

theorem J1bar_nonneg : 0 ≤ J1bar := by
  unfold J1bar
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5 / 4)
  positivity

/-- `∫₁^b ω'/θ² ≤ J̄₁` for every `b ≥ 1`. -/
theorem integral_nsRamp'_div_sq_le {b : ℝ} (hb : 1 ≤ b) : ∫ θ in (1 : ℝ)..b, nsRamp' θ / θ ^ 2 ≤ J1bar := by
  have hci : ∀ u v, 0 < u → u ≤ v → IntervalIntegrable (fun θ => nsRamp' θ / θ ^ 2) MeasureTheory.volume u v := by
    intro u v hu huv
    apply ContinuousOn.intervalIntegrable
    intro θ hθ
    rw [uIcc_of_le huv] at hθ
    have h0 : 0 < θ := by linarith [hθ.1]
    exact ((continuousOn_nsRamp'.continuousAt (Ioi_mem_nhds h0)).div (continuousAt_id.pow 2)
      (pow_ne_zero 2 h0.ne')).continuousWithinAt
  have hzero : ∀ c, 1 ≤ c → c ≤ 5 / 4 → ∫ θ in (1 : ℝ)..c, nsRamp' θ / θ ^ 2 = 0 := by
    intro c hc1 hc2
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ hθ => by
      rw [uIcc_of_le hc1] at hθ
      simp [nsRamp'_of_le (le_trans hθ.2 hc2)]]
    simp
  rcases le_or_gt b (5 / 4) with hb54 | hb54
  · rw [hzero b hb hb54]; exact J1bar_nonneg
  rw [← intervalIntegral.integral_add_adjacent_intervals (hci 1 (5 / 4) one_pos (by norm_num))
    (hci (5 / 4) b (by norm_num) hb54.le), hzero (5 / 4) (by norm_num) le_rfl, zero_add]
  -- G(θ) = nsRamp θ/θ² − 2 L3 θ, with G' ≥ nsRamp'/θ²
  set G' := fun θ : ℝ => nsRamp' θ / θ ^ 2 - 2 * nsRamp θ / θ ^ 3 + 2 * (Real.log θ / θ ^ 3) with hG'
  have hpos : ∀ θ ∈ uIcc (5 / 4 : ℝ) b, 0 < θ := fun θ hθ => by
    rw [uIcc_of_le hb54.le] at hθ; linarith [hθ.1]
  have hG : ∀ θ ∈ uIcc (5 / 4 : ℝ) b, HasDerivAt (fun x => nsRamp x / x ^ 2 - 2 * L3 x) (G' θ) θ := by
    intro θ hθ
    have h0 := hpos θ hθ
    have h1 := (hasDerivAt_nsRamp h0).div (hasDerivAt_pow 2 θ) (pow_ne_zero 2 h0.ne')
    have h2 := (hasDerivAt_neg_L3 h0).const_mul 2
    have h3 := h1.add h2
    refine (h3.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [hG']
      field_simp
      ring
    · filter_upwards with x
      simp only [Pi.add_apply, Pi.div_apply]
      ring
  have hGc : ContinuousOn G' (uIcc (5 / 4 : ℝ) b) := by
    intro θ hθ
    have h0 := hpos θ hθ
    simp only [hG']
    exact ((((continuousOn_nsRamp'.continuousAt (Ioi_mem_nhds h0)).div (continuousAt_id.pow 2)
      (pow_ne_zero 2 h0.ne')).sub ((continuousAt_const.mul (continuousOn_nsRamp.continuousAt (Ioi_mem_nhds h0))).div
      (continuousAt_id.pow 3) (pow_ne_zero 3 h0.ne'))).add (continuousAt_const.mul
      ((Real.continuousAt_log h0.ne').div (continuousAt_id.pow 3) (pow_ne_zero 3 h0.ne')))).continuousWithinAt
  have hle : ∫ θ in (5 / 4 : ℝ)..b, nsRamp' θ / θ ^ 2 ≤ ∫ θ in (5 / 4 : ℝ)..b, G' θ := by
    apply intervalIntegral.integral_mono_on hb54.le (hci _ _ (by norm_num) hb54.le) hGc.intervalIntegrable
    intro θ hθ
    have h0 : 0 < θ := by linarith [hθ.1]
    simp only [hG']
    have hw := nsRamp_le_log (by linarith [hθ.1] : (1 : ℝ) ≤ θ)
    have : 2 * nsRamp θ / θ ^ 3 ≤ 2 * (Real.log θ / θ ^ 3) := by
      rw [mul_div_assoc]; gcongr
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG hGc.intervalIntegrable] at hle
  have hb0 : 0 < b := by linarith
  have hw := nsRamp_le_log (by linarith : (1 : ℝ) ≤ b)
  have h54 : nsRamp (5 / 4) = 0 := nsRamp_of_le le_rfl
  have hJ : 2 * L3 (5 / 4) = J1bar := by unfold L3 J1bar; norm_num; ring
  have hLb : nsRamp b / b ^ 2 - 2 * L3 b ≤ 0 := by
    unfold L3
    have : nsRamp b / b ^ 2 ≤ Real.log b / b ^ 2 := by gcongr
    have e : 2 * ((2 * Real.log b + 1) / (4 * b ^ 2)) = Real.log b / b ^ 2 + 1 / (2 * b ^ 2) := by
      field_simp; ring
    have : 0 < 1 / (2 * b ^ 2) := by positivity
    linarith
  simp only [h54, zero_div, zero_sub] at hle
  linarith

theorem PhiBar_eq (m : ℕ) :
    PhiBar m = J1bar + 2 * (Real.log m / 2 - eps0 + 1 / (2 * (m : ℝ) ^ 2))
      + CM m * (Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4)) := by
  unfold PhiBar phi0; field_simp; ring

theorem PhiBar_nonneg {m : ℕ} (hm : 2 ≤ m) : 0 ≤ PhiBar m := by
  have h2 := integral_abs_div_pow3_le hm le_rfl
  have h3 := integral_abs_div_pow5_le hm le_rfl
  simp only [intervalIntegral.integral_same] at h2 h3
  rw [PhiBar_eq]
  have := J1bar_nonneg
  have := CM_nonneg hm
  positivity

theorem PhiBar_le {m : ℕ} (hm : 2 ≤ m) : PhiBar m ≤ (1 + 43 / 66) * Real.log m + J1bar + 1 := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hC := CM_le hm
  have hC0 := CM_nonneg hm
  have hl : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have he0 : 0 ≤ eps0 := by unfold eps0; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2); positivity
  have he3 : 0 ≤ eps3 := by unfold eps3; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2); positivity
  have hm4 : 1 / (8 * (m : ℝ) ^ 4) ≤ 1 / 128 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pow_le_pow_left₀ (by norm_num) hm2 4]
  have hm2' : 1 / (m : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  unfold PhiBar phi0
  have hX : CM m * (Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4)) ≤ 86 / 33 * (Real.log m / 4 + 1 / 128) := by
    have hY : Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4) ≤ Real.log m / 4 + 1 / 128 := by linarith
    have hY0 : 0 ≤ Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4) := by
      have h3 := integral_abs_div_pow5_le hm le_rfl
      simp only [intervalIntegral.integral_same] at h3
      linarith
    calc CM m * (Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4)) ≤ 86 / 33 * (Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4)) :=
          mul_le_mul_of_nonneg_right hC hY0
      _ ≤ 86 / 33 * (Real.log m / 4 + 1 / 128) := mul_le_mul_of_nonneg_left hY (by norm_num)
  nlinarith

/-- `2∫₁^b ρ_mn ≤ 2g_mn(1)Φ̄_m` for `2 ≤ m < n` and every `b ≥ 1`. -/
theorem two_mul_integral_remDensity_le {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) {b : ℝ} (hb : 1 ≤ b) :
    2 * ∫ θ in (1 : ℝ)..b, remDensity nsRamp nsRamp' m n θ ≤ 2 * cutG m n 1 * PhiBar m := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  have hm0 : (0 : ℝ) < m := by linarith
  have hG1 : 0 ≤ cutG m n 1 := cutG_nonneg hm0 (by linarith) (by linarith) (cutGamma_pos_of_two_le hm2 hmn' le_rfl)
  have hC0 := CM_nonneg hm
  set M := fun θ : ℝ => cutG m n 1 * (nsRamp' θ / θ ^ 2 + 2 * (|Real.log m - nsRamp θ| / θ ^ 3)
    + CM m * (|Real.log m - nsRamp θ| / θ ^ 5)) with hM
  have hpt : ∀ θ ∈ Icc (1 : ℝ) b, remDensity nsRamp nsRamp' m n θ ≤ M θ := by
    intro θ hθ
    have hθ1 : 1 ≤ θ := hθ.1
    have hθ0 : 0 < θ := by linarith
    have hΓ := cutGamma_pos_of_two_le hm2 hmn' hθ1
    have hstar := remDensity_le_cutG_mul (ω := nsRamp) (ω₁ := nsRamp') hm0 (by linarith) (by nlinarith) hΓ
    have hA := cutA_le hm hmn hθ1
    have hw1 : |nsRamp' θ| = nsRamp' θ := abs_of_nonneg (nsRamp'_nonneg hθ1)
    have hsq := sq_mul_cutG_le (m := (m : ℝ)) (n := (n : ℝ)) (a := 1) (θ := θ) hm0 (by linarith) (by linarith)
      hθ1 (cutGamma_pos_of_two_le hm2 hmn' le_rfl)
    have hG : cutG m n θ ≤ cutG m n 1 / θ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hGθ0 : 0 ≤ cutG m n θ := cutG_nonneg hm0 (by linarith) (by nlinarith) hΓ
    have hW := abs_nonneg (Real.log m - nsRamp θ)
    have hw' := nsRamp'_nonneg hθ1
    have hA0 : 0 ≤ cutA m n θ := by
      unfold cutA
      have : (1 : ℝ) ≤ θ ^ 2 := by nlinarith
      have : 0 < (m : ℝ) ^ 2 * θ ^ 2 - 1 := by nlinarith
      have : 0 ≤ cutDeltaBound m n θ := by unfold cutDeltaBound; positivity
      positivity
    rw [hw1] at hstar
    calc remDensity nsRamp nsRamp' m n θ ≤ cutG m n θ * (nsRamp' θ + |Real.log m - nsRamp θ| * cutA m n θ) := hstar
      _ ≤ cutG m n 1 / θ ^ 2 * (nsRamp' θ + |Real.log m - nsRamp θ| * (2 / θ + CM m / θ ^ 3)) := by
          gcongr
      _ = M θ := by simp only [hM]; field_simp; ring
  have hcw : ContinuousOn (fun θ => |Real.log m - nsRamp θ|) (Icc 1 b) := fun θ hθ =>
    (continuousAt_const.sub (continuousOn_nsRamp.continuousAt (Ioi_mem_nhds (by linarith [hθ.1])))).abs.continuousWithinAt
  have hcw' : ContinuousOn nsRamp' (Icc 1 b) := continuousOn_nsRamp'.mono fun θ hθ => mem_Ioi.mpr (by linarith [hθ.1])
  have hpow : ∀ k : ℕ, ContinuousOn (fun θ : ℝ => θ ^ k) (Icc 1 b) := fun k => (continuous_pow k).continuousOn
  have hne : ∀ k : ℕ, ∀ θ ∈ Icc (1 : ℝ) b, θ ^ k ≠ 0 := fun k θ hθ => pow_ne_zero k (by linarith [hθ.1])
  have hi1 : IntervalIntegrable (fun θ => nsRamp' θ / θ ^ 2) MeasureTheory.volume 1 b :=
    ContinuousOn.intervalIntegrable_of_Icc hb (hcw'.div (hpow 2) (hne 2))
  have hi3 : IntervalIntegrable (fun θ => |Real.log m - nsRamp θ| / θ ^ 3) MeasureTheory.volume 1 b :=
    ContinuousOn.intervalIntegrable_of_Icc hb (hcw.div (hpow 3) (hne 3))
  have hi5 : IntervalIntegrable (fun θ => |Real.log m - nsRamp θ| / θ ^ 5) MeasureTheory.volume 1 b :=
    ContinuousOn.intervalIntegrable_of_Icc hb (hcw.div (hpow 5) (hne 5))
  have hMi : IntervalIntegrable M MeasureTheory.volume 1 b :=
    ((hi1.add (hi3.const_mul 2)).add (hi5.const_mul (CM m))).const_mul (cutG m n 1)
  have hRi : IntervalIntegrable (fun θ => remDensity nsRamp nsRamp' m n θ) MeasureTheory.volume 1 b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hb
    refine continuousOn_remDensity (continuousOn_nsRamp.mono fun θ hθ => mem_Ioi.mpr (by linarith [hθ.1])) hcw'
      (fun θ hθ => ?_) (fun θ hθ => ?_) (fun θ hθ => cutGamma_pos_of_two_le hm2 hmn' hθ.1)
    · have h1 : (1 : ℝ) ≤ θ := hθ.1
      have : (1 : ℝ) ≤ θ ^ 2 := by nlinarith
      nlinarith
    · have h1 : (1 : ℝ) ≤ θ := hθ.1
      have : (1 : ℝ) ≤ θ ^ 2 := by nlinarith
      nlinarith
  have hle := intervalIntegral.integral_mono_on hb hRi hMi hpt
  have hMint : ∫ θ in (1 : ℝ)..b, M θ = cutG m n 1 * ((∫ θ in (1 : ℝ)..b, nsRamp' θ / θ ^ 2)
      + 2 * (∫ θ in (1 : ℝ)..b, |Real.log m - nsRamp θ| / θ ^ 3)
      + CM m * ∫ θ in (1 : ℝ)..b, |Real.log m - nsRamp θ| / θ ^ 5) := by
    simp only [hM]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hi1.add (hi3.const_mul 2))
      (hi5.const_mul _), intervalIntegral.integral_add hi1 (hi3.const_mul 2), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hJ1 := integral_nsRamp'_div_sq_le hb
  have hJ2 := integral_abs_div_pow3_le hm hb
  have hJ3 := integral_abs_div_pow5_le hm hb
  have hbound : (∫ θ in (1 : ℝ)..b, nsRamp' θ / θ ^ 2) + 2 * (∫ θ in (1 : ℝ)..b, |Real.log m - nsRamp θ| / θ ^ 3)
      + CM m * (∫ θ in (1 : ℝ)..b, |Real.log m - nsRamp θ| / θ ^ 5) ≤ PhiBar m := by
    rw [PhiBar_eq]
    nlinarith [mul_le_mul_of_nonneg_left hJ3 hC0]
  rw [hMint] at hle
  nlinarith [mul_le_mul_of_nonneg_left hbound hG1]

/-- **The rows `m ≥ 2` of `κ(X)`**: each is at most `2σ_mΦ̄_m`. -/
theorem kap_row_le {m : ℕ} (hm : 2 ≤ m) (X : ℝ) :
    ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => m < n),
        2 * ∫ θ in cutLo (5 / 4) m..cutHi (5 / 4) X m n, remDensity nsRamp nsRamp' m n θ
      ≤ 2 * sigma m * PhiBar m := by
  have hm1 : m ≠ 1 := by omega
  have hlo : cutLo (5 / 4) m = 1 := if_neg hm1
  have hP := PhiBar_nonneg hm
  have hterm : ∀ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => m < n),
      2 * ∫ θ in cutLo (5 / 4) m..cutHi (5 / 4) X m n, remDensity nsRamp nsRamp' m n θ
        ≤ 2 * PhiBar m * cutG m n 1 := by
    intro n hn
    have hmn := (Finset.mem_filter.mp hn).2
    have hhi : 1 ≤ cutHi (5 / 4) X m n := by unfold cutHi; rw [hlo]; exact le_max_left _ _
    rw [hlo]
    have := two_mul_integral_remDensity_le hm hmn hhi
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have := sum_cutG_one_le hm ⌊X⌋₊
  nlinarith

/-- `Σ_{m≥2} σ_mΦ̄_m` converges. -/
theorem summable_sigma_mul_PhiBar : Summable fun m : ℕ => if 2 ≤ m then sigma m * PhiBar m else 0 := by
  have hJ := J1bar_nonneg
  refine (summable_one_add_log_sq.mul_left (4 / 3 * (1 + π ^ 2 / 6) * (109 / 66 + J1bar + 1))).of_nonneg_of_le
    (fun m => by
      split_ifs with h
      · exact mul_nonneg (sigma_nonneg m) (PhiBar_nonneg h)
      · exact le_rfl) fun m => ?_
  split_ifs with hm
  · have hl : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    have hs := sigma_le hm
    have hs0 := sigma_nonneg m
    have hP := PhiBar_le hm
    have hP0 := PhiBar_nonneg hm
    have hpi : 0 ≤ π ^ 2 / 6 := by positivity
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hsig : sigma m ≤ 4 / 3 * (1 + π ^ 2 / 6) * ((1 + Real.log m) / (m : ℝ) ^ 2) := by
      refine hs.trans ?_
      rw [show 4 / 3 * (1 + π ^ 2 / 6) * ((1 + Real.log m) / (m : ℝ) ^ 2)
          = 4 / 3 * ((1 + π ^ 2 / 6) * (1 + Real.log m)) / (m : ℝ) ^ 2 by ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg hl hpi]
    have hPle : PhiBar m ≤ (109 / 66 + J1bar + 1) * (1 + Real.log m) := by nlinarith
    calc sigma m * PhiBar m ≤ (4 / 3 * (1 + π ^ 2 / 6) * ((1 + Real.log m) / (m : ℝ) ^ 2))
          * ((109 / 66 + J1bar + 1) * (1 + Real.log m)) := mul_le_mul hsig hPle hP0 (by positivity)
      _ = 4 / 3 * (1 + π ^ 2 / 6) * (109 / 66 + J1bar + 1) * ((1 + Real.log m) ^ 2 / (m : ℝ) ^ 2) := by ring
  · have : 0 ≤ (1 + Real.log m) ^ 2 / (m : ℝ) ^ 2 := by positivity
    have : 0 ≤ 4 / 3 * (1 + π ^ 2 / 6) * (109 / 66 + J1bar + 1) := by positivity
    positivity

theorem kappaBar2_nonneg : 0 ≤ kappaBar2 := by
  unfold kappaBar2
  refine mul_nonneg (by norm_num) (tsum_nonneg fun m => ?_)
  split_ifs with h
  · exact mul_nonneg (sigma_nonneg m) (PhiBar_nonneg h)
  · exact le_rfl

theorem hasDerivAt_inv_sq_half {θ : ℝ} (hθ : θ ≠ 0) :
    HasDerivAt (fun x : ℝ => -(1 / x ^ 2) / 2) (1 / θ ^ 3) θ := by
  have h0 := (hasDerivAt_const θ (1 : ℝ)).div (hasDerivAt_pow 2 θ) (pow_ne_zero 2 hθ)
  have h := h0.neg.div_const 2
  refine h.congr_deriv ?_
  norm_num
  field_simp

/-- On `[u, v] ⊆ [1, ∞)`, `f ≤ F(ω' + ωA)` with `F ≤ F(u)`, `A ≤ A(u)` integrates to at most `F(u)(ω(v) − ω(u) + A(u)ω(v)(v − u))`. -/
theorem integral_le_ramp_cell {f F A : ℝ → ℝ} {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v)
    (hfi : IntervalIntegrable f MeasureTheory.volume u v)
    (hfle : ∀ θ ∈ Icc u v, f θ ≤ F θ * (nsRamp' θ + nsRamp θ * A θ))
    (hF0 : ∀ θ ∈ Icc u v, 0 ≤ F θ) (hA0 : ∀ θ ∈ Icc u v, 0 ≤ A θ)
    (hFu : ∀ θ ∈ Icc u v, F θ ≤ F u) (hAu : ∀ θ ∈ Icc u v, A θ ≤ A u) :
    ∫ θ in u..v, f θ ≤ F u * (nsRamp v - nsRamp u + A u * nsRamp v * (v - u)) := by
  have hu0 : 0 < u := by linarith
  have hd : ∀ θ ∈ uIcc u v, HasDerivAt nsRamp (nsRamp' θ) θ := fun θ hθ => by
    rw [uIcc_of_le huv] at hθ
    exact hasDerivAt_nsRamp (by linarith [hθ.1])
  have hc' : ContinuousOn nsRamp' (uIcc u v) :=
    continuousOn_nsRamp'.mono fun θ hθ => by
      rw [uIcc_of_le huv] at hθ
      exact mem_Ioi.mpr (by linarith [hθ.1])
  have hgi : IntervalIntegrable (fun θ => F u * nsRamp' θ + F u * A u * nsRamp v) MeasureTheory.volume u v :=
    ((hc'.intervalIntegrable).const_mul (F u)).add intervalIntegrable_const
  have hle : ∀ θ ∈ Icc u v, f θ ≤ F u * nsRamp' θ + F u * A u * nsRamp v := by
    intro θ hθ
    have h1 : 1 ≤ θ := le_trans hu hθ.1
    have hw' := nsRamp'_nonneg h1
    have hw := nsRamp_nonneg h1
    have hwv : nsRamp θ ≤ nsRamp v :=
      nsRamp_monotoneOn (mem_Ici.mpr h1) (mem_Ici.mpr (le_trans hu huv)) hθ.2
    have hF := hFu θ hθ
    have hA := hAu θ hθ
    have hF0θ := hF0 θ hθ
    have hA0θ := hA0 θ hθ
    have hFu0 := hF0 u ⟨le_rfl, huv⟩
    have hAu0 := hA0 u ⟨le_rfl, huv⟩
    calc f θ ≤ F θ * (nsRamp' θ + nsRamp θ * A θ) := hfle θ hθ
      _ = F θ * nsRamp' θ + F θ * (nsRamp θ * A θ) := by ring
      _ ≤ F u * nsRamp' θ + F u * (nsRamp v * A u) := by
          have := nsRamp_nonneg (le_trans hu huv)
          gcongr
      _ = F u * nsRamp' θ + F u * A u * nsRamp v := by ring
  calc ∫ θ in u..v, f θ ≤ ∫ θ in u..v, (F u * nsRamp' θ + F u * A u * nsRamp v) :=
        intervalIntegral.integral_mono_on huv hfi hgi hle
    _ = F u * (nsRamp v - nsRamp u) + F u * A u * nsRamp v * (v - u) := by
        rw [intervalIntegral.integral_add ((hc'.intervalIntegrable).const_mul (F u)) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc'.intervalIntegrable,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ = F u * (nsRamp v - nsRamp u + A u * nsRamp v * (v - u)) := by ring

/-- On `[u, v] ⊆ [3/2, ∞)`, `θ²F` and `θA` nonincreasing give `∫f ≤ F(u)u²((u⁻² − v⁻²)/2 + A(u)u(L₃(u) − L₃(v)))`. -/
theorem integral_le_tail_cell {f F A : ℝ → ℝ} {u v : ℝ} (hu : 3 / 2 ≤ u) (huv : u ≤ v)
    (hfi : IntervalIntegrable f MeasureTheory.volume u v)
    (hfle : ∀ θ ∈ Icc u v, f θ ≤ F θ * (nsRamp' θ + nsRamp θ * A θ))
    (hF0 : ∀ θ ∈ Icc u v, 0 ≤ F θ) (hA0 : ∀ θ ∈ Icc u v, 0 ≤ A θ)
    (hFu : ∀ θ ∈ Icc u v, θ ^ 2 * F θ ≤ u ^ 2 * F u) (hAu : ∀ θ ∈ Icc u v, θ * A θ ≤ u * A u) :
    ∫ θ in u..v, f θ ≤ F u * u ^ 2 * ((1 / u ^ 2 - 1 / v ^ 2) / 2 + A u * u * (L3 u - L3 v)) := by
  have hu0 : 0 < u := by linarith
  have hpos : ∀ θ ∈ uIcc u v, 0 < θ := fun θ hθ => by
    rw [uIcc_of_le huv] at hθ; linarith [hθ.1]
  have hc3 : ContinuousOn (fun θ : ℝ => 1 / θ ^ 3) (uIcc u v) := fun θ hθ =>
    (continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 (hpos θ hθ).ne')).continuousWithinAt
  have hcl : ContinuousOn (fun θ : ℝ => Real.log θ / θ ^ 3) (uIcc u v) := fun θ hθ =>
    ((Real.continuousAt_log (hpos θ hθ).ne').div (continuousAt_id.pow 3)
      (pow_ne_zero 3 (hpos θ hθ).ne')).continuousWithinAt
  set K1 := F u * u ^ 2
  set K2 := F u * A u * u ^ 3
  have hgi : IntervalIntegrable (fun θ => K1 * (1 / θ ^ 3) + K2 * (Real.log θ / θ ^ 3)) MeasureTheory.volume u v :=
    (hc3.intervalIntegrable.const_mul K1).add (hcl.intervalIntegrable.const_mul K2)
  have hle : ∀ θ ∈ Icc u v, f θ ≤ K1 * (1 / θ ^ 3) + K2 * (Real.log θ / θ ^ 3) := by
    intro θ hθ
    have hθ0 : 0 < θ := by linarith [hθ.1]
    have h32 : 3 / 2 ≤ θ := le_trans hu hθ.1
    have hl := Real.log_nonneg (by linarith : (1 : ℝ) ≤ θ)
    have hFθ : F θ ≤ u ^ 2 * F u / θ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith [hFu θ hθ]
    have hAθ : A θ ≤ u * A u / θ := by
      rw [le_div_iff₀ hθ0]; linarith [hAu θ hθ]
    have hF0θ := hF0 θ hθ
    have hA0θ := hA0 θ hθ
    have hfθ := hfle θ hθ
    rw [nsRamp'_of_ge h32, nsRamp_of_ge h32] at hfθ
    calc f θ ≤ F θ * (1 / θ + Real.log θ * A θ) := hfθ
      _ ≤ (u ^ 2 * F u / θ ^ 2) * (1 / θ + Real.log θ * (u * A u / θ)) := by
          gcongr
          · exact le_trans hF0θ hFθ
      _ = K1 * (1 / θ ^ 3) + K2 * (Real.log θ / θ ^ 3) := by
          simp only [K1, K2]; field_simp
  calc ∫ θ in u..v, f θ ≤ ∫ θ in u..v, (K1 * (1 / θ ^ 3) + K2 * (Real.log θ / θ ^ 3)) :=
        intervalIntegral.integral_mono_on huv hfi hgi hle
    _ = K1 * ((1 / u ^ 2 - 1 / v ^ 2) / 2) + K2 * (L3 u - L3 v) := by
        rw [intervalIntegral.integral_add (hc3.intervalIntegrable.const_mul K1) (hcl.intervalIntegrable.const_mul K2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          integral_log_div_pow3 hu0 huv,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ hθ => hasDerivAt_inv_sq_half (hpos θ hθ).ne')
            hc3.intervalIntegrable]
        ring
    _ = F u * u ^ 2 * ((1 / u ^ 2 - 1 / v ^ 2) / 2 + A u * u * (L3 u - L3 v)) := by
        simp only [K1, K2]; ring

end Cvs.L2a.CutRemainderDensity
