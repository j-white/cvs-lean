import Mathlib
import Cvs.L2a.CutEstimateFrameFloor
import Cvs.L2a.CutGap
import Cvs.L2a.CutPointCountForm
import Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow
import Cvs.Upstream.SineSquaredRamp
import Cvs.Upstream.WeightedSchurHarmonicSums

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cut sums of the NS ramp, uniformly in `X`

`θ²g_mn(θ) = k(mθ)k(nθ)(mk(mθ) + nk(nθ))/(mnΓ_mn(θ))` decreases along every cut (`k(u) = u/√(u² − 1)`), the rows at
`θ = 1` telescope to `σ_m = k_m k_{m+1}(H_m + ζ(2)δ'_m)/m²`, and each `m = 1` top cut is at most `4φ̄/n²`: `CutPointCountForm`'s
`lamCount nsRamp (5/4) X ≤ 2S̄ + (2π²/3 − 4)φ̄` for every `X`, `S̄ = 2Σ log m·σ_m`, `φ̄ = 3 log(3/2)/(15/(4π) + 11/16)`.
-/

namespace Cvs.L2a.RampCutSumsUniform

open Real Set Cvs.L2a.CutGap Cvs.L2a.CutPointCountForm Cvs.L2a.CutEstimateFrameFloor

/-- `k(u) = u/√(u² − 1)`. -/
noncomputable def kU (u : ℝ) : ℝ := u / √(u ^ 2 - 1)

/-- `α(u) = u²/(u² − 1)`, which is `k(u)²` for `u > 1`. -/
noncomputable def aU (u : ℝ) : ℝ := u ^ 2 / (u ^ 2 - 1)

/-- The cut kernel `g_mn(θ) = (mK_m + nK_n)/(Γ_mn√(p_m p_n))`, so `cutCount ω m n θ = |log m − ω θ|·g_mn(θ)`. -/
noncomputable def cutG (m n θ : ℝ) : ℝ :=
  (m * cutK m θ + n * cutK n θ) / (cutGamma m n θ * √((m ^ 2 * θ ^ 2 - 1) * (n ^ 2 * θ ^ 2 - 1)))

/-- `g₁₂(θ) = [θ/√(4θ² − 1) + 4θ√(θ² − 1)/(4θ² − 1)]/(3θ² − 4)`, the kernel of the pair `(1, 2)`. -/
noncomputable def g12 (θ : ℝ) : ℝ :=
  (θ / √(4 * θ ^ 2 - 1) + 4 * θ * √(θ ^ 2 - 1) / (4 * θ ^ 2 - 1)) / (3 * θ ^ 2 - 4)

/-- `δ_m = mk_m − m`. -/
noncomputable def delM (m : ℕ) : ℝ := m * kU m - m

/-- `δ'_m = δ_m/(1 − δ_m)`. -/
noncomputable def delM' (m : ℕ) : ℝ := delM m / (1 - delM m)

/-- `σ_m = k_m k_{m+1}(H_m + ζ(2)δ'_m)/m²`, with `ζ(2) = π²/6`. -/
noncomputable def sigma (m : ℕ) : ℝ :=
  kU m * kU ((m : ℝ) + 1) * (Cvs.Upstream.WeightedSchurHarmonicSums.H m + π ^ 2 / 6 * delM' m) / (m : ℝ) ^ 2

/-- `S̄ = 2Σ_m log m·σ_m`; the terms `m = 0, 1` vanish. -/
noncomputable def SBar : ℝ := 2 * ∑' m : ℕ, Real.log m * sigma m

/-- `φ̄ = 3 log(3/2)/(15/(4π) + 11/16)`. -/
noncomputable def phiBar : ℝ := 3 * Real.log (3 / 2) / (15 / (4 * π) + 11 / 16)

/-- `Λ̄₀ = 2S̄ + (2π²/3 − 4)φ̄`. -/
noncomputable def LambdaBar0 : ℝ := 2 * SBar + (2 * π ^ 2 / 3 - 4) * phiBar

theorem cutGamma_eq (m n θ : ℝ) : cutGamma m n θ = n ^ 2 - m ^ 2 * aU (m * θ) := by
  unfold cutGamma aU; rw [mul_pow]; ring

theorem cutCount_eq (ω : ℝ → ℝ) (m n θ : ℝ) : cutCount ω m n θ = |Real.log m - ω θ| * cutG m n θ := by
  unfold cutCount cutG; ring

theorem kU_pos {u : ℝ} (hu : 1 < u) : 0 < kU u := by
  unfold kU
  have : 0 < u ^ 2 - 1 := by nlinarith
  positivity

theorem one_lt_kU {u : ℝ} (hu : 1 < u) : 1 < kU u := by
  unfold kU
  have hp : 0 < u ^ 2 - 1 := by nlinarith
  have hs : 0 < √(u ^ 2 - 1) := Real.sqrt_pos.2 hp
  rw [lt_div_iff₀ hs, one_mul]
  have : √(u ^ 2 - 1) < √(u ^ 2) := Real.sqrt_lt_sqrt hp.le (by linarith)
  rwa [Real.sqrt_sq (by linarith)] at this

theorem kU_sq {u : ℝ} (hu : 1 < u) : kU u ^ 2 = aU u := by
  unfold kU aU
  have hp : 0 < u ^ 2 - 1 := by nlinarith
  rw [div_pow, Real.sq_sqrt hp.le]

theorem kU_anti {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) : kU v ≤ kU u :=
  Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow.div_sqrt_antitone hu huv

theorem aU_anti {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) : aU v ≤ aU u := by
  unfold aU
  have h1 : 0 < u ^ 2 - 1 := by nlinarith
  have h2 : 0 < v ^ 2 - 1 := by nlinarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

theorem cutGamma_mono {m n a θ : ℝ} (hm : 0 < m) (hma : 1 < m * a) (haθ : a ≤ θ) :
    cutGamma m n a ≤ cutGamma m n θ := by
  rw [cutGamma_eq, cutGamma_eq]
  have := aU_anti hma (mul_le_mul_of_nonneg_left haθ hm.le)
  nlinarith [sq_nonneg m]

/-- `θ²g_mn(θ) = k(mθ)k(nθ)(mk(mθ) + nk(nθ))/(mnΓ_mn(θ))`. -/
theorem sq_mul_cutG_eq {m n θ : ℝ} (hm : 0 < m) (hn : 0 < n) (hθ : 0 < θ) (hmθ : 1 < m * θ)
    (hnθ : 1 < n * θ) :
    θ ^ 2 * cutG m n θ
      = kU (m * θ) * kU (n * θ) * (m * kU (m * θ) + n * kU (n * θ)) / (m * n * cutGamma m n θ) := by
  have hpm : 0 < m ^ 2 * θ ^ 2 - 1 := by nlinarith
  have hpn : 0 < n ^ 2 * θ ^ 2 - 1 := by nlinarith
  have hsm : 0 < √(m ^ 2 * θ ^ 2 - 1) := Real.sqrt_pos.2 hpm
  have hsn : 0 < √(n ^ 2 * θ ^ 2 - 1) := Real.sqrt_pos.2 hpn
  have ekm : kU (m * θ) = m * θ / √(m ^ 2 * θ ^ 2 - 1) := by unfold kU; rw [mul_pow]
  have ekn : kU (n * θ) = n * θ / √(n ^ 2 * θ ^ 2 - 1) := by unfold kU; rw [mul_pow]
  unfold cutG cutK
  rw [ekm, ekn, Real.sqrt_mul hpm.le]
  by_cases hΓ : cutGamma m n θ = 0
  · simp [hΓ]
  · field_simp

/-- **The cut kernel decreases along a cut**: `θ²g_mn(θ) ≤ a²g_mn(a)` for `1 < ma`, `a ≤ θ`. -/
theorem sq_mul_cutG_le {m n a θ : ℝ} (hm : 0 < m) (hmn : m ≤ n) (hma : 1 < m * a) (haθ : a ≤ θ)
    (hΓ : 0 < cutGamma m n a) : θ ^ 2 * cutG m n θ ≤ a ^ 2 * cutG m n a := by
  have hn : 0 < n := by linarith
  have ha : 0 < a := by
    by_contra h; push Not at h; nlinarith
  have hθ : 0 < θ := by linarith
  have hna : 1 < n * a := by nlinarith
  have hmθ : m * a ≤ m * θ := mul_le_mul_of_nonneg_left haθ hm.le
  have hnθ' : n * a ≤ n * θ := mul_le_mul_of_nonneg_left haθ hn.le
  rw [sq_mul_cutG_eq hm hn hθ (by linarith) (by linarith), sq_mul_cutG_eq hm hn ha hma hna]
  have h1 := kU_anti hma hmθ
  have h2 := kU_anti hna hnθ'
  have hk1 := kU_pos (by linarith : 1 < m * θ)
  have hk2 := kU_pos (by linarith : 1 < n * θ)
  have hΓθ := cutGamma_mono (n := n) hm hma haθ
  apply div_le_div₀ (by have := kU_pos hma; have := kU_pos hna; positivity)
  · apply mul_le_mul (mul_le_mul h1 h2 hk2.le (kU_pos hma).le) _ (by positivity)
      (by have := kU_pos hma; have := kU_pos hna; positivity)
    have := mul_le_mul_of_nonneg_left h1 hm.le
    have := mul_le_mul_of_nonneg_left h2 hn.le
    linarith
  · positivity
  · exact mul_le_mul_of_nonneg_left hΓθ (by positivity)

theorem cutG_nonneg {m n θ : ℝ} (hm : 0 < m) (hmn : m ≤ n) (hmθ : 1 < m * θ) (hΓ : 0 < cutGamma m n θ) :
    0 ≤ cutG m n θ := by
  have hθ : 0 < θ := by by_contra h; push Not at h; nlinarith
  have hn : 0 < n := by linarith
  have hnθ : 1 < n * θ := lt_of_lt_of_le hmθ (mul_le_mul_of_nonneg_right hmn hθ.le)
  unfold cutG cutK
  have hpm : 0 < m ^ 2 * θ ^ 2 - 1 := by nlinarith
  have hpn : 0 < n ^ 2 * θ ^ 2 - 1 := by nlinarith
  positivity

theorem delM_pos {m : ℕ} (hm : 2 ≤ m) : 0 < delM m := by
  unfold delM
  have hm' : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have := one_lt_kU hm'
  nlinarith

theorem delM_le_half {m : ℕ} (hm : 2 ≤ m) : delM m ≤ 1 / 2 := by
  unfold delM kU
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < √((m : ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hp
  have hss := Real.sq_sqrt hp.le
  -- m²/√(m²−1) ≤ m + 1/2 ⟺ m² ≤ (m + 1/2)√(m²−1); square both sides
  have key : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1 / 2) * √((m : ℝ) ^ 2 - 1) := by
    have h0 : 0 ≤ ((m : ℝ) + 1 / 2) * √((m : ℝ) ^ 2 - 1) := by positivity
    have hsq : ((m : ℝ) ^ 2) ^ 2 ≤ (((m : ℝ) + 1 / 2) * √((m : ℝ) ^ 2 - 1)) ^ 2 := by
      rw [mul_pow, hss]
      nlinarith [sq_nonneg ((m : ℝ) - 2)]
    exact le_of_pow_le_pow_left₀ two_ne_zero h0 hsq
  have h2 : (m : ℝ) * ((m : ℝ) / √((m : ℝ) ^ 2 - 1)) ≤ (m : ℝ) + 1 / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hs]; nlinarith [key]
  linarith

/-- At `θ = 1`, `g_mn(1) ≤ (k_m k_{m+1}/m²)(1/(n − mk_m) − 1/n)` for `2 ≤ m < n`. -/
theorem cutG_one_le {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    cutG m n 1 ≤ kU m * kU ((m : ℝ) + 1) / (m : ℝ) ^ 2 * (1 / ((n : ℝ) - m * kU m) - 1 / n) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hm0 : (0 : ℝ) < m := by linarith
  have hmn1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  have hn1 : (1 : ℝ) < n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  set k := kU m with hk
  set k1 := kU ((m : ℝ) + 1) with hk1
  set kn := kU n with hkn
  have hk1' : 1 < k := one_lt_kU hm1
  have hkn0 : 0 < kn := kU_pos hn1
  have hkn1 : kn ≤ k1 := kU_anti (by linarith) hmn1
  have hknk : kn ≤ k := kU_anti hm1 (by linarith)
  have hδ := delM_le_half hm
  unfold delM at hδ
  rw [← hk] at hδ
  set r := (m : ℝ) * k with hr
  have hnr : 0 < (n : ℝ) - r := by linarith
  have hmr : (m : ℝ) ≤ r := by rw [hr]; nlinarith
  have hΓ : cutGamma m n 1 = ((n : ℝ) - r) * ((n : ℝ) + r) := by
    rw [cutGamma_eq, mul_one, ← kU_sq hm1, ← hk, hr]; ring
  have hcut : cutG m n 1 = k * kn * (m * k + n * kn) / (m * n * (((n : ℝ) - r) * ((n : ℝ) + r))) := by
    have h := sq_mul_cutG_eq (m := (m : ℝ)) (n := (n : ℝ)) (θ := 1) hm0 hn0 one_pos (by simpa using hm1)
      (by simpa using hn1)
    simp only [one_pow, one_mul, mul_one] at h
    rw [h, hΓ]
  have hnum : k * kn * (m * k + n * kn) ≤ k * k * k1 * ((n : ℝ) + r) := by
    have h1 : (m : ℝ) * k + n * kn ≤ k * ((n : ℝ) + r) := by nlinarith
    calc k * kn * (m * k + n * kn) ≤ k * kn * (k * ((n : ℝ) + r)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ k * k1 * (k * ((n : ℝ) + r)) := by
          gcongr
      _ = k * k * k1 * ((n : ℝ) + r) := by ring
  have hnr' : 0 < (n : ℝ) + r := by positivity
  rw [hcut]
  calc k * kn * (m * k + n * kn) / (m * n * (((n : ℝ) - r) * ((n : ℝ) + r)))
      ≤ k * k * k1 * ((n : ℝ) + r) / (m * n * (((n : ℝ) - r) * ((n : ℝ) + r))) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = k * k1 / (m : ℝ) ^ 2 * (1 / ((n : ℝ) - r) - 1 / n) := by
        have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
        have hnr0 : (n : ℝ) - r ≠ 0 := hnr.ne'
        have e1 : k * k1 / (m : ℝ) ^ 2 * (1 / ((n : ℝ) - r) - 1 / n)
            = k * k1 * r / ((m : ℝ) ^ 2 * n * ((n : ℝ) - r)) := by
          field_simp; ring
        rw [e1, div_eq_div_iff (mul_pos (mul_pos hm0 hn0) (mul_pos hnr hnr')).ne'
          (mul_pos (mul_pos (by positivity) hn0) hnr).ne', hr]
        ring

/-- **The rows at `θ = 1`**: `Σ_{m<n≤J} g_mn(1) ≤ σ_m` for `m ≥ 2`. -/
theorem sum_cutG_one_le {m : ℕ} (hm : 2 ≤ m) (J : ℕ) :
    ∑ n ∈ (Finset.Icc 1 J).filter (fun n => m < n), cutG m n 1 ≤ sigma m := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hm0 : (0 : ℝ) < m := by linarith
  set c := kU m * kU ((m : ℝ) + 1) / (m : ℝ) ^ 2 with hc
  have hc0 : 0 ≤ c := by
    have := kU_pos hm1; have := kU_pos (by linarith : (1 : ℝ) < m + 1); positivity
  set δ := delM m with hδ
  have hδ0 : 0 < δ := delM_pos hm
  have hδ1 : δ ≤ 1 / 2 := delM_le_half hm
  set δ' := delM' m with hδ'
  have hδ'e : δ' = δ / (1 - δ) := rfl
  have hδ'0 : 0 ≤ δ' := by rw [hδ'e]; apply div_nonneg hδ0.le; linarith
  have hr : (m : ℝ) * kU m = m + δ := by rw [hδ]; unfold delM; ring
  have hfilter : (Finset.Icc 1 J).filter (fun n => m < n) = Finset.Ioc m J := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hfilter]
  -- termwise bound, then reindex `n = m + 1 + k`
  have hterm : ∀ n ∈ Finset.Ioc m J, cutG m n 1 ≤ c * (1 / ((n : ℝ) - m * kU m) - 1 / n) := fun n hn =>
    cutG_one_le hm (Finset.mem_Ioc.mp hn).1
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hkey : ∑ n ∈ Finset.Ioc m J, (1 / ((n : ℝ) - m * kU m) - 1 / n)
      ≤ Cvs.Upstream.WeightedSchurHarmonicSums.H m + π ^ 2 / 6 * δ' := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
    have hpt : ∀ k ∈ Finset.range (J + 1 - (m + 1)),
        1 / (((m + 1 + k : ℕ) : ℝ) - m * kU m) - 1 / ((m + 1 + k : ℕ) : ℝ)
          ≤ (m : ℝ) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + m))) + δ' * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
      intro k _
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast
      rw [hr]
      have e1 : (m : ℝ) + 1 + k - (m + δ) = (k + 1) - δ := by ring
      rw [e1]
      have hkd : 0 < (k : ℝ) + 1 - δ := by linarith
      have hkd' : ((k : ℝ) + 1) * (1 - δ) ≤ (k : ℝ) + 1 - δ := by nlinarith
      have h1 : 1 / ((k : ℝ) + 1 - δ) ≤ 1 / ((k : ℝ) + 1) + δ' * (1 / ((k : ℝ) + 1) ^ 2) := by
        rw [hδ'e]
        have h1δ : 0 < 1 - δ := by linarith
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
        have e : 1 / ((k : ℝ) + 1 - δ) = 1 / ((k : ℝ) + 1) + δ / (((k : ℝ) + 1) * ((k : ℝ) + 1 - δ)) := by
          field_simp; ring
        have e2 : δ / (1 - δ) * (1 / ((k : ℝ) + 1) ^ 2) = δ / ((1 - δ) * ((k : ℝ) + 1) ^ 2) := by
          field_simp
        have hb : δ / (((k : ℝ) + 1) * ((k : ℝ) + 1 - δ)) ≤ δ / ((1 - δ) * ((k : ℝ) + 1) ^ 2) := by
          apply div_le_div_of_nonneg_left hδ0.le (by positivity)
          nlinarith
        rw [e, e2]
        linarith
      have h2 : 1 / ((k : ℝ) + 1) - 1 / ((m : ℝ) + 1 + k) = (m : ℝ) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + m))) := by
        field_simp; ring
      linarith [h1, h2]
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hs1 := sum_le_hasSum (Finset.range (J + 1 - (m + 1))) (fun i _ => by positivity)
      (Cvs.Upstream.WeightedSchurHarmonicSums.hasSum_inv_mul_add (show 1 ≤ m by omega))
    have hs2 : ∑ i ∈ Finset.range (J + 1 - (m + 1)), (1 / ((i + 1 : ℕ) : ℝ) ^ 2) ≤ π ^ 2 / 6 := by
      have := sum_le_hasSum (Finset.range (J + 1 - (m + 1) + 1)) (fun i _ => by positivity) hasSum_zeta_two
      rw [Finset.sum_range_succ'] at this
      simpa using this
    have e : (m : ℝ) * (Cvs.Upstream.WeightedSchurHarmonicSums.H m / m) = Cvs.Upstream.WeightedSchurHarmonicSums.H m := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hs1 hm0.le, mul_le_mul_of_nonneg_left hs2 hδ'0]
  calc c * ∑ n ∈ Finset.Ioc m J, (1 / ((n : ℝ) - m * kU m) - 1 / n)
      ≤ c * (Cvs.Upstream.WeightedSchurHarmonicSums.H m + π ^ 2 / 6 * δ') := mul_le_mul_of_nonneg_left hkey hc0
    _ = sigma m := by rw [hc]; unfold sigma; ring

theorem sigma_nonneg (m : ℕ) : 0 ≤ sigma m := by
  rcases lt_or_ge m 2 with hm | hm
  · interval_cases m <;> simp [sigma, kU]
  · have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    have h1 := kU_pos hm1
    have h2 := kU_pos (by linarith : (1 : ℝ) < m + 1)
    have hd := delM_pos hm
    have hd2 := delM_le_half hm
    have hd' : 0 ≤ delM' m := div_nonneg hd.le (by linarith)
    have hH := Cvs.Upstream.WeightedSchurHarmonicSums.H_nonneg m
    unfold sigma
    positivity

/-- `σ_m ≤ (4/3)(1 + log m + ζ(2))/m²` for `m ≥ 2`. -/
theorem sigma_le {m : ℕ} (hm : 2 ≤ m) : sigma m ≤ 4 / 3 * (1 + Real.log m + π ^ 2 / 6) / (m : ℝ) ^ 2 := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) < m := by linarith
  have h1 := kU_pos hm1
  have h2 := kU_pos (by linarith : (1 : ℝ) < m + 1)
  have hk : kU ((m : ℝ) + 1) ≤ kU m := kU_anti hm1 (by linarith)
  have hkk : kU m * kU ((m : ℝ) + 1) ≤ 4 / 3 := by
    have hsq : kU m * kU m = aU m := by rw [← sq, kU_sq hm1]
    have ha : aU m ≤ aU 2 := aU_anti (by norm_num) hm2
    have ha2 : aU 2 = 4 / 3 := by unfold aU; norm_num
    nlinarith
  have hd := delM_pos hm
  have hd2 := delM_le_half hm
  have hd'1 : delM' m ≤ 1 := by
    unfold delM'; rw [div_le_one (by linarith)]; linarith
  have hd'0 : 0 ≤ delM' m := div_nonneg hd.le (by linarith)
  have hH := Cvs.Upstream.WeightedSchurHarmonicSums.H_le m
  have hH0 := Cvs.Upstream.WeightedSchurHarmonicSums.H_nonneg m
  unfold sigma
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hpi : 0 ≤ π ^ 2 / 6 := by positivity
  calc kU m * kU ((m : ℝ) + 1) * (Cvs.Upstream.WeightedSchurHarmonicSums.H m + π ^ 2 / 6 * delM' m)
      ≤ 4 / 3 * (Cvs.Upstream.WeightedSchurHarmonicSums.H m + π ^ 2 / 6 * delM' m) :=
        mul_le_mul_of_nonneg_right hkk (by positivity)
    _ ≤ 4 / 3 * (1 + Real.log m + π ^ 2 / 6) := by
        gcongr
        nlinarith

/-- `Σ_m (1 + log m)²/m²` converges. -/
theorem summable_one_add_log_sq : Summable fun m : ℕ => (1 + Real.log m) ^ 2 / (m : ℝ) ^ 2 := by
  have hb : Summable fun m : ℕ => 25 * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 25
  refine hb.of_nonneg_of_le (fun m => by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have : (0 : ℝ) ≤ Real.log m := Real.log_natCast_nonneg m
      positivity) fun m => ?_
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast h
  have hm0 : (0 : ℝ) < m := by linarith
  set t := (m : ℝ) ^ (1 / 4 : ℝ) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hm (by norm_num)
  have hlog : Real.log m ≤ 4 * t := by
    have := Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← ht] at this; linarith
  have hl0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have ht4 : t ^ 4 = m := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
  have h32 : (m : ℝ) ^ (3 / 2 : ℝ) = m * t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le, show (3 / 2 : ℝ) = 1 + 1 / 4 * (2 : ℕ) by norm_num,
      Real.rpow_add hm0, Real.rpow_one]
  rw [h32, div_le_iff₀ (by positivity)]
  have hsq : (1 + Real.log m) ^ 2 ≤ 25 * t ^ 2 := by nlinarith
  have hpos : 0 < (m : ℝ) * t ^ 2 := by positivity
  rw [mul_inv, ← mul_assoc]
  calc (1 + Real.log m) ^ 2 ≤ 25 * t ^ 2 := hsq
    _ = 25 * (m : ℝ)⁻¹ * (t ^ 2)⁻¹ * (m : ℝ) ^ 2 := by
        field_simp
        nlinarith [ht4]

theorem summable_log_mul_sigma : Summable fun m : ℕ => Real.log m * sigma m := by
  refine (summable_one_add_log_sq.mul_left (4 / 3 * (1 + π ^ 2 / 6))).of_nonneg_of_le
    (fun m => mul_nonneg (Real.log_natCast_nonneg m) (sigma_nonneg m)) fun m => ?_
  rcases lt_or_ge m 2 with hm | hm
  · interval_cases m <;> simp
    all_goals positivity
  have hl0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hs := sigma_le hm
  have hpi : 0 ≤ π ^ 2 / 6 := by positivity
  calc Real.log m * sigma m ≤ Real.log m * (4 / 3 * (1 + Real.log m + π ^ 2 / 6) / (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hs hl0
    _ ≤ 4 / 3 * (1 + π ^ 2 / 6) * ((1 + Real.log m) ^ 2 / (m : ℝ) ^ 2) := by
        rw [mul_div_assoc', mul_div_assoc']
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_nonneg hl0 hpi, mul_nonneg (mul_nonneg hl0 hl0) hpi]

/-- `g_1n(θ) = [k(nθ)/(n(θ² − 1)) + α(nθ)/(θ√(θ² − 1))]/Γ_1n(θ)`. -/
theorem cutG_one_eq {n θ : ℝ} (hn : 0 < n) (hθ : 1 < θ) (hnθ : 1 < n * θ) :
    cutG 1 n θ = (kU (n * θ) / (n * (θ ^ 2 - 1)) + aU (n * θ) / (θ * √(θ ^ 2 - 1))) / cutGamma 1 n θ := by
  have hθ0 : 0 < θ := by linarith
  have hp : 0 < θ ^ 2 - 1 := by nlinarith
  have hpn : 0 < n ^ 2 * θ ^ 2 - 1 := by nlinarith
  by_cases hΓ : cutGamma 1 n θ = 0
  · simp [cutG, hΓ]
  have e1 : (1 : ℝ) ^ 2 * θ ^ 2 - 1 = θ ^ 2 - 1 := by ring
  unfold cutG cutK kU aU
  rw [mul_pow, e1, Real.sqrt_mul hp.le]
  set s1 := √(θ ^ 2 - 1) with hs1
  set sn := √(n ^ 2 * θ ^ 2 - 1) with hsn
  have hs1p : 0 < s1 := Real.sqrt_pos.2 hp
  have hsnp : 0 < sn := Real.sqrt_pos.2 hpn
  have h1 : θ ^ 2 - 1 = s1 ^ 2 := (Real.sq_sqrt hp.le).symm
  have h2 : n ^ 2 * θ ^ 2 - 1 = sn ^ 2 := (Real.sq_sqrt hpn.le).symm
  rw [show (1 : ℝ) * θ = θ by ring]
  rw [h1, h2]
  field_simp

theorem cutG_one_two_eq {θ : ℝ} (hθ : 1 < θ) : cutG 1 2 θ = g12 θ := by
  have hθ0 : 0 < θ := by linarith
  have hp : 0 < θ ^ 2 - 1 := by nlinarith
  have hq : 0 < 4 * θ ^ 2 - 1 := by nlinarith
  rw [cutG_one_eq two_pos hθ (by linarith)]
  have hΓ : cutGamma 1 2 θ = (3 * θ ^ 2 - 4) / (θ ^ 2 - 1) := by
    unfold cutGamma; field_simp; ring
  rw [hΓ]
  unfold g12 kU aU
  rw [mul_pow]
  have e4 : (2 : ℝ) ^ 2 * θ ^ 2 - 1 = 4 * θ ^ 2 - 1 := by ring
  rw [e4, show (2 : ℝ) ^ 2 = 4 by norm_num]
  set sp := √(θ ^ 2 - 1) with hsp
  set sq := √(4 * θ ^ 2 - 1) with hsq
  have hspp : 0 < sp := Real.sqrt_pos.2 hp
  have hsqp : 0 < sq := Real.sqrt_pos.2 hq
  have h1 : θ ^ 2 - 1 = sp ^ 2 := (Real.sq_sqrt hp.le).symm
  have h2 : 4 * θ ^ 2 - 1 = sq ^ 2 := (Real.sq_sqrt hq.le).symm
  by_cases h34 : 3 * θ ^ 2 - 4 = 0
  · simp [h34]
  rw [h1, h2]
  field_simp

/-- `g₁₂(θ) ≤ (3/2)/(3θ² − 4)` on `θ ≥ 5/4`. -/
theorem g12_le {θ : ℝ} (hθ : 5 / 4 ≤ θ) : g12 θ ≤ 3 / 2 / (3 * θ ^ 2 - 4) := by
  have hθ0 : 0 < θ := by linarith
  have hp : 0 < θ ^ 2 - 1 := by nlinarith
  have hq : 0 < 4 * θ ^ 2 - 1 := by nlinarith
  have h34 : 0 < 3 * θ ^ 2 - 4 := by nlinarith
  unfold g12
  apply div_le_div_of_nonneg_right _ h34.le
  set q := 4 * θ ^ 2 - 1 with hqdef
  have hsq : 0 < √q := Real.sqrt_pos.2 hq
  have hsq2 : √q ^ 2 = q := Real.sq_sqrt hq.le
  have hsp2 : √(θ ^ 2 - 1) ^ 2 = θ ^ 2 - 1 := Real.sq_sqrt hp.le
  have hsp0 : 0 ≤ √(θ ^ 2 - 1) := Real.sqrt_nonneg _
  -- θ/√q ≤ 1/2 + 1/(4q)
  have hA : θ / √q ≤ 1 / 2 + 1 / (4 * q) := by
    have h0 : 0 ≤ θ / √q := by positivity
    have hb : 0 ≤ 1 / 2 + 1 / (4 * q) := by positivity
    apply le_of_pow_le_pow_left₀ two_ne_zero hb
    rw [div_pow, hsq2, div_le_iff₀ hq]
    have : (1 / 2 + 1 / (4 * q)) ^ 2 * q = q / 4 + 1 / 4 + 1 / (16 * q) := by field_simp; ring
    rw [this]
    have : 0 < 1 / (16 * q) := by positivity
    nlinarith
  -- 4θ√(θ²−1)/q ≤ 1 − 1/q
  have hB : 4 * θ * √(θ ^ 2 - 1) / q ≤ 1 - 1 / q := by
    rw [div_le_iff₀ hq]
    have e : (1 - 1 / q) * q = q - 1 := by field_simp
    rw [e]
    have h0 : 0 ≤ 4 * θ * √(θ ^ 2 - 1) := by positivity
    have hb : 0 ≤ q - 1 := by nlinarith
    apply le_of_pow_le_pow_left₀ two_ne_zero hb
    rw [mul_pow, hsp2]
    nlinarith
  have : 0 < 1 / q := by positivity
  have : 1 / (4 * q) = 1 / q / 4 := by field_simp
  linarith

theorem g12_nonneg {θ : ℝ} (hθ : 5 / 4 ≤ θ) : 0 ≤ g12 θ := by
  unfold g12
  have : 0 < θ ^ 2 - 1 := by nlinarith
  have : 0 < 4 * θ ^ 2 - 1 := by nlinarith
  have : 0 < 3 * θ ^ 2 - 4 := by nlinarith
  have : 0 < θ := by linarith
  positivity

/-- `g_1n ≤ (4/n²)g₁₂` on `θ ≥ 5/4`. -/
theorem cutG_one_le_two {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (hθ : 5 / 4 ≤ θ) :
    cutG 1 n θ ≤ 4 / (n : ℝ) ^ 2 * g12 θ := by
  have hθ1 : 1 < θ := by linarith
  have hθ0 : 0 < θ := by linarith
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hp : 0 < θ ^ 2 - 1 := by nlinarith
  rw [← cutG_one_two_eq hθ1, cutG_one_eq hn0 hθ1 (by nlinarith), cutG_one_eq two_pos hθ1 (by linarith)]
  have hΓe : ∀ k : ℝ, cutGamma 1 k θ = k ^ 2 - aU θ := fun k => by rw [cutGamma_eq]; simp
  rw [hΓe, hΓe]
  have haθ : 0 ≤ aU θ := by unfold aU; positivity
  have ha4 : aU θ < 4 := by
    unfold aU; rw [div_lt_iff₀ hp]; nlinarith
  have hΓ2 : 0 < (2 : ℝ) ^ 2 - aU θ := by linarith
  have hΓn : (n : ℝ) ^ 2 / 4 * ((2 : ℝ) ^ 2 - aU θ) ≤ (n : ℝ) ^ 2 - aU θ := by
    nlinarith [mul_nonneg haθ (by nlinarith : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 4 - 1)]
  have hk : kU (n * θ) ≤ kU (2 * θ) := kU_anti (by linarith) (by nlinarith)
  have ha : aU (n * θ) ≤ aU (2 * θ) := aU_anti (by linarith) (by nlinarith)
  have hk0 : 0 ≤ kU (n * θ) := (kU_pos (by nlinarith)).le
  have ha0 : 0 ≤ aU (n * θ) := by unfold aU; have : 0 < (n * θ) ^ 2 - 1 := by nlinarith
                                  positivity
  have hsp : 0 < √(θ ^ 2 - 1) := Real.sqrt_pos.2 hp
  have hk2 : 0 ≤ kU (2 * θ) := (kU_pos (by linarith)).le
  have hnum : kU (n * θ) / (n * (θ ^ 2 - 1)) + aU (n * θ) / (θ * √(θ ^ 2 - 1))
      ≤ kU (2 * θ) / (2 * (θ ^ 2 - 1)) + aU (2 * θ) / (θ * √(θ ^ 2 - 1)) := by
    gcongr
  have hnum0 : 0 ≤ kU (n * θ) / (n * (θ ^ 2 - 1)) + aU (n * θ) / (θ * √(θ ^ 2 - 1)) := by positivity
  calc (kU (n * θ) / (n * (θ ^ 2 - 1)) + aU (n * θ) / (θ * √(θ ^ 2 - 1))) / ((n : ℝ) ^ 2 - aU θ)
      ≤ (kU (2 * θ) / (2 * (θ ^ 2 - 1)) + aU (2 * θ) / (θ * √(θ ^ 2 - 1)))
          / ((n : ℝ) ^ 2 / 4 * ((2 : ℝ) ^ 2 - aU θ)) :=
        div_le_div₀ (le_trans hnum0 hnum) hnum (by positivity) hΓn
    _ = 4 / (n : ℝ) ^ 2 * ((kU (2 * θ) / (2 * (θ ^ 2 - 1)) + aU (2 * θ) / (θ * √(θ ^ 2 - 1)))
          / ((2 : ℝ) ^ 2 - aU θ)) := by
        field_simp

/-- `3ω(θ) ≤ φ̄(3θ² − 4)` on `θ ≥ 5/4` for the NS ramp. -/
theorem three_mul_nsRamp_le {θ : ℝ} (hθ : 5 / 4 ≤ θ) : 3 * nsRamp θ ≤ phiBar * (3 * θ ^ 2 - 4) := by
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  set K := 15 / (4 * π) + 11 / 16 with hKdef
  have hK : 0 < K := by positivity
  have hL0 : 1 / 3 ≤ Real.log (3 / 2) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    norm_num at this ⊢; linarith
  have hKle : K ≤ 31 / 16 := by
    have : 15 / (4 * π) ≤ 5 / 4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hθ0 : 0 < θ := by linarith
  unfold phiBar
  rw [← hKdef, div_mul_eq_mul_div, le_div_iff₀ hK]
  rcases le_or_gt (3 / 2) θ with h32 | h32
  · rw [nsRamp_of_ge h32]
    have hlog : Real.log θ ≤ Real.log (3 / 2) + (2 * θ / 3 - 1) := by
      have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * θ / 3)
      have e : Real.log θ = Real.log (3 / 2) + Real.log (2 * θ / 3) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
      linarith
    have hlogθ : 0 ≤ Real.log θ := Real.log_nonneg (by linarith)
    have hc : 0 ≤ 2 * θ / 3 - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hKle hc, mul_le_mul_of_nonneg_right hlog hK.le,
      mul_le_mul_of_nonneg_right hL0 (by nlinarith : (0 : ℝ) ≤ 3 * θ ^ 2 - 4 - K)]
  · have hlog : Real.log θ ≤ Real.log (3 / 2) := Real.log_le_log hθ0 h32.le
    have hlogθ : 0 ≤ Real.log θ := Real.log_nonneg (by linarith)
    have hL : 0 ≤ Real.log (3 / 2) := by linarith
    -- the ramp value
    set s := Cvs.Upstream.SineSquaredRamp.ramp (5 / 4) (1 / 4) θ with hs
    have hs0 : 0 ≤ s := Cvs.Upstream.SineSquaredRamp.ramp_nonneg _ _ _
    have hsK : s * K ≤ 3 * θ ^ 2 - 4 := by
      rw [hs]
      unfold Cvs.Upstream.SineSquaredRamp.ramp
      split_ifs with h1 h2
      · nlinarith
      · set u := π * (θ - 5 / 4) / (2 * (1 / 4)) with hu
        have hu0 : 0 ≤ u := by rw [hu]; apply div_nonneg (mul_nonneg hpi0.le (by linarith)) (by norm_num)
        have hs1 : Real.sin u ^ 2 ≤ 1 := Real.sin_sq_le_one u
        have hsu : Real.sin u ^ 2 ≤ u := by
          have ha := Real.abs_sin_le_one u
          have hb : |Real.sin u| ≤ u := by simpa [abs_of_nonneg hu0] using (Real.abs_sin_le_abs (x := u))
          have : Real.sin u ^ 2 = |Real.sin u| * |Real.sin u| := by rw [← sq_abs, sq]
          rw [this]
          calc |Real.sin u| * |Real.sin u| ≤ 1 * |Real.sin u| := by gcongr
            _ ≤ u := by linarith
        have hku : u * (15 / (4 * π)) = 15 / 2 * (θ - 5 / 4) := by rw [hu]; field_simp
        have hsq : 0 ≤ Real.sin u ^ 2 := sq_nonneg _
        have : Real.sin u ^ 2 * K = Real.sin u ^ 2 * (15 / (4 * π)) + Real.sin u ^ 2 * (11 / 16) := by
          rw [hKdef]; ring
        rw [this]
        have hpos : 0 ≤ 15 / (4 * π) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hsu hpos, sq_nonneg (θ - 5 / 4)]
      · exact absurd h32 (by linarith)
    have hnr : nsRamp θ = Real.log θ * s := rfl
    rw [hnr]
    have h1 : 3 * (Real.log θ * s) * K ≤ 3 * Real.log (3 / 2) * (s * K) := by
      have := mul_le_mul_of_nonneg_right hlog (mul_nonneg hs0 hK.le)
      nlinarith
    have h2 : 3 * Real.log (3 / 2) * (s * K) ≤ 3 * Real.log (3 / 2) * (3 * θ ^ 2 - 4) :=
      mul_le_mul_of_nonneg_left hsK (by positivity)
    linarith

/-- Each `m = 1` top cut: `2·cutCount(1, n, θ) ≤ 4φ̄/n²` on `θ ≥ 5/4`. -/
theorem two_mul_cutCount_one_le {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (hθ : 5 / 4 ≤ θ) :
    2 * cutCount nsRamp 1 n θ ≤ 4 / (n : ℝ) ^ 2 * phiBar := by
  have hθ1 : 1 ≤ θ := by linarith
  have h34 : 0 < 3 * θ ^ 2 - 4 := by nlinarith
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hw0 := nsRamp_nonneg hθ1
  rw [cutCount_eq, Real.log_one, zero_sub, abs_neg, abs_of_nonneg hw0]
  have h1 := cutG_one_le_two hn hθ
  have h2 := g12_le hθ
  have h3 := three_mul_nsRamp_le hθ
  have hn0 : 0 < 4 / (n : ℝ) ^ 2 := by positivity
  have hg0 : 0 ≤ g12 θ := by
    unfold g12
    have : 0 < θ ^ 2 - 1 := by nlinarith
    have : 0 < 4 * θ ^ 2 - 1 := by nlinarith
    positivity
  calc 2 * (nsRamp θ * cutG 1 n θ) ≤ 2 * (nsRamp θ * (4 / (n : ℝ) ^ 2 * (3 / 2 / (3 * θ ^ 2 - 4)))) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hn0.le)
    _ = 4 / (n : ℝ) ^ 2 * (3 * nsRamp θ / (3 * θ ^ 2 - 4)) := by field_simp
    _ ≤ 4 / (n : ℝ) ^ 2 * phiBar := by
        gcongr
        rw [div_le_iff₀ h34]; exact h3

/-- `|log m − ω(θ)|/θ² ≤ log m` for `m ≥ 2`, `θ ≥ 1`. -/
theorem abs_log_sub_nsRamp_div_sq_le {m : ℕ} (hm : 2 ≤ m) {θ : ℝ} (hθ : 1 ≤ θ) :
    |Real.log m - nsRamp θ| / θ ^ 2 ≤ Real.log m := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hθ0 : 0 < θ := by linarith
  have hθ2 : 1 ≤ θ ^ 2 := by nlinarith
  have hlm : 1 / 2 ≤ Real.log m := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < m)
    have : (m : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hm2
    linarith
  have hw0 := nsRamp_nonneg hθ
  have hwl := nsRamp_le_log hθ
  rw [div_le_iff₀ (by positivity)]
  rcases le_total (nsRamp θ) (Real.log m) with h | h
  · rw [abs_of_nonneg (by linarith)]
    nlinarith
  · rw [abs_of_nonpos (by linarith)]
    have hlog : Real.log θ - Real.log m ≤ θ / m - 1 := by
      rw [← Real.log_div hθ0.ne' (by positivity)]
      exact Real.log_le_sub_one_of_pos (by positivity)
    have : θ / m ≤ θ / 2 := div_le_div_of_nonneg_left hθ0.le (by norm_num) hm2
    nlinarith

theorem cutCount_nsRamp_one (m n : ℕ) : cutCount nsRamp m n 1 = Real.log m * cutG m n 1 := by
  rw [cutCount_eq, nsRamp_of_le (by norm_num), sub_zero, abs_of_nonneg (Real.log_natCast_nonneg m)]

/-- For `m ≥ 2` a cut at `θ ≥ 1` weighs at most the cut at `θ = 1`. -/
theorem cutCount_nsRamp_le_one {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) {θ : ℝ} (hθ : 1 ≤ θ) :
    cutCount nsRamp m n θ ≤ cutCount nsRamp m n 1 := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  have hθ0 : 0 < θ := by linarith
  have hΓ1 : 0 < cutGamma m n 1 := cutGamma_pos_of_two_le hm2 hmn' le_rfl
  have hsq := sq_mul_cutG_le (m := (m : ℝ)) (n := (n : ℝ)) (a := 1) (θ := θ) (by linarith) (by linarith)
    (by linarith) hθ hΓ1
  have hG0 : 0 ≤ cutG m n θ := cutG_nonneg (by linarith) (by linarith) (by nlinarith)
    (cutGamma_pos_of_two_le hm2 hmn' hθ)
  have hw := abs_log_sub_nsRamp_div_sq_le hm hθ
  rw [cutCount_nsRamp_one, cutCount_eq]
  have e : |Real.log m - nsRamp θ| * cutG m n θ = (|Real.log m - nsRamp θ| / θ ^ 2) * (θ ^ 2 * cutG m n θ) := by
    field_simp
  rw [e]
  have hl0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  calc (|Real.log m - nsRamp θ| / θ ^ 2) * (θ ^ 2 * cutG m n θ) ≤ Real.log m * (1 ^ 2 * cutG m n 1) :=
        mul_le_mul hw hsq (by positivity) hl0
    _ = Real.log m * cutG m n 1 := by ring

theorem phiBar_nonneg : 0 ≤ phiBar := by
  unfold phiBar
  have : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have := Real.pi_pos
  positivity

theorem SBar_nonneg : 0 ≤ SBar := by
  unfold SBar
  exact mul_nonneg (by norm_num) (tsum_nonneg fun m => mul_nonneg (Real.log_natCast_nonneg m) (sigma_nonneg m))

theorem LambdaBar0_nonneg : 0 ≤ LambdaBar0 := by
  unfold LambdaBar0
  have h1 := SBar_nonneg
  have h2 := phiBar_nonneg
  have h3 : 0 ≤ 2 * π ^ 2 / 3 - 4 := by nlinarith [Real.pi_gt_three]
  positivity

/-- **`Λ°(X)` uniformly in `X`**: `lamCount nsRamp (5/4) X ≤ 2S̄ + (2π²/3 − 4)φ̄`. -/
theorem lamCount_nsRamp_le (X : ℝ) : lamCount nsRamp (5 / 4) X ≤ LambdaBar0 := by
  set N := ⌊X⌋₊ with hN
  have hpi := Real.pi_gt_three
  have hrow : ∀ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m < n),
      2 * (cutCount nsRamp m n (cutHi (5 / 4) X m n) + cutCount nsRamp m n (cutLo (5 / 4) m))
      ≤ (if m = 1 then (2 * π ^ 2 / 3 - 4) * phiBar else 0) + 4 * (Real.log m * sigma m) := by
    intro m hm
    obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
    rcases eq_or_lt_of_le hm1 with h | h
    · subst h
      simp only [if_true, Nat.cast_one, Real.log_one, zero_mul, mul_zero, add_zero]
      have hlo : ∀ n : ℕ, cutCount nsRamp 1 n (cutLo (5 / 4) 1) = 0 := by
        intro n
        rw [show cutLo (5 / 4) 1 = 5 / 4 from if_pos rfl, cutCount_eq, nsRamp_of_le le_rfl]
        simp
      have hterm : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => 1 < n),
          2 * (cutCount nsRamp 1 n (cutHi (5 / 4) X 1 n) + cutCount nsRamp 1 n (cutLo (5 / 4) 1))
            ≤ 4 * phiBar * (1 / (n : ℝ) ^ 2) := by
        intro n hn
        have hn2 : 2 ≤ n := (Finset.mem_filter.mp hn).2
        rw [hlo, add_zero]
        have hhi : 5 / 4 ≤ cutHi (5 / 4) X 1 n := by
          unfold cutHi; exact le_trans (le_of_eq (if_pos rfl).symm) (le_max_left _ _)
        have := two_mul_cutCount_one_le hn2 hhi
        calc _ ≤ 4 / (n : ℝ) ^ 2 * phiBar := this
          _ = _ := by ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum]
      have h1 : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => 1 < n), 1 / (n : ℝ) ^ 2 ≤ π ^ 2 / 6 - 1 := by
        have hnot : (1 : ℕ) ∉ (Finset.Icc 1 N).filter (fun n => 1 < n) := by simp
        have := sum_le_hasSum (insert 1 ((Finset.Icc 1 N).filter (fun n => 1 < n)))
          (fun i _ => by positivity) hasSum_zeta_two
        rw [Finset.sum_insert hnot] at this
        norm_num at this ⊢
        linarith
      have := phiBar_nonneg
      nlinarith
    · have hm2 : 2 ≤ m := h
      have hm1' : m ≠ 1 := by omega
      rw [if_neg hm1', zero_add]
      have hlo : cutLo (5 / 4) m = 1 := if_neg hm1'
      have hterm : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => m < n),
          2 * (cutCount nsRamp m n (cutHi (5 / 4) X m n) + cutCount nsRamp m n (cutLo (5 / 4) m))
            ≤ 4 * Real.log m * cutG m n 1 := by
        intro n hn
        have hmn : m < n := (Finset.mem_filter.mp hn).2
        rw [hlo]
        have hhi : 1 ≤ cutHi (5 / 4) X m n := by
          unfold cutHi; rw [hlo]; exact le_max_left _ _
        have := cutCount_nsRamp_le_one hm2 hmn hhi
        rw [cutCount_nsRamp_one] at this ⊢
        linarith
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum]
      have := sum_cutG_one_le hm2 N
      have hl0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
      nlinarith
  unfold lamCount
  rw [← hN]
  refine (Finset.sum_le_sum hrow).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hite : ∑ m ∈ Finset.Icc 1 N, (if m = 1 then (2 * π ^ 2 / 3 - 4) * phiBar else 0)
      ≤ (2 * π ^ 2 / 3 - 4) * phiBar := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · have h3 : 0 ≤ 2 * π ^ 2 / 3 - 4 := by nlinarith [Real.pi_gt_three]
      exact mul_nonneg h3 phiBar_nonneg
  have htsum : ∑ m ∈ Finset.Icc 1 N, Real.log m * sigma m ≤ ∑' m : ℕ, Real.log m * sigma m :=
    summable_log_mul_sigma.sum_le_tsum _ fun m _ => mul_nonneg (Real.log_natCast_nonneg m) (sigma_nonneg m)
  unfold LambdaBar0 SBar
  linarith

end Cvs.L2a.RampCutSumsUniform
