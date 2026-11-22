import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.BandwidthSpectrumFlow
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LevelsBelowLinearBound
import Cvs.Prolate.ScaleGeneratorCauchyWeight
import Cvs.Prolate.SincOperatorEigenCount
import Cvs.Prolate.SincTopIsRung
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Prolate.SlepianSignRule

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Cauchy law of the scaling Laplacian on the even rungs

For the even rungs `h_k = rung c k` (the prolate `h_{2k}`), `p = h(1)`, `q = h′(1)`, `μ = muR`, `χ = lev`, `θ = v d/dv`
and `M_kl = ∫_{−1}^{1} (H_c h_l) h_k`: `(μ_k − μ_l)M_kl = 2μ_k(p_l q_k − q_l p_k)`,
`∫(−(θ + ½)²h_l)h_k = −(χ_l + ¼)δ_kl + M_kl`, and for `c ≠ 0`, `(μ_k + μ_l)∫(θh_l)h_k = μ_k(2p_k p_l − δ_kl)`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.ScalingLaplacianCauchyLaw
open Cvs.ZeroCounting

open Cvs.Prolate.SlepianCommutingRelation (kint)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev muR IsLevelIdx rung_spec psi_rung lev_spec lev_lt rung_ne_zero continuousOn_rung)

/-! ### The operators -/

/-- `H_c g = −g″ + c²v²g`, from `g` and its second derivative `g₂`. -/
def hamC (c : ℝ) (g g₂ : ℝ → ℝ) (v : ℝ) : ℝ := -g₂ v + c ^ 2 * v ^ 2 * g v

/-- The scaling Laplacian `−(θ + ½)²g = −(v²g″ + 2vg′ + g/4)` with `θ = v d/dv`, from `g` and its two derivatives. -/
def scalingLap (g g₁ g₂ : ℝ → ℝ) (v : ℝ) : ℝ := -(v ^ 2 * g₂ v + 2 * v * g₁ v + g v / 4)

/-- **The scaling Laplacian on an angular solution**: if `(1 − v²)g″ − 2vg′ − c²v²g + χg = 0` at `v`, then
`−(θ + ½)²g = H_c g − (χ + ¼)g` at `v`. -/
theorem scalingLap_eq_of_ode {c χ v : ℝ} {g g₁ g₂ : ℝ → ℝ}
    (hode : (1 - v ^ 2) * g₂ v - 2 * v * g₁ v - c ^ 2 * v ^ 2 * g v + χ * g v = 0) :
    scalingLap g g₁ g₂ v = hamC c g g₂ v - (χ + 1 / 4) * g v := by
  unfold scalingLap hamC
  linear_combination hode

/-! ### Derivatives on `[−1, 1]` and the by-parts formula -/

/-- **Derivatives follow an identity on `[−1, 1]`**: if `f = μg` on `[−1, 1]`, then `f′(w) = μg′(w)` at every
`w ∈ [−1, 1]`, endpoints included. -/
theorem deriv_eq_of_eqOn {f g : ℝ → ℝ} {f' g' μ w : ℝ} (heq : ∀ s ∈ Icc (-1 : ℝ) 1, f s = μ * g s)
    (hw : w ∈ Icc (-1 : ℝ) 1) (hf : HasDerivAt f f' w) (hg : HasDerivAt g g' w) : f' = μ * g' := by
  have h1 : HasDerivWithinAt f (μ * g') (Icc (-1) 1) w :=
    ((hg.const_mul μ).hasDerivWithinAt).congr (fun s hs => heq s hs) (heq w hw)
  exact (uniqueDiffOn_Icc (by norm_num) w hw).eq_deriv _ hf.hasDerivWithinAt h1

/-- **Parity passes to the derivative**: if `g(−s) = εg(s)` on `[−1, 1]`, then `g′(−s) = −εg′(s)` there. -/
theorem deriv_parity {g g₁ : ℝ → ℝ} {ε : ℝ} (hg : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hpar : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = ε * g s) : ∀ s ∈ Icc (-1 : ℝ) 1, g₁ (-s) = -(ε * g₁ s) := by
  intro s hs
  have hs' : -s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1 : HasDerivAt (fun t => g (-t)) (g₁ (-s) * (-1)) s := (hg (-s) hs').comp s (hasDerivAt_neg s)
  have h2 := deriv_eq_of_eqOn hpar hs h1 (hg s hs)
  linarith

/-- **By parts against the cosine kernel**: for `g ∈ C²[−1, 1]`,
`∫_{−1}^{1} g″(v) cos(cwv) dv = cos(cw)(g′(1) − g′(−1)) + cw sin(cw)(g(1) + g(−1)) − c²w² ψg(w)`. -/
theorem integral_deriv₂_mul_cos {c : ℝ} {g g₁ g₂ : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (w : ℝ) :
    ∫ v in (-1 : ℝ)..1, g₂ v * cos (c * w * v)
      = cos (c * w) * (g₁ 1 - g₁ (-1)) + c * w * sin (c * w) * (g 1 + g (-1)) - c ^ 2 * w ^ 2 * psi c g w := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hW : ∀ v ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun v => g₁ v * cos (c * w * v) + g v * (c * w * sin (c * w * v)))
        (g₂ v * cos (c * w * v) + c ^ 2 * w ^ 2 * (g v * cos (c * w * v))) v := by
    intro v hv
    have hc : HasDerivAt (fun v => cos (c * w * v)) (-(sin (c * w * v)) * (c * w)) v :=
      ((hasDerivAt_id v).const_mul (c * w)).cos.congr_deriv (by simp)
    have hs : HasDerivAt (fun v => c * w * sin (c * w * v)) (c * w * (cos (c * w * v) * (c * w))) v :=
      (((hasDerivAt_id v).const_mul (c * w)).sin.congr_deriv (by simp)).const_mul (c * w)
    refine (((hg₁ v hv).mul hc).add ((hg v hv).mul hs)).congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun v => g₂ v * cos (c * w * v) + c ^ 2 * w ^ 2 * (g v * cos (c * w * v)))
      volume (-1) 1 :=
    ((hg₂c.mul (by fun_prop)).add (continuousOn_const.mul (hgc.mul (by fun_prop)))).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hW hint
  have i1 : IntervalIntegrable (fun v => g₂ v * cos (c * w * v)) volume (-1) 1 :=
    (hg₂c.mul (by fun_prop)).intervalIntegrable
  have i2 : IntervalIntegrable (fun v => g v * cos (c * w * v)) volume (-1) 1 :=
    (hgc.mul (by fun_prop)).intervalIntegrable
  rw [intervalIntegral.integral_add i1 (i2.const_mul (c ^ 2 * w ^ 2)), intervalIntegral.integral_const_mul] at hftc
  have hpsi : psi c g w = ∫ v in (-1 : ℝ)..1, g v * cos (c * w * v) := rfl
  rw [hpsi]
  have e1 : c * w * (-1 : ℝ) = -(c * w) := by ring
  simp only [mul_one, e1, cos_neg, sin_neg] at hftc
  linear_combination hftc

/-! ### The Cauchy pairing -/

/-- **The Cauchy pairing for cosine-transform eigenfunctions**: if `ψg = νg` and `ψh = μh` on `[−1, 1]`, `g ∈ C²`,
`h` continuous with `h′(1) = q`, then
`(μ − ν)∫_{−1}^{1} (H_c g) h = μ[(g(1) + g(−1))q − (g′(1) − g′(−1))h(1)]`. -/
theorem cauchy_pairing {c μ ν q : ℝ} {g g₁ g₂ h : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hhc : ContinuousOn h (uIcc (-1) 1)) (hh : HasDerivAt h q 1)
    (hgν : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = ν * g s) (hhμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ * h s) :
    (μ - ν) * ∫ v in (-1 : ℝ)..1, hamC c g g₂ v * h v
      = μ * ((g 1 + g (-1)) * q - (g₁ 1 - g₁ (-1)) * h 1) := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hFc : ContinuousOn (hamC c g g₂) (uIcc (-1) 1) := by
    unfold hamC
    exact hg₂c.neg.add ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hgc)
  -- the derivatives of `ψg` on `[−1, 1]`
  have hd1 : ∀ s ∈ Icc (-1 : ℝ) 1, kint g (fun ξ s => -(c * s * sin (c * ξ * s))) s = ν * g₁ s := fun s hs =>
    deriv_eq_of_eqOn hgν hs (Cvs.Prolate.SincTopIsRung.hasDerivAt_psi hgc s) (hg s (hI ▸ hs))
  have hd2 : ∀ s ∈ Icc (-1 : ℝ) 1, kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) s = ν * g₂ s :=
    fun s hs => deriv_eq_of_eqOn hd1 hs (Cvs.Prolate.SincTopIsRung.hasDerivAt_psi₁ hgc s) (hg₁ s (hI ▸ hs))
  have hq : kint h (fun ξ s => -(c * s * sin (c * ξ * s))) 1 = μ * q :=
    deriv_eq_of_eqOn hhμ ⟨by norm_num, le_rfl⟩ (Cvs.Prolate.SincTopIsRung.hasDerivAt_psi hhc 1) hh
  have hp : psi c h 1 = μ * h 1 := hhμ 1 ⟨by norm_num, le_rfl⟩
  -- `ψ(H_c g) = ν H_c g − B₁ cos(cw) − B₀ cw sin(cw)` on `[−1, 1]`, `B₁ = g′(1) − g′(−1)`, `B₀ = g(1) + g(−1)`
  have hψF : ∀ w ∈ Icc (-1 : ℝ) 1,
      psi c (hamC c g g₂) w
        = ν * hamC c g g₂ w - (g₁ 1 - g₁ (-1)) * cos (c * w) - (g 1 + g (-1)) * (c * w * sin (c * w)) := by
    intro w hw
    have e : psi c (hamC c g g₂) w
        = -(∫ v in (-1 : ℝ)..1, g₂ v * cos (c * w * v))
          - kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) w := by
      simp only [psi, kint, hamC]
      rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_sub]
      · refine intervalIntegral.integral_congr fun v _ => ?_
        ring
      · exact (hg₂c.mul (by fun_prop)).neg.intervalIntegrable
      · exact (hgc.mul (by fun_prop)).intervalIntegrable
    rw [e, integral_deriv₂_mul_cos hg hg₁ hg₂c w, hd2 w hw, hgν w hw]
    unfold hamC
    ring
  -- pair with `h`
  have hS1 : μ * ∫ v in (-1 : ℝ)..1, hamC c g g₂ v * h v
      = ∫ w in (-1 : ℝ)..1, psi c (hamC c g g₂) w * h w := by
    have hsym := Cvs.Prolate.BandwidthSpectrumFlow.psi_symm (hI ▸ hFc) (hI ▸ hhc) c
    rw [intervalIntegral.integral_congr (fun w _ => mul_comm (psi c (hamC c g g₂) w) (h w)), hsym,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [hhμ v (hI ▸ hv)]
    ring
  have hS2 : ∫ w in (-1 : ℝ)..1, psi c (hamC c g g₂) w * h w
      = ν * (∫ v in (-1 : ℝ)..1, hamC c g g₂ v * h v) - (g₁ 1 - g₁ (-1)) * psi c h 1
        + (g 1 + g (-1)) * kint h (fun ξ s => -(c * s * sin (c * ξ * s))) 1 := by
    have e : ∫ w in (-1 : ℝ)..1, psi c (hamC c g g₂) w * h w
        = ∫ w in (-1 : ℝ)..1, (ν * (hamC c g g₂ w * h w) - (g₁ 1 - g₁ (-1)) * (h w * cos (c * 1 * w))
          + (g 1 + g (-1)) * (h w * -(c * w * sin (c * 1 * w)))) := by
      refine intervalIntegral.integral_congr fun w hw => ?_
      rw [hψF w (hI ▸ hw), mul_one]
      ring
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · rfl
    · exact ((hFc.mul hhc).const_smul ν).intervalIntegrable
    · exact ((hhc.mul (by fun_prop)).const_smul (g₁ 1 - g₁ (-1))).intervalIntegrable
    · exact (((hFc.mul hhc).const_smul ν).sub ((hhc.mul (by fun_prop)).const_smul (g₁ 1 - g₁ (-1)))).intervalIntegrable
    · exact ((hhc.mul (by fun_prop)).const_smul (g 1 + g (-1))).intervalIntegrable
  rw [hS2, hp, hq] at hS1
  linear_combination hS1

/-! ### On the even rungs -/

section rung

variable {c : ℝ} {k l : ℕ}

/-- **The edge relation**: `2h_k′(1) = (χ_k − c²)h_k(1)`, the angular equation at the singular point `v = 1`. -/
theorem two_mul_rung₁_one (h : ∃ χ, IsLevelIdx c k χ) :
    2 * rung₁ c k 1 = (lev c k - c ^ 2) * rung c k 1 := by
  have := (rung_spec h).2.2.2.1 1 (by rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact ⟨by norm_num, le_rfl⟩)
  linear_combination -this

/-- The rung's derivative is odd on `[−1, 1]`. -/
theorem rung₁_neg (h : ∃ χ, IsLevelIdx c k χ) : ∀ s ∈ Icc (-1 : ℝ) 1, rung₁ c k (-s) = -rung₁ c k s := by
  obtain ⟨hg, -, -, -, heven, -⟩ := rung_spec h
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hg
  intro s hs
  have := deriv_parity (ε := 1) hg (fun s hs => by rw [heven s hs, one_mul]) s hs
  rw [this, one_mul]

/-- The rung's second derivative is even on `[−1, 1]`. -/
theorem rung₂_neg (h : ∃ χ, IsLevelIdx c k χ) : ∀ s ∈ Icc (-1 : ℝ) 1, rung₂ c k (-s) = rung₂ c k s := by
  obtain ⟨-, hg₁, -, -, -, -⟩ := rung_spec h
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hg₁
  intro s hs
  have := deriv_parity (ε := -1) hg₁ (fun s hs => by rw [rung₁_neg h s hs, neg_one_mul]) s hs
  rw [this]; ring

/-- **The Cauchy law on the rungs**: `(μ_k − μ_l)∫_{−1}^{1} (H_c h_l) h_k = 2μ_k(p_l q_k − q_l p_k)` with
`p = h(1)`, `q = h′(1)`. -/
theorem cauchy_rung (hk : ∃ χ, IsLevelIdx c k χ) (hl : ∃ χ, IsLevelIdx c l χ) :
    (muR c k - muR c l) * ∫ v in (-1 : ℝ)..1, hamC c (rung c l) (rung₂ c l) v * rung c k v
      = 2 * muR c k * (rung c l 1 * rung₁ c k 1 - rung₁ c l 1 * rung c k 1) := by
  obtain ⟨hg, hg₁, hg₂c, -, heven, -⟩ := rung_spec hl
  obtain ⟨hh, -, -, -, -, -⟩ := rung_spec hk
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have h1' : (1 : ℝ) ∈ uIcc (-1 : ℝ) 1 := by rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact h1
  rw [cauchy_pairing hg hg₁ hg₂c (by rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact continuousOn_rung hk)
    (hh 1 h1') (psi_rung hl) (psi_rung hk), heven 1 h1, rung₁_neg hl 1 h1]
  ring

/-- **The scaling Laplacian on a rung** is `H_c h − (χ + ¼)h` on `[−1, 1]`. -/
theorem scalingLap_rung (hl : ∃ χ, IsLevelIdx c l χ) {v : ℝ} (hv : v ∈ uIcc (-1 : ℝ) 1) :
    scalingLap (rung c l) (rung₁ c l) (rung₂ c l) v
      = hamC c (rung c l) (rung₂ c l) v - (lev c l + 1 / 4) * rung c l v :=
  scalingLap_eq_of_ode ((rung_spec hl).2.2.2.1 v hv)

/-- `H_c h_l` is continuous on `[−1, 1]`. -/
theorem continuousOn_hamC_rung (hl : ∃ χ, IsLevelIdx c l χ) :
    ContinuousOn (hamC c (rung c l) (rung₂ c l)) (uIcc (-1) 1) := by
  obtain ⟨hg, -, hg₂c, -, -, -⟩ := rung_spec hl
  have hgc : ContinuousOn (rung c l) (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  unfold hamC
  exact hg₂c.neg.add ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hgc)

/-- **The diagonal split**: `∫_{−1}^{1} (−(θ + ½)²h_l) h_k = −(χ_l + ¼)δ_lk + ∫_{−1}^{1} (H_c h_l) h_k`. -/
theorem integral_scalingLap_rung (hk : ∃ χ, IsLevelIdx c k χ) (hl : ∃ χ, IsLevelIdx c l χ) :
    ∫ v in (-1 : ℝ)..1, scalingLap (rung c l) (rung₁ c l) (rung₂ c l) v * rung c k v
      = -(lev c l + 1 / 4) * (if l = k then 1 else 0)
        + ∫ v in (-1 : ℝ)..1, hamC c (rung c l) (rung₂ c l) v * rung c k v := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hkc : ContinuousOn (rung c k) (uIcc (-1) 1) := hI ▸ continuousOn_rung hk
  have hlc : ContinuousOn (rung c l) (uIcc (-1) 1) := hI ▸ continuousOn_rung hl
  have e : ∫ v in (-1 : ℝ)..1, scalingLap (rung c l) (rung₁ c l) (rung₂ c l) v * rung c k v
      = ∫ v in (-1 : ℝ)..1, (hamC c (rung c l) (rung₂ c l) v * rung c k v
          - (lev c l + 1 / 4) * (rung c l v * rung c k v)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [scalingLap_rung hl hv]
    ring
  have i1 : IntervalIntegrable (fun v => hamC c (rung c l) (rung₂ c l) v * rung c k v) volume (-1) 1 :=
    ((continuousOn_hamC_rung hl).mul hkc).intervalIntegrable
  have i2 : IntervalIntegrable (fun v => rung c l v * rung c k v) volume (-1) 1 := (hlc.mul hkc).intervalIntegrable
  rw [e, intervalIntegral.integral_sub i1 (i2.const_mul (lev c l + 1 / 4)), intervalIntegral.integral_const_mul,
    Cvs.Prolate.SincOperatorEigenCount.integral_rung_mul_rung_eq hl hk]
  ring

/-- **The Cauchy law off the diagonal, product form**: for `k ≠ l`,
`(μ_k − μ_l)∫_{−1}^{1} (−(θ + ½)²h_l) h_k = 2μ_k(p_l q_k − q_l p_k)`. -/
theorem cauchy_scalingLap_rung (hk : ∃ χ, IsLevelIdx c k χ) (hl : ∃ χ, IsLevelIdx c l χ) (hkl : k ≠ l) :
    (muR c k - muR c l) * ∫ v in (-1 : ℝ)..1, scalingLap (rung c l) (rung₁ c l) (rung₂ c l) v * rung c k v
      = 2 * muR c k * (rung c l 1 * rung₁ c k 1 - rung₁ c l 1 * rung c k 1) := by
  rw [integral_scalingLap_rung hk hl, if_neg (Ne.symm hkl), mul_zero, zero_add]
  exact cauchy_rung hk hl

/-- **The edge cross term in closed form**: `p_l q_k − q_l p_k = p_k p_l(χ_k − χ_l)/2`. -/
theorem cross_edge (hk : ∃ χ, IsLevelIdx c k χ) (hl : ∃ χ, IsLevelIdx c l χ) :
    rung c l 1 * rung₁ c k 1 - rung₁ c l 1 * rung c k 1
      = rung c k 1 * rung c l 1 * (lev c k - lev c l) / 2 := by
  linear_combination (rung c l 1 / 2) * two_mul_rung₁_one hk - (rung c k 1 / 2) * two_mul_rung₁_one hl

/-- **Distinct rungs have distinct cosine-transform eigenvalues**: for `c > 0`, `μ_l² < μ_k²` when `k < l`. -/
theorem muR_sq_lt (hc : 0 < c) (hl : ∃ χ, IsLevelIdx c l χ) (hkl : k < l) : muR c l ^ 2 < muR c k ^ 2 := by
  have hk : ∃ χ, IsLevelIdx c k χ := by
    obtain ⟨χ, h⟩ := hl
    exact Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_of_le h hkl.le
  obtain ⟨hg, hg₁, hg₂c, hang, heven, -⟩ := rung_spec hk
  obtain ⟨hh, hh₁, hh₂c, hang', heven', -⟩ := rung_spec hl
  exact Cvs.Prolate.SlepianEvenOrdering.mu_sq_lt hc hg hg₁ hg₂c hang heven (rung_ne_zero hk) hh hh₁ hh₂c hang' heven'
    (rung_ne_zero hl) (psi_rung hk) (psi_rung hl) (lev_lt hl hkl)

/-- For `c > 0`, distinct rungs have distinct `μ`. -/
theorem muR_ne (hc : 0 < c) (hk : ∃ χ, IsLevelIdx c k χ) (hl : ∃ χ, IsLevelIdx c l χ) (hkl : k ≠ l) :
    muR c k ≠ muR c l := by
  intro he
  rcases lt_or_gt_of_ne hkl with h | h
  · have := muR_sq_lt hc hl h; rw [he] at this; exact lt_irrefl _ this
  · have := muR_sq_lt hc hk h; rw [he] at this; exact lt_irrefl _ this

/-- **The Cauchy law, entry form**: for `k ≠ l`, `∫_{−1}^{1} (−(θ + ½)²h_l) h_k = ∫_{−1}^{1} (H_c h_l) h_k
= 2μ_k(p_l q_k − q_l p_k)/(μ_k − μ_l) = μ_k p_k p_l(χ_k − χ_l)/(μ_k − μ_l)`. -/
theorem cauchy_entry (hc : 0 < c) (hk : ∃ χ, IsLevelIdx c k χ) (hl : ∃ χ, IsLevelIdx c l χ) (hkl : k ≠ l) :
    ∫ v in (-1 : ℝ)..1, scalingLap (rung c l) (rung₁ c l) (rung₂ c l) v * rung c k v
        = ∫ v in (-1 : ℝ)..1, hamC c (rung c l) (rung₂ c l) v * rung c k v ∧
      ∫ v in (-1 : ℝ)..1, hamC c (rung c l) (rung₂ c l) v * rung c k v
        = 2 * muR c k * (rung c l 1 * rung₁ c k 1 - rung₁ c l 1 * rung c k 1) / (muR c k - muR c l) ∧
      ∫ v in (-1 : ℝ)..1, hamC c (rung c l) (rung₂ c l) v * rung c k v
        = muR c k * rung c k 1 * rung c l 1 * (lev c k - lev c l) / (muR c k - muR c l) := by
  have hne : muR c k - muR c l ≠ 0 := sub_ne_zero.mpr (muR_ne hc hk hl hkl)
  have h2 : ∫ v in (-1 : ℝ)..1, hamC c (rung c l) (rung₂ c l) v * rung c k v
      = 2 * muR c k * (rung c l 1 * rung₁ c k 1 - rung₁ c l 1 * rung c k 1) / (muR c k - muR c l) := by
    rw [eq_div_iff hne, mul_comm]
    exact cauchy_rung hk hl
  refine ⟨?_, h2, ?_⟩
  · rw [integral_scalingLap_rung hk hl, if_neg (Ne.symm hkl)]; ring
  · rw [h2, cross_edge hk hl]
    ring

/-- For `c > 0` every rung has `μ ≠ 0`. -/
theorem muR_ne_zero (hc : 0 < c) (hk : ∃ χ, IsLevelIdx c k χ) : muR c k ≠ 0 := by
  intro h
  have := Cvs.Prolate.SlepianSignRule.neg_one_pow_mul_muR_pos hc hk
  rw [h, mul_zero] at this
  exact lt_irrefl _ this

/-- **The first-order law on the rungs** (from the virial pairing of Cvs.Prolate.ScaleGeneratorCauchyWeight):
`(μ_k + μ_l)∫_{−1}^{1} (θh_l) h_k = μ_k(2p_k p_l − δ_lk)` with `θh = v h′`. -/
theorem theta_rung (hc : c ≠ 0) (hk : ∃ χ, IsLevelIdx c k χ) (hl : ∃ χ, IsLevelIdx c l χ) :
    (muR c k + muR c l) * ∫ v in (-1 : ℝ)..1, v * rung₁ c l v * rung c k v
      = muR c k * (2 * rung c k 1 * rung c l 1 - if l = k then 1 else 0) := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  obtain ⟨hgk, hgk₁, -, -, hevk, -⟩ := rung_spec hk
  obtain ⟨hgl, hgl₁, -, -, hevl, -⟩ := rung_spec hl
  have hA := Cvs.Prolate.ScaleGeneratorCauchyWeight.virial_left (g := rung c k) hc hgl (psi_rung hl)
  have hB := Cvs.Prolate.ScaleGeneratorCauchyWeight.virial_left (g := rung c l) hc hgk (psi_rung hk)
  have hS := Cvs.Prolate.ScaleGeneratorCauchyWeight.symm_pair (continuousOn_rung hk) (continuousOn_rung hl) c
  have hE := Cvs.Prolate.ScaleGeneratorCauchyWeight.edge_sum hgk (fun s hs => (hgk₁ s hs).continuousAt.continuousWithinAt)
    hgl (fun s hs => (hgl₁ s hs).continuousAt.continuousWithinAt) (hevk 1 ⟨by norm_num, le_rfl⟩)
    (hevl 1 ⟨by norm_num, le_rfl⟩)
  have horth := Cvs.Prolate.SincOperatorEigenCount.integral_rung_mul_rung_eq hk hl
  have e : ∫ v in (-1 : ℝ)..1, v * rung₁ c l v * rung c k v = ∫ v in (-1 : ℝ)..1, v * rung c k v * rung₁ c l v :=
    intervalIntegral.integral_congr fun v _ => by ring
  rw [e]
  set A := ∫ v in (-1 : ℝ)..1, v * rung c k v * rung₁ c l v
  set B := ∫ v in (-1 : ℝ)..1, v * rung c l v * rung₁ c k v
  have hAB : muR c l * A = muR c k * B := by
    have h := hA.symm.trans (hS.trans hB)
    field_simp at h
    linarith
  have hkl : (if l = k then (1 : ℝ) else 0) = if k = l then 1 else 0 := by
    by_cases h : l = k
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [hkl, ← horth]
  linear_combination hAB + muR c k * hE

/-- At `c = 2πx` the rungs `rung c (2j)`, `j < x` (the prolates `h_{4j}`), all have levels. -/
theorem rungSpace_level {x j : ℕ} (hj : j < x) : ∃ χ, IsLevelIdx (2 * π * x) (2 * j) χ := by
  have hj' : (j : ℝ) + 1 ≤ x := by exact_mod_cast hj
  refine (Cvs.Prolate.LevelsBelowLinearBound.lev_lt_lin ?_).2
  push_cast
  nlinarith [pi_pos, mul_nonneg pi_pos.le (sub_nonneg.2 hj')]

end rung

end Cvs.Prolate.ScalingLaplacianCauchyLaw
