import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Upstream.ArsinhLipschitzStrip
import Cvs.Upstream.ComplexArsinhStrip
import Cvs.Upstream.InvSqrtKernelStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The canonical logarithm of the frozen root

With `τ₀ = −1/(2ω)`: `√(τ₀² + 1) − τ₀ = (s+2)/ω`, so `g(s) = ash(τ₀) − ash(τ)` satisfies `exp g = ρ*`; and on the region
`g(s) − ĝ(s + 3/2) = −(ash τ − ash(τ₀ + w)) − Φ(τ₀, w) + (1 − k(w))(τ₀ + 1/(2u))` with `u = s + 3/2`, `w = u/(2c)`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.FrozenRootCanonicalLog

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Upstream.ComplexArsinhStrip Cvs.Prolate.Mellin.WkbPhaseAntiderivative Cvs.Upstream.InvSqrtKernelStrip Cvs.Upstream.ArsinhLipschitzStrip

/-- `τ₀ = −1/(2ω)`. -/
def tau0 (s : ℂ) : ℂ := -1 / (2 * omega s)

/-- The canonical logarithm of `ρ*`. -/
def gL (c χ : ℝ) (s : ℂ) : ℂ := ash (tau0 s) - ash (tau c χ s)

variable {ε c χ : ℝ} {s : ℂ}

theorem Hyp.norm_omega_ge' (h : Hyp ε c χ s) : 15 / 16 * ‖s + 3 / 2‖ ≤ ‖omega s‖ := by
  have h1 := h.norm_omega_sub
  have h2 := h.norm_m_ge
  have := norm_sub_norm_le (s + 3 / 2) (omega s)
  rw [norm_sub_rev] at h1
  linarith

theorem Hyp.norm_omega_le' (h : Hyp ε c χ s) : ‖omega s‖ ≤ 17 / 16 * ‖s + 3 / 2‖ := by
  have h1 := h.norm_omega_sub
  have h2 := h.norm_m_ge
  have := norm_sub_norm_le (omega s) (s + 3 / 2)
  linarith

theorem Hyp.norm_tau0 (h : Hyp ε c χ s) : ‖tau0 s‖ ≤ 8 / (15 * ‖s + 3 / 2‖) := by
  have hω := (Hyp.norm_omega_ge' h)
  have h2 := h.norm_m_ge
  unfold tau0
  rw [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_two,
    div_le_div_iff₀ (by have := norm_pos_iff.mpr h.omega_ne; positivity) (by positivity)]
  nlinarith

/-- `‖ω − u‖ ≤ 1/(4‖u‖)`. -/
theorem Hyp.norm_omega_sub' (h : Hyp ε c χ s) : ‖omega s - (s + 3 / 2)‖ ≤ 1 / (4 * ‖s + 3 / 2‖) := by
  have h1 := h.norm_omega_sub
  have h2 := h.norm_m_ge
  have hsq := omega_sq h.m_ne
  have e : (omega s - (s + 3 / 2)) * (omega s + (s + 3 / 2)) = -1 / 4 := by linear_combination hsq
  have hp : ‖s + 3 / 2‖ ≤ ‖omega s + (s + 3 / 2)‖ := by
    have := norm_sub_norm_le (2 * (s + 3 / 2)) (-(omega s - (s + 3 / 2)))
    rw [norm_neg, show 2 * (s + 3 / 2) - -(omega s - (s + 3 / 2)) = omega s + (s + 3 / 2) by ring,
      norm_mul, Complex.norm_two] at this
    linarith
  have hn : ‖omega s - (s + 3 / 2)‖ * ‖omega s + (s + 3 / 2)‖ = 1 / 4 := by
    rw [← norm_mul, e]; norm_num
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (omega s - (s + 3 / 2))]

/-- `√(τ₀² + 1) − τ₀ = (s+2)/ω`. -/
theorem Hyp.zeta_tau0 (h : Hyp ε c χ s) : csqrt (tau0 s ^ 2 + 1) - tau0 s = (s + 2) / omega s := by
  have hω := h.omega_ne
  have hsq := omega_sq h.m_ne
  have hcs : csqrt (tau0 s ^ 2 + 1) = (s + 3 / 2) / omega s := by
    apply csqrt_eq_of_sq
    · unfold tau0; field_simp; linear_combination (-4) * hsq
    · have hd : (s + 3 / 2) / omega s = 1 - (omega s - (s + 3 / 2)) / omega s := by field_simp; ring
      rw [hd]
      have hb : ‖(omega s - (s + 3 / 2)) / omega s‖ ≤ 1 / 15 := by
        rw [norm_div, div_le_div_iff₀ (norm_pos_iff.mpr hω) (by norm_num)]
        have := h.norm_omega_sub; have := (Hyp.norm_omega_ge' h); have := h.norm_m_ge; nlinarith
      have := Complex.abs_re_le_norm ((omega s - (s + 3 / 2)) / omega s)
      simp only [Complex.sub_re, Complex.one_re]
      have := abs_le.mp (this.trans hb); linarith
  rw [hcs]; unfold tau0; field_simp; ring

theorem Hyp.tau_mem (h : Hyp ε c χ s) : tau c χ s ∈ St (ε / 4) := Hyp.abs_im_tau_le h

theorem Hyp.tau0_mem (h : Hyp ε c χ s) : tau0 s ∈ St (ε / 4) := by
  have h1 := (Hyp.norm_tau0 h)
  have h2 := h.norm_m_ge
  have h3 : ‖tau0 s‖ ≤ 4 / 15 := h1.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have := Complex.abs_im_le_norm (tau0 s)
  show |(tau0 s).im| ≤ 1 - ε / 4
  linarith [h.hε1]

/-- **`exp g = ρ*`.** -/
theorem Hyp.exp_gL (h : Hyp ε c χ s) : Complex.exp (gL c χ s) = rhoStar c χ s := by
  have hδ : 0 < ε / 4 := by linarith [h.hε]
  have e1 := exp_neg_ash (strip hδ (Hyp.tau_mem h))
  have e2 := exp_neg_ash (strip hδ (Hyp.tau0_mem h))
  rw [(Hyp.zeta_tau0 h)] at e2
  have hs2 := h.s2_ne
  have hω := h.omega_ne
  unfold gL rhoStar zeta
  rw [show ash (tau0 s) - ash (tau c χ s) = -ash (tau c χ s) - -ash (tau0 s) by ring, Complex.exp_sub, e1, e2]
  field_simp

theorem convex_St_re (δ r : ℝ) : Convex ℝ (St δ ∩ {t : ℂ | r ≤ t.re}) := by
  refine (convex_St δ).inter ?_
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  have : (a • x + b • y).re = a * x.re + b * y.re := by simp
  rw [this]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  have : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  linarith

/-- `ĝ`'s correction term: `u/(2S(S+2c)) = (1 − k(w))/(2u)`. -/
theorem corr_eq (hc : 0 < c) {u : ℂ} (hu : |u.im| < 2 * c) (hu0 : u ≠ 0) :
    u / (2 * Sq c u * (Sq c u + 2 * c)) = (1 - kf (u / (2 * c))) / (2 * u) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hS := Sq_ne_zero hc hu
  have hS2 := Sq_add_ne_zero hc hu
  have e := two_c_mul_csqrt hc hu
  have hcs : csqrt ((u / (2 * c)) ^ 2 + 1) = Sq c u / (2 * c) := by rw [← e]; field_simp
  have hsq := Sq_sq c u
  unfold kf
  rw [hcs]
  field_simp
  linear_combination (-1 : ℂ) * hsq

theorem Hyp.norm_w (h : Hyp ε c χ s) : ‖(s + 3 / 2) / (2 * (c : ℂ))‖ = ‖s + 3 / 2‖ / (2 * c) := by
  rw [norm_div, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg h.c_pos.le]

theorem Hyp.im_w (h : Hyp ε c χ s) : ((s + 3 / 2) / (2 * (c : ℂ))).im = s.im / (2 * c) := by
  rw [show (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]; simp

theorem Hyp.re_w (h : Hyp ε c χ s) : ((s + 3 / 2) / (2 * (c : ℂ))).re = (s.re + 3 / 2) / (2 * c) := by
  rw [show (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]; simp

theorem Hyp.strip_u (h : Hyp ε c χ s) : |(s + 3 / 2).im| < 2 * c := by
  have : (s + 3 / 2).im = s.im := by simp
  rw [this]; have := h.him; have := h.hε; have := h.c_pos; nlinarith

theorem Hyp.w_mem (h : Hyp ε c χ s) : (s + 3 / 2) / (2 * (c : ℂ)) ∈ St (ε / 4) := by
  show |((s + 3 / 2) / (2 * (c : ℂ))).im| ≤ 1 - ε / 4
  have hc := h.c_pos
  rw [Hyp.im_w h, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * c), div_le_iff₀ (by positivity)]
  have := h.him; have := h.hε; nlinarith

theorem Hyp.c_ge_eps (h : Hyp ε c χ s) : 64 / ε ≤ c := by
  have h1 := h.hc
  have hε := h.hε
  have : 64 / ε ≤ 64 / ε ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith [h.hε1]
  linarith

theorem Hyp.tau0_w_mem (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    tau0 s + (s + 3 / 2) / (2 * (c : ℂ)) ∈ St (ε / 4) := by
  show |(tau0 s + (s + 3 / 2) / (2 * (c : ℂ))).im| ≤ 1 - ε / 4
  have hc := h.c_pos
  have hε := h.hε
  have hτ0 := Hyp.norm_tau0 h
  have hU2 := h.norm_m_ge
  rw [Complex.add_im, Hyp.im_w h]
  have h1 := Complex.abs_im_le_norm (tau0 s)
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * c)]
  by_cases hy : c ≤ |s.im|
  · have hUc : c ≤ ‖s + 3 / 2‖ := by
      have := Complex.abs_im_le_norm (s + 3 / 2); simp at this; linarith
    have hcε := Hyp.c_ge_eps h
    have : ‖tau0 s‖ ≤ ε / 4 := by
      refine hτ0.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 64 ≤ ε * c := by rw [div_le_iff₀ hε] at hcε; linarith
      nlinarith
    have hw : |s.im| / (2 * c) ≤ 1 - ε / 2 := by
      rw [div_le_iff₀ (by positivity)]; have := h.him; nlinarith
    linarith
  · push_neg at hy
    have : ‖tau0 s‖ ≤ 4 / 15 := hτ0.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    have hw : |s.im| / (2 * c) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith

/-- **The offset `τ − τ₀ − w`.** -/
theorem Hyp.norm_offset (h : Hyp ε c χ s) :
    ‖tau c χ s - (tau0 s + (s + 3 / 2) / (2 * (c : ℂ)))‖ ≤ 3 / (4 * c * ‖omega s‖) := by
  have hc := h.c_pos
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hωne := h.omega_ne
  have hωpos : 0 < ‖omega s‖ := norm_pos_iff.mpr hωne
  have hU2 := h.norm_m_ge
  have hω2 := Hyp.norm_omega_le' h
  have hωu := Hyp.norm_omega_sub' h
  have e : tau c χ s - (tau0 s + (s + 3 / 2) / (2 * (c : ℂ)))
      = (omega s * (omega s - (s + 3 / 2)) - ((χ : ℂ) - c)) / (2 * c * omega s) := by
    unfold tau tau0; field_simp; ring
  have hn : ‖(2 : ℂ) * c * omega s‖ = 2 * c * ‖omega s‖ := by
    rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hc.le]
  rw [e, norm_div, hn, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ‖omega s * (omega s - (s + 3 / 2))‖ ≤ 17 / 64 := by
    rw [norm_mul]
    have hU0 : ‖s + 3 / 2‖ ≠ 0 := by positivity
    calc ‖omega s‖ * ‖omega s - (s + 3 / 2)‖ ≤ 17 / 16 * ‖s + 3 / 2‖ * (1 / (4 * ‖s + 3 / 2‖)) := by gcongr
      _ = 17 / 64 * (‖s + 3 / 2‖ / ‖s + 3 / 2‖) := by ring
      _ = 17 / 64 := by rw [div_self hU0, mul_one]
  have h2 : ‖((χ : ℂ) - c)‖ ≤ 1 := by
    rw [show ((χ : ℂ) - c) = ((χ - c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h.hχ0, h.hχ1]
  have := norm_sub_le (omega s * (omega s - (s + 3 / 2))) ((χ : ℂ) - c)
  have hnum : ‖omega s * (omega s - (s + 3 / 2)) - ((χ : ℂ) - c)‖ ≤ 3 / 2 := by linarith
  have hp : 0 < 4 * c * ‖omega s‖ := by positivity
  calc ‖omega s * (omega s - (s + 3 / 2)) - ((χ : ℂ) - c)‖ * (4 * c * ‖omega s‖)
      ≤ 3 / 2 * (4 * c * ‖omega s‖) := mul_le_mul_of_nonneg_right hnum hp.le
    _ = 3 * (2 * c * ‖omega s‖) := by ring

/-- **The Lipschitz term.** -/
theorem Hyp.T1_le (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖ash (tau c χ s) - ash (tau0 s + (s + 3 / 2) / (2 * (c : ℂ)))‖
      ≤ 12 / (ε / 4) / (‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c)) := by
  have hε := h.hε
  have hδ : 0 < ε / 4 := by positivity
  have hδ1 : ε / 4 ≤ 1 := by linarith
  have hc := h.c_pos
  have hU2 := h.norm_m_ge
  have hω1 := Hyp.norm_omega_ge' h
  have hτ0 := Hyp.norm_tau0 h
  have hA := Hyp.norm_offset h
  have hωpos : 0 < ‖omega s‖ := norm_pos_iff.mpr h.omega_ne
  have mt := Hyp.tau_mem h
  have mt0w := Hyp.tau0_w_mem h hε4
  have hA' : ‖tau c χ s - (tau0 s + (s + 3 / 2) / (2 * (c : ℂ)))‖ ≤ 4 / (5 * c * ‖s + 3 / 2‖) := by
    refine hA.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  by_cases hU : ‖s + 3 / 2‖ ≤ 4 * c
  · have hl := norm_ash_sub_le hδ (convex_St (ε / 4)) subset_rfl (K := 3 / (ε / 4))
      (fun t ht => (norm_kf_le hδ hδ1 ht).trans (by
        apply div_le_div_of_nonneg_left (by norm_num) hδ; nlinarith [norm_nonneg t])) mt0w mt
    refine hl.trans ?_
    calc 3 / (ε / 4) * ‖tau c χ s - (tau0 s + (s + 3 / 2) / (2 * (c : ℂ)))‖
        ≤ 3 / (ε / 4) * (4 / (5 * c * ‖s + 3 / 2‖)) := by gcongr
      _ = 12 / (ε / 4) * (1 / (5 * c * ‖s + 3 / 2‖)) := by field_simp; ring
      _ ≤ 12 / (ε / 4) * (1 / (‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      _ = _ := by ring
  · push_neg at hU
    set r := (s.re + 3 / 2) / (2 * c) - 1
    have hre0 : 0 ≤ s.re + 3 / 2 := by linarith [h.hre]
    have hx : ‖s + 3 / 2‖ / 2 ≤ s.re + 3 / 2 := by
      have := Complex.norm_le_abs_re_add_abs_im (s + 3 / 2)
      simp only [Complex.add_re, Complex.add_im] at this
      norm_num at this
      rw [abs_of_nonneg hre0] at this
      have := h.him; have := abs_nonneg s.im; nlinarith
    have h1r : ‖s + 3 / 2‖ / (4 * c) ≤ 1 + r := by
      have e : 1 + r = (s.re + 3 / 2) / (2 * c) := by simp only [r]; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hr0 : 0 ≤ r := by
      have : 1 ≤ ‖s + 3 / 2‖ / (4 * c) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    have m1 : tau0 s + (s + 3 / 2) / (2 * (c : ℂ)) ∈ St (ε / 4) ∩ {t : ℂ | r ≤ t.re} := by
      refine ⟨mt0w, ?_⟩
      show r ≤ (tau0 s + (s + 3 / 2) / (2 * (c : ℂ))).re
      rw [Complex.add_re, Hyp.re_w h]
      have h3 : ‖tau0 s‖ ≤ 1 := hτ0.trans (by rw [div_le_one (by positivity)]; nlinarith)
      have := abs_le.mp ((Complex.abs_re_le_norm (tau0 s)).trans h3)
      simp only [r]; linarith
    have m2 : tau c χ s ∈ St (ε / 4) ∩ {t : ℂ | r ≤ t.re} := by
      refine ⟨mt, ?_⟩
      show r ≤ (tau c χ s).re
      have e : tau c χ s = (tau0 s + (s + 3 / 2) / (2 * (c : ℂ)))
          + (tau c χ s - (tau0 s + (s + 3 / 2) / (2 * (c : ℂ)))) := by ring
      rw [e, Complex.add_re, Complex.add_re, Hyp.re_w h]
      have h3 : ‖tau0 s‖ ≤ 4 / 15 :=
        hτ0.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
      have h4 : ‖tau c χ s - (tau0 s + (s + 3 / 2) / (2 * (c : ℂ)))‖ ≤ 1 / 2 :=
        hA'.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [h.c_ge])
      have h5 := abs_le.mp ((Complex.abs_re_le_norm (tau0 s)).trans h3)
      have h6 := abs_le.mp ((Complex.abs_re_le_norm _).trans h4)
      simp only [r]; linarith
    have hl := norm_ash_sub_le hδ (convex_St_re (ε / 4) r) Set.inter_subset_left
      (K := 3 / (ε / 4 * (1 + r)))
      (fun t ht => (norm_kf_le hδ hδ1 ht.1).trans (by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have h7 := Complex.re_le_norm t
        have h8 : r ≤ t.re := ht.2
        nlinarith)) m1 m2
    refine hl.trans ?_
    calc 3 / (ε / 4 * (1 + r)) * ‖tau c χ s - (tau0 s + (s + 3 / 2) / (2 * (c : ℂ)))‖
        ≤ 3 / (ε / 4 * (‖s + 3 / 2‖ / (4 * c))) * (4 / (5 * c * ‖s + 3 / 2‖)) := by gcongr
      _ = 12 / (ε / 4) * (4 / (5 * ‖s + 3 / 2‖ ^ 2)) := by field_simp; ring
      _ ≤ 12 / (ε / 4) * (1 / (‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      _ = _ := by ring

/-- **The second-difference term.** -/
theorem Hyp.T2_le (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖ash (tau0 s + (s + 3 / 2) / (2 * (c : ℂ))) - ash (tau0 s) - ash ((s + 3 / 2) / (2 * (c : ℂ)))
        - tau0 s * (kf ((s + 3 / 2) / (2 * (c : ℂ))) - 1)‖
      ≤ 139 / (ε / 4) ^ 5 / (‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c)) := by
  have hε := h.hε
  have hδ : 0 < ε / 4 := by positivity
  have hδ1 : ε / 4 ≤ 1 := by linarith
  have hc := h.c_pos
  have hU2 := h.norm_m_ge
  have hτ0 := Hyp.norm_tau0 h
  have hΦ := norm_ash_second_le hδ hδ1 (Hyp.tau0_mem h) (Hyp.w_mem h) (Hyp.tau0_w_mem h hε4)
  rw [Hyp.norm_w h] at hΦ
  refine hΦ.trans ?_
  have h35 : 1 / (ε / 4) ^ 3 ≤ 1 / (ε / 4) ^ 5 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_of_le_one hδ.le hδ1 (by norm_num))
  generalize hU : ‖s + 3 / 2‖ = U at *
  generalize ε / 4 = δ at *
  have hτ2 : ‖tau0 s‖ ^ 2 ≤ 64 / (225 * U ^ 2) := by
    calc ‖tau0 s‖ ^ 2 ≤ (8 / (15 * U)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hτ0 2
      _ = 64 / (225 * U ^ 2) := by ring
  have hm0 : 0 ≤ min (54 / δ ^ 3) (486 * (U / (2 * c)) / δ ^ 5) := le_min (by positivity) (by positivity)
  rw [div_div]
  by_cases hUc : U ≤ c
  · calc ‖tau0 s‖ ^ 2 * min (54 / δ ^ 3) (486 * (U / (2 * c)) / δ ^ 5)
        ≤ 64 / (225 * U ^ 2) * (486 * (U / (2 * c)) / δ ^ 5) := mul_le_mul hτ2 (min_le_right _ _) hm0 (by positivity)
      _ = (64 * 486 * U) / (225 * U ^ 2 * (2 * c) * δ ^ 5) := by field_simp
      _ ≤ 139 / (δ ^ 5 * (U * (U + c))) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hk : 0 ≤ δ ^ 5 * U ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left (show 31104 * (U + c) ≤ 62550 * c by linarith) hk]
  · push_neg at hUc
    have h54 : 54 / δ ^ 3 ≤ 54 / δ ^ 5 := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div 54]; exact mul_le_mul_of_nonneg_left h35 (by norm_num)
    calc ‖tau0 s‖ ^ 2 * min (54 / δ ^ 3) (486 * (U / (2 * c)) / δ ^ 5)
        ≤ 64 / (225 * U ^ 2) * (54 / δ ^ 5) := mul_le_mul hτ2 ((min_le_left _ _).trans h54) hm0 (by positivity)
      _ = (64 * 54) / (225 * U ^ 2 * δ ^ 5) := by field_simp
      _ ≤ 139 / (δ ^ 5 * (U * (U + c))) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hk : 0 ≤ δ ^ 5 * U := by positivity
          nlinarith [mul_le_mul_of_nonneg_left (show 3456 * (U + c) ≤ 31275 * U by linarith) hk]

/-- **The frozen-root offset term.** -/
theorem Hyp.T3_le (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖(1 - kf ((s + 3 / 2) / (2 * (c : ℂ)))) * (tau0 s + 1 / (2 * (s + 3 / 2)))‖
      ≤ 1 / (ε / 4) / (‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c)) := by
  have hε := h.hε
  have hδ : 0 < ε / 4 := by positivity
  have hδ1 : ε / 4 ≤ 1 := by linarith
  have hc := h.c_pos
  have hc1 : 1 ≤ c := by linarith [h.c_ge]
  have hU2 := h.norm_m_ge
  have hω1 := Hyp.norm_omega_ge' h
  have hωu := Hyp.norm_omega_sub' h
  have hωne := h.omega_ne
  have hu0 := h.m_ne
  have h1 := norm_one_sub_kf_le hδ hδ1 (Hyp.w_mem h)
  rw [Hyp.norm_w h] at h1
  have e : tau0 s + 1 / (2 * (s + 3 / 2)) = (omega s - (s + 3 / 2)) / (2 * (s + 3 / 2) * omega s) := by
    have h3 : (3 + s * 2 : ℂ) ≠ 0 := by intro h0; apply hu0; linear_combination h0 / 2
    have h3' : (s * 2 + 3 : ℂ) ≠ 0 := by intro h0; apply hu0; linear_combination h0 / 2
    have hx : (3 + s * 2) * (3 + s * 2)⁻¹ = 1 := mul_inv_cancel₀ h3
    unfold tau0; field_simp; linear_combination hx
  rw [norm_mul, e, norm_div, norm_mul, norm_mul, Complex.norm_two]
  generalize hU : ‖s + 3 / 2‖ = U at *
  generalize ε / 4 = δ at *
  have hωpos : 0 < ‖omega s‖ := norm_pos_iff.mpr hωne
  calc ‖1 - kf ((s + 3 / 2) / (2 * (c : ℂ)))‖ * (‖omega s - (s + 3 / 2)‖ / (2 * U * ‖omega s‖))
      ≤ 3 / δ * (U / (2 * c)) * ((1 / (4 * U)) / (2 * U * (15 / 16 * U))) := by gcongr
    _ = 1 / (5 * δ * c * U ^ 2) := by field_simp; ring
    _ ≤ 1 / δ / (U * (U + c)) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hk : 0 ≤ δ * U := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (show U + c ≤ 5 * c * U by nlinarith) hk]

/-- **The pointwise comparison of `log ρ*` with `ĝ`.** -/
theorem Hyp.norm_gL_sub_gh_le (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖gL c χ s - gh c (s + 3 / 2)‖ ≤ 160 / (ε / 4) ^ 5 / (‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c)) := by
  have hε := h.hε
  have hδ : 0 < ε / 4 := by positivity
  have hδ1 : ε / 4 ≤ 1 := by linarith
  have hc := h.c_pos
  have hcorr := corr_eq hc (Hyp.strip_u h) h.m_ne
  have hid : gL c χ s - gh c (s + 3 / 2)
      = -(ash (tau c χ s) - ash (tau0 s + (s + 3 / 2) / (2 * (c : ℂ))))
        - (ash (tau0 s + (s + 3 / 2) / (2 * (c : ℂ))) - ash (tau0 s) - ash ((s + 3 / 2) / (2 * (c : ℂ)))
            - tau0 s * (kf ((s + 3 / 2) / (2 * (c : ℂ))) - 1))
        + (1 - kf ((s + 3 / 2) / (2 * (c : ℂ)))) * (tau0 s + 1 / (2 * (s + 3 / 2))) := by
    unfold gL gh; rw [hcorr]; ring
  rw [hid]
  have t1 := Hyp.T1_le h hε4
  have t2 := Hyp.T2_le h hε4
  have t3 := Hyp.T3_le h hε4
  have n1 := norm_add_le (-(ash (tau c χ s) - ash (tau0 s + (s + 3 / 2) / (2 * (c : ℂ))))
        - (ash (tau0 s + (s + 3 / 2) / (2 * (c : ℂ))) - ash (tau0 s) - ash ((s + 3 / 2) / (2 * (c : ℂ)))
            - tau0 s * (kf ((s + 3 / 2) / (2 * (c : ℂ))) - 1)))
    ((1 - kf ((s + 3 / 2) / (2 * (c : ℂ)))) * (tau0 s + 1 / (2 * (s + 3 / 2))))
  have n2 := norm_sub_le (-(ash (tau c χ s) - ash (tau0 s + (s + 3 / 2) / (2 * (c : ℂ)))))
    (ash (tau0 s + (s + 3 / 2) / (2 * (c : ℂ))) - ash (tau0 s) - ash ((s + 3 / 2) / (2 * (c : ℂ)))
      - tau0 s * (kf ((s + 3 / 2) / (2 * (c : ℂ))) - 1))
  rw [norm_neg] at n2
  have hU2 := h.norm_m_ge
  have h15 : 1 / (ε / 4) ≤ 1 / (ε / 4) ^ 5 := by
    apply one_div_le_one_div_of_le (by positivity)
    calc (ε / 4) ^ 5 ≤ (ε / 4) ^ 1 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num)
      _ = ε / 4 := pow_one _
  have hD : 0 < ‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c) := by positivity
  have hfin : 12 / (ε / 4) / (‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c)) + 139 / (ε / 4) ^ 5 / (‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c))
      + 1 / (ε / 4) / (‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c)) ≤ 160 / (ε / 4) ^ 5 / (‖s + 3 / 2‖ * (‖s + 3 / 2‖ + c)) := by
    rw [← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hD.le
    rw [show 12 / (ε / 4) = 12 * (1 / (ε / 4)) by ring, show 139 / (ε / 4) ^ 5 = 139 * (1 / (ε / 4) ^ 5) by ring,
      show 160 / (ε / 4) ^ 5 = 160 * (1 / (ε / 4) ^ 5) by ring]
    have : 0 < 1 / (ε / 4) ^ 5 := by positivity
    linarith
  linarith

end Cvs.Prolate.Mellin.FrozenRootCanonicalLog
