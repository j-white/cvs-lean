import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.RegularSolutionChiVariation
import Cvs.Prolate.RegularSolutionEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A Robin cell carries a phase increment of exactly `π` at the rate `θ' = (4c/3)N/((cy)² + y'²)`

Between consecutive Robin nodes `σ < σ'` through `χ`, `θ = arg(z(s) z̄(σ)) + arg z(σ)`, `z = cy(½) + i y'(½)`, is
continuous on `[σ, σ']`, has derivative `nodeRate c s` inside, satisfies `y' cos θ = cy sin θ` and `θ(σ') = θ(σ) + π`;
so some interior point has `nodeRate·(σ' − σ) = π`, and a lower bound `L` on the rate bounds the cell by `π/L`.
-/

noncomputable section

open Real Set Filter Topology Complex
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC)
open Cvs.Prolate.RegularSolutionChiVariation (regDot regUDot hasDerivAt_regSol_regDot hasDerivAt_regU_chi)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass regV_half nodeMass_eq)
open Cvs.Prolate.Gram.RobinNodeLatticeDualFloor (robinW)

namespace Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement
open Cvs.ZeroCounting

variable {c χ σ σ' : ℝ}

/-- The Robin node rate `θ' = (4c/3)N/((c y(½))² + y'(½)²)`. -/
def nodeRate (c σ : ℝ) : ℝ :=
  4 * c / 3 * nodeMass c σ / ((c * regSol (sqC c) σ (1 / 2)) ^ 2 + regV (sqC c) σ (1 / 2) ^ 2)

/-- Consecutive Robin nodes `σ < σ'` through `χ`: both nodes, and no node strictly between. -/
def ConsecNodes (c χ σ σ' : ℝ) : Prop :=
  σ < σ' ∧ robinW c χ σ = 0 ∧ robinW c χ σ' = 0 ∧ ∀ s ∈ Ioo σ σ', robinW c χ s ≠ 0

/-- The Robin vector `z(s) = c y(½) + i y'(½)`. -/
def robinZ (c s : ℝ) : ℂ := (c * regSol (sqC c) s (1 / 2) : ℝ) + (regV (sqC c) s (1 / 2) : ℝ) * I

theorem robinZ_re (c s : ℝ) : (robinZ c s).re = c * regSol (sqC c) s (1 / 2) := by simp [robinZ]

theorem robinZ_im (c s : ℝ) : (robinZ c s).im = regV (sqC c) s (1 / 2) := by simp [robinZ]

/-- `(cy)² + y'² > 0` at `½`. -/
theorem refNorm_pos (hc : c ≠ 0) (s : ℝ) :
    0 < (c * regSol (sqC c) s (1 / 2)) ^ 2 + regV (sqC c) s (1 / 2) ^ 2 := by
  have h := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.ref_pos c s
  rw [regV_half]
  rcases (show regSol (sqC c) s (1 / 2) ≠ 0 ∨ regU (sqC c) s (1 / 2) ≠ 0 by
    by_contra hh; push Not at hh; rw [hh.1, hh.2] at h; norm_num at h) with h0 | h0
  · have : 0 < (c * regSol (sqC c) s (1 / 2)) ^ 2 := by positivity
    nlinarith [sq_nonneg (-(4 / 3) * regU (sqC c) s (1 / 2))]
  · have : 0 < (-(4 / 3) * regU (sqC c) s (1 / 2)) ^ 2 := by positivity
    nlinarith [sq_nonneg (c * regSol (sqC c) s (1 / 2))]

theorem robinZ_ne_zero (hc : c ≠ 0) (s : ℝ) : robinZ c s ≠ 0 := by
  intro h
  have := refNorm_pos hc s
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  rw [robinZ_re] at h1; rw [robinZ_im] at h2
  simp only [Complex.zero_re, Complex.zero_im] at h1 h2
  rw [h1, h2] at this; norm_num at this

theorem nodeRate_pos (hc : 0 < c) (s : ℝ) : 0 < nodeRate c s := by
  unfold nodeRate
  have := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos c s
  have := refNorm_pos hc.ne' s
  positivity

theorem hasDerivAt_robinZ (c s : ℝ) :
    HasDerivAt (robinZ c) ((c * regDot (sqC c) s (1 / 2) : ℝ) +
      ((-(4 / 3) * regUDot (sqC c) s (1 / 2) : ℝ) : ℂ) * I) s := by
  have hX := ((hasDerivAt_regSol_regDot (sqC c) s (1 / 2)).const_mul c).ofReal_comp
  have hY : HasDerivAt (fun s => regV (sqC c) s (1 / 2)) (-(4 / 3) * regUDot (sqC c) s (1 / 2)) s := by
    have := (hasDerivAt_regU_chi (sqC c) s (show (-1 : ℝ) < 1 / 2 by norm_num)).const_mul (-(4 / 3 : ℝ))
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    exact regV_half c r
  exact hX.add (hY.ofReal_comp.mul_const I)

/-- The imaginary part of `z(s) z̄(σ)` is `−(4c/3) W(σ, s)`. -/
theorem im_robinZ_mul_conj (c σ s : ℝ) :
    (robinZ c s * (starRingEnd ℂ) (robinZ c σ)).im = -(4 * c / 3) * robinW c σ s := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, robinZ_re, robinZ_im]
  unfold robinW
  rw [regV_half, regV_half]
  ring

/-- **The Robin angle relation**: for `θ = arg(z(s) z̄(σ)) + arg z(σ)`, `y' cos θ = c y sin θ`. -/
theorem angle_rel (hc : c ≠ 0) (σ s : ℝ) :
    regV (sqC c) s (1 / 2) * Real.cos (arg (robinZ c s * (starRingEnd ℂ) (robinZ c σ)) + arg (robinZ c σ)) =
      c * regSol (sqC c) s (1 / 2) *
        Real.sin (arg (robinZ c s * (starRingEnd ℂ) (robinZ c σ)) + arg (robinZ c σ)) := by
  set a := robinZ c s * (starRingEnd ℂ) (robinZ c σ)
  set b := robinZ c σ
  have hb : b ≠ 0 := robinZ_ne_zero hc σ
  have ha : a ≠ 0 := mul_ne_zero (robinZ_ne_zero hc s) ((map_ne_zero _).mpr hb)
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg ha, Complex.cos_arg hb, Complex.sin_arg, Complex.sin_arg]
  have hab : a * b = robinZ c s * (Complex.normSq b : ℂ) := by
    simp only [a, b]; rw [mul_assoc, Complex.normSq_eq_conj_mul_self]
  have hre : a.re * b.re - a.im * b.im = (robinZ c s).re * Complex.normSq b := by
    have := congrArg Complex.re hab
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
    linarith
  have him : a.re * b.im + a.im * b.re = (robinZ c s).im * Complex.normSq b := by
    have := congrArg Complex.im hab
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero] at this
    linarith
  rw [robinZ_re c s] at hre; rw [robinZ_im c s] at him
  have key : regV (sqC c) s (1 / 2) * (a.re * b.re - a.im * b.im) =
      c * regSol (sqC c) s (1 / 2) * (a.im * b.re + a.re * b.im) := by
    linear_combination regV (sqC c) s (1 / 2) * hre - c * regSol (sqC c) s (1 / 2) * him
  have e : ∀ x y : ℝ, x / ‖a‖ * (y / ‖b‖) = x * y / (‖a‖ * ‖b‖) := fun x y => div_mul_div_comm x ‖a‖ y ‖b‖
  rw [e, e, e, e, ← sub_div, ← add_div, mul_div_assoc', mul_div_assoc', key]

/-- At consecutive nodes, `W(σ, s) ≠ 0` strictly between them and `W(σ, σ') = 0`. -/
theorem robinW_self_ne (h : ConsecNodes c χ σ σ') :
    (∀ s ∈ Ioo σ σ', robinW c σ s ≠ 0) ∧ robinW c σ σ' = 0 := by
  obtain ⟨-, hσ, hσ', hne⟩ := h
  refine ⟨fun s hs => ?_, Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinW_nodes hσ hσ'⟩
  have e : robinW c σ s = Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinR c χ σ * robinW c χ s := by
    rw [Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinW_anti, Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinW_node hσ s, Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinW_anti c χ s]; ring
  rw [e]
  exact mul_ne_zero (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinR_ne_zero hσ) (hne s hs)

theorem continuous_robinW (c σ : ℝ) : Continuous fun s => robinW c σ s := by
  have hy : Continuous fun s => regSol (sqC c) s (1 / 2) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_regSol_regDot (sqC c) s (1 / 2)).continuousAt
  have hU : Continuous fun s => regU (sqC c) s (1 / 2) :=
    continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_regU_chi (sqC c) s (show (-1 : ℝ) < 1 / 2 by norm_num)).continuousAt
  unfold robinW
  fun_prop

/-- **The sign inside a cell**: `W(σ, s) < 0` strictly between consecutive nodes. -/
theorem robinW_neg (h : ConsecNodes c χ σ σ') : ∀ s ∈ Ioo σ σ', robinW c σ s < 0 := by
  obtain ⟨hne, -⟩ := robinW_self_ne h
  have hlt := h.1
  -- the derivative at `σ` is `−N(σ) < 0`
  have hd : HasDerivAt (fun s => robinW c σ s)
      (regSol (sqC c) σ (1 / 2) * regUDot (sqC c) σ (1 / 2) - regU (sqC c) σ (1 / 2) * regDot (sqC c) σ (1 / 2))
      σ := by
    have hy := hasDerivAt_regSol_regDot (sqC c) σ (1 / 2)
    have hU := hasDerivAt_regU_chi (sqC c) σ (show (-1 : ℝ) < 1 / 2 by norm_num)
    unfold robinW
    exact (hU.const_mul _).sub (hy.const_mul _)
  have hval : regSol (sqC c) σ (1 / 2) * regUDot (sqC c) σ (1 / 2) -
      regU (sqC c) σ (1 / 2) * regDot (sqC c) σ (1 / 2) = -nodeMass c σ := by
    rw [nodeMass_eq]; ring
  rw [hval] at hd
  have hN := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos c σ
  have hev := Cvs.Prolate.EdgeCentreSign.eventually_mul_deriv_pos hd (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinW_self c σ) (by linarith)
  obtain ⟨s₀, hs₀, hs₀I⟩ := (hev.and (Ioo_mem_nhdsGT hlt)).exists
  have hs₀neg : robinW c σ s₀ < 0 := by
    by_contra hh; push Not at hh
    have : robinW c σ s₀ * -nodeMass c σ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh (by linarith)
    linarith
  intro s hs
  by_contra hpos; push Not at hpos
  have hpos' : 0 < robinW c σ s := lt_of_le_of_ne hpos (hne s hs).symm
  have hcont := (continuous_robinW c σ).continuousOn (s := uIcc s₀ s)
  obtain ⟨r, hr, hr0⟩ := intermediate_value_uIcc hcont (show (0 : ℝ) ∈ uIcc (robinW c σ s₀) (robinW c σ s) by
    rw [uIcc_of_le (by linarith)]; exact ⟨hs₀neg.le, hpos⟩)
  have hrI : r ∈ Ioo σ σ' := by
    rcases le_total s₀ s with h1 | h1
    · rw [uIcc_of_le h1] at hr; exact ⟨hs₀I.1.trans_le hr.1, hr.2.trans_lt hs.2⟩
    · rw [uIcc_of_ge h1] at hr; exact ⟨hs.1.trans_le hr.1, hr.2.trans_lt hs₀I.2⟩
  exact hne r hrI hr0

/-- **The cell angle**: between consecutive nodes there is a continuous Robin angle with `θ' = nodeRate` inside,
`θ(σ') = θ(σ) + π` and `y' cos θ = cy sin θ` everywhere. -/
theorem cell_angle (hc : 0 < c) (h : ConsecNodes c χ σ σ') :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc σ σ') ∧ (∀ s ∈ Ioo σ σ', HasDerivAt θ (nodeRate c s) s) ∧
      θ σ' = θ σ + π ∧
      ∀ s, regV (sqC c) s (1 / 2) * Real.cos (θ s) = c * regSol (sqC c) s (1 / 2) * Real.sin (θ s) := by
  set b := robinZ c σ
  set ζ : ℝ → ℂ := fun s => robinZ c s * (starRingEnd ℂ) b with hζ
  set θ : ℝ → ℝ := fun s => arg (ζ s) + arg b with hθ
  have hlt := h.1
  have hrel : ∀ s, regV (sqC c) s (1 / 2) * Real.cos (θ s) = c * regSol (sqC c) s (1 / 2) * Real.sin (θ s) :=
    fun s => angle_rel hc.ne' σ s
  have hb : b ≠ 0 := robinZ_ne_zero hc.ne' σ
  have hζne : ∀ s, ζ s ≠ 0 := fun s => mul_ne_zero (robinZ_ne_zero hc.ne' s) ((map_ne_zero _).mpr hb)
  have hζim : ∀ s, (ζ s).im = -(4 * c / 3) * robinW c σ s := fun s => im_robinZ_mul_conj c σ s
  have hneg := robinW_neg h
  have himpos : ∀ s ∈ Ioo σ σ', 0 < (ζ s).im := fun s hs => by
    rw [hζim]; have := hneg s hs; nlinarith
  -- `ζ(σ) = |b|² > 0`
  have hζσ : ζ σ = (Complex.normSq b : ℂ) := by simp only [hζ]; rw [Complex.mul_conj]
  have hζσre : 0 < (ζ σ).re := by rw [hζσ]; simp [Complex.normSq_pos.mpr hb]
  have hargσ : arg (ζ σ) = 0 := by rw [hζσ]; exact arg_ofReal_of_nonneg (Complex.normSq_nonneg b)
  -- derivative inside
  have hζd : ∀ s, HasDerivAt ζ (((c * regDot (sqC c) s (1 / 2) : ℝ) +
      ((-(4 / 3) * regUDot (sqC c) s (1 / 2) : ℝ) : ℂ) * I) * (starRingEnd ℂ) b) s :=
    fun s => (hasDerivAt_robinZ c s).mul_const _
  have hderiv : ∀ s, ζ s ∈ slitPlane → HasDerivAt θ (nodeRate c s) s := by
    intro s hs
    have hlog := (hζd s).clog_real hs
    have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hlog
    obtain ⟨d, harg⟩ : ∃ d, HasDerivAt θ d s := ⟨_, by
      have := him.add_const (arg b)
      simp only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] at this
      exact this⟩
    have hpr := Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate.prufer_rate harg (Eventually.of_forall fun r => hrel r)
    have hR := refNorm_pos hc.ne' s
    refine harg.congr_deriv ?_
    unfold nodeRate
    rw [eq_div_iff hR.ne']
    exact hpr
  have hderivI : ∀ s ∈ Ioo σ σ', HasDerivAt θ (nodeRate c s) s := fun s hs =>
    hderiv s (Or.inr (himpos s hs).ne')
  -- the endpoint `σ'`
  have him' : (ζ σ').im = 0 := by rw [hζim, (robinW_self_ne h).2, mul_zero]
  have hre' : (ζ σ').re < 0 := by
    have hne : (ζ σ').re ≠ 0 := by
      intro h0; apply hζne σ'; exact Complex.ext h0 him'
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact h1
    exfalso
    have hcontAt : ∀ s ∈ Icc σ σ', ContinuousAt θ s := by
      intro s hs
      have hsl : ζ s ∈ slitPlane := by
        rcases eq_or_lt_of_le hs.1 with h2 | h2
        · rw [← h2]; exact Or.inl hζσre
        rcases eq_or_lt_of_le hs.2 with h3 | h3
        · rw [h3]; exact Or.inl h1
        exact Or.inr (himpos s ⟨h2, h3⟩).ne'
      exact (hderiv s hsl).continuousAt
    obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope θ (nodeRate c) hlt
      (fun s hs => (hcontAt s hs).continuousWithinAt) hderivI
    have hargσ' : arg (ζ σ') = 0 := by
      have : ζ σ' = ((ζ σ').re : ℂ) := Complex.ext (by simp) (by simp [him'])
      rw [this]; exact arg_ofReal_of_nonneg h1.le
    have hdiff : θ σ' - θ σ = 0 := by simp only [hθ, hargσ, hargσ']; ring
    rw [hdiff, zero_div] at hξe
    exact (nodeRate_pos hc ξ).ne' hξe
  have hargσ' : arg (ζ σ') = π := Complex.arg_eq_pi_iff.mpr ⟨hre', him'⟩
  refine ⟨θ, ?_, hderivI, ?_, hrel⟩
  · intro s hs
    rcases eq_or_lt_of_le hs.2 with h3 | h3
    · -- continuity within at `σ'`
      rw [h3]
      have hcw := Complex.continuousWithinAt_arg_of_re_neg_of_im_zero hre' him'
      have hζc : ContinuousWithinAt ζ (Icc σ σ') σ' :=
        (hζd σ').continuousAt.continuousWithinAt
      have hmaps : MapsTo ζ (Icc σ σ') {z : ℂ | 0 ≤ z.im} := by
        intro r hr
        show 0 ≤ (ζ r).im
        rcases eq_or_lt_of_le hr.1 with h2 | h2
        · rw [← h2, hζσ]; simp
        rcases eq_or_lt_of_le hr.2 with h4 | h4
        · rw [h4, him']
        exact (himpos r ⟨h2, h4⟩).le
      exact (hcw.comp hζc hmaps).add continuousWithinAt_const
    · have hsl : ζ s ∈ slitPlane := by
        rcases eq_or_lt_of_le hs.1 with h2 | h2
        · rw [← h2]; exact Or.inl hζσre
        exact Or.inr (himpos s ⟨h2, h3⟩).ne'
      exact (hderiv s hsl).continuousAt.continuousWithinAt
  · simp only [hθ, hargσ, hargσ']; ring

/-- **The cell identity**: some point strictly inside a Robin cell has `nodeRate·(σ' − σ) = π`. -/
theorem exists_nodeRate_mul_eq (hc : 0 < c) (h : ConsecNodes c χ σ σ') :
    ∃ ξ ∈ Ioo σ σ', nodeRate c ξ * (σ' - σ) = π := by
  obtain ⟨θ, hcont, hd, hπ, -⟩ := cell_angle hc h
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope θ (nodeRate c) h.1 hcont hd
  refine ⟨ξ, hξ, ?_⟩
  rw [hξe, hπ]
  have : σ' - σ ≠ 0 := (sub_pos.mpr h.1).ne'
  field_simp; ring

/-- **The cell length**: if `nodeRate ≥ L > 0` on the part of the cell below `σ + π/L`, then `σ' − σ ≤ π/L`. -/
theorem cell_length_le (hc : 0 < c) (h : ConsecNodes c χ σ σ') {L : ℝ} (hL : 0 < L)
    (hr : ∀ s ∈ Ioo σ σ', s < σ + π / L → L ≤ nodeRate c s) : σ' - σ ≤ π / L := by
  by_contra hcon; push Not at hcon
  obtain ⟨θ, hcont, hd, hπ, -⟩ := cell_angle hc h
  set m := σ + π / L
  have hm : σ < m := by simp only [m]; have := div_pos pi_pos hL; linarith
  have hm' : m < σ' := by simp only [m]; linarith
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope θ (nodeRate c) hm (hcont.mono (Icc_subset_Icc le_rfl hm'.le))
    fun s hs => hd s ⟨hs.1, hs.2.trans hm'⟩
  obtain ⟨ξ', hξ', hξ'e⟩ := exists_hasDerivAt_eq_slope θ (nodeRate c) hm' (hcont.mono (Icc_subset_Icc hm.le le_rfl))
    fun s hs => hd s ⟨hm.trans hs.1, hs.2⟩
  have h1 : L ≤ nodeRate c ξ := hr ξ ⟨hξ.1, hξ.2.trans hm'⟩ hξ.2
  have h2 : 0 < nodeRate c ξ' := nodeRate_pos hc ξ'
  have hmσ : m - σ = π / L := by simp only [m]; ring
  rw [hmσ] at hξe
  have e1 : θ m - θ σ = nodeRate c ξ * (π / L) := by
    rw [hξe]; field_simp
  have e2 : θ σ' - θ m = nodeRate c ξ' * (σ' - m) := by
    rw [hξ'e]; have : σ' - m ≠ 0 := (sub_pos.mpr hm').ne'; field_simp
  have h3 : π ≤ nodeRate c ξ * (π / L) := by
    calc π = L * (π / L) := by field_simp
      _ ≤ nodeRate c ξ * (π / L) := mul_le_mul_of_nonneg_right h1 (div_pos pi_pos hL).le
  have h4 : 0 < nodeRate c ξ' * (σ' - m) := mul_pos h2 (sub_pos.mpr hm')
  linarith

end Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement

end
