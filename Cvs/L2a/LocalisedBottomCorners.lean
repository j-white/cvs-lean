import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.BandTransferKernelForm
import Cvs.L2a.CleanBandDilation
import Cvs.L2a.CornerSuprema
import Cvs.L2a.CutKernelSimplified
import Cvs.L2a.CutKernels
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.QIdentityCutPoint
import Cvs.L2a.QIdentityIterated
import Cvs.L2a.RampTopQuadratic
import Cvs.L2a.ScaledBandTransfer
import Cvs.L2a.SpanPoleMellinFromRungs
import Cvs.Prolate.Envelope.RungCountEnvelope
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungCauchySplit
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Upstream.ExpDifferenceBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# LOC, bottom: the localised bottom corners

The simplified kernel at `x₀ = m`, `y = t/m` is two poles off the band, so Cvs.L2a.ScaledBandTransfer bounds `𝔅_m^si(t)²` by
`(π⁻²(f_m − cos(2ct)g_m) + collar)·W_m + (2/π)T/D²·P`; t-integration gives `L_near`, `L_far`, an `O(1/c)`
oscillation and closed collar and chirp terms, Lemma K plus the count envelope bound the exact-kernel excess,
the `m = 2` strip and the tail, and windows of mass `≤ (1 + π²d²)P` close `2Σ|∫ū𝔅_m| ≤ ℬ·P` given the `m = 2` shells.
-/

noncomputable section

namespace Cvs.L2a.LocalisedBottomCorners

open Real Set MeasureTheory Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts Cvs.L2a.OrbitGapIntegerM Cvs.Prolate.RungCauchySplit Cvs.L2a.BandTransferBandForm
open scoped ComplexConjugate

/-! ### The far gap `g₀` -/

/-- `g₀ = 3 − 4/√3`, the least gap `M − b_m` over `2 ≤ m < M`. -/
def gZero : ℝ := 3 - 4 / √3

theorem bm_two : Cvs.L2a.CornerSuprema.bm 2 = 4 / √3 := by
  unfold Cvs.L2a.CornerSuprema.bm; norm_num

theorem gZero_pos : 0 < gZero := by
  unfold gZero
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs : (5 : ℝ) / 3 < √3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [sub_pos, div_lt_iff₀ h3]; linarith

theorem gZero_lt : gZero < 13 / 16 := by
  unfold gZero
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs : √3 < 64 / 35 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have : 35 / 16 < 4 / √3 := by rw [lt_div_iff₀ h3]; linarith
  linarith

/-- **The far gap**: `g₀ ≤ M − b_m` for `2 ≤ m`, `m + 1 ≤ M`. -/
theorem M_sub_b_ge {m M : ℝ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) (hm2 : m = 2 ∨ 3 ≤ m) :
    gZero ≤ M - Cvs.L2a.CornerSuprema.bm m := by
  rcases hm2 with h | h
  · subst h; rw [bm_two]; unfold gZero; linarith
  · have h1 := Cvs.L2a.CornerSuprema.bm_sub_lt (by linarith : 1 < m)
    have h2 : m / (2 * (m ^ 2 - 1)) ≤ 3 / 16 := by
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
    have := gZero_lt
    linarith

/-- The far gap at natural `m`. -/
theorem M_sub_b_ge_nat {m M : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) :
    gZero ≤ (M : ℝ) - Cvs.L2a.CornerSuprema.bm m := by
  refine M_sub_b_ge (by exact_mod_cast hm) (by exact_mod_cast hmM) ?_
  rcases Nat.lt_or_ge m 3 with h | h
  · left; exact_mod_cast (by omega : m = 2)
  · right; exact_mod_cast h

/-! ### The simplified kernel as two poles -/

/-- The symmetrised simplified kernel in `v = ξ/c`: `β_y(v) = (μ_si)_s(cv)`. -/
def siPole (c y x : ℝ) (v : ℝ) : ℂ :=
  Cvs.L2a.QIdentityCutPoint.muSym (fun v => Cvs.L2a.CutKernelSimplified.muSi c y x (c * v)) v

/-- The two residues `A₁ = −i e^{icxy}/(2c)`, `A₂ = i conj(e^{icxy})/(2c)`. -/
def resA (c y x : ℝ) : ℂ := -I * eF c y x / (2 * c)

def resB (c y x : ℝ) : ℂ := I * conj (eF c y x) / (2 * c)

theorem norm_resA {c y x : ℝ} (hc : 0 < c) : ‖resA c y x‖ = 1 / (2 * c) := by
  unfold resA
  rw [norm_div, norm_mul, norm_neg, Complex.norm_I, (continuous_eF c y).2, one_mul,
    show ((2 : ℂ) * c) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

theorem norm_resB {c y x : ℝ} (hc : 0 < c) : ‖resB c y x‖ = 1 / (2 * c) := by
  unfold resB
  rw [norm_div, norm_mul, Complex.norm_I, RCLike.norm_conj, (continuous_eF c y).2, one_mul,
    show ((2 : ℂ) * c) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-- **Partial fractions**: `β_y(v) = A₁/(y + v) + A₂/(y − v)`. -/
theorem siPole_eq (c y x v : ℝ) :
    siPole c y x v = resA c y x / ((y + 1 * v : ℝ) : ℂ) + resB c y x / ((y + (-1) * v : ℝ) : ℂ) := by
  unfold siPole Cvs.L2a.QIdentityCutPoint.muSym Cvs.L2a.CutKernelSimplified.muSi resA resB
  have e1 : ((c * y + c * v : ℝ) : ℂ) = (c : ℂ) * ((y + 1 * v : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((c * y + c * -v : ℝ) : ℂ) = (c : ℂ) * ((y + -1 * v : ℝ) : ℂ) := by push_cast; ring
  beta_reduce
  rw [e1, e2]
  simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  generalize ((y + 1 * v : ℝ) : ℂ) = p
  generalize ((y + -1 * v : ℝ) : ℂ) = q
  ring

/-- The pole multiplier's derivatives. -/
def siPoleD (c y x : ℝ) (j : ℕ) (v : ℝ) : ℂ :=
  Cvs.L2a.ScaledBandTransfer.poleD (resA c y x) y 1 j v + Cvs.L2a.ScaledBandTransfer.poleD (resB c y x) y (-1) j v

/-- **The simplified kernel is a band multiplier**: at distance `≥ r > 0` from both poles on the band,
`N_j = (1/(cr))·j!/r^j`. -/
theorem isBandMult_siPole {c y x r δ Y : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hdist : ∀ v ∈ bandRg δ Y, r ≤ |y + v| ∧ r ≤ |y - v|) :
    IsBandMult (siPole c y x) (siPoleD c y x 1) (siPoleD c y x 2) (siPoleD c y x 3) δ Y
      (fun j => 1 / (c * r) * ((j.factorial : ℝ) / r ^ j)) := by
  have h1 := Cvs.L2a.ScaledBandTransfer.isBandMult_pole (A := resA c y x) (p := y) (q := 1) (δ := δ) (Y := Y) hr
    (fun v hv => by simpa using (hdist v hv).1)
  have h2 := Cvs.L2a.ScaledBandTransfer.isBandMult_pole (A := resB c y x) (p := y) (q := -1) (δ := δ) (Y := Y) hr
    (fun v hv => by simpa [sub_eq_add_neg] using (hdist v hv).2)
  have h := Cvs.L2a.ScaledBandTransfer.IsBandMult.add h1 h2
  have e : (fun v => resA c y x / ((y + 1 * v : ℝ) : ℂ) + resB c y x / ((y + -1 * v : ℝ) : ℂ))
      = siPole c y x := funext fun v => (siPole_eq c y x v).symm
  rw [e] at h
  refine Cvs.L2a.ScaledBandTransfer.IsBandMult.mono h fun j _ => le_of_eq ?_
  rw [norm_resA hc, norm_resB hc]
  simp only [abs_one, abs_neg, one_pow, mul_one]
  field_simp
  ring

/-- Near the band from inside: `y + r ≤ 1 − δ`, `0 ≤ y` keep both poles at distance `≥ r`. -/
theorem dist_near {y r δ Y : ℝ} (hy : 0 ≤ y) (h : y + r ≤ 1 - δ) :
    ∀ v ∈ bandRg δ Y, r ≤ |y + v| ∧ r ≤ |y - v| := by
  intro v hv
  have hv1 : 1 - δ ≤ |v| := hv.1
  constructor
  · have := abs_sub_abs_le_abs_sub v (-y)
    rw [abs_neg, abs_of_nonneg hy, sub_neg_eq_add, add_comm] at this
    linarith
  · have := abs_sub_abs_le_abs_sub v y
    rw [abs_of_nonneg hy, abs_sub_comm] at this
    linarith

/-- Beyond the band: `Y + δ + r ≤ y` keeps both poles at distance `≥ r`. -/
theorem dist_far {y r δ Y : ℝ} (h : Y + δ + r ≤ y) :
    ∀ v ∈ bandRg δ Y, r ≤ |y + v| ∧ r ≤ |y - v| := by
  intro v hv
  have hv1 : |v| ≤ Y + δ := hv.2
  have hv2 := abs_le.1 hv1
  exact ⟨by linarith [le_abs_self (y + v)], by linarith [le_abs_self (y - v)]⟩

/-! ### The band integral -/

theorem muSym_neg (μ : ℝ → ℂ) (v : ℝ) :
    Cvs.L2a.QIdentityCutPoint.muSym μ (-v) = conj (Cvs.L2a.QIdentityCutPoint.muSym μ v) := by
  unfold Cvs.L2a.QIdentityCutPoint.muSym
  rw [neg_neg, map_div₀, map_add, Complex.conj_conj, map_ofNat]
  ring

theorem norm_siPole_neg (c y x v : ℝ) : ‖siPole c y x (-v)‖ = ‖siPole c y x v‖ := by
  unfold siPole; rw [muSym_neg, RCLike.norm_conj]

theorem eF_eq (c y x : ℝ) :
    eF c y x = ((Real.cos (c * y * x) : ℝ) : ℂ) + ((Real.sin (c * y * x) : ℝ) : ℂ) * I := by
  unfold eF
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **The band density**: `‖β_y(v)‖² = (1/(4c²))(1/(y+v)² + 1/(y−v)² − 2cos(2cyx)/(y² − v²))`. -/
theorem norm_siPole_sq {c : ℝ} (hc : 0 < c) (y x v : ℝ) (hp : y + v ≠ 0) (hq : y - v ≠ 0) :
    ‖siPole c y x v‖ ^ 2
      = 1 / (4 * c ^ 2) * (1 / (y + v) ^ 2 + 1 / (y - v) ^ 2 - 2 * Real.cos (2 * (c * y * x)) / (y ^ 2 - v ^ 2)) := by
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = c * y * x := ⟨_, rfl⟩
  rw [← hθ]
  have hk := Real.sin_sq_add_cos_sq θ
  have e : siPole c y x v = (((Real.sin θ / (y + v) + Real.sin θ / (y - v)) / (2 * c) : ℝ) : ℂ)
      + (((Real.cos θ / (y - v) - Real.cos θ / (y + v)) / (2 * c) : ℝ) : ℂ) * I := by
    rw [siPole_eq, resA, resB, eF_eq, ← hθ]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have hp' : ((y + v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp
    have hq' : ((y - v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [show y + 1 * v = y + v by ring, show y + -1 * v = y - v by ring]
    push_cast at hp' hq' ⊢
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hsc : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith
  have hyv : y ^ 2 - v ^ 2 = (y + v) * (y - v) := by ring
  rw [hyv, Real.cos_two_mul]
  field_simp
  rw [hsc]
  ring

/-- The band `{|ξ| ∈ [c, cY]}` of Cvs.L2a.BandTransferBandForm. -/
def bandSet (c Y : ℝ) : Set ℝ := {ξ | |ξ| ∈ Icc c (c * Y)}

theorem measurableSet_bandSet (c Y : ℝ) : MeasurableSet (bandSet c Y) :=
  measurableSet_Icc.preimage continuous_abs.measurable

theorem bandSet_eq {c Y : ℝ} (hc : 0 < c) : bandSet c Y = Icc (-(c * Y)) (-c) ∪ Icc c (c * Y) := by
  ext ξ
  simp only [bandSet, mem_ofPred_eq, mem_Icc, mem_union]
  rcases le_or_gt 0 ξ with h | h
  · rw [abs_of_nonneg h]
    constructor
    · exact Or.inr
    · rintro (⟨h1, h2⟩ | h')
      · exact absurd h2 (by linarith)
      · exact h'
  · rw [abs_of_neg h]
    constructor
    · rintro ⟨h1, h2⟩; exact Or.inl ⟨by linarith, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by linarith, by linarith⟩
      · exact absurd h1 (by linarith)

theorem isCompact_bandSet {c Y : ℝ} (hc : 0 < c) : IsCompact (bandSet c Y) := by
  rw [bandSet_eq hc]; exact isCompact_Icc.union isCompact_Icc

/-- **The band integral of an even profile**: `∫_{|ξ|∈[c,cY]} F(ξ/c) = 2c∫₁^Y F`. -/
theorem integral_bandSet {F : ℝ → ℝ} {c Y : ℝ} (hc : 0 < c) (hY : 1 ≤ Y)
    (hF : ContinuousOn F {v | |v| ∈ Icc 1 Y}) (heven : ∀ v, F (-v) = F v) :
    ∫ ξ in bandSet c Y, F (ξ / c) = 2 * c * ∫ v in (1 : ℝ)..Y, F v := by
  have hcY : c ≤ c * Y := by nlinarith
  have hFc : ContinuousOn (fun ξ => F (ξ / c)) (bandSet c Y) := by
    refine hF.comp (continuous_id.div_const c).continuousOn fun ξ hξ => ?_
    simp only [bandSet, mem_ofPred_eq, mem_Icc] at hξ ⊢
    rw [abs_div, abs_of_pos hc, le_div_iff₀ hc, div_le_iff₀ hc]
    exact ⟨by linarith, by linarith⟩
  have hint := hFc.integrableOn_compact (μ := volume) (isCompact_bandSet hc)
  rw [bandSet_eq hc] at hint ⊢
  have hdisj : Disjoint (Icc (-(c * Y)) (-c)) (Icc c (c * Y)) := by
    rw [Set.disjoint_left]; intro ξ h1 h2; linarith [h1.2, h2.1]
  rw [setIntegral_union hdisj measurableSet_Icc (hint.mono_set subset_union_left)
    (hint.mono_set subset_union_right), integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le hcY,
    intervalIntegral.integral_comp_div _ hc.ne', intervalIntegral.integral_comp_div _ hc.ne']
  have e1 : c / c = 1 := div_self hc.ne'
  have e2 : c * Y / c = Y := by field_simp
  have e3 : -(c * Y) / c = -Y := by field_simp
  have e4 : -c / c = -1 := by field_simp
  rw [e1, e2, e3, e4]
  have hneg : ∫ v in -Y..-1, F v = ∫ v in (1 : ℝ)..Y, F v := by
    rw [← neg_neg (-1 : ℝ), ← intervalIntegral.integral_comp_neg]
    simp only [neg_neg, heven]
  rw [hneg]
  simp only [smul_eq_mul]
  ring

/-- The `v`-closed form `∫₁^Y (1/(y+v)² + 1/(y−v)²)`. -/
def fY (y Y : ℝ) : ℝ := -1 / (y + Y) + 1 / (y - Y) + 1 / (y + 1) - 1 / (y - 1)

/-- The `v`-closed form `∫₁^Y dv/(y² − v²)`. -/
def gY (y Y : ℝ) : ℝ :=
  (Real.log (y + Y) - Real.log (y - Y) - Real.log (y + 1) + Real.log (y - 1)) / (2 * y)

/-- The band main term `(4πc)⁻¹(f_Y − 2cos(2cyx)g_Y)`. -/
def bandMain (c y x Y : ℝ) : ℝ := (4 * π * c)⁻¹ * (fY y Y - 2 * Real.cos (2 * (c * y * x)) * gY y Y)

/-- Off the poles, the `v`-integral of the band density is closed: `f_Y − 2cos(2θ)g_Y`. -/
theorem integral_density_eq {y Y θ : ℝ} (hY : 1 ≤ Y) (hy : 0 < y)
    (hq : ∀ v ∈ Icc 1 Y, y - v ≠ 0) :
    ∫ v in (1 : ℝ)..Y, (1 / (y + v) ^ 2 + 1 / (y - v) ^ 2 - 2 * Real.cos (2 * θ) / (y ^ 2 - v ^ 2))
      = fY y Y - 2 * Real.cos (2 * θ) * gY y Y := by
  have hp : ∀ v ∈ Icc 1 Y, 0 < y + v := fun v hv => by linarith [hv.1]
  set G : ℝ → ℝ := fun v => -1 / (y + v) + 1 / (y - v)
      - 2 * Real.cos (2 * θ) * ((Real.log (y + v) - Real.log (y - v)) / (2 * y)) with hG
  have hu : uIcc (1 : ℝ) Y = Icc 1 Y := uIcc_of_le hY
  have hd : ∀ v ∈ uIcc (1 : ℝ) Y, HasDerivAt G
      (1 / (y + v) ^ 2 + 1 / (y - v) ^ 2 - 2 * Real.cos (2 * θ) / (y ^ 2 - v ^ 2)) v := by
    intro v hv
    rw [hu] at hv
    have h1 := hp v hv
    have h2 := hq v hv
    have hA : HasDerivAt (fun v => y + v) 1 v := (hasDerivAt_id v).const_add y
    have hB : HasDerivAt (fun v => y - v) (-1) v := by
      simpa using (hasDerivAt_id v).const_sub y
    have k1 := (hA.inv h1.ne').const_mul (-1)
    have k2 := (hB.inv h2).const_mul 1
    have k3 := (((hA.log h1.ne').sub (hB.log h2)).div_const (2 * y)).const_mul (2 * Real.cos (2 * θ))
    refine (((k1.add k2).sub k3).congr_deriv ?_).congr_of_eventuallyEq ?_
    · have : y ^ 2 - v ^ 2 = (y + v) * (y - v) := by ring
      rw [this]; field_simp; ring
    · exact Filter.Eventually.of_forall fun w => by
        simp only [hG, Pi.add_apply, Pi.sub_apply, Pi.inv_apply, div_eq_mul_inv]
  have hcont : ContinuousOn (fun v => 1 / (y + v) ^ 2 + 1 / (y - v) ^ 2
      - 2 * Real.cos (2 * θ) / (y ^ 2 - v ^ 2)) (uIcc (1 : ℝ) Y) := by
    rw [hu]
    refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
    · have h0 : ∀ v ∈ Icc 1 Y, (y + v) ^ 2 ≠ 0 := fun v hv => pow_ne_zero 2 (hp v hv).ne'
      have hg : ContinuousOn (fun v : ℝ => (y + v) ^ 2) (Icc 1 Y) := by fun_prop
      exact continuousOn_const.div₀ hg h0
    · have h0 : ∀ v ∈ Icc 1 Y, (y - v) ^ 2 ≠ 0 := fun v hv => pow_ne_zero 2 (hq v hv)
      have hg : ContinuousOn (fun v : ℝ => (y - v) ^ 2) (Icc 1 Y) :=
        (continuousOn_const.sub continuousOn_id).pow 2
      exact continuousOn_const.div₀ hg h0
    · have h0 : ∀ v ∈ Icc 1 Y, y ^ 2 - v ^ 2 ≠ 0 := fun v hv => by
        rw [show y ^ 2 - v ^ 2 = (y + v) * (y - v) by ring]
        exact mul_ne_zero (hp v hv).ne' (hq v hv)
      have hg : ContinuousOn (fun v : ℝ => y ^ 2 - v ^ 2) (Icc 1 Y) :=
        continuousOn_const.sub (continuousOn_id.pow 2)
      exact continuousOn_const.div₀ hg h0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)]
  simp only [hG, fY, gY]
  field_simp
  ring

theorem ne_of_off {y Y : ℝ} (hy : 0 < y) (hq : ∀ v ∈ Icc 1 Y, y ≠ v) {v : ℝ} (hv : |v| ∈ Icc 1 Y) :
    y + v ≠ 0 ∧ y - v ≠ 0 := by
  rcases le_or_gt 0 v with h | h
  · rw [abs_of_nonneg h] at hv
    exact ⟨by linarith, sub_ne_zero.2 (hq v hv)⟩
  · rw [abs_of_neg h] at hv
    refine ⟨fun h0 => hq (-v) hv (by linarith), by linarith⟩

theorem continuousOn_siPole {c y x Y : ℝ} (hy : 0 < y) (hq : ∀ v ∈ Icc 1 Y, y ≠ v) :
    ContinuousOn (fun v => ‖siPole c y x v‖ ^ 2) {v | |v| ∈ Icc 1 Y} := by
  have e : (fun v => ‖siPole c y x v‖ ^ 2)
      = fun v => ‖resA c y x / ((y + 1 * v : ℝ) : ℂ) + resB c y x / ((y + (-1) * v : ℝ) : ℂ)‖ ^ 2 :=
    funext fun v => by rw [siPole_eq]
  rw [e]
  refine ContinuousOn.pow (ContinuousOn.norm (ContinuousOn.add ?_ ?_)) 2
  · refine continuousOn_const.div₀ (by fun_prop) fun v hv => ?_
    have := (ne_of_off hy hq hv).1
    exact_mod_cast (by rw [one_mul]; exact this : y + 1 * v ≠ 0)
  · refine continuousOn_const.div₀ (by fun_prop) fun v hv => ?_
    have := (ne_of_off hy hq hv).2
    exact_mod_cast (by rw [neg_one_mul, ← sub_eq_add_neg]; exact this : y + -1 * v ≠ 0)

/-- **The band integral in closed form**: `(2π)⁻¹∫_{|ξ|∈[c,cY]}‖β_y(ξ/c)‖² = (4πc)⁻¹(f_Y − 2cos(2cyx)g_Y)`. -/
theorem bandInt_eq {c y x Y : ℝ} (hc : 0 < c) (hY : 1 ≤ Y) (hy : 0 < y) (hq : ∀ v ∈ Icc 1 Y, y ≠ v) :
    (2 * π)⁻¹ * ∫ ξ in bandSet c Y, ‖siPole c y x (ξ / c)‖ ^ 2 = bandMain c y x Y := by
  rw [integral_bandSet (F := fun v => ‖siPole c y x v‖ ^ 2) hc hY (continuousOn_siPole hy hq)
    (fun v => by simp only [norm_siPole_neg])]
  have hu : uIcc (1 : ℝ) Y = Icc 1 Y := uIcc_of_le hY
  have e : ∫ v in (1 : ℝ)..Y, ‖siPole c y x v‖ ^ 2
      = ∫ v in (1 : ℝ)..Y, 1 / (4 * c ^ 2) * (1 / (y + v) ^ 2 + 1 / (y - v) ^ 2
          - 2 * Real.cos (2 * (c * y * x)) / (y ^ 2 - v ^ 2)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [hu] at hv
    have hv' : |v| ∈ Icc 1 Y := by rw [abs_of_nonneg (by linarith [hv.1])]; exact hv
    obtain ⟨h1, h2⟩ := ne_of_off hy hq hv'
    exact norm_siPole_sq hc y x v h1 h2
  rw [e, intervalIntegral.integral_const_mul,
    integral_density_eq hY hy fun v hv => sub_ne_zero.2 (hq v hv), bandMain]
  field_simp

/-! ### LBT-h on the simplified kernel, pointwise in `t` -/

/-- The chirp and window factor `T = 2τ̂_r√((ΔY + 2κ_Sδ)G/π) + τ̂_r²G`, `G = 6J/(c(x₀² − 1))`. -/
def tT (c x₀ d δ r J : ℝ) : ℝ :=
  2 * tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j)
      * √((Ymax x₀ - 1 + 2 * (181 / 462) * δ) * (6 * J / (c * (x₀ ^ 2 - 1))) / π)
    + tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j) ^ 2 * (6 * J / (c * (x₀ ^ 2 - 1)))

/-- `T` is antitone in the pole distance `r`. -/
theorem tT_anti {c x₀ d δ r r₀ J : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hδ : 0 ≤ δ) (hJ : 0 ≤ J)
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) : tT c x₀ d δ r J ≤ tT c x₀ d δ r₀ J := by
  have hx : 0 < x₀ ^ 2 - 1 := by nlinarith
  have hN : ∀ j ≤ 3, 0 ≤ (j.factorial : ℝ) / r ^ j := fun j _ => by
    have : 0 < r := lt_of_lt_of_le hr₀ hr
    positivity
  have hle : ∀ j ≤ 3, (j.factorial : ℝ) / r ^ j ≤ (j.factorial : ℝ) / r₀ ^ j := fun j _ => by
    gcongr
  have h1 := Cvs.L2a.ScaledBandTransfer.tauHat_mono hc.le hd hxd hδ hN hle
  have h0 := Cvs.L2a.ScaledBandTransfer.tauHat_nonneg hc.le hd hxd hδ hN
  have hG : 0 ≤ 6 * J / (c * (x₀ ^ 2 - 1)) := by positivity
  unfold tT
  gcongr

theorem tT_nonneg {c x₀ d δ r J : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hδ : 0 ≤ δ) (hJ : 0 ≤ J)
    (hr : 0 < r) : 0 ≤ tT c x₀ d δ r J := by
  have hx : 0 < x₀ ^ 2 - 1 := by nlinarith
  have h0 := Cvs.L2a.ScaledBandTransfer.tauHat_nonneg (N := fun j => (j.factorial : ℝ) / r ^ j) hc.le hd hxd hδ
    fun j _ => by positivity
  unfold tT
  positivity

/-- `Re Σaₙ Sₙ[μ_si] = Σaₙ Sₙ[β_y(·/c)]`. -/
theorem re_sum_smp_muSi {ι : Type} [Fintype ι] (a : ι → ℝ) {c : ℝ} (hc : c ≠ 0) (χ : ι → ℝ)
    (g : ι → ℝ → ℝ) (y x₀ : ℝ) :
    (((∑ i, (a i : ℂ) * smp (Cvs.L2a.CutKernelSimplified.muSi c y x₀) c (χ i) (g i) x₀).re : ℝ) : ℂ)
      = ∑ i, (a i : ℂ) * smp (fun ξ => siPole c y x₀ (ξ / c)) c (χ i) (g i) x₀ := by
  have h := Cvs.L2a.ScaledBandTransfer.smp_sPart a (fun v => Cvs.L2a.CutKernelSimplified.muSi c y x₀ (c * v)) c χ g x₀
  have e : (fun ξ => Cvs.L2a.CutKernelSimplified.muSi c y x₀ (c * (ξ / c))) = Cvs.L2a.CutKernelSimplified.muSi c y x₀ :=
    funext fun ξ => by rw [mul_div_cancel₀ ξ hc]
  simp only [e] at h
  exact h

/-- `‖β_y(v)‖ ≤ (1/(2c))(1/|y + v| + 1/|y − v|)`. -/
theorem norm_siPole_le {c : ℝ} (hc : 0 < c) (y x v : ℝ) :
    ‖siPole c y x v‖ ≤ 1 / (2 * c) * (1 / |y + v| + 1 / |y - v|) := by
  rw [siPole_eq]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_div, norm_div, norm_resA hc, norm_resB hc, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, show y + 1 * v = y + v by ring, show y + -1 * v = y - v by ring]
  ring

/-- The pole pair seen from inside the band: `1/|y + v| + 1/|y − v| ≤ 2A/(A² − y²)` for `0 ≤ y < A ≤ |v|`. -/
theorem inv_add_inv_near {y A v : ℝ} (hy : 0 ≤ y) (hyA : y < A) (hv : A ≤ |v|) :
    1 / |y + v| + 1 / |y - v| ≤ 2 * A / (A ^ 2 - y ^ 2) := by
  have hu : 0 < |v| - y := by linarith
  have key : 1 / |y + v| + 1 / |y - v| = 1 / (|v| + y) + 1 / (|v| - y) := by
    rcases le_or_gt 0 v with h | h
    · rw [abs_of_nonneg h] at hv ⊢
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; ring
    · rw [abs_of_neg h] at hv ⊢
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; ring
  rw [key, div_add_div _ _ (by linarith) hu.ne', div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ |v| - A) (by nlinarith : (0 : ℝ) ≤ |v| * A + y ^ 2)]

/-- The pole pair seen from beyond the band: `1/|y + v| + 1/|y − v| ≤ 2y/(y² − B²)` for `|v| ≤ B < y`. -/
theorem inv_add_inv_far {y B v : ℝ} (hB : 0 ≤ B) (hyB : B < y) (hv : |v| ≤ B) :
    1 / |y + v| + 1 / |y - v| ≤ 2 * y / (y ^ 2 - B ^ 2) := by
  have hv' := abs_le.1 hv
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith), div_add_div _ _ (by linarith) (by linarith),
    div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  have : v ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg v) hv 2
  nlinarith

/-- **The corner at one `t`**: with both poles at distance `≥ r` from the band of collar `δ` and `‖β_y‖ ≤ n₀ ≤ 1/(cr)`
there, `(Re Σaₙ Sₙ[μ_si])² ≤ ((4πc)⁻¹(f_Y − 2cos(2cyx₀)g_Y) + c(2κ_S/π)δn₀²)·W + T/(cr²)·∫₁^∞Φ²`. -/
theorem corner_local {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {X x₀ y d δ r n₀ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hX : 2 ≤ X) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hx₀ : x₀ ∈ Icc (6 / 5 : ℝ) X)
    (hd : 0 < d) (hxd : 1 < x₀ - d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (hy : 0 < y)
    (hdist : ∀ v ∈ bandRg δ (Ymax x₀), r ≤ |y + v| ∧ r ≤ |y - v|)
    (hn0 : ∀ v ∈ bandRg δ (Ymax x₀), ‖siPole c y x₀ v‖ ≤ n₀) (hn0r : n₀ ≤ 1 / (c * r)) :
    (∑ i, (a i : ℂ) * smp (Cvs.L2a.CutKernelSimplified.muSi c y x₀) c (χ i) (g i) x₀).re ^ 2
      ≤ (bandMain c y x₀ (Ymax x₀) + c * (2 * (181 / 462) / π * δ * n₀ ^ 2))
          * (∫ x in (x₀ - d)..(x₀ + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + tT c x₀ d δ r (Fintype.card ι) / (c * r ^ 2) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hx1 : 1 < x₀ := by linarith [hx₀.1]
  have hY := one_le_Ymax hx1
  have hμ0 := isBandMult_siPole (x := x₀) hc0 hr hdist
  have hμ : IsBandMult (siPole c y x₀) (siPoleD c y x₀ 1) (siPoleD c y x₀ 2) (siPoleD c y x₀ 3) δ (Ymax x₀)
      (fun j => if j = 0 then n₀ else 1 / (c * r) * ((j.factorial : ℝ) / r ^ j)) :=
    { d0 := hμ0.d0, d1 := hμ0.d1, d2 := hμ0.d2, c3 := hμ0.c3
      bd := fun v hv => by
        obtain ⟨_, b1, b2, b3⟩ := hμ0.bd v hv
        exact ⟨by simpa using hn0 v hv, by simpa using b1, by simpa using b2, by simpa using b3⟩ }
  have hNb : ∀ j ≤ 3, (fun j => if j = 0 then n₀ else 1 / (c * r) * ((j.factorial : ℝ) / r ^ j)) j
      ≤ 1 / (c * r) * ((j.factorial : ℝ) / r ^ j) := fun j _ => by
    by_cases h0 : j = 0
    · subst h0; simpa using hn0r
    · simp [h0]
  have hq : ∀ v ∈ Icc 1 (Ymax x₀), y ≠ v := fun v hv h0 => by
    have hb : v ∈ bandRg δ (Ymax x₀) := by
      show |v| ∈ Icc (1 - δ) (Ymax x₀ + δ)
      rw [abs_of_nonneg (by linarith [hv.1])]; exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have := (hdist v hb).2
    rw [h0, sub_self, abs_zero] at this; linarith
  have hBi : IntegrableOn (fun ξ => ‖siPole c y x₀ (ξ / c)‖ ^ 2) (bandSet c (Ymax x₀)) := by
    refine ContinuousOn.integrableOn_compact (isCompact_bandSet hc0) ?_
    refine (continuousOn_siPole hy hq).comp (continuous_id.div_const c).continuousOn fun ξ hξ => ?_
    simp only [bandSet, mem_ofPred_eq, mem_Icc] at hξ ⊢
    rw [abs_div, abs_of_pos hc0, le_div_iff₀ hc0, div_le_iff₀ hc0]
    exact ⟨by linarith, by linarith⟩
  have h := Cvs.L2a.ScaledBandTransfer.lbt_band_scaled (r := r) (Nb := 1 / (c * r)) a hg hg₁ hg₂c hang hc hχ0 hχc hχi
    hX hM hx₀ hd hxd hδ hδ1 hμ hNb (measurableSet_bandSet c (Ymax x₀)) (fun ξ hξ => hξ) hBi
  rw [← re_sum_smp_muSi a hc0.ne' χ g y x₀, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    bandInt_eq hc0 hY hy hq] at h
  refine h.trans (le_of_eq ?_)
  have e2 : c * (1 / (c * r)) ^ 2 * (tT c x₀ d δ r (Fintype.card ι)) = tT c x₀ d δ r (Fintype.card ι) / (c * r ^ 2) := by
    field_simp
  rw [← e2]
  rfl

/-! ### The bottom corner in `t` -/

section tform

variable {ι : Type} [Fintype ι]

/-- The simplified bottom kernel `𝔅_m^si(t) = −(κ/m)Re Σᵢaᵢ Sᵢ[μ_si]` at `x₀ = m`, `y = t/m`. -/
def bSi (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  -(√(2 * c / π) / m) * (∑ i, (a i : ℂ) * smp (Cvs.L2a.CutKernelSimplified.muSi c (t / m) m) c (χ i) (g i) m).re

/-- `g_m(t) = ∫₁^{Y(m)} dv/(t² − m²v²)` in closed form. -/
def gT (m t : ℝ) : ℝ := gY (t / m) (Ymax m) / m ^ 2

theorem bSi_sq (c : ℝ) (hc : 0 ≤ c) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (m : ℕ) (t : ℝ) :
    bSi c χ g a m t ^ 2 = 2 * c / (π * m ^ 2)
      * (∑ i, (a i : ℂ) * smp (Cvs.L2a.CutKernelSimplified.muSi c (t / m) m) c (χ i) (g i) m).re ^ 2 := by
  unfold bSi
  rw [mul_pow, neg_sq, div_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- `f_Y(t/m, Y(m)) = 2m² f_m(t)`. -/
theorem fY_eq {m t : ℝ} (hm : 1 < m) (ht : 0 < t) (htm : t ≠ m) (htb : t ≠ Cvs.L2a.CornerSuprema.bm m) :
    fY (t / m) (Ymax m) = 2 * m ^ 2 * Cvs.L2a.CornerSuprema.fm m t := by
  have hm0 : 0 < m := by linarith
  have hs : 0 < √(m ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith)
  set s := √(m ^ 2 - 1) with hsd
  have hb : Cvs.L2a.CornerSuprema.bm m = m ^ 2 / s := rfl
  have hY : Ymax m = m / s := rfl
  rw [hb] at htb
  have h1 : t * s - m ^ 2 ≠ 0 := fun h => htb (by field_simp; linarith)
  have h2 : t - m ≠ 0 := sub_ne_zero.2 htm
  have h3 : t * s + m ^ 2 ≠ 0 := by positivity
  unfold fY Cvs.L2a.CornerSuprema.fm
  rw [hY, hb]
  have e1 : t / m + m / s = (t * s + m ^ 2) / (m * s) := by field_simp
  have e2 : t / m - m / s = (t * s - m ^ 2) / (m * s) := by field_simp
  have e3 : t / m + 1 = (t + m) / m := by field_simp
  have e4 : t / m - 1 = (t - m) / m := by field_simp
  have e5 : m ^ 2 - t ^ 2 = -((t - m) * (t + m)) := by ring
  have e6 : (m ^ 2 / s) ^ 2 - t ^ 2 = -((t * s - m ^ 2) * (t * s + m ^ 2)) / s ^ 2 := by field_simp; ring
  rw [e1, e2, e3, e4, e5, e6]
  have h4 : t + m ≠ 0 := by positivity
  field_simp
  ring

/-- **The band main term in `t`**: `(κ/m)²(4πc)⁻¹(f_Y − 2cos(2ct)g_Y) = π⁻²(f_m(t) − cos(2ct)g_m(t))`. -/
theorem mainB_eq {c m t : ℝ} (hc : 0 < c) (hm : 1 < m) (ht : 0 < t) (htm : t ≠ m)
    (htb : t ≠ Cvs.L2a.CornerSuprema.bm m) :
    2 * c / (π * m ^ 2) * bandMain c (t / m) m (Ymax m)
      = (π ^ 2)⁻¹ * (Cvs.L2a.CornerSuprema.fm m t - Real.cos (2 * c * t) * gT m t) := by
  have hm0 : 0 < m := by linarith
  unfold bandMain gT
  rw [fY_eq hm ht htm htb, show c * (t / m) * m = c * t by field_simp, show 2 * (c * t) = 2 * c * t by ring]
  field_simp
  ring

variable {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

/-- **The near corner at one `t`**: for `0 < t < a = m(1 − δ)` and `0 < r₀ ≤ 1 − δ − t/m`,
`𝔅_m^si(t)² ≤ (π⁻²(f_m − cos(2ct)g_m) + (4κ_S/π²)δa²/(a² − t²)²)·W_m + (2/π)T(r₀)/(a − t)²·∫₁^∞Φ²`. -/
theorem bSi_sq_le_near (a : ι → ℝ) {M m : ℕ} {d δ t r₀ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hm : 2 ≤ m) (hmM : m ≤ M)
    (hd : 0 < d) (hxd : 1 < (m : ℝ) - d) (hδ : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) (hta : t < m * (1 - δ))
    (hr₀ : 0 < r₀) (hr₀t : r₀ ≤ 1 - δ - t / m) :
    bSi c χ g a m t ^ 2
      ≤ ((π ^ 2)⁻¹ * (Cvs.L2a.CornerSuprema.fm m t - Real.cos (2 * c * t) * gT m t)
          + 4 * (181 / 462) / π ^ 2 * δ * (m * (1 - δ)) ^ 2 / ((m * (1 - δ)) ^ 2 - t ^ 2) ^ 2)
          * (∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + 2 / π * tT c m d δ r₀ (Fintype.card ι) / (m * (1 - δ) - t) ^ 2
          * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hMr : (m : ℝ) ≤ M := by exact_mod_cast hmM
  obtain ⟨A, hA⟩ : ∃ A, A = 1 - δ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = t / m := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  have hyA : y < A := by rw [hy, hA, div_lt_iff₀ hm0]; linarith
  obtain ⟨r, hr⟩ : ∃ r, r = A - y := ⟨_, rfl⟩
  have hr0 : 0 < r := by linarith
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = 1 / c * (A / (A ^ 2 - y ^ 2)) := ⟨_, rfl⟩
  have hAy : 0 < A ^ 2 - y ^ 2 := by nlinarith
  have hn0 : ∀ v ∈ bandRg δ (Ymax m), ‖siPole c y m v‖ ≤ n₀ := fun v hv => by
    refine (norm_siPole_le hc0 y m v).trans ?_
    have := inv_add_inv_near hy0.le hyA (by have := hv.1; rw [hA]; linarith : A ≤ |v|)
    rw [hn₀]
    calc 1 / (2 * c) * (1 / |y + v| + 1 / |y - v|) ≤ 1 / (2 * c) * (2 * A / (A ^ 2 - y ^ 2)) := by gcongr
      _ = _ := by ring
  have hn0r : n₀ ≤ 1 / (c * r) := by
    have h1 : 0 < A - y := by linarith
    have h2 : 0 < A + y := by linarith
    rw [hn₀, hr, show A ^ 2 - y ^ 2 = (A - y) * (A + y) by ring, one_div_mul_eq_div, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos h1 hc0) hy0]
  have h := corner_local (X := M) (x₀ := m) (y := y) (d := d) (δ := δ) (r := r) a hg hg₁ hg₂c hang hc hχ0 hχc hχi
    (by linarith) hM ⟨by linarith, hMr⟩ hd hxd hδ hδ1.le hr0 hy0 (dist_near hy0.le (by rw [hr, hA]; linarith))
    hn0 hn0r
  have hW : 0 ≤ ∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hQ : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have hk : 0 ≤ 2 * c / (π * m ^ 2) := by positivity
  rw [bSi_sq c hc0.le, ← hy]
  have hmain : 2 * c / (π * m ^ 2) * bandMain c y m (Ymax m)
      = (π ^ 2)⁻¹ * (Cvs.L2a.CornerSuprema.fm m t - Real.cos (2 * c * t) * gT m t) :=
    hy ▸ mainB_eq hc0 (by linarith) ht (by nlinarith) (by
      have := Cvs.L2a.CornerSuprema.lt_bm (by linarith : (1 : ℝ) < m); nlinarith)
  have hcoll : 2 * c / (π * m ^ 2) * (c * (2 * (181 / 462) / π * δ * n₀ ^ 2))
      = 4 * (181 / 462) / π ^ 2 * δ * (m * (1 - δ)) ^ 2 / ((m * (1 - δ)) ^ 2 - t ^ 2) ^ 2 := by
    rw [hn₀, hy, hA]
    have : ((m : ℝ) * (1 - δ)) ^ 2 - t ^ 2 ≠ 0 := by
      have : 0 < ((m : ℝ) * (1 - δ)) ^ 2 - t ^ 2 := by nlinarith
      exact this.ne'
    have : (1 - δ) ^ 2 - (t / m) ^ 2 ≠ 0 := by rw [← hA, ← hy]; exact hAy.ne'
    field_simp
    ring
  have hT := tT_anti (J := (Fintype.card ι : ℝ)) (r := r) hc0 hd.le hxd hδ.le (by positivity) hr₀
    (by rw [hr, hA, hy]; exact hr₀t)
  have hP : 2 * c / (π * m ^ 2) * (tT c m d δ r (Fintype.card ι) / (c * r ^ 2))
      ≤ 2 / π * tT c m d δ r₀ (Fintype.card ι) / (m * (1 - δ) - t) ^ 2 := by
    have e : (m : ℝ) * (1 - δ) - t = m * r := by rw [hr, hA, hy]; field_simp
    rw [e]
    have : 2 * c / (π * m ^ 2) * (tT c m d δ r (Fintype.card ι) / (c * r ^ 2))
        = 2 / π * tT c m d δ r (Fintype.card ι) / (m * r) ^ 2 := by field_simp
    rw [this]
    gcongr
  calc 2 * c / (π * m ^ 2) * (∑ i, (a i : ℂ) * smp (Cvs.L2a.CutKernelSimplified.muSi c y m) c (χ i) (g i) m).re ^ 2
      ≤ 2 * c / (π * m ^ 2) * ((bandMain c y m (Ymax m) + c * (2 * (181 / 462) / π * δ * n₀ ^ 2))
          * (∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + tT c m d δ r (Fintype.card ι) / (c * r ^ 2) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) :=
        mul_le_mul_of_nonneg_left h hk
    _ = (2 * c / (π * m ^ 2) * bandMain c y m (Ymax m) + 2 * c / (π * m ^ 2) * (c * (2 * (181 / 462) / π * δ * n₀ ^ 2)))
          * (∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + 2 * c / (π * m ^ 2) * (tT c m d δ r (Fintype.card ι) / (c * r ^ 2))
          * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by ring
    _ ≤ _ := by
        rw [hmain, hcoll]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hP hQ)

/-- **The far corner at one `t`**: for `t > b′ = m(Y(m) + δ)` and `0 < r₀ ≤ t/m − Y(m) − δ`,
`𝔅_m^si(t)² ≤ (π⁻²(f_m − cos(2ct)g_m) + (4κ_S/π²)δt²/(t² − b′²)²)·W_m + (2/π)T(r₀)/(t − b′)²·∫₁^∞Φ²`. -/
theorem bSi_sq_le_far (a : ι → ℝ) {M m : ℕ} {d δ t r₀ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hm : 2 ≤ m) (hmM : m ≤ M)
    (hd : 0 < d) (hxd : 1 < (m : ℝ) - d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (htb : m * (Ymax m + δ) < t)
    (hr₀ : 0 < r₀) (hr₀t : r₀ ≤ t / m - Ymax m - δ) :
    bSi c χ g a m t ^ 2
      ≤ ((π ^ 2)⁻¹ * (Cvs.L2a.CornerSuprema.fm m t - Real.cos (2 * c * t) * gT m t)
          + 4 * (181 / 462) / π ^ 2 * δ * t ^ 2 / (t ^ 2 - (m * (Ymax m + δ)) ^ 2) ^ 2)
          * (∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + 2 / π * tT c m d δ r₀ (Fintype.card ι) / (t - m * (Ymax m + δ)) ^ 2
          * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hMr : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hY1 := one_le_Ymax (by linarith : (1 : ℝ) < m)
  obtain ⟨B, hB⟩ : ∃ B, B = Ymax m + δ := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; linarith
  obtain ⟨y, hy⟩ : ∃ y, y = t / m := ⟨_, rfl⟩
  have hyB : B < y := by rw [hy, hB, lt_div_iff₀ hm0]; linarith
  have hy0 : 0 < y := by linarith
  obtain ⟨r, hr⟩ : ∃ r, r = y - B := ⟨_, rfl⟩
  have hr0 : 0 < r := by linarith
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = 1 / c * (y / (y ^ 2 - B ^ 2)) := ⟨_, rfl⟩
  have hyB2 : 0 < y ^ 2 - B ^ 2 := by nlinarith
  have hn0 : ∀ v ∈ bandRg δ (Ymax m), ‖siPole c y m v‖ ≤ n₀ := fun v hv => by
    refine (norm_siPole_le hc0 y m v).trans ?_
    have := inv_add_inv_far hB0.le hyB (by have := hv.2; rw [hB]; linarith : |v| ≤ B)
    rw [hn₀]
    calc 1 / (2 * c) * (1 / |y + v| + 1 / |y - v|) ≤ 1 / (2 * c) * (2 * y / (y ^ 2 - B ^ 2)) := by gcongr
      _ = _ := by ring
  have hn0r : n₀ ≤ 1 / (c * r) := by
    have h1 : 0 < y - B := by linarith
    have h2 : 0 < y + B := by linarith
    rw [hn₀, hr, show y ^ 2 - B ^ 2 = (y - B) * (y + B) by ring, one_div_mul_eq_div, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos h1 hc0) hB0]
  have h := corner_local (X := M) (x₀ := m) (y := y) (d := d) (δ := δ) (r := r) a hg hg₁ hg₂c hang hc hχ0 hχc hχi
    (by linarith) hM ⟨by linarith, hMr⟩ hd hxd hδ hδ1 hr0 hy0 (dist_far (by rw [hr, hB]; linarith))
    hn0 hn0r
  have hQ : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have hk : 0 ≤ 2 * c / (π * m ^ 2) := by positivity
  rw [bSi_sq c hc0.le, ← hy]
  have hbm : Cvs.L2a.CornerSuprema.bm m = m * Ymax m := by
    unfold Cvs.L2a.CornerSuprema.bm Ymax; ring
  have hmain : 2 * c / (π * m ^ 2) * bandMain c y m (Ymax m)
      = (π ^ 2)⁻¹ * (Cvs.L2a.CornerSuprema.fm m t - Real.cos (2 * c * t) * gT m t) :=
    hy ▸ mainB_eq hc0 (by linarith) (by nlinarith) (by nlinarith) (by rw [hbm]; nlinarith)
  have hcoll : 2 * c / (π * m ^ 2) * (c * (2 * (181 / 462) / π * δ * n₀ ^ 2))
      = 4 * (181 / 462) / π ^ 2 * δ * t ^ 2 / (t ^ 2 - (m * (Ymax m + δ)) ^ 2) ^ 2 := by
    rw [hn₀, ← hB]
    have e : t = m * y := by rw [hy]; field_simp
    rw [e]
    have : ((m : ℝ) * y) ^ 2 - (m * B) ^ 2 ≠ 0 := by
      have : 0 < ((m : ℝ) * y) ^ 2 - (m * B) ^ 2 := by
        rw [show ((m : ℝ) * y) ^ 2 - (m * B) ^ 2 = m ^ 2 * (y ^ 2 - B ^ 2) by ring]; positivity
      exact this.ne'
    field_simp
    ring
  have hT := tT_anti (J := (Fintype.card ι : ℝ)) (r := r) hc0 hd.le hxd hδ.le (by positivity) hr₀
    (by rw [hr, hB, hy]; linarith)
  have hP : 2 * c / (π * m ^ 2) * (tT c m d δ r (Fintype.card ι) / (c * r ^ 2))
      ≤ 2 / π * tT c m d δ r₀ (Fintype.card ι) / (t - m * (Ymax m + δ)) ^ 2 := by
    have e : t - (m : ℝ) * (Ymax m + δ) = m * r := by rw [hr, hB, hy]; field_simp
    rw [e]
    have : 2 * c / (π * m ^ 2) * (tT c m d δ r (Fintype.card ι) / (c * r ^ 2))
        = 2 / π * tT c m d δ r (Fintype.card ι) / (m * r) ^ 2 := by field_simp
    rw [this]
    gcongr
  calc 2 * c / (π * m ^ 2) * (∑ i, (a i : ℂ) * smp (Cvs.L2a.CutKernelSimplified.muSi c y m) c (χ i) (g i) m).re ^ 2
      ≤ 2 * c / (π * m ^ 2) * ((bandMain c y m (Ymax m) + c * (2 * (181 / 462) / π * δ * n₀ ^ 2))
          * (∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + tT c m d δ r (Fintype.card ι) / (c * r ^ 2) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) :=
        mul_le_mul_of_nonneg_left h hk
    _ = (2 * c / (π * m ^ 2) * bandMain c y m (Ymax m) + 2 * c / (π * m ^ 2) * (c * (2 * (181 / 462) / π * δ * n₀ ^ 2)))
          * (∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + 2 * c / (π * m ^ 2) * (tT c m d δ r (Fintype.card ι) / (c * r ^ 2))
          * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by ring
    _ ≤ _ := by
        rw [hmain, hcoll]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hP hQ)

end tform

/-! ### The count envelope on a symmetrised multiplier -/

section envelope

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

theorem smp_sub (μ ν : ℝ → ℂ) (c χ : ℝ) (g : ℝ → ℝ) (x₀ : ℝ) :
    smp (fun ξ => μ ξ - ν ξ) c χ g x₀ = smp μ c χ g x₀ - smp ν c χ g x₀ := by
  unfold smp; ring

theorem norm_smp_le {μ : ℝ → ℂ} {c χ x : ℝ} {g : ℝ → ℝ} (hx : 1 < x) (hc : 0 < c) (hχc : χ < c ^ 2) :
    ‖smp μ c χ g x‖ ≤ (‖μ (kP c χ x)‖ + ‖μ (-kP c χ x)‖) * (Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c χ g x / 2) := by
  have h := Cvs.L2a.CutKernelSimplified.norm_smp_sub_le (μ := μ) (ν := fun _ => 0) (g := g) hx hc hχc
  have e : smp (fun _ => (0 : ℂ)) c χ g x = 0 := by unfold smp; simp
  simpa [e] using h

/-- `Re Σaᵢ Sᵢ[μ] = Σaᵢ Sᵢ[μ_s]`. -/
theorem re_sum_smp (a : ι → ℝ) (μ : ℝ → ℂ) (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (x₀ : ℝ) :
    (((∑ i, (a i : ℂ) * smp μ c (χ i) (g i) x₀).re : ℝ) : ℂ)
      = ∑ i, (a i : ℂ) * smp (Cvs.L2a.QIdentityCutPoint.muSym μ) c (χ i) (g i) x₀ := by
  rw [Complex.re_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_ofReal_mul, Complex.ofReal_mul, Cvs.L2a.QIdentityCutPoint.re_smp]

/-- `Σaᵢ²∫₁^X ψᵢ² ≤ ∫₁^∞Φ²` on injective spectra. -/
theorem span_le_full (a : ι → ℝ) {X : ℝ} (hX : 1 ≤ X)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχi : Function.Injective χ) :
    ∑ i, a i ^ 2 * (∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hψ2 : ∀ i, IntegrableOn (fun x => psi c (g i) x ^ 2) (Ioi 1) := fun i =>
    (memLp_two_iff_integrable_sq ((Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i)
      (hang i)).2.2.1.aestronglyMeasurable)).mp (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i)
      (hang i) hc)
  rw [Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc hχi]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [intervalIntegral.integral_of_le hX]
  exact setIntegral_mono_set (hψ2 i) (ae_of_all _ fun x => sq_nonneg _)
    (ae_of_all _ fun x hx => show 1 < x from hx.1)

/-- **The count envelope on a real part (T0)**: if `‖μ_s‖ ≤ B` on `[c, cY(x₀)]` then
`|Re Σaᵢ Sᵢ[μ](x₀)| ≤ B√(6J/(x₀² − 1))·√(∫₁^∞Φ²)`. -/
theorem t0_re (a : ι → ℝ) {X x₀ B : ℝ} {μ : ℝ → ℂ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hX : 2 ≤ X) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hx₀ : x₀ ∈ Icc (6 / 5 : ℝ) X)
    (hb : ∀ ξ ∈ Icc c (c * Ymax x₀), ‖Cvs.L2a.QIdentityCutPoint.muSym μ ξ‖ ≤ B) :
    |(∑ i, (a i : ℂ) * smp μ c (χ i) (g i) x₀).re|
      ≤ B * √(6 * (Fintype.card ι : ℝ) / (x₀ ^ 2 - 1)) * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hx1 : 1 < x₀ := by linarith [hx₀.1]
  have hY := one_le_Ymax hx1
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb c ⟨le_rfl, by nlinarith⟩)
  have hXs : ∀ i, ‖smp (Cvs.L2a.QIdentityCutPoint.muSym μ) c (χ i) (g i) x₀‖
      ≤ B * Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c (χ i) (g i) x₀ := fun i => by
    have hk := Cvs.Upstream.ExpDifferenceBound.kP_mem_Icc hx1 hc0 (hχ0 i) (hχc i)
    have h1 := hb _ hk
    have h2 : ‖Cvs.L2a.QIdentityCutPoint.muSym μ (-kP c (χ i) x₀)‖ ≤ B := by
      rw [muSym_neg, RCLike.norm_conj]; exact h1
    refine (norm_smp_le hx1 hc0 (hχc i)).trans ?_
    have : 0 ≤ Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c (χ i) (g i) x₀ := Real.sqrt_nonneg _
    nlinarith
  have hmass := Cvs.L2a.BandTransferKernelForm.norm_sum_le_mass a _ _ _ hM hXs
  rw [Cvs.L2a.BandTransferKernelForm.massSum_const_mul] at hmass
  have hcount := Cvs.Prolate.Envelope.RungCountEnvelope.count_envelope hg hg₁ hg₂c hang hc hχ0 hχc hX hM hx₀
  have ea : |(∑ i, (a i : ℂ) * smp μ c (χ i) (g i) x₀).re|
      = ‖(((∑ i, (a i : ℂ) * smp μ c (χ i) (g i) x₀).re : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [ea, re_sum_smp]
  refine hmass.trans ?_
  have hP := span_le_full a (X := X) (by linarith) hg hg₁ hg₂c hang hc0 hχi
  rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]
  calc √(∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) * (B * √(Cvs.L2a.SpanPoleMellinFromRungs.massSum
        (fun i => Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c (χ i) (g i) x₀) fun i => ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2))
      ≤ √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) * (B * √(6 * (Fintype.card ι : ℝ) / (x₀ ^ 2 - 1))) := by
        gcongr
    _ = _ := by ring

/-! ### Lemma K on the symmetrised kernels -/

theorem norm_muSi {c y x η : ℝ} (hc : 0 < c) :
    ‖Cvs.L2a.CutKernelSimplified.muSi c y x (c * η)‖ = 1 / (c * |y + η|) := by
  unfold Cvs.L2a.CutKernelSimplified.muSi
  rw [norm_div, norm_mul, norm_neg, Complex.norm_I, (continuous_eF c y).2, Complex.norm_real,
    Real.norm_eq_abs, ← mul_add, abs_mul, abs_of_pos hc, one_mul]

theorem muSym_muSi (c y x v : ℝ) :
    Cvs.L2a.QIdentityCutPoint.muSym (Cvs.L2a.CutKernelSimplified.muSi c y x) (c * v) = siPole c y x v := by
  unfold siPole Cvs.L2a.QIdentityCutPoint.muSym
  beta_reduce
  rw [mul_neg]

/-- `1/|y + v| + 1/|y − v| ≤ 2√(y² + v²)/|y² − v²|`. -/
theorem inv_add_inv_le_sqrt {y v : ℝ} (hp : y + v ≠ 0) (hq : y - v ≠ 0) :
    1 / |y + v| + 1 / |y - v| ≤ 2 * √(y ^ 2 + v ^ 2) / |y ^ 2 - v ^ 2| := by
  have h1 : 0 < |y + v| := abs_pos.2 hp
  have h2 : 0 < |y - v| := abs_pos.2 hq
  have e : |y ^ 2 - v ^ 2| = |y + v| * |y - v| := by rw [← abs_mul]; ring_nf
  rw [e, div_add_div _ _ h1.ne' h2.ne', div_le_div_iff_of_pos_right (by positivity)]
  have hs : (|y - v| + |y + v|) ^ 2 ≤ (2 * √(y ^ 2 + v ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (|y - v| - |y + v|), sq_abs (y - v), sq_abs (y + v)]
  have := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hs
  linarith

/-- The simplified kernel under the envelope: `‖(μ_si)_s(cv)‖ ≤ (1/c)√(y² + v²)/|y² − v²|`. -/
theorem norm_muSym_muSi_le {c y x v : ℝ} (hc : 0 < c) (hp : y + v ≠ 0) (hq : y - v ≠ 0) :
    ‖Cvs.L2a.QIdentityCutPoint.muSym (Cvs.L2a.CutKernelSimplified.muSi c y x) (c * v)‖
      ≤ 1 / c * (√(y ^ 2 + v ^ 2) / |y ^ 2 - v ^ 2|) := by
  rw [muSym_muSi]
  refine (norm_siPole_le hc y x v).trans ?_
  have := inv_add_inv_le_sqrt hp hq
  calc 1 / (2 * c) * (1 / |y + v| + 1 / |y - v|) ≤ 1 / (2 * c) * (2 * √(y ^ 2 + v ^ 2) / |y ^ 2 - v ^ 2|) := by
        gcongr
    _ = _ := by ring

/-- **Lemma K, relative, symmetrised**: with `K ≥ K_cmp` at `±v`,
`‖(μ − μ_si)_s(cv)‖ ≤ (K/c)(1/c)√(y² + v²)/|y² − v²|`. -/
theorem norm_muSym_co_le {c y x v K : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : 0 < y) (hp : y + v ≠ 0) (hq : y - v ≠ 0)
    (hK1 : Cvs.L2a.CutKernelSimplified.kCmp c x y v ≤ K) (hK2 : Cvs.L2a.CutKernelSimplified.kCmp c x y (-v) ≤ K) :
    ‖Cvs.L2a.QIdentityCutPoint.muSym (fun ξ => Cvs.L2a.QIdentityCutPoint.muCut c y x ξ - Cvs.L2a.CutKernelSimplified.muSi c y x ξ)
        (c * v)‖ ≤ K / c * (1 / c * (√(y ^ 2 + v ^ 2) / |y ^ 2 - v ^ 2|)) := by
  have hD : y ^ 2 ≠ v ^ 2 := fun h => by
    have : (y + v) * (y - v) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 this with h1 | h1
    exacts [hp h1, hq h1]
  have hD' : y ^ 2 ≠ (-v) ^ 2 := by rwa [neg_sq]
  have h1 := Cvs.L2a.CutKernelSimplified.mul_norm_muCut_sub_muSi_le hc hx hy hp hD
  have h2 := Cvs.L2a.CutKernelSimplified.mul_norm_muCut_sub_muSi_le (η := -v) hc hx hy (by rwa [← sub_eq_add_neg]) hD'
  rw [norm_muSi hc] at h1 h2
  rw [← sub_eq_add_neg] at h2
  have hK : 0 ≤ K := (by unfold Cvs.L2a.CutKernelSimplified.kCmp; have := (pP_pos hx).le; positivity : (0 : ℝ) ≤ _).trans hK1
  have hp' : 0 < |y + v| := abs_pos.2 hp
  have hq' : 0 < |y - v| := abs_pos.2 hq
  have e1 : ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * v) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * v)‖
      ≤ K / c * (1 / (c * |y + v|)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm]
    exact h1.trans (mul_le_mul_of_nonneg_right hK1 (by positivity))
  have e2 : ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * -v) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * -v)‖
      ≤ K / c * (1 / (c * |y - v|)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm]
    exact h2.trans (mul_le_mul_of_nonneg_right hK2 (by positivity))
  unfold Cvs.L2a.QIdentityCutPoint.muSym
  rw [norm_div, Complex.norm_two, ← mul_neg]
  have := inv_add_inv_le_sqrt hp hq
  calc ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * v) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * v)
        + conj (Cvs.L2a.QIdentityCutPoint.muCut c y x (c * -v) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * -v))‖ / 2
      ≤ (K / c * (1 / (c * |y + v|)) + K / c * (1 / (c * |y - v|))) / 2 := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [RCLike.norm_conj]
        exact add_le_add e1 e2
    _ = K / c * (1 / c * ((1 / |y + v| + 1 / |y - v|) / 2)) := by field_simp
    _ ≤ K / c * (1 / c * ((2 * √(y ^ 2 + v ^ 2) / |y ^ 2 - v ^ 2|) / 2)) := by gcongr
    _ = _ := by ring

theorem muSym_add (μ ν : ℝ → ℂ) (ξ : ℝ) :
    Cvs.L2a.QIdentityCutPoint.muSym (fun ξ => μ ξ + ν ξ) ξ
      = Cvs.L2a.QIdentityCutPoint.muSym μ ξ + Cvs.L2a.QIdentityCutPoint.muSym ν ξ := by
  unfold Cvs.L2a.QIdentityCutPoint.muSym; rw [map_add]; ring

/-- **The exact kernel under the envelope**: `‖μ_s(cv)‖ ≤ (1 + K/c)(1/c)√(y² + v²)/|y² − v²|`. -/
theorem norm_muSym_muCut_le {c y x v K : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : 0 < y) (hp : y + v ≠ 0)
    (hq : y - v ≠ 0) (hK1 : Cvs.L2a.CutKernelSimplified.kCmp c x y v ≤ K)
    (hK2 : Cvs.L2a.CutKernelSimplified.kCmp c x y (-v) ≤ K) :
    ‖Cvs.L2a.QIdentityCutPoint.muSym (Cvs.L2a.QIdentityCutPoint.muCut c y x) (c * v)‖
      ≤ (1 + K / c) * (1 / c * (√(y ^ 2 + v ^ 2) / |y ^ 2 - v ^ 2|)) := by
  have e : Cvs.L2a.QIdentityCutPoint.muCut c y x = fun ξ => Cvs.L2a.CutKernelSimplified.muSi c y x ξ
      + (Cvs.L2a.QIdentityCutPoint.muCut c y x ξ - Cvs.L2a.CutKernelSimplified.muSi c y x ξ) := funext fun ξ => by ring
  rw [e, muSym_add]
  refine (norm_add_le _ _).trans ?_
  have := norm_muSym_muSi_le (x := x) hc hp hq
  have := norm_muSym_co_le hc hx hy hp hq hK1 hK2
  linarith

/-- **Lemma K (ii)**: for `0 < y < 1 ≤ |η|`, `‖(μ − μ_si)(cη)‖ ≤ 1/(c|y + η|) + 1/(cy)`. -/
theorem mu_co_abs_le {c y x η : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : 0 < y) (hy1 : y < 1) (hη : 1 ≤ |η|) :
    ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * η) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * η)‖
      ≤ 1 / (c * |y + η|) + 1 / (c * y) := by
  have hx0 : 0 < x := by linarith
  have hp : 0 < pP x := pP_pos hx
  have hyη : y + η ≠ 0 := fun h => by
    have : |η| = y := by rw [show η = -y by linarith, abs_neg, abs_of_pos hy]
    linarith
  have hs : c * y + c * η ≠ 0 := by rw [← mul_add]; exact mul_ne_zero hc.ne' hyη
  set Q := Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η) with hQd
  have hQim : 2 * c * x * y ≤ ‖Q‖ := Cvs.L2a.QIdentityCutPoint.le_norm_qQk_im hc.le hx0.le hy.le
  have hQ0 : 0 < ‖Q‖ := lt_of_lt_of_le (by positivity) hQim
  have hη2 : 1 ≤ η ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg η]
  have hQsq : ‖Q‖ ^ 2 = (pP x * (c ^ 2 * y ^ 2 - (c * η) ^ 2)) ^ 2 + (2 * c * x * y) ^ 2 := by
    rw [hQd, Cvs.L2a.QIdentityCutPoint.qQk, Complex.sq_norm, sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg,
      Complex.normSq_add_mul_I]
    ring
  have hQam : 4 * pP x * c ^ 3 * x * y * (η ^ 2 - y ^ 2) ≤ ‖Q‖ ^ 2 := by
    rw [hQsq]
    have e : pP x * (c ^ 2 * y ^ 2 - (c * η) ^ 2) = -(pP x * c ^ 2 * (η ^ 2 - y ^ 2)) := by ring
    rw [e]
    nlinarith [sq_nonneg (pP x * c ^ 2 * (η ^ 2 - y ^ 2) - 2 * c * x * y)]
  have hQ1 := Cvs.L2a.QIdentityIterated.norm_qQ₁_le_abs (c := c) (y := y) (x := x) hx0.le hy.le hc.le
  have hy2 : |y ^ 2 - 1| = 1 - y ^ 2 := by rw [abs_of_neg (by nlinarith)]; ring
  rw [hy2] at hQ1
  rw [Cvs.L2a.CutKernelSimplified.muCut_eq_muSi_add hc hx0 hy hs, add_sub_cancel_left, norm_mul, (continuous_eF c y).2,
    one_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * c * x * y), ← mul_add, abs_mul, abs_of_pos hc, ← hQd]
    have hb : 0 < c * |y + η| := mul_pos hc (abs_pos.2 hyη)
    rw [div_le_div_iff₀ (by positivity) hb]
    nlinarith [mul_le_mul_of_nonneg_right hQim hb.le]
  · rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, ← hQd]
    have hη0 : 0 < η ^ 2 - y ^ 2 := by nlinarith
    have hA : pP x * (2 * c ^ 2 * x * (1 - y ^ 2)) / ‖Q‖ ^ 2 ≤ 1 / (2 * c * y) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : pP x * (2 * c ^ 2 * x * (1 - y ^ 2)) * (2 * c * y) ≤ 4 * pP x * c ^ 3 * x * y * (η ^ 2 - y ^ 2) := by
        have : 1 - y ^ 2 ≤ η ^ 2 - y ^ 2 := by linarith
        have : 0 ≤ 4 * pP x * c ^ 3 * x * y := by positivity
        nlinarith
      linarith
    have hB : pP x * (2 * c * y) / ‖Q‖ ^ 2 ≤ 1 / (2 * c * y) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hq2 : (2 * c * x * y) ^ 2 ≤ ‖Q‖ ^ 2 := pow_le_pow_left₀ (by positivity) hQim 2
      have hpx : pP x ≤ x ^ 2 := by unfold pP; linarith
      have : pP x * (2 * c * y) * (2 * c * y) ≤ (2 * c * x * y) ^ 2 := by
        have : 0 ≤ (2 * c * y) * (2 * c * y) := by positivity
        nlinarith
      linarith
    calc pP x * ‖qQ₁ c y x‖ / ‖Q‖ ^ 2 ≤ pP x * (2 * c ^ 2 * x * (1 - y ^ 2) + 2 * c * y) / ‖Q‖ ^ 2 := by
          gcongr
      _ = pP x * (2 * c ^ 2 * x * (1 - y ^ 2)) / ‖Q‖ ^ 2 + pP x * (2 * c * y) / ‖Q‖ ^ 2 := by ring
      _ ≤ 1 / (2 * c * y) + 1 / (2 * c * y) := add_le_add hA hB
      _ = 1 / (c * y) := by field_simp; ring

/-- **The strip envelope**: for `0 < y < 1 ≤ v`, `‖μ_s(cv)‖ ≤ (1/c)(2/(1 − y²) + 1/y)`. -/
theorem norm_muSym_muCut_strip {c y x v : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : 0 < y) (hy1 : y < 1) (hv : 1 ≤ v) :
    ‖Cvs.L2a.QIdentityCutPoint.muSym (Cvs.L2a.QIdentityCutPoint.muCut c y x) (c * v)‖
      ≤ 1 / c * (2 / (1 - y ^ 2) + 1 / y) := by
  have hv1 : 1 ≤ |v| := by rw [abs_of_pos (by linarith)]; exact hv
  have hv2 : 1 ≤ |-v| := by rwa [abs_neg]
  have hp : 0 < |y + v| := abs_pos.2 (by linarith)
  have hq : 0 < |y - v| := abs_pos.2 (by linarith)
  have k : ∀ η, 1 ≤ |η| → ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * η)‖ ≤ 2 / (c * |y + η|) + 1 / (c * y) := by
    intro η hη
    have h1 := mu_co_abs_le (x := x) hc hx hy hy1 hη
    have h2 : ‖Cvs.L2a.CutKernelSimplified.muSi c y x (c * η)‖ = 1 / (c * |y + η|) := norm_muSi hc
    calc ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * η)‖
        ≤ ‖Cvs.L2a.CutKernelSimplified.muSi c y x (c * η)‖
          + ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * η) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * η)‖ := by
          have := norm_add_le (Cvs.L2a.CutKernelSimplified.muSi c y x (c * η))
            (Cvs.L2a.QIdentityCutPoint.muCut c y x (c * η) - Cvs.L2a.CutKernelSimplified.muSi c y x (c * η))
          rwa [add_sub_cancel] at this
      _ ≤ _ := by rw [h2]; linarith [show 2 / (c * |y + η|) = 1 / (c * |y + η|) + 1 / (c * |y + η|) by ring]
  have kv := k v hv1
  have kv' := k (-v) hv2
  rw [← sub_eq_add_neg] at kv'
  have hn := inv_add_inv_near (A := 1) hy.le hy1 hv1
  unfold Cvs.L2a.QIdentityCutPoint.muSym
  rw [norm_div, Complex.norm_two, ← mul_neg]
  calc ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * v) + conj (Cvs.L2a.QIdentityCutPoint.muCut c y x (c * -v))‖ / 2
      ≤ (2 / (c * |y + v|) + 1 / (c * y) + (2 / (c * |y - v|) + 1 / (c * y))) / 2 := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [RCLike.norm_conj]
        exact add_le_add kv kv'
    _ = 1 / c * ((1 / |y + v| + 1 / |y - v|) + 1 / y) := by field_simp; ring
    _ ≤ 1 / c * (2 * 1 / (1 ^ 2 - y ^ 2) + 1 / y) := by gcongr
    _ = _ := by ring

/-- The envelope from inside: `√(y² + v²)/|y² − v²| ≤ √(y² + 1)/(1 − y²)` for `0 ≤ y < 1 ≤ v`. -/
theorem env_near {y v : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) (hv : 1 ≤ v) :
    √(y ^ 2 + v ^ 2) / |y ^ 2 - v ^ 2| ≤ √(y ^ 2 + 1) / (1 - y ^ 2) := by
  have h1 : 0 < 1 - y ^ 2 := by nlinarith
  have hD : 0 < v ^ 2 - y ^ 2 := by nlinarith
  rw [abs_sub_comm, abs_of_pos hD]
  rw [div_le_div_iff₀ hD h1]
  have hs : √(y ^ 2 + v ^ 2) * (1 - y ^ 2) ≤ √(y ^ 2 + 1) * (v ^ 2 - y ^ 2) := by
    rw [← Real.sqrt_sq h1.le, ← Real.sqrt_sq hD.le, ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have hV : 0 ≤ v ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg hV h1.le, mul_nonneg (mul_nonneg hV hV) (by positivity : (0 : ℝ) ≤ y ^ 2 + 1),
      mul_nonneg (mul_nonneg hV h1.le) (by positivity : (0 : ℝ) ≤ y ^ 2 + 1), sq_nonneg y]
  linarith

/-- The envelope from beyond: `√(y² + v²)/|y² − v²| ≤ √(y² + Y²)/(y² − Y²)` for `0 ≤ v ≤ Y < y`. -/
theorem env_far {y v Y : ℝ} (hv : 0 ≤ v) (hvY : v ≤ Y) (hYy : Y < y) :
    √(y ^ 2 + v ^ 2) / |y ^ 2 - v ^ 2| ≤ √(y ^ 2 + Y ^ 2) / (y ^ 2 - Y ^ 2) := by
  have hv2 : v ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hv hvY 2
  have hD : 0 < y ^ 2 - Y ^ 2 := by nlinarith
  rw [abs_of_pos (by linarith)]
  exact div_le_div₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith)) hD (by linarith)

end envelope

/-! ### The count envelope in `t`: tail, correction and strip -/

section t0

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

/-- The correction `𝔅_m^co = 𝔅_m − 𝔅_m^si`. -/
def bCo (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  Cvs.L2a.CutKernels.frakB c χ g a m t - bSi c χ g a m t

theorem bCo_eq (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (m : ℕ) (t : ℝ) :
    bCo c χ g a m t = -(√(2 * c / π) / m) * (∑ i, (a i : ℂ) * smp (fun ξ =>
      Cvs.L2a.QIdentityCutPoint.muCut c (t / m) m ξ - Cvs.L2a.CutKernelSimplified.muSi c (t / m) m ξ) c (χ i) (g i) m).re := by
  unfold bCo bSi Cvs.L2a.CutKernels.frakB Cvs.L2a.CutKernels.cutSample
  simp only [smp_sub, mul_sub, Finset.sum_sub_distrib, Complex.sub_re]

/-- `κ_ι = 12J/(πc)`. -/
def kapI (c J : ℝ) : ℝ := 12 * J / (π * c)

/-- **The count envelope at a cut (T0) on the exact and the correction kernels**: if `kCmp ≤ K` on the band
and `√(y² + v²)/|y² − v²| ≤ S` on `[1, Y(m)]`, then `𝔅_m(t)² ≤ (1 + K/c)²κ_ι S²/(m²(m² − 1))·∫₁^∞Φ²` and
`𝔅_m^co(t)² ≤ (K/c)²κ_ι S²/(m²(m² − 1))·∫₁^∞Φ²`, `y = t/m`. -/
theorem t0_frakB (a : ι → ℝ) {M m : ℕ} {t K S : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hm : 2 ≤ m) (hmM : m ≤ M) (ht : 0 < t)
    (hoff : ∀ v ∈ Icc 1 (Ymax m), t / m ≠ v)
    (hK : ∀ η, 1 ≤ |η| → |η| ≤ Ymax m → Cvs.L2a.CutKernelSimplified.kCmp c m (t / m) η ≤ K)
    (hS : ∀ v ∈ Icc 1 (Ymax m), √((t / m) ^ 2 + v ^ 2) / |(t / m) ^ 2 - v ^ 2| ≤ S) :
    Cvs.L2a.CutKernels.frakB c χ g a m t ^ 2
        ≤ (1 + K / c) ^ 2 * kapI c (Fintype.card ι) * S ^ 2 / (m ^ 2 * (m ^ 2 - 1))
          * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2
      ∧ bCo c χ g a m t ^ 2
        ≤ (K / c) ^ 2 * kapI c (Fintype.card ι) * S ^ 2 / (m ^ 2 * (m ^ 2 - 1))
          * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hMr : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hy : 0 < t / m := by positivity
  have hx₀ : (m : ℝ) ∈ Icc (6 / 5 : ℝ) M := ⟨by linarith, hMr⟩
  have hY1 := one_le_Ymax (by linarith : (1 : ℝ) < m)
  have hpq : ∀ v ∈ Icc 1 (Ymax m), t / m + v ≠ 0 ∧ t / m - v ≠ 0 := fun v hv =>
    ⟨by linarith [hv.1], sub_ne_zero.2 (hoff v hv)⟩
  have hKv : ∀ v ∈ Icc 1 (Ymax m), Cvs.L2a.CutKernelSimplified.kCmp c m (t / m) v ≤ K ∧
      Cvs.L2a.CutKernelSimplified.kCmp c m (t / m) (-v) ≤ K := fun v hv => by
    have h1 : |v| = v := abs_of_nonneg (by linarith [hv.1])
    exact ⟨hK v (by rw [h1]; exact hv.1) (by rw [h1]; exact hv.2),
      hK (-v) (by rw [abs_neg, h1]; exact hv.1) (by rw [abs_neg, h1]; exact hv.2)⟩
  have hv_of : ∀ ξ ∈ Icc c (c * Ymax m), ξ / c ∈ Icc 1 (Ymax m) ∧ ξ = c * (ξ / c) := fun ξ hξ =>
    ⟨⟨by rw [le_div_iff₀ hc0]; linarith [hξ.1], by rw [div_le_iff₀ hc0]; linarith [hξ.2]⟩,
      by field_simp⟩
  have hS0 : 0 ≤ S := (div_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)).trans (hS 1 ⟨le_rfl, hY1⟩)
  have hK0 : 0 ≤ K := by
    refine le_trans ?_ (hKv 1 ⟨le_rfl, hY1⟩).1
    unfold Cvs.L2a.CutKernelSimplified.kCmp
    have := pP_pos (ξ := (m : ℝ)) (by linarith)
    positivity
  have hQ : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have hfin : ∀ (B R : ℝ), 0 ≤ B → |R| ≤ B * √(6 * (Fintype.card ι : ℝ) / ((m : ℝ) ^ 2 - 1))
      * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) →
      (-(√(2 * c / π) / m) * R) ^ 2 ≤ 2 * c / (π * m ^ 2) * B ^ 2 * (6 * (Fintype.card ι : ℝ) / ((m : ℝ) ^ 2 - 1))
        * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
    intro B R hB hR
    have hG : 0 ≤ 6 * (Fintype.card ι : ℝ) / ((m : ℝ) ^ 2 - 1) := by
      have : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
      positivity
    have h2 := pow_le_pow_left₀ (abs_nonneg R) hR 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hG, Real.sq_sqrt hQ, sq_abs] at h2
    rw [mul_pow, neg_sq, div_pow, Real.sq_sqrt (by positivity)]
    have : 2 * c / π / (m : ℝ) ^ 2 = 2 * c / (π * m ^ 2) := by ring
    rw [this]
    have hk : 0 ≤ 2 * c / (π * (m : ℝ) ^ 2) := by positivity
    calc 2 * c / (π * (m : ℝ) ^ 2) * R ^ 2
        ≤ 2 * c / (π * m ^ 2) * (B ^ 2 * (6 * (Fintype.card ι : ℝ) / ((m : ℝ) ^ 2 - 1))
          * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := mul_le_mul_of_nonneg_left h2 hk
      _ = _ := by ring
  have hconv : ∀ (L : ℝ), 2 * c / (π * m ^ 2) * (L * (1 / c * S)) ^ 2 * (6 * (Fintype.card ι : ℝ) / ((m : ℝ) ^ 2 - 1))
      = L ^ 2 * kapI c (Fintype.card ι) * S ^ 2 / (m ^ 2 * (m ^ 2 - 1)) := by
    intro L
    have hm1 : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
    unfold kapI
    field_simp
    ring
  constructor
  · have h := t0_re a (X := M) (B := (1 + K / c) * (1 / c * S)) (μ := Cvs.L2a.QIdentityCutPoint.muCut c (t / m) m)
      hg hg₁ hg₂c hang hc hχ0 hχc hχi (by linarith) hM hx₀ fun ξ hξ => by
        obtain ⟨hv, e⟩ := hv_of ξ hξ
        rw [e]
        refine (norm_muSym_muCut_le hc0 (by linarith) hy (hpq _ hv).1 (hpq _ hv).2 (hKv _ hv).1
          (hKv _ hv).2).trans ?_
        gcongr
        exact hS _ hv
    have := hfin _ _ (by positivity) h
    unfold Cvs.L2a.CutKernels.frakB Cvs.L2a.CutKernels.cutSample
    rw [← hconv]
    exact this
  · have h := t0_re a (X := M) (B := K / c * (1 / c * S))
      (μ := fun ξ => Cvs.L2a.QIdentityCutPoint.muCut c (t / m) m ξ - Cvs.L2a.CutKernelSimplified.muSi c (t / m) m ξ)
      hg hg₁ hg₂c hang hc hχ0 hχc hχi (by linarith) hM hx₀ fun ξ hξ => by
        obtain ⟨hv, e⟩ := hv_of ξ hξ
        rw [e]
        refine (norm_muSym_co_le hc0 (by linarith) hy (hpq _ hv).1 (hpq _ hv).2 (hKv _ hv).1
          (hKv _ hv).2).trans ?_
        gcongr
        exact hS _ hv
    have := hfin _ _ (by positivity) h
    rw [bCo_eq, ← hconv]
    exact this

/-- **The strip envelope at `m = 2`**: for `0 < t < 2`, `𝔅₂(t)² ≤ (J/(πc))(8/(4 − t²) + 2/t)²·∫₁^∞Φ²`. -/
theorem t0_strip (a : ι → ℝ) {M : ℕ} {t : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hM2 : 2 ≤ M) (ht : 0 < t) (ht2 : t < 2) :
    Cvs.L2a.CutKernels.frakB c χ g a 2 t ^ 2
      ≤ Fintype.card ι / (π * c) * (8 / (4 - t ^ 2) + 2 / t) ^ 2 * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hy : 0 < t / 2 := by positivity
  have hy1 : t / 2 < 1 := by linarith
  have hQ : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have h := t0_re a (X := M) (x₀ := 2) (B := 1 / c * (2 / (1 - (t / 2) ^ 2) + 1 / (t / 2)))
    (μ := Cvs.L2a.QIdentityCutPoint.muCut c (t / 2) 2) hg hg₁ hg₂c hang hc hχ0 hχc hχi hMr hM
    ⟨by norm_num, hMr⟩ fun ξ hξ => by
      have e : ξ = c * (ξ / c) := by field_simp
      rw [e]
      exact norm_muSym_muCut_strip hc0 (by norm_num) hy hy1 (by rw [le_div_iff₀ hc0]; linarith [hξ.1])
  have hB : 0 ≤ 1 / c * (2 / (1 - (t / 2) ^ 2) + 1 / (t / 2)) := by
    have : 0 < 1 - (t / 2) ^ 2 := by nlinarith
    positivity
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hQ, sq_abs] at h2
  unfold Cvs.L2a.CutKernels.frakB Cvs.L2a.CutKernels.cutSample
  rw [mul_pow, neg_sq, div_pow, Real.sq_sqrt (by positivity)]
  push_cast
  have e1 : 2 / (1 - (t / 2) ^ 2) + 1 / (t / 2) = 8 / (4 - t ^ 2) + 2 / t := by
    have : 4 - t ^ 2 ≠ 0 := by nlinarith
    rw [show 1 - (t / 2) ^ 2 = (4 - t ^ 2) / 4 by ring]
    field_simp; ring
  rw [e1] at h2
  calc 2 * c / π / 2 ^ 2 * (∑ i, (a i : ℂ) * smp (Cvs.L2a.QIdentityCutPoint.muCut c (t / 2) 2) c (χ i) (g i) 2).re ^ 2
      ≤ 2 * c / π / 2 ^ 2 * ((1 / c * (8 / (4 - t ^ 2) + 2 / t)) ^ 2 * (6 * (Fintype.card ι : ℝ) / (2 ^ 2 - 1))
          * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by gcongr
    _ = _ := by field_simp; ring

end t0

/-! ### The ramp is `C¹` -/

/-- **The ramp is differentiable everywhere**, with derivative `wF₁`. -/
theorem hasDerivAt_wF_all (x : ℝ) : HasDerivAt wF (wF₁ x) x := by
  set F : ℝ → ℝ := fun z => Real.sin (π * (z - 3 / 2)) ^ 2 with hFd
  have hF : ∀ y, HasDerivAt F (π * Real.sin (2 * π * (y - 3 / 2))) y := fun y => by
    have := (((hasDerivAt_id y).sub_const (3 / 2)).const_mul π).sin.pow 2
    refine this.congr_deriv ?_
    rw [show 2 * π * (y - 3 / 2) = 2 * (π * (y - 3 / 2)) by ring, Real.sin_two_mul]
    simp; ring
  have hcl : ∀ y ∈ Icc (3 / 2 : ℝ) 2, clampW y = y := fun y hy => by
    unfold clampW; rw [min_eq_left hy.2, max_eq_right hy.1]
  have hFeq : ∀ y ∈ Icc (3 / 2 : ℝ) 2, wF y = F y := fun y hy => by unfold wF; rw [hcl y hy]
  have h1eq : ∀ y ∈ Icc (3 / 2 : ℝ) 2, wF₁ y = π * Real.sin (2 * π * (y - 3 / 2)) := fun y hy => by
    unfold wF₁; rw [hcl y hy]
  rcases lt_trichotomy x (3 / 2) with h | h | h
  · have h0 : wF₁ x = 0 := by
      unfold wF₁ clampW; rw [max_eq_left (min_le_of_left_le h.le)]; simp
    rw [h0]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Iio_mem_nhds h) fun y hy => Cvs.L2a.FarFarBound.wF_eq_zero_of_le (le_of_lt hy))
  · subst h
    have h0 := wF_three_halves
    rw [h0.2]
    have hl : HasDerivWithinAt wF 0 (Iic (3 / 2)) (3 / 2) :=
      (hasDerivWithinAt_const (3 / 2 : ℝ) _ (0 : ℝ)).congr (fun y hy => Cvs.L2a.FarFarBound.wF_eq_zero_of_le hy) h0.1
    have hr : HasDerivWithinAt wF 0 (Ici (3 / 2)) (3 / 2) := by
      have := (hF (3 / 2)).hasDerivWithinAt (s := Ici (3 / 2))
      rw [show π * Real.sin (2 * π * ((3 / 2 : ℝ) - 3 / 2)) = 0 by simp] at this
      refine this.congr_of_eventuallyEq ?_ (hFeq _ ⟨le_rfl, by norm_num⟩)
      filter_upwards [inter_mem_nhdsWithin (Ici (3 / 2 : ℝ)) (Iio_mem_nhds (by norm_num : (3 / 2 : ℝ) < 2))]
        with y hy
      exact hFeq y ⟨hy.1, hy.2.le⟩
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rcases lt_trichotomy x 2 with h2 | h2 | h2
    · exact (hasDerivAt_wF h h2.ne).1
    · subst h2
      have h0 := wF_of_two_le (le_refl (2 : ℝ))
      rw [h0.2]
      have hr : HasDerivWithinAt wF 0 (Ici 2) 2 :=
        (hasDerivWithinAt_const (2 : ℝ) _ (1 : ℝ)).congr (fun y hy => (wF_of_two_le hy).1) h0.1
      have hl : HasDerivWithinAt wF 0 (Iic 2) 2 := by
        have := (hF 2).hasDerivWithinAt (s := Iic 2)
        rw [show π * Real.sin (2 * π * ((2 : ℝ) - 3 / 2)) = 0 by
          rw [show 2 * π * ((2 : ℝ) - 3 / 2) = π by ring, Real.sin_pi, mul_zero]] at this
        refine this.congr_of_eventuallyEq ?_ (hFeq _ ⟨by norm_num, le_rfl⟩)
        filter_upwards [inter_mem_nhdsWithin (Iic (2 : ℝ)) (Ioi_mem_nhds (by norm_num : (3 / 2 : ℝ) < 2))]
          with y hy
        exact hFeq y ⟨hy.2.le, hy.1⟩
      have := hl.union hr
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · exact (hasDerivAt_wF h h2.ne').1

theorem wF₁_nonneg (x : ℝ) : 0 ≤ wF₁ x := by
  unfold wF₁
  refine mul_nonneg pi_pos.le (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
  · unfold clampW
    have := le_max_left (3 / 2 : ℝ) (min x 2)
    nlinarith [pi_pos]
  · unfold clampW
    have : max (3 / 2 : ℝ) (min x 2) ≤ 2 := max_le (by norm_num) (min_le_right _ _)
    nlinarith [pi_pos]

/-! ### The oscillation: one integration by parts -/

/-- **Oscillation on the ramp**: for `G ≤ 0` with `G′ ≤ 0` on `[1, b]`,
`|∫₁^b (1 − wF)G cos(λt)| ≤ 2|G(b)|/|λ|`. -/
theorem osc_near {G G' : ℝ → ℝ} {b lam : ℝ} (hb1 : 1 ≤ b) (hlam : lam ≠ 0)
    (hG : ∀ t ∈ Icc 1 b, HasDerivAt G (G' t) t) (hG'c : ContinuousOn G' (Icc 1 b))
    (hG'0 : ∀ t ∈ Icc 1 b, G' t ≤ 0) (hG0 : ∀ t ∈ Icc 1 b, G t ≤ 0) :
    |∫ t in (1 : ℝ)..b, (1 - wF t) * G t * Real.cos (lam * t)| ≤ 2 * |G b| / |lam| := by
  have hu : uIcc (1 : ℝ) b = Icc 1 b := uIcc_of_le hb1
  have hw1 : wF 1 = 0 := Cvs.L2a.FarFarBound.wF_eq_zero_of_le (by norm_num)
  have hGc : ContinuousOn G (Icc 1 b) := fun t ht => (hG t ht).continuousAt.continuousWithinAt
  have hanti : AntitoneOn G (Icc 1 b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 1 b) hGc
      (fun t ht => (hG t (interior_subset ht)).hasDerivWithinAt) fun t ht => hG'0 t (interior_subset ht)
  have hf : ∀ t ∈ uIcc (1 : ℝ) b, HasDerivAt (fun t => (1 - wF t) * G t)
      (-wF₁ t * G t + (1 - wF t) * G' t) t := fun t ht => by
    rw [hu] at ht
    have := ((hasDerivAt_wF_all t).const_sub 1).mul (hG t ht)
    refine this.congr_deriv ?_; ring
  have hf'c : ContinuousOn (fun t => -wF₁ t * G t + (1 - wF t) * G' t) (Icc 1 b) :=
    ((continuous_wF.2.neg.continuousOn).mul hGc).add
      (((continuous_const.sub continuous_wF.1).continuousOn).mul hG'c)
  have h := Cvs.L2a.CutKernelSimplified.abs_integral_mul_cos_le hb1 hlam hf (by rw [hu] at *; exact hf'c.intervalIntegrable_of_Icc hb1)
  refine h.trans ?_
  rw [div_le_div_iff_of_pos_right (abs_pos.2 hlam)]
  have hGb : ∀ t ∈ Icc 1 b, |G t| ≤ -G b := fun t ht => by
    rw [abs_of_nonpos (hG0 t ht)]
    have := hanti ht ⟨hb1, le_rfl⟩ ht.2
    linarith
  have hb' : b ∈ Icc 1 b := ⟨hb1, le_rfl⟩
  have h1' : (1 : ℝ) ∈ Icc 1 b := ⟨le_rfl, hb1⟩
  have hwb : 0 ≤ 1 - wF b := by linarith [(Cvs.L2a.FarFarBound.wF_bounds b).2.1]
  have hint : ∫ t in (1 : ℝ)..b, |-wF₁ t * G t + (1 - wF t) * G' t|
      ≤ ∫ t in (1 : ℝ)..b, (wF₁ t * (-G b) + -G' t) := by
    refine intervalIntegral.integral_mono_on hb1 (hf'c.intervalIntegrable_of_Icc hb1).abs
      ((((continuous_wF.2.mul continuous_const).continuousOn).add hG'c.neg).intervalIntegrable_of_Icc hb1)
      fun t ht => ?_
    have hw1t := wF₁_nonneg t
    have hwt := Cvs.L2a.FarFarBound.wF_bounds t
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hw1t, abs_of_nonneg (show 0 ≤ 1 - wF t by linarith [hwt.2.1]),
      abs_of_nonpos (hG'0 t ht)]
    have : (1 - wF t) * -G' t ≤ -G' t := by
      have := hG'0 t ht
      nlinarith [hwt.1]
    nlinarith [mul_le_mul_of_nonneg_left (hGb t ht) hw1t]
  have hFw : ∫ t in (1 : ℝ)..b, wF₁ t = wF b - wF 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_wF_all t)
      (continuous_wF.2.intervalIntegrable _ _)
  have hFG : ∫ t in (1 : ℝ)..b, G' t = G b - G 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hG t (by rwa [hu] at ht))
      (hG'c.intervalIntegrable_of_Icc hb1)
  have hsplit : ∫ t in (1 : ℝ)..b, (wF₁ t * (-G b) + -G' t) = (wF b - wF 1) * (-G b) - (G b - G 1) := by
    rw [intervalIntegral.integral_add (f := fun t => wF₁ t * (-G b)) (g := fun t => -G' t)
      ((continuous_wF.2.mul continuous_const).intervalIntegrable _ _)
      (hG'c.intervalIntegrable_of_Icc hb1).neg, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_neg, hFw, hFG]
    ring
  rw [hsplit] at hint
  rw [hw1, sub_zero, one_mul, abs_of_nonpos (hG0 1 h1'), abs_mul, abs_of_nonneg hwb,
    abs_of_nonpos (hG0 b hb')]
  have := (Cvs.L2a.FarFarBound.wF_bounds b).2.1
  nlinarith [hG0 b hb']

/-- **Oscillation on the far side**: for `G ≥ 0` with `G′ ≤ 0` on `[M, ∞)`,
`|∫_M^∞ G cos(λt)| ≤ 2G(M)/|λ|`. -/
theorem osc_far {G G' : ℝ → ℝ} {M lam : ℝ} (hlam : lam ≠ 0)
    (hG : ∀ t ∈ Ici M, HasDerivAt G (G' t) t) (hG'c : ContinuousOn G' (Ici M))
    (hG'0 : ∀ t ∈ Ici M, G' t ≤ 0) (hG0 : ∀ t ∈ Ici M, 0 ≤ G t)
    (hint : IntegrableOn (fun t => G t * Real.cos (lam * t)) (Ioi M)) :
    |∫ t in Ioi M, G t * Real.cos (lam * t)| ≤ 2 * G M / |lam| := by
  have hR : ∀ R, M ≤ R → |∫ t in M..R, G t * Real.cos (lam * t)| ≤ 2 * G M / |lam| := by
    intro R hMR
    have hu : uIcc M R = Icc M R := uIcc_of_le hMR
    have hsub : Icc M R ⊆ Ici M := Icc_subset_Ici_self
    have h := Cvs.L2a.CutKernelSimplified.abs_integral_mul_cos_le hMR hlam
      (fun t ht => hG t (hsub (by rwa [hu] at ht))) ((hG'c.mono hsub).intervalIntegrable_of_Icc hMR)
    refine h.trans ?_
    rw [div_le_div_iff_of_pos_right (abs_pos.2 hlam)]
    have hGR : ∫ t in M..R, |G' t| = G M - G R := by
      rw [show (∫ t in M..R, |G' t|) = ∫ t in M..R, -G' t from
        intervalIntegral.integral_congr fun t ht => by
          rw [hu] at ht; rw [abs_of_nonpos (hG'0 t (hsub ht))],
        intervalIntegral.integral_neg,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hG t (hsub (by rwa [hu] at ht)))
          ((hG'c.mono hsub).intervalIntegrable_of_Icc hMR)]
      ring
    rw [hGR, abs_of_nonneg (hG0 M (mem_Ici.2 le_rfl)), abs_of_nonneg (hG0 R hMR)]
    linarith
  have ht := intervalIntegral_tendsto_integral_Ioi M hint Filter.tendsto_id
  exact le_of_tendsto ht.abs (Filter.eventually_atTop.2 ⟨M, fun R hR' => hR R hR'⟩)

/-! ### `g_m`: closed form, sign, monotonicity, derivative -/

/-- `∫₁^Y dv/(y² − v²) = g_Y(y)` off the poles. -/
theorem integral_inv_sq_sub {y Y : ℝ} (hY : 1 ≤ Y) (hy : 0 < y) (hq : ∀ v ∈ Icc 1 Y, y - v ≠ 0) :
    ∫ v in (1 : ℝ)..Y, 1 / (y ^ 2 - v ^ 2) = gY y Y := by
  have hp : ∀ v ∈ Icc 1 Y, 0 < y + v := fun v hv => by linarith [hv.1]
  have hu : uIcc (1 : ℝ) Y = Icc 1 Y := uIcc_of_le hY
  have hd : ∀ v ∈ uIcc (1 : ℝ) Y, HasDerivAt (fun v => (Real.log (y + v) - Real.log (y - v)) / (2 * y))
      (1 / (y ^ 2 - v ^ 2)) v := by
    intro v hv
    rw [hu] at hv
    have hA : HasDerivAt (fun v => y + v) 1 v := (hasDerivAt_id v).const_add y
    have hB : HasDerivAt (fun v => y - v) (-1) v := by simpa using (hasDerivAt_id v).const_sub y
    refine (((hA.log (hp v hv).ne').sub (hB.log (hq v hv))).div_const (2 * y)).congr_deriv ?_
    have := hq v hv
    have := (hp v hv).ne'
    rw [show y ^ 2 - v ^ 2 = (y + v) * (y - v) by ring]
    field_simp; ring
  have hc : ContinuousOn (fun v => 1 / (y ^ 2 - v ^ 2)) (uIcc (1 : ℝ) Y) := by
    rw [hu]
    refine continuousOn_const.div₀ (by fun_prop) fun v hv => ?_
    rw [show y ^ 2 - v ^ 2 = (y + v) * (y - v) by ring]
    exact mul_ne_zero (hp v hv).ne' (hq v hv)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable, gY]
  ring

/-- `g_m(t) = ∫₁^{Y(m)} dv/(t² − m²v²)` off the band `t/m ∈ [1, Y(m)]`. -/
theorem gT_eq_integral {m t : ℝ} (hm : 1 < m) (ht : 0 < t) (hoff : ∀ v ∈ Icc 1 (Ymax m), t / m ≠ v) :
    gT m t = ∫ v in (1 : ℝ)..Ymax m, 1 / (t ^ 2 - m ^ 2 * v ^ 2) := by
  have hm0 : 0 < m := by linarith
  have hY := one_le_Ymax hm
  unfold gT
  rw [← integral_inv_sq_sub hY (by positivity) fun v hv => sub_ne_zero.2 (hoff v hv),
    ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun v _ => ?_
  rw [div_pow, div_div]
  congr 1
  field_simp

theorem off_near {m t : ℝ} (hm : 0 < m) (htm : t < m) : ∀ v ∈ Icc 1 (Ymax m), t / m ≠ v := fun v hv h => by
  have : t / m < 1 := by rw [div_lt_one hm]; exact htm
  linarith [hv.1]

theorem off_far {m t : ℝ} (hm : 1 < m) (htb : Cvs.L2a.CornerSuprema.bm m < t) :
    ∀ v ∈ Icc 1 (Ymax m), t / m ≠ v := fun v hv h => by
  have hm0 : 0 < m := by linarith
  have hb : Cvs.L2a.CornerSuprema.bm m = m * Ymax m := by unfold Cvs.L2a.CornerSuprema.bm Ymax; ring
  have : Ymax m < t / m := by rw [lt_div_iff₀ hm0]; linarith
  linarith [hv.2]

/-- `g_m ≤ 0` and `g_m` antitone inside, `0 < t < m`. -/
theorem gT_near {m : ℝ} (hm : 1 < m) :
    (∀ t ∈ Ioo 0 m, gT m t ≤ 0) ∧ AntitoneOn (gT m) (Ioo 0 m) := by
  have hm0 : 0 < m := by linarith
  have hY := one_le_Ymax hm
  have hneg : ∀ t ∈ Ioo 0 m, ∀ v ∈ Icc 1 (Ymax m), t ^ 2 - m ^ 2 * v ^ 2 < 0 := fun t ht v hv => by
    have : m ^ 2 ≤ m ^ 2 * v ^ 2 := le_mul_of_one_le_right (by positivity) (by nlinarith [hv.1])
    nlinarith [ht.1, ht.2]
  have hcont : ∀ t ∈ Ioo 0 m, IntervalIntegrable (fun v => 1 / (t ^ 2 - m ^ 2 * v ^ 2)) volume 1 (Ymax m) :=
    fun t ht => (continuousOn_const.div₀ (by fun_prop) fun v hv => (hneg t ht v
      (by rwa [uIcc_of_le hY] at hv)).ne).intervalIntegrable
  constructor
  · intro t ht
    rw [gT_eq_integral hm ht.1 (off_near hm0 ht.2)]
    have := intervalIntegral.integral_mono_on hY (hcont t ht) (intervalIntegrable_const (c := (0 : ℝ)))
      fun v hv => (one_div_neg.2 (hneg t ht v hv)).le
    simpa using this
  · intro t₁ h₁ t₂ h₂ h12
    rw [gT_eq_integral hm h₁.1 (off_near hm0 h₁.2), gT_eq_integral hm h₂.1 (off_near hm0 h₂.2)]
    refine intervalIntegral.integral_mono_on hY (hcont t₂ h₂) (hcont t₁ h₁) fun v hv => ?_
    have a1 := hneg t₁ h₁ v hv
    have a2 := hneg t₂ h₂ v hv
    exact one_div_le_one_div_of_neg_of_le a2 (by nlinarith [h₁.1])

/-- `g_m ≥ 0` and `g_m` antitone beyond, `t > b_m`; there `g_m(t) ≤ (Y(m) − 1)/(t² − b_m²)`. -/
theorem gT_far {m : ℝ} (hm : 1 < m) :
    (∀ t ∈ Ioi (Cvs.L2a.CornerSuprema.bm m), 0 ≤ gT m t
        ∧ gT m t ≤ (Ymax m - 1) / (t ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2))
      ∧ AntitoneOn (gT m) (Ioi (Cvs.L2a.CornerSuprema.bm m)) := by
  have hm0 : 0 < m := by linarith
  have hY := one_le_Ymax hm
  have hb : Cvs.L2a.CornerSuprema.bm m = m * Ymax m := by unfold Cvs.L2a.CornerSuprema.bm Ymax; ring
  have hb0 : 0 < Cvs.L2a.CornerSuprema.bm m := by rw [hb]; positivity
  have hpos : ∀ t ∈ Ioi (Cvs.L2a.CornerSuprema.bm m), ∀ v ∈ Icc 1 (Ymax m),
      t ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2 ≤ t ^ 2 - m ^ 2 * v ^ 2 := fun t ht v hv => by
    have := pow_le_pow_left₀ (by linarith [hv.1]) hv.2 2
    rw [hb]; nlinarith
  have hpos' : ∀ t ∈ Ioi (Cvs.L2a.CornerSuprema.bm m), 0 < t ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2 :=
    fun t ht => by have : Cvs.L2a.CornerSuprema.bm m < t := ht; nlinarith
  have hcont : ∀ t ∈ Ioi (Cvs.L2a.CornerSuprema.bm m),
      IntervalIntegrable (fun v => 1 / (t ^ 2 - m ^ 2 * v ^ 2)) volume 1 (Ymax m) :=
    fun t ht => (continuousOn_const.div₀ (by fun_prop) fun v hv => (lt_of_lt_of_le (hpos' t ht) (hpos t ht v
      (by rwa [uIcc_of_le hY] at hv))).ne').intervalIntegrable
  have hint : ∀ t (ht : t ∈ Ioi (Cvs.L2a.CornerSuprema.bm m)), gT m t = _ := fun t ht =>
    gT_eq_integral hm (lt_trans hb0 ht) (off_far hm ht)
  refine ⟨fun t ht => ⟨?_, ?_⟩, fun t₁ h₁ t₂ h₂ h12 => ?_⟩
  · rw [hint t ht]
    exact intervalIntegral.integral_nonneg hY fun v hv =>
      (one_div_pos.2 (lt_of_lt_of_le (hpos' t ht) (hpos t ht v hv))).le
  · rw [hint t ht]
    have := intervalIntegral.integral_mono_on hY (hcont t ht)
      (intervalIntegrable_const (c := 1 / (t ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2))) fun v hv =>
        one_div_le_one_div_of_le (hpos' t ht) (hpos t ht v hv)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [div_eq_mul_one_div (Ymax m - 1)]
    exact this
  · rw [hint t₁ h₁, hint t₂ h₂]
    refine intervalIntegral.integral_mono_on hY (hcont t₂ h₂) (hcont t₁ h₁) fun v hv => ?_
    have a1 := lt_of_lt_of_le (hpos' t₁ h₁) (hpos t₁ h₁ v hv)
    exact one_div_le_one_div_of_le a1 (by have : (0 : ℝ) < t₁ := lt_trans hb0 h₁; nlinarith)

/-- The derivative of `g_Y` in `y`. -/
def gYd (y Y : ℝ) : ℝ :=
  ((1 / (y + Y) - 1 / (y - Y) - 1 / (y + 1) + 1 / (y - 1)) * (2 * y)
    - (Real.log (y + Y) - Real.log (y - Y) - Real.log (y + 1) + Real.log (y - 1)) * 2) / (2 * y) ^ 2

/-- The derivative of `g_m` in `t`. -/
def gTd (m t : ℝ) : ℝ := gYd (t / m) (Ymax m) * (1 / m) / m ^ 2

theorem hasDerivAt_gY {y Y : ℝ} (h1 : y + Y ≠ 0) (h2 : y - Y ≠ 0) (h3 : y + 1 ≠ 0) (h4 : y - 1 ≠ 0)
    (h5 : y ≠ 0) : HasDerivAt (fun y => gY y Y) (gYd y Y) y := by
  have hA := ((hasDerivAt_id y).add_const Y).log h1
  have hB := ((hasDerivAt_id y).sub_const Y).log h2
  have hC := ((hasDerivAt_id y).add_const 1).log h3
  have hD := ((hasDerivAt_id y).sub_const 1).log h4
  have hN := ((hA.sub hB).sub hC).add hD
  have hE : HasDerivAt (fun y : ℝ => 2 * y) 2 y := by simpa using (hasDerivAt_id y).const_mul 2
  have := hN.div hE (by positivity)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  · simp only [gYd, Pi.add_apply, Pi.sub_apply, id]
  · simp only [gY, Pi.div_apply, Pi.add_apply, Pi.sub_apply, id]

theorem continuousAt_gYd {y Y : ℝ} (h1 : y + Y ≠ 0) (h2 : y - Y ≠ 0) (h3 : y + 1 ≠ 0) (h4 : y - 1 ≠ 0)
    (h5 : y ≠ 0) : ContinuousAt (fun y => gYd y Y) y := by
  have h6 : (2 * y) ^ 2 ≠ 0 := by positivity
  unfold gYd
  fun_prop (disch := assumption)

/-- The derivative of `g_m` away from `0`, `m` and `b_m`. -/
theorem hasDerivAt_gT {m t : ℝ} (hm : 1 < m) (ht : 0 < t) (htm : t ≠ m)
    (htb : t ≠ Cvs.L2a.CornerSuprema.bm m) : HasDerivAt (gT m) (gTd m t) t ∧ ContinuousAt (gTd m) t := by
  have hm0 : 0 < m := by linarith
  have hY := one_le_Ymax hm
  have hb : Cvs.L2a.CornerSuprema.bm m = m * Ymax m := by unfold Cvs.L2a.CornerSuprema.bm Ymax; ring
  have hy : 0 < t / m := by positivity
  have h2 : t / m - Ymax m ≠ 0 := fun h => htb (by rw [hb]; field_simp at h; linarith)
  have h4 : t / m - 1 ≠ 0 := fun h => htm (by field_simp at h; linarith)
  have hd := hasDerivAt_gY (Y := Ymax m) (by linarith) h2 (by linarith) h4 hy.ne'
  have hc := continuousAt_gYd (Y := Ymax m) (by linarith) h2 (by linarith) h4 hy.ne'
  have hlin : HasDerivAt (fun t : ℝ => t / m) (1 / m) t := by simpa using (hasDerivAt_id t).div_const m
  constructor
  · have := (hd.comp t hlin).div_const (m ^ 2)
    unfold gT gTd
    simpa [Function.comp] using this
  · unfold gTd
    exact ((ContinuousAt.comp (g := fun y => gYd y (Ymax m)) (f := fun t : ℝ => t / m) hc
      (by fun_prop)).mul continuousAt_const).div_const _

theorem accPt_of_isOpen {s : Set ℝ} (hs : IsOpen s) {x : ℝ} (hx : x ∈ s) : AccPt x (Filter.principal s) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU (hs.mem_nhds hx))
  refine ⟨x + ε / 2, hball ?_, by linarith⟩
  rw [Metric.mem_ball, Real.dist_eq, show x + ε / 2 - x = ε / 2 by ring, abs_of_pos (by positivity)]
  linarith

/-- `g_m′ ≤ 0` inside, `0 < t < m`. -/
theorem gTd_nonpos_near {m t : ℝ} (hm : 1 < m) (ht : 0 < t) (htm : t < m) : gTd m t ≤ 0 := by
  have hb := Cvs.L2a.CornerSuprema.lt_bm hm
  obtain ⟨hd, -⟩ := hasDerivAt_gT hm ht htm.ne (by linarith)
  exact hd.hasDerivWithinAt.nonpos_of_antitoneOn (accPt_of_isOpen isOpen_Ioo ⟨ht, htm⟩) (gT_near hm).2

/-- `g_m′ ≤ 0` beyond, `t > b_m`. -/
theorem gTd_nonpos_far {m t : ℝ} (hm : 1 < m) (ht : Cvs.L2a.CornerSuprema.bm m < t) : gTd m t ≤ 0 := by
  have hb := Cvs.L2a.CornerSuprema.lt_bm hm
  obtain ⟨hd, -⟩ := hasDerivAt_gT hm (by linarith) (by linarith) ht.ne'
  exact hd.hasDerivWithinAt.nonpos_of_antitoneOn (accPt_of_isOpen isOpen_Ioi ht) (gT_far hm).2

/-- Integrability on `(M, ∞)` from a bound `C/(t − β)²`, `β < M`. -/
theorem integrableOn_Ioi_of_le_inv_sq {f : ℝ → ℝ} {M β C : ℝ} (hβ : β < M) (hf : ContinuousOn f (Ici M))
    (hb : ∀ t ∈ Ici M, |f t| ≤ C / (t - β) ^ 2) : IntegrableOn f (Ioi M) := by
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hb M (mem_Ici.2 le_rfl))
    have h2 : 0 < (M - β) ^ 2 := by have : 0 < M - β := by linarith
                                    positivity
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 h2)
  have hg : IntegrableOn (fun t => C / (t - β) ^ 2) (Ioi M) := by
    have hd : ∀ t ∈ Ici M, HasDerivAt (fun t => -C / (t - β)) (C / (t - β) ^ 2) t := fun t ht => by
      have h0 : t - β ≠ 0 := by have : M ≤ t := ht; linarith
      have := (((hasDerivAt_id t).sub_const β).inv h0).const_mul (-C)
      refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      · simp only [id]; field_simp
      · simp only [id, div_eq_mul_inv, Pi.inv_apply]
    have hlim : Filter.Tendsto (fun t => -C / (t - β)) Filter.atTop (nhds 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      exact (Filter.tendsto_atTop_add_const_right _ (-β) Filter.tendsto_id).congr fun t => by simp; ring
    exact integrableOn_Ioi_deriv_of_nonneg' hd (fun t ht => by
      have : 0 < t - β := by linarith [ht.out]
      positivity) hlim
  refine hg.mono' ((hf.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs]
  exact hb t (Ioi_subset_Ici_self ht)

/-- **The near oscillation**: `|∫₁^b (1 − wF)g_m cos(2ct)| ≤ |g_m(b)|/c` for `1 ≤ b < m`. -/
theorem osc_gT_near {m b c : ℝ} (hm : 1 < m) (hb1 : 1 ≤ b) (hbm : b < m) (hc : 0 < c) :
    |∫ t in (1 : ℝ)..b, (1 - wF t) * gT m t * Real.cos (2 * c * t)| ≤ |gT m b| / c := by
  have hbm' := Cvs.L2a.CornerSuprema.lt_bm hm
  have h := osc_near (G := gT m) (G' := gTd m) (lam := 2 * c) hb1 (by positivity)
    (fun t ht => (hasDerivAt_gT hm (by linarith [ht.1]) (by linarith [ht.2]) (by linarith [ht.2])).1)
    (fun t ht => (hasDerivAt_gT hm (by linarith [ht.1]) (by linarith [ht.2])
      (by linarith [ht.2])).2.continuousWithinAt)
    (fun t ht => gTd_nonpos_near hm (by linarith [ht.1]) (by linarith [ht.2]))
    (fun t ht => (gT_near hm).1 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  rw [abs_of_pos (by positivity : 0 < 2 * c)] at h
  calc _ ≤ 2 * |gT m b| / (2 * c) := h
    _ = |gT m b| / c := by field_simp

/-- **The far oscillation**: `|∫_M^∞ g_m cos(2ct)| ≤ g_m(M)/c` for `M > b_m`. -/
theorem osc_gT_far {m M c : ℝ} (hm : 1 < m) (hM : Cvs.L2a.CornerSuprema.bm m < M) (hc : 0 < c) :
    |∫ t in Ioi M, gT m t * Real.cos (2 * c * t)| ≤ gT m M / c := by
  have hb0 : 0 < Cvs.L2a.CornerSuprema.bm m := by linarith [Cvs.L2a.CornerSuprema.lt_bm hm]
  have hI : ∀ t ∈ Ici M, Cvs.L2a.CornerSuprema.bm m < t := fun t ht => lt_of_lt_of_le hM ht
  have hd : ∀ t ∈ Ici M, HasDerivAt (gT m) (gTd m t) t ∧ ContinuousAt (gTd m) t := fun t ht =>
    hasDerivAt_gT hm (by linarith [hI t ht]) (by linarith [hI t ht, Cvs.L2a.CornerSuprema.lt_bm hm])
      (hI t ht).ne'
  have hint : IntegrableOn (fun t => gT m t * Real.cos (2 * c * t)) (Ioi M) := by
    refine integrableOn_Ioi_of_le_inv_sq (β := Cvs.L2a.CornerSuprema.bm m) (C := Ymax m - 1) hM
      (fun t ht => ((hd t ht).1.continuousAt.mul (by fun_prop)).continuousWithinAt) fun t ht => ?_
    obtain ⟨h0, h1⟩ := (gT_far hm).1 t (hI t ht)
    have ht' := hI t ht
    rw [abs_mul, abs_of_nonneg h0]
    calc gT m t * |Real.cos (2 * c * t)| ≤ gT m t * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ ≤ (Ymax m - 1) / (t ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2) := by rw [mul_one]; exact h1
      _ ≤ (Ymax m - 1) / (t - Cvs.L2a.CornerSuprema.bm m) ^ 2 := by
          have := one_le_Ymax hm
          have h2 : 0 < t - Cvs.L2a.CornerSuprema.bm m := by linarith
          exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith)
  have h := osc_far (G := gT m) (G' := gTd m) (lam := 2 * c) (by positivity) (fun t ht => (hd t ht).1)
    (fun t ht => (hd t ht).2.continuousWithinAt) (fun t ht => gTd_nonpos_far hm (hI t ht))
    (fun t ht => ((gT_far hm).1 t (hI t ht)).1) hint
  rw [abs_of_pos (by positivity : 0 < 2 * c)] at h
  calc _ ≤ 2 * gT m M / (2 * c) := h
    _ = gT m M / c := by field_simp

/-! ### Closed `t`-integrals -/

theorem tendsto_log_sub (p q : ℝ) :
    Filter.Tendsto (fun t => Real.log (t + p) - Real.log (t - q)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun t => 1 + (p + q) / (t - q)) Filter.atTop (nhds 1) := by
    have : Filter.Tendsto (fun t => t - q) Filter.atTop Filter.atTop :=
      (Filter.tendsto_atTop_add_const_right _ (-q) Filter.tendsto_id).congr fun t => by simp; ring
    simpa using (tendsto_const_nhds.div_atTop this).const_add 1
  have h2 := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1)
  rw [Real.log_one] at h2
  refine h2.congr' (Filter.eventually_atTop.2 ⟨|p| + |q| + 1, fun t ht => ?_⟩)
  have hp : 0 < t + p := by linarith [neg_abs_le p, abs_nonneg q]
  have hq : 0 < t - q := by linarith [le_abs_self q, abs_nonneg p]
  simp only [Function.comp]
  rw [← Real.log_div hp.ne' hq.ne']
  congr 1
  field_simp
  ring

/-- `L_far` as a `t`-integral: `∫_M^∞ f_m = π²L_far(m, M)` for `M > b_m`. -/
theorem integral_fm_far {m M : ℝ} (hm : 1 < m) (hM : Cvs.L2a.CornerSuprema.bm m < M) :
    ∫ t in Ioi M, Cvs.L2a.CornerSuprema.fm m t = π ^ 2 * Cvs.L2a.CornerSuprema.Lfar m M := by
  have hb := Cvs.L2a.CornerSuprema.lt_bm hm
  set b := Cvs.L2a.CornerSuprema.bm m with hbd
  have hm0 : 0 < m := by linarith
  set F : ℝ → ℝ := fun t => (Real.log (t + m) - Real.log (t - m) - Real.log (t + b) + Real.log (t - b)) / (2 * m)
    with hF
  have hd : ∀ t ∈ Ici M, HasDerivAt F (Cvs.L2a.CornerSuprema.fm m t) t := fun t ht => by
    have ht' : M ≤ t := ht
    have h1 : t + m ≠ 0 := by linarith
    have h2 : t - m ≠ 0 := by linarith
    have h3 : t + b ≠ 0 := by linarith
    have h4 : t - b ≠ 0 := by linarith
    have := ((((((hasDerivAt_id t).add_const m).log h1).sub (((hasDerivAt_id t).sub_const m).log h2)).sub
      (((hasDerivAt_id t).add_const b).log h3)).add (((hasDerivAt_id t).sub_const b).log h4)).div_const (2 * m)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    · unfold Cvs.L2a.CornerSuprema.fm
      simp only [id]
      rw [← hbd]
      have h5 : m ^ 2 - t ^ 2 ≠ 0 := by nlinarith
      have h6 : b ^ 2 - t ^ 2 ≠ 0 := by nlinarith
      field_simp
      ring
    · simp only [hF, id, Pi.add_apply, Pi.sub_apply]
  have hpos : ∀ t ∈ Ioi M, 0 ≤ Cvs.L2a.CornerSuprema.fm m t := fun t ht => by
    have ht' : M < t := ht
    unfold Cvs.L2a.CornerSuprema.fm
    rw [← hbd]
    have h5 : 0 < t ^ 2 - m ^ 2 := by nlinarith
    have h6 : 0 < t ^ 2 - b ^ 2 := by nlinarith
    rw [show 1 / (m ^ 2 - t ^ 2) = -(1 / (t ^ 2 - m ^ 2)) by rw [← one_div_neg_eq_neg_one_div]; ring_nf,
      show b / m / (b ^ 2 - t ^ 2) = -(b / m / (t ^ 2 - b ^ 2)) by rw [← div_neg]; ring_nf]
    rw [neg_sub_neg, sub_nonneg, div_div, div_le_div_iff₀ h5 (by positivity)]
    have hbm : (0 : ℝ) < t ^ 2 + b * m := by nlinarith
    nlinarith [mul_pos (sub_pos.2 hb) hbm]
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have := ((tendsto_log_sub m m).sub (tendsto_log_sub b b)).div_const (2 * m)
    simp only [sub_self, zero_div] at this
    refine this.congr fun t => ?_
    simp only [hF]; ring
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hlim, Cvs.L2a.CornerSuprema.Lfar, ← hbd]
  have hMb : 0 < M - b := by linarith
  rw [Real.log_div (by linarith) hMb.ne', Real.log_div (by linarith) (by linarith)]
  simp only [hF]
  field_simp
  ring

/-- `∫_M^∞ t²/(t² − β²)² = M/(2(M² − β²)) + (1/(4β))log((M + β)/(M − β))` for `0 < β < M`. -/
def collF (β M : ℝ) : ℝ := M / (2 * (M ^ 2 - β ^ 2)) + 1 / (4 * β) * Real.log ((M + β) / (M - β))

theorem integral_collar_far {β M : ℝ} (hβ : 0 < β) (hM : β < M) :
    ∫ t in Ioi M, t ^ 2 / (t ^ 2 - β ^ 2) ^ 2 = collF β M := by
  set F : ℝ → ℝ := fun t => -t / (2 * (t ^ 2 - β ^ 2)) + 1 / (4 * β) * (Real.log (t - β) - Real.log (t + β))
    with hF
  have hd : ∀ t ∈ Ici M, HasDerivAt F (t ^ 2 / (t ^ 2 - β ^ 2) ^ 2) t := fun t ht => by
    have ht' : M ≤ t := ht
    have h1 : t - β ≠ 0 := by linarith
    have h2 : t + β ≠ 0 := by linarith
    have h30 : 0 < t ^ 2 - β ^ 2 := by nlinarith
    have h3 : 2 * (t ^ 2 - β ^ 2) ≠ 0 := by positivity
    have hq : HasDerivAt (fun t : ℝ => 2 * (t ^ 2 - β ^ 2)) (2 * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).sub_const (β ^ 2)).const_mul 2
      simpa using this
    have := ((hasDerivAt_id t).neg.div hq h3).add
      ((((hasDerivAt_id t).sub_const β).log h1).sub (((hasDerivAt_id t).add_const β).log h2) |>.const_mul (1 / (4 * β)))
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    · simp only [id, Pi.neg_apply]
      have h4 : t ^ 2 - β ^ 2 ≠ 0 := h30.ne'
      field_simp
      ring
    · simp only [hF, id, Pi.neg_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply, neg_div]
  have hpos : ∀ t ∈ Ioi M, 0 ≤ t ^ 2 / (t ^ 2 - β ^ 2) ^ 2 := fun t _ => by positivity
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have hi : ∀ p : ℝ, Filter.Tendsto (fun t : ℝ => 1 / (t + p)) Filter.atTop (nhds 0) := fun p =>
      tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ p Filter.tendsto_id)
    have h1 : Filter.Tendsto (fun t : ℝ => -t / (2 * (t ^ 2 - β ^ 2))) Filter.atTop (nhds 0) := by
      have := ((hi (-β)).add (hi β)).const_mul (-(1 / 4 : ℝ))
      simp only [add_zero, mul_zero] at this
      refine this.congr' (Filter.eventually_atTop.2 ⟨β + 1, fun t ht => ?_⟩)
      have h5 : t - β ≠ 0 := by linarith
      have h6 : t + β ≠ 0 := by linarith
      have h7 : t ^ 2 - β ^ 2 ≠ 0 := by
        rw [show t ^ 2 - β ^ 2 = (t - β) * (t + β) by ring]; exact mul_ne_zero h5 h6
      rw [← sub_eq_add_neg]
      field_simp
      ring
    have h2 := ((tendsto_log_sub β β).neg).const_mul (1 / (4 * β))
    simp only [neg_zero, mul_zero] at h2
    have := h1.add h2
    simp only [add_zero] at this
    refine this.congr fun t => ?_
    simp only [hF]
    ring
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hlim, collF]
  simp only [hF]
  rw [Real.log_div (by linarith) (by linarith)]
  ring

/-- `∫_M^∞ dt/(t − β)² = 1/(M − β)` for `β < M`. -/
theorem integral_inv_sq_far {β M : ℝ} (hM : β < M) : ∫ t in Ioi M, 1 / (t - β) ^ 2 = 1 / (M - β) := by
  have hd : ∀ t ∈ Ici M, HasDerivAt (fun t => -1 / (t - β)) (1 / (t - β) ^ 2) t := fun t ht => by
    have h0 : t - β ≠ 0 := by have : M ≤ t := ht; linarith
    have := (((hasDerivAt_id t).sub_const β).inv h0).const_mul (-1)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    · simp only [id]; field_simp
    · simp only [id, div_eq_mul_inv, Pi.inv_apply]
  have hlim : Filter.Tendsto (fun t => -1 / (t - β)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ((Filter.tendsto_atTop_add_const_right _ (-β) Filter.tendsto_id).congr
      fun t => by simp; ring)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun t ht => by positivity) hlim]
  ring

/-- `∫₁² dt/(a − t)² = 1/(a − 2) − 1/(a − 1)` for `a > 2`. -/
theorem integral_inv_sq_near {a : ℝ} (ha : 2 < a) :
    ∫ t in (1 : ℝ)..2, 1 / (a - t) ^ 2 = 1 / (a - 2) - 1 / (a - 1) := by
  have hd : ∀ t ∈ uIcc (1 : ℝ) 2, HasDerivAt (fun t => 1 / (a - t)) (1 / (a - t) ^ 2) t := fun t ht => by
    rw [uIcc_of_le (by norm_num)] at ht
    have h0 : a - t ≠ 0 := by linarith [ht.2]
    have := ((hasDerivAt_id t).const_sub a).inv h0
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    · simp only [id]; field_simp
    · simp only [id, one_div, Pi.inv_apply]
  have hc : ContinuousOn (fun t => 1 / (a - t) ^ 2) (uIcc (1 : ℝ) 2) := by
    rw [uIcc_of_le (by norm_num)]
    exact continuousOn_const.div₀ (by fun_prop) fun t ht => by
      have : a - t ≠ 0 := by linarith [ht.2]
      positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]

/-- `∫₁² (t² + m²)/(m² − t²)² = 𝔑_m` for `m > 2`. -/
theorem integral_nearEnv {m : ℝ} (hm : 2 < m) :
    ∫ t in (1 : ℝ)..2, (t ^ 2 + m ^ 2) / (m ^ 2 - t ^ 2) ^ 2 = Cvs.L2a.CornerSuprema.nearN m := by
  have hp : ∀ t ∈ Icc (1 : ℝ) 2, 0 < m ^ 2 - t ^ 2 := fun t ht => by nlinarith [ht.2, ht.1]
  have hd : ∀ t ∈ uIcc (1 : ℝ) 2, HasDerivAt (fun t => t / (m ^ 2 - t ^ 2))
      ((t ^ 2 + m ^ 2) / (m ^ 2 - t ^ 2) ^ 2) t := fun t ht => by
    rw [uIcc_of_le (by norm_num)] at ht
    have h0 := (hp t ht).ne'
    have hq : HasDerivAt (fun t : ℝ => m ^ 2 - t ^ 2) (-(2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_sub (m ^ 2)
    refine ((hasDerivAt_id t).div hq h0).congr_deriv ?_
    simp only [id]; field_simp; ring
  have hc : ContinuousOn (fun t => (t ^ 2 + m ^ 2) / (m ^ 2 - t ^ 2) ^ 2) (uIcc (1 : ℝ) 2) := by
    rw [uIcc_of_le (by norm_num)]
    exact (by fun_prop : Continuous fun t : ℝ => t ^ 2 + m ^ 2).continuousOn.div₀ (by fun_prop)
      fun t ht => pow_ne_zero 2 (hp t ht).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable, Cvs.L2a.CornerSuprema.nearN]
  have h4 : m ^ 2 - 4 ≠ 0 := by nlinarith
  have h1 : m ^ 2 - 1 ≠ 0 := by nlinarith
  norm_num

/-- `∫_M^∞ (t² + b²)/(t² − b²)² = 𝔉_m(M)` for `M > b = b_m`. -/
theorem integral_farEnv {m M : ℝ} (hm : 1 < m) (hM : Cvs.L2a.CornerSuprema.bm m < M) :
    ∫ t in Ioi M, (t ^ 2 + Cvs.L2a.CornerSuprema.bm m ^ 2) / (t ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2) ^ 2
      = Cvs.L2a.CornerSuprema.farF m M := by
  have hb0 : 0 < Cvs.L2a.CornerSuprema.bm m := by linarith [Cvs.L2a.CornerSuprema.lt_bm hm]
  set b := Cvs.L2a.CornerSuprema.bm m with hbd
  have hp : ∀ t ∈ Ici M, 0 < t ^ 2 - b ^ 2 := fun t ht => by
    have : M ≤ t := ht; nlinarith
  have hd : ∀ t ∈ Ici M, HasDerivAt (fun t => -t / (t ^ 2 - b ^ 2)) ((t ^ 2 + b ^ 2) / (t ^ 2 - b ^ 2) ^ 2) t :=
    fun t ht => by
      have h0 := (hp t ht).ne'
      have hq : HasDerivAt (fun t : ℝ => t ^ 2 - b ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t).sub_const (b ^ 2)
      refine (((hasDerivAt_id t).neg.div hq h0).congr_deriv ?_).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => ?_)
      · simp only [id, Pi.neg_apply]; field_simp; ring
      · simp only [id, Pi.neg_apply, Pi.div_apply]
  have hlim : Filter.Tendsto (fun t => -t / (t ^ 2 - b ^ 2)) Filter.atTop (nhds 0) := by
    have hi : ∀ p : ℝ, Filter.Tendsto (fun t : ℝ => 1 / (t + p)) Filter.atTop (nhds 0) := fun p =>
      tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ p Filter.tendsto_id)
    have := ((hi (-b)).add (hi b)).const_mul (-(1 / 2 : ℝ))
    simp only [add_zero, mul_zero] at this
    refine this.congr' (Filter.eventually_atTop.2 ⟨b + 1, fun t ht => ?_⟩)
    have h5 : t - b ≠ 0 := by linarith
    have h6 : t + b ≠ 0 := by linarith
    have h7 : t ^ 2 - b ^ 2 ≠ 0 := by
      rw [show t ^ 2 - b ^ 2 = (t - b) * (t + b) by ring]; exact mul_ne_zero h5 h6
    rw [← sub_eq_add_neg]
    field_simp
    ring
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun t ht => by positivity) hlim, Cvs.L2a.CornerSuprema.farF]
  ring

/-! ### Weighted Cauchy–Schwarz from pointwise majorants -/

theorem integral_sqrt_mul_le {S : Set ℝ} {p q : ℝ → ℝ} (hp : IntegrableOn p S) (hq : IntegrableOn q S)
    (hp0 : ∀ t ∈ S, 0 ≤ p t) (hq0 : ∀ t ∈ S, 0 ≤ q t) (hS : MeasurableSet S) :
    ∫ t in S, √(p t) * √(q t) ≤ √(∫ t in S, p t) * √(∫ t in S, q t) := by
  have hmp : AEStronglyMeasurable (fun t => √(p t)) (volume.restrict S) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hp.1
  have hmq : AEStronglyMeasurable (fun t => √(q t)) (volume.restrict S) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hq.1
  have hp2 : (fun t => √(p t) ^ 2) =ᵐ[volume.restrict S] p :=
    (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun t ht => Real.sq_sqrt (hp0 t ht))
  have hq2 : (fun t => √(q t) ^ 2) =ᵐ[volume.restrict S] q :=
    (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun t ht => Real.sq_sqrt (hq0 t ht))
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict S) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg (p t))
    (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg (q t))
    (by rw [ENNReal.ofReal_ofNat]; exact (memLp_two_iff_integrable_sq hmp).mpr (hp.congr hp2.symm))
    (by rw [ENNReal.ofReal_ofNat]; exact (memLp_two_iff_integrable_sq hmq).mpr (hq.congr hq2.symm))
  simp only [Real.rpow_two] at h
  rw [integral_congr_ae hp2, integral_congr_ae hq2] at h
  rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **Cauchy–Schwarz with two majorants**: `|h| ≤ √p(√q₁ + √q₂)` on `S` gives
`|∫_S h| ≤ √(∫_S p)(√(∫_S q₁) + √(∫_S q₂))`. -/
theorem abs_integral_le_sqrt {S : Set ℝ} (hS : MeasurableSet S) {h p q₁ q₂ : ℝ → ℝ}
    (hp : IntegrableOn p S) (hq₁ : IntegrableOn q₁ S) (hq₂ : IntegrableOn q₂ S)
    (hp0 : ∀ t ∈ S, 0 ≤ p t) (hq₁0 : ∀ t ∈ S, 0 ≤ q₁ t) (hq₂0 : ∀ t ∈ S, 0 ≤ q₂ t)
    (hh : ∀ t ∈ S, |h t| ≤ √(p t) * (√(q₁ t) + √(q₂ t))) :
    |∫ t in S, h t| ≤ √(∫ t in S, p t) * (√(∫ t in S, q₁ t) + √(∫ t in S, q₂ t)) := by
  have hi : ∀ q : ℝ → ℝ, IntegrableOn q S → (∀ t ∈ S, 0 ≤ q t) →
      IntegrableOn (fun t => √(p t) * √(q t)) S := fun q hq hq0 => by
    refine Integrable.mono' ((hp.add hq).div_const 2)
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hp.1).mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable hq.1)) ?_
    refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have a := Real.sq_sqrt (hp0 t ht)
    have b := Real.sq_sqrt (hq0 t ht)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (√(p t) - √(q t))]
  calc |∫ t in S, h t| ≤ ∫ t in S, |h t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in S, (√(p t) * √(q₁ t) + √(p t) * √(q₂ t)) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => abs_nonneg _)
          ((hi q₁ hq₁ hq₁0).add (hi q₂ hq₂ hq₂0)) ?_
        refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun t ht => ?_)
        have := hh t ht
        linarith
    _ = (∫ t in S, √(p t) * √(q₁ t)) + ∫ t in S, √(p t) * √(q₂ t) :=
        integral_add (hi q₁ hq₁ hq₁0) (hi q₂ hq₂ hq₂0)
    _ ≤ √(∫ t in S, p t) * √(∫ t in S, q₁ t) + √(∫ t in S, p t) * √(∫ t in S, q₂ t) :=
        add_le_add (integral_sqrt_mul_le hp hq₁ hp0 hq₁0 hS) (integral_sqrt_mul_le hp hq₂ hp0 hq₂0 hS)
    _ = _ := by ring

/-! ### The near side, `m ≥ 3` -/

/-- The bottom near comparison constant of Cvs.L2a.CutKernelSimplified (`m ≥ 3`). -/
def kNb : ℝ := 9 / 10 + 2 * (3 + 2 / 3) * (2 / 3 + 3 / √8) / (8 * (5 / 9) ^ 2)

/-- The bottom far comparison constant of Cvs.L2a.CutKernelSimplified. -/
def kFb (c : ℝ) : ℝ := 84 / 11 + 40 / (11 * c)

theorem kNb_le_kFb {c : ℝ} (hc : 0 < c) : kNb ≤ kFb c := by
  have h8 : (14 / 5 : ℝ) ≤ √8 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h3 : 3 / √8 ≤ 15 / 14 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have : 0 ≤ 40 / (11 * c) := by positivity
  unfold kNb kFb
  have : 2 * (3 + 2 / 3) * (2 / 3 + 3 / √8) / (8 * (5 / 9) ^ 2) ≤ 2 * (3 + 2 / 3) * (2 / 3 + 15 / 14) / (8 * (5 / 9) ^ 2) := by
    gcongr
  norm_num at this ⊢
  linarith

/-- The near main factor `Λⁿ_m = L_near(m) + |g_m(2)|/(π²c) + (4κ_S/π²)δ(3/4)a²/(a² − 4)²`, `a = m(1 − δ)`. -/
def lamN (c δ m : ℝ) : ℝ :=
  Cvs.L2a.CornerSuprema.Lnear m + |gT m 2| / (π ^ 2 * c)
    + 4 * (181 / 462) / π ^ 2 * δ * (3 / 4) * ((m * (1 - δ)) ^ 2 / ((m * (1 - δ)) ^ 2 - 4) ^ 2)

/-- The near chirp factor `Eⁿ_m = (2/π)T(c, m, d, δ, (a − 2)/m)(1/(a − 2) − 1/(a − 1))`. -/
def eN (c d δ m J : ℝ) : ℝ :=
  2 / π * tT c m d δ ((m * (1 - δ) - 2) / m) J * (1 / (m * (1 - δ) - 2) - 1 / (m * (1 - δ) - 1))

/-- The near correction factor `Kⁿ_m = (k_n/c)²κ_ι𝔑_m/(m² − 1)`. -/
def kN (c J m : ℝ) : ℝ := (kNb / c) ^ 2 * kapI c J * Cvs.L2a.CornerSuprema.nearN m / (m ^ 2 - 1)

theorem env_sq_div {m t : ℝ} (hm : 0 < m) (ht : t < m) (ht0 : 0 ≤ t) :
    (√((t / m) ^ 2 + 1) / (1 - (t / m) ^ 2)) ^ 2 / (m ^ 2 * (m ^ 2 - 1))
      = (t ^ 2 + m ^ 2) / (m ^ 2 - t ^ 2) ^ 2 / (m ^ 2 - 1) := by
  rw [div_pow, Real.sq_sqrt (by positivity)]
  have h1 : m ^ 2 - t ^ 2 ≠ 0 := by nlinarith
  rw [show 1 - (t / m) ^ 2 = (m ^ 2 - t ^ 2) / m ^ 2 by field_simp]
  field_simp

/-- The near main integrand `π⁻²(f_m − cos(2ct)g_m) + (4κ_S/π²)δa²/(a² − t²)²`, `a = m(1 − δ)`. -/
def mainN (c δ m t : ℝ) : ℝ :=
  (π ^ 2)⁻¹ * (Cvs.L2a.CornerSuprema.fm m t - Real.cos (2 * c * t) * gT m t)
    + 4 * (181 / 462) / π ^ 2 * δ * (m * (1 - δ)) ^ 2 / ((m * (1 - δ)) ^ 2 - t ^ 2) ^ 2

/-- The near chirp integrand `(2/π)T(c, m, d, δ, (a − 2)/m)/(a − t)²`. -/
def chirpN (c d δ m J t : ℝ) : ℝ := 2 / π * tT c m d δ ((m * (1 - δ) - 2) / m) J / (m * (1 - δ) - t) ^ 2

/-- The near envelope `(t² + m²)/((m² − t²)²(m² − 1))`. -/
def envN (m t : ℝ) : ℝ := (t ^ 2 + m ^ 2) / (m ^ 2 - t ^ 2) ^ 2 / (m ^ 2 - 1)

theorem continuousOn_fm_near {m b : ℝ} (hm : 1 < m) (hb : b < m) :
    ContinuousOn (Cvs.L2a.CornerSuprema.fm m) (Icc 0 b) := by
  have hbm := Cvs.L2a.CornerSuprema.lt_bm hm
  unfold Cvs.L2a.CornerSuprema.fm
  have hg1 : ContinuousOn (fun t : ℝ => m ^ 2 - t ^ 2) (Icc 0 b) :=
    continuousOn_const.sub (continuousOn_id.pow 2)
  have hg2 : ContinuousOn (fun t : ℝ => Cvs.L2a.CornerSuprema.bm m ^ 2 - t ^ 2) (Icc 0 b) :=
    continuousOn_const.sub (continuousOn_id.pow 2)
  refine (continuousOn_const.div₀ hg1 fun t ht => ?_).sub
    (continuousOn_const.div₀ hg2 fun t ht => ?_)
  · nlinarith [ht.2, ht.1]
  · nlinarith [ht.2, ht.1]

theorem continuousOn_gT_near {m b : ℝ} (hm : 1 < m) (hb : b < m) :
    ContinuousOn (gT m) (Icc 1 b) := fun t ht =>
  (hasDerivAt_gT hm (by linarith [ht.1]) (by linarith [ht.2])
    (by linarith [ht.2, Cvs.L2a.CornerSuprema.lt_bm hm])).1.continuousAt.continuousWithinAt

theorem continuousOn_mainN {c δ m : ℝ} (hm : 2 < m) (ha : 2 < m * (1 - δ)) :
    ContinuousOn (mainN c δ m) (Icc 1 2) := by
  have hfm := (continuousOn_fm_near (b := 2) (by linarith) hm).mono
    (Icc_subset_Icc (by norm_num : (0 : ℝ) ≤ 1) le_rfl)
  refine (continuousOn_const.mul (hfm.sub ((by fun_prop : Continuous fun t => Real.cos (2 * c * t)).continuousOn.mul
    (continuousOn_gT_near (by linarith) hm)))).add (continuousOn_const.div₀ (by fun_prop) fun t ht => ?_)
  have : 0 < (m * (1 - δ)) ^ 2 - t ^ 2 := by nlinarith [ht.1, ht.2]
  positivity

theorem continuousOn_chirpN {c d δ m J : ℝ} (ha : 2 < m * (1 - δ)) :
    ContinuousOn (chirpN c d δ m J) (Icc 1 2) :=
  continuousOn_const.div₀ (by fun_prop) fun t ht => pow_ne_zero 2 (by linarith [ht.2])

theorem continuousOn_envN {m : ℝ} (hm : 2 < m) : ContinuousOn (envN m) (Icc 1 2) := by
  refine ((by fun_prop : Continuous fun t : ℝ => t ^ 2 + m ^ 2).continuousOn.div₀ (by fun_prop) fun t ht => ?_).div_const _
  have : 0 < m ^ 2 - t ^ 2 := by nlinarith [ht.2, ht.1]
  positivity

/-- `∫₁²(1 − wF)·main ≤ Λⁿ_m`. -/
theorem integral_mainN_le {c δ m : ℝ} (hm : 3 ≤ m) (hδ : 0 < δ) (hδ1 : δ < 1) (ha : 2 < m * (1 - δ))
    (hc : 0 < c) : ∫ t in (1 : ℝ)..2, (1 - wF t) * mainN c δ m t ≤ lamN c δ m := by
  set A := m * (1 - δ) with hA
  have hw : ∀ t, 0 ≤ 1 - wF t ∧ 1 - wF t ≤ 1 := fun t => by
    have := Cvs.L2a.FarFarBound.wF_bounds t; constructor <;> linarith
  have hwc : ContinuousOn (fun t => 1 - wF t) (Icc 1 2) := (continuous_const.sub continuous_wF.1).continuousOn
  have hfm := (continuousOn_fm_near (m := m) (b := 2) (by linarith) (by linarith)).mono
    (Icc_subset_Icc (by norm_num : (0 : ℝ) ≤ 1) le_rfl)
  have hgT := continuousOn_gT_near (m := m) (by linarith) (by linarith : (2 : ℝ) < m)
  have hcos : Continuous fun t => Real.cos (2 * c * t) := by fun_prop
  have hden : ∀ t ∈ Icc (1 : ℝ) 2, 0 < A ^ 2 - t ^ 2 := fun t ht => by nlinarith [ht.1, ht.2]
  have i1 : IntervalIntegrable (fun t => (π ^ 2)⁻¹ * ((1 - wF t) * Cvs.L2a.CornerSuprema.fm m t)) volume 1 2 :=
    (continuousOn_const.mul (hwc.mul hfm)).intervalIntegrable_of_Icc (by norm_num)
  have i2 : IntervalIntegrable (fun t => (π ^ 2)⁻¹ * ((1 - wF t) * gT m t * Real.cos (2 * c * t))) volume 1 2 :=
    (continuousOn_const.mul ((hwc.mul hgT).mul hcos.continuousOn)).intervalIntegrable_of_Icc (by norm_num)
  have hcollc : ContinuousOn (fun t => (1 - wF t) * (4 * (181 / 462) / π ^ 2 * δ * A ^ 2 / (A ^ 2 - t ^ 2) ^ 2))
      (Icc 1 2) := hwc.mul (continuousOn_const.div₀ (by fun_prop) fun t ht => by
        have := hden t ht; positivity)
  have i3 := hcollc.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (1 : ℝ) ≤ 2)
  have e : (fun t => (1 - wF t) * mainN c δ m t)
      = fun t => (π ^ 2)⁻¹ * ((1 - wF t) * Cvs.L2a.CornerSuprema.fm m t)
        - (π ^ 2)⁻¹ * ((1 - wF t) * gT m t * Real.cos (2 * c * t))
        + (1 - wF t) * (4 * (181 / 462) / π ^ 2 * δ * A ^ 2 / (A ^ 2 - t ^ 2) ^ 2) :=
    funext fun t => by rw [mainN, ← hA]; ring
  rw [e, intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hL : (π ^ 2)⁻¹ * ∫ t in (1 : ℝ)..2, (1 - wF t) * Cvs.L2a.CornerSuprema.fm m t
      = Cvs.L2a.CornerSuprema.Lnear m := rfl
  have hO := osc_gT_near (m := m) (b := 2) (c := c) (by linarith) (by norm_num) (by linarith) hc
  have hO' : -((π ^ 2)⁻¹ * ∫ t in (1 : ℝ)..2, (1 - wF t) * gT m t * Real.cos (2 * c * t))
      ≤ |gT m 2| / (π ^ 2 * c) := by
    have := neg_abs_le (∫ t in (1 : ℝ)..2, (1 - wF t) * gT m t * Real.cos (2 * c * t))
    calc -((π ^ 2)⁻¹ * ∫ t in (1 : ℝ)..2, (1 - wF t) * gT m t * Real.cos (2 * c * t))
        ≤ (π ^ 2)⁻¹ * |∫ t in (1 : ℝ)..2, (1 - wF t) * gT m t * Real.cos (2 * c * t)| := by
          rw [← mul_neg]; gcongr; linarith
      _ ≤ (π ^ 2)⁻¹ * (|gT m 2| / c) := by gcongr
      _ = _ := by field_simp
  have hC : ∫ t in (1 : ℝ)..2, (1 - wF t) * (4 * (181 / 462) / π ^ 2 * δ * A ^ 2 / (A ^ 2 - t ^ 2) ^ 2)
      ≤ 4 * (181 / 462) / π ^ 2 * δ * (3 / 4) * (A ^ 2 / (A ^ 2 - 4) ^ 2) := by
    have hA4 : 0 < A ^ 2 - 4 := by nlinarith
    calc ∫ t in (1 : ℝ)..2, (1 - wF t) * (4 * (181 / 462) / π ^ 2 * δ * A ^ 2 / (A ^ 2 - t ^ 2) ^ 2)
        ≤ ∫ t in (1 : ℝ)..2, (4 * (181 / 462) / π ^ 2 * δ * A ^ 2 / (A ^ 2 - 4) ^ 2) * (1 - wF t) := by
          refine intervalIntegral.integral_mono_on (by norm_num) i3
            ((continuousOn_const.mul hwc).intervalIntegrable_of_Icc (by norm_num)) fun t ht => ?_
          rw [mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ (hw t).1
          have h1 : A ^ 2 - 4 ≤ A ^ 2 - t ^ 2 := by nlinarith [ht.1, ht.2]
          have := hden t ht
          gcongr
      _ = _ := by
          rw [intervalIntegral.integral_const_mul, Cvs.L2a.CornerSuprema.integral_weight]; ring
  rw [lamN, ← hA, hL]
  linarith

/-- `∫₁²(1 − wF)·chirp ≤ Eⁿ_m`. -/
theorem integral_chirpN_le {c d δ m J : ℝ} (hc : 0 < c) (hd : 0 < d) (hxd : 1 < m - d) (hδ : 0 ≤ δ)
    (hJ : 0 ≤ J) (ha : 2 < m * (1 - δ)) :
    ∫ t in (1 : ℝ)..2, (1 - wF t) * chirpN c d δ m J t ≤ eN c d δ m J := by
  have hm0 : 0 < m := by nlinarith
  have hT := tT_nonneg (J := J) (c := c) (x₀ := m) (d := d) (δ := δ) (r := (m * (1 - δ) - 2) / m) hc hd.le hxd hδ
    hJ (div_pos (by linarith) hm0)
  have hwc : ContinuousOn (fun t => 1 - wF t) (Icc 1 2) := (continuous_const.sub continuous_wF.1).continuousOn
  have hc1 := continuousOn_chirpN (c := c) (d := d) (J := J) ha
  calc ∫ t in (1 : ℝ)..2, (1 - wF t) * chirpN c d δ m J t
      ≤ ∫ t in (1 : ℝ)..2, 2 / π * tT c m d δ ((m * (1 - δ) - 2) / m) J * (1 / (m * (1 - δ) - t) ^ 2) := by
        refine intervalIntegral.integral_mono_on (by norm_num) ((hwc.mul hc1).intervalIntegrable_of_Icc (by norm_num))
          ((continuousOn_const.mul (continuousOn_const.div₀
            (show ContinuousOn (fun t : ℝ => (m * (1 - δ) - t) ^ 2) (Icc 1 2) from
              (continuousOn_const.sub continuousOn_id).pow 2) fun t ht =>
            (pow_ne_zero 2 (by linarith [ht.2]) : (m * (1 - δ) - t) ^ 2 ≠ 0))).intervalIntegrable_of_Icc (by norm_num)) fun t ht => ?_
        have hE0 : 0 ≤ chirpN c d δ m J t := by unfold chirpN; positivity
        have := Cvs.L2a.FarFarBound.wF_bounds t
        calc (1 - wF t) * chirpN c d δ m J t ≤ 1 * chirpN c d δ m J t :=
              mul_le_mul_of_nonneg_right (by linarith) hE0
          _ = _ := by unfold chirpN; ring
    _ = eN c d δ m J := by rw [intervalIntegral.integral_const_mul, integral_inv_sq_near ha, eN]

/-- `∫₁²(1 − wF)·env ≤ 𝔑_m/(m² − 1)`. -/
theorem integral_envN_le {m : ℝ} (hm : 2 < m) :
    ∫ t in (1 : ℝ)..2, (1 - wF t) * envN m t ≤ Cvs.L2a.CornerSuprema.nearN m / (m ^ 2 - 1) := by
  have hwc : ContinuousOn (fun t => 1 - wF t) (Icc 1 2) := (continuous_const.sub continuous_wF.1).continuousOn
  have hc1 := continuousOn_envN hm
  rw [← integral_nearEnv hm, ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_mono_on (by norm_num) ((hwc.mul hc1).intervalIntegrable_of_Icc (by norm_num))
    (hc1.intervalIntegrable_of_Icc (by norm_num)) fun t ht => ?_
  have hE0 : 0 ≤ envN m t := by
    unfold envN
    have : 0 < m ^ 2 - 1 := by nlinarith
    positivity
  have := Cvs.L2a.FarFarBound.wF_bounds t
  calc (1 - wF t) * envN m t ≤ 1 * envN m t := mul_le_mul_of_nonneg_right (by linarith) hE0
    _ = _ := by unfold envN; ring

/-! ### The far side -/

/-- The far collar end `b′ = m(Y(m) + δ)`. -/
def bP (m δ : ℝ) : ℝ := m * (Ymax m + δ)

/-- The far main integrand `π⁻²(f_m − cos(2ct)g_m) + (4κ_S/π²)δt²/(t² − b′²)²`. -/
def mainF (c δ m t : ℝ) : ℝ :=
  (π ^ 2)⁻¹ * (Cvs.L2a.CornerSuprema.fm m t - Real.cos (2 * c * t) * gT m t)
    + 4 * (181 / 462) / π ^ 2 * δ * t ^ 2 / (t ^ 2 - bP m δ ^ 2) ^ 2

/-- The far chirp integrand `(2/π)T(c, m, d, δ, (M − b′)/m)/(t − b′)²`. -/
def chirpF (c d δ m M J t : ℝ) : ℝ := 2 / π * tT c m d δ ((M - bP m δ) / m) J / (t - bP m δ) ^ 2

/-- The far envelope `(t² + b_m²)/((t² − b_m²)²(m² − 1))`. -/
def envF (m t : ℝ) : ℝ :=
  (t ^ 2 + Cvs.L2a.CornerSuprema.bm m ^ 2) / (t ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2) ^ 2 / (m ^ 2 - 1)

/-- The far main factor `Λᶠ_m = L_far(m, M) + g_m(M)/(π²c) + (4κ_S/π²)δ·collF(b′, M)`. -/
def lamF (c δ m M : ℝ) : ℝ :=
  Cvs.L2a.CornerSuprema.Lfar m M + gT m M / (π ^ 2 * c) + 4 * (181 / 462) / π ^ 2 * δ * collF (bP m δ) M

/-- The far chirp factor `Eᶠ_m = (2/π)T(c, m, d, δ, (M − b′)/m)/(M − b′)`. -/
def eFar (c d δ m M J : ℝ) : ℝ := 2 / π * tT c m d δ ((M - bP m δ) / m) J / (M - bP m δ)

/-- The far correction factor `Kᶠ_m = (k_f/c)²κ_ι𝔉_m(M)/(m² − 1)`. -/
def kF (c J m M : ℝ) : ℝ := (kFb c / c) ^ 2 * kapI c J * Cvs.L2a.CornerSuprema.farF m M / (m ^ 2 - 1)

theorem bm_le_bP {m δ : ℝ} (hm : 0 ≤ m) (hδ : 0 ≤ δ) : Cvs.L2a.CornerSuprema.bm m ≤ bP m δ := by
  have : Cvs.L2a.CornerSuprema.bm m = m * Ymax m := by unfold Cvs.L2a.CornerSuprema.bm Ymax; ring
  rw [this, bP]; nlinarith

theorem integrableOn_gTcos_far {m M c : ℝ} (hm : 1 < m) (hM : Cvs.L2a.CornerSuprema.bm m < M) :
    IntegrableOn (fun t => gT m t * Real.cos (2 * c * t)) (Ioi M) := by
  have hI : ∀ t ∈ Ici M, Cvs.L2a.CornerSuprema.bm m < t := fun t ht => lt_of_lt_of_le hM ht
  have hb := Cvs.L2a.CornerSuprema.lt_bm hm
  refine integrableOn_Ioi_of_le_inv_sq (β := Cvs.L2a.CornerSuprema.bm m) (C := Ymax m - 1) hM
    (fun t ht => ((hasDerivAt_gT hm (by linarith [hI t ht]) (by linarith [hI t ht])
      (hI t ht).ne').1.continuousAt.mul (by fun_prop)).continuousWithinAt) fun t ht => ?_
  obtain ⟨h0, h1⟩ := (gT_far hm).1 t (hI t ht)
  have ht' := hI t ht
  rw [abs_mul, abs_of_nonneg h0]
  have := one_le_Ymax hm
  have h2 : 0 < t - Cvs.L2a.CornerSuprema.bm m := by linarith
  calc gT m t * |Real.cos (2 * c * t)| ≤ gT m t * 1 := by gcongr; exact Real.abs_cos_le_one _
    _ ≤ (Ymax m - 1) / (t ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2) := by rw [mul_one]; exact h1
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith)

theorem integrableOn_fm_far {m M : ℝ} (hm : 1 < m) (hM : Cvs.L2a.CornerSuprema.bm m < M) :
    IntegrableOn (Cvs.L2a.CornerSuprema.fm m) (Ioi M) := by
  have hb := Cvs.L2a.CornerSuprema.lt_bm hm
  set b := Cvs.L2a.CornerSuprema.bm m with hbd
  have hm0 : 0 < m := by linarith
  refine integrableOn_Ioi_of_le_inv_sq (β := b) (C := 1 / (b - m) ^ 2 * 0 + (b / m + 1)) hM
    (fun t ht => ?_) fun t ht => ?_
  · have ht' : M ≤ t := ht
    unfold Cvs.L2a.CornerSuprema.fm
    rw [← hbd]
    have hg1 : ContinuousAt (fun t : ℝ => m ^ 2 - t ^ 2) t :=
      continuousAt_const.sub (continuousAt_id.pow 2)
    have hg2 : ContinuousAt (fun t : ℝ => b ^ 2 - t ^ 2) t :=
      continuousAt_const.sub (continuousAt_id.pow 2)
    refine ((continuousAt_const.div₀ hg1 ?_).sub (continuousAt_const.div₀ hg2 ?_)).continuousWithinAt
    · nlinarith
    · nlinarith
  · have ht' : M ≤ t := ht
    have h1 : 0 < t - b := by linarith
    have h5 : 0 < t ^ 2 - m ^ 2 := by nlinarith
    have h6 : 0 < t ^ 2 - b ^ 2 := by nlinarith
    unfold Cvs.L2a.CornerSuprema.fm
    rw [← hbd, show 1 / (m ^ 2 - t ^ 2) = -(1 / (t ^ 2 - m ^ 2)) by rw [← one_div_neg_eq_neg_one_div]; ring_nf,
      show b / m / (b ^ 2 - t ^ 2) = -(b / m / (t ^ 2 - b ^ 2)) by rw [← div_neg]; ring_nf]
    have hle : (t - b) ^ 2 ≤ t ^ 2 - b ^ 2 := by nlinarith
    have hle' : (t - b) ^ 2 ≤ t ^ 2 - m ^ 2 := by nlinarith
    have hb0 : 0 < b := by linarith
    have a1 : 1 / (t ^ 2 - m ^ 2) ≤ 1 / (t - b) ^ 2 := one_div_le_one_div_of_le (pow_pos h1 2) hle'
    have a2 : b / m / (t ^ 2 - b ^ 2) ≤ b / m / (t - b) ^ 2 := div_le_div_of_nonneg_left
      (div_nonneg hb0.le hm0.le) (pow_pos h1 2) hle
    have a3 : 0 ≤ 1 / (t ^ 2 - m ^ 2) := div_nonneg zero_le_one h5.le
    have a4 : 0 ≤ b / m / (t ^ 2 - b ^ 2) := div_nonneg (div_nonneg hb0.le hm0.le) h6.le
    rw [abs_le]
    constructor
    · have : (1 / (b - m) ^ 2 * 0 + (b / m + 1)) / (t - b) ^ 2 = b / m / (t - b) ^ 2 + 1 / (t - b) ^ 2 := by ring
      rw [this]; linarith
    · have : (1 / (b - m) ^ 2 * 0 + (b / m + 1)) / (t - b) ^ 2 = b / m / (t - b) ^ 2 + 1 / (t - b) ^ 2 := by ring
      rw [this]; linarith

/-- `∫_M^∞ main_far ≤ Λᶠ_m` for `M > b′`. -/
theorem integral_mainF_le {c δ m M : ℝ} (hm : 1 < m) (hδ : 0 < δ) (hM : bP m δ < M) (hc : 0 < c) :
    ∫ t in Ioi M, mainF c δ m t ≤ lamF c δ m M := by
  have hm0 : 0 < m := by linarith
  have hbb := bm_le_bP hm0.le hδ.le
  have hbM : Cvs.L2a.CornerSuprema.bm m < M := lt_of_le_of_lt hbb hM
  have hb0 : 0 < bP m δ := lt_of_lt_of_le (by linarith [Cvs.L2a.CornerSuprema.lt_bm hm]) hbb
  have i1 : IntegrableOn (fun t => (π ^ 2)⁻¹ * Cvs.L2a.CornerSuprema.fm m t) (Ioi M) :=
    (integrableOn_fm_far hm hbM).const_mul _
  have i2 : IntegrableOn (fun t => (π ^ 2)⁻¹ * (gT m t * Real.cos (2 * c * t))) (Ioi M) :=
    (integrableOn_gTcos_far hm hbM).const_mul _
  have i3 : IntegrableOn (fun t => 4 * (181 / 462) / π ^ 2 * δ * (t ^ 2 / (t ^ 2 - bP m δ ^ 2) ^ 2)) (Ioi M) := by
    refine Integrable.const_mul ?_ _
    refine integrableOn_Ioi_of_le_inv_sq (β := bP m δ) (C := 1) hM (fun t ht => ?_) fun t ht => ?_
    · have ht' : M ≤ t := ht
      exact (continuousAt_id.pow 2 |>.div₀ (by fun_prop) (by
        have : 0 < t ^ 2 - bP m δ ^ 2 := by nlinarith
        positivity)).continuousWithinAt
    · have ht' : M ≤ t := ht
      have h1 : 0 < t - bP m δ := by linarith
      rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by
        have : 0 < t ^ 2 - bP m δ ^ 2 := by nlinarith
        positivity) (by positivity), one_mul]
      have : (t - bP m δ) ^ 2 * t ^ 2 ≤ (t - bP m δ) ^ 2 * (t + bP m δ) ^ 2 := by
        gcongr
        · linarith
        · linarith
      nlinarith
  have e : (fun t => mainF c δ m t) = fun t => (π ^ 2)⁻¹ * Cvs.L2a.CornerSuprema.fm m t
      - (π ^ 2)⁻¹ * (gT m t * Real.cos (2 * c * t))
      + 4 * (181 / 462) / π ^ 2 * δ * (t ^ 2 / (t ^ 2 - bP m δ ^ 2) ^ 2) := funext fun t => by
    unfold mainF; ring
  have i12 : IntegrableOn (fun t => (π ^ 2)⁻¹ * Cvs.L2a.CornerSuprema.fm m t
      - (π ^ 2)⁻¹ * (gT m t * Real.cos (2 * c * t))) (Ioi M) := i1.sub i2
  rw [e, integral_add i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_fm_far hm hbM, integral_collar_far hb0 hM]
  have hO := osc_gT_far (c := c) hm hbM hc
  have hO' : -((π ^ 2)⁻¹ * ∫ t in Ioi M, gT m t * Real.cos (2 * c * t)) ≤ gT m M / (π ^ 2 * c) := by
    have := neg_abs_le (∫ t in Ioi M, gT m t * Real.cos (2 * c * t))
    calc -((π ^ 2)⁻¹ * ∫ t in Ioi M, gT m t * Real.cos (2 * c * t))
        ≤ (π ^ 2)⁻¹ * |∫ t in Ioi M, gT m t * Real.cos (2 * c * t)| := by
          rw [← mul_neg]; gcongr; linarith
      _ ≤ (π ^ 2)⁻¹ * (gT m M / c) := by gcongr
      _ = _ := by field_simp
  rw [lamF]
  have : (π ^ 2)⁻¹ * (π ^ 2 * Cvs.L2a.CornerSuprema.Lfar m M) = Cvs.L2a.CornerSuprema.Lfar m M := by
    field_simp
  linarith

/-- `∫_M^∞ chirp_far = Eᶠ_m`. -/
theorem integral_chirpF {c d δ m M J : ℝ} (hM : bP m δ < M) :
    ∫ t in Ioi M, chirpF c d δ m M J t = eFar c d δ m M J := by
  unfold chirpF eFar
  simp_rw [div_eq_mul_one_div (2 / π * tT c m d δ ((M - bP m δ) / m) J)]
  rw [integral_const_mul, integral_inv_sq_far hM]

theorem integrableOn_chirpF {c d δ m M J : ℝ} (hM : bP m δ < M) :
    IntegrableOn (chirpF c d δ m M J) (Ioi M) := by
  have hint : IntegrableOn (fun t => 1 / (t - bP m δ) ^ 2) (Ioi M) := by
    refine integrableOn_Ioi_of_le_inv_sq (β := bP m δ) (C := 1) hM (fun t ht => ?_) fun t ht => ?_
    · have ht' : M ≤ t := ht
      exact (continuousAt_const.div₀ (by fun_prop) (by
        have : 0 < t - bP m δ := by linarith
        positivity)).continuousWithinAt
    · rw [abs_of_nonneg (by positivity)]
  unfold chirpF
  simp_rw [div_eq_mul_one_div (2 / π * tT c m d δ ((M - bP m δ) / m) J)]
  exact hint.const_mul _

theorem integrableOn_envF {m M : ℝ} (hm : 1 < m) (hM : Cvs.L2a.CornerSuprema.bm m < M) :
    IntegrableOn (envF m) (Ioi M) := by
  have hb := Cvs.L2a.CornerSuprema.lt_bm hm
  set b := Cvs.L2a.CornerSuprema.bm m with hbd
  have hm1 : 0 < m ^ 2 - 1 := by nlinarith
  refine integrableOn_Ioi_of_le_inv_sq (β := b) (C := 1 / (m ^ 2 - 1)) hM (fun t ht => ?_) fun t ht => ?_
  · have ht' : M ≤ t := ht
    unfold envF; rw [← hbd]
    exact ((by fun_prop : ContinuousAt (fun t : ℝ => t ^ 2 + b ^ 2) t).div₀ (by fun_prop) (by
      have : 0 < t ^ 2 - b ^ 2 := by nlinarith
      positivity)).div_const _ |>.continuousWithinAt
  · have ht' : M ≤ t := ht
    have h1 : 0 < t - b := by linarith
    have h2 : 0 < t ^ 2 - b ^ 2 := by nlinarith
    unfold envF; rw [← hbd]
    have hk : (t ^ 2 + b ^ 2) * (t - b) ^ 2 ≤ (t ^ 2 - b ^ 2) ^ 2 := by
      have : (t ^ 2 - b ^ 2) ^ 2 = (t - b) ^ 2 * (t + b) ^ 2 := by ring
      rw [this]
      have : t ^ 2 + b ^ 2 ≤ (t + b) ^ 2 := by nlinarith [hb]
      nlinarith [sq_nonneg (t - b)]
    have e1 : (t ^ 2 + b ^ 2) / (t ^ 2 - b ^ 2) ^ 2 / (m ^ 2 - 1)
        = 1 / (m ^ 2 - 1) * ((t ^ 2 + b ^ 2) / (t ^ 2 - b ^ 2) ^ 2) := by ring
    have e2 : 1 / (m ^ 2 - 1) / (t - b) ^ 2 = 1 / (m ^ 2 - 1) * (1 / (t - b) ^ 2) := by ring
    rw [e1, e2, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    exact hk

theorem integral_envF {m M : ℝ} (hm : 1 < m) (hM : Cvs.L2a.CornerSuprema.bm m < M) :
    ∫ t in Ioi M, envF m t = Cvs.L2a.CornerSuprema.farF m M / (m ^ 2 - 1) := by
  unfold envF
  rw [integral_div, integral_farEnv hm hM]

/-! ### The windows -/

theorem window_unique {d t : ℝ} (hd : d ≤ 1 / 2) {m m' : ℕ} (h : t ∈ Ioc ((m : ℝ) - d) (m + d))
    (h' : t ∈ Ioc ((m' : ℝ) - d) (m' + d)) : m = m' := by
  have a1 : (m : ℝ) < m' + 1 := by linarith [h.1, h'.2]
  have a2 : (m' : ℝ) < m + 1 := by linarith [h'.1, h.2]
  have b1 : m < m' + 1 := by exact_mod_cast a1
  have b2 : m' < m + 1 := by exact_mod_cast a2
  omega

/-- At most one window covers a point: `Σ_m 1_{(m−d, m+d]}(t)f ≤ f`. -/
theorem sum_window_le {d t : ℝ} {f : ℝ → ℝ} (hd : d ≤ 1 / 2) (hf : 0 ≤ f t) (S : Finset ℕ) :
    ∑ m ∈ S, (Ioc ((m : ℝ) - d) (m + d)).indicator f t ≤ f t := by
  by_cases h : ∃ m ∈ S, t ∈ Ioc ((m : ℝ) - d) (m + d)
  · obtain ⟨m₀, hm₀, ht⟩ := h
    rw [Finset.sum_eq_single_of_mem m₀ hm₀ fun m _ hne => indicator_of_notMem
      (fun hm => hne (window_unique hd hm ht)) _, indicator_of_mem ht]
  · simp only [not_exists, not_and] at h
    rw [Finset.sum_eq_zero fun m hm => indicator_of_notMem (h m hm) _]
    exact hf

/-- **The window mass**: `∫_{(1,2]}wΦ² + ∫_{(M,∞)}Φ² + Σ_m W_m ≤ (1 + π²d²)∫₁^∞Φ²` for windows `(m − d, m + d)`,
`2 ≤ m ≤ M − 1`, `d ≤ 1/2`. -/
theorem window_mass_le {Φ : ℝ → ℝ} (hΦ : IntegrableOn (fun t => Φ t ^ 2) (Ioi 1)) {M : ℕ} (hM : 3 ≤ M) {d : ℝ}
    (hd0 : 0 < d) (hd : d ≤ 1 / 2) {S : Finset ℕ} (hS : ∀ m ∈ S, 2 ≤ m ∧ m + 1 ≤ M) :
    (∫ t in Ioc 1 2, (1 - wF t) * Φ t ^ 2) + (∫ t in Ioi (M : ℝ), Φ t ^ 2)
        + ∑ m ∈ S, ∫ x in ((m : ℝ) - d)..(m + d), Φ x ^ 2
      ≤ (1 + π ^ 2 * d ^ 2) * ∫ t in Ioi 1, Φ t ^ 2 := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM3 : ∀ m ∈ S, (m : ℝ) + 1 ≤ M := fun m hm => by exact_mod_cast (hS m hm).2
  have hm2 : ∀ m ∈ S, (2 : ℝ) ≤ m := fun m hm => by exact_mod_cast (hS m hm).1
  have hwm : Measurable fun t => 1 - wF t := (continuous_const.sub continuous_wF.1).measurable
  have i1 : IntegrableOn ((Ioc 1 2).indicator fun t => (1 - wF t) * Φ t ^ 2) (Ioi 1) := by
    refine Integrable.indicator ?_ measurableSet_Ioc
    refine hΦ.mono' (hwm.aestronglyMeasurable.mul hΦ.1) (ae_of_all _ fun t => ?_)
    have := Cvs.L2a.FarFarBound.wF_bounds t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (Φ t)]
  have i2 : IntegrableOn ((Ioi (M : ℝ)).indicator fun t => Φ t ^ 2) (Ioi 1) := hΦ.indicator measurableSet_Ioi
  have i3 : ∀ m ∈ S, IntegrableOn ((Ioc ((m : ℝ) - d) (m + d)).indicator fun t => Φ t ^ 2) (Ioi 1) :=
    fun m _ => hΦ.indicator measurableSet_Ioc
  have e1 : ∫ t in Ioc 1 2, (1 - wF t) * Φ t ^ 2
      = ∫ t in Ioi 1, (Ioc 1 2).indicator (fun t => (1 - wF t) * Φ t ^ 2) t := by
    rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 Ioc_subset_Ioi_self]
  have e2 : ∫ t in Ioi (M : ℝ), Φ t ^ 2 = ∫ t in Ioi 1, (Ioi (M : ℝ)).indicator (fun t => Φ t ^ 2) t := by
    rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 (Ioi_subset_Ioi (by linarith))]
  have e3 : ∀ m ∈ S, ∫ x in ((m : ℝ) - d)..(m + d), Φ x ^ 2
      = ∫ t in Ioi 1, (Ioc ((m : ℝ) - d) (m + d)).indicator (fun t => Φ t ^ 2) t := fun m hm => by
    have hsub : Ioc ((m : ℝ) - d) (m + d) ⊆ Ioi (1 : ℝ) := fun t ht => mem_Ioi.2 (by linarith [ht.1, hm2 m hm])
    rw [intervalIntegral.integral_of_le (by linarith), setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.2 hsub]
  have i12 : IntegrableOn (fun t => (Ioc 1 2).indicator (fun t => (1 - wF t) * Φ t ^ 2) t
      + (Ioi (M : ℝ)).indicator (fun t => Φ t ^ 2) t) (Ioi 1) := i1.add i2
  have i4 : IntegrableOn (fun t => ∑ m ∈ S, (Ioc ((m : ℝ) - d) (m + d)).indicator (fun t => Φ t ^ 2) t) (Ioi 1) :=
    integrable_finsetSum S i3
  rw [e1, e2, Finset.sum_congr rfl e3, ← integral_finsetSum S i3, ← integral_add i1 i2,
    ← integral_add i12 i4, ← integral_const_mul]
  refine setIntegral_mono_on (i12.add i4) (hΦ.const_mul _) measurableSet_Ioi fun t ht => ?_
  have ht1 : 1 < t := ht
  have hf := sq_nonneg (Φ t)
  have hw := Cvs.L2a.FarFarBound.wF_bounds t
  have hπd : 0 ≤ π ^ 2 * d ^ 2 * Φ t ^ 2 := by positivity
  have hsum := sum_window_le (t := t) (f := fun t => Φ t ^ 2) hd hf S
  rcases lt_or_ge (M : ℝ) t with hT | hT
  · rw [indicator_of_notMem (fun h => by linarith [h.2] : t ∉ Ioc 1 2), indicator_of_mem (mem_Ioi.2 hT),
      Finset.sum_eq_zero fun m hm => indicator_of_notMem (fun h => by linarith [h.2, hM3 m hm]) _]
    nlinarith
  · rw [indicator_of_notMem (fun h => by linarith [mem_Ioi.1 h] : t ∉ Ioi (M : ℝ))]
    rcases le_or_gt t 2 with h2 | h2
    · rw [indicator_of_mem (show t ∈ Ioc (1 : ℝ) 2 from ⟨ht1, h2⟩)]
      rcases le_or_gt t (2 - d) with h3 | h3
      · rw [Finset.sum_eq_zero fun m hm => indicator_of_notMem (fun h => by linarith [h.1, hm2 m hm]) _]
        nlinarith
      · have hwd : 1 - wF t ≤ π ^ 2 * d ^ 2 := by
          refine (Cvs.L2a.RampTopQuadratic.one_sub_wF_le t).trans ?_
          have : (2 - t) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
          gcongr
        nlinarith [mul_le_mul_of_nonneg_right hwd hf]
    · rw [indicator_of_notMem (fun h => by linarith [h.2] : t ∉ Ioc 1 2)]
      linarith

section nearside

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

theorem continuous_Phi (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0) :
    Continuous fun t => ∑ i, a i * psi c (g i) t :=
  continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1

/-- The pointwise split `|wΦ𝔅| ≤ √(wΦ²)(√(w𝔅_si²) + √(w𝔅_co²))`. -/
theorem abs_wPhi_frakB_le {w Φ F S C q₁ q₂ : ℝ} (hw : 0 ≤ w) (hF : F = S + C) (h1 : w * S ^ 2 ≤ q₁)
    (h2 : w * C ^ 2 ≤ q₂) : |w * Φ * F| ≤ √(w * Φ ^ 2) * (√q₁ + √q₂) := by
  have e1 : √(w * Φ ^ 2) = √w * |Φ| := by rw [Real.sqrt_mul hw, Real.sqrt_sq_eq_abs]
  have k1 : √w * |S| ≤ √q₁ := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hw]; exact Real.sqrt_le_sqrt h1
  have k2 : √w * |C| ≤ √q₂ := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hw]; exact Real.sqrt_le_sqrt h2
  rw [e1, hF, abs_mul, abs_mul, abs_of_nonneg hw]
  have hs := Real.mul_self_sqrt hw
  calc w * |Φ| * |S + C| ≤ w * |Φ| * (|S| + |C|) := by gcongr; exact abs_add_le _ _
    _ = √w * |Φ| * (√w * |S| + √w * |C|) := by
        conv_lhs => rw [← hs]
        ring
    _ ≤ √w * |Φ| * (√q₁ + √q₂) := by gcongr

/-- **The near corner, `m ≥ 3`**: `|∫_{(1,2]} wΦ𝔅_m| ≤ √(∫_{(1,2]} wΦ²)(√(Λⁿ_m W_m + Eⁿ_m P) + √(Kⁿ_m P))`. -/
theorem near_range (a : ι → ℝ) {M m : ℕ} {d δ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hm : 3 ≤ m) (hmM : m ≤ M)
    (hd : 0 < d) (hxd : 1 < (m : ℝ) - d) (hδ : 0 < δ) (hδ1 : δ < 1) (ha : 2 < m * (1 - δ)) :
    |∫ t in Ioc 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t|
      ≤ √(∫ t in Ioc 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2)
        * (√(lamN c δ m * (∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2)
              + eN c d δ m (Fintype.card ι) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
          + √(kN c (Fintype.card ι) m * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)) := by
  have hc0 : 0 < c := by linarith
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hΦc : Continuous fun t => ∑ i, a i * psi c (g i) t := continuous_Phi a hg hg₁ hg₂c hang
  set W := ∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2 with hW
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have hw : ∀ t, 0 ≤ 1 - wF t ∧ 1 - wF t ≤ 1 := fun t => by
    have := Cvs.L2a.FarFarBound.wF_bounds t; constructor <;> linarith
  have hwc : ContinuousOn (fun t => 1 - wF t) (Icc 1 2) := (continuous_const.sub continuous_wF.1).continuousOn
  have hsi : ∀ t ∈ Icc (1 : ℝ) 2, bSi c χ g a m t ^ 2
      ≤ mainN c δ m t * W + chirpN c d δ m (Fintype.card ι) t * P := fun t ht =>
    bSi_sq_le_near a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM (by omega) hmM hd hxd hδ hδ1
      (by linarith [ht.1]) (by linarith [ht.2]) (div_pos (by linarith) hm0) (by
        rw [div_le_iff₀ hm0]
        have : t / m * m = t := by field_simp
        nlinarith [ht.2])
  have hco : ∀ t ∈ Icc (1 : ℝ) 2, bCo c χ g a m t ^ 2
      ≤ (kNb / c) ^ 2 * kapI c (Fintype.card ι) * envN m t * P := fun t ht => by
    have htm : t < m := by linarith [ht.2]
    have h := (t0_frakB a (K := kNb) (S := √((t / m) ^ 2 + 1) / (1 - (t / m) ^ 2)) hg hg₁ hg₂c hang hc hχ0 hχc
      hχi hM (by omega) hmM (by linarith [ht.1]) (off_near hm0 htm) (fun η h1 h2 => by
        refine (Cvs.L2a.CutKernelSimplified.kCmp_le_near (y₀ := 2 / m) hc0 (by linarith)
          (div_pos (by linarith [ht.1]) hm0) (by rw [div_le_div_iff_of_pos_right hm0]; exact ht.2)
          (by rw [div_lt_one hm0]; linarith) h1 h2).trans ?_
        have := Cvs.L2a.CutKernelSimplified.kNear_bot_le m hm (c := c) (by linarith)
        unfold kNb
        exact this)
      (fun v hv => env_near (div_pos (by linarith [ht.1]) hm0).le (by rw [div_lt_one hm0]; exact htm) hv.1)).2
    rw [envN, ← env_sq_div hm0 htm (by linarith [ht.1])]
    calc _ ≤ _ := h
      _ = _ := by ring
  have hq1c : ContinuousOn (fun t => (1 - wF t) * (mainN c δ m t * W + chirpN c d δ m (Fintype.card ι) t * P))
      (Icc 1 2) :=
    hwc.mul (((continuousOn_mainN (c := c) (by linarith) ha).mul continuousOn_const).add
      ((continuousOn_chirpN ha).mul continuousOn_const))
  have hq2c : ContinuousOn (fun t => (1 - wF t) * ((kNb / c) ^ 2 * kapI c (Fintype.card ι) * envN m t * P))
      (Icc 1 2) := hwc.mul ((continuousOn_const.mul (continuousOn_envN (by linarith))).mul continuousOn_const)
  have hsi' : ∀ t ∈ Icc (1 : ℝ) 2, (1 - wF t) * bSi c χ g a m t ^ 2
      ≤ (1 - wF t) * (mainN c δ m t * W + chirpN c d δ m (Fintype.card ι) t * P) :=
    fun t ht => mul_le_mul_of_nonneg_left (hsi t ht) (hw t).1
  have hco' : ∀ t ∈ Icc (1 : ℝ) 2, (1 - wF t) * bCo c χ g a m t ^ 2
      ≤ (1 - wF t) * ((kNb / c) ^ 2 * kapI c (Fintype.card ι) * envN m t * P) :=
    fun t ht => mul_le_mul_of_nonneg_left (hco t ht) (hw t).1
  have hIcc : ∀ t ∈ Ioc (1 : ℝ) 2, t ∈ Icc (1 : ℝ) 2 := fun t ht => ⟨ht.1.le, ht.2⟩
  have key := abs_integral_le_sqrt
    (h := fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t)
    measurableSet_Ioc
    (((hwc.mul (hΦc.pow 2).continuousOn).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    (hq1c.integrableOn_Icc.mono_set Ioc_subset_Icc_self) (hq2c.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (fun t _ => mul_nonneg (hw t).1 (sq_nonneg _))
    (fun t ht => (mul_nonneg (hw t).1 (sq_nonneg _)).trans (hsi' t (hIcc t ht)))
    (fun t ht => (mul_nonneg (hw t).1 (sq_nonneg _)).trans (hco' t (hIcc t ht)))
    (fun t ht => abs_wPhi_frakB_le (hw t).1 (by unfold bCo; ring) (hsi' t (hIcc t ht)) (hco' t (hIcc t ht)))
  refine key.trans (mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_))
    (Real.sqrt_nonneg _))
  · rw [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    have i1 : IntervalIntegrable (fun t => (1 - wF t) * mainN c δ m t) volume 1 2 :=
      (hwc.mul (continuousOn_mainN (c := c) (by linarith) ha)).intervalIntegrable_of_Icc (by norm_num)
    have i2 : IntervalIntegrable (fun t => (1 - wF t) * chirpN c d δ m (Fintype.card ι) t) volume 1 2 :=
      (hwc.mul (continuousOn_chirpN (c := c) (d := d) (J := Fintype.card ι) ha)).intervalIntegrable_of_Icc
        (by norm_num)
    have e : (fun t => (1 - wF t) * (mainN c δ m t * W + chirpN c d δ m (Fintype.card ι) t * P))
        = fun t => W * ((1 - wF t) * mainN c δ m t) + P * ((1 - wF t) * chirpN c d δ m (Fintype.card ι) t) :=
      funext fun t => by ring
    rw [e, intervalIntegral.integral_add (i1.const_mul W) (i2.const_mul P), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    have h1 := integral_mainN_le (c := c) hm3 hδ hδ1 ha hc0
    have h2 := integral_chirpN_le (J := (Fintype.card ι : ℝ)) hc0 hd hxd hδ.le (by positivity) ha
    nlinarith [mul_le_mul_of_nonneg_left h1 hW0, mul_le_mul_of_nonneg_left h2 hP0]
  · rw [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    have i1 : IntervalIntegrable (fun t => (1 - wF t) * envN m t) volume 1 2 :=
      (hwc.mul (continuousOn_envN (m := m) (by linarith))).intervalIntegrable_of_Icc (by norm_num)
    have e : (fun t => (1 - wF t) * ((kNb / c) ^ 2 * kapI c (Fintype.card ι) * envN m t * P))
        = fun t => ((kNb / c) ^ 2 * kapI c (Fintype.card ι) * P) * ((1 - wF t) * envN m t) :=
      funext fun t => by ring
    rw [e, intervalIntegral.integral_const_mul]
    have h1 := integral_envN_le (m := m) (by linarith)
    have hk : 0 ≤ (kNb / c) ^ 2 * kapI c (Fintype.card ι) * P := by unfold kapI; positivity
    calc _ ≤ (kNb / c) ^ 2 * kapI c (Fintype.card ι) * P * (Cvs.L2a.CornerSuprema.nearN m / (m ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_left h1 hk
      _ = _ := by rw [kN]; ring

theorem integrableOn_Phi_sq (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0) (hc : 0 < c) :
    MemLp (fun x => ∑ i, a i * psi c (g i) x) 2 (volume.restrict (Ioi 1))
      ∧ IntegrableOn (fun x => (∑ i, a i * psi c (g i) x) ^ 2) (Ioi 1) := by
  have hm : MemLp (fun x => ∑ i, a i * psi c (g i) x) 2 (volume.restrict (Ioi 1)) := by
    have := memLp_finsetSum' Finset.univ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
    refine this.ae_eq (ae_of_all _ fun x => ?_)
    simp [Finset.sum_apply]
  exact ⟨hm, (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm⟩

/-- **The far corner**: for `b′ = m(Y(m) + δ) < M`, `|∫_{(M,∞)} Φ𝔅_m| ≤ √(∫_{(M,∞)} Φ²)(√(Λᶠ_m W_m + Eᶠ_m P)
+ √(Kᶠ_m P))`. -/
theorem far_range (a : ι → ℝ) {M m : ℕ} {d δ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hm : 2 ≤ m) (hmM : m + 1 ≤ M)
    (hd : 0 < d) (hxd : 1 < (m : ℝ) - d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hbM : bP m δ < M) :
    |∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t|
      ≤ √(∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) ^ 2)
        * (√(lamF c δ m M * (∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2)
              + eFar c d δ m M (Fintype.card ι) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
          + √(kF c (Fintype.card ι) m M * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)) := by
  have hc0 : 0 < c := by linarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) < m := by linarith
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hY := one_le_Ymax hm1
  have hbb := bm_le_bP hm0.le hδ.le
  have hbm := Cvs.L2a.CornerSuprema.lt_bm hm1
  have hbM' : Cvs.L2a.CornerSuprema.bm m < M := lt_of_le_of_lt hbb hbM
  have hbmY : Cvs.L2a.CornerSuprema.bm m = m * Ymax m := by unfold Cvs.L2a.CornerSuprema.bm Ymax; ring
  have hYM : Ymax m < (M : ℝ) / m := by rw [lt_div_iff₀ hm0]; linarith
  have hΦ := integrableOn_Phi_sq a hg hg₁ hg₂c hang hc0
  set W := ∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2 with hW
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have hsi : ∀ t ∈ Ioi (M : ℝ), bSi c χ g a m t ^ 2
      ≤ mainF c δ m t * W + chirpF c d δ m M (Fintype.card ι) t * P := fun t ht => by
    have ht' : (M : ℝ) < t := ht
    exact bSi_sq_le_far a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM hm (by omega) hd hxd hδ hδ1
      (by rw [← bP]; linarith) (div_pos (by linarith) hm0) (by
        rw [div_le_iff₀ hm0, bP]
        have : (t / m - Ymax m - δ) * m = t - m * (Ymax m + δ) := by field_simp; ring
        rw [this]; linarith)
  have hco : ∀ t ∈ Ioi (M : ℝ), bCo c χ g a m t ^ 2
      ≤ (kFb c / c) ^ 2 * kapI c (Fintype.card ι) * envF m t * P := fun t ht => by
    have ht' : (M : ℝ) < t := ht
    have hyM : (M : ℝ) / m ≤ t / m := by gcongr
    have h := (t0_frakB a (K := kFb c) (S := √((t / m) ^ 2 + Ymax m ^ 2) / ((t / m) ^ 2 - Ymax m ^ 2))
      hg hg₁ hg₂c hang hc hχ0 hχc hχi hM hm (by omega) (by linarith) (off_far hm1 (by linarith))
      (fun η h1 h2 => by
        refine (Cvs.L2a.CutKernelSimplified.kCmp_le_far (y₁ := (M : ℝ) / m) hc0 hm1 hY h2 (le_of_eq ?_) hYM hyM).trans ?_
        · unfold Ymax
          rw [div_pow, Real.sq_sqrt (by nlinarith)]
          have : (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
          field_simp; ring
        · exact Cvs.L2a.CutKernelSimplified.kFar_bot_le M m hm (by omega) hc0)
      (fun v hv => env_far (by linarith [hv.1]) hv.2 (lt_of_lt_of_le hYM hyM))).2
    have e : (√((t / m) ^ 2 + Ymax m ^ 2) / ((t / m) ^ 2 - Ymax m ^ 2)) ^ 2 / (m ^ 2 * (m ^ 2 - 1))
        = envF m t := by
      unfold envF
      rw [hbmY, div_pow, Real.sq_sqrt (by positivity)]
      have h1 : (t / m) ^ 2 - Ymax m ^ 2 ≠ 0 := by
        have := lt_of_lt_of_le hYM hyM
        have : 0 < (t / m) ^ 2 - Ymax m ^ 2 := by nlinarith [hY]
        exact this.ne'
      have h2 : t ^ 2 - (m * Ymax m) ^ 2 ≠ 0 := by
        have : t ^ 2 - (m * Ymax m) ^ 2 = m ^ 2 * ((t / m) ^ 2 - Ymax m ^ 2) := by field_simp
        rw [this]; exact mul_ne_zero (by positivity) h1
      have h3 : (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp
    rw [← e]
    calc _ ≤ _ := h
      _ = _ := by ring
  have hIM : IntegrableOn (fun t => (∑ i, a i * psi c (g i) t) ^ 2) (Ioi (M : ℝ)) :=
    hΦ.2.mono_set (Ioi_subset_Ioi (by linarith))
  have hb0 : 0 < bP m δ := by linarith
  have iMain : IntegrableOn (mainF c δ m) (Ioi (M : ℝ)) := by
      have i1 := (integrableOn_fm_far hm1 hbM').const_mul (π ^ 2)⁻¹
      have i2 := (integrableOn_gTcos_far (c := c) hm1 hbM').const_mul (π ^ 2)⁻¹
      have i3 : IntegrableOn (fun t => 4 * (181 / 462) / π ^ 2 * δ * (t ^ 2 / (t ^ 2 - bP m δ ^ 2) ^ 2)) (Ioi (M : ℝ)) := by
        refine Integrable.const_mul ?_ _
        refine integrableOn_Ioi_of_le_inv_sq (β := bP m δ) (C := 1) hbM (fun t ht => ?_) fun t ht => ?_
        · have ht' : (M : ℝ) ≤ t := ht
          have hg : ContinuousAt (fun t : ℝ => (t ^ 2 - bP m δ ^ 2) ^ 2) t :=
            ((continuousAt_id.pow 2).sub continuousAt_const).pow 2
          have h0 : (t ^ 2 - bP m δ ^ 2) ^ 2 ≠ 0 := by
            have : 0 < t ^ 2 - bP m δ ^ 2 := by nlinarith
            positivity
          exact ((continuousAt_id.pow 2).div₀ hg h0).continuousWithinAt
        · have ht' : (M : ℝ) ≤ t := ht
          have h1 : 0 < t - bP m δ := by linarith
          rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by
            have : 0 < t ^ 2 - bP m δ ^ 2 := by nlinarith
            positivity) (by positivity), one_mul]
          have : (t - bP m δ) ^ 2 * t ^ 2 ≤ (t - bP m δ) ^ 2 * (t + bP m δ) ^ 2 := by
            gcongr
            · linarith
            · linarith
          nlinarith
      have e : mainF c δ m = fun t => (π ^ 2)⁻¹ * Cvs.L2a.CornerSuprema.fm m t
          - (π ^ 2)⁻¹ * (gT m t * Real.cos (2 * c * t))
          + 4 * (181 / 462) / π ^ 2 * δ * (t ^ 2 / (t ^ 2 - bP m δ ^ 2) ^ 2) := funext fun t => by
        unfold mainF; ring
      rw [e]
      exact (i1.sub i2).add i3
  have iCh := integrableOn_chirpF (c := c) (d := d) (J := Fintype.card ι) hbM
  have iM : IntegrableOn (fun t => mainF c δ m t * W + chirpF c d δ m M (Fintype.card ι) t * P) (Ioi (M : ℝ)) :=
    (iMain.mul_const W).add (iCh.mul_const P)
  have iK : IntegrableOn (fun t => (kFb c / c) ^ 2 * kapI c (Fintype.card ι) * envF m t * P) (Ioi (M : ℝ)) :=
    ((integrableOn_envF hm1 hbM').const_mul ((kFb c / c) ^ 2 * kapI c (Fintype.card ι))).mul_const P
  have key := abs_integral_le_sqrt
    (h := fun t => (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t)
    (p := fun t => (∑ i, a i * psi c (g i) t) ^ 2) measurableSet_Ioi hIM iM iK
    (fun t _ => sq_nonneg _)
    (fun t ht => (sq_nonneg _).trans (hsi t ht))
    (fun t ht => (sq_nonneg _).trans (hco t ht))
    (fun t ht => by
      have := abs_wPhi_frakB_le (w := 1) (Φ := ∑ i, a i * psi c (g i) t)
        (F := Cvs.L2a.CutKernels.frakB c χ g a m t) (S := bSi c χ g a m t) (C := bCo c χ g a m t)
        (q₁ := mainF c δ m t * W + chirpF c d δ m M (Fintype.card ι) t * P)
        (q₂ := (kFb c / c) ^ 2 * kapI c (Fintype.card ι) * envF m t * P) zero_le_one
        (by unfold bCo; ring) (by rw [one_mul]; exact hsi t ht) (by rw [one_mul]; exact hco t ht)
      simpa only [one_mul] using this)
  refine key.trans (mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_))
    (Real.sqrt_nonneg _))
  · rw [integral_add (iMain.mul_const W) (iCh.mul_const P), integral_mul_const, integral_mul_const,
      integral_chirpF hbM]
    have h1 := integral_mainF_le hm1 hδ hbM hc0
    nlinarith [mul_le_mul_of_nonneg_right h1 hW0]
  · rw [integral_mul_const, integral_const_mul, integral_envF hm1 hbM']
    unfold kF
    have : 0 ≤ (kFb c / c) ^ 2 * kapI c (Fintype.card ι) := by unfold kapI; positivity
    apply le_of_eq; ring

/-- The exact kernel on the near side under the envelope, `m ≥ 3`: `𝔅_m(t)² ≤ (1 + k_f/c)²κ_ι env_n(t)·P`. -/
theorem frakB_sq_le_near (a : ι → ℝ) {M m : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hm : 3 ≤ m) (hmM : m ≤ M) {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) 2) :
    Cvs.L2a.CutKernels.frakB c χ g a m t ^ 2
      ≤ (1 + kFb c / c) ^ 2 * kapI c (Fintype.card ι) * envN m t * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have htm : t < m := by linarith [ht.2]
  have h2m : 2 / (m : ℝ) < 1 := by rw [div_lt_one hm0]; linarith
  have h := (t0_frakB a (K := kFb c) (S := √((t / m) ^ 2 + 1) / (1 - (t / m) ^ 2)) hg hg₁ hg₂c hang hc hχ0 hχc
    hχi hM (by omega) hmM (by linarith [ht.1]) (off_near hm0 htm) (fun η h1 h2 => by
      refine (Cvs.L2a.CutKernelSimplified.kCmp_le_near (y₀ := 2 / m) hc0 (by linarith)
        (div_pos (by linarith [ht.1]) hm0) (by rw [div_le_div_iff_of_pos_right hm0]; exact ht.2)
        h2m h1 h2).trans (le_trans ?_ (kNb_le_kFb hc0))
      have := Cvs.L2a.CutKernelSimplified.kNear_bot_le m hm (c := c) (by linarith)
      unfold kNb
      exact this)
    (fun v hv => env_near (div_pos (by linarith [ht.1]) hm0).le (by rw [div_lt_one hm0]; exact htm) hv.1)).1
  rw [envN, ← env_sq_div hm0 htm (by linarith [ht.1])]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- The exact kernel on the far side under the envelope: `𝔅_m(t)² ≤ (1 + k_f/c)²κ_ι env_f(t)·P`, `t > M`. -/
theorem frakB_sq_le_far (a : ι → ℝ) {M m : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hm : 2 ≤ m) (hmM : m + 1 ≤ M) {t : ℝ}
    (ht : (M : ℝ) < t) :
    Cvs.L2a.CutKernels.frakB c χ g a m t ^ 2
      ≤ (1 + kFb c / c) ^ 2 * kapI c (Fintype.card ι) * envF m t * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) < m := by linarith
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hY := one_le_Ymax hm1
  have hbm := Cvs.L2a.CornerSuprema.lt_bm hm1
  have hbmY : Cvs.L2a.CornerSuprema.bm m = m * Ymax m := by unfold Cvs.L2a.CornerSuprema.bm Ymax; ring
  have hgap := M_sub_b_ge_nat hm hmM
  have hYM : Ymax m < (M : ℝ) / m := by
    rw [lt_div_iff₀ hm0]; have := gZero_pos; linarith
  have hyM : (M : ℝ) / m ≤ t / m := by gcongr
  have h := (t0_frakB a (K := kFb c) (S := √((t / m) ^ 2 + Ymax m ^ 2) / ((t / m) ^ 2 - Ymax m ^ 2))
    hg hg₁ hg₂c hang hc hχ0 hχc hχi hM hm (by omega) (by linarith) (off_far hm1 (by
      have := gZero_pos; linarith))
    (fun η h1 h2 => by
      refine (Cvs.L2a.CutKernelSimplified.kCmp_le_far (y₁ := (M : ℝ) / m) hc0 hm1 hY h2 (le_of_eq ?_) hYM hyM).trans ?_
      · unfold Ymax
        rw [div_pow, Real.sq_sqrt (by nlinarith)]
        have : (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
        field_simp; ring
      · exact Cvs.L2a.CutKernelSimplified.kFar_bot_le M m hm (by omega) hc0)
    (fun v hv => env_far (by linarith [hv.1]) hv.2 (lt_of_lt_of_le hYM hyM))).1
  have e : (√((t / m) ^ 2 + Ymax m ^ 2) / ((t / m) ^ 2 - Ymax m ^ 2)) ^ 2 / (m ^ 2 * (m ^ 2 - 1)) = envF m t := by
    unfold envF
    rw [hbmY, div_pow, Real.sq_sqrt (by positivity)]
    have h1 : (t / m) ^ 2 - Ymax m ^ 2 ≠ 0 := by
      have := lt_of_lt_of_le hYM hyM
      have : 0 < (t / m) ^ 2 - Ymax m ^ 2 := by nlinarith [hY]
      exact this.ne'
    have h2 : t ^ 2 - (m * Ymax m) ^ 2 ≠ 0 := by
      have : t ^ 2 - (m * Ymax m) ^ 2 = m ^ 2 * ((t / m) ^ 2 - Ymax m ^ 2) := by field_simp
      rw [this]; exact mul_ne_zero (by positivity) h1
    have h3 : (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
  rw [← e]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- `√a√x + √b√y ≤ √(a + b)√(x + y)` for nonnegative reals. -/
theorem sqrt_cs_two {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √a * √x + √b * √y ≤ √(a + b) * √(x + y) := by
  rw [← Real.sqrt_mul (add_nonneg ha hb)]
  refine Real.le_sqrt_of_sq_le ?_
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sq_sqrt hx
  have h4 := Real.sq_sqrt hy
  nlinarith [sq_nonneg (√a * √y - √b * √x), Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg x,
    Real.sqrt_nonneg y]

/-- **The count-envelope tail at one cut**: for `3 ≤ m ≤ M − 1`, with the exact kernel,
`|∫_{(1,2]} wΦ𝔅_m| + |∫_{(M,∞)} Φ𝔅_m| ≤ √P_A·(1 + k_f/c)√(κ_ι(𝔑_m + 𝔉_m(M))/(m² − 1))·√P`. -/
theorem tail_range (a : ι → ℝ) {M m : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hm : 3 ≤ m) (hmM : m + 1 ≤ M) :
    |∫ t in Ioc 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t|
        + |∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t|
      ≤ √((∫ t in Ioc 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2)
            + ∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) ^ 2)
        * √((1 + kFb c / c) ^ 2 * kapI c (Fintype.card ι) * ((Cvs.L2a.CornerSuprema.nearN m
            + Cvs.L2a.CornerSuprema.farF m M) / ((m : ℝ) ^ 2 - 1)) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) < m := by linarith
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hgap := M_sub_b_ge_nat (by omega : 2 ≤ m) hmM
  have hbM' : Cvs.L2a.CornerSuprema.bm m < M := by linarith [gZero_pos]
  have hΦ := integrableOn_Phi_sq a hg hg₁ hg₂c hang hc0
  have hΦc : Continuous fun t => ∑ i, a i * psi c (g i) t := continuous_Phi a hg hg₁ hg₂c hang
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  set L := (1 + kFb c / c) ^ 2 * kapI c (Fintype.card ι) with hL
  have hL0 : 0 ≤ L := by rw [hL]; unfold kapI; positivity
  have hw : ∀ t, 0 ≤ 1 - wF t ∧ 1 - wF t ≤ 1 := fun t => by
    have := Cvs.L2a.FarFarBound.wF_bounds t; constructor <;> linarith
  have hwc : ContinuousOn (fun t => 1 - wF t) (Icc 1 2) := (continuous_const.sub continuous_wF.1).continuousOn
  have hn := fun t (ht : t ∈ Icc (1 : ℝ) 2) =>
    frakB_sq_le_near a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM hm (by omega) ht
  have hf := fun t (ht : t ∈ Ioi (M : ℝ)) =>
    frakB_sq_le_far a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM (by omega) hmM (t := t) ht
  have hIcc : ∀ t ∈ Ioc (1 : ℝ) 2, t ∈ Icc (1 : ℝ) 2 := fun t ht => ⟨ht.1.le, ht.2⟩
  have hqn : ContinuousOn (fun t => (1 - wF t) * (L * envN m t * P)) (Icc 1 2) :=
    hwc.mul ((continuousOn_const.mul (continuousOn_envN (by linarith))).mul continuousOn_const)
  have kn := abs_integral_le_sqrt
    (h := fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t)
    (p := fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2)
    (q₂ := fun _ => 0) measurableSet_Ioc
    (((hwc.mul (hΦc.pow 2).continuousOn).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    (hqn.integrableOn_Icc.mono_set Ioc_subset_Icc_self) integrableOn_zero
    (fun t _ => mul_nonneg (hw t).1 (sq_nonneg _))
    (fun t ht => (mul_nonneg (hw t).1 (sq_nonneg _)).trans (mul_le_mul_of_nonneg_left (hn t (hIcc t ht)) (hw t).1))
    (fun _ _ => le_rfl)
    (fun t ht => by
      have := abs_wPhi_frakB_le (w := 1 - wF t) (Φ := ∑ i, a i * psi c (g i) t)
        (F := Cvs.L2a.CutKernels.frakB c χ g a m t) (S := Cvs.L2a.CutKernels.frakB c χ g a m t) (C := 0)
        (q₁ := (1 - wF t) * (L * envN m t * P)) (q₂ := 0) (hw t).1 (by ring)
        (mul_le_mul_of_nonneg_left (hn t (hIcc t ht)) (hw t).1) (by simp)
      simpa using this)
  have kf := abs_integral_le_sqrt
    (h := fun t => (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t)
    (p := fun t => (∑ i, a i * psi c (g i) t) ^ 2) (q₂ := fun _ => 0) measurableSet_Ioi
    (hΦ.2.mono_set (Ioi_subset_Ioi (by linarith)))
    (((integrableOn_envF hm1 hbM').const_mul L).mul_const P) integrableOn_zero
    (fun t _ => sq_nonneg _) (fun t ht => (sq_nonneg _).trans (hf t ht)) (fun _ _ => le_rfl)
    (fun t ht => by
      have := abs_wPhi_frakB_le (w := 1) (Φ := ∑ i, a i * psi c (g i) t)
        (F := Cvs.L2a.CutKernels.frakB c χ g a m t) (S := Cvs.L2a.CutKernels.frakB c χ g a m t) (C := 0)
        (q₁ := L * envF m t * P) (q₂ := 0) zero_le_one (by ring) (by rw [one_mul]; exact hf t ht) (by simp)
      simpa using this)
  simp only [integral_zero, Real.sqrt_zero, add_zero] at kn kf
  have In : ∫ t in Ioc 1 2, (1 - wF t) * (L * envN m t * P)
      ≤ L * (Cvs.L2a.CornerSuprema.nearN m / (m ^ 2 - 1)) * P := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    have e : (fun t => (1 - wF t) * (L * envN m t * P)) = fun t => (L * P) * ((1 - wF t) * envN m t) :=
      funext fun t => by ring
    rw [e, intervalIntegral.integral_const_mul]
    have := integral_envN_le (m := m) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hL0 hP0)]
  have If : ∫ t in Ioi (M : ℝ), L * envF m t * P = L * (Cvs.L2a.CornerSuprema.farF m M / (m ^ 2 - 1)) * P := by
    rw [integral_mul_const, integral_const_mul, integral_envF hm1 hbM']
  have hm21 : (0 : ℝ) < m ^ 2 - 1 := by nlinarith
  have hN0 : 0 ≤ Cvs.L2a.CornerSuprema.nearN m := Cvs.L2a.CornerSuprema.nearN_nonneg hm3
  have hF0 : 0 ≤ Cvs.L2a.CornerSuprema.farF m M := Cvs.L2a.CornerSuprema.farF_nonneg (by linarith) hMr
  refine (add_le_add (kn.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt In) (Real.sqrt_nonneg _)))
    (kf.trans (le_of_eq (by rw [If])))).trans ?_
  refine (sqrt_cs_two (setIntegral_nonneg measurableSet_Ioc fun t _ => mul_nonneg (hw t).1 (sq_nonneg _))
    (setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _) (by positivity) (by positivity)).trans
    (le_of_eq ?_)
  congr 1
  congr 1
  ring

/-- The strip factor `𝒮_b = 2πs√(πJs/c)(8/(4 − s) + 2s/(2 − s))`. -/
def stripB (c s J : ℝ) : ℝ := 2 * π * s * √(π * J * s / c) * (8 / (4 - s) + 2 * s / (2 - s))

/-- **The `m = 2` strip**: `2|∫_{(2−s,2]} wΦ𝔅₂| ≤ 𝒮_b·P` for `0 < s ≤ 1`. -/
theorem strip_m2 (a : ι → ℝ) {M : ℕ} {s : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hM2 : 2 ≤ M) (hs : 0 < s) (hs1 : s ≤ 1) :
    2 * |∫ t in Ioc (2 - s) 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t|
      ≤ stripB c s (Fintype.card ι) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hΦ := integrableOn_Phi_sq a hg hg₁ hg₂c hang hc0
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  set J := (Fintype.card ι : ℝ) with hJ
  set K := 8 / (4 - s) + 2 * s / (2 - s) with hK
  have hK0 : 0 ≤ K := by
    have : 0 < 4 - s := by linarith
    have : 0 < 2 - s := by linarith
    positivity
  set q := π * J / c * K ^ 2 * P with hq
  have hq0 : 0 ≤ q := by positivity
  have hw : ∀ t, 0 ≤ 1 - wF t ∧ 1 - wF t ≤ 1 := fun t => by
    have := Cvs.L2a.FarFarBound.wF_bounds t; constructor <;> linarith
  have hsub : Ioc (2 - s) 2 ⊆ Ioi 1 := fun t ht => show 1 < t by linarith [ht.1]
  -- the weight on the strip
  have hws : ∀ t ∈ Ioc (2 - s) 2, 1 - wF t ≤ π ^ 2 * s ^ 2 := fun t ht => by
    refine (Cvs.L2a.RampTopQuadratic.one_sub_wF_le t).trans ?_
    have h1 : 0 ≤ 2 - t := by linarith [ht.2]
    have h2 : 2 - t ≤ s := by linarith [ht.1]
    gcongr
  -- the pointwise kernel bound
  have hk : ∀ t ∈ Ioc (2 - s) 2, (1 - wF t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t ^ 2 ≤ q := fun t ht => by
    have ht0 : 0 < t := by linarith [ht.1]
    rcases eq_or_lt_of_le ht.2 with h2 | h2
    · rw [h2, (wF_of_two_le le_rfl).1, sub_self, zero_mul]; exact hq0
    have hb := t0_strip a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM hM2 ht0 h2
    have hu : 0 < 2 - t := by linarith
    have hwu := Cvs.L2a.RampTopQuadratic.one_sub_wF_le t
    have e : (2 - t) * (8 / (4 - t ^ 2) + 2 / t) = 8 / (2 + t) + 2 * (2 - t) / t := by
      have : 4 - t ^ 2 = (2 - t) * (2 + t) := by ring
      rw [this]; field_simp
    have hle : 8 / (2 + t) + 2 * (2 - t) / t ≤ K := by
      rw [hK]
      have h3 : 4 - s ≤ 2 + t := by linarith [ht.1]
      have : 8 / (2 + t) ≤ 8 / (4 - s) := div_le_div_of_nonneg_left (by norm_num) (by linarith) h3
      have : 2 * (2 - t) / t ≤ 2 * s / (2 - s) := by
        rw [div_le_div_iff₀ ht0 (by linarith)]
        nlinarith [ht.1]
      linarith
    have h0 : 0 ≤ 8 / (2 + t) + 2 * (2 - t) / t := by positivity
    calc (1 - wF t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t ^ 2
        ≤ π ^ 2 * (2 - t) ^ 2 * (J / (π * c) * (8 / (4 - t ^ 2) + 2 / t) ^ 2 * P) :=
          mul_le_mul hwu hb (sq_nonneg _) (by positivity)
      _ = π * J / c * ((2 - t) * (8 / (4 - t ^ 2) + 2 / t)) ^ 2 * P := by field_simp
      _ ≤ q := by
          rw [e, hq]
          gcongr
  have hS : MeasurableSet (Ioc (2 - s) 2) := measurableSet_Ioc
  have key := abs_integral_le_sqrt
    (h := fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t)
    (p := fun t => π ^ 2 * s ^ 2 * (∑ i, a i * psi c (g i) t) ^ 2) (q₁ := fun _ => q) (q₂ := fun _ => 0) hS
    ((hΦ.2.mono_set hsub).const_mul _) (integrableOn_const (by simp)) integrableOn_zero
    (fun t _ => by positivity) (fun _ _ => hq0) (fun _ _ => le_rfl)
    (fun t ht => by
      have hwt := hw t
      have e1 : √(π ^ 2 * s ^ 2 * (∑ i, a i * psi c (g i) t) ^ 2) = π * s * |∑ i, a i * psi c (g i) t| := by
        rw [show π ^ 2 * s ^ 2 * (∑ i, a i * psi c (g i) t) ^ 2 = (π * s * |∑ i, a i * psi c (g i) t|) ^ 2 by
          rw [mul_pow, mul_pow, sq_abs], Real.sqrt_sq (by positivity)]
      have e2 : √(1 - wF t) ≤ π * s := by
        rw [show π * s = √((π * s) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
        exact Real.sqrt_le_sqrt (by rw [mul_pow]; exact hws t ht)
      have e3 : √(1 - wF t) * |Cvs.L2a.CutKernels.frakB c χ g a 2 t| ≤ √q := by
        rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hwt.1]; exact Real.sqrt_le_sqrt (hk t ht)
      simp only [Real.sqrt_zero, add_zero]
      rw [e1, abs_mul, abs_mul, abs_of_nonneg hwt.1]
      have hs1 := Real.mul_self_sqrt hwt.1
      calc (1 - wF t) * |∑ i, a i * psi c (g i) t| * |Cvs.L2a.CutKernels.frakB c χ g a 2 t|
          = √(1 - wF t) * |∑ i, a i * psi c (g i) t| * (√(1 - wF t) * |Cvs.L2a.CutKernels.frakB c χ g a 2 t|) := by
            conv_lhs => rw [← hs1]
            ring
        _ ≤ π * s * |∑ i, a i * psi c (g i) t| * √q := by
            gcongr
      )
  simp only [integral_zero, Real.sqrt_zero, add_zero, integral_const, smul_eq_mul] at key
  rw [integral_const_mul] at key
  have hp : ∫ t in Ioc (2 - s) 2, (∑ i, a i * psi c (g i) t) ^ 2 ≤ P :=
    setIntegral_mono_set hΦ.2 (ae_of_all _ fun _ => sq_nonneg _) (LE.le.eventuallySubset hsub)
  have hvol : (volume.restrict (Ioc (2 - s) 2) Set.univ).toReal = s := by
    simp [Real.volume_Ioc, hs.le]
  rw [measureReal_def, hvol] at key
  calc 2 * |∫ t in Ioc (2 - s) 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t|
      ≤ 2 * (√(π ^ 2 * s ^ 2 * ∫ t in Ioc (2 - s) 2, (∑ i, a i * psi c (g i) t) ^ 2) * √(s * q)) := by gcongr
    _ ≤ 2 * (√(π ^ 2 * s ^ 2 * P) * √(s * q)) := by gcongr
    _ = stripB c s J * P := by
        rw [← Real.sqrt_mul (by positivity), show π ^ 2 * s ^ 2 * P * (s * q) = (π * s * K * P) ^ 2 * (π * J * s / c) by
          rw [hq]; ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), stripB, ← hK]
        ring

end nearside

/-! ### The `m = 2` shells and the bottom budget -/

/-- The far collar `δ_m = min(δ, g₀/(2m))`. -/
def deltaM (δ m : ℝ) : ℝ := min δ (gZero / (2 * m))

/-- The shell ends `e_k = min(1, s·2^k)`. -/
def eSh (s : ℝ) (k : ℕ) : ℝ := min 1 (s * 2 ^ k)

/-- The shell collars `δ_k = min(δ, e_k/4)`. -/
def dSh (δ s : ℝ) (k : ℕ) : ℝ := min δ (eSh s k / 4)

/-- The number of shells `⌈log₂(1/s)⌉`. -/
def nSh (s : ℝ) : ℕ := ⌈Real.logb 2 (1 / s)⌉₊

/-- The weighted shell mass `∫_{2−e_{k+1}}^{2−e_k} 4(1 − wF)/(2 − t)²`. -/
def iSh (s : ℝ) (k : ℕ) : ℝ := ∫ t in (2 - eSh s (k + 1))..(2 - eSh s k), 4 * (1 - wF t) / (2 - t) ^ 2

/-- The `m = 2` near main factor: `L_near(2) + |g₂(2 − s)|/(π²c) + Σ_k (4κ_S/π²)δ_k·I_k`. -/
def lam2 (c δ s : ℝ) : ℝ :=
  Cvs.L2a.CornerSuprema.Lnear 2 + |gT 2 (2 - s)| / (π ^ 2 * c)
    + ∑ k ∈ Finset.range (nSh s), 4 * (181 / 462) / π ^ 2 * dSh δ s k * iSh s k

/-- The `m = 2` near chirp factor `Σ_k (2/π)T(c, 2, d, δ_k, e_k/4)·I_k`. -/
def e2 (c d δ s J : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (nSh s), 2 / π * tT c 2 d (dSh δ s k) (eSh s k / 4) J * iSh s k

/-- The `m = 2` near correction factor `(κ_ι/c²)∫₁^{2−s}(1 − wF)K_near(t)²·env_n(t)`. -/
def k2 (c s J : ℝ) : ℝ :=
  kapI c J / c ^ 2 * ∫ t in (1 : ℝ)..(2 - s),
    (1 - wF t) * Cvs.L2a.CutKernelSimplified.kNear c 2 (t / 2) (Ymax 2) ^ 2 * envN 2 t

/-- **The `m = 2` shells (target)**: `|∫_{(1,2−s]} wΦ𝔅₂| ≤ √(∫_{(1,2−s]} wΦ²)(√(Λⁿ₂W₂ + Eⁿ₂P) + √(Kⁿ₂P))`. -/
def ShellM2 {ι : Type} [Fintype ι] (c d δ s : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) : Prop :=
  |∫ t in Ioc 1 (2 - s), (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t|
    ≤ √(∫ t in Ioc 1 (2 - s), (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2)
      * (√(lam2 c δ s * (∫ x in (2 - d)..(2 + d), (∑ i, a i * psi c (g i) x) ^ 2)
            + e2 c d δ s (Fintype.card ι) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
        + √(k2 c s (Fintype.card ι) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2))

/-- The per-cut main factor `Λ_m`: near (`m = 2` shells or `m ≥ 3`) plus far. -/
def lamT (c δ s m M : ℝ) : ℝ := (if m = 2 then lam2 c δ s else lamN c δ m) + lamF c (deltaM δ m) m M

/-- The per-cut chirp factor `E_m`. -/
def eT (c d δ s m M J : ℝ) : ℝ := (if m = 2 then e2 c d δ s J else eN c d δ m J) + eFar c d (deltaM δ m) m M J

/-- The per-cut correction factor `K_m`. -/
def kT (c s m M J : ℝ) : ℝ := (if m = 2 then k2 c s J else kN c J m) + kF c J m M

/-- **The bottom budget** `ℬ = (1 + π²d²)√(Σ_{m<K}Λ_m) + 2Σ_{m<K}(√E_m + √K_m) + 𝒮_b + [M > X_b](1 + k_f/c)T̄_bot(X_b)`,
`K = min(M, X_b)`. -/
def calB (c d δ s : ℝ) (Xb M : ℕ) (J : ℝ) : ℝ :=
  (1 + π ^ 2 * d ^ 2) * √(∑ m ∈ Finset.Ico 2 (min M Xb), lamT c δ s m M)
    + 2 * ∑ m ∈ Finset.Ico 2 (min M Xb), (√(eT c d δ s m M J) + √(kT c s m M J))
    + stripB c s J + (if Xb < M then (1 + kFb c / c) * Cvs.L2a.CornerSuprema.Tbar (kapI c J) Xb else 0)

/-! ### Nonnegativity and the per-cut combination -/

theorem deltaM_pos {δ m : ℝ} (hδ : 0 < δ) (hm : 0 < m) : 0 < deltaM δ m :=
  lt_min hδ (div_pos gZero_pos (by positivity))

theorem bP_deltaM_lt (δ : ℝ) {m M : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) :
    bP m (deltaM δ m) < M := by
  have hm0 : (0 : ℝ) < m := by have : (2 : ℝ) ≤ m := by exact_mod_cast hm
                               linarith
  have hg := M_sub_b_ge_nat hm hmM
  have hle : (m : ℝ) * deltaM δ m ≤ gZero / 2 := by
    have := min_le_right δ (gZero / (2 * m))
    calc (m : ℝ) * deltaM δ m ≤ m * (gZero / (2 * m)) := mul_le_mul_of_nonneg_left this hm0.le
      _ = gZero / 2 := by field_simp
  have hb : Cvs.L2a.CornerSuprema.bm m = m * Ymax m := by unfold Cvs.L2a.CornerSuprema.bm Ymax; ring
  have := gZero_pos
  unfold bP
  nlinarith

theorem collF_nonneg {β M : ℝ} (hβ : 0 < β) (hM : β < M) : 0 ≤ collF β M := by
  unfold collF
  have h1 : 0 < M ^ 2 - β ^ 2 := by nlinarith
  have h2 : 0 ≤ Real.log ((M + β) / (M - β)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have : 0 < M := by linarith
  positivity

theorem lamN_nonneg {c δ m : ℝ} (hm : 3 ≤ m) (hδ : 0 ≤ δ) (hc : 0 < c) : 0 ≤ lamN c δ m := by
  unfold lamN
  have := Cvs.L2a.CornerSuprema.Lnear_nonneg (by linarith : (2 : ℝ) ≤ m)
  positivity

theorem lamF_nonneg {c δ : ℝ} {m M : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) (hδ : 0 < δ) (hc : 0 < c) :
    0 ≤ lamF c (deltaM δ m) m M := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hδm := deltaM_pos hδ (by linarith : (0 : ℝ) < m)
  have hbM := bP_deltaM_lt δ hm hmM
  have hbb := bm_le_bP (m := m) (by linarith) hδm.le
  have hb0 : 0 < bP m (deltaM δ m) := lt_of_lt_of_le (by linarith [Cvs.L2a.CornerSuprema.lt_bm (by linarith :
    (1 : ℝ) < m)]) hbb
  unfold lamF
  have h1 := Cvs.L2a.CornerSuprema.Lfar_nonneg hm2 hMr
  have h2 := ((gT_far (by linarith : (1 : ℝ) < m)).1 M (lt_of_le_of_lt hbb hbM)).1
  have h3 := collF_nonneg hb0 hbM
  positivity

theorem lam2_nonneg {c δ s : ℝ} (hδ : 0 ≤ δ) (hs : 0 ≤ s) (hc : 0 < c) : 0 ≤ lam2 c δ s := by
  unfold lam2
  have h1 := Cvs.L2a.CornerSuprema.Lnear_nonneg (le_refl (2 : ℝ))
  have h2 : ∀ k ∈ Finset.range (nSh s), 0 ≤ 4 * (181 / 462) / π ^ 2 * dSh δ s k * iSh s k := fun k _ => by
    have hd : 0 ≤ dSh δ s k := le_min hδ (by unfold eSh; positivity)
    have hi : 0 ≤ iSh s k := by
      unfold iSh
      refine intervalIntegral.integral_nonneg ?_ fun t _ => ?_
      · have : eSh s k ≤ eSh s (k + 1) := by
          unfold eSh
          refine min_le_min le_rfl (mul_le_mul_of_nonneg_left ?_ hs)
          exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
        linarith
      · have := Cvs.L2a.FarFarBound.wF_bounds t
        have : 0 ≤ 1 - wF t := by linarith
        positivity
    positivity
  have := Finset.sum_nonneg h2
  positivity

theorem e2_nonneg {c d δ s J : ℝ} (hc : 0 < c) (hd : 0 < d) (hd1 : d < 1) (hδ : 0 < δ) (hs : 0 < s) (hJ : 0 ≤ J) :
    0 ≤ e2 c d δ s J := by
  unfold e2
  refine Finset.sum_nonneg fun k _ => ?_
  have he : 0 < eSh s k := lt_min one_pos (by positivity)
  have hd' : 0 ≤ dSh δ s k := le_min hδ.le (by positivity)
  have hT := tT_nonneg (c := c) (x₀ := 2) (d := d) (δ := dSh δ s k) (r := eSh s k / 4) (J := J) hc hd.le
    (by linarith) hd' hJ (by positivity)
  have hi : 0 ≤ iSh s k := by
    unfold iSh
    refine intervalIntegral.integral_nonneg ?_ fun t _ => ?_
    · have : eSh s k ≤ eSh s (k + 1) := by
        unfold eSh
        refine min_le_min le_rfl (mul_le_mul_of_nonneg_left ?_ hs.le)
        exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
      linarith
    · have := Cvs.L2a.FarFarBound.wF_bounds t
      have : 0 ≤ 1 - wF t := by linarith
      positivity
  positivity

theorem k2_nonneg {c s J : ℝ} (hc : 0 < c) (hs1 : s ≤ 1) (hJ : 0 ≤ J) : 0 ≤ k2 c s J := by
  unfold k2 kapI
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by linarith) fun t ht => ?_)
  have := Cvs.L2a.FarFarBound.wF_bounds t
  have h1 : 0 ≤ 1 - wF t := by linarith
  have h2 : 0 ≤ envN 2 t := by unfold envN; norm_num; positivity
  positivity

theorem eN_nonneg {c d δ m J : ℝ} (hc : 0 < c) (hd : 0 < d) (hxd : 1 < m - d) (hδ : 0 ≤ δ) (hJ : 0 ≤ J)
    (ha : 2 < m * (1 - δ)) : 0 ≤ eN c d δ m J := by
  have hm0 : 0 < m := by nlinarith
  have hT := tT_nonneg (J := J) (c := c) (x₀ := m) (d := d) (δ := δ) (r := (m * (1 - δ) - 2) / m) hc hd.le hxd hδ
    hJ (div_pos (by linarith) hm0)
  unfold eN
  have : 0 ≤ 1 / (m * (1 - δ) - 2) - 1 / (m * (1 - δ) - 1) := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  positivity

theorem eFar_nonneg {c d δ J : ℝ} {m M : ℕ} (hc : 0 < c) (hd : 0 < d) (hxd : 1 < (m : ℝ) - d) (hδ : 0 < δ)
    (hJ : 0 ≤ J) (hm : 2 ≤ m) (hmM : m + 1 ≤ M) : 0 ≤ eFar c d (deltaM δ m) m M J := by
  have hm0 : (0 : ℝ) < m := by have : (2 : ℝ) ≤ m := by exact_mod_cast hm
                               linarith
  have hbM := bP_deltaM_lt δ hm hmM
  have hT := tT_nonneg (J := J) (c := c) (x₀ := m) (d := d) (δ := deltaM δ m) (r := (M - bP m (deltaM δ m)) / m)
    hc hd.le hxd (deltaM_pos hδ hm0).le hJ (div_pos (by linarith) hm0)
  unfold eFar
  have : 0 < (M : ℝ) - bP m (deltaM δ m) := by linarith
  positivity

theorem kN_nonneg {c J m : ℝ} (hc : 0 < c) (hJ : 0 ≤ J) (hm : 3 ≤ m) : 0 ≤ kN c J m := by
  unfold kN kapI
  have := Cvs.L2a.CornerSuprema.nearN_nonneg hm
  have : 0 < m ^ 2 - 1 := by nlinarith
  positivity

theorem kF_nonneg {c J m M : ℝ} (hc : 0 < c) (hJ : 0 ≤ J) (hm : 2 ≤ m) (hmM : m + 1 ≤ M) : 0 ≤ kF c J m M := by
  unfold kF kapI
  have := Cvs.L2a.CornerSuprema.farF_nonneg hm hmM
  have : 0 < m ^ 2 - 1 := by nlinarith
  positivity

/-- **The per-cut combination** of the near and far bounds. -/
theorem comb_two {pn pf Λn Λf En Ef Kn Kf W P In If : ℝ} (hpn : 0 ≤ pn) (hpf : 0 ≤ pf) (hΛn : 0 ≤ Λn)
    (hΛf : 0 ≤ Λf) (hEn : 0 ≤ En) (hEf : 0 ≤ Ef) (hKn : 0 ≤ Kn) (hKf : 0 ≤ Kf) (hW : 0 ≤ W) (hP : 0 ≤ P)
    (hn : |In| ≤ √pn * (√(Λn * W + En * P) + √(Kn * P)))
    (hf : |If| ≤ √pf * (√(Λf * W + Ef * P) + √(Kf * P))) :
    |In| + |If| ≤ √(pn + pf) * (√(Λn + Λf) * √W + (√(En + Ef) + √(Kn + Kf)) * √P) := by
  have h1 := sqrt_cs_two hpn hpf (by positivity : 0 ≤ Λn * W + En * P) (by positivity : 0 ≤ Λf * W + Ef * P)
  have h2 := sqrt_cs_two hpn hpf (by positivity : 0 ≤ Kn * P) (by positivity : 0 ≤ Kf * P)
  have e1 : Λn * W + En * P + (Λf * W + Ef * P) = (Λn + Λf) * W + (En + Ef) * P := by ring
  have e2 : Kn * P + Kf * P = (Kn + Kf) * P := by ring
  rw [e1] at h1
  rw [e2] at h2
  have h3 := Cvs.L2a.CornerSuprema.sqrt_add_le_add (by positivity : 0 ≤ (Λn + Λf) * W)
    (by positivity : 0 ≤ (En + Ef) * P)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)] at h3
  rw [Real.sqrt_mul (show 0 ≤ Kn + Kf by positivity) P] at h2
  have hs := Real.sqrt_nonneg (pn + pf)
  have h4 := mul_le_mul_of_nonneg_left h3 hs
  rw [mul_add] at hn hf
  calc |In| + |If| ≤ (√pn * √(Λn * W + En * P) + √pf * √(Λf * W + Ef * P))
        + (√pn * √(Kn * P) + √pf * √(Kf * P)) := by linarith
    _ ≤ √(pn + pf) * √((Λn + Λf) * W + (En + Ef) * P) + √(pn + pf) * (√(Kn + Kf) * √P) := add_le_add h1 h2
    _ ≤ √(pn + pf) * (√(Λn + Λf) * √W + √(En + Ef) * √P) + √(pn + pf) * (√(Kn + Kf) * √P) := by linarith
    _ = _ := by ring

/-! ### Assembly -/

section assembly

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

theorem memLp_frakB (a : ι → ℝ) {m : ℕ} (hm : 2 ≤ m) (hc : 0 < c) :
    MemLp (Cvs.L2a.CutKernels.frakB c χ g a m) 2 (volume.restrict (Ioi 1)) := by
  have hm0 : (1 : ℝ) < m := by have : (2 : ℝ) ≤ m := by exact_mod_cast hm
                               linarith
  exact (Cvs.L2a.CutKernels.memLp_cutSample_div χ g a hm0 hc (by linarith)).const_mul _

/-- The ū-split with the near range half-open: `∫_{(1,∞)} ū𝔅_m = ∫_{(1,2]} wΦ𝔅_m + ∫_{(M,∞)} Φ𝔅_m`. -/
theorem integral_ubar_split (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) {M m : ℕ} (hM : 2 ≤ M) (hm : 2 ≤ m) :
    ∫ t in Ioi 1, Cvs.L2a.CleanBandDilation.ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t
        * Cvs.L2a.CutKernels.frakB c χ g a m t
      = (∫ t in Ioc 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t)
        + ∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t := by
  rw [Cvs.L2a.CutKernels.integral_ubar_mul (integrableOn_Phi_sq a hg hg₁ hg₂c hang hc).1
    (memLp_frakB a hm hc) (by exact_mod_cast hM), integral_Ioc_eq_integral_Ioo]

theorem integrableOn_wPhiF (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) {m : ℕ} (hm : 2 ≤ m) :
    IntegrableOn (fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a m t)
      (Ioi 1) := by
  have hΦ := (integrableOn_Phi_sq a hg hg₁ hg₂c hang hc).1
  have hw : MemLp (fun x => (1 - wF x) * ∑ i, a i * psi c (g i) x) 2 (volume.restrict (Ioi 1)) :=
    hΦ.of_le ((continuous_const.sub continuous_wF.1).aestronglyMeasurable.mul hΦ.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        obtain ⟨h0, h1, -, -⟩ := Cvs.L2a.FarFarBound.wF_bounds x
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith))
  exact hw.integrable_mul (memLp_frakB a hm hc)

/-- The near and far mass `P_A = ∫_{(1,2]} wΦ² + ∫_{(M,∞)} Φ²`. -/
def massA (c : ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M : ℕ) : ℝ :=
  (∫ t in Ioc 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2) + ∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) ^ 2

/-- **One cut, `3 ≤ m < M`**: `|∫ū𝔅_m| ≤ √P_A(√Λ_m√W_m + (√E_m + √K_m)√P)`. -/
theorem cut_bound (a : ι → ℝ) {M m : ℕ} {d δ s : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hm : 3 ≤ m) (hmM : m + 1 ≤ M)
    (hd : 0 < d) (hd2 : d ≤ 1 / 2) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) :
    |∫ t in Ioi 1, Cvs.L2a.CleanBandDilation.ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t
        * Cvs.L2a.CutKernels.frakB c χ g a m t|
      ≤ √(massA c g a M) * (√(lamT c δ s m M) * √(∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + (√(eT c d δ s m M (Fintype.card ι)) + √(kT c s m M (Fintype.card ι)))
          * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)) := by
  have hc0 : 0 < c := by linarith
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm2' : (m : ℝ) ≠ 2 := by linarith
  have hxd : 1 < (m : ℝ) - d := by linarith
  have hδm := deltaM_pos hδ (by linarith : (0 : ℝ) < m)
  have hδm1 : deltaM δ m ≤ 1 := (min_le_left _ _).trans (by linarith)
  rw [integral_ubar_split a hg hg₁ hg₂c hang hc0 (by omega) (by omega)]
  have hn := near_range a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM hm (by omega) hd hxd hδ (by linarith)
    (by nlinarith)
  have hf := far_range a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM (by omega) hmM hd hxd hδm hδm1
    (bP_deltaM_lt δ (by omega) hmM)
  have hw : ∀ t, 0 ≤ 1 - wF t := fun t => by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hJ : (0 : ℝ) ≤ Fintype.card ι := by positivity
  have hcomb := comb_two (setIntegral_nonneg measurableSet_Ioc fun t _ => mul_nonneg (hw t) (sq_nonneg _))
    (setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _) (lamN_nonneg hm3 hδ.le hc0)
    (lamF_nonneg (by omega) hmM hδ hc0)
    (eN_nonneg hc0 hd hxd hδ.le hJ (by nlinarith)) (eFar_nonneg hc0 hd hxd hδ hJ (by omega) hmM)
    (kN_nonneg hc0 hJ hm3) (kF_nonneg hc0 hJ (by linarith) (by exact_mod_cast hmM))
    (intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _)
    (setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _) hn hf
  refine (abs_add_le _ _).trans (hcomb.trans (le_of_eq ?_))
  unfold massA lamT eT kT
  simp only [ite_eq_right hm2']

/-- **The cut `m = 2`**: the shells, the strip and the far side,
`|∫ū𝔅₂| ≤ √P_A(√Λ₂√W₂ + (√E₂ + √K₂)√P) + (𝒮_b/2)P`. -/
theorem cut_bound_two (a : ι → ℝ) {M : ℕ} {d δ s : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hM3 : 3 ≤ M)
    (hd : 0 < d) (hd2 : d ≤ 1 / 2) (hδ : 0 < δ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hshell : ShellM2 c d δ s χ g a) :
    |∫ t in Ioi 1, Cvs.L2a.CleanBandDilation.ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t
        * Cvs.L2a.CutKernels.frakB c χ g a 2 t|
      ≤ √(massA c g a M) * (√(lamT c δ s 2 M) * √(∫ x in (2 - d)..(2 + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + (√(eT c d δ s 2 M (Fintype.card ι)) + √(kT c s 2 M (Fintype.card ι)))
          * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2))
        + stripB c s (Fintype.card ι) / 2 * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hxd : 1 < (2 : ℝ) - d := by linarith
  have hδm := deltaM_pos hδ (by norm_num : (0 : ℝ) < 2)
  have hδm1 : deltaM δ 2 ≤ 1 := by
    refine (min_le_right _ _).trans ?_
    have := gZero_lt
    rw [div_le_one (by norm_num)]; linarith
  rw [integral_ubar_split a hg hg₁ hg₂c hang hc0 (by omega) le_rfl]
  have hint := (integrableOn_wPhiF a hg hg₁ hg₂c hang hc0 (m := 2) le_rfl (χ := χ)).mono_set
    (Ioc_subset_Ioi_self : Ioc (1 : ℝ) 2 ⊆ Ioi 1)
  have hsplit : ∫ t in Ioc 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t
      = (∫ t in Ioc 1 (2 - s), (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t)
        + ∫ t in Ioc (2 - s) 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hint.mono_set (Ioc_subset_Ioc_right (by linarith))) (hint.mono_set (Ioc_subset_Ioc_left (by linarith))),
      Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
  rw [hsplit]
  have hf := far_range a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM le_rfl (by omega) hd hxd hδm hδm1
    (bP_deltaM_lt δ le_rfl (by omega))
  have hstr := strip_m2 a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM (by omega) hs hs1
  have hw : ∀ t, 0 ≤ 1 - wF t := fun t => by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hJ : (0 : ℝ) ≤ Fintype.card ι := by positivity
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have nF : 0 ≤ lamF c (deltaM δ 2) 2 M := by
    have := lamF_nonneg (c := c) (δ := δ) (m := 2) (M := M) le_rfl (by omega) hδ hc0
    simpa using this
  have nEF : 0 ≤ eFar c d (deltaM δ 2) 2 M (Fintype.card ι) := by
    have := eFar_nonneg (c := c) (d := d) (δ := δ) (J := Fintype.card ι) (m := 2) (M := M) hc0 hd
      (by norm_num; linarith) hδ hJ le_rfl (by omega)
    simpa using this
  have hshell' := hshell
  unfold ShellM2 at hshell'
  have hcomb := comb_two (In := ∫ t in Ioc 1 (2 - s), (1 - wF t) * (∑ i, a i * psi c (g i) t)
      * Cvs.L2a.CutKernels.frakB c χ g a 2 t)
    (setIntegral_nonneg measurableSet_Ioc fun t _ => mul_nonneg (hw t) (sq_nonneg _))
    (setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _) (lam2_nonneg hδ.le hs.le hc0) nF
    (e2_nonneg hc0 hd (by linarith) hδ hs hJ) nEF
    (k2_nonneg hc0 hs1 hJ) (kF_nonneg (m := 2) (M := M) hc0 hJ (by norm_num) (by linarith))
    (intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _)
    (setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _) hshell' (by simpa using hf)
  have hpA : (∫ t in Ioc 1 (2 - s), (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2)
      + ∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) ^ 2 ≤ massA c g a M := by
    unfold massA
    have hc2 : Continuous fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2 :=
      (continuous_const.sub continuous_wF.1).mul ((continuous_Phi a hg hg₁ hg₂c hang).pow 2)
    have := setIntegral_mono_set (μ := volume) (s := Ioc 1 (2 - s)) (t := Ioc 1 2)
      (hc2.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (ae_of_all _ fun t => mul_nonneg (hw t) (sq_nonneg _)) (LE.le.eventuallySubset (Ioc_subset_Ioc_right (by linarith)))
    linarith
  have hX : 0 ≤ √(lamT c δ s 2 M) * √(∫ x in (2 - d)..(2 + d), (∑ i, a i * psi c (g i) x) ^ 2)
      + (√(eT c d δ s 2 M (Fintype.card ι)) + √(kT c s 2 M (Fintype.card ι)))
        * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by positivity
  have e : lam2 c δ s + lamF c (deltaM δ 2) 2 M = lamT c δ s 2 M ∧
      e2 c d δ s (Fintype.card ι) + eFar c d (deltaM δ 2) 2 M (Fintype.card ι) = eT c d δ s 2 M (Fintype.card ι) ∧
      k2 c s (Fintype.card ι) + kF c (Fintype.card ι) 2 M = kT c s 2 M (Fintype.card ι) := by
    unfold lamT eT kT; simp
  rw [e.1, e.2.1, e.2.2] at hcomb
  calc _ ≤ |∫ t in Ioc 1 (2 - s), (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t|
        + |∫ t in Ioc (2 - s) 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t|
        + |∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hpA) hX
        linarith

theorem massA_le (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) {M : ℕ} (hM : 2 ≤ M) :
    massA c g a M ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hΦ := (integrableOn_Phi_sq a hg hg₁ hg₂c hang hc).2
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  unfold massA
  have h1 : ∫ t in Ioc 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2
      ≤ ∫ t in Ioc 1 2, (∑ i, a i * psi c (g i) t) ^ 2 := by
    refine setIntegral_mono_on ?_ (hΦ.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t _ => ?_
    · have hc2 : Continuous fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2 :=
        (continuous_const.sub continuous_wF.1).mul ((continuous_Phi a hg hg₁ hg₂c hang).pow 2)
      exact hc2.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · have := Cvs.L2a.FarFarBound.wF_bounds t
      nlinarith [sq_nonneg (∑ i, a i * psi c (g i) t)]
  have h2 : (∫ t in Ioc 1 2, (∑ i, a i * psi c (g i) t) ^ 2) + ∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) ^ 2
      ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
    rw [← setIntegral_union (Set.disjoint_left.2 fun t h1 h2 => by
        have : (M : ℝ) < t := h2
        linarith [h1.2]) measurableSet_Ioi
      (hΦ.mono_set Ioc_subset_Ioi_self) (hΦ.mono_set (Ioi_subset_Ioi (by linarith)))]
    exact setIntegral_mono_set hΦ (ae_of_all _ fun _ => sq_nonneg _)
      (LE.le.eventuallySubset (union_subset Ioc_subset_Ioi_self (Ioi_subset_Ioi (by linarith))))
  linarith

/-- **LOC, bottom**: for `M ≥ 3`, `X_b ≥ 3`, `d ≤ 1/2`, `0 < δ < 1/3`, `0 < s ≤ 1` and the `m = 2` shells,
`2Σ_{m=2}^{M−1}|∫_{(1,∞)} ū𝔅_m| ≤ ℬ(c, M)·∫₁^∞Φ²`. -/
theorem Dbot_local (a : ι → ℝ) {M Xb : ℕ} {d δ s : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hM3 : 3 ≤ M) (hXb : 3 ≤ Xb)
    (hd : 0 < d) (hd2 : d ≤ 1 / 2) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hs : 0 < s) (hs1 : s ≤ 1)
    (hshell : ShellM2 c d δ s χ g a) :
    2 * ∑ m ∈ Finset.Icc 2 (M - 1), |∫ t in Ioi 1,
        Cvs.L2a.CleanBandDilation.ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * Cvs.L2a.CutKernels.frakB c χ g a m t|
      ≤ calB c d δ s Xb M (Fintype.card ι) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  set PA := massA c g a M with hPA
  set J := (Fintype.card ι : ℝ) with hJd
  have hJ : 0 ≤ J := by positivity
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have hw : ∀ t, 0 ≤ 1 - wF t := fun t => by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hPA0 : 0 ≤ PA := add_nonneg (setIntegral_nonneg measurableSet_Ioc fun t _ => mul_nonneg (hw t) (sq_nonneg _))
    (setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _)
  have hPAP : PA ≤ P := massA_le a hg hg₁ hg₂c hang hc0 (by omega)
  set K := min M Xb with hK
  have hK3 : 3 ≤ K := le_min hM3 hXb
  have hKM : K ≤ M := min_le_left _ _
  set F : ℕ → ℝ := fun m => |∫ t in Ioi 1,
    Cvs.L2a.CleanBandDilation.ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * Cvs.L2a.CutKernels.frakB c χ g a m t|
    with hF
  set W : ℕ → ℝ := fun m => ∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2 with hWd
  have hW0 : ∀ m, 0 ≤ W m := fun m => intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hIcc : Finset.Icc 2 (M - 1) = Finset.Ico 2 M := by ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, ← Finset.sum_Ico_consecutive _ (by omega : 2 ≤ K) hKM]
  -- the head
  set B : ℕ → ℝ := fun m => √(lamT c δ s m M) * √(W m) + (√(eT c d δ s m M J) + √(kT c s m M J)) * √P with hB
  have hhead : ∑ m ∈ Finset.Ico 2 K, F m ≤ √PA * ∑ m ∈ Finset.Ico 2 K, B m + stripB c s J / 2 * P := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < K), Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < K),
      mul_add]
    have h2 := cut_bound_two a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM hM3 hd hd2 hδ hs hs1 hshell
    have h3 : ∑ m ∈ Finset.Ico (2 + 1) K, F m ≤ ∑ m ∈ Finset.Ico (2 + 1) K, √PA * B m := by
      refine Finset.sum_le_sum fun m hm => ?_
      have hm' := Finset.mem_Ico.1 hm
      exact cut_bound a (s := s) hg hg₁ hg₂c hang hc hχ0 hχc hχi hM hm'.1 (by omega) hd hd2 hδ hδ3
    rw [← Finset.mul_sum] at h3
    have e2 : F 2 = |∫ t in Ioi 1, Cvs.L2a.CleanBandDilation.ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t
        * Cvs.L2a.CutKernels.frakB c χ g a 2 t| := rfl
    have eB : B 2 = √(lamT c δ s 2 M) * √(∫ x in (2 - d)..(2 + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + (√(eT c d δ s 2 M J) + √(kT c s 2 M J)) * √P := by simp only [hB, hWd]; norm_num
    rw [e2, eB]
    linarith
  -- the tail
  have htail : 2 * ∑ m ∈ Finset.Ico K M, F m
      ≤ (if Xb < M then (1 + kFb c / c) * Cvs.L2a.CornerSuprema.Tbar (kapI c J) Xb else 0) * P := by
    split_ifs with hXM
    · have hKX : K = Xb := min_eq_right hXM.le
      have hk0 : 0 ≤ kapI c J := by unfold kapI; positivity
      have hT := Cvs.L2a.CornerSuprema.Tbot_le hk0 Xb M hXb
      have hm : ∀ m ∈ Finset.Ico K M, F m ≤ √PA * ((1 + kFb c / c)
          * √(kapI c J * (Cvs.L2a.CornerSuprema.nearN m + Cvs.L2a.CornerSuprema.farF m M) / ((m : ℝ) ^ 2 - 1))
          * √P) := fun m hm => by
        have hm' := Finset.mem_Ico.1 hm
        have h := tail_range a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM (m := m) (by omega) (by omega)
        have hsplit := integral_ubar_split a hg hg₁ hg₂c hang hc0 (M := M) (m := m) (by omega) (by omega)
          (χ := χ)
        simp only [hF]
        rw [hsplit]
        refine (abs_add_le _ _).trans (h.trans (le_of_eq ?_))
        have hm1 : (0 : ℝ) < (m : ℝ) ^ 2 - 1 := by
          have : (3 : ℝ) ≤ m := by exact_mod_cast (show 3 ≤ m by omega)
          nlinarith
        have hNF : 0 ≤ Cvs.L2a.CornerSuprema.nearN m + Cvs.L2a.CornerSuprema.farF m M := by
          have : (3 : ℝ) ≤ m := by exact_mod_cast (show 3 ≤ m by omega)
          have hMm : (m : ℝ) + 1 ≤ M := by exact_mod_cast (show m + 1 ≤ M by omega)
          exact add_nonneg (Cvs.L2a.CornerSuprema.nearN_nonneg this)
            (Cvs.L2a.CornerSuprema.farF_nonneg (by linarith) hMm)
        rw [show (1 + kFb c / c) ^ 2 * kapI c J * ((Cvs.L2a.CornerSuprema.nearN m + Cvs.L2a.CornerSuprema.farF m M)
            / ((m : ℝ) ^ 2 - 1)) * P = (1 + kFb c / c) ^ 2 * (kapI c J * (Cvs.L2a.CornerSuprema.nearN m
              + Cvs.L2a.CornerSuprema.farF m M) / ((m : ℝ) ^ 2 - 1)) * P by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by unfold kFb; positivity)]
        rfl
      have hs := Finset.sum_le_sum hm
      rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, hKX] at hs
      have hPP : √PA * √P ≤ P := by
        calc √PA * √P ≤ √P * √P := by gcongr
          _ = P := Real.mul_self_sqrt hP0
      have hk1 : 0 ≤ 1 + kFb c / c := by unfold kFb; positivity
      have hS0 : 0 ≤ ∑ m ∈ Finset.Ico Xb M,
          √(kapI c J * (Cvs.L2a.CornerSuprema.nearN m + Cvs.L2a.CornerSuprema.farF m M) / ((m : ℝ) ^ 2 - 1)) :=
        Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
      calc 2 * ∑ m ∈ Finset.Ico K M, F m
          ≤ 2 * (√PA * ((1 + kFb c / c) * (∑ m ∈ Finset.Ico Xb M,
            √(kapI c J * (Cvs.L2a.CornerSuprema.nearN m + Cvs.L2a.CornerSuprema.farF m M) / ((m : ℝ) ^ 2 - 1)))
              * √P)) := by rw [hKX]; linarith
        _ = (1 + kFb c / c) * (2 * ∑ m ∈ Finset.Ico Xb M,
            √(kapI c J * (Cvs.L2a.CornerSuprema.nearN m + Cvs.L2a.CornerSuprema.farF m M) / ((m : ℝ) ^ 2 - 1)))
              * (√PA * √P) := by ring
        _ ≤ (1 + kFb c / c) * Cvs.L2a.CornerSuprema.Tbar (kapI c J) Xb * P := by
            have hTb : 0 ≤ Cvs.L2a.CornerSuprema.Tbar (kapI c J) Xb :=
              Cvs.L2a.CornerSuprema.Tbar_nonneg (by exact_mod_cast hXb)
            have h1 := mul_le_mul_of_nonneg_left hT hk1
            calc _ ≤ (1 + kFb c / c) * Cvs.L2a.CornerSuprema.Tbar (kapI c J) Xb * (√PA * √P) :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
              _ ≤ _ := mul_le_mul_of_nonneg_left hPP (by positivity)
    · have hKM' : K = M := min_eq_left (not_lt.1 hXM)
      rw [hKM', Finset.Ico_self, Finset.sum_empty]; simp
  -- the windows and the final count
  have hΛ0 : ∀ m ∈ Finset.Ico 2 K, 0 ≤ lamT c δ s m M := fun m hm => by
    have hm' := Finset.mem_Ico.1 hm
    have hmM : m + 1 ≤ M := by omega
    have hF := lamF_nonneg (c := c) (δ := δ) hm'.1 hmM hδ hc0
    unfold lamT
    split_ifs with h2
    · exact add_nonneg (lam2_nonneg hδ.le hs.le hc0) hF
    · have : (3 : ℝ) ≤ m := by
        have : m ≠ 2 := fun h => h2 (by rw [h]; norm_num)
        exact_mod_cast (show 3 ≤ m by omega)
      exact add_nonneg (lamN_nonneg this hδ.le hc0) hF
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.Ico 2 K) (fun m => √(lamT c δ s m M)) (fun m => √(W m))
  rw [Finset.sum_congr rfl fun m hm => Real.sq_sqrt (hΛ0 m hm), Finset.sum_congr rfl fun m _ => Real.sq_sqrt (hW0 m)]
    at hcs
  have hwin := window_mass_le (integrableOn_Phi_sq a hg hg₁ hg₂c hang hc0).2 hM3 hd hd2
    (S := Finset.Ico 2 K) fun m hm => by have := Finset.mem_Ico.1 hm; omega
  have hW2 : 2 * √PA * √(∑ m ∈ Finset.Ico 2 K, W m) ≤ (1 + π ^ 2 * d ^ 2) * P := by
    have h1 := Real.sq_sqrt hPA0
    have h2 := Real.sq_sqrt (Finset.sum_nonneg fun m (_ : m ∈ Finset.Ico 2 K) => hW0 m)
    have : 2 * √PA * √(∑ m ∈ Finset.Ico 2 K, W m) ≤ PA + ∑ m ∈ Finset.Ico 2 K, W m := by
      nlinarith [sq_nonneg (√PA - √(∑ m ∈ Finset.Ico 2 K, W m))]
    have e : PA + ∑ m ∈ Finset.Ico 2 K, W m = (∫ t in Ioc 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2)
        + (∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) ^ 2)
        + ∑ m ∈ Finset.Ico 2 K, ∫ x in ((m : ℝ) - d)..(m + d), (∑ i, a i * psi c (g i) x) ^ 2 := by
      rw [hPA]; rfl
    linarith
  have hPP : √PA * √P ≤ P := by
    calc √PA * √P ≤ √P * √P := by gcongr
      _ = P := Real.mul_self_sqrt hP0
  have hSE : 0 ≤ ∑ m ∈ Finset.Ico 2 K, (√(eT c d δ s m M J) + √(kT c s m M J)) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hSq0 : 0 ≤ √(∑ m ∈ Finset.Ico 2 K, lamT c δ s m M) := Real.sqrt_nonneg _
  have hBsum : ∑ m ∈ Finset.Ico 2 K, B m = ∑ m ∈ Finset.Ico 2 K, √(lamT c δ s m M) * √(W m)
      + (∑ m ∈ Finset.Ico 2 K, (√(eT c d δ s m M J) + √(kT c s m M J))) * √P := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  have key1 : 2 * (√PA * ∑ m ∈ Finset.Ico 2 K, √(lamT c δ s m M) * √(W m))
      ≤ (1 + π ^ 2 * d ^ 2) * √(∑ m ∈ Finset.Ico 2 K, lamT c δ s m M) * P := by
    have h := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 2 * √PA)
    have h' := mul_le_mul_of_nonneg_left hW2 hSq0
    nlinarith
  have key2 : 2 * (√PA * ((∑ m ∈ Finset.Ico 2 K, (√(eT c d δ s m M J) + √(kT c s m M J))) * √P))
      ≤ 2 * (∑ m ∈ Finset.Ico 2 K, (√(eT c d δ s m M J) + √(kT c s m M J))) * P := by
    have := mul_le_mul_of_nonneg_left hPP hSE
    nlinarith
  unfold calB
  rw [← hK]
  rw [hBsum, mul_add] at hhead
  nlinarith [hhead, htail, key1, key2]

end assembly

end Cvs.L2a.LocalisedBottomCorners
