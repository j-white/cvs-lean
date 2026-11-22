import Mathlib
import Cvs.L2a.AdmixtureNegligibleModes
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.LeakageEnergyScaling
import Cvs.L2a.PoleChannelNegligible
import Cvs.L2a.PrimeChannelDiagonalSplit
import Cvs.L2a.TailNormDiagonalSplit
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.ArcsineLawErrorSizes
import Cvs.Prolate.Envelope.EdgeValueSoninBound
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ExteriorMassArcsineFinite
import Cvs.Prolate.ExteriorMassEdgeLayer
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.ModeEnergyArcsineLaw
import Cvs.Prolate.RungEndpointMass
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.WeilForm.Archimedean.ArchFormIntegrable
import Cvs.WeilForm.Archimedean.ArchSymbolOnTail
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The weighted arcsine laws of the diagonal Weil channels

For `h₀, h₄, h₈`: `Σ_{M≥1} log M (1/M)∫_M^∞ ψ_j² = (2/c)(1 − λ_j) S₁ + o((1 − λ_j)/c)`, `S₁ = Σ log M arcsin(1/M)/M`, and
`Σ_{M≥1} (1/M)∫_M^∞ ψ_j² (a(ν) − log(c/π)) = (2/c)(1 − λ_j) S_A + o(·)`, `ν = c w²/√(w² − 1)`,
`S_A = Σ (1/M) ℓ(arcsin(1/M))`, `ℓ(β) = ∫₀^β −log sin 2v`, `ℓ(π/2) = (π/2) log 2`. Generic form: a density
`0 ≤ ρ ≤ C/(w√(w²−1))` obeying a uniform arcsine law, with an edge bound, for any radial family with `χ/c² → 0`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology

namespace Cvs.L2a.WeightedArcsineDiagonal
open Cvs.ZeroCounting

/-- The arcsine density `1/(w√(w²−1))`. -/
def rr (w : ℝ) : ℝ := 1 / (w * √(w ^ 2 - 1))

/-- The local log-frequency weight `log(w²/(2√(w²−1)))`, which is `−log sin 2β` at `w = 1/sin β`. -/
def lw (w : ℝ) : ℝ := Real.log (w ^ 2 / (2 * √(w ^ 2 - 1)))

/-- `ℓ(β) = ∫₀^β −log sin 2v`. -/
def ell (β : ℝ) : ℝ := ∫ v in (0 : ℝ)..β, -Real.log (Real.sin (2 * v))

/-! ### The substitution `w = 1/sin v` -/

theorem image_arcsin_inv {Y : ℝ} (hY : 1 ≤ Y) :
    (fun w : ℝ => arcsin (1 / w)) '' Ioi Y = Ioo 0 (arcsin (1 / Y)) := by
  have hY0 : 0 < Y := by linarith
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw0 : 0 < w := hY0.trans hw
    have h1 : 1 / w < 1 / Y := one_div_lt_one_div_of_lt hY0 hw
    refine ⟨arcsin_pos.mpr (by positivity), arcsin_lt_arcsin (by linarith [one_div_pos.mpr hw0]) h1 ?_⟩
    rw [div_le_one hY0]; exact hY
  · rintro ⟨hv0, hvb⟩
    have hb : arcsin (1 / Y) ≤ π / 2 := arcsin_le_pi_div_two _
    have hs0 : 0 < sin v := sin_pos_of_pos_of_lt_pi hv0 (by linarith [pi_pos])
    have hsY : sin v < 1 / Y := by
      have := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) hb hvb
      rwa [sin_arcsin (by rw [le_div_iff₀ hY0]; linarith) (by rw [div_le_one hY0]; exact hY)] at this
    refine ⟨1 / sin v, ?_, ?_⟩
    · show Y < 1 / sin v
      rw [lt_div_iff₀ hs0]; rw [lt_div_iff₀ hY0] at hsY; linarith
    · show arcsin (1 / (1 / sin v)) = v
      rw [one_div_one_div, arcsin_sin (by linarith [pi_pos]) (by linarith)]

theorem hasDerivAt_arcsin_inv {w : ℝ} (hw : 1 < w) :
    HasDerivAt (fun s : ℝ => arcsin (1 / s)) (-rr w) w := by
  have h := (Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.hasDerivAt_arcsec hw).const_sub (π / 2)
  have e : (fun s : ℝ => arcsin (1 / s)) = fun s => π / 2 - arccos (1 / s) := by
    funext s; rw [arccos_eq_pi_div_two_sub_arcsin]; ring
  rw [e]; unfold rr; simpa using h

theorem injOn_arcsin_inv {Y : ℝ} (hY : 1 ≤ Y) : InjOn (fun w : ℝ => arcsin (1 / w)) (Ioi Y) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by have : Y < x := hx; linarith
  have hy0 : 0 < y := by have : Y < y := hy; linarith
  have hx1 : 1 / x ≤ 1 := by rw [div_le_one hx0]; have : Y < x := hx; linarith
  have hy1 : 1 / y ≤ 1 := by rw [div_le_one hy0]; have : Y < y := hy; linarith
  have := injOn_arcsin ⟨by linarith [one_div_pos.mpr hx0], hx1⟩ ⟨by linarith [one_div_pos.mpr hy0], hy1⟩ hxy
  have h2 : (1 / x)⁻¹ = (1 / y)⁻¹ := by rw [this]
  simpa using h2

theorem rr_pos {w : ℝ} (hw : 1 < w) : 0 < rr w := by
  have : 0 < w ^ 2 - 1 := by nlinarith
  unfold rr; have := sqrt_pos.mpr this; have : 0 < w := by linarith
  positivity

/-- **The substitution**: `∫_{Ioo 0 β} G = ∫_{Ioi Y} rr(w) G(arcsin(1/w))`, `β = arcsin(1/Y)`. -/
theorem integral_rr_mul {Y : ℝ} (hY : 1 ≤ Y) (G : ℝ → ℝ) :
    ∫ w in Ioi Y, rr w * G (arcsin (1 / w)) = ∫ v in Ioo 0 (arcsin (1 / Y)), G v := by
  rw [← image_arcsin_inv hY, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun w hw => (hasDerivAt_arcsin_inv (lt_of_le_of_lt hY hw)).hasDerivWithinAt) (injOn_arcsin_inv hY)]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  rw [abs_neg, abs_of_pos (rr_pos (lt_of_le_of_lt hY hw)), smul_eq_mul]

theorem integrableOn_rr_mul_iff {Y : ℝ} (hY : 1 ≤ Y) (G : ℝ → ℝ) :
    IntegrableOn (fun w => rr w * G (arcsin (1 / w))) (Ioi Y) ↔
      IntegrableOn G (Ioo 0 (arcsin (1 / Y))) := by
  rw [← image_arcsin_inv hY, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun w hw => (hasDerivAt_arcsin_inv (lt_of_le_of_lt hY hw)).hasDerivWithinAt) (injOn_arcsin_inv hY)]
  refine integrableOn_congr_fun (fun w hw => ?_) measurableSet_Ioi
  rw [abs_neg, abs_of_pos (rr_pos (lt_of_le_of_lt hY hw)), smul_eq_mul]

/-- `−log sin(2 arcsin(1/w)) = lw w` for `w > 1`. -/
theorem neg_log_sin_two_arcsin {w : ℝ} (hw : 1 < w) : -Real.log (sin (2 * arcsin (1 / w))) = lw w := by
  have hw0 : 0 < w := by linarith
  have hB : 0 < w ^ 2 - 1 := by nlinarith
  have hs : √(1 - (1 / w) ^ 2) = √(w ^ 2 - 1) / w := by
    rw [show 1 - (1 / w) ^ 2 = (w ^ 2 - 1) / w ^ 2 by field_simp, sqrt_div hB.le, sqrt_sq hw0.le]
  rw [sin_two_mul, sin_arcsin (by linarith [one_div_pos.mpr hw0]) (by rw [div_le_one hw0]; linarith),
    cos_arcsin, hs, lw, ← Real.log_inv]
  congr 1
  have := sqrt_pos.mpr hB
  field_simp

theorem integrableOn_neg_log_sin {β : ℝ} (hβ : 0 ≤ β) :
    IntegrableOn (fun v => -Real.log (sin (2 * v))) (Ioo 0 β) := by
  have h := (intervalIntegrable_log_sin (a := 0) (b := 2 * β)).comp_mul_left (c := 2)
  simp only [Function.comp_apply, zero_div, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] at h
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hβ).mp h).neg

/-- **The arcsine mass**: `∫_Y^∞ rr = arcsin(1/Y)`. -/
theorem integral_rr {Y : ℝ} (hY : 1 ≤ Y) : ∫ w in Ioi Y, rr w = arcsin (1 / Y) := by
  have h := integral_rr_mul hY (fun _ => 1)
  simp only [mul_one] at h
  rw [h, setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo_of_le
    (arcsin_nonneg.mpr (by positivity)), sub_zero]

theorem integrableOn_rr {Y : ℝ} (hY : 1 ≤ Y) : IntegrableOn rr (Ioi Y) := by
  have h := (integrableOn_rr_mul_iff hY (fun _ => (1 : ℝ))).mpr (integrableOn_const (by simp))
  simpa using h

/-- **The log-weighted arcsine mass**: `∫_Y^∞ rr·lw = ℓ(arcsin(1/Y))`. -/
theorem integral_rr_lw {Y : ℝ} (hY : 1 ≤ Y) : ∫ w in Ioi Y, rr w * lw w = ell (arcsin (1 / Y)) := by
  have h := integral_rr_mul hY (fun v => -Real.log (sin (2 * v)))
  rw [ell, intervalIntegral.integral_of_le (arcsin_nonneg.mpr (by positivity)), integral_Ioc_eq_integral_Ioo,
    ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  show rr w * lw w = rr w * -Real.log (sin (2 * arcsin (1 / w)))
  rw [neg_log_sin_two_arcsin (lt_of_le_of_lt hY hw)]

theorem integrableOn_rr_lw {Y : ℝ} (hY : 1 ≤ Y) : IntegrableOn (fun w => rr w * lw w) (Ioi Y) := by
  have h := (integrableOn_rr_mul_iff hY (fun v => -Real.log (sin (2 * v)))).mpr
    (integrableOn_neg_log_sin (arcsin_nonneg.mpr (by positivity)))
  refine h.congr_fun (fun w hw => ?_) measurableSet_Ioi
  show rr w * -Real.log (sin (2 * arcsin (1 / w))) = rr w * lw w
  rw [neg_log_sin_two_arcsin (lt_of_le_of_lt hY hw)]

/-! ### The comparison lemma -/

/-- The tail `D(x) = ∫_x^∞ f` is `D(a) − ∫_a^x f` past `a`. -/
theorem integral_Ioi_eq_sub {f : ℝ → ℝ} {a x : ℝ} (hfi : IntegrableOn f (Ioi a)) (hx : a ≤ x) :
    ∫ t in Ioi x, f t = (∫ t in Ioi a, f t) - ∫ t in a..x, f t := by
  rw [intervalIntegral.integral_of_le hx, eq_sub_iff_add_eq, add_comm, ← setIntegral_union
    (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hfi.mono_set Ioc_subset_Ioi_self)
    (hfi.mono_set (Ioi_subset_Ioi hx)), Ioc_union_Ioi_eq_Ioi hx]

theorem hasDerivAt_integral_Ioi {f : ℝ → ℝ} {a x : ℝ} (hfc : ContinuousOn f (Ioi a))
    (hfi : IntegrableOn f (Ioi a)) (hx : a < x) :
    HasDerivAt (fun y => ∫ t in Ioi y, f t) (-f x) x := by
  have hI : IntervalIntegrable f volume a x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mpr (hfi.mono_set Ioc_subset_Ioi_self)
  have h := (intervalIntegral.integral_hasDerivAt_right hI
    (hfc.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hfc.continuousAt (Ioi_mem_nhds hx))).const_sub
    (∫ t in Ioi a, f t)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact integral_Ioi_eq_sub hfi (le_of_lt hy)

theorem tendsto_integral_Ioi_nhdsGT {f : ℝ → ℝ} {a : ℝ} (hfi : IntegrableOn f (Ioi a)) :
    Tendsto (fun y => ∫ t in Ioi y, f t) (𝓝[>] a) (𝓝 (∫ t in Ioi a, f t)) := by
  have hI : IntervalIntegrable f volume (min a a) (max a (a + 1)) := by
    rw [min_self, max_eq_right (by linarith)]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
      (hfi.mono_set Ioc_subset_Ioi_self)
  have hc := intervalIntegral.continuousWithinAt_primitive (μ := volume) (b₀ := a) (b₁ := a) (b₂ := a + 1)
    (by simp) hI
  have hc' : Tendsto (fun b => ∫ x in a..b, f x) (𝓝[>] a) (𝓝 (∫ x in a..a, f x)) := by
    refine hc.tendsto.mono_left (nhdsWithin_le_of_mem ?_)
    exact mem_of_superset (Ioc_mem_nhdsGT (by linarith : a < a + 1)) Ioc_subset_Icc_self
  rw [intervalIntegral.integral_same] at hc'
  have h2 := hc'.const_sub (∫ t in Ioi a, f t)
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (integral_Ioi_eq_sub hfi (le_of_lt hy)).symm

/-- **Comparison through the tail**: if `|∫_x^∞ f| ≤ e(x)` for `x ≥ a`, then
`|∫_a^∞ L f| ≤ |L(a)| e(a) + ∫_a^∞ |L'| e`. -/
theorem abs_integral_mul_le {f L L' e : ℝ → ℝ} {a : ℝ}
    (hfc : ContinuousOn f (Ioi a)) (hfi : IntegrableOn f (Ioi a))
    (hL : ∀ x ∈ Ioi a, HasDerivAt L (L' x) x) (hLa : ContinuousAt L a)
    (hL'c : ContinuousOn L' (Ioi a))
    (hLf : IntegrableOn (fun x => L x * f x) (Ioi a))
    (hD : ∀ x, a ≤ x → |∫ t in Ioi x, f t| ≤ e x)
    (he : IntegrableOn (fun x => |L' x| * e x) (Ioi a))
    (hinf : Tendsto (fun x => |L x| * e x) atTop (𝓝 0)) :
    |∫ x in Ioi a, L x * f x| ≤ |L a| * e a + ∫ x in Ioi a, |L' x| * e x := by
  set D : ℝ → ℝ := fun y => ∫ t in Ioi y, f t with hDdef
  have hDd : ∀ x ∈ Ioi a, HasDerivAt (fun y => -D y) (f x) x := fun x hx => by
    have h := (hasDerivAt_integral_Ioi hfc hfi hx).neg
    rw [neg_neg] at h
    exact h
  have hDc : ContinuousOn D (Ioi a) := fun x hx =>
    (hasDerivAt_integral_Ioi hfc hfi hx).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun x => L' x * -D x) (volume.restrict (Ioi a)) :=
    (hL'c.mul hDc.neg).aestronglyMeasurable measurableSet_Ioi
  have hbd : ∀ x ∈ Ioi a, ‖L' x * -D x‖ ≤ |L' x| * e x := fun x hx => by
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hD x (le_of_lt hx)) (abs_nonneg _)
  have hint : IntegrableOn (fun x => L' x * -D x) (Ioi a) :=
    he.mono' hmeas (ae_restrict_of_forall_mem measurableSet_Ioi hbd)
  have h0 : Tendsto (L * fun y => -D y) (𝓝[>] a) (𝓝 (L a * -D a)) :=
    (hLa.tendsto.mono_left nhdsWithin_le_nhds).mul (tendsto_integral_Ioi_nhdsGT hfi).neg
  have hinf' : Tendsto (L * fun y => -D y) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hinf
    filter_upwards [eventually_gt_atTop a] with x hx
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hD x (le_of_lt hx)) (abs_nonneg _)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hL hDd hLf hint h0 hinf'
  rw [hibp]
  have e1 : (0 : ℝ) - L a * -D a - ∫ x in Ioi a, L' x * -D x = L a * D a + -∫ x in Ioi a, L' x * -D x := by ring
  rw [e1]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD a le_rfl) (abs_nonneg _)
  · rw [abs_neg, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le he (ae_restrict_of_forall_mem measurableSet_Ioi hbd)

/-! ### The weight `lw` -/

/-- `lw' = (w² − 2)/(w(w² − 1))`. -/
def lwd (w : ℝ) : ℝ := (w ^ 2 - 2) / (w * (w ^ 2 - 1))

theorem lw_eq {w : ℝ} (hw : 1 < w) : lw w = 2 * Real.log w - Real.log 2 - Real.log (w ^ 2 - 1) / 2 := by
  have hw0 : 0 < w := by linarith
  have hB : 0 < w ^ 2 - 1 := by nlinarith
  rw [lw, Real.log_div (by positivity) (by positivity), Real.log_mul two_ne_zero (sqrt_pos.mpr hB).ne',
    Real.log_sqrt hB.le, Real.log_pow]
  push_cast; ring

theorem hasDerivAt_lw {w : ℝ} (hw : 1 < w) : HasDerivAt lw (lwd w) w := by
  have hw0 : 0 < w := by linarith
  have hB : 0 < w ^ 2 - 1 := by nlinarith
  have h1 := (Real.hasDerivAt_log hw0.ne').const_mul 2
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2 - 1) (2 * w) w := by
    simpa using (hasDerivAt_pow 2 w).sub_const 1
  have h3 := (h2.log hB.ne').div_const 2
  have h := (h1.sub_const (Real.log 2)).sub h3
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds hw] with x hx
    exact lw_eq hx
  · unfold lwd; field_simp; ring

theorem continuousOn_lwd : ContinuousOn lwd (Ioi 1) := by
  have hf : ContinuousOn (fun w : ℝ => w ^ 2 - 2) (Ioi 1) := by fun_prop
  have hg : ContinuousOn (fun w : ℝ => w * (w ^ 2 - 1)) (Ioi 1) := by fun_prop
  have hne : ∀ w ∈ Ioi (1 : ℝ), w * (w ^ 2 - 1) ≠ 0 := fun w hw => by
    have hw' : (1 : ℝ) < w := hw
    have : 0 < w ^ 2 - 1 := by nlinarith
    have : 0 < w := by linarith
    positivity
  have h := hf.div hg hne
  have he : lwd = fun w : ℝ => (w ^ 2 - 2) / (w * (w ^ 2 - 1)) := rfl
  rw [he]
  exact h

theorem lw_nonneg {w : ℝ} (hw : 1 < w) : 0 ≤ lw w := by
  have hB : 0 < w ^ 2 - 1 := by nlinarith
  have hs := sqrt_pos.mpr hB
  have hss := sq_sqrt hB.le
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (√(w ^ 2 - 1) - 1)]

theorem lw_le_log {w : ℝ} (hw : 2 ≤ w) : lw w ≤ Real.log w := by
  have hw0 : 0 < w := by linarith
  have hB : 0 < w ^ 2 - 1 := by nlinarith
  have hs := sqrt_pos.mpr hB
  have hss := sq_sqrt hB.le
  unfold lw
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ (by positivity)]
  have : w / 2 ≤ √(w ^ 2 - 1) := by
    rw [Real.le_sqrt (by positivity) hB.le]; nlinarith
  nlinarith

/-- `|lw'(x)| ≤ 3Y²/((Y² − 1)x)` for `1 < Y ≤ x`. -/
theorem abs_lwd_le {Y x : ℝ} (hY : 1 < Y) (hx : Y ≤ x) : |lwd x| ≤ 3 * Y ^ 2 / ((Y ^ 2 - 1) * x) := by
  have hx1 : 1 < x := lt_of_lt_of_le hY hx
  have hx0 : 0 < x := by linarith
  have hB : 0 < x ^ 2 - 1 := by nlinarith
  have hBY : 0 < Y ^ 2 - 1 := by nlinarith
  have hYx : Y ^ 2 ≤ x ^ 2 := by nlinarith
  unfold lwd
  rw [abs_div, abs_of_pos (by positivity : 0 < x * (x ^ 2 - 1)), div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |x ^ 2 - 2| ≤ 3 * x ^ 2 := by rw [abs_le]; constructor <;> nlinarith
  -- `(Y² − 1)x² ≤ Y²(x² − 1)`
  have h2 : (Y ^ 2 - 1) * x ^ 2 ≤ Y ^ 2 * (x ^ 2 - 1) := by nlinarith
  calc |x ^ 2 - 2| * ((Y ^ 2 - 1) * x) ≤ 3 * x ^ 2 * ((Y ^ 2 - 1) * x) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 3 * x * ((Y ^ 2 - 1) * x ^ 2) := by ring
    _ ≤ 3 * x * (Y ^ 2 * (x ^ 2 - 1)) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 3 * Y ^ 2 * (x * (x ^ 2 - 1)) := by ring

/-- Near the edge, `lw(w) ≤ −½ log(w − 1)` for `1 < w`, `w² ≤ 2`. -/
theorem lw_le_edge {w : ℝ} (hw : 1 < w) (hw2 : w ^ 2 ≤ 2) : lw w ≤ -(Real.log (w - 1) / 2) := by
  have hw0 : 0 < w := by linarith
  rw [lw_eq hw]
  have h1 : 2 * Real.log w - Real.log 2 ≤ 0 := by
    rw [← Real.log_rpow hw0, sub_nonpos]
    apply Real.log_le_log (by positivity); norm_cast
  have h2 : Real.log (w - 1) ≤ Real.log (w ^ 2 - 1) := Real.log_le_log (by linarith) (by nlinarith)
  linarith

/-! ### One tail against the arcsine law -/

theorem continuousOn_rr : ContinuousOn rr (Ioi 1) := by
  have hg : ContinuousOn (fun w : ℝ => w * √(w ^ 2 - 1)) (Ioi 1) := by fun_prop
  refine ContinuousOn.div (f := fun _ : ℝ => (1 : ℝ)) (g := fun w : ℝ => w * √(w ^ 2 - 1))
    continuousOn_const hg fun w hw => ?_
  have hw' : (1 : ℝ) < w := hw
  exact (mul_pos (by linarith) (sqrt_pos.mpr (by nlinarith))).ne'

theorem continuousOn_lw : ContinuousOn lw (Ioi 1) := fun _ hw =>
  (hasDerivAt_lw hw).continuousAt.continuousWithinAt

theorem tendsto_log_div : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simpa using h

/-- A density dominated by the arcsine density has every log-weighted tail integrable. -/
theorem integrableOn_mul_lw {ρ : ℝ → ℝ} {C : ℝ} (hρc : ContinuousOn ρ (Ioi 1))
    (hρ0 : ∀ w, 1 < w → 0 ≤ ρ w) (hρC : ∀ w, 1 < w → ρ w ≤ C * rr w) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun w => ρ w * lw w) (Ioi Y) := by
  have hm : AEStronglyMeasurable (fun w => ρ w * lw w) (volume.restrict (Ioi Y)) :=
    ((hρc.mul continuousOn_lw).mono (Ioi_subset_Ioi hY)).aestronglyMeasurable measurableSet_Ioi
  refine ((integrableOn_rr_lw hY).const_mul C).mono' hm (ae_restrict_of_forall_mem measurableSet_Ioi ?_)
  intro w hw
  have hw1 : 1 < w := lt_of_le_of_lt hY hw
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 w hw1) (lw_nonneg hw1)), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hρC w hw1) (lw_nonneg hw1)

theorem integrableOn_of_le_rr {ρ : ℝ → ℝ} {C : ℝ} (hρc : ContinuousOn ρ (Ioi 1))
    (hρ0 : ∀ w, 1 < w → 0 ≤ ρ w) (hρC : ∀ w, 1 < w → ρ w ≤ C * rr w) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn ρ (Ioi Y) := by
  refine ((integrableOn_rr hY).const_mul C).mono' ((hρc.mono (Ioi_subset_Ioi hY)).aestronglyMeasurable
    measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => ?_)
  have hw1 : 1 < w := lt_of_le_of_lt hY hw
  rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 w hw1)]
  exact hρC w hw1

/-- **One tail against the arcsine law**: if `|∫_x^∞ ρ − K arcsin(1/x)| ≤ ε/x` for `x ≥ Y > 1`, then
`|∫_Y^∞ ρ·lw − K ℓ(arcsin(1/Y))| ≤ ε (lw(Y)/Y + 3Y/(Y² − 1))`. -/
theorem abs_tail_lw_le {ρ : ℝ → ℝ} {C K ε Y : ℝ} (hY : 1 < Y) (hε : 0 ≤ ε)
    (hρc : ContinuousOn ρ (Ioi 1)) (hρ0 : ∀ w, 1 < w → 0 ≤ ρ w) (hρC : ∀ w, 1 < w → ρ w ≤ C * rr w)
    (hlaw : ∀ x, Y ≤ x → |(∫ t in Ioi x, ρ t) - K * arcsin (1 / x)| ≤ ε / x) :
    |(∫ w in Ioi Y, ρ w * lw w) - K * ell (arcsin (1 / Y))| ≤ ε * (lw Y / Y + 3 * Y / (Y ^ 2 - 1)) := by
  have hY0 : 0 < Y := by linarith
  have hBY : 0 < Y ^ 2 - 1 := by nlinarith
  set f : ℝ → ℝ := fun w => ρ w - K * rr w with hf
  have hρi : IntegrableOn ρ (Ioi Y) := integrableOn_of_le_rr hρc hρ0 hρC hY.le
  have hri : IntegrableOn rr (Ioi Y) := integrableOn_rr hY.le
  have hρl : IntegrableOn (fun w => ρ w * lw w) (Ioi Y) := integrableOn_mul_lw hρc hρ0 hρC hY.le
  have hrl : IntegrableOn (fun w => rr w * lw w) (Ioi Y) := integrableOn_rr_lw hY.le
  have hfi : IntegrableOn f (Ioi Y) := hρi.sub (hri.const_mul K)
  have hLf : IntegrableOn (fun x => lw x * f x) (Ioi Y) := by
    refine (hρl.sub (hrl.const_mul K)).congr_fun (fun w _ => ?_) measurableSet_Ioi
    show ρ w * lw w - K * (rr w * lw w) = lw w * (ρ w - K * rr w)
    ring
  have hmain : (∫ w in Ioi Y, ρ w * lw w) - K * ell (arcsin (1 / Y)) = ∫ x in Ioi Y, lw x * f x := by
    rw [← integral_rr_lw hY.le, ← integral_const_mul, ← integral_sub hρl (hrl.const_mul K)]
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    simp only [hf]; ring
  have hD : ∀ x, Y ≤ x → |∫ t in Ioi x, f t| ≤ ε / x := fun x hx => by
    have hfx : ∫ t in Ioi x, f t = (∫ t in Ioi x, ρ t) - K * arcsin (1 / x) := by
      simp only [hf]
      rw [integral_sub (hρi.mono_set (Ioi_subset_Ioi hx)) ((hri.mono_set (Ioi_subset_Ioi hx)).const_mul K),
        integral_const_mul, integral_rr (by linarith)]
    rw [hfx]; exact hlaw x hx
  have hbd : ∀ x ∈ Ioi Y, |lwd x| * (ε / x) ≤ 3 * Y ^ 2 * ε / (Y ^ 2 - 1) * (1 / x ^ 2) := fun x hx => by
    have hx : Y ≤ x := le_of_lt hx
    have hx0 : 0 < x := by linarith
    calc |lwd x| * (ε / x) ≤ 3 * Y ^ 2 / ((Y ^ 2 - 1) * x) * (ε / x) :=
          mul_le_mul_of_nonneg_right (abs_lwd_le hY hx) (by positivity)
      _ = 3 * Y ^ 2 * ε / (Y ^ 2 - 1) * (1 / x ^ 2) := by field_simp
  have hdom : IntegrableOn (fun x : ℝ => 3 * Y ^ 2 * ε / (Y ^ 2 - 1) * (1 / x ^ 2)) (Ioi Y) :=
    (Cvs.L2a.FullTailConvergence.integrableOn_one_div_sq hY0).const_mul _
  have hYsub : Ioi Y ⊆ Ioi 1 := Ioi_subset_Ioi hY.le
  have he : IntegrableOn (fun x => |lwd x| * (ε / x)) (Ioi Y) := by
    refine hdom.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ((continuousOn_lwd.mono hYsub).abs).mul (continuousOn_const.div continuousOn_id fun x hx => ?_)
      exact (lt_trans hY0 hx).ne'
    · rw [Real.norm_eq_abs, abs_of_nonneg (by have : 0 < x := lt_trans hY0 hx; positivity)]
      exact hbd x hx
  have hinf : Tendsto (fun x => |lw x| * (ε / x)) atTop (𝓝 0) := by
    have h := tendsto_log_div.const_mul ε
    rw [mul_zero] at h
    refine squeeze_zero' ((eventually_ge_atTop 0).mono fun x hx => by positivity) ?_ h
    · filter_upwards [eventually_ge_atTop 2] with x hx
      have hx1 : 1 < x := by linarith
      rw [abs_of_nonneg (lw_nonneg hx1)]
      calc lw x * (ε / x) ≤ Real.log x * (ε / x) :=
            mul_le_mul_of_nonneg_right (lw_le_log hx) (by positivity)
        _ = ε * (Real.log x / x) := by ring
  have hcmp := abs_integral_mul_le (f := f) (L := lw) (L' := lwd) (e := fun x => ε / x) (a := Y)
    ((hρc.mono hYsub).sub (continuousOn_const.mul (continuousOn_rr.mono hYsub)))
    hfi (fun x hx => hasDerivAt_lw (lt_trans hY hx)) (hasDerivAt_lw hY).continuousAt
    (continuousOn_lwd.mono hYsub) hLf hD he hinf
  rw [hmain]
  refine hcmp.trans ?_
  rw [abs_of_nonneg (lw_nonneg hY)]
  have hint : ∫ x in Ioi Y, |lwd x| * (ε / x) ≤ 3 * Y * ε / (Y ^ 2 - 1) := by
    calc ∫ x in Ioi Y, |lwd x| * (ε / x)
        ≤ ∫ x in Ioi Y, 3 * Y ^ 2 * ε / (Y ^ 2 - 1) * (1 / x ^ 2) :=
          setIntegral_mono_on he hdom measurableSet_Ioi hbd
      _ = 3 * Y * ε / (Y ^ 2 - 1) := by
          rw [integral_const_mul, Cvs.L2a.FullTailConvergence.integral_one_div_sq hY0]; field_simp
  have e1 : ε * (lw Y / Y + 3 * Y / (Y ^ 2 - 1)) = lw Y * (ε / Y) + 3 * Y * ε / (Y ^ 2 - 1) := by
    field_simp
  rw [e1]; linarith

/-! ### The constants -/

theorem intervalIntegrable_neg_log_sin (a b : ℝ) :
    IntervalIntegrable (fun v => -Real.log (sin (2 * v))) volume a b := by
  have h := (intervalIntegrable_log_sin (a := 2 * a) (b := 2 * b)).comp_mul_left (c := 2)
  simp only [Function.comp_apply, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] at h
  exact h.neg

theorem continuous_ell : Continuous ell :=
  intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_neg_log_sin a b) 0

/-- `ℓ(π/2) = (π/2) log 2`. -/
theorem ell_pi_div_two : ell (π / 2) = π / 2 * Real.log 2 := by
  unfold ell
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_mul_left (fun v => Real.log (sin v))
    (two_ne_zero' ℝ), mul_zero, show 2 * (π / 2) = π by ring, integral_log_sin_zero_pi]
  ring

theorem neg_log_sin_nonneg {v : ℝ} (hv0 : 0 < v) (hv : v < π / 2) : 0 ≤ -Real.log (sin (2 * v)) := by
  have : 0 < sin (2 * v) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have := Real.log_nonpos this.le (sin_le_one _)
  linarith

theorem ell_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < π / 2) : ell a ≤ ell b := by
  unfold ell
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_neg_log_sin 0 a)
    (intervalIntegrable_neg_log_sin a b)]
  have : 0 ≤ ∫ v in a..b, -Real.log (sin (2 * v)) := by
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_nonneg_ae measurableSet_Ioc (ae_of_all _ fun v hv => ?_)
    rcases eq_or_lt_of_le hv.2 with h | h
    · exact neg_log_sin_nonneg (lt_of_le_of_lt ha hv.1) (h ▸ hb)
    · exact neg_log_sin_nonneg (lt_of_le_of_lt ha hv.1) (lt_trans h hb)
  linarith

theorem ell_nonneg {a : ℝ} (ha : 0 ≤ a) (hb : a < π / 2) : 0 ≤ ell a := by
  have := ell_mono le_rfl ha hb
  simpa [ell] using this

/-- **The decay of `ℓ`**: `ℓ(arcsin(1/Y)) ≤ (π/(2Y))(1 + log(Y/2))` for `Y ≥ 2`. -/
theorem ell_arcsin_le {Y : ℝ} (hY : 2 ≤ Y) :
    ell (arcsin (1 / Y)) ≤ π / (2 * Y) * (1 + Real.log (Y / 2)) := by
  have hY0 : 0 < Y := by linarith
  have hπ := pi_pos
  set b := π / (2 * Y) with hb
  have hb0 : 0 < b := by positivity
  have hb4 : b ≤ π / 4 := by
    rw [hb, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hβ0 : 0 ≤ arcsin (1 / Y) := arcsin_nonneg.mpr (by positivity)
  have hβb : arcsin (1 / Y) ≤ b := by
    have := Cvs.L2a.LeakageEnergyScaling.arcsin_le_pi_div_two_mul (y := 1 / Y) (by positivity)
      (by rw [div_le_one hY0]; linarith)
    calc arcsin (1 / Y) ≤ π / 2 * (1 / Y) := this
      _ = b := by rw [hb]; field_simp
  refine (ell_mono hβ0 hβb (by linarith)).trans ?_
  -- `−log sin 2v ≤ −log(4v/π)` on `(0, b]`
  have hlog : IntervalIntegrable (fun v => -Real.log (4 / π * v)) volume 0 b := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := 4 / π * 0) (b := 4 / π * b)).comp_mul_left
      (c := 4 / π)
    simp only [mul_div_cancel_left₀ _ (by positivity : (4 / π : ℝ) ≠ 0)] at h
    exact h.neg
  have hle : ell b ≤ ∫ v in (0 : ℝ)..b, -Real.log (4 / π * v) := by
    unfold ell
    refine intervalIntegral.integral_mono_ae_restrict hb0.le (intervalIntegrable_neg_log_sin 0 b) hlog ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine ae_of_all _ fun v hv => ?_
    rcases eq_or_lt_of_le hv.1 with h | h
    · subst h; simp
    · have h2 : 2 / π * (2 * v) ≤ sin (2 * v) := mul_le_sin (by linarith) (by linarith [hv.2])
      have h4 : 0 < 4 / π * v := by positivity
      have : Real.log (4 / π * v) ≤ Real.log (sin (2 * v)) :=
        Real.log_le_log h4 (by linarith [show 2 / π * (2 * v) = 4 / π * v by ring])
      linarith
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_mul_left (fun v => Real.log v)
    (by positivity : (4 / π : ℝ) ≠ 0), integral_log]
  have e : 4 / π * b = 2 / Y := by rw [hb]; field_simp; ring
  rw [e]
  simp only [smul_eq_mul]
  have hl : Real.log (2 / Y) = -Real.log (Y / 2) := by rw [← Real.log_inv, inv_div]
  rw [hl, hb]; field_simp; ring

/-- `S₁ = Σ_{M≥1} log M · arcsin(1/M)/M`. -/
def sOne : ℝ := ∑' M : ℕ, Real.log ((M : ℝ) + 1) * arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1)

/-- `S_A = Σ_{M≥1} ℓ(arcsin(1/M))/M`, `ℓ(β) = ∫₀^β −log sin 2v`. -/
def sArch : ℝ := ∑' M : ℕ, ell (arcsin (1 / ((M : ℝ) + 1))) / ((M : ℝ) + 1)

/-- The error weight `Σ_{M≥1} (log M + 4)/M²`. -/
def sErr : ℝ := ∑' M : ℕ, (Real.log ((M : ℝ) + 1) + 4) / ((M : ℝ) + 1) ^ 2

theorem summable_err : Summable fun M : ℕ => (Real.log ((M : ℝ) + 1) + 4) / ((M : ℝ) + 1) ^ 2 := by
  refine (Cvs.L2a.PrimeChannelDiagonalSplit.summable_wLog_div.add (Cvs.Prolate.ModeEnergyArcsineLaw.summable_inv_sq.mul_left 4)).congr
    fun M => ?_
  unfold Cvs.L2a.PrimeChannelDiagonalSplit.wLog; field_simp

theorem summable_sOne : Summable fun M : ℕ =>
    Real.log ((M : ℝ) + 1) * arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1) := by
  refine (Cvs.L2a.PrimeChannelDiagonalSplit.summable_wLog_div.mul_left (π / 2)).of_nonneg_of_le (fun M => ?_) fun M => ?_
  · have := Real.log_nonneg (by linarith [M.cast_nonneg (α := ℝ)] : (1 : ℝ) ≤ (M : ℝ) + 1)
    have := arcsin_nonneg.mpr (by positivity : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1))
    positivity
  · have hM : (0 : ℝ) < M + 1 := by positivity
    have hl := Real.log_nonneg (by linarith [M.cast_nonneg (α := ℝ)] : (1 : ℝ) ≤ (M : ℝ) + 1)
    have h := Cvs.L2a.LeakageEnergyScaling.arcsin_le_pi_div_two_mul (y := 1 / ((M : ℝ) + 1)) (by positivity)
      (by rw [div_le_one hM]; linarith [M.cast_nonneg (α := ℝ)])
    unfold Cvs.L2a.PrimeChannelDiagonalSplit.wLog
    calc Real.log ((M : ℝ) + 1) * arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1)
        ≤ Real.log ((M : ℝ) + 1) * (π / 2 * (1 / ((M : ℝ) + 1))) / ((M : ℝ) + 1) := by gcongr
      _ = π / 2 * (Real.log ((M : ℝ) + 1) / ((M : ℝ) + 1) / ((M : ℝ) + 1)) := by ring

theorem summable_sArch : Summable fun M : ℕ => ell (arcsin (1 / ((M : ℝ) + 1))) / ((M : ℝ) + 1) := by
  rw [← summable_nat_add_iff 1]
  refine ((summable_err.mul_left π)).of_nonneg_of_le (fun M => ?_) fun M => ?_
  · have hM : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) + 1 := by positivity
    have h1 : arcsin (1 / (((M + 1 : ℕ) : ℝ) + 1)) < π / 2 := by
      have : arcsin (1 / (((M + 1 : ℕ) : ℝ) + 1)) ≤ π / 2 * (1 / (((M + 1 : ℕ) : ℝ) + 1)) :=
        Cvs.L2a.LeakageEnergyScaling.arcsin_le_pi_div_two_mul (by positivity)
          (by rw [div_le_one hM]; push_cast; linarith [M.cast_nonneg (α := ℝ)])
      have h2 : π / 2 * (1 / (((M + 1 : ℕ) : ℝ) + 1)) < π / 2 := by
        have : 1 / (((M + 1 : ℕ) : ℝ) + 1) < 1 := by
          rw [div_lt_one hM]; push_cast; linarith [M.cast_nonneg (α := ℝ)]
        nlinarith [pi_pos]
      linarith
    exact div_nonneg (ell_nonneg (arcsin_nonneg.mpr (by positivity)) h1) hM.le
  · set Y : ℝ := ((M + 1 : ℕ) : ℝ) + 1 with hYd
    have hY : 2 ≤ Y := by rw [hYd]; push_cast; linarith [M.cast_nonneg (α := ℝ)]
    have hY0 : 0 < Y := by linarith
    have h := ell_arcsin_le hY
    have hl : Real.log (Y / 2) ≤ Real.log Y := Real.log_le_log (by positivity) (by linarith)
    have hlY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
    have hlog2 : Real.log ((M : ℝ) + 1) ≤ Real.log Y :=
      Real.log_le_log (by positivity) (by rw [hYd]; push_cast; linarith)
    have hYM : Y ≤ 2 * ((M : ℝ) + 1) := by rw [hYd]; push_cast; linarith [M.cast_nonneg (α := ℝ)]
    have hlY2 : Real.log Y ≤ Real.log ((M : ℝ) + 1) + 1 := by
      have := Real.log_le_log hY0 hYM
      rw [Real.log_mul (by norm_num) (by positivity)] at this
      have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
      linarith
    have hMY : (M : ℝ) + 1 ≤ Y := by rw [hYd]; push_cast; linarith
    calc ell (arcsin (1 / Y)) / Y ≤ π / (2 * Y) * (1 + Real.log (Y / 2)) / Y :=
          div_le_div_of_nonneg_right h hY0.le
      _ ≤ π / (2 * Y) * (2 + Real.log ((M : ℝ) + 1)) / Y := by
          have h3 : Real.log (Y / 2) ≤ Real.log ((M : ℝ) + 1) :=
            Real.log_le_log (by positivity) (by rw [hYd]; push_cast; linarith)
          gcongr; linarith
      _ = π * ((2 + Real.log ((M : ℝ) + 1)) / (2 * Y ^ 2)) := by field_simp
      _ ≤ π * ((Real.log ((M : ℝ) + 1) + 4) / ((M : ℝ) + 1) ^ 2) := by
          gcongr ?_ * ?_
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hl0 := Real.log_nonneg (by linarith [M.cast_nonneg (α := ℝ)] : (1 : ℝ) ≤ (M : ℝ) + 1)
          nlinarith [mul_le_mul hMY hMY (by positivity) (by positivity)]

/-! ### The weighted sums -/

/-- The edge split: `∫_1^∞ ρ lw = ∫_{(1, ξ]} ρ lw + ∫_ξ^∞ ρ lw`. -/
theorem integral_Ioi_one_split {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 1)) {ξ : ℝ} (h1 : 1 ≤ ξ) :
    ∫ w in Ioi 1, g w = (∫ w in Ioc 1 ξ, g w) + ∫ w in Ioi ξ, g w := by
  rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hg.mono_set Ioc_subset_Ioi_self)
    (hg.mono_set (Ioi_subset_Ioi h1)), Ioc_union_Ioi_eq_Ioi h1]

/-- **The log-weighted mode sum** (generic): for `0 ≤ ρ ≤ C·rr` with `|∫_x^∞ ρ − K arcsin(1/x)| ≤ ε/x` (`x ≥ 1`) and
`∫_{(1, ξ]} ρ lw ≤ E`, `Σ_M (1/M)∫_M^∞ ρ lw` converges and is within
`E + K(ℓ(π/2) − ℓ(arcsin(1/ξ))) + ε(lw(ξ)/ξ + 3ξ/(ξ² − 1)) + ε S_err` of `K S_A`. -/
theorem abs_sum_lw_sub_le {ρ : ℝ → ℝ} {C K ε ξ E : ℝ} (hξ : 1 < ξ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hρc : ContinuousOn ρ (Ioi 1)) (hρ0 : ∀ w, 1 < w → 0 ≤ ρ w) (hρC : ∀ w, 1 < w → ρ w ≤ C * rr w)
    (hlaw : ∀ x, 1 ≤ x → |(∫ t in Ioi x, ρ t) - K * arcsin (1 / x)| ≤ ε / x)
    (hedge : ∫ w in Ioc 1 ξ, ρ w * lw w ≤ E) :
    Summable (fun M : ℕ => (∫ w in Ioi ((M : ℝ) + 1), ρ w * lw w) / ((M : ℝ) + 1)) ∧
      |∑' M : ℕ, (∫ w in Ioi ((M : ℝ) + 1), ρ w * lw w) / ((M : ℝ) + 1) - K * sArch|
        ≤ E + K * (ell (π / 2) - ell (arcsin (1 / ξ))) + ε * (lw ξ / ξ + 3 * ξ / (ξ ^ 2 - 1)) + ε * sErr := by
  set a : ℕ → ℝ := fun M => (∫ w in Ioi ((M : ℝ) + 1), ρ w * lw w) / ((M : ℝ) + 1) with ha
  set b : ℕ → ℝ := fun M => ell (arcsin (1 / ((M : ℝ) + 1))) / ((M : ℝ) + 1) with hb
  set E0 : ℝ := E + K * (ell (π / 2) - ell (arcsin (1 / ξ))) + ε * (lw ξ / ξ + 3 * ξ / (ξ ^ 2 - 1)) with hE0
  set d : ℕ → ℝ := fun M => (if M = 0 then E0 else 0) + ε * ((Real.log ((M : ℝ) + 1) + 4) / ((M : ℝ) + 1) ^ 2)
    with hd
  -- the mode bounds
  have hmode : ∀ M : ℕ, |a M - K * b M| ≤ d M := by
    intro M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp only [ha, hb, hd, Nat.cast_zero, zero_add, div_one, ite_true, Real.log_one]
      have hg : IntegrableOn (fun w => ρ w * lw w) (Ioi 1) := integrableOn_mul_lw hρc hρ0 hρC le_rfl
      rw [integral_Ioi_one_split hg hξ.le, arcsin_one]
      have hedge0 : 0 ≤ ∫ w in Ioc 1 ξ, ρ w * lw w :=
        setIntegral_nonneg measurableSet_Ioc fun w hw => mul_nonneg (hρ0 w hw.1) (lw_nonneg hw.1)
      have htail := abs_tail_lw_le hξ hε hρc hρ0 hρC fun x hx => hlaw x (by linarith)
      have e : (∫ w in Ioc 1 ξ, ρ w * lw w) + (∫ w in Ioi ξ, ρ w * lw w) - K * ell (π / 2)
          = (∫ w in Ioc 1 ξ, ρ w * lw w) - K * (ell (π / 2) - ell (arcsin (1 / ξ)))
            + ((∫ w in Ioi ξ, ρ w * lw w) - K * ell (arcsin (1 / ξ))) := by ring
      rw [e]
      have hdiff : 0 ≤ ell (π / 2) - ell (arcsin (1 / ξ)) := by
        have h := intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_neg_log_sin 0
          (arcsin (1 / ξ))) (intervalIntegrable_neg_log_sin (arcsin (1 / ξ)) (π / 2))
        have hle : arcsin (1 / ξ) ≤ π / 2 := arcsin_le_pi_div_two _
        have hβ0 : 0 < arcsin (1 / ξ) := arcsin_pos.mpr (by have : 0 < ξ := by linarith
                                                            positivity)
        have : 0 ≤ ∫ v in (arcsin (1 / ξ))..(π / 2), -Real.log (sin (2 * v)) := by
          rw [intervalIntegral.integral_of_le hle]
          refine setIntegral_nonneg_ae measurableSet_Ioc (ae_of_all _ fun v hv => ?_)
          rcases eq_or_lt_of_le hv.2 with h' | h'
          · rw [h', show 2 * (π / 2) = π by ring, sin_pi, Real.log_zero, neg_zero]
          · exact neg_log_sin_nonneg (lt_trans hβ0 hv.1) h'
        unfold ell; linarith
      have hKd := mul_nonneg hK hdiff
      have h1 : |(∫ w in Ioc 1 ξ, ρ w * lw w) - K * (ell (π / 2) - ell (arcsin (1 / ξ)))|
          ≤ E + K * (ell (π / 2) - ell (arcsin (1 / ξ))) := by
        rw [abs_le]; constructor <;> linarith
      have h4 : 0 ≤ ε * (4 / 1 ^ 2) := by positivity
      calc _ ≤ |(∫ w in Ioc 1 ξ, ρ w * lw w) - K * (ell (π / 2) - ell (arcsin (1 / ξ)))|
            + |(∫ w in Ioi ξ, ρ w * lw w) - K * ell (arcsin (1 / ξ))| := abs_add_le _ _
        _ ≤ E0 + ε * (4 / 1 ^ 2) := by rw [hE0]; linarith
    · have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
      set Y : ℝ := (M : ℝ) + 1 with hY
      have hY2 : 2 ≤ Y := by linarith
      have hY0 : 0 < Y := by linarith
      simp only [ha, hb, hd, ite_eq_right (Nat.pos_iff_ne_zero.mp hM), zero_add]
      have htail := abs_tail_lw_le (by linarith : 1 < Y) hε hρc hρ0 hρC fun x hx => hlaw x (by linarith)
      have hlw : lw Y ≤ Real.log Y := lw_le_log hY2
      have h3 : 3 * Y / (Y ^ 2 - 1) ≤ 4 / Y := by
        rw [div_le_div_iff₀ (by nlinarith) hY0]; nlinarith
      have e : (∫ w in Ioi Y, ρ w * lw w) / Y - K * (ell (arcsin (1 / Y)) / Y)
          = ((∫ w in Ioi Y, ρ w * lw w) - K * ell (arcsin (1 / Y))) / Y := by field_simp
      rw [e, abs_div, abs_of_pos hY0, div_le_iff₀ hY0]
      calc _ ≤ ε * (lw Y / Y + 3 * Y / (Y ^ 2 - 1)) := htail
        _ ≤ ε * (Real.log Y / Y + 4 / Y) := by gcongr
        _ = ε * ((Real.log Y + 4) / Y ^ 2) * Y := by field_simp
  have hite : Summable fun M : ℕ => (if M = 0 then E0 else 0) := (hasSum_ite_eq 0 E0).summable
  have hsd : Summable d := hite.add (summable_err.mul_left ε)
  have hsb : Summable b := summable_sArch
  have hsa' : Summable fun M => a M - K * b M :=
    Summable.of_norm_bounded hsd fun M => by rw [Real.norm_eq_abs]; exact hmode M
  have hsa : Summable a := by simpa using hsa'.add (hsb.mul_left K)
  refine ⟨hsa, ?_⟩
  have e : ∑' M : ℕ, a M - K * sArch = ∑' M : ℕ, (a M - K * b M) := by
    rw [hsa.tsum_sub (hsb.mul_left K), tsum_mul_left]; rfl
  rw [e]
  have hdsum : ∑' M : ℕ, d M = E0 + ε * sErr := by
    rw [hd, hite.tsum_add (summable_err.mul_left ε), tsum_ite_eq, tsum_mul_left]
    rfl
  calc |∑' M : ℕ, (a M - K * b M)| ≤ ∑' M : ℕ, d M := by
        rw [← Real.norm_eq_abs]
        exact tsum_of_norm_bounded hsd.hasSum fun M => by rw [Real.norm_eq_abs]; exact hmode M
    _ = _ := by rw [hdsum]

/-! ### The edge of a radial solution -/

section Radial

open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.ExteriorMassEdgeLayer Cvs.Prolate.ExteriorMassArcsineFinite

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}
    (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
include hψ hv hode

/-- **The envelope**: past `ξ₀`, `ψ² ≤ (G₀F/√(c² − χ))·rr`. -/
theorem sq_le_env (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {ξ₀ t : ℝ} (h1 : 1 < ξ₀) (ht : ξ₀ ≤ t)
    (hW : wP c χ ξ₀ < 2) :
    ψ t ^ 2 ≤ enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / √(c ^ 2 - χ) * rr t := by
  have ht1 : 1 < t := lt_of_lt_of_le h1 ht
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos ht1 hc2 hχ
  have hE := (enG_bounds hψ hv hode hc hχ0 hχ h1 ht hW).2
  have hG : aP c χ t * ψ t ^ 2 ≤ enG c χ ψ v t := by
    unfold enG Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy
    have : 0 ≤ (pP t * v t) ^ 2 / aP c χ t := by positivity
    linarith
  have hia := Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.inv_a_le ht1 hc hχ0 hχ
  have hF0 := fac_pos h1 hc hχ hW
  have hG0 := enG_nonneg h1 hc hχ (ψ := ψ) (v := v)
  have hs : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr (by linarith)
  have h2 : ψ t ^ 2 ≤ enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ * (1 / aP c χ t) := by
    rw [mul_one_div, le_div_iff₀ ha]; linarith
  calc ψ t ^ 2 ≤ enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ * (1 / aP c χ t) := h2
    _ ≤ enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ * (1 / (√(c ^ 2 - χ) * (t * √(t ^ 2 - 1)))) :=
        mul_le_mul_of_nonneg_left hia (by positivity)
    _ = _ := by unfold rr; field_simp

omit hv hode in
theorem continuousOn_sq : ContinuousOn (fun t => ψ t ^ 2) (Ioi 1) := fun t ht =>
  ((hψ t (Set.mem_Ici.mpr (le_of_lt ht))).continuousAt.pow 2).continuousWithinAt

theorem sq_le_edge (hχ : χ < c ^ 2) {t : ℝ} (ht : 1 ≤ t) : ψ t ^ 2 ≤ ψ 1 ^ 2 :=
  Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge hχ ⟨ht, le_rfl⟩ (fun r hr => hψ r hr.1) (fun r hr => hv r hr.1)
    (fun r hr => hode r hr.1)

/-- **Domination by the arcsine density** on `(1, ∞)`. -/
theorem sq_le_mul_rr (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {ξ₀ : ℝ} (h1 : 1 < ξ₀)
    (hW : wP c χ ξ₀ < 2) {t : ℝ} (ht : 1 < t) :
    ψ t ^ 2 ≤ (ψ 1 ^ 2 * (ξ₀ * √(ξ₀ ^ 2 - 1))
      + enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / √(c ^ 2 - χ)) * rr t := by
  have hF0 := fac_pos h1 hc hχ hW
  have hG0 := enG_nonneg h1 hc hχ (ψ := ψ) (v := v)
  have hr := rr_pos ht
  have hC2 : 0 ≤ enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / √(c ^ 2 - χ) := by positivity
  have hξ0 : 0 < ξ₀ := by linarith
  have hC1 : 0 ≤ ψ 1 ^ 2 * (ξ₀ * √(ξ₀ ^ 2 - 1)) := by positivity
  rcases le_or_gt ξ₀ t with h | h
  · have := sq_le_env hψ hv hode hc hχ0 hχ h1 h hW
    nlinarith
  · have hE := sq_le_edge hψ hv hode hχ ht.le
    have ht0 : 0 < t := by linarith
    have hB : 0 < t ^ 2 - 1 := by nlinarith
    have hmono : t * √(t ^ 2 - 1) ≤ ξ₀ * √(ξ₀ ^ 2 - 1) :=
      mul_le_mul h.le (sqrt_le_sqrt (by nlinarith)) (sqrt_nonneg _) (by linarith)
    have hone : 1 ≤ ξ₀ * √(ξ₀ ^ 2 - 1) * rr t := by
      unfold rr
      rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
    have : ψ 1 ^ 2 ≤ ψ 1 ^ 2 * (ξ₀ * √(ξ₀ ^ 2 - 1)) * rr t := by
      rw [mul_assoc]; nlinarith [sq_nonneg (ψ 1)]
    nlinarith

omit hψ hv hode in
/-- `∫₁^{1+δ} −½ log(w − 1) = (δ/2)(1 − log δ)`. -/
theorem integral_neg_log_sub (δ : ℝ) :
    ∫ w in (1 : ℝ)..1 + δ, -(Real.log (w - 1) / 2) = δ / 2 * (1 - Real.log δ) := by
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_div,
    intervalIntegral.integral_comp_sub_right (fun w => Real.log w), sub_self, add_sub_cancel_left,
    integral_log]
  simp; ring

/-- **The edge integral**: for `ξ₀ ≤ ξ`, `ξ² ≤ 2`,
`∫_{(1, ξ]} ψ² lw ≤ ψ(1)²(δ/2)(1 − log δ) + (G₀F/√(c² − χ))(ℓ(π/2) − ℓ(arcsin(1/ξ)))`, `δ = ξ₀ − 1`. -/
theorem integral_edge_le (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {ξ₀ ξ : ℝ} (h1 : 1 < ξ₀)
    (hW : wP c χ ξ₀ < 2) (h0 : ξ₀ ≤ ξ) (hξ2 : ξ ^ 2 ≤ 2) :
    ∫ w in Ioc 1 ξ, ψ w ^ 2 * lw w
      ≤ ψ 1 ^ 2 * ((ξ₀ - 1) / 2 * (1 - Real.log (ξ₀ - 1)))
        + enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / √(c ^ 2 - χ)
          * (ell (π / 2) - ell (arcsin (1 / ξ))) := by
  set Cenv := enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / √(c ^ 2 - χ) with hCenv
  have hF0 := fac_pos h1 hc hχ hW
  have hG0 := enG_nonneg h1 hc hχ (ψ := ψ) (v := v)
  have hCe : 0 ≤ Cenv := by positivity
  have hρC := fun t (ht : 1 < t) => sq_le_mul_rr hψ hv hode hc hχ0 hχ h1 hW ht
  have hρc := continuousOn_sq hψ (ψ := ψ)
  have hρ0 : ∀ w, 1 < w → 0 ≤ ψ w ^ 2 := fun w _ => sq_nonneg _
  have hg : IntegrableOn (fun w => ψ w ^ 2 * lw w) (Ioi 1) := integrableOn_mul_lw hρc hρ0 hρC le_rfl
  have hξ1 : 1 < ξ := lt_of_lt_of_le h1 h0
  -- split at `ξ₀`
  have hsplit : ∫ w in Ioc 1 ξ, ψ w ^ 2 * lw w
      = (∫ w in Ioc 1 ξ₀, ψ w ^ 2 * lw w) + ∫ w in Ioc ξ₀ ξ, ψ w ^ 2 * lw w := by
    rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hg.mono_set (Ioc_subset_Ioi_self)) (hg.mono_set (fun x hx => lt_trans h1 hx.1)),
      Ioc_union_Ioc_eq_Ioc h1.le h0]
  rw [hsplit]
  -- the inner layer
  have hlogI : IntegrableOn (fun w => -(Real.log (w - 1) / 2)) (Ioc 1 ξ₀) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := 1 - 1) (b := ξ₀ - 1)).comp_sub_right 1
    simp only [sub_add_cancel] at h
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le h1.le).mp ((h.div_const 2).neg))
  have hin : ∫ w in Ioc 1 ξ₀, ψ w ^ 2 * lw w ≤ ψ 1 ^ 2 * ((ξ₀ - 1) / 2 * (1 - Real.log (ξ₀ - 1))) := by
    have hle : ∫ w in Ioc 1 ξ₀, ψ w ^ 2 * lw w ≤ ∫ w in Ioc 1 ξ₀, ψ 1 ^ 2 * -(Real.log (w - 1) / 2) := by
      refine setIntegral_mono_on (hg.mono_set Ioc_subset_Ioi_self) (hlogI.const_mul _) measurableSet_Ioc
        fun w hw => ?_
      have hw1 : 1 < w := hw.1
      have hw2 : w ^ 2 ≤ 2 := by nlinarith [hw.2]
      exact mul_le_mul (sq_le_edge hψ hv hode hχ hw1.le) (lw_le_edge hw1 hw2) (lw_nonneg hw1)
        (sq_nonneg _)
    refine hle.trans (le_of_eq ?_)
    rw [integral_const_mul, ← intervalIntegral.integral_of_le h1.le,
      show ξ₀ = 1 + (ξ₀ - 1) by ring, integral_neg_log_sub]
    ring_nf
  -- the outer layer
  have hout : ∫ w in Ioc ξ₀ ξ, ψ w ^ 2 * lw w ≤ Cenv * (ell (π / 2) - ell (arcsin (1 / ξ))) := by
    have hrl := integrableOn_rr_lw (le_refl (1 : ℝ))
    have hle : ∫ w in Ioc ξ₀ ξ, ψ w ^ 2 * lw w ≤ ∫ w in Ioc ξ₀ ξ, Cenv * (rr w * lw w) := by
      refine setIntegral_mono_on (hg.mono_set fun x (hx : x ∈ Ioc ξ₀ ξ) => lt_trans h1 hx.1)
        ((hrl.mono_set fun x (hx : x ∈ Ioc ξ₀ ξ) => lt_trans h1 hx.1).const_mul _) measurableSet_Ioc fun w hw => ?_
      have hw1 : 1 < w := lt_trans h1 hw.1
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (sq_le_env hψ hv hode hc hχ0 hχ h1 hw.1.le hW) (lw_nonneg hw1)
    refine hle.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hCe
    have hsub : ∫ w in Ioc ξ₀ ξ, rr w * lw w ≤ ∫ w in Ioc 1 ξ, rr w * lw w :=
      setIntegral_mono_set (hrl.mono_set Ioc_subset_Ioi_self)
        (ae_restrict_of_forall_mem measurableSet_Ioc fun w hw => mul_nonneg (rr_pos hw.1).le (lw_nonneg hw.1))
        (Eventually.of_forall (Ioc_subset_Ioc_left h1.le))
    have heq : ∫ w in Ioc 1 ξ, rr w * lw w = ell (π / 2) - ell (arcsin (1 / ξ)) := by
      have h := integral_Ioi_one_split hrl hξ1.le
      rw [integral_rr_lw le_rfl, integral_rr_lw hξ1.le, div_one, arcsin_one] at h
      linarith
    linarith
  linarith

end Radial

/-! ### Limits at the reference point `ξ₀ = √(1 + √c/c²)` -/

open Cvs.Prolate.ArcsineLawErrorSizes in
/-- `c δ (1 − log δ) → 0` for `δ = ξ₀ − 1`. -/
theorem tendsto_edge :
    Tendsto (fun c => c * (xiAt c √c - 1) * (1 - Real.log (xiAt c √c - 1))) atTop (𝓝 0) := by
  have hg : Tendsto (fun t : ℝ => (1 + Real.log 3) / 2 * t⁻¹ + 3 / 2 * (Real.log t / t)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.const_mul ((1 + Real.log 3) / 2)).add (tendsto_log_div.const_mul (3 / 2))
    simpa using h
  refine squeeze_zero' ?_ ?_ (hg.comp tendsto_sqrt_atTop)
  · filter_upwards [eventually_ge_atTop 1] with c hc
    have hx : 0 ≤ √c / c ^ 2 := by positivity
    have hx1 : √c / c ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc √c ≤ c := by rw [sqrt_le_left (by linarith)]; nlinarith
        _ ≤ c ^ 2 := by nlinarith
    have hδ0 : 0 ≤ xiAt c √c - 1 := by have := one_le_xiAt (c := c) (sqrt_nonneg c); linarith
    have hδ1 : xiAt c √c - 1 ≤ 1 := by
      unfold xiAt; have : √(1 + √c / c ^ 2) ≤ 2 := by rw [sqrt_le_left (by norm_num)]; linarith
      linarith
    have hl : Real.log (xiAt c √c - 1) ≤ 0 := Real.log_nonpos hδ0 hδ1
    have : 0 ≤ 1 - Real.log (xiAt c √c - 1) := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop 1] with c hc
    obtain ⟨t, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ c = t ^ 2 := ⟨√c, by simpa using sqrt_le_sqrt hc, (sq_sqrt (by linarith)).symm⟩
    simp only [Function.comp_apply, sqrt_sq (by linarith : (0 : ℝ) ≤ t)]
    have ht0 : 0 < t := by linarith
    set x : ℝ := t / (t ^ 2) ^ 2 with hxd
    have hxe : x = 1 / t ^ 3 := by rw [hxd]; field_simp
    have hx0 : 0 < x := by rw [hxe]; positivity
    have hx1 : x ≤ 1 := by rw [hxe, div_le_one (by positivity)]; nlinarith [pow_le_pow_left₀ zero_le_one ht 3]
    have hxi : xiAt (t ^ 2) t = √(1 + x) := rfl
    rw [hxi]
    have hup : √(1 + x) - 1 ≤ x / 2 := by
      have : √(1 + x) ≤ 1 + x / 2 := by rw [sqrt_le_left (by positivity)]; nlinarith
      linarith
    have hlo : x / 3 ≤ √(1 + x) - 1 := by
      have : 1 + x / 3 ≤ √(1 + x) := by rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
      linarith
    have hδ0 : 0 < √(1 + x) - 1 := lt_of_lt_of_le (by positivity) hlo
    have hlog : -Real.log (√(1 + x) - 1) ≤ Real.log 3 + 3 * Real.log t := by
      have h1 : Real.log (x / 3) ≤ Real.log (√(1 + x) - 1) := Real.log_le_log (by positivity) hlo
      have h2 : Real.log (x / 3) = -(Real.log 3 + 3 * Real.log t) := by
        rw [hxe, Real.log_div (by positivity) (by norm_num), one_div, Real.log_inv, Real.log_pow]; push_cast; ring
      linarith
    have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
    have hfac : 0 ≤ 1 - Real.log (√(1 + x) - 1) := by
      have := Real.log_nonpos hδ0.le (by linarith); linarith
    calc t ^ 2 * (√(1 + x) - 1) * (1 - Real.log (√(1 + x) - 1))
        ≤ t ^ 2 * (x / 2) * (1 + (Real.log 3 + 3 * Real.log t)) := by
          gcongr
          · linarith
      _ = (1 + Real.log 3) / 2 * t⁻¹ + 3 / 2 * (Real.log t / t) := by rw [hxe]; field_simp; ring

/-! ### The law for a radial family -/

open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.ExteriorMassEdgeLayer Cvs.Prolate.ExteriorMassArcsineFinite Cvs.Prolate.ArcsineLawErrorSizes in
/-- **The log-weighted arcsine law** for a family of radial solutions with `χ/c² → 0`: for all large `c`,
`Σ_{M≥1} (1/M)∫_M^∞ ψ² lw` converges and is within `η ∫_1^∞ ψ²` of `(2/π) S_A ∫_1^∞ ψ²`. -/
theorem lw_law {χ : ℝ → ℝ} {ψ v v' : ℝ → ℝ → ℝ}
    (hu : Tendsto (fun c => χ c / c ^ 2) atTop (𝓝 0))
    (hsys : ∀ᶠ c in atTop, 0 ≤ χ c ∧ (∀ r ∈ Ici (1 : ℝ), HasDerivAt (ψ c) (v c r) r) ∧
      (∀ r ∈ Ici (1 : ℝ), HasDerivAt (v c) (v' c r) r) ∧
      (∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' c r + 2 * r * v c r + (c ^ 2 * r ^ 2 - χ c) * ψ c r = 0) ∧
      IntegrableOn (fun t => ψ c t ^ 2) (Ioi 1))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c in atTop, Summable (fun M : ℕ => (∫ w in Ioi ((M : ℝ) + 1), ψ c w ^ 2 * lw w) / ((M : ℝ) + 1)) ∧
      |∑' M : ℕ, (∫ w in Ioi ((M : ℝ) + 1), ψ c w ^ 2 * lw w) / ((M : ℝ) + 1)
        - 2 / π * (∫ t in Ioi 1, ψ c t ^ 2) * sArch| ≤ η * ∫ t in Ioi 1, ψ c t ^ 2 := by
  have hπ := pi_pos
  -- the cut `ξs`, independent of `c`
  have hcont : Tendsto (fun ξ : ℝ => ell (arcsin (1 / ξ))) (𝓝[>] 1) (𝓝 (ell (π / 2))) := by
    have h : ContinuousAt (fun ξ : ℝ => ell (arcsin (1 / ξ))) 1 :=
      continuous_ell.continuousAt.comp (continuous_arcsin.continuousAt.comp
        (continuousAt_const.div continuousAt_id one_ne_zero))
    have h2 := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    simpa [arcsin_one] using h2
  have hsq : ∀ᶠ ξ in 𝓝[>] (1 : ℝ), ξ ^ 2 < 2 := by
    have h : ContinuousAt (fun ξ : ℝ => ξ ^ 2) 1 := by fun_prop
    exact (h.tendsto.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) ^ 2 < 2))).filter_mono nhdsWithin_le_nhds
  have hclose := Metric.tendsto_nhds.mp hcont (η / 8) (by positivity)
  obtain ⟨ξs, hξs1, hξs2, hξsd⟩ := ((eventually_mem_nhdsWithin (s := Ioi (1 : ℝ)) (a := 1)).and (hsq.and hclose)).exists
  have hξs1 : (1 : ℝ) < ξs := hξs1
  have hΔ : ell (π / 2) - ell (arcsin (1 / ξs)) ≤ η / 8 := by
    rw [Real.dist_eq] at hξsd; have := neg_abs_le (ell (arcsin (1 / ξs)) - ell (π / 2)); linarith
  set Cξ := lw ξs / ξs + 3 * ξs / (ξs ^ 2 - 1) with hCξd
  have hCξ : 0 ≤ Cξ := by
    have := lw_nonneg hξs1; have : 0 < ξs ^ 2 - 1 := by nlinarith
    rw [hCξd]; positivity
  have hsErr : 0 ≤ sErr := tsum_nonneg fun M => by
    have := Real.log_nonneg (by linarith [M.cast_nonneg (α := ℝ)] : (1 : ℝ) ≤ (M : ℝ) + 1)
    positivity
  set η' := η / (4 * (Cξ + sErr + 1)) with hη'd
  have hη' : 0 < η' := by rw [hη'd]; positivity
  have hη'C : η' * (Cξ + sErr) ≤ η / 4 := by
    rw [hη'd, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- the constants
  have hden : Tendsto (fun c => π / 2 * lowL c (χ c) (xiAt c √c) - errE c (χ c) (xiAt c √c)) atTop
      (𝓝 (π / 2 * 1 - 0)) := ((tendsto_lowL hu).const_mul (π / 2)).sub (tendsto_errE hu)
  rw [mul_one, sub_zero] at hden
  have hκ : Tendsto (fun c => 2 * (c / √(c ^ 2 - χ c)) * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c (χ c) (xiAt c √c)
      / (π / 2 * lowL c (χ c) (xiAt c √c) - errE c (χ c) (xiAt c √c))) atTop (𝓝 (2 * 1 * 1 / (π / 2))) :=
    (((tendsto_c_div_sigma hu).const_mul 2).mul (tendsto_fac_ref hu)).div hden (by positivity)
  have hκ2 : 2 * 1 * 1 / (π / 2) < 2 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_gt_three]
  have hE : Tendsto (fun c => kEdge c (χ c) (xiAt c 1) * (c * (xiAt c √c - 1) * (1 - Real.log (xiAt c √c - 1)))
      / (π / 2 * lowL c (χ c) (xiAt c √c) - errE c (χ c) (xiAt c √c))) atTop (𝓝 (4 * exp 1 * 0 / (π / 2))) :=
    ((tendsto_kEdge hu).mul tendsto_edge).div hden (by positivity)
  rw [mul_zero, zero_div] at hE
  have hχ0e : ∀ᶠ c in atTop, 0 ≤ χ c := hsys.mono fun c h => h.1
  filter_upwards [Cvs.Prolate.ModeEnergyArcsineLaw.arcsine_law hu hsys hη', hsys, eventually_hyps hu hχ0e,
    (tendsto_xiAt tendsto_sqrt_div_sq).eventually (gt_mem_nhds hξs1), hκ.eventually (gt_mem_nhds hκ2),
    hE.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 4))]
    with c hA ⟨_, hψ, hv, hode, hint⟩ ⟨hc, hχ0, hχ, hb1, hb0, ha4, hWb, hW, hdn⟩ hξ0s hκc hEc
  set T1 := ∫ t in Ioi 1, ψ c t ^ 2 with hT1d
  have hT1 : 0 ≤ T1 := setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  set ξ₀ := xiAt c √c with hξ₀d
  have h1 : 1 < ξ₀ := lt_of_lt_of_le hb1 hb0
  set den := π / 2 * lowL c (χ c) ξ₀ - errE c (χ c) ξ₀ with hdend
  have hden0 : 0 < den := by rw [hdend]; linarith
  set G₀ := enG c (χ c) (ψ c) (v c) ξ₀ with hG₀d
  set F := Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c (χ c) ξ₀ with hFd
  have hF0 : 0 < F := fac_pos h1 hc hχ hW
  have hG0 : 0 ≤ G₀ := enG_nonneg h1 hc hχ
  have hs : 0 < √(c ^ 2 - χ c) := sqrt_pos.mpr (by linarith)
  have hG : G₀ ≤ 2 * c * T1 / den := Cvs.L2a.PoleChannelNegligible.enG_le_mass hψ hv hode hint hc hχ0 hχ h1 hW hdn
  have hψ1 : ψ c 1 ^ 2 ≤ kEdge c (χ c) (xiAt c 1) * G₀ := by
    have h := Cvs.Prolate.Envelope.EdgeValueSoninBound.edge_le_energy hc hχ0 hχ (ξ₁ := ξ₀) (fun r hr => hψ r hr.1)
      (fun r hr => hv r hr.1) (fun r hr => hode r hr.1) hb1 hb0 le_rfl ha4 hWb
    unfold kEdge; rw [hG₀d]; unfold enG; exact h
  have hkE : 0 ≤ kEdge c (χ c) (xiAt c 1) := by
    have hFb := fac_pos hb1 hc hχ hWb
    have hab := aP_pos hb1 (by positivity : 0 < c ^ 2) hχ
    have : 0 < 1 - pP (xiAt c 1) * qP c (χ c) (xiAt c 1) / 4 := by linarith
    unfold kEdge; positivity
  -- the edge bound
  set δ := ξ₀ - 1 with hδd
  have hδ0 : 0 < δ := by rw [hδd]; linarith
  have hδ1 : δ ≤ 1 := by
    have : ξs < 2 := by nlinarith
    rw [hδd]; linarith
  have hfac0 : 0 ≤ δ / 2 * (1 - Real.log δ) := by
    have := Real.log_nonpos hδ0.le hδ1; have : 0 ≤ 1 - Real.log δ := by linarith
    positivity
  have hξs2' : ξs ^ 2 ≤ 2 := hξs2.le
  have hedge := integral_edge_le hψ hv hode hc hχ0 hχ h1 hW hξ0s.le hξs2'
  set Cenv := G₀ * F / √(c ^ 2 - χ c) with hCenvd
  have hCenv0 : 0 ≤ Cenv := by positivity
  have hCenv : Cenv ≤ 2 * T1 := by
    have h2 : Cenv ≤ 2 * c * T1 / den * F / √(c ^ 2 - χ c) := by
      rw [hCenvd]; gcongr
    refine h2.trans ?_
    have e : 2 * c * T1 / den * F / √(c ^ 2 - χ c)
        = T1 * (2 * (c / √(c ^ 2 - χ c)) * F / den) := by field_simp
    rw [e]
    have : 2 * (c / √(c ^ 2 - χ c)) * F / den < 2 := hκc
    calc T1 * (2 * (c / √(c ^ 2 - χ c)) * F / den) ≤ T1 * 2 := mul_le_mul_of_nonneg_left this.le hT1
      _ = 2 * T1 := by ring
  have hEdge0 : ψ c 1 ^ 2 * (δ / 2 * (1 - Real.log δ)) ≤ T1 * (η / 4) := by
    have h2 : ψ c 1 ^ 2 * (δ / 2 * (1 - Real.log δ))
        ≤ kEdge c (χ c) (xiAt c 1) * (2 * c * T1 / den) * (δ / 2 * (1 - Real.log δ)) :=
      mul_le_mul_of_nonneg_right (hψ1.trans (mul_le_mul_of_nonneg_left hG hkE)) hfac0
    refine h2.trans ?_
    have e : kEdge c (χ c) (xiAt c 1) * (2 * c * T1 / den) * (δ / 2 * (1 - Real.log δ))
        = T1 * (kEdge c (χ c) (xiAt c 1) * (c * δ * (1 - Real.log δ)) / den) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hEc.le hT1
  have hEdge : ∫ w in Ioc 1 ξs, ψ c w ^ 2 * lw w ≤ T1 * (η / 4) + 2 * T1 * (η / 8) := by
    refine hedge.trans ?_
    have : Cenv * (ell (π / 2) - ell (arcsin (1 / ξs))) ≤ 2 * T1 * (η / 8) :=
      (mul_le_mul_of_nonneg_left hΔ hCenv0).trans (mul_le_mul_of_nonneg_right hCenv (by positivity))
    linarith
  -- the sum
  have hlaw : ∀ x, 1 ≤ x → |(∫ t in Ioi x, ψ c t ^ 2) - 2 / π * T1 * arcsin (1 / x)| ≤ η' * T1 / x :=
    fun x hx => by
      have := hA x hx
      rwa [show 2 / π * arcsin (1 / x) * T1 = 2 / π * T1 * arcsin (1 / x) by ring] at this
  have hmain := abs_sum_lw_sub_le (ρ := fun w => ψ c w ^ 2) (K := 2 / π * T1) (ε := η' * T1) hξs1
    (by positivity) (by positivity) (continuousOn_sq hψ) (fun w _ => sq_nonneg _)
    (fun t ht => sq_le_mul_rr hψ hv hode hc hχ0 hχ h1 hW ht) hlaw hEdge
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  have hK : 2 / π * T1 * (ell (π / 2) - ell (arcsin (1 / ξs))) ≤ T1 * (η / 8) := by
    have h2 : 2 / π ≤ 1 := by rw [div_le_one hπ]; linarith [pi_gt_three]
    calc 2 / π * T1 * (ell (π / 2) - ell (arcsin (1 / ξs))) ≤ 2 / π * T1 * (η / 8) :=
          mul_le_mul_of_nonneg_left hΔ (by positivity)
      _ ≤ 1 * T1 * (η / 8) := by gcongr
      _ = T1 * (η / 8) := by ring
  have hε : η' * T1 * Cξ + η' * T1 * sErr ≤ T1 * (η / 4) := by
    have := mul_le_mul_of_nonneg_left hη'C hT1
    have e : η' * T1 * Cξ + η' * T1 * sErr = T1 * (η' * (Cξ + sErr)) := by ring
    rw [e]; exact this
  have e2 : T1 * (η / 4) + 2 * T1 * (η / 8) + 2 / π * T1 * (ell (π / 2) - ell (arcsin (1 / ξs)))
      + η' * T1 * (lw ξs / ξs + 3 * ξs / (ξs ^ 2 - 1)) + η' * T1 * sErr
      = T1 * (η / 4) + 2 * T1 * (η / 8) + 2 / π * T1 * (ell (π / 2) - ell (arcsin (1 / ξs)))
      + (η' * T1 * Cξ + η' * T1 * sErr) := by rw [hCξd]; ring
  rw [e2]
  have e3 : η * T1 = T1 * (η / 4) + 2 * T1 * (η / 8) + T1 * (η / 8) + T1 * (η / 4) + T1 * (η / 8) := by ring
  rw [e3]
  have : 0 ≤ T1 * (η / 8) := by positivity
  linarith

/-! ### The rungs -/

/-- The local-frequency arch sum `Σ_{M≥1} (1/M)∫_M^∞ Φ² lw`. -/
def archLoc (Φ : ℝ → ℝ) : ℝ := ∑' M : ℕ, (∫ w in Ioi ((M : ℝ) + 1), Φ w ^ 2 * lw w) / ((M : ℝ) + 1)

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex in
/-- **The log-weighted arcsine law for the rung of index `j`**: if `0 ≤ χ_j ≤ Kc` eventually, then for all large
`c`, `|Σ_{M≥1} (1/M)∫_M^∞ ψ_j² lw − (2/c)(1 − λ_j) S_A| ≤ η (π/c)(1 − λ_j)`, the sum converging. -/
theorem archLoc_law_rung {j : ℕ} {K : ℝ}
    (hlev : ∀ᶠ c : ℝ in atTop, (∃ χ, IsLevelIdx c j χ) ∧ 0 ≤ lev c j ∧ lev c j ≤ K * c)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop,
      Summable (fun M : ℕ => (∫ w in Ioi ((M : ℝ) + 1), psi c (rung c j) w ^ 2 * lw w) / ((M : ℝ) + 1)) ∧
      |archLoc (psi c (rung c j)) - 2 / c * (1 - lamR c j) * sArch| ≤ η * (π / c * (1 - lamR c j)) := by
  have hu := Cvs.Prolate.ModeEnergyArcsineLaw.tendsto_lev_div_sq (hlev.mono fun c h => h.2)
  have hsys : ∀ᶠ c in atTop, 0 ≤ lev c j ∧
      (∀ r ∈ Ici (1 : ℝ), HasDerivAt (psi c (rung c j))
        (Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c * s * sin (c * ξ * s))) r) r) ∧
      (∀ r ∈ Ici (1 : ℝ), HasDerivAt (Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c * s * sin (c * ξ * s))))
        (Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) r) r) ∧
      (∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * Cvs.Prolate.SlepianCommutingRelation.kint (rung c j)
          (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) r
        + 2 * r * Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c * s * sin (c * ξ * s))) r
        + (c ^ 2 * r ^ 2 - lev c j) * psi c (rung c j) r = 0) ∧
      IntegrableOn (fun t => psi c (rung c j) t ^ 2) (Ioi 1) := by
    filter_upwards [hlev, eventually_gt_atTop 0] with c h hc
    exact ⟨h.2.1, Cvs.Prolate.ModeEnergyArcsineLaw.rung_sys hc h.1⟩
  filter_upwards [lw_law (ψ := fun c => psi c (rung c j)) hu hsys hη, hlev, eventually_gt_atTop 0]
    with c hL h hc
  obtain ⟨-, -, -, -, heven, hnorm⟩ := rung_spec h.1
  have hmass : ∫ t in Ioi 1, psi c (rung c j) t ^ 2 = π / c * (1 - lamR c j) :=
    Cvs.Prolate.AngularBesselInequality.mass_eq hc (continuousOn_rung h.1) heven (psi_rung h.1) hnorm
  refine ⟨hL.1, ?_⟩
  have h2 := hL.2
  rw [hmass] at h2
  have e : 2 / π * (π / c * (1 - lamR c j)) * sArch = 2 / c * (1 - lamR c j) * sArch := by
    field_simp
  rw [e] at h2
  exact h2

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex in
/-- **The log-weighted arcsine law for `h₀`, `h₄`, `h₈`**, with no hypotheses. -/
theorem archLoc_law_even {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop,
      Summable (fun M : ℕ => (∫ w in Ioi ((M : ℝ) + 1), psi c (rung c j) w ^ 2 * lw w) / ((M : ℝ) + 1)) ∧
      |archLoc (psi c (rung c j)) - 2 / c * (1 - lamR c j) * sArch| ≤ η * (π / c * (1 - lamR c j)) :=
  archLoc_law_rung (Cvs.Prolate.ModeEnergyArcsineLaw.hlev_even hj).choose_spec hη

/-! ### The prime diagonal -/

/-- `Σ_{M≥1} log M/M²`. -/
def sLog : ℝ := ∑' M : ℕ, Cvs.L2a.PrimeChannelDiagonalSplit.wLog M / ((M : ℝ) + 1)

theorem sLog_nonneg : 0 ≤ sLog :=
  tsum_nonneg fun M => div_nonneg (Cvs.L2a.PrimeChannelDiagonalSplit.wLog_nonneg M) (by positivity)

/-- **The log-weighted mode sum**: if `|T(M) − K arcsin(1/M)| ≤ e/M` for every `M ≥ 1`, then
`Σ_M log M · T(M)/M` converges and is within `e Σ_M log M/M²` of `K S₁`. -/
theorem modeSum_wLog_le {T : ℝ → ℝ} {K e : ℝ}
    (hlaw : ∀ M : ℕ, |T ((M : ℝ) + 1) - K * arcsin (1 / ((M : ℝ) + 1))| ≤ e / ((M : ℝ) + 1)) :
    Summable (fun M : ℕ => Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * T ((M : ℝ) + 1)) ∧
      |∑' M : ℕ, Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * T ((M : ℝ) + 1) - K * sOne| ≤ e * sLog := by
  have hdiff : ∀ M : ℕ, |Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * T ((M : ℝ) + 1)
      - K * (Real.log ((M : ℝ) + 1) * arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1))|
        ≤ e * (Cvs.L2a.PrimeChannelDiagonalSplit.wLog M / ((M : ℝ) + 1)) := by
    intro M
    have hM : (0 : ℝ) < M + 1 := by positivity
    have hw := Cvs.L2a.PrimeChannelDiagonalSplit.wLog_nonneg M
    have e1 : Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * T ((M : ℝ) + 1)
        - K * (Real.log ((M : ℝ) + 1) * arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1))
        = Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * (T ((M : ℝ) + 1) - K * arcsin (1 / ((M : ℝ) + 1))) := by
      unfold Cvs.L2a.PrimeChannelDiagonalSplit.wLog; ring
    rw [e1, abs_mul, abs_of_nonneg hw]
    calc Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * |T ((M : ℝ) + 1) - K * arcsin (1 / ((M : ℝ) + 1))|
        ≤ Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * (e / ((M : ℝ) + 1)) := mul_le_mul_of_nonneg_left (hlaw M) hw
      _ = e * (Cvs.L2a.PrimeChannelDiagonalSplit.wLog M / ((M : ℝ) + 1)) := by ring
  have hs2 := summable_sOne.mul_left K
  have hsE := Cvs.L2a.PrimeChannelDiagonalSplit.summable_wLog_div.mul_left e
  have hsd := Summable.of_norm_bounded hsE (fun M => by rw [Real.norm_eq_abs]; exact hdiff M)
  have hsT : Summable (fun M : ℕ => Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * T ((M : ℝ) + 1)) := by
    simpa using hsd.add hs2
  refine ⟨hsT, ?_⟩
  have e2 : ∑' M : ℕ, Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * T ((M : ℝ) + 1) - K * sOne
      = ∑' M : ℕ, (Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * T ((M : ℝ) + 1)
        - K * (Real.log ((M : ℝ) + 1) * arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1))) := by
    rw [hsT.tsum_sub hs2, tsum_mul_left]; rfl
  rw [e2]
  calc _ ≤ ∑' M : ℕ, e * (Cvs.L2a.PrimeChannelDiagonalSplit.wLog M / ((M : ℝ) + 1)) := by
        rw [← Real.norm_eq_abs]
        exact tsum_of_norm_bounded hsE.hasSum (fun M => by rw [Real.norm_eq_abs]; exact hdiff M)
    _ = e * sLog := by rw [tsum_mul_left]; rfl

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex in
/-- **The prime diagonal of `h₀`, `h₄`, `h₈`**: `Σ_{M≥1} log M · (1/M)∫_M^∞ ψ_j² = (2/c)(1 − λ_j) S₁ + o((1 − λ_j)/c)`. -/
theorem primeDiag_law_even {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop,
      Summable (fun M : ℕ => Cvs.L2a.PrimeChannelDiagonalSplit.wLog M * ∫ t in Ioi ((M : ℝ) + 1), psi c (rung c j) t ^ 2) ∧
      |Cvs.L2a.PrimeChannelDiagonalSplit.primeDiag (psi c (rung c j)) - 2 / c * (1 - lamR c j) * sOne|
        ≤ η * (π / c * (1 - lamR c j)) := by
  have hS : 0 < sLog + 1 := by linarith [sLog_nonneg]
  filter_upwards [Cvs.Prolate.ModeEnergyArcsineLaw.arcsine_law_even hj (div_pos hη hS)] with c hA
  have h := modeSum_wLog_le (T := fun Y => ∫ t in Ioi Y, psi c (rung c j) t ^ 2) (K := 2 / c * (1 - lamR c j))
    (e := η / (sLog + 1) * (π / c * (1 - lamR c j)))
    (fun M => hA _ (by linarith [M.cast_nonneg (α := ℝ)]))
  refine ⟨h.1, ?_⟩
  unfold Cvs.L2a.PrimeChannelDiagonalSplit.primeDiag Cvs.L2a.AdmixtureNegligibleModes.modeSum
  refine h.2.trans ?_
  have h3 : 0 ≤ η / (sLog + 1) * (π / c * (1 - lamR c j)) := by
    have := le_trans (abs_nonneg _) (hA 1 le_rfl); rwa [div_one] at this
  have hm : 0 ≤ π / c * (1 - lamR c j) := (mul_nonneg_iff_of_pos_left (div_pos hη hS)).mp h3
  calc η / (sLog + 1) * (π / c * (1 - lamR c j)) * sLog
      = η * (π / c * (1 - lamR c j)) * (sLog / (sLog + 1)) := by field_simp
    _ ≤ η * (π / c * (1 - lamR c j)) * 1 := by
        gcongr; rw [div_le_one hS]; linarith
    _ = η * (π / c * (1 - lamR c j)) := mul_one _

/-! ### The archimedean symbol at the local frequency -/

/-- The Mellin local frequency `c w²/√(w² − 1)` (`= 2c/sin 2β` at `w = 1/sin β`). -/
def nuLoc (c w : ℝ) : ℝ := c * w ^ 2 / √(w ^ 2 - 1)

theorem two_mul_le_nuLoc {c w : ℝ} (hc : 0 < c) (hw : 1 < w) : 2 * c ≤ nuLoc c w := by
  have hB : 0 < w ^ 2 - 1 := by nlinarith
  have hs := sqrt_pos.mpr hB
  have hss := sq_sqrt hB.le
  unfold nuLoc
  rw [le_div_iff₀ hs]
  nlinarith [sq_nonneg (√(w ^ 2 - 1) - 1)]

theorem log_nuLoc {c w : ℝ} (hc : 0 < c) (hw : 1 < w) : Real.log (nuLoc c w / (2 * c)) = lw w := by
  unfold nuLoc lw; congr 1; field_simp

/-- `|a(ν(w)) − log(c/π) − lw(w)| ≤ 57/(2c)` for `c ≥ 1`, `w > 1`. -/
theorem abs_archSymbol_nuLoc_le {c w : ℝ} (hc : 1 ≤ c) (hw : 1 < w) :
    |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (nuLoc c w) - Real.log (c / π) - lw w| ≤ 57 / (2 * c) := by
  have hc0 : 0 < c := by linarith
  have hν := two_mul_le_nuLoc hc0 hw
  have h := Cvs.WeilForm.Archimedean.ArchSymbolOnTail.abs_archSymbol_sub_le hc0 (by linarith : 2 ≤ nuLoc c w)
  rw [log_nuLoc hc0 hw] at h
  exact h.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hν)

theorem continuousOn_nuLoc (c : ℝ) : ContinuousOn (nuLoc c) (Ioi 1) := by
  have hf : ContinuousOn (fun w : ℝ => c * w ^ 2) (Ioi 1) := by fun_prop
  have hg : ContinuousOn (fun w : ℝ => √(w ^ 2 - 1)) (Ioi 1) := by fun_prop
  refine ContinuousOn.div (f := fun w : ℝ => c * w ^ 2) (g := fun w : ℝ => √(w ^ 2 - 1))
    hf hg fun w hw => ?_
  have hw' : (1 : ℝ) < w := hw
  exact (sqrt_pos.mpr (by nlinarith)).ne'

/-- The arch sum at the local frequency, `Σ_{M≥1} (1/M)∫_M^∞ Φ² (a(ν) − log(c/π))`. -/
def archSymLoc (c : ℝ) (Φ : ℝ → ℝ) : ℝ :=
  ∑' M : ℕ, (∫ w in Ioi ((M : ℝ) + 1), Φ w ^ 2 * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (nuLoc c w)
    - Real.log (c / π))) / ((M : ℝ) + 1)

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex in
/-- **The local-frequency arch law for `h₀`, `h₄`, `h₈`** (the weighted arcsine law of S9's Cvs.L2a.WeightedArcsineDiagonal), with no
hypotheses: `Σ_{M≥1} (1/M)∫_M^∞ ψ_j² (a(ν(w)) − log(c/π)) = (2/c)(1 − λ_j) S_A + o((1 − λ_j)/c)`, `ν = c w²/√(w² − 1)`. -/
theorem archSymLoc_law_even {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop,
      Summable (fun M : ℕ => (∫ w in Ioi ((M : ℝ) + 1), psi c (rung c j) w ^ 2
        * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (nuLoc c w) - Real.log (c / π))) / ((M : ℝ) + 1)) ∧
      |archSymLoc c (psi c (rung c j)) - 2 / c * (1 - lamR c j) * sArch| ≤ η * (π / c * (1 - lamR c j)) := by
  have hS0 := Cvs.L2a.AdmixtureNegligibleModes.sZero_pos
  have hπ := pi_pos
  set A : ℝ := 57 * (2 * Cvs.Prolate.ModeEnergyArcsineLaw.sZero / π + 1) with hAd
  have hA0 : 0 < A := by rw [hAd]; positivity
  filter_upwards [archLoc_law_even hj (half_pos hη), Cvs.Prolate.ModeEnergyArcsineLaw.modeSum_law_even hj one_pos,
    Cvs.L2a.AdmixtureNegligibleModes.eventually_summable hj, (Cvs.Prolate.ModeEnergyArcsineLaw.hlev_even hj).choose_spec,
    eventually_ge_atTop (max 1 (A / η)), Cvs.Prolate.RungEndpointMass.eventually_mul_one_sub_lamR_pos hj]
    with c hL hMS hsum h hc hpos
  have hc1 : 1 ≤ c := le_trans (le_max_left _ _) hc
  have hc0 : 0 < c := by linarith
  have hcA : A / η ≤ c := le_trans (le_max_right _ _) hc
  obtain ⟨hψd, -, -, hint⟩ := Cvs.Prolate.ModeEnergyArcsineLaw.rung_sys hc0 h.1
  set ψ := psi c (rung c j) with hψdef
  have hψc : ContinuousOn (fun t => ψ t ^ 2) (Ioi 1) := fun t ht =>
    ((hψd t (Set.mem_Ici.mpr (le_of_lt ht))).continuousAt.pow 2).continuousWithinAt
  set g : ℝ → ℝ := fun w => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (nuLoc c w) - Real.log (c / π) - lw w with hgd
  have hgc : ContinuousOn g (Ioi 1) :=
    ((Cvs.WeilForm.Archimedean.ArchFormIntegrable.continuous_archSymbol.comp_continuousOn (continuousOn_nuLoc c)).sub
      continuousOn_const).sub continuousOn_lw
  have hgb : ∀ w, 1 < w → |g w| ≤ 57 / (2 * c) := fun w hw => abs_archSymbol_nuLoc_le hc1 hw
  -- domination by the arcsine density
  obtain ⟨hg, hg₁, hg₂c, -, -, -⟩ := rung_spec h.1
  obtain ⟨B, hB⟩ := Cvs.L2a.TailNormDiagonalSplit.exists_abs_psi_le hg hg₁ hg₂c hc0
  have hdom : ∀ w, 1 < w → ψ w ^ 2 ≤ B ^ 2 * rr w := fun w hw => by
    have hw0 : 0 < w := by linarith
    have hB2 : ψ w ^ 2 ≤ (B / w) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB w hw.le) 2
    have hr : 1 / w ^ 2 ≤ rr w := by
      unfold rr
      have hB' : 0 < w ^ 2 - 1 := by nlinarith
      apply one_div_le_one_div_of_le (by positivity)
      have : √(w ^ 2 - 1) ≤ w := by rw [sqrt_le_left hw0.le]; linarith
      nlinarith [sqrt_nonneg (w ^ 2 - 1)]
    calc ψ w ^ 2 ≤ (B / w) ^ 2 := hB2
      _ = B ^ 2 * (1 / w ^ 2) := by ring
      _ ≤ B ^ 2 * rr w := mul_le_mul_of_nonneg_left hr (sq_nonneg B)
  have hρ0 : ∀ w, 1 < w → 0 ≤ ψ w ^ 2 := fun w _ => sq_nonneg _
  -- each mode
  have hmode : ∀ M : ℕ, ∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (nuLoc c w) - Real.log (c / π))
      = (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * lw w) + ∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w := by
    intro M
    have hY : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [M.cast_nonneg (α := ℝ)]
    have hsub : Ioi ((M : ℝ) + 1) ⊆ Ioi 1 := Ioi_subset_Ioi hY
    have hl : IntegrableOn (fun w => ψ w ^ 2 * lw w) (Ioi ((M : ℝ) + 1)) :=
      integrableOn_mul_lw hψc hρ0 hdom hY
    have hgi : IntegrableOn (fun w => ψ w ^ 2 * g w) (Ioi ((M : ℝ) + 1)) := by
      refine ((hint.mono_set hsub).const_mul (57 / (2 * c))).mono' (((hψc.mul hgc).mono hsub).aestronglyMeasurable
        measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hgb w (hsub hw)) (sq_nonneg _)
    rw [← integral_add hl hgi]
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    simp only [hgd]; ring
  have hrbd : ∀ M : ℕ, |(∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w) / ((M : ℝ) + 1)|
      ≤ 57 / (2 * c) * (Cvs.L2a.AdmixtureNegligibleModes.wInv M * ∫ t in Ioi ((M : ℝ) + 1), ψ t ^ 2) := by
    intro M
    have hY : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [M.cast_nonneg (α := ℝ)]
    have hsub : Ioi ((M : ℝ) + 1) ⊆ Ioi 1 := Ioi_subset_Ioi hY
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hI : |∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w| ≤ 57 / (2 * c) * ∫ t in Ioi ((M : ℝ) + 1), ψ t ^ 2 := by
      rw [← integral_const_mul, ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hint.mono_set hsub).const_mul _)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hgb w (hsub hw)) (sq_nonneg _)
    rw [abs_div, abs_of_pos hM, Cvs.L2a.AdmixtureNegligibleModes.wInv]
    calc |∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w| / ((M : ℝ) + 1)
        ≤ 57 / (2 * c) * (∫ t in Ioi ((M : ℝ) + 1), ψ t ^ 2) / ((M : ℝ) + 1) :=
          div_le_div_of_nonneg_right hI hM.le
      _ = _ := by ring
  have hsr : Summable fun M : ℕ => (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w) / ((M : ℝ) + 1) :=
    Summable.of_norm_bounded (hsum.mul_left (57 / (2 * c))) fun M => by rw [Real.norm_eq_abs]; exact hrbd M
  have hsplit : (fun M : ℕ => (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (nuLoc c w) - Real.log (c / π))) / ((M : ℝ) + 1))
      = fun M : ℕ => (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * lw w) / ((M : ℝ) + 1)
        + (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w) / ((M : ℝ) + 1) := by
    funext M; rw [hmode M, add_div]
  have hsA : Summable (fun M : ℕ => (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (nuLoc c w) - Real.log (c / π))) / ((M : ℝ) + 1)) := by
    rw [hsplit]; exact hL.1.add hsr
  refine ⟨hsA, ?_⟩
  have hsum_eq : archSymLoc c ψ = archLoc ψ
      + ∑' M : ℕ, (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w) / ((M : ℝ) + 1) := by
    unfold archSymLoc archLoc; rw [hsplit, hL.1.tsum_add hsr]
  -- the symbol error against the mode sum
  have hT1 : 0 ≤ π / c * (1 - lamR c j) := by
    have := pos_of_mul_pos_right hpos hc0.le
    exact mul_nonneg (div_nonneg pi_pos.le hc0.le) this.le
  have hrsum : |∑' M : ℕ, (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w) / ((M : ℝ) + 1)|
      ≤ η / 2 * (π / c * (1 - lamR c j)) := by
    have h1 : |∑' M : ℕ, (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w) / ((M : ℝ) + 1)|
        ≤ 57 / (2 * c) * Cvs.L2a.AdmixtureNegligibleModes.modeSum Cvs.L2a.AdmixtureNegligibleModes.wInv ψ := by
      rw [← Real.norm_eq_abs, Cvs.L2a.AdmixtureNegligibleModes.modeSum, ← tsum_mul_left]
      exact tsum_of_norm_bounded (hsum.mul_left _).hasSum fun M => by rw [Real.norm_eq_abs]; exact hrbd M
    have hms : Cvs.L2a.AdmixtureNegligibleModes.modeSum Cvs.L2a.AdmixtureNegligibleModes.wInv ψ
        ≤ (2 * Cvs.Prolate.ModeEnergyArcsineLaw.sZero / π + 1) * (π / c * (1 - lamR c j)) := by
      rw [Cvs.L2a.AdmixtureNegligibleModes.modeSum_wInv]
      have := (abs_le.mp hMS).2
      have e : 2 / c * (1 - lamR c j) * Cvs.Prolate.ModeEnergyArcsineLaw.sZero
          = 2 * Cvs.Prolate.ModeEnergyArcsineLaw.sZero / π * (π / c * (1 - lamR c j)) := by field_simp
      rw [e] at this; linarith
    refine h1.trans ?_
    calc 57 / (2 * c) * Cvs.L2a.AdmixtureNegligibleModes.modeSum Cvs.L2a.AdmixtureNegligibleModes.wInv ψ
        ≤ 57 / (2 * c) * ((2 * Cvs.Prolate.ModeEnergyArcsineLaw.sZero / π + 1) * (π / c * (1 - lamR c j))) :=
          mul_le_mul_of_nonneg_left hms (by positivity)
      _ = A / c / 2 * (π / c * (1 - lamR c j)) := by rw [hAd]; field_simp
      _ ≤ η / 2 * (π / c * (1 - lamR c j)) := by
          gcongr
          rw [div_le_iff₀ hc0]; rw [div_le_iff₀ hη] at hcA; linarith
  rw [hsum_eq]
  have e : archLoc ψ + ∑' M : ℕ, (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w) / ((M : ℝ) + 1)
      - 2 / c * (1 - lamR c j) * sArch
      = (archLoc ψ - 2 / c * (1 - lamR c j) * sArch)
        + ∑' M : ℕ, (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w) / ((M : ℝ) + 1) := by ring
  rw [e]
  calc _ ≤ |archLoc ψ - 2 / c * (1 - lamR c j) * sArch|
        + |∑' M : ℕ, (∫ w in Ioi ((M : ℝ) + 1), ψ w ^ 2 * g w) / ((M : ℝ) + 1)| := abs_add_le _ _
    _ ≤ η / 2 * (π / c * (1 - lamR c j)) + η / 2 * (π / c * (1 - lamR c j)) := add_le_add hL.2 hrsum
    _ = η * (π / c * (1 - lamR c j)) := by ring

end Cvs.L2a.WeightedArcsineDiagonal

end
