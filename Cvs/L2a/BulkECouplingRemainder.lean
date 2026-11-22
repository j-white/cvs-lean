import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityComplexWeight
import Cvs.L2a.QIdentityCutPoint
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.RungCauchySplit
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The bulk of the E-coupling as a remainder integral

At `y² < 1`, `x > 1`, `χ < c²`, `Re Q < 0`, so `QIdentityComplexWeight`'s Q-identity holds at `y = s/m`, `s ∈ [−1, 1]`, `m ≥ 2`. With
`w = 1` on each cut `[m, M]`, Fubini in `(s, t)` and linearity of the sample in the multiplier give
`bulkE = Re Σ_m Σᵢ aᵢ (1/m) ∫ g_j(s) ∫_m^M e^{icst/m} ψᵢ(t) R(c, χᵢ, s/m, t) dt ds`.
-/

namespace Cvs.L2a.BulkECouplingRemainder

open Real Set Filter MeasureTheory intervalIntegral Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FarIntegrationByParts Cvs.L2a.QIdentityComplexWeight Cvs.Prolate.RungCauchySplit
open scoped ComplexConjugate

/-! ### `Q ≠ 0` inside the light cone -/

/-- `Q ≠ 0` for `y² < 1`, `x > 1`, `χ < c²`, from `Re Q = c²(x² − 1)(y² − 1) − (c² − χ) < 0`. -/
theorem qQ_ne_zero_of_sq_lt_one {c χ y x : ℝ} (hy : y ^ 2 < 1) (hx : 1 < x) (hχ : χ < c ^ 2) :
    qQ c χ y x ≠ 0 := by
  intro h
  have hre := qQ_re c χ y x
  rw [h, Complex.zero_re] at hre
  have h1 : c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg c) (by nlinarith)) (by linarith)
  linarith

/-- **`QIdentityComplexWeight`'s Q-identity with `Q ≠ 0` on `[α, β]` in place of `y > 0`**. -/
theorem ibpC_Icc_of_ne {g g₁ g₂ : ℝ → ℝ} {w w₁ w₂ : ℝ → ℂ} {c χ y α β : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hα : 1 < α) (hαβ : α ≤ β) (hQ : ∀ x ∈ Icc α β, qQ c χ y x ≠ 0)
    (hw : ∀ x ∈ Icc α β, HasDerivAt w (w₁ x) x) (hw₁ : ∀ x ∈ Icc α β, HasDerivAt w₁ (w₂ x) x)
    (hw₂ : ContinuousOn w₂ (Icc α β)) :
    ∫ x in α..β, w x * (psi c g x : ℂ) * eF c y x
      = (∫ x in α..β, eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x)
        + (bBc w w₁ c χ g y β - bBc w w₁ c χ g y α) := by
  obtain ⟨-, -, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hI : uIcc α β = Icc α β := uIcc_of_le hαβ
  have hwc : ContinuousOn w (Icc α β) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hw₁c : ContinuousOn w₁ (Icc α β) := fun x hx => (hw₁ x hx).continuousAt.continuousWithinAt
  have hL : IntervalIntegrable (fun x => w x * (psi c g x : ℂ) * eF c y x) volume α β :=
    ((hwc.mul (continuous_ofReal.comp hψc).continuousOn).mul
      (continuous_eF c y).1.continuousOn).intervalIntegrable_of_Icc hαβ
  have hR : IntervalIntegrable (fun x => eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x) volume α β :=
    (((continuous_eF c y).1.continuousOn.mul (continuous_ofReal.comp hψc).continuousOn).mul
      (continuousOn_gWc_rRc hwc hw₁c hw₂ hQ).2.2).intervalIntegrable_of_Icc hαβ
  have hderiv : ∀ x ∈ uIcc α β, HasDerivAt (bBc w w₁ c χ g y)
      ((fun x => w x * (psi c g x : ℂ) * eF c y x
        - eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x) x) x := by
    intro x hx
    rw [hI] at hx
    exact hasDerivAt_bBc hg hg₁ hg₂c hang (by linarith [hx.1]) (hw x hx) (hw₁ x hx) (hQ x hx)
  have hftc := integral_eq_sub_of_hasDerivAt hderiv (hL.sub hR)
  rw [intervalIntegral.integral_sub hL hR] at hftc
  linear_combination hftc

/-- **The Q-identity with `w = 1` at `y² < 1`**: `∫_α^β eψ = ∫_α^β eψR + S[μ_cut(y, β)](β) − S[μ_cut(y, α)](α)`. -/
theorem ibp_one {g g₁ g₂ : ℝ → ℝ} {c χ y α β : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχc : χ < c ^ 2) (hy : y ^ 2 < 1) (hα : 1 < α) (hαβ : α ≤ β) :
    ∫ x in α..β, eF c y x * (psi c g x : ℂ)
      = (∫ x in α..β, eF c y x * (psi c g x : ℂ) * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y x)
        + (Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c y β) c χ g β - Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c y α) c χ g α) := by
  have h := ibpC_Icc_of_ne (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0) (w₂ := fun _ => 0) (χ := χ) (y := y)
    hg hg₁ hg₂c hang hα hαβ (fun x hx => qQ_ne_zero_of_sq_lt_one hy (by linarith [hx.1]) hχc)
    (fun x _ => hasDerivAt_const x 1) (fun x _ => hasDerivAt_const x 0) continuousOn_const
  rw [Cvs.L2a.QIdentityCutPoint.bBc_cut_split (w := fun _ => (1 : ℂ)) (w₁ := fun _ => (0 : ℂ)) (g := g) (y := y) (by linarith) hc hχc
      rfl rfl, Cvs.L2a.QIdentityCutPoint.bBc_cut_split (w := fun _ => (1 : ℂ)) (w₁ := fun _ => (0 : ℂ)) (g := g) (y := y) hα hc hχc
      rfl rfl] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

/-! ### The cut multiplier at `±k` in `s` -/

/-- At `ξ = ±k(x)`, `s ↦ μ_cut(c, s/m, x, ξ)` is continuous on `[−1, 1]` for `m > 1`, `x > 1`, `χ < c²`. -/
theorem continuousOn_muCut_kP {c χ m x ξ : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hm : 1 < m) (hx : 1 < x)
    (hξ : ξ = kP c χ x ∨ ξ = -kP c χ x) :
    ContinuousOn (fun s => Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x ξ) (Icc (-1) 1) := by
  intro s hs
  have hy : (s / m) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (by linarith [hs.1] : (0 : ℝ) ≤ s + 1),
      mul_pos (by linarith : (0 : ℝ) < m - 1) (by linarith : (0 : ℝ) < m + 1)]
  have hQ : Cvs.L2a.QIdentityCutPoint.qQk c (s / m) x ξ ≠ 0 := by
    have h0 : Cvs.L2a.QIdentityCutPoint.qQk c (s / m) x ξ = Cvs.L2a.QIdentityCutPoint.qQk c (s / m) x (kP c χ x) := by
      rcases hξ with rfl | rfl
      · rfl
      · exact Cvs.L2a.QIdentityCutPoint.qQk_neg _ _ _ _
    rw [h0, Cvs.L2a.QIdentityCutPoint.qQk_kP hx hc hχc]
    exact qQ_ne_zero_of_sq_lt_one hy hx hχc
  have hq : Continuous fun s : ℝ => Cvs.L2a.QIdentityCutPoint.qQk c (s / m) x ξ := by unfold Cvs.L2a.QIdentityCutPoint.qQk; fun_prop
  have hq1 : Continuous fun s : ℝ => qQ₁ c (s / m) x := by unfold qQ₁; fun_prop
  have he : Continuous fun s : ℝ => eF c (s / m) x := by unfold eF; fun_prop
  have hl : Continuous fun s : ℝ => Complex.I * ((ξ - c * (s / m) : ℝ) : ℂ) := by fun_prop
  apply ContinuousAt.continuousWithinAt
  unfold Cvs.L2a.QIdentityCutPoint.muCut Cvs.L2a.QIdentityCutPoint.muQ
  exact he.continuousAt.mul (continuousAt_const.mul ((hl.continuousAt.div hq.continuousAt hQ).add
    (hq1.continuousAt.div (hq.continuousAt.pow 2) (pow_ne_zero 2 hQ))))

/-! ### The sample is linear in the multiplier -/

/-- **Linearity of the sample under the `s`-integral**: `(1/m)∫ g(s) S[μ_cut(s/m, x)](x) ds = S[ν_cut(m, x)](x)`. -/
theorem smp_integral {g gi : ℝ → ℝ} {c χ m x : ℝ}
    (hp : IntervalIntegrable (fun s => (g s : ℂ) * Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x (kP c χ x)) volume (-1) 1)
    (hn : IntervalIntegrable (fun s => (g s : ℂ) * Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x (-kP c χ x)) volume (-1) 1) :
    ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (g s : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x) c χ gi x
      = Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.BandRungOutgoingWave.nuCut c g m x) c χ gi x := by
  unfold Cvs.L2a.BandTransferBandForm.smp Cvs.L2a.BandRungOutgoingWave.nuCut
  have h : ∀ s, (g s : ℂ) * (Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x (kP c χ x) * psiP c χ gi x
        + Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x (-kP c χ x) * conj (psiP c χ gi x))
      = (g s : ℂ) * Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x (kP c χ x) * psiP c χ gi x
        + (g s : ℂ) * Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x (-kP c χ x) * conj (psiP c χ gi x) := fun s => by ring
  simp_rw [h]
  rw [intervalIntegral.integral_add (hp.mul_const _) (hn.mul_const _), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const]
  ring

/-- The sample of a finite sum of multipliers is the sum of the samples. -/
theorem smp_sum {α : Type*} (S : Finset α) (μ : α → ℝ → ℂ) (c χ : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    Cvs.L2a.BandTransferBandForm.smp (fun ξ => ∑ k ∈ S, μ k ξ) c χ g x = ∑ k ∈ S, Cvs.L2a.BandTransferBandForm.smp (μ k) c χ g x := by
  unfold Cvs.L2a.BandTransferBandForm.smp
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]

/-! ### The dilate sum at an integer level -/

/-- At integer `M ≥ 2`, `dilSum(Φ, M) = Σ_{2 ≤ m < M} 1_(1, M/m] Φ(m·)`: the `m = M` term is empty. -/
theorem dilSum_nat (Φ : ℝ → ℝ) {M : ℕ} (hM : 2 ≤ M) (θ : ℝ) :
    Cvs.L2a.CoreArmIdentity.dilSum Φ M θ = ∑ m ∈ Finset.Ico 2 M, (Ioc 1 ((M : ℝ) / m)).indicator (fun θ => Φ (m * θ)) θ := by
  unfold Cvs.L2a.CoreArmIdentity.dilSum
  rw [Nat.floor_natCast, ← Finset.Ico_insert_right hM, Finset.sum_insert Finset.right_notMem_Ico]
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [div_self hM0, Ioc_self, indicator_empty, zero_add]

/-- `∫_{(1,∞)} ψ·dilSum(Φ, M) = Σ_{2 ≤ m < M} (1/m) ∫_m^M ψ(t/m)Φ(t) dt` for continuous `ψ, Φ`. -/
theorem integral_psi_dilSum {ψ Φ : ℝ → ℝ} (hψ : Continuous ψ) (hΦ : Continuous Φ) {M : ℕ} (hM : 2 ≤ M) :
    ∫ x in Ioi 1, ψ x * Cvs.L2a.CoreArmIdentity.dilSum Φ M x
      = ∑ m ∈ Finset.Ico 2 M, (1 / (m : ℝ)) * ∫ t in (m : ℝ)..M, ψ (t / m) * Φ t := by
  simp_rw [dilSum_nat Φ hM, Finset.mul_sum]
  have hcut : ∀ m : ℕ, (fun x => ψ x * (Ioc 1 ((M : ℝ) / m)).indicator (fun θ => Φ (m * θ)) x)
      = (Ioc 1 ((M : ℝ) / m)).indicator (fun θ => ψ θ * Φ (m * θ)) := fun m => by
    funext x; rw [Set.indicator_mul_right]
  have hcont : ∀ m : ℕ, Continuous fun θ => ψ θ * Φ (m * θ) := fun m =>
    hψ.mul (hΦ.comp (continuous_const.mul continuous_id))
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_Ico.1 hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hb : 1 ≤ (M : ℝ) / m := by
      rw [le_div_iff₀ hm0, one_mul]; exact_mod_cast hm'.2.le
    rw [hcut m, setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 Ioc_subset_Ioi_self,
      ← intervalIntegral.integral_of_le hb]
    have h := intervalIntegral.integral_comp_mul_left (a := (1 : ℝ)) (b := (M : ℝ) / m)
      (fun t => ψ (t / m) * Φ t) hm0.ne'
    have e1 : (∫ x in (1 : ℝ)..(M : ℝ) / m, ψ x * Φ (m * x))
        = ∫ x in (1 : ℝ)..(M : ℝ) / m, (fun t => ψ (t / m) * Φ t) (m * x) :=
      intervalIntegral.integral_congr fun x _ => by simp only [mul_div_cancel_left₀ x hm0.ne']
    have e2 : (m : ℝ) * ((M : ℝ) / m) = M := by field_simp
    rw [e1, h, mul_one, e2, smul_eq_mul, one_div]
  · intro m _
    rw [hcut m]
    exact ((((hcont m).integrableOn_Icc (a := 1) (b := (M : ℝ) / m)).mono_set Ioc_subset_Icc_self).integrable_indicator
      measurableSet_Ioc).integrableOn

/-! ### Fubini on the cut rectangle -/

/-- **Fubini on a rectangle** for an integrand continuous on it. -/
theorem integral_swap_rect {f : ℝ → ℝ → ℂ} {a b α β : ℝ} (hab : a ≤ b) (hαβ : α ≤ β)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc α β)) :
    ∫ s in a..b, ∫ t in α..β, f s t = ∫ t in α..β, ∫ s in a..b, f s t := by
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hαβ]
  have hi : Integrable (Function.uncurry f) ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc α β))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact integral_integral_swap hi

/-- The complex transform `E_j(t) = ∫ g_j(s) e^{ic(s/m)t} ds`. -/
noncomputable def eJ (c : ℝ) (gj : ℝ → ℝ) (m t : ℝ) : ℂ := ∫ s in (-1 : ℝ)..1, (gj s : ℂ) * eF c (s / m) t

/-- `E_j` is continuous in `t` for `g_j` continuous on `[−1, 1]`. -/
theorem continuous_eJ {c m : ℝ} {gj : ℝ → ℝ} (hgj : ContinuousOn gj (Icc (-1) 1)) :
    Continuous (eJ c gj m) := by
  have h1 : (-1 : ℝ) ≤ 1 := by norm_num
  obtain ⟨G, hGc, hGe⟩ : ∃ G : ℝ → ℝ, Continuous G ∧ ∀ s ∈ Icc (-1 : ℝ) 1, G s = gj s :=
    ⟨Set.IccExtend h1 ((Icc (-1 : ℝ) 1).domRestrict gj), continuous_IccExtend_iff.2 hgj.domRestrict,
      fun s hs => by simp only [Set.IccExtend_of_mem h1 _ hs, Set.domRestrict_apply]⟩
  have hEq : eJ c gj m = fun t => ∫ s in (-1 : ℝ)..1, ((G s : ℝ) : ℂ) * eF c (s / m) t := by
    funext t
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le h1] at hs
    simp only [hGe s hs]
  rw [hEq]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t s => ((G s : ℝ) : ℂ) * eF c (s / m) t) ?_ _ _
  exact (continuous_ofReal.comp (hGc.comp continuous_snd)).mul
    (by unfold eF; fun_prop : Continuous fun p : ℝ × ℝ => eF c (p.2 / m) p.1)

/-- `ψ_j(t/m) = Re E_j(t)`. -/
theorem psi_div_eq_re {c m t : ℝ} {gj : ℝ → ℝ} (hgj : ContinuousOn gj (Icc (-1) 1)) :
    psi c gj (t / m) = (eJ c gj m t).re := by
  have hii : IntervalIntegrable (fun s => (gj s : ℂ) * eF c (s / m) t) volume (-1) 1 :=
    ((continuous_ofReal.comp_continuousOn hgj).mul
      (by unfold eF; fun_prop : Continuous fun s : ℝ => eF c (s / m) t).continuousOn).intervalIntegrable_of_Icc
      (by norm_num)
  have hre : ∫ s in (-1 : ℝ)..1, ((gj s : ℂ) * eF c (s / m) t).re
      = (∫ s in (-1 : ℝ)..1, (gj s : ℂ) * eF c (s / m) t).re := intervalIntegral_re hii
  unfold eJ
  rw [← hre]
  unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [eF, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [show c * (s / m) * t = c * (t / m) * s by ring]

/-- **Fubini on a cut**: `∫ g_j(s) ∫_m^X e^{ic(s/m)t} ψ(t) dt ds = ∫_m^X E_j(t) ψ(t) dt`. -/
theorem integral_swap_eJ {c m X : ℝ} {gj ψ : ℝ → ℝ} (hgj : ContinuousOn gj (Icc (-1) 1)) (hψ : Continuous ψ)
    (hmX : m ≤ X) :
    ∫ s in (-1 : ℝ)..1, (gj s : ℂ) * ∫ t in m..X, eF c (s / m) t * (ψ t : ℂ)
      = ∫ t in m..X, eJ c gj m t * (ψ t : ℂ) := by
  have h1 : ∀ s, (gj s : ℂ) * (∫ t in m..X, eF c (s / m) t * (ψ t : ℂ))
      = ∫ t in m..X, (gj s : ℂ) * (eF c (s / m) t * (ψ t : ℂ)) :=
    fun s => (intervalIntegral.integral_const_mul _ _).symm
  have h2 : ∀ t, eJ c gj m t * (ψ t : ℂ) = ∫ s in (-1 : ℝ)..1, (gj s : ℂ) * (eF c (s / m) t * (ψ t : ℂ)) := by
    intro t
    unfold eJ
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  simp_rw [h1, h2]
  refine integral_swap_rect (by norm_num) hmX ?_
  have hg' : ContinuousOn (fun p : ℝ × ℝ => (gj p.1 : ℂ)) (Icc (-1) 1 ×ˢ Icc m X) :=
    (continuous_ofReal.comp_continuousOn hgj).comp continuous_fst.continuousOn (fun p hp => hp.1)
  have he : Continuous fun p : ℝ × ℝ => eF c (p.1 / m) p.2 * (ψ p.2 : ℂ) :=
    (by unfold eF; fun_prop : Continuous fun p : ℝ × ℝ => eF c (p.1 / m) p.2).mul
      (continuous_ofReal.comp (hψ.comp continuous_snd))
  exact hg'.mul he.continuousOn

/-! ### The per-cut identity -/

/-- **One cut, one rung**: `(1/m)∫ g_j ∫_m^X eψ = (1/m)∫ g_j ∫_m^X eψR + S[ν_cut(m, X)](X) − S[ν_cut(m, m)](m)`,
`R = R(c, χ, s/m, t)` the `w = 1` remainder. -/
theorem cut_identity {g g₁ g₂ gj : ℝ → ℝ} {c χ m X : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχc : χ < c ^ 2) (hgj : ContinuousOn gj (Icc (-1) 1)) (hm : 2 ≤ m) (hmX : m ≤ X) :
    ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (gj s : ℂ) * ∫ t in m..X, eF c (s / m) t * (psi c g t : ℂ)
      = ((1 / m : ℝ) : ℂ) * (∫ s in (-1 : ℝ)..1, (gj s : ℂ) * ∫ t in m..X, eF c (s / m) t * (psi c g t : ℂ)
          * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ (s / m) t)
        + (Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.BandRungOutgoingWave.nuCut c gj m X) c χ g X - Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.BandRungOutgoingWave.nuCut c gj m m) c χ g m) := by
  obtain ⟨-, -, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hm1 : 1 < m := by linarith
  have hX1 : 1 < X := by linarith
  have hsq : ∀ s ∈ Icc (-1 : ℝ) 1, (s / m) ^ 2 < 1 := fun s hs => by
    rw [div_pow, div_lt_one (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (by linarith [hs.1] : (0 : ℝ) ≤ s + 1)]
  have hgjC : ContinuousOn (fun s => (gj s : ℂ)) (Icc (-1) 1) := continuous_ofReal.comp_continuousOn hgj
  have hL : Continuous fun s => ∫ t in m..X, eF c (s / m) t * (psi c g t : ℂ) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s t => eF c (s / m) t * (psi c g t : ℂ)) ?_ _ _
    exact (by unfold eF; fun_prop : Continuous fun p : ℝ × ℝ => eF c (p.1 / m) p.2).mul
      (continuous_ofReal.comp (hψc.comp continuous_snd))
  have hB : ∀ x, 1 < x → ContinuousOn (fun s => Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x) c χ g x) (Icc (-1) 1) := by
    intro x hx
    unfold Cvs.L2a.BandTransferBandForm.smp
    exact ((continuousOn_muCut_kP hc hχc hm1 hx (Or.inl rfl)).mul continuousOn_const).add
      ((continuousOn_muCut_kP hc hχc hm1 hx (Or.inr rfl)).mul continuousOn_const)
  have hμ : ∀ x, 1 < x → ∀ ξ, (ξ = kP c χ x ∨ ξ = -kP c χ x) →
      IntervalIntegrable (fun s => (gj s : ℂ) * Cvs.L2a.QIdentityCutPoint.muCut c (s / m) x ξ) volume (-1) 1 :=
    fun x hx ξ hξ => (hgjC.mul (continuousOn_muCut_kP hc hχc hm1 hx hξ)).intervalIntegrable_of_Icc (by norm_num)
  have iL : IntervalIntegrable (fun s => (gj s : ℂ) * ∫ t in m..X, eF c (s / m) t * (psi c g t : ℂ))
      volume (-1) 1 := (hgjC.mul hL.continuousOn).intervalIntegrable_of_Icc (by norm_num)
  have iX : IntervalIntegrable (fun s => (gj s : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c (s / m) X) c χ g X)
      volume (-1) 1 := (hgjC.mul (hB X hX1)).intervalIntegrable_of_Icc (by norm_num)
  have im : IntervalIntegrable (fun s => (gj s : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c (s / m) m) c χ g m)
      volume (-1) 1 := (hgjC.mul (hB m hm1)).intervalIntegrable_of_Icc (by norm_num)
  have hR : (∫ s in (-1 : ℝ)..1, (gj s : ℂ) * ∫ t in m..X, eF c (s / m) t * (psi c g t : ℂ)
        * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ (s / m) t)
      = ∫ s in (-1 : ℝ)..1, ((gj s : ℂ) * (∫ t in m..X, eF c (s / m) t * (psi c g t : ℂ))
        - (gj s : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c (s / m) X) c χ g X
        + (gj s : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c (s / m) m) c χ g m) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    rw [ibp_one hg hg₁ hg₂c hang hc hχc (hsq s hs) hm1 hmX]
    ring
  rw [hR, intervalIntegral.integral_add (iL.sub iX) im, intervalIntegral.integral_sub iL iX,
    ← smp_integral (hμ X hX1 _ (Or.inl rfl)) (hμ X hX1 _ (Or.inr rfl)),
    ← smp_integral (hμ m hm1 _ (Or.inl rfl)) (hμ m hm1 _ (Or.inr rfl))]
  ring

/-! ### The bulk -/

section bulk
variable {ι : Type} [Fintype ι]

/-- The remainder bulk `Re Σ_{2 ≤ m < M} Σᵢ aᵢ (1/m) ∫ g_j(s) ∫_m^M e^{ic(s/m)t} ψᵢ(t) R(c, χᵢ, s/m, t) dt ds`. -/
noncomputable def bulkR (c : ℝ) (gj : ℝ → ℝ) (a χ : ι → ℝ) (g : ι → ℝ → ℝ) (M : ℕ) : ℝ :=
  (∑ m ∈ Finset.Ico 2 M, ∑ i, (a i : ℂ) * ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (gj s : ℂ)
    * ∫ t in (m : ℝ)..M, eF c (s / m) t * (psi c (g i) t : ℂ)
      * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c (χ i) (s / m) t).re

/-- The cut term `Σᵢ aᵢ (1/m) ∫ g_j(s) ∫_m^M e^{ic(s/m)t} ψᵢ(t) dt ds` before the Q-identity. -/
noncomputable def wCut (c : ℝ) (gj : ℝ → ℝ) (a : ι → ℝ) (g : ι → ℝ → ℝ) (M m : ℕ) : ℂ :=
  ∑ i, (a i : ℂ) * ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (gj s : ℂ)
    * ∫ t in (m : ℝ)..M, eF c (s / m) t * (psi c (g i) t : ℂ)

/-- **`eCoup = Re Σ_m wCut_m`**: the dilate sum by cuts, `t = mx`, `ψ_j = Re E_j` and Fubini. -/
theorem eCoup_eq_re_wCut {c : ℝ} {gj : ℝ → ℝ} {a : ι → ℝ} {g : ι → ℝ → ℝ} {M : ℕ}
    (hψ : ∀ i, Continuous (psi c (g i))) (hgj : ContinuousOn gj (Icc (-1) 1)) (hM : 2 ≤ M) :
    Cvs.L2a.BandRungOutgoingWave.eCoup c gj a g M = (∑ m ∈ Finset.Ico 2 M, wCut c gj a g M m).re := by
  have hΦ : Continuous fun ξ => ∑ i, a i * psi c (g i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hψ i)
  unfold Cvs.L2a.BandRungOutgoingWave.eCoup
  rw [integral_psi_dilSum (Cvs.Prolate.PlungeMassTrace.continuous_psi hgj) hΦ hM, Complex.re_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Ico.1 hm).2.le
  have h1 : wCut c gj a g M m
      = ((1 / m : ℝ) : ℂ) * ∫ t in (m : ℝ)..M, eJ c gj m t * ((∑ i, a i * psi c (g i) t : ℝ) : ℂ) := by
    have hpt : ∀ t, eJ c gj m t * ((∑ i, a i * psi c (g i) t : ℝ) : ℂ)
        = ∑ i, (a i : ℂ) * (eJ c gj m t * (psi c (g i) t : ℂ)) := by
      intro t
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum (f := fun i t => (a i : ℂ) * (eJ c gj m t * (psi c (g i) t : ℂ)))
      fun i _ => by
        exact (((continuous_eJ hgj).mul (continuous_ofReal.comp (hψ i))).intervalIntegrable _ _).const_mul _]
    unfold wCut
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_swap_eJ hgj (hψ i) hmM, intervalIntegral.integral_const_mul]
    ring
  rw [h1, Complex.re_ofReal_mul]
  congr 1
  have hii : IntervalIntegrable (fun t => eJ c gj m t * ((∑ i, a i * psi c (g i) t : ℝ) : ℂ)) volume m M :=
    ((continuous_eJ hgj).mul (continuous_ofReal.comp hΦ)).intervalIntegrable _ _
  have hre : ∫ t in (m : ℝ)..M, (eJ c gj m t * ((∑ i, a i * psi c (g i) t : ℝ) : ℂ)).re
      = (∫ t in (m : ℝ)..M, eJ c gj m t * ((∑ i, a i * psi c (g i) t : ℝ) : ℂ)).re := intervalIntegral_re hii
  rw [← hre]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [Complex.re_mul_ofReal, ← psi_div_eq_re hgj]

/-- **`bulkE` is the remainder bulk**: `BandRungOutgoingWave`'s `bulkE`, defined as what the per-cut identity leaves, equals
`bulkR`, for `M ≥ 2`, `c > 0`, angular rungs with `χᵢ < c²` and `g_j` continuous on `[−1, 1]`. -/
theorem bulkE_eq_bulkR {c : ℝ} {gj : ℝ → ℝ} {a χ : ι → ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {M : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) (hgj : ContinuousOn gj (Icc (-1) 1)) (hM : 2 ≤ M) :
    Cvs.L2a.BandRungOutgoingWave.bulkE c gj a χ g M = bulkR c gj a χ g M := by
  have hψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hWm : ∀ m ∈ Finset.Ico 2 M, wCut c gj a g M m
      = (∑ i, (a i : ℂ) * ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (gj s : ℂ)
          * ∫ t in (m : ℝ)..M, eF c (s / m) t * (psi c (g i) t : ℂ)
            * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c (χ i) (s / m) t)
        + ∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.BandRungOutgoingWave.nuCut c gj m M) c (χ i) (g i) M - Cvs.L2a.BandRungOutgoingWave.botS c gj a χ g m := by
    intro m hm
    have hm' := Finset.mem_Ico.1 hm
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm'.1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast hm'.2.le
    unfold wCut Cvs.L2a.BandRungOutgoingWave.botS
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hci := cut_identity (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχc i) hgj hm2 hmM
    linear_combination (a i : ℂ) * hci
  have hTop : ∑ m ∈ Finset.Ico 2 M, ∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.BandRungOutgoingWave.nuCut c gj m M) c (χ i) (g i) M
      = ∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.BandRungOutgoingWave.nuTop c gj M) c (χ i) (g i) M := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact (smp_sum (Finset.Ico 2 M) (fun m : ℕ => Cvs.L2a.BandRungOutgoingWave.nuCut c gj m M) _ _ _ _).symm
  have hW : ∑ m ∈ Finset.Ico 2 M, wCut c gj a g M m
      = (∑ m ∈ Finset.Ico 2 M, ∑ i, (a i : ℂ) * ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (gj s : ℂ)
          * ∫ t in (m : ℝ)..M, eF c (s / m) t * (psi c (g i) t : ℂ)
            * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c (χ i) (s / m) t)
        + ∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.BandRungOutgoingWave.nuTop c gj M) c (χ i) (g i) M
        - ∑ m ∈ Finset.Ico 2 M, Cvs.L2a.BandRungOutgoingWave.botS c gj a χ g m := by
    rw [Finset.sum_congr rfl hWm, Finset.sum_sub_distrib, Finset.sum_add_distrib, hTop]
  unfold Cvs.L2a.BandRungOutgoingWave.bulkE Cvs.L2a.BandRungOutgoingWave.topE bulkR
  rw [eCoup_eq_re_wCut hψ hgj hM, hW]
  simp only [Complex.add_re, Complex.sub_re, Complex.re_sum]
  ring

end bulk

end Cvs.L2a.BulkECouplingRemainder
