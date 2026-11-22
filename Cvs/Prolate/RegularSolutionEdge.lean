import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Prolate.VolterraResolventEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The regular solution at ξ = 1, and the rung as its multiple

For continuous `Q` and real `χ`, `regSol Q χ` solves `((ξ²−1)y')' + (Q − χ)y = 0` on `(−1, ∞)` with `y(1) = 1` and
zero flux at `1`; its flux, its exact second derivative (Frobenius coefficients at `1`) and its `χ`-derivative are
given. Every zero-flux solution is `ψ(1)` times it; so are the rung `psi c g` and the angular function on `(−1, 1]`.
-/

noncomputable section

open Real Set intervalIntegral MeasureTheory Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.VolterraResolventEdge
open scoped Interval

namespace Cvs.Prolate.RegularSolutionEdge

variable {a b : ℝ}

/-! ### Interval selection -/

/-- The left end of the interval used at `ξ`. -/
def lo (ξ : ℝ) : ℝ := if -1 < ξ then min 0 ((ξ - 1) / 2) else 0

/-- The right end of the interval used at `ξ`. -/
def hi (ξ : ℝ) : ℝ := max 2 (ξ + 1)

theorem adm_lohi (ξ : ℝ) : Adm (lo ξ) (hi ξ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold lo; split_ifs with h
    · exact lt_min (by norm_num) (by linarith)
    · norm_num
  · unfold lo; split_ifs
    · exact (min_le_left _ _).trans (by norm_num)
    · norm_num
  · unfold hi; exact (by norm_num : (1:ℝ) ≤ 2).trans (le_max_left _ _)

theorem mem_lohi {ξ : ℝ} (hξ : -1 < ξ) : ξ ∈ Ioo (lo ξ) (hi ξ) := by
  constructor
  · unfold lo; rw [if_pos hξ]
    rcases le_or_gt ξ 0 with h | h
    · exact (min_le_right _ _).trans_lt (by linarith)
    · exact (min_le_left _ _).trans_lt h
  · unfold hi; exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

theorem pP_ne_zero {t : ℝ} (ht : -1 < t) (h1 : t ≠ 1) : pP t ≠ 0 := by
  unfold pP; intro e
  have : (t - 1) * (t + 1) = 0 := by linear_combination e
  rcases mul_eq_zero.mp this with h | h
  · exact h1 (by linarith)
  · linarith

/-! ### The regular solution -/

/-- The solution of `((ξ²−1)y')' + (Q − χ)y = 0` regular at `1` with `y(1) = 1`. -/
def regSol (Q : C(ℝ, ℝ)) (χ ξ : ℝ) : ℝ :=
  (regOn (adm_lohi ξ) (Cab.restr (Q - ContinuousMap.const ℝ χ))).ext (adm_lohi ξ).le ξ

/-- The derivative of the regular solution, `−avg((Q − χ) regSol)`. -/
def regV (Q : C(ℝ, ℝ)) (χ ξ : ℝ) : ℝ := -avg (fun s => (Q s - χ) * regSol Q χ s) ξ

/-- The flux `(ξ²−1) regSol'` of the regular solution. -/
def regU (Q : C(ℝ, ℝ)) (χ ξ : ℝ) : ℝ := -∫ s in (1:ℝ)..ξ, (Q s - χ) * regSol Q χ s

/-- The potential `c²ξ²` of the radial prolate equation. -/
def sqC (c : ℝ) : C(ℝ, ℝ) := ⟨fun ξ => c ^ 2 * ξ ^ 2, by fun_prop⟩

theorem sqC_sub (c χ ξ : ℝ) : sqC c ξ - χ = qP c χ ξ := rfl

theorem regSol_eq_regOn (Q : C(ℝ, ℝ)) (χ : ℝ) (h : Adm a b) {ξ : ℝ} (hξ : ξ ∈ Icc a b) :
    regSol Q χ ξ = (regOn h (Cab.restr (Q - ContinuousMap.const ℝ χ))).ext h.le ξ := by
  have hξ1 : -1 < ξ := lt_of_lt_of_le h.neg_one_lt hξ.1
  have h0 := adm_lohi ξ
  have hm := mem_lohi hξ1
  have hH : Adm (min a (lo ξ)) (max b (hi ξ)) :=
    ⟨lt_min h.neg_one_lt h0.neg_one_lt, (min_le_left _ _).trans h.le_one, h.one_le.trans (le_max_left _ _)⟩
  unfold regSol
  rw [regOn_restrict h0 hH (min_le_right _ _) (le_max_right _ _) _ ⟨hm.1.le, hm.2.le⟩,
    regOn_restrict h hH (min_le_left _ _) (le_max_left _ _) _ hξ]

theorem regSol_one (Q : C(ℝ, ℝ)) (χ : ℝ) : regSol Q χ 1 = 1 := by
  have h := adm_lohi 1
  have h1 : (1:ℝ) ∈ Icc (lo 1) (hi 1) := ⟨h.le_one, h.one_le⟩
  unfold regSol
  rw [Cab.ext_eq _ _ h1, regOn_apply]
  simp [green]

theorem hasDerivAt_regSol (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ₀ : ℝ} (hξ₀ : -1 < ξ₀) :
    HasDerivAt (regSol Q χ) (regV Q χ ξ₀) ξ₀ := by
  have h₀ := adm_lohi ξ₀
  have hm := mem_lohi hξ₀
  set q : Cab (lo ξ₀) (hi ξ₀) := Cab.restr (Q - ContinuousMap.const ℝ χ)
  set F : ℝ → ℝ := fun ξ => 1 - green ((q * regOn h₀ q).ext h₀.le) ξ
  have hF : HasDerivAt F (-avg ((q * regOn h₀ q).ext h₀.le) ξ₀) ξ₀ :=
    (hasDerivAt_green ((q * regOn h₀ q).continuous_ext h₀.le) hξ₀).const_sub 1
  have heq : regSol Q χ =ᶠ[𝓝 ξ₀] F := by
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with ξ hξ
    rw [regSol_eq_regOn Q χ h₀ ⟨hξ.1.le, hξ.2.le⟩, Cab.ext_eq _ _ ⟨hξ.1.le, hξ.2.le⟩, regOn_apply]
  refine (hF.congr_of_eventuallyEq heq).congr_deriv ?_
  unfold regV
  congr 1
  apply avg_congr
  intro s hs
  have hsI : s ∈ Icc (lo ξ₀) (hi ξ₀) := h₀.sub ⟨hm.1.le, hm.2.le⟩ hs
  rw [Cab.ext_mul]
  simp only [Pi.mul_apply]
  rw [Cab.ext_restr _ _ hsI, regSol_eq_regOn Q χ h₀ hsI]
  rfl

theorem continuousOn_regSol (Q : C(ℝ, ℝ)) (χ : ℝ) : ContinuousOn (regSol Q χ) (Ioi (-1)) :=
  fun _ hξ => (hasDerivAt_regSol Q χ hξ).continuousAt.continuousWithinAt

theorem continuousOn_regZ (Q : C(ℝ, ℝ)) (χ : ℝ) :
    ContinuousOn (fun s => (Q s - χ) * regSol Q χ s) (Ioi (-1)) :=
  ((Q.continuous.sub continuous_const).continuousOn).mul (continuousOn_regSol Q χ)

theorem pP_mul_regV (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) : pP ξ * regV Q χ ξ = regU Q χ ξ := by
  unfold regV regU
  rw [mul_neg, pP_mul_avg _ (by intro e; linarith)]

theorem hasDerivAt_regU (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) :
    HasDerivAt (regU Q χ) (-((Q ξ - χ) * regSol Q χ ξ)) ξ := by
  have hz := continuousOn_regZ Q χ
  have hI : IntervalIntegrable (fun s => (Q s - χ) * regSol Q χ s) volume 1 ξ :=
    (hz.mono (uIcc_one_subset_Ioi hξ)).intervalIntegrable
  have hd := integral_hasDerivAt_right hI (hz.stronglyMeasurableAtFilter isOpen_Ioi ξ hξ)
    (hz.continuousAt (Ioi_mem_nhds hξ))
  exact hd.neg

theorem regV_one (Q : C(ℝ, ℝ)) (χ : ℝ) : regV Q χ 1 = -(Q 1 - χ) / 2 := by
  simp only [regV, avg, sub_self, zero_mul, add_zero, regSol_one, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, one_mul, mul_one]
  ring

/-- **The regular solution as a `(ψ, v, u)` system**: initial data at `1`, `ψ' = v`, `pv = u`, `u' = −(Q − χ)ψ`. -/
theorem regSol_system (Q : C(ℝ, ℝ)) (χ : ℝ) :
    regSol Q χ 1 = 1 ∧ regV Q χ 1 = -(Q 1 - χ) / 2 ∧ regU Q χ 1 = 0 ∧
      ∀ ξ, -1 < ξ → HasDerivAt (regSol Q χ) (regV Q χ ξ) ξ ∧ pP ξ * regV Q χ ξ = regU Q χ ξ ∧
        HasDerivAt (regU Q χ) (-((Q ξ - χ) * regSol Q χ ξ)) ξ :=
  ⟨regSol_one Q χ, regV_one Q χ, by simp [regU], fun _ hξ =>
    ⟨hasDerivAt_regSol Q χ hξ, pP_mul_regV Q χ hξ, hasDerivAt_regU Q χ hξ⟩⟩

theorem hasDerivAt_regSol_div (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : 1 < ξ) :
    HasDerivAt (regSol Q χ) (regU Q χ ξ / pP ξ) ξ := by
  have hξ' : -1 < ξ := by linarith
  rw [← pP_mul_regV Q χ hξ', mul_div_cancel_left₀ _ (pP_ne_zero hξ' hξ.ne')]
  exact hasDerivAt_regSol Q χ hξ'

/-! ### The second derivative -/

theorem hasDerivAt_regV_of_ne (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) (h1 : ξ ≠ 1) :
    HasDerivAt (regV Q χ) (-((Q ξ - χ) * regSol Q χ ξ + 2 * ξ * regV Q χ ξ) / pP ξ) ξ := by
  have hp : pP ξ ≠ 0 := pP_ne_zero hξ h1
  have hpd : HasDerivAt pP (2 * ξ) ξ := by
    have := (hasDerivAt_pow 2 ξ).sub_const 1; unfold pP; simpa using this
  have hq := (hasDerivAt_regU Q χ hξ).div hpd hp
  have heq : regV Q χ =ᶠ[𝓝 ξ] fun r => regU Q χ r / pP r := by
    have hopen : IsOpen (Ioi (-1 : ℝ) ∩ {1}ᶜ) := isOpen_Ioi.inter isOpen_compl_singleton
    filter_upwards [hopen.mem_nhds ⟨hξ, h1⟩] with r hr
    rw [← pP_mul_regV Q χ hr.1, mul_div_cancel_left₀ _ (pP_ne_zero hr.1 hr.2)]
  refine (hq.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [← pP_mul_regV Q χ hξ]
  field_simp
  ring

/-- The Frobenius coefficient at `1`: `v'(1) = ((Q(1) − χ) + (Q(1) − χ)²/2 − Q'(1))/4`. -/
theorem hasDerivAt_regV_one (Q : C(ℝ, ℝ)) (χ : ℝ) {Q₁ : ℝ} (hQ : HasDerivAt Q Q₁ 1) :
    HasDerivAt (regV Q χ) (((Q 1 - χ) + (Q 1 - χ) ^ 2 / 2 - Q₁) / 4) 1 := by
  set z : ℝ → ℝ := fun s => (Q s - χ) * regSol Q χ s with hzdef
  have hz : HasDerivAt z (Q₁ * regSol Q χ 1 + (Q 1 - χ) * regV Q χ 1) 1 :=
    (hQ.sub_const χ).mul (hasDerivAt_regSol Q χ (by norm_num))
  have hzc : ∀ᶠ t in 𝓝 (1:ℝ), ContinuousOn z (uIcc 1 t) := by
    filter_upwards [Ioi_mem_nhds (show (-1:ℝ) < 1 by norm_num)] with t ht
    exact (continuousOn_regZ Q χ).mono (uIcc_one_subset_Ioi ht)
  have hv : regV Q χ = fun t => -avg z t := rfl
  rw [hv]
  refine (hasDerivAt_avg_one hz hzc).neg.congr_deriv ?_
  simp only [hzdef, regSol_one, regV_one]
  ring

/-- The exact second derivative of the regular solution on `(−1, ∞)`. -/
def regV₂ (Q : C(ℝ, ℝ)) (Q₁ χ r : ℝ) : ℝ :=
  if r = 1 then ((Q 1 - χ) + (Q 1 - χ) ^ 2 / 2 - Q₁) / 4
  else -((Q r - χ) * regSol Q χ r + 2 * r * regV Q χ r) / pP r

/-- **The ODE in the form of Cvs.Prolate.LiouvilleGreen.SoninFunction/Cvs.Prolate.Envelope.EdgeValueSoninBound**: `(r² − 1)v' + 2rv + (Q − χ)ψ = 0` on `(−1, ∞)`. -/
theorem regSol_ode (Q : C(ℝ, ℝ)) (χ : ℝ) {Q₁ : ℝ} (hQ : HasDerivAt Q Q₁ 1) :
    ∀ r, -1 < r → HasDerivAt (regV Q χ) (regV₂ Q Q₁ χ r) r ∧
      (r ^ 2 - 1) * regV₂ Q Q₁ χ r + 2 * r * regV Q χ r + (Q r - χ) * regSol Q χ r = 0 := by
  intro r hr
  by_cases h1 : r = 1
  · subst h1
    refine ⟨by simpa [regV₂] using hasDerivAt_regV_one Q χ hQ, ?_⟩
    rw [regV_one, regSol_one]; ring
  · have hp := pP_ne_zero hr h1
    refine ⟨by simpa [regV₂, h1] using hasDerivAt_regV_of_ne Q χ hr h1, ?_⟩
    simp only [regV₂, h1, if_false]
    change pP r * _ + _ + _ = 0
    field_simp
    ring

/-! ### The `χ`-dependence -/

theorem restr_sub_const (Q : C(ℝ, ℝ)) (χ : ℝ) :
    (Cab.restr (Q - ContinuousMap.const ℝ χ) : Cab a b) = Cab.restr Q - algebraMap ℝ (Cab a b) χ := by
  apply ContinuousMap.ext; intro ξ; rfl

theorem regSol_chi_eq (Q : C(ℝ, ℝ)) (ξ : ℝ) :
    (fun χ => regSol Q χ ξ) = (Cab.evalAt (adm_lohi ξ).le ξ) ∘
      (fun χ => regOn (adm_lohi ξ) (Cab.restr Q - algebraMap ℝ _ χ)) := by
  funext χ
  simp only [Function.comp_apply, Cab.evalAt_apply, regSol, restr_sub_const]

/-- The `χ`-derivative of the regular solution is the variational solution `dotOn`. -/
theorem hasDerivAt_regSol_chi (Q : C(ℝ, ℝ)) (ξ χ : ℝ) :
    HasDerivAt (fun χ' => regSol Q χ' ξ)
      ((dotOn (adm_lohi ξ) (Cab.restr (Q - ContinuousMap.const ℝ χ))).ext (adm_lohi ξ).le ξ) χ := by
  have hd := hasDerivAt_regOn_sub (adm_lohi ξ) (Cab.restr Q) χ
  have he := (Cab.evalAt (adm_lohi ξ).le ξ).hasFDerivAt.comp_hasDerivAt χ hd
  rw [regSol_chi_eq]
  refine he.congr_deriv ?_
  rw [restr_sub_const]
  rfl

/-- The regular solution is real-analytic in `χ` at every point. -/
theorem analyticAt_regSol_chi (Q : C(ℝ, ℝ)) (ξ χ : ℝ) : AnalyticAt ℝ (fun χ' => regSol Q χ' ξ) χ := by
  rw [regSol_chi_eq]
  exact (Cab.evalAt (adm_lohi ξ).le ξ).analyticAt _ |>.comp (analyticAt_regOn_sub _ _ χ)

/-! ### Uniqueness -/

theorem ftc_uIcc {f f' : ℝ → ℝ} {x y : ℝ} (hcont : ContinuousOn f (uIcc x y))
    (hderiv : ∀ s ∈ Ioo (min x y) (max x y), HasDerivAt f (f' s) s) (hint : IntervalIntegrable f' volume x y) :
    ∫ s in x..y, f' s = f y - f x :=
  integral_eq_sub_of_hasDeriv_right hcont (fun s hs => (hderiv s hs).hasDerivWithinAt) hint

theorem ioo_sub_of_adm (h : Adm a b) {t : ℝ} (ht : t ∈ Icc a b) : Ioo (min 1 t) (max 1 t) ⊆ Ioo a b := by
  intro s hs
  exact ⟨lt_of_le_of_lt (le_min h.le_one ht.1) hs.1, lt_of_lt_of_le hs.2 (max_le h.one_le ht.2)⟩

/-- **Uniqueness**: a solution with zero flux at `1` is `ψ(1)` times the regular solution, flux included. -/
theorem eq_mul_regSol (Q : C(ℝ, ℝ)) (χ : ℝ) (h : Adm a b) {ψ u : ℝ → ℝ}
    (hψc : ContinuousOn ψ (Icc a b)) (huc : ContinuousOn u (Icc a b))
    (hψ : ∀ t ∈ Ioo a b, t ≠ 1 → HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (-((Q t - χ) * ψ t)) t) (hu1 : u 1 = 0) :
    ∀ t ∈ Icc a b, ψ t = ψ 1 * regSol Q χ t ∧ u t = ψ 1 * regU Q χ t := by
  set y : Cab a b := Cab.ofFun ψ hψc
  set z : ℝ → ℝ := fun s => (Q s - χ) * y.ext h.le s with hz
  have hzc : Continuous z := (Q.continuous.sub continuous_const).mul (y.continuous_ext h.le)
  have hyψ : ∀ s ∈ Icc a b, y.ext h.le s = ψ s := fun s hs => by rw [Cab.ext_eq _ _ hs, Cab.ofFun_apply]
  have hseg : ∀ t ∈ Icc a b, uIcc 1 t ⊆ Icc a b := fun t ht => h.sub ht
  have hflux : ∀ t ∈ Icc a b, u t = -∫ s in (1:ℝ)..t, z s := by
    intro t ht
    have hI := ftc_uIcc (f := u) (f' := fun s => -z s) (x := 1) (y := t) (huc.mono (hseg t ht))
      (fun s hs => by
        have hsI := ioo_sub_of_adm h ht hs
        refine (hu s hsI).congr_deriv ?_
        simp only [hz, hyψ s (Ioo_subset_Icc_self hsI)])
      (hzc.neg.intervalIntegrable _ _)
    rw [intervalIntegral.integral_neg, hu1, sub_zero] at hI
    linarith
  have hval : ∀ t ∈ Icc a b, ψ t = ψ 1 - green z t := by
    intro t ht
    have hI := ftc_uIcc (f := ψ) (f' := fun s => -avg z s) (x := 1) (y := t) (hψc.mono (hseg t ht))
      (fun s hs => by
        have hsI := ioo_sub_of_adm h ht hs
        have hs1 : s ≠ 1 := by
          intro e; rw [e] at hs
          rcases le_total 1 t with h1 | h1
          · simp [min_eq_left h1] at hs
          · simp [max_eq_left h1] at hs
        have hsm : -1 < s := lt_trans h.neg_one_lt hsI.1
        have hp := pP_ne_zero hsm hs1
        refine (hψ s hsI hs1).congr_deriv ?_
        rw [hflux s (Ioo_subset_Icc_self hsI), ← pP_mul_avg z hsm.ne']
        field_simp)
      (((continuousOn_avg hzc).mono (uIcc_one_subset_Ioi (lt_of_lt_of_le h.neg_one_lt ht.1))).neg.intervalIntegrable)
    rw [intervalIntegral.integral_neg] at hI
    unfold green
    linarith
  have hy : y + volterra h (Cab.restr (Q - ContinuousMap.const ℝ χ) * y) = ψ 1 • 1 := by
    apply ContinuousMap.ext; intro ξ
    show y.toC ξ + (volterra h (Cab.restr (Q - ContinuousMap.const ℝ χ) * y)).toC ξ = ψ 1 * 1
    rw [volterra_apply, Cab.ofFun_apply]
    have hg : green ((Cab.restr (Q - ContinuousMap.const ℝ χ) * y).ext h.le) ξ = green z ξ := by
      apply green_congr; intro s hs
      rw [Cab.ext_mul]; simp only [Pi.mul_apply]; rw [Cab.ext_restr _ _ (h.sub ξ.2 hs)]; rfl
    rw [hg, hval ξ ξ.2]; ring
  have hyr := eq_smul_regOn h hy
  have hψreg : ∀ t ∈ Icc a b, ψ t = ψ 1 * regSol Q χ t := by
    intro t ht
    rw [regSol_eq_regOn Q χ h ht, ← hyψ t ht, hyr]
    rfl
  intro t ht
  refine ⟨hψreg t ht, ?_⟩
  rw [hflux t ht, regU, mul_neg, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hsI := hseg t ht hs
  simp only [hz, hyψ s hsI, hψreg s hsI]
  ring

/-! ### The rung and the angular function -/

/-- **The rung is `ψ(1)` times the regular solution**, its flux `rungU` likewise. -/
theorem psi_eq_mul_regSol {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ : ℝ} (hξ : -1 < ξ) :
    Cvs.L2a.AngularProlateTailPositive.psi c g ξ = Cvs.L2a.AngularProlateTailPositive.psi c g 1 * regSol (sqC c) χ ξ ∧
      Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c g ξ = Cvs.L2a.AngularProlateTailPositive.psi c g 1 * regU (sqC c) χ ξ := by
  obtain ⟨hψ', -, -⟩ := Cvs.L2a.AngularProlateTailPositive.psi_system hg hg₁ hg₂c hang
  obtain ⟨-, hu, hψc, huc⟩ := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang
  have h : Adm (lo ξ) (hi ξ) := adm_lohi ξ
  have hm := mem_lohi hξ
  refine eq_mul_regSol (sqC c) χ h (ψ := Cvs.L2a.AngularProlateTailPositive.psi c g) (u := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c g)
    hψc.continuousOn huc.continuousOn ?_ ?_ ?_ ξ ⟨hm.1.le, hm.2.le⟩
  · intro t ht ht1
    have hp := pP_ne_zero (lt_trans h.neg_one_lt ht.1) ht1
    refine (hψ' t).congr_deriv ?_
    unfold Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU
    rw [mul_div_cancel_left₀ _ hp]
  · intro t _
    exact (hu t).congr_deriv (by rw [sqC_sub])
  · unfold Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU pP; simp

/-- **The angular function on `(−1, 1]` is `g(1)` times the regular solution.** -/
theorem angular_eq_mul_regSol {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    ∀ s ∈ Ioc (-1 : ℝ) 1, g s = g 1 * regSol (sqC c) χ s := by
  intro s hs
  have h : Adm s 1 := ⟨hs.1, hs.2, le_rfl⟩
  have hsub : Icc s 1 ⊆ uIcc (-1 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc hs.1.le le_rfl
  have hpd : ∀ t : ℝ, HasDerivAt pP (2 * t) t := fun t => by
    have := (hasDerivAt_pow 2 t).sub_const 1; unfold pP; simpa using this
  refine (eq_mul_regSol (sqC c) χ h (ψ := g) (u := fun t => pP t * g₁ t)
    (fun t ht => (hg t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => ((hpd t).mul (hg₁ t (hsub ht))).continuousAt.continuousWithinAt) ?_ ?_ ?_ s
    ⟨le_rfl, hs.2⟩).1
  · intro t ht ht1
    have hp := pP_ne_zero (lt_trans hs.1 ht.1) ht1
    refine (hg t (hsub (Ioo_subset_Icc_self ht))).congr_deriv ?_
    rw [mul_div_cancel_left₀ _ hp]
  · intro t ht
    have htI := hsub (Ioo_subset_Icc_self ht)
    refine ((hpd t).mul (hg₁ t htI)).congr_deriv ?_
    have := hang t htI
    simp only [sqC, ContinuousMap.coe_mk, pP]
    linear_combination -this
  · simp [pP]

end Cvs.Prolate.RegularSolutionEdge
