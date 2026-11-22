import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.PlungeMassTrace
import Cvs.Route.Visibility.AliasWindowCornerCut

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The alias tail through the window: `‖T₃‖² ≤ (W̃/2)E + off-diagonal`, `W̃ = 19/20`, and AL-R

With `y_k(θ) = √x·ψ_G(kθ)`, `S_K = Σ_{k=3}^{K} y_k` and `J_{kl}(w) = ∫ w·y_k·y_l`:
`∫_{(1/2,1]} S_K² ≤ Σ_{k,l} J_{kl}(ρ)`; AM–GM moves `2J₃₄(ρ(1 − τ))` to the diagonal `x∫ψ_G²W̃_K ≤ (19/20)x∫₁^∞ψ_G²`,
Fatou passes to `T₃ = lim S_K`, and the rest over `P′ = {k ≠ l} ∖ {(3,4), (4,3)}` plus `2J₃₄(ρτ)` is `OffDiag C₁`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Finset

namespace Cvs.Route.Visibility.AliasTailThroughWindow
open Cvs.ZeroCounting

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Approximant.DeepIndexSpineSpan (spineG)
open Cvs.Route.Visibility.AliasWindowCornerCut (rho tau rho_nonneg rho_le_one rho_eq_one rho_eq_zero_of_le rho_eq_zero_of_ge)

/-! ### Continuity and support of the window -/

/-- `ρ` is continuous. -/
theorem continuous_rho : Continuous rho := by
  unfold rho; fun_prop

/-- `τ` is continuous. -/
theorem continuous_tau : Continuous tau := by
  unfold tau; fun_prop

/-- `ρ` vanishes off `[12/25, 11/10]`. -/
theorem rho_eq_zero_of_notMem {θ : ℝ} (h : θ ∉ Icc (12 / 25 : ℝ) (11 / 10)) : rho θ = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · exact rho_eq_zero_of_le h.le
  · exact rho_eq_zero_of_ge h.le

/-- `ρ` has compact support. -/
theorem hasCompactSupport_rho : HasCompactSupport rho :=
  HasCompactSupport.intro isCompact_Icc fun _ h => rho_eq_zero_of_notMem h

/-- The corner weight `ρ(1 − τ)`. -/
def rhoC (θ : ℝ) : ℝ := rho θ * (1 - tau θ)

/-- The corner weight `ρτ`. -/
def rhoT (θ : ℝ) : ℝ := rho θ * tau θ

/-! ### The aliases, their partial sums and the pair integrals -/

variable (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ)

/-- The alias `y_k(θ) = √x·ψ_G(kθ)`. -/
def yk (k : ℕ) (θ : ℝ) : ℝ := √(x : ℝ) * psi (2 * π * x) (spineG (2 * π * x) b) (k * θ)

/-- The partial alias tail `S_K = Σ_{k=3}^{K} y_k`. -/
def partialTail (K : ℕ) (θ : ℝ) : ℝ := ∑ k ∈ Icc 3 K, yk x b k θ

/-- The pair integral `J_{kl}(w) = ∫ w·y_k·y_l`. -/
def pairJ (w : ℝ → ℝ) (k l : ℕ) : ℝ := ∫ θ, w θ * (yk x b k θ * yk x b l θ)

/-- The off-diagonal pairs `P′ = {k ≠ l} ∖ {(3,4), (4,3)}`. -/
def offP (k l : ℕ) : Prop := k ≠ l ∧ ¬(k = 3 ∧ l = 4) ∧ ¬(k = 4 ∧ l = 3)

instance (k l : ℕ) : Decidable (offP k l) := by unfold offP; infer_instance

/-- **The off-diagonal incoherence bound** (alr/PROOF.md Steps 3–7): eventually, for every spine class `b` and
`K ≥ 4`, `Σ_{P′, k,l ≤ K} J_{kl}(ρ) + 2J₃₄(ρτ) ≤ (C₁/c)‖g‖²` with `‖g‖² = x∫_{(1,∞)}ψ_G²` at `c = 2πx`. -/
def OffDiag (C₁ : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (K : ℕ), 4 ≤ K →
    ∑ k ∈ Icc 3 K, ∑ l ∈ Icc 3 K, (if offP k l then pairJ x b rho k l else 0) + 2 * pairJ x b rhoT 3 4
      ≤ C₁ / (2 * π * x) * ((x : ℝ) * ∫ ξ in Ioi 1, psi (2 * π * x) (spineG (2 * π * x) b) ξ ^ 2)

variable {x}

/-- `ψ_G` is continuous. -/
theorem continuous_psiG : Continuous (psi (2 * π * x) (spineG (2 * π * x) b)) :=
  Cvs.Prolate.PlungeMassTrace.continuous_psi (Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ b)

/-- `y_k` is continuous. -/
theorem continuous_yk (k : ℕ) : Continuous (yk x b k) :=
  continuous_const.mul ((continuous_psiG b).comp (continuous_const.mul continuous_id))

/-- A continuous weight with compact support makes every pair integrand integrable. -/
theorem integrable_pair {w : ℝ → ℝ} (hw : Continuous w) (hs : HasCompactSupport w) (k l : ℕ) :
    Integrable fun θ => w θ * (yk x b k θ * yk x b l θ) :=
  (hw.mul ((continuous_yk b k).mul (continuous_yk b l))).integrable_of_hasCompactSupport (hs.mul_right)

/-- `ρτ` is continuous with compact support. -/
theorem rhoT_spec : Continuous rhoT ∧ HasCompactSupport rhoT :=
  ⟨continuous_rho.mul continuous_tau, hasCompactSupport_rho.mul_right⟩

/-- `ρ(1 − τ)` is continuous with compact support. -/
theorem rhoC_spec : Continuous rhoC ∧ HasCompactSupport rhoC :=
  ⟨continuous_rho.mul (continuous_const.sub continuous_tau), hasCompactSupport_rho.mul_right⟩

/-! ### The window bound and the expansion -/

/-- `∫_{(1/2,1]} S_K² ≤ ∫ρS_K²`. -/
theorem integral_partial_sq_le (K : ℕ) :
    ∫ θ in Ioc (1 / 2 : ℝ) 1, partialTail x b K θ ^ 2 ≤ ∫ θ, rho θ * partialTail x b K θ ^ 2 := by
  have hc : Continuous (partialTail x b K) := continuous_finsetSum _ fun k _ => continuous_yk b k
  have hi : Integrable fun θ => rho θ * partialTail x b K θ ^ 2 :=
    (continuous_rho.mul (hc.pow 2)).integrable_of_hasCompactSupport hasCompactSupport_rho.mul_right
  calc ∫ θ in Ioc (1 / 2 : ℝ) 1, partialTail x b K θ ^ 2
      = ∫ θ in Ioc (1 / 2 : ℝ) 1, rho θ * partialTail x b K θ ^ 2 := by
        refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        rw [rho_eq_one hθ.1.le hθ.2, one_mul]
    _ ≤ ∫ θ, rho θ * partialTail x b K θ ^ 2 :=
        setIntegral_le_integral hi (Eventually.of_forall fun θ => mul_nonneg (rho_nonneg θ) (sq_nonneg _))

/-- `∫ρS_K² = Σ_{k,l} J_{kl}(ρ)`. -/
theorem integral_rho_partial_sq (K : ℕ) :
    ∫ θ, rho θ * partialTail x b K θ ^ 2 = ∑ k ∈ Icc 3 K, ∑ l ∈ Icc 3 K, pairJ x b rho k l := by
  have e : ∀ θ, rho θ * partialTail x b K θ ^ 2
      = ∑ k ∈ Icc 3 K, ∑ l ∈ Icc 3 K, rho θ * (yk x b k θ * yk x b l θ) := by
    intro θ
    rw [partialTail, sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
  simp_rw [e]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    integrable_pair b continuous_rho hasCompactSupport_rho k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => integrable_pair b continuous_rho hasCompactSupport_rho k l]
  rfl

/-- `J_{kl}(w)` is symmetric. -/
theorem pairJ_comm (w : ℝ → ℝ) (k l : ℕ) : pairJ x b w k l = pairJ x b w l k := by
  unfold pairJ; simp_rw [mul_comm (yk x b k _)]

/-- **The corner split with AM–GM**: `2J₃₄(ρ) ≤ 2J₃₄(ρτ) + J₃₃(ρ(1 − τ)) + J₄₄(ρ(1 − τ))`. -/
theorem corner_le : 2 * pairJ x b rho 3 4
    ≤ 2 * pairJ x b rhoT 3 4 + pairJ x b rhoC 3 3 + pairJ x b rhoC 4 4 := by
  have e : pairJ x b rho 3 4 = pairJ x b rhoT 3 4 + pairJ x b rhoC 3 4 := by
    unfold pairJ
    rw [← integral_add (integrable_pair b rhoT_spec.1 rhoT_spec.2 3 4)
      (integrable_pair b rhoC_spec.1 rhoC_spec.2 3 4)]
    congr 1; funext θ; unfold rhoT rhoC; ring
  have h : 2 * pairJ x b rhoC 3 4 ≤ pairJ x b rhoC 3 3 + pairJ x b rhoC 4 4 := by
    unfold pairJ
    rw [← integral_add (integrable_pair b rhoC_spec.1 rhoC_spec.2 3 3)
      (integrable_pair b rhoC_spec.1 rhoC_spec.2 4 4), ← integral_const_mul]
    refine integral_mono ((integrable_pair b rhoC_spec.1 rhoC_spec.2 3 4).const_mul 2)
      ((integrable_pair b rhoC_spec.1 rhoC_spec.2 3 3).add (integrable_pair b rhoC_spec.1 rhoC_spec.2 4 4))
      fun θ => ?_
    have h0 : 0 ≤ rhoC θ := mul_nonneg (rho_nonneg θ) (Cvs.Route.Visibility.AliasWindowCornerCut.one_sub_tau_mem θ).1
    have := mul_nonneg h0 (sq_nonneg (yk x b 3 θ - yk x b 4 θ))
    nlinarith
  linarith

/-- **The change of variables** `J_{kk}(w) = (x/k)∫ w(s/k)ψ_G(s)² ds`. -/
theorem pairJ_diag (w : ℝ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    pairJ x b w k k = (x : ℝ) / k * ∫ s, w (s / k) * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold pairJ yk
  have h := Measure.integral_comp_mul_left
    (fun s => w (s / k) * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2) (k : ℝ)
  have e : ∀ θ : ℝ, w θ * (√(x : ℝ) * psi (2 * π * x) (spineG (2 * π * x) b) (k * θ)
      * (√(x : ℝ) * psi (2 * π * x) (spineG (2 * π * x) b) (k * θ)))
      = (x : ℝ) * (w (k * θ / k) * psi (2 * π * x) (spineG (2 * π * x) b) (k * θ) ^ 2) := by
    intro θ
    rw [mul_div_cancel_left₀ _ hk0.ne']
    have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) x)
    linear_combination (w θ * psi (2 * π * x) (spineG (2 * π * x) b) (k * θ) ^ 2) * this
  simp_rw [e]
  rw [integral_const_mul, h, abs_of_pos (inv_pos.2 hk0), smul_eq_mul]
  field_simp

end Cvs.Route.Visibility.AliasTailThroughWindow
