import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullSpanIndexFloor
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ExteriorSpanBernstein
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Route.Visibility.AliasMomentMajorants
import Cvs.Route.Visibility.AliasPairIntegratedBound
import Cvs.Route.Visibility.AliasPairPointwiseBound
import Cvs.Route.Visibility.AliasPairThetaKernel
import Cvs.Route.Visibility.AliasRemainderCentreBound
import Cvs.Route.Visibility.AliasRemainderOffDiagonal
import Cvs.Route.Visibility.AliasRemainderSplit
import Cvs.Route.Visibility.AliasTailThroughWindow
import Cvs.Route.Visibility.AliasWindowCornerCut
import Cvs.Route.Visibility.WindowChainCellFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The off-diagonal incoherence bound `OffDiag C₁` of AL-R

Summing Cvs.Route.Visibility.AliasPairIntegratedBound over the pairs `P′` (window `ρ`) and `{3, 4}` (window `ρτ` on `θ ≥ 3/5`), the leading terms are bounded
by Cvs.Route.Visibility.AliasMomentMajorants (Hilbert, `C_H`) and the majorants by Schur and `Σ(N + 1)²(N + 2)²(3/4)^N ≤ 24·4⁵`; letting `M → ∞` removes
the remainder, so `OffDiag offC` holds with `offC = 30(C_H + 4ω₀) + 5898240Γ₀ ≤ 5·10⁹`.
-/

noncomputable section

namespace Cvs.Route.Visibility.AliasOffDiagonalIncoherence
open Cvs.ZeroCounting

open Real Set MeasureTheory intervalIntegral Filter
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev rung_spec)
open Cvs.Approximant.DeepIndexSpineSpan (spineG)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (coefH)
open Cvs.Route.Visibility.AliasWindowCornerCut (rho tau rho_nonneg rho_le_one rho_eq_zero_of_le rho_eq_zero_of_ge)
open Cvs.Route.Visibility.AliasTailThroughWindow (rhoT pairJ yk offP OffDiag continuous_rho continuous_tau)
open Cvs.Prolate.ExteriorSpanBernstein (IsRungFamily spanH)
open Cvs.Route.Visibility.AliasPairThetaKernel (rhoD rhoTD cornersRho cornersRhoT hasDerivAt_rho hasDerivAt_rhoT abs_rhoD_le abs_rhoTD_le measurable_rhoD measurable_rhoTD rhoT_eq_zero tau_mem qK qK_le)
open Cvs.Route.Visibility.AliasPairPointwiseBound (Hn Dn Zf N0 Rf ω₀ L₀ Γ₀)
open Cvs.Route.Visibility.AliasMomentMajorants (continuousOn_Hn continuousOn_Dn sum_integral_moment_le abs_N0_le abs_sum_N0_le CH integral_sum_Zf_sq_le schur_inv_sq sum_series_le)
open Cvs.Route.Visibility.AliasPairIntegratedBound (pair_integral_le N0_intervalIntegrable continuousOn_Zf continuousOn_Rf)

/-- The rung family of the spine at `c = 2πx`. -/
theorem rungFamily {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    IsRungFamily (2 * π * x) (fun n : Fin x => rung (2 * π * x) (2 * (n : ℕ)))
      (fun n => rung₁ (2 * π * x) (2 * (n : ℕ))) (fun n => rung₂ (2 * π * x) (2 * (n : ℕ)))
      (fun n => lev (2 * π * x) (2 * (n : ℕ))) :=
  ⟨fun n => (rung_spec (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n)).1, fun n => (rung_spec (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n)).2.1,
    fun n => (rung_spec (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n)).2.2.1, fun n => (rung_spec (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n)).2.2.2.1⟩

/-- The spine levels lie in `[0, c²]`. -/
theorem lev_mem {x : ℕ} (hx : 80 ≤ 2 * π * x) (n : Fin x) :
    0 ≤ lev (2 * π * x) (2 * (n : ℕ)) ∧ lev (2 * π * x) (2 * (n : ℕ)) ≤ (2 * π * x) ^ 2 := by
  refine ⟨Cvs.Prolate.RungFamilyRangePartners.lev_main_nonneg hx ⟨n, Finset.mem_range.mpr n.2⟩, ?_⟩
  have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx n.2).2
  have h2 := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (c := 2 * π * x) (by linarith)
  linarith

/-- The pair integral in span form: `J_{kl}(w) = x∫w·h(kθ)h(lθ)`. -/
theorem pairJ_eq {x : ℕ} (hx1 : 1 ≤ x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (w : ℝ → ℝ) (k l : ℕ) :
    pairJ x b w k l = x * ∫ θ, w θ * (spanH (2 * π * x) (fun n : Fin x => rung (2 * π * x) (2 * (n : ℕ)))
      (coefH x b) (k * θ)
        * spanH (2 * π * x) (fun n : Fin x => rung (2 * π * x) (2 * (n : ℕ))) (coefH x b) (l * θ)) := by
  rw [← MeasureTheory.integral_const_mul]
  unfold pairJ yk
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [Cvs.Route.Visibility.AliasRemainderSplit.psi_spineG_eq_sum hx1 b, spanH]
  have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) x)
  linear_combination (w θ * (∑ n : Fin x, coefH x b n * psi (2 * π * x) (rung (2 * π * x) (2 * (n : ℕ))) (k * θ))
    * (∑ n : Fin x, coefH x b n * psi (2 * π * x) (rung (2 * π * x) (2 * (n : ℕ))) (l * θ))) * this

/-- The window integral over `ℝ` is the interval integral over `[12/25, 11/10]`. -/
theorem integral_rho_eq (F : ℝ → ℝ) :
    ∫ θ, rho θ * F θ = ∫ θ in (12 / 25 : ℝ)..(11 / 10), rho θ * F θ := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun θ hθ => ?_).symm
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hθ
  rcases hθ with h | h
  · rw [rho_eq_zero_of_le h, zero_mul]
  · rw [rho_eq_zero_of_ge h.le, zero_mul]

/-- The corner window integral over `ℝ` is the interval integral over `[3/5, 11/10]`. -/
theorem integral_rhoT_eq (F : ℝ → ℝ) :
    ∫ θ, rhoT θ * F θ = ∫ θ in (3 / 5 : ℝ)..(11 / 10), rhoT θ * F θ := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun θ hθ => ?_).symm
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hθ
  rcases hθ with h | h
  · rw [rhoT_eq_zero h, zero_mul]
  · simp only [rhoT, rho_eq_zero_of_ge h.le, zero_mul]

section Family

variable {ι : Type*} [Fintype ι] {c : ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ}

/-- The zeroth-moment energy `Σ_m E₀(mθ)` integrates to at most `30∫_{(1,∞)}h²`. -/
theorem integral_sum_E0_le (hF : IsRungFamily c g g₁ g₂ χ) (hc : 3 ≤ c) (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ c ^ 2)
    (hinj : Function.Injective χ) (b : ι → ℝ) {K : ℕ} (hK : 3 ≤ K) :
    ∫ θ in (12 / 25 : ℝ)..(11 / 10), ∑ m ∈ Finset.Icc 3 K, (Hn c g χ b 0 (m * θ) ^ 2 + Dn c g χ b 0 (m * θ) ^ 2)
      ≤ 30 * ∫ ξ in Ioi 1, spanH c g b ξ ^ 2 := by
  have hint : ∀ m ∈ Finset.Icc 3 K, IntervalIntegrable
      (fun θ => Hn c g χ b 0 (m * θ) ^ 2 + Dn c g χ b 0 (m * θ) ^ 2) volume (12 / 25) (11 / 10) :=
    fun m hm => (((continuousOn_Hn hF b 0 m).pow 2).add
      ((continuousOn_Dn hF b 0 (Finset.mem_Icc.mp hm).1).pow 2)).intervalIntegrable_of_Icc (by norm_num)
  rw [intervalIntegral.integral_finsetSum hint]
  exact sum_integral_moment_le hF hc hχ hinj b 0 hK

/-- `Σ_m E₀(mθ)` is continuous and nonnegative on the window. -/
theorem continuousOn_sum_E0 (hF : IsRungFamily c g g₁ g₂ χ) (b : ι → ℝ) (K : ℕ) :
    ContinuousOn (fun θ => ∑ m ∈ Finset.Icc 3 K, (Hn c g χ b 0 (m * θ) ^ 2 + Dn c g χ b 0 (m * θ) ^ 2))
      (Icc (12 / 25) (11 / 10)) :=
  continuousOn_finsetSum _ fun m hm => ((continuousOn_Hn hF b 0 m).pow 2).add
    ((continuousOn_Dn hF b 0 (Finset.mem_Icc.mp hm).1).pow 2)

/-- **One leading term integrates to `O(1/c)`**: `|∫_α^{11/10} N₀(k, l)| ≤ (ω₀/c)·30∫_{(1,∞)}h²`. -/
theorem abs_integral_N0_le (hF : IsRungFamily c g g₁ g₂ χ) (hc : 3 ≤ c) (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ c ^ 2)
    (hinj : Function.Injective χ) (b : ι → ℝ) {K : ℕ} (hK : 3 ≤ K) {k l : ℕ} (hk : k ∈ Finset.Icc 3 K)
    (hl : l ∈ Finset.Icc 3 K) (hkl : k ≠ l) {α : ℝ} (hα : 12 / 25 ≤ α) (hα1 : α ≤ 11 / 10) {w w' : ℝ → ℝ}
    (hwb : ∀ θ, |w θ| ≤ 1) (hw'b : ∀ θ, |w' θ| ≤ 70) :
    |∫ θ in α..(11 / 10), N0 c g b w w' k l θ| ≤ ω₀ / c * (30 * ∫ ξ in Ioi 1, spanH c g b ξ ^ 2) := by
  have hc0 : 0 < c := by linarith
  set E : ℝ → ℝ := fun θ => ∑ m ∈ Finset.Icc 3 K, (Hn c g χ b 0 (m * θ) ^ 2 + Dn c g χ b 0 (m * θ) ^ 2)
  have hE0 : ∀ θ, 0 ≤ E θ := fun θ => Finset.sum_nonneg fun m _ => by positivity
  have hEc := continuousOn_sum_E0 hF b K
  have hω0 : 0 ≤ ω₀ := by simp only [ω₀, Cvs.Route.Visibility.AliasPairPointwiseBound.βb]; norm_num
  have hpt : ∀ θ ∈ Ioc α (11 / 10), ‖N0 c g b w w' k l θ‖ ≤ ω₀ / c * E θ := by
    intro θ hθ
    rw [Real.norm_eq_abs]
    refine (abs_N0_le (χ := χ) hc0 b (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hl).1 hkl (hα.trans hθ.1.le) hθ.2
      (hwb θ) (hw'b θ)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun m : ℕ => Hn c g χ b 0 (m * θ) ^ 2 + Dn c g χ b 0 (m * θ) ^ 2)
      (Finset.insert_subset hk (Finset.singleton_subset_iff.mpr hl)) (fun m _ _ => by positivity)
    rw [Finset.sum_pair hkl] at h2
    exact h2
  have h1 := intervalIntegral.norm_integral_le_of_norm_le hα1 (ae_of_all _ hpt)
    (((hEc.mono (Icc_subset_Icc hα le_rfl)).const_smul (ω₀ / c)).intervalIntegrable_of_Icc (μ := volume) hα1)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine (intervalIntegral.integral_mono_interval hα hα1 le_rfl (ae_of_all _ fun θ => hE0 θ)
    (hEc.intervalIntegrable_of_Icc (μ := volume) (by norm_num))).trans ?_
  exact integral_sum_E0_le hF hc hχ hinj b hK

/-- A double sum of a single-point indicator: `Σ_{k,l ∈ S} 1[k = a, l = a′]v = v` for `a, a′ ∈ S`. -/
theorem sum_sum_ite_pt (S : Finset ℕ) {a a' : ℕ} (ha : a ∈ S) (ha' : a' ∈ S) (v : ℝ) :
    ∑ k ∈ S, ∑ l ∈ S, (if k = a ∧ l = a' then v else 0) = v := by
  have h : ∀ k, ∑ l ∈ S, (if k = a ∧ l = a' then v else 0) = if k = a then v else 0 := by
    intro k
    by_cases hk : k = a
    · simp only [hk, true_and, if_true]
      rw [Finset.sum_ite_eq' S a', if_pos ha']
    · simp only [hk, false_and, if_false, Finset.sum_const_zero]
  simp only [h]
  rw [Finset.sum_ite_eq' S a, if_pos ha]

/-- `Σ_{k≠l} f(k, l) = Σ_{P′} f(k, l) + f(3, 4) + f(4, 3)` when `3, 4 ∈ S`. -/
theorem sum_ne_split (S : Finset ℕ) (h3 : 3 ∈ S) (h4 : 4 ∈ S) (f : ℕ → ℕ → ℝ) :
    ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else f k l)
      = ∑ k ∈ S, ∑ l ∈ S, (if offP k l then f k l else 0) + f 3 4 + f 4 3 := by
  have hpt : ∀ k l, (if k = l then 0 else f k l) = (if offP k l then f k l else 0)
      + (if k = 3 ∧ l = 4 then f 3 4 else 0) + (if k = 4 ∧ l = 3 then f 4 3 else 0) := by
    intro k l
    by_cases h1 : k = l
    · subst h1
      rw [if_pos rfl, if_neg (fun h : offP k k => h.1 rfl), if_neg (by omega), if_neg (by omega)]; ring
    · by_cases h2 : k = 3 ∧ l = 4
      · obtain ⟨rfl, rfl⟩ := h2
        rw [if_neg h1, if_neg (fun h : offP 3 4 => h.2.1 ⟨rfl, rfl⟩), if_pos ⟨rfl, rfl⟩, if_neg (by omega)]; ring
      · by_cases h3 : k = 4 ∧ l = 3
        · obtain ⟨rfl, rfl⟩ := h3
          rw [if_neg h1, if_neg (fun h : offP 4 3 => h.2.2 ⟨rfl, rfl⟩), if_neg (by omega), if_pos ⟨rfl, rfl⟩]; ring
        · rw [if_neg h1, if_pos (show offP k l from ⟨h1, h2, h3⟩), if_neg h2, if_neg h3]; ring
  simp only [hpt, Finset.sum_add_distrib]
  rw [sum_sum_ite_pt S h3 h4, sum_sum_ite_pt S h4 h3]

/-- **Schur over the pairs, integrated**: `Σ_{k≠l}∫Z_N(kθ)Z_N(lθ)/(k − l)² ≤ 240(N + 2)²∫_{(1,∞)}h²`. -/
theorem sum_pair_Zf_le (hF : IsRungFamily c g g₁ g₂ χ) (hc : 3 ≤ c) (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ c ^ 2)
    (hinj : Function.Injective χ) (b : ι → ℝ) {K : ℕ} (hK : 3 ≤ K) (N : ℕ) :
    ∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K, (if k = l then 0 else
      (∫ θ in (12 / 25 : ℝ)..(11 / 10), Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) / ((k : ℝ) - l) ^ 2)
      ≤ 240 * ((N : ℝ) + 2) ^ 2 * ∫ ξ in Ioi 1, spanH c g b ξ ^ 2 := by
  set S := Finset.Icc 3 K
  have hZc : ∀ k ∈ S, ContinuousOn (fun θ => Zf c g χ b N (k * θ)) (Icc (12 / 25) (11 / 10)) :=
    fun k hk => continuousOn_Zf hF b N (Finset.mem_Icc.mp hk).1
  have hpair : ∀ k ∈ S, ∀ l ∈ S, IntervalIntegrable
      (fun θ => if k = l then 0 else Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ) / ((k : ℝ) - l) ^ 2)
      volume (12 / 25) (11 / 10) := by
    intro k hk l hl
    by_cases h : k = l
    · simp only [h, if_true]; exact intervalIntegrable_const
    · simp only [h, if_false]
      exact (((hZc k hk).mul (hZc l hl)).div_const _).intervalIntegrable_of_Icc (by norm_num)
  have e : ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else
      (∫ θ in (12 / 25 : ℝ)..(11 / 10), Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) / ((k : ℝ) - l) ^ 2)
      = ∫ θ in (12 / 25 : ℝ)..(11 / 10), ∑ k ∈ S, ∑ l ∈ S,
          (if k = l then 0 else Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ) / ((k : ℝ) - l) ^ 2) := by
    rw [intervalIntegral.integral_finsetSum fun k hk =>
      (IntervalIntegrable.sum S fun l hl => hpair k hk l hl).congr fun θ _ => by simp [Finset.sum_apply]]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [intervalIntegral.integral_finsetSum fun l hl => hpair k hk l hl]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : k = l
    · simp [h]
    · simp only [h, if_false]; rw [intervalIntegral.integral_div]
  rw [e]
  have hmono : ∀ θ ∈ Icc (12 / 25 : ℝ) (11 / 10), ∑ k ∈ S, ∑ l ∈ S,
      (if k = l then 0 else Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ) / ((k : ℝ) - l) ^ 2)
      ≤ 4 * ∑ k ∈ S, Zf c g χ b N (k * θ) ^ 2 := fun θ _ =>
    schur_inv_sq S (fun k => Zf c g χ b N (k * θ))
  have hsumc : ContinuousOn (fun θ => ∑ k ∈ S, Zf c g χ b N (k * θ) ^ 2) (Icc (12 / 25) (11 / 10)) :=
    continuousOn_finsetSum _ fun k hk => (hZc k hk).pow 2
  have hI4 : IntervalIntegrable (fun θ => 4 * ∑ k ∈ S, Zf c g χ b N (k * θ) ^ 2) volume (12 / 25) (11 / 10) :=
    (continuousOn_const.mul hsumc).intervalIntegrable_of_Icc (by norm_num)
  refine (intervalIntegral.integral_mono_on (by norm_num)
    ((IntervalIntegrable.sum S fun k hk => IntervalIntegrable.sum S fun l hl => hpair k hk l hl).congr
      fun θ _ => by simp [Finset.sum_apply]) hI4 hmono).trans ?_
  rw [intervalIntegral.integral_const_mul]
  have := integral_sum_Zf_sq_le hF hc hχ hinj b N hK
  nlinarith

/-- The off-diagonal constant `C₁ = 30(C_H + 4ω₀) + 240·24·4⁵·Γ₀`. -/
def offC : ℝ := 30 * (CH + 4 * ω₀) + 5898240 * Γ₀

/-- The window data of `ρ`. -/
theorem rho_data :
    ContinuousOn rho (Icc (12 / 25) (11 / 10)) ∧ cornersRho.Countable
      ∧ (∀ θ ∈ Ioo (12 / 25 : ℝ) (11 / 10) \ cornersRho, HasDerivAt rho (rhoD θ) θ) ∧ Measurable rhoD
      ∧ rho (12 / 25) = 0 ∧ rho (11 / 10) = 0 ∧ (∀ θ, |rho θ| ≤ 1) ∧ ∀ θ, |rhoD θ| ≤ 70 := by
  refine ⟨continuous_rho.continuousOn, ?_, fun θ h => hasDerivAt_rho h.2, measurable_rhoD,
    rho_eq_zero_of_le le_rfl, rho_eq_zero_of_ge le_rfl, fun θ => ?_, fun θ => (abs_rhoD_le θ).trans (by norm_num)⟩
  · unfold cornersRho; simp [Set.countable_insert]
  · rw [abs_of_nonneg (rho_nonneg θ)]; exact rho_le_one θ

/-- The window data of `ρτ`. -/
theorem rhoT_data :
    ContinuousOn rhoT (Icc (3 / 5) (11 / 10)) ∧ cornersRhoT.Countable
      ∧ (∀ θ ∈ Ioo (3 / 5 : ℝ) (11 / 10) \ cornersRhoT, HasDerivAt rhoT (rhoTD θ) θ) ∧ Measurable rhoTD
      ∧ rhoT (3 / 5) = 0 ∧ rhoT (11 / 10) = 0 ∧ (∀ θ, |rhoT θ| ≤ 1) ∧ ∀ θ, |rhoTD θ| ≤ 70 := by
  refine ⟨(continuous_rho.mul continuous_tau).continuousOn, ?_,
    fun θ h => hasDerivAt_rhoT h.2, measurable_rhoTD, rhoT_eq_zero le_rfl, ?_, fun θ => ?_, abs_rhoTD_le⟩
  · unfold cornersRhoT; simp [Set.countable_insert]
  · show rho (11 / 10) * tau (11 / 10) = 0
    rw [rho_eq_zero_of_ge le_rfl, zero_mul]
  · have h1 := tau_mem θ
    rw [rhoT, abs_mul, abs_of_nonneg (rho_nonneg θ), abs_of_nonneg h1.1]
    exact mul_le_one₀ (rho_le_one θ) h1.1 h1.2

/-- **The off-diagonal bound at truncation `M`** for the span `h = Σ b_iψ_i`. -/
theorem offDiag_trunc (hF : IsRungFamily c g g₁ g₂ χ) (hc : 3 ≤ c) (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ c ^ 2)
    (hinj : Function.Injective χ) (b : ι → ℝ) {K : ℕ} (hK : 4 ≤ K) {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K, (if offP k l then
        ∫ θ in (12 / 25 : ℝ)..(11 / 10), rho θ * (spanH c g b (k * θ) * spanH c g b (l * θ)) else 0)
      + 2 * ∫ θ in (3 / 5 : ℝ)..(11 / 10), rhoT θ * (spanH c g b ((3 : ℕ) * θ) * spanH c g b ((4 : ℕ) * θ))
      ≤ offC / c * (∫ ξ in Ioi 1, spanH c g b ξ ^ 2)
        + (2 * M + 1) * (3 / 4) ^ M * ∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K, (if k = l then 0 else
            (k + l) * (8 * ω₀ + 192 * L₀) / c ^ 2 * ∫ θ in (12 / 25 : ℝ)..(11 / 10), Rf c g b k l θ) := by
  have hK3 : 3 ≤ K := by omega
  have hc0 : 0 < c := by linarith
  set S := Finset.Icc 3 K with hSdef
  have hS3 : 3 ∈ S := Finset.mem_Icc.mpr ⟨le_rfl, hK3⟩
  have hS4 : 4 ∈ S := Finset.mem_Icc.mpr ⟨by norm_num, hK⟩
  set Nm := ∫ ξ in Ioi 1, spanH c g b ξ ^ 2 with hNm
  set T : ℝ := (2 * M + 1) * (3 / 4) ^ M with hT
  set IS : ℕ → ℕ → ℝ := fun k l => ∫ θ in (12 / 25 : ℝ)..(11 / 10), ∑ N ∈ Finset.range M,
    ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) with hIS
  set IR : ℕ → ℕ → ℝ := fun k l => ∫ θ in (12 / 25 : ℝ)..(11 / 10), Rf c g b k l θ with hIR
  set F : ℕ → ℕ → ℝ := fun k l => Γ₀ / (c * ((k : ℝ) - l) ^ 2) * IS k l
    + (k + l) * (8 * ω₀ + 192 * L₀) / c ^ 2 * T * IR k l with hF'
  set A : ℕ → ℕ → ℝ := fun k l => ∫ θ in (12 / 25 : ℝ)..(11 / 10), N0 c g b rho rhoD k l θ with hA
  set B : ℕ → ℕ → ℝ := fun k l => ∫ θ in (3 / 5 : ℝ)..(11 / 10), N0 c g b rhoT rhoTD k l θ with hB
  obtain ⟨hρc, hρE, hρd, hρm, hρα, hρβ, hρb, hρ'b⟩ := rho_data
  obtain ⟨hTc, hTE, hTd, hTm, hTα, hTβ, hTb, hT'b⟩ := rhoT_data
  -- the pair bounds
  have hρ : ∀ k ∈ S, ∀ l ∈ S, offP k l →
      ∫ θ in (12 / 25 : ℝ)..(11 / 10), rho θ * (spanH c g b (k * θ) * spanH c g b (l * θ)) ≤ A k l + F k l := by
    intro k hk l hl hkl
    have h := pair_integral_le hF hc hχ b (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hl).1 hkl.1 le_rfl
      (by norm_num) hρE hρc hρd hρm hρα hρβ hρb hρ'b
      (fun θ hθ => qK_le (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hl).1 hkl.1 hθ.1 (Or.inl ⟨hkl.2.1, hkl.2.2⟩))
      hM
    simp only [hA, hF', hIS, hIR, hT]
    linarith
  have h34 : ∫ θ in (3 / 5 : ℝ)..(11 / 10), rhoT θ * (spanH c g b ((3 : ℕ) * θ) * spanH c g b ((4 : ℕ) * θ))
      ≤ B 3 4 + F 3 4 := by
    have h := pair_integral_le hF hc hχ b (le_refl 3) (by norm_num : 3 ≤ 4) (by norm_num) (by norm_num)
      (by norm_num) hTE hTc hTd hTm hTα hTβ hTb hT'b
      (fun θ hθ => qK_le (le_refl 3) (by norm_num) (by norm_num) (by linarith [hθ.1]) (Or.inr hθ.1)) hM
    simp only [hB, hF', hIS, hIR, hT]
    linarith
  have h43 : ∫ θ in (3 / 5 : ℝ)..(11 / 10), rhoT θ * (spanH c g b ((4 : ℕ) * θ) * spanH c g b ((3 : ℕ) * θ))
      ≤ B 4 3 + F 4 3 := by
    have h := pair_integral_le hF hc hχ b (by norm_num : 3 ≤ 4) (le_refl 3) (by norm_num) (by norm_num)
      (by norm_num) hTE hTc hTd hTm hTα hTβ hTb hT'b
      (fun θ hθ => qK_le (by norm_num) (le_refl 3) (by norm_num) (by linarith [hθ.1]) (Or.inr hθ.1)) hM
    simp only [hB, hF', hIS, hIR, hT]
    linarith
  -- the leading terms
  have hw'i : IntervalIntegrable rhoD volume (12 / 25) (11 / 10) :=
    (intervalIntegrable_const (c := (70 : ℝ))).mono_fun' hρm.aestronglyMeasurable
      (ae_of_all _ fun θ => by simpa using hρ'b θ)
  have hN0i : ∀ k ∈ S, ∀ l ∈ S, IntervalIntegrable (fun θ => if k = l then 0 else N0 c g b rho rhoD k l θ)
      volume (12 / 25) (11 / 10) := by
    intro k hk l hl
    by_cases h : k = l
    · simp only [h, if_true]; exact intervalIntegrable_const
    · simp only [h, if_false]
      exact N0_intervalIntegrable hF hc0 b (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hl).1 h le_rfl
        (by norm_num) hρc hw'i
  have hAsum : ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else A k l) ≤ CH / c * (30 * Nm) := by
    have e : ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else A k l)
        = ∫ θ in (12 / 25 : ℝ)..(11 / 10), ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else N0 c g b rho rhoD k l θ) := by
      rw [intervalIntegral.integral_finsetSum fun k hk =>
        (IntervalIntegrable.sum S fun l hl => hN0i k hk l hl).congr fun θ _ => by simp [Finset.sum_apply]]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [intervalIntegral.integral_finsetSum fun l hl => hN0i k hk l hl]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : k = l
      · simp [h]
      · simp only [h, if_false, hA]
    rw [e]
    set E : ℝ → ℝ := fun θ => ∑ m ∈ S, (Hn c g χ b 0 (m * θ) ^ 2 + Dn c g χ b 0 (m * θ) ^ 2)
    have hEc := continuousOn_sum_E0 hF b K
    have hpt : ∀ θ ∈ Ioc (12 / 25 : ℝ) (11 / 10),
        ‖∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else N0 c g b rho rhoD k l θ)‖ ≤ CH / c * E θ := by
      intro θ hθ
      rw [Real.norm_eq_abs]
      exact abs_sum_N0_le (χ := χ) hc0 b K hθ.1.le hθ.2 (hρb θ) (hρ'b θ)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (by norm_num) (ae_of_all _ hpt)
      ((hEc.const_smul (CH / c)).intervalIntegrable_of_Icc (μ := volume) (by norm_num))
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at h1
    have hCH : 0 ≤ CH := by simp only [CH, ω₀, Cvs.Route.Visibility.AliasPairPointwiseBound.βb]; positivity
    exact (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_left
      (integral_sum_E0_le hF hc hχ hinj b hK3) (by positivity)))
  have hA34 : -A 3 4 ≤ ω₀ / c * (30 * Nm) := (neg_le_abs _).trans
    (abs_integral_N0_le hF hc hχ hinj b hK3 hS3 hS4 (by norm_num) le_rfl (by norm_num) hρb hρ'b)
  have hA43 : -A 4 3 ≤ ω₀ / c * (30 * Nm) := (neg_le_abs _).trans
    (abs_integral_N0_le hF hc hχ hinj b hK3 hS4 hS3 (by norm_num) le_rfl (by norm_num) hρb hρ'b)
  have hB34 : B 3 4 ≤ ω₀ / c * (30 * Nm) := (le_abs_self _).trans
    (abs_integral_N0_le hF hc hχ hinj b hK3 hS3 hS4 (by norm_num) (by norm_num) (by norm_num) hTb hT'b)
  have hB43 : B 4 3 ≤ ω₀ / c * (30 * Nm) := (le_abs_self _).trans
    (abs_integral_N0_le hF hc hχ hinj b hK3 hS4 hS3 (by norm_num) (by norm_num) (by norm_num) hTb hT'b)
  -- the majorants
  have hISeq : ∀ k ∈ S, ∀ l ∈ S, IS k l = ∑ N ∈ Finset.range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N
      * ∫ θ in (12 / 25 : ℝ)..(11 / 10), Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ) := by
    intro k hk l hl
    simp only [hIS]
    have hint : ∀ N ∈ Finset.range M, IntervalIntegrable (fun θ => ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N
        * (Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ))) volume (12 / 25) (11 / 10) := fun N _ =>
      (continuousOn_const.mul ((continuousOn_Zf hF b N (Finset.mem_Icc.mp hk).1).mul
        (continuousOn_Zf hF b N (Finset.mem_Icc.mp hl).1))).intervalIntegrable_of_Icc (by norm_num)
    rw [intervalIntegral.integral_finsetSum hint]
    exact Finset.sum_congr rfl fun N _ => intervalIntegral.integral_const_mul _ _
  have hSsum : ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else Γ₀ / (c * ((k : ℝ) - l) ^ 2) * IS k l)
      ≤ Γ₀ / c * (5898240 * Nm) := by
    have e : ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else Γ₀ / (c * ((k : ℝ) - l) ^ 2) * IS k l)
        = Γ₀ / c * ∑ N ∈ Finset.range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else
          (∫ θ in (12 / 25 : ℝ)..(11 / 10), Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) / ((k : ℝ) - l) ^ 2) := by
      calc ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else Γ₀ / (c * ((k : ℝ) - l) ^ 2) * IS k l)
          = ∑ k ∈ S, ∑ l ∈ S, ∑ N ∈ Finset.range M, Γ₀ / c * (((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N
              * (if k = l then 0 else (∫ θ in (12 / 25 : ℝ)..(11 / 10),
                Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) / ((k : ℝ) - l) ^ 2)) := by
            refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
            by_cases h : k = l
            · simp [h]
            · simp only [h, if_false, hISeq k hk l hl, Finset.mul_sum]
              refine Finset.sum_congr rfl fun N _ => ?_
              field_simp
        _ = ∑ k ∈ S, ∑ N ∈ Finset.range M, ∑ l ∈ S, Γ₀ / c * (((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N
              * (if k = l then 0 else (∫ θ in (12 / 25 : ℝ)..(11 / 10),
                Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) / ((k : ℝ) - l) ^ 2)) :=
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
        _ = ∑ N ∈ Finset.range M, ∑ k ∈ S, ∑ l ∈ S, Γ₀ / c * (((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N
              * (if k = l then 0 else (∫ θ in (12 / 25 : ℝ)..(11 / 10),
                Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) / ((k : ℝ) - l) ^ 2)) := Finset.sum_comm
        _ = _ := by simp only [Finset.mul_sum]
    rw [e]
    have hNm0 : 0 ≤ Nm := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
    have hΓ0 : 0 ≤ Γ₀ := by simp only [Γ₀, ω₀, L₀, Cvs.Route.Visibility.AliasPairPointwiseBound.βb]; norm_num
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ N ∈ Finset.range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else
          (∫ θ in (12 / 25 : ℝ)..(11 / 10), Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) / ((k : ℝ) - l) ^ 2)
        ≤ ∑ N ∈ Finset.range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (240 * ((N : ℝ) + 2) ^ 2 * Nm) :=
          Finset.sum_le_sum fun N _ => mul_le_mul_of_nonneg_left (sum_pair_Zf_le hF hc hχ hinj b hK3 N)
            (by positivity)
      _ = 240 * Nm * ∑ N ∈ Finset.range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * ((N : ℝ) + 2) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun N _ => by ring
      _ ≤ 240 * Nm * (24 * 4 ^ 5) := mul_le_mul_of_nonneg_left (sum_series_le M) (by positivity)
      _ = 5898240 * Nm := by ring
  have hFsplit : ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else F k l)
      = ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else Γ₀ / (c * ((k : ℝ) - l) ^ 2) * IS k l)
        + T * ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else
            (k + l) * (8 * ω₀ + 192 * L₀) / c ^ 2 * ∫ θ in (12 / 25 : ℝ)..(11 / 10), Rf c g b k l θ) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases h : k = l
    · simp [h]
    · simp only [h, if_false, hF', hIR]; ring
  -- assemble
  have hsym : ∫ θ in (3 / 5 : ℝ)..(11 / 10), rhoT θ * (spanH c g b ((4 : ℕ) * θ) * spanH c g b ((3 : ℕ) * θ))
      = ∫ θ in (3 / 5 : ℝ)..(11 / 10), rhoT θ * (spanH c g b ((3 : ℕ) * θ) * spanH c g b ((4 : ℕ) * θ)) :=
    intervalIntegral.integral_congr fun θ _ => by ring
  have hle1 : ∑ k ∈ S, ∑ l ∈ S, (if offP k l then
        ∫ θ in (12 / 25 : ℝ)..(11 / 10), rho θ * (spanH c g b (k * θ) * spanH c g b (l * θ)) else 0)
      ≤ ∑ k ∈ S, ∑ l ∈ S, (if offP k l then A k l else 0) + ∑ k ∈ S, ∑ l ∈ S, (if offP k l then F k l else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun l hl => ?_
    by_cases h : offP k l
    · simp only [if_pos h]; exact hρ k hk l hl h
    · simp only [if_neg h]; norm_num
  have hAs := sum_ne_split S hS3 hS4 A
  have hFs := sum_ne_split S hS3 hS4 F
  rw [hFsplit] at hFs
  have hNm0 : 0 ≤ Nm := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hoff : offC / c * Nm = CH / c * (30 * Nm) + 4 * (ω₀ / c * (30 * Nm)) + Γ₀ / c * (5898240 * Nm) := by
    simp only [offC]; ring
  rw [hoff, two_mul]
  nth_rewrite 2 [← hsym]
  linarith

/-- `(2M + 1)(3/4)^M → 0`. -/
theorem tendsto_rem : Tendsto (fun M : ℕ => (2 * (M : ℝ) + 1) * (3 / 4) ^ M) atTop (nhds 0) := by
  have h1 := tendsto_self_mul_const_pow_of_lt_one (r := 3 / 4) (by norm_num) (by norm_num)
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  have := (h1.const_mul 2).add h2
  simp only [mul_zero, add_zero] at this
  refine this.congr fun M => ?_
  ring

/-- **The off-diagonal incoherence bound for a rung span**: for `K ≥ 4`,
`Σ_{P′}∫ρh(kθ)h(lθ) + 2∫ρτh(3θ)h(4θ) ≤ (C₁/c)∫_{(1,∞)} h²` with `C₁ = offC`. -/
theorem offDiag_family (hF : IsRungFamily c g g₁ g₂ χ) (hc : 3 ≤ c) (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ c ^ 2)
    (hinj : Function.Injective χ) (b : ι → ℝ) {K : ℕ} (hK : 4 ≤ K) :
    ∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K, (if offP k l then
        ∫ θ in (12 / 25 : ℝ)..(11 / 10), rho θ * (spanH c g b (k * θ) * spanH c g b (l * θ)) else 0)
      + 2 * ∫ θ in (3 / 5 : ℝ)..(11 / 10), rhoT θ * (spanH c g b ((3 : ℕ) * θ) * spanH c g b ((4 : ℕ) * θ))
      ≤ offC / c * ∫ ξ in Ioi 1, spanH c g b ξ ^ 2 := by
  set Q := ∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K, (if k = l then 0 else
    (k + l) * (8 * ω₀ + 192 * L₀) / c ^ 2 * ∫ θ in (12 / 25 : ℝ)..(11 / 10), Rf c g b k l θ)
  have hlim : Tendsto (fun M : ℕ => offC / c * (∫ ξ in Ioi 1, spanH c g b ξ ^ 2)
      + (2 * (M : ℝ) + 1) * (3 / 4) ^ M * Q) atTop (nhds (offC / c * (∫ ξ in Ioi 1, spanH c g b ξ ^ 2))) := by
    have := (tendsto_rem.mul_const Q).const_add (offC / c * (∫ ξ in Ioi 1, spanH c g b ξ ^ 2))
    simpa using this
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact offDiag_trunc hF hc hχ hinj b hK hM

end Family

/-- **`OffDiag offC`**: the off-diagonal incoherence estimate of AL-R (alr/PROOF.md Steps 3–7) with the explicit
constant `offC = 30(C_H + 4ω₀) + 5898240Γ₀`, for every `x ≥ 13`. -/
theorem offDiag : OffDiag offC := by
  filter_upwards [eventually_ge_atTop 13] with x hx b K hK
  have hx' : (13 : ℝ) ≤ x := by exact_mod_cast hx
  have hx80 : 80 ≤ 2 * π * x := by nlinarith [Real.pi_gt_d2]
  have hx1 : 1 ≤ x := by omega
  set c : ℝ := 2 * π * x with hcdef
  have hc3 : 3 ≤ c := by linarith
  have hF := rungFamily hx80
  have hχ := lev_mem hx80
  have hinj : Function.Injective fun n : Fin x => lev c (2 * (n : ℕ)) := (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lev_strictMono hx80).injective
  set G : Fin x → ℝ → ℝ := fun n => rung c (2 * (n : ℕ))
  have hfam := offDiag_family hF hc3 hχ hinj (coefH x b) hK
  have hψ : (fun ξ => psi c (spineG c b) ξ) = spanH c G (coefH x b) :=
    funext fun ξ => Cvs.Route.Visibility.AliasRemainderSplit.psi_spineG_eq_sum hx1 b ξ
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  -- rewrite every pair integral
  have hρ : ∀ k l, pairJ x b rho k l
      = x * ∫ θ in (12 / 25 : ℝ)..(11 / 10), rho θ * (spanH c G (coefH x b) (k * θ) * spanH c G (coefH x b) (l * θ)) :=
    fun k l => by rw [pairJ_eq hx1, integral_rho_eq]
  have hτ : pairJ x b rhoT 3 4
      = x * ∫ θ in (3 / 5 : ℝ)..(11 / 10), rhoT θ * (spanH c G (coefH x b) ((3 : ℕ) * θ)
        * spanH c G (coefH x b) ((4 : ℕ) * θ)) := by rw [pairJ_eq hx1, integral_rhoT_eq]
  simp only [hρ, hτ]
  have hint : ∫ ξ in Ioi 1, psi c (spineG c b) ξ ^ 2 = ∫ ξ in Ioi 1, spanH c G (coefH x b) ξ ^ 2 := by
    congr 1; funext ξ; rw [← hψ]
  rw [hint]
  have e : ∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K, (if offP k l then (x : ℝ) * ∫ θ in (12 / 25 : ℝ)..(11 / 10),
        rho θ * (spanH c G (coefH x b) (k * θ) * spanH c G (coefH x b) (l * θ)) else 0)
      = x * ∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K, (if offP k l then ∫ θ in (12 / 25 : ℝ)..(11 / 10),
        rho θ * (spanH c G (coefH x b) (k * θ) * spanH c G (coefH x b) (l * θ)) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [e]
  have := mul_le_mul_of_nonneg_left hfam hx0
  calc _ = (x : ℝ) * (∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K, (if offP k l then
        ∫ θ in (12 / 25 : ℝ)..(11 / 10), rho θ * (spanH c G (coefH x b) (k * θ) * spanH c G (coefH x b) (l * θ))
          else 0)
      + 2 * ∫ θ in (3 / 5 : ℝ)..(11 / 10), rhoT θ * (spanH c G (coefH x b) ((3 : ℕ) * θ)
        * spanH c G (coefH x b) ((4 : ℕ) * θ))) := by ring
    _ ≤ (x : ℝ) * (offC / c * ∫ ξ in Ioi 1, spanH c G (coefH x b) ξ ^ 2) := this
    _ = offC / c * ((x : ℝ) * ∫ ξ in Ioi 1, spanH c G (coefH x b) ξ ^ 2) := by ring

/-- **AL-R from `ZBound` alone** at `W̃ = 57/60`, `C₁ = offC`. -/
theorem alr_of_zBound (hZ : Cvs.Route.Visibility.AliasRemainderCentreBound.ZBound) : Cvs.Route.Visibility.WindowChainCellFloors.ALR (57 / 60) offC := Cvs.Route.Visibility.AliasRemainderOffDiagonal.alr_of_offDiag hZ offDiag

end Cvs.Route.Visibility.AliasOffDiagonalIncoherence
