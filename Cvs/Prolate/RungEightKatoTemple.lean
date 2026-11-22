import Mathlib
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungKatoTemple
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Prolate.HermiteTrialsSixEight
import Cvs.Prolate.LevelThreeNearMuSix
import Cvs.Prolate.SepticLevelComparison
import Cvs.Prolate.SturmFromCentre

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Kato–Temple for the rung `h₈`: `χ₈ = 17c − 147/4 + O(1/c)`

The decic `y = (ξ¹⁰ + aξ⁸ + bξ⁶ + dξ⁴ + eξ² + f)e^{−Gξ²/2}`, `G² + 23G = c²`, with `aG ∈ [−45/2, 0]` a root of a sextic,
puts every even level of index at least five at or above `21G + 20 ≥ 21c − 443/2`. With `lev c 3 ≤ 13c − 13/4` the other
levels are `4c − 739/4` from `μ₈`, and the `F₈` trial is orthogonal to its residual, so `|χ₈ − μ₈| ≤ 256/c` for `c ≥ 400`.
-/

noncomputable section

open Real Set MeasureTheory Polynomial

namespace Cvs.Prolate.RungEightKatoTemple
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx lev lev_spec lev_eq)
open Cvs.Prolate.HermiteTrialResiduals (pg herm rq mu kap2 gE gm)

/-! ### The decic comparison -/

/-- `ξ¹⁰ + aξ⁸ + bξ⁶ + dξ⁴ + eξ² + f` has at most five zeros in `(0, 1)`. -/
theorem encard_zeros_le (a b d e f : ℝ) :
    {t | t ∈ Ioo (0 : ℝ) 1 ∧ t ^ 10 + a * t ^ 8 + b * t ^ 6 + d * t ^ 4 + e * t ^ 2 + f = 0}.encard ≤ 5 := by
  set S := {t | t ∈ Ioo (0 : ℝ) 1 ∧ t ^ 10 + a * t ^ 8 + b * t ^ 6 + d * t ^ 4 + e * t ^ 2 + f = 0} with hS
  set p : ℝ[X] := X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C d * X ^ 2 + C e * X + C f with hp
  have hp0 : p ≠ 0 := fun h => by
    have := congrArg (fun q : ℝ[X] => q.coeff 5) h
    simp [hp] at this
  have hinj : InjOn (fun t : ℝ => t ^ 2) S := fun x hx y hy hxy =>
    (pow_left_inj₀ hx.1.1.le hy.1.1.le two_ne_zero).mp hxy
  have hsub : (fun t : ℝ => t ^ 2) '' S ⊆ (p.roots.toFinset : Set ℝ) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp0, IsRoot, hp]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination ht.2
  have hdeg : p.natDegree ≤ 5 := by rw [hp]; compute_degree
  calc S.encard = ((fun t : ℝ => t ^ 2) '' S).encard := (hinj.encard_image).symm
    _ ≤ (p.roots.toFinset : Set ℝ).encard := Set.encard_le_encard hsub
    _ = (p.roots.toFinset.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ 5 := by
      have h1 := Multiset.toFinset_card_le p.roots
      have h2 := card_roots' p
      exact_mod_cast h1.trans (h2.trans hdeg)

/-- The potential `(G² + 23G)ξ² − G²ξ⁴ − (21G + 110 + 4aG)` of the decic comparison function. -/
def potTen (G a : ℝ) : C(ℝ, ℝ) :=
  ⟨fun s => (G ^ 2 + 23 * G) * s ^ 2 - G ^ 2 * s ^ 4 - (21 * G + 110 + 4 * a * G), by fun_prop⟩

/-- **The decic comparison**: for `G² + 23G = c²`, coefficients `a, b, d, e, f` solving the five conditions and
`Λ ≤ 21G + 110 + 4aG`, every even level of index at least five lies at or above `Λ`. -/
theorem le_of_isLevelIdx_of_sq {c G a b d e f Λ χ : ℝ} {j : ℕ} (hc : G ^ 2 + 23 * G = c ^ 2)
    (h8 : 2 * G * a ^ 2 + 2 * G * a - 4 * G * b + 19 * a + 45 = 0)
    (h6 : G * a * b + 2 * G * b - 3 * G * d + 14 * a + 17 * b = 0)
    (h4 : 2 * G * a * d + 6 * G * d - 8 * G * e + 15 * b + 45 * d = 0)
    (h2 : G * a * e + 4 * G * e - 5 * G * f + 3 * d + 26 * e = 0)
    (h0 : 2 * G * a * f + 10 * G * f + e + 55 * f = 0)
    (hΛ : Λ ≤ 21 * G + 110 + 4 * a * G) (hχ : IsLevelIdx c j χ) (hj : 5 ≤ j) : Λ ≤ χ := by
  have hP : ∀ s : ℝ, HasDerivAt (fun s => s ^ 10 + a * s ^ 8 + b * s ^ 6 + d * s ^ 4 + e * s ^ 2 + f)
      (10 * s ^ 9 + 8 * a * s ^ 7 + 6 * b * s ^ 5 + 4 * d * s ^ 3 + 2 * e * s) s := fun s =>
    ((((((hasDerivAt_pow 10 s).add ((hasDerivAt_pow 8 s).const_mul a)).add
      ((hasDerivAt_pow 6 s).const_mul b)).add ((hasDerivAt_pow 4 s).const_mul d)).add
      ((hasDerivAt_pow 2 s).const_mul e)).add_const f).congr_deriv (by push_cast; ring)
  have hP₁ : ∀ s : ℝ, HasDerivAt (fun s => 10 * s ^ 9 + 8 * a * s ^ 7 + 6 * b * s ^ 5 + 4 * d * s ^ 3 + 2 * e * s)
      (90 * s ^ 8 + 56 * a * s ^ 6 + 30 * b * s ^ 4 + 12 * d * s ^ 2 + 2 * e) s := fun s =>
    (((((hasDerivAt_pow 9 s).const_mul 10).add ((hasDerivAt_pow 7 s).const_mul (8 * a))).add
      ((hasDerivAt_pow 5 s).const_mul (6 * b))).add ((hasDerivAt_pow 3 s).const_mul (4 * d))).add
      ((hasDerivAt_id' s).const_mul (2 * e)) |>.congr_deriv (by push_cast; ring)
  refine Cvs.Prolate.SturmFromCentre.le_of_polyGauss_even (k := 4) (Q' := potTen G a) (χ' := 0) (G := G)
    (fun s _ => hP s) (fun s _ => hP₁ s) (fun s _ => ?_) (by ring) (fun t ht => ?_)
    ((encard_zeros_le a b d e f).trans le_rfl) hχ hj
  · simp only [potTen, ContinuousMap.coe_mk]
    linear_combination 2 * s ^ 8 * h8 + 4 * s ^ 6 * h6 + 2 * s ^ 4 * h4 + 4 * s ^ 2 * h2 + 2 * h0
  · have h4' : 0 ≤ G ^ 2 * t ^ 4 := by positivity
    have hct : c ^ 2 * t ^ 2 = (G ^ 2 + 23 * G) * t ^ 2 := by rw [hc]
    simp only [potTen, ContinuousMap.coe_mk]
    linarith

/-- The sextic in `A = aG` whose roots give the decic coefficients. -/
def sextic (G A : ℝ) : ℝ :=
  8 * A ^ 6 + (120 * G + 820) * A ^ 5 + (680 * G ^ 2 + 10180 * G + 32754) * A ^ 4
    + (1800 * G ^ 3 + 46364 * G ^ 2 + 322906 * G + 633667) * A ^ 3
    + (2192 * G ^ 4 + 94364 * G ^ 3 + 1108234 * G ^ 2 + 4645855 * G + 5889575) * A ^ 2
    + (960 * G ^ 5 + 81840 * G ^ 4 + 1541190 * G ^ 3 + 10685025 * G ^ 2 + 28473750 * G + 20785050) * A
    + (21600 * G ^ 5 + 710100 * G ^ 4 + 7624125 * G ^ 3 + 32956875 * G ^ 2 + 49227750 * G)

/-- **The sextic has a root in `[−45/2, 0]`** for `G ≥ 9`: it is `−2700G(8G³ − 80G² + 93G + 195)` at `−45/2`
and `675G(32G⁴ + 1052G³ + 11295G² + 48825G + 72930)` at `0`. -/
theorem exists_sextic_eq_zero {G : ℝ} (hG : 9 ≤ G) :
    ∃ A ∈ Icc (-45 / 2 : ℝ) 0, sextic G A = 0 := by
  have hcont : ContinuousOn (sextic G) (Icc (-45 / 2) 0) := by unfold sextic; fun_prop
  have hm : sextic G (-45 / 2) ≤ 0 := by
    have : sextic G (-45 / 2) = -2700 * G * (8 * G ^ 3 - 80 * G ^ 2 + 93 * G + 195) := by
      unfold sextic; ring
    rw [this]
    set t := G - 9 with ht
    have ht0 : 0 ≤ t := by linarith
    have hG' : G = t + 9 := by linarith
    have hpoly : 8 * G ^ 3 - 80 * G ^ 2 + 93 * G + 195 = 8 * t ^ 3 + 136 * t ^ 2 + 597 * t + 384 := by
      rw [hG']; ring
    rw [hpoly]
    have : 0 ≤ 8 * t ^ 3 + 136 * t ^ 2 + 597 * t + 384 := by positivity
    have hG0 : 0 ≤ G := by linarith
    nlinarith
  have hp : 0 ≤ sextic G 0 := by
    have : sextic G 0 = 675 * G * (32 * G ^ 4 + 1052 * G ^ 3 + 11295 * G ^ 2 + 48825 * G + 72930) := by
      unfold sextic; ring
    rw [this]
    have : 0 ≤ G := by linarith
    positivity
  exact intermediate_value_Icc (by norm_num) hcont ⟨hm, hp⟩

/-- **Coefficients of the decic comparison**: for `G ≥ 9` there are `a, b, d, e, f` solving the five conditions
with `aG ∈ [−45/2, 0]`. -/
theorem exists_coeffs {G : ℝ} (hG : 9 ≤ G) : ∃ a b d e f : ℝ,
    2 * G * a ^ 2 + 2 * G * a - 4 * G * b + 19 * a + 45 = 0 ∧
    G * a * b + 2 * G * b - 3 * G * d + 14 * a + 17 * b = 0 ∧
    2 * G * a * d + 6 * G * d - 8 * G * e + 15 * b + 45 * d = 0 ∧
    G * a * e + 4 * G * e - 5 * G * f + 3 * d + 26 * e = 0 ∧
    2 * G * a * f + 10 * G * f + e + 55 * f = 0 ∧ -45 / 2 ≤ a * G ∧ a * G ≤ 0 := by
  obtain ⟨A, hA, hF⟩ := exists_sextic_eq_zero hG
  have hG0 : G ≠ 0 := by linarith
  set B := (2 * A ^ 2 + 2 * A * G + 19 * A + 45 * G) / 4 with hB
  set D := (B * (A + 2 * G + 17) + 14 * A * G) / 3 with hD
  set E := (D * (2 * A + 6 * G + 45) + 15 * B * G) / 8 with hE
  set F := (E * (A + 4 * G + 26) + 3 * D * G) / 5 with hFd
  have haG : A / G * G = A := div_mul_cancel₀ A hG0
  refine ⟨A / G, B / G ^ 2, D / G ^ 3, E / G ^ 4, F / G ^ 5, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB]; field_simp; ring
  · rw [hD]; field_simp; ring
  · rw [hE]; field_simp; ring
  · rw [hFd]; field_simp; ring
  · have h : 2 * G * (A / G) * (F / G ^ 5) + 10 * G * (F / G ^ 5) + E / G ^ 4 + 55 * (F / G ^ 5)
        = sextic G A / (480 * G ^ 5) := by
      rw [hFd, hE, hD, hB]; unfold sextic; field_simp; ring
    rw [h, hF, zero_div]
  · rw [haG]; exact hA.1
  · rw [haG]; exact hA.2

/-- The positive root `G = (√(529 + 4c²) − 23)/2` of `G² + 23G = c²`. -/
def gTen (c : ℝ) : ℝ := (√(529 + 4 * c ^ 2) - 23) / 2

theorem gTen_sq_add (c : ℝ) : gTen c ^ 2 + 23 * gTen c = c ^ 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 529 + 4 * c ^ 2 by positivity)
  unfold gTen
  linear_combination h / 4

theorem nine_le_gTen {c : ℝ} (hc : 288 ≤ c ^ 2) : 9 ≤ gTen c := by
  have h : (41 : ℝ) ≤ √(529 + 4 * c ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  unfold gTen
  linarith

theorem abs_sub_le_gTen (c : ℝ) : |c| - 23 / 2 ≤ gTen c := by
  have h : 2 * |c| ≤ √(529 + 4 * c ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity), mul_pow, sq_abs]
    linarith
  unfold gTen
  linarith

/-- **Every even level of index at least five lies at or above `21γ² + 20`**, `γ² = gTen c`, for `c² ≥ 288`. -/
theorem le_of_isLevelIdx_five_le {c χ : ℝ} {j : ℕ} (hc : 288 ≤ c ^ 2)
    (hχ : IsLevelIdx c j χ) (hj : 5 ≤ j) : 21 * gTen c + 20 ≤ χ := by
  obtain ⟨a, b, d, e, f, h8, h6, h4, h2, h0, ha, -⟩ := exists_coeffs (nine_le_gTen hc)
  exact le_of_isLevelIdx_of_sq (gTen_sq_add c) h8 h6 h4 h2 h0 (by linarith) hχ hj

/-- **Every even level of index at least five lies at or above `21c − 443/2`** for `c ≥ 17`. -/
theorem twentyone_mul_sub_le {c χ : ℝ} {j : ℕ} (hc : 17 ≤ c) (hχ : IsLevelIdx c j χ) (hj : 5 ≤ j) :
    21 * c - 443 / 2 ≤ χ := by
  have h := abs_sub_le_gTen c
  rw [abs_of_nonneg (by linarith)] at h
  linarith [le_of_isLevelIdx_five_le (by nlinarith) hχ hj]

/-! ### The gap at `μ₈` -/

/-- **The gap at `μ₈`**: for `c ≥ 40` every even level of index `j ≠ 4` is at least `4c − 739/4` from
`μ₈ = 17c − 147/4`. -/
theorem le_abs_sub_mu_four {c : ℝ} (hc : 40 ≤ c) {j : ℕ} {χ : ℝ} (hχ : IsLevelIdx c j χ) (hj : j ≠ 4) :
    4 * c - 739 / 4 ≤ |χ - mu c 4| := by
  rw [Cvs.Prolate.HermiteTrialsSixEight.mu_four]
  rcases lt_or_gt_of_ne hj with hj | hj
  · have h3 : χ ≤ lev c 3 :=
      hχ.le (lev_spec (Cvs.Prolate.EvenRungDavisKahan.exists_isLevelIdx_of_le_three (by linarith) le_rfl)) (by omega)
    have := Cvs.Prolate.LevelThreeNearMuSix.lev_three_le hc
    exact (by linarith : 4 * c - 739 / 4 ≤ -(χ - (17 * c - 147 / 4))).trans (neg_le_abs _)
  · have h5 := twentyone_mul_sub_le (by linarith) hχ hj
    exact (by linarith : 4 * c - 739 / 4 ≤ χ - (17 * c - 147 / 4)).trans (le_abs_self _)

/-! ### The trial `F₈` is orthogonal to its residual -/

theorem gE_herm_mul_rq_four (r : ℝ) : gE r (herm 4 * rq 4) =
    41902660800 * r ^ 10 - 207307900800 * r ^ 9 + 459631972800 * r ^ 8 - 602983180800 * r ^ 7
      + 519856444800 * r ^ 6 - 309416889600 * r ^ 5 + 129620131200 * r ^ 4 - 38051596800 * r ^ 3
      + 7546392000 * r ^ 2 - 901756800 * r + 103723200 := by
  rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 11)
    (fun k => ([103723200, -1803513600, 10061856000, -20294184960, 19751639040, -10477608960, 3200655360,
      -571146240, 58048512, -3080192, 65536] : List ℝ).getD k 0)
    (fun t => by simp [rq, Cvs.Prolate.HermiteTrialResiduals.herm_four, Cvs.Prolate.HermiteTrialsSixEight.herm_six, Cvs.Prolate.HermiteTrialResiduals.herm_two, Finset.sum_range_succ,
      Nat.descFactorial]; ring)]
  simp [gm, Finset.sum_range_succ, Nat.factorial]; ring

/-- `∫_ℝ F₈ R₈ = 0`. -/
theorem integral_trial_mul_resid_four {c : ℝ} (hc : 0 < c) :
    ∫ w, pg c (herm 4) w * pg c (rq 4) w = 0 := by
  simp_rw [Cvs.Prolate.EvenRungKatoTemple.pg_mul]
  rw [Cvs.Prolate.HermiteTrialResiduals.integral_eval_mul_gaussian hc, div_self hc.ne', gE_herm_mul_rq_four]
  norm_num

/-- **Kato–Temple at the `F₈` trial**: with every other level `δ > 0` from `μ₈`,
`|χ₈ − μ₈| (∫F² − ∫R²/δ²) ≤ ½(cut masses of F² and R²) + ∫R²/δ` on `[−1, 1]`. -/
theorem abs_lev_four_sub_mu_mul_le {c : ℝ} (hc : 0 < c) (hk : ∃ χ, IsLevelIdx c 4 χ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ j χ, IsLevelIdx c j χ → j ≠ 4 → δ ≤ |χ - mu c 4|) :
    |lev c 4 - mu c 4| * ((∫ s in (-1 : ℝ)..1, pg c (herm 4) s ^ 2) - (∫ s in (-1 : ℝ)..1, pg c (rq 4) s ^ 2) / δ ^ 2)
      ≤ ((∫ w, pg c (herm 4) w ^ 2) - (∫ w in (-1 : ℝ)..1, pg c (herm 4) w ^ 2)
          + ((∫ w, pg c (rq 4) w ^ 2) - ∫ w in (-1 : ℝ)..1, pg c (rq 4) w ^ 2)) / 2
        + (∫ s in (-1 : ℝ)..1, pg c (rq 4) s ^ 2) / δ := by
  have h := Cvs.Prolate.EvenRungKatoTemple.abs_lev_sub_mul_le hc.ne' (fun s _ => Cvs.Prolate.HermiteTrialResiduals.hasDerivAt_pg c _ s)
    (fun s _ => Cvs.Prolate.HermiteTrialResiduals.hasDerivAt_pg₁ c _ s) (Cvs.Prolate.HermiteTrialResiduals.continuous_pg₂ c _).continuousOn
    (fun s _ => Cvs.Prolate.HermiteTrialsSixEight.trial_ode le_rfl c s) (fun s _ => Cvs.Prolate.HermiteTrialResiduals.pg_neg c _ s) (fun s _ => Cvs.Prolate.HermiteTrialResiduals.pg_neg c _ s)
    hk hδ hgap
  have ht := Cvs.Prolate.EvenRungKatoTemple.abs_intervalIntegral_mul_le hc (herm 4) (rq 4) (integral_trial_mul_resid_four hc)
  linarith

/-! ### Explicit `O(1/c)` -/

theorem gE_rq_sq_four (r : ℝ) :
    gE r (rq 4 ^ 2) = 5059746291600 * r ^ 12 - 29038543934400 * r ^ 11 + 76744723255200 * r ^ 10
      - 123359227992000 * r ^ 9 + 134336784582000 * r ^ 8 - 104630295369600 * r ^ 7
      + 60049706270400 * r ^ 6 - 25772501462400 * r ^ 5 + 8287465158000 * r ^ 4
      - 1968592248000 * r ^ 3 + 331455952800 * r ^ 2 - 35784504000 * r + 3811827600 := by
  rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 13) (fun k => ([3811827600, -71569008000,
      441941270400, -1049915865600, 1262851833600, -872719626240, 369714401280, -99105914880,
      16965857280, -1832878080, 120029184, -4325376, 65536] : List ℝ).getD k 0)
      (fun t => by simp [rq, Cvs.Prolate.HermiteTrialsSixEight.herm_six, Cvs.Prolate.HermiteTrialResiduals.herm_two, Finset.sum_range_succ,
        Nat.descFactorial]; ring)]
  simp [gm, Finset.sum_range_succ, Nat.factorial]; ring

/-- `e^{−c/2} ≤ 10! · 2¹⁰/c¹⁰` for `c > 0`, from `x¹⁰/10! ≤ eˣ`. -/
theorem exp_neg_half_le {c : ℝ} (hc : 0 < c) : exp (-(c / 2)) ≤ 3715891200 / c ^ 10 := by
  have h := Real.pow_div_factorial_le_exp (c / 2) (by positivity) 10
  have hf : ((Nat.factorial 10 : ℕ) : ℝ) = 3628800 := by norm_num [Nat.factorial]
  rw [hf] at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) (by positivity)]
  have : (c / 2) ^ 10 / 3628800 = c ^ 10 / 3715891200 := by ring
  rw [this] at h
  nlinarith [exp_pos (c / 2)]

/-- `c e^{−c/2} ≤ 10^{−13}` for `c ≥ 400`. -/
theorem exp_small {c : ℝ} (hc : 400 ≤ c) : exp (-(c / 2)) * c ≤ 1 / 10 ^ 13 := by
  have hc0 : 0 < c := by linarith
  have hE := exp_neg_half_le hc0
  have hE0 : 0 < exp (-(c / 2)) := exp_pos _
  have hc9 : (400 : ℝ) ^ 9 ≤ c ^ 9 := pow_le_pow_left₀ (by norm_num) hc 9
  have h1 : exp (-(c / 2)) * c ^ 10 ≤ 3715891200 := by
    rw [le_div_iff₀ (by positivity)] at hE; exact hE
  have h2 : exp (-(c / 2)) * c * 400 ^ 9 ≤ 3715891200 := by
    have : exp (-(c / 2)) * c * 400 ^ 9 ≤ exp (-(c / 2)) * c * c ^ 9 :=
      mul_le_mul_of_nonneg_left hc9 (by positivity)
    nlinarith
  have : exp (-(c / 2)) * c ≤ 3715891200 / 400 ^ 9 := by rw [le_div_iff₀ (by norm_num)]; linarith
  linarith [show (3715891200 : ℝ) / 400 ^ 9 ≤ 1 / 10 ^ 13 by norm_num]

/-- **The level `χ₈` to `O(1/c)`**: `|χ₈ − (17c − 147/4)| ≤ 256/c` for `c ≥ 400`. -/
theorem abs_lev_four_sub_le {c : ℝ} (hc : 400 ≤ c) : |lev c 4 - mu c 4| ≤ 256 / c := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 < 4 * c - 739 / 4 := by linarith
  have hT := abs_lev_four_sub_mu_mul_le hc0
    (Cvs.Prolate.SepticLevelComparison.exists_isLevelIdx_of_le_four (by linarith [Real.pi_lt_d2]) le_rfl) hδ
    fun _ _ hχ hj => le_abs_sub_mu_four (by linarith) hχ hj
  have hS : 0 < 10321920 * √(π / c) := by have := Real.sqrt_pos.mpr (show 0 < π / c by positivity); positivity
  have hFR : ∫ w, pg c (herm 4) w ^ 2 = 1 * (10321920 * √(π / c)) := by
    rw [Cvs.Prolate.HermiteTrialsSixEight.integral_trial_sq hc0 le_rfl]; norm_num [Nat.factorial]
  have hRR : ∫ w, pg c (rq 4) w ^ 2 = 1695 / 2 * 1 * (10321920 * √(π / c)) := by
    rw [Cvs.Prolate.HermiteTrialResiduals.integral_pg_sq hc0, Cvs.Prolate.HermiteTrialsSixEight.gE_one_rq_sq le_rfl, Cvs.Prolate.HermiteTrialsSixEight.kap2_three_four.2]
    norm_num [Nat.factorial]; ring
  have hcF := Cvs.Prolate.EvenRungKatoTemple.cut_le hc0 (herm 4)
  have hcR := Cvs.Prolate.EvenRungKatoTemple.cut_le hc0 (rq 4)
  rw [Cvs.Prolate.HermiteTrialsSixEight.gE_herm_sq_four] at hcF
  rw [gE_rq_sq_four] at hcR
  rw [hFR] at hT
  rw [hRR] at hT
  have hb := Cvs.Prolate.EvenRungKatoTemple.cut_nonneg hc0 (rq 4)
  rw [hRR] at hb
  rw [hFR] at hcF
  rw [hRR] at hcR
  have hEc := exp_small hc
  have hE0 : 0 < exp (-(c / 2)) := exp_pos _
  have hs2 := Cvs.Prolate.EvenRungKatoTemple.sqrt_two_le
  have hs20 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hcF' : 1 * (10321920 * √(π / c)) - ∫ w in (-1 : ℝ)..1, pg c (herm 4) w ^ 2
      ≤ exp (-(c / 2)) * (205731 / 128 * √2) * (10321920 * √(π / c)) := by
    have : exp (-(c / 2)) * ((2822400 - 22579200 * 2 + 169344000 * 2 ^ 2 - 699955200 * 2 ^ 3
      + 1823270400 * 2 ^ 4 - 3048192000 * 2 ^ 5 + 3203988480 * 2 ^ 6 - 1937295360 * 2 ^ 7
      + 518918400 * 2 ^ 8 : ℝ) * √2) * √(π / c)
        = exp (-(c / 2)) * (205731 / 128 * √2) * (10321920 * √(π / c)) := by ring
    linarith
  have hcR' : 1695 / 2 * 1 * (10321920 * √(π / c)) - ∫ w in (-1 : ℝ)..1, pg c (rq 4) w ^ 2
      ≤ exp (-(c / 2)) * (161619778875 / 2048 * √2) * (10321920 * √(π / c)) := by
    have : exp (-(c / 2)) * ((5059746291600 * 2 ^ 12 - 29038543934400 * 2 ^ 11 + 76744723255200 * 2 ^ 10
      - 123359227992000 * 2 ^ 9 + 134336784582000 * 2 ^ 8 - 104630295369600 * 2 ^ 7
      + 60049706270400 * 2 ^ 6 - 25772501462400 * 2 ^ 5 + 8287465158000 * 2 ^ 4
      - 1968592248000 * 2 ^ 3 + 331455952800 * 2 ^ 2 - 35784504000 * 2 + 3811827600 : ℝ) * √2) * √(π / c)
        = exp (-(c / 2)) * (161619778875 / 2048 * √2) * (10321920 * √(π / c)) := by ring
    linarith
  have hδc : 353 / 100 * c ≤ 4 * c - 739 / 4 := by linarith
  have hδ2 : 1412 ^ 2 ≤ (4 * c - 739 / 4) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hK : 1695 / 2 * 1 / (4 * c - 739 / 4) ^ 2 ≤ 1 / 2000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hE9 : exp (-(c / 2)) ≤ 1 / 10 ^ 15 := by
    have : exp (-(c / 2)) * 400 ≤ exp (-(c / 2)) * c := mul_le_mul_of_nonneg_left hc hE0.le
    linarith
  have hEF : exp (-(c / 2)) * (205731 / 128 * √2) ≤ 1 / 10000 := by nlinarith
  have hD : 0 < 1 - exp (-(c / 2)) * (205731 / 128 * √2) - 1695 / 2 * 1 / (4 * c - 739 / 4) ^ 2 := by linarith
  have key := Cvs.Prolate.EvenRungKatoTemple.le_of_temple (gF := 205731 / 128 * √2) (gR := 161619778875 / 2048 * √2) (abs_nonneg _) hS hT
    hcF' hcR' (by linarith) hδ hD
  refine key.trans ?_
  rw [div_le_div_iff₀ hD hc0]
  have h1 : exp (-(c / 2)) * (205731 / 128 * √2 + 161619778875 / 2048 * √2) / 2 * c ≤ 1 / 10 ^ 13 * 60000000 := by
    have : exp (-(c / 2)) * (205731 / 128 * √2 + 161619778875 / 2048 * √2) / 2 * c
        = exp (-(c / 2)) * c * (161623070571 / 4096 * √2) := by ring
    rw [this]; nlinarith
  have h2 : 1695 / 2 * 1 / (4 * c - 739 / 4) * c ≤ 100 / 353 * (1695 / 2) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ]; nlinarith
  nlinarith

end Cvs.Prolate.RungEightKatoTemple
