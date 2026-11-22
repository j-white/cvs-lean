import Mathlib
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Divisor-square Dirichlet bounds and the mollified detector series

`mollifiedDetector X s = ζ(s) M_X(s) - 1` equals `-1` at `ζ`-zeros and expands on `Re s > 2` into the tail series
`∑'_{n > X} truncMoebiusSum X n · n^{-s}`, whose square-sum on `α ≥ 1/2 + c` is `≤ divSqConst c · X^{-c}`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint (dirichletPolyC zetaMollifier truncMoebiusSum truncMoebiusSum_eq_of_le norm_moebius_le_one)

namespace Cvs.Zeta.MollifiedDetectorSeries

/-! ### Truncated Möbius and divisor-count bounds -/

/-- `|truncMoebiusSum X n| ≤ d(n)` since `|μ(d)| ≤ 1` on each divisor `d ≤ X` of `n`. -/
theorem norm_truncMoebiusSum_le_divisors_card (X n : ℕ) :
    ‖(truncMoebiusSum X n : ℂ)‖ ≤ (n.divisors.card : ℝ) := by
  rw [truncMoebiusSum, Int.cast_sum]
  calc ‖∑ d ∈ n.divisors.filter (· ≤ X), (ArithmeticFunction.moebius d : ℂ)‖
      ≤ ∑ d ∈ n.divisors.filter (· ≤ X), ‖(ArithmeticFunction.moebius d : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors.filter (· ≤ X), (1 : ℝ) :=
        Finset.sum_le_sum fun d _ => norm_moebius_le_one d
    _ = ((n.divisors.filter (· ≤ X)).card : ℝ) := by simp
    _ ≤ (n.divisors.card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _

/-- Every natural number `n` has at most `n` divisors (`0.divisors = ∅`). -/
theorem divisors_card_le (n : ℕ) : n.divisors.card ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hsub : n.divisors ⊆ Finset.Icc 1 n := fun d hd =>
      Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)⟩
    calc n.divisors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
      _ = n := by rw [Nat.card_Icc]; omega

/-- Hence `‖truncMoebiusSum X n‖ ≤ n` for every `X, n : ℕ`. -/
theorem norm_truncMoebiusSum_le_self (X n : ℕ) :
    ‖(truncMoebiusSum X n : ℂ)‖ ≤ (n : ℝ) :=
  (norm_truncMoebiusSum_le_divisors_card X n).trans (by exact_mod_cast divisors_card_le n)

/-! ### Quadruple factorization and `∑_{n ≤ N} d(n)² n^{-s} ≤ (∑_{m ≤ N} m^{-s})⁴` -/

/-- The quadruple map sending `(n, (a, b))` with `a, b ∣ n` to `((g, a/g), (b/g, n/lcm(a,b)))`,
where `g = gcd(a, b)`. -/
def quadMap (x : (_n : ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) :=
  let g := Nat.gcd x.2.1 x.2.2
  ((g, x.2.1 / g), (x.2.2 / g, x.1 / Nat.lcm x.2.1 x.2.2))

/-- Exact multiplicative recovery and range bounds for `quadMap` on triples `(n, a, b)` with
`1 ≤ n ≤ N` and `a, b ∈ n.divisors`. -/
theorem quadMap_spec {N : ℕ} {x : (_n : ℕ) × (ℕ × ℕ)}
    (hx : x ∈ (Finset.Icc 1 N).sigma (fun n => n.divisors ×ˢ n.divisors)) :
    quadMap x ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N)
      ∧ (quadMap x).1.1 * (quadMap x).1.2 = x.2.1
      ∧ (quadMap x).1.1 * (quadMap x).2.1 = x.2.2
      ∧ (quadMap x).1.1 * (quadMap x).1.2 * (quadMap x).2.1 * (quadMap x).2.2 = x.1 := by
  rcases x with ⟨n, a, b⟩
  simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_product, Nat.mem_divisors] at hx
  obtain ⟨⟨hn1, hnN⟩, ⟨han, _⟩, ⟨hbn, _⟩⟩ := hx
  have hn0 : 0 < n := by omega
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos han hn0
  have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hbn hn0
  have haN : a ≤ N := (Nat.le_of_dvd hn0 han).trans hnN
  have hbN : b ≤ N := (Nat.le_of_dvd hn0 hbn).trans hnN
  set g := Nat.gcd a b
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left b ha0
  have hga : g * (a / g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * (b / g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hgN : g ≤ N := (Nat.le_of_dvd ha0 (Nat.gcd_dvd_left a b)).trans haN
  have hu0 : 1 ≤ a / g := Nat.div_pos (Nat.le_of_dvd ha0 (Nat.gcd_dvd_left a b)) hg0
  have hv0 : 1 ≤ b / g := Nat.div_pos (Nat.le_of_dvd hb0 (Nat.gcd_dvd_right a b)) hg0
  have huN : a / g ≤ N := (Nat.div_le_self a g).trans haN
  have hvN : b / g ≤ N := (Nat.div_le_self b g).trans hbN
  set L := Nat.lcm a b
  have hLn : L ∣ n := Nat.lcm_dvd han hbn
  have hL0 : 0 < L := Nat.pos_of_dvd_of_pos hLn hn0
  have hLk : L * (n / L) = n := Nat.mul_div_cancel' hLn
  have hk0 : 1 ≤ n / L := Nat.div_pos (Nat.le_of_dvd hn0 hLn) hL0
  have hkN : n / L ≤ N := (Nat.div_le_self n L).trans hnN
  have hL_eq : L = g * (a / g) * (b / g) := by
    have hgl : g * L = g * (g * (a / g) * (b / g)) := by
      calc g * L = a * b := Nat.gcd_mul_lcm a b
        _ = (g * (a / g)) * (g * (b / g)) := by rw [hga, hgb]
        _ = g * (g * (a / g) * (b / g)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg0 hgl
  have hn_eq : g * (a / g) * (b / g) * (n / L) = n := by
    rw [← hL_eq, hLk]
  refine ⟨?_, hga, hgb, hn_eq⟩
  simp only [quadMap, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨⟨hg0, hgN⟩, ⟨hu0, huN⟩⟩, ⟨⟨hv0, hvN⟩, ⟨hk0, hkN⟩⟩⟩

/-- `quadMap` is injective on triples `(n, (a, b))` with `1 ≤ n ≤ N` and `a, b ∈ n.divisors`. -/
theorem quadMap_injOn (N : ℕ) :
    Set.InjOn quadMap
      (((Finset.Icc 1 N).sigma (fun n => n.divisors ×ˢ n.divisors) : Finset _) : Set _) := by
  intro x hx y hy hxy
  have sx := quadMap_spec (Finset.mem_coe.mp hx)
  have sy := quadMap_spec (Finset.mem_coe.mp hy)
  rcases x with ⟨nx, ax, bx⟩
  rcases y with ⟨ny, ay, by_⟩
  dsimp only at sx sy
  have h1 : ax = ay := by rw [← sx.2.1, ← sy.2.1, hxy]
  have h2 : bx = by_ := by rw [← sx.2.2.1, ← sy.2.2.1, hxy]
  have h3 : nx = ny := by rw [← sx.2.2.2, ← sy.2.2.2, hxy]
  subst h1 h2 h3
  rfl

/-- **Finite Ramanujan majorant**: `∑_{n=1}^N d(n)² n^{-s} ≤ (∑_{m=1}^N m^{-s})⁴` for every `s : ℝ`. -/
theorem sum_divisors_card_sq_rpow_le (N : ℕ) (s : ℝ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s)
      ≤ (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-s)) ^ 4 := by
  set S := (Finset.Icc 1 N).sigma (fun n => n.divisors ×ˢ n.divisors)
  set Q := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N)
  set f : (ℕ × ℕ) × (ℕ × ℕ) → ℝ := fun q =>
    (q.1.1 : ℝ) ^ (-s) * (q.1.2 : ℝ) ^ (-s) * (q.2.1 : ℝ) ^ (-s) * (q.2.2 : ℝ) ^ (-s)
  have hLHS : ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-s)
      = ∑ x ∈ S, f (quadMap x) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hterm : ∀ p ∈ n.divisors ×ˢ n.divisors, f (quadMap ⟨n, p⟩) = (n : ℝ) ^ (-s) := by
      intro p hp
      have hspec := (quadMap_spec (x := ⟨n, p⟩) (Finset.mem_sigma.mpr ⟨hn, hp⟩)).2.2.2
      dsimp only [f]
      have hcast : ((quadMap ⟨n, p⟩).1.1 : ℝ) * (quadMap ⟨n, p⟩).1.2
          * (quadMap ⟨n, p⟩).2.1 * (quadMap ⟨n, p⟩).2.2 = (n : ℝ) := by exact_mod_cast hspec
      rw [← hcast]
      repeat rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast
    ring
  have hRHS : ∑ q ∈ Q, f q = (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-s)) ^ 4 := by
    have hpair : ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (p.1 : ℝ) ^ (-s) * (p.2 : ℝ) ^ (-s)
        = (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-s)) ^ 2 := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sq]
    have hprod_eq : ∑ q ∈ Q, f q
        = (∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (p.1 : ℝ) ^ (-s) * (p.2 : ℝ) ^ (-s))
          * (∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (p.1 : ℝ) ^ (-s) * (p.2 : ℝ) ^ (-s)) := by
      dsimp only [Q, f]
      rw [Finset.sum_product]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      simp_rw [← mul_assoc, ← Finset.sum_mul]
    rw [hprod_eq, hpair]
    ring
  rw [hLHS, ← Finset.sum_image (fun x hx y hy h => quadMap_injOn N hx hy h), ← hRHS]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => by dsimp only [f]; positivity)
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  exact (quadMap_spec hx).1

/-- The uniform fourth-power zeta constant `(∑'_{m=0}^∞ m^{-(1+c)})⁴`. -/
def divSqConst (c : ℝ) : ℝ := (∑' m : ℕ, (m : ℝ) ^ (-(1 + c))) ^ 4

theorem divSqConst_nonneg (c : ℝ) : 0 ≤ divSqConst c := by
  unfold divSqConst; positivity

/-- **Uniform divisor-square bound**: for `c > 0` and every `N : ℕ`,
`∑_{n=1}^N d(n)² n^{-(1+c)} ≤ divSqConst c`. -/
theorem sum_divisors_card_sq_le_divSqConst {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + c)) ≤ divSqConst c := by
  have hsum : Summable (fun m : ℕ => (m : ℝ) ^ (-(1 + c))) := by
    have h := Real.summable_nat_rpow.mpr (show -(1 + c) < -1 by linarith)
    exact h
  have hpart : ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 + c)) ≤ ∑' m : ℕ, (m : ℝ) ^ (-(1 + c)) :=
    hsum.sum_le_tsum (Finset.Icc 1 N) (fun m _ => by positivity)
  have h0 : 0 ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 + c)) :=
    Finset.sum_nonneg fun m _ => by positivity
  exact (sum_divisors_card_sq_rpow_le N (1 + c)).trans (pow_le_pow_left₀ h0 hpart 4)

/-- **Mollifier tail mean-square coefficient bound**: for `c > 0`, `1 ≤ X`, and `1/2 + c ≤ α`,
`∑_{X < n ≤ N} ‖truncMoebiusSum X n‖² n^{-2α} ≤ divSqConst c · X^{-c}`. -/
theorem sum_truncMoebiusSum_sq_tail_le {c α : ℝ} (hc : 0 < c) (hα : 1 / 2 + c ≤ α)
    {X : ℕ} (hX : 1 ≤ X) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
        (if X < n then ‖(truncMoebiusSum X n : ℂ)‖ ^ 2 * (n : ℝ) ^ (-(2 * α)) else 0)
      ≤ divSqConst c * (X : ℝ) ^ (-c) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hpt : ∀ n ∈ Finset.Icc 1 N,
      (if X < n then ‖(truncMoebiusSum X n : ℂ)‖ ^ 2 * (n : ℝ) ^ (-(2 * α)) else 0)
        ≤ (X : ℝ) ^ (-c) * ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + c))) := by
    intro n _
    split_ifs with hnX
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hn0 : (0 : ℝ) < n := by linarith
      have hXn : (X : ℝ) ≤ n := by exact_mod_cast hnX.le
      have h1 : ‖(truncMoebiusSum X n : ℂ)‖ ^ 2 ≤ (n.divisors.card : ℝ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_truncMoebiusSum_le_divisors_card X n) 2
      have h2 : (n : ℝ) ^ (-(2 * α)) ≤ (n : ℝ) ^ (-(1 + 2 * c)) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have h3 : (n : ℝ) ^ (-(1 + 2 * c)) = (n : ℝ) ^ (-c) * (n : ℝ) ^ (-(1 + c)) := by
        rw [← Real.rpow_add hn0]; congr 1; ring
      have h4 : (n : ℝ) ^ (-c) ≤ (X : ℝ) ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos hX0 hXn (by linarith)
      calc ‖(truncMoebiusSum X n : ℂ)‖ ^ 2 * (n : ℝ) ^ (-(2 * α))
          ≤ (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + 2 * c)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (n : ℝ) ^ (-c) * ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + c))) := by
            rw [h3]; ring
        _ ≤ (X : ℝ) ^ (-c) * ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + c))) :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
    · positivity
  calc ∑ n ∈ Finset.Icc 1 N,
          (if X < n then ‖(truncMoebiusSum X n : ℂ)‖ ^ 2 * (n : ℝ) ^ (-(2 * α)) else 0)
      ≤ ∑ n ∈ Finset.Icc 1 N,
          (X : ℝ) ^ (-c) * ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + c))) :=
        Finset.sum_le_sum hpt
    _ = (X : ℝ) ^ (-c) * ∑ n ∈ Finset.Icc 1 N,
          (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + c)) := by rw [← Finset.mul_sum]
    _ ≤ (X : ℝ) ^ (-c) * divSqConst c :=
        mul_le_mul_of_nonneg_left (sum_divisors_card_sq_le_divSqConst hc N) (by positivity)
    _ = divSqConst c * (X : ℝ) ^ (-c) := mul_comm _ _

/-! ### The mollified detector `ζ(s) M_X(s) - 1` and its Dirichlet series on `Re s > 2` -/

/-- The mollified zero-detector `f_X(s) = ζ(s) M_X(s) - 1`. -/
def mollifiedDetector (X : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * zetaMollifier X s - 1

/-- `zetaMollifier X` is entire in `s`. -/
theorem differentiable_zetaMollifier (X : ℕ) : Differentiable ℂ (zetaMollifier X) := by
  intro s
  unfold zetaMollifier dirichletPolyC
  refine DifferentiableAt.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  exact (differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hn0))

/-- `mollifiedDetector X` is holomorphic off `s = 1`. -/
theorem differentiableOn_mollifiedDetector (X : ℕ) :
    DifferentiableOn ℂ (mollifiedDetector X) {1}ᶜ := by
  intro s hs
  unfold mollifiedDetector
  exact (((differentiableAt_riemannZeta hs).mul
    (differentiable_zetaMollifier X s)).sub (differentiableAt_const 1)).differentiableWithinAt

/-- At every zero `ρ` of `ζ`, `mollifiedDetector X ρ = -1`. -/
theorem mollifiedDetector_eq_neg_one_of_zeta_zero (X : ℕ) {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    mollifiedDetector X ρ = -1 := by
  simp [mollifiedDetector, hρ]

/-- Single-divisor rescaling of the zeta series on `Re s > 1`:
`(d : ℂ)^{-s} · ζ(s) = ∑'_{n : ℕ} (if n ≠ 0 ∧ d ∣ n then n^{-s} else 0)` for `d ≥ 1`. -/
theorem cpow_mul_zeta_eq_tsum_dvd {d : ℕ} (hd : 1 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    (d : ℂ) ^ (-s) * riemannZeta s
      = ∑' n : ℕ, (if n ≠ 0 ∧ d ∣ n then (n : ℂ) ^ (-s) else 0) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hsum : Summable (fun m : ℕ => (1 : ℂ) / (m : ℂ) ^ s) := summable_one_div_nat_cpow.mpr hs
  rw [zeta_eq_tsum_one_div_nat_cpow hs, ← tsum_mul_left]
  have hterm : ∀ m : ℕ, (d : ℂ) ^ (-s) * ((1 : ℂ) / (m : ℂ) ^ s)
      = if m = 0 then 0 else ((d * m : ℕ) : ℂ) ^ (-s) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.cast_zero, Complex.zero_cpow hs0, div_zero, mul_zero, if_pos rfl]
    · rw [if_neg hm.ne', one_div, ← Complex.cpow_neg]
      have hmul := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg m) (-s)
      push_cast at hmul ⊢
      exact hmul.symm
  simp_rw [hterm]
  symm
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun (x : {m : ℕ // (if m = 0 then (0 : ℂ) else ((d * m : ℕ) : ℂ) ^ (-s)) ≠ 0}) => d * x.1)
    ?_ ?_ ?_
  · intro x y hxy
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left (by omega) hxy)
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_cases hnd : n ≠ 0 ∧ d ∣ n
    · rw [if_pos hnd] at hn
      obtain ⟨m, rfl⟩ := hnd.2
      have hm0 : m ≠ 0 := fun h => hnd.1 (by simp [h])
      refine ⟨⟨m, ?_⟩, rfl⟩
      simp only [Function.mem_support, ne_eq, if_neg hm0]
      exact hn
    · exact (hn (if_neg hnd)).elim
  · intro x
    have hx0 : x.1 ≠ 0 := fun h => x.2 (by simp [h])
    have hdx0 : d * x.1 ≠ 0 := Nat.mul_ne_zero (by omega) hx0
    rw [if_pos ⟨hdx0, dvd_mul_right d x.1⟩, if_neg hx0]

/-- Norm bound for the `n`-th mollified coefficient on `Re s = σ`: `≤ n^{1 - σ}`. -/
theorem norm_truncMoebiusSum_mul_cpow_le (X n : ℕ) (s : ℂ) (hs : 1 < s.re) :
    ‖(if n = 0 then (0 : ℂ) else (truncMoebiusSum X n : ℂ) * (n : ℂ) ^ (-s))‖
      ≤ (n : ℝ) ^ (1 - s.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos rfl, norm_zero, Nat.cast_zero, Real.zero_rpow (by linarith)]
  · rw [if_neg hn.ne', norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    calc ‖(truncMoebiusSum X n : ℂ)‖ * (n : ℝ) ^ (-s.re)
        ≤ (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-s.re) := by
          rw [Real.rpow_one]
          exact mul_le_mul_of_nonneg_right (norm_truncMoebiusSum_le_self X n) (by positivity)
      _ = (n : ℝ) ^ (1 - s.re) := by rw [← Real.rpow_add hn0, ← sub_eq_add_neg]

/-- **Exact tail Dirichlet series of `mollifiedDetector`** on `Re s > 2` for `X ≥ 1`:
all terms `1 ≤ n ≤ X` cancel `-1` via `truncMoebiusSum_eq_of_le`. -/
theorem mollifiedDetector_eq_tsum {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 2 < s.re) :
    mollifiedDetector X s
      = ∑' n : ℕ, if X < n then (truncMoebiusSum X n : ℂ) * (n : ℂ) ^ (-s) else 0 := by
  have hs1 : 1 < s.re := by linarith
  have hsum_d : ∀ d ∈ Finset.Icc 1 X, Summable (fun n : ℕ =>
      if n ≠ 0 ∧ d ∣ n then (ArithmeticFunction.moebius d : ℂ) * (n : ℂ) ^ (-s) else 0) := by
    intro d _
    have hdom : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine Summable.of_norm_bounded hdom fun n => ?_
    by_cases h : n ≠ 0 ∧ d ∣ n
    · rw [if_pos h, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h.1),
        Complex.neg_re]
      exact mul_le_of_le_one_left (by positivity) (norm_moebius_le_one d)
    · rw [if_neg h, norm_zero]
      positivity
  have hprod : riemannZeta s * zetaMollifier X s
      = ∑' n : ℕ, if n = 0 then 0 else (truncMoebiusSum X n : ℂ) * (n : ℂ) ^ (-s) := by
    rw [mul_comm, zetaMollifier, dirichletPolyC, Finset.sum_mul]
    have h1 : ∀ d ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s) * riemannZeta s
          = ∑' n : ℕ, if n ≠ 0 ∧ d ∣ n
              then (ArithmeticFunction.moebius d : ℂ) * (n : ℂ) ^ (-s) else 0 := by
      intro d hd
      rw [mul_assoc, cpow_mul_zeta_eq_tsum_dvd (Finset.mem_Icc.mp hd).1 hs1, ← tsum_mul_left]
      congr 1; ext n; split_ifs <;> ring
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum hsum_d]
    congr 1; ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne', truncMoebiusSum, Int.cast_sum, Finset.sum_mul]
      have hfilt : n.divisors.filter (· ≤ X) = (Finset.Icc 1 X).filter (· ∣ n) := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
        exact ⟨fun ⟨⟨hdn, _⟩, hdX⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hdn hn, hdX⟩, hdn⟩,
          fun ⟨⟨_, hdX⟩, hdn⟩ => ⟨⟨hdn, hn.ne'⟩, hdX⟩⟩
      rw [hfilt, Finset.sum_filter]
      exact Finset.sum_congr rfl fun d _ => by simp [hn.ne']
  have hfull : Summable (fun n : ℕ =>
      if n = 0 then (0 : ℂ) else (truncMoebiusSum X n : ℂ) * (n : ℂ) ^ (-s)) :=
    Summable.of_norm_bounded (Real.summable_nat_rpow.mpr (by linarith)) fun n =>
      norm_truncMoebiusSum_mul_cpow_le X n s hs1
  have hhead : ∑ n ∈ Finset.range (X + 1),
      (if n = 0 then (0 : ℂ) else (truncMoebiusSum X n : ℂ) * (n : ℂ) ^ (-s)) = 1 := by
    have hcongr : ∀ n ∈ Finset.range (X + 1),
        (if n = 0 then (0 : ℂ) else (truncMoebiusSum X n : ℂ) * (n : ℂ) ^ (-s))
          = if n = 1 then 1 else 0 := by
      intro n hn
      rw [Finset.mem_range] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · rw [if_neg hn0.ne', truncMoebiusSum_eq_of_le hn0 (by omega)]
        by_cases h1 : n = 1
        · subst h1; simp
        · simp [h1]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  rw [mollifiedDetector, hprod, ← hfull.sum_add_tsum_compl (s := Finset.range (X + 1)), hhead, add_sub_cancel_left]
  -- match `tsum` over `(Finset.range (X + 1))ᶜ` with `if X < n`
  rw [← tsum_subtype_eq_of_support_subset (s := ((Finset.range (X + 1) : Finset ℕ) : Set ℕ)ᶜ)]
  · refine tsum_congr fun x => ?_
    have hx : X < x.1 := by
      have hm := x.2
      simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range, not_lt] at hm
      omega
    have hx0 : x.1 ≠ 0 := by omega
    rw [if_neg hx0, if_pos hx]
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range, not_lt]
    by_contra hle
    have hnot : ¬ X < n := by omega
    exact hn (if_neg hnot)

end Cvs.Zeta.MollifiedDetectorSeries

end
