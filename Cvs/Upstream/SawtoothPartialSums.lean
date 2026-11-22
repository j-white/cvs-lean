import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sawtooth partial sums

Lagrange's closed form for `Σ sin(mx)`, the Abel tail, `|Σ_{m≤M} sin(mx)/m| ≤ 1 + π` (so every block is
at most `G₀ = 2(1 + π)`), and the window and dyadic integrals of `min(G², β²/sin²(cθ/2))`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.Upstream.SawtoothPartialSums

/-- Lagrange's closed form: `2 sin(x/2) Σ_{p≤m≤q} sin(mx) = cos((p − ½)x) − cos((q + ½)x)`. -/
theorem two_sin_half_mul_sum_sin {p q : ℕ} (hpq : p ≤ q + 1) (x : ℝ) :
    2 * Real.sin (x / 2) * ∑ m ∈ Finset.Icc p q, Real.sin (m * x) =
      Real.cos (((p : ℝ) - 1 / 2) * x) - Real.cos (((q : ℝ) + 1 / 2) * x) := by
  obtain ⟨n, hn⟩ : ∃ n, q + 1 = p + n := ⟨q + 1 - p, by omega⟩
  have hI : Finset.Icc p q = Finset.Ico p (p + n) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hq : ((q : ℝ) + 1 / 2) = ((p + n : ℕ) : ℝ) - 1 / 2 := by
    have : ((q + 1 : ℕ) : ℝ) = ((p + n : ℕ) : ℝ) := by rw [hn]
    push_cast at this ⊢; linarith
  rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.mul_sum, hq]
  set F : ℕ → ℝ := fun k => -Real.cos ((((p + k : ℕ) : ℝ) - 1 / 2) * x) with hF
  have key : ∀ k ∈ Finset.range n,
      2 * Real.sin (x / 2) * Real.sin (((p + k : ℕ) : ℝ) * x) = F (k + 1) - F k := by
    intro k _
    simp only [hF]
    push_cast
    have h1 : ((p : ℝ) + (k + 1) - 1 / 2) * x = ((p : ℝ) + k) * x + x / 2 := by ring
    have h2 : ((p : ℝ) + k - 1 / 2) * x = ((p : ℝ) + k) * x - x / 2 := by ring
    rw [h1, h2, Real.cos_add, Real.cos_sub]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub]
  simp only [hF, Nat.add_zero]
  ring

/-- The partial sums of `sin(mx)` are at most `1/|sin(x/2)|`. -/
theorem abs_sum_sin_mul_le (p q : ℕ) (x : ℝ) :
    |∑ m ∈ Finset.Icc p q, Real.sin (m * x)| * |Real.sin (x / 2)| ≤ 1 := by
  rcases le_or_gt p (q + 1) with hpq | hpq
  · have h := two_sin_half_mul_sum_sin hpq x
    have hc : |Real.cos (((p : ℝ) - 1 / 2) * x) - Real.cos (((q : ℝ) + 1 / 2) * x)| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [Real.neg_one_le_cos (((p : ℝ) - 1 / 2) * x),
        Real.cos_le_one (((p : ℝ) - 1 / 2) * x), Real.neg_one_le_cos (((q : ℝ) + 1 / 2) * x),
        Real.cos_le_one (((q : ℝ) + 1 / 2) * x)]
    rw [← h, abs_mul, abs_mul, abs_two] at hc
    nlinarith [abs_nonneg (Real.sin (x / 2)), abs_nonneg (∑ m ∈ Finset.Icc p q, Real.sin (m * x))]
  · rw [Finset.Icc_eq_empty (by omega)]; simp

/-- `2 sin(x/2) sin((m+1)x) = cos((m + ½)x) − cos((m + 3/2)x)`. -/
theorem two_sin_half_mul_sin_succ (m : ℕ) (x : ℝ) :
    2 * Real.sin (x / 2) * Real.sin (((m + 1 : ℕ) : ℝ) * x) =
      Real.cos (((m : ℝ) + 1 / 2) * x) - Real.cos ((((m + 1 : ℕ) : ℝ) + 1 / 2) * x) := by
  push_cast
  have h1 : ((m : ℝ) + 1 + 1 / 2) * x = ((m : ℝ) + 1) * x + x / 2 := by ring
  have h2 : ((m : ℝ) + 1 / 2) * x = ((m : ℝ) + 1) * x - x / 2 := by ring
  rw [h1, h2, Real.cos_add, Real.cos_sub]; ring

/-- The Abel tail: `|Σ_{M<m≤N} sin(mx)/m| · (M+1)|sin(x/2)| ≤ 1`. -/
theorem abs_sum_sin_div_Ioc_mul_le (M N : ℕ) (x : ℝ) :
    |∑ m ∈ Finset.Ioc M N, Real.sin (m * x) / m| * (((M : ℝ) + 1) * |Real.sin (x / 2)|) ≤ 1 := by
  set s := Real.sin (x / 2) with hs
  set c0 := Real.cos (((M : ℝ) + 1 / 2) * x)
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have inv : ∀ n : ℕ, |2 * s * ∑ m ∈ Finset.Ioc M (M + n), Real.sin (m * x) / m
      - c0 / ((M : ℝ) + 1) + Real.cos ((((M + n : ℕ) : ℝ) + 1 / 2) * x) / (((M + n : ℕ) : ℝ) + 1)|
      ≤ 1 / ((M : ℝ) + 1) - 1 / (((M + n : ℕ) : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp [c0]
    | succ n ih =>
      have hN : M ≤ M + n := by omega
      rw [show M + (n + 1) = M + n + 1 by omega, Finset.sum_Ioc_succ_top hN]
      have hst := two_sin_half_mul_sin_succ (M + n) x
      rw [← hs] at hst
      set N := M + n
      set S := ∑ m ∈ Finset.Ioc M N, Real.sin (m * x) / m
      set cN := Real.cos (((N : ℝ) + 1 / 2) * x)
      set cN1 := Real.cos ((((N + 1 : ℕ) : ℝ) + 1 / 2) * x)
      have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have h2 : 2 * s * (S + Real.sin (((N + 1 : ℕ) : ℝ) * x) / ((N + 1 : ℕ) : ℝ))
          = 2 * s * S + (cN - cN1) / ((N : ℝ) + 1) := by
        rw [← hst]; push_cast; ring
      have heq : 2 * s * (S + Real.sin (((N + 1 : ℕ) : ℝ) * x) / ((N + 1 : ℕ) : ℝ))
          - c0 / ((M : ℝ) + 1) + cN1 / (((N + 1 : ℕ) : ℝ) + 1)
          = (2 * s * S - c0 / ((M : ℝ) + 1) + cN / ((N : ℝ) + 1))
            - cN1 * (1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2)) := by
        rw [h2]; push_cast; ring
      rw [heq]
      have hd : 0 ≤ 1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2) := by
        rw [sub_nonneg]; exact one_div_le_one_div_of_le hpos (by linarith)
      have hc : |cN1 * (1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2))|
          ≤ 1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2) := by
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_of_le_one_left hd (Real.abs_cos_le_one _)
      have hcast : (((N + 1 : ℕ) : ℝ) + 1) = (N : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      calc _ ≤ |2 * s * S - c0 / ((M : ℝ) + 1) + cN / ((N : ℝ) + 1)|
            + |cN1 * (1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 2))| := abs_sub _ _
        _ ≤ _ := by linarith
  rcases le_or_gt N M with h | h
  · rw [Finset.Ioc_eq_empty (by omega)]; simp
  obtain ⟨n, rfl⟩ : ∃ n, N = M + n := ⟨N - M, by omega⟩
  have h1 := abs_le.1 (inv n)
  set S := ∑ m ∈ Finset.Ioc M (M + n), Real.sin (m * x) / m
  set cN := Real.cos ((((M + n : ℕ) : ℝ) + 1 / 2) * x)
  have hpos : (0 : ℝ) < ((M + n : ℕ) : ℝ) + 1 := by positivity
  have bnd : ∀ (c d : ℝ), 0 < d → |c| ≤ 1 → -(1 / d) ≤ c / d ∧ c / d ≤ 1 / d := by
    intro c d hd hc
    rw [abs_le] at hc
    exact ⟨by rw [← neg_div]; exact div_le_div_of_nonneg_right hc.1 hd.le,
      div_le_div_of_nonneg_right hc.2 hd.le⟩
  have hc0 := bnd c0 _ hM (Real.abs_cos_le_one _)
  have hcN := bnd cN _ hpos (Real.abs_cos_le_one _)
  have hu : 0 < 1 / ((M : ℝ) + 1) := by positivity
  have key : |s * S * ((M : ℝ) + 1)| ≤ 1 := by
    rw [abs_le]
    have e : s * S * ((M : ℝ) + 1) = (2 * s * S) / (2 * (1 / ((M : ℝ) + 1))) := by
      field_simp
    rw [e]
    have hu2 : 0 < 2 * (1 / ((M : ℝ) + 1)) := by positivity
    constructor
    · rw [le_div_iff₀ hu2]; linarith
    · rw [div_le_iff₀ hu2]; linarith
  calc |S| * (((M : ℝ) + 1) * |s|) = |s * S * ((M : ℝ) + 1)| := by
        rw [abs_mul, abs_mul, abs_of_pos hM]; ring
    _ ≤ 1 := key

/-- Jordan's inequality in absolute form: `(2/π)|u| ≤ |sin u|` for `|u| ≤ π/2`. -/
theorem two_div_pi_mul_abs_le_abs_sin {u : ℝ} (hu : |u| ≤ π / 2) :
    2 / π * |u| ≤ |Real.sin u| := by
  refine (Real.mul_le_sin (abs_nonneg u) hu).trans ?_
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]; exact le_abs_self _
  · rw [abs_of_neg h, Real.sin_neg]; exact neg_le_abs _

/-- The sawtooth bound for `|y| ≤ π`. -/
theorem abs_sum_sin_div_le_of_abs_le_pi {y : ℝ} (hy : |y| ≤ π) (M : ℕ) :
    |∑ m ∈ Finset.Icc 1 M, Real.sin (m * y) / m| ≤ 1 + π := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp; positivity
  have hya : 0 < |y| := abs_pos.2 hy0
  have hjordan : |y| / π ≤ |Real.sin (y / 2)| := by
    have h := two_div_pi_mul_abs_le_abs_sin (u := y / 2) (by rw [abs_div, abs_two]; linarith)
    rw [abs_div, abs_two] at h
    calc |y| / π = 2 / π * (|y| / 2) := by ring
      _ ≤ _ := h
  set K := ⌊1 / |y|⌋₊
  have hK1 : (K : ℝ) * |y| ≤ 1 := by
    have := Nat.floor_le (a := 1 / |y|) (by positivity)
    rwa [le_div_iff₀ hya] at this
  have hK2 : 1 < ((K : ℝ) + 1) * |y| := by
    have := Nat.lt_floor_add_one (1 / |y|)
    rwa [div_lt_iff₀ hya] at this
  have head : ∀ L ≤ K, |∑ m ∈ Finset.Icc 1 L, Real.sin (m * y) / m| ≤ 1 := by
    intro L hL
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ m ∈ Finset.Icc 1 L, |Real.sin (m * y) / m| ≤ |y| := by
      intro m hm
      have hm1 : (0 : ℝ) < m := by
        have := (Finset.mem_Icc.1 hm).1; exact_mod_cast this
      rw [abs_div, Nat.abs_cast, div_le_iff₀ hm1]
      calc |Real.sin (m * y)| ≤ |(m : ℝ) * y| := Real.abs_sin_le_abs
        _ = |y| * m := by rw [abs_mul, Nat.abs_cast]; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    have : (L : ℝ) ≤ K := by exact_mod_cast hL
    nlinarith
  rcases le_or_gt M K with hMK | hMK
  · exact (head M hMK).trans (by linarith [Real.pi_pos])
  have hIcc : ∀ n, Finset.Icc 1 n = Finset.Ioc 0 n := by
    intro n; ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit := Finset.sum_Ioc_consecutive (fun m : ℕ => Real.sin (m * y) / m)
    (Nat.zero_le K) hMK.le
  rw [hIcc, ← hsplit, ← hIcc]
  have htail := abs_sum_sin_div_Ioc_mul_le K M y
  have hb : 1 / π ≤ ((K : ℝ) + 1) * |Real.sin (y / 2)| := by
    calc 1 / π ≤ ((K : ℝ) + 1) * |y| / π := by
          exact div_le_div_of_nonneg_right hK2.le Real.pi_pos.le
      _ = ((K : ℝ) + 1) * (|y| / π) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hjordan (by positivity)
  have ht : |∑ m ∈ Finset.Ioc K M, Real.sin (m * y) / m| ≤ π := by
    have := (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans htail
    rwa [mul_one_div, div_le_one Real.pi_pos] at this
  exact (abs_add_le _ _).trans (add_le_add (head K le_rfl) ht)

/-- The sawtooth partial sums are uniformly bounded: `|Σ_{m≤M} sin(mx)/m| ≤ 1 + π`. -/
theorem abs_sum_sin_div_le (M : ℕ) (x : ℝ) :
    |∑ m ∈ Finset.Icc 1 M, Real.sin (m * x) / m| ≤ 1 + π := by
  set y := toIocMod Real.two_pi_pos (-π) x
  have hy : y ∈ Set.Ioc (-π) (-π + 2 * π) := toIocMod_mem_Ioc _ _ _
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x = y + k * (2 * π) :=
    ⟨toIocDiv Real.two_pi_pos (-π) x,
      by rw [← zsmul_eq_mul, toIocMod_add_toIocDiv_zsmul]⟩
  have hyabs : |y| ≤ π := abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hterm : ∀ m : ℕ, Real.sin (m * x) = Real.sin (m * y) := by
    intro m
    rw [hk, mul_add, show (m : ℝ) * (k * (2 * π)) = ((m * k : ℤ) : ℝ) * (2 * π) by push_cast; ring,
      Real.sin_add_int_mul_two_pi]
  simp_rw [hterm]
  exact abs_sum_sin_div_le_of_abs_le_pi hyabs M

/-- Every block of the sawtooth series is bounded by `G₀ = 2(1 + π)`. -/
theorem abs_sum_sin_div_Ioc_le (M N : ℕ) (x : ℝ) :
    |∑ m ∈ Finset.Ioc M N, Real.sin (m * x) / m| ≤ 2 * (1 + π) := by
  rcases le_or_gt N M with h | h
  · rw [Finset.Ioc_eq_empty (by omega)]; simp; positivity
  have hIcc : ∀ n, Finset.Icc 1 n = Finset.Ioc 0 n := by
    intro n; ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit := Finset.sum_Ioc_consecutive (fun m : ℕ => Real.sin (m * x) / m)
    (Nat.zero_le M) h.le
  have h1 := abs_sum_sin_div_le M x
  have h2 := abs_sum_sin_div_le N x
  rw [hIcc] at h1 h2
  rw [← hsplit] at h2
  set A := ∑ m ∈ Finset.Ioc 0 M, Real.sin (m * x) / m
  set B := ∑ m ∈ Finset.Ioc M N, Real.sin (m * x) / m
  calc |B| = |(A + B) - A| := by ring_nf
    _ ≤ |A + B| + |A| := abs_sub _ _
    _ ≤ 2 * (1 + π) := by linarith

/-- If `sin(x/2) = 0` then every `sin(mx)` vanishes. -/
theorem sin_mul_eq_zero_of_sin_half {x : ℝ} (h : Real.sin (x / 2) = 0) (m : ℕ) :
    Real.sin (m * x) = 0 := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h
  rw [show (m : ℝ) * x = ((2 * m * n : ℤ) : ℝ) * π by push_cast; linear_combination (-2 * (m : ℝ)) * hn]
  exact Real.sin_int_mul_pi _

/-- The sawtooth series `Σ sin(mx)/m` has Cauchy partial sums at every `x`. -/
theorem cauchySeq_sum_sin_div (x : ℝ) :
    CauchySeq fun N : ℕ => ∑ m ∈ Finset.Icc 1 N, Real.sin (m * x) / m := by
  have hre : ∀ N : ℕ, ∑ m ∈ Finset.Icc 1 N, Real.sin (m * x) / m =
      ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1)) • Real.sin (((i + 1 : ℕ) : ℝ) * x) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih, smul_eq_mul]
      push_cast; ring
  have hre' : ∀ n : ℕ, ∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * x) =
      ∑ m ∈ Finset.Icc 1 n, Real.sin (m * x) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
  have hb : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * x)‖ ≤
      1 / |Real.sin (x / 2)| := by
    intro n
    rw [hre', Real.norm_eq_abs]
    rcases eq_or_ne (Real.sin (x / 2)) 0 with h0 | h0
    · simp [sin_mul_eq_zero_of_sin_half h0]
    · rw [le_div_iff₀ (abs_pos.2 h0)]; exact abs_sum_sin_mul_le 1 n x
  have hanti : Antitone fun i : ℕ => 1 / ((i : ℝ) + 1) := by
    intro a b hab
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    tendsto_one_div_add_atTop_nhds_zero_nat hb
  simpa only [hre] using this

/-- A measurable function squeezed between `0` and an interval-integrable one is interval integrable. -/
theorem intervalIntegrable_of_nonneg_of_le {f g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (hf : Measurable f)
    (h0 : ∀ x ∈ Set.uIoc a b, 0 ≤ f x) (hle : ∀ x ∈ Set.uIoc a b, f x ≤ g x) :
    IntervalIntegrable f volume a b :=
  hg.mono_fun hf.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (h0 x hx), abs_of_nonneg ((h0 x hx).trans (hle x hx))]
      exact hle x hx))

/-- `min(G², B²/u²)` is measurable. -/
theorem measurable_min_div_sq (G B : ℝ) : Measurable fun u : ℝ => min (G ^ 2) (B ^ 2 / u ^ 2) :=
  measurable_const.min (measurable_const.div (measurable_id.pow_const 2))

/-- `min(G², β²/sin² v)` is measurable. -/
theorem measurable_min_div_sin_sq (G β : ℝ) :
    Measurable fun v : ℝ => min (G ^ 2) (β ^ 2 / Real.sin v ^ 2) :=
  measurable_const.min (measurable_const.div (Real.continuous_sin.measurable.pow_const 2))

/-- `min(G², B²/u²)` is interval integrable on every interval. -/
theorem intervalIntegrable_min_div_sq (G B a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => min (G ^ 2) (B ^ 2 / u ^ 2)) volume a b :=
  intervalIntegrable_of_nonneg_of_le intervalIntegrable_const (measurable_min_div_sq G B)
    (fun _ _ => by positivity) (fun _ _ => min_le_left _ _)

/-- `min(G², β²/sin² v)` is interval integrable on every interval. -/
theorem intervalIntegrable_min_div_sin_sq (G β a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => min (G ^ 2) (β ^ 2 / Real.sin v ^ 2)) volume a b :=
  intervalIntegrable_of_nonneg_of_le intervalIntegrable_const (measurable_min_div_sin_sq G β)
    (fun _ _ => by positivity) (fun _ _ => min_le_left _ _)

/-- `min(G², β²/sin²(cθ/2))` is interval integrable on every interval. -/
theorem intervalIntegrable_min_div_sin_mul_sq (G β c a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => min (G ^ 2) (β ^ 2 / Real.sin (c * θ / 2) ^ 2)) volume a b :=
  intervalIntegrable_of_nonneg_of_le intervalIntegrable_const
    (measurable_const.min (measurable_const.div ((Real.continuous_sin.measurable.comp
      ((measurable_const.mul measurable_id).div_const 2)).pow_const 2)))
    (fun _ _ => by positivity) (fun _ _ => min_le_left _ _)

/-- The half-line integral `∫₀^T min(G², B²/u²) du ≤ 2GB`. -/
theorem integral_min_div_sq_le {G B T : ℝ} (hG : 0 ≤ G) (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, min (G ^ 2) (B ^ 2 / u ^ 2) ≤ 2 * G * B := by
  have hnn : ∀ u : ℝ, 0 ≤ min (G ^ 2) (B ^ 2 / u ^ 2) := fun u => by positivity
  rcases hG.eq_or_lt with rfl | hG'
  · have : ∀ u : ℝ, min ((0 : ℝ) ^ 2) (B ^ 2 / u ^ 2) = 0 := fun u => by
      rw [zero_pow two_ne_zero]; exact min_eq_left (by positivity)
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun u _ => this u)]; simp
  rcases hB.eq_or_lt with rfl | hB'
  · have : ∀ u : ℝ, min (G ^ 2) ((0 : ℝ) ^ 2 / u ^ 2) = 0 := fun u => by
      rw [zero_pow two_ne_zero, zero_div]; exact min_eq_right (by positivity)
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun u _ => this u)]; simp
  set h := fun u : ℝ => min (G ^ 2) (B ^ 2 / u ^ 2) with hh
  set t0 := B / G
  have ht0 : 0 < t0 := div_pos hB' hG'
  set T' := max T t0
  have hT' : t0 ≤ T' := le_max_right _ _
  have step1 : ∫ u in (0 : ℝ)..T, h u ≤ ∫ u in (0 : ℝ)..T', h u :=
    intervalIntegral.integral_mono_interval le_rfl hT (le_max_left _ _)
      (Eventually.of_forall fun u => hnn u) (intervalIntegrable_min_div_sq G B 0 T')
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := t0)
    (intervalIntegrable_min_div_sq G B 0 t0) (intervalIntegrable_min_div_sq G B t0 T')] at step1
  have hA : ∫ u in (0 : ℝ)..t0, h u ≤ G * B := by
    calc ∫ u in (0 : ℝ)..t0, h u ≤ ∫ _ in (0 : ℝ)..t0, G ^ 2 :=
          intervalIntegral.integral_mono_on ht0.le (intervalIntegrable_min_div_sq G B 0 t0)
            intervalIntegrable_const (fun u _ => min_le_left _ _)
      _ = G * B := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; simp only [t0]; field_simp
  have hcont : ContinuousOn (fun u : ℝ => B ^ 2 / u ^ 2) (Set.uIcc t0 T') := by
    refine continuousOn_const.div (continuousOn_id.pow 2) fun u hu => ?_
    rw [Set.uIcc_of_le hT'] at hu
    exact pow_ne_zero 2 (ht0.trans_le hu.1).ne'
  have hderiv : ∀ u ∈ Set.uIcc t0 T', HasDerivAt (fun u : ℝ => -B ^ 2 * u⁻¹) (B ^ 2 / u ^ 2) u := by
    intro u hu
    rw [Set.uIcc_of_le hT'] at hu
    have hu0 : u ≠ 0 := (ht0.trans_le hu.1).ne'
    have := (hasDerivAt_inv hu0).const_mul (-B ^ 2)
    have e : B ^ 2 / u ^ 2 = -B ^ 2 * -(u ^ 2)⁻¹ := by rw [div_eq_mul_inv]; ring
    rw [e]; exact this
  have hB2 : ∫ u in t0..T', h u ≤ G * B := by
    calc ∫ u in t0..T', h u ≤ ∫ u in t0..T', B ^ 2 / u ^ 2 :=
          intervalIntegral.integral_mono_on hT' (intervalIntegrable_min_div_sq G B t0 T')
            (hcont.intervalIntegrable) (fun u _ => min_le_right _ _)
      _ = -B ^ 2 * T'⁻¹ - -B ^ 2 * t0⁻¹ :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
      _ ≤ B ^ 2 * t0⁻¹ := by
          have : 0 ≤ B ^ 2 * T'⁻¹ := by
            have : 0 < T' := ht0.trans_le hT'
            positivity
          linarith
      _ = G * B := by simp only [t0]; field_simp
  linarith

/-- One period window: `∫_{-π/2}^{π/2} min(G², β²/sin² u) du ≤ 2πGβ`. -/
theorem integral_window_le {G β : ℝ} (hG : 0 ≤ G) (hβ : 0 ≤ β) :
    ∫ u in -(π / 2)..(π / 2), min (G ^ 2) (β ^ 2 / Real.sin u ^ 2) ≤ 2 * π * G * β := by
  set B := β * π / 2
  have hB : 0 ≤ B := by positivity
  have hpt : ∀ u ∈ Set.Icc (-(π / 2)) (π / 2),
      min (G ^ 2) (β ^ 2 / Real.sin u ^ 2) ≤ min (G ^ 2) (B ^ 2 / u ^ 2) := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hu0
    · simp
    refine min_le_min le_rfl ?_
    have habs : |u| ≤ π / 2 := abs_le.2 ⟨hu.1, hu.2⟩
    have hj := two_div_pi_mul_abs_le_abs_sin habs
    have hpos : 0 < 2 / π * |u| := by have := Real.pi_pos; positivity
    have hsq : (2 / π * |u|) ^ 2 ≤ Real.sin u ^ 2 := by
      rw [← sq_abs (Real.sin u)]; exact pow_le_pow_left₀ hpos.le hj 2
    calc β ^ 2 / Real.sin u ^ 2 ≤ β ^ 2 / (2 / π * |u|) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ = B ^ 2 / u ^ 2 := by
          simp only [B]; rw [mul_pow, sq_abs]; field_simp
  have hle := intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (intervalIntegrable_min_div_sin_sq G β (-(π / 2)) (π / 2))
    (intervalIntegrable_min_div_sq G B (-(π / 2)) (π / 2)) hpt
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (intervalIntegrable_min_div_sq G B _ _) (intervalIntegrable_min_div_sq G B _ _)] at hle
  have hneg : ∫ u in -(π / 2)..0, min (G ^ 2) (B ^ 2 / u ^ 2) =
      ∫ u in (0 : ℝ)..(π / 2), min (G ^ 2) (B ^ 2 / u ^ 2) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π / 2)
      (fun u : ℝ => min (G ^ 2) (B ^ 2 / u ^ 2))
    simp only [neg_sq, neg_zero] at this
    exact this.symm
  have h1 := integral_min_div_sq_le hG hB (T := π / 2) (by positivity)
  rw [hneg] at hle
  calc _ ≤ _ := hle
    _ ≤ 2 * G * B + 2 * G * B := by linarith
    _ = 2 * π * G * β := by simp only [B]; ring

/-- `min(G², β²/sin² v)` has period `π`. -/
theorem periodic_min_div_sin_sq (G β : ℝ) :
    Function.Periodic (fun v : ℝ => min (G ^ 2) (β ^ 2 / Real.sin v ^ 2)) π := by
  intro v
  simp only [Real.sin_add_pi, neg_sq]

/-- Covering `[A, B]` by `⌈(B − A)/π⌉` period windows. -/
theorem integral_min_div_sin_sq_le_ceil {G β A B : ℝ} (hG : 0 ≤ G) (hβ : 0 ≤ β) (hAB : A ≤ B) :
    ∫ v in A..B, min (G ^ 2) (β ^ 2 / Real.sin v ^ 2) ≤
      (⌈(B - A) / π⌉₊ : ℝ) * (2 * π * G * β) := by
  set f := fun v : ℝ => min (G ^ 2) (β ^ 2 / Real.sin v ^ 2) with hf
  set n := ⌈(B - A) / π⌉₊
  have hn : B ≤ A + n * π := by
    have := Nat.le_ceil ((B - A) / π)
    rw [div_le_iff₀ Real.pi_pos] at this
    linarith
  have step1 : ∫ v in A..B, f v ≤ ∫ v in A..(A + n * π), f v :=
    intervalIntegral.integral_mono_interval le_rfl hAB hn
      (Eventually.of_forall fun u => by simp only [hf]; positivity)
      (intervalIntegrable_min_div_sin_sq G β _ _)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := fun k : ℕ => A + k * π) (n := n)
    (fun k _ => intervalIntegrable_min_div_sin_sq G β _ _)
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  rw [← hsum] at step1
  have hk : ∀ k ∈ Finset.range n,
      ∫ v in (A + (k : ℕ) * π)..(A + ((k + 1 : ℕ) : ℝ) * π), f v ≤ 2 * π * G * β := by
    intro k _
    have e : A + ((k + 1 : ℕ) : ℝ) * π = (A + k * π) + π := by push_cast; ring
    rw [e, (periodic_min_div_sin_sq G β).intervalIntegral_add_eq (A + k * π) (-(π / 2)),
      show -(π / 2) + π = π / 2 by ring]
    exact integral_window_le hG hβ
  refine step1.trans ((Finset.sum_le_sum hk).trans ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The window integral: `∫_a^b min(G², β²/sin²(cθ/2)) dθ ≤ ((b − a)c/(2π) + 2) · 4πGβ/c`. -/
theorem integral_min_div_sin_sq_le {c G β a b : ℝ} (hc : 0 < c) (hG : 0 ≤ G) (hβ : 0 ≤ β)
    (hab : a ≤ b) :
    ∫ θ in a..b, min (G ^ 2) (β ^ 2 / Real.sin (c * θ / 2) ^ 2) ≤
      ((b - a) * c / (2 * π) + 2) * (4 * π * G * β / c) := by
  set f := fun v : ℝ => min (G ^ 2) (β ^ 2 / Real.sin v ^ 2) with hf
  have hc2 : c / 2 ≠ 0 := by positivity
  have hfun : (fun θ : ℝ => min (G ^ 2) (β ^ 2 / Real.sin (c * θ / 2) ^ 2)) =
      fun θ => f ((c / 2) * θ) := by
    funext θ; simp only [hf]; ring_nf
  rw [hfun, intervalIntegral.integral_comp_mul_left (fun v => f v) hc2, smul_eq_mul]
  have hAB : c / 2 * a ≤ c / 2 * b := mul_le_mul_of_nonneg_left hab (by positivity)
  have h1 := integral_min_div_sin_sq_le_ceil hG hβ hAB
  have h2 := Nat.ceil_lt_add_one (R := ℝ) (a := (c / 2 * b - c / 2 * a) / π)
    (div_nonneg (by linarith) Real.pi_pos.le)
  have hP : 0 ≤ 2 * π * G * β := by have := Real.pi_pos; positivity
  have hQ : 0 ≤ 4 * π * G * β / c := by have := Real.pi_pos; positivity
  have hinv : 0 ≤ (c / 2)⁻¹ := by positivity
  calc (c / 2)⁻¹ * ∫ v in c / 2 * a..c / 2 * b, f v
      ≤ (c / 2)⁻¹ * (((c / 2 * b - c / 2 * a) / π + 1) * (2 * π * G * β)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) hinv
        exact mul_le_mul_of_nonneg_right h2.le hP
    _ = ((b - a) * c / (2 * π) + 1) * (4 * π * G * β / c) := by
        field_simp; ring
    _ ≤ ((b - a) * c / (2 * π) + 2) * (4 * π * G * β / c) := by nlinarith

/-- The dyadic integral: `∫₁^X min(G²/θ², 1/(X² sin²(cθ/2))) dθ ≤ 4G(log₂X + 1 + 8π/c)/X`. -/
theorem integral_dyadic_le {c G X : ℝ} (hc : 0 < c) (hG : 0 ≤ G) (hX : 1 ≤ X) :
    ∫ θ in (1 : ℝ)..X, min (G ^ 2 / θ ^ 2) (1 / (X ^ 2 * Real.sin (c * θ / 2) ^ 2)) ≤
      4 * G * (Real.logb 2 X + 1 + 8 * π / c) / X := by
  set g := fun θ : ℝ => min (G ^ 2 / θ ^ 2) (1 / (X ^ 2 * Real.sin (c * θ / 2) ^ 2)) with hg
  have hX0 : 0 < X := by linarith
  have hgm : Measurable g := by simp only [hg]; fun_prop
  have hgnn : ∀ θ, 0 ≤ g θ := fun θ => by simp only [hg]; positivity
  have hint : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable g volume a b := by
    intro a b ha hb
    refine intervalIntegrable_of_nonneg_of_le (g := fun _ => G ^ 2) intervalIntegrable_const hgm
      (fun θ _ => hgnn θ) (fun θ hθ => ?_)
    have hθ1 : 1 ≤ θ := by
      rcases hθ with ⟨h1, h2⟩
      have := min_le_left a b
      rw [min_def] at h1
      split_ifs at h1 <;> linarith
    refine (min_le_left _ _).trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg G, one_le_pow₀ (n := 2) hθ1]
  set L := Real.logb 2 X
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) hX
  set n := ⌈L⌉₊
  have hn1 : (n : ℝ) < L + 1 := Nat.ceil_lt_add_one hL
  have hXn : X ≤ 2 ^ n := by
    calc X = (2 : ℝ) ^ L := (Real.rpow_logb (by norm_num) (by norm_num) hX0).symm
      _ ≤ (2 : ℝ) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil L)
      _ = 2 ^ n := Real.rpow_natCast 2 n
  have hpow1 : ∀ j : ℕ, (1 : ℝ) ≤ 2 ^ j := fun j => one_le_pow₀ (by norm_num)
  have step1 : ∫ θ in (1 : ℝ)..X, g θ ≤ ∫ θ in (1 : ℝ)..(2 ^ n), g θ :=
    intervalIntegral.integral_mono_interval le_rfl hX hXn (Eventually.of_forall hgnn)
      (hint _ _ le_rfl (hpow1 n))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
    (a := fun j : ℕ => (2 : ℝ) ^ j) (n := n) (fun k _ => hint _ _ (hpow1 k) (hpow1 (k + 1)))
  simp only [pow_zero] at hsum
  rw [← hsum] at step1
  have hblock : ∀ j ∈ Finset.range n, ∫ θ in ((2 : ℝ) ^ j)..(2 ^ (j + 1)), g θ ≤
      2 * G / X + 8 * π * G / (c * X) * (1 / 2) ^ j := by
    intro j _
    set w : ℝ := 2 ^ j
    have hw : 0 < w := by positivity
    have hw2 : (2 : ℝ) ^ (j + 1) = 2 * w := by rw [pow_succ]; ring
    have hq : ((1 : ℝ) / 4) ^ j = (w ^ 2)⁻¹ := by
      rw [show w ^ 2 = (4 : ℝ) ^ j by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      rw [one_div_pow, one_div]
    have hh : ((1 : ℝ) / 2) ^ j = w⁻¹ := by rw [one_div_pow, one_div]
    have hpt : ∀ θ ∈ Set.Icc w (2 * w), g θ ≤
        ((1 : ℝ) / 4) ^ j * min (G ^ 2) ((w / X) ^ 2 / Real.sin (c * θ / 2) ^ 2) := by
      intro θ hθ
      have hθ0 : 0 < θ := hw.trans_le hθ.1
      rw [hq, mul_min_of_nonneg _ _ (by positivity)]
      refine min_le_min ?_ (le_of_eq ?_)
      · rw [div_le_iff₀ (by positivity)]
        have : w ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hw.le hθ.1 2
        calc G ^ 2 = (w ^ 2)⁻¹ * G ^ 2 * w ^ 2 := by field_simp
          _ ≤ (w ^ 2)⁻¹ * G ^ 2 * θ ^ 2 :=
            mul_le_mul_of_nonneg_left this (by positivity)
      · rw [div_pow]; field_simp
    have hmono : ∫ θ in w..2 * w, g θ ≤ ∫ θ in w..2 * w,
        ((1 : ℝ) / 4) ^ j * min (G ^ 2) ((w / X) ^ 2 / Real.sin (c * θ / 2) ^ 2) :=
      intervalIntegral.integral_mono_on (by linarith)
        (hint w (2 * w) (hpow1 j) (by linarith [hpow1 j]))
        ((intervalIntegrable_min_div_sin_mul_sq G (w / X) c w (2 * w)).const_mul _) hpt
    · rw [hw2]
      refine hmono.trans ?_
      rw [intervalIntegral.integral_const_mul]
      have hwin := integral_min_div_sin_sq_le hc hG (β := w / X) (by positivity)
        (show w ≤ 2 * w by linarith)
      calc ((1 : ℝ) / 4) ^ j * ∫ θ in w..2 * w, min (G ^ 2) ((w / X) ^ 2 / Real.sin (c * θ / 2) ^ 2)
          ≤ ((1 : ℝ) / 4) ^ j * (((2 * w - w) * c / (2 * π) + 2) * (4 * π * G * (w / X) / c)) :=
            mul_le_mul_of_nonneg_left hwin (by positivity)
        _ = 2 * G / X + 8 * π * G / (c * X) * (1 / 2) ^ j := by
            rw [hq, hh]; field_simp; ring
  have hgeo := sum_geometric_two_le n
  have hpos : 0 ≤ 8 * π * G / (c * X) := by have := Real.pi_pos; positivity
  calc ∫ θ in (1 : ℝ)..X, g θ
      ≤ ∑ j ∈ Finset.range n, (2 * G / X + 8 * π * G / (c * X) * (1 / 2) ^ j) :=
        step1.trans (Finset.sum_le_sum hblock)
    _ = n * (2 * G / X) + 8 * π * G / (c * X) * ∑ j ∈ Finset.range n, ((1 : ℝ) / 2) ^ j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Finset.mul_sum]
    _ ≤ (L + 1) * (2 * G / X) + 8 * π * G / (c * X) * 2 := by
        have h2GX : 0 ≤ 2 * G / X := by positivity
        gcongr
    _ = 2 * G * (L + 1 + 8 * π / c) / X := by field_simp
    _ ≤ 4 * G * (L + 1 + 8 * π / c) / X := by
        have : 0 ≤ G * (L + 1 + 8 * π / c) / X := by have := Real.pi_pos; positivity
        rw [show 2 * G * (L + 1 + 8 * π / c) / X = 2 * (G * (L + 1 + 8 * π / c) / X) by ring,
          show 4 * G * (L + 1 + 8 * π / c) / X = 4 * (G * (L + 1 + 8 * π / c) / X) by ring]
        linarith

end Cvs.Upstream.SawtoothPartialSums
