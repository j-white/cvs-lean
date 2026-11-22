import Mathlib
import Cvs.L2a.TailLogScaleTest
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.RiemannPhiContinuous
import Cvs.Xi.RiemannPhiEven
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.XiOffRealLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window of the quartic Hermite profile is `Φ` less a Gaussian tail

With `c = 2πx` and `g_H(w) = (16c²w⁴ − 48cw²)e^{−cw²/2}`, `√u g_H(nu/√x) = 32 phiTerm n (log u)`,
so `logScale(window(1/x) g_H)(s − log x) = 32x^{−3/4}(Φ(s − log x/2) − T_x(s))` on `[0, log x]`,
where `T_x(s)` sums the terms with `n > eˢ`. For `x ≥ 4/π`,
`0 ≤ T_x ≤ 2π²x^{9/4}e^{−πx}/(1 − e^{−π})` there, so `∫₀^{log x} T_x² ≤ C x^{11/2} e^{−2πx}`.
-/

noncomputable section

open Real Set Filter MeasureTheory

namespace Cvs.Approximant.QuarticHermiteWindowPhi
open Cvs.ZeroCounting

open Cvs.Xi.RiemannPhiKernel (phiTerm riemannPhi phiTerm_eq summable_shifted)
open Cvs.L2a.TailLogScaleTest (logScale)

/-! ### The profile and the tail -/

/-- The quartic Hermite–Gaussian profile `g_H(w) = (16c²w⁴ − 48cw²)e^{−cw²/2}`. -/
def gH (c w : ℝ) : ℝ := (16 * c ^ 2 * w ^ 4 - 48 * c * w ^ 2) * exp (-(c * w ^ 2 / 2))

/-- The tail of `Φ`'s series past its `N`-th term. -/
def phiTail (N : ℕ) (t : ℝ) : ℝ := ∑' k : ℕ, phiTerm (k + N + 1) t

/-- The tail `T_x(s)`: the terms of `Φ(log x/2 − s)` with `n > eˢ`. -/
def tailX (x s : ℝ) : ℝ := phiTail ⌊exp s⌋₊ (log x / 2 - s)

/-- `Φ` is its first `N` terms plus the tail. -/
theorem sum_Icc_add_phiTail (N : ℕ) (t : ℝ) :
    ∑ n ∈ Finset.Icc 1 N, phiTerm n t + phiTail N t = riemannPhi t := by
  have hI : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp_rw [add_comm 1]
  exact (summable_shifted t).sum_add_tsum_nat_add N

/-- `T_x(s)` is `Φ(s − log x/2)` less the terms with `n ≤ eˢ`. -/
theorem tailX_eq (x s : ℝ) :
    tailX x s = riemannPhi (s - log x / 2)
      - ∑ n ∈ Finset.Icc 1 ⌊exp s⌋₊, phiTerm n (log x / 2 - s) := by
  rw [show s - log x / 2 = -(log x / 2 - s) by ring, Cvs.Xi.RiemannPhiEven.riemannPhi_neg,
    ← sum_Icc_add_phiTail ⌊exp s⌋₊ (log x / 2 - s), tailX]
  ring

/-! ### H1: the termwise identity and the window -/

/-- **The termwise identity** `√u g_H(nu/√x) = 32 phiTerm n (log u)` at `c = 2πx`. -/
theorem sqrt_mul_gH {x u : ℝ} (hx : 0 < x) (hu : 0 < u) (n : ℕ) :
    √u * gH (2 * π * x) (n * u / √x) = 32 * phiTerm n (log u) := by
  set t := log u
  have hut : u = exp t := (exp_log hu).symm
  have hsq : √u = exp (t / 2) := by rw [hut, Real.exp_half]
  have hx2 : √x ^ 2 = x := Real.sq_sqrt hx.le
  have hw : (n * u / √x) ^ 2 = n ^ 2 * exp (2 * t) / x := by
    rw [div_pow, hx2, mul_pow, hut, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hw4 : (n * u / √x) ^ 4 = (n ^ 2 * exp (2 * t) / x) ^ 2 := by
    rw [← hw]; ring
  have harg : 2 * π * x * (n ^ 2 * exp (2 * t) / x) / 2 = π * n ^ 2 * exp (2 * t) := by
    field_simp
  have h9 : exp (9 * t / 2) = exp (t / 2) * exp (2 * t) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have h5 : exp (5 * t / 2) = exp (t / 2) * exp (2 * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [gH, hw4, hw, harg, hsq, phiTerm, h9, h5]
  field_simp
  ring

/-- The profile at `n e^{−s}` is `32 e^{−t/2} phiTerm n t` with `t = log x/2 − s`. -/
theorem gH_mul_exp_neg {x : ℝ} (hx : 0 < x) (n : ℕ) (s : ℝ) :
    gH (2 * π * x) (n * exp (-s))
      = 32 * exp (-((log x / 2 - s) / 2)) * phiTerm n (log x / 2 - s) := by
  set t := log x / 2 - s
  have h := sqrt_mul_gH hx (exp_pos t) n
  rw [Real.log_exp] at h
  have hsx : √x = exp (log x / 2) := by rw [Real.exp_half, exp_log hx]
  have harg : (n : ℝ) * exp t / √x = n * exp (-s) := by
    rw [hsx, mul_div_assoc, ← Real.exp_sub]; congr 2; ring
  rw [harg, ← Real.exp_half] at h
  calc gH (2 * π * x) (n * exp (-s))
      = exp (-(t / 2)) * (exp (t / 2) * gH (2 * π * x) (n * exp (-s))) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ = 32 * exp (-(t / 2)) * phiTerm n t := by rw [h]; ring

/-- `e^{s − log x} ∈ [1/x, 1]` exactly when `s ∈ [0, log x]`. -/
theorem exp_sub_log_mem_Icc_iff {x : ℝ} (hx : 0 < x) (s : ℝ) :
    exp (s - log x) ∈ Icc (1 / x) 1 ↔ s ∈ Icc 0 (log x) := by
  have h1 : 1 / x = exp (0 - log x) := by rw [zero_sub, Real.exp_neg, exp_log hx, one_div]
  have h2 : (1 : ℝ) = exp (log x - log x) := by rw [sub_self, Real.exp_zero]
  rw [h1]
  conv_lhs => rw [h2]
  simp only [mem_Icc, Real.exp_le_exp, sub_le_sub_iff_right]

/-- **H1.** `logScale(window(1/x) g_H)(s − log x) = 32x^{−3/4}(Φ(s − log x/2) − T_x(s))`
on `[0, log x]`, and `0` off it. -/
theorem logScale_window_gH {x : ℝ} (hx : 0 < x) (s : ℝ) :
    logScale (Cvs.Xi.EImageWindowPoisson.window (1 / x) (gH (2 * π * x))) (s - log x)
      = (Icc 0 (log x)).indicator
          (fun s => 32 * x ^ (-(3 / 4 : ℝ)) * (riemannPhi (s - log x / 2) - tailX x s)) s := by
  unfold logScale Cvs.Xi.EImageWindowPoisson.window
  by_cases hs : s ∈ Icc 0 (log x)
  · rw [indicator_of_mem ((exp_sub_log_mem_Icc_iff hx s).2 hs), indicator_of_mem hs,
      Cvs.Xi.EImageWindowPoisson.eimage]
    have hθ : exp (s - log x) = exp s / x := by rw [Real.exp_sub, exp_log hx]
    have hfl : exp (s - log x) / (1 / x) = exp s := by rw [hθ]; field_simp
    have hpt : ∀ n : ℕ, (n : ℝ) * (1 / x) / exp (s - log x) = n * exp (-s) := by
      intro n; rw [hθ, Real.exp_neg]; field_simp
    have hpre : 1 / x / exp (s - log x) = exp (-s) := by
      rw [hθ, Real.exp_neg]; field_simp
    simp_rw [hfl, hpt, gH_mul_exp_neg hx, ← Finset.mul_sum]
    have hsum := sum_Icc_add_phiTail ⌊exp s⌋₊ (log x / 2 - s)
    rw [show s - log x / 2 = -(log x / 2 - s) by ring, Cvs.Xi.RiemannPhiEven.riemannPhi_neg,
      ← hsum, tailX, hpre, Real.rpow_def_of_pos hx]
    have he : exp (-s) * exp (-((log x / 2 - s) / 2)) * exp ((s - log x) / 2)
        = exp (log x * (-(3 / 4))) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [← he]; ring
  · rw [indicator_of_notMem (fun h => hs ((exp_sub_log_mem_Icc_iff hx s).1 h)),
      indicator_of_notMem hs, zero_mul]

/-- **H1, almost everywhere**, against the recentred window `1_(0,L] Φ(· − L/2)` of `Cvs.Xi.XiOffRealLine`. -/
theorem logScale_window_gH_ae {x : ℝ} (hx : 0 < x) :
    (fun s => logScale (Cvs.Xi.EImageWindowPoisson.window (1 / x) (gH (2 * π * x))) (s - log x))
      =ᵐ[volume] fun s => 32 * x ^ (-(3 / 4 : ℝ))
        * (Cvs.Xi.XiOffRealLine.phiWindow (log x) s - (Ioc 0 (log x)).indicator (tailX x) s) := by
  have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with s hs
  rw [logScale_window_gH hx s, Cvs.Xi.XiOffRealLine.phiWindow]
  by_cases hm : s ∈ Ioc 0 (log x)
  · rw [indicator_of_mem (Ioc_subset_Icc_self hm), indicator_of_mem hm, indicator_of_mem hm]
  · have hm' : s ∉ Icc 0 (log x) := by
      intro h; exact hm ⟨lt_of_le_of_ne h.1 (Ne.symm hs), h.2⟩
    rw [indicator_of_notMem hm', indicator_of_notMem hm, indicator_of_notMem hm]
    ring

/-! ### H2: the tail is Gaussian-small -/

/-- `y² ≤ Y² e^{π(y − Y)/2}` for `4/π ≤ Y ≤ y`. -/
theorem sq_le_sq_mul_exp {Y y : ℝ} (hY : 4 / π ≤ Y) (hy : Y ≤ y) :
    y ^ 2 ≤ Y ^ 2 * exp (π / 2 * (y - Y)) := by
  have hpi := pi_pos
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY
  have h1 : y / Y ≤ exp ((y - Y) / Y) := by
    have := add_one_le_exp ((y - Y) / Y)
    rwa [div_add_one hY0.ne', sub_add_cancel] at this
  have hinv : 1 / Y ≤ π / 4 := by
    rw [div_le_iff₀ hY0]; rw [div_le_iff₀ hpi] at hY; linarith
  have h2 : (y - Y) / Y ≤ π / 4 * (y - Y) := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hinv (sub_nonneg.mpr hy)
  have h3 : y ≤ Y * exp (π / 4 * (y - Y)) := by
    have := h1.trans (Real.exp_le_exp.mpr h2)
    rwa [div_le_iff₀ hY0, mul_comm] at this
  have hy0 : 0 ≤ y := hY0.le.trans hy
  calc y ^ 2 ≤ (Y * exp (π / 4 * (y - Y))) ^ 2 := pow_le_pow_left₀ hy0 h3 2
    _ = Y ^ 2 * exp (π / 2 * (y - Y)) := by
      rw [mul_pow, sq (exp _), ← Real.exp_add]; ring_nf

/-- One tail term is positive and at most `2π² e^{t/2} Y² e^{−πY} e^{−πk}`. -/
theorem phiTerm_tail_bound {N k : ℕ} {t Y : ℝ} (hY : 4 / π ≤ Y)
    (hNY : Y ≤ ((N : ℝ) + 1) ^ 2 * exp (2 * t)) (h1 : 1 ≤ ((N : ℝ) + 1) * exp (2 * t)) :
    0 < phiTerm (k + N + 1) t ∧ phiTerm (k + N + 1) t
      ≤ 2 * π ^ 2 * exp (t / 2) * Y ^ 2 * exp (-(π * Y)) * exp (-π) ^ k := by
  have hpi := pi_pos
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY
  set E := exp (2 * t) with hE
  set n : ℝ := ((k + N + 1 : ℕ) : ℝ) with hn
  have hn' : n = (k : ℝ) + ((N : ℝ) + 1) := by rw [hn]; push_cast; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hE0 : 0 < E := exp_pos _
  set y := n ^ 2 * E with hy
  have hyY : Y + 2 * k ≤ y := by
    have : y = ((N : ℝ) + 1) ^ 2 * E + 2 * k * (((N : ℝ) + 1) * E) + k ^ 2 * E := by
      rw [hy, hn']; ring
    rw [this]; nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hE0.le]
  have hYy : Y ≤ y := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le hY0 hYy
  constructor
  · rw [phiTerm_eq]
    have h8 : 0 < 2 * π * ((k + N + 1 : ℕ) : ℝ) ^ 2 * E - 3 := by
      have : 2 * π * y ≥ 8 := by
        rw [div_le_iff₀ hpi] at hY; nlinarith
      rw [← hn]; nlinarith
    have hnpos : (0 : ℝ) < ((k + N + 1 : ℕ) : ℝ) := by positivity
    positivity
  · have hupper : phiTerm (k + N + 1) t ≤ 2 * π ^ 2 * exp (t / 2) * (y ^ 2 * exp (-(π * y))) := by
      have h9 : exp (9 * t / 2) = exp (t / 2) * E ^ 2 := by
        rw [hE, sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
      have hyy : y ^ 2 = n ^ 4 * E ^ 2 := by rw [hy]; ring
      have hexp : exp (-(π * n ^ 2 * E)) = exp (-(π * y)) := by rw [hy]; ring_nf
      have heq : phiTerm (k + N + 1) t = 2 * π ^ 2 * exp (t / 2) * (y ^ 2 * exp (-(π * y)))
          - 3 * π * n ^ 2 * exp (5 * t / 2) * exp (-(π * y)) := by
        unfold phiTerm; rw [h9, ← hn, ← hE, hexp, hyy]; ring
      have : 0 ≤ 3 * π * n ^ 2 * exp (5 * t / 2) * exp (-(π * y)) := by positivity
      rw [heq]; linarith
    have hg : y ^ 2 * exp (-(π * y)) ≤ Y ^ 2 * exp (-(π * Y)) * exp (-π) ^ k := by
      have hs := sq_le_sq_mul_exp hY hYy
      have hsplit : exp (-(π * y)) = exp (-(π * Y)) * exp (-(π * (y - Y))) := by
        rw [← Real.exp_add]; ring_nf
      have hgeo : exp (π / 2 * (y - Y)) * exp (-(π * (y - Y))) ≤ exp (-π) ^ k := by
        rw [← Real.exp_add, ← Real.exp_nat_mul, Real.exp_le_exp]; nlinarith
      calc y ^ 2 * exp (-(π * y))
          ≤ Y ^ 2 * exp (π / 2 * (y - Y)) * (exp (-(π * Y)) * exp (-(π * (y - Y)))) := by
            rw [← hsplit]; exact mul_le_mul_of_nonneg_right hs (exp_pos _).le
        _ = Y ^ 2 * exp (-(π * Y)) * (exp (π / 2 * (y - Y)) * exp (-(π * (y - Y)))) := by ring
        _ ≤ Y ^ 2 * exp (-(π * Y)) * exp (-π) ^ k :=
            mul_le_mul_of_nonneg_left hgeo (by positivity)
    calc phiTerm (k + N + 1) t ≤ 2 * π ^ 2 * exp (t / 2) * (y ^ 2 * exp (-(π * y))) := hupper
      _ ≤ 2 * π ^ 2 * exp (t / 2) * (Y ^ 2 * exp (-(π * Y)) * exp (-π) ^ k) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring

/-- **The tail past `N`** lies in `[0, 2π² e^{t/2} Y² e^{−πY}/(1 − e^{−π})]`
when `4/π ≤ Y ≤ (N+1)² e^{2t}` and `1 ≤ (N+1) e^{2t}`. -/
theorem phiTail_mem_Icc {N : ℕ} {t Y : ℝ} (hY : 4 / π ≤ Y)
    (hNY : Y ≤ ((N : ℝ) + 1) ^ 2 * exp (2 * t)) (h1 : 1 ≤ ((N : ℝ) + 1) * exp (2 * t)) :
    phiTail N t ∈ Icc 0 (2 * π ^ 2 * exp (t / 2) * Y ^ 2 * exp (-(π * Y)) / (1 - exp (-π))) := by
  have hr0 : 0 ≤ exp (-π) := (exp_pos _).le
  have hr1 : exp (-π) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith [pi_pos])
  set A := 2 * π ^ 2 * exp (t / 2) * Y ^ 2 * exp (-(π * Y))
  have hb := fun k : ℕ => phiTerm_tail_bound (k := k) hY hNY h1
  have hgeo : Summable fun k : ℕ => A * exp (-π) ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left A
  have hsum : Summable fun k : ℕ => phiTerm (k + N + 1) t :=
    Summable.of_nonneg_of_le (fun k => (hb k).1.le) (fun k => (hb k).2) hgeo
  refine ⟨tsum_nonneg fun k => (hb k).1.le, ?_⟩
  calc phiTail N t ≤ ∑' k : ℕ, A * exp (-π) ^ k :=
        Summable.tsum_le_tsum (fun k => (hb k).2) hsum hgeo
    _ = A / (1 - exp (-π)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- The constant of the pointwise tail bound, `2π² x^{9/4} e^{−πx}/(1 − e^{−π})`. -/
def tailBound (x : ℝ) : ℝ := 2 * π ^ 2 * x ^ (9 / 4 : ℝ) * exp (-(π * x)) / (1 - exp (-π))

/-- **`0 ≤ T_x(s) ≤ 2π² x^{9/4} e^{−πx}/(1 − e^{−π})`** on `[0, log x]` for `x ≥ 4/π`. -/
theorem tailX_mem_Icc {x s : ℝ} (hx : 4 / π ≤ x) (hs : s ∈ Icc 0 (log x)) :
    tailX x s ∈ Icc 0 (tailBound x) := by
  have hpi := pi_pos
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  set N := ⌊exp s⌋₊
  set t := log x / 2 - s
  have hes : 0 < exp s := exp_pos s
  have hN : exp s < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hesx : exp s ≤ x := by rw [← exp_log hx0]; exact Real.exp_le_exp.mpr hs.2
  have hE : exp (2 * t) = x / exp s ^ 2 := by
    rw [show 2 * t = log x - 2 * s by ring, Real.exp_sub, exp_log hx0, ← Real.exp_nat_mul]
    push_cast; ring_nf
  have hNY : x ≤ ((N : ℝ) + 1) ^ 2 * exp (2 * t) := by
    rw [hE, mul_div_assoc', le_div_iff₀ (by positivity)]
    have : exp s ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hes.le hN.le 2
    nlinarith
  have h1 : 1 ≤ ((N : ℝ) + 1) * exp (2 * t) := by
    rw [hE, mul_div_assoc', le_div_iff₀ (by positivity), one_mul, sq]
    exact mul_le_mul hN.le hesx hes.le (by positivity)
  obtain ⟨h0, hle⟩ := phiTail_mem_Icc hx hNY h1
  refine ⟨h0, hle.trans ?_⟩
  have hden : 0 < 1 - exp (-π) := by
    rw [sub_pos, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have ht : exp (t / 2) ≤ x ^ (1 / 4 : ℝ) := by
    have htdef : t = log x / 2 - s := rfl
    rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp]; linarith [hs.1]
  have h94 : x ^ (9 / 4 : ℝ) = x ^ (1 / 4 : ℝ) * x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; norm_num
  rw [tailBound, h94]
  apply div_le_div_of_nonneg_right _ hden.le
  have := mul_le_mul_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ x ^ 2 * exp (-(π * x)))
  nlinarith [sq_nonneg π]

/-- `T_x` is measurable. -/
theorem measurable_tailX (x : ℝ) : Measurable (tailX x) := by
  have hF : Measurable fun p : ℝ × ℕ =>
      ∑ n ∈ Finset.Icc 1 p.2, phiTerm n (log x / 2 - p.1) := by
    refine measurable_from_prod_countable_left fun N => ?_
    show Measurable fun s : ℝ => ∑ n ∈ Finset.Icc 1 N, phiTerm n (log x / 2 - s)
    refine Continuous.measurable (continuous_finsetSum _ fun n _ => ?_)
    unfold phiTerm; fun_prop
  have hg : Measurable fun s : ℝ => (s, ⌊exp s⌋₊) :=
    measurable_id.prodMk (Nat.measurable_floor.comp measurable_exp)
  have hc : Measurable fun s : ℝ => ∑ n ∈ Finset.Icc 1 ⌊exp s⌋₊, phiTerm n (log x / 2 - s) :=
    Measurable.comp (g := fun p : ℝ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, phiTerm n (log x / 2 - p.1))
      (f := fun s : ℝ => (s, ⌊exp s⌋₊)) hF hg
  have hR : Measurable fun s : ℝ => riemannPhi (s - log x / 2) :=
    (Cvs.Xi.RiemannPhiContinuous.continuous_riemannPhi.comp (continuous_sub_right _)).measurable
  have h : tailX x = fun s => riemannPhi (s - log x / 2)
      - ∑ n ∈ Finset.Icc 1 ⌊exp s⌋₊, phiTerm n (log x / 2 - s) := funext (tailX_eq x)
  rw [h]
  exact hR.sub hc

/-- `T_x` is square integrable on `(0, log x]` for `x ≥ 4/π`. -/
theorem memLp_tailX {x : ℝ} (hx : 4 / π ≤ x) :
    MemLp (tailX x) 2 (volume.restrict (Ioc 0 (log x))) := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (log x))) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  refine MemLp.of_bound (measurable_tailX x).aestronglyMeasurable (tailBound x) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
  obtain ⟨h0, h1⟩ := tailX_mem_Icc hx (Ioc_subset_Icc_self hs)
  rwa [Real.norm_eq_abs, abs_of_nonneg h0]

/-- **H2.** `∫₀^{log x} T_x² ≤ log x · (2π² x^{9/4} e^{−πx}/(1 − e^{−π}))²` for `x ≥ 4/π`. -/
theorem integral_tailX_sq_le {x : ℝ} (hx : 4 / π ≤ x) :
    ∫ s in (0 : ℝ)..log x, tailX x s ^ 2 ≤ log x * tailBound x ^ 2 := by
  have hpi := pi_pos
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ 4 / π := by rw [le_div_iff₀ hpi]; linarith [pi_lt_four]
    linarith
  have hL : 0 ≤ log x := Real.log_nonneg hx1
  have hb : ∀ s ∈ uIoc 0 (log x), ‖tailX x s ^ 2‖ ≤ tailBound x ^ 2 := by
    intro s hs
    rw [uIoc_of_le hL] at hs
    obtain ⟨h0, h1⟩ := tailX_mem_Icc hx (Ioc_subset_Icc_self hs)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h0 h1 2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg hL] at this
  linarith [le_abs_self (∫ s in (0 : ℝ)..log x, tailX x s ^ 2), Real.norm_eq_abs
    (∫ s in (0 : ℝ)..log x, tailX x s ^ 2)]

/-- **H2, as a power times `e^{−2πx}`:** `∫₀^{log x} T_x² ≤ C x^{11/2} e^{−2πx}`
with `C = 4π⁴/(1 − e^{−π})²`, for `x ≥ 4/π`. -/
theorem integral_tailX_sq_le_rpow {x : ℝ} (hx : 4 / π ≤ x) :
    ∫ s in (0 : ℝ)..log x, tailX x s ^ 2
      ≤ 4 * π ^ 4 / (1 - exp (-π)) ^ 2 * x ^ (11 / 2 : ℝ) * exp (-(2 * π * x)) := by
  have hpi := pi_pos
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hlog : log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hT : tailBound x ^ 2 * x
      = 4 * π ^ 4 / (1 - exp (-π)) ^ 2 * x ^ (11 / 2 : ℝ) * exp (-(2 * π * x)) := by
    have h112 : (x ^ (9 / 4 : ℝ)) ^ 2 * x = x ^ (11 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add_one hx0.ne']; norm_num
    have he : exp (-(2 * π * x)) = exp (-(π * x)) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [tailBound, div_pow, ← h112, he]; ring
  calc ∫ s in (0 : ℝ)..log x, tailX x s ^ 2 ≤ log x * tailBound x ^ 2 := integral_tailX_sq_le hx
    _ ≤ x * tailBound x ^ 2 := mul_le_mul_of_nonneg_right hlog (sq_nonneg _)
    _ = _ := by rw [mul_comm, hT]

end Cvs.Approximant.QuarticHermiteWindowPhi
