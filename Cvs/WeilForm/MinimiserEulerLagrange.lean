import Mathlib
import Cvs.Upstream.DiagonalRankOneMinimum
import Cvs.Upstream.TightCoordinateConvergence
import Cvs.WeilForm.EvenSectorMinimum
import Cvs.WeilForm.PoleTermLpContinuity

/-!
# A minimiser satisfies the Euler–Lagrange equation

    (λ − Dₘ)·ηₘ = c·⟨v,η⟩·vₘ

Perturb at one mode: the numerator less `λ` times the denominator is a quadratic in `t`,
nonnegative and vanishing at `0`, so its linear coefficient is zero.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Upstream.TightCoordinateConvergence Cvs.Upstream.DiagonalRankOneMinimum Cvs.WeilForm.EvenSectorMinimum

namespace Cvs.WeilForm.MinimiserEulerLagrange

variable {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]

/-- A quadratic that is nonnegative everywhere and vanishes at the origin has no linear
term. -/
theorem linear_coeff_eq_zero {A B : ℝ} (h : ∀ t : ℝ, 0 ≤ 2 * t * A + t ^ 2 * B) : A = 0 := by
  -- opposite steps force the quadratic coefficient nonnegative
  have hB : 0 ≤ B := by
    have h1 := h 1
    have h2 := h (-1)
    nlinarith [h1, h2]
  -- and pin the linear one against it at every scale
  have key : ∀ t : ℝ, 0 < t → 2 * |A| ≤ t * B := by
    intro t ht
    rcases abs_cases A with ⟨hA1, _⟩ | ⟨hA1, _⟩
    · have hstep := h (-t)
      rw [hA1]
      nlinarith [hstep, ht]
    · have hstep := h t
      rw [hA1]
      nlinarith [hstep, ht]
  by_contra hA
  have hAp : 0 < |A| := abs_pos.mpr hA
  have hden : (0:ℝ) < B + 1 := by linarith
  have ht : 0 < |A| / (B + 1) := div_pos hAp hden
  have hk := key _ ht
  have hb : (|A| / (B + 1)) * B ≤ |A| := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [hAp, hB]
  linarith

/-! ### Perturbing at one mode -/

variable {D v : ι → ℝ} {c : ℝ}

/-- The perturbed vector: the minimiser, moved at a single mode. -/
def pert (η : ι → ℝ) (m : ι) (t : ℝ) : ι → ℝ := Function.update η m (η m + t)

theorem pert_apply_ne {η : ι → ℝ} {m n : ι} (t : ℝ) (h : n ≠ m) : pert η m t n = η n := by
  simp [pert, Function.update_of_ne h]

@[simp] theorem pert_apply_self {η : ι → ℝ} (m : ι) (t : ℝ) : pert η m t m = η m + t := by
  simp [pert]

/-- **A sum over the perturbed vector** differs from the original in one term only. -/
theorem pert_pointwise {η : ι → ℝ} {m : ι} {t : ℝ} (g : ι → ℝ → ℝ) (n : ι) :
    g n (pert η m t n)
      = g n (η n) + (if n = m then g m (η m + t) - g m (η m) else 0) := by
  classical
  by_cases h : n = m
  · subst h
    rw [pert_apply_self]
    simp
  · rw [pert_apply_ne t h, if_neg h, add_zero]

theorem summable_correction {η : ι → ℝ} {m : ι} {t : ℝ} (g : ι → ℝ → ℝ) :
    Summable fun n : ι => if n = m then g m (η m + t) - g m (η m) else 0 := by
  classical
  exact summable_of_ne_finset_zero (s := {m}) fun n hn => by
    simp [Finset.mem_singleton.not.mp hn]

theorem summable_pert {η : ι → ℝ} {m : ι} {t : ℝ} {g : ι → ℝ → ℝ}
    (hf : Summable fun n => g n (η n)) : Summable fun n => g n (pert η m t n) :=
  (hf.add (summable_correction g)).congr fun n => (pert_pointwise g n).symm

theorem tsum_pert {η : ι → ℝ} {m : ι} {t : ℝ} {g : ι → ℝ → ℝ}
    (hf : Summable fun n => g n (η n)) :
    ∑' n : ι, g n (pert η m t n) = (∑' n : ι, g n (η n)) + (g m (η m + t) - g m (η m)) := by
  classical
  rw [tsum_congr (fun n => pert_pointwise (η := η) (m := m) (t := t) g n),
    hf.tsum_add (summable_correction g)]
  congr 1
  rw [tsum_eq_sum (s := {m}) (fun n hn => by simp [Finset.mem_singleton.not.mp hn])]
  simp

/-! ### Minimality, unnormalised -/

/-- **The minimum bounds the form on every vector**, scaled by its norm. -/
theorem min_mul_tsum_le {D v : ι → ℝ} {K c : ℝ} {η : ι → ℝ}
    (hmin : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η ≤ diagFormVal D c v a)
    {a : ι → ℝ} (ha1 : Summable fun n => (a n) ^ 2)
    (ha2 : Summable fun n => (D n - K) * (a n) ^ 2) :
    diagFormVal D c v η * (∑' n : ι, (a n) ^ 2) ≤ diagFormVal D c v a := by
  classical
  set N : ℝ := ∑' n : ι, (a n) ^ 2 with hN
  have hNnn : 0 ≤ N := tsum_nonneg fun n => sq_nonneg _
  rcases eq_or_lt_of_le hNnn with hN0 | hNpos
  · -- no mass: both sides vanish
    have hzero : ∀ n : ι, a n = 0 := by
      intro n
      have hle : (a n) ^ 2 ≤ N := by
        have := sum_le_hasSum {n} (fun k _ => sq_nonneg (a k)) ha1.hasSum
        simpa using this
      have h0 : (a n) ^ 2 ≤ 0 := by linarith [hle, hN0]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h0 (sq_nonneg _))
    have hd : diagFormVal D c v a = 0 := by
      unfold diagFormVal rankOneVal
      have e1 : (fun n : ι => D n * (a n) ^ 2) = fun _ => (0:ℝ) :=
        funext fun n => by rw [hzero n]; ring
      have e2 : (fun n : ι => v n * a n) = fun _ => (0:ℝ) :=
        funext fun n => by rw [hzero n]; ring
      rw [e1, e2, tsum_zero]
      ring
    rw [hd, ← hN0, mul_zero]
  · -- normalise and use minimality
    have hsq : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
    have hNne : N ≠ 0 := ne_of_gt hNpos
    set b : ι → ℝ := fun n => a n / Real.sqrt N with hb
    have hbsq : ∀ n : ι, (b n) ^ 2 = (a n) ^ 2 / N := by
      intro n
      rw [hb, div_pow, Real.sq_sqrt hNnn]
    have hb1 : Summable fun n : ι => (b n) ^ 2 := by
      refine (ha1.div_const N).congr fun n => ?_
      rw [hbsq n]
    have hbunit : ∑' n : ι, (b n) ^ 2 = 1 := by
      rw [tsum_congr hbsq, tsum_div_const, ← hN, div_self hNne]
    have hb2 : Summable fun n : ι => (D n - K) * (b n) ^ 2 := by
      refine (ha2.div_const N).congr fun n => ?_
      rw [hbsq n]
      ring
    have hbmem : b ∈ sphereDom (fun n => D n - K) := ⟨hb1, hbunit, hb2⟩
    have hhom : diagFormVal D c v b = diagFormVal D c v a / N := by
      unfold diagFormVal rankOneVal
      have h1 : ∑' n : ι, D n * (b n) ^ 2 = (∑' n : ι, D n * (a n) ^ 2) / N := by
        rw [← tsum_div_const]
        refine tsum_congr fun n => ?_
        rw [hbsq n]
        ring
      have h2 : ∑' n : ι, v n * b n = (∑' n : ι, v n * a n) / Real.sqrt N := by
        rw [← tsum_div_const]
        refine tsum_congr fun n => ?_
        rw [hb]
        ring
      rw [h1, h2, div_pow, Real.sq_sqrt hNnn]
      ring
    have := hmin b hbmem
    rw [hhom, le_div_iff₀ hNpos] at this
    linarith

/-! ### The equation -/

/-- **A minimiser is an eigenvector.**  Perturbing at one mode gives a quadratic in `t` that
is nonnegative and vanishes at `0`; its linear coefficient is the equation. -/
theorem euler_lagrange {D v : ι → ℝ} {K c : ℝ} {η : ι → ℝ}
    (hη : η ∈ sphereDom (fun n => D n - K))
    (hmin : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η ≤ diagFormVal D c v a)
    (hvsum : Summable fun n => (v n) ^ 2) (m : ι) :
    (diagFormVal D c v η - D m) * η m = c * (∑' n : ι, v n * η n) * v m := by
  obtain ⟨hnorm, hunit, hshift⟩ := hη
  have hDsum : Summable fun n : ι => D n * (η n) ^ 2 := by
    have := hshift.add (hnorm.mul_left K)
    refine this.congr fun n => ?_
    ring
  have hvη : Summable fun n : ι => v n * η n :=
    Cvs.WeilForm.PoleTermLpContinuity.summable_mul hvsum hnorm
  set lam : ℝ := diagFormVal D c v η with hlam
  set S : ℝ := ∑' n : ι, v n * η n with hS
  have hkey : ∀ t : ℝ, 0 ≤ 2 * t * (D m * η m + c * S * v m - lam * η m)
      + t ^ 2 * (D m + c * (v m) ^ 2 - lam) := by
    intro t
    have h1 : Summable fun n : ι => (pert η m t n) ^ 2 :=
      summable_pert (g := fun _ x => x ^ 2) hnorm
    have h2 : Summable fun n : ι => (D n - K) * (pert η m t n) ^ 2 :=
      summable_pert (g := fun n x => (D n - K) * x ^ 2) hshift
    have hle := min_mul_tsum_le hmin h1 h2
    have e1 : ∑' n : ι, (pert η m t n) ^ 2 = 1 + (2 * t * η m + t ^ 2) := by
      rw [tsum_pert (g := fun _ x => x ^ 2) hnorm, hunit]
      ring
    have e2 : ∑' n : ι, D n * (pert η m t n) ^ 2
        = (∑' n : ι, D n * (η n) ^ 2) + D m * (2 * t * η m + t ^ 2) := by
      rw [tsum_pert (g := fun n x => D n * x ^ 2) hDsum]
      ring
    have e3 : ∑' n : ι, v n * pert η m t n = S + v m * t := by
      rw [tsum_pert (g := fun n x => v n * x) hvη, hS]
      ring
    have e4 : diagFormVal D c v (pert η m t)
        = (∑' n : ι, D n * (η n) ^ 2) + D m * (2 * t * η m + t ^ 2) + c * (S + v m * t) ^ 2 := by
      unfold diagFormVal rankOneVal
      rw [e2, e3]
    have e5 : lam = (∑' n : ι, D n * (η n) ^ 2) + c * S ^ 2 := by
      rw [hlam]
      unfold diagFormVal rankOneVal
      rw [hS]
    rw [e1, e4] at hle
    nlinarith [hle, e5]
  have := linear_coeff_eq_zero hkey
  linarith [this]

/-! ### Simplicity -/

omit [Countable ι] [DecidableEq ι] [Nonempty ι] in
/-- **Two solutions of the equation at a separated `λ` are proportional.**  Each coordinate is
determined by one scalar, so the solution space is a line. -/
theorem eigen_proportional {D v : ι → ℝ} {c lam : ℝ} {η η' : ι → ℝ}
    (hsep : ∀ n : ι, lam ≠ D n)
    (hEL : ∀ m : ι, (lam - D m) * η m = c * (∑' n : ι, v n * η n) * v m)
    (hEL' : ∀ m : ι, (lam - D m) * η' m = c * (∑' n : ι, v n * η' n) * v m)
    (hne : ∃ n : ι, η n ≠ 0) :
    ∃ t : ℝ, ∀ n : ι, η' n = t * η n := by
  set μ : ℝ := c * ∑' n : ι, v n * η n with hμ
  set μ' : ℝ := c * ∑' n : ι, v n * η' n with hμ'
  have hden : ∀ n : ι, lam - D n ≠ 0 := fun n => sub_ne_zero.mpr (hsep n)
  have hcoord : ∀ n : ι, η n = μ * v n / (lam - D n) := by
    intro n
    rw [eq_div_iff (hden n), mul_comm (η n), hEL n, hμ]
  have hcoord' : ∀ n : ι, η' n = μ' * v n / (lam - D n) := by
    intro n
    rw [eq_div_iff (hden n), mul_comm (η' n), hEL' n, hμ']
  have hμne : μ ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := hne
    exact hn (by rw [hcoord n, h]; simp)
  refine ⟨μ' / μ, fun n => ?_⟩
  rw [hcoord n, hcoord' n]
  field_simp

/-- **The minimum is a simple eigenvalue.**  Any two minimisers are proportional. -/
theorem minimiser_unique {D v : ι → ℝ} {K c : ℝ} {η η' : ι → ℝ}
    (hη : η ∈ sphereDom (fun n => D n - K)) (hη' : η' ∈ sphereDom (fun n => D n - K))
    (hmin : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η ≤ diagFormVal D c v a)
    (hmin' : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η' ≤ diagFormVal D c v a)
    (hvsum : Summable fun n => (v n) ^ 2)
    (hsep : ∀ n : ι, diagFormVal D c v η ≠ D n) (hne : ∃ n : ι, η n ≠ 0) :
    ∃ t : ℝ, ∀ n : ι, η' n = t * η n := by
  have hval : diagFormVal D c v η' = diagFormVal D c v η :=
    le_antisymm (hmin' _ hη) (hmin _ hη')
  refine eigen_proportional hsep (euler_lagrange hη hmin hvsum) ?_ hne
  intro m
  have := euler_lagrange hη' hmin' hvsum m
  rw [hval] at this
  exact this

end Cvs.WeilForm.MinimiserEulerLagrange
