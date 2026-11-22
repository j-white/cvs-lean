import Mathlib

/-!
# A tight, coordinatewise-convergent sequence converges in norm

    ∑' (xₖ n − x n)²  ≤  2·tail T xₖ + 2·tail T x + ∑_{n ∈ T} (xₖ n − x n)²

so uniform tightness plus convergence at each coordinate is convergence in `ℓ²`.  This is
what `Cvs.WeilForm.Archimedean.ArchimedeanCoercive`'s coercivity is for: without it a minimising sequence can lose its mass.
-/

set_option maxHeartbeats 1600000

noncomputable section


namespace Cvs.Upstream.TightCoordinateConvergence

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- The mass a vector puts outside a finite set of modes. -/
def tail (T : Finset ι) (x : ι → ℝ) : ℝ := ∑' n : ι, if n ∈ T then (0:ℝ) else (x n) ^ 2

theorem summable_tail (T : Finset ι) {x : ι → ℝ} (hx : Summable fun n => (x n) ^ 2) :
    Summable fun n : ι => if n ∈ T then (0:ℝ) else (x n) ^ 2 :=
  hx.of_nonneg_of_le (fun n => by positivity) (fun n => by
    by_cases h : n ∈ T <;> simp [h, sq_nonneg])

/-- **The norm splits at any finite set.** -/
theorem tsum_sq_eq_add (T : Finset ι) {x : ι → ℝ} (hx : Summable fun n => (x n) ^ 2) :
    ∑' n : ι, (x n) ^ 2 = (∑ n ∈ T, (x n) ^ 2) + tail T x := by
  classical
  have hin : Summable fun n : ι => if n ∈ T then (x n) ^ 2 else 0 :=
    hx.of_nonneg_of_le (fun n => by positivity) (fun n => by
      by_cases h : n ∈ T <;> simp [h, sq_nonneg])
  have hsplit : ∑' n : ι, (x n) ^ 2
      = (∑' n : ι, if n ∈ T then (x n) ^ 2 else 0) + tail T x := by
    unfold tail
    rw [← hin.tsum_add (summable_tail T hx)]
    refine tsum_congr fun n => ?_
    by_cases h : n ∈ T <;> simp [h]
  rw [hsplit]
  congr 1
  rw [tsum_eq_sum (s := T) (f := fun n : ι => if n ∈ T then (x n) ^ 2 else 0)
    (fun n hn => by simp [hn])]
  exact Finset.sum_congr rfl fun n hn => by simp [hn]

/-- **The distance is the head plus twice the two tails.** -/
theorem tsum_sq_sub_le (T : Finset ι) {x y : ι → ℝ}
    (hx : Summable fun n => (x n) ^ 2) (hy : Summable fun n => (y n) ^ 2)
    (hsub : Summable fun n => (x n - y n) ^ 2) :
    ∑' n : ι, (x n - y n) ^ 2
      ≤ (∑ n ∈ T, (x n - y n) ^ 2) + 2 * tail T x + 2 * tail T y := by
  classical
  have hin : Summable fun n : ι => if n ∈ T then (x n - y n) ^ 2 else 0 :=
    hsub.of_nonneg_of_le (fun n => by positivity) (fun n => by
      by_cases h : n ∈ T <;> simp [h, sq_nonneg])
  have houtsum : Summable fun n : ι => if n ∈ T then (0:ℝ) else (x n - y n) ^ 2 :=
    hsub.of_nonneg_of_le (fun n => by positivity) (fun n => by
      by_cases h : n ∈ T <;> simp [h, sq_nonneg])
  have hsplit : ∑' n : ι, (x n - y n) ^ 2
      = (∑' n : ι, if n ∈ T then (x n - y n) ^ 2 else 0)
        + ∑' n : ι, (if n ∈ T then (0:ℝ) else (x n - y n) ^ 2) := by
    rw [← hin.tsum_add houtsum]
    refine tsum_congr fun n => ?_
    by_cases h : n ∈ T <;> simp [h]
  have hhead : (∑' n : ι, if n ∈ T then (x n - y n) ^ 2 else 0) = ∑ n ∈ T, (x n - y n) ^ 2 := by
    rw [tsum_eq_sum (s := T) (f := fun n : ι => if n ∈ T then (x n - y n) ^ 2 else 0)
      (fun n hn => by simp [hn])]
    exact Finset.sum_congr rfl fun n hn => by simp [hn]
  have htail : (∑' n : ι, if n ∈ T then (0:ℝ) else (x n - y n) ^ 2)
      ≤ 2 * tail T x + 2 * tail T y := by
    unfold tail
    rw [← (summable_tail T hx).tsum_mul_left 2, ← (summable_tail T hy).tsum_mul_left 2,
      ← ((summable_tail T hx).mul_left 2).tsum_add ((summable_tail T hy).mul_left 2)]
    refine Summable.tsum_le_tsum (fun n => ?_) houtsum
      (((summable_tail T hx).mul_left 2).add ((summable_tail T hy).mul_left 2))
    by_cases h : n ∈ T
    · simp [h]
    · simp only [h, if_false]
      nlinarith [sq_nonneg (x n + y n), sq_nonneg (x n - y n)]
  rw [hsplit, hhead]
  linarith

/-- Differences of square-summable vectors are square-summable. -/
theorem summable_sq_sub {x y : ι → ℝ} (hx : Summable fun n => (x n) ^ 2)
    (hy : Summable fun n => (y n) ^ 2) : Summable fun n => (x n - y n) ^ 2 := by
  refine ((hx.mul_left 2).add (hy.mul_left 2)).of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_)
  nlinarith [sq_nonneg (x n + y n), sq_nonneg (x n - y n)]

/-- **Tight plus coordinatewise is norm convergence.**  The head goes to zero because each
coordinate does, and the tails are uniformly small by hypothesis. -/
theorem tendsto_tsum_sq_sub {x : ℕ → ι → ℝ} {y : ι → ℝ}
    (hx : ∀ k, Summable fun n => (x k n) ^ 2) (hy : Summable fun n => (y n) ^ 2)
    (hcoord : ∀ n : ι, Filter.Tendsto (fun k => x k n) Filter.atTop (nhds (y n)))
    (htight : ∀ ε : ℝ, 0 < ε → ∃ T : Finset ι, (∀ k, tail T (x k) ≤ ε) ∧ tail T y ≤ ε) :
    Filter.Tendsto (fun k => ∑' n : ι, (x k n - y n) ^ 2) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT1, hT2⟩ := htight (ε / 8) (by positivity)
  have hhead : Filter.Tendsto (fun k => ∑ n ∈ T, (x k n - y n) ^ 2) Filter.atTop (nhds 0) := by
    have hz : Filter.Tendsto (fun k => ∑ n ∈ T, (x k n - y n) ^ 2) Filter.atTop
        (nhds (∑ n ∈ T, (0:ℝ))) := by
      refine tendsto_finsetSum T fun n _ => ?_
      have h := (hcoord n).sub (tendsto_const_nhds (x := y n))
      have h0 : Filter.Tendsto (fun k => x k n - y n) Filter.atTop (nhds 0) := by
        simpa using h
      simpa using h0.pow 2
    simpa using hz
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hhead (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have hbound := tsum_sq_sub_le T (hx k) hy (summable_sq_sub (hx k) hy)
  have hh : ∑ n ∈ T, (x k n - y n) ^ 2 < ε / 2 := by
    have := hN k hk
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun n _ => sq_nonneg _)] at this
    exact this
  have hnn : 0 ≤ ∑' n : ι, (x k n - y n) ^ 2 :=
    tsum_nonneg fun n => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have h1 := hT1 k
  linarith [hbound, hh, h1, hT2]

/-! ### The form does not grow in a coordinatewise limit -/

/-- **Fatou for a nonnegative diagonal form.**  A bound that holds along a sequence holds at
its coordinatewise limit. -/
theorem tsum_le_of_coord_limit {σ : ι → ℝ} (hσ : ∀ n, 0 ≤ σ n) {x : ℕ → ι → ℝ} {y : ι → ℝ}
    (hcoord : ∀ n : ι, Filter.Tendsto (fun k => x k n) Filter.atTop (nhds (y n)))
    {C : ℝ} (hsum : ∀ k, Summable fun n => σ n * (x k n) ^ 2)
    (hC : ∀ᶠ k in Filter.atTop, ∑' n : ι, σ n * (x k n) ^ 2 ≤ C) :
    ∑' n : ι, σ n * (y n) ^ 2 ≤ C := by
  refine Real.tsum_le_of_sum_le (fun n => mul_nonneg (hσ n) (sq_nonneg _)) fun T => ?_
  have hlim : Filter.Tendsto (fun k => ∑ n ∈ T, σ n * (x k n) ^ 2) Filter.atTop
      (nhds (∑ n ∈ T, σ n * (y n) ^ 2)) := by
    refine tendsto_finsetSum T fun n _ => ?_
    exact ((hcoord n).pow 2).const_mul (σ n)
  refine le_of_tendsto hlim ?_
  filter_upwards [hC] with k hk
  exact le_trans (sum_le_hasSum T (fun n _ => mul_nonneg (hσ n) (sq_nonneg _)) (hsum k).hasSum) hk

/-- **The mass passes to the limit too**, in both directions: the head is a limit of heads. -/
theorem tsum_sq_le_of_coord_limit {x : ℕ → ι → ℝ} {y : ι → ℝ}
    (hcoord : ∀ n : ι, Filter.Tendsto (fun k => x k n) Filter.atTop (nhds (y n)))
    {C : ℝ} (hsum : ∀ k, Summable fun n => (x k n) ^ 2)
    (hC : ∀ᶠ k in Filter.atTop, ∑' n : ι, (x k n) ^ 2 ≤ C) :
    ∑' n : ι, (y n) ^ 2 ≤ C := by
  have := tsum_le_of_coord_limit (σ := fun _ => (1:ℝ)) (fun _ => zero_le_one) hcoord
    (fun k => by simpa using hsum k) (by filter_upwards [hC] with k hk; simpa using hk)
  simpa using this

/-- **A tail bound passes to the limit.**  What the sequence keeps outside a finite set, the
limit keeps too — which is what stops mass escaping. -/
theorem tail_le_of_coord_limit {x : ℕ → ι → ℝ} {y : ι → ℝ} (T : Finset ι)
    (hcoord : ∀ n : ι, Filter.Tendsto (fun k => x k n) Filter.atTop (nhds (y n)))
    {ε : ℝ} (hsum : ∀ k, Summable fun n => (x k n) ^ 2)
    (hε : ∀ k, tail T (x k) ≤ ε) :
    tail T y ≤ ε := by
  unfold tail
  refine Real.tsum_le_of_sum_le (fun n => by by_cases h : n ∈ T <;> simp [h, sq_nonneg])
    fun S => ?_
  have hlim : Filter.Tendsto (fun k => ∑ n ∈ S, if n ∈ T then (0:ℝ) else (x k n) ^ 2)
      Filter.atTop (nhds (∑ n ∈ S, if n ∈ T then (0:ℝ) else (y n) ^ 2)) := by
    refine tendsto_finsetSum S fun n _ => ?_
    by_cases h : n ∈ T
    · simp [h]
    · simpa [h] using (hcoord n).pow 2
  refine le_of_tendsto hlim ?_
  filter_upwards with k
  refine le_trans (sum_le_hasSum S (fun n _ => by
    by_cases h : n ∈ T <;> simp [h, sq_nonneg]) (summable_tail T (hsum k)).hasSum) ?_
  exact hε k

/-! ### Compactness: a bounded sequence converges at every coordinate, along a subsequence -/

/-- **The coordinate box is compact.** -/
theorem isCompact_box :
    IsCompact {a : ι → ℝ | ∀ n : ι, a n ∈ Set.Icc (-1 : ℝ) 1} :=
  isCompact_pi_infinite fun _ => isCompact_Icc

/-- **Bolzano–Weierstrass, coordinatewise.**  A sequence of vectors bounded by one at every
coordinate has a subsequence converging at every coordinate. -/
theorem exists_coord_subseq {x : ℕ → ι → ℝ} (hb : ∀ (k : ℕ) (n : ι), |x k n| ≤ 1) :
    ∃ (y : ι → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ n : ι, Filter.Tendsto (fun k => x (φ k) n) Filter.atTop (nhds (y n)) := by
  have hmem : ∀ k, x k ∈ {a : ι → ℝ | ∀ n : ι, a n ∈ Set.Icc (-1 : ℝ) 1} := by
    intro k n
    exact abs_le.mp (hb k n)
  obtain ⟨y, _, φ, hφ, htend⟩ := isCompact_box.tendsto_subseq hmem
  refine ⟨y, φ, hφ, fun n => ?_⟩
  exact (tendsto_pi_nhds.mp htend) n

/-- A unit vector has every coordinate bounded by one. -/
theorem abs_le_one_of_unit {a : ι → ℝ} (hsum : Summable fun n => (a n) ^ 2)
    (hunit : ∑' n : ι, (a n) ^ 2 = 1) (n : ι) : |a n| ≤ 1 := by
  have hle : (a n) ^ 2 ≤ ∑' m : ι, (a m) ^ 2 := by
    have := sum_le_hasSum {n} (fun m _ => sq_nonneg _) hsum.hasSum
    simpa using this
  rw [hunit] at hle
  nlinarith [abs_nonneg (a n), sq_abs (a n)]

/-! ### Coercivity, for a general nonnegative symbol -/

/-- **The tail is paid for by the form.**  Mass outside a set whose complement sits above `M`
costs `M` per unit, so a bounded form leaves little of it. -/
theorem tail_le_of_form_le {σ : ι → ℝ} (hσ : ∀ n, 0 ≤ σ n) {a : ι → ℝ} {C M : ℝ} (hM : 0 < M)
    (hsum : Summable fun n => σ n * (a n) ^ 2) (hC : ∑' n : ι, σ n * (a n) ^ 2 ≤ C)
    (hnorm : Summable fun n => (a n) ^ 2)
    (T : Finset ι) (hout : ∀ n ∉ T, M ≤ σ n) :
    tail T a ≤ C / M := by
  classical
  have hstep : M * tail T a ≤ ∑' n : ι, σ n * (a n) ^ 2 := by
    unfold tail
    rw [← (summable_tail T hnorm).tsum_mul_left M]
    refine Summable.tsum_le_tsum (fun n => ?_) ((summable_tail T hnorm).mul_left M) hsum
    by_cases h : n ∈ T
    · simp only [h, if_true, mul_zero]
      exact mul_nonneg (hσ n) (sq_nonneg _)
    · simp only [h, if_false]
      exact mul_le_mul_of_nonneg_right (hout n h) (sq_nonneg _)
  rw [le_div_iff₀ hM, mul_comm]
  linarith [hstep, hC]

/-- **Uniform tightness from a uniform form bound**, given that only finitely many modes sit
below any level. -/
theorem exists_tail_le {σ : ι → ℝ} (hσ : ∀ n, 0 ≤ σ n)
    (hproper : ∀ M : ℝ, {n : ι | σ n < M}.Finite) {C : ℝ} (hC0 : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset ι, ∀ a : ι → ℝ, Summable (fun n => σ n * (a n) ^ 2) →
      Summable (fun n => (a n) ^ 2) → ∑' n : ι, σ n * (a n) ^ 2 ≤ C → tail T a ≤ ε := by
  classical
  set M : ℝ := C / ε + 1 with hMdef
  have hM : 0 < M := by
    have : 0 ≤ C / ε := by positivity
    linarith
  refine ⟨(hproper M).toFinset, fun a hsum hnorm hCa => ?_⟩
  have hout : ∀ n ∉ (hproper M).toFinset, M ≤ σ n := by
    intro n hn
    have : n ∉ {n : ι | σ n < M} := by simpa using hn
    exact not_lt.mp (by simpa using this)
  have := tail_le_of_form_le hσ hM hsum hCa hnorm _ hout
  refine le_trans this ?_
  rw [div_le_iff₀ hM, hMdef]
  have : C / ε * ε = C := by field_simp
  nlinarith [hε, hC0, this]

/-! ### The minimum is attained -/

/-- The form's domain on the unit sphere. -/
def sphereDom (σ : ι → ℝ) : Set (ι → ℝ) :=
  {a | (Summable fun n => (a n) ^ 2) ∧ (∑' n : ι, (a n) ^ 2 = 1)
        ∧ Summable fun n => σ n * (a n) ^ 2}

/-- The quadratic form: a nonnegative diagonal part and a bounded part. -/
def formVal (σ : ι → ℝ) (Bfun : (ι → ℝ) → ℝ) (a : ι → ℝ) : ℝ :=
  (∑' n : ι, σ n * (a n) ^ 2) + Bfun a

/-- **The direct method.**  A nonnegative diagonal form whose modes leave every level, plus a
bounded part continuous along `ℓ²` convergence, attains its minimum on the unit sphere. -/
theorem exists_minimiser {σ : ι → ℝ} {Bfun : (ι → ℝ) → ℝ} {CB : ℝ}
    (hσ : ∀ n, 0 ≤ σ n)
    (hproper : ∀ M : ℝ, {n : ι | σ n < M}.Finite)
    (hBbdd : ∀ a ∈ sphereDom σ, |Bfun a| ≤ CB)
    (hBcont : ∀ (x : ℕ → ι → ℝ) (y : ι → ℝ), (∀ k, x k ∈ sphereDom σ) → y ∈ sphereDom σ →
        Filter.Tendsto (fun k => ∑' n : ι, (x k n - y n) ^ 2) Filter.atTop (nhds 0) →
        Filter.Tendsto (fun k => Bfun (x k)) Filter.atTop (nhds (Bfun y)))
    (hne : (sphereDom σ).Nonempty) :
    ∃ η ∈ sphereDom σ, ∀ a ∈ sphereDom σ, formVal σ Bfun η ≤ formVal σ Bfun a := by
  classical
  set V : Set ℝ := formVal σ Bfun '' sphereDom σ with hV
  have hVne : V.Nonempty := hne.image _
  have hbdd : BddBelow V := by
    refine ⟨-CB, ?_⟩
    rintro v ⟨a, ha, rfl⟩
    have h1 : 0 ≤ ∑' n : ι, σ n * (a n) ^ 2 :=
      tsum_nonneg fun n => mul_nonneg (hσ n) (sq_nonneg _)
    have h2 : -CB ≤ Bfun a := neg_le_of_abs_le (hBbdd a ha)
    unfold formVal
    linarith
  set I : ℝ := sInf V with hI
  -- a minimising sequence
  have hstep : ∀ k : ℕ, ∃ a ∈ sphereDom σ, formVal σ Bfun a < I + 1 / (k + 1) := by
    intro k
    have hpos : (0:ℝ) < 1 / (k + 1) := by positivity
    obtain ⟨v, hv, hlt⟩ := exists_lt_of_csInf_lt hVne (by linarith : I < I + 1 / (k + 1))
    obtain ⟨a, ha, rfl⟩ := hv
    exact ⟨a, ha, hlt⟩
  choose a ha hlt using hstep
  -- uniform bounds along it
  set C : ℝ := I + 1 + CB with hC
  have hC0 : 0 ≤ C := by
    have h0 : -CB ≤ I := le_csInf hVne (by
      rintro v ⟨b, hb, rfl⟩
      have h1 : 0 ≤ ∑' n : ι, σ n * (b n) ^ 2 :=
        tsum_nonneg fun n => mul_nonneg (hσ n) (sq_nonneg _)
      have h2 : -CB ≤ Bfun b := neg_le_of_abs_le (hBbdd b hb)
      unfold formVal
      linarith)
    linarith [abs_nonneg (Bfun (a 0)), hBbdd (a 0) (ha 0)]
  have hformC : ∀ k, ∑' n : ι, σ n * (a k n) ^ 2 ≤ C := by
    intro k
    have h1 := hlt k
    have h2 : -CB ≤ Bfun (a k) := neg_le_of_abs_le (hBbdd (a k) (ha k))
    have h3 : (1:ℝ) / (k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0:ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    unfold formVal at h1
    linarith
  -- a coordinatewise convergent subsequence
  have hbnd : ∀ (k : ℕ) (n : ι), |a k n| ≤ 1 := fun k n =>
    abs_le_one_of_unit (ha k).1 (ha k).2.1 n
  obtain ⟨y, φ, hφ, hcoord⟩ := exists_coord_subseq hbnd
  set x : ℕ → ι → ℝ := fun k => a (φ k) with hxdef
  have hxdom : ∀ k, x k ∈ sphereDom σ := fun k => ha (φ k)
  have hxform : ∀ k, ∑' n : ι, σ n * (x k n) ^ 2 ≤ C := fun k => hformC (φ k)
  -- tightness, uniform along the sequence and inherited by the limit
  have htight : ∀ ε : ℝ, 0 < ε → ∃ T : Finset ι, (∀ k, tail T (x k) ≤ ε) ∧ tail T y ≤ ε := by
    intro ε hε
    obtain ⟨T, hT⟩ := exists_tail_le hσ hproper hC0 hε
    have hall : ∀ k, tail T (x k) ≤ ε := fun k =>
      hT (x k) (hxdom k).2.2 (hxdom k).1 (hxform k)
    exact ⟨T, hall, tail_le_of_coord_limit T hcoord (fun k => (hxdom k).1) hall⟩
  -- the limit is square-summable, and a unit vector
  have hysum : Summable fun n : ι => (y n) ^ 2 := by
    refine summable_of_sum_le (c := 1) (fun n => sq_nonneg _) fun T => ?_
    have hlim : Filter.Tendsto (fun k => ∑ n ∈ T, (x k n) ^ 2) Filter.atTop
        (nhds (∑ n ∈ T, (y n) ^ 2)) :=
      tendsto_finsetSum T fun n _ => ((hcoord n).pow 2)
    refine le_of_tendsto hlim ?_
    filter_upwards with k
    calc ∑ n ∈ T, (x k n) ^ 2
        ≤ ∑' n : ι, (x k n) ^ 2 := sum_le_hasSum T (fun n _ => sq_nonneg _) (hxdom k).1.hasSum
      _ = 1 := (hxdom k).2.1
  have hyunit : ∑' n : ι, (y n) ^ 2 = 1 := by
    refine le_antisymm ?_ ?_
    · exact tsum_sq_le_of_coord_limit hcoord (fun k => (hxdom k).1)
        (Filter.Eventually.of_forall fun k => le_of_eq (hxdom k).2.1)
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨T, hT1, _⟩ := htight ε hε
      have hlim : Filter.Tendsto (fun k => ∑ n ∈ T, (x k n) ^ 2) Filter.atTop
          (nhds (∑ n ∈ T, (y n) ^ 2)) :=
        tendsto_finsetSum T fun n _ => ((hcoord n).pow 2)
      have hge : ∀ k, 1 - ε ≤ ∑ n ∈ T, (x k n) ^ 2 := by
        intro k
        have hsplit := tsum_sq_eq_add T (hxdom k).1
        rw [(hxdom k).2.1] at hsplit
        linarith [hT1 k]
      have h1 : 1 - ε ≤ ∑ n ∈ T, (y n) ^ 2 :=
        ge_of_tendsto hlim (Filter.Eventually.of_forall hge)
      have h2 : ∑ n ∈ T, (y n) ^ 2 ≤ ∑' n : ι, (y n) ^ 2 :=
        sum_le_hasSum T (fun n _ => sq_nonneg _) hysum.hasSum
      linarith
  have hyform : Summable fun n : ι => σ n * (y n) ^ 2 := by
    refine summable_of_sum_le (c := C) (fun n => mul_nonneg (hσ n) (sq_nonneg _)) fun T => ?_
    have hlim : Filter.Tendsto (fun k => ∑ n ∈ T, σ n * (x k n) ^ 2) Filter.atTop
        (nhds (∑ n ∈ T, σ n * (y n) ^ 2)) :=
      tendsto_finsetSum T fun n _ => ((hcoord n).pow 2).const_mul (σ n)
    refine le_of_tendsto hlim ?_
    filter_upwards with k
    exact le_trans (sum_le_hasSum T (fun n _ => mul_nonneg (hσ n) (sq_nonneg _))
      (hxdom k).2.2.hasSum) (hxform k)
  -- tightness upgrades coordinatewise convergence to norm convergence
  have hstrong := tendsto_tsum_sq_sub (fun k => (hxdom k).1) hysum hcoord htight
  have hBlim := hBcont x y hxdom ⟨hysum, hyunit, hyform⟩ hstrong
  -- the value at the limit is the infimum
  have hQy : formVal σ Bfun y ≤ I := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hsmall : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hev1 : ∀ᶠ k in Filter.atTop, formVal σ Bfun (x k) < I + ε / 2 := by
      have hlt2 : ∀ k : ℕ, formVal σ Bfun (x k) < I + 1 / ((k : ℝ) + 1) := by
        intro k
        refine lt_of_lt_of_le (hlt (φ k)) ?_
        have hk : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφ.le_apply
        have : (1:ℝ) / ((φ k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          linarith
        linarith
      have hlim0 : ∀ᶠ k : ℕ in Filter.atTop, 1 / ((k : ℝ) + 1) < ε / 2 :=
        hsmall.eventually_lt_const (by positivity)
      filter_upwards [hlim0] with k hk
      linarith [hlt2 k]
    have hev2 : ∀ᶠ k in Filter.atTop, Bfun y - ε / 2 < Bfun (x k) := by
      have := hBlim.eventually (lt_mem_nhds (by linarith : Bfun y - ε / 2 < Bfun y))
      simpa using this
    have hev : ∀ᶠ k in Filter.atTop,
        ∑' n : ι, σ n * (x k n) ^ 2 ≤ I + ε - Bfun y := by
      filter_upwards [hev1, hev2] with k h1 h2
      unfold formVal at h1
      linarith
    have := tsum_le_of_coord_limit hσ hcoord (fun k => (hxdom k).2.2) hev
    unfold formVal
    linarith
  refine ⟨y, ⟨hysum, hyunit, hyform⟩, fun b hb => ?_⟩
  exact le_trans hQy (csInf_le hbdd ⟨b, hb, rfl⟩)

end Cvs.Upstream.TightCoordinateConvergence
