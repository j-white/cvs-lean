import Mathlib
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaEulerLimitInstance

/-!
# The digamma asymptotic on the critical vertical line

Re ψ(¼ + it/2) = log(t/2) + O(1/t) for `t ≥ 2`.
-/

open Real Filter Topology

namespace DigammaAsym

open Filter Topology

/-- `q k = (¼+k)² + (t/2)²` — the denominator of `Re (¼+k+it/2)⁻¹`. -/
noncomputable def qq (t : ℝ) (k : ℕ) : ℝ := (1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2

theorem qq_pos (t : ℝ) (k : ℕ) : 0 < qq t k := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h : (0 : ℝ) < 1 / 4 + (k : ℝ) := by linarith
  unfold qq
  nlinarith [sq_nonneg (t / 2)]

theorem qq_succ (t : ℝ) (k : ℕ) :
    qq t (k + 1) = qq t k + (2 * (1 / 4 + (k : ℝ)) + 1) := by
  unfold qq; push_cast; ring

/-- The real part of the shifted reciprocal, in `qq` notation. -/
theorem re_inv_eq (t : ℝ) (k : ℕ) :
    (Cvs.Zeta.digammaArg t k)⁻¹.re = (1 / 4 + (k : ℝ)) / qq t k := by
  rw [Cvs.Zeta.re_inv_digammaArg]; rfl

/-- The discrepancy between the term and the telescoping log increment. -/
noncomputable def dd (t : ℝ) (k : ℕ) : ℝ :=
  (1 / 4 + (k : ℝ)) / qq t k
    - (Real.log (qq t (k + 1)) / 2 - Real.log (qq t k) / 2)

/-- **Exact decomposition.**  The partial sum is a telescoped log plus `Σ dd`. -/
theorem sum_inv_eq (t : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (Cvs.Zeta.digammaArg t k)⁻¹.re
      = (Real.log (qq t n) / 2 - Real.log (qq t 0) / 2)
        + ∑ k ∈ Finset.range n, dd t k := by
  have hterm : ∀ k ∈ Finset.range n, (Cvs.Zeta.digammaArg t k)⁻¹.re
      = (Real.log (qq t (k + 1)) / 2 - Real.log (qq t k) / 2) + dd t k := by
    intro k _
    rw [re_inv_eq, dd]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_range_sub (fun k => Real.log (qq t k) / 2) n

/-! ### The two-sided bound on `dd` -/

theorem dd_lower (t : ℝ) (k : ℕ) : -(1 / (2 * qq t k)) ≤ dd t k := by
  have hq := qq_pos t k
  have hq' := qq_pos t (k + 1)
  have hlog : Real.log (qq t (k + 1)) - Real.log (qq t k)
      ≤ (qq t (k + 1) - qq t k) / qq t k := by
    have h := Real.log_le_sub_one_of_pos (x := qq t (k + 1) / qq t k) (by positivity)
    rw [Real.log_div (ne_of_gt hq') (ne_of_gt hq)] at h
    have : qq t (k + 1) / qq t k - 1 = (qq t (k + 1) - qq t k) / qq t k := by
      field_simp
    linarith [this ▸ h]
  rw [qq_succ] at hlog
  have hsimp : (qq t k + (2 * (1 / 4 + (k : ℝ)) + 1) - qq t k) / qq t k
      = (2 * (1 / 4 + (k : ℝ)) + 1) / qq t k := by ring_nf
  rw [hsimp] at hlog
  rw [dd, qq_succ, ← sub_nonneg]
  have key : (1 / 4 + (k : ℝ)) / qq t k
      - (Real.log (qq t k + (2 * (1 / 4 + (k : ℝ)) + 1)) / 2 - Real.log (qq t k) / 2)
      - -(1 / (2 * qq t k))
      = ((2 * (1 / 4 + (k : ℝ)) + 1) / qq t k
          - (Real.log (qq t k + (2 * (1 / 4 + (k : ℝ)) + 1)) - Real.log (qq t k))) / 2 := by
    field_simp
    ring
  rw [key]
  linarith

theorem dd_upper (t : ℝ) (k : ℕ) : dd t k ≤ 7 / (2 * qq t k) := by
  have hq := qq_pos t k
  have hq' := qq_pos t (k + 1)
  have hlog : (qq t (k + 1) - qq t k) / qq t (k + 1)
      ≤ Real.log (qq t (k + 1)) - Real.log (qq t k) := by
    have h := Real.log_le_sub_one_of_pos (x := qq t k / qq t (k + 1)) (by positivity)
    rw [Real.log_div (ne_of_gt hq) (ne_of_gt hq')] at h
    have he : qq t k / qq t (k + 1) - 1 = (qq t k - qq t (k + 1)) / qq t (k + 1) := by
      field_simp
    rw [he] at h
    have hneg : (qq t k - qq t (k + 1)) / qq t (k + 1)
        = -((qq t (k + 1) - qq t k) / qq t (k + 1)) := by ring_nf
    rw [hneg] at h
    linarith
  -- reduce to a polynomial inequality
  rw [dd, ← sub_nonneg]
  have hstep : 7 / (2 * qq t k)
      - ((1 / 4 + (k : ℝ)) / qq t k
          - (Real.log (qq t (k + 1)) / 2 - Real.log (qq t k) / 2))
      = (7 / (2 * qq t k) - (1 / 4 + (k : ℝ)) / qq t k
          + (qq t (k + 1) - qq t k) / (2 * qq t (k + 1)))
        + ((Real.log (qq t (k + 1)) - Real.log (qq t k))
            - (qq t (k + 1) - qq t k) / qq t (k + 1)) / 2 := by
    field_simp
    ring
  rw [hstep]
  have hA : 0 ≤ 7 / (2 * qq t k) - (1 / 4 + (k : ℝ)) / qq t k
      + (qq t (k + 1) - qq t k) / (2 * qq t (k + 1)) := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hqq' : qq t (k + 1) = qq t k + (2 * (1 / 4 + (k : ℝ)) + 1) := qq_succ t k
    have hexp : 7 / (2 * qq t k) - (1 / 4 + (k : ℝ)) / qq t k
        + (qq t (k + 1) - qq t k) / (2 * qq t (k + 1))
        = (7 * qq t (k + 1) - 2 * (1 / 4 + (k : ℝ)) * qq t (k + 1)
            + (qq t (k + 1) - qq t k) * qq t k)
          / (2 * qq t k * qq t (k + 1)) := by
      field_simp
    rw [hexp]
    apply div_nonneg _ (by positivity)
    rw [hqq']
    unfold qq
    nlinarith [sq_nonneg (t / 2), sq_nonneg (1 / 4 + (k : ℝ)), hk]
  have hB : 0 ≤ ((Real.log (qq t (k + 1)) - Real.log (qq t k))
      - (qq t (k + 1) - qq t k) / qq t (k + 1)) / 2 := by linarith
  linarith

theorem abs_dd_le (t : ℝ) (k : ℕ) : |dd t k| ≤ 7 / (2 * qq t k) := by
  have hq := qq_pos t k
  have h1 := dd_lower t k
  have h2 := dd_upper t k
  rw [abs_le]
  constructor
  · have hpos : (0 : ℝ) < 2 * qq t k := by positivity
    have h7 : 1 / (2 * qq t k) ≤ 7 / (2 * qq t k) := by
      rw [div_le_div_iff₀ hpos hpos]; nlinarith
    linarith
  · exact h2

/-! ### `Σ 1/q k = O(1/t)` : two-regime split with a telescoped tail -/

/-- Telescoped tail: `Σ_{k ∈ [K,n)} 1/q k ≤ 1/(K−¾) − 1/(n−¾)` for `K ≥ 1`. -/
theorem tail_telescope (t : ℝ) {K : ℕ} (hK : 1 ≤ K) : ∀ n, K ≤ n →
    ∑ k ∈ Finset.Ico K n, 1 / qq t k
      ≤ 1 / ((K : ℝ) - 3 / 4) - 1 / ((n : ℝ) - 3 / 4) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
      have hmK : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans hK hm
      rw [Finset.sum_Ico_succ_top hm]
      have h1 : (0 : ℝ) < (m : ℝ) - 3 / 4 := by linarith
      have h2 : (0 : ℝ) < (m : ℝ) + 1 / 4 := by linarith
      have h1n : ((m : ℝ) - 3 / 4) ≠ 0 := ne_of_gt h1
      have h2n : ((m : ℝ) + 1 / 4) ≠ 0 := ne_of_gt h2
      have hterm : 1 / qq t m ≤ 1 / ((m : ℝ) - 3 / 4) - 1 / ((m : ℝ) + 1 / 4) := by
        have heq : 1 / ((m : ℝ) - 3 / 4) - 1 / ((m : ℝ) + 1 / 4)
            = 1 / (((m : ℝ) - 3 / 4) * ((m : ℝ) + 1 / 4)) := by
          rw [div_sub_div _ _ h1n h2n]
          congr 1
          ring
        rw [heq]
        have hdom : ((m : ℝ) - 3 / 4) * ((m : ℝ) + 1 / 4) ≤ qq t m := by
          unfold qq
          nlinarith [sq_nonneg (t / 2)]
        exact one_div_le_one_div_of_le (by positivity) hdom
      have hcast : (((m + 1 : ℕ) : ℝ) - 3 / 4) = ((m : ℝ) + 1 / 4) := by push_cast; ring
      rw [hcast]
      linarith

/-- **`Σ_{k<n} 1/q k ≤ 12/t`, uniformly in `n`, for `t ≥ 2`.** -/
theorem sum_inv_qq_le (t : ℝ) (ht : 2 ≤ t) (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / qq t k ≤ 16 / t := by
  have htpos : (0 : ℝ) < t := by linarith
  have hT : (1 : ℝ) ≤ t / 2 := by linarith
  set K : ℕ := ⌈t / 2⌉₊ with hKdef
  have hKge : (t / 2 : ℝ) ≤ (K : ℝ) := Nat.le_ceil _
  have hKlt : (K : ℝ) < t / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hK1 : 1 ≤ K := by
    by_contra h
    have : K = 0 := by omega
    rw [this] at hKge; norm_num at hKge; linarith
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  -- head bound
  have hhead : ∑ k ∈ Finset.range K, 1 / qq t k ≤ (K : ℝ) * (1 / (t / 2) ^ 2) := by
    have hb : ∀ k ∈ Finset.range K, 1 / qq t k ≤ 1 / (t / 2) ^ 2 := by
      intro k _
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      refine one_div_le_one_div_of_le (by positivity) ?_
      unfold qq; nlinarith
    calc ∑ k ∈ Finset.range K, 1 / qq t k
        ≤ ∑ _k ∈ Finset.range K, 1 / (t / 2) ^ 2 := Finset.sum_le_sum hb
      _ = (K : ℝ) * (1 / (t / 2) ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hhead' : ∑ k ∈ Finset.range K, 1 / qq t k ≤ 8 / t := by
    have heq : (K : ℝ) * (1 / (t / 2) ^ 2) = 4 * (K : ℝ) / t ^ 2 := by
      field_simp; ring
    have h1 : (K : ℝ) * (1 / (t / 2) ^ 2) ≤ 8 / t := by
      rw [heq, div_le_div_iff₀ (by positivity) htpos]
      nlinarith [hKlt, htpos, ht]
    linarith
  -- tail bound
  have htail : ∀ m : ℕ, ∑ k ∈ Finset.Ico K m, 1 / qq t k ≤ 8 / t := by
    intro m
    rcases le_or_gt K m with hm | hm
    · have h := tail_telescope t hK1 m hm
      have hmR : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hpos : (0 : ℝ) < (m : ℝ) - 3 / 4 := by linarith
      have hKpos : (0 : ℝ) < (K : ℝ) - 3 / 4 := by linarith
      have hb : 1 / ((K : ℝ) - 3 / 4) ≤ 8 / t := by
        rw [div_le_div_iff₀ hKpos htpos]
        nlinarith [hKge, ht]
      have : (0 : ℝ) < 1 / ((m : ℝ) - 3 / 4) := by positivity
      linarith
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      positivity
  -- combine
  rcases le_or_gt n K with hn | hn
  · have hsub : Finset.range n ⊆ Finset.range K := Finset.range_mono hn
    have hnn : ∀ k ∈ Finset.range K, k ∉ Finset.range n → 0 ≤ 1 / qq t k := by
      intro k _ _; have := qq_pos t k; positivity
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    have hsplit16 : (16 : ℝ) / t = 8 / t + 8 / t := by ring
    have h8 : (0 : ℝ) ≤ 8 / t := by positivity
    linarith
  · have hsplit : ∑ k ∈ Finset.range n, 1 / qq t k
        = (∑ k ∈ Finset.range K, 1 / qq t k) + ∑ k ∈ Finset.Ico K n, 1 / qq t k := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) (le_of_lt hn)]
    rw [hsplit]
    have := htail n
    have hsplit16 : (16 : ℝ) / t = 8 / t + 8 / t := by ring
    linarith

/-- **The partial sums of `dd` are uniformly `O(1/t)`.** -/
theorem abs_sum_dd_le (t : ℝ) (ht : 2 ≤ t) (n : ℕ) :
    |∑ k ∈ Finset.range n, dd t k| ≤ 56 / t := by
  have htpos : (0 : ℝ) < t := by linarith
  calc |∑ k ∈ Finset.range n, dd t k|
      ≤ ∑ k ∈ Finset.range n, |dd t k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (7 / 2) * (1 / qq t k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have := abs_dd_le t k
        have hq := qq_pos t k
        have heq : 7 / (2 * qq t k) = (7 / 2) * (1 / qq t k) := by field_simp
        linarith [heq ▸ this]
    _ = (7 / 2) * ∑ k ∈ Finset.range n, 1 / qq t k := (Finset.mul_sum _ _ _).symm
    _ ≤ (7 / 2) * (16 / t) := by
        have h := sum_inv_qq_le t ht n
        exact mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 56 / t := by ring

/-! ### The remainder `c n = ½ log q n − log n → 0` -/

noncomputable def cc (t : ℝ) (n : ℕ) : ℝ := Real.log (qq t n) / 2 - Real.log n

theorem cc_nonneg (t : ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ cc t n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ 2 ≤ qq t n := by
    unfold qq; nlinarith [sq_nonneg (t / 2)]
  have h2 : Real.log ((n : ℝ) ^ 2) ≤ Real.log (qq t n) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  unfold cc
  push_cast at h2
  linarith

theorem cc_le (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    cc t n ≤ (1 / 4 + (1 / 16 + (t / 2) ^ 2) / 2) / (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hq := qq_pos t n
  have h := Real.log_le_sub_one_of_pos (x := qq t n / (n : ℝ) ^ 2) (by positivity)
  rw [Real.log_div (ne_of_gt hq) (by positivity), Real.log_pow] at h
  have hkey : qq t n / (n : ℝ) ^ 2 - 1
      = ((n : ℝ) / 2 + 1 / 16 + (t / 2) ^ 2) / (n : ℝ) ^ 2 := by
    unfold qq; field_simp; ring
  rw [hkey] at h
  unfold cc
  push_cast at h
  have hb : ((n : ℝ) / 2 + 1 / 16 + (t / 2) ^ 2) / (n : ℝ) ^ 2
      ≤ 2 * ((1 / 4 + (1 / 16 + (t / 2) ^ 2) / 2) / (n : ℝ)) := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (1 : ℝ) ≤ (n : ℝ) := hnR
    have : 2 * ((1 / 4 + (1 / 16 + (t / 2) ^ 2) / 2) / (n : ℝ)) * (n : ℝ) ^ 2
        = (1 / 2 + (1 / 16 + (t / 2) ^ 2)) * (n : ℝ) := by field_simp; ring
    rw [this]
    nlinarith [sq_nonneg (t / 2), h2]
  linarith

theorem tendsto_cc (t : ℝ) : Tendsto (fun n : ℕ => cc t n) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_const_div_atTop_nhds_zero_nat (1 / 4 + (1 / 16 + (t / 2) ^ 2) / 2))
  · filter_upwards [eventually_ge_atTop 1] with n hn using cc_nonneg t hn
  · filter_upwards [eventually_ge_atTop 1] with n hn using cc_le t hn

/-! ### Assembly -/

/-- `Σ_{k<n} dd = ½ log q₀ − c n − F n`, where `F n` is the Euler–Gauss
approximant.  Exact, for every `n`. -/
theorem sum_dd_eq (t : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, dd t k
      = Real.log (qq t 0) / 2 - cc t n
        - (Real.log n - ∑ k ∈ Finset.range n, (Cvs.Zeta.digammaArg t k)⁻¹.re) := by
  rw [sum_inv_eq t n, cc]
  ring

/-- **`|½ log q₀ − Re ψ(¼+it/2)| ≤ 56/t`.** -/
theorem abs_logq0_sub_re_digamma_le (t : ℝ) (ht : 2 ≤ t) :
    |Real.log (qq t 0) / 2 - (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re| ≤ 56 / t := by
  have hF := (Cvs.Transform.instDigammaEulerLimitRe t).tendsto
  have hD : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, dd t k) atTop
      (𝓝 (Real.log (qq t 0) / 2 - 0
            - (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re)) := by
    simp only [sum_dd_eq t]
    exact (tendsto_const_nhds.sub (tendsto_cc t)).sub hF
  have habs := hD.abs
  simp only [sub_zero] at habs
  exact le_of_tendsto habs (Eventually.of_forall fun n => abs_sum_dd_le t ht n)

/-- `|½ log q₀ − log(t/2)| ≤ 1/(16 t)`. -/
theorem abs_logq0_sub_log_le (t : ℝ) (ht : 2 ≤ t) :
    |Real.log (qq t 0) / 2 - Real.log (t / 2)| ≤ 1 / (16 * t) := by
  have htpos : (0 : ℝ) < t := by linarith
  have hT : (1 : ℝ) ≤ t / 2 := by linarith
  have hq0 : qq t 0 = 1 / 16 + (t / 2) ^ 2 := by unfold qq; norm_num
  have hq0pos : (0 : ℝ) < qq t 0 := qq_pos t 0
  -- lower: log q₀ ≥ log ((t/2)^2)
  have hlo : Real.log ((t / 2) ^ 2) ≤ Real.log (qq t 0) := by
    refine Real.log_le_log (by positivity) ?_
    rw [hq0]; linarith
  have hlog2 : Real.log ((t / 2) ^ 2) = 2 * Real.log (t / 2) := by
    rw [Real.log_pow]; push_cast; ring
  -- upper: log(q₀/(t/2)^2) ≤ q₀/(t/2)^2 − 1 = 1/(16 (t/2)^2)
  have hup := Real.log_le_sub_one_of_pos (x := qq t 0 / (t / 2) ^ 2) (by positivity)
  rw [Real.log_div (ne_of_gt hq0pos) (by positivity), hlog2] at hup
  have hval : qq t 0 / (t / 2) ^ 2 - 1 = 1 / (16 * (t / 2) ^ 2) := by
    rw [hq0]; field_simp; ring
  rw [hval] at hup
  have hsmall : 1 / (16 * (t / 2) ^ 2) ≤ 2 * (1 / (16 * t)) := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 * (1 / (16 * t)) * (16 * (t / 2) ^ 2) = t / 2 := by field_simp
    rw [this]; linarith
  rw [abs_le]
  constructor <;> linarith

/-- **The digamma asymptotic on the critical vertical line.** `Re ψ(¼ + it/2) = log(t/2) +
O(1/t)`, with the explicit constant `57`. -/
theorem abs_re_digamma_sub_log_le (t : ℝ) (ht : 2 ≤ t) :
    |(Complex.digamma (Cvs.Zeta.digammaArg t 0)).re - Real.log (t / 2)| ≤ 57 / t := by
  have htpos : (0 : ℝ) < t := by linarith
  have h1 := abs_logq0_sub_re_digamma_le t ht
  have h2 := abs_logq0_sub_log_le t ht
  have hsmall : 1 / (16 * t) ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) htpos]; linarith
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have e1 : (57 : ℝ) / t = 56 / t + 1 / t := by ring
  rw [abs_le]
  constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2, hsmall, e1]

end DigammaAsym
