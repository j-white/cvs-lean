import Mathlib
import Cvs.Upstream.MontgomeryVaughanDuality
import Cvs.Upstream.MontgomeryVaughanEigenBound
import Cvs.Upstream.MontgomeryVaughanQuadratic
import Cvs.Upstream.MontgomeryVaughanRealAntisymmetric

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Hilbert's inequality with constant `π` for real nodes with a uniform gap

For real `λ_r` with `|λ_r − λ_s| ≥ D > 0` (`r ≠ s`), every distance shell `[kD, (k+1)D)` around a node holds at most two
other nodes, so `Σ_{m≠n} D²/(λ_n − λ_m)² ≤ 2ζ(2) = π²/3`; with the Preissmann–Lévêque identity every eigenvalue of
`√D√D/(λ_m − λ_n)` is at most `π`, whence `|Σ_{r≠t} x_r x̄_t/(λ_r − λ_t)| ≤ (π/D)Σ|x_r|²` and, for real vectors,
`|Σ_{r≠t} x_r z_t/(λ_r − λ_t)| ≤ (π/2)(s²Σx_r² + Σz_r²/s²)/D`.
-/

noncomputable section

namespace Cvs.Upstream.HilbertInequalityUniformGap

open Finset Complex Real Matrix
open scoped ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι] {freq : ι → ℝ} {D : ℝ}

/-- The shell index `⌊|λ_m − λ_n|/D⌋`. -/
def shell (freq : ι → ℝ) (D : ℝ) (n m : ι) : ℕ := ⌊|freq m - freq n| / D⌋₊

omit [Fintype ι] [DecidableEq ι] in
theorem shell_bounds (hD : 0 < D) (n m : ι) :
    (shell freq D n m : ℝ) * D ≤ |freq m - freq n| ∧ |freq m - freq n| < ((shell freq D n m : ℝ) + 1) * D := by
  have h0 : 0 ≤ |freq m - freq n| / D := by positivity
  constructor
  · have := Nat.floor_le h0; unfold shell; rwa [le_div_iff₀ hD] at this
  · have := Nat.lt_floor_add_one (|freq m - freq n| / D); unfold shell; rwa [div_lt_iff₀ hD] at this

omit [Fintype ι] [DecidableEq ι] in
theorem one_le_shell (hD : 0 < D) (hgap : ∀ r s, r ≠ s → D ≤ |freq r - freq s|) {n m : ι} (hmn : m ≠ n) :
    1 ≤ shell freq D n m := by
  unfold shell
  apply Nat.le_floor
  rw [Nat.cast_one, le_div_iff₀ hD, one_mul]; exact hgap m n hmn

/-- **At most two nodes in each shell.** -/
theorem card_shell_le (hD : 0 < D) (hgap : ∀ r s, r ≠ s → D ≤ |freq r - freq s|) (n : ι) (k : ℕ) :
    ((univ.erase n).filter (fun m => shell freq D n m = k)).card ≤ 2 := by
  set S := (univ.erase n).filter (fun m => shell freq D n m = k) with hS
  have hsplit : S = S.filter (fun m => freq m < freq n) ∪ S.filter (fun m => ¬ freq m < freq n) :=
    (Finset.filter_union_filter_not_eq _ _).symm
  have hside : ∀ P : ι → Prop, [DecidablePred P] → (∀ m ∈ S, ∀ m' ∈ S, P m → P m' →
      |freq m - freq m'| < D) → (S.filter P).card ≤ 1 := by
    intro P _ hP
    rw [Finset.card_le_one]
    intro m hm m' hm'
    rw [Finset.mem_filter] at hm hm'
    by_contra hne
    have := hgap m m' hne
    have := hP m hm.1 m' hm'.1 hm.2 hm'.2
    linarith
  have hk : ∀ m ∈ S, (k : ℝ) * D ≤ |freq m - freq n| ∧ |freq m - freq n| < ((k : ℝ) + 1) * D := by
    intro m hm
    rw [hS, Finset.mem_filter] at hm
    have := shell_bounds (freq := freq) hD n m
    rw [hm.2] at this; exact this
  have hL : (S.filter (fun m => freq m < freq n)).card ≤ 1 := hside _ fun m hm m' hm' hlt hlt' => by
    obtain ⟨a1, a2⟩ := hk m hm; obtain ⟨b1, b2⟩ := hk m' hm'
    rw [abs_of_neg (by linarith)] at a1 a2; rw [abs_of_neg (by linarith)] at b1 b2
    rw [abs_lt]; constructor <;> linarith
  have hR : (S.filter (fun m => ¬ freq m < freq n)).card ≤ 1 := hside _ fun m hm m' hm' hlt hlt' => by
    push Not at hlt hlt'
    obtain ⟨a1, a2⟩ := hk m hm; obtain ⟨b1, b2⟩ := hk m' hm'
    rw [abs_of_nonneg (by linarith)] at a1 a2; rw [abs_of_nonneg (by linarith)] at b1 b2
    rw [abs_lt]; constructor <;> linarith
  calc S.card ≤ (S.filter (fun m => freq m < freq n)).card + (S.filter (fun m => ¬ freq m < freq n)).card := by
        conv_lhs => rw [hsplit]
        exact Finset.card_union_le _ _
    _ ≤ 2 := by omega

/-- **The spacing sum**: `Σ_{m≠n} D²/(λ_n − λ_m)² ≤ π²/3`. -/
theorem spacing_sum_le (hD : 0 < D) (hgap : ∀ r s, r ≠ s → D ≤ |freq r - freq s|) (n : ι) :
    ∑ m ∈ univ.erase n, D ^ 2 / (freq n - freq m) ^ 2 ≤ π ^ 2 / 3 := by
  set kf := shell freq D n with hkf
  have hterm : ∀ m ∈ univ.erase n, D ^ 2 / (freq n - freq m) ^ 2 ≤ 1 / (kf m : ℝ) ^ 2 := by
    intro m hm
    have hmn : m ≠ n := Finset.ne_of_mem_erase hm
    have h1 : (1 : ℝ) ≤ kf m := by exact_mod_cast one_le_shell hD hgap hmn
    have hb := (shell_bounds (freq := freq) hD n m).1
    have hsq : (freq n - freq m) ^ 2 = |freq m - freq n| ^ 2 := by rw [sq_abs]; ring
    have hpos : 0 < |freq m - freq n| := lt_of_lt_of_le hD (hgap m n hmn)
    rw [hsq, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have : ((kf m : ℝ) * D) ^ 2 ≤ |freq m - freq n| ^ 2 :=
      pow_le_pow_left₀ (by positivity) hb 2
    nlinarith
  have hS := Finset.sum_le_sum hterm
  -- group by shells
  have hgroup : ∑ m ∈ univ.erase n, 1 / (kf m : ℝ) ^ 2
      = ∑ k ∈ (univ.erase n).image kf, (((univ.erase n).filter (fun m => kf m = k)).card : ℝ) * (1 / (k : ℝ) ^ 2) := by
    rw [Finset.sum_comp (fun k : ℕ => 1 / (k : ℝ) ^ 2) kf]
    simp [nsmul_eq_mul]
  have hcard : ∑ k ∈ (univ.erase n).image kf, (((univ.erase n).filter (fun m => kf m = k)).card : ℝ) * (1 / (k : ℝ) ^ 2)
      ≤ ∑ k ∈ (univ.erase n).image kf, 2 * (1 / (k : ℝ) ^ 2) := by
    apply Finset.sum_le_sum; intro k _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast card_shell_le hD hgap n k
  have hz : ∑ k ∈ (univ.erase n).image kf, 1 / (k : ℝ) ^ 2 ≤ π ^ 2 / 6 := by
    have hs : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) := hasSum_zeta_two.summable
    have := hs.sum_le_tsum ((univ.erase n).image kf) (fun k _ => by positivity)
    rwa [hasSum_zeta_two.tsum_eq] at this
  rw [← Finset.mul_sum] at hcard
  linarith

/-- **The cross form**: for `v ≥ 0`, `Σ_m Σ_{n≠m} D² v_m v_n/(λ_m − λ_n)² ≤ (π²/3) Σ v²`. -/
theorem cross_sum_le (hD : 0 < D) (hgap : ∀ r s, r ≠ s → D ≤ |freq r - freq s|) (v : ι → ℝ) :
    ∑ m, ∑ n ∈ univ.erase m, D ^ 2 * v m * v n / (freq m - freq n) ^ 2 ≤ π ^ 2 / 3 * ∑ m, v m ^ 2 := by
  have hpt : ∀ m n, m ≠ n → D ^ 2 * v m * v n / (freq m - freq n) ^ 2
      ≤ (v m ^ 2 + v n ^ 2) / 2 * (D ^ 2 / (freq m - freq n) ^ 2) := by
    intro m n hmn
    have hd : 0 < (freq m - freq n) ^ 2 := by
      have hpos : 0 < |freq m - freq n| := lt_of_lt_of_le hD (hgap m n hmn)
      rw [← sq_abs]; positivity
    have hvv : v m * v n ≤ (v m ^ 2 + v n ^ 2) / 2 := by nlinarith [sq_nonneg (v m - v n)]
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hd]
    nlinarith [sq_nonneg D]
  have h1 := Finset.sum_le_sum fun m (_ : m ∈ univ) =>
    Finset.sum_le_sum fun n (hn : n ∈ univ.erase m) => hpt m n (Finset.ne_of_mem_erase hn).symm
  have hsymm : ∑ m, ∑ n ∈ univ.erase m, v n ^ 2 / 2 * (D ^ 2 / (freq m - freq n) ^ 2)
      = ∑ m, ∑ n ∈ univ.erase m, v m ^ 2 / 2 * (D ^ 2 / (freq m - freq n) ^ 2) := by
    rw [Cvs.Zeta.Base.MV.sum_erase_comm]; apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl
    intro n _; congr 2; ring
  have e : ∑ m, ∑ n ∈ univ.erase m, (v m ^ 2 + v n ^ 2) / 2 * (D ^ 2 / (freq m - freq n) ^ 2)
      = ∑ m, v m ^ 2 * ∑ n ∈ univ.erase m, D ^ 2 / (freq m - freq n) ^ 2 := by
    have : ∀ m, ∑ n ∈ univ.erase m, (v m ^ 2 + v n ^ 2) / 2 * (D ^ 2 / (freq m - freq n) ^ 2)
        = ∑ n ∈ univ.erase m, v m ^ 2 / 2 * (D ^ 2 / (freq m - freq n) ^ 2)
          + ∑ n ∈ univ.erase m, v n ^ 2 / 2 * (D ^ 2 / (freq m - freq n) ^ 2) := fun m => by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro n _; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, hsymm, ← two_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; ring
  have h2 : ∑ m, v m ^ 2 * ∑ n ∈ univ.erase m, D ^ 2 / (freq m - freq n) ^ 2 ≤ ∑ m, v m ^ 2 * (π ^ 2 / 3) :=
    Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (spacing_sum_le hD hgap m) (sq_nonneg _)
  rw [← Finset.sum_mul] at h2
  linarith

/-- **Every eigenvalue is at most `π`**: for a unit `u` with `(Hu)_m = iμ u_m`, `H_{mn} = D/(λ_m − λ_n)`. -/
theorem eigen_le_pi (hD : 0 < D) (hgap : ∀ r s, r ≠ s → D ≤ |freq r - freq s|) (u : ι → ℂ)
    (hu : ∑ n, ‖u n‖ ^ 2 = 1) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ univ.erase m, ((Real.sqrt D * Real.sqrt D / (freq m - freq n) : ℝ) : ℂ) * u n
      = (μ : ℂ) * Complex.I * u m) : |μ| ≤ π := by
  have hinj : Function.Injective freq := fun r s h => by
    by_contra hne; have := hgap r s hne; rw [h, sub_self, abs_zero] at this; linarith
  set c : ι → ℝ := fun _ => Real.sqrt D with hc
  have hcpos : ∀ r, 0 < c r := fun r => Real.sqrt_pos.mpr hD
  have hsD : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  have hid := Cvs.Zeta.Base.MV.eigen_identity hinj c hcpos u μ heig
  have hsum : μ ^ 2 = (∑ m, ∑ n ∈ univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
      + 2 * ∑ m, ∑ n ∈ univ.erase m, c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2 := by
    calc μ ^ 2 = ∑ m, μ ^ 2 * ‖u m‖ ^ 2 := by rw [← Finset.mul_sum, hu, mul_one]
      _ = _ := by rw [Finset.sum_congr rfl fun m _ => hid m, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- the first sum
  have hS : ∑ m, ∑ n ∈ univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2 ≤ π ^ 2 / 3 := by
    have e : ∀ m n, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2
        = ‖u n‖ ^ 2 * (D ^ 2 / (freq n - freq m) ^ 2) := by
      intro m n; simp only [hc, mul_pow, hsD]
      rw [show (freq m - freq n) ^ 2 = (freq n - freq m) ^ 2 by ring]; ring
    simp_rw [e]
    rw [Cvs.Zeta.Base.MV.sum_erase_comm]
    calc ∑ n, ∑ m ∈ univ.erase n, ‖u n‖ ^ 2 * (D ^ 2 / (freq n - freq m) ^ 2)
        = ∑ n, ‖u n‖ ^ 2 * ∑ m ∈ univ.erase n, D ^ 2 / (freq n - freq m) ^ 2 := by
          apply Finset.sum_congr rfl; intro n _; rw [Finset.mul_sum]
      _ ≤ ∑ n, ‖u n‖ ^ 2 * (π ^ 2 / 3) :=
          Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (spacing_sum_le hD hgap n) (sq_nonneg _)
      _ = π ^ 2 / 3 := by rw [← Finset.sum_mul, hu, one_mul]
  -- the second sum
  have hT : |∑ m, ∑ n ∈ univ.erase m, c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2|
      ≤ π ^ 2 / 3 := by
    have hper : ∀ m n, |c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2|
        ≤ D ^ 2 * ‖u m‖ * ‖u n‖ / (freq m - freq n) ^ 2 := by
      intro m n
      have hre : |(u m * conj (u n)).re| ≤ ‖u m‖ * ‖u n‖ := by
        refine (Complex.abs_re_le_norm _).trans ?_; rw [norm_mul, RCLike.norm_conj]
      have hc4 : c m ^ 3 * c n = D ^ 2 := by
        simp only [hc]; rw [show Real.sqrt D ^ 3 * Real.sqrt D = (Real.sqrt D ^ 2) ^ 2 by ring, hsD]
      rw [hc4, abs_div, abs_mul, abs_of_nonneg (sq_nonneg D), abs_of_nonneg (sq_nonneg (freq m - freq n))]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hre (sq_nonneg D)
    calc |∑ m, ∑ n ∈ univ.erase m, c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2|
        ≤ ∑ m, ∑ n ∈ univ.erase m, |c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ m, ∑ n ∈ univ.erase m, D ^ 2 * ‖u m‖ * ‖u n‖ / (freq m - freq n) ^ 2 :=
          Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => hper m n
      _ ≤ π ^ 2 / 3 * ∑ m, ‖u m‖ ^ 2 := cross_sum_le hD hgap (fun m => ‖u m‖)
      _ = π ^ 2 / 3 := by rw [hu, mul_one]
  have hmain : μ ^ 2 ≤ π ^ 2 := by
    have := abs_le.mp hT; linarith [hS, this.1, this.2]
  exact abs_le_of_sq_le_sq' hmain pi_pos.le |> fun h => abs_le.mpr h

/-- Every eigenvalue of `M = iK` for the uniform-gap family has absolute value `≤ π`. -/
theorem abs_eigenvalue_le_pi (hD : 0 < D) (hgap : ∀ r s, r ≠ s → D ≤ |freq r - freq s|) (j : ι) :
    |(Cvs.Zeta.Base.MV.Mmat_isHermitian freq (fun _ => D)).eigenvalues j| ≤ π := by
  set hM := Cvs.Zeta.Base.MV.Mmat_isHermitian freq (fun _ : ι => D)
  set ν : ℝ := hM.eigenvalues j
  set v : ι → ℂ := ⇑(hM.eigenvectorBasis j) with hvdef
  have hv : Cvs.Zeta.Base.MV.Mmat freq (fun _ => D) *ᵥ v = ν • v := hM.mulVec_eigenvectorBasis j
  have hunit : ∑ n, ‖v n‖ ^ 2 = 1 := by
    have h1 : ‖hM.eigenvectorBasis j‖ = 1 := hM.eigenvectorBasis.orthonormal.1 j
    rw [← EuclideanSpace.norm_sq_eq, h1, one_pow]
  have heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
      ((Real.sqrt D * Real.sqrt D / (freq m - freq n) : ℝ) : ℂ) * v n
        = ((-ν : ℝ) : ℂ) * Complex.I * v m := by
    intro m
    have hm := congrFun hv m
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at hm
    have hsplit : ∑ s, Cvs.Zeta.Base.MV.Mmat freq (fun _ => D) m s * v s
        = ∑ s ∈ Finset.univ.erase m, (Cvs.Zeta.Base.MV.kfun freq (fun _ => D) m s : ℂ) * Complex.I * v s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
      simp [Cvs.Zeta.Base.MV.Mmat, Cvs.Zeta.Base.MV.kfun]
    rw [hsplit] at hm
    have hk : ∀ s ∈ Finset.univ.erase m, (Cvs.Zeta.Base.MV.kfun freq (fun _ => D) m s : ℂ) * Complex.I * v s
        = Complex.I * (((Real.sqrt D * Real.sqrt D / (freq m - freq s) : ℝ) : ℂ) * v s) := by
      intro s hs
      have hsm : m ≠ s := fun e => (Finset.mem_erase.mp hs).1 e.symm
      simp only [Cvs.Zeta.Base.MV.kfun, if_neg hsm]; ring
    rw [Finset.sum_congr rfl hk, ← Finset.mul_sum] at hm
    calc ∑ n ∈ Finset.univ.erase m, ((Real.sqrt D * Real.sqrt D / (freq m - freq n) : ℝ) : ℂ) * v n
        = -Complex.I * (Complex.I * ∑ n ∈ Finset.univ.erase m,
            ((Real.sqrt D * Real.sqrt D / (freq m - freq n) : ℝ) : ℂ) * v n) := by
          rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
      _ = -Complex.I * ((ν : ℂ) * v m) := by rw [hm]
      _ = ((-ν : ℝ) : ℂ) * Complex.I * v m := by push_cast; ring
  have := eigen_le_pi hD hgap v hunit (-ν) heig
  simpa using this

/-- **Hilbert's inequality with constant `π`, uniform gap**: `|Σ_{r≠t} x_r x̄_t/(λ_r − λ_t)| ≤ (π/D) Σ|x_r|²`. -/
theorem hilbert_diag (hD : 0 < D) (hgap : ∀ r s, r ≠ s → D ≤ |freq r - freq s|) (x : ι → ℂ) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ π * ∑ r, ‖x r‖ ^ 2 / D := by
  have hinj : Function.Injective freq := fun r s h => by
    by_contra hne; have := hgap r s hne; rw [h, sub_self, abs_zero] at this; linarith
  set y : ι → ℂ := fun r => x r / (Real.sqrt D : ℂ) with hydef
  have hsq : (Real.sqrt D : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hxy : ∀ r, x r = (Real.sqrt D : ℂ) * y r := fun r => by simp only [hydef]; field_simp [hsq]
  have hnorm : ∑ r, ‖y r‖ ^ 2 = ∑ r, ‖x r‖ ^ 2 / D := by
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hydef, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hD.le]
  have hterm : ∀ r s, (if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ))
      = y r * conj (y s) * (Cvs.Zeta.Base.MV.kfun freq (fun _ => D) r s : ℂ) := by
    intro r s
    by_cases hrs : r = s
    · simp [hrs, Cvs.Zeta.Base.MV.kfun]
    · rw [if_neg hrs]
      simp only [Cvs.Zeta.Base.MV.kfun, if_neg hrs, hxy r, hxy s, map_mul, Complex.conj_ofReal]
      have hf : ((freq r - freq s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (fun e => hrs (hinj e))
      push_cast
      field_simp
  have hsum : (∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ))
      = conj (star y ⬝ᵥ (Cvs.Zeta.Base.MV.Mmat freq (fun _ => D) *ᵥ y)) * Complex.I := by
    simp only [hterm, dotProduct, Matrix.mulVec, Cvs.Zeta.Base.MV.Mmat, Pi.star_apply, Complex.star_def, map_sum,
      map_mul, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_I, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (y r * conj (y s) * (Cvs.Zeta.Base.MV.kfun freq (fun _ => D) r s : ℂ)) * this
  rw [hsum, norm_mul, Complex.norm_I, mul_one, Complex.norm_conj, ← hnorm]
  set hM := Cvs.Zeta.Base.MV.Mmat_isHermitian freq (fun _ : ι => D)
  rw [Cvs.Zeta.Base.MV.star_dotProduct_mulVec_eq hM, Complex.norm_real, Real.norm_eq_abs,
    ← Cvs.Zeta.Base.MV.sum_norm_sq_unitary hM y, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right (abs_eigenvalue_le_pi hD hgap i) (sq_nonneg _)

/-- **Hilbert's inequality, real bilinear, constant `π`**: for real `x, z` and `s > 0`,
`|Σ_{r≠t} x_r z_t/(λ_r − λ_t)| ≤ (π/2)(s² Σ x_r² + Σ z_r²/s²)/D`. -/
theorem hilbert_real_bilinear (hD : 0 < D) (hgap : ∀ r s, r ≠ s → D ≤ |freq r - freq s|) (x z : ι → ℝ)
    {s : ℝ} (hs : 0 < s) :
    |∑ r, ∑ t, (if r = t then 0 else x r * z t / (freq r - freq t))|
      ≤ π / 2 * (s ^ 2 * ∑ r, x r ^ 2 + (∑ r, z r ^ 2) / s ^ 2) / D := by
  set y : ι → ℂ := fun r => ((s * x r : ℝ) : ℂ) + ((z r / s : ℝ) : ℂ) * I with hy
  have hmv := hilbert_diag hD hgap y
  set B : ℝ := ∑ r, ∑ t, (if r = t then 0 else x r * z t / (freq r - freq t)) with hB
  have hBc : ((B : ℝ) : ℂ) = ∑ r, ∑ t, ((x r : ℂ) * (z t : ℂ)) * Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T freq r t := by
    rw [hB]; push_cast; apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro t _
    unfold Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T; split_ifs
    · simp
    · rw [mul_one_div]; push_cast; ring
  have hsum : (∑ r, ∑ t, if r = t then (0 : ℂ) else y r * conj (y t) / ((freq r - freq t : ℝ) : ℂ))
      = -2 * I * ((B : ℝ) : ℂ) := by
    have e1 : ∀ r t, (if r = t then (0 : ℂ) else y r * conj (y t) / ((freq r - freq t : ℝ) : ℂ))
        = ((s : ℂ) ^ 2 * ((x r : ℂ) * (x t : ℂ)) + ((z r : ℂ) * (z t : ℂ)) / (s : ℂ) ^ 2)
            * Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T freq r t
          + I * (((z r : ℂ) * (x t : ℂ)) * Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T freq r t
            - ((x r : ℂ) * (z t : ℂ)) * Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T freq r t) := by
      intro r t
      have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      unfold Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T; split_ifs with h
      · simp
      · simp only [hy, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
        push_cast
        field_simp
        ring_nf
        rw [Complex.I_sq]; ring
    simp_rw [e1]
    rw [Finset.sum_congr rfl fun r _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hsym := Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.sum_sym_T freq
      (fun r t => (s : ℂ) ^ 2 * ((x r : ℂ) * (x t : ℂ)) + ((z r : ℂ) * (z t : ℂ)) / (s : ℂ) ^ 2)
      (fun r t => by ring)
    have hswap : ∑ r, ∑ t, ((z r : ℂ) * (x t : ℂ)) * Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T freq r t
        = -∑ r, ∑ t, ((x r : ℂ) * (z t : ℂ)) * Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T freq r t := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro r _
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro t _
      rw [Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T_swap]; ring
    rw [hsym, zero_add]
    have e2 : ∑ r, ∑ t, I * (((z r : ℂ) * (x t : ℂ)) * Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T freq r t
          - ((x r : ℂ) * (z t : ℂ)) * Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T freq r t)
        = I * (∑ r, ∑ t, ((z r : ℂ) * (x t : ℂ)) * Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T freq r t
          - ∑ r, ∑ t, ((x r : ℂ) * (z t : ℂ)) * Cvs.Upstream.MontgomeryVaughanRealAntisymmetric.T freq r t) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [e2, hswap, hBc]; ring
  have hnorm : ∀ r, ‖y r‖ ^ 2 = (s * x r) ^ 2 + (z r / s) ^ 2 := fun r => by
    rw [Complex.sq_norm, hy]; simp only; rw [Complex.normSq_add_mul_I]
  rw [hsum] at hmv
  have hl : ‖-2 * I * ((B : ℝ) : ℂ)‖ = 2 * |B| := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]; norm_num
  rw [hl] at hmv
  have e : ∑ r, ‖y r‖ ^ 2 / D = (s ^ 2 * ∑ r, x r ^ 2 + (∑ r, z r ^ 2) / s ^ 2) / D := by
    simp_rw [hnorm]
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _; field_simp
  have hr : π * ∑ r, ‖y r‖ ^ 2 / D = 2 * (π / 2 * (s ^ 2 * ∑ r, x r ^ 2 + (∑ r, z r ^ 2) / s ^ 2) / D) := by
    rw [e]; ring
  rw [hr] at hmv
  linarith

end Cvs.Upstream.HilbertInequalityUniformGap
