import Mathlib
import Cvs.Finite.CosineModeTransformBounds
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.ModeTransformEnvelopes
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The division polynomial of an odd vector

`vecOf p = ω ⊙ xOf p` with `xOf p = (w_i p(ω_i²))`, `w = 1` at mode `0` and `(−1)^K e_K` at `±K`. For
`deg p < N`: `xdiv (vecOf p) = xOf p`, `ω·vecOf p ∝ p_{N−1}`, every odd vector is some `vecOf p`, the
window transform of `xOf p` vanishes where `p(t²)` does, and `W²` acts as multiplication by `X`.
-/

noncomputable section

open Matrix Real Polynomial

namespace Cvs.Finite.OddDisplacementPencil
open Cvs.ZeroCounting
open Cvs.Finite.SymmetricModeSet (Idx mode negI negI_involutive mode_negI mode_injective)
open Cvs.Finite.OddEigenvectorResolvent (xdiv om om_none)

variable {L : ℝ} {N : ℕ}

/-! ### The dictionary -/

/-- The lattice frequency `ν_K = 2πK/L`. -/
def nu (L : ℝ) (K : ℕ) : ℝ := 2 * π * K / L

/-- The binomial weight `e_K = C(2N, N+K)/C(2N, N)`. -/
def eCoef (N K : ℕ) : ℝ := (Nat.choose (2 * N) (N + K) : ℝ) / (Nat.choose (2 * N) N : ℝ)

/-- The signed weight of an index: `1` at the zero mode and `(−1)^K e_K` at the modes `±K`. -/
def wt (N : ℕ) : Idx N → ℝ
  | none => 1
  | some (k, _) => (-1) ^ ((k : ℕ) + 1) * eCoef N ((k : ℕ) + 1)

/-- The even vector of a polynomial: `x_i = w_i p(ω_i²)`. -/
def xOf (L : ℝ) (N : ℕ) (p : ℝ[X]) : Idx N → ℝ := fun i => wt N i * p.eval (om L N i ^ 2)

/-- The odd vector of a polynomial: `ω_i x_i`. -/
def vecOf (L : ℝ) (N : ℕ) : ℝ[X] →ₗ[ℝ] (Idx N → ℝ) where
  toFun p i := om L N i * xOf L N p i
  map_add' p q := by funext i; simp only [xOf, eval_add, Pi.add_apply]; ring
  map_smul' c p := by
    funext i; simp only [xOf, eval_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]; ring

theorem vecOf_apply (p : ℝ[X]) (i : Idx N) : vecOf L N p i = om L N i * xOf L N p i := rfl

theorem om_negI (i : Idx N) : om L N (negI N i) = -om L N i :=
  Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg (mode_negI N) i

theorem om_some (k : Fin N) (b : Bool) :
    om L N (some (k, b)) = (if b then 1 else -1) * nu L ((k : ℕ) + 1) := by
  cases b
  · simp [om, Cvs.Finite.TruncationZeroFreeOffAxes.omega, mode, nu]; ring
  · simp [om, Cvs.Finite.TruncationZeroFreeOffAxes.omega, mode, nu]

theorem om_sq_some (k : Fin N) (b : Bool) : om L N (some (k, b)) ^ 2 = nu L ((k : ℕ) + 1) ^ 2 := by
  rw [om_some]; cases b <;> simp

theorem wt_negI (i : Idx N) : wt N (negI N i) = wt N i := by
  rcases i with _ | ⟨k, b⟩ <;> rfl

theorem wt_sq_some (k : Fin N) (b : Bool) : wt N (some (k, b)) ^ 2 = eCoef N ((k : ℕ) + 1) ^ 2 := by
  simp only [wt, mul_pow]
  rw [← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow, one_mul]

theorem xOf_negI (p : ℝ[X]) (i : Idx N) : xOf L N p (negI N i) = xOf L N p i := by
  simp only [xOf, wt_negI, om_negI, neg_sq]

theorem vecOf_negI (p : ℝ[X]) (i : Idx N) : vecOf L N p (negI N i) = -vecOf L N p i := by
  simp only [vecOf_apply, om_negI, xOf_negI, neg_mul]

/-- `W²` acts on odd vectors of polynomials as multiplication by `X`. -/
theorem vecOf_X_mul (p : ℝ[X]) : vecOf L N (X * p) = fun i => om L N i ^ 2 * vecOf L N p i := by
  funext i; simp only [vecOf_apply, xOf, eval_mul, eval_X]; ring

/-! ### The alternating binomial sum -/

/-- The `n`-th forward difference of a polynomial of degree at most `n` is `n!` times its `n`-th
coefficient. -/
private theorem fwdDiff_iter_eval_eq {P : ℝ[X]} {n : ℕ} (hP : P.natDegree ≤ n) (y : ℝ) :
    (fwdDiff (1 : ℝ))^[n] P.eval y = P.coeff n * (n.factorial : ℝ) := by
  rcases hP.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [Polynomial.fwdDiff_iter_degree_eq_factorial, Pi.smul_apply, smul_eq_mul, Pi.natCast_apply]
    rfl

/-- A sum over `Idx N` splits into the zero mode and the pairs `±K`. -/
private theorem sum_idx' (f : Idx N → ℝ) :
    ∑ i, f i = f none + ∑ k : Fin N, (f (some (k, true)) + f (some (k, false))) := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]

/-- A sum over `j ≤ 2N` splits into the centre `j = N` and the pairs `N ± (k + 1)`. -/
private theorem sum_range_two_mul_add_one (N : ℕ) (h : ℕ → ℝ) :
    ∑ j ∈ Finset.range (2 * N + 1), h j
      = h N + ∑ k : Fin N, (h (N + ((k : ℕ) + 1)) + h (N - ((k : ℕ) + 1))) := by
  rw [show 2 * N + 1 = N + (N + 1) by ring, Finset.sum_range_add, Finset.sum_range_succ',
    Fin.sum_univ_eq_sum_range (fun k => h (N + (k + 1)) + h (N - (k + 1))) N,
    Finset.sum_add_distrib, ← Finset.sum_range_reflect h N]
  have : ∀ j ∈ Finset.range N, h (N - 1 - j) = h (N - (j + 1)) := fun j _ => by
    congr 1; omega
  rw [Finset.sum_congr rfl this, add_zero]
  ring

/-- `∑_{j ≤ 2N} (−1)^{2N−j} C(2N, j) ((j − N)²)^m` is `(2N)!` at `m = N` and `0` for `m < N`. -/
private theorem alt_choose_sum (N m : ℕ) (hm : m ≤ N) :
    ∑ j ∈ Finset.range (2 * N + 1), (-1 : ℝ) ^ (2 * N - j) * ((2 * N).choose j : ℝ)
      * (((j : ℝ) - N) ^ 2) ^ m = if m = N then ((2 * N).factorial : ℝ) else 0 := by
  have hdeg : ((X - C (N : ℝ)) ^ (2 * m)).natDegree ≤ 2 * N := by
    rw [natDegree_pow, natDegree_X_sub_C]; omega
  have h1 := fwdDiff_iter_eq_sum_shift (1 : ℝ) (((X - C (N : ℝ)) ^ (2 * m)).eval) (2 * N) 0
  rw [fwdDiff_iter_eval_eq hdeg] at h1
  have hc : ((X - C (N : ℝ)) ^ (2 * m)).coeff (2 * N) = if m = N then 1 else 0 := by
    split_ifs with h
    · rw [h]
      have := ((monic_X_sub_C (N : ℝ)).pow (2 * N)).coeff_natDegree
      rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at this
    · exact coeff_eq_zero_of_natDegree_lt (by rw [natDegree_pow, natDegree_X_sub_C]; omega)
  rw [hc] at h1
  have h2 : ∀ j ∈ Finset.range (2 * N + 1), ((-1 : ℤ) ^ (2 * N - j) * ((2 * N).choose j : ℤ)) •
      ((X - C (N : ℝ)) ^ (2 * m)).eval (0 + j • (1 : ℝ))
      = (-1 : ℝ) ^ (2 * N - j) * ((2 * N).choose j : ℝ) * (((j : ℝ) - N) ^ 2) ^ m := by
    intro j _
    rw [zsmul_eq_mul, nsmul_eq_mul, eval_pow, eval_sub, eval_X, eval_C, ← pow_mul]
    push_cast; ring
  rw [Finset.sum_congr rfl h2] at h1
  rw [← h1]; split_ifs <;> simp

/-- The signed weights against even powers of the modes: `∑_i w_i (mode_i²)^m` is
`(−1)^N (N!)²` at `m = N` and `0` for `m < N`. -/
private theorem sum_wt_mode_pow (N m : ℕ) (hm : m ≤ N) :
    ∑ i : Idx N, wt N i * ((mode N i : ℝ) ^ 2) ^ m
      = if m = N then (-1) ^ N * (N.factorial : ℝ) ^ 2 else 0 := by
  have hC : (0 : ℝ) < (2 * N).choose N := by exact_mod_cast Nat.choose_pos (by omega)
  have key : (-1) ^ N * ((2 * N).choose N : ℝ) * ∑ i : Idx N, wt N i * ((mode N i : ℝ) ^ 2) ^ m
      = if m = N then ((2 * N).factorial : ℝ) else 0 := by
    rw [← alt_choose_sum N m hm, sum_range_two_mul_add_one, sum_idx', mul_add, Finset.mul_sum]
    congr 1
    · simp [wt, mode, show 2 * N - N = N by omega]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (k : ℕ) + 1 ≤ N := k.isLt
      have e1 : 2 * N - (N + ((k : ℕ) + 1)) = N - ((k : ℕ) + 1) := by omega
      have e2 : 2 * N - (N - ((k : ℕ) + 1)) = N - ((k : ℕ) + 1) + 2 * ((k : ℕ) + 1) := by omega
      have hch : (2 * N).choose (N - ((k : ℕ) + 1)) = (2 * N).choose (N + ((k : ℕ) + 1)) :=
        Nat.choose_symm_of_eq_add (by omega)
      have he : eCoef N ((k : ℕ) + 1) * ((2 * N).choose N : ℝ)
          = (2 * N).choose (N + ((k : ℕ) + 1)) := by
        unfold eCoef; field_simp
      have hpow : (-1 : ℝ) ^ N = (-1) ^ (N - ((k : ℕ) + 1)) * (-1) ^ ((k : ℕ) + 1) := by
        rw [← pow_add]; congr 1; omega
      have hsq : ((-1 : ℝ) ^ ((k : ℕ) + 1)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
      rw [e1, e2, hch, Nat.cast_sub hk, pow_add, pow_mul, neg_one_sq, one_pow, mul_one, hpow]
      simp only [wt, mode, if_true, Bool.false_eq_true, if_false]
      push_cast
      have hm1 : (((N : ℝ) + ((k : ℝ) + 1) - N) ^ 2) ^ m = (((k : ℝ) + 1) ^ 2) ^ m := by ring_nf
      have hm2 : (((N : ℝ) - ((k : ℝ) + 1) - N) ^ 2) ^ m = (((k : ℝ) + 1) ^ 2) ^ m := by ring_nf
      have hm3 : ((-((k : ℝ) + 1)) ^ 2) ^ m = (((k : ℝ) + 1) ^ 2) ^ m := by rw [neg_sq]
      rw [hm1, hm2, hm3, ← he]
      linear_combination (2 * (-1) ^ (N - ((k : ℕ) + 1)) * eCoef N ((k : ℕ) + 1)
        * ((2 * N).choose N : ℝ) * (((k : ℝ) + 1) ^ 2) ^ m) * hsq
  have hfact : ((2 * N).factorial : ℝ) = (2 * N).choose N * (N.factorial : ℝ) ^ 2 := by
    rw [two_mul]; exact_mod_cast (by rw [← Nat.add_choose_mul_factorial_mul_factorial N N]; ring)
  have hs : ((-1 : ℝ) ^ N) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  split_ifs at key ⊢ with h
  · apply mul_left_cancel₀ hC.ne'
    rw [hfact] at key
    linear_combination (-1 : ℝ) ^ N * key
      - ((2 * N).choose N : ℝ) * (∑ i : Idx N, wt N i * ((mode N i : ℝ) ^ 2) ^ m) * hs
  · have h0 : (-1 : ℝ) ^ N * ((2 * N).choose N : ℝ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) hC.ne'
    exact (mul_eq_zero.mp key).resolve_left h0

/-- **The signed weights read off the `N`-th coefficient**: for `natDegree q ≤ N`,
`∑_i w_i q(ω_i²) = (−1)^N (N!)² (2π/L)^{2N} q_N`. -/
private theorem sum_wt_eval (L : ℝ) {q : ℝ[X]} (hq : q.natDegree ≤ N) :
    ∑ i : Idx N, wt N i * q.eval (om L N i ^ 2)
      = (-1) ^ N * (N.factorial : ℝ) ^ 2 * (2 * π / L) ^ (2 * N) * q.coeff N := by
  have hom : ∀ i, om L N i ^ 2 = (2 * π / L) ^ 2 * (mode N i : ℝ) ^ 2 := fun i => by
    simp only [om, Cvs.Finite.TruncationZeroFreeOffAxes.omega]; ring
  have hexp : ∀ i, wt N i * q.eval (om L N i ^ 2) = ∑ m ∈ Finset.range (N + 1),
      q.coeff m * ((2 * π / L) ^ 2) ^ m * (wt N i * ((mode N i : ℝ) ^ 2) ^ m) := fun i => by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hq), hom, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun m hm => by
    rw [sum_wt_mode_pow N m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self, if_true]
  rw [← pow_mul]; ring

/-- An off-zero frequency is nonzero when `L ≠ 0`. -/
private theorem om_some_ne' (hL : L ≠ 0) (j : Fin N × Bool) : om L N (some j) ≠ 0 := by
  obtain ⟨k, b⟩ := j
  rw [om_some]
  refine mul_ne_zero (by cases b <;> norm_num) (div_ne_zero ?_ hL)
  have : ((((k : ℕ) + 1 : ℕ)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  positivity

/-! ### The polynomial picture -/

-- f52 polynomial picture: `x₀ = p(0)` (alternating binomial sum)
/-- **The division vector of `vecOf p` is `xOf p`** for `deg p < N`: off the zero mode by
definition, at the zero mode `−∑_{K ≠ 0} (−1)^K e_K p(ω_K²) = p(0)`. -/
theorem xdiv_vecOf (hL : L ≠ 0) {p : ℝ[X]} (hp : p.degree < N) : xdiv L N (vecOf L N p) = xOf L N p := by
  have hdiv : ∀ j, vecOf L N p (some j) / om L N (some j) = xOf L N p (some j) := fun j => by
    rw [vecOf_apply]; exact mul_div_cancel_left₀ _ (om_some_ne' hL j)
  funext i
  rcases i with _ | j
  · have hsum := sum_wt_eval L (q := p) (natDegree_le_iff_degree_le.mpr hp.le)
    rw [coeff_eq_zero_of_degree_lt hp, mul_zero, Fintype.sum_option] at hsum
    simp only [xdiv, hdiv]
    simp only [xOf] at hsum ⊢
    linarith
  · simp only [xdiv, hdiv]

-- f52 polynomial picture: `η·s ∝` the leading coefficient
/-- **`ω·vecOf p` is the top coefficient**: for `deg p < N`,
`ω·vecOf p = (−1)^N (N!)² (2π/L)^{2N} p_{N−1}`. -/
theorem om_dotProduct_vecOf {p : ℝ[X]} (hp : p.degree < N) :
    om L N ⬝ᵥ vecOf L N p
      = (-1) ^ N * (N.factorial : ℝ) ^ 2 * (2 * π / L) ^ (2 * N) * p.coeff (N - 1) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hp0 : p = 0 := by
      rw [← Polynomial.degree_eq_bot]
      exact (WithBot.lt_coe_bot).mp (by simpa using hp)
    subst hp0
    simp [dotProduct, vecOf_apply, xOf]
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hpn : p.natDegree ≤ n := by
      by_cases hp0 : p = 0
      · simp [hp0]
      · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hp0).mpr hp)
    have hdeg : (X * p).natDegree ≤ n + 1 := by
      refine (natDegree_mul_le).trans ?_
      rw [natDegree_X]; omega
    have h := sum_wt_eval L hdeg
    rw [coeff_X_mul] at h
    rw [Nat.add_sub_cancel, ← h]
    simp only [dotProduct, vecOf_apply, xOf, eval_mul, eval_X]
    exact Finset.sum_congr rfl fun i _ => by ring

-- f52 polynomial picture: odd vectors are `vecOf` of polynomials of degree `< N`
/-- **Every odd vector is `vecOf p` with `deg p < N`** (Lagrange interpolation at the nodes `ω_K²`). -/
theorem exists_vecOf_eq (hL : L ≠ 0) {v : Idx N → ℝ} (hv : ∀ i, v (negI N i) = -v i) :
    ∃ p : ℝ[X], p.degree < N ∧ vecOf L N p = v := by
  classical
  have hnu : ∀ k : Fin N, nu L ((k : ℕ) + 1) ≠ 0 := fun k => by
    have : ((((k : ℕ) + 1 : ℕ)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    exact div_ne_zero (by positivity) hL
  have hwt : ∀ k : Fin N, wt N (some (k, true)) ≠ 0 := fun k => by
    have h1 : (0 : ℝ) < (2 * N).choose (N + ((k : ℕ) + 1)) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have h2 : (0 : ℝ) < (2 * N).choose N := by exact_mod_cast Nat.choose_pos (by omega)
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (div_pos h1 h2).ne'
  set node : Fin N → ℝ := fun k => nu L ((k : ℕ) + 1) ^ 2 with hnode
  have hinj : Set.InjOn node (Finset.univ : Finset (Fin N)) := by
    intro k _ k' _ h
    have ha : (2 * π / L) ^ 2 ≠ 0 := pow_ne_zero _ (div_ne_zero (by positivity) hL)
    have h' : (2 * π / L) ^ 2 * ((k : ℝ) + 1) ^ 2 = (2 * π / L) ^ 2 * ((k' : ℝ) + 1) ^ 2 := by
      have := h; simp only [hnode, nu] at this; push_cast at this; linear_combination this
    have h'' := (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp
      (mul_left_cancel₀ ha h')
    exact Fin.ext (by exact_mod_cast (add_left_inj 1).mp h'')
  set r : Fin N → ℝ := fun k => v (some (k, true)) / (nu L ((k : ℕ) + 1) * wt N (some (k, true)))
    with hr
  refine ⟨Lagrange.interpolate Finset.univ node r, ?_, ?_⟩
  · simpa using Lagrange.degree_interpolate_lt r hinj
  · funext i
    rcases i with _ | ⟨k, b⟩
    · rw [vecOf_apply, om_none, zero_mul]
      have := hv none
      simp only [negI] at this
      linarith
    · have hev :
          (Lagrange.interpolate Finset.univ node r).eval (om L N (some (k, b)) ^ 2) = r k := by
        rw [om_sq_some]; exact Lagrange.eval_interpolate_at_node r hinj (Finset.mem_univ k)
      rw [vecOf_apply, xOf, hev, om_some]
      have hw : wt N (some (k, b)) = wt N (some (k, true)) := by cases b <;> rfl
      rw [hw, hr]
      cases b
      · have := hv (some (k, true))
        simp only [negI, Bool.not_true] at this
        rw [this]
        simp only [Bool.false_eq_true, if_false]
        field_simp [hnu k, hwt k]
      · simp only [if_true]
        field_simp [hnu k, hwt k]

-- H_fix Step 2 (`X_g(t) = p_g(t²) E_N(t)` off the lattice: partial fractions)
/-- **The rational factor of `xOf p` is `p(t²)` over the nodal product**: for `deg p ≤ N` and
`t² ≠ ω_i²`, `∑_i x_i/(ω_i² − t²) = (N!)² (2π/L)^{2N} p(t²) / (−t² ∏_K (ν_K² − t²))`. -/
theorem sum_xOf_div_eq {p : ℝ[X]} (hp : p.degree ≤ N) {t : ℝ}
    (ht : ∀ i : Idx N, om L N i ^ 2 ≠ t ^ 2) :
    ∑ i : Idx N, xOf L N p i / (om L N i ^ 2 - t ^ 2)
      = (N.factorial : ℝ) ^ 2 * (2 * π / L) ^ (2 * N) * p.eval (t ^ 2)
        / (-t ^ 2 * ∏ k : Fin N, (nu L ((k : ℕ) + 1) ^ 2 - t ^ 2)) := by
  set s := t ^ 2 with hs
  have hmon : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      (X - C (nu L ((k : ℕ) + 1) ^ 2) : ℝ[X]).Monic := fun k _ => monic_X_sub_C _
  set D : ℝ[X] := X * ∏ k : Fin N, (X - C (nu L ((k : ℕ) + 1) ^ 2)) with hD
  have hDmon : D.Monic := monic_X.mul (monic_prod_of_monic _ _ hmon)
  have hDdeg : D.natDegree = N + 1 := by
    rw [hD, monic_X.natDegree_mul (monic_prod_of_monic _ _ hmon), natDegree_prod_of_monic _ _ hmon]
    simp only [natDegree_X, natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
    ring
  have hDnode : ∀ i : Idx N, D.eval (om L N i ^ 2) = 0 := by
    rintro (_ | ⟨k, b⟩)
    · simp [hD, om_none]
    · rw [om_sq_some]
      simp only [hD, eval_mul, eval_X, eval_prod, eval_sub, eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _), mul_zero]
  have hDs : D.eval s = s * ∏ k : Fin N, (s - nu L ((k : ℕ) + 1) ^ 2) := by
    simp [hD, eval_prod]
  have hs0 : s ≠ 0 := by
    have := ht none
    rw [om_none] at this
    exact fun h => this (by rw [h]; ring)
  have hsk : ∀ k : Fin N, s - nu L ((k : ℕ) + 1) ^ 2 ≠ 0 := fun k h =>
    ht (some (k, true)) (by rw [om_sq_some]; linarith)
  have hDs0 : D.eval s ≠ 0 := by
    rw [hDs]; exact mul_ne_zero hs0 (Finset.prod_ne_zero_iff.mpr fun k _ => hsk k)
  set F : ℝ[X] := C (D.eval s) * p - C (p.eval s) * D with hF
  have hFroot : F.IsRoot s := by simp only [IsRoot, hF, eval_sub, eval_mul, eval_C]; ring
  set G := F /ₘ (X - C s) with hG
  have hFG : (X - C s) * G = F := mul_divByMonic_eq_iff_isRoot.mpr hFroot
  have hpdeg : p.natDegree ≤ N := natDegree_le_iff_degree_le.mpr hp
  have hFdeg : F.natDegree ≤ N + 1 := by
    rw [hF]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans (hpdeg.trans (Nat.le_succ N))
    · exact (natDegree_C_mul_le _ _).trans hDdeg.le
  have hGdeg : G.natDegree ≤ N := by
    rw [hG, natDegree_divByMonic _ (monic_X_sub_C s), natDegree_X_sub_C]; omega
  have hGN : G.coeff N = -p.eval s := by
    have h : ((X - C s) * G).coeff (N + 1) = F.coeff (N + 1) := by rw [hFG]
    rw [coeff_X_sub_C_mul, coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < N + 1),
      mul_zero, sub_zero] at h
    rw [h, hF, coeff_sub, coeff_C_mul, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < N + 1), ← hDdeg,
      hDmon.coeff_natDegree]
    ring
  have hterm : ∀ i : Idx N, xOf L N p i / (om L N i ^ 2 - s)
      = wt N i * G.eval (om L N i ^ 2) / D.eval s := by
    intro i
    have hu : om L N i ^ 2 - s ≠ 0 := sub_ne_zero.mpr (ht i)
    have h := congrArg (eval (om L N i ^ 2)) hFG
    simp only [eval_mul, eval_sub, eval_X, eval_C, hF, hDnode i, mul_zero, sub_zero] at h
    unfold xOf
    rw [div_eq_div_iff hu hDs0]
    linear_combination (-wt N i) * h
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_div, sum_wt_eval L hGdeg, hGN, hDs]
  have hprod : ∏ k : Fin N, (nu L ((k : ℕ) + 1) ^ 2 - s)
      = (-1) ^ N * ∏ k : Fin N, (s - nu L ((k : ℕ) + 1) ^ 2) := by
    rw [show ((-1 : ℝ) ^ N) = (-1) ^ (Finset.univ : Finset (Fin N)).card by
      rw [Finset.card_fin], ← Finset.prod_neg]
    exact Finset.prod_congr rfl fun k _ => by ring
  have hP0 : ∏ k : Fin N, (s - nu L ((k : ℕ) + 1) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => hsk k
  have hsq : ((-1 : ℝ) ^ N) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [hprod, div_eq_div_iff (mul_ne_zero hs0 hP0)
    (mul_ne_zero (neg_ne_zero.mpr hs0) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hP0))]
  linear_combination ((N.factorial : ℝ) ^ 2 * (2 * π / L) ^ (2 * N) * p.eval s * s
    * ∏ k : Fin N, (s - nu L ((k : ℕ) + 1) ^ 2)) * hsq

/-- `∫_0^L e^{2πiks/L} ds` is `L` at `k = 0` and `0` at every other integer `k`. -/
private theorem integral_exp_lattice (L : ℝ) (k : ℤ) :
    ∫ s in (0 : ℝ)..L, Complex.exp (((2 * π * k / L : ℝ) : ℂ) * Complex.I * s)
      = if k = 0 then (L : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp
  · by_cases hL : L = 0
    · subst hL; simp
    · have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
      have hc : ((2 * π * k / L : ℝ) : ℂ) * Complex.I ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) hL)) Complex.I_ne_zero
      rw [integral_exp_mul_complex hc]
      have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
      have : ((2 * π * k / L : ℝ) : ℂ) * Complex.I * (L : ℂ) = (k : ℂ) * (2 * π * Complex.I) := by
        push_cast; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
        sub_self, zero_div]

/-- The mode transform at a lattice frequency: `W_m(2πn/L) = (L/2)([m = n] + [m = −n])`. -/
private theorem Wm_lattice (L : ℝ) (m n : ℤ) :
    Cvs.Finite.ModeTransformEnvelopes.Wm L m ((2 * π * n / L : ℝ) : ℂ)
      = (if m - n = 0 then (L : ℂ) else 0) / 2 + (if -m - n = 0 then (L : ℂ) else 0) / 2 := by
  unfold Cvs.Finite.ModeTransformEnvelopes.Wm Cvs.Detection.windowTransform Cvs.WeilForm.SelfConvolutionTransform.cf
  have hpt : ∀ s : ℝ, Complex.exp (-((s : ℂ) * ((2 * π * n / L : ℝ) : ℂ)) * Complex.I)
        * ((Real.cos (2 * π * m / L * s) : ℝ) : ℂ)
      = Complex.exp (((2 * π * ((m - n : ℤ) : ℝ) / L : ℝ) : ℂ) * Complex.I * s) / 2
        + Complex.exp (((2 * π * ((-m - n : ℤ) : ℝ) / L : ℝ) : ℂ) * Complex.I * s) / 2 := by
    intro s
    rw [Complex.ofReal_cos, Complex.cos, mul_div_assoc', mul_add, ← Complex.exp_add,
      ← Complex.exp_add, add_div]
    congr 2 <;> congr 1 <;> push_cast <;> ring
  simp_rw [hpt]
  have hint : ∀ k : ℤ, IntervalIntegrable
      (fun s : ℝ => Complex.exp (((2 * π * (k : ℝ) / L : ℝ) : ℂ) * Complex.I * s) / 2)
      MeasureTheory.volume 0 L := fun k =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_add (hint _) (hint _), intervalIntegral.integral_div,
    intervalIntegral.integral_div, integral_exp_lattice, integral_exp_lattice]

-- H_fix Step 2 (`X_g(ω_K) = L x_K` on the lattice: orthogonality of the modes)
/-- **The window transform of an even cosine polynomial at a mode frequency** is `L` times the
coefficient: `Ŵ_x(ω_i) = L x_i`. -/
theorem windowTransform_cosPoly_om {x : Idx N → ℝ} (hx : ∀ i, x (negI N i) = x i) (i : Idx N) :
    Cvs.Detection.windowTransform L
      (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) x)) (om L N i : ℂ)
      = (L : ℂ) * x i := by
  unfold Cvs.Finite.EvenSectorZeroSide.cosPoly
  rw [Cvs.Finite.CosineModeTransformBounds.windowTransform_sum_cf L x
    (fun j y => Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) j * y)) (fun j => by fun_prop)]
  change ∑ j, (x j : ℂ) * Cvs.Finite.ModeTransformEnvelopes.Wm L (mode N j)
    ((2 * π * (mode N i : ℤ) / L : ℝ) : ℂ) = _
  have h1 : ∀ j, (mode N j - mode N i = 0 ↔ j = i) := fun j => by
    rw [sub_eq_zero]; exact (mode_injective N).eq_iff
  have h2 : ∀ j, (-mode N j - mode N i = 0 ↔ j = negI N i) := fun j => by
    rw [← (mode_injective N).eq_iff, mode_negI]; omega
  simp only [Wm_lattice, h1, h2, ite_div, zero_div, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hx]
  ring

/-- **The window transform of `xOf p` vanishes at the roots of `p(t²)`**: for `deg p < N` and real
`t` with `p(t²) = 0`, `Ŵ_{xOf p}(t) = 0`. -/
theorem windowTransform_xOf_eq_zero (hL : 0 < L) {p : ℝ[X]} (hp : p.degree < N) {t : ℝ}
    (ht : p.eval (t ^ 2) = 0) :
    Cvs.Detection.windowTransform L
      (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xOf L N p))) (t : ℂ) = 0 := by
  by_cases hlat : ∃ i : Idx N, om L N i ^ 2 = t ^ 2
  · obtain ⟨i, hi⟩ := hlat
    obtain ⟨j, hj⟩ : ∃ j : Idx N, om L N j = t := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hi with h | h
      · exact ⟨i, h⟩
      · exact ⟨negI N i, by rw [om_negI, h, neg_neg]⟩
    subst hj
    rw [windowTransform_cosPoly_om (xOf_negI p) j]
    simp [xOf, ht]
  · push Not at hlat
    have hgen : ∀ k : Idx N, ((2 * π * mode N k / L : ℝ) : ℂ) ^ 2 - (t : ℂ) ^ 2 ≠ 0 := fun k h => by
      apply hlat k
      have h' : ((om L N k ^ 2 - t ^ 2 : ℝ) : ℂ) = 0 := by
        rw [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_pow]; exact h
      have h'' := Complex.ofReal_eq_zero.mp h'
      linarith
    rw [Cvs.Finite.UniversalFunctionPairing.transform_cosPoly_eq hL (mode N) (xOf L N p) hgen]
    have hS : Cvs.Finite.UniversalFunctionPairing.S L (mode N) (xOf L N p) (t : ℂ) = 0 := by
      have hr := sum_xOf_div_eq hp.le hlat
      rw [ht, mul_zero, zero_div] at hr
      unfold Cvs.Finite.UniversalFunctionPairing.S
      have hc : ∑ k : Idx N, (xOf L N p k : ℂ) / (((2 * π * mode N k / L : ℝ) : ℂ) ^ 2 - (t : ℂ) ^ 2)
          = ((∑ i : Idx N, xOf L N p i / (om L N i ^ 2 - t ^ 2) : ℝ) : ℂ) := by
        simp only [om, Cvs.Finite.TruncationZeroFreeOffAxes.omega]
        push_cast
        rfl
      rw [hc, hr, Complex.ofReal_zero]
    rw [hS, mul_zero]

/-! ### Consequences -/

/-- A polynomial of degree `< N − 1` has `ω·vecOf p = 0`. -/
theorem om_dotProduct_vecOf_eq_zero {p : ℝ[X]} (hp : p.degree < (N - 1 : ℕ)) :
    om L N ⬝ᵥ vecOf L N p = 0 := by
  have hpN : p.degree < N := lt_of_lt_of_le hp (by exact_mod_cast Nat.sub_le N 1)
  rw [om_dotProduct_vecOf hpN, Polynomial.coeff_eq_zero_of_degree_lt hp, mul_zero]

/-- A polynomial of degree `< N` with `ω·vecOf p = 0` has degree `< N − 1`. -/
theorem degree_lt_pred_of_om_dotProduct (hL : L ≠ 0) {p : ℝ[X]} (hp : p.degree < N)
    (h : om L N ⬝ᵥ vecOf L N p = 0) : p.degree < (N - 1 : ℕ) := by
  rw [om_dotProduct_vecOf hp] at h
  have hc : p.coeff (N - 1) = 0 := by
    have h2 : (2 * π / L) ≠ 0 := div_ne_zero (by positivity) hL
    have hf : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
    rcases mul_eq_zero.mp h with h' | h'
    · exfalso
      rcases mul_eq_zero.mp h' with h'' | h''
      · rcases mul_eq_zero.mp h'' with h3 | h3
        · exact pow_ne_zero _ (by norm_num) h3
        · exact pow_ne_zero _ hf h3
      · exact pow_ne_zero _ h2 h''
    · exact h'
  rw [Polynomial.degree_lt_iff_coeff_zero] at hp ⊢
  intro m hm
  rcases Nat.lt_or_ge m N with hmN | hmN
  · have : m = N - 1 := by omega
    rw [this]; exact hc
  · exact hp m hmN

/-- A polynomial of degree `< N` with `ω·vecOf p ≠ 0` has degree `N − 1`. -/
theorem degree_eq_pred_of_om_dotProduct_ne {p : ℝ[X]} (hp : p.degree < N)
    (h : om L N ⬝ᵥ vecOf L N p ≠ 0) : p.degree = (N - 1 : ℕ) := by
  rw [om_dotProduct_vecOf hp] at h
  have hc : p.coeff (N - 1) ≠ 0 := fun hc => h (by rw [hc, mul_zero])
  have hp0 : p ≠ 0 := fun h0 => hc (by rw [h0, coeff_zero])
  have hle : N - 1 ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hc
  have hlt : p.natDegree < N := by
    rwa [Polynomial.degree_eq_natDegree hp0, Nat.cast_lt] at hp
  rw [Polynomial.degree_eq_natDegree hp0]
  congr 1
  omega

/-! ### Norms on the lattice -/

/-- A sum over `Idx N` splits into the zero mode and the pairs `±K`. -/
theorem sum_idx (f : Idx N → ℝ) :
    ∑ i, f i = f none + ∑ k : Fin N, (f (some (k, true)) + f (some (k, false))) := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]

/-- `|vecOf p|² = 2 ∑_K ν_K² p(ν_K²)² e_K²`. -/
theorem dot_vecOf_self (p : ℝ[X]) :
    vecOf L N p ⬝ᵥ vecOf L N p = 2 * ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 2
      * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 := by
  simp only [dotProduct]
  rw [sum_idx, Finset.mul_sum]
  simp only [vecOf_apply, xOf, om_none, zero_mul, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  have w1 := wt_sq_some (N := N) k true
  have w2 := wt_sq_some (N := N) k false
  calc om L N (some (k, true)) * (wt N (some (k, true)) * eval (om L N (some (k, true)) ^ 2) p)
        * (om L N (some (k, true)) * (wt N (some (k, true)) * eval (om L N (some (k, true)) ^ 2) p))
      + om L N (some (k, false)) * (wt N (some (k, false)) * eval (om L N (some (k, false)) ^ 2) p)
        * (om L N (some (k, false)) * (wt N (some (k, false)) * eval (om L N (some (k, false)) ^ 2) p))
      = om L N (some (k, true)) ^ 2 * wt N (some (k, true)) ^ 2 * eval (om L N (some (k, true)) ^ 2) p ^ 2
        + om L N (some (k, false)) ^ 2 * wt N (some (k, false)) ^ 2
          * eval (om L N (some (k, false)) ^ 2) p ^ 2 := by ring
    _ = _ := by rw [om_sq_some, om_sq_some, w1, w2]; ring

/-- `(W² vecOf p)·vecOf p = 2 ∑_K ν_K⁴ p(ν_K²)² e_K²`. -/
theorem dot_W2_vecOf (p : ℝ[X]) :
    (fun i => om L N i ^ 2 * vecOf L N p i) ⬝ᵥ vecOf L N p = 2 * ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 4
      * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 := by
  simp only [dotProduct]
  rw [sum_idx, Finset.mul_sum]
  simp only [vecOf_apply, xOf, om_none, zero_mul, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  have w1 := wt_sq_some (N := N) k true
  have w2 := wt_sq_some (N := N) k false
  calc om L N (some (k, true)) ^ 2 * (om L N (some (k, true))
          * (wt N (some (k, true)) * eval (om L N (some (k, true)) ^ 2) p))
        * (om L N (some (k, true)) * (wt N (some (k, true)) * eval (om L N (some (k, true)) ^ 2) p))
      + om L N (some (k, false)) ^ 2 * (om L N (some (k, false))
          * (wt N (some (k, false)) * eval (om L N (some (k, false)) ^ 2) p))
        * (om L N (some (k, false)) * (wt N (some (k, false)) * eval (om L N (some (k, false)) ^ 2) p))
      = (om L N (some (k, true)) ^ 2) ^ 2 * wt N (some (k, true)) ^ 2
          * eval (om L N (some (k, true)) ^ 2) p ^ 2
        + (om L N (some (k, false)) ^ 2) ^ 2 * wt N (some (k, false)) ^ 2
          * eval (om L N (some (k, false)) ^ 2) p ^ 2 := by ring
    _ = _ := by rw [om_sq_some, om_sq_some, w1, w2]; ring

/-- `|xOf p|² = p(0)² + 2 ∑_K p(ν_K²)² e_K²`. -/
theorem dot_xOf_self (p : ℝ[X]) :
    xOf L N p ⬝ᵥ xOf L N p = p.eval 0 ^ 2 + 2 * ∑ k : Fin N,
      p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 := by
  simp only [dotProduct]
  rw [sum_idx, Finset.mul_sum]
  simp only [xOf, om_none]
  congr 1
  · simp [wt]; ring
  refine Finset.sum_congr rfl fun k _ => ?_
  have w1 := wt_sq_some (N := N) k true
  have w2 := wt_sq_some (N := N) k false
  calc wt N (some (k, true)) * eval (om L N (some (k, true)) ^ 2) p
        * (wt N (some (k, true)) * eval (om L N (some (k, true)) ^ 2) p)
      + wt N (some (k, false)) * eval (om L N (some (k, false)) ^ 2) p
        * (wt N (some (k, false)) * eval (om L N (some (k, false)) ^ 2) p)
      = wt N (some (k, true)) ^ 2 * eval (om L N (some (k, true)) ^ 2) p ^ 2
        + wt N (some (k, false)) ^ 2 * eval (om L N (some (k, false)) ^ 2) p ^ 2 := by ring
    _ = _ := by rw [om_sq_some, om_sq_some, w1, w2]; ring

end Cvs.Finite.OddDisplacementPencil
