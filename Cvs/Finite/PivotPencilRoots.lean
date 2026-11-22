import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A symmetric pencil with a pivot on polynomials of degree `< d`

For symmetric `G ≥ 0` on degree `< d` with `G(Xp, q) = G(p, Xq)` there and a `G`-orthogonal `P` of
degree `d`: the radical is the multiples of a monic `h ∣ P`, `h` has real simple roots `r_0 < ⋯`,
and `G(Xg, g) ≤ r_k G(g, g)` on `g = q·∏_{k<i<n}(X − r_i)`, `deg q ≤ k`.
-/

noncomputable section

open Polynomial

namespace Cvs.Finite.OddDisplacementPencil
variable {G : LinearMap.BilinForm ℝ ℝ[X]} {d : ℕ} {P : ℝ[X]}

/-- A polynomial of natural degree `< d` has degree `< d`. -/
private lemma deg_lt_of_natDeg_lt {p : ℝ[X]} (h : p.natDegree < d) : p.degree < d :=
  lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast h)

/-- Multiplying a polynomial of degree `< d` by `X` gives degree `≤ d`. -/
private lemma degree_X_mul_le {p : ℝ[X]} (hp : p.degree < d) :
    (X * p).degree ≤ (d : WithBot ℕ) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have h1 : p.natDegree < d := (natDegree_lt_iff_degree_lt hp0).mpr hp
  have h2 : (X * p).natDegree ≤ X.natDegree + p.natDegree := natDegree_mul_le
  rw [natDegree_X] at h2
  exact degree_le_of_natDegree_le (by omega)

/-- A pivot has degree `d`, so it is nonzero. -/
private lemma pivot_ne_zero (hP : P.degree = d) : P ≠ 0 := by
  rintro rfl
  simp at hP

/-- **Cauchy–Schwarz on the radical**: a `G`-isotropic polynomial of degree `< d` is
`G`-orthogonal to every polynomial of degree `< d`. -/
private lemma orth_of_isotropic (hsymm : ∀ p q, G p q = G q p)
    (hpsd : ∀ p : ℝ[X], p.degree < d → 0 ≤ G p p) {w : ℝ[X]} (hw : w.degree < d)
    (h0 : G w w = 0) (u : ℝ[X]) (hu : u.degree < d) : G w u = 0 := by
  have key : ∀ t : ℝ, 0 ≤ G u u * (t * t) + 2 * G w u * t + G w w := by
    intro t
    have hm : w + t • u ∈ degreeLT ℝ d :=
      add_mem (mem_degreeLT.mpr hw) (Submodule.smul_mem _ t (mem_degreeLT.mpr hu))
    have e : G (w + t • u) (w + t • u) = G u u * (t * t) + 2 * G w u * t + G w w := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hsymm u w]
      ring
    exact e ▸ hpsd _ (mem_degreeLT.mp hm)
  have hd := discrim_le_zero key
  rw [discrim, h0] at hd
  have hsq : G w u ^ 2 ≤ 0 := by nlinarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hsq (sq_nonneg _))

/-- `G(h, ·)` vanishes on degree `< d` for a divisor `h` of the pivot that generates the
radical: from `hrad` when `deg h < d`, from the pivot when `h` is an associate of `P`. -/
private lemma gen_orth (hP : P.degree = d) (hpiv : ∀ q : ℝ[X], q.degree < d → G P q = 0)
    {h : ℝ[X]} (hdvd : h ∣ P)
    (hrad : ∀ p : ℝ[X], p.degree < d → ((∀ q : ℝ[X], q.degree < d → G p q = 0) ↔ h ∣ p))
    (f : ℝ[X]) (hf : f.degree < d) : G h f = 0 := by
  by_cases hlt : h.degree < d
  · exact (hrad h hlt).mpr dvd_rfl f hf
  have hP0 := pivot_ne_zero hP
  obtain ⟨m, hm⟩ := hdvd
  have hh0 : h ≠ 0 := by rintro rfl; rw [zero_mul] at hm; exact hP0 hm
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact hP0 hm
  have hdeg := congrArg natDegree hm
  rw [natDegree_mul hh0 hm0, natDegree_eq_of_degree_eq_some hP] at hdeg
  have hdh : d ≤ h.natDegree := by
    by_contra hc
    exact hlt (deg_lt_of_natDeg_lt (by omega))
  have hmC : m = C (m.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  have ha : m.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, C_0] at hmC
    exact hm0 hmC
  have hPf := hpiv f hf
  rw [hm, hmC, mul_comm, ← smul_eq_C_mul, map_smul, LinearMap.smul_apply, smul_eq_mul] at hPf
  exact (mul_eq_zero.mp hPf).resolve_left ha

/-- `X − a` moves across `G` between polynomials of degree `< d`. -/
private lemma X_sub_C_mul_comm
    (hcomm : ∀ p q : ℝ[X], p.degree < d → q.degree < d → G (X * p) q = G p (X * q)) (a : ℝ)
    {u v : ℝ[X]} (hu : u.degree < d) (hv : v.degree < d) :
    G ((X - C a) * u) v = G u ((X - C a) * v) := by
  simp only [sub_mul, C_mul', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hcomm u v hu hv]

/-- A nonzero `G`-isotropic polynomial has natural degree at least that of the radical
generator. -/
private lemma false_of_isotropic (hsymm : ∀ p q, G p q = G q p)
    (hpsd : ∀ p : ℝ[X], p.degree < d → 0 ≤ G p p) {h : ℝ[X]} (hhd : h.natDegree ≤ d)
    (hrad : ∀ p : ℝ[X], p.degree < d → ((∀ q : ℝ[X], q.degree < d → G p q = 0) ↔ h ∣ p))
    {w : ℝ[X]} (hw0 : w ≠ 0) (hwh : w.natDegree < h.natDegree) (hww : G w w = 0) : False := by
  have hwd : w.degree < d := deg_lt_of_natDeg_lt (by omega)
  have hdw : h ∣ w := (hrad w hwd).mp (orth_of_isotropic hsymm hpsd hwd hww)
  have := natDegree_le_of_dvd hdw hw0
  omega

/-- A divisor of the pivot has natural degree `≤ d`. -/
private lemma natDegree_le_of_dvd_pivot (hP : P.degree = d) {h : ℝ[X]} (hdvd : h ∣ P) :
    h.natDegree ≤ d := by
  have := natDegree_le_of_dvd hdvd (pivot_ne_zero hP)
  rwa [natDegree_eq_of_degree_eq_some hP] at this

-- H_fix Step 1.4-1.5 (`K` is `T`-invariant, hence `K = (h)/(p_π)` with `h ∣ p_π`)
/-- **The radical of a pencil with a pivot is an ideal**: the polynomials of degree `< d` that are
`G`-orthogonal to all of degree `< d` are those divisible by a monic `h ∣ P`. -/
theorem exists_radical_generator (hsymm : ∀ p q, G p q = G q p)
    (hcomm : ∀ p q : ℝ[X], p.degree < d → q.degree < d → G (X * p) q = G p (X * q))
    (hP : P.degree = d) (hpiv : ∀ q : ℝ[X], q.degree < d → G P q = 0) :
    ∃ h : ℝ[X], h.Monic ∧ h ∣ P ∧
      ∀ p : ℝ[X], p.degree < d → ((∀ q : ℝ[X], q.degree < d → G p q = 0) ↔ h ∣ p) := by
  classical
  have hP0 := pivot_ne_zero hP
  set Pm := P * C P.leadingCoeff⁻¹ with hPm
  have hmon : Pm.Monic := monic_mul_leadingCoeff_inv hP0
  have hPmdeg : Pm.degree = d := by rw [hPm, degree_mul_leadingCoeff_inv _ hP0, hP]
  have hGPm : ∀ q : ℝ[X], q.degree < d → G Pm q = 0 := by
    intro q hq
    rw [hPm, mul_comm, ← smul_eq_C_mul, map_smul, LinearMap.smul_apply, hpiv q hq, smul_zero]
  have hred : ∀ r : ℝ[X], r.degree ≤ d → ∀ q : ℝ[X], q.degree < d →
      G (r %ₘ Pm) q = G r q := by
    intro r hr q hq
    obtain ⟨c, hc⟩ : ∃ c, r /ₘ Pm = C c := ⟨_, eq_C_of_natDegree_le_zero (by
      rw [natDegree_divByMonic _ hmon, natDegree_eq_of_degree_eq_some hPmdeg]
      have := natDegree_le_of_degree_le hr
      omega)⟩
    rw [modByMonic_eq_sub_mul_div, hc, mul_comm, ← smul_eq_C_mul, map_sub, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, hGPm q hq, smul_zero, sub_zero]
  have hPmlt : ∀ f : ℝ[X], (f %ₘ Pm).degree < d := fun f => hPmdeg ▸ degree_modByMonic_lt f hmon
  have hX : ∀ f : ℝ[X], (∀ q : ℝ[X], q.degree < d → G (f %ₘ Pm) q = 0) →
      ∀ q : ℝ[X], q.degree < d → G ((X * f) %ₘ Pm) q = 0 := by
    intro f hf q hq
    have hpd := hPmlt f
    have hXf : (X * f) %ₘ Pm = (X * (f %ₘ Pm)) %ₘ Pm := by
      apply modByMonic_eq_of_dvd_sub hmon
      refine ⟨X * (f /ₘ Pm), ?_⟩
      linear_combination (-X) * modByMonic_add_div f Pm
    rw [hXf, hred _ (degree_X_mul_le hpd) q hq, hcomm _ q hpd hq, hsymm,
      ← hred _ (degree_X_mul_le hq) _ hpd, hsymm]
    exact hf _ (hPmlt _)
  let S : Submodule ℝ ℝ[X] :=
    { carrier := {f | ∀ q : ℝ[X], q.degree < d → G (f %ₘ Pm) q = 0}
      add_mem' := by
        intro a b ha hb q hq
        rw [add_modByMonic, map_add, LinearMap.add_apply, ha q hq, hb q hq, add_zero]
      zero_mem' := by
        intro q _
        rw [zero_modByMonic, map_zero, LinearMap.zero_apply]
      smul_mem' := by
        intro c f hf q hq
        rw [smul_modByMonic, map_smul, LinearMap.smul_apply, hf q hq, smul_zero] }
  have hS : ∀ f, f ∈ S ↔ ∀ q : ℝ[X], q.degree < d → G (f %ₘ Pm) q = 0 := fun f => Iff.rfl
  let I : Ideal ℝ[X] :=
    { S.toAddSubmonoid with
      smul_mem' := by
        intro c f hf
        change c * f ∈ S
        induction c using Polynomial.induction_on with
        | C a => rw [C_mul']; exact S.smul_mem a hf
        | add p q hp hq => rw [add_mul]; exact S.add_mem hp hq
        | monomial n a ih =>
          rw [show C a * X ^ (n + 1) * f = X * (C a * X ^ n * f) by ring]
          exact (hS _).mpr (hX _ ((hS _).mp ih)) }
  have hI : ∀ f, f ∈ I ↔ ∀ q : ℝ[X], q.degree < d → G (f %ₘ Pm) q = 0 := fun f => Iff.rfl
  have hg : ∀ f, f ∈ I ↔ Submodule.IsPrincipal.generator I ∣ f := fun f =>
    Submodule.IsPrincipal.mem_iff_generator_dvd I
  have hPmI : Pm ∈ I := (hI Pm).mpr fun q _ => by
    rw [modByMonic_self hmon, map_zero, LinearMap.zero_apply]
  have hg0 : Submodule.IsPrincipal.generator I ≠ 0 := by
    intro h0
    have := (hg Pm).mp hPmI
    rw [h0, zero_dvd_iff] at this
    exact hmon.ne_zero this
  have hPmP : Pm ∣ P := ⟨C P.leadingCoeff, by
    rw [hPm, mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hP0), C_1, mul_one]⟩
  refine ⟨normalize (Submodule.IsPrincipal.generator I), monic_normalize hg0, ?_, ?_⟩
  · rw [normalize_dvd_iff]
    exact dvd_trans ((hg Pm).mp hPmI) hPmP
  · intro p hp
    rw [normalize_dvd_iff, ← hg, hI, (modByMonic_eq_self_iff hmon).mpr (hPmdeg ▸ hp)]

/-- **No non-real eigenvalue**: no real quadratic `X² − sX + t` with `s² < 4t` divides a divisor
`h` of the pivot that generates the radical. -/
private lemma not_quadratic_dvd (hsymm : ∀ p q, G p q = G q p)
    (hpsd : ∀ p : ℝ[X], p.degree < d → 0 ≤ G p p)
    (hcomm : ∀ p q : ℝ[X], p.degree < d → q.degree < d → G (X * p) q = G p (X * q))
    (hP : P.degree = d) (hpiv : ∀ q : ℝ[X], q.degree < d → G P q = 0) {h : ℝ[X]} (hdvd : h ∣ P)
    (hrad : ∀ p : ℝ[X], p.degree < d → ((∀ q : ℝ[X], q.degree < d → G p q = 0) ↔ h ∣ p))
    {s t : ℝ} (hst : s ^ 2 < 4 * t) : ¬ (X ^ 2 - C s * X + C t) ∣ h := by
  rintro ⟨k, hk⟩
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact pivot_ne_zero hP (zero_dvd_iff.mp hdvd)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact hh0 hk
  have hQ : (X ^ 2 - C s * X + C t : ℝ[X]).natDegree = 2 := by compute_degree!
  have hQ0 : (X ^ 2 - C s * X + C t : ℝ[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hQ
    exact absurd hQ (by norm_num)
  have hhk : h.natDegree = 2 + k.natDegree := by rw [hk, natDegree_mul hQ0 hk0, hQ]
  have hhd := natDegree_le_of_dvd_pivot hP hdvd
  have hkd : k.degree < d := deg_lt_of_natDeg_lt (by omega)
  have hXk : (X * k).natDegree ≤ X.natDegree + k.natDegree := natDegree_mul_le
  rw [natDegree_X] at hXk
  have hXkd : (X * k).degree < (d : WithBot ℕ) := deg_lt_of_natDeg_lt (by omega)
  have hGkh : G k h = 0 := by
    rw [hsymm]
    exact gen_orth hP hpiv hdvd hrad k hkd
  have hexp : h = X * (X * k) - s • (X * k) + t • k := by
    rw [hk, smul_eq_C_mul, smul_eq_C_mul]
    ring
  rw [hexp] at hGkh
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at hGkh
  have hA : G (X * k) (X * k) = G k (X * (X * k)) := hcomm k (X * k) hkd hXkd
  have hB : G (X * k) k = G k (X * k) := hsymm _ _
  have hwd : (X * k - (s / 2) • k).degree < (d : WithBot ℕ) :=
    mem_degreeLT.mp (sub_mem (mem_degreeLT.mpr hXkd)
      (Submodule.smul_mem _ _ (mem_degreeLT.mpr hkd)))
  have hw := hpsd _ hwd
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hw
  have hC := hpsd k hkd
  have key : (4 * t - s ^ 2) * G k k ≤ 0 := by
    rw [hA, hB] at hw
    nlinarith
  have hC0 : G k k = 0 := by
    refine le_antisymm ?_ hC
    by_contra hc
    rw [not_le] at hc
    nlinarith [mul_pos (sub_pos.mpr hst) hc]
  exact false_of_isotropic hsymm hpsd hhd hrad hk0 (by omega) hC0

-- H_fix Step 1.5 (`T` is `G`-self-adjoint on `H_W/K`: no non-real eigenvalue)
/-- **The radical generator splits over `ℝ`**: no irreducible quadratic factor `(X − a)² + b²`
divides `h`. -/
theorem splits_of_radical_generator (hsymm : ∀ p q, G p q = G q p)
    (hpsd : ∀ p : ℝ[X], p.degree < d → 0 ≤ G p p)
    (hcomm : ∀ p q : ℝ[X], p.degree < d → q.degree < d → G (X * p) q = G p (X * q))
    (hP : P.degree = d) (hpiv : ∀ q : ℝ[X], q.degree < d → G P q = 0) {h : ℝ[X]} (hdvd : h ∣ P)
    (hrad : ∀ p : ℝ[X], p.degree < d → ((∀ q : ℝ[X], q.degree < d → G p q = 0) ↔ h ∣ p)) :
    h.Splits := by
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact pivot_ne_zero hP (zero_dvd_iff.mp hdvd)
  refine Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _) fun z hz => ?_
  by_cases him : z.im = 0
  · exact ⟨z.re, Complex.ext (by simp) (by simp [him])⟩
  have hz' : aeval z h = 0 := by
    rw [mem_roots (map_ne_zero hh0), IsRoot.def, eval_map_algebraMap] at hz
    exact hz
  refine absurd (quadratic_dvd_of_aeval_eq_zero_im_ne_zero h hz' him)
    (not_quadratic_dvd hsymm hpsd hcomm hP hpiv hdvd hrad ?_)
  rw [Complex.sq_norm, Complex.normSq_apply]
  have := mul_self_pos.mpr him
  nlinarith

-- H_fix Step 1.5 (`T` is cyclic and `G`-self-adjoint on `H_W/K`: no repeated eigenvalue)
/-- **The radical generator is squarefree**: no `q²` with `q` nonconstant divides `h`. -/
theorem squarefree_of_radical_generator (hsymm : ∀ p q, G p q = G q p)
    (hpsd : ∀ p : ℝ[X], p.degree < d → 0 ≤ G p p)
    (hcomm : ∀ p q : ℝ[X], p.degree < d → q.degree < d → G (X * p) q = G p (X * q))
    (hP : P.degree = d) (hpiv : ∀ q : ℝ[X], q.degree < d → G P q = 0) {h : ℝ[X]} (hdvd : h ∣ P)
    (hrad : ∀ p : ℝ[X], p.degree < d → ((∀ q : ℝ[X], q.degree < d → G p q = 0) ↔ h ∣ p)) :
    Squarefree h := by
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact pivot_ne_zero hP (zero_dvd_iff.mp hdvd)
  have hsp := splits_of_radical_generator hsymm hpsd hcomm hP hpiv hdvd hrad
  have hhd := natDegree_le_of_dvd_pivot hP hdvd
  intro x hx
  by_contra hxu
  have hxs : x.Splits := hsp.of_dvd hh0 (dvd_trans (dvd_mul_right x x) hx)
  obtain ⟨a, ha⟩ := hxs.exists_eval_eq_zero fun h0 => hxu (isUnit_iff_degree_eq_zero.mpr h0)
  have hax : X - C a ∣ x := dvd_iff_isRoot.mpr ha
  obtain ⟨k, hk⟩ := dvd_trans (mul_dvd_mul hax hax) hx
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact hh0 hk
  have hl0 := X_sub_C_ne_zero a
  have hhk : h.natDegree = k.natDegree + 2 := by
    rw [hk, natDegree_mul (mul_ne_zero hl0 hl0) hk0, natDegree_mul hl0 hl0, natDegree_X_sub_C]
    ring
  have hkd : k.degree < d := deg_lt_of_natDeg_lt (by omega)
  have hw0 : (X - C a) * k ≠ 0 := mul_ne_zero hl0 hk0
  have hwn : ((X - C a) * k).natDegree = k.natDegree + 1 := by
    rw [natDegree_mul hl0 hk0, natDegree_X_sub_C]
    ring
  have hwd : ((X - C a) * k).degree < (d : WithBot ℕ) := deg_lt_of_natDeg_lt (by omega)
  have hww : G ((X - C a) * k) ((X - C a) * k) = 0 := by
    rw [X_sub_C_mul_comm hcomm a hkd hwd, ← mul_assoc, ← hk, hsymm]
    exact gen_orth hP hpiv hdvd hrad k hkd
  exact false_of_isotropic hsymm hpsd hhd hrad hw0 (by omega) hww

/-- A list product of linear factors is the product over its indices. -/
private lemma list_prod_X_sub_C (l : List ℝ) :
    (l.map (fun a => X - C a)).prod = ∏ i ∈ Finset.range l.length, (X - C (l.getD i 0)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.length_cons, Finset.prod_range_succ']
    simp [mul_comm]

-- H_fix Step 1.5 (real simple roots `r_1 < ⋯ < r_n`)
/-- **A monic squarefree real polynomial that splits is `∏_{i<n}(X − r_i)` with `r` strictly
increasing.** -/
theorem exists_strictMono_roots {h : ℝ[X]} (hmon : h.Monic) (hs : h.Splits) (hsq : Squarefree h) :
    ∃ (n : ℕ) (r : ℕ → ℝ), StrictMonoOn r (Set.Iio n) ∧ h = ∏ i ∈ Finset.range n, (X - C (r i)) := by
  have hnd : h.roots.Nodup := nodup_roots (PerfectField.separable_iff_squarefree.mpr hsq)
  set l := h.roots.sort (· ≤ ·)
  have hlm : (l : Multiset ℝ) = h.roots := Multiset.sort_eq _ _
  have hlnd : l.Nodup := by rw [← Multiset.coe_nodup, hlm]; exact hnd
  have hlt : l.Pairwise (· < ·) :=
    ((Multiset.pairwise_sort h.roots (· ≤ ·)).and hlnd).imp fun h12 => lt_of_le_of_ne h12.1 h12.2
  refine ⟨l.length, fun i => l.getD i 0, ?_, ?_⟩
  · intro i hi j hj hij
    have hi' : i < l.length := hi
    have hj' : j < l.length := hj
    show l.getD i 0 < l.getD j 0
    rw [List.getD_eq_getElem l 0 hi', List.getD_eq_getElem l 0 hj']
    exact List.pairwise_iff_getElem.mp hlt i j hi' hj' hij
  · calc h = (h.roots.map (fun a => X - C a)).prod := hs.eq_prod_roots_of_monic hmon
      _ = (l.map (fun a => X - C a)).prod := by rw [← hlm, Multiset.map_coe, Multiset.prod_coe]
      _ = _ := list_prod_X_sub_C l

/-- **The radical generator has real simple roots**: `h = ∏_{i<n} (X − r_i)` with `r` strictly
increasing. -/
theorem exists_roots_of_radical_generator (hsymm : ∀ p q, G p q = G q p)
    (hpsd : ∀ p : ℝ[X], p.degree < d → 0 ≤ G p p)
    (hcomm : ∀ p q : ℝ[X], p.degree < d → q.degree < d → G (X * p) q = G p (X * q))
    (hP : P.degree = d) (hpiv : ∀ q : ℝ[X], q.degree < d → G P q = 0) {h : ℝ[X]} (hmon : h.Monic)
    (hdvd : h ∣ P) (hrad : ∀ p : ℝ[X], p.degree < d → ((∀ q : ℝ[X], q.degree < d → G p q = 0) ↔ h ∣ p)) :
    ∃ (n : ℕ) (r : ℕ → ℝ), StrictMonoOn r (Set.Iio n) ∧ h = ∏ i ∈ Finset.range n, (X - C (r i)) :=
  exists_strictMono_roots hmon
    (splits_of_radical_generator hsymm hpsd hcomm hP hpiv hdvd hrad)
    (squarefree_of_radical_generator hsymm hpsd hcomm hP hpiv hdvd hrad)

/-- `∏_{i<n}(X − r_i) = ∏_{i<k}(X − r_i)·(X − r_k)·∏_{k<i<n}(X − r_i)` for `k < n`. -/
private lemma prod_range_split (r : ℕ → ℝ) {k n : ℕ} (hk : k < n) :
    ∏ i ∈ Finset.range n, (X - C (r i)) =
      (∏ i ∈ Finset.range k, (X - C (r i))) * (X - C (r k)) *
        ∏ i ∈ Finset.Ioo k n, (X - C (r i)) := by
  rw [← Finset.prod_range_mul_prod_Ico _ hk.le, ← Finset.Ioo_insert_left hk,
    Finset.prod_insert Finset.left_notMem_Ioo, mul_assoc]

/-- `∏_{k<i<n}(X − r_i) = (X − r_{k+1})·∏_{k+1<i<n}(X − r_i)` for `k + 1 < n`. -/
private lemma prod_Ioo_succ (r : ℕ → ℝ) {k n : ℕ} (hk : k + 1 < n) :
    ∏ i ∈ Finset.Ioo k n, (X - C (r i)) =
      (X - C (r (k + 1))) * ∏ i ∈ Finset.Ioo (k + 1) n, (X - C (r i)) := by
  have hs : Finset.Ioo k n = insert (k + 1) (Finset.Ioo (k + 1) n) := by
    ext i
    simp only [Finset.mem_Ioo, Finset.mem_insert]
    omega
  rw [hs, Finset.prod_insert Finset.left_notMem_Ioo]

/-- **The Rayleigh bound from `G(h, ·) = 0`**: `G(Xg, g) ≤ r_k G(g, g)` for
`g = q·∏_{k<i<n}(X − r_i)` with `deg q ≤ k`, splitting off the eigen-class `∏_{i≠k}(X − r_i)`,
which is `G`-orthogonal to the remainder `(X − r_k)q'·∏_{k<i<n}(X − r_i)`. -/
private lemma rayleigh_step (hsymm : ∀ p q, G p q = G q p)
    (hpsd : ∀ p : ℝ[X], p.degree < d → 0 ≤ G p p)
    (hcomm : ∀ p q : ℝ[X], p.degree < d → q.degree < d → G (X * p) q = G p (X * q))
    {n : ℕ} {r : ℕ → ℝ} (hr : StrictMonoOn r (Set.Iio n)) (hnd : n ≤ d)
    (hH : ∀ f : ℝ[X], f.degree < d → G (∏ i ∈ Finset.range n, (X - C (r i))) f = 0) (k : ℕ) :
    k < n → ∀ q : ℝ[X], q.natDegree ≤ k →
      G (X * (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i)))) (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i)))
        ≤ r k * G (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i)))
          (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i))) := by
  have hu : ∀ j, (∏ i ∈ Finset.Ioo j n, (X - C (r i))).natDegree = n - j - 1 := fun j => by
    rw [natDegree_finsetProd_X_sub_C_eq_card, Nat.card_Ioo]
  have hdeg : ∀ f : ℝ[X], f.natDegree < n → f.degree < d := fun f hf =>
    deg_lt_of_natDeg_lt (by omega)
  induction k with
  | zero =>
    intro hn q hq
    obtain ⟨c, rfl⟩ : ∃ c, q = C c := ⟨_, eq_C_of_natDegree_le_zero hq⟩
    have hsplit := prod_range_split r hn
    rw [Finset.prod_range_zero, one_mul] at hsplit
    set u := ∏ i ∈ Finset.Ioo 0 n, (X - C (r i)) with hu0
    have hgd : (C c * u).degree < d := hdeg _ (by
      have h1 := natDegree_mul_le (p := C c) (q := u)
      rw [natDegree_C, hu 0] at h1
      omega)
    have hXg : X * (C c * u) = r 0 • (C c * u) + c • ∏ i ∈ Finset.range n, (X - C (r i)) := by
      rw [hsplit, smul_eq_C_mul, smul_eq_C_mul]
      ring
    rw [hXg]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hH _ hgd, mul_zero, add_zero, le_refl]
  | succ k ih =>
    intro hn q hq
    have hrk : r k < r (k + 1) :=
      hr (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr hn) (by omega)
    have hℓr : (∏ i ∈ Finset.range (k + 1), (X - C (r i))).eval (r (k + 1)) ≠ 0 := by
      rw [eval_prod, Finset.prod_ne_zero_iff]
      intro i hi
      rw [Finset.mem_range] at hi
      rw [eval_sub, eval_X, eval_C, sub_ne_zero]
      exact (hr (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr hn) hi).ne'
    have hu01 := prod_Ioo_succ r hn
    have hHsplit := prod_range_split r hn
    set r1 := r (k + 1) with hr1
    set u1 := ∏ i ∈ Finset.Ioo (k + 1) n, (X - C (r i)) with hu1
    set u0 := ∏ i ∈ Finset.Ioo k n, (X - C (r i)) with hu0
    set ℓ := ∏ i ∈ Finset.range (k + 1), (X - C (r i)) with hℓ
    set H := ∏ i ∈ Finset.range n, (X - C (r i)) with hHdef
    have hℓdeg : ℓ.natDegree = k + 1 := by
      rw [hℓ, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range]
    set c := q.eval r1 / ℓ.eval r1 with hc
    have hroot : (q - C c * ℓ).IsRoot r1 := by
      rw [IsRoot.def, eval_sub, eval_mul, eval_C, hc, div_mul_cancel₀ _ hℓr, sub_self]
    set q' := (q - C c * ℓ) /ₘ (X - C r1) with hq'
    have hq'mul : (X - C r1) * q' = q - C c * ℓ := mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hq'deg : q'.natDegree ≤ k := by
      rw [hq', natDegree_divByMonic _ (monic_X_sub_C r1), natDegree_X_sub_C]
      have h1 : (q - C c * ℓ).natDegree ≤ max q.natDegree (C c * ℓ).natDegree :=
        natDegree_sub_le _ _
      have h2 : (C c * ℓ).natDegree ≤ ℓ.natDegree := natDegree_C_mul_le _ _
      omega
    set e := ℓ * u1 with he
    set g' := q' * u0 with hg'
    have hu1d : u1.natDegree = n - (k + 1) - 1 := hu (k + 1)
    have hu0d : u0.natDegree = n - k - 1 := hu k
    have hed : e.degree < d := hdeg _ (by
      have h1 : e.natDegree ≤ ℓ.natDegree + u1.natDegree := natDegree_mul_le
      omega)
    have hg'd : g'.degree < d := hdeg _ (by
      have h1 : g'.natDegree ≤ q'.natDegree + u0.natDegree := natDegree_mul_le
      omega)
    have hfd : (q' * u1).degree < d := hdeg _ (by
      have h1 : (q' * u1).natDegree ≤ q'.natDegree + u1.natDegree := natDegree_mul_le
      omega)
    have hg : q * u1 = c • e + g' := by
      rw [smul_eq_C_mul, he, hg', hu01]
      linear_combination (-u1) * hq'mul
    have hXe : X * e = r1 • e + H := by
      rw [hHsplit, he, smul_eq_C_mul]
      ring
    have K3 : ∀ w : ℝ[X], w.degree < d → G (X * e) w = r1 * G e w := by
      intro w hw
      rw [hXe, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hH w hw, add_zero,
        smul_eq_mul]
    have K2 : G e g' = 0 := by
      have hg'f : g' = (X - C r1) * (q' * u1) := by
        rw [hg', hu01]
        ring
      rw [hg'f, ← X_sub_C_mul_comm hcomm r1 hed hfd,
        show (X - C r1) * e = H by rw [hHsplit, he]; ring]
      exact hH _ hfd
    have K4 : G (X * g') e = 0 := by
      rw [hcomm g' e hg'd hed, hsymm, K3 g' hg'd, K2, mul_zero]
    have hXg : X * (q * u1) = c • (X * e) + X * g' := by
      rw [hg, mul_add, mul_smul_comm]
    have ihk : G (X * g') g' ≤ r k * G g' g' := ih (by omega) q' hq'deg
    have hpos : 0 ≤ G g' g' := hpsd g' hg'd
    rw [hXg, hg]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [K3 e hed, K3 g' hg'd, K2, K4, hsymm g' e, K2]
    nlinarith [mul_le_mul_of_nonneg_right hrk.le hpos]

-- H_fix Step 2 (eigen-classes `[h/(λ − r_i)]` are `G`-orthogonal; `B/G ≤ r_k` on their span)
/-- **The Rayleigh bound on a root deflation**: for `g = q·∏_{k<i<n}(X − r_i)` with `deg q ≤ k`,
`G(Xg, g) ≤ r_k G(g, g)`, and `G(g, g) > 0` when `q ≠ 0`. -/
theorem rayleigh_le_of_roots (hsymm : ∀ p q, G p q = G q p)
    (hpsd : ∀ p : ℝ[X], p.degree < d → 0 ≤ G p p)
    (hcomm : ∀ p q : ℝ[X], p.degree < d → q.degree < d → G (X * p) q = G p (X * q))
    (hP : P.degree = d) (hpiv : ∀ q : ℝ[X], q.degree < d → G P q = 0) {n : ℕ} {r : ℕ → ℝ}
    (hr : StrictMonoOn r (Set.Iio n)) (hdvd : (∏ i ∈ Finset.range n, (X - C (r i))) ∣ P)
    (hrad : ∀ p : ℝ[X], p.degree < d →
      ((∀ q : ℝ[X], q.degree < d → G p q = 0) ↔ (∏ i ∈ Finset.range n, (X - C (r i))) ∣ p))
    {k : ℕ} (hk : k < n) {q : ℝ[X]} (hq : q.natDegree ≤ k) :
    G (X * (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i)))) (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i)))
        ≤ r k * G (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i))) (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i)))
      ∧ (q ≠ 0 →
        0 < G (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i))) (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i)))) := by
  have hhd := natDegree_le_of_dvd_pivot hP hdvd
  have hnd : n ≤ d := by
    rwa [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range] at hhd
  refine ⟨rayleigh_step hsymm hpsd hcomm hr hnd (gen_orth hP hpiv hdvd hrad) k hk q hq,
    fun hq0 => ?_⟩
  have hg0 := mul_ne_zero hq0 (monic_prod_X_sub_C r (Finset.Ioo k n)).ne_zero
  have hgn : (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i))).natDegree < n := by
    have h1 := natDegree_mul_le (p := q) (q := ∏ i ∈ Finset.Ioo k n, (X - C (r i)))
    rw [natDegree_finsetProd_X_sub_C_eq_card, Nat.card_Ioo] at h1
    omega
  have hgd : (q * ∏ i ∈ Finset.Ioo k n, (X - C (r i))).degree < (d : WithBot ℕ) :=
    deg_lt_of_natDeg_lt (by omega)
  rcases (hpsd _ hgd).lt_or_eq with h1 | h1
  · exact h1
  · refine (false_of_isotropic hsymm hpsd hhd hrad hg0 ?_ h1.symm).elim
    rwa [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range]

end Cvs.Finite.OddDisplacementPencil
