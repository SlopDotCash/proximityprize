/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Round 5 (#357): truncated recurrence transversality — the Sylvester-pairing lemma

The annihilator-trichotomy programme (issue record) needs the **pairwise transversality**
engine: two truncated linear-recurrent sequences with coprime characteristic polynomials
share only the zero sequence once the window length reaches the degree sum. Proven here by
a resultant-free Sylvester argument:

* `pair_mul_eq_zero` — the coefficient pairing `⟨p, s⟩ = Σ_{n<m} p_n s_n` vanishes on every
  multiple `u·A` whose degree stays below the window (`AnnAt A s m` unfolds monomial-wise
  into shifted annihilation windows);
* `exists_sylvester_combination` — coprime `A, B` express **every** `p` of degree `< m` as
  `u·A + v·B` with both summands of degree `< m` (Bezout + one monic Euclidean reduction +
  re-absorbing the `A·B`-multiple; the degree bookkeeping is the invertibility of the
  Sylvester system, no determinants);
* `trunc_transversality` — **the lemma**: a sequence annihilated by two coprime
  characteristic polynomials on all windows of `[0, m)`, with `deg A + deg B ≤ m`, vanishes
  identically on `[0, m)`.

In staircase terms: moment sequences of two disjoint blocks never collide once
`d ≥ 2b − 1` — the lower edge of the explosion strip and the first ingredient of the
boundary-row analysis and the MDS rank attack.

All results are `sorry`-free and axiom-clean.
-/

set_option autoImplicit false

namespace ProximityGap.TruncatedRecurrenceTransversality

open Polynomial Finset

variable {F : Type} [Field F]

/-- Annihilation of `s` by `P` on every window inside `[0, m)`. -/
def AnnAt (P : F[X]) (s : ℕ → F) (m : ℕ) : Prop :=
  ∀ i, i + P.natDegree < m →
    ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * s (i + j) = 0

/-- The coefficient pairing against the first `m` coordinates. -/
def pair (p : F[X]) (s : ℕ → F) (m : ℕ) : F :=
  ∑ n ∈ Finset.range m, p.coeff n * s n

theorem pair_add (p q : F[X]) (s : ℕ → F) (m : ℕ) :
    pair (p + q) s m = pair p s m + pair q s m := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_add]
  ring

/-- Pairing a single shifted monomial multiple of `A` is a shifted annihilation window. -/
theorem pair_monomial_mul (A : F[X]) (s : ℕ → F) (m : ℕ) (hAnn : AnnAt A s m)
    (c : F) (k : ℕ) (hk : k + A.natDegree < m) :
    pair (C c * (A * X ^ k)) s m = 0 := by
  unfold pair
  have hcoeff : ∀ n, (C c * (A * X ^ k)).coeff n
      = c * (if k ≤ n then A.coeff (n - k) else 0) := by
    intro n
    rw [coeff_C_mul, coeff_mul_X_pow']
  calc ∑ n ∈ Finset.range m, (C c * (A * X ^ k)).coeff n * s n
      = ∑ n ∈ Finset.range m, c * ((if k ≤ n then A.coeff (n - k) else 0) * s n) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hcoeff n]
        ring
    _ = c * ∑ n ∈ Finset.range m, (if k ≤ n then A.coeff (n - k) else 0) * s n := by
        rw [Finset.mul_sum]
    _ = c * ∑ n ∈ Finset.Ico k m, A.coeff (n - k) * s n := by
        congr 1
        rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (by omega)]
        have h1 : ∑ n ∈ Finset.Ico 0 k, (if k ≤ n then A.coeff (n - k) else 0) * s n
            = 0 := by
          refine Finset.sum_eq_zero fun n hn => ?_
          rw [Finset.mem_Ico] at hn
          rw [if_neg (by omega)]
          ring
        have h2 : ∑ n ∈ Finset.Ico k m, (if k ≤ n then A.coeff (n - k) else 0) * s n
            = ∑ n ∈ Finset.Ico k m, A.coeff (n - k) * s n := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_Ico] at hn
          rw [if_pos hn.1]
        rw [h1, h2, zero_add]
    _ = c * ∑ j ∈ Finset.range (m - k), A.coeff j * s (k + j) := by
        congr 1
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.add_sub_cancel_left]
    _ = c * ∑ j ∈ Finset.range (A.natDegree + 1), A.coeff j * s (k + j) := by
        congr 1
        refine (Finset.sum_subset ?_ ?_).symm
        · intro j hj
          rw [Finset.mem_range] at hj ⊢
          omega
        · intro j _ hj
          rw [Finset.mem_range, not_lt] at hj
          rw [coeff_eq_zero_of_natDegree_lt (by omega)]
          ring
    _ = c * 0 := by rw [hAnn k hk]
    _ = 0 := mul_zero c

/-- The pairing is additive over polynomial finite sums. -/
theorem pair_finset_sum {σ : Type} (T : Finset σ) (f : σ → F[X]) (s : ℕ → F) (m : ℕ) :
    pair (∑ k ∈ T, f k) s m = ∑ k ∈ T, pair (f k) s m := by
  unfold pair
  calc ∑ n ∈ Finset.range m, (∑ k ∈ T, f k).coeff n * s n
      = ∑ n ∈ Finset.range m, ∑ k ∈ T, (f k).coeff n * s n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Polynomial.finset_sum_coeff, Finset.sum_mul]
    _ = ∑ k ∈ T, ∑ n ∈ Finset.range m, (f k).coeff n * s n := Finset.sum_comm

/-- The pairing vanishes on every multiple `u·A` staying below the window. -/
theorem pair_mul_eq_zero (A : F[X]) (s : ℕ → F) (m : ℕ) (hAnn : AnnAt A s m)
    (u : F[X]) (hu : u.natDegree + A.natDegree < m) :
    pair (u * A) s m = 0 := by
  conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq u, Polynomial.sum, Finset.sum_mul]
  rw [pair_finset_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hassoc : C (u.coeff k) * X ^ k * A = C (u.coeff k) * (A * X ^ k) := by ring
  rw [hassoc]
  refine pair_monomial_mul A s m hAnn (u.coeff k) k ?_
  have hkle : k ≤ u.natDegree := Polynomial.le_natDegree_of_mem_supp k hk
  omega

/-- **Sylvester spanning, full window**: coprime `A, B` (both of positive degree) express
every `p` of degree `< m` as `u·A + v·B` with `deg u + deg A < m` and `deg v + deg B ≤ m`,
provided `deg A + deg B ≤ m`. -/
theorem exists_sylvester_combination {A B : F[X]} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : IsCoprime A B) (hdA : 1 ≤ A.natDegree) (hdB : 1 ≤ B.natDegree)
    {m : ℕ} (hm : A.natDegree + B.natDegree ≤ m)
    {p : F[X]} (hp : p.natDegree < m) (hp0 : p ≠ 0) :
    ∃ u v : F[X], u.natDegree + A.natDegree < m ∧ v.natDegree + B.natDegree < m ∧
      p = u * A + v * B := by
  -- Bezout, then reduce the A-cofactor modulo the monic normalization of B
  obtain ⟨α, β, hbez⟩ := hAB
  set c : F := B.leadingCoeff with hc
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hB
  set Bm : F[X] := B * C c⁻¹ with hBm
  have hBmonic : Bm.Monic := monic_mul_leadingCoeff_inv hB
  have hBmdeg : Bm.natDegree = B.natDegree := by
    rw [hBm, natDegree_mul hB (by simp [hc0]), natDegree_C, add_zero]
  set u : F[X] := (p * α) %ₘ Bm with hu
  set q : F[X] := (p * α) /ₘ Bm with hq
  have hdiv : p * α = u + Bm * q := by
    rw [hu, hq]
    have h := modByMonic_add_div (p * α) Bm
    linear_combination -h
  set v : F[X] := p * β + (q * C c⁻¹) * A with hv
  have hpid : p = u * A + v * B := by
    have hqB : Bm * q = (q * C c⁻¹) * B := by
      rw [hBm]; ring
    have hp1 : p = (p * α) * A + (p * β) * B := by
      calc p = p * 1 := (mul_one p).symm
        _ = p * (α * A + β * B) := by rw [hbez]
        _ = (p * α) * A + (p * β) * B := by ring
    rw [hp1, hdiv, hqB, hv]
    ring
  -- degree of u: strictly below deg B
  have hudeg : u = 0 ∨ u.natDegree < B.natDegree := by
    by_cases hu0 : u = 0
    · exact Or.inl hu0
    · right
      have h := degree_modByMonic_lt (p * α) hBmonic
      rw [← hu] at h
      have h2 : u.degree < (Bm.natDegree : WithBot ℕ) := by
        rwa [degree_eq_natDegree hBmonic.ne_zero] at h
      rw [hBmdeg] at h2
      exact natDegree_lt_iff_degree_lt hu0 |>.mpr h2
  -- degree of v: from v·B = p − u·A
  have hvB : v * B = p - u * A := by linear_combination -hpid
  have hvdeg : v = 0 ∨ v.natDegree + B.natDegree < m := by
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · right
      have hvB0 : v * B ≠ 0 := mul_ne_zero hv0 hB
      have hsubdeg : (p - u * A).natDegree < m := by
        refine lt_of_le_of_lt (natDegree_sub_le p (u * A)) ?_
        rw [max_lt_iff]
        refine ⟨hp, ?_⟩
        rcases hudeg with hu0 | hud
        · rw [hu0, zero_mul, natDegree_zero]
          omega
        · refine lt_of_le_of_lt (natDegree_mul_le) ?_
          omega
      have hmul : (v * B).natDegree = v.natDegree + B.natDegree :=
        natDegree_mul hv0 hB
      rw [hvB] at hmul
      omega
  rcases hvdeg with hv0 | hvlt
  · -- v = 0: p = u·A with deg u + deg A = deg p < m
    have hpu : p = u * A := by rw [hpid, hv0]; ring
    have hu0 : u ≠ 0 := by
      rintro hu0
      rw [hu0, zero_mul] at hpu
      exact hp0 hpu
    have hmul : (u * A).natDegree = u.natDegree + A.natDegree := natDegree_mul hu0 hA
    rw [← hpu] at hmul
    refine ⟨u, 0, by omega, ?_, by rw [hpid, hv0]⟩
    rw [natDegree_zero]
    omega
  · rcases hudeg with hu0 | hud
    · refine ⟨0, v, ?_, hvlt, by rw [hpid, hu0]⟩
      rw [natDegree_zero]
      omega
    · exact ⟨u, v, by omega, hvlt, hpid⟩

/-- **THE TRANSVERSALITY LEMMA**: a truncated sequence annihilated on all windows by two
coprime characteristic polynomials of total degree within the window vanishes. The lower
edge of the explosion strip (`d ≥ 2b − 1`): disjoint-block moment sequences never collide. -/
theorem trunc_transversality {A B : F[X]} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : IsCoprime A B) {m : ℕ} (hm : A.natDegree + B.natDegree ≤ m)
    {s : ℕ → F} (hAnnA : AnnAt A s m) (hAnnB : AnnAt B s m) :
    ∀ n < m, s n = 0 := by
  -- degenerate cases: a constant annihilator kills directly
  by_cases hdA : A.natDegree = 0
  · intro n hn
    have h := hAnnA n (by omega)
    rw [hdA] at h
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.add_zero] at h
    have hA0 : A.coeff 0 ≠ 0 := by
      intro hz
      have hAC := Polynomial.eq_C_of_natDegree_eq_zero hdA
      rw [hz, map_zero] at hAC
      exact hA hAC
    exact (mul_eq_zero.mp h).resolve_left hA0
  by_cases hdB : B.natDegree = 0
  · intro n hn
    have h := hAnnB n (by omega)
    rw [hdB] at h
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.add_zero] at h
    have hB0 : B.coeff 0 ≠ 0 := by
      intro hz
      have hBC := Polynomial.eq_C_of_natDegree_eq_zero hdB
      rw [hz, map_zero] at hBC
      exact hB hBC
    exact (mul_eq_zero.mp h).resolve_left hB0
  -- main case: test the pairing against X^n
  intro n hn
  have hXn : (X : F[X]) ^ n ≠ 0 := pow_ne_zero n X_ne_zero
  obtain ⟨u, v, hu, hv, hid⟩ := exists_sylvester_combination hA hB hAB
    (by omega) (by omega) hm (by rwa [natDegree_X_pow]) hXn
  have hpairX : pair ((X : F[X]) ^ n) s m = s n := by
    unfold pair
    rw [Finset.sum_eq_single n]
    · rw [coeff_X_pow, if_pos rfl, one_mul]
    · intro k _ hk
      rw [coeff_X_pow, if_neg hk, zero_mul]
    · intro habs
      exact absurd (Finset.mem_range.mpr hn) habs
  rw [← hpairX, hid, pair_add]
  rw [pair_mul_eq_zero A s m hAnnA u hu]
  rw [pair_mul_eq_zero B s m hAnnB v hv]
  exact zero_add 0

/-! ## Source audit -/

#print axioms pair_mul_eq_zero
#print axioms exists_sylvester_combination
#print axioms trunc_transversality

end ProximityGap.TruncatedRecurrenceTransversality
