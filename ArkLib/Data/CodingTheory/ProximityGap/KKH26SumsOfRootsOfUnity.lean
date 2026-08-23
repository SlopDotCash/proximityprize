/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ResultantLiftLoop52
import ArkLib.ToMathlib.OddCharacterOrthogonality
import Mathlib

/-!
# KKH26 Lemma 1 — distinct signed sums of roots of unity at an explicit prime threshold

This file formalizes **Lemma 1** of [KKH26] (Krachun–Kazanin–Haböck, *Failure of proximity
gaps close to capacity*, ePrint 2026/782), the single new mathematical kernel of their
counterexample to the [BCIKS20] up-to-capacity proximity-gap conjecture (Conjecture 1) and the
[BGKS20] list-decoding conjecture (Conjecture 2) for Reed–Solomon codes over smooth
multiplicative subgroups of **prime fields** — the Proximity Prize regime (issue #232).

> **Lemma 1 [KKH26].** Let `G` be a multiplicative subgroup of a prime field `F_p` of size
> `s = 2^m`. If `p > s^{s/2}`, then for any integer `1 ≤ r ≤ s/2`,
> `#{x₁ + ⋯ + x_r : distinct x₁, …, x_r ∈ G} ≥ 2^r · (s/2).choose r`.

The proof follows the paper: a sum of `r` distinct elements of `G` stemming from `S ⊆ G` with
`S ∩ (−S) = ∅` is the value at a generator `g` of a **signed sum-polynomial**
`P = ∑ (−1)^{ε_k} X^{i_k}` with distinct exponents `i_k ∈ [0, s/2)`.  If two distinct
sum-polynomials `P, Q` collide at `g`, then `R = P − Q` and `Φ_s = X^{s/2} + 1` share a root
mod `p`, so `p ∣ Res_ℤ(R, Φ_s)` (Loop52 pillar).  The resultant is nonzero by irreducibility
of `Φ_s` over `ℚ` (Loop52 pillar), and over `ℂ` it is the product of the `s/2` values of `R`
at primitive `s`-th roots of unity, each of modulus `≤ ‖R‖₁ ≤ 2r ≤ s`; hence
`0 < |Res| ≤ s^{s/2} < p`, a contradiction.  Distinct data therefore give distinct values,
and there are exactly `2^r · (s/2).choose r` data.

### Relation to in-tree work

`CandidateFiniteFieldDisproofLoop53.lean` proves the *unsigned, existential-prime* variant
(some Dirichlet prime avoiding the finitely many collision resultants).  This file proves the
**quantitative** form the paper's Theorem 1 consumes: *every* `p ≡ 1 (mod s)` above the
**explicit threshold** `s^{s/2}` works, for **signed** sums at **each fixed** `r` — the fixed-`r`
count is what ties to the code distance `δ* = 1 − (r−2)/s` in [KKH26] Proposition 1.  The new
analytic ingredient over Loop52/53 is the archimedean resultant bound
(`natAbs_resultant_cyclotomic_le`).

### What is *not* formalized (honest frontier)

[KKH26] Theorem 1 / Proposition 1 additionally need: vanishing-polynomial gap codeword
constructions over the projection `π : H → G`, Stirling asymptotics for `2^r·C(s/2,r)`, and —
for polynomial field sizes `p = Θ(n^β)` — the Thorner–Zaman quantitative PNT in arithmetic
progressions.  Those remain external; this file is the complete additive-combinatorics core.

## Main results

* `natAbs_resultant_cyclotomic_le` — `|Res_ℤ(R, Φ_{2^m})| ≤ ‖R‖₁^{2^{m-1}}` (window ℓ¹-norm).
* `not_isRoot_of_l1On_pow_lt` — explicit-threshold non-collision: a nonzero `R` with
  `deg R < 2^{m-1}` and `‖R‖₁^{2^{m-1}} < p` has `R(g) ≠ 0` for `g` a primitive `2^m`-th root
  of unity in `F_p`.
* `sVal_injOn` — distinct signed `(U, T)`-data give distinct values `∑_{T} g^i − ∑_{U∖T} g^i`
  whenever `(2^m)^{2^{m-1}} < p`.
* `kkh26_lemma1` — **[KKH26] Lemma 1**: the set of sums of `r` distinct elements of the
  order-`2^m` subgroup `⟨g⟩ ⊆ F_p^×` has at least `2^r · (2^{m-1}).choose r` elements.
* **Divisibility route (issue #334, [KKH26] Lemma 2 wiring):** `collisionResultant` exposes
  the integer `N(d₁,d₂) = Res_ℤ(P_{d₁} − P_{d₂}, Φ_{2^m})` the size route bounds internally;
  `sVal_injOn_of_not_dvd` and `kkh26_lemma1_of_not_dvd` re-run the chain with the size
  hypothesis `p > s^{s/2}` replaced by "`p` divides no collision resultant" (plus the mild
  `p > 2^m`), the form consumable at `p = Θ(n^β)` from the [TZ24] good-prime supply
  (`KKH26ThornerZaman.lean`); `not_dvd_collisionResultant_of_lt` shows the old hypothesis
  implies the new one, while `not_dvd_collisionResultant_of_natAbs_sq_lt` is the small
  arithmetic adapter for squared resultant bounds such as the proposed Landau envelope.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.KKH26

open ArkLib.ProximityGap.ResultantLiftLoop52

/-! ### Window ℓ¹ bookkeeping -/

/-- The ℓ¹-norm of the coefficients of `f` on the window `[0, n)`.  For the polynomials of
this file (supported on `[0, n)`) this is the full ℓ¹ norm `∑ |coeff|`. -/
def l1On (n : ℕ) (f : Polynomial ℤ) : ℕ := ∑ j ∈ range n, (f.coeff j).natAbs

/-- The squared ℓ²-norm of the coefficients of `f` on the window `[0, n)`. -/
def l2SqOn (n : ℕ) (f : Polynomial ℤ) : ℕ := ∑ j ∈ range n, (f.coeff j).natAbs ^ 2

lemma l1On_sub_le (n : ℕ) (f g : Polynomial ℤ) :
    l1On n (f - g) ≤ l1On n f + l1On n g := by
  unfold l1On
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Polynomial.coeff_sub]
  exact Int.natAbs_sub_le _ _

/-- The elementary square inequality used to make the `ℓ²` collision-poly bound additive. -/
lemma nat_add_sq_le_two_sq (A B : ℕ) : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
  nlinarith [sq_nonneg ((A : ℤ) - (B : ℤ))]

lemma natAbs_sub_sq_le_two_sq (a b : ℤ) :
    (a - b).natAbs ^ 2 ≤ 2 * a.natAbs ^ 2 + 2 * b.natAbs ^ 2 := by
  have hN : (a - b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_sub_le a b
  have hsq : (a - b).natAbs ^ 2 ≤ (a.natAbs + b.natAbs) ^ 2 :=
    Nat.pow_le_pow_left hN 2
  exact le_trans hsq (nat_add_sq_le_two_sq a.natAbs b.natAbs)

lemma l2SqOn_sub_le (n : ℕ) (f g : Polynomial ℤ) :
    l2SqOn n (f - g) ≤ 2 * l2SqOn n f + 2 * l2SqOn n g := by
  unfold l2SqOn
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Polynomial.coeff_sub]
  exact natAbs_sub_sq_le_two_sq _ _

lemma natAbs_leadingCoeff_le_l1On {f : Polynomial ℤ} {n : ℕ} (hf : f.natDegree < n) :
    f.leadingCoeff.natAbs ≤ l1On n f := by
  unfold l1On
  rw [Polynomial.leadingCoeff]
  exact Finset.single_le_sum (f := fun j => (f.coeff j).natAbs)
    (fun _ _ => Nat.zero_le _) (mem_range.mpr hf)

/-! ### Norm bounds over `ℂ` -/

/-- A product of complex numbers each of norm `≤ B` has norm `≤ B^card`. -/
lemma norm_multiset_prod_le (s : Multiset ℂ) {B : ℝ} (h : ∀ x ∈ s, ‖x‖ ≤ B) :
    ‖s.prod‖ ≤ B ^ (Multiset.card s) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hB : 0 ≤ B := le_trans (norm_nonneg a) (h a (Multiset.mem_cons_self a s))
    rw [Multiset.prod_cons, Multiset.card_cons]
    calc ‖a * s.prod‖ = ‖a‖ * ‖s.prod‖ := norm_mul a s.prod
      _ ≤ B * B ^ Multiset.card s :=
          mul_le_mul (h a (Multiset.mem_cons_self a s))
            (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
            (norm_nonneg _) hB
      _ = B ^ (Multiset.card s + 1) := (pow_succ' B _).symm

/-- On the unit circle, an integer polynomial of degree `< n` is bounded by its window
ℓ¹-norm. -/
lemma norm_eval_le_l1On {f : Polynomial ℤ} {n : ℕ} (hf : f.natDegree < n) {z : ℂ}
    (hz : ‖z‖ = 1) : ‖(f.map (Int.castRingHom ℂ)).eval z‖ ≤ (l1On n f : ℝ) := by
  have hdeg : (f.map (Int.castRingHom ℂ)).natDegree < n := by
    rwa [natDegree_map_eq_of_injective Int.cast_injective]
  rw [Polynomial.eval_eq_sum_range' hdeg]
  refine le_trans (norm_sum_le _ _) ?_
  unfold l1On
  rw [Nat.cast_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, norm_pow, hz, one_pow, mul_one, Polynomial.coeff_map]
  rw [show ((Int.castRingHom ℂ) (f.coeff i)) = ((f.coeff i : ℤ) : ℂ) from rfl]
  rw [Complex.norm_intCast, Nat.cast_natAbs]
  exact le_of_eq Int.cast_abs.symm

private lemma totient_two_pow {m : ℕ} (hm : 1 ≤ m) :
    Nat.totient (2 ^ m) = 2 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [Nat.zero_add, Nat.totient_prime_pow_succ Nat.prime_two]
  simp

/-! ### The archimedean resultant bound (the new quantitative core over Loop52/53) -/

/-- **Archimedean bound for the cyclotomic resultant.** For `R : ℤ[X]` of degree
`< 2^{m-1} = deg Φ_{2^m}`,
`|Res_ℤ(R, Φ_{2^m})| ≤ ‖R‖₁^{2^{m-1}}`, since over `ℂ` the resultant is (up to sign) the
product of the `2^{m-1}` values of `R` at primitive `2^m`-th roots of unity, each of modulus
`≤ ‖R‖₁`.  This is the explicit-threshold ingredient of [KKH26] Lemma 1 (inequality (3)). -/
theorem natAbs_resultant_cyclotomic_le {m : ℕ} (hm : 1 ≤ m) (R : Polynomial ℤ)
    (hdeg : R.natDegree < 2 ^ (m - 1)) :
    (Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs
      ≤ l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) := by
  classical
  set ι : ℤ →+* ℂ := Int.castRingHom ℂ with hι
  have hinj : Function.Injective ι := Int.cast_injective
  set Φ : Polynomial ℤ := cyclotomic (2 ^ m) ℤ with hΦdef
  -- swap the argument order (the sign dies under `natAbs`)
  have hswap : (Polynomial.resultant R Φ).natAbs = (Polynomial.resultant Φ R).natAbs := by
    rw [Polynomial.resultant_comm, Int.natAbs_mul, Int.natAbs_pow]
    simp
  -- transport the resultant to `ℂ`
  have hdegΦ : (Φ.map ι).natDegree = Φ.natDegree :=
    natDegree_map_eq_of_injective hinj _
  have hdegR : (R.map ι).natDegree = R.natDegree :=
    natDegree_map_eq_of_injective hinj _
  have hmap : Polynomial.resultant (Φ.map ι) (R.map ι) = ι (Polynomial.resultant Φ R) := by
    rw [show Polynomial.resultant (Φ.map ι) (R.map ι)
          = Polynomial.resultant (Φ.map ι) (R.map ι) Φ.natDegree R.natDegree by
        rw [hdegΦ, hdegR],
      Polynomial.resultant_map_map]
  -- the product formula over `ℂ`
  have hΦC : Φ.map ι = cyclotomic (2 ^ m) ℂ := map_cyclotomic_int _ ℂ
  have hmonic : (Φ.map ι).Monic := (cyclotomic.monic _ ℤ).map ι
  have hsplits : (Φ.map ι).Splits := IsAlgClosed.splits _
  have hprod : Polynomial.resultant (Φ.map ι) (R.map ι)
      = (((Φ.map ι).roots).map (R.map ι).eval).prod := by
    have h := Polynomial.resultant_eq_prod_eval (Φ.map ι) (R.map ι)
      ((R.map ι).natDegree) le_rfl hsplits
    rwa [hmonic.leadingCoeff, one_pow, one_mul] at h
  -- each root of `Φ` over `ℂ` lies on the unit circle
  have hroots : ∀ z ∈ (Φ.map ι).roots, ‖(R.map ι).eval z‖ ≤ (l1On (2 ^ (m - 1)) R : ℝ) := by
    intro z hz
    have hroot : (Φ.map ι).IsRoot z := isRoot_of_mem_roots hz
    have hdvd : (Φ.map ι) ∣ (X ^ (2 ^ m) - 1 : Polynomial ℂ) := by
      rw [hΦC]; exact cyclotomic.dvd_X_pow_sub_one (2 ^ m) ℂ
    have hz1 : z ^ (2 ^ m) = 1 := by
      have h0 := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hroot
      simpa [sub_eq_zero] using h0
    have hnorm : ‖z‖ = 1 := by
      have h1 : ‖z‖ ^ (2 ^ m) = 1 := by rw [← norm_pow, hz1, norm_one]
      rcases lt_trichotomy ‖z‖ 1 with h | h | h
      · exact absurd h1 (ne_of_lt (pow_lt_one₀ (norm_nonneg z) h (by positivity)))
      · exact h
      · exact absurd h1 (ne_of_gt (one_lt_pow₀ h (by positivity)))
    exact norm_eval_le_l1On hdeg hnorm
  -- count the roots
  have hcard : Multiset.card (Φ.map ι).roots = 2 ^ (m - 1) := by
    have h1 := hsplits.natDegree_eq_card_roots
    rw [← h1, hdegΦ, hΦdef, natDegree_cyclotomic, totient_two_pow hm]
  -- assemble over `ℝ`
  have hbound : ‖(ι (Polynomial.resultant Φ R) : ℂ)‖
      ≤ ((l1On (2 ^ (m - 1)) R : ℝ)) ^ (2 ^ (m - 1)) := by
    rw [← hmap, hprod]
    have := norm_multiset_prod_le (((Φ.map ι).roots).map (R.map ι).eval)
      (B := (l1On (2 ^ (m - 1)) R : ℝ))
      (by intro x hx
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
          exact hroots z hz)
    rwa [Multiset.card_map, hcard] at this
  have hcast : ‖(ι (Polynomial.resultant Φ R) : ℂ)‖
      = ((Polynomial.resultant Φ R).natAbs : ℝ) := by
    rw [show (ι (Polynomial.resultant Φ R) : ℂ)
          = ((Polynomial.resultant Φ R : ℤ) : ℂ) from rfl]
    rw [Complex.norm_intCast, Nat.cast_natAbs]
    exact Int.cast_abs.symm
  rw [hswap]
  have hfin : ((Polynomial.resultant Φ R).natAbs : ℝ)
      ≤ ((l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) : ℕ) : ℝ) := by
    rw [← hcast]
    push_cast
    exact hbound
  exact_mod_cast hfin

/-! ### Explicit-threshold non-collision -/

/-- **Explicit-threshold non-vanishing at a primitive root** ([KKH26] Lemma 1, collision
step).  If `g ∈ F_p` is a primitive `2^m`-th root of unity and `R : ℤ[X]` is nonzero of
degree `< 2^{m-1}` with `‖R‖₁^{2^{m-1}} < p`, then `R(g) ≠ 0` in `F_p`.  (Loop52's pillars
turn a root into `p ∣ Res_ℤ(R, Φ_{2^m}) ≠ 0`; the archimedean bound caps `|Res| < p`.) -/
theorem not_isRoot_of_l1On_pow_lt {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {R : Polynomial ℤ} (hR0 : R ≠ 0) (hdeg : R.natDegree < 2 ^ (m - 1))
    (hp : l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) < p) :
    ¬ (R.map (Int.castRingHom (ZMod p))).IsRoot g := by
  intro hroot
  -- the leading coefficient of `R` survives mod `p`
  have hlcR : ((R.leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : (p : ℤ) ∣ R.leadingCoeff := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have hlcne : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR0
    have h1 : p ≤ R.leadingCoeff.natAbs := by
      have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
      simpa using Nat.le_of_dvd (Int.natAbs_pos.mpr hlcne) (by simpa using h2)
    have h2 : R.leadingCoeff.natAbs ≤ l1On (2 ^ (m - 1)) R :=
      natAbs_leadingCoeff_le_l1On hdeg
    have h3 : l1On (2 ^ (m - 1)) R ≤ l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) :=
      Nat.le_self_pow (by positivity) _
    omega
  -- `Φ` is monic, so its leading coefficient survives as well
  have hΦmonic : (cyclotomic (2 ^ m) ℤ).Monic := cyclotomic.monic _ ℤ
  have hlcΦ : (((cyclotomic (2 ^ m) ℤ).leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
    rw [hΦmonic.leadingCoeff]
    simp
  -- `g` is a common root of `R` and `Φ` mod `p`
  have hΦroot : ((cyclotomic (2 ^ m) ℤ).map (Int.castRingHom (ZMod p))).IsRoot g := by
    rw [map_cyclotomic_int]
    exact hg.isRoot_cyclotomic (by positivity)
  -- Loop52 pillars: `p ∣ Res ≠ 0`
  have hdvd := prime_dvd_resultant_of_common_root R (cyclotomic (2 ^ m) ℤ)
    hlcR hlcΦ hroot hΦroot
  have hne : Polynomial.resultant R (cyclotomic (2 ^ m) ℤ) ≠ 0 :=
    resultant_int_ne_zero_of_isCoprime_rat _ _ (diff_coprime_cyclotomic_rat hm R hdeg hR0)
  -- size contradiction against the archimedean bound
  have hle : p ≤ (Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs := by
    have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (by simpa using h2)
  have hub := natAbs_resultant_cyclotomic_le hm R hdeg
  omega

/-! ### Signed sum-polynomials -/

/-- The signed sum-polynomial of a pair `T ⊆ U`:
`P_{U,T} = ∑_{i ∈ T} X^i − ∑_{i ∈ U∖T} X^i` — equation (1) of [KKH26], with `T` the positive
support and `U ∖ T` the negative support. -/
noncomputable def sumPoly (U T : Finset ℕ) : Polynomial ℤ :=
  ∑ i ∈ T, X ^ i - ∑ i ∈ U \ T, X ^ i

lemma coeff_sum_X_pow (T : Finset ℕ) (k : ℕ) :
    (∑ i ∈ T, (X : Polynomial ℤ) ^ i).coeff k = if k ∈ T then 1 else 0 := by
  classical
  rw [finset_sum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq T k (fun _ => (1 : ℤ))]

lemma sumPoly_coeff (U T : Finset ℕ) (k : ℕ) :
    (sumPoly U T).coeff k
      = (if k ∈ T then 1 else 0) - (if k ∈ U \ T then 1 else 0) := by
  rw [sumPoly, coeff_sub, coeff_sum_X_pow, coeff_sum_X_pow]

lemma sumPoly_coeff_eq_one_iff (U T : Finset ℕ) (k : ℕ) :
    (sumPoly U T).coeff k = 1 ↔ k ∈ T := by
  rw [sumPoly_coeff]
  by_cases h1 : k ∈ T
  · have h2 : k ∉ U \ T := fun hc => (mem_sdiff.mp hc).2 h1
    simp [h1, h2]
  · by_cases h2 : k ∈ U \ T <;> simp [h1, h2]

lemma sumPoly_coeff_eq_neg_one_iff (U T : Finset ℕ) (k : ℕ) :
    (sumPoly U T).coeff k = -1 ↔ k ∈ U \ T := by
  rw [sumPoly_coeff]
  by_cases h1 : k ∈ T
  · have h2 : k ∉ U \ T := fun hc => (mem_sdiff.mp hc).2 h1
    simp [h1, h2]
  · by_cases h2 : k ∈ U \ T <;> simp [h1, h2]

/-- Distinct `(U, T)`-data give distinct sum-polynomials. -/
lemma sumPoly_inj {U₁ T₁ U₂ T₂ : Finset ℕ} (hT₁ : T₁ ⊆ U₁) (hT₂ : T₂ ⊆ U₂)
    (h : sumPoly U₁ T₁ = sumPoly U₂ T₂) : U₁ = U₂ ∧ T₁ = T₂ := by
  have hT : T₁ = T₂ := by
    ext k
    rw [← sumPoly_coeff_eq_one_iff U₁ T₁ k, ← sumPoly_coeff_eq_one_iff U₂ T₂ k, h]
  have hD : U₁ \ T₁ = U₂ \ T₂ := by
    ext k
    rw [← sumPoly_coeff_eq_neg_one_iff U₁ T₁ k, ← sumPoly_coeff_eq_neg_one_iff U₂ T₂ k, h]
  refine ⟨?_, hT⟩
  rw [← Finset.union_sdiff_of_subset hT₁, ← Finset.union_sdiff_of_subset hT₂, hD, hT]

lemma sumPoly_natDegree_lt {U T : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hU : U ⊆ range n) (hT : T ⊆ U) : (sumPoly U T).natDegree < n := by
  classical
  have hdeg : (sumPoly U T).degree < (n : WithBot ℕ) := by
    rw [sumPoly]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun i hi => ?_
      exact lt_of_le_of_lt (degree_X_pow_le _)
        (WithBot.coe_lt_coe.mpr (mem_range.mp (hU (hT hi))))
    · refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun i hi => ?_
      exact lt_of_le_of_lt (degree_X_pow_le _)
        (WithBot.coe_lt_coe.mpr (mem_range.mp (hU (mem_sdiff.mp hi).1)))
  by_cases h0 : sumPoly U T = 0
  · rw [h0]; simpa using hn
  · rwa [natDegree_lt_iff_degree_lt h0]

/-- The window ℓ¹-norm of a sum-polynomial is exactly `|U|` (its number of `±1` terms). -/
lemma l1On_sumPoly {U T : Finset ℕ} {n : ℕ} (hU : U ⊆ range n) (hT : T ⊆ U) :
    l1On n (sumPoly U T) = U.card := by
  classical
  unfold l1On
  have hpt : ∀ j ∈ range n, ((sumPoly U T).coeff j).natAbs = if j ∈ U then 1 else 0 := by
    intro j _
    rw [sumPoly_coeff]
    by_cases hjT : j ∈ T
    · have hjU : j ∈ U := hT hjT
      have hjD : j ∉ U \ T := fun hc => (mem_sdiff.mp hc).2 hjT
      simp [hjT, hjU, hjD]
    · by_cases hjU : j ∈ U
      · have hjD : j ∈ U \ T := mem_sdiff.mpr ⟨hjU, hjT⟩
        simp [hjT, hjU, hjD]
      · have hjD : j ∉ U \ T := fun hc => hjU (mem_sdiff.mp hc).1
        simp [hjT, hjU, hjD]
  rw [Finset.sum_congr rfl hpt, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.inter_eq_right.mpr hU]

/-- The window squared ℓ²-norm of a signed sum-polynomial is exactly `|U|`, since every
nonzero coefficient is `±1`. -/
lemma l2SqOn_sumPoly {U T : Finset ℕ} {n : ℕ} (hU : U ⊆ range n) (hT : T ⊆ U) :
    l2SqOn n (sumPoly U T) = U.card := by
  classical
  unfold l2SqOn
  have hpt : ∀ j ∈ range n, ((sumPoly U T).coeff j).natAbs ^ 2
      = if j ∈ U then 1 else 0 := by
    intro j _
    rw [sumPoly_coeff]
    by_cases hjT : j ∈ T
    · have hjU : j ∈ U := hT hjT
      have hjD : j ∉ U \ T := fun hc => (mem_sdiff.mp hc).2 hjT
      simp [hjT, hjU, hjD]
    · by_cases hjU : j ∈ U
      · have hjD : j ∈ U \ T := mem_sdiff.mpr ⟨hjU, hjT⟩
        simp [hjT, hjU, hjD]
      · have hjD : j ∉ U \ T := fun hc => hjU (mem_sdiff.mp hc).1
        simp [hjT, hjU, hjD]
  rw [Finset.sum_congr rfl hpt, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.inter_eq_right.mpr hU]

lemma sumPoly_map_eval {F : Type*} [CommRing F] (φ : ℤ →+* F) (g : F) (U T : Finset ℕ) :
    ((sumPoly U T).map φ).eval g = ∑ i ∈ T, g ^ i - ∑ i ∈ U \ T, g ^ i := by
  rw [sumPoly, Polynomial.map_sub, eval_sub]
  congr 1 <;>
  · rw [Polynomial.map_sum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_pow, map_X, Polynomial.eval_pow, eval_X]

/-! ### The signed-data index set and its value map -/

/-- The index set of [KKH26] equation (2): pairs `(U, T)` with `T ⊆ U ⊆ [0, n)` and
`|U| = r` — `U` is the exponent support, `T ⊆ U` the positive signs. -/
def sigData (n r : ℕ) : Finset ((_ : Finset ℕ) × Finset ℕ) :=
  (powersetCard r (range n)).sigma fun U => U.powerset

lemma mem_sigData {n r : ℕ} {d : (_ : Finset ℕ) × Finset ℕ} :
    d ∈ sigData n r ↔ (d.1 ⊆ range n ∧ d.1.card = r) ∧ d.2 ⊆ d.1 := by
  obtain ⟨U, T⟩ := d
  simp [sigData, Finset.mem_sigma, mem_powersetCard, mem_powerset]

/-- The collision polynomial has degree below the cyclotomic half-window. -/
lemma collisionPoly_natDegree_lt {m r : ℕ} (_hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r) :
    (sumPoly d₁.1 d₁.2 - sumPoly d₂.1 d₂.2).natDegree < 2 ^ (m - 1) := by
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, _⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, _⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
    (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))

/-- A collision polynomial `P_{d₁} - P_{d₂}` has squared coefficient-`ℓ²` norm at most
`4r`.  This is the finite coefficient brick needed before applying any Landau/Hadamard
resultant envelope. -/
lemma l2SqOn_collisionPoly_le_four_r {m r : ℕ} {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r) :
    l2SqOn (2 ^ (m - 1)) (sumPoly d₁.1 d₁.2 - sumPoly d₂.1 d₂.2) ≤ 4 * r := by
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have h := l2SqOn_sub_le (2 ^ (m - 1)) (sumPoly U₁ T₁) (sumPoly U₂ T₂)
  rw [l2SqOn_sumPoly hU₁ hT₁, l2SqOn_sumPoly hU₂ hT₂, hc₁, hc₂] at h
  calc
    l2SqOn (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ≤ 2 * r + 2 * r := h
    _ = 4 * r := by ring

/-- If `r` is inside the KKH26 half-window, the collision-polynomial squared `ℓ²` norm is
bounded by `4·2^(m-1)`, the coefficient-side input of the proposed Landau envelope. -/
lemma l2SqOn_collisionPoly_le_four_window {m r : ℕ}
    (hr : r ≤ 2 ^ (m - 1)) {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r) :
    l2SqOn (2 ^ (m - 1)) (sumPoly d₁.1 d₁.2 - sumPoly d₂.1 d₂.2)
      ≤ 4 * 2 ^ (m - 1) := by
  exact le_trans (l2SqOn_collisionPoly_le_four_r hd₁ hd₂) (Nat.mul_le_mul_left 4 hr)

/-- There are exactly `2^r · n.choose r` signed data. -/
lemma card_sigData (n r : ℕ) : (sigData n r).card = 2 ^ r * n.choose r := by
  classical
  rw [sigData, Finset.card_sigma]
  have h : ∀ U ∈ powersetCard r (range n), U.powerset.card = 2 ^ r := by
    intro U hU
    rw [card_powerset, (mem_powersetCard.mp hU).2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, card_powersetCard, card_range,
    mul_comm]

/-- The signed sum value `∑_{i ∈ T} g^i − ∑_{i ∈ U∖T} g^i` of a signed datum. -/
def sVal {F : Type*} [CommRing F] (g : F) (d : (_ : Finset ℕ) × Finset ℕ) : F :=
  ∑ i ∈ d.2, g ^ i - ∑ i ∈ d.1 \ d.2, g ^ i

lemma sVal_eq_eval {F : Type*} [CommRing F] (g : F) (U T : Finset ℕ) :
    sVal g ⟨U, T⟩ = ((sumPoly U T).map (Int.castRingHom F)).eval g := by
  rw [sumPoly_map_eval]; rfl

/-- **Injectivity of signed sums at a primitive root** ([KKH26] Lemma 1, main step).
Above the explicit threshold `p > (2^m)^{2^{m-1}} = s^{s/2}`, distinct signed data give
distinct values. -/
theorem sVal_injOn {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    (hp : ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) < p) {r : ℕ} (hr : r ≤ 2 ^ (m - 1)) :
    Set.InjOn (sVal g) (sigData (2 ^ (m - 1)) r) := by
  classical
  intro d₁ hd₁ d₂ hd₂ heq
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  by_cases hR : sumPoly U₁ T₁ - sumPoly U₂ T₂ = 0
  · obtain ⟨hU, hT⟩ := sumPoly_inj hT₁ hT₂ (sub_eq_zero.mp hR)
    subst hU; subst hT; rfl
  · exfalso
    -- the collision polynomial has `g` as a root
    have hroot : ((sumPoly U₁ T₁ - sumPoly U₂ T₂).map
        (Int.castRingHom (ZMod p))).IsRoot g := by
      rw [IsRoot.def, Polynomial.map_sub, eval_sub, sub_eq_zero,
        ← sVal_eq_eval g U₁ T₁, ← sVal_eq_eval g U₂ T₂]
      exact heq
    -- degree and ℓ¹ bookkeeping
    have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
        (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
    have hl1 : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ≤ 2 * r := by
      have h := l1On_sub_le (2 ^ (m - 1)) (sumPoly U₁ T₁) (sumPoly U₂ T₂)
      rw [l1On_sumPoly hU₁ hT₁, l1On_sumPoly hU₂ hT₂, hc₁, hc₂] at h
      omega
    have h2r : 2 * r ≤ 2 ^ m := by
      have hsum : 2 ^ (m - 1) * 2 = 2 ^ m := by
        rw [← pow_succ, Nat.sub_add_cancel hm]
      omega
    have hpow : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ^ 2 ^ (m - 1)
        < p :=
      lt_of_le_of_lt (Nat.pow_le_pow_left (le_trans hl1 h2r) _) hp
    exact not_isRoot_of_l1On_pow_lt hm hg hR hdegR hpow hroot

/-! ### From signed data to sums of distinct subgroup elements -/

/-- The `r`-element subset of `⟨g⟩` realizing a signed datum: positive signs use `g^i`,
negative signs use `−g^i = g^{i + 2^{m-1}}`. -/
def elemSet {p : ℕ} (g : ZMod p) (half : ℕ) (d : (_ : Finset ℕ) × Finset ℕ) :
    Finset (ZMod p) :=
  d.2.image (fun i => g ^ i) ∪ (d.1 \ d.2).image (fun i => g ^ (i + half))

/-- `g^{2^{m-1}} = −1` for a primitive `2^m`-th root of unity in a prime field. -/
lemma pow_half_eq_neg_one {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) : g ^ (2 ^ (m - 1)) = -1 := by
  have hsum : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  have h2 : g ^ (2 ^ (m - 1)) * g ^ (2 ^ (m - 1)) = 1 := by
    rw [← pow_add, hsum, hg.pow_eq_one]
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exact absurd h (hg.pow_ne_one_of_pos_of_lt (by positivity)
      (Nat.pow_lt_pow_right one_lt_two (by omega)))
  · exact h

section Embed

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {g : ZMod p}

private lemma half_add_half {m : ℕ} (hm : 1 ≤ m) :
    2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
  have h := pow_succ 2 (m - 1)
  rw [Nat.sub_add_cancel hm] at h
  omega

private lemma half_lt_pow {m : ℕ} (hm : 1 ≤ m) : 2 ^ (m - 1) < 2 ^ m :=
  Nat.pow_lt_pow_right one_lt_two (by omega)

/-- The two image families of an `elemSet` are injective and disjoint. -/
private lemma embed_inj_disj (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    {U T : Finset ℕ} (hU : U ⊆ range (2 ^ (m - 1))) (hT : T ⊆ U) :
    Set.InjOn (fun i => g ^ i) ↑T ∧
    Set.InjOn (fun i => g ^ (i + 2 ^ (m - 1))) ↑(U \ T) ∧
    Disjoint (T.image (fun i => g ^ i))
      ((U \ T).image (fun i => g ^ (i + 2 ^ (m - 1)))) := by
  have hsum := half_add_half hm
  have hwin : ∀ i ∈ U, i < 2 ^ (m - 1) := fun i hi => mem_range.mp (hU hi)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj h
    exact hg.pow_inj
      (lt_trans (hwin i (hT hi)) (half_lt_pow hm))
      (lt_trans (hwin j (hT hj)) (half_lt_pow hm)) h
  · intro i hi j hj h
    have hi' : i ∈ U \ T := Finset.mem_coe.mp hi
    have hj' : j ∈ U \ T := Finset.mem_coe.mp hj
    have h1 := hg.pow_inj
      (by have := hwin i (mem_sdiff.mp hi').1; omega)
      (by have := hwin j (mem_sdiff.mp hj').1; omega) h
    omega
  · rw [Finset.disjoint_left]
    rintro x hx₁ hx₂
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hx₂
    have h1 := hg.pow_inj
      (by have := hwin j (mem_sdiff.mp hj).1; omega)
      (lt_trans (hwin i (hT hi)) (half_lt_pow hm)) hji
    have := hwin i (hT hi)
    omega

lemma elemSet_subset (hm : 1 ≤ m) {r : ℕ} {d : (_ : Finset ℕ) × Finset ℕ}
    (hd : d ∈ sigData (2 ^ (m - 1)) r) :
    elemSet g (2 ^ (m - 1)) d ⊆ (range (2 ^ m)).image (fun i => g ^ i) := by
  obtain ⟨⟨hU, _⟩, hT⟩ := mem_sigData.mp hd
  have hsum := half_add_half hm
  refine Finset.union_subset ?_ ?_
  · refine Finset.image_subset_iff.mpr fun i hi => Finset.mem_image.mpr ?_
    exact ⟨i, mem_range.mpr (lt_trans (mem_range.mp (hU (hT hi))) (half_lt_pow hm)), rfl⟩
  · refine Finset.image_subset_iff.mpr fun i hi => Finset.mem_image.mpr ?_
    have hilt : i < 2 ^ (m - 1) := mem_range.mp (hU (mem_sdiff.mp hi).1)
    exact ⟨i + 2 ^ (m - 1), mem_range.mpr (by omega), rfl⟩

lemma elemSet_card (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    {r : ℕ} {d : (_ : Finset ℕ) × Finset ℕ}
    (hd : d ∈ sigData (2 ^ (m - 1)) r) :
    (elemSet g (2 ^ (m - 1)) d).card = r := by
  classical
  obtain ⟨⟨hU, hc⟩, hT⟩ := mem_sigData.mp hd
  obtain ⟨hinj₁, hinj₂, hdisj⟩ := embed_inj_disj hm hg hU hT
  rw [elemSet, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn hinj₁, Finset.card_image_of_injOn hinj₂]
  have h1 : #(d.1 \ d.2) + #d.2 = #(d.1 ∪ d.2) := Finset.card_sdiff_add_card _ _
  rw [Finset.union_eq_left.mpr hT] at h1
  omega

lemma elemSet_sum (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    {r : ℕ} {d : (_ : Finset ℕ) × Finset ℕ}
    (hd : d ∈ sigData (2 ^ (m - 1)) r) :
    ∑ x ∈ elemSet g (2 ^ (m - 1)) d, x = sVal g d := by
  classical
  obtain ⟨⟨hU, hc⟩, hT⟩ := mem_sigData.mp hd
  obtain ⟨hinj₁, hinj₂, hdisj⟩ := embed_inj_disj hm hg hU hT
  rw [elemSet, Finset.sum_union hdisj, Finset.sum_image hinj₁, Finset.sum_image hinj₂]
  have hneg : ∀ j ∈ d.1 \ d.2, g ^ (j + 2 ^ (m - 1)) = -(g ^ j) := by
    intro j _
    rw [pow_add, pow_half_eq_neg_one hm hg, mul_neg, mul_one]
  rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  rfl

end Embed

/-! ### The main theorem -/

/-- **[KKH26] Lemma 1.** Let `g ∈ F_p` be a primitive `2^m`-th root of unity (so
`G = {g^i : i < 2^m}` is the multiplicative subgroup of order `s = 2^m`), and suppose
`p > s^{s/2}`.  Then for every `r ≤ s/2`, the set of sums of `r` distinct elements of `G`
has at least `2^r · (s/2).choose r` elements. -/
theorem kkh26_lemma1 {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m) {g : ZMod p}
    (hg : IsPrimitiveRoot g (2 ^ m)) (hp : ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) < p)
    {r : ℕ} (hr : r ≤ 2 ^ (m - 1)) :
    2 ^ r * (2 ^ (m - 1)).choose r ≤
      ((((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x).card := by
  classical
  have hinj : Set.InjOn (sVal g) (sigData (2 ^ (m - 1)) r) := sVal_injOn hm hg hp hr
  have hcard : ((sigData (2 ^ (m - 1)) r).image (sVal g)).card
      = 2 ^ r * (2 ^ (m - 1)).choose r := by
    rw [Finset.card_image_of_injOn hinj, card_sigData]
  have hsub : (sigData (2 ^ (m - 1)) r).image (sVal g) ⊆
      (((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨elemSet g (2 ^ (m - 1)) d, ?_, elemSet_sum hm hg hd⟩
    exact mem_powersetCard.mpr ⟨elemSet_subset hm hd, elemSet_card hm hg hd⟩
  calc 2 ^ r * (2 ^ (m - 1)).choose r
      = ((sigData (2 ^ (m - 1)) r).image (sVal g)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ### The divisibility route (issue #334, [KKH26] Lemma 2 wiring)

The size hypothesis `p > s^{s/2}` enters the chain above at exactly one point: it forces the
nonzero resultant `N = Res_ℤ(R, Φ_{2^m})` (of absolute value `≤ s^{s/2}` by
`natAbs_resultant_cyclotomic_le`) to satisfy `|N| < p`, so `p ∤ N`.  The lemmas below factor
the proof through that divisibility statement instead, so that [KKH26] Lemma 2's good prime
`p = Θ(n^β)` (supplied conditionally by `kkh26_good_prime_of_TZ` in `KKH26ThornerZaman.lean`)
can drive the same separation argument: `not_dvd_resultant_of_l1On_pow_lt` is the bridge
"size ⟹ not-dvd", `not_isRoot_of_not_dvd_resultant` is the non-vanishing core under the
divisibility hypothesis (it only needs the mild `‖R‖₁ < p` to keep the leading coefficient
alive mod `p`), `collisionResultant` names the integer family indexed by pairs of signed
data, and `sVal_injOn_of_not_dvd` / `kkh26_lemma1_of_not_dvd` are the generalized
injectivity and count.  The original statements above are untouched. -/

/-- **Size ⟹ not-dvd bridge.**  The explicit-threshold hypothesis of
`not_isRoot_of_l1On_pow_lt` already implies that `p` divides no collision resultant: the
resultant is nonzero (Loop52 pillars) and of absolute value `< p` (archimedean bound). -/
theorem not_dvd_resultant_of_l1On_pow_lt {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {R : Polynomial ℤ} (hR0 : R ≠ 0) (hdeg : R.natDegree < 2 ^ (m - 1))
    (hp : l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) < p) :
    ¬ (p : ℤ) ∣ Polynomial.resultant R (cyclotomic (2 ^ m) ℤ) := by
  intro hdvd
  have hne : Polynomial.resultant R (cyclotomic (2 ^ m) ℤ) ≠ 0 :=
    resultant_int_ne_zero_of_isCoprime_rat _ _ (diff_coprime_cyclotomic_rat hm R hdeg hR0)
  have hle : p ≤ (Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs := by
    have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (by simpa using h2)
  have hub := natAbs_resultant_cyclotomic_le hm R hdeg
  omega

/-- **Non-vanishing at a primitive root, divisibility form** (issue #334).  If `p` does not
divide `Res_ℤ(R, Φ_{2^m})` — instead of the size hypothesis `‖R‖₁^{2^{m-1}} < p` — then `R`
has no root at a primitive `2^m`-th root of unity `g ∈ F_p`.  The residual hypothesis
`‖R‖₁ < p` only keeps the leading coefficient of `R` alive mod `p` (so the Loop52 resultant
pillar applies); it is far weaker than the original threshold. -/
theorem not_isRoot_of_not_dvd_resultant {p : ℕ} [Fact p.Prime] {m : ℕ}
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {R : Polynomial ℤ} (hR0 : R ≠ 0) (hdeg : R.natDegree < 2 ^ (m - 1))
    (hl1 : l1On (2 ^ (m - 1)) R < p)
    (hndvd : ¬ (p : ℤ) ∣ Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)) :
    ¬ (R.map (Int.castRingHom (ZMod p))).IsRoot g := by
  intro hroot
  -- the leading coefficient of `R` survives mod `p`
  have hlcR : ((R.leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : (p : ℤ) ∣ R.leadingCoeff := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have hlcne : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR0
    have h1 : p ≤ R.leadingCoeff.natAbs := by
      have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
      simpa using Nat.le_of_dvd (Int.natAbs_pos.mpr hlcne) (by simpa using h2)
    have h2 : R.leadingCoeff.natAbs ≤ l1On (2 ^ (m - 1)) R :=
      natAbs_leadingCoeff_le_l1On hdeg
    omega
  -- `Φ` is monic, so its leading coefficient survives as well
  have hΦmonic : (cyclotomic (2 ^ m) ℤ).Monic := cyclotomic.monic _ ℤ
  have hlcΦ : (((cyclotomic (2 ^ m) ℤ).leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
    rw [hΦmonic.leadingCoeff]
    simp
  -- `g` is a common root of `R` and `Φ` mod `p`, so `p ∣ Res` — contradiction
  have hΦroot : ((cyclotomic (2 ^ m) ℤ).map (Int.castRingHom (ZMod p))).IsRoot g := by
    rw [map_cyclotomic_int]
    exact hg.isRoot_cyclotomic (by positivity)
  exact hndvd (prime_dvd_resultant_of_common_root R (cyclotomic (2 ^ m) ℤ)
    hlcR hlcΦ hroot hΦroot)

/-- **The collision resultant** of a pair of signed data — the integer
`N(d₁, d₂) = Res_ℤ(P_{d₁} − P_{d₂}, Φ_{2^m})` that the size route of
`not_isRoot_of_l1On_pow_lt` bounds internally, exposed as a definition so that the
[TZ24] good prime of `KKH26ThornerZaman.lean` can be required to divide none of them. -/
noncomputable def collisionResultant (m : ℕ) (d₁ d₂ : (_ : Finset ℕ) × Finset ℕ) : ℤ :=
  Polynomial.resultant (sumPoly d₁.1 d₁.2 - sumPoly d₂.1 d₂.2) (cyclotomic (2 ^ m) ℤ)

/-- The squared Landau/Hadamard-style envelope `((4h)^h) * 2^(h-1)` for a degree-`h`
cyclotomic window.  This definition is only the numerical target; proving that collision
resultants satisfy it is the remaining analytic brick. -/
def landauSqEnvelope (h : ℕ) : ℕ := (4 * h) ^ h * 2 ^ (h - 1)

/-- The analytic Landau/Hadamard squared resultant obligation for the `2^m` cyclotomic
window.  Once this is proved, the finite collision-resultant bad-side certificate follows
from coefficient bookkeeping in this file. -/
def cyclotomicLandauSqBound (m : ℕ) : Prop :=
  ∀ R : Polynomial ℤ,
    R.natDegree < 2 ^ (m - 1) →
      l2SqOn (2 ^ (m - 1)) R ≤ 4 * 2 ^ (m - 1) →
        (Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs ^ 2
          ≤ landauSqEnvelope (2 ^ (m - 1))

/-! ### Parseval + AM-GM proof of the squared cyclotomic Landau bound -/

lemma cyclotomic_two_pow_eq_X_pow_add_one {R : Type*} [CommRing R] {m : ℕ}
    (hm : 1 ≤ m) :
    cyclotomic (2 ^ m) R = X ^ (2 ^ (m - 1)) + 1 := by
  rw [show 2 ^ m = 2 ^ ((m - 1) + 1) by rw [Nat.sub_add_cancel hm]]
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := R) (p := 2) (n := m - 1)
    Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [pow_succ, add_comm]

lemma primitiveRoot_pow_half_eq_neg_one {R : Type*} [CommRing R] [IsDomain R] {h : ℕ}
    (hh : 0 < h) {ζ : R} (hζ : IsPrimitiveRoot ζ (2 * h)) : ζ ^ h = -1 := by
  have hprim2 : IsPrimitiveRoot (ζ ^ h) 2 := by
    refine hζ.pow (by positivity) ?_
    rw [mul_comm]
  exact IsPrimitiveRoot.eq_neg_one_of_two_right hprim2

lemma oddPowerFactor_term {R : Type*} [CommMonoid R] (ζ : R) (i : ℕ) :
    (ζ ^ 2) ^ i * ζ = ζ ^ (2 * i + 1) := by
  rw [← pow_mul, ← pow_succ]

lemma X_pow_add_one_eq_prod_odd_powers {R : Type*} [CommRing R] [IsDomain R]
    {h : ℕ} (hh : 0 < h) {ζ : R} (hζ : IsPrimitiveRoot ζ (2 * h)) :
    X ^ h + 1 = ∏ i ∈ Finset.range h, (X - C (ζ ^ (2 * i + 1))) := by
  have hhalf : ζ ^ h = -1 := primitiveRoot_pow_half_eq_neg_one hh hζ
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) h := by
    refine hζ.pow (by positivity) ?_
    rfl
  have hfac := X_pow_sub_C_eq_prod (R := R) (ζ := ζ ^ 2) hζ2
      (α := ζ) (a := (-1 : R)) hh hhalf
  trans ∏ i ∈ Finset.range h, (X - C ((ζ ^ 2) ^ i * ζ) : Polynomial R)
  · simpa [sub_neg_eq_add] using hfac
  · refine Finset.prod_congr rfl ?_
    intro i _hi
    rw [oddPowerFactor_term]

lemma roots_X_pow_add_one_eq_odd_powers {R : Type*} [CommRing R] [IsDomain R]
    {h : ℕ} (hh : 0 < h) {ζ : R} (hζ : IsPrimitiveRoot ζ (2 * h)) :
    (X ^ h + 1 : Polynomial R).roots =
      (Finset.range h).val.map (fun i => ζ ^ (2 * i + 1)) := by
  rw [X_pow_add_one_eq_prod_odd_powers hh hζ]
  rw [← Finset.prod_map_val]
  rw [show
      (Multiset.map (fun i => (X - C (ζ ^ (2 * i + 1)) : Polynomial R))
        (Finset.range h).val)
        = Multiset.map (fun a => (X - C a : Polynomial R))
          ((Finset.range h).val.map (fun i => ζ ^ (2 * i + 1))) by
        rw [Multiset.map_map]; rfl]
  rw [roots_multiset_prod_X_sub_C]

lemma resultant_X_pow_add_one_eq_prod_odd_powers {h : ℕ} (hh : 0 < h) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * h)) (R : Polynomial ℤ) :
    Polynomial.resultant (X ^ h + 1 : Polynomial ℂ) (R.map (Int.castRingHom ℂ)) =
      ∏ i ∈ Finset.range h, (R.map (Int.castRingHom ℂ)).eval (ζ ^ (2 * i + 1)) := by
  have hsplits : (X ^ h + 1 : Polynomial ℂ).Splits := IsAlgClosed.splits _
  have hmonic : (X ^ h + 1 : Polynomial ℂ).Monic := by
    simpa using (monic_X_pow_add_C (R := ℂ) (a := (1 : ℂ)) hh.ne')
  have hprod := Polynomial.resultant_eq_prod_eval (X ^ h + 1 : Polynomial ℂ)
      (R.map (Int.castRingHom ℂ)) (R.map (Int.castRingHom ℂ)).natDegree le_rfl hsplits
  rw [hmonic.leadingCoeff, one_pow, one_mul] at hprod
  rw [roots_X_pow_add_one_eq_odd_powers hh hζ] at hprod
  rw [hprod]
  rw [← Finset.prod_map_val]
  rw [Multiset.map_map]
  rfl

lemma inverse_odd_power_sum_eq_star {h : ℕ} {w : ℂ} (hw : ‖w‖ = 1) (c : ℕ → ℤ) :
    (∑ j ∈ Finset.range h, ((c j : ℤ) : ℂ) * (w⁻¹) ^ j) =
      star (∑ j ∈ Finset.range h, ((c j : ℤ) : ℂ) * w ^ j) := by
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [star_mul, star_pow]
  simp [Complex.inv_eq_conj hw, mul_comm]

lemma eval_map_intCast_complex_eq_sum_range {h : ℕ} {R : Polynomial ℤ}
    (hdeg : R.natDegree < h) (w : ℂ) :
    (R.map (Int.castRingHom ℂ)).eval w =
      ∑ j ∈ Finset.range h, ((R.coeff j : ℤ) : ℂ) * w ^ j := by
  have hdegC : (R.map (Int.castRingHom ℂ)).natDegree < h := by
    rwa [natDegree_map_eq_of_injective Int.cast_injective]
  rw [Polynomial.eval_eq_sum_range' hdegC]
  simp [Polynomial.coeff_map]

lemma intCast_sq_eq_natAbs_sq_complex (a : ℤ) :
    ((a : ℂ) ^ 2) = (((a.natAbs ^ 2 : ℕ) : ℂ)) := by
  have h : (a ^ 2 : ℤ) = ((a.natAbs ^ 2 : ℕ) : ℤ) := by
    simp
  rw [← Int.cast_pow]
  exact congrArg (fun z : ℤ => (z : ℂ)) h

lemma sum_coeff_sq_eq_l2SqOn_complex (h : ℕ) (R : Polynomial ℤ) :
    (∑ j ∈ Finset.range h, ((R.coeff j : ℤ) : ℂ) ^ 2) = (l2SqOn h R : ℂ) := by
  unfold l2SqOn
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [intCast_sq_eq_natAbs_sq_complex]

theorem odd_power_parseval_l2SqOn_complex {h : ℕ} (hh : 0 < h) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * h)) {R : Polynomial ℤ} (hdeg : R.natDegree < h) :
    ∑ i ∈ Finset.range h,
      ‖(R.map (Int.castRingHom ℂ)).eval (ζ ^ (2 * i + 1))‖ ^ 2 =
        (h : ℝ) * (l2SqOn h R : ℝ) := by
  have hparse := ArkLib.CharacterSums.parseval_odd_powers (F := ℂ) hh hζ
      (fun j : ℕ => ((R.coeff j : ℤ) : ℂ))
  have hcomplex :
      (∑ i ∈ Finset.range h,
        ((‖(R.map (Int.castRingHom ℂ)).eval (ζ ^ (2 * i + 1))‖ ^ 2 : ℝ) : ℂ)) =
          ((h : ℂ) * (l2SqOn h R : ℂ)) := by
    calc
      (∑ i ∈ Finset.range h,
        ((‖(R.map (Int.castRingHom ℂ)).eval (ζ ^ (2 * i + 1))‖ ^ 2 : ℝ) : ℂ))
          = ∑ i ∈ Finset.range h,
              (∑ j ∈ Finset.range h, ((R.coeff j : ℤ) : ℂ) *
                  (ζ ^ (2 * i + 1)) ^ j) *
                (∑ j ∈ Finset.range h, ((R.coeff j : ℤ) : ℂ) *
                  ((ζ ^ (2 * i + 1))⁻¹) ^ j) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              have hw : ‖ζ ^ (2 * i + 1)‖ = 1 := by
                rw [Complex.norm_pow, hζ.norm'_eq_one (by positivity), one_pow]
              rw [← eval_map_intCast_complex_eq_sum_range hdeg]
              rw [inverse_odd_power_sum_eq_star hw (fun j : ℕ => R.coeff j)]
              rw [← eval_map_intCast_complex_eq_sum_range hdeg]
              simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          _ = (h : ℂ) * ∑ j ∈ Finset.range h, ((R.coeff j : ℤ) : ℂ) ^ 2 := hparse
          _ = (h : ℂ) * (l2SqOn h R : ℂ) := by
              rw [sum_coeff_sq_eq_l2SqOn_complex]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simpa [Complex.ofReal_mul] using hcomplex

lemma finset_prod_le_average_pow {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ≤ ((∑ i ∈ s, z i) / (s.card : ℝ)) ^ s.card := by
  have hcard_pos_nat : 0 < s.card := Finset.card_pos.mpr hs
  have hcard_ne : (s.card : ℝ) ≠ 0 := by exact_mod_cast hcard_pos_nat.ne'
  have hgm := Real.geom_mean_le_arith_mean s (fun _ : ι => (1 : ℝ)) z
      (by intro i hi; positivity)
      (by simpa using (show (0 : ℝ) < s.card by exact_mod_cast hcard_pos_nat)) hz
  have hprod_nonneg : 0 ≤ ∏ i ∈ s, z i := by
    exact Finset.prod_nonneg hz
  have hgm' : (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹)
      ≤ (∑ i ∈ s, z i) / (s.card : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using hgm
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hprod_nonneg _) hgm'
      (by positivity : 0 ≤ (s.card : ℝ))
  have hleft : ((∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹)) ^ (s.card : ℝ) =
      ∏ i ∈ s, z i := by
    rw [← Real.rpow_mul hprod_nonneg, inv_mul_cancel₀ hcard_ne, Real.rpow_one]
  rw [hleft, Real.rpow_natCast] at hpow
  exact hpow

def oddEvalProductSqBound (m : ℕ) : Prop :=
  ∀ R : Polynomial ℤ,
    R.natDegree < 2 ^ (m - 1) →
      l2SqOn (2 ^ (m - 1)) R ≤ 4 * 2 ^ (m - 1) →
        ∀ ζ : ℂ, IsPrimitiveRoot ζ (2 * 2 ^ (m - 1)) →
          ‖∏ i ∈ Finset.range (2 ^ (m - 1)),
              (R.map (Int.castRingHom ℂ)).eval (ζ ^ (2 * i + 1))‖ ^ 2
            ≤ (landauSqEnvelope (2 ^ (m - 1)) : ℝ)

theorem oddEvalProductSqBound_proved (m : ℕ) : oddEvalProductSqBound m := by
  intro R hdeg hl2 ζ hζ
  set h : ℕ := 2 ^ (m - 1) with hhdef
  have hhpos : 0 < h := by rw [hhdef]; positivity
  have hs_nonempty : (Finset.range h).Nonempty := ⟨0, by simpa using hhpos⟩
  let z : ℕ → ℝ := fun i =>
    ‖(R.map (Int.castRingHom ℂ)).eval (ζ ^ (2 * i + 1))‖ ^ 2
  have hz_nonneg : ∀ i ∈ Finset.range h, 0 ≤ z i := by
    intro i _hi
    exact sq_nonneg _
  have hprod_amgm := finset_prod_le_average_pow (Finset.range h) hs_nonempty z hz_nonneg
  have hparse := odd_power_parseval_l2SqOn_complex hhpos hζ (by simpa [hhdef] using hdeg)
  have hprod_l2 : ∏ i ∈ Finset.range h, z i ≤ (l2SqOn h R : ℝ) ^ h := by
    have hhnz : (h : ℝ) ≠ 0 := by exact_mod_cast hhpos.ne'
    have havg : (h : ℝ) * ((l2SqOn h R : ℝ) * (h : ℝ)⁻¹) =
        (l2SqOn h R : ℝ) := by
      field_simp [hhnz]
    rw [hparse, Finset.card_range] at hprod_amgm
    simpa [div_eq_mul_inv, mul_assoc, havg] using hprod_amgm
  have hl2real : (l2SqOn h R : ℝ) ≤ (4 * h : ℕ) := by
    exact_mod_cast (by simpa [hhdef] using hl2)
  have hpow_l2 : (l2SqOn h R : ℝ) ^ h ≤ ((4 * h : ℕ) : ℝ) ^ h :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hl2real h
  have henvnat : (4 * h) ^ h ≤ landauSqEnvelope h := by
    unfold landauSqEnvelope
    exact Nat.le_mul_of_pos_right ((4 * h) ^ h) (Nat.two_pow_pos _)
  have henvreal : (((4 * h) ^ h : ℕ) : ℝ) ≤ (landauSqEnvelope h : ℝ) := by
    exact_mod_cast henvnat
  have hprod_env : ∏ i ∈ Finset.range h, z i ≤ (landauSqEnvelope h : ℝ) := by
    exact le_trans hprod_l2 (le_trans (by simpa using hpow_l2) henvreal)
  have hnorm_eq : ‖∏ i ∈ Finset.range h,
              (R.map (Int.castRingHom ℂ)).eval (ζ ^ (2 * i + 1))‖ ^ 2 =
      ∏ i ∈ Finset.range h, z i := by
    rw [norm_prod]
    rw [Finset.prod_pow]
  rw [hnorm_eq]
  simpa [hhdef] using hprod_env

theorem cyclotomicLandauSqBound_of_oddEvalProductSqBound {m : ℕ}
    (hm : 1 ≤ m) (hB : oddEvalProductSqBound m) : cyclotomicLandauSqBound m := by
  classical
  intro R hdeg hl2
  set ι : ℤ →+* ℂ := Int.castRingHom ℂ with hι
  have hinj : Function.Injective ι := Int.cast_injective
  set h : ℕ := 2 ^ (m - 1) with hhdef
  set Φ : Polynomial ℤ := cyclotomic (2 ^ m) ℤ with hΦdef
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 ^ m : ℕ)) with hζdef
  have hhpos : 0 < h := by rw [hhdef]; positivity
  have h2h : 2 * h = 2 ^ m := by
    rw [hhdef, mul_comm, ← pow_succ, Nat.sub_add_cancel hm]
  have hζpow : IsPrimitiveRoot ζ (2 * h) := by
    rw [h2h]
    rw [hζdef]
    exact Complex.isPrimitiveRoot_exp (2 ^ m) (by positivity)
  have hswap : (Polynomial.resultant R Φ).natAbs = (Polynomial.resultant Φ R).natAbs := by
    rw [Polynomial.resultant_comm, Int.natAbs_mul, Int.natAbs_pow]
    simp
  have hdegΦ : (Φ.map ι).natDegree = Φ.natDegree :=
    natDegree_map_eq_of_injective hinj _
  have hdegR : (R.map ι).natDegree = R.natDegree :=
    natDegree_map_eq_of_injective hinj _
  have hmap : Polynomial.resultant (Φ.map ι) (R.map ι) = ι (Polynomial.resultant Φ R) := by
    rw [show Polynomial.resultant (Φ.map ι) (R.map ι)
          = Polynomial.resultant (Φ.map ι) (R.map ι) Φ.natDegree R.natDegree by
        rw [hdegΦ, hdegR],
      Polynomial.resultant_map_map]
  have hΦC : Φ.map ι = cyclotomic (2 ^ m) ℂ := map_cyclotomic_int _ ℂ
  have hΦX : Φ.map ι = (X ^ h + 1 : Polynomial ℂ) := by
    rw [hΦC, cyclotomic_two_pow_eq_X_pow_add_one (R := ℂ) hm, hhdef]
  have hprod : Polynomial.resultant (Φ.map ι) (R.map ι) =
      ∏ i ∈ Finset.range h, (R.map ι).eval (ζ ^ (2 * i + 1)) := by
    rw [hΦX]
    exact resultant_X_pow_add_one_eq_prod_odd_powers hhpos hζpow R
  have hbound := hB R (by simpa [hhdef] using hdeg) (by simpa [hhdef] using hl2) ζ hζpow
  have hnorm : ‖(ι (Polynomial.resultant Φ R) : ℂ)‖ ^ 2 ≤
      (landauSqEnvelope h : ℝ) := by
    rw [← hmap, hprod]
    simpa [hhdef] using hbound
  have hcast : ‖(ι (Polynomial.resultant Φ R) : ℂ)‖ =
      ((Polynomial.resultant Φ R).natAbs : ℝ) := by
    rw [show (ι (Polynomial.resultant Φ R) : ℂ)
          = ((Polynomial.resultant Φ R : ℤ) : ℂ) from rfl]
    rw [Complex.norm_intCast, Nat.cast_natAbs]
    exact Int.cast_abs.symm
  rw [hswap]
  have hreal : (((Polynomial.resultant Φ R).natAbs ^ 2 : ℕ) : ℝ) ≤
      (landauSqEnvelope h : ℝ) := by
    rw [Nat.cast_pow, ← hcast]
    exact hnorm
  exact_mod_cast hreal

theorem cyclotomicLandauSqBound_proved {m : ℕ} (hm : 1 ≤ m) :
    cyclotomicLandauSqBound m :=
  cyclotomicLandauSqBound_of_oddEvalProductSqBound hm (oddEvalProductSqBound_proved m)

/-- Collision resultants of *distinct* signed data are nonzero (char-0 distinctness of
sum-polynomials + irreducibility of `Φ_{2^m}` over `ℚ`, the Loop52 pillars). -/
theorem collisionResultant_ne_zero {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hne : d₁ ≠ d₂) : collisionResultant m d₁ d₂ ≠ 0 := by
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, _⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, _⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  have hR0 : sumPoly U₁ T₁ - sumPoly U₂ T₂ ≠ 0 := by
    intro h0
    obtain ⟨hU, hT⟩ := sumPoly_inj hT₁ hT₂ (sub_eq_zero.mp h0)
    subst hU; subst hT
    exact hne rfl
  have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  exact resultant_int_ne_zero_of_isCoprime_rat _ _
    (diff_coprime_cyclotomic_rat hm _ hdegR hR0)

/-- Collision resultants are bounded by `s^{s/2} = (2^m)^{2^{m-1}}` in absolute value
(the archimedean bound applied to the difference polynomial, whose window ℓ¹-norm is
`≤ 2r ≤ 2^m`). -/
theorem natAbs_collisionResultant_le {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hr : r ≤ 2 ^ (m - 1)) :
    (collisionResultant m d₁ d₂).natAbs ≤ ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) := by
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  have hl1 : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ≤ 2 * r := by
    have h := l1On_sub_le (2 ^ (m - 1)) (sumPoly U₁ T₁) (sumPoly U₂ T₂)
    rw [l1On_sumPoly hU₁ hT₁, l1On_sumPoly hU₂ hT₂, hc₁, hc₂] at h
    omega
  have h2r : 2 * r ≤ 2 ^ m := by
    have hsum : 2 ^ (m - 1) * 2 = 2 ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    omega
  have hub := natAbs_resultant_cyclotomic_le hm (sumPoly U₁ T₁ - sumPoly U₂ T₂) hdegR
  exact le_trans hub (Nat.pow_le_pow_left (le_trans hl1 h2r) _)

/-- The old explicit-threshold hypothesis implies the new divisibility hypothesis: above
`p > s^{s/2}` no collision resultant can be divisible by `p` (it is nonzero of absolute
value `≤ s^{s/2} < p`).  Hence the size route is a special case of the dvd route. -/
theorem not_dvd_collisionResultant_of_lt {p : ℕ} [Fact p.Prime] {m r : ℕ} (hm : 1 ≤ m)
    (hp : ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) < p) (hr : r ≤ 2 ^ (m - 1))
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hne : d₁ ≠ d₂) : ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro hdvd
  have h1 : p ≤ (collisionResultant m d₁ d₂).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (collisionResultant_ne_zero hm hd₁ hd₂ hne))
      (by simpa using Int.natAbs_dvd_natAbs.mpr hdvd)
  have h2 := natAbs_collisionResultant_le hm hd₁ hd₂ hr
  omega

/-- **Absolute-size handoff for the divisibility route.**  To discharge the named
`collisionResultant` nondivisibility hypothesis it is enough to prove the relevant resultant
has absolute value strictly below the prime.  This is the endpoint a sharper archimedean
bound, such as a Mahler/Landau estimate, should feed. -/
theorem not_dvd_collisionResultant_of_natAbs_lt {p : ℕ} {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hne : d₁ ≠ d₂) (hlt : (collisionResultant m d₁ d₂).natAbs < p) :
    ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro hdvd
  have hle : p ≤ (collisionResultant m d₁ d₂).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (collisionResultant_ne_zero hm hd₁ hd₂ hne))
      (by simpa using Int.natAbs_dvd_natAbs.mpr hdvd)
  omega

/-- Family version of `not_dvd_collisionResultant_of_natAbs_lt`, matching the hypothesis
shape consumed by `kkh26_lemma1_of_not_dvd`. -/
theorem collisionResultant_not_dvd_of_forall_natAbs_lt {p : ℕ} {m r : ℕ} (hm : 1 ≤ m)
    (hbound : ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → (collisionResultant m d₁ d₂).natAbs < p) :
    ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro d₁ hd₁ d₂ hd₂ hne
  exact not_dvd_collisionResultant_of_natAbs_lt hm hd₁ hd₂ hne
    (hbound d₁ hd₁ d₂ hd₂ hne)

/-- **Squared absolute-size handoff for the divisibility route.**  Landau/Hadamard-style
bounds often produce `|N(d₁,d₂)|² < p²`; this avoids extracting a square root before
feeding the finite nondivisibility certificate. -/
theorem not_dvd_collisionResultant_of_natAbs_sq_lt {p : ℕ} {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hne : d₁ ≠ d₂) (hsq : (collisionResultant m d₁ d₂).natAbs ^ 2 < p ^ 2) :
    ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro hdvd
  have hle : p ≤ (collisionResultant m d₁ d₂).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (collisionResultant_ne_zero hm hd₁ hd₂ hne))
      (by simpa using Int.natAbs_dvd_natAbs.mpr hdvd)
  have hsq_le : p ^ 2 ≤ (collisionResultant m d₁ d₂).natAbs ^ 2 :=
    Nat.pow_le_pow_left hle 2
  exact (not_lt_of_ge hsq_le) hsq

/-- A uniform squared absolute-value envelope for all distinct collision resultants implies
the divisibility hypothesis consumed by `kkh26_lemma1_of_not_dvd`. -/
theorem collisionResultant_not_dvd_of_uniform_natAbs_sq_bound {p B : ℕ}
    {m r : ℕ} (hm : 1 ≤ m)
    (hB : ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → (collisionResultant m d₁ d₂).natAbs ^ 2 ≤ B)
    (hBp : B < p ^ 2) :
    ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro d₁ hd₁ d₂ hd₂ hne
  exact not_dvd_collisionResultant_of_natAbs_sq_lt (p := p) (m := m) (r := r) hm
    hd₁ hd₂ hne (lt_of_le_of_lt (hB d₁ hd₁ d₂ hd₂ hne) hBp)

/-- A proved cyclotomic Landau squared bound immediately bounds every collision resultant in
the KKH26 half-window. -/
theorem collisionResultant_natAbs_sq_le_of_cyclotomicLandauSqBound {m r : ℕ}
    (hL : cyclotomicLandauSqBound m) (hm : 1 ≤ m) (hr : r ≤ 2 ^ (m - 1))
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r) :
    (collisionResultant m d₁ d₂).natAbs ^ 2 ≤ landauSqEnvelope (2 ^ (m - 1)) := by
  unfold collisionResultant
  exact hL (sumPoly d₁.1 d₁.2 - sumPoly d₂.1 d₂.2)
    (collisionPoly_natDegree_lt hm hd₁ hd₂)
    (l2SqOn_collisionPoly_le_four_window hr hd₁ hd₂)

/-- A proved cyclotomic Landau squared bound plus `landauSqEnvelope < p²` supplies the
finite no-divisibility certificate consumed by `kkh26_lemma1_of_not_dvd`. -/
theorem collisionResultant_not_dvd_of_cyclotomicLandauSqBound {p : ℕ}
    {m r : ℕ} (hL : cyclotomicLandauSqBound m) (hm : 1 ≤ m) (hr : r ≤ 2 ^ (m - 1))
    (hBp : landauSqEnvelope (2 ^ (m - 1)) < p ^ 2) :
    ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  refine collisionResultant_not_dvd_of_uniform_natAbs_sq_bound (p := p)
    (B := landauSqEnvelope (2 ^ (m - 1))) hm ?_ hBp
  intro d₁ hd₁ d₂ hd₂ _hne
  exact collisionResultant_natAbs_sq_le_of_cyclotomicLandauSqBound hL hm hr hd₁ hd₂

/-- **Injectivity of signed sums, divisibility form** (issue #334).  If `p > 2^m` and `p`
divides no collision resultant of distinct signed data, then distinct signed data give
distinct values at the primitive root — the conclusion of `sVal_injOn` without the
superpolynomial threshold `p > s^{s/2}`. -/
theorem sVal_injOn_of_not_dvd {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    (hpl : (2 : ℕ) ^ m < p) {r : ℕ} (hr : r ≤ 2 ^ (m - 1))
    (hndvd : ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂) :
    Set.InjOn (sVal g) (sigData (2 ^ (m - 1)) r) := by
  classical
  intro d₁ hd₁ d₂ hd₂ heq
  by_contra hne
  have hnd : ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := hndvd d₁ hd₁ d₂ hd₂ hne
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  have hR0 : sumPoly U₁ T₁ - sumPoly U₂ T₂ ≠ 0 := by
    intro h0
    obtain ⟨hU, hT⟩ := sumPoly_inj hT₁ hT₂ (sub_eq_zero.mp h0)
    subst hU; subst hT
    exact hne rfl
  -- the collision polynomial has `g` as a root
  have hroot : ((sumPoly U₁ T₁ - sumPoly U₂ T₂).map
      (Int.castRingHom (ZMod p))).IsRoot g := by
    rw [IsRoot.def, Polynomial.map_sub, eval_sub, sub_eq_zero,
      ← sVal_eq_eval g U₁ T₁, ← sVal_eq_eval g U₂ T₂]
    exact heq
  -- degree and ℓ¹ bookkeeping
  have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  have hl1 : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ≤ 2 * r := by
    have h := l1On_sub_le (2 ^ (m - 1)) (sumPoly U₁ T₁) (sumPoly U₂ T₂)
    rw [l1On_sumPoly hU₁ hT₁, l1On_sumPoly hU₂ hT₂, hc₁, hc₂] at h
    omega
  have h2r : 2 * r ≤ 2 ^ m := by
    have hsum : 2 ^ (m - 1) * 2 = 2 ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    omega
  have hl1lt : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) < p := by omega
  have hnd' : ¬ (p : ℤ) ∣ Polynomial.resultant (sumPoly U₁ T₁ - sumPoly U₂ T₂)
      (cyclotomic (2 ^ m) ℤ) := hnd
  exact not_isRoot_of_not_dvd_resultant hg hR0 hdegR hl1lt hnd' hroot

/-- **[KKH26] Lemma 1, divisibility form** (issue #334).  The count of `kkh26_lemma1` under
the hypothesis that `p > 2^m` divides no collision resultant of distinct signed data — the
form fed by the [TZ24] good prime `p = Θ(n^β)` of `kkh26_good_prime_of_TZ`
(`KKH26ThornerZaman.lean`) in place of the superpolynomial threshold `p > s^{s/2}`. -/
theorem kkh26_lemma1_of_not_dvd {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m) {g : ZMod p}
    (hg : IsPrimitiveRoot g (2 ^ m)) (hpl : (2 : ℕ) ^ m < p)
    {r : ℕ} (hr : r ≤ 2 ^ (m - 1))
    (hndvd : ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂) :
    2 ^ r * (2 ^ (m - 1)).choose r ≤
      ((((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x).card := by
  classical
  have hinj : Set.InjOn (sVal g) (sigData (2 ^ (m - 1)) r) :=
    sVal_injOn_of_not_dvd hm hg hpl hr hndvd
  have hcard : ((sigData (2 ^ (m - 1)) r).image (sVal g)).card
      = 2 ^ r * (2 ^ (m - 1)).choose r := by
    rw [Finset.card_image_of_injOn hinj, card_sigData]
  have hsub : (sigData (2 ^ (m - 1)) r).image (sVal g) ⊆
      (((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨elemSet g (2 ^ (m - 1)) d, ?_, elemSet_sum hm hg hd⟩
    exact mem_powersetCard.mpr ⟨elemSet_subset hm hd, elemSet_card hm hg hd⟩
  calc 2 ^ r * (2 ^ (m - 1)).choose r
      = ((sigData (2 ^ (m - 1)) r).image (sVal g)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.natAbs_resultant_cyclotomic_le
#print axioms ArkLib.ProximityGap.KKH26.not_isRoot_of_l1On_pow_lt
#print axioms ArkLib.ProximityGap.KKH26.sVal_injOn
#print axioms ArkLib.ProximityGap.KKH26.kkh26_lemma1
#print axioms ArkLib.ProximityGap.KKH26.l2SqOn_sub_le
#print axioms ArkLib.ProximityGap.KKH26.l2SqOn_sumPoly
#print axioms ArkLib.ProximityGap.KKH26.odd_power_parseval_l2SqOn_complex
#print axioms ArkLib.ProximityGap.KKH26.oddEvalProductSqBound_proved
#print axioms ArkLib.ProximityGap.KKH26.cyclotomicLandauSqBound_proved
#print axioms ArkLib.ProximityGap.KKH26.collisionPoly_natDegree_lt
#print axioms ArkLib.ProximityGap.KKH26.l2SqOn_collisionPoly_le_four_r
#print axioms ArkLib.ProximityGap.KKH26.l2SqOn_collisionPoly_le_four_window
#print axioms ArkLib.ProximityGap.KKH26.not_dvd_resultant_of_l1On_pow_lt
#print axioms ArkLib.ProximityGap.KKH26.not_isRoot_of_not_dvd_resultant
#print axioms ArkLib.ProximityGap.KKH26.collisionResultant_ne_zero
#print axioms ArkLib.ProximityGap.KKH26.natAbs_collisionResultant_le
#print axioms ArkLib.ProximityGap.KKH26.not_dvd_collisionResultant_of_lt
#print axioms ArkLib.ProximityGap.KKH26.not_dvd_collisionResultant_of_natAbs_lt
#print axioms ArkLib.ProximityGap.KKH26.collisionResultant_not_dvd_of_forall_natAbs_lt
#print axioms ArkLib.ProximityGap.KKH26.not_dvd_collisionResultant_of_natAbs_sq_lt
#print axioms ArkLib.ProximityGap.KKH26.collisionResultant_not_dvd_of_uniform_natAbs_sq_bound
#print axioms ArkLib.ProximityGap.KKH26.collisionResultant_natAbs_sq_le_of_cyclotomicLandauSqBound
#print axioms ArkLib.ProximityGap.KKH26.collisionResultant_not_dvd_of_cyclotomicLandauSqBound
#print axioms ArkLib.ProximityGap.KKH26.sVal_injOn_of_not_dvd
#print axioms ArkLib.ProximityGap.KKH26.kkh26_lemma1_of_not_dvd
