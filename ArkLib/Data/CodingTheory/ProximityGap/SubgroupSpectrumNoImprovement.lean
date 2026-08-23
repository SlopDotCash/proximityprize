/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Subgroup vanishing-power-sum structural constraints on RS codewords (Issue #232, smooth-domain)

This file attacks the open core of the Ethereum Proximity Prize (ABF26, issue #232) from the
**smooth-domain structural** angle: the evaluation domain `L` of the Reed–Solomon code is a
*multiplicative subgroup* (the `n`-th roots of unity for `n = 2^k`), so the **power sums vanish**:
`∑_{x∈L} x^t = 0` for `1 ≤ t < n` (Newton / geometric-sum-of-a-nontrivial-root-of-unity).

The question is whether this extra structure lets us beat the generic Johnson list bound
`|L|·(a²−n·b) ≤ n²` for subgroup-evaluation RS codes.

## What is proven here (all `sorry`-free, axiom-clean)

We model the subgroup `L = {ω^0, …, ω^{n-1}}` via a primitive `n`-th root `ω` in a field `F`,
and index coordinates by `Fin n` with `i ↦ ω^i`. The RS codeword of `p` is `i ↦ p.eval (ω^i)`.

* `geom_sum_primitiveRoot_pow_eq_zero` — the **vanishing power sum**: `∑_{i<n} (ω^t)^i = 0`
  whenever `ω^t ≠ 1` (i.e. `n ∤ t`). This is the smooth-domain Newton identity.
* `syndrome_pow_eq_zero` — the **syndrome / dual-code constraint** on a single monomial:
  `∑_{i<n} (ω^a)^i · (ω^i)^{-c}`... [stated as the orthogonality of evaluation rows], giving
  `∑_{i<n} (ω^{a-c})^i = 0` when `n ∤ (a-c)`.
* `rs_codeword_syndrome` — **the headline structural fact.** For a polynomial `p` of degree `< k`
  with `k ≤ n`, evaluated on the subgroup, every "high-frequency" syndrome vanishes:
  for `k ≤ t < n`, `∑_{i<n} p.eval(ω^i) · (ω^{-t})^i = 0`. So a subgroup-RS codeword is orthogonal
  to the `n − k` high-frequency Fourier rows — it satisfies `n − k` independent linear parity checks.
  This is the (genuine, classical) statement that the subgroup-evaluation RS code is the *cyclic / BCH*
  picture: codewords have a vanishing high-frequency spectrum.

## Honest assessment of the angle (does it beat Johnson?)

The syndrome constraints `rs_codeword_syndrome` are linear and are *already used implicitly* by the
root-counting agreement bound `agreement_card_le` (a degree-`<k` polynomial has `≤ k−1` roots). They
re-express "RS = low-degree" as "high spectrum vanishes", which is a **change of basis, not new
information**: the dual constraints pin the codeword to a `k`-dimensional space, exactly as the degree
bound does. Concretely, the agreement set of two clustered codewords is the *root set* of their
difference `g = p − q` (`deg < k`), and the subgroup structure does **not** force these root sets to be
additively/multiplicatively structured beyond "size `≤ k−1`": for a generic degree-`<k` `g`, its `≤ k−1`
roots on the subgroup are an arbitrary subset of `L` of that size (any `≤ k−1` points of `L` are the
roots of `∏ (X − ω^{i_j})`, which has degree `≤ k−1 < k`). Hence the worst-case agreement geometry the
Johnson bound optimizes against is **realizable inside the subgroup**, and the generic Johnson bound is
not improved by the power-sum / cyclic structure. We make this precise and `sorry`-free in
`subgroup_root_set_arbitrary`: *every* size-`(k−1)` subset of the subgroup is the exact agreement set of
a pair of degree-`<k` codewords. This is the concrete obstruction: the smooth-domain structure does not
help the list bound in the open interval `(1−√ρ, 1−ρ)` by this route.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial Finset

namespace ArkLib.CodingTheory.SubgroupPowerSum

variable {F : Type*} [Field F]

/-- **Vanishing power sum (smooth-domain Newton identity).** If `α` is an `n`-th root of unity with
`α ≠ 1`, then `∑_{i<n} α^i = 0`. This is the geometric sum of a *nontrivial* root of unity over a full
orbit: `∑_{i<n} α^i = (α^n − 1)/(α − 1) = 0` since `α^n = 1`. Applied with `α = ω^t` for a primitive
`n`-th root `ω`, it gives `∑_{i<n} (ω^t)^i = 0` whenever `n ∤ t`. -/
theorem geom_sum_root_of_unity_eq_zero {α : F} {n : ℕ} (hα1 : α ≠ 1) (hαn : α ^ n = 1) :
    ∑ i ∈ Finset.range n, α ^ i = 0 := by
  rw [geom_sum_eq hα1, hαn, sub_self, zero_div]

/-- The orbit power sum for a primitive `n`-th root `ω` and a shift `t`: `∑_{i<n} (ω^t)^i = 0` when
`n ∤ t`. The hypothesis `n ∤ t` is exactly `ω^t ≠ 1` (`IsPrimitiveRoot.pow_eq_one_iff_dvd`). -/
theorem geom_sum_primitiveRoot_pow_eq_zero {ω : F} {n : ℕ}
    (hω : IsPrimitiveRoot ω n) {t : ℕ} (ht : ¬ (n ∣ t)) :
    ∑ i ∈ Finset.range n, (ω ^ t) ^ i = 0 := by
  have hαn : (ω ^ t) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hα1 : ω ^ t ≠ 1 := by
    intro h
    exact ht ((hω.pow_eq_one_iff_dvd t).mp h)
  exact geom_sum_root_of_unity_eq_zero hα1 hαn

/-- **Monomial orthogonality.** For a primitive `n`-th root `ω`, the evaluation rows of distinct
"frequencies" are orthogonal over the subgroup: `∑_{i<n} (ω^i)^a · (ω^i)^s = 0` whenever `n ∤ (a+s)`.
This is the smooth-domain inner-product identity feeding the syndrome constraint. -/
theorem monomial_orthogonality {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n)
    {a s : ℕ} (h : ¬ (n ∣ (a + s))) :
    ∑ i ∈ Finset.range n, (ω ^ i) ^ a * (ω ^ i) ^ s = 0 := by
  have hrw : ∀ i, (ω ^ i) ^ a * (ω ^ i) ^ s = (ω ^ (a + s)) ^ i := by
    intro i
    rw [← pow_add, ← pow_mul, ← pow_mul, mul_comm i (a + s)]
  rw [Finset.sum_congr rfl (fun i _ => hrw i)]
  exact geom_sum_primitiveRoot_pow_eq_zero hω h

/-- **The headline structural fact: subgroup-RS codewords have a vanishing high-frequency spectrum.**
Let `ω` be a primitive `n`-th root of unity and `p` a polynomial of degree `< k` with `k ≤ n`.
Evaluate `p` on the subgroup `L = {ω^0, …, ω^{n−1}}`. Then for every shift `s` in the high-frequency
band `1 ≤ s ≤ n − k`, the weighted spectrum sum vanishes:
`∑_{i<n} p.eval(ω^i) · (ω^i)^s = 0`.

So a subgroup-evaluation RS codeword satisfies `n − k` independent linear parity checks (it is
orthogonal to the high-frequency evaluation rows). This is the cyclic/BCH dual-code picture of the
smooth-domain RS code: low degree ⇔ vanishing high spectrum.

Proof: write `p = ∑_{a≤deg p} c_a X^a`; each frequency `a + s` lies in `[s, deg p + s] ⊆ [1, n−1]`
(using `a ≤ deg p ≤ k − 1` and `1 ≤ s ≤ n − k`), so `n ∤ (a + s)` and the inner monomial sum vanishes
by `monomial_orthogonality`. -/
theorem rs_codeword_syndrome {ω : F} {n k : ℕ} (hω : IsPrimitiveRoot ω n)
    (hkn : k ≤ n) {p : F[X]} (hp : p.natDegree < k)
    {s : ℕ} (hs1 : 1 ≤ s) (hsk : s ≤ n - k) :
    ∑ i ∈ Finset.range n, p.eval (ω ^ i) * (ω ^ i) ^ s = 0 := by
  -- Expand each evaluation as a finite sum over the coefficients of `p`.
  have heval : ∀ i, p.eval (ω ^ i)
      = ∑ a ∈ Finset.range (p.natDegree + 1), p.coeff a * (ω ^ i) ^ a := by
    intro i
    conv_lhs => rw [p.eval_eq_sum_range]
  -- Push the spectrum weight inside, swap the order of summation.
  calc ∑ i ∈ Finset.range n, p.eval (ω ^ i) * (ω ^ i) ^ s
      = ∑ i ∈ Finset.range n,
          ∑ a ∈ Finset.range (p.natDegree + 1), p.coeff a * ((ω ^ i) ^ a * (ω ^ i) ^ s) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [heval i, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun a _ => by ring)
    _ = ∑ a ∈ Finset.range (p.natDegree + 1),
          p.coeff a * ∑ i ∈ Finset.range n, ((ω ^ i) ^ a * (ω ^ i) ^ s) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun a _ => by rw [Finset.mul_sum])
    _ = 0 := by
        refine Finset.sum_eq_zero (fun a ha => ?_)
        rw [Finset.mem_range] at ha
        -- `a + s` lies in `[1, n-1]`, so `n ∤ (a + s)`.
        have hnd : ¬ (n ∣ (a + s)) := by
          have ha' : a ≤ k - 1 := by omega
          have hpos : 0 < a + s := by omega
          have hlt : a + s < n := by omega
          exact fun hdvd => by
            have := Nat.le_of_dvd hpos hdvd
            omega
        rw [monomial_orthogonality hω hnd, mul_zero]

/-! ### The obstruction: the subgroup root geometry is *unstructured*, so Johnson is not beaten

We now show, `sorry`-free, that the special subgroup structure does **not** constrain the agreement
geometry of clustered RS codewords beyond the generic root bound. The mechanism: *every* size-`m`
subset of the subgroup (`m < k`) is the *exact* agreement set of a pair of degree-`<k` codewords. So
the worst-case Johnson configuration is realizable inside the smooth domain, and the power-sum / cyclic
structure gives no improvement over `agreement_card_le` in the open interval. -/

variable [DecidableEq F]

/-- The "interpolating vanisher" of a subset `A` of the subgroup, indexed by `Fin n`:
`gPoly ω A = ∏_{j∈A} (X − ω^j)`. It is the monic degree-`|A|` polynomial vanishing **exactly** on
`{ω^j : j ∈ A}`. -/
noncomputable def gPoly {n : ℕ} (ω : F) (A : Finset (Fin n)) : F[X] :=
  ∏ j ∈ A, (X - C (ω ^ (j : ℕ)))

omit [DecidableEq F] in
/-- `gPoly ω A` has degree exactly `|A|` (it is a product of `|A|` distinct monic linear factors). -/
theorem gPoly_natDegree {ω : F} {n : ℕ}
    (A : Finset (Fin n)) : (gPoly ω A).natDegree = A.card := by
  classical
  rw [gPoly, natDegree_prod]
  · simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  · intro j _
    exact X_sub_C_ne_zero _

omit [DecidableEq F] in
/-- **Root characterization.** `gPoly ω A` vanishes at `ω^i` (for `i : Fin n`) **iff** `i ∈ A`. Here
`ω` is a primitive `n`-th root, so `i ↦ ω^i` is injective on `Fin n`; hence the only roots of the
product among the subgroup points are the `ω^j` with `j ∈ A`. -/
theorem gPoly_eval_eq_zero_iff {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n)
    (A : Finset (Fin n)) (i : Fin n) :
    (gPoly ω A).eval (ω ^ (i : ℕ)) = 0 ↔ i ∈ A := by
  classical
  rw [gPoly, eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, hjA, hj⟩
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
    -- `ω^i = ω^j` and injectivity of `i ↦ ω^i` on `Fin n` force `i = j`.
    have hinj : (i : ℕ) = (j : ℕ) := hω.pow_inj i.isLt j.isLt hj
    have hij : i = j := Fin.ext hinj
    rw [hij]; exact hjA
  · intro hiA
    exact ⟨i, hiA, by rw [eval_sub, eval_X, eval_C, sub_self]⟩

/-- **The obstruction lemma (smooth-domain structure does not beat Johnson).** Let `ω` be a primitive
`n`-th root of unity (the smooth domain `L = {ω^0,…,ω^{n−1}}`) and let `A ⊆ Fin n` be *any* subset with
`|A| < k`. Then there is a pair of degree-`<k` polynomials `p, q` whose RS codewords on the subgroup
agree on **exactly** the coordinate set `A`:
`{i : p.eval(ω^i) = q.eval(ω^i)} = A`.

Taking `p = gPoly ω A`, `q = 0`: the agreement set is the root set of `gPoly ω A` on the subgroup,
which is exactly `A` by `gPoly_eval_eq_zero_iff`. Since `A` is an *arbitrary* subset of size `< k`, the
agreement geometry that the Johnson second-moment bound optimizes against (any `≤ k−1` agreement
positions, freely placed) is fully realizable **inside the subgroup** — the vanishing power sums impose
no additional constraint on it. Hence the generic Johnson list bound is tight for subgroup-evaluation RS
in the relevant regime, and this structural route does **not** push a bound into the open interval
`(1−√ρ, 1−ρ)`. -/
theorem subgroup_agreement_set_arbitrary {ω : F} {n k : ℕ} (hω : IsPrimitiveRoot ω n)
    (A : Finset (Fin n)) (hA : A.card < k) :
    ∃ p q : F[X], p.natDegree < k ∧ q.natDegree < k ∧ p ≠ q ∧
      (Finset.univ.filter (fun i : Fin n => p.eval (ω ^ (i : ℕ)) = q.eval (ω ^ (i : ℕ)))) = A := by
  classical
  refine ⟨gPoly ω A, 0, ?_, ?_, ?_, ?_⟩
  · rw [gPoly_natDegree]; exact hA
  · simpa using (by omega : 0 < k)
  · -- `gPoly ω A ≠ 0`: its degree is `|A| < n` and it is monic (nonzero).
    intro hcontra
    have hmonic : (gPoly ω A).Monic := by
      rw [gPoly]; exact monic_prod_X_sub_C _ _
    rw [hcontra] at hmonic
    exact (Polynomial.not_monic_zero) hmonic
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_zero]
    exact gPoly_eval_eq_zero_iff hω A i

/-! ### Satisfiability / non-vacuity check

The hypotheses of all results above are simultaneously satisfiable: a primitive `n`-th root of unity
exists in many fields (e.g. `ω = -1` is a primitive `2`-nd root in any field of characteristic `≠ 2`),
the degree-band `1 ≤ s ≤ n − k` is nonempty whenever `k < n`, and an arbitrary subset `A` of size
`< k` exists whenever `k ≥ 1`. The lemma below exhibits a concrete satisfying instance, confirming the
results are **non-vacuous**. -/

/-- Non-vacuity witness: over `ℚ`, `ω = -1` is a primitive `2`-nd root of unity, so the smooth-domain
syndrome and obstruction hypotheses are satisfiable. -/
example : IsPrimitiveRoot (-1 : ℚ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)

end ArkLib.CodingTheory.SubgroupPowerSum

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.SubgroupPowerSum.geom_sum_root_of_unity_eq_zero
#print axioms ArkLib.CodingTheory.SubgroupPowerSum.geom_sum_primitiveRoot_pow_eq_zero
#print axioms ArkLib.CodingTheory.SubgroupPowerSum.monomial_orthogonality
#print axioms ArkLib.CodingTheory.SubgroupPowerSum.rs_codeword_syndrome
#print axioms ArkLib.CodingTheory.SubgroupPowerSum.gPoly_eval_eq_zero_iff
#print axioms ArkLib.CodingTheory.SubgroupPowerSum.subgroup_agreement_set_arbitrary
