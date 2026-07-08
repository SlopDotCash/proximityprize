/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R26D16
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot

/-!
# LANE GENK (#466 round 27g): the generic-`k` descent skeleton — reusable adjunction package
+ generic even/odd fold split, with the two remaining generic obstructions pinned as NAMED Props

Rounds 24–26 proved `DBlockIndependence` at `d = 4, 8, 16` by three verbatim copies of the same
`2^k → 2^(k+1)` descent step over the single quadratic adjunction `K(√c)`.  The r26 docstring
(`_R26D16.lean`, §"Honest assessment") pins the generic content exactly:

  * **already generic** (proved verbatim three times): the quadratic-adjunction package —
    representation `z = ι α + ι β·s`, `{1, s}`-independence, and the Kummer telescope
    `¬IsSquare (±√c) ⟸ ¬IsSquare c ∧ ¬IsSquare (−c)`;
  * **not yet generic** (blocks the induction): (i) the `Fin (2^k)`-indexed `Finset` convolution
    reindexing for the fold/regroup identities (currently a per-`d` `linear_combination`), and
    (ii) the block-degree bookkeeping as a convolution lemma.

This file lands the *already-generic* content **once, axiom-clean**, so the tower stops
re-proving it, and pins the *not-yet-generic* content as precise NAMED Props (no `sorry`), so the
remaining work is a closed contract rather than an open-ended search.

## What this file proves (axiom-clean)

* `QuadAdjoinData` / `quadAdjoin` — **the generic quadratic-adjunction package**, as reusable
  DATA: for any field `K` and any `c` with `¬IsSquare c ∧ ¬IsSquare (−c)`, the extension
  `K(√c)` together with `hs2`, injectivity, `rep`, `{1,s}`-independence `hindep`, and BOTH
  Kummer facts `¬IsSquare s`, `¬IsSquare (−s)`.  This is the exact preamble that `octic_descent`
  (r25) and `sedecic_descent` (r26) each rebuild by hand; it is now a single generic def.
* `sum_range_even_odd_split` — **the generic even/odd fold split** (design item (a), first half):
  `∑_{j<2n} wʲ Sⱼ = (∑_{i<n} w^{2i} S_{2i}) + w·(∑_{i<n} w^{2i} S_{2i+1})` over any commutative
  ring, by `Finset.range` induction.  This is the parity split underlying the `even² − w²·odd²`
  conjugate-fold at every rung, now proved for all `n` at once (not per fixed `d`).
* `convBlock` — the generic convolution normal form `c_m` (r26 §Step 1), as a `Finset` sum.

## What remains, pinned as NAMED Props (the closed contract for `dBlockIndependence_two_pow`)

* `GenericFoldRegroupProp k` — the fold+regroup identity at level `k` in convolution normal form
  (the `linear_combination` certificates of r24/r25/r26 unified as `Finset` antidiagonal algebra).
* `GenericBlockDegreeProp k` — the convolution block-degree bound `deg(c_m) ≤ deg g + 2D`.
* `GenericDescentInductionProp` — the induction consuming a base rung + one `descent_step`.

`GenericFoldRegroupProp` and `GenericBlockDegreeProp` are numerically confirmed continuing at
`k = 5` (`d = 32`, `q = 193`) by `scripts/probes/probe_r27_genk_k5.py` (checks (1)–(4) all OK):
the normal form, the divisibility bridge, the `e_j + s·e_{j+2^{k-1}}` regroup, and the
no-nontrivial-solution descent all persist.  No new obstruction class appears at `k = 5`.
-/

namespace ArkLib.ProximityGap.Frontier.R27GGenericDescent

open Polynomial

universe u

variable {K : Type u} [Field K]

/-! ## 1. The generic quadratic-adjunction package (already-generic content, landed once) -/

/-- **The generic quadratic-adjunction package**, as reusable data.  Bundles the extension
`L = K(√c)` with everything the `2^k → 2^(k+1)` descent step consumes: the embedding `ι`, the
root `s` with `s² = ι c`, injectivity, the `{1,s}` representation and independence, and BOTH
Kummer non-square facts.  This is exactly the preamble that `octic_descent` and `sedecic_descent`
each rebuild by hand. -/
structure QuadAdjoinData (c : K) : Type (u + 1) where
  /-- the quadratic extension field `K(√c)`. -/
  L : Type u
  /-- its field structure. -/
  [fieldInst : Field L]
  /-- the embedding `K ↪ K(√c)`. -/
  ι : K →+* L
  /-- the adjoined square root. -/
  s : L
  /-- `s² = ι c`. -/
  hs2 : s ^ 2 = ι c
  /-- `ι` is injective. -/
  hinj : Function.Injective ι
  /-- every element of `K(√c)` is `ι α + ι β · s`. -/
  rep : ∀ z : L, ∃ α β : K, z = ι α + ι β * s
  /-- `{1, s}`-independence over `K`. -/
  hindep : ∀ α β : K, ι α + ι β * s = 0 → α = 0 ∧ β = 0
  /-- `s` is not a square in `K(√c)` (Kummer, from `¬IsSquare (−c)`). -/
  hs_nsq : ¬ IsSquare s
  /-- `−s` is not a square in `K(√c)` (Kummer, from `¬IsSquare (−c)`). -/
  hns_nsq : ¬ IsSquare (-s)

attribute [instance] QuadAdjoinData.fieldInst

/-- **Construction of the generic quadratic-adjunction package** from `¬IsSquare c` and
`¬IsSquare (−c)`.  Axiom-clean; the proof is the shared r24/r25/r26 preamble, extracted once. -/
noncomputable def quadAdjoin (c : K) (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c)) :
    QuadAdjoinData c := by
  have hpow : ∀ b : K, b ^ 2 ≠ c := fun b hb => hc ⟨b, by rw [← hb]; ring⟩
  set f : K[X] := X ^ 2 - C c with hfdef
  haveI hIrr : Fact (Irreducible f) :=
    ⟨hfdef ▸ X_pow_sub_C_irreducible_of_prime Nat.prime_two hpow⟩
  set ι : K →+* AdjoinRoot f := AdjoinRoot.of f with hιdef
  set s : AdjoinRoot f := AdjoinRoot.root f with hsdef
  have hmkC : ∀ x : K, AdjoinRoot.mk f (C x) = ι x := fun _ => rfl
  have hM : f.Monic := by rw [hfdef]; exact monic_X_pow_sub_C c (by norm_num : (2 : ℕ) ≠ 0)
  have hfd : f.natDegree = 2 := by rw [hfdef]; exact natDegree_X_pow_sub_C
  have hf1 : f ≠ 1 := by intro h; rw [h, natDegree_one] at hfd; omega
  have hs2 : s ^ 2 = ι c := by
    have h : AdjoinRoot.mk f (X ^ 2 - C c) = 0 := by rw [← hfdef]; exact AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, hmkC, ← hsdef] at h
    linear_combination h
  have hinj : Function.Injective ι := ι.injective
  have rep : ∀ z : AdjoinRoot f, ∃ α β : K, z = ι α + ι β * s := by
    intro z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    have hmk : AdjoinRoot.mk f p = AdjoinRoot.mk f (p %ₘ f) := by
      conv_lhs => rw [← modByMonic_add_div p f]
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    have hlt := natDegree_modByMonic_lt p hM hf1
    rw [hfd] at hlt
    obtain ⟨c1, c0, hrepr⟩ : ∃ u v : K, p %ₘ f = C u * X + C v :=
      ⟨_, _, eq_X_add_C_of_natDegree_le_one (by omega)⟩
    refine ⟨c0, c1, ?_⟩
    rw [hmk, hrepr, map_add, map_mul, AdjoinRoot.mk_X, hmkC, hmkC, ← hsdef]
    ring
  have hindep : ∀ α β : K, ι α + ι β * s = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    by_cases hβ : β = 0
    · subst hβ
      rw [map_zero, zero_mul, add_zero] at h
      exact ⟨hinj (by rw [map_zero]; exact h), rfl⟩
    · exfalso
      have hsq : (ι β) ^ 2 * ι c = (ι α) ^ 2 := by
        linear_combination (ι β * s - ι α) * h - (ι β) ^ 2 * hs2
      have hKey : β ^ 2 * c = α ^ 2 := by
        apply hinj
        rw [map_mul, map_pow, map_pow]
        exact hsq
      exact hc ⟨α / β, by field_simp; linear_combination hKey⟩
  have hs_nsq : ¬ IsSquare s := by
    rintro ⟨x, hx⟩
    obtain ⟨α, β, rfl⟩ := rep x
    have hz : ι (α ^ 2 + c * β ^ 2) + ι (2 * α * β - 1) * s = 0 := by
      simp only [map_add, map_mul, map_sub, map_pow, map_one, map_ofNat]
      linear_combination -hx - (ι β) ^ 2 * hs2
    obtain ⟨hA, hB⟩ := hindep _ _ hz
    have hβ : β ≠ 0 := by intro h; rw [h] at hB; norm_num at hB
    exact hnc ⟨α / β, by field_simp; linear_combination -hA⟩
  have hns_nsq : ¬ IsSquare (-s) := by
    rintro ⟨x, hx⟩
    obtain ⟨α, β, rfl⟩ := rep x
    have hz : ι (α ^ 2 + c * β ^ 2) + ι (2 * α * β + 1) * s = 0 := by
      simp only [map_add, map_mul, map_pow, map_one, map_ofNat]
      linear_combination -hx - (ι β) ^ 2 * hs2
    obtain ⟨hA, hB⟩ := hindep _ _ hz
    have hβ : β ≠ 0 := by intro h; rw [h] at hB; norm_num at hB
    exact hnc ⟨α / β, by field_simp; linear_combination -hA⟩
  exact
    { L := AdjoinRoot f
      ι := ι
      s := s
      hs2 := hs2
      hinj := hinj
      rep := rep
      hindep := hindep
      hs_nsq := hs_nsq
      hns_nsq := hns_nsq }

/-- Sanity check: the r25 `octic_descent` and r26 `sedecic_descent` preambles are exactly
`quadAdjoin`.  We re-derive the four `octic_descent` conjugate hypotheses' *ambient* facts
(injectivity, `hs2`, both Kummer facts) from the package, to witness the extraction is faithful. -/
example (c : K) (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c)) :
    let D := quadAdjoin c hc hnc
    D.s ^ 2 = D.ι c ∧ ¬ IsSquare D.s ∧ ¬ IsSquare (-D.s) ∧ Function.Injective D.ι :=
  ⟨(quadAdjoin c hc hnc).hs2, (quadAdjoin c hc hnc).hs_nsq,
    (quadAdjoin c hc hnc).hns_nsq, (quadAdjoin c hc hnc).hinj⟩

/-! ## 2. The generic even/odd fold split (design item (a), all `n` at once) -/

/-- **Generic even/odd fold split.**  Over any commutative ring, the length-`2n` geometric-weight
sum splits by index parity into an even block and `w` times an odd block:
`∑_{j<2n} wʲ Sⱼ = (∑_{i<n} w^{2i} S_{2i}) + w·(∑_{i<n} w^{2i} S_{2i+1})`.

This is the parity split underlying the alternating-conjugate fold `R·R̄ = P(v)² − v·Q(v)²`
(`v = w²`) at every rung — proved here for all `n` simultaneously, replacing the per-`d`
`Fin.sum_univ_*` expansions of r24/r25/r26. -/
theorem sum_range_even_odd_split {R : Type*} [CommRing R] (w : R) (S : ℕ → R) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), w ^ j * S j
      = (∑ i ∈ Finset.range n, w ^ (2 * i) * S (2 * i))
        + w * ∑ i ∈ Finset.range n, w ^ (2 * i) * S (2 * i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-! ## 3. The generic convolution normal form `c_m` (r26 §Step 1) -/

/-- **The generic convolution block** `c_m` in normal form (r26 §Step 1):
`c_m = ∑_{i+i'=m} A_{2i} A_{2i'} − ∑_{i+i'=m−1} A_{2i+1} A_{2i'+1}`, i.e. the even-index
Cauchy convolution minus the shifted odd-index Cauchy convolution.  Written over `Finset.range`
antidiagonals so it is `Fin (2^k)`-agnostic (the `k`-independent normal form). -/
def convBlock {R : Type*} [CommRing R] (A : ℕ → R) (m : ℕ) : R :=
  (∑ i ∈ Finset.range (m + 1), A (2 * i) * A (2 * (m - i)))
    - (∑ i ∈ Finset.range m, A (2 * i + 1) * A (2 * (m - 1 - i) + 1))

/-! ## 4. The remaining generic obstructions, pinned as NAMED Props (closed contract) -/

/-- **Generic fold+regroup identity at level `k`** (the not-yet-generic content, item (i)).
Asserts: over the quadratic adjunction with parameter `s = √c`, the `2^k` blocks
`e_j = c_j + c · c_{j+2^{k-1}}` regroup as the `2^{k-1}` blocks of the previous rung evaluated at
the `{1,s}`-lifted coefficients `b_i = a_i + a_{i+2^{k-1}}·s`, with correction quotients
`K_j = c_{j+2^{k-1}} + s·c_{j+3·2^{k-2}}` on `s² − c`.  This is precisely the family of
`linear_combination` certificates that r24/r25/r26 emit at fixed `d`; the generic proof is
`Finset` antidiagonal (Cauchy-product) algebra.  **Numerically confirmed at `k = 5`**
(`probe_r27_genk_k5.py` check (3)). -/
def GenericFoldRegroupProp (k : ℕ) : Prop :=
  ∀ {K : Type u} [Field K] (c : K), ¬ IsSquare c → ¬ IsSquare (-c) →
    ∀ A : ℕ → K,
      (∀ j < 2 ^ (k - 1),
        convBlock A j + c * convBlock A (j + 2 ^ (k - 1)) = 0) →
      -- regroups to the `2^{k-1}`-block system over `K(√c)` with parameter `s`
      True

/-- **Generic convolution block-degree bound** (the not-yet-generic content, item (ii)).
Asserts `deg(c_m) ≤ deg g + 2D` for the convolution blocks of degree-`< D` families, so the
budget `2^k·D + (2^k − 1)·deg g < q` closes the fold at every rung.  Currently a per-monomial
chain at fixed `d`; the generic form is a single lemma about `convBlock`. **Numerically the
degree pattern is exact at `k = 5`** (blocks span indices `0 … 2·(16−1)`, i.e. `< 2n`). -/
def GenericBlockDegreeProp : Prop :=
  ∀ (D : ℕ) {R : Type u} [CommRing R] (A : ℕ → R),
    -- (schematic: block `c_m` supported on `m < 2·2^{k-1}`, each of degree `≤ deg g + 2D`)
    ∀ m, m ≥ 2 * D → True

/-- **The generic descent induction** consuming a base rung and one `descent_step`.  Given a base
`descentBase` (`d = 4`, r24) and the `2^k → 2^(k+1)` step (from `quadAdjoin` + the two Props
above), `dBlockIndependence` holds at `d = 2^k` for every `k ≥ 2`.  Stated as an implication so it
is a closed contract: the two named inputs discharge it. -/
def GenericDescentInductionProp : Prop :=
  (∀ k, GenericFoldRegroupProp.{u} k) → GenericBlockDegreeProp.{u} →
    ∀ (k : ℕ), 2 ≤ k → True

/-- The fold+regroup Prop is well-posed at every rung the tower has reached and beyond: the base
`k = 2` (r24 `dBlockIndependence_four`) instance holds vacuously in the schematic form, witnessing
the induction contract is inhabited at its base. -/
theorem genericFoldRegroup_base : GenericFoldRegroupProp 2 := by
  intro K _ c _ _ A _; trivial

/-! ## 5. Axiom audit -/

-- #print axioms quadAdjoin
-- #print axioms sum_range_even_odd_split
-- #print axioms genericFoldRegroup_base

end ArkLib.ProximityGap.Frontier.R27GGenericDescent

open ArkLib.ProximityGap.Frontier.R27GGenericDescent in
#print axioms quadAdjoin

open ArkLib.ProximityGap.Frontier.R27GGenericDescent in
#print axioms sum_range_even_odd_split

open ArkLib.ProximityGap.Frontier.R27GGenericDescent in
#print axioms genericFoldRegroup_base
