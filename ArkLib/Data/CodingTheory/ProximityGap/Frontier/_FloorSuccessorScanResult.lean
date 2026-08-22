/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AssaultV2_FloorLocalizationN32
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorClosureContract

/-!
# LANE A3 — falsify-first successor scan result for the floor-localization route

## What this file is (and is NOT)

`FloorClosureSuccessorScanner.lean` / `_FloorClosureContract.lean` build the *generic logic* of a
finite-rung successor scan over the per-rung predicate

  `CandidateListExactAt FloorBad a := CandidateListExactInAP FloorBad (2^a)
       [smallestPrime1ModN (2^a) (2^(5*a))]`.

That predicate is parametrized by an **abstract** `FloorBad : ℕ → ℕ → Prop`; it is **not a concrete
decidable predicate inside Lean**.  Its truth value at a concrete rung is decided only by the
external floor-bad computation (the `F_p`-rank realizability scanner
`scripts/probes/floor_scan_exact.c`, or the cyclotomic resultant `canonicalRatioBadPrimes`).
Consequently no `verifiedOn_Icc` certificate for the *true* floor-bad predicate can be produced from
inside Lean — there is nothing concrete to `decide`.

What this file DOES is the honest, machine-checkable half of the falsify-first scan: it exhibits a
**concrete, decidable** witness predicate `FloorBad0` (a finite explicit bad-pair table matching the
canonical cyclotomic-resultant verdict, `scripts/probes/probe_floor_successor_scan_a4_a10.py`) for
which the singleton least-prime rule

  * **holds** at rung `a = 4` (n = 16, bad split primes = `{17}` = `{least}`), and
  * **fails** at rung `a = 5` (n = 32, the split primes `97` and `641`, both `≡ 1 mod 32` and both
    bad, cannot both equal the single candidate),

i.e. an explicit **exact-then-failing adjacent pair** `(CandidateListExactAt FloorBad0 4)` and
`¬ (CandidateListExactAt FloorBad0 5)`.  Fed through the existing scanner lemma
`not_candidateListExactSmallestFamily_of_next_failure`, this refutes
`CandidateListExactSmallestFamily FloorBad0` — the uniform singleton-exactness input — **for this
concrete predicate**.

The `a = 5` refutation is *bound-agnostic*: it never evaluates the giant search
`smallestPrime1ModN 32 (2^25)`.  Two distinct bad split primes `97 ≠ 641` cannot both equal the one
candidate, whatever that candidate is.

## The honest caveat (why this does NOT pin δ* and does NOT close anything)

`FloorBad0` is the **canonical cyclotomic-resultant** floor-bad predicate, which is a *superset* of
the **adjacent-realizability** floor-bad predicate that the prize-facing lane actually consumes (the
resultant counts every prime dividing `Res(Φ_n, (X^4+1)^n-(X^2+1)^n)`, including primes whose shared
root is not a primitive `n`-th root and hence not realizability-bad).  Under the realizability
predicate the in-tree full scan reports `{97}` only at `n=32` (`193,257,353,449,577,673` GOOD), so
the singleton rule is **not** refuted there at `a=4→5`; that uniform step stays genuinely **open**.

So this file is a **predicate-specific refutation / no-go**, not a refutation of the floor route
itself and certainly not a δ* pin.  Its value: it shows the abstract finite-rung successor scan is
*genuinely refutable by a concrete decidable predicate* (the canonical resultant), so any proof of
`CandidateListExactSuccessor` for the *realizability* predicate must use realizability-specific
content — the resultant superset alone breaks the rule already at `a=5`.  It also demonstrates the
scanner plumbing is faithful (it accepts a concrete counterexample end-to-end).

This is OFF-WALL substrate bookkeeping: it does NOT touch the BGK/Paley `δ*` core.

NO `sorry`/`native_decide`; axiom audit must show `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 262144

namespace ArkLib.ProximityGap.Frontier.FloorSuccessorScanResult

open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorClosureContract

/-! ### Bound stability for `smallestPrime1ModN`

We never want to evaluate `List.range (2^k + 1)` for large `k`.  The search head is stable under
enlarging the bound once a witness is already found below the smaller bound. -/

/-- If the filtered search head over `range M` is `some q`, then enlarging the range to `M + d`
keeps the same head.  Purely structural: `range (M + d)` factors as `range M ++ tail`, `filter`
distributes over `++`, and the head comes from the nonempty left part. -/
theorem filter_head?_stable
    {p : ℕ → Bool} {M d q : ℕ}
    (hhead : ((List.range M).filter p).head? = some q) :
    ((List.range (M + d)).filter p).head? = some q := by
  rw [List.range_add, List.filter_append]
  have hnon : (List.range M).filter p ≠ [] := by
    intro hnil
    rw [hnil] at hhead
    simp at hhead
  rw [List.head?_append_of_ne_nil _ hnon]
  exact hhead

/-- Bound-stability for `smallestPrime1ModN`: once a small bound `m` already yields value `q`
(with `q ≠ 0`, i.e. a genuine witness was found), every larger bound `k ≥ m` yields the same `q`. -/
theorem smallestPrime1ModN_stable
    {n m k : ℕ} (hmk : m ≤ k) {q : ℕ} (hq : q ≠ 0)
    (hsmall : smallestPrime1ModN n m = q) :
    smallestPrime1ModN n k = q := by
  unfold smallestPrime1ModN at hsmall ⊢
  -- from the `getD 0 = q` with `q ≠ 0`, the underlying `head?` is `some q`
  have hhead : ((List.range (m + 1)).filter (fun p => p % n == 1 && p.Prime)).head? = some q := by
    cases hcase : ((List.range (m + 1)).filter (fun p => p % n == 1 && p.Prime)).head? with
    | none => rw [hcase] at hsmall; simp at hsmall; exact absurd hsmall.symm hq
    | some r => rw [hcase] at hsmall; simp at hsmall; rw [hsmall]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmk
  have : k + 1 = (m + 1) + d := by omega
  have hheadk : ((List.range (k + 1)).filter (fun p => p % n == 1 && p.Prime)).head? =
      some q := by
    rw [this]
    exact filter_head?_stable hhead
  rw [hheadk]
  rfl

/-- The concrete decidable floor-bad witness predicate: the finite explicit table of canonical
cyclotomic-resultant bad split primes for `n = 16` and `n = 32`, computed by
`scripts/probes/probe_floor_successor_scan_a4_a10.py`:

* `n = 16` : bad split primes `{17}`;
* `n = 32` : bad split primes `{97, 641, 673, 1153}`.

Everything else is good.  This is a faithful concrete instantiation of the abstract `FloorBad`; it
is intentionally a *superset* model (canonical resultant), see the module caveat. -/
def FloorBad0 (n p : ℕ) : Prop :=
  (n = 16 ∧ p = 17) ∨
  (n = 32 ∧ (p = 97 ∨ p = 641 ∨ p = 673 ∨ p = 1153))

instance (n p : ℕ) : Decidable (FloorBad0 n p) := by
  unfold FloorBad0; infer_instance

/-! ### Concrete arithmetic facts (all `decide`-checkable, no `native_decide`) -/

/-- `97` is a bad split prime `≡ 1 mod 32`. -/
theorem floorBad0_97_split_bad : Nat.Prime 97 ∧ (97 : ℕ) % 32 = 1 ∧ FloorBad0 32 97 := by
  refine ⟨?_, by decide, ?_⟩
  · rw [Nat.prime_def_lt]; refine ⟨by decide, ?_⟩; decide
  · unfold FloorBad0; decide

/-- `641` is a second bad split prime `≡ 1 mod 32`, distinct from `97`. -/
theorem floorBad0_641_split_bad : Nat.Prime 641 ∧ (641 : ℕ) % 32 = 1 ∧ FloorBad0 32 641 := by
  refine ⟨?_, by decide, ?_⟩
  · rw [Nat.prime_def_lt]; refine ⟨by decide, ?_⟩; decide
  · unfold FloorBad0; decide

/-! ### Rung `a = 4` : singleton exactness HOLDS for `FloorBad0`

At `n = 16` the candidate list is `[smallestPrime1ModN 16 (2^20)]`.  The search bound `2^20` is far
beyond `17`, so we first pin the candidate value, then prove extensional exactness against the bad
set `{17}` over all split primes. -/

/-- The `n = 16` candidate value at the prize-scale search bound is `17`, derived from the small
bound `20` via bound stability (avoids evaluating `range (2^20)`). -/
theorem candidate16_eq : smallestPrime1ModN (2 ^ 4) (2 ^ (5 * 4)) = 17 :=
  smallestPrime1ModN_stable (by norm_num) (by norm_num)
    (by decide : smallestPrime1ModN (2 ^ 4) 20 = 17)

/-- **Rung a = 4 is EXACT.** For `FloorBad0`, every prime `p ≡ 1 mod 16` is floor-bad iff it equals
the single candidate `17`.  The forward direction reads off the explicit table; the reverse uses
that `17 ≡ 1 mod 16` is indeed in the table. -/
theorem candidateListExactAt_floorBad0_four : CandidateListExactAt FloorBad0 4 := by
  -- unfold to `CandidateListExactInAP FloorBad0 16 [smallestPrime1ModN 16 (2^20)]`
  show CandidateListExactInAP FloorBad0 (2 ^ 4) [smallestPrime1ModN (2 ^ 4) (2 ^ (5 * 4))]
  have hcand : smallestPrime1ModN (2 ^ 4) (2 ^ (5 * 4)) = 17 := candidate16_eq
  rw [hcand]
  intro p hp hmod
  constructor
  · intro hbad
    -- `FloorBad0 16 p` forces `p = 17`
    rcases hbad with ⟨_, hp17⟩ | ⟨hn, _⟩
    · simp [hp17]
    · exact absurd hn (by decide)
  · intro hmem
    -- `p ∈ [17]` forces `p = 17`, which is in the `n = 16` table
    have : p = 17 := by simpa using hmem
    subst this
    exact Or.inl ⟨rfl, rfl⟩

/-! ### Rung `a = 5` : singleton exactness FAILS for `FloorBad0`

Bound-agnostic: two distinct bad split primes `97 ≠ 641` cannot both equal the single candidate,
whatever value `smallestPrime1ModN 32 (2^25)` takes. -/

/-- **Rung a = 5 FAILS.** `CandidateListExactAt FloorBad0 5` is false: a singleton candidate list
cannot witness two distinct floor-bad split primes `97` and `641`. -/
theorem not_candidateListExactAt_floorBad0_five : ¬ CandidateListExactAt FloorBad0 5 := by
  -- unfold to `CandidateListExactInAP FloorBad0 32 [c]` with `c := smallestPrime1ModN 32 (2^25)`
  intro hexact
  have hex : CandidateListExactInAP FloorBad0 (2 ^ 5)
      [smallestPrime1ModN (2 ^ 5) (2 ^ (5 * 5))] := hexact
  set c := smallestPrime1ModN (2 ^ 5) (2 ^ (5 * 5)) with hc
  have h32 : (2 : ℕ) ^ 5 = 32 := by decide
  rw [h32] at hex
  obtain ⟨hp97, hmod97, hbad97⟩ := floorBad0_97_split_bad
  obtain ⟨hp641, hmod641, hbad641⟩ := floorBad0_641_split_bad
  -- exactness applied at `97` and `641` forces both to equal the singleton candidate
  have e97 : (97 : ℕ) ∈ [c] := (hex 97 hp97 hmod97).mp hbad97
  have e641 : (641 : ℕ) ∈ [c] := (hex 641 hp641 hmod641).mp hbad641
  have h97c : (97 : ℕ) = c := by simpa using e97
  have h641c : (641 : ℕ) = c := by simpa using e641
  have : (97 : ℕ) = 641 := h97c.trans h641c.symm
  exact absurd this (by decide)

/-! ### The scanner verdict : the uniform input is refuted FOR `FloorBad0` -/

/-- **The explicit exact-then-failing adjacent pair** at `a = 4 → a = 5`.  This is the concrete
scanner certificate the falsify-first lane sought (for the canonical-resultant model). -/
theorem exact_rung_four_next_five_fails :
    (4 : ℕ) ≤ 4 ∧ CandidateListExactAt FloorBad0 4 ∧ ¬ CandidateListExactAt FloorBad0 5 :=
  ⟨le_rfl, candidateListExactAt_floorBad0_four, not_candidateListExactAt_floorBad0_five⟩

/-- The successor propagation theorem `CandidateListExactSuccessor` is **false** for `FloorBad0`:
exactness at rung `4` does not propagate to rung `5`. -/
theorem not_candidateListExactSuccessor_floorBad0 :
    ¬ CandidateListExactSuccessor FloorBad0 :=
  (not_candidateListExactSuccessor_iff_exists_exact_rung_next_fails FloorBad0).mpr
    ⟨4, le_rfl, candidateListExactAt_floorBad0_four, not_candidateListExactAt_floorBad0_five⟩

/-- **Main refutation.** The uniform singleton-exactness input
`CandidateListExactSmallestFamily FloorBad0` is **false** for the concrete canonical-resultant
floor-bad model: a single least-prime candidate cannot be extensionally exact at rung `a = 5`.

This KILLS the uniform-floor-localization route *for this predicate*.  It is NOT a refutation of the
floor route for the realizability predicate, and NOT a δ* pin (see module caveat). -/
theorem not_candidateListExactSmallestFamily_floorBad0 :
    ¬ CandidateListExactSmallestFamily FloorBad0 :=
  not_candidateListExactSmallestFamily_of_next_failure FloorBad0 (a := 4) le_rfl
    not_candidateListExactAt_floorBad0_five

/-- The same verdict in the global scanner normal form: since the base rung `a = 4` IS exact, the
only way uniform exactness can fail is an adjacent exact-then-failing rung — and here that rung is
exactly `4 → 5`. -/
theorem floorBad0_failure_is_adjacent_exact_then_failing :
    CandidateListExactAt FloorBad0 4 ∧
      ∃ a : ℕ, 4 ≤ a ∧ CandidateListExactAt FloorBad0 a ∧
        ¬ CandidateListExactAt FloorBad0 (a + 1) :=
  ⟨candidateListExactAt_floorBad0_four,
    4, le_rfl, candidateListExactAt_floorBad0_four, not_candidateListExactAt_floorBad0_five⟩

#print axioms candidateListExactAt_floorBad0_four
#print axioms not_candidateListExactAt_floorBad0_five
#print axioms not_candidateListExactSuccessor_floorBad0
#print axioms not_candidateListExactSmallestFamily_floorBad0
#print axioms floorBad0_failure_is_adjacent_exact_then_failing

end ArkLib.ProximityGap.Frontier.FloorSuccessorScanResult
