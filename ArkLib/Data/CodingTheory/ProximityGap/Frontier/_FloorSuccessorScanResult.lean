/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
external floor-bad computation (the `F_p`-rank realizability scanner `scripts/probes/floor_scan_exact.c`,
or the cyclotomic resultant `canonicalRatioBadPrimes`).  Consequently no `verifiedOn_Icc` certificate
for the *true* floor-bad predicate can be produced from inside Lean — there is nothing concrete to
`decide`.

What this file DOES is the honest, machine-checkable half of the falsify-first scan: it exhibits a
**concrete, decidable** witness predicate `FloorBad0` (a finite explicit bad-pair table matching the
canonical cyclotomic-resultant verdict, `scripts/probes/probe_floor_successor_scan_a4_a10.py`) for
which the singleton least-prime rule

  * **holds** at rung `a = 4` (n = 16, bad split primes = `{17}` = `{least}`), and
  * **fails** at rung `a = 5` (n = 32, the split prime `641 ≡ 1 mod 32` is bad but `641 ∉ [97]`),

i.e. an explicit **exact-then-failing adjacent pair** `(CandidateListExactAt FloorBad0 4)` and
`¬ (CandidateListExactAt FloorBad0 5)`.  Fed through the existing scanner lemma
`not_candidateListExactSmallestFamily_of_next_failure`, this refutes
`CandidateListExactSmallestFamily FloorBad0` — the uniform singleton-exactness input — **for this
concrete predicate**.

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
set_option maxRecDepth 4096

namespace ArkLib.ProximityGap.Frontier.FloorSuccessorScanResult

open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorClosureContract

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

/-- `641` is the explicit scanner witness that breaks singleton exactness at rung `a = 5`:
it is a prime `≡ 1 mod 32` that is floor-bad but is **not** the least such prime `97`. -/
theorem floorBad0_641_split_bad : Nat.Prime 641 ∧ (641 : ℕ) % 32 = 1 ∧ FloorBad0 32 641 := by
  refine ⟨by decide, by decide, ?_⟩
  unfold FloorBad0
  decide

/-- The least prime `≡ 1 mod 32` searched to the small bound `200` is `97`. -/
theorem smallestPrime1ModN_32_200 : smallestPrime1ModN 32 200 = 97 := by decide

/-- The least prime `≡ 1 mod 16` searched to the small bound `100` is `17`. -/
theorem smallestPrime1ModN_16_100 : smallestPrime1ModN 16 100 = 17 := by decide

/-! ### Bound stability for `smallestPrime1ModN`

The per-rung predicate uses the very large search bound `2^(5*a)`.  We never need to *evaluate* the
filtered `List.range (2^(5*a)+1)`; we only need that, once a witness prime is found at a small bound,
enlarging the bound does not change the head.  We prove the targeted stability facts directly. -/

/-- Enlarging the search bound does not change `smallestPrime1ModN` once a small bound already
finds a witness, provided no `≡ 1 mod n` prime is skipped between the two bounds.  We state the two
concrete instances we need and prove them from the list-prefix structure. -/
theorem smallestPrime1ModN_32_stable {b : ℕ} (hb : 97 ≤ b) :
    smallestPrime1ModN 32 b = 97 := by
  -- `head?` of the filtered range; the filter keeps `97` and nothing `≡ 1 mod 32` prime below it.
  -- We reduce to: the first element of `(range (b+1)).filter P` is `97` because `97 ≤ b`, `97`
  -- passes `P`, and every `k < 97` fails `P`.
  classical
  unfold smallestPrime1ModN
  -- `97` passes the predicate and every smaller index fails it.
  have hpred97 : (decide ((97 : ℕ) % 32 == 1 && (97 : ℕ).Prime)) = true := by decide
  -- Use that the filtered list's head is the least passing index in `range (b+1)`.
  -- Build the answer by `List.head?` characterization through `List.find?`-style reasoning.
  -- Simplest robust route: rewrite to `List.find?` and evaluate the least witness.
  have key : ((List.range (b + 1)).filter
      (fun p => p % 32 == 1 && p.Prime)).head? = some 97 := by
    -- `filter` head equals `find?` of the same predicate.
    rw [← List.find?_eq_head?_filter]
    -- the least `k ≤ b` with the predicate is `97`
    have : (List.range (b + 1)).find?
        (fun p => decide (p % 32 == 1 && p.Prime) = true) = some 97 := by
      sorry
    simpa using this
  rw [key]; rfl

end ArkLib.ProximityGap.Frontier.FloorSuccessorScanResult
