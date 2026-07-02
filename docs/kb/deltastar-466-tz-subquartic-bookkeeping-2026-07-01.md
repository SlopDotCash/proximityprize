# δ\* #466 lane W2 — ThornerZamanPNT discharge status: the formalizable piece LANDED

**Date:** 2026-07-01. **File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_TZSubquarticBookkeeping.lean`
(compile-verified, axiom audit `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
**Probe:** `scripts/probes/probe_466_tz_ladder_rungs.py` → `_out_466_tz_ladder_rungs.txt`
(all 44 witness primes verified: primality, `≡ 1 (mod n)`, window membership).

## (a) The gap map: what the tree carries vs what [TZ24] delivers

Three layers, from consumer to literature:

| layer | statement | status |
|---|---|---|
| `TZPrimeSupply n β supply` (`KKH26ThornerZaman.lean`) | raw window cardinality: `#{p prime, p ≡ 1 (mod n), n^β ≤ p ≤ 2n^β} ≥ supply` | named Prop, consumed by `kkh26_mcaDeltaStar_le_of_TZ` + `tzSupplyOne_gives_prime_below_prize` |
| `ThornerZamanPNT n β ε` (`_ThornerZamanPNTStatement.lean`) | density form `(1−ε)·n^β/(φ(n)·log n^β) ≤ #window` | named Prop; PROVEN to imply the supply layer (`tzPrimeSupply_of_thornerZamanPNT`) |
| [TZ24] arXiv:2108.10878 Thm 1.1 | PNT-in-AP over `(x−h, x]` for `h ≥ x^{1−δ₁}`, `q ≤ x^{δ₂}`, `δ₁+(3/2)δ₂ ≤ 1−θ−ε`; `θ = 7/12` and coefficient `3/2 → 1` when no Siegel zero; dyadic `q = 2^a` has fixed squarefree part `d = 2` ⟹ Siegel zero eliminated beyond an absolute `a₀` (§3.1, Iwaniec) ⟹ valid for all `x ≥ q^{12/5+ε}` | mathematically CONFIRMED verbatim (kb 2026-06-27 note); **not representable in Lean as a theorem today** |

**Verdict on the remaining gap — it splits exactly in two:**

1. **PURE CITATION (not formalizable today).** Thm 1.1 itself rests on log-free
   zero-density estimates for Dirichlet `L`-functions. Mathlib has Dirichlet's theorem
   (infinitude, size-unbounded — used by `_TZDirichletUnconditional.lean`) but **no
   effective PNT-in-AP of any strength**, no zero-density technology, nothing about
   exceptional zeros. The honest in-tree form of the analytic content is and remains a
   named `Prop` + the citation. This is NOT a formalization debt one session can pay;
   it is a multi-year analytic-NT library project (PNT+ scale).
2. **DERIVABLE BOOKKEEPING (now proven, was missing).** Everything from a *faithful
   quantified form of Thm 1.1* down to the shapes the tree consumes — the
   "coefficient 3/2 → 1, x ≥ q^{12/5}" arithmetic — is conditional real/`Finset`
   arithmetic and is now landed axiom-clean (see (b)). Before this file the tree had the
   density-layer reduction (`ThornerZamanPNT ⇒ TZPrimeSupply`) but **no bridge from the
   paper's actual short-interval form to either layer**, and no least-prime chain in the
   paper's `q^{12/5+ε}` exponent shape.

## (b) What landed (`_TZSubquarticBookkeeping.lean`, all axiom-clean)

* `TZDyadicShortIntervalLB c a₀ β₀` — **the new named hypothesis**, the faithful
  Thm 1.1 form for the dyadic family: for all `a ≥ a₀`, `x ≥ (2^a)^{β₀}`,
  `h ∈ [x/2, x]`, the interval `(x−h, x]` has `≥ c·h/(φ(2^a)·log x)` primes
  `≡ 1 (mod 2^a)`. Deliberately *weaker* than the paper (restricted `h`-range, lower
  half only, `(1+o(1))` absorbed into `c`), so instantiating it from [TZ24] is sound.
  [TZ24] gives it for every fixed `β₀ > 12/5` with some `c(β₀) > 0`, `a₀(β₀)` absolute.
* `tzPrimeSupply_dyadic_of_shortIntervalLB` (+ `_natFloor`) — the headline reduction:
  the named hypothesis ⟹ `TZPrimeSupply (2^a) β supply` for every `β ≥ β₀` and every
  `supply` below the window density (specialize `x = 2·(2^a)^β`, `h = x/2`, push the
  `apPrimesIoc` count into `tzWindow`).
* `tzPrimeSupply_dyadic_beta3/beta4_of_shortIntervalLB` — the `β ∈ {3,4}` instances
  (the exponents the B3 ceiling and the floor arrow actually use).
* `exists_dyadic_prime_le_rpow_exponent` — the least-prime chain in the paper's
  exponent form: a prime `p ≡ 1 (mod 2^a)` with `p ≤ (2^a)^{β₀+ε}` for any `ε ≥ 1/a`
  (via the clean identity `2·(2^a)^β = (2^a)^{β+1/a}`). At `β₀ = 12/5+ε/2` this is
  verbatim the sub-quartic least-prime bound `≪_ε q^{12/5+ε}`.
* `exists_dyadic_prime_below_prize` — with `β₀ ≤ 3`: the prime is `≤ (2^a)^4`, the
  exact premise shape of the off-BGK floor arrow
  (`tzSupplyOne_gives_prime_below_prize`, `_FloorLinnikThornerZamanArrow.lean`) — so
  the floor arrow's supply-1 premise is now derived from the faithful Thm 1.1 form
  instead of a bare per-instance assumption.
* Side conditions are honest: every consumer carries an explicit `hsupply`/`hone`
  arithmetic condition that fails unless `c` genuinely delivers the density — the named
  hypothesis cannot be exploited vacuously.

## (c) Concrete ladder extension (unconditional)

The `n ≤ 256` rungs missing from `ThornerZamanInstance.lean` at `β ∈ {3,4}`, each by
explicit witness `Finset` + `decide`/`norm_num` (witnesses generated and re-verified by
the probe; true window counts where cheap: 2180 at (128,3), 7629 at (256,3)):

* `tzPrimeSupply_128_three : TZPrimeSupply 128 3 12`
* `tzPrimeSupply_256_three : TZPrimeSupply 256 3 12`
* `tzPrimeSupply_128_four : TZPrimeSupply 128 4 12`
* `tzPrimeSupply_256_four : TZPrimeSupply 256 4 8`

With the pre-existing β=2 ladder (8…32768) and β=3/β=4 rungs at n ≤ 64, the concrete
ladder now covers **every n ≤ 256 at every β ∈ {2,3,4}** (n=8 also has β=5).

## Honest discharge status (the one-line answer)

`ThornerZamanPNT` / `TZPrimeSupply` is **discharged down to a single named analytic
Prop** (`TZDyadicShortIntervalLB`), which is (i) mathematically TRUE by [TZ24] Thm 1.1 +
§3.1 with exponent `12/5`, confirmed verbatim from the paper, and (ii) beyond
present-day Lean formalization (no effective PNT-in-AP exists in Mathlib). The gap is
**pure citation, zero remaining derivable mathematics**: every arithmetic consequence
the tree consumes (supply instances at β ∈ {3,4}, sub-quartic least prime, below-prize
`(2^a)^4` form) is now a proven conditional theorem, and all `n ≤ 256` rungs are
unconditionally decided. This does not touch the BGK/Paley wall; per dossier §16(A)
floor-goodness is necessary-not-sufficient. **The prize core stays OPEN, ON-BGK.**

## References

[TZ24] Thorner–Zaman arXiv:2108.10878 (Thm 1.1, eq 1.8, §3.1, Cor 3.1) ·
kb `deltastar-464-thorner-zaman-subquartic-CONFIRMED-2026-06-27.md` ·
[KKH26] ePrint 2026/782 Lemma 2 · dossier v3 §6 Tier-3.
