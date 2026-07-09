# delta* sweep A30 — cross-level locus-incidence lattice: does inclusion-exclusion beat the union bound? (2026-06-14)

**Actionable A30** (merged 232-T10 / 334-T23 G5). Type: numerical-probe.
**Artifact:** `scripts/probes/sweep_A30_locus_incidence.py` (deterministic, exact GF(p),
exit 0; Bonferroni-bracket hard-gated at every order; reproduces all RESULTS-INCIDENCE.md
numbers exactly).
**Verdict: PARTIAL — the deciding question is answered NEGATIVE (with proof-shaped reason);
the union-bound slack is real but Bonferroni truncation cannot capture it.**

## Context (the only surviving Conjecture-D channel)

After DISPROOF_LOG O109 (level-1 Conjecture-D slack = classical MDS, exact), O115 +
`probe_tower_level2_census.py` (the 2-adic fold tower multiplies CHOICES not CONSTRAINTS;
the level-≥2 union bound is termwise ≥ level-1), the *counting* side of the fold tower is
CLOSED. The DISPROOF_LOG conclusion is explicit: "all that survives is the
incidence/inclusion–exclusion channel over locus overlaps and the anticorrelation
structure, both genuinely open." RESULTS-INCIDENCE.md then measured the lattice and named
the open next step verbatim: *test whether Bonferroni-2 inclusion-exclusion on the
intersection lattice of the 35 fiber-subsets with the 580 B-blocks beats the union bound —
the only path to a list bound improving the trivial union bound.* A30 executes that test.

## The configuration (exact, self-contained)

Split prime `p ≡ 1 (mod 32)`; code `RS[F_p, mu_32, 16]` (deg < 16); received word
`w(x) = x^18 + lam·x^16`, `lam = -i4`. This is the canonical max-fiber / Kambiré
near-capacity (`eta = 1/16`, beyond Johnson) configuration of #232. Its proven-complete
bad list at agreement ≥ 17 is **L = 35 witnesses (agree 18) + 1344 dense (agree 17) = 1379**
(the char-0 / law-holds count; verified at BabyBear `15·2^27+1` and `3·2^30+1` via
`lane_a.py`'s exact consistency-equation generator — no kernel). The witness–dense
difference vanishes on `mu_32` exactly on `T_w ∩ T_t` (EXACTNESS THEOREM, proven), and its
level-1 dead-fiber locus is exactly `S_w ∩ B_t` over `mu_16` (dead-fiber dichotomy). So the
cross-pair incidence IS the intersection lattice of the 35 fiber-subsets `S_w` (9-subsets of
`mu_16`) against the 580 distinct B-blocks `B_t` (7-subsets).

## Hard-gated facts reproduced

- 35 × 1344 = **47,040 cross pairs**; **4,072 distinct level-1 loci**; mean multiplicity
  **11.55**, max **144** (RESULTS-INCIDENCE.md exact). Multiplicity menu concentrated at
  {2,4}, all even — echoing the B-census `488×2 + 92×4`.
- The same lattice (index-identical histograms) at both BabyBear primes — char-invariant.

## The deciding result (three forms, all exact, all Bonferroni-bracket-gated)

The Bonferroni inequalities hold EXACTLY in every form: the odd truncation (union, 1st
order) is an upper bound, the even truncation (2nd order) is a lower bound, on the true
`|union|`. This is verified as a hard gate at every order/threshold (0 violations).

**FORM C (the faithful list-cover test).** Ground set = the 1344 dense elements; covering
family = the 35 witnesses, with `cover(w) = { t : |S_w ∩ B_t| ≥ thr }`.

| thr | covered = \|union\| | U1 = Σ\|cover\| | U1/covered | IE2 = U1 − Σ\|cover∩cover\| |
|----:|----:|----:|----:|----:|
| 1 | 1344 | 47040 | **35.0×** | **−752640** |
| 2 | 1344 | 46912 | 34.9× | −748440 |
| 5 | 1344 | 16592 | 12.3× | −85864 |
| 7 |  152 |   152 | 1.0× | 152 |

At every actionable threshold **all 35 witnesses cover essentially the whole ground set**
(covered = 1344). The union bound `Σ|cover(w)|` over-counts by **exactly 35×** (the number
of witnesses) because every witness shares a nonempty locus with (almost) every dense
element. Bonferroni-2 is hugely **negative** (`−752640`) — a valid but useless lower bound,
because the pairwise overlaps `Σ|cover∩cover|` dwarf `U1` (the covers are near-**identical**,
not near-disjoint).

**FORM A (size-z0 sub-locus cover, the O97/O99 literature template).** `U1(z0) = Σ_e C(|locus_e|, z0)`,
exact `|union| = #cross pairs with |locus|≥z0`. At z0=1: U1 = 193,200 vs exact 47,040
(**4.11× slack** = the 11.55× sharing summed). IE2(z0) < 0 throughout; the order-3 odd
truncation IE3 explodes far above U1 (the C(occ,3) terms over the size-1 sub-loci dominate)
— no usable improvement.

**n=16 lower rung (list = 19 = 3 + 16).** Same phenomenon, sharper: 3 witnesses cover all 16
dense, U1 = 48 = 3×16, **IE2 = 0 exactly** (the 3-fold-redundant cover collapses to zero at
second order). The verdict is **rung-independent**.

## Why Bonferroni cannot beat the union bound here (proof-shaped)

Bonferroni's theorem is a *bracket*, not a tightening: `U1 ≥ |union| ≥ IE2` always. To
*lower the upper bound* one needs either (a) a genuine PACKING (`occ(τ)` bounded, so
`|L| ≤ COV·maxocc` with small `maxocc`), or (b) an odd-order truncation strictly below `U1`
that stays ≥ `|union|`. Form C shows **(a) fails**: the covering sets are near-identical, so
the incidence matrix is dense and the second-order correction overshoots; there is no
almost-disjoint sub-family. Form A shows **(b) fails**: the size-z0 sub-locus family makes the
higher-order terms blow up (C(occ,·) over many sub-loci), so the odd truncations diverge
above U1. The 4.11×/35× union slack is **recovered only by FULL inclusion–exclusion = the
exact count itself** — the alternating partial sums bracket, they do not converge from above.

## Honest scope / what remains open

- One word (canonical max-fiber `lam`), one radius pair (18/17), n=32 (+ n=16 rung); the
  exactness/dichotomy that make the loci `= S_w ∩ B_t` are proven only for this family.
- **NEGATIVE for the named mechanism:** low-order inclusion–exclusion on the locus lattice
  does NOT give a valid sub-union list bound. A list bound below the union bound must come
  from a PACKING / fixed-degree (Hankel/realizability, A33) or LP-fractional-cover argument
  — NOT from Bonferroni truncation. This retires the "inclusion-exclusion beats union" lever
  the way O115 retired the tower-budget-multiplication lever.
- The genuinely open residue on this channel is now the **fractional/LP cover** or
  **anticorrelation (negative-association, A25)** structure of the dense incidence matrix —
  i.e. whether the near-identical covers admit a fractional packing certificate. The Form-C
  matrix (35 × 1344, the explicit dense incidence) is the object to feed an LP next.

## Cross-links

- Direct predecessor: `scripts/probes/incidence/RESULTS-INCIDENCE.md` (H-INC3, the 11.55/144
  measurement and the named open step) and `scripts/probes/incidence/exactness/lane_a.py`
  (the exact generator reused here).
- Counting-side closure this complements: DISPROOF_LOG O109/O110/O115 and
  `scripts/probes/probe_tower_level2_census.py`.
- Adjacent live levers: A33 (realizability/Hankel — the packing lever this verdict points
  to), A25 (negative-association of incidence indicators).
