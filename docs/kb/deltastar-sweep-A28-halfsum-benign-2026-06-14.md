# A28 — Refined incidence-coupled Half-Sum Lemma: BENIGN (the relation does not boost the count)

**Date:** 2026-06-14 · **Actionable:** A28 (#407, merged `407-T14`) · **Type:** numerical-probe
**Status:** **PARTIAL** (char-free crux numerically proven; refined coupling question answered **BENIGN** = a clean negative)
**Artifact:** `scripts/probes/sweep_A28_halfsum.py`

---

## The question (and why the naive form was already dead)

The δ* prize reduces to bounding the per-line **bad-scalar count** of the far-line MCA event for
explicit smooth RS codes. The dual ("half-sum") view counts spurious vanishing/additive
coincidences among `μ_n` mod `p`. The **naive Half-Sum Lemma** asserted, *uniformly in n*, that a
char-`p` coincidence among the period sums — a relation holding mod `p` but **not** in char 0,
e.g. `(1/2)(η³+η⁴) = 1 + η⁶ + η⁷` at `p=17` — forces the bad-scalar count above the budget `n`.

That naive form is **DEAD** (`407-T14`): the set of primes admitting *some* char-`p` coincidence
**saturates to density ~1**, so "a coincidence exists" carries no information. This probe **first
re-confirms the saturation** (every prime tested carries between 4 and 847 such relations,
saturation fraction = `1.00`), then attacks the **refined, never-measured** question:

> Does a char-`p` half-sum relation actually **BOOST** the operational bad-scalar count past `n`,
> or is it **BENIGN** (present, but the far-line incidence stays at the generic baseline)?

---

## (S0) Char-free crux — numerically PROVEN (exact, char 0)

> **Crux.** For a multiset `S` of `n`-th roots of unity, *all* odd power sums
> `p_1 = p_3 = … = p_{n-1} = 0` (equivalently all odd elementary-symmetric functions vanish)
> **⟺** `S` is closed under negation (antipodal, `i ↦ i + n/2`).

Verified **exactly over `Z[ζ_n]`** (sympy cyclotomic-field reduction mod `Φ_n`) on **every**
index subset of `{0,…,n−1}`:

| n | subsets checked | agree (vanish ⟺ antipodal) | counterexamples |
|---|---|---|---|
| 4 | 16 | 16 | 0 |
| 6 | 64 | 64 | 0 |
| 8 | 256 | 256 | 0 |
| 12 | 4096 | 4096 | 0 |
| 16 | 39203 (size ≤ 8) | 39203 | 0 |

Zero counterexamples. The `⟸` direction is elementary (antipodal pairs `ζ^i + ζ^{i+n/2} = 0`
kill every odd power); the `⟹` direction is the substantive half (vanishing odd power sums force
negation-closure) — it holds on every tested instance and is provable elementarily by Newton's
identities restricted to the odd-graded part. This is the "all-odd-`e_i`=0 ⟹ antipodal" fact the
actionable named, now backed by exhaustive exact evidence.

---

## (S1–S3) The coupling: BENIGN, established by a decisive control

Operational setup, prize-shaped & exact over `F_q`: `C = RS[F_q, μ_n, k]`, line word
`w_γ = u0 + γ·u1`; `γ` is **bad at radius δ** if `w_γ` agrees with some codeword on
`≥ ⌈(1−δ)n⌉` coords. `n ∈ {8,16}`, `k ∈ {2,3}`, smallest primes `≡ 1 (mod n)`, full `F_p`
γ-sweep, full `p^k` codeword enumeration (numpy-vectorized).

**Radius sweep (the trap).** Sweeping the agreement threshold across the far window, the
bad-count *does* exceed `n` — but **only at the over-Johnson radius** (`agree ≥ 4` at `n=8,k=3` is
`δ ≈ 1/2`, at/beyond the Johnson radius `1−√ρ ≈ 0.39`): `max-bad = 17, 36` vs `n = 8`. This is the
**Johnson-list combinatorial blowup**, present for *every* direction, and would be mistaken for a
"boost" by a naive reading.

**Decisive control (separates relation from radius).** At fixed `(p,n,k,radius)`, compare the line
whose direction **encodes the char-`p` relation** (`u1 = `coeff vector of
`η^a+η^b − 2 − 2η^c − 2η^d`) against the distribution of bad-counts over **random far directions**:

| n | k | p | radius (agree≥) | relation-dir count | random mean | random max | z-score | rel > random max? |
|---|---|---|---|---|---|---|---|---|
| 8 | 3 | 17 | 5 | 2 | 2.6 | 6 | −0.50 | no |
| 8 | 3 | 41 | 5 | 0 | 1.3 | 3 | −1.34 | no |
| 8 | 2 | 73 | 5 | 0 | 0.0 | 1 | −0.19 | no |
| 16 | 2 | 97 | 9 | 0 | 0.0 | 0 | — | no |

The relation-direction lands **at or below the random mean** in every case (never above the
random max). Pearson `corr(relation_count, max_bad) = −0.149` (**negative**): more relations does
**not** mean more bad scalars.

**Named relation `(1/2)(η³+η⁴) = 1 + η⁶ + η⁷` at `p=17`, `μ_8 = [1,9,13,15,16,8,4,2]`:** the
relation holds (`LHS = RHS = 7`), and a line in exactly that direction has the same Johnson-driven
count as any other far direction — no excess over baseline.

---

## Verdict — BENIGN

Char-`p` half-sum relations **saturate the bad-prime ledger** (fraction = 1.00, hundreds per
prime), yet a line whose direction *encodes* the relation produces **no more** bad scalars than a
generic random direction at the same radius. The radius (Johnson blowup), not the relation, is
what drives the count above `n`. **The refined incidence-coupled Half-Sum Lemma is BENIGN: the
char-`p` relation does not boost far-line incidence.**

This is an honest **negative** that strengthens, rather than reopens, the dead-naive conclusion:
both the naive (uniform-in-`n`) and the refined (incidence-coupled) Half-Sum routes fail to feed a
super-budget far-line count. The "half-sum coincidence" lever has now been closed from both sides.

## What is NOT settled (the gap)

- Prize-shaped *small cases* only (`n ≤ 16`, smallest `≡1 (mod n)` primes; `p^k`-enumerable). The
  prize regime (`n = 2^32`, `p ~ n·2^128`) is not reachable by exhaustive enumeration — this is
  evidence, not proof. The benign behavior could in principle change at scale, though the negative
  correlation and the radius-attribution argument suggest it is structural (Johnson list size, not
  the relation, is the carrier).
- The char-free crux (S0) is proven *numerically exactly* on all small subsets but is **not
  Lean-formalized**; the Newton-identity proof of the substantive `⟹` direction is elementary and
  would make a clean future brick.
- The genuine open core (`B(μ_n) ≤ C√(n·log(q/n))`, the four equivalent forms) is **unchanged**.
  A28 only closes one tributary (the half-sum coincidence lever); it does not touch the BGK /
  specific-subgroup-faithfulness wall.

## Reproduce

```bash
python3 scripts/probes/sweep_A28_halfsum.py
# (sympy + numpy; ~2-3 min; prints S0 crux table, S1-S3 radius sweep, the decisive control, verdict)
```
