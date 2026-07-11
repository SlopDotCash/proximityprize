# δ*/#466 — SYZ39: bad-prime law and cyclotomic structure of `SylvesterInjective` (2026-07-11)

## TL;DR

SYZ38 localized the *entire* rate-`1/2` proximity-strip residual to one predicate,
`SylvesterInjective WAB WAC WBC bAC bBC`: the generalized Sylvester map of a pairwise-coprime band
triple `(W_AB, W_AC, W_BC)` over the `μ_n` domain is injective on the in-budget cofactor window.
SYZ39 characterizes that predicate's arithmetic exactly (probe:
`scripts/probes/probe_syz39_sylvester_badprime_structure.py`, pure-stdlib exact cyclotomic
computation) and lands two axiom-clean invariance lemmas
(`Frontier/_SYZ39SylvesterArithmetic.lean`).

**Bad-prime law (per fixed config).** Over `μ_n`, injectivity fails exactly at primes dividing the
char-0 obstruction `N = Res(Φ_n, Δ)`, where `Δ` is the cyclotomic-integer determinant of a maximal
minor of the Sylvester *evaluation* matrix `M[root ρ of W_AB][col] = ±W_XC(ρ)·ρ^j`. The bad primes
split cleanly:

* **ramified part = primes dividing `n`** (the discriminant/different of `ℚ(ω_n)`): *always*
  present, structural, `≤ n`. For prime `n=13`, `N` is a power of `13` in the degenerate configs
  (`N = 13^4 = 28561`). Confirmed: atomic root-difference norms `N(ω^a − ω^b) = N(ω^{a−b} − 1)`
  involve **only** primes `∣ n` — over all `a`, for `n ∈ {13,14,15,16}` the prime set is exactly
  `rad(n)`.
* **genuine field-dependent part** = a sparse set of *extra* primes not dividing `n`
  (`n=13`: `{53, 79, 103, 131, 157, 181, …}` — all `≡ 1 (mod 13)`; `n=16`: `{17, 31}`;
  `n=14`: `{13}`; `n=15`: `∅` beyond `rad(15)`). These are the true injectivity obstruction.

**Size bound.** For every fixed small `(n, k)` config, `|N|` is *tiny*: bit-length `≤ 38` (n=13,
ncols=2), `≤ 45` (ncols=3), `≤ 67` (ncols=4). The largest genuine bad prime seen through `n=16` is
`181`. So **each fixed configuration is prime-clean at the prize characteristic** (`P ≈ 2^{158} ≫`
all these): a fixed band triple can only fail `SylvesterInjective` at one of a handful of small
primes, none near `P`. This is real, concrete progress over the abstract BGK moment tower —
per-config the residual is a *decidable, bounded-height integer non-vanishing*.

**Consistency.** The `p ≡ 1 (mod n)` GF(p) rank scan (a *fixed* primitive root, as in a concrete
prize field) found **0** actual failures across 480 sampled configs — matching SYZ37's
14 908-triple 0-counterexample result. The char-0 norm's extra primes are divisibilities at a
*different* conjugate `ω^j` (a different prime above `p`) than the embedding scanned; for the natural
embedding no rate-`1/2` `μ_n` config in the sample fails. The "field-dependent flip" cited in
SYZ38 (`n=13,k=7`, `p=31`) is a **generic-domain / above-rate** phenomenon, not a `μ_n`-at-rate-`1/2`
one.

## The cyclotomic factor structure — VERDICT: it does *not* factor through cyclotomic norms

This was the hope (task 2): if `N` were a product of atomic cyclotomic quantities (root-difference
norms), the uniform statement would reduce to finitely many cyclotomic non-vanishing facts per `n`,
attackable by the in-tree cyclotomic/Lucas machinery. **The probe refutes this.**

* Atomic root-difference norms `N(ω^a − ω^b)` provably involve *only* primes dividing `n`
  (verified exactly for `n ∈ {13,14,15,16}`). Hence **any product of atomic cyclotomic norms can
  only ever produce primes in `rad(n)`.**
* But the genuine bad primes (`53, 79, 103, …, 17, 31`) do **not** divide `n`. Therefore `N` is
  **not** a product of root-difference norms. The extra primes come from the *determinant* — an
  **additive** combination (subresultant / μ-basis balance) of the cyclotomic terms — where
  characteristic-`p` cancellation among roots of unity creates primes invisible to any
  multiplicative norm.

So: the ramified part is cyclotomic-controllable (and irrelevant — it never divides `P`), but the
part that actually governs injectivity is a genuine resultant with additive-cancellation origin,
outside the reach of the campaign's cyclotomic/Lucas tools.

## The uniformity wall (task 2, the real question)

* **Per-config:** clean at `P` (bounded height). **Not** a union bound over `∼ C(n,s)^3` configs.
* **Scaling:** `bit-length(|N|)` grows *linearly in the minor size* `ncols = 2k − m_AC − m_BC`
  (`≈ 38 → 45 → 67` for `ncols = 2 → 3 → 4` at `n=13`), i.e. `∝ n`. At the prize scale `n = 2^{30}`
  a maximal minor has degree `∼ n` and `|N|` has bit-length `∼ c·n ≈ 2^{30}`-ish bits — an integer
  of astronomically large height, whose largest prime factor is *not* a priori below `P ≈ 2^{158}`.
* **Equivariance (the one lever).** `SylvesterInjective` is invariant under (a) swapping the two
  carrying pairs and (b) scaling each band factor by a nonzero constant — the two lemmas landed this
  file. So `N` descends to the orbit space of band triples under pair-relabelling + projective
  scaling, and the `μ_n` rotation `ω^i ↦ ω^{i+1}` acts on configs permuting the `N`'s within a
  bit-length class. This *reduces* the config count by the symmetry group order (`∼ n`), but
  `C(n,s)^3 / n` is still super-polynomial: equivariance alone does **not** collapse the union bound.

A uniform proof would need either (i) a *height/largest-prime-factor* bound on `N` uniform over the
orbit space that stays below `P` (no mechanism in hand — the additive cancellation defeats norm
bounds), or (ii) a structural non-vanishing of the μ-basis balance for *every* band degree profile
over `μ_n` at the fixed prize embedding (which is exactly SYZ37's probe-verified, unproved law).

## Brutal-honesty comparison with the BGK wall

The prize's original arithmetic wall (dossier §"β=4"): bound `M(n) = max_a |Σ_{x∈μ_n} e_p(ax)|`, an
**exponential sum over the multiplicative subgroup `μ_n ⊂ F_p`**; the only unconditional bound is
BGK `n^{1−o(1)}`, half a power off the `√n` target, with the `o(1)` **ineffective**
(BKT + Balog–Szemerédi–Gowers, non-constructive) — an additive-combinatorics / sum-product barrier.

**Is SYZ39 the same problem in a new coat, or genuinely more tractable? Honest answer: mostly the
same coat, with one real gain.**

* **Same core difficulty.** Both objects are *characteristic-`p` additive cancellation among `n`th
  roots of unity over `μ_n`* that no multiplicative/cyclotomic-norm control captures. BGK bounds a
  sum `Σ ω^{a·index}`; SYZ39 asks a determinant `det[±W_XC(ω^i)ω^{ij}]` (a signed sum of products of
  root differences) to be nonzero mod `p`. The SYZ39 probe's decisive finding — the obstruction
  primes do **not** factor through root-difference norms — is the exact analogue of BGK's wall: the
  hard part is additive, not multiplicative, so cyclotomic machinery does not bite. In that sense
  the reduction has *not* escaped the BGK-type arithmetic.
* **One genuine gain (do not oversell it).** SYZ39 replaces an *asymptotic, ineffective* sum bound
  with a *per-configuration, effective, decidable* statement: a fixed band triple fails only at
  primes dividing a concrete bounded-height integer `N`, so *for any fixed configuration the residual
  is closed at the prize prime by a finite computation*. BGK gives nothing per-instance. The wall has
  moved from "bound an exponential sum uniformly" to "bound the largest prime factor of a resultant
  uniformly over an orbit space" — a *different* and arguably more concrete question, but **not**
  known to be easier: both are `n → 2^{30}` uniformity statements over `μ_n` with no effective handle.
* **Net.** SYZ39 is honest, sharp, and gives a clean per-instance certificate, but it is **not** a
  bypass of the BGK-class wall. It re-expresses the same additive-cancellation-over-`μ_n` obstruction
  as resultant nonvanishing. Progress = concreteness + effectivity per config + a proof that
  cyclotomic norms cannot close it; **not** an unconditional δ*.

## Lean landed: `Frontier/_SYZ39SylvesterArithmetic.lean` (2 thms, axiom-clean)

`propext / Classical.choice / Quot.sound` only; no `sorry`, no `native_decide`.

* `sylvester_injective_symm` — `SylvesterInjective` is symmetric under swapping the two cofactor
  slots `(WAC,bAC) ↔ (WBC,bBC)` (via `dvd_neg`).
* `sylvester_injective_unit_scale` — invariant under scaling a band factor by a nonzero constant
  `c` (via `natDegree_C_mul`, `C_eq_zero`; the cofactor bijection `r ↦ c⁻¹ r`). This is the
  projective-scaling equivariance that makes the char-0 norm `N` a well-defined orbit invariant.

## Probe: `scripts/probes/probe_syz39_sylvester_badprime_structure.py`

Exact cyclotomic-integer arithmetic (`Z[ω] = Z[x]/Φ_n(x)`), maximal-minor determinants by cofactor
expansion over the ring `Z[ω]`, norms `Res(Φ_n, Δ)` by CRT of mod-`q` resultants; bad primes by
`Res(Φ_n, Δ) ≡ 0 (mod q)`; GF(p) rank scan over `p ≡ 1 (mod n)` for the fixed-embedding check.
Reproduces: `n` always divides `N`; genuine extra primes small and non-`rad(n)`; atomic
root-difference norms confined to `rad(n)`; 0 fixed-embedding failures.

## Honest final state

`SylvesterInjective` is now fully characterized arithmetically: per-config it is a bounded-height
resultant non-vanishing (prize-clean by finite computation), governed by primes that split into a
harmless `rad(n)` ramified part and a genuine additive-cancellation part **provably not reachable by
cyclotomic norms**. The uniform statement at `n = 2^{30}` remains open and is of BGK type — the same
additive-cancellation-over-`μ_n` wall, now as resultant nonvanishing. No unconditional δ*.
