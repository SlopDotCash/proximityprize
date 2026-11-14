# The lower half of the Grand MCA determination closes, per-prime, for the whole window
### A routine fixed-parameter instantiation of Krachun–Kazanin–Haböck (ePrint 2026/782, Appendix A)

Lane `nubs/issue232-effective-pa`, 2026-06-09. Status: **derivation independently
re-verified step-by-step against the published text; all credit to the cited works —
the only contributions here are (i) noticing the fixed-(s,r) instantiation that the
paper leaves asymptotic, and (ii) a one-degree shift (r = ρs+1 instead of ρs+2) that
makes the construction hit the prize's exact rate and improves the gap from 2/s to
1/s.** This subsumes the window form of O38's Corollary E3 (which survives as the
constructive, exact-count variant — see §4) and retires the η=1/128 "open residual"
of `EffectivePerPrimeExactness.md` §5 on the lower side.

**Sources.** [KKH26] Krachun–Kazanin–Haböck, *Failure of proximity gaps close to
capacity*, ePrint 2026/782 (received 2026-04-20 — this is the published version of
what the program record cites as "KK25, personal communications"; update citations
accordingly). Appendix A there gives a quotient ("DEEP", [BGKS20]) proof of their
Theorem 1, crediting the quotient-from-a-bad-list-center idea to [CS25] and
[BCHKS25], and using the second-moment value-spread lemma of [BCIKS20]
([KKH26] Lemma 3, restated below). All asymptotics in [KKH26] are existential over
primes (`p ∈ [n^β, 2n^β]` via Linnik-type input); the observation here is that the
Appendix-A argument, run at *fixed* (s, r), is per-prime and threshold-free.

---

## 1. The instantiated statement

**Theorem Q (instantiation of [KKH26] App. A; exact-rate variant).** Let `n = 2^a`,
`s | n` a 2-power with `ρs ∈ ℤ`, `r := ρs + 1 ≤ s − 1`, `m := n/s`. Let `p ≡ 1 (mod n)`
be **any** prime, `H ⊆ F_p^×` the order-`n` subgroup, `G = H^m` the order-`s`
subgroup, and `C = RS[F_p, H, ρn]` (dimension `ρn`, the prize's exact rate-ρ code).
Then

    ε_mca(C, 1 − ρ − 1/s)  ≥  ( ½ · min( C(s, r), p/(ρn) ) − n ) / p.

*Consequences.* The right side exceeds `2^−128` throughout

    2^129 ≤ p < 2^127 · C(s, ρs+1)        (and trivially for all p ≤ 2^129·…),

so for every prime in that range, `δ*_C < 1 − ρ − 1/s` whenever `δ*_C` exists.
Choosing the largest admissible `s` per field size, for **every** prize rate and
**every** prime in the **entire window** `[2^129, 2^256)` (with `s | n`, i.e. enough
2-adicity):

    δ*_C  <  1 − ρ − η   for every dyadic η ≥ (H₂(ρ) + o(1)) / (log₂ p − 127),

— the lower half of the conjectured determination formula
(`δ* = 1 − ρ − Θ(H₂(ρ)/(log₂|F| − 128 − log₂ n))`, S-two/CGHLL26 App. A shape; the
`log₂ n ≤ 40` term is absorbed by the window), now **per-prime, effective, and
unconditional**, by published machinery plus this instantiation.

Concrete full-window choices (exact binomials):

| ρ | s (η = 1/s) | r | log₂C(s,r) | per-prime pin for p < |
|---|---|---|---|---|
| 1/2 | 128 | 65 | 124.15 | 2^251.1 |
| 1/2 | 256 | 129 | 251.66 | 2^378.7 → **whole window at η=1/256** |
| 1/4 | 128 | 33 | 101.76 | 2^228.8 |
| 1/4 | 256 | 65 | 205.13 | 2^332.1 → whole window |
| 1/8 | 128 | 17 | 69.06 | 2^196.1 |
| 1/8 | 256 | 33 | 138.18 | 2^265.2 → whole window |
| 1/16 | 256 | 17 | 86.88 | 2^213.9 |
| 1/16 | 512 | 33 | 172.77 | 2^299.8 → whole window |

(η = 1/128 itself: covered per-prime up to 2^251.1 / 2^228.8 / 2^196.1 at
ρ = 1/2, 1/4, 1/8 — already beyond everything O38's E3 could reach; the residual
slivers near 2^256 are pinned at the *stronger* gaps 1/256, 1/512 by the next `s`.)

## 2. The construction and proof (re-derived; nothing new beyond the two tweaks)

Write `u(x) = x^{rm}` on `H`. For each `r`-subset `S ⊆ G` let
`v_S(Y) = Π_{a∈S}(Y−a) = Y^r − p_S(Y)` with `deg p_S ≤ r−1`, and
`c_S(X) := X^{rm} − v_S(X^m) = p_S-part`, i.e. `c_S = X^{rm} − v_S(X^m)`,
`deg c_S ≤ (r−1)m = ρn`.

- **The list.** `L = {c_S : S ∈ C(G, r)}` has `|L| = C(s,r)` distinct elements
  (distinct `S` give distinct `v_S`), and any two agree on at most
  `A := (r−1)m = ρn` points of `F_p` (their difference is a nonzero polynomial of
  degree ≤ ρn).
- **Value spread ([KKH26] Lemma 3 = [BCIKS20]; second-moment).** For any set `L` of
  functions on `S₀ = F_p` with pairwise agreement ≤ A:
  `E_{z∈F_p}[|L(z)|] ≥ ½·min(|L|, p/A)`. Hence some `z` attains it; discarding the
  ≤ `n` points `z` with `z^m ∈ G` costs at most `n` (each `|L(z)| ≤ min(|L|, p)` and
  the totals dominate the correction in-window — `p/A ≥ 2^129/2^40 ≫ 2n`), giving a
  good `z` with `|L(z)| ≥ ½·min(C(s,r), p/(ρn)) − n` and `z^m ∉ G`.
- **The line.** `u₀ = u/(x^m − z^m)`, `u₁ = 1/(x^m − z^m)` on `H` (well-defined:
  `z^m ∉ G`).
- **Bad scalars.** On the `m`-fold preimage of `S` in `H` (exactly `rm` points),
  `x^{rm} = p_S(x^m)` (since `v_S(x^m) = 0`), so with `λ_S := −p_S(z^m)`:
  `u₀ + λ_S u₁ = (p_S(x^m) − p_S(z^m))/(x^m − z^m) = q_S(x)` there, where
  `q_S(X) := (p_S(X^m) − p_S(z^m))/(X^m − z^m)` is a polynomial of degree
  `≤ (r−2)m = ρn − m ≤ ρn − 1`, i.e. `q_S ∈ C`. Agreement `≥ rm = (ρ + 1/s)n`, so
  `u₀ + λ_S u₁` is `δ`-close at `δ = 1 − ρ − 1/s`. Distinct values `p_S(z^m)`
  (= `c_S(z) − z^{rm}` up to the common shift) give distinct `λ` — exactly `|L(z)|`
  many.
- **Far side ⇒ MCA-bad.** Any `c ∈ C` agreeing with `u₁` at `x` satisfies
  `c(X)(X^m − z^m) − 1 = 0` at `x`; that polynomial is nonzero (it equals −1 at any
  root of `X^m − z^m` in `F̄_p`) of degree `≤ ρn − 1 + m`, so `u₁` agrees with any
  codeword on `≤ ρn + m − 1 < (ρ + 1/s)n` points. Hence the pair `(u₀, u₁)` has no
  joint `(1−δ)n`-agreement set, and **every** `δ`-close point of the line is MCA-bad
  (any witness of the point fails to extend to the line). Therefore
  `ε_mca(C, δ) ≥ |L(z)|/p`. ∎

(Both tweaks vs the literal Appendix A: [KKH26] use `r = ρs + 2` with code dimension
`(r−2)m + 1 = ρn + 1` — rate `ρ + 1/n` — and gap `2/s`; shifting to `r = ρs + 1`
lands `deg q_S ≤ ρn − 1`, the exact-rate dimension-`ρn` code, with gap `1/s`. The
far-side margin tightens from `1/s` to `1/n·(n/s − ... )` — still strict, as shown.)

## 3. What remains open after this (the honest ledger, updated)

The **lower half** of the Grand MCA determination is now closed per-prime across the
window: `δ*_C < 1 − ρ − (H₂(ρ)+o(1))/(log₂p − 127)`. The **upper half** — proving
`ε_mca(C, δ) ≤ 2^−128` for `δ` in `(Johnson, 1 − ρ − Θ(H₂(ρ)/(log₂p − 128)))`, i.e.
that `δ*` sits *at* the formula rather than below it — is the entire remaining
content of the prize, exactly as the descent program (O13–O13″, Conjecture D) and
the upper-half cartography frame it. No change to that side from here.

## 4. Status of O38/O39 after this note

- O38's **E1/E2 (norm threshold, exactness)** stand untouched and remain the only
  *exactness* results (image exactly `N₀(m,r)`, char-0 fibers) — a finer invariant
  than Theorem Q's `≥ ½min(…)` count, and the right tool for transition-zone
  structure (O39) — but they are no longer needed for the prize's lower half.
- O38's **E3 windows are subsumed** by Theorem Q (which is threshold-free, covers
  every prime including below `T(m,r)`, reaches every dyadic gap, and needs no
  norm bound at all). E3 retains: constructive bad scalars on an explicit line
  *without* the z-search, the exact count `N₀`, and the m=16/32 exact-onset data.
- O39's class-group/short-generator program and the cert(p) idea are **retired for
  the lower half** (nothing to certify — Theorem Q is threshold-free); they remain
  relevant only to the exact-image question as such.
- O38's literature hedge resolves as: the as-stated priority claim was consistent
  with the published record, but [KKH26] App. A *implied* (unstated) the stronger
  per-prime result; this note records that and corrects the program's citations
  ("KK25 personal communications" → ePrint 2026/782 throughout).
