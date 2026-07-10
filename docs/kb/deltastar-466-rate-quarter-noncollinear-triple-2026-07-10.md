# Rate-quarter predecessor: the non-collinear shared triple — rigidity, dichotomy, and the F₃₇ escape

## Status

Successor of
`deltastar-466-rate-quarter-shared-fresh-coordinate-2026-07-10.md`.  That
note reduced the fixed-witness branch of the P1 predecessor pin to the
residual `SharedFreshTripleFree` (no fresh coordinate outside a threshold
joint set carries three distinct bad scalars).  This note settles the
structure of the remaining **non-collinear** case and records why the
residual is now conjecturally **false**.

Formal kernel (compiles clean, 11 audited theorems all
`[propext, Classical.choice, Quot.sound]`, no `sorry`, no `axiom`):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterNonCollinearTriple.lean
```

Probe: `scripts/probes/probe_rate_quarter_p1_noncollinear_triple.py`
(deterministic; constructs and verifies the `F_37` certificate).

Related lane files: `_P1RateQuarterSharedFreshCoordinate.lean` (imported
substrate: pencil transport, absorption dichotomy, collinear boost,
`predecessor_sep`, the residual and its consumer) and the concurrent swarm
transcription `_RateQuarterSharedFreshCoordinateCounterexampleF11.lean`
(independent kernel check of the same `RS[8,2]/F_11` shared-fresh
countermodel; not touched by this session).

## 1. Pencil rigidity and the P1 dichotomy (proved)

* `triple_pencil_rigidity`: if the code separates on `k` points and
  `|S₁ ∩ S₂ ∩ S₃| ≥ k`, the pairwise divided-difference pencils coincide and
  `p_j = w₀ + γ_j·w₁` for a single codeword pencil `(w₀, w₁)`.
  (Proof: the two directions `(p₂−p₁)/(γ₂−γ₁)` and `(p₃−p₁)/(γ₃−γ₁)` both
  equal `u₁` on the triple overlap, hence are equal codewords.)
* `shared_triple_dichotomy` (P1): every shared triple of threshold witnesses
  of distinct bad scalars either (a) lies on one pencil jointly agreeing with
  the stack on `≥ 352,321,537 ≥ k = 2^28` coordinates (collinear boost on the
  two-cover region), or (b) has triple overlap `≤ k − 1`.
* `noncollinear_triple_overlap_le`: contrapositive — non-collinear triples
  have triple overlap `≤ k − 1`.
* `triple_floor_negative`: `3T < 2N` (`3T − 2N = −369,098,750`), so the
  rigidity premise is **never forced** at P1: the dichotomy cannot
  unconditionally collapse the non-collinear branch.

## 2. The non-collinear escape is real at the exact P1 shape (kernel-checked)

`RS[32,8]` over `F_37`, domain `0..31`, radius `7/16`, threshold `T = 18`.
Shape inequalities all match P1: `2T−n = 4 > 0`, `3T−2n = −10 < 0`,
`2T ≤ n+k−1 = 39`, `k/n = 1/4`, `T/n = 0.5625 ≈ 0.552`.

```text
q0 = 1+X, q1 = 2+X^3, J = {0..17}
gamma = 1,2,3; witness polys:
  p1 = 15+32X+16X^2+22X^3+23X^4+32X^5+5X^6+X^7
  p2 = 5+26X+30X^2+33X^3+16X^4+20X^5+30X^6+19X^7
  p3 = 7+X+3X^3          (the q-line at gamma=3)
witnesses (18 coords each) share fresh coordinate 18 ∉ J
triple overlap = {18,21,26,28,30,...}: exactly 6 ≤ k−1 = 7
```

Kernel-checked (`nonCollinearSharedFreshTriple_realizable`): three literal
`mcaEvent`s; `J` jointly explained; no joint pair on `J ∪ {18}`
(non-absorption); and **non-collinearity** — no pencil of arbitrary
functions reproduces the three witness codewords (`not_collinear`: the
values `15, 5, 7` at coordinate `0` violate the pencil identity by
`12 ≠ 0` in `F_37`).

Construction: `p₁ = qline₁ + c₁A₁`, `p₂ = qline₂ + c₂A₂`, `p₃ = qline₃`,
with `A₁, A₂` degree-7 products of distinct `J`-linear factors chosen (by
the collision statistic `r_t = −A₁(t)/A₂(t)` over the fresh region) so that
the second divided difference is a nonzero multiple of `A₁ + r·A₂` with five
roots planted in the fresh region — these roots are the triple-overlap
coordinates, making the shared stack values consistent without collinearity.

## 3. Residual split and the honest state of the branch

* `sharedFreshTripleFree_of_split` (proved): `SharedFreshTripleFree` follows
  from `CollinearTripleFree ∧ NonCollinearTripleFree` (explicit-witness
  forms via `SharedTripleWitnessData`).
* `CollinearTripleFree` (OPEN): a collinear triple carries a `≥ 352M`
  agreement pencil — below `T = 592,794,966`, so nothing contradicts it yet.
* `NonCollinearTripleFree` (OPEN, **conjecturally false**): the `F_37`
  construction uses only products of linear factors over subsets of the
  domain.  On the literal smooth P1 domain `μ_{2^30}`, products over
  subgroup cosets collapse to binomials `x^m − c`, so `A₁ + rA₂` becomes an
  explicit binomial pencil and planting `~1.1×10^7` fresh-region roots
  (the two-cover floor `3(T−k+1) − 2(N−T) = 11,184,817`) looks constructible.
  A kernel-checked P1-scale lift is the designated next move; success would
  refute `SharedFreshTripleFree` and kill the fixed-witness charge branch,
  redirecting the predecessor pin to counting arguments that tolerate shared
  triples (e.g. bounding the *number* of fresh coordinates carrying triples,
  or a global pencil-count argument at agreement `2T−N`).

## 4. What this is not

Not a proof of the predecessor uniform count and not a delta-star pin.  The
operational bracket `3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30) < 1/2` is
unchanged.  The contribution is the exact collinear/non-collinear dichotomy,
the arithmetic proof that rigidity cannot close it, the realizability of the
non-collinear escape at the exact P1 inequality shape, and the formal
reduction of the residual to the two named refined residuals.
