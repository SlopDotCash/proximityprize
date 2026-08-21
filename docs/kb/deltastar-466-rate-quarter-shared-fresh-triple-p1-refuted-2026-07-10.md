# Rate-quarter predecessor: `SharedFreshTripleFree` refuted at literal P1 — the fixed-witness charge
branch is dead

## Status

Closes the shared-fresh arc
(`deltastar-466-rate-quarter-shared-fresh-coordinate-2026-07-10.md`,
`deltastar-466-rate-quarter-noncollinear-triple-2026-07-10.md`).  The residual
`SharedFreshTripleFree` — no fresh coordinate outside a threshold
joint-agreement set carries three distinct bad scalars at the P1 predecessor
— is **false at the literal canonical P1 domain**, kernel-checked.

Formal kernel (compiles clean, 11 audited theorems all
`[propext, Classical.choice, Quot.sound]`, no `sorry`, no `axiom`):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterSharedFreshTripleP1Refuted.lean
```

Headline theorems: `sharedFreshTripleFree_refuted` (every order-`2^30` power
domain of `F_P`), `sharedFreshTripleFree_canonicalDomain_refuted` (the
canonical domain of `_P1RateQuarterCanonicalCodeBridge`), and the existence
form.  Probe:
`scripts/probes/probe_rate_quarter_p1_shared_fresh_triple_refuted.py`.

## 1. The generator-symbolic certificate

`ω = g^(2^26)` has order 16 (`g` = the certified order-`2^30` element of
`F_P` from `_PrizeShapePrimeP30`); `y = x^(2^26)` folds `μ_{2^30}` onto
`μ_16`.  In residue classes `t = e mod 16` of the power enumeration
`e ↦ g^e`:

* `J` = cosets `{0,1,2,3,4,8,9,10,11}`: `|J| = 9·2^26 = 603979776 ≥ T =
  592794966` (`residueSet_card`, a 20-line `Fin` bijection — no giant
  enumeration);
* `u₀(e) = (g^e)^(2^27)`, `u₁(e) = 1` on the seven fresh cosets
  `{5,6,7,12,13,14,15}`; `u₀ = u₁ = 0` on `J`, so `(0,0)` jointly explains
  `J`;
* `γ_j = −ω^(2j)`, `j = 0,1,2` — distinct because `ω` has order 16;
* witness codewords `p_j = X^(2^27) + γ_j` (degree `2^27 < k = 2^28`);
  witness sets `S_j` = fresh cosets + cosets `{j, j+8}` (`≥ T`); agreement on
  the two joint cosets is the identity `ω^(2t) = −γ_j` exactly at
  `t = j, j+8` (`pow_fold`: `(g^e)^(2^27) = ω^(2(e mod 16))`);
* non-jointness: any degree-`<k` explanation of the `u₁` row agrees with the
  constant-`1` codeword on `7·2^26 ≥ k` fresh points, hence equals it
  (`predecessor_sep`), but `u₁ = 0` at the `J`-part anchor of `S_j`;
* the fresh coordinate (index 5, residue 5) lies in every `S_j`, outside `J`.

Everything is proved from `orderOf g = 2^30` and `g ≠ 0` alone — no big
field numerals.  The probe additionally enumerates the identical construction
end-to-end at the mid-scale image `μ_256 = F_257^*` (`k = 64`, threshold 142)
and verifies all 16 coset-level identities at the literal `P` with
big-integer arithmetic.

Lean pitfall worth recording: wrapping the degree-`2^27` polynomial in a
standalone `def` and stating lemmas about it made kernel defeq compare two
independently elaborated `X ^ 2^27` instance chains, recursing through
`npow` (~1.3×10^8 deep).  Inlining the polynomial into a single `refine` so
unification binds one elaboration fixes it.

## 2. Consequence for the P1 predecessor pin

* The fixed-witness escape-charge branch is **dead** at the canonical
  domain: `badFamily_card_le_N_of_sharedFreshTripleFree`'s hypothesis is
  unsatisfiable, and no per-coordinate injective/2-bounded charge can prove
  the predecessor cap.
* This refutes the *proof route*, not the count: the constructed stack
  exhibits exactly three bad scalars.  The operational bracket
  `3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30) < 1/2` and the predecessor
  residual (`PredecessorStructuredFloorResidual`) are untouched.
* Note the constructed triple is *collinear* (`p_j = w₀ + γ_j·w₁` with
  `w₀ = x^(2^27)`, `w₁ = 1`), matching the collinear boost: the pencil
  `(w₀, w₁)` jointly agrees with the stack on the `7·2^26` fresh coordinates,
  comfortably above the `⌈(3T−N)/2⌉` floor and below `T`.  Both refined
  residuals of `_P1RateQuarterNonCollinearTriple.lean` should now be regarded
  as false-at-P1 (`CollinearTripleFree` is refuted by this certificate
  outright; the non-collinear side already has the P1-shape `F_37`
  realization).

## 3. Lane successor (after consolidation)

Counting arguments that tolerate shared triples, powered by the landed
structure theorems (pencil transport on `≥ 2T−N` pairwise intersections,
witness incomparability, absorption dichotomy, collinear boost, triple
rigidity at overlap `≥ k`):

1. bound the number of fresh coordinates that can carry ≥3 scalars (the
   present certificate uses `7·2^26` of them — a cap on triple-carrying
   coordinates times 2 plus doubles could still bound `#bad`);
2. a global pencil count: every pair of bad scalars determines a joint-list
   pencil at agreement `≥ 2T−N`; bounding the number of distinct pencils and
   the scalars per pencil (a pencil with `d` scalars gives joint agreement on
   a `d`-fold two-cover) is the natural surviving route to the predecessor
   uniform count.

## 4. What this is not

Not a delta-star change, not a refutation of `#bad ≤ N`, and not a
counterexample to MCA proximity gaps.  It is the exact identification and
kernel-checked closure (negative) of one proof architecture for the
predecessor pin.
