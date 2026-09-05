# CLM-046 two-label reciprocal fingerprint (2026-08-29)

**Status:** independently reviewed human proof / ported KB note; **not Lean-PROVEN**. The
accompanying `F_41[u]/(u^2-3)` program is a reproducible finite diagnostic, not evidence for the
all-parameter theorem.

## Scope and assumptions

This note carries the bounded injectivity result registered as `CLM-046`. It works in the accepted
`CLM-045` domain and uses the following exact assumptions and definitions.

1. `F` is a finite field, `L` is an ordered set of 128 distinct evaluation points, and
   `C=RS[F,L,32]` uses polynomials of degree strictly less than 32.
2. The inherited direction `f2` has exact maximum agreement
   `h(f2,C)=max_(r in C)|Agr(f2,r)|=33`. Here `h` is maximum agreement, not Hamming distance.
3. `S` is the selected 41-point support, `O=L\S`, and `w` is the central residual. For a passing
   eight-point core `A subset S`, put

   ```text
   T_A=S\A,
   r_A in C with r_A=f2 on T_A,
   z_A=f2-r_A.
   ```

   The accepted interpolation result makes `r_A` unique.
4. `L_A` is the set of distinct nonzero reciprocal-pencil labels actually selected for `A`; it is
   not the set of every possible outside eight-subset. For `a in L_A`, define the complete fiber

   ```text
   Phi_A(a)={x in O:w(x)=a*z_A(x)}.
   ```

   The originally selected outside eight-set lies in this fiber.

All root counts, agreement counts, cancellations, and divisions are exact finite-field operations.
There is no floating-point, probabilistic, optimizer, characteristic-transfer, or asymptotic
premise.

## Canonical full fibers

The residual `z_A` is nonzero at every point of `O`. It already vanishes on the 33 points of
`T_A`; one more zero in `O` would make `r_A` agree with `f2` in at least 34 places, contradicting
the exact maximum agreement.

Each complete fiber `Phi_A(a)` contains its original selected eight-set. The order on `L` therefore
makes this canonical prefix well-defined:

```text
B_A(a)=the eight least-indexed elements of Phi_A(a).
```

Distinct labels for one core have disjoint complete fibers. If a point belonged to the fibers of
both `a` and `b`, then `a*z_A(x)=w(x)=b*z_A(x)`; nonvanishing of `z_A(x)` gives `a=b`.

For distinct `a,b in L_A`, lexicographically order their disjoint prefixes as `B_0<B_1`, carry the
corresponding labels as `a_0,a_1`, and define

```text
kappa(A,{a,b})=(B_0,B_1,a_0/a_1).
```

Both selected labels are nonzero, so the ratio is defined.

## Equal fingerprints have one common scalar

Suppose `(A,{a,b})` and `(A',{a',b'})` have the same fingerprint. Equality of the support
components gives the same ordered `B_0,B_1`. Equality of the ratio gives a common nonzero scalar

```text
lambda=a'_0/a_0=a'_1/a_1.
```

On all 16 points of `B_0 union B_1`, the two fiber equations yield

```text
z_A'=lambda^(-1)z_A.
```

Put `c=|A intersect A'|`. The retained inside sets intersect in

```text
|T_A intersect T_A'|=25+c.
```

Those inside points are disjoint from the 16 outside points.

## Case 1: `lambda!=1`

The difference

```text
z_A'-lambda^(-1)z_A
```

is a nonzero scalar multiple of `f2-r` for a codeword `r in C`. It vanishes on the 16 outside
points and the `25+c` common inside points, hence on at least

```text
16+(25+c)=41+c>33
```

points. This contradicts the exact maximum agreement. Equal fingerprints therefore cannot have
`lambda!=1`.

## Case 2: `lambda=1`

Now `r_A'-r_A` has degree strictly less than 32 and vanishes on the same `41+c>31` points, so the
finite-field root bound gives `r_A'=r_A` as polynomials. If `A!=A'`, then `c<=7`; the common
codeword would agree with `f2` on

```text
|T_A union T_A'|=41-c>=34
```

points, again contradicting maximum agreement. Therefore `A=A'`.

Each `B_i` is nonempty and lies in `O`, where `z_A` is nonzero. The equations
`w=a_i*z_A=a'_i*z_A` recover both ordered labels, hence also the original unordered pair. Thus
`kappa` is injective on the full inputs `(A,{a,b})` counted by
`Q=sum_A binom(m_A,2)`.

## Reproducible exact diagnostic

The companion script independently reconstructs `F_41[u]/(u^2-3)` using only Python integers and
explicit field operations. It checks all 1,681 field elements, 87 outside points, ten disjoint
eight-point blocks, and five cores with representatives and eighth-power shifts

```text
representatives=(1,10,16,18,37),
shifts=(1,16,37,10,18).
```

For every core shift `s` and block value `b`, it checks the two sign conventions

```text
delta=b-s,
a=s-b=-delta.
```

All 50 challenge labels and all 50 reciprocal labels are globally distinct and nonzero. The probe
reselects every canonical fiber prefix, carries the labels with lexicographically ordered blocks,
and verifies exactly

```text
inputs                              225
plain support-pair buckets           45
multiplicity of every plain bucket    5
distinct enriched fingerprints       225.
```

Run it from the repository root:

```text
python3 scripts/probes/probe_clm046_f41_two_label_fingerprint.py
```

A successful run ends with `PASS: all exact assertions reproduced`. The program imports no
Paradox module and uses neither floating point nor Lean. It is subordinate finite diagnostic
support, not the human proof.

## Exact source locators and review boundary

The port is derived from exact clean source revision
`1b34a48c3d0733ed082446f6b1a370c786350ee5` in the Paradox research repository. Relevant paths at
that revision are:

- `theory/claims.toml`, entry `CLM-046`;
- `theory/proofs/PRF-024-two-label-reciprocal-fingerprint.md`;
- `theory/proofs/PRF-024-assumptions.md` and `PRF-024-dependencies.toml`;
- `src/proximity_lab/e87_h33_two_label_fingerprint.py` and
  `tests/test_clm046_two_label_fingerprint.py`;
- `reports/e87-h33-two-label-fingerprint.md`.

`REV-080` independently reviewed that clean producer commit, reproduced all registration and
dependency pins, checked the proof's two scalar cases, ran a separate integer-only diagnostic,
and verified the source repository's four locked gates. Source revision
`9e178ebc0166c9d49bd1e9083d4adb6912805882` records the append-only review and `CLM-046`
`OPEN`-to-`PROVEN` transition. This is evidence for a reviewed **human proof**, not a Lean theorem.

The inherited Reed--Solomon and MCA definitions come only from Gal Arnon, Dan Boneh, and Giacomo
Fenzi, *Open Problems in List Decoding and Correlated Agreement*, IACR ePrint 2026/680, revision
`20260706:152933`: Definition 2.11 on PDF page 9 and Definition 4.3 on PDF page 17. The inspected
55-page PDF has SHA-256
`ccb3eea9966485d9dd312a0eb46b3219d9a92cbe4fd191a88ad9976115ed892a`. It states none of the
`CLM-046` conclusions.

The pinned dependency record uses the accepted `CLM-045` proof and review for the inherited domain.
It records the association-scheme material as route context only and the ArkLib issue capture as
historical collision provenance only. Neither supplies the two-label theorem, a realizable-
fingerprint capacity bound, correctness, promotion, novelty, or priority evidence.

## Registered nonclaims retained by this port

- Registration supplies no proof, diagnostic, disproof, review, promotion, or
  obligation-acceptance evidence.
- This claim does not bound the number of realizable `(B_0,B_1,rho)` fingerprints, prove
  `Q<=61686610`, imply `M<=19731940`, prove `CLM-030`, decide `CLM-027`, satisfy `OBL-021`, or
  handle `h>33`.
- It supplies no fixed-prime subgroup transfer, sufficiently-large-field family, threshold, Grand
  MCA or Grand List-Decoding resolution, general Proximity Cap result, novelty, priority, prize or
  prize-worthy-partial conclusion, publication, authorship, affiliation, payment, award, license,
  copyright, legal, financial, organizer-email, or formal-submission conclusion.
- The source registration and reviewed proof evidence performed no external write. This port is a
  separate, authorized publication step; it performs no organizer email or formal prize submission
  and makes no award or payment representation.

The injectivity result itself supplies no capacity or `Q` bound: it does not count how many
enriched fingerprints can actually occur.

## Attribution and licensing

The original proof, exact diagnostic, and this port are attributed to `geofflava`. The original
contribution is licensed under both MIT and Apache-2.0, consistent with `LICENSE-MIT`, `LICENSE`,
and the repository contribution policy. No copyright is assigned by this contribution. Historical
or third-party material retains its original license and attribution boundaries.
