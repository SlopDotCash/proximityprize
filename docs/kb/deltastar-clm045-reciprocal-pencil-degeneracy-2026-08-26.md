# CLM-045 reciprocal-pencil degeneracy and fixed-set cap (2026-08-26)

**Status:** human proof / ported KB note; **not Lean-PROVEN**. The proof was independently reviewed
at its pinned source revision, but it has not been formalized in Lean in this repository. The
accompanying `F_7` program is a reproducible scaled diagnostic, not evidence for the theorem.

## Scope and assumptions

This note carries four bounded theorem groups from the accepted `CLM-044` reciprocal-pencil domain.
The exact inherited assumptions are:

1. `F` is a finite field, `L` consists of 128 distinct points, and `C=RS[F,L,32]` uses
   polynomials of degree strictly less than 32.
2. `f2` is outside `C`, and its maximum agreement with a word of `C` is exactly
   `h(f2,C)=33`.
3. `S` is a selected 41-point central support, `O=L\S`, and the central residual `w` vanishes on
   `S`.
4. For `H_S(X)=prod_(s in S)(X-s)` and `alpha_s=1/H_S'(s)`, define on polynomials of degree at
   most eight

   ```text
   Lambda(g)=sum_(s in S) alpha_s f2(s)g(s),
   K_x(g)=H_S(x) sum_(s in S) alpha_s f2(s)g(s)/(x-s),
   W=ker Lambda,
   U_B(g)_b=f2(b)g(b)-K_b(g),
   V_B(g)_b=w(b)g(b).
   ```

5. A valid outside set `B` has eight distinct points in `O`; every valid `b` satisfies
   `w(b)!=0`; and `g_B=prod_(b in B)(X-b)`.
6. The inherited `CLM-044` fiber facts are used without change: for distinct cores with
   `c=|A intersect A'|` and `d=|B intersect B'|`, equal labels give `c+d<=6`, unequal labels give
   `c+d<=8`, and a fixed pair `(B,a)` has at most one valid core.
7. All ranks, determinants, roots, interpolation identities, and divisions use exact finite-field
   arithmetic. The threshold calculation uses exact integers only.

There is no prime-field, characteristic, smooth-domain, asymptotic, probabilistic, optimizer, or
floating-point premise. The only inherited mathematical result is the bounded `CLM-044` normal
form; the four statements below are proved locally.

## Group 1: `Lambda` is nonzero and `dim W=8`

Let `I` be the unique degree-at-most-40 interpolant of `f2` on `S`:

```text
I(X)=sum_(s in S) alpha_s f2(s) H_S(X)/(X-s).
```

Write `H_S(X)=X^41+h_40 X^40+...+h_0`. For `0<=j<=8`, the coefficient of `X^(40-j)` in
`H_S(X)/(X-Y)` is

```text
c_j(Y)=Y^j+h_40 Y^(j-1)+...+h_(41-j).
```

Thus `c_j` is monic of degree `j`, and the coefficient of `X^(40-j)` in `I` is
`Lambda(c_j)`. If `Lambda` vanished on all polynomials of degree at most eight, it would vanish on
the basis `c_0,...,c_8`. The top nine coefficients of `I`, in degrees 40 down to 32, would then be
zero, so `deg I<=31`. Its evaluation would agree with `f2` on all 41 points of `S`, contradicting
`h(f2,C)=33`.

Therefore `Lambda` is nonzero. Since the polynomials of degree at most eight form a
nine-dimensional space, its kernel has

```text
dim W=8.
```

## Group 2: an identically singular fixed-`B` pencil

Fix a valid outside eight-set `B` and suppose its determinant polynomial `D_B(a)` vanishes
identically. On `W`, write the eight-by-eight pencil as

```text
M(a)=aU_B-V_B.
```

The original nine-by-nine determinant and `det M(a)` differ by a fixed nonzero change-of-basis
scalar, so `det M(a)=0` as a polynomial.

At `a=0`, the map `V_B` is singular. A nonzero `g in ker V_B` vanishes at all eight points of `B`
because `w(b)!=0`. The degree bound forces `g` to be a scalar multiple of `g_B`. Hence

```text
Lambda(g_B)=0,
ker V_B=span(g_B),
rank V_B=7.
```

The two maps have no common nonzero kernel vector. To see this, define

```text
K(g)(X)=H_S(X) sum_(s in S) alpha_s f2(s)g(s)/(X-s).
```

It satisfies `K(g)(s)=f2(s)g(s)` on `S`, and its `X^40` coefficient is `Lambda(g)`. A common
kernel vector would be a multiple of `g_B`; the equations `U_B(g_B)=0` say that `K(g_B)` also
vanishes on `B`. Thus `g_B` divides `K(g_B)`. Since `Lambda(g_B)=0`, the quotient

```text
r(X)=K(g_B)(X)/g_B(X)
```

has degree at most 31. Because `S` and `B` are disjoint, it agrees with `f2` on all 41 points of
`S`, again contradicting `h(f2,C)=33`.

Finally, `M(0)=-V_B` has rank seven, while `det M(a)=0`; therefore `M(a)` has rank exactly seven
over `F(a)`. Its adjugate is nonzero, and any nonzero column supplies a polynomial kernel vector.
Each entry is a seven-by-seven minor of an affine-linear matrix, so

```text
G(a)=g_0+a g_1+...+a^e g_e,     e<=7,
M(a)G(a)=0.
```

This vector cannot be constant, because a constant vector would be a common nonzero kernel vector
of `U_B` and `V_B`. Therefore `1<=e<=7`. Comparing powers of `a` gives the exact chain

```text
V_B g_0=0,
U_B g_(i-1)=V_B g_i     for 1<=i<=e,
U_B g_e=0.
```

This is a maximal-minor argument over `F[a]`; it imports no matrix-pencil classification or
Kronecker canonical form.

## Group 3: at most five fibers over one fixed `B`

For a valid fiber `(A,a,B)`, every `b in B` satisfies `g_A(b)!=0` and `w(b)!=0`. The equation

```text
a U_B(g_A)_b=w(b)g_A(b)
```

therefore determines the label `a` from `(A,B)`. Two distinct fibers over the same `B` cannot
share a core, and inherited fixed-`(B,a)` uniqueness prevents distinct cores from sharing a label.
Their labels are distinct.

They also share all eight outside points, so `d=8`. The inherited different-label spacing bound
`c+d<=8` forces `c=0`: their eight-point inside cores are disjoint. A 41-point set contains at most

```text
floor(41/8)=5
```

such cores. If `m_B` counts valid fibers over `B` and `M=sum_B m_B>0`, then

```text
m_B(m_B-1)<=4m_B,
A_(8,0)=(1/M) sum_B m_B(m_B-1)<=4.
```

The empty-family case is vacuous.

## Group 4: exact colored-moment threshold

Let

```text
P=2729892,
0<=m_A<=10,
M=sum_A m_A,
Q=sum_A binom(m_A,2),
T=19731940.
```

Pad unused passing-core slots with zeros so exactly `P` multiplicities are present. If
`x>=y+2`, transferring one unit from `x` to `y` lowers the pair mass by

```text
binom(x,2)+binom(y,2)-binom(x-1,2)-binom(y+1,2)=x-y-1>0.
```

Consequently, for fixed `M=qP+r`, `0<=r<P`, the minimum is attained by entries differing by at
most one and equals

```text
(P-r)binom(q,2)+r binom(q+1,2).
```

The relevant balanced values seven and eight respect the cap ten. Exact division gives

```text
T=7P+622696,
Q>=61686604 when M=T,
Q>=61686611 when M=T+1.
```

Deleting units cannot increase `Q`, so every `M>=T+1` has `Q>=61686611`. Thus

```text
Q<=61686610
```

is sufficient to force `M<=T`. It is the weakest integer upper cap of this form: the balanced
profile at `M=T+1` has exactly `Q=61686611`.

## Reproducible scaled diagnostic

The companion script uses `RS_<2` over `F_7`, with

```text
S={0,1,2,3,4}, B={5,6}, f=(0,0,0,1,5,1,3).
```

It exhausts all 49 affine words and all 343 coefficient vectors for every label. It recomputes
the agreement histogram `{0:16,1:22,2:6,3:5}`, the interpolation rows, the identically zero
determinant polynomial, all seven normalized kernels and their root sets, and the exact convexity
threshold. Run it from the repository root:

```text
python3 scripts/probes/probe_clm045_f7_reciprocal_pencil.py
```

A successful run ends with `PASS: all exact assertions reproduced`. The program uses only Python's
standard library, integers, and explicit finite-field operations. It imports no Paradox module and
uses neither floating point nor Lean.

## Exact source locators and review boundary

The port is derived from exact source revision
`e1ce1347de20e1adb156e8c58ee76015324c2e88` in the Paradox research repository. Relevant paths at
that revision are:

- `theory/claims.toml`, entry `CLM-045`;
- `theory/proofs/PRF-023-reciprocal-pencil-degeneracy-and-fixed-b-cap.md`;
- `theory/proofs/PRF-023-assumptions.md` and `PRF-023-dependencies.toml`;
- `theory/reviews/REV-079-e87-h33-pencil-degeneracy-and-fixed-b-cap.toml`;
- `src/proximity_lab/e87_h33_pencil_degeneracy.py` and
  `tests/test_clm045_reciprocal_pencil_degeneracy.py`;
- `reports/e87-h33-pencil-degeneracy-retention.md`.

`REV-079` independently reviewed clean producer commit
`47f02d85d65cab8c987fbc0521baf1598d86278f`, reproduced the proof boundary and a separate
integer-only F7 replay, and passed the source repository's four locked gates. The later source
revision above records the append-only review and claim transition. This is evidence for a
reviewed **human proof**, not a Lean theorem.

The inherited coding-theory conventions come only from Gal Arnon, Dan Boneh, and Giacomo Fenzi,
*Open Problems in List Decoding and Correlated Agreement*, IACR ePrint 2026/680, revision
[`20260706:152933`](https://eprint.iacr.org/archive/2026/680/20260706:152933): Definition 2.11 on
PDF page 9 for the degree-`<k` Reed--Solomon convention and Definition 4.3 on PDF page 17 for the
same-coordinate-set MCA event. The inspected
[55-page PDF](https://eprint.iacr.org/archive/2026/680/1783351773.pdf) has SHA-256
`ccb3eea9966485d9dd312a0eb46b3219d9a92cbe4fd191a88ad9976115ed892a`. The paper states none of
the four CLM-045 conclusions.

The pinned dependency record locates the imported bounded result at
`theory/proofs/PRF-022-reciprocal-pencil-near-mds-normal-form.md` and its independent review at
`theory/reviews/REV-078-e87-h33-reciprocal-pencil-normal-form.toml`. It also records
`sources/notes/SRC-034-delsarte-levenshtein-association-schemes.md` as product-Johnson route context
only and `sources/notes/SRC-036-arklib-e87-h33-adjacent-core-collision.md` as historical collision
provenance only. Neither is a theorem input for the four groups above.

## Registered nonclaims retained by this port

- The original registration itself supplied no proof, diagnostic, disproof, review, promotion, or
  obligation-acceptance evidence; those later evidence boundaries remain separately recorded.
- The fixed-`B` cap does not control the number of outside eight-sets and does not prove the
  weighted adjacent-core fiber inequality or any aggregate fiber cap.
- The retained feasible point has `A_(8,0)=0`, so the new product-Johnson inequality alone does not
  repair the retained product-Johnson route.
- `Q<=61686610` is a future-work target. This note proves that such a bound would be sufficient; it
  does not establish the bound itself.
- This result does not prove `CLM-030`, gives no upper bound for `h(f2,C)>33`, does not decide
  `CLM-027`, and does not satisfy `OBL-021`. The broader E87 decision remains open.
- The F7 example is a scaled diagnostic only. It creates no experiment record, computed
  E87 conclusion, proof, or refutation of a registered E87 claim.
- No E87 aggregate cap, asymptotic bridge, Grand Challenge result, prize or prize-worthy-partial
  result, novelty, priority, prize eligibility, payment, authorship, affiliation,
  conflict-of-interest, award, or other legal or financial conclusion follows.
- No growing-family result and no general Proximity Cap result is asserted.
- The source registration and proof evidence performed no external write, push, publication,
  organizer email, or formal submission. This port is a separate, authorized publication step;
  it performs no organizer email or formal prize submission and makes no award or payment
  representation.

## Attribution and licensing

The original proof, exact diagnostic, and this port are attributed to `geofflava`. The original
contribution is licensed under both MIT and Apache-2.0, consistent with `LICENSE-MIT`, `LICENSE`,
and the repository contribution policy. No copyright is assigned by this contribution. Historical
or third-party material retains its original license and attribution boundaries.
