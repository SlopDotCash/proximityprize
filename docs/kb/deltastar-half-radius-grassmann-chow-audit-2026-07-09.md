# Delta-star half-radius predecessor: Grassmann/Chow audit (2026-07-09)

## Target and exact coordinates

Write `n = 2h`.  The one-lattice-step predecessor of radius `1/2` has agreement
threshold

```text
t = h + 1,      error support size <= h - 1.
```

For `RS[n,k]`, use a parity-check matrix whose projective columns are the
Vandermonde points

```text
v(x) = (1,x,...,x^(n-k-1)).
```

For an error support `E`, let `V_E = span{v(x):x in E}`.  A scalar `gamma` on a
syndrome line `L = s0 + gamma*s1` has a nonjoint witness with complement `E` iff

```text
s0 + gamma*s1 is in V_E,       but the whole line L is not contained in V_E.
```

Thus the desired good side is the finite-geometry statement

```text
# {gamma : L meets some (h-2)-plane V_E nontrivially/nonjointly} <= 2h.
```

The support locator `Lambda_E(X)` has degree `h-1`.  Its truncated recurrence
kernel is the kernel of a Hankel pencil.  The vector dimension of this kernel is
generically `k-1`, so for `k>2` it is a genuine projective plane (or higher flat),
not a Cramer point.  This is exactly where the degree-`n` argument for `k=2`
stops: a naive compound-matrix/Chow form pays for all points of a kernel plane and
recovers an exponential or binomial loss.

## Lifted heavy-hyperplane formulation

Interpolate each word row on the domain and instead lift every coordinate to

```text
r_x = (u0(x), u1(x), 1, x, ..., x^(k-1)) in F^(k+2).
```

If `f_gamma` is the decoded degree-`<k` polynomial, put

```text
P_gamma = (1, gamma, -coeff(f_gamma)).
```

Then `x` belongs to the agreement set `S_gamma` exactly when
`r_x dot P_gamma = 0`.  The nonjoint clause has an important sharp consequence:
the rows indexed by `S_gamma` span that hyperplane.  Indeed, a second kernel
normal with independent first two coordinates would give separate degree-`<k`
explanations of `u0` and `u1`; a kernel normal with first two coordinates zero is
a degree-`<k` polynomial vanishing on at least `h+1 >= k` points and is zero.

So every bad scalar is a distinct, uniquely-normalized hyperplane containing at
least `h+1` of the `2h` lifted points.

Two exact intersection laws follow.

1. If three decoded normals are not collinear, their common agreement set has
   size at most `k-1`.  Their common annihilator has vector dimension `k-1`, while
   any `k` lifted rows are independent because their last `k` coordinates form a
   Vandermonde matrix.
2. If `L` decoded normals lie on one affine line
   `f_gamma = f0 + gamma*f1`, their agreement sets form a sunflower.  The core is
   the set where both translated rows vanish; outside the core each coordinate
   belongs to at most one petal.  If the core has size `z`, then

   ```text
   L * (h + 1 - z) + z <= 2h.
   ```

These are the precise inputs for the rich-line/third-moment route.  They also
explain the sharp packing family: two `h`-point decoded-normal lines, each with an
`h`-point core and singleton petals.

## Why a bare Chow/split-fibre count is insufficient

The toy pencil `K(gamma,X) = X - gamma^2` is the basic red team.  Its fibres split
over a fixed domain whenever `gamma^2` lies in that domain, and the gamma-degree
is two.  It can therefore produce twice the domain-size incidence count.  Any
claim of `<= n` must use the Hankel/Vandermonde origin of the kernel plane or the
nonjoint heavy-hyperplane condition; “the locator splits over the domain” alone
does not imply it.

At `k=2`, the kernel is one-dimensional and the usual bidegree count is valid:
the Cramer locator has gamma-degree at most `h-1`; every split fibre contributes
`h-1` domain roots; and there are at most `n(h-1)` point-fibre incidences.  This
recovers `#bad <= n`.  The higher-corank case needs a different invariant.

## Machine-checked finite calculations (Python, exact modular arithmetic)

The reproducible probe is

```text
scripts/probes/probe_half_radius_grassmann.py
```

Observed results:

* `(n,k,h-1,p)=(8,2,3,17)`: the full radius-3 syndrome ball was enumerated;
  500,000 sampled ball-secants had maximum exactly `8` bad scalars.
* The same cell over `p=97` (300,000 support-secants) and `p=257` (100,000)
  again had maximum `8`, attained by packing.
* `(n,k,h-1,p)=(16,4,7,97)`: all `C(16,8)=12,870` packing half-blocks were
  exhausted.  Every block gives exactly `16` bad scalars, with no accidental
  seventeenth.  Another 100,000 arbitrary support-secants found no value above
  `16`.
* A pencil with a two-root common factor lies in many half-support spans.  It
  creates 45 different support representations for each of several scalars, but
  only 14 distinct bad scalars.  The extra support intersections collapse to the
  same values `gamma = -f0(x)/f1(x)`.  This falsifies a support-count argument but
  supports a distinct-scalar bound.

Run the two exact adversarial modes with

```text
python3 scripts/probes/probe_half_radius_grassmann.py --packing-extension
python3 scripts/probes/probe_half_radius_grassmann.py --witness-trade
```

### Exact packing-extension census

Over `F_17`, impose the 16 packing scalars and their nine-point witnesses as a
linear system in the 32 word-row coordinates.  Its kernel has dimension 11.  For
the unused scalar `gamma=0`, all `C(16,9)=11,440` possible nine-point witnesses
were tested.  The enlarged-kernel histogram is

```text
nullity 8:  10,976
nullity 9:     448
nullity 10:     16
```

Every extension forces at least one prescribed witness to become joint.  The 16
nullity-10 supports are exactly the existing packing supports; both `gamma=0` and
the old scalar using that support are forced joint.  The test is exact: if none of
the at most `q=17` joint subspaces were forced, the standard finite-vector-space
covering lemma would supply a vector outside their union.

## A failed rank conjecture and its exact counterexample

The attractive conjecture

```text
for any choice of one witness S_gamma per bad scalar,
the vectors 1_{S_gamma} are Q-linearly independent
```

is false.

Over `F_17`, `n=16`, `k=4`, domain `3^i`, take

```text
C  = {0,1}
A0 = {2,3,4}        A1 = {5,6,7}
B0 = {8,9,10,11}    B1 = {12,13,14,15}

S1 = C union A0 union B0
S2 = C union A1 union B1
S3 = C union A0 union B1
S4 = C union A1 union B0.
```

Then

```text
1_S1 + 1_S2 = 1_S3 + 1_S4.
```

For scalars `(1,2,3,4)`, the word rows

```text
u0 = [0,0,2,13,12,5,15,0,7,16,5,7,0,0,0,0]
u1 = [0,0,5, 7,13,6, 1,0,0, 0,0,0,0,0,0,0]
```

make each line word degree-`<4`-fit on its displayed `S_i`, while `u1` is not
degree-`<4`-fit there.  Hence all four are genuine nonjoint MCA witnesses, but
the displayed incidence matrix has rank three.

The stronger red team is informative rather than fatal to every rank route.  The
complete witness census of this stack is

```text
gamma 1: 10 witnesses
gamma 2:  1 witness
gamma 3: 10 witnesses
gamma 4:  1 witness
```

and some alternative choice of one witness per scalar has full rank four.  Thus
the following weaker target survives this counterexample.

## Surviving exact conjectures

### Independent-transversal conjecture

For every bad-scalar set `G`, let `W_gamma` be the family of incidence vectors of
all nonjoint witnesses for `gamma`.  There is a choice
`w_gamma in W_gamma` such that the chosen vectors are linearly independent over
`Q`.

By Rado's linear-transversal theorem, this is equivalent to the family of rank
inequalities

```text
dim_Q span(union_{gamma in J} W_gamma) >= |J|
```

for every subset `J` of bad scalars.  It would immediately give `#bad <= n` and
is compatible with both the packing family and the witness-trade counterexample.
It is not proved.

### Rich-flat weighted-rank conjecture

A weaker alternative is to charge every incidence-rank defect to affine circuits
of the decoded normals.  Collinear circuits are already controlled exactly by the
sunflower inequality above; the four-witness trade is a rank-three affine-plane
circuit and exhibits the first higher-flat correction.  A successful inequality
must count such rank-`r` clusters with the sharp common-codegree cap `k+2-r`, not
pay the naive compound-matrix degree.

### Max-`n` predecessor conjecture

For every field/domain in the prize regime, every even `n`, and `2 <= k <= n/4`,
the nonjoint bad-scalar count at agreement threshold `n/2+1` is at most `n`.
Packing proves sharpness.  The calculations here strongly support it but do not
prove it in production dimension.

## Current verdict

The pure Grassmann/Chow count does not close the higher-corank case.  The useful
new reduction is the lifted heavy-hyperplane geometry, with exact noncollinear
triple and collinear-sunflower laws.  Raw witness-incidence independence is
refuted; an independent transversal among all witnesses, or a weighted
rich-flat rank inequality, is the surviving route to the sharp `n` bound.
