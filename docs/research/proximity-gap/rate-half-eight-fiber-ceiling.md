# A rate-half MCA upper bound from four cubic polynomials

At length $n=2^{30}$, dimension $k=2^{29}$ and the first repository prime
$p=365375409332725729550921208179070755120141565953$, there are received
rows with at least $n+2$ distinct MCA-bad scalars at **335544321 errors**.
Since $\lfloor p/2^{128}\rfloor=n$, the operational rate-half supremum satisfies

$$
\delta^*\ \le\ \frac{335544321}{1073741824}
               =\frac5{16}+\frac1{2^{30}}.
$$

This improves the three-polynomial construction by 22,369,620 Hamming steps.
The unique-decoding lower bound remains below this value.
[Three-polynomial construction](rate-half-mobius-seams.md)

## The quotient polynomials

More generally, write $n=8s$ for even $s\ge4$. Let $F$ be a finite field
with $3(n+2)+1<|F|$ and an element $g$ of exact order $n$.
Use the domain $D=\langle g\rangle$, dimension $k=4s$ and $\omega=g^s$.
The fiber $D_j=\{x\in D:x^s=\omega^j\}$ has $s$ points for $0\le j<8$.

Put $f_0=0$. For the other three heads take

$$
R_1=\{3,6,7\},\quad R_2=\{3,5,7\},\quad R_3=\{4,5,6\},
\qquad B_i(Y)=\prod_{r\in R_i}(Y-\omega^r),\qquad
f_i(Y)=B_i(Y)/B_i(\omega^2).
$$

The following table gives the equality classes of the four values
$f_i(\omega^j)$. A string such as $023$ denotes heads $0,2,3$.

| $j$ | Equality classes | Class used for ordinary coordinates |
|---|---|---|
| 0 | $0,1,23$ | $23$ |
| 1 | $0,2,13$ | $13$ |
| 2 | $0,123$ | $123$ |
| 3 | $012,3$ | $012$ |
| 4 | $1,2,03$ | $03$ |
| 5 | $1,023$ | $023$ |
| 6 | $2,013$ | $013$ |
| 7 | $012,3$ | $012$ |

The specified zeros and the normalization at $\omega^2$ give all but two of
the required equalities. For the other two, direct multiplication in
$\mathbb Z[T]/(T^4+1)$, using $T$ for $\omega$, gives

$$
B_1(T)B_3(T^2)=B_3(T)B_1(T^2),\qquad
B_2(1)B_3(T^2)=B_3(1)B_2(T^2).
$$

These identities specialize because $\omega^4=-1$. The $B_i(\omega^2)$
are nonzero because the eight powers are distinct. Each pair of polynomials
is distinct by its zero set. Each pair already has three equality points in
the table, which exhaust the roots of its difference of degree at most three.

## Received rows and distinct bad scalars

Choose $s/2-1$ points from each of $D_0,D_1$ and form the monic product
$H$ of their linear factors. The four pairs of codeword polynomials are

$$
W_i(X)=(XH(X)f_i(X^s),\ H(X)f_i(X^s)).
$$

Their degrees are at most $1+(s-2)+3s=k-1$.
On the roots of $H$ put $u(x)=(0,0)$, so all four heads agree with $u$.
Reserve $s/2$ coordinates of $D_4$ for the construction below. At every
other coordinate put $u(x)=W_i(x)$ for any head from the indicated ordinary
class. Every unmatched head has the same mixed value as $u$ at the scalar
$-x$, since all four head vectors and $u(x)$ lie on the line
$\{(xv,v):v\in F\}$. Assign the label $-x$ to one unmatched head there.
These ordinary labels are distinct across coordinates.

At a reserved coordinate $x$, the four heads have three distinct values
$(xv,v)$. Choose $u_1(x)$ different from all three $v$ and choose
$u_0(x)\ne x u_1(x)$. The scalar making each value agree with the mixed row
is

$$
\gamma_v=(xv-u_0(x))/(u_1(x)-v).
$$

For $v\ne v'$ their equality would force $u_0(x)=x u_1(x)$. To preserve
distinction across coordinates, assign the ordinary labels first and then
process the reserved coordinates in any order. Each previously used label
and each $v$ forbid one choice of $u_0(x)$. Together with the single
off-line restriction, fewer than $|F|$ values are forbidden by the assumed
field size. Thus each reserved coordinate supplies three new labels and
jointly matches no head.

At the production prime there is also a choice made simultaneously for all
reserved points. Write $c$ for one of the three distinct $f_i(\omega^4)$,
choose $\tau$ different from all three, and set
$u(x)=(H(x)(x\tau-t),H(x)\tau)$. The resulting labels are
$-x+t/(\tau-c)$. Together with the ordinary labels these have four distinct
coefficients of $t$, counting zero. For any two different coefficients, a
collision restricts $t$ to a scalar multiple of the difference set
$D-D$, of size at most $n^2$. There are six pairs, and $6n^2<p$.
Choose $t$ outside their union. This also excludes zero, and labels with
the same coefficient are already distinct for different $x$.

The number of distinct assigned labels is
$n-(s-2)-s/2+3s/2=n+2$. Let $C_i$ be the coordinates on which the two
received rows jointly match $W_i$. Counting in the table gives

$$
(|C_0|,|C_1|,|C_2|,|C_3|)
=(11s/2-2,\ 11s/2-1,\ 11s/2-1,\ 11s/2).
$$

For each assigned label choose its head $i$ and its fresh coordinate $x$.
The mixed head $W_{i,0}+\gamma W_{i,1}$ agrees on $C_i\cup\{x\}$.
This set has at least $11s/2-1$ points. A pair of degree-below-$k$
polynomials jointly explaining these rows there would equal $W_i$, since
each component already agrees on at least $k$ distinct core points.
That contradicts the explicit mismatch at $x$. Hence every label is MCA-bad
at $n-(11s/2-1)=5s/2+1$ errors. Monotonicity gives the claimed upper
bound at the first sponsor parameters.

## Integer bound for this allocation

Within this eight-fiber table, the smallest core cannot be improved to
$11s/2-1$ using at most $s-2$ common roots and charging one fresh coordinate
per scalar. Let $E=|C_0|+|C_1|+|C_2|$, let $R$ count roots and let $L$
count labels at one per ordinary point and one per distinct head value per
off-line point. Coordinate by coordinate, the maximum contribution to
$2E+L-3R$ is respectively $3,3,5,7,3,5,5,7$ on the eight fibers.
Thus $2E+L-3R\le38s$. If $L\ge8s+1$ and $R\le s-2$, then
$E\le 33s/2-4$. Three cores all at least $11s/2-1$ would exceed this.
The bound concerns these cubic heads and this assignment rule.

## Reproduction

Run `python3 -O scripts/probes/probe_rate_half_eight_fibers.py`.
The script checks both cyclotomic identities over the integers, the actual
quotient values modulo the first sponsor prime, every slot bound and the
production counts. At lengths 32, 64 and 256 in the same field, it constructs
the rows explicitly and checks every bad-scalar witness. The length-$2^{30}$
conclusion uses the symbolic construction and count above.
