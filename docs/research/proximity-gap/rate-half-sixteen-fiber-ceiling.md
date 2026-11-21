# A rate-half MCA ceiling of 19/64

For the first prime $p=365375409332725729550921208179070755120141565953$,
length $n=2^{30}$ and dimension $k=2^{29}$, there are two received rows with
at least **1,073,741,826 distinct MCA-bad scalars at 318,767,104 errors**.
This gives the operational supremum bound $\delta^*\le19/64$. The preceding
eight-fiber bound was 335,544,321 errors. The exact threshold still requires
a matching lower bound. [Eight-fiber construction](rate-half-eight-fiber-ceiling.md)

## Four polynomial pairs

Write $n=16s$, where $4\mid s$ and $s\ge4$. Let $g$ have order $n$ in a
finite field $F$, put $D=\langle g\rangle$, and take dimension $k=8s$.
The construction below gives $n+2$ bad scalars whenever $|F|>3(n+2)+1$.
Put $\omega=g^s$. Each fiber $D_j=\{x\in D:x^s=\omega^j\}$ has $s$ elements.
Define $P_R(Y)=\prod_{r\in R}(Y-\omega^r)$ for the following sets:

$$
A=\{0,1,2,3,4,9,11\},\quad B=\{0,3,5,10,11,12,13\},
\quad C=\{1,4,5,9,12,13,14\}.
$$

Take the four polynomials

$$
f_0=0,\quad f_1=P_A,\quad
f_2=\frac{P_A(\omega^6)}{P_B(\omega^6)}P_B,\quad
f_3=\frac{P_A(\omega^7)}{P_C(\omega^7)}P_C.
$$

Both scale factors are nonzero because their evaluation points avoid the
indicated root sets. Here are the exact equality classes at each fiber
and the number of coordinates assigned to each action. Digits such as
$013$ mean that the normal received value matches heads 0, 1 and 3.

| $j$ | Classes | Allocation |
|---|---|---|
| 0, 3, 11 | $012,3$ | all $012$ |
| 1, 4, 9 | $013,2$ | all $013$ |
| 5, 12, 13 | $023,1$ | all $023$ |
| 7, 8, 15 | $0,123$ | all $123$ |
| 2 | $01,23$ | $s/2$ to each pair |
| 10 | $02,13$ | $s/2$ to each pair |
| 6 | $0,12,3$ | $s/4-1$ roots, $s/4+1$ to $12$, $s/2$ off-line |
| 14 | $03,1,2$ | $3s/4-1$ roots, $s/4+1$ to $03$ |

One way to check all the table entries in integer arithmetic is to replace
$\omega$ by $T$ modulo $T^8+1$. Represent $T^j$ by $e_j$ for $0\le j<8$
and $-e_{j-8}$ for $8\le j<16$. Multiply coefficient vectors by convolution
with $e_{i+8}=-e_i$. For each fiber form the four numerator vectors and
the denominators $1,1,P_B(T^6),P_C(T^7)$ as in the formulas above, then
cross-multiply each pair. The equality sets for pairs $01,02,03$ are
$A,B,C$. Those for $12,13,23$ are respectively

$$
\{0,3,6,7,8,11,15\},\quad
\{1,4,7,8,9,10,15\},\quad
\{2,5,7,8,12,13,15\}.
$$

The integer-ring check below tests these identities before reduction to the
first prime. They persist on specialization since $\omega^8=-1$. There
are seven certified equalities for each pair. The polynomials are distinct
by their zero sets, so their degree bound seven rules out further equalities.

Let $H$ be the monic product of the linear factors for the selected roots
in fibers 6 and 14. Its degree is $s-2$. Put

$$W_i(X)=(XH(X)f_i(X^s),\ H(X)f_i(X^s)).$$

Both entries have degree at most $1+(s-2)+7s=8s-1$.

## Receiving and counting

At the roots receive $(0,0)$. At a normal coordinate receive the vector
$W_i(x)$ from its assigned class. Every head outside that class has the
same scalar combination with the received rows at $\gamma=-x$, since
all the vectors at $x$ have form $(xv,v)$. Assign $-x$ to one such head.
Different normal coordinates yield distinct labels.

At an off-line coordinate the heads have three distinct vectors $(xv,v)$.
Choose $u_1$ different from the three $v$ values and choose $u_0\ne x u_1$.
Mixing the received rows and a head agrees at the scalar
$\gamma_v=(xv-u_0)/(u_1-v)$. For two different $v$ these scalars are distinct.
After assigning all normal labels, process the off-line coordinates one
at a time. For any earlier label and each of the three $v$ values, at most
one $u_0$ would reuse that label. The field-size hypothesis leaves an
available $u_0$ after also excluding $x u_1$. None of these points jointly
matches any head. At the first prime one may alternatively use the common
parameter choice in the eight-fiber proof because $6n^2<p$ and all off-line
points lie in one fiber.

There are $s-2$ roots and $s/2$ off-line points. The assigned labels total
$n-(s-2)-s/2+3s/2=n+2$. Each head has a joint agreement set $C_i$ of
size exactly $45s/4-1$. Indeed, the twelve triple fibers give $9s$ to
each head, the two equally split fibers give another $s$, and the roots
give $s-2$. Each head also belongs to exactly one of $12,03$, which gives
$s/4+1$ more. This sums to $45s/4-1$.

For each assigned label let $x$ be its coordinate and $i$ its chosen
unmatched head. The mixed polynomial from $W_i$ agrees on
$C_i\cup\{x\}$, a set of size $45s/4$. A joint explanation on this set
must equal $W_i$ in both rows because the two components agree there on the
$|C_i|\ge k$ core points and have degree below $k$. The mismatch at $x$
precludes that explanation. This is an MCA-bad witness at
$n-45s/4=19n/64$ errors. At the first prime,
$\lfloor p/2^{128}\rfloor=n<n+2$.

For this fixed table and slot rule, this core size is integer-optimal.
Let $E$ sum the four core sizes, $L$ count the labels supplied and $R$
count the roots. On each point of a triple fiber $E+L-R$ gains at most
four. On each point of the other four fibers it gains at most three.
Thus $E+L-R\le60s$. The requirements $L\ge16s+1$ and $R\le s-2$ force
$E\le45s-3$. At least one of the four integer core sizes is at most
$45s/4-1$.

## Reproduction

Run `python3 -O scripts/probes/probe_rate_half_sixteen_fibers.py`.
At the production parameters the script checks every pair of quotient
polynomials, obtains four joint cores of size 754,974,719, and verifies
the integer threshold and label budget. It constructs the full received
rows and checks every witness individually in the same field at lengths
64, 128 and 256. The counts there are 66, 130 and 258 labels at 19, 38 and
76 errors. The production-size argument is the symbolic count above.

## Rigidity under further power-map lifts

Fix the first head as zero by subtracting it from all four heads. Each of the twelve triple classes imposes two linear conditions on the 24 coefficients of the other three degree-seven heads. The probe row-reduces this matrix over the production prime and obtains rank 23. Its nullspace is therefore exactly the span of the displayed three polynomials.

This rules out a deformation that keeps every lifted triple agreement. Suppose the domain of order $16r$ maps onto the sixteen quotient points under $X\mapsto X^r$. Write a candidate head of degree below $8r$ as $\sum_{j<r}X^jP_j(X^r)$, with $\deg P_j<8$. At a prescribed triple value $y$, a head difference vanishes on all $r$ roots of $X^r=y$. Its remainder $\sum_{j<r}X^j(P_j(y)-P'_j(y))$ vanishes identically, as its degree is below $r$. Thus each of the $r$ triples of coefficient polynomials satisfies the original rank-23 system. All three lifted heads have the form $H(X)f_i(X^r)$ for one common $H$ of degree below $r$. Away from its roots the equality classes are those of the original table. A different construction must change at least one lifted triple or leave this degree range.
