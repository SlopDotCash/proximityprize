# Counting the quadratic component at the second sixteenth-rate budget

At the second designated prime, every radius-**820,050,000** closed list ball
of the length-$n=2^{30}$, dimension-$n/16$ Reed–Solomon code has at most
$2n$ words. The first failing error count is therefore at least
**820,050,001**, an increase of **248,118** over the
[preceding bound](sixteenth-list-factor-contact-orders.md). The argument
works on every injective grid in this field and at every positive finite
interleaving width. It does not settle the exact threshold or change the
first designated prime's budget-$n$ bound.

Put $d=n/16-1$, $t=n-820050000$, $P=9t$, $b=\lfloor(P-1)/(d-1)\rfloor=34$
and $L=\lfloor n/20\rfloor$. Use the established scalarization, first-order
interpolation and assignment of candidate jets to irreducible factors over
the coordinate function field. The primary slot surplus at order 9 and
derivative cap 4 is 587,179,205. Write $g$ for the squarefree product of the
positive-derivative factors assigned at least $L$ words. If $v=\deg_V g$
and $D$ is its weight for weights $(1,d,d-1)$, at most $(4-v)L+b$ assigned
words lie outside its groups. [Interpolation, factor grouping and quotient bounds](sixteenth-list-joint-quotient.md)

## The degree-two alternative

Consider $v=2$ and $7(d-1)\le D\le13(d-1)$. There are just two possibilities
for the product $g$.

* If it splits into two factors of $V$-degree one, let their total
  $(Y,V)$-degrees be $B_1,B_2$. Their sum $B$ is at most 13. Applying the
  [normalized curve count](first-order-normalized-curve.md#the-derivative-on-the-smooth-curve)
  separately at $v=1$ bounds the assigned populations in their union by
  $$3B-2+(2B-4)d+2(n-d)/(t-d).$$
  Adding $2L+b$ outside gives at most 1,583,769,249 words, including possible
  singular solutions. Here the sum of the two linear counts is appreciably
  smaller than the generic degree-two bound for a product of the same degree.
* If $g$ is irreducible, any list of more than $2n$ words assigns at least
  $M=2n+1-2L-b=2,040,109,433$ words to this single factor. After removing its
  singular jets at least $M-b^2$ remain. Use secondary contact order
  $r=24000$, and either $(h,\lambda)=(6440,2424)$ or $(6750,2070)$ on each
  of 256 weight intervals. The multiplicity at a site of primary contact
  order $o$ is $q=\max(0,r-\lambda o)$. For an integer gap $a\in\{1,2,3,4\}$
  take $w=(r-a)t-\lambda(t+D-d+1)$. The
  [weighted-agreement estimate](sixteenth-list-factor-contact-orders.md#a-site-order-that-decreases-with-the-primary-contact)
  gives at least $(M-b^2)at/(rt-w)$ words of weighted agreement at least
  $w$. The verifier compares this strictly with
  $2\lfloor(w-1)/d\rfloor+hb$, the mixed resultant degree. It also tests the
  concave lower bound on the quotient dimension at both endpoints. The least
  verified surplus in this entire interval is 15,117,218,237,572. The new
  population bound is needed here: using $L$ for $M$ makes these same two
  interpolation choices fail already on the first interval.

## The other weights

The existing contact-order comparisons apply with the parameters above.
For $v=1$ the linear comparison excludes $D\ge10d-1$. A linear product of
total degree $B$ has weight at least $Bd-1$, so the remaining total degree
is at most 9. For $v\ge2$ every product has weight at least $(d-1)B$.

| $v$ | High weights excluded through $P-1$ | Least verified surplus | Lower-degree case counted directly |
|---|---|---:|---:|
| 1 | $D\ge10d-1$ | 958,324,435,813,315 | $B\le9$ |
| 2 | $D\ge13(d-1)$ | 1,084,229,666,973 | $B\le6$ |
| 3 | $D\ge5(d-1)$ | 639,730,963,527 | $B\le4$ |
| 4 | $D\ge5(d-1)$ | 3,213,209,551,885 | $B\le4$ |

In each lower-degree case apply the normalized curve count at that total
degree and add $(4-v)L+b$; the sum fits the literal budget $2n$. The
degree-two alternative fills the interval between the low and high ranges.
If $g$ is empty, $4L+b$ suffices. The field characteristic exceeds the
interpolation orders, weights and curve regularity requirements in the
cited comparisons. No new assumption on the received word is used.

Run `python3 scripts/probes/probe_sixteenth_quadratic_population.py` to check
the primary, the resultant comparisons and all endpoint surpluses with exact
arithmetic. The factor geometry and interpolation implications are the
written arguments linked above.
