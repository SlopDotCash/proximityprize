# Choosing secondary multiplicities from the primary factor's contact order

At rate $1/16$ and length $n=2^{30}$, every closed ball through **819,801,882 errors** contains at most $n$ words on either named field. This holds on every injective grid and at every positive interleaving width. Thus the first failure occurs at or after **819,801,883 errors**, for the first field's budget $n$ and the second field's budget $2n$. The respective increases in these lower bounds are 1,073,742 and 536,871. The exact thresholds remain open. [Exact verifier](../../../scripts/probes/probe_sixteenth_factor_contact_orders.py)

Write $d=n/16-1$, $t=\lceil473n/2000\rceil$, $L=\lfloor n/13\rfloor$, $P=9t$ and $b=\lfloor(P-1)/(d-1)\rfloor$. Use the standard scalarization and weights $1,d,d-1$ on $X,Y,V$. As before, $N(w,h)$ denotes the number of monomials of weight strictly below $w$ and derivative degree at most $h$, and $C(r,h)$ denotes the unrestricted local contact rank. The primary inequality $N(P,4)>nC(9,4)$ supplies an interpolant containing all the jets. Assign candidates to irreducible factors. Form the product $g$ of distinct positive-derivative factors assigned at least $L$ candidates. Put $v=\deg_Vg$ and let $D$ be its weight. At most $(4-v)L+b$ words remain outside the assigned large groups. [Primary and local ranks](sixteenth-list-quotient-jets.md) · [Grouping](sixteenth-list-joint-quotient.md)

## A site order that decreases with the primary contact

Let $o_x$ be the order of $g$ at the received point under the substitution $X=x+U$, $Y=y+Uz$, $V=z+Uw$. At each large factor remove the at most $b^2$ assigned jets on $g_V=0$. For each remaining word choose exactly $t$ of its agreement sites. If $p_j(x)$ denotes the fraction of the $j$th group selecting site $x$, then
$$
 \sum_x p_j(x)=t,\qquad \sum_x p_j(x)o_x\le t+D-d+1.
$$
The second inequality follows by evaluating $g_V$ on each word. This nonzero polynomial has degree at most $D-d+1$ and order at least $o_x-1$ at every chosen hit. At every site $o_x\le D/d+v$ because $g$ has no vertical fiber factor. [Derivative and local order bounds](sixteenth-list-quotient-jets.md#bounding-the-mean-contact-order)

Fix $r=3000$, positive integers $h\ge v$ and $\lambda$, and an integer gap $a\in\{1,2,3,4\}$. Set
$$
 q_x=\max(0,r-\lambda o_x),\qquad w=(r-a)t-\lambda(t+D-d+1).
$$
In every large group the mean weighted agreement is at least $rt-\lambda(t+D-d+1)=w+at$. Every weighted agreement is at most $rt$, so at least $(L-b^2)at/(rt-w)$ members of **each** large group have weighted agreement at least $w$.

Impose that at site $x$ the secondary interpolant of derivative degree at most $h$ belongs to the local image of multiples of $g$ through order $q_x$. This imposes at most $C(q_x,h)-C(q_x-o_x,h-v)$ conditions. The total cost is bounded above by
$$
 n\max_{0\le o\le\lfloor D_{\max}/d\rfloor+v}
      [C(q,h)-C(q-o,h-v)],\qquad q=\max(0,r-\lambda o),
$$
where $D_{\max}=P-1$. Here $C(k,h)=0$ for $k\le0$. If this cost is strictly below $N(w,h)-N(w-D,h-v)$, the quotient construction supplies a secondary polynomial of weight below $w$ that is coprime to at least one large factor. It vanishes on all eligible members of every group by their weighted agreements. For the coprime factor the nonzero resultant in $V$ has $Y$-degree at most $v\lfloor(w-1)/d\rfloor+hb$. The verifier checks that each group has strictly more eligible words. [Local quotient and mixed resultant](sixteenth-list-joint-quotient.md#finite-quotient-comparisons)

## A quadratic lower bound throughout the weight interval

For $z\ge0$, put $u=\{z/d\}$. Summing the positive parts in a monomial row gives
$$
 \sum_{j\ge0}(z-jd)_+=\frac{z^2+dz}{2d}+\frac d2u(1-u).
$$
The last term lies in $[0,d/8]$. Sum the first term over $z=w-k(d-1)$ for $0\le k\le h$ and call the result $S(w,h)$. On all certified intervals the verifier checks $w-D\ge h(d-1)$, so the row formula applies to both dimensions. Thus
$$
 N(w,h)-N(w-D,h-v)\ \ge
 S(w,h)-S(w-D,h-v)-(h-v+1)d/8 .
$$
Substituting $w=(r-a)t-\lambda(t+D-d+1)$ makes this lower bound quadratic in $D$. Its quadratic coefficient is $[v\lambda^2-(h-v+1)(2\lambda+1)]/(2d)$, which is nonpositive for every board used. On each of 256 weight intervals the same $(h,\lambda,a)$ serves at both endpoints. The upper cost is constant on that interval, and the lower bound is concave. For eligibility use the smaller group count at the right endpoint and the larger resultant degree at the left. The following are the least verified surpluses after rounding down.

| Derivative degree | Range of weights | Least quotient surplus |
|---:|:---|---:|
| 2 | $6d-2\le D<P$ | 1,070,816,294,126 |
| 3 | $4(d-1)\le D<P$ | 6,614,665,992,695 |
| 4 | $4(d-1)\le D<P$ | 5,219,311,400,734 |

## The remaining groups

For $v=2$ and $4(d-1)\le D\le6d-2$, use the contact constraints on the coefficient of $V^2$ and its ordinate Hasse derivatives, including the three-slope bound at sites with $o_x\le1$. The verifier reruns the ordinary secondary order $6000$ with the $d,t,b,L$ of this proof and the rational combinations stored for these parameters. The smallest certified surplus is **5,166,568,239,981**. [Coefficient-contact proof](eighth-list-quadratic-coefficient-contacts.md#contacts-of-the-quadratic-coefficient)

For $v=2,3$ the surviving product has total degree at most three. In both cases the normalized differential-curve bound plus $(4-v)L+b$ fits $n$. Derivative degree four requires weight at least $4(d-1)$, already excluded. For $v=1$ the ordinary linear coefficient intersection comparison at order $3000$ excludes $D\ge8d-1$. Total degree is therefore at most seven. Its list contribution is at most $\max(7+12d,(n-d)/(t-d))$. Adding $3L+b$ fits $n$. Finally $4L+b\le n$ when no positive-derivative factor is large. Both named characteristics satisfy the degree conditions throughout. [Normalized curve bound](first-order-normalized-curve.md) · [Linear coefficient comparison](linear-contact-quotient.md)

Run the finite certificate with `python3 scripts/probes/probe_sixteenth_factor_contact_orders.py`.
