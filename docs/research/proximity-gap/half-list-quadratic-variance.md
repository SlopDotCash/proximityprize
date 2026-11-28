# Half-rate list safety from a second moment of the contact orders

At either named prime, every closed ball through **315,391,700 errors** at rate $1/2$ has at most **1,800,015 words**. Its first failing error count is therefore at least **315,391,701** for each of the two field-specific budgets $n$ and $2n$. The result holds on every injective length-$n$ grid and at every positive interleaving width. [Exact verifier](../../../scripts/probes/probe_half_list_quadratic_variance.py)

Use the notation and linear coefficient bounds of the preceding half-rate proof, now with $t=\lfloor\sqrt{nd}\rfloor-900000$, $L=900000$, and secondary order $r=40000$. The primary order remains eleven, its derivative degree cap is two, and its surplus is **110,544,294**. The total jet degree bound is $b_0=15$. Every group of at least $L$ words exceeds the generic secondary Bézout bound. [Linear coefficient inequalities and the quotient test](half-list-coefficient-derivatives.md)

Suppose the primary factor $g$ has derivative degree two and weight $w$. Write it as $A_0+A_1V+A_2V^2$, and let $o$ be its local contact order. The $z_1^2$ coefficient of $g(x+u,y+uz,z+uz_1)$ gives ordinary plane multiplicity at least $(o-2)_+$ for $A_2$. The coefficients of $z_1$ and $1$ successively give the same lower bound for $A_1$ and $A_0$.

Choose a constant $\lambda$ in the algebraic closure so that $A_2$ and $A_0+\lambda A_1$ are relatively prime. Such a choice exists because the three coefficients have no common nonconstant divisor, and only finitely many choices can introduce any given irreducible factor of $A_2$. Put $a=\lfloor(w-2(d-1))/d\rfloor$ and $b=\lfloor w/d\rfloor$. The weighted Sylvester estimate for these two polynomials bounds their total local intersection multiplicity on the grid by $nI$, where
$$
                   I=[aw+b(w-2(d-1))-dab]/n.
$$
The usual product bound on the local intersection multiplicity is at least $(o-2)_+^2$ at each site. It also follows by the local quotient length: modulo powers of the maximal ideal of total degree $2m$, two equations vanishing to order $m$ impose at most $m(m+1)$ conditions in a space of dimension $m(2m+1)$. Thus
$$
                   \mathbb E(o-2)^2\le I+4 .
$$
The extra four permits $o=0$ or $1$. The Sylvester estimate includes specialization degree drops, and its right side is nondecreasing in both degree caps. [Weighted resultant and local length](linear-contact-quotient.md)

Remove the at most $b_0^2$ singular generic jets and use the group occupancy $p$ from the preceding proof, with mean $s=t/n$ and variance at most $\sigma^2=d/n-s^2+(s-d/n)/(L-b_0^2)$. The nonzero evaluation of $g_V$ gives $\mathbb E[p o]\le s+(w-d+1)/n$. For $c\ge2$ and $\theta>0$, Young's inequality gives
$$
 s\mathbb E o\le s+(w-d+1)/n+
          \frac{\sigma^2}{2\theta}+\frac{\theta}{2}\mathbb E(o-c)^2 .
$$
Expanding around $2$ and applying the second moment proves
$$
 [s+\theta(c-2)]\mathbb E o
 \le s+(w-d+1)/n+\frac{\sigma^2}{2\theta}
   +\frac{\theta}{2}\big[I+4+4(c-2)+(c-2)^2\big].
$$
For fixed $a,b,c,\theta$ this upper bound is affine in $w$. On each interval of fixed degree caps, one choice of these parameters and a secondary derivative cap gives positive quotient surplus at both endpoints. Concavity gives the full interval.

Across **28** quadratic weight intervals the smallest endpoint surplus is **8,392,250,490,539,212**. For linear factors the preceding coefficient and content proof gives a surplus of at least **4,178,202,201,860** on **179** low-weight intervals, and at least **125,376,114,617,475,152** at weights from $13d$ up to the primary cutoff. When reusing pointwise rows of the preceding verifier with its slightly larger mean $s_0$, add $(s_0-s)\max Q_j$ to the corresponding right side. This follows from $\mathbb E[(s_0-s)Q_j]\le(s_0-s)\max Q_j$.

No positive-derivative factor carries a large group. At most two such factors and at most $b_0$ residual words therefore give the stated bound $2L+b_0=1800015$.
