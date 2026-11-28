# Counting polynomial slopes at a multiple radial point

Let $B(X,Y)Y'=A(X,Y)$ in characteristic zero or characteristic $p>(m+2)(d+2)$. At a marked point translated to the origin, suppose the first nonzero homogeneous parts have the form
$$
 B_m=XQ_{m-1}(X,Y),\qquad A_m=YQ_{m-1}(X,Y)
$$
with $Q_{m-1}$ nonzero and $m\ge1$. A degree-at-most-$d$ polynomial solution through the origin has $Y=Xz$. Set
$$
 Q(X,z)=B(X,Xz)/X^m,\qquad P(X,z)=(A(X,Xz)-zB(X,Xz))/X^{m+1}.
$$
Then $Qz'=P$. Write $q=Q(0,z)$, $p_0=P(0,z)$, $l=\deg q\le m-1$, and let $a$ be the number of distinct finite roots of $q$ over the algebraic closure. Let $b$ count the roots of $q$ at which $p_0\ne0$. If **$b>0$**, then the number of polynomial solutions with $q(Y'(0))\ne0$ is at most
$$
                         (m+1+b)d+1-a .
$$
There are at most $a$ other possible slopes. Several solutions can have a common one of these exceptional slopes. The [ordinary radial bound](radial-ode-slope-cap.md) handles $m=1$ via the direction at infinity.

For a generic initial slope $s$, write $z=\sum_{j\ge0} c_j(s)X^j$ to the required finite order. Each $c_j$ is rational in $s$ and has poles only at the zeros of $q$ and infinity, by recursion from $Q(0,s)=q(s)$. Regular initial slopes determine at most one polynomial of degree at most $d$.

At a root $s_*$ of multiplicity $\nu$, put $s=s_*+\epsilon$, $z=s_*+\epsilon Z$, $X=\epsilon^\gamma t$, where $\gamma=\nu+1$ if $p_0(s_*)\ne0$ and $\gamma=\nu$ otherwise. After rescaling the coefficient of $Z'$ is $\epsilon^{-\nu}Q(\epsilon^\gamma t,s_*+\epsilon Z)$, and the right side is $\epsilon^{\gamma-1-\nu}P(\epsilon^\gamma t,s_*+\epsilon Z)$. Both are regular in $\epsilon$. In the second case the needed factor of $\epsilon$ in $P$ follows from $p_0(s_*)=0$ and $\gamma\ge1$. With $Z(0)=1$ the leading denominator at $t=0$ is a unit in the power-series ring in $\epsilon$. Its recursion therefore gives pole order at most $\gamma j-1$ for $c_j$ when $j\ge1$.

At a root counted by $b$, setting $\epsilon=0$ gives $c Z^\nu Z'=p_0(s_*)$ with $c\ne0$. The coefficient of $t^d$ in its solution $(1+(\nu+1)p_0(s_*)t/c)^{1/(\nu+1)}$ is nonzero under the characteristic hypothesis. Consequently $c_d$ has an actual pole there and is not identically zero.

At infinity take $s=\epsilon^{-1}$, $z=\epsilon^{-1}Z$ and $X=\epsilon^{m+1-l}t$. The $X^i$ coefficients of $Q$ and $P$ have degrees at most $m+i$ and $m+i+2$, respectively. After multiplying $Q$ by $\epsilon^l$ and $P$ by $\epsilon^{l+m+2-l}$, the rescaled equation again has regular coefficients. For $Q$ the constant coefficient has degree $l$, and the $i=1$ coefficient requires exactly the stated scaling bound. At $Z(0)=1$ the resulting leading denominator is a unit at $\epsilon=0$. Thus the pole order of $c_j$ at infinity is at most $(m+1-l)j+1$.

Adding the pole orders at the finite roots and infinity gives total height at most $(m+1+b)j+1-a$ for $c_j$. Since $Y=Xz$, every polynomial solution of degree at most $d$ at a regular initial slope must have $c_d(s)=0$. Counting the zeros of this nonzero rational function proves the bound. [Finite pole-order controls](../../../scripts/probes/probe_radial_ode_multiple_directions.py)
