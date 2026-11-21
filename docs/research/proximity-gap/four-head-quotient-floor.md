# A radius floor for four heads on a power quotient

Let $D$ have $n=4h$ distinct field elements. Suppose the map $x\mapsto x^q$ on $D$ has $M$ fibers, every fiber has $q$ points, and $M$ is even. Choose four distinct polynomials of the form

$$P_i(X)=B(X)+H(X)f_i(X^q),\qquad i=0,1,2,3.$$

If each polynomial has degree below $2h$ and each agrees with a single scalar word at all but $e$ positions, then

$$4e\ \ge\ n+q+2.$$

For the two-row construction take $W_i=(B_0,B_1)+(A_0,A_1)Hf_i(X^q)$ of row degree below $2h$, where $A_0,A_1$ are coprime and $\max(\deg A_0,\deg A_1)\ge1$. The same inequality holds when every head has a joint core of size at least $n-e-1$ and more than $n$ distinct labels have fresh mixed agreements with these heads. For each such label a fresh agreement means that the received pair and the selected head differ at that coordinate but their scalar combination agrees. Here a label is assigned to one fresh coordinate. The required core sizes specify exactly how the sixteen-fiber construction uses its fresh agreements.

For the first prime with $n=2^{30}$ and $M=16$ this gives $e\ge285212673$. The verified sixteen-fiber construction supplies $e=318767104$. For $M=8$ the floor is $301989889$. Every power quotient with $q\ge3$ is excluded at $e=h+1$ for these families. The bound allows arbitrary choices of the four quotient polynomials, a common locator and the received rows. Arbitrary MCA witnesses need not have this form. [Sixteen-fiber construction](rate-half-sixteen-fiber-ceiling.md)

## Counting equalities on the quotient

Subtract $f_0$ from all four quotient heads and absorb its contribution into $B$ or $(B_0,B_1)$. Set $d=\max_i\deg(f_i-f_0)$ and $r=\deg H$. Write $s=1$ in the scalar problem and $s=2$ in the two-row problem. Taking the difference of two heads whose quotient difference has degree $d$, and using the largest-degree direction component in the two-row case, gives

$$r+qd+s\le n/2.$$

At a quotient input $y$ let $w(y)=2$ when all four values coincide, $w(y)=1$ when exactly three coincide and $w(y)=0$ otherwise. Consider the two nonzero products

$$U=(f_0-f_1)(f_2-f_3),\qquad V=(f_0-f_2)(f_1-f_3).$$

Both are divisible by $(X-y)^{w(y)}$ for each quotient coordinate. Their degrees are at most $2d$. If the two products are not proportional over the field, a nonzero member of their linear span has degree below $2d$, by cancellation of the top coefficient. It follows that $\sum_y w(y)\le2d-1$.

Write $m(x)$ for the number of heads matching the received scalar or received pair, $E=\sum_x m(x)$ and $z=|\{x:m(x)=0\}|$. In the scalar case, $m(x)+2\mathbf1_{m(x)=0}\le 2+w(x^q)+2\mathbf1_{H(x)=0}$. For paired heads coprimality makes the direction vector nonzero at every coordinate, giving the same inequality. Consequently in the nonproportional case

$$E+2z+q\le 2n+2(r+qd)\le3n-2s.$$

For scalar lists $E\ge4(n-e)$, giving $4e\ge n+q+2$. For the two-row case $E\ge4(n-e-1)$. At a position with $m(x)>0$ the receiver equals one head, so any other differing head can give at most the single scalar canceling the common direction at $x$. Thus more than $n$ distinct fresh labels require $z\ge1$, and again $4e\ge n+q+2$.

## The proportional case

Suppose $U=tV$. Pairwise distinct heads give $t\ne0,1$. For $t=1$ the identity $U-V=-(f_0-f_3)(f_1-f_2)$ would force two heads to be identical. At any base coordinate, a repeated pair forces a triple since all three opposite-pair products vanish together. Thus the quotient equality patterns are four equal values, a triple and a singleton, or four distinct values. Call their counts $c,b,a$ respectively. Counting the roots of $U$ with multiplicities gives $2c+b\le2d$, hence $M+c\le a+2d$.

Away from locator roots the largest matching class on the three types has size $4,3,1$ respectively. At a root its size can increase by at most three. Charging one unit for each coordinate where no head matches gives

$$E+z\le3n-2qa+qc+3r\le3n-2q(M-2d)+3r.$$

Using $r\le n/2-qd-s$ gives $E+z\le3n-(n/2-qd)-3s$. Since $M$ is even and $qd<n/2$, the gap $n/2-qd$ is at least $q$. Thus $E+z+q+3s\le3n$. Substitution of the scalar or paired incidence lower bounds proves the claimed floor in this case as well.
