# An exact subfield obstruction to recovering the original chart

Let $s$ be an odd prime power, $F=\mathbb F_{s^2}$ and $A=\mathbb F_s\subset F$. Use the quadratic character $\chi_F$ on the ambient field. Write $A_t=\{(a-t)^{-1}:a\in A,\ a\ne t\}$ and $S(X,B)=\sum_{x\in X,b\in B}\chi_F(x-b)$. The following two bounds determine which charts exhibit a fixed positive relative bias against a partner of size at least $s$.

* For every $t\in A$, take $B=A$. Then $S(A_t,B)=(s-1)^2$. At the original placement, $S(A,A)=s(s-1)$.
* For **every** $t\notin A$ and every $|B|\ge s$,
  $|S(A_t,B)|/(s|B|)\le 2/\sqrt s+2/s$.

Consequently for any fixed $0<h<1$ and all sufficiently large $s$, the fraction of poles admitting a partner with $|S(A_t,B)|\ge h s|B|$ is **exactly $1/s$**. At this size the order of the uniform fourth-moment upper bound on exceptional charts is sharp over odd finite fields. The prime-field Paley problem excludes the subfield in this construction. A proof using only estimates valid without change over all odd finite fields would encounter this example. [General inversion estimate](paley-cross-ratio-moments.md) · [Prime-field formulation, §2.4](https://arxiv.org/html/2309.09124v3#S2.SS4)

For the first claim, every nonzero subfield element is a square in $F$ and $A_t=A\setminus\{0\}$. For the second, write $N(x)=x^{s+1}$. Euler's criterion gives $\chi_F(x)=\chi_s(N(x))$, including zero. For $u\notin A$ the monic quadratic $P_u(X)=(X-u)(X-u^s)$ is irreducible over $A$, and $\sum_{a\in A}\chi_s(P_u(a))=-1$. Indeed, completing the square reduces this to counting $(x-y)(x+y)=c\ne0$, which has $s-1$ solutions.

At a nonzero target $z=(y-t)^{-1}$ the absolute row sum equals the magnitude of $\sum_{a\in A}\chi_s(P_t(a)P_y(a))$. For $y=t^s$ the polynomials coincide and the magnitude is $s$. For $y\in A$, $P_y=(X-y)^2$ and deleting one term from the quadratic sum gives magnitude at most 2. For any other admissible $y$, the two irreducible polynomials have disjoint roots. Their product defines the smooth genus-one double cover with two rational points at infinity. Its character sum has magnitude at most $2\sqrt s+1$ by the Hasse bound. At $z=0$ the row sum is $-1$. There is just one target of magnitude $s$, so the sum of magnitudes on any $B$ is bounded by $s+(2\sqrt s+1)|B|$. [Hasse bound over finite fields](https://math.mit.edu/classes/18.783/2019/LectureNotes8.pdf)

## What the genus-one average sees

For $s\ge5$, average the degree-four sum $Q_F(I)=\sum_{b\in F}\chi_F(\prod_{u\in I}(b+u))$ over all four-element $I\subset A$. Its exact mean is
$$
s-1+\frac{3}{s-2}.
$$
In the base field itself the mean is $3/(s-2)$. Thus base extension adds exactly $s-1$ to this average and violates every upper estimate $s(s^2)^{-\eta}$ with fixed $\eta>0$ for large $s$. This exhibits the obstruction directly in the one-sided trace estimate.

Indeed the original rows equal $s-1$ at each $b\in A$ and $-1$ elsewhere by the norm calculation. The quartic identity follows by the same partition expansion over every odd finite field. Insert $m=s$, field size $s^2$, fourth moment $s(s-1)^4+s^2-s$ and pole sum $s(s-1)^2$. The result is $24\sum_I Q_F(I)=s(s-1)(s-3)(s^2-3s+5)$. Dividing by $24\binom s4$ gives the stated mean. In the base field summing the fourth elementary symmetric polynomial at each shift gives $s\binom{(s-1)/2}{2}$, since each full row has generating polynomial $(1-X^2)^{(s-1)/2}$. [Quartic identity and fixed-prime-field means](paley-domain-tails.md) · [Independent finite-field check](../../../scripts/probes/probe_paley_square_field_charts.py)

The obstruction persists at **every fixed positive genus**. For $1\le2r\le s$, the exact mean of the $2r$-branch character sum in $F$ is
$$
s-2r+(s^2-s)(-1)^r\frac{\binom{(s-1)/2}{r}}{\binom{s}{2r}}.
$$
For $b\in A$ the $s$ character values have generating polynomial $(1+X)^{s-1}$. For $b\notin A$ their sum is $-1$ and all values are nonzero, so the generating polynomial is $(1-X)(1-X^2)^{(s-1)/2}$. Extracting the coefficient of $X^{2r}$ and dividing by the number of branch sets proves the formula. For $r=1$ the mean is $-1$ as required by quadratic orthogonality. For every fixed $r\ge2$ it is asymptotic to $s$. In particular, increasing the fixed genus in the [one-sided criterion](paley-domain-tails.md) still requires an argument that uses the prime field.
