# Polynomial slopes at an ordinary radial singularity

Let $A,B\in K[X,Y]$ and let $f$ run over the polynomial solutions of $B(X,f)f'=A(X,f)$ of degree at most $d\ge1$. Translate a marked point to $(0,0)$. Suppose the degree-one parts are $A_1=\lambda Y$, $B_1=\lambda X$, with both constant terms zero and $\lambda\ne0$. Suppose $B(0,Y)$ has finite vanishing order $2\le k\le d+1$. In characteristic zero or characteristic $p>2d+2$, at most **$2d+1$ distinct polynomial solutions** can pass through the marked point. This cap depends on the message degree alone. The underlying first-derivative interpolation for Reed–Solomon words is the method of [Dao, Kominers and Thaler](https://eprint.iacr.org/2026/2056). The proposition here concerns a linear differential factor with the stated local form.

## Truncated solutions

Fix the initial slope $s$. Setting $f=Xz$ and $f'=z+Xz'$ gives
$$
 \big(B(X,Xz)/X\big)z'=\big(A(X,Xz)-zB(X,Xz)\big)/X^2.
$$
Both sides have polynomial coefficients in $X,z$. The coefficient of $z'$ at $X=0$ is the unit $\lambda$. Therefore the initial condition $z(0)=s$ determines every coefficient through order below the characteristic, by ordinary power-series recursion. In particular the coefficients $b_j(s)$ of $f$ through the orders used below are polynomials in $s$. Two polynomial solutions of degree $\le d$ through this point with the same slope are identical.

Consider the weighted rescaling $X=\epsilon^k t$, $f=\epsilon Z$, $s=\epsilon^{1-k}$, and set
$$
 \widetilde A(t,Z)=\epsilon^{-1}A(\epsilon^k t,\epsilon Z),\qquad
 \widetilde B(t,Z)=\epsilon^{-k}B(\epsilon^k t,\epsilon Z).
$$
These are polynomials in $\epsilon,t,Z$. For $\widetilde B$ this uses the order $k$ of $B(0,Y)$, while every monomial involving $X$ has weight at least $k$. The new equation is $\widetilde B Z'=\widetilde A$. It still has degree-one parts $\lambda t,\lambda Z$, respectively. The same recursion produces a solution of initial slope one with all coefficients in $K[\epsilon]$ through the required order. Over $K(\epsilon)$ its $t^j$ coefficient is exactly $\epsilon^{kj-1}b_j(\epsilon^{1-k})$. Thus $\deg_s b_j\le (kj-1)/(k-1)$.

At $\epsilon=0$, writing $b\ne0$ for the coefficient of $Y^k$ in $B(0,Y)$, the limit equation becomes
$$
 (\lambda t+bZ^k)Z'=\lambda Z,\qquad Z=t+O(t^2).
$$
Its inverse series is $t=Z+cZ^k$ with $c=b/(\lambda(k-1))$. Indeed this polynomial inverse satisfies the equation by differentiation, and the preceding recursion supplies uniqueness. Put $\ell=\lceil d/(k-1)\rceil$ and $j=1+(k-1)\ell$. Then $j>d$. Formal inversion gives the nonzero coefficient
$$
 [t^j]Z=\frac{(-c)^\ell}{j}\binom{j+\ell-1}{\ell}.
$$
Here $j+\ell-1=k\ell\le2d$. To check the latter inequality, write $d=(k-1)q+a$, $0\le a<k-1$; if $a>0$, then $q\ge1$ and $k(q+1)\le2((k-1)q+1)$. All divisions and the binomial are valid under the characteristic hypothesis. This inversion coefficient shows that $b_j$ has degree exactly $j+\ell=1+k\ell\le2d+1$. For every polynomial solution of degree at most $d$, its slope must be a root of this one nonzero polynomial because its $j$th coefficient vanishes. Uniqueness for the slope completes the proof. [Finite slope and coefficient controls](../../../scripts/probes/probe_radial_ode_slope_cap.py)

The hypotheses can be tested on the coefficients of a proposed differential factor at each received point. Higher-multiplicity singularities require a further local analysis. If $B(x,Y)$ vanishes identically, a solution at $x$ instead takes a root of $A(x,Y)$ whenever the latter is nonzero. The local slope cap alone does not establish a new all-center decoding radius.
