# Coset interpolation for the unrestricted first-prime quarter-rate pencil

At the first unresolved quarter-rate error count, 447392428, a failure is equivalent to a rational function of degree $D=2^{28}-2$ with three completely split simple fibers on $H=\mu_{2^{30}}$. Every such function has at most $2\lfloor D/q\rfloor$ constant cosets of $\mu_q$, counting **all** projective values, for every dyadic divisor $q>2$ of $2^{30}$. In particular it has at most two constant cosets of $\mu_{2^{27}}$ and six of $\mu_{2^{26}}$. The scalar values on different cosets may coincide. The result also gives the following constraints on partial cosets and an exact description at equality. [Production equivalence](quarter-successor-split-pencil.md)

Let $R=P/Q$ be a coprime rational function of degree $d$ over any field containing the grid, and assume $R\notin K(X^q)$. This condition is automatic when $q\nmid d$, as degrees of rational maps multiply. For $b$ chosen cosets of $\mu_q$, prescribe an arbitrary projective value separately on each. The total number of sites at which these prescriptions agree with $R$ is at most
\[
                    d+q\lfloor b/2\rfloor .
\]
Indeed put $Y=X^q$ and $h=\lfloor b/2\rfloor$. Two polynomials $A,B$ of degree at most $h$ have more than $b$ coefficients together, so some nonzero pair satisfies the $b$ homogeneous interpolation equations at the distinct coset values of $Y$. Each matched grid site kills $P(X)B(X^q)-Q(X)A(X^q)$, even if $A,B$ both vanish at its coset value. This polynomial is nonzero by the assumption on $R$. The root bound proves the claim. Taking $b=2\lfloor d/q\rfloor+1$ proves the count of whole constant cosets. The matched-site argument also applies directly to rational pencils having different numbers of sites in their three selected fibers.

For a second proof, write $P=\sum_{j<q}X^jP_j(Y)$, $Q=\sum_{j<q}X^jQ_j(Y)$, and denote the maximum possible component degree by $L=\lfloor d/q\rfloor$. At a constant coset, $(P_j(y),Q_j(y))$ is proportional to its prescribed projective value for every $j$. This follows by reducing the appropriate linear combination of $P,Q$ modulo $X^q-y$. Thus each such $y$ kills all minors $P_iQ_j-P_jQ_i$. Some minor is nonzero since otherwise every column over $K(Y)$ is proportional to the same vector and $R\in K(X^q)$. Each minor has degree at most $2L$.

## A basis for every specified collection of constant cosets

Fix $b$ constant cosets, with values $y_i=X^q$ and targets $z_i$. The polynomial pairs in $K[Y]^2$ whose value at each $y_i$ is proportional to $z_i$ form a module with two generators $U,V$. They may be chosen to have independent leading coefficient vectors and degrees $a\le c$ satisfying $a+c=b$. Their determinant is a nonzero scalar multiple of $\prod_i(Y-y_i)$.

Start with the two constant coordinate vectors. At a new point $y$, evaluation is a basis because its determinant is nonzero. Choose the generator of smallest degree among those failing the new homogeneous linear equation. Subtract its appropriate constant multiple from the other generator to make the latter satisfy the equation. Replace the chosen generator by its product with $Y-y$. These two elements generate exactly the new module, since after the subtraction the coefficient of the violating generator must be divisible by $Y-y$. The operation preserves independence of the two leading coefficient vectors. Indeed subtraction from a higher-degree generator leaves its leading term unchanged, equal degrees give an invertible constant row operation, and a lower-degree generator already satisfied the equation. The total degree and determinant change as claimed.

It follows that every such pencil admits the exact expression
\[
  (P(X),Q(X))=F(X)U(X^q)+G(X)V(X^q),\qquad
  \deg F\le d-qa,\quad \deg G\le d-qc .
\]
Apply the module representation to each residue column $(P_j,Q_j)$. Independence of the leading vectors implies $\deg(AU+BV)=\max(\deg A+a,\deg B+c)$ for a nonzero combination. Reassemble its coefficients with the factors $X^j$ to obtain the displayed degree bounds, including $j>d\bmod q$. Both $F$ and $G$ are nonzero because $R\notin K(X^q)$, and they are coprime because a common factor would divide both $P,Q$.

When $b=2L$, the preceding bounds force $a=c=L$. Write $r=d-qL$. Now $T=F/G$ has degree exactly $r$, since $P$ or $Q$ has degree $d$. The original map is a projectivity applied to $T(X)$ whose coefficients are polynomials of degree at most $L$ in $X^q$. The projectivity is nonsingular away from the $2L$ constant cosets. At the production successor, $r=q-2$ whenever $4\le q\le2^{28}$ divides the domain size.

If one of the three full target values occurs on $L$ of these constant cosets, its remaining $r$ points form a full simple fiber of $T$. To see this, apply the linear form selecting the target to both basis vectors. Each resulting polynomial of degree at most $L$ is divisible by the vanisher of the $L$ coset values. After removing that vanisher, the residual fiber equation is a nonzero constant linear combination of $F,G$. All its zeros have already been specified by the original full simple fiber. For instance six whole order-$2^{26}$ blocks give a residual pencil of degree 67108862; a target on three of these blocks supplies a complete simple fiber of that residual map. These conditions leave open pencils with other distributions of their roots.
