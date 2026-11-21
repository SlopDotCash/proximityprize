# Character averages with a prescribed first set

Let $A$ be any $m$-subset of $\mathbb F_p$, $m\ge1$. Write $W_\psi(b)=\sum_{a\in A}\psi(a+b)$ for a multiplicative character, extending **every** character by zero at zero. Let $E_+(A)$ count ordered solutions in $A^4$ of $u+v=w+z$. There is an exact complete fourth moment
$$
\frac1{p-1}\sum_{\psi\ne1}\sum_b |W_\psi(b)|^4
=p(2m^2-m)-4m^3+4m^2-m-E_+(A)
 +\frac{m(m-1)(3m^2-3m+1)}{p-1}
\le p(2m^2-m).
$$

For the proof, first sum over all characters. Orthogonality counts the shifts where $(b+u)(b+v)=(b+w)(b+z)\ne0$. For the $m$ constant quadruples there are $p-1$ shifts. For the $2m(m-1)$ other ordered quadruples with matching unordered pairs there are $p-2$. Distinct pairs sharing a site contribute zero, because after removing the common linear factor the two products differ at all other shifts. Disjoint pairs with distinct sums contribute one shift, by solving the linear equation. Disjoint pairs with equal sums contribute none. There are $m(m-1)^2+m(m-1)(m-2)^2$ disjoint ordered pairs of pairs, of which $E_+(A)-(2m^2-m)$ have equal sums. Finally subtract the principal character's contribution $((p-m)m^4+m(m-1)^4)/(p-1)$. Simplifying gives the identity. The upper bound follows from $m-1\le p-1$ and $m^2\le m^3$.

For every integer $r\ge1$ the same argument gives
$$
\frac1{p-1}\sum_\psi\sum_b |W_\psi(b)|^{2r}
\le r!\,p\,m^r+(r-1)m^{2r}.
$$
Indeed for any two ordered $r$-tuples from $A$, equality between the two shifted products is a polynomial equation of degree at most $r-1$. If the polynomials coincide, the two multisets of roots agree. There are at most $r!m^r$ such pairs, with at most $p$ valid shifts each. For every other pair the equation has at most $r-1$ solutions.

Thus for each **prescribed** $A$ the fraction of characters admitting any partner $|B|\ge m$ with $|\sum_{b\in B} W_\psi(b)|\ge \rho m|B|$ is at most
$$
\rho^{-2r}\left(\frac{r!p}{m^{r+1}}+\frac{r-1}{m}\right).
$$
This follows from Hölder, which forces the complete $2r$-th moment to be at least $m^{2r+1}\rho^{2r}$ for each exceptional character. For $m\ge p^\epsilon$, take a fixed $r$ with $(r+1)\epsilon>1$ and then take $\rho=p^{-\delta}$ with $2r\delta<\min((r+1)\epsilon-1,\epsilon)$. The fraction tends to zero by a power of $p$, simultaneously over all partners for each good character. At fourth order the exact nonprincipal estimate gives the fraction bound $(p-1)p(2m^2-m)/((p-2)m^5\rho^4)$ among nonprincipal characters for $p>2$. The classical Paley conjecture prescribes the quadratic character, which can still lie in the exceptional set.

The probe sums Fourier energies via the histogram of nonzero products separately at every shift. It checks the exact fourth moment on every nonempty domain in $\mathbb F_3,\mathbb F_5,\mathbb F_7,\mathbb F_{11}$, including the full domain on which the nonprincipal left side vanishes. [Exact arithmetic verifier](../../../scripts/probes/probe_paley_character_average.py)
