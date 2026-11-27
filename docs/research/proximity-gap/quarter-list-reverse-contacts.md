# Quarter-rate list safety through 536,870,919 errors

At the second named prime, every closed ball of radius **536,870,919 errors** has at most \(2^{31}\) words at rate one quarter and length \(n=2^{30}\). This holds on every injective grid and at every positive interleaving width. The proof interpolates an equation through 61 polynomial sections, shows that it contains a quadratic function, and uses contacts in the opposite direction to bound the number of sections outside the same irreducible factor. This is a written proof with an exact integer verifier. [Arithmetic certificate](../../../scripts/probes/probe_quarter_list_reverse_contacts.py)

## Extracting polynomial sections

Set \(d=n/4-1,\ t=2d-5,\ m=2n+1\). A list of \(m\) words supplies \(m\) distinct scalar polynomials over a common extension field by identifying the interleaving alphabet with a vector space basis of that extension. Work over its algebraic closure. Choose \(t\) agreement sites per word. Put \(a=t-d,\ \kappa=d/a,\ L=1+m(nd-t^2)/(na)\). For the deficit matrix with entries \((d-|S_i\cap S_j|)/a\) away from the diagonal, let \(S\) denote its squared Frobenius norm. The fourth-moment argument gives \(S\ge m\) and
\[
 2S^2/m-\sum_{ij}D_{ij}^4-2S+m\le Q=2L(L-1)(L+1)^2 .
\]
These two inequalities hold for \(\kappa>1\) as well. [Spectral proof](spectral-deficit-list.md)

For an integer \(h\), join pairs whose intersection is smaller than \(h\), and put \(\mu=(d-h)/a\). If two adjacent edges shared a word, the two other supports would overlap in at least \(3t-n-2(h-1)\) sites by inclusion-exclusion. For both choices of \(h\) below this exceeds \(d\), so the edges form a matching. With \(P\) edges the fourth-power sum is at most \(\mu^2 S+2P\kappa^2(\kappa^2-\mu^2)\). Since \(0<\mu<1\), substituting \(S\ge m\) gives
\[
  P\ge \frac{m(1-\mu^2)-Q}{2\kappa^2(\kappa^2-\mu^2)} .
\]
At \(h=736083\) there are at least 100456 pairs, each missing at most \(s=736096\) sites. At \(h=50000000\) there are at least \(M=1056336697\) pairs, each missing at most 50000013 sites. Two tight pairs and any broad pair cover more than \(3d\) common sites. Consequently their polynomial pairs belong to one pencil by the three-row determinant. The argument with the two tight pairs gives at most \(4s-4=2944380\) exceptional sites. If the actual number is \(x>s\), the 100456 tight parameters each agree at \(x-s\) sites with one prescribed value on this exceptional set, with pairwise intersections at most \(w=\lfloor(x-4)/2\rfloor\). Thus
\[
 100456((x-s)^2-xw)\le x(x-s-w).
\]
Checking each integer from 2513197 through 2944380 yields a contradiction. [Pencil construction and exceptional-site count](complementary-list-pencil.md)

Use the upper bound \(E=2513196\). All \(M\) broad parameters \(U_i\) are distinct polynomials of degree at most \(u=(E-4)/2=1256596\). The pencil yields coprime \(A,B\), with \(\deg A\le d\), and a polynomial \(N=B^2-AS_0B+A^2P_0\) of degree at most \(n-4\) having at least \(n-E\) distinct roots, for fixed pair sum and product \(S_0,P_0\). Put \(b_0=E-4\). At most \(b_0\) distinct roots are multiple, and at least \(n-2E+4\) are simple. On the smooth curve \(C\) for \(Y^2=N\) put \(H=(2B-AS_0+2Y)/A^2,\ V=dH/dX\). The degree \(D\) of \(H\) is at least \(D_0=(n-2E+4)/2=534357718\). Its conjugate \(H^\sigma\) is distinct and agrees with it at every branch point of the double cover, including common poles. There are consequently at most \(2D\) branch points. For each polynomial section the norm of \(H-U_i\) is a square, and simple roots of \(N\) support no contacts. [Double-cover argument](quarter-list-moving-jets.md)

## The contacts in both directions

Discard the at most two sections for which \(H-U_i\) has a zero above infinity. Each remaining section has finite contact orders \(a_{i,P}=\max(0,\operatorname{ord}_P(H-U_i))\) summing to at least \(D-2u\). On \(r\) selected sections put \(J_r=u r(r-1)\). The total, over distinct pairs, of \(\min(a_{i,P},a_{j,P})\) over all \(P\) is at most \(J_r\), since a polynomial difference of degree at most \(u\) pulls back to a function of degree at most \(2u\).

The union of the finite odd-order contact sites has size at most \(O=d+2b_0\), independently of the chosen sections. Ramified contacts have even order by the square norm. At an unramified odd contact the conjugate place has odd valuation too. If it is a pole, its base point is a zero of \(A\). For each zero of \(A\) there is just one pole and at most one conjugate contact there. Indeed \(N\equiv B^2\bmod A\) and \(B\) is a unit there. One numerator \(2B-AS_0\pm2Y\) is a unit and the product of the two numerators equals \(A^2(S_0^2-4P_0)\), so the other sheet is regular. If both conjugate places are contacts then \(H=H^\sigma\), which away from \(A=0\) requires \(N=0\). Such an unramified root is multiple, contributing at most two points. This proves the count.

If \(F(X,U_i,U_i')=0\), substituting the contact into \(F(X,H,V)\) gives order at least \(a_{i,P}-1\) at unramified sites and \(a_{i,P}-2\) at branch sites. Division by \(dX\) costs one extra order at the latter, where \(a_{i,P}\ge2\), so all evaluations are regular. The same estimates hold for \(F(X,U_i,U_i')\) when \(F(X,H,V)=0\), by subtracting the two polynomial evaluations. For every integer \(a\ge1\), \(a-1\ge (a-\mathbf1_{a\text{ odd}})/2\).

If \(F\) contains \(r\) selected sections, apply this estimate to the *largest* contact order at each site. Its sum over sites is at least \(r(D-2u)-J_r\). At most \(O\) maxima are odd and at most \(b_0\) sites are branch contacts. Hence a nonzero \(F(X,H,V)\) has zeros of total order at least
\[
 [r(D-2u)-J_r-O]/2-b_0.                                      \tag{1}
\]
Conversely, suppose \(g(X,H,V)=0\) and \(R\) selected sections give nonzero \(g(X,U_i,U_i')\). Sum their zeros individually. At a site counted by \(k\) different odd contacts, the excess \(k-1\) is at most the sum of the pairwise minimum orders there. Thus odd contacts counted with their indices number at most \(O+J_R\). Branch contacts contribute at most \(R b_0\). The sum of the zero degrees, evaluated on \(C\), is at least
\[
 [R(D-2u)-J_R-O]/2-Rb_0 .                                    \tag{2}
\]

## Interpolation and exclusion

Use the 76 monomials \(Z^kW^l\) with \(k+l\le17,\ 2k+3l\le35,\ l\le4\). Set \(e=74000000\), \(c=14u\). For each monomial permit a polynomial coefficient of degree at most \(\min(e,e+c-(k+l)u)\). Evaluating on one polynomial jet gives degree at most \(e+c\). With \(r=61\) selected sections the coefficients give 5600124752 unknowns and at most 5587133045 homogeneous linear equations over the constant field. A nonzero \(F(X,Z,W)\) vanishes on these sections.

At a finite pole of \(H\), the base point is a zero of \(A\), and the pole has order \(k_0=2\operatorname{ord}_x A\) by the numerator calculation above. Since the point is unramified, the pole order of \(V\) is at most \(k_0+1\le3k_0/2\). At infinity, \(dX\) has a pole of order at least two, so \(V\) has at most the pole order of \(H\) there and is regular if \(H\) is regular. Away from poles of \(H\) and infinity, \(V\) can have at most a simple pole at each finite branch point. A common pole divisor for all terms of \(F(X,H,V)\) therefore has degree at most \(2e+(35/2+8)D\). Bound (1) strictly exceeds this degree at \(D_0\), with larger slope thereafter. Hence \(F(X,H,V)=0\).

Choose an irreducible factor \(g\) containing \((H,V)\). Its \(X\)-degree is at most \(e\), its total \((Z,W)\)-degree is at most 17 and its \(W\)-degree is at most four. On each polynomial section, \(g(X,U_i,U_i')\) has degree at most \(e+17u\) on the base. For \(R=15\), bound (2) exceeds \(2R(e+17u)\) even at \(D_0\). Thus at most 14 of the retained sections can yield a nonzero substitution. At least \(M-16\) jets lie on this one factor. In particular \(g\) has positive \(W\)-degree, since the \(U_i\) are distinct.

The resultant of \(g\) with \(g_W\) in \(W\) is nonzero and has \(X\)-degree at most \(7e<D_0\). Thus \(g_W(X,H,V)\ne0\) by the minimal equation of \(X\) over \(k(H)\). The section bound on the differential equation of total degree 17 is \(17^2(1+2u)<M-16\). It forces the derivative of order \(u+1\) of \(H\) to vanish. At any simple root of \(N\) the half-integral leading term gives a nonzero derivative at this order since the characteristic exceeds \(2(u+1)\). This contradiction proves the asserted ball bound. [Differential equation and section bound](quarter-list-jet-derivation.md)
