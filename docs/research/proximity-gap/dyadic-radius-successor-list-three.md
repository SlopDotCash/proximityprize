# At most three rate-half codewords one step past unique decoding on dyadic roots of unity (characteristic zero)

**Status.** Written proof for $n\ge64$; the case $n=32$ additionally uses one finite census (reproducible, exact). Lean checks three internal steps with standard axioms only: the Fourier step of Lemma 2 (`ProximityGap.DyadicParity.dyadic_eq_zero_of_three_centers`), the class count of Theorem A (`ProximityGap.DyadicOddPencil.three_odd_sets_one_class`) and the 4-cycle contradiction of Section 4 (`ProximityGap.DyadicFourCycle.four_cycle_false`). Lean also derives the set statement of Lemma 2 from the reflection equations (2.1) (`ProximityGap.DyadicParity.symmetric_on_other_class`). Theorem A itself is composed in Lean as `ProximityGap.DyadicOddPencil.odd_triple_bound`: three pairwise disjoint sets of odd size $m\ge5$ in $\mathbb Z/2^{e+1}$ satisfying (2.1) in all three roles have $3(m-2)\le2^e$. Section 4 is composed as `ProximityGap.DyadicFourCycle.four_cycle_refl`, with (2.1) at the four vertices and the two class counts as hypotheses. Not formalized: the overlap-pattern classification of Section 1, the passage from vanisher ratios to the reflection equations (cyclotomic units), and the final assembly.

## Statement

Let $n=2^k\ge32$, $b=n/4$, and let $F$ be a field of characteristic zero containing the group $\mu_n$ of $n$-th roots of unity. Let $C$ be the Reed–Solomon code of polynomials of degree below $2b$ evaluated on $\mu_n$.

> **Theorem 1.** Every Hamming ball of radius $b+1$ contains at most three codewords of $C$.

Three is attained (the geometric-sum center in PROGRESS.md, "Exact list of the geometric-sum center"). Radius $b$ is the unique-decoding radius. For $n=8$ the statement is false (the octagon has four), and for $n=16$ the argument below does not apply.

Notation: identify $\mu_n$ with $\mathbb Z/n$ through a fixed primitive root $\zeta$. $L_S$ is the monic polynomial with simple roots $S\subseteq\mu_n$, and $K=X^n-1$. A set $S\subseteq\mathbb Z/n$ is *symmetric* if $S=S+n/2$. The two *parity classes* are the even and the odd residues; $x\mapsto x+n/2$ preserves each. $S$ is *symmetric on a class $W$* if $S\cap W$ is symmetric.

## 1. Overlap patterns of four close codewords

Suppose $P_0,\dots,P_3$ are distinct codewords within distance $b+1$ of one word, with error sets $E_i$. Minimum distance $2b+1$ gives $|E_i\cup E_j|\ge2b+1$.

* No $E_i$ has fewer than $b$ points, and at most one has exactly $b$.
* If $|E_0|=b$, the other three have $b+1$ points, are disjoint from $E_0$, and pairwise meet in at most one point. Covering at most $3b$ sites forces three pairwise overlaps at three distinct sites (**star**).
* If all four have $b+1$ points, every pair meets in at most one site. Let $a_j$ be the number of sites with exactly $j$ erring heads. Then $a_2+2a_3+3a_4=4+a_0$ and $a_2+3a_3+6a_4\le6$. Two sites with three erring heads would give one pair two common errors. The solutions are: one three-error site plus two or three two-error sites; or $a_3=a_4=0$ with four, five or six two-error sites.

A *triangle* is a triple $i,j,l$ whose three pairwise overlaps exist and are three distinct sites. The star, the patterns with a three-error site (use the fourth head and two heads of that site), and every pattern with five or six overlaps contain a triangle. Four two-error sites form either a triangle with a pendant edge or a **4-cycle** $0,1,2,3$ with $a_0=0$.

**Triangle.** With $Q_i=E_i\setminus\{\text{its two triangle sites}\}$ ($b-1$ points, pairwise disjoint) and $Z$ the complement of $E_i\cup E_j\cup E_l$ ($b$ points), each difference $P_i-P_j$ is a nonzero polynomial of degree at most $2b-1$ vanishing on the $2b-1$ points of $Z\cup Q_l$, so $P_i-P_j=c_{ij}L_ZL_{Q_l}$ with $c_{ij}\ne0$. Summing around the triangle,
$$c_{ij}L_{Q_l}+c_{jl}L_{Q_i}+c_{li}L_{Q_j}=0 .$$
Three monic, pairwise coprime, linearly dependent polynomials of degree $m$ with all roots in $\mu_n$ will be called a **three-split pencil** of degree $m$. A triangle gives one of odd degree $m=b-1$.

**4-cycle.** Write $Q_i$ for the $b-1$ private error sites of head $i$ and $s_{i,i+1}$ for the overlaps (indices mod 4). The domain is partitioned into the four $Q_i$ and the four overlap sites. Here $P_i-P_{i+1}=c_iL_{Q_{i+2}}L_{Q_{i+3}}(X-s_{i+2,i+3})$. The four differences sum to zero. Evaluating at $x\in Q_j$ kills two terms and leaves
$$\frac{L_{Q_{j-1}\cup\{s_{j-2,j-1}\}}(x)}{L_{Q_{j+1}\cup\{s_{j+1,j+2}\}}(x)}=\text{const}\qquad(x\in Q_j). \tag{1.1}$$
Call the two $b$-sets in (1.1) the *neighbour sets* $N_j$ of vertex $j$. For $j=0$ they are $Q_3\cup\{s_{23}\}$ and $Q_1\cup\{s_{12}\}$.

In a pencil $A-\lambda B=(1-\lambda)C$ with root sets $\alpha,\beta,\gamma$, evaluation at the roots gives the same kind of statement in all three roles: $L_\alpha/L_\gamma$ is constant on $\beta$, $L_\alpha/L_\beta$ on $\gamma$, and $L_\beta/L_\gamma$ on $\alpha$.

## 2. The antipodal difference equation

**Input from cyclotomic units.** For $n=2^k$ the numbers $1-\zeta^r$, $r$ odd, $0<r<n/2$, are multiplicatively independent modulo roots of unity (Washington, *Introduction to Cyclotomic Fields*, Lemma 8.1 and Theorem 8.2, together with the fact that $1-\zeta$ is not a unit). The regulator-type determinant $\det(\log|1-\zeta^{ar}|)$ is numerically $-0.305$, $0.846$, $42.7$, $2.2\cdot10^6$, $2.5\cdot10^{18}$, $1.4\cdot10^{47}$ for $n=8,\dots,256$.

For $d=2^ad'$ with $d'$ odd and $d\not\equiv0$, $1-\zeta^d=\prod_{t<2^a}(1-\zeta^{d'+tn/2^a})$, and $1-\zeta^{-r}=-\zeta^{-r}(1-\zeta^r)$. So modulo torsion $x-s$ maps to the vector $\Phi(x-s)\in\mathbb Z^{n/4}$ indexed by odd classes $i$ mod $\pm$, with $\Phi(d)_i=[d\equiv\pm2^ai]$ for $2^a\,\|\,d$, $a\le k-2$, and $\Phi(n/2)_i=2$.

Let $\alpha,\gamma$ be disjoint and suppose $L_\alpha/L_\gamma$ is constant on a set $\beta$ disjoint from both. Then $\Psi_\alpha(x)-\Psi_\gamma(x)$ is independent of $x\in\beta$, where $\Psi_S(x)=\sum_{s\in S}\Phi(x-s)$. Subtract the coordinates $i$ and $i+n/2$: all terms with $a\ge1$ cancel, and with $a_S^-(y)=\mathbf 1_S(y)-\mathbf 1_S(y+n/2)$ and $f^-=a_\alpha^--a_\gamma^-$,
$$f^-(x+i)+f^-(x-i)=c_i\quad\text{for all }x\in\beta\text{ and all odd }i. \tag{2.1}$$
Note $f^-(y+n/2)=-f^-(y)$.

At $n=16$ the full condition "$\Psi$-differences constant in all three roles" has exactly 7 solutions in degree 3 and 23 in degree 4, the same sets as the true pencils. So on small cases the lattice condition is also sufficient.

**Lemma 2 (parity lemma).** Assume (2.1). If $\beta$ has at least three points in one parity class $W$, then $f^-$ vanishes on the other class $\overline W$, and $\alpha$ and $\gamma$ are both symmetric on $\overline W$.

*Proof.* For $x\in X=\beta\cap W$ and odd $i$ the points $x\pm i$ lie in $\overline W$. Let $F$ be $f^-$ on $\overline W$ and zero on $W$. Then $T_x(i)=F(x+i)+F(x-i)$ vanishes for even $i$ and equals $c_i$ for odd $i$, so $T_x$ is the same function for all $x\in X$. Its Fourier coefficient at $\xi$ is $\hat F(\xi)e(\xi x/n)+\overline{\hat F(\xi)}e(-\xi x/n)=2|\hat F(\xi)|\cos(2\pi\xi x/n+\theta_\xi)$. Antiperiodicity gives $\hat F(\xi)=0$ for even $\xi$. For odd $\xi$ the residues $\xi x$, $x\in X$, are distinct, and a cosine takes each value at most twice per period. Three points force $\hat F(\xi)=0$. Hence $F=0$. If $a_\alpha^-(y)=a_\gamma^-(y)\ne0$ at some $y\in\overline W$, then $y$ or $y+n/2$ lies in both $\alpha$ and $\gamma$. So both vanish on $\overline W$. $\square$

The lemma was checked against every verified pencil on $\mu_{16}$ and $\mu_{32}$ (more than 1800 instances, no failure).

## 3. No three-split pencil of large odd degree

> **Theorem A.** Let $n=2^k$ and let $m\ge5$ be odd with $3(m-2)>n/2$. In characteristic zero there is no three-split pencil of degree $m$ on $\mu_n$.

*Proof.* Each root set has odd size, so none is symmetric. If some root set had three points in each parity class, Lemma 2 in that role would make the other two symmetric. Hence each root set has at most two points in one class and at least $m-2\ge3$ in the other, its *dominant* class. Two of the sets, say $\alpha,\beta$, share a dominant class $E$. Lemma 2 in the roles of $\beta$ and $\alpha$ shows that $\alpha$, $\beta$, $\gamma$ are symmetric on the other class $O$. Thus $|\alpha\cap O|\in\{0,2\}$ and $|\alpha\cap E|$ is odd. If $\gamma$ were dominant on $O$, Lemma 2 in the role of $\gamma$ would make $\alpha\cap E$ symmetric, of even size. So all three are dominant on $E$, and $3(m-2)\le|E|=n/2$. $\square$

For $m=b-1$ the hypothesis holds exactly when $n\ge64$. Data: no pencils of degree 5 on $\mu_{16}$ and none of degree 9 or 10 on $\mu_{32}$, as predicted; degrees 5 and 7 on $\mu_{32}$ are outside the hypothesis and are also empty by the census.

## 4. The 4-cycle is impossible for $b\ge8$

Use (1.1) and Lemma 2 with $\beta=Q_j$: if $Q_j$ has at least three points in a class $W$, both neighbour sets $N_j$ are symmetric on $\overline W$. Write $S(j,X)$ for "both sets of $N_j$ are symmetric on $X$", and $c(j)$ for the set of classes in which $Q_j$ has at least three points; $c(j)\neq\emptyset$ because $|Q_j|=b-1\ge7$. Two elementary facts, using that $|Q|$ is odd and the $Q$'s and overlap sites are pairwise disjoint:

* (F1) If $Q\cup\{s\}$ and $Q\cup\{s'\}$ with $s\ne s'$ are both symmetric on $X$, then $s,s'\notin X$ and $Q\cap X$ is symmetric.
* (F2) $Q\cup\{s\}$ and $Q'\cup\{s\}$ with $Q\ne Q'$ cannot both be symmetric, and $Q\cup\{s\}$, $Q\cup\{s'\}$ with $s\neq s'$ cannot both be symmetric.

$N_j$ and $N_{j+2}$ contain $Q_{j+1}$ with two different overlap sites and $Q_{j-1}$ with the other two. So by (F1), $S(j,X)$ and $S(j+2,X)$ put all four overlap sites outside $X$ and make $Q_{j\pm1}\cap X$ symmetric. $N_j$ and $N_{j+1}$ share one overlap site attached to two different $Q$'s.

**Case I: $W\in c(0)\cap c(2)$ and $W'\in c(1)\cap c(3)$.** All overlap sites lie in $W$ and in $W'$, so $W=W'$, and every $Q_j\cap\overline W$ is symmetric. The class $\overline W$ has $2b$ points, all in the $Q_j$. If $Q_j$ has three points in $\overline W$, then $S(j,W)$ holds and both sets of $N_j$ are fully symmetric. Two such vertices contradict (F2), whether opposite or adjacent. So three of the $Q_j$ have at most two points in $\overline W$ and $2b\le(b-1)+6$, false for $b\ge8$.

**Case II: $c(0)=\{E\}$, $c(2)=\{O\}$** (or with $E,O$ exchanged). Then $S(0,O)$ and $S(2,E)$ hold, $|Q_0\cap O|\le2$ and $|Q_2\cap E|\le2$.

*IIa: $W'\in c(1)\cap c(3)$.* All overlap sites lie in $W'$ and $Q_0\cap\overline{W'}$, $Q_2\cap\overline{W'}$ are symmetric. If $W'=E$: $S(0,O)$ makes $Q_1\cap O$, $Q_3\cap O$ symmetric, and $S(2,E)$ then makes $Q_1\cup\{s_{01}\}$ and $Q_3\cup\{s_{30}\}$ fully symmetric. Counting $O$ gives $|Q_1\cap O|+|Q_3\cap O|\ge b-1$, so $S(1,E)$ or $S(3,E)$ holds. The first makes $Q_0\cup\{s_{30}\}$ fully symmetric, the second $Q_0\cup\{s_{01}\}$; both contradict (F2). If $W'=O$: $S(2,E)$ makes $Q_1\cap E$, $Q_3\cap E$ symmetric and $S(0,O)$ makes $Q_3\cup\{s_{23}\}$, $Q_1\cup\{s_{12}\}$ fully symmetric. Counting $E$ gives $S(1,O)$ or $S(3,O)$, hence $Q_2\cup\{s_{23}\}$ or $Q_2\cup\{s_{12}\}$ fully symmetric, again contradicting (F2).

*IIb: $c(1)$ and $c(3)$ are different singletons.* Each $Q_j$ sits in one statement on $E$ and one on $O$, each with one attached overlap site. Since $|Q_j|$ is odd, exactly one of its two attached sites lies in the class of its statement. Writing the four parity conditions out forces all four overlap sites into one class. In either class two different $Q$'s become fully symmetric after adding the same overlap site, contradicting (F2).

The remaining case ($c(1)\cap c(3)=\emptyset$, $c(0)\cap c(2)\ne\emptyset$) is Case IIa after rotating the labels by one. $\square$

## 5. Proof of Theorem 1

Every pattern of Section 1 contains a triangle or is a 4-cycle. A triangle gives a three-split pencil of odd degree $b-1$, excluded by Theorem A when $n\ge64$ and by the census (no degree-7 pencil on $\mu_{32}$) when $n=32$. The 4-cycle is excluded by Section 4 for $b\ge8$. For $n=32$ the census independently lists all 33 solutions of (1.1) at one vertex; all have symmetric neighbour sets, which gives the same contradiction.

## 6. Census on $\mu_{32}$ (characteristic zero)

Three-split pencils up to the dihedral action on the first root set, by degree:

| degree | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| classes | 2401 | 101 | 449 | 0 | 7 | 0 | 23 | 0 | 0 |
| not a pullback under $X\mapsto X^2$ | 2296 | 101 | 164 | 0 | 0 | 0 | 0 | 0 | 0 |

The degree-6 and degree-8 classes are exactly the pullbacks of the 7 and 23 classes of degrees 3 and 4 on $\mu_{16}$. The filters test necessary conditions (quadratic characters of $L_D(\beta)L_B'(\beta)\beta$, which lie in one square class along a root set; a cubic character for the star) modulo 14 to 16 small split primes; survivors are decided exactly modulo a 61-bit split prime. Filter-free brute force at lengths 8 and 16 reproduces the filtered counts. Commands and expected outputs are in `scripts/probes/probe_mu32_split_pencil_verify.py`.

## 7. Scope: why this is not a prime-field statement at production length

Characteristic zero enters only through the independence of the $n/4$ numbers $1-\zeta^r$. Modulo a prime $p$ they generate a subgroup of the cyclic group $\mathbb F_p^\times$, so their relation lattice in $\mathbb Z^{n/4}$ has index at most $p-1$. By Minkowski it contains nonzero vectors with all entries of size about $p^{4/n}$. At $n=2^{30}$ and $p\approx2^{160}$ this is below 2: there are relations with exponents in $\{-1,0,1\}$ that do not exist in characteristic zero. The proof above uses each single ratio equality separately and therefore fails there. For fixed $n$ the theorem still holds for all primes outside a finite, non-explicit set. A prime-field version at production length needs an argument that uses all $b-1$ equalities of (1.1) jointly; a counting heuristic ($4^n$ configurations against $p^{-(b-1)}$) says the statement should remain true, but that is not a proof. The MCA thresholds, the list thresholds at the named primes, and the Paley bound are not addressed.
