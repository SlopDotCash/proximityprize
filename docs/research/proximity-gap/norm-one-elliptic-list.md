# An exact sixteenth-rate list threshold at length 8,192

On the order-\(8192\) subgroup of \(\mathbb F_{8191^{10}}^\times\), the dimension-\(512\) Reed–Solomon code at 128-bit tolerance has last safe integer error count **5,377** and first failing count **5,378**. The list supremum is \(5378/8192=2689/4096\). On the same input the first mutual-correlated-agreement failure occurs at **3 errors**, giving MCA supremum \(3/8192\). These counts hold at every positive interleaving width and on every multiplicative coset of this subgroup. The field order is \(1359468845100412723218362927388368486401\), giving integer list budget three. [Complete polynomial construction and verification at every site](../../../scripts/probes/probe_norm_one_elliptic_list.py)

## Six disjoint 511-point fibers

Let \(p=8191,\ k=\mathbb F_p,\ d=511\). The verifier certifies primality by trial division through \(\sqrt p\). It constructs polynomials \(N,D\in k[T]\) of degrees 511 and 510. After homogenizing both to degree 511, their ratio sends exactly 511 sites of \(\mathbb P^1(k)\) to each of the six entries below. Define four homogeneous sections by using the pair \((N,D)\) in these lines:
\[
   0,\qquad N-903D,\qquad
   1942(N-2163D),\qquad 5400(N-3378D).
\]
At the projective target infinity their leading coefficients \(0,1,1942,5400\) are distinct. At finite targets the pair-equality equations give the following values, with all arithmetic in \(k\).

| Pair of sections | Target value of \(N/D\) | Physical sites |
|---|---:|---:|
| 0, 1 | 903 | 511 |
| 0, 2 | 2163 | 511 |
| 0, 3 | 3378 | 511 |
| 1, 2 | 5911 | 511 |
| 1, 3 | 4002 | 511 |
| 2, 3 | 3435 | 511 |

Here are reproducible definitions of the two polynomials. Elliptic addition gives a short description of the interpolation data. The fiber assertion itself is verified by direct polynomial evaluation.

1. On \(E':y^2=x^3+2794x+2628\), start at \(Q=(5911,2328)\). Repeatedly add \(Q\) to obtain the distinct nonidentity points \(jQ,\ 1\le j\le15\), with \(16Q=0\). Let \(C_0\) consist of their distinct abscissas.
2. For \(x\notin C_0\), set
   \[
       \psi(x)=x+\sum_{c\in C_0}
       \left[\frac{\tau_c}{x-c}+\frac{4y_c^2}{(x-c)^2}\right],
       \quad y_c^2=c^3+2794c+2628 .
   \]
   Here \(\tau_c=2(3c^2+2794)\) for nonzero \(y_c^2\), and \(\tau_c=3c^2+2794\) for \(y_c^2=0\). Let \(K\) consist of the distinct values \(\psi(x)\) as \(x\) runs over the finite abscissas on \(E'\) outside \(C_0\). There are 255. Every \(c\in K\) satisfies \(c^3+3076c+286\ne0\).
3. Write \(G(T)=\prod_{c\in K}(T-c)\). Then
   \[
   D(T)=G(T)^2,\qquad N(T)=T D(T)+
   \sum_{c\in K}\big[2(3c^2+3076)(T-c)+4(c^3+3076c+286)\big]
                      \left(\frac{G(T)}{T-c}\right)^2 .
   \]
   In particular \(N(c)\ne0\) at every root of \(D\). Infinity has nonzero leading numerator. The verifier forms every coefficient by multiplication and synthetic division in \(k[T]\), then checks the six fiber counts by Horner evaluation at all \(8191\) finite points and the leading forms at infinity.

To explain the choice of data, the first curve has \(8176=16\cdot511\) rational points. The cyclic quotient by \(\langle Q\rangle\) gives \(y^2=x^3+3076x+286\). The rational abscissas in \(K\) belong to the kernel of the complementary degree-511 isogeny obtained by factoring \(1-\operatorname{Frob}_p\) through the first quotient. Thus the seven pairs \(\{\pm jQ\},1\le j\le7\), yield full rational fibers on the abscissa line. The displayed four lines use six of them. The explicit finite verification proves the required six equalities independently of this derivation.

## Transport to the smooth grid

The extension \(\mathbb F_{p^{10}}\) contains \(\mathbb F_{p^2}=k(i)\), with \(i^2=-1\) since \(p\equiv3\bmod4\). The map \(t\mapsto u=(t-i)/(t+i)\) sends \(\mathbb P^1(k)\) bijectively to the order-\(p+1\) subgroup, taking infinity to one. Indeed the norm is one and the inverse is \(t=i(1+u)/(1-u)\). For any of the four binary forms \(F\) of degree \(d\), use the ordinary message polynomial
\[
                 f_F(U)= F\big(i(1+U),1-U\big).
\]
At \(u\ne1\) its value is \((1-u)^dF(t,1)\). At \(u=1\) its value is \((2i)^dF(1,0)\). These nonzero factors preserve every pair equality. Substituting a rescaled variable transports the four words and their center to any multiplicative coset.

Receive the common value at every site of a marked pair. There is exactly one pair at each such site since the six targets are distinct. Each word obtains \(3\cdot511=1533\) hits. Distribute the remaining \(8192-6\cdot511=5126\) sites cyclically among the four words. The verifier checks all sites in the quadratic subfield, obtains four distinct evaluation words, and counts their respective agreements as \(2815,2815,2814,2814\). An independent evaluation in the same verifier expands both transformed coefficient polynomials in $U$, evaluates them by a radix-two Fourier transform on successive powers of a generator, and compares all four words at every physical site. Repeating the scalar row gives four words in the same ball at every positive width. Thus a closed ball at \(8192-2814=5378\) errors exceeds budget three.

Conversely, for any four distinct words of any positive width and any center, write \(m_x\) for their number of hits at site \(x\). Each pair of words can coincide at no more than 511 sites since at least one pair of row polynomials differs. Therefore
\[
             \sum_xm_x\le \sum_x(1+\tbinom{m_x}{2})
                    \le8192+6\cdot511=11258<4\cdot2815.
\]
A ball at 5377 errors requires 2815 agreements from every word. This rules out four and proves the matching safety bound. The exact result concerns this 130-bit extension field and length 8192. The first failing list counts at the two designated length-\(2^{30}\) prime fields remain open.

## Mutual correlated agreement on the same input

The general staircase and spike theorem gives first failing count equal to the integer budget \(B\) on every injective domain whenever \(k+3(B-1)\le n\) and \(k+B+1\le n\). Here \(B=3\), \(512+6\le8192\), and \(512+4\le8192\). Thus every received pair is safe through two errors and some pair has at least four bad labels at three errors. In the witness four exceptional sites supply four distinct labels, each folding to the reference word on its own exceptional site and on the common \(n-4\) ordinary sites. The closed MCA test fails at the supremum. [Kernel-checked staircase and spike theorem](../../../ArkLib/Research/ProximityGap/RankExecutable.lean#L302)
