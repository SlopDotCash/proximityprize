# Ramification on the ordered triples of a quarter-rate split pencil

At the first prime and quarter rate, an overrun at \(447392428\) errors is equivalent to a degree-\(D=268435454\) rational function whose fibers over \(0,1,\infty\) each consist of \(D\) distinct points of \(H=\mu_{2^{30}}\). For such a function \(R\), let \(b_j\) be the orders of the geometric inertia generators at its branch values. Its ramification excess satisfies
\[
 E_R=\sum_j(1-1/b_j)-2
 \ \ge\ \frac{45663621513021794134939}{103042957874781541548323}
 \ >\ 0.4431513.
\]
The previous ordered-pair lower bound was \(0.399999932\). In particular, a three-branch pencil cannot have orders \((2,b,c)\) with \(b\le17\) or \((3,4,c)\), for any \(c\). For first orders \((2,18),(2,19),(3,5),(4,4)\), the last order must be at least \(774,238,43,18\), respectively. Four branch values with orders \((2,2,2,c)\) require \(c\ge18\). [Exact split-pencil criterion](quarter-successor-split-pencil.md) · [Ordered-pair bounds](quarter-split-wronskian-suborbits.md)

The cycle types give a separate restriction. If \(R\) has precisely three branch values, the following bounds hold for each inertia generator on all \(D\) sheets.

| Inertia order | Minimum number of moved sheets |
| --- | ---: |
| Any | 45,679,662 |
| Two | 128,108,138 |
| Three | 77,980,500 |

The proof covers every remaining decomposition of \(R\). The Wronskian, function-field arguments and ramification interpretation are proved below. Lean checks the discrete third-moment inequality and the numerical implications. The probe checks the underlying permutation formulas on all cycle types of degrees three through nine. Existence of the required pencil at \(447392428\) errors remains open. [Lean](../../../ArkLib/Research/ProximityGap/Frontier/QuarterTripleSheetRamification.lean) · [Exact arithmetic and permutation verification](../../../scripts/probes/probe_quarter_triple_sheet_ramification.py)

## The curve of ordered distinct triples

Work over an algebraic closure \(K\) of the first designated field. Write \(R=V\circ W\circ U\) and \((s,h,m)=(\deg V,\deg U,\deg W)\). The remaining possibilities are \((1,1,268435454),(1,2,134217727),(2,1,134217727)\). The geometric monodromy of \(W\) contains \(A_m\) in its natural action, hence acts transitively on ordered distinct triples. The branch permutations are tame because the characteristic \(p>D\) does not divide \(D!\). [Primitive-stage classification](quarter-split-pencil-pullbacks.md#a-primitive-factor-must-have-alternating-or-symmetric-monodromy) · [Three remaining degrees](quarter-split-wronskian-suborbits.md)

Let \(Y\) be the smooth projective curve of ordered distinct sheets \((y_1,y_2,y_3)\) of \(W\) over a common target value. It is irreducible. Put \(a=(m-1)(m-2)\). Each \(y_i\) has degree \(a\), and the map to the common target has degree \(ma\). Choose any irreducible component \(X\) of the normalized cover obtained by adjoining \(x_i\) with \(U(x_i)=y_i\). Write \(c=[K(X):K(Y)]\), so \(c\le h^3\), and each \(x_i\) has degree \(ca/h\) on \(X\).

The three designated fibers of \(R\) are unramified throughout this decomposition. They give \(3s\) full fibers of \(W\). Every point of \(X\) above an ordered triple in these fibers has \(x_i\in H\). There are exactly \(3smac\) such points since \(X\to Y\) is unramified there. Let \(n=2^{30}\), \(u_i=x_i^n\), and let \(S\) contain just the zeros and poles of the three \(x_i\).

The eight cube monomials \(\prod_{i\in I}u_i\), for \(I\subseteq\{1,2,3\}\), are linearly independent over \(K\) on **each** \(X\). Indeed, over \(K(y_2,y_3)\), the first primitive sheet \(y_1\) has degree \(m-2\) by triple transitivity. Adjoining \(x_2,x_3\) extends that base field by at most \(h^2\). Thus \(x_1\) has at least \((m-2)/h^2\) distinct conjugates over \(K(x_2,x_3)\), by separability. Among generic sheets of \(R\), at most two can have the same \(n\)-th power. Equality of two powers makes their ratio some \(\zeta\in H\), and \(R(\zeta X)=R(X)\) then holds identically. All such scalings form a subgroup whose order divides both \(D\) and \(n\), hence divides two. It follows that \(u_1\) has degree at least \((m-2)/(2h^2)>1\) over \(K(x_2,x_3)\). The same argument for the ordered pair gives degree at least \((m-1)/(2h)>1\) for \(u_2\) over \(K(x_3)\). Successively extracting the two coefficients of a multiaffine relation in \(u_1\), then in \(u_2\), then in the nonconstant \(u_3\), proves independence.

## The seven-dimensional Wronskian

Let \(L\) be the span of the seven nonconstant cube monomials with 1 subtracted from each. Every element has poles bounded by \(\sum_i(u_i)_\infty\), of degree \(3nca/h<p\) at the stated parameters. The Wronskian differential of a basis of \(L\) is a nonzero meromorphic section of \((\Omega_X^1)^{\otimes21}\). At a point outside the pole divisor choose a basis with strictly increasing vanishing orders. All seven orders are between \(0\) and \(3nca/h<p\). Their Vandermonde determinant is nonzero in \(K\), so the Wronskian is nonzero. [Valuation comparison and large-characteristic Wronskian proof](quarter-split-wronskian-suborbits.md#self-contained-wronskian-gcd-bound-in-large-characteristic)

At a point where \(u_1=u_2=u_3=1\), all elements of \(L\) vanish and the seven distinct orders are at least \(1,\ldots,7\). After subtracting \(21\) for the derivatives the Wronskian has order at least seven. At other points outside \(S\) its order is nonnegative. At a point of \(S\), write \(v_i=\operatorname{ord}(u_i)\). The sum of the seven adapted orders is at least the sum of the seven smallest cube-monomial orders. This follows from the valuation filtration on their eight-dimensional span. The omitted largest order is \(\sum_i\max(0,v_i)\). The sum of all eight orders over all of \(S\) is zero by the product formula. Thus the total contribution over \(S\) is at least \(-3nca/h-21|S|\). Taking the degree of the Wronskian gives
\[
  3smac\ \le\ \frac{3nca}{7h}+3\bigl(2g(X)-2+|S|\bigr).
\]

For \(h=1\), \(X=Y\) and \(|S|\le6a\). For \(h=2\), the cover \(X\to Y\) is a compositum of quadratic extensions. Its branch points lie over either branch value of \(U\) in one of the three coordinates. There are at most \(6a\) such points on \(Y\), and tame cyclic inertia has order at most two. The ramification contribution is at most \(3ca\). Also \(|S|\le 6ca/h=3ca\). Both cases give \(2g(X)-2+|S|\le c(2g(Y)-2+6a)\). Putting \(G=2g(Y)-2\), and using \(n/h=4sm+8/h\), proves
\[
  \frac{G}{a}\ \ge\ \frac{3sm}{7}-6-\frac8{7h}. \tag{1}
\]

## The third fixed-point moment

For each inertia generator of \(W\) of order \(d\), give its \(d-1\) nonidentity powers weight \(w=1/d\), and let \(f\) be the number of sheets fixed by a power. Write \((f)_3=f(f-1)(f-2)\). Burnside's cycle formula and Riemann–Hurwitz on the original \(m\) sheets and on ordered distinct triples give
\[
  \sum w=E+2,\qquad \sum wf=mE+2,\qquad
  G=maE-\sum w(f)_3.
\]
Here \(E\) is the excess for \(W\). For every integer \(b\ge1\), set \(B=3b(b-1)\), \(C=2b(b-1)(b+1)\). The difference \((f)_3-(Bf-C)=(f-b)(f-b-1)(f+2b-2)\) is nonnegative for all nonnegative integers \(f\). Consequently
\[
 G\ \le\ maE-B(mE+2)+C(E+2). \tag{2}
\]
With \(s=1\), take \(b=24345100\) for \(m=134217727\) and \(b=48690201\) for \(m=268435454\). Combining (1) and (2) gives the following exact floors.

| \(h\) | \(m\) | Lower bound for \(E\) |
| ---: | ---: | --- |
| 2 | 134217727 | \(45663621513021794134939/103042957874781541548323\) |
| 1 | 268435454 | \(9243648649097604732874/20858898488376704579481\) |

The whole pencil has \(E_R\ge E/s\) by tame Riemann–Hurwitz on the Galois closures. For \(s=2\), the ordered-pair bound already gives \(E\ge268435426/268435465\), whose half exceeds either value in the table. This proves the asserted uniform floor. [Whole-map charging argument](quarter-split-suborbits.md#branch-orders-of-the-primitive-factor-and-of-the-whole-pencil)

## How many sheets each inertia generator must move

Suppose \(R\) has exactly three branch values. Fix one of them with inertia order \(q\ge2\), let \(\theta=1-1/q\), and let \(F\) be its count of fixed sheets of \(R\). If its action on the \(s\) outer blocks interchanges two blocks, then \(s=2\) and \(F=0\). Otherwise \(V\) is unramified there. Above this value it has \(s\) distinct preimages with inertia permutations for \(W\) of order dividing \(q\). Denote their fixed counts by \(f_i\). A fixed full sheet determines a fixed primitive sheet, so \(F\le h\sum_i f_i\).

There are at most two further points on the source of \(V\) where \(W\) can branch. This is immediate for \(s=1\). For \(s=2\), both other branch values of \(R\) are the two distinct branch values of \(V\), each with a single preimage. In Burnside's cycle formula one may average over any cyclic order divisible by the actual permutation order. Assign the nominal order \(q\) to each of the \(s\) selected permutations, allowing identity permutations. The other two terms \(1-1/d\) in the excess formula sum to less than two. Thus the excess \(\widehat E\) computed using these nominal orders is at most \(s\theta\). The ordered-triple formula for \(G\) remains exact with the corresponding nominal powers. Every nonzero nominal exponent at the selected points fixes at least \(f_i\) primitive sheets. Writing \(T=s^{-1}\sum_i(f_i)_3\), discarding the other nonnegative contributions gives
\[
  G\ \le\ ma\,s\theta-s\theta T,\qquad
  T\ \le\ a\left(m-\frac{3m/7-(6+8/(7h))/s}{\theta}\right). \tag{3}
\]
This implies \(7T\le a(4m+50)\) for arbitrary \(q\), \(7T\le a(m+100)\) for \(q=2\), and \(14T\le a(5m+150)\) for \(q=3\).

For \(\bar f=s^{-1}\sum_i f_i\), the same discrete tangent gives \(B\bar f-C\le T\). For arbitrary \(q\), take \(b=\lfloor82983m/100000\rfloor\) in the tangent to obtain \(\bar f<82983m/100000\) for both production values of \(m\). For \(q=2,3\) use \(b=\lfloor13069m/25000\rfloor,\lfloor1419m/2000\rfloor\), respectively. The corresponding bounds are \(\bar f<13069m/25000\) and \(\bar f<1419m/2000\). Applying \(F/D\le\bar f/m\) gives the table, including the even number of moved sheets in an involution.

## A production-degree branch system satisfying these tests

Even three branch values can satisfy all the inequalities above at \(m=D\). Partition the \(m\) letters into three ordered lists \((c_i),(u_i),(v_i)\) of lengths \(k=89478484,\ l=89478499,\ t=89478471\). Let \(\sigma\) cycle through the \(c_i\) and then the \(u_i\). Let \(\tau\) cycle through the \(c_i\) in reverse order and then the \(v_i\). The product \(\sigma\tau\) fixes \(c_2,\ldots,c_k\) and cycles through the other \(l+t+1\) letters. The triple \(\sigma,\tau,(\sigma\tau)^{-1}\) consequently has single nontrivial cycle lengths \(178956983,178956955,178956971\). Their indices sum to \(2m-2\), giving a genus-zero system.

The group is transitive since the first two supports meet and together cover all letters. The first cycle has prime length greater than \(m/2\). In any nontrivial block system, both the block size and block count are smaller than this prime. The first cycle would have to fix each block and its support would have to lie in a single block, which is impossible. The group is primitive. The prime cycle fixes at least three points, so Jordan's theorem gives \(A_m\) in the natural action. All three generators are even, hence the group is precisely \(A_m\). [Jordan's theorem in Jones, Theorem 1.1](https://arxiv.org/abs/1209.5169)

The triple has \(G=17193610840088566682587812\), exceeding \(0.88ma\), and all three generators move more than \(178956950\) letters. This supplies explicit admissible branch data. The assignment of three **unramified** fibers to the specific subgroup \(H\) remains the additional requirement for a threshold witness. The verification enumerates cycle types only at degrees three through nine and checks the production branch system by its cycle formulas.
