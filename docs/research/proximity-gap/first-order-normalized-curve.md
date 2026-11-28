# Counting isolated polynomial solutions on the normalized differential curve

For the four first-order interpolation examples, counting the poles of the derivative on a smooth curve gives list budgets of **81, 53, 32 and 20 times the block length**. Each row below proves an unrestricted closed-ball bound at length \(n=2^{30}\), on every injective grid and at every positive width in the stated characteristic range. The two designated fields have smaller literal budgets. [Interpolation and the preceding finite bounds](first-order-integral-families.md) · [Exact checks](../../../scripts/probes/probe_first_order_normalized_curve.py)

| Rate | Safe errors | List budget | Multiplicity \(r\) | Total jet degree \(b\) | Derivative degree \(v\) |
|---:|---:|---:|---:|---:|---:|
| \(1/2\) | 318,582,739 | \(81n\) | 13 | 18 | 3 |
| \(1/4\) | 547,807,172 | \(53n\) | 12 | 23 | 3 |
| \(1/8\) | 706,542,381 | \(32n\) | 10 | 27 | 3 |
| \(1/16\) | 816,890,638 | \(20n\) | 7 | 25 | 4 |

Keeping the four larger field budgets of the preceding note instead gives these additional safe counts.

| Rate | Existing field budget | Safe errors | \(r,b,v\) |
|---:|---:|---:|---:|
| \(1/2\) | \(89n\) | 319,220,543 | 14, 19, 3 |
| \(1/4\) | \(59n\) | 548,801,377 | 10, 19, 4 |
| \(1/8\) | \(35n\) | 708,016,270 | 9, 22, 4 |
| \(1/16\) | \(22n\) | 818,211,920 | 8, 27, 4 |

Let \(d=k-1\) be the message degree bound, and \(n\ge t>d\ge1\) the agreement requirement. Use a first-order interpolant with the slot surplus and degree bounds of the preceding note. Assume characteristic zero or
\[
           p>\max(rt+1,2b^3+2).
\]
The resulting list cardinality is at most
\[
  2bv-v^2+b+d(4bv-2b-2v^2)+\frac{v(n-d)}{t-d}.                 \tag{1}
\]
The first-order interpolation threshold and the linear asymptotic dependence on length are established by Dao, Kominers and Thaler and by Gabizon. The calculation below sharpens the finite coefficient for these inputs. [Dao–Kominers–Thaler](https://eprint.iacr.org/2026/2056) · [Gabizon](https://eprint.iacr.org/2026/2048)

## The derivative on the smooth curve

Scalarize the interleaving and take \(k\) to be the algebraic closure of the resulting coefficient field. Factor the interpolant over \(K=k(X)\) in \(Y,V\). Fix an irreducible factor \(g\) of total degree \(B\) and positive \(V\)-degree \(s\le B\). Write \(T=g_V\). Coprimality of \(g,T\) follows from the degree and characteristic bounds. The singular solution jets \(g=T=0\) have cardinality at most \(2Bs-s^2-B\) by the plane intersection bound at infinity. If \(g\) has a regular polynomial solution, its \(K\)-rational point \((f,f')\) lies on exactly one geometric component since \(T\ne0\) there. The geometric components of an irreducible curve are conjugate over a separable closure, and this point is fixed under all such conjugations. Thus \(g\) is geometrically irreducible. In detail, coprimality with \(T\) persists under scalar extension and makes the curve geometrically reduced. A purely inseparable extension is a universal homeomorphism, so the distinct components already occur over the separable closure.

Work with \(L=K^{\mathrm{sep}}\) and its unique extension of the derivation \(d/dX\). The function field of the curve carries the derivation
\[
       \delta Y=V,\qquad
       \delta V=-(g_X+Vg_Y)/T .
\]
In \(g_X\) the coefficients are differentiated. On the smooth projective model consider the projection \(Y\) of degree \(s\), which is separable and tame since \(s<p\). Over the algebraic closure, the plane model has degree \(B\) and multiplicity at least \(B-s\) at \([0:1:0]\) in coordinates \([Y:V:H]\). The plane genus bound subtracts at least \((B-s)(B-s-1)/2\) from the arithmetic genus. Hence the sum \(R\) of \(e_P-1\) over the ramification points of the projection satisfies, by Riemann–Hurwitz,
\[
                 R\le (s-1)(2B-s).
\]

Here the exceptional places used to compute poles admit expansions over \(L\) itself. The leading coefficient of \(g\) in \(V\) has \(Y\)-degree at most \(B\). The binary discriminant in \(V\) has \(Y\)-degree at most \((s-1)(2B-s)\). Indeed each term of the discriminant uses \(2s-2\) coefficients with total index weight \(s(s-1)\), and coefficient \(j\) has degree at most \(B-j\). For \(s=1\) take the discriminant to be one. Away from their zeros and infinity all points have finite coordinates and \(T\ne0\); every iterated derivative of \(Y\) is regular there by its expression in the localization at \(T\). The exceptional base values belong to \(L\), since each of these nonzero univariate polynomials has degree below \(p\). So do the residue fields of the places over them: these extensions of \(L\) have degree at most \(s<p\). In characteristic zero the separable closure is already algebraically closed. The local rings on the normalization at these rational places are discrete valuation rings with completion \(L[[\tau]]\), geometrically regular there. Thus the pole calculation also counts the geometric poles. It only uses a derivation on the separable closure.

At a finite exceptional base value write \(Y=a+\tau^{e_P}\) using tameness and extracting the root of a unit in the completion. At a pole of \(Y\) use \(Y=\tau^{-e_P}\). In the two cases respectively,
\[
 \delta\tau=\frac{V-a'}{e_P\tau^{e_P-1}},
 \qquad
 \delta\tau=-\frac{V\tau^{e_P+1}}{e_P}.
\]
Coefficientwise differentiation plus \((\delta\tau)d/d\tau\) defines a derivation on the completed Laurent series field. Its value on \(Y\) is \(V\), so its restriction to the curve field is the specified derivation by separability over \(L(Y)\).

If \(Y\) is finite and \(V\) has a pole of order \(h>0\), each differentiation increases the current pole bound by at most \(h+e_P\). At a finite ramification point where \(V\) is regular the increase is at most \(e_P\); at a finite unramified point with \(V\) regular it stays regular. Above \(Y=\infty\) the increase is at most \((h-e_P)_+\), with \(h=0\) if \(V\) is regular. These statements follow by differentiating Laurent series with the two formulas above.

For a generic constant \(\lambda\), the degree of \(V-\lambda Y\) is at most \(B\), by intersecting the plane curve with lines. Taking \(\lambda\) away from the finitely many leading-term cancellations gives
\[
 \sum_{Y\text{ finite}} h+\sum_{Y\text{ infinite}}(h-e_P)_+\le B-s .
\]
The number of finite \(V\)-poles is at most \(B-s\) as well. At each of these poles write \(e_P=1+(e_P-1)\); each other finite ramified place satisfies \(e_P\le2(e_P-1)\). Consequently the total pole increase per derivative is at most
\[
       2(B-s)+2R\le 4Bs-2B-2s^2 .
\]
Starting with \(V\), which has pole degree at most \(B\), yields
\[
       \deg(\delta^{d+1}Y)_\infty\le B+d(4Bs-2B-2s^2).          \tag{2}
\]
If this derivative is nonzero, every regular polynomial solution gives a distinct zero of it, evaluated at the generic coordinate \(X\). Thus (2) bounds the regular solutions on such a factor. The pole count can have linear growth of this order even in characteristic zero. For example when \(g=V\prod_{j=1}^{B-1}(Y-c_j)-1\) with distinct constants, \(V\) has \(B-1\) simple poles, each of order \(1+2d\) after \(d\) differentiations under \(\delta Y=V\).

## Entire families and the finite inputs

If \(\delta^{d+1}Y=0\), the truncated Taylor construction produces a whole family of polynomial solutions on the initial curve at an independent transcendental point \(\xi\). For factors carrying a regular solution, geometric irreducibility proved above means this initial curve has only one component. Its generic evaluation map has degree at most \(s\) by reverse Taylor reconstruction. Specializing the independent variable only decreases the common pole divisor bound for nonconstant evaluations. At most \(d\) domain sites give a constant agreeing value. The incidence estimate for the family is therefore \(s(n-d)/(t-d)\). [Taylor construction and incidence proof](first-order-integral-families.md#entire-families-of-polynomial-solutions)

For all positive-derivative factors, combine their singular charges with (2) and the family estimate. The sums of the individual \(s\) and \(B\) are bounded by \(v\) and \(b\). Both \(2Bs-s^2\) and \(4Bs-2B-2s^2\) are increasing in the integral degree bounds \(1\le s\le B\) and are superadditive on this cone. The cross term of the latter at two factors is \(4(B_1s_2+B_2s_1-s_1s_2)\). Factors independent of \(V\) contribute at most \(b\) words in total. This gives (1).

For the four rows in order, put \(p=c2^{158}+h2^{100}+1\), with \((c,h,a)=(81,22,3),(53,28,7),(32,64,5),(20,95,3)\). The verifier checks \(a^{(p-1)/2}\equiv-1\bmod p\) and \((2^{100}+1)^2>p\), which force primality since every prime divisor of \(p\) is \(1\bmod 2^{100}\). Each field has an order-\(n\) subgroup and literal 128-bit list budget \(cn\). The proof applies to every injective length-\(n\) grid in it.

On the earlier fields with budgets $89n,59n,35n,22n$, the pole count allows error counts **319,220,543, 548,801,377, 708,016,270 and 818,211,920**, respectively. All eight boards have positive surplus at the displayed error and exhaust that surplus one error later. Other interpolation boards and other proofs could extend these safety results. The geometric argument is written. Lean verifies all eight slot and degree comparisons at the exact endpoints. [Finite comparisons](../../../ArkLib/Research/ProximityGap/Frontier/FirstOrderIntegralFamilyCounts.lean)
