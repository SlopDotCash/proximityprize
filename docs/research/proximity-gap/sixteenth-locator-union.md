# Overlapping locator lists at rate one sixteenth

At length $n=2^{30}$ and dimension $2^{26}$, a single received word on the first designated prime has at least **1,075,401,692** codewords within **989,855,734 errors**. On the second prime there are at least **2,183,380,672** within **989,855,741 errors**. Each number exceeds its field's budget $B=\lfloor p/2^{128}\rfloor$. The scalar lists lift to every positive interleaving width by repeating the same row in the center and each candidate. Scaling transports the construction to any multiplicative coset of order $n$ over a field with the indicated budget.

Using squared locator values gives the two witnesses below. Keeping the sign gives the sharper first-prime witness.

| Field | Budget $B$ | Max. signatures per anchor | Anchor incidences | Distinct candidates | Gain $g$ | First failure at or before |
|---|---:|---:|---:|---:|---:|---:|
| First | 1,073,741,824 | 419,430 | 1,276,465,776 | 1,124,276,896 | 10 | **989,855,735** |
| Second | 2,147,483,648 | 1,048,576 | 2,659,659,888 | 2,183,380,672 | 4 | **989,855,741** |

The earlier seven-anchor ceilings were 989,855,741 and 989,855,744. The exact first failing counts remain open on both domains. [Previous construction and prime certificates](reciprocal-fiber-lists.md)

## One center at all fifteen anchors

Set $M=128$, $h=n/M=2^{23}$, and let $u$ generate the quotient group $\mu_M$ obtained as the image of $x\mapsto x^h$ on $\mu_n$. The exponents of the subgroup $S=\mu_{16}$ are the multiples of eight. Take nine-element subsets $T$ of $\mu_M\setminus S$ with $\prod_{z\in T}z=1$. Their locators $L_T(Y)=\prod_{z\in T}(Y-z)$ all have constant coefficient $c=-1$. Put

\[
Q_T(Y)=\frac{Y^9+c-L_T(Y)}{Y},\qquad f_T(X)=H(X)Q_T(X^h),
\]

where $H$ is monic and its roots are exactly $h-1$ sites of $x^h=1$. Leading and constant terms cancel in the numerator, so $\deg f_T\le 8h-1<k$. The baseline center $w(x)=H(x)((x^h)^9+c)/x^h$ agrees with $f_T$ on the $9h$ points with $x^h\in T$ and on the $h-1$ roots of $H$. Distinct $T$ give distinct locators and hence distinct $f_T$ by injectivity of substitution and cancellation of $H$. Evaluation preserves distinctness since $\deg f_T<n$. Scaling $X$ transports both the center and candidates to any coset.

For each $y\in S\setminus\{1\}$ classify $T/y$ by its vector $v$ of 32 leaf sums in the reciprocal-pair tree. For $N(z)=(1-z)(1-z^{-1})$, the identities $N(z)=N(z^{-1})$ and $N(z^2)=N(z)N(-z)$ express the product of the $N(z)$ over $T/y$ using only $v$. Since $\prod_{z\in T/y} z=y^{-9}$, the identity

\[
  L_{T/y}(1)^2=(-1)^9y^{-9}\prod_{z\in T/y}N(z)
\]

gives at most two possibilities for $L_T(y)=y^9L_{T/y}(1)$ at fixed $y,v$. Select at most $b$ vectors at each anchor. Inside its $h$ sites allocate $g=\lfloor h/(2b)\rfloor$ sites for each of the at most $2b$ distinct locator values $l$. Use $H(x)(y^9+c-l)/y$ as the received value on the sites allotted to $l$. This specifies one center. The allocated coordinates at all fifteen anchors are disjoint from all $9h+(h-1)$ baseline agreements. Every $T$ with a selected vector at one or more anchors has at least $10h-1+g$ agreements, giving the two displayed ceilings. The allocations use at most 8,388,600 and 8,388,608 of the 8,388,608 sites per anchor.

## Counting the union exactly

A vector's score is its number of nine-subsets before imposing the product. The 112 ordinary roots form eight disjoint reciprocal-pair trees of four leaves each. The node occupancy $a\in\{0,1,2\}$ adds $a$ to every descendant leaf and contributes the factor $\binom{2}{a}X^a$ to its size enumerator. The coefficient of $X^9$ after multiplying the eight subtrees' enumerators is the score. The verifier generates all labelled vectors with even leaf sum and score greater than 7,680. The parity constraint follows from the even exponent of $y^{-9}$ and the fact that an internal node has an even number of leaves. It produces 1,923,274 distinct vectors. [Reciprocal-pair recurrence](reciprocal-fiber-lists.md#counting-root-sets-with-few-locator-values)

Using the same pools at every anchor gives a first-prime ceiling of 989,855,737 and a second-prime ceiling of 989,855,742. For this uniform choice the first pool consists of all scores greater than 9,504. The second takes all scores greater than 8,192, then whole odd-multiplier orbits at score 8,192 up to capacity $\lfloor h/6\rfloor=1,398,101$. The verifier orders tied orbits by the least unsigned integer encoding of a member and skips orbits larger than the remaining capacity. The encoding places the tree's first leaf in the least significant four bits, visiting the child $j/2$ before $(M-j)/2$. Multiplication of exponents by any odd $u'$ permutes the leaves, fixes the required product 1, and permutes the fifteen nonidentity anchors. Both pools are invariant under this action.

For each anchor exponent $a$ and selected vector, enumerate all nine-subsets of relative exponents with that vector and sum $-9a\bmod128$. Adding $a$ to each relative exponent gives exactly the desired original root sets of product 1. The verifier forms local subsets on the fourteen ordinary sites in each tree, joins their masks by leaf sum, and imposes the size and residue conditions. It enumerates one representative for each orbit of anchor-vector pairs and multiplies by the orbit size. The anchor representatives $a=8,16,32,64$ have orbit sizes $8,4,2,1$. Inside a fixed anchor it uses precisely the odd multipliers fixing that anchor.

For the sharper table, let $P_a(v)$ count these product-one subsets rooted at anchor $a$ with relative vector $v$. At each anchor representative, rank stabilizer orbits by decreasing $P_a(v)$ and break ties by their least packed integer. Select each orbit that fits within $b=419430$ or $1048576$ vectors, respectively, and transport the choices to the other anchors by odd multipliers. Write $U_a(v)$ for the number of members of this class whose vectors were selected at none of the fourteen other anchors. Perform one simultaneous reselection, using the same capacity rule with score $P_a(v)+3U_a(v)$. Each member previously missed everywhere else has weight four when choosing the replacement pool. Both scores are invariant under the anchor stabilizer, and transportation does not depend on the chosen multiplier. The resulting pools can differ from anchor to anchor.

For every such incidence the verifier recomputes the vectors at all fifteen anchors. If $T$ occurs at $j$ anchors in the pool, add $D/j$, where $D=\operatorname{lcm}(1,\ldots,15)=360360$. Each admitted $T$ contributes exactly $D$ over all its incidences. This weight is invariant under odd multipliers. Dividing the orbit-weighted sum by $D$ gives the table’s number of distinct candidates. The full count fits unsigned 64-bit arithmetic since $D\binom{112}{9}=1,980,020,864,777,155,200<2^{64}$. Lists obtained by changing the fixed root product would have a different common constant $c$ in the baseline center. Their cardinalities cannot simply be added to this construction.

## Keeping the locator sign at the first prime

At a fixed anchor $u^a$, let $R$ denote the relative root exponents, each represented by its integer in $[0,M)$. For a fixed leaf vector $v$, the extra bit of $e(R)=\sum_{j\in R}j\bmod 2M$ above the known residue $-9a\bmod M$ determines the actual locator value. At a complex primitive $M$th root the absolute value is fixed by the leaf norms and the phase by $e(R)$, since $1-e^{2\pi ij/M}=-2i\,e^{\pi ij/M}\sin(\pi j/M)$ and all the sines are positive. Equality at the complex root implies divisibility of the difference of the two integer locator evaluations by $\Phi_M$, so the equality holds at the primitive $M$th root in either named field. Each selected signed mode therefore needs a single allocation. With $b=762600$ modes per anchor, $11b=8388600\le h$. [Signed locator identity](oriented-fiber-list-bounds.md#the-locator-value-at-the-spare-fiber)

To transport this bit, put $f_w(j)=\lfloor wj/M\rfloor$ for an odd multiplier $w$. For a relative set of size $m$ the transformed exponent sum satisfies
\[
 e(wR)\equiv w e(R)-M\left[\sum_{i\text{ leaf}}v_i f_w(i)
          +\tfrac{w-1}{2}\left(\sum_i v_i-m\right)\right]\pmod{2M}.
\]
Indeed $f_w(M-j)=w-1-f_w(j)$ has the same parity as $f_w(j)$. At an even node $j$, $f_w(j/2)+f_w((M-j)/2)\equiv f_w(j)+(w-1)/2\pmod2$. Expanding the node down to its $s$ leaves uses $s-1$ such steps. The leaf vector records each node once per descendant leaf, giving the correction displayed above. To move from one anchor to another, subtract the offset from each ordinary exponent and add $M$ once for each representative that crosses zero. The verifier implements both operations with integer bit masks.

Rank the signed modes initially by their prescribed-product populations $P_a$. Make one simultaneous reselection by $P_a+2U_a$, then two further reselections by $U_a$ alone, first at anchor exponent 64, then simultaneously at 32 and 96. In each reselection $U_a$ uses the selections immediately preceding that round. The same orbit capacity rule applies, breaking ties first by the packed leaf vector and then by the high bit. These symmetric selections give 1,240,417,392 incidences and a union of 1,073,709,616 candidates.

Finally hold the fourteen anchors other than 32 fixed. At 32 the signed modes partition the root sets, so choosing the $b$ individual modes with largest $U_{32}$ maximizes the number of additional candidates at that anchor within the generated pool. The remaining anchors miss **61,386,048** candidates from the old selection at 32. They miss **63,078,124** from the new selection. For a particular selection, break equal exclusive populations by the packed leaf vector and then the high bit. The verifier counts the multiplicities of those equal populations on stabilizer orbits. A partial final group of tied modes has the same exclusive count for every choice of its specified size. The resulting list contains exactly
\[
  1073709616-61386048+63078124=1075401692
\]
distinct certified words. This exceeds $2^{30}$ by **1,659,868**. With eleven additional agreements, the first failing count is at most **989,855,734**.

## Allocating partial agreements across these two pools

Suppose the two unsigned selections in the table receive $x$ and $y$ sites, respectively, for each possible locator value. Using the certified two-value allowance for each signature gives $419430x+1048576y\le4194304$. In particular $x+2y\le10$ and $y\le4$. A root set having $r,s$ selected anchors in the two pools receives $xr+ys$ certified extra agreements, counting both allocations when the two pools select the same anchor.

Writing $I$ for incidence count and $U$ for union size, at most $(I-U)/(j-1)$ candidates of a given pool have at least $j\ge2$ hits, since each such candidate contributes at least $j-1$ to $I-U$. Gain 11 forces either $r\ge2$ or $s\ge3$. The unsigned table thus bounds this population by $152188880+476279216/2=390328488$, below the first budget. Gain 5 forces $r\ge1$ or $s\ge2$, for at most $1124276896+476279216=1600556112$ candidates, below the second budget. This counts only the memberships and the uniform per-mode allocations specified here. Different selections or certified coincidences between locator values could change the conclusion.

## Reproduction

Run the following from the repository root with Python 3 and a C++17 compiler supporting unsigned 128-bit integers. The program builds in a temporary directory. Select one to three workers.

```sh
python3 scripts/probes/check_sixteenth_locator_union.py --workers 3
```

The controls enumerate all 220 root sets at $(M,|S|,m)=(16,4,3)$ and all 42,504 at $(32,8,5)$. They compare every retained labelled vector and its score with the size recurrence. They independently choose the tied orbits by multiplying actual root exponents, count union sizes by direct membership, and compare these results with the C++ census. On the smaller board all four selected polynomials are also evaluated over the entire length-1,024 domain in $\mathbb F_{65537}$. The smallest actual agreement count is 285. Both controls also construct the initial product-conditioned pools and recompute every unshared population by direct membership. For the refined pools at order 32 the direct unions have 728 and 984 root sets. On the order-32 signed control, direct enumeration gives 968 candidates before the last substitution and 992 afterwards. The production output is

```text
Uniform pools
orbits=421270 denominator=360360
bins=517954 incidences=1551671296 unique=1132216224
bins=1398090 incidences=3367652416 unique=2459641984
Product-conditioned pools after one overlap refinement
orbits=554246 denominator=360360
bins=419430 incidences=1276465776 unique=1124276896
bins=1048576 incidences=2659659888 unique=2183380672
budget=1073741824 list=1124276896 gain=10 first_bad<=989855735
budget=2147483648 list=2183380672 gain=4 first_bad<=989855741
Signed modes at the first budget
response_anchor=32 pool=0 previous=61386048 offered=63078124 increase=1692076
orbits=1040088 denominator=360360
bins=762600 incidences=1240417392 unique=1073709616
budget=1073741824 list=1075401692 gain=11 first_bad<=989855734
```

Lean proves the locator and fiber-allocation identities. The production union sizes use the executable integer census. [Allocation lemmas](../../../ArkLib/Research/ProximityGap/Frontier/ReciprocalFiberLists.lean) · [Pool generator and independent controls](../../../scripts/probes/check_sixteenth_locator_union.py) · [Exact union census](../../../scripts/probes/probe_sixteenth_locator_union.cpp)
