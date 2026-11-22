# Sharp weight two on both named order-128 grids

On the order-128 roots in either named field, every balanced integer-weight locator comparison with $|w(j)|\le2$ lifts to the complex roots with the same exponents. The bound is sharp in each field. Here balanced means $\sum_j w(j)=0$, and the two compared sites avoid the support. Positive and negative weights are multiplicities of disjoint numerator and denominator locators.

| Named field | Exact maximum uniform weight | Ellipsoid points across 64 displacements | Final integer separating rows | Weight-three witness degrees | Witness centers |
|---|---:|---:|---:|---:|---|
| First | 2 | 216,604 | 75 | 168 | 0, 51 |
| Second | 2 | 107,204 | 36 | 160 | 0, 39 |

The witness ratios take the finite values 363642071178106647899388690939548965289232361949 and 102290252946794350420103001858531213796044284166, respectively, at both listed centers. Their primitive-unit exponent differences are nonzero, so the complex ratios differ. The certificate supplies the complete 128 entries and the verifier evaluates both finite ratios directly. [Witnesses and separating rows](../../../scripts/probes/mu128_balanced_weight_two_certificates.json)

## Consequence for antipodal pairs at length 256

For a signed difference $w=1_P-1_D$ of equal-size disjoint simple supports in $\mu_{256}$, write $s(j)=w(j)+w(j+128)$. Taking the product of the ratio over an antipodal pair gives the order-128 weighted ratio with this $s$, up to a fixed sign. Thus if two complete antipodal pairs are tested at one common value, the corresponding projected comparison lifts for arbitrary placements of the two pairs. No assumption on the individual root placements within pairs is needed. [Orbit product identity](dyadic-orbit-norm-split-pencils.md#norms-of-evaluations-on-complete-cosets)

In particular, for **any three-split pencil of odd degree on either named length-256 grid**, there is a quotient parity on which at most one of its fibers contains three complete antipodal pairs. To see this, call a fiber heavy on quotient parity $p$ if it contains at least three complete antipodal pairs with exponent representatives in that parity. For a heavy fiber, the quotient ratio of the other two fiber locators agrees on three centers in that parity. Transfer and the complex three-center theorem for integer weights force equality of their signed half-population differences on the opposite parity. These are the differences between each of the two opposite pairs in a four-site orbit. [Three-center theorem](quarter-dyadic-parity.md#three-equal-ratios-in-one-parity-class)

If two fibers were heavy on each parity, then on every four-site orbit all three fiber half-population differences would agree. A nonzero common value requires all three disjoint fibers to occupy a single half of size two. Hence all three differences vanish everywhere. Each fiber then has even cardinality, contradicting the pencil degree. The fibers furnishing the two comparisons may vary with the parity. The argument uses six sites per heavy fiber and parity and permits arbitrary positions of the three antipodal pairs. [Lean counting theorem](../../../ArkLib/Research/ProximityGap/Frontier/DyadicAntiperiodicReflection.lean)

## Exact replay

The proof uses the full-group phase equations, energy ellipsoids and integer separating rows from the sharp order-64 method. Here the primitive-unit dimension is 32, the energy limit is $126\cdot2^2=504$, and all 64 displacements are tested. The inversion identity holds within each named field. Nonzero vectors are excluded by a verified separating row or a direct phase computation. The remaining zero exponent gives the same root-of-unity phase in both fields of definition. [Balanced phase and separation proof](mu64-balanced-weight-threshold.md)

The default verifier accelerates the enumeration using a rigorous integer enclosure. For the exact Gram–Schmidt coefficients $\mu_{ji}$ and squared lengths $d_i$, choose $C=2^{15}$ and $K=2^{25}$. With squared search radius $R$, set $a_{ji}=\operatorname{round}(C\mu_{ji})$ and $b_i=\lfloor Kd_i/R\rfloor>0$. After fixing lattice coordinates $v_j$ for $j>i$, let $S_i=\sum_{j>i}a_{ji}v_j$ and $E=\sum_{j>i}|v_j|$. The contribution of row $i$ to the Gram form, in units of $R/(KC^2)$, is at least
$$
 b_i\max(0,|Cv_i+S_i|-E)^2 .
$$
The native program enumerates the entire integer tree with these lower bounds and budget $KC^2$. Its integer square root corrects the initial approximation by exact integer comparisons. Before the call, Python bounds the absolute value of every possible coordinate, every partial sum and the fixed-point products against signed-integer overflow. At every leaf Python reconstructs and checks the original integral Gram form exactly. Complete runs with opposite basis orders give the same counts. A slower mode branches directly using exact rational orthogonal coordinates. On first-field displacement 1 the two methods independently found all 5,699 points. [Verifier](../../../scripts/probes/probe_mu128_balanced_weight.py) · [Integer enclosure](../../../scripts/probes/probe_lattice_enclosure.cpp)

Run `uv run --no-project --with python-flint python scripts/probes/probe_mu128_balanced_weight.py`. Use `--reverse-basis` to change the basis order, or `--rational --field 2 --shifts 32 64` for a small rational replay.
