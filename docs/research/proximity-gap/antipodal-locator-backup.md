# Antipodal backup sites for an eighth-rate list

On the first named prime at length $n=2^{30}$ and rate $1/8$, one scalar center has at least **1,077,779,404** distinct words within **921,069,147** errors. A second construction retains the full earlier list of 1,091,906,924 words within 921,069,150 errors. The budget is $2^{30}=1,073,741,824$. This improves the earlier first-failure ceiling by thirteen errors and applies at every positive interleaving width by repeating one scalar row. The exact first failure remains open. [Earlier center and signed-mode identity](rotated-locator-union.md) · [Verifier](../../../scripts/probes/probe_antipodal_locator_backup.py)

## The two primary sign classes

Let $M=128$, $h=n/M=8,388,608$, and let $u$ have order $M$. Reserve the eight fibers $x^h=u^{16a}$ for $0\le a<8$. Use the earlier palette of 34 signed modes for ordinary 17-subsets $T$ whose exponent sum is eight modulo 128. It has five modes at anchors 2 and 7 and four at every other anchor. At each five-mode anchor two of the modes have the all-ones vector and the two possible signs. The palette represents at least 1,091,906,924 distinct sets by its single count 1,092,217,628 and its pair sum 310,704. The verifier regenerates the palette and both counts.

At a primary anchor the pair of relative exponents $\{j,-j\}$ becomes $\{64-j,-(64-j)\}$ at the opposite anchor. Its two orientations therefore have the same contribution to the opposite leaf vector. Given the primary vector, enumerate the occupancies of its inverse pairs, each taking values 0, 1 or 2. The occupied exponent pairs are disjoint. For each pair of occupancy $q$, add $q$ times the leaf vector of the singleton $64-j$ to the opposite vector. At an internal node subtract $q$ from the prescribed descendant entries and recurse on both children. At a leaf its residual must equal $q$. Reserved nodes have $q=0$. Keeping only total occupancy 17 gives exactly the attainable opposite vectors before imposing a product restriction. The finite recurrence gives **17,068** vectors for the all-ones input. At the opposite anchor the fixed root product determines the sum of relative exponents modulo 128. There are at most two choices modulo 256, hence at most **34,136** signed modes for both primary signs together. Each signed mode fixes one field value of the locator. [Signed-mode formula](rotated-locator-union.md#signed-modes-over-the-field)

## Site allocation

Give each of the 34 primary modes $G=1,677,731$ sites, except that both all-ones modes at each five-mode anchor get $G-24$ sites. At the corresponding opposite anchors 6 and 3, respectively, give each of the 34,136 possible signed modes another 24 sites. Choose disjoint sites for every assignment, including any duplicated value. Every represented set now has at least $G$ assigned agreements. Its primary allotment alone suffices unless it uses one of the four shortened modes, in which case its opposite allotment supplies the 24 missing agreements.

The two five-mode fibers use $5G-48=8,388,607$ sites each. The two backup fibers use $4G+34,136\cdot24=7,530,188$ sites each. The four other fibers use $4G=6,710,924$ sites each. After the assignments, placing $h-1$ distinct common roots in the remaining reserved sites still leaves 38,971 sites free.

Let $H$ be the monic polynomial with those $h-1$ roots, let $L_T(Y)=\prod_{j\in T}(Y-u^j)$, and let $c=L_T(0)$, common to all represented sets. Use the message $H(X)(Y^{17}+c-L_T(Y))/Y$, where $Y=X^h$. Its degree is at most $16h-1$. Distinct locators yield distinct messages. The center at $x$ is $H(x)(y^{17}+c-v)/y$, with $y=x^h$ and $v$ the assigned locator value, or zero at an unassigned site. Each represented message agrees on its $17h$ ordinary root sites, the $h-1$ common sites, and at least $G$ assigned sites. These site sets are disjoint. The resulting error count is $n-18h+1-G=921,069,150$.

## Keeping the most populated backup values

For the smaller radius, use $G=1,677,734$, shorten the two primary signs by 31 sites, and provide 31 backup sites for each of the 27,055 most populated signed opposite modes at each backup anchor. Compute the population conditional on the all-ones primary vector, allowing both primary signs. In the tree recurrence attach a polynomial modulo $Z^{256}-1$ to each total size and opposite vector. The orientation factor for node $j$ is $1$ for zero occupancy, $Z^{64-j}+Z^{64+j}$ for one, and $Z^{128}$ for two. Multiplying child polynomials and the node factor counts the ordinary representative sums at the opposite anchor. Keep only the two residues compatible with absolute product eight modulo 128. Each of the two shortened sign pairs originally contains 66,347,424 sets. At each backup anchor the omitted coefficients sum to 7,063,760. Subtracting both omitted masses from the earlier union lower bound still leaves **1,077,779,404** distinct sets. This subtraction allows all omissions to be distinct, including any sets that another main mode continues to serve.

The two five-mode fibers now use exactly 8,388,608 sites each. The backup fibers use 7,549,641 each, and the four remaining fibers use 6,710,936 each. These assignments leave 15 sites beyond the $h-1$ common roots. Every retained set therefore achieves $18h-1+G$ agreements and at most **921,069,147** errors.

The histogram code packs each of the $2M$ coefficients as a base-$2^M$ digit. Coefficients count subsets of fewer than $M$ ordinary positions. Children and node use disjoint positions, so even unreduced convolution entries and the subsequent cyclic sums stay below the digit base. End-around reduction of the digit blocks implements $Z^{2M}=1$.

The executable compares the opposite-vector recurrence with exhaustive signed-root sets at orders 16 and 32, checks the field factorization at the production prime, and recomputes the pair intersections. The new allocation and its production counts are a written proof with executable finite checks.

```sh
python3 scripts/probes/probe_antipodal_locator_backup.py
```
