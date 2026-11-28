# Additional serving fibers for eighth-rate lists

At length $2^{30}$ and rate $1/8$, explicit scalar centers exceed both designated list budgets at the following error counts. These first-failure ceilings extend to every positive interleaving width by repeating a scalar row. The exact first failures remain open. [Earlier regular-fiber construction](rotated-locator-union.md) · [Antipodal backup construction](antipodal-locator-backup.md) · [Verifier](../../../scripts/probes/probe_staggered_locator_anchors.py)

| Field | First failure at or before | Distinct words at least | Budget |
|---|---:|---:|---:|
| First named prime | **920,811,049** | 1,078,794,742 | 1,073,741,824 |
| Second named prime | **921,826,181** | 2,158,985,328 | 2,147,483,648 |

## Nine serving fibers

A nine-fiber construction first gives **2,157,494,640** distinct words within **921,840,005 errors** on the second prime. The ten-fiber construction below gives the two table entries.

Take $M=128$, $h=n/M$ and $u$ of order $M$. The original eight serving fibers have quotient exponents $a\in16\mathbb Z/M$. Add the fiber with exponent 8. Take ordinary 17-subsets $T$ disjoint from these nine exponents and with absolute exponent sum $8\bmod128$. At the extra anchor count only sets also omitting its antipode, exponent 72. Every counted mode is thus a signed reciprocal-tree mode with a unique field locator value. [Signed-mode identity](rotated-locator-union.md#signed-modes-over-the-field)

At each original anchor use the nine most populated signed modes among the all-ones vector and the vectors formed by raising a single aligned block of four or eight leaves from one to two. Rank ties by decreasing vector and then decreasing signed exponent. At the extra anchor take both signs of the all-ones vector. The exact single-anchor sum is 2,159,232,164. Across the original anchors the earlier pair counter gives at most 1,736,356 repetitions, since it permits the extra exponent 8 among the roots.

## The mixed pairs

For anchor $a$ put $W_a(T)=\sum_{j\in T}\gcd(j-a,128)$. This equals the sum of the leaf entries, since each inverse-pair node covers that many odd leaves. If $a$ is an original anchor, a root $j$ not divisible by eight contributes the same weight at $a$ and at 8. For $j\equiv8\bmod16$ the contribution at $a$ is eight and at 8 it is at least sixteen. The nine reserved exponents already exclude all multiples of sixteen and 8 itself. Thus $W_8\ge W_a$, with equality precisely for sets avoiding every multiple of eight. A mode at the extra anchor has $W_8=32$, while a selected original vector has weight at least 32, with equality only for the all-ones vector. A mixed intersection therefore has both vectors all ones and all its roots off the subgroup of order sixteen.

Measure exponents relative to the extra anchor. The required product residue is zero. Each original anchor now has relative exponent $8w$ for some odd $w$. Multiplication by an odd unit permutes ordinary exponents, preserves product residue zero, and permutes the leaves of each reciprocal tree. Indeed, it commutes with doubling up to sign on the inverse pairs. The two all-ones signatures are invariant under this permutation. Both signs occur at the extra anchor. Counting both at the other anchor therefore gives a common upper bound for every mixed intersection. It suffices to count at relative anchors 0 and 8.

With the multiples of eight omitted, the tree at zero consists of eight four-leaf subtrees whose roots are $4,12,\ldots,60$. To cover four leaves exactly once, either occupy the root with one of its two orientations, or take an independent cut covering each child exactly once. At a leaf choose one of its two orientations. For every local cut record its selected size, its exponent sum modulo 128, and the leaves it covers at the other anchor. Discard any cut covering an opposite leaf twice. Combine four subtrees at a time, retaining disjoint opposite leaf masks. Join the halves with complementary masks, total size 17 and total residue zero. This counts **146** subsets. Each qualifying subset occurs exactly once since its occupied nodes and orientations recover the cuts. The verifier checks the recurrence against every five-subset and every product on a smaller order-32 board.

## The shared center

The union therefore contains at least $2,159,232,164-1,736,356-8\cdot146=2,157,494,640$ distinct subsets. Give each of the 74 primary modes $g=906,876$ disjoint sites at its anchor. Each original fiber has room for nine such allotments, and $74g+h-1\le9h$ leaves room for $h-1$ common roots among the unused serving sites.

Let $H$ vanish at those common roots and $L_T(Y)=\prod_{j\in T}(Y-u^j)$. All locators have the same constant $c$. Use $f_T(X)=H(X)(Y^{17}+c-L_T(Y))/Y$ with $Y=X^h$. Its degree is at most $16h-1$. At each assigned site use $H(x)(y^{17}+c-v)/y$, where $y=x^h$ and $v$ is the assigned locator value. Use $v=0$ elsewhere. The $17h$ ordinary root sites, the $h-1$ common sites and the $g$ assigned sites give at least $18h-1+g$ agreements for each member. Distinct locators yield distinct evaluation words. The construction and finite numerical bounds here use a written proof and an executable integer census. [Polynomial construction](rotated-locator-union.md#one-center-for-the-selected-sets)

## Ten serving fibers

Add both exponents 8 and 72 to the original eight. At the original anchors retain the preceding candidate vectors. At the two extra anchors consider all ones, all twos, and the vectors obtained by replacing one aligned two-leaf block of twos by ones. For each field rank signed modes first by population, breaking ties by vector, signed exponent and anchor in descending order. Take the best $\lfloor h/g\rfloor$ at each anchor and the best $K$ of their union. The pairs $(g,K)$ are $(1,935,832,39)$ and $(920,700,82)$ for the first and second primes. Both satisfy $Kg+h-1\le10h$.

The untrimmed incidence counts are 1,079,356,632 and 2,160,447,288. On the original eight anchors the pair sums are at most 301,560 and 1,130,126, respectively, by the regular-board count allowing the two extra exponents. At the two extra anchors the unrestricted two-anchor board in coordinates relative to 8 gives pair bounds 71,642 and 143,146. Its product residue is zero and its two anchors are antipodes.

### Mixed intersections after restricting the two extra palettes

Relative to either extra anchor $a$, the special roots outside the regular tree with step eight are
\[
E=\{16,32,48,80,96,112\}.
\]
The original anchors exclude all relative coordinates congruent to eight modulo sixteen, and the extra anchors exclude 0 and 64. Fix $Z=(T-a)\cap E$. For an original anchor $b$, the difference of the two leaf sums is
\[
\Delta=W_a(T)-W_b(T)=\sum_{j\in Z}(\gcd(j,128)-8).
\]
Four special roots contribute 8 apiece, and the two roots $\pm32$ contribute 24 apiece. The selected original weights are 32, 36 and 40, while extra-anchor weights are 32, 62 and 64. A weight-62 extra mode cannot overlap an original mode since this difference must be divisible by eight. For a weight-32 extra mode, only weight 32 with $Z$ empty is possible. These all-ones mixed pairs have size at most 146 for anchor 8 and 106 for anchor 72, using the cut count above at the respective relative product residues 0 and 64.

Suppose the extra vector is all twos. For an overlap, $\Delta$ is 24 or 32. At each extra anchor omit every all-twos incidence with $\Delta=32$ or with $\Delta=24$ and $|Z|=3$. To bound the discarded population, enumerate the subsets $Z$ of the six special roots, subtract their leaf-vector contribution from the target, and count ordinary sets of size $17-|Z|$ with the remaining signature and each required signed exponent. Counting both original signs of the all-twos vector gives at most **87,840** omissions at anchor 8 and **87,952** at anchor 72.

Every remaining all-twos mixed intersection has $\Delta=24$ and a single special root $z=32$ or $96$. Relative to the extra anchor, this root contributes one to every leaf. The sixteen remaining roots have the all-ones vector and avoid all multiples of eight. At an original anchor, the special root contributes one to one aligned block $J$ of eight leaves. The original weight must be 40, so its selected vector is one plus the indicator of some aligned eight-leaf block $D$. Thus the required vector for the remaining sixteen roots at the original anchor is
\[
{\boldsymbol 1}+{\boldsymbol 1}_D-{\boldsymbol 1}_J.
\]
Normalize the original anchor's relative exponent to 8 by multiplication by an odd unit. This transformation permutes the four aligned eight-leaf blocks because they are the descendant sets of the four nodes at the same tree depth. The relative product residue of the remaining roots is either 32 or 96 and multiplication by an odd unit preserves this pair of possibilities.

For each ordered choice $(D,J)$ and each of the two possible residues, the sixteen-root count is at most **85**. The verifier enumerates the same four-leaf cuts as above, recording the full vector of the leaves covered at the other anchor. It joins four subtrees against four by complementary vectors summing to the displayed target, complementary sizes totaling sixteen and complementary residues. A half with an entry above two, or entries equal to two in different blocks, cannot occur in such a target. The verifier packs the 32 coordinates in four-bit digits. At an odd leaf at the other anchor at most six of the permitted roots can contribute, so digit addition computes the coordinate sums exactly.

For a fixed pair of anchors, each of the two choices of $z$ fixes $J$ and the normalized residue, and there are four possible $D$. Ignoring both high exponent bits bounds these surviving all-twos intersections by $2\cdot4\cdot85=680$. Summing also the all-ones counts over the sixteen mixed pairs gives at most $8(146+680)+8(106+680)=12,896$ mixed repetitions. Subtract the omitted incidence bounds once, then the three kinds of pair repeats, to obtain the two union lower bounds
\[
\begin{split}
1,079,356,632-175,792-301,560-71,642-12,896&=1,078,794,742,\\
2,160,447,288-175,792-1,130,126-143,146-12,896&=2,158,985,328.
\end{split}
\]
The common-root construction above supplies $18h-1+g$ agreements for every retained word, giving the stated error ceilings.

Run both the small exhaustive control and all production counts with Python 3 and a C++20 compiler.

```sh
python3 scripts/probes/probe_staggered_locator_anchors.py
```
