# A tangent-head ladder of safe line-MCA radii at length $2^{30}$

Let $n=2^{30}$. Over every finite field with at least $2^{128+\beta}$ elements
and characteristic at least $2^{47}$, and on every injective evaluation domain
of length $n$, the closed ball through the listed number of errors passes the
128-bit line-MCA test at every positive interleaving width. Every prime field
of that size satisfies the characteristic condition.

| $\beta$ | Rate 1/2 | Rate 1/4 | Rate 1/8 | Rate 1/16 |
|---:|---:|---:|---:|---:|
| 32 | 307,759,023 | 527,124,673 | 671,088,385 | 738,197,249 |
| 34 | 309,134,539 | 529,408,947 | 680,837,212 | 786,379,766 |
| 36 | 310,191,320 | 530,904,312 | 687,671,509 | 798,744,899 |
| 38 | 311,064,833 | 532,151,237 | 688,993,288 | 800,141,773 |
| 40 | 311,753,565 | 533,136,284 | 690,063,301 | 801,231,080 |
| 44 | 312,769,668 | 534,507,592 | 691,551,680 | 802,743,393 |
| 48 | 313,401,975 | 535,375,373 | 692,503,565 | 803,694,497 |
| 52 | 313,793,593 | 535,924,515 | 693,095,909 | 804,286,356 |
| 56 | 314,048,997 | 536,193,245 | 693,247,147 | 804,286,356 |
| Johnson count | 314,491,699 | 536,870,913 | 694,116,762 | 805,306,370 |

For comparison, the kernel-checked
[weighted Johnson ladder](../../../ArkLib/Research/ProximityGap/Frontier/JohnsonBudgetLadder.lean)
gives the following counts, with no condition on the characteristic.

| $\beta$ | Rate 1/2 | Rate 1/4 | Rate 1/8 | Rate 1/16 |
|---:|---:|---:|---:|---:|
| 36 | 264,305,680 | 441,001,106 | 590,558,004 | 709,234,733 |
| 40 | 286,064,053 | 497,724,075 | 654,203,879 | 768,608,494 |
| 44 | 302,702,397 | 521,162,467 | 678,319,226 | 791,028,984 |
| 48 | 309,697,726 | 530,597,867 | 687,862,086 | 799,681,249 |
| 56 | 313,729,682 | 535,880,485 | 693,133,819 | 804,424,509 |

At $\beta=36$ the new counts are larger by 45,885,640, 89,903,206, 97,113,505
and 89,510,166 errors. At $\beta=48$ they are larger by 3,704,249, 4,777,506,
4,641,479 and 4,013,248. At $\beta=56$ the first three rates gain 319,315,
312,760 and 113,328 errors, and the sixteenth-rate entry is below the weighted
Johnson count; it repeats the $\beta=52$ entry, which remains valid for every
larger budget.

**Status.** Written lower bounds with an
[exact-arithmetic certificate](../../../scripts/probes/probe_tangent_head_ladder.py)
for every entry. They rest on Theorem D′ of the
[section-incidence note](section-incidence-hodge-index.md#a-second-route-below-the-johnson-radius-tangent-heads),
whose counting half is kernel-checked in
[TangentHeadCount.lean](../../../ArkLib/Research/ProximityGap/Frontier/TangentHeadCount.lean)
and whose geometric half is a written argument. For the twelve entries at
$\beta=32$, 34 and 36, Lean checks both interpolant counts, the Johnson-type
conditions, the head tests and every degree allocation with at most the
packing number of rich heads, in
[TangentHeadLadder.lean](../../../ArkLib/Research/ProximityGap/Frontier/TangentHeadLadder.lean).
The cap enters there as the definition of a price, and the packing bound on
rich heads as a hypothesis. Lean does not check the entries at larger
exponents. The weighted Johnson ladder is a Lean theorem and is
the stronger statement for fields of small characteristic and from
$\beta=64$ on.

## Budgets between the two named primes

The two named primes have integer budgets $n$ and $2n$. For a field whose
budget is at least $jn/8$, with the same condition on the characteristic, the
same argument gives the following safe error counts on every injective domain
of length $n$.

| Budget | Rate 1/2 | Rate 1/4 | Rate 1/8 |
|---:|---:|---:|---:|
| $9n/8$ | 293,018,651 | 469,749,153 | 601,620,356 |
| $10n/8$ | 302,936,496 | 488,619,120 | 625,533,909 |
| $11n/8$ | 305,038,412 | 504,801,583 | |
| $12n/8$ | 305,705,113 | 518,960,616 | |
| $13n/8$ | 305,940,243 | 522,404,939 | |
| $14n/8$ | 306,465,090 | 523,490,200 | |
| $15n/8$ | 306,465,090 | 524,083,702 | |
| $2n$ | 306,780,000 | 524,700,000 | 671,088,385 |

At rate $1/8$ the exact first failure 626,349,397 is already known for budgets
from 1,409,286,144 to 1,879,048,193, so only the two smaller budgets are
listed. At rate $1/2$ the entry for $15n/8$ repeats the one for $14n/8$. The
previous bounds for budgets strictly between $n$ and $2n$ were the first-prime
floors, 268,435,456 safe errors at rate $1/2$ and 447,392,427 at rate $1/4$.

At rate $1/4$ and budgets up to about $11n/8$ the binding allocation is three
collinear rich heads. Their cores cover at least $3C-3d$ sites, a covered
site gives one label and an uncovered one three, so they carry at most
$3n-6C+6d$ labels. This is at most $B$ exactly when
$e\le B/6+n/4-254$, which is 469,761,794 at $9n/8$, within the search tolerance of the
entry, and tends to the known
floor $5n/12$ as $B$ decreases to $n$. A matching failure needs three
collinear heads whose pairwise coincidence sets all have $d$ sites.

## Length $2^{40}$

The caps for nonlinear factors are numbers that do not grow with the length,
while the labels on affine heads do. At a longer length the same budget
relative to $n$ therefore reaches closer to the Johnson count. For
$n=2^{40}$, fields of characteristic at least $2^{57}$ and integer budget at
least the listed multiple of $n$, the closed ball through the listed number of
errors is safe on every injective domain.

| Budget | Rate 1/2 | Rate 1/4 | Rate 1/8 | Rate 1/16 |
|---:|---:|---:|---:|---:|
| $2n$ | 319,230,068,958 | 545,382,552,916 | 687,188,686,354 | |
| $64n$ | 320,634,784,370 | 547,825,429,161 | 707,216,801,511 | 819,792,658,433 |
| as a fraction of $n$, $2n$ | 0.29034 | 0.49602 | 0.62499 | |
| as a fraction of $n$, $64n$ | 0.29162 | 0.49824 | 0.64321 | 0.74560 |
| Johnson fraction | 0.29289 | 0.50000 | 0.64645 | 0.75000 |

At length $2^{30}$ and budget $2n$ the first two fractions are 0.28571 and
0.48866. The sixteenth-rate entry at budget $2n$ is omitted because the exact
first failure $\lfloor 2n/3\rfloor$ is already known there. The eighth-rate
entry at $2n$ ends at the same four-head boundary $5n/8$ as at length
$2^{30}$. The argument has absolute constants, such as the cutoff
$1+\lfloor e/256\rfloor$ for rich heads, and it does not certify these windows
at length $2^{20}$.

## Argument

The allocation argument is the one of the
[tangent-head windows](tangent-head-windows.md) with the budget $2n$ replaced
by $2^\beta$. A field with at least $2^{128+\beta}$ elements has integer
budget at least $2^\beta$. Two mixed Hasse interpolants contain every selected
section. A factor carrying more labels than the cutoff divides both. A
nonlinear factor of value degree $b$ is capped by Theorem D′, with
$W=rt-1-(\ell-b)d$ and $m=a-j$ as before. A rich affine head carries at most
$e+1$ labels.

One input is added. Rich heads have joint cores of size at least $C=t-255$,
and two distinct heads share at most $d$ core sites. Counting pairs of cores
through each site gives at most
$$
\Bigl\lfloor\frac{n(C-d)}{C^2-nd}\Bigr\rfloor
$$
rich heads whenever $C^2>nd$. Allocations with more rich heads do not occur.
For $j$ collinear rich heads the union of the cores has at least
$jC-\binom j2d$ sites, as well as the second-moment bound used in the windows;
the certificate takes the larger of the two.
Without this bound the trivial count $j(e+1)$ for $j$ up to the value degree
would exceed the smaller budgets.

The certificate uses the proportional-price test of the Lean window files.
For $j$ rich heads and total value degree $\ell$, it checks that the heads
fit the budget and that every value degree $b$ costs at most the share
$b/(\ell-j)$ of what they leave. Each row lists its two shapes $(r,v,s)$ in
the certificate.

## What limits the entries

* At $\beta=32$ the eighth-rate and sixteenth-rate entries end where the
  four-head determinant test $4C>n+4d$ fails, at 671,088,385 and 738,197,249
  errors. One step later the head count used here allows more rich heads than
  the budget can pay for.
* The other entries are limited by the cap for the largest nonlinear factor,
  which grows like $b^2mW/(t^2-nd)$ while the value degree and order of the
  interpolant grow as the Johnson count is approached. The search over shapes
  was a heuristic bisection with a tolerance of 20,000 errors. Nearby shapes
  may certify slightly more.
* The search was limited to interpolants of order and value degree at most
  400. The entries at $\beta=52$ and 56 reach that limit, and for
  $\beta\ge64$ the weighted Johnson ladder is stronger.

## Reproduce

```bash
python3 -O scripts/probes/probe_tangent_head_ladder.py
```

The entries at $\beta=52$ and 56 are checked with `--deep`, which takes about
40 seconds.
