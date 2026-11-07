# The prize is DOUBLY-barriered: every "changed regime" relaxation is provably load-bearing (#407)

**Status: decisive regime map.** A 6-agent survey of each "change the problem" regime where δ* is
PROVEN, looking for an open path back toward the plain-RS prize that avoids BCHKS Conjecture 1.12.
Result (as corrected 2026-10-28, audit T121): the survey found two independent obstruction
mechanisms, but only the first is established for the prize's finite fields; the second (BCDZ25
Thm 1.11) is proven only over algebraically closed fields under parameter guards, so the folding
relaxation is not shown provably necessary over the prime field. (The original 2026-06-13 text
claimed "two independent proven barriers" with every relaxation "provably NECESSARY"; that
overstated the second wall.) 2026-06-13.

## The two independent walls
The plain-RS-over-μ_n prize sits at the intersection of two unrelated obstructions (the second only
heuristic over finite fields, see below):
1. **Character-sum / worst-case-list route → BCHKS Conjecture 1.12** (= GK07/BGK sum-product wall).
   [`deltastar-floor-IS-BCHKS-conjecture-1-12`]
2. **Subspace-design / higher-order-MDS route → BCDZ25 Thm 1.11 Schubert-calculus barrier — but
   only under its own guards.** Thm 1.11 is stated over an **algebraically closed** field, for
   `1 ≤ d ≤ s`, and is triggered when `n ≤ d(k−d)/(s−d+1)`. The source itself gives a finite-field
   (`F_3`) exception and lists the finite-field extension as open. At `s = d = 1` with faithful
   scalar code dimension `k ≤ n`, the trigger would need `n ≤ k−1`, which is impossible. So this
   source does **not** establish a finite-field unfoldability theorem for the prime-field prize; it
   is a heuristic signal about the subspace-design route, not a proven wall. (GGH26's remark that
   "this property necessarily requires the code to be folded" should be read with the same
   guards.) Separately, the in-tree machine-checked negation-symmetry refutation
   (`MuTwoPowDerandRefutation.lean`: even μ_n SATURATES generalized-Singleton since `−1∈μ_n`) is a
   genuine finite-field obstruction to the higher-order-MDS genericity step for even-order μ_n.

Correction (2026-10-28 audit, T121): an earlier version presented Thm 1.11 as a proven necessary
folding barrier for the prime-field prize, dropping the algebraic-closure and parameter guards.

The two routes are independent in mechanism (one is additive-NT subset-sum spreading, the other is
Grassmannian codimension); only wall 1's reduction and the negation refutation are established for
the prize's finite fields.

## The regime map (which relaxation is load-bearing, and why)
| Regime | δ* proven? | un-relax → prize | blocker |
|---|---|---|---|
| **Folded RS** (GG25/BCDZ25) | YES, BGK-free | drive folding `s→1` | re-hits BCHKS-1.12; Schubert barrier only over alg. closed fields (finite-field version open) |
| **Multiplicity codes** (GG25) | YES, BGK-free | drive mult `s→1` | dies EARLIER at design-dim collapse `τ(r)=1 ∀r≥2` (before BCHKS) |
| **Random RS** (BGM/GZ, large field) | YES, BGK-free | derandomize → explicit μ_n | negation symmetry refutes μ_n genericity (higher-order-MDS) |
| **Large-field RS** | counting only | reduce `q→n·2¹²⁸` | doesn't fix explicit-μ_n genericity; re-hits BCHKS |
| **Subspace-design** (JLR26/BCDZ25) | YES, BGK-free | transfer to RS | subspace-design route appears to need folding; proven (Thm 1.11) only over alg. closed fields |
| **CLOSEST: explicit folded RS** (BCDZ25 Thm 1.4) | YES, BGK-free, `q=Θ(sn)`, for fixed `b`-local properties | un-fold | no finite-field un-foldability theorem; Thm 1.11 is alg.-closed-field only |

**The closest proven, BGK-free, prize-adjacent result:** BCDZ25 (Brakensiek–Chen–Dhar–Zhang,
arXiv:2510.13777, Oct 2025) Thm 1.4 — a **positive** construction: explicit `s`-folded RS /
multiplicity codes over `q=Θ(sn)` (field size EASIER than the prize 2¹²⁸) inherit local properties
of random linear codes with a **fixed `b`-local profile**, at rate `R−ε` (rate loss `ε`), provided
the folding satisfies `s ≥ b(R/ε+1)`, routing through subspace-designs + GK16 explicit expanders +
LMS25/GM-MDS — **never touching BCHKS-1.12/BGK**. To claim a specific protocol property (e.g. a
proximity gap toward capacity `1−R−ε`) transfers, that property must be genuinely encoded as such a
fixed-`b` local property and the rate loss and folding bound accounted for; this note does not do
that encoding. Thm 1.11 shows the subspace-design property needs folding **only over algebraically
closed fields, for `1 ≤ d ≤ s` and `n ≤ d(k−d)/(s−d+1)`**; the finite-field transfer is open (the
source records an `F_3` exception), and at `s = d = 1` the trigger is never met. And failure of the
subspace-design route does not exclude every plain-RS argument.

## The one un-refuted (but unresolved) opening: ODD-ORDER smooth domains
The even-order floor refutation is SPECIFICALLY the negation symmetry (`−1=ω^{n/2}∈μ_n`, forced for
`n=2^a`). ODD-order multiplicative subgroups (`n=3^a`, radix-3 NTT, `−1∉μ_n`) REMOVE it. Numerics
(`probe_oddorder_*.py`): even μ_n sits at the WORSE end of the random worst-case-list range; odd μ_n is
random-like — but at the small radii tested the random spread is too tight (lists 2–3) to cleanly show
odd-order is MORE generic (`< random`). So odd-order is the one route that escapes BOTH the negation
refutation and (via the GM-MDS/higher-order-MDS route, which Route 4 showed is BGK-free) the
character-sum wall — reducing the prize to "is odd-order μ_n higher-order MDS?", a DIFFERENT open
problem than BGK. CAVEAT: odd-order is a changed smoothness (radix-3, not the prize's 2-power NTT), and
the genericity is unproven. Worth a dedicated GM-MDS-minor (not list-size) test.

## Net (honest)
No open path from any proven regime to the PLAIN-RS prize was found in this survey. The randomness
relaxation is shown load-bearing for even-order μ_n by the in-tree negation refutation; the
multiplicity relaxation by the design-dimension collapse; the folding relaxation only **heuristically**
for finite fields — BCDZ25 Thm 1.11 proves it over algebraically closed fields under its parameter
guards, and the finite-field version is open. So the second wall is not a proven finite-field
theorem. The closest proven result is explicit FOLDED RS (BCDZ25 Thm 1.4, for fixed `b`-local
properties with rate loss), gap = the folding, whose necessity over the prize's prime field is
unproven. If the internal team "solved MCA," they either (a) resolved
BCHKS-1.12/BGK, (b) used folding/multiplicity (changed the problem, where it IS proven, BCDZ25/GG25),
or (c) found a construction outside this map. The single un-refuted lead is odd-order smooth RS via
higher-order MDS.

New paper: **BCDZ25, arXiv:2510.13777** (Oct 2025) — "From Random to Explicit via Subspace Designs",
Thm 1.4 (explicit folded-RS inherits random-LC local properties with a fixed `b`-local profile, at
rate `R−ε`, for folding `s ≥ b(R/ε+1)`) + Thm 1.11 (folding necessary for the subspace-design
property over algebraically closed fields, `1 ≤ d ≤ s`, `n ≤ d(k−d)/(s−d+1)`; finite-field
extension open).
