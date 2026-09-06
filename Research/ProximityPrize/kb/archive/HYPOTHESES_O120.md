# O120 — The Hypothesis Program (2026-06-10)

Ten hypotheses on the open mathematics of issue #232, each with constraint
analysis, novelty audit (anti-larp check against the in-tree ledger and the
literature pins), and a prove-out plan. Five grounded in known mathematics
(R1–R5); five into unknown territory (X1–X5). Probes and Lean prove-outs run
as workflow agents; results land in O120+ entries.

**Literature base** (DISPROOF_LOG pins, read in full): BCIKS 2025/2055,
Crites–Stewart 2025/2046, Diamond–Gruen 2025/2010, Chai–Fan 2026/861 + 858,
Goyal–Guruswami 2025/2054, Lam–Leung J. Algebra 224 (2000), Mann 1965,
Conway–Jones Acta Arith. 30 (1976) Thm 5 (Σ_{p|Q}(p−2) ≤ w−2),
Christie–Dykema–Klep, Malikiosis 2005.05800, Kiss–Łaba–Marshall–Somlai
2507.11672 (non-downward-closed prescriptions fail).

**In-tree state consumed** (both lanes): O94–O116 + `int_windowed_law`
(ℤ-windowed law at EVERY modulus), `DeBruijnLamLeungSmallWeights` (w ≤ 3),
`SliceLevelTwoCount`, `TwoGenPackingCapacity`, agreement-spectrum M2 entries.

## The semigroup collapse (framing R5/X5)

⟨p₁,…,p_k⟩ has finitely many gaps; with {2,3} ⊆ {p_i} there are none ≥ 2.
Weight 1 is impossible (in-tree) ⟹ **Lam–Leung is TRIVIAL at every 6 ∣ n.**
Via O116, Lam–Leung at squarefree n ⟺ no minimal sum has gap weight (finite
list per n). The CJ inequality Σ_{p∣Q}(p−2) ≤ w−2 excludes each gap weight by
arithmetic. So: Lam–Leung (squarefree) ⟸ O116 + CJ + semigroup arithmetic —
ONE analytic ingredient remains (CJ 1976).

## R1 — Interval-window μ_p-closure at every modulus
Constraints: μ_d-coset indicators are +n/p-shift-invariant iff p ∣ d; the
parallel int_windowed_law classifies interval windows over ℤ at every n.
Anti-larp: not among that file's consumers; O97 covers two-prime only; days-old
mathematics, no literature. Novelty: completes the SET interval law at every n
with threshold t_p(n) = largest p-free divisor.
**R1**: t ≥ largest p-free divisor of n, window [1,t] ⟹ T ⊆ μ_n is μ_p-closed.
Prove-out: Lean (int_windowed_law + shift-invariance transport). Expect THEOREM.

## R2 — Divisor-representative sparse window at pqr
Constraints: O97's two-prime sparse window = the p-free divisors {q^c}; at pqr
those are {1,q,r,qr} (4 exponents vs interval's qr). Packet route dead (O105);
KLMS does not apply (window is downward-closed in the divisor lattice).
Anti-larp: not in tree (O112 = counts only; O114 = dense); not in literature
(window law original here). Novelty: the candidate sharp sparse window at 3
primes. **R2**: at n = pqr, window {1,q,r,qr} ⟹ μ_p-closure.
Prove-out: MITM-exhaustive probe at n = 30 + sharpness controls; Lean only if
the probe survives.

## R3 — Exact pairwise Bonferroni for the Conjecture-D union
Constraints: S_Z ∩ S_Z' = S_{Z∪Z'} with EXACT count q^(k−2|Z∪Z'|) (O96) — all
intersection terms known. Anti-larp: both lanes flag the channel open; no
lower bound exists in-tree; mathlib Bonferroni support unknown (agent checks).
Novelty: first two-sided Conjecture-D count; slack quantified ≤ N²/q.
**R3**: |⋃S_Z| ≥ C(N,z₀)q^(k−2z₀) − Σ_{i<z₀}C(N,z₀)C(z₀,i)C(N−z₀,z₀−i)
q^(k−2(2z₀−i))/2; first-order tight for q > N².
Prove-out: probe (exact unions vs truncations, small q); Lean Bonferroni-2.

## R4 — Shadow-span composition at three primes
Constraints: O112's components are ℕ-valued; summing the fiber-count function
recovers |T|. Anti-larp: all in-tree cardinality laws consume j=1 vanishing;
this consumes ONLY Σ y^q = 0. Novelty: span constraints from single
gcd-exponents; triple-window intersection.
**R4**: at pqr, Σ_T y^q = 0 ⟹ |T| ∈ ℕp + ℕr (and intersections over windows).
Prove-out: Lean today (O112 + sum_mod_fiber). Expect THEOREM.

## R5 — No weight-4 minimal sums at gcd(n,6)=1 (the gap ladder)
Constraints: in-tree ladder stops at w=3; first open gaps for 3∤n odd moduli
include w=4; CJ at w=4 forces support order ∣ 6 ⟹ trivial at gcd(n,6)=1.
Anti-larp: w=4 not in the small-weights file; CDK classification unformalized
anywhere. Novelty: first CJ-inequality instance machine-checked.
**R5**: squarefree n, gcd(n,6)=1 ⟹ no vanishing ℕ-weight of total 4.
Prove-out: probe (exhaustive w=4 at n=35); Lean case analysis on 1+a+b+c=0
(pairings need 2∣n; quadruple case needs the CJ-style algebra — agent assesses).

## X1 — Squarefree unit-window ℤ-structure theorem
Constraints: the unit window is NOT downward-closed (KLMS territory); their
counterexample needs high prime powers (2⁹3⁶); squarefree removes the ladder.
O105's witness vanishes at all units of 30 — ℤ (not ℕ) is the right ring.
Anti-larp: int_windowed_law = intervals only; KLMS prove failure for general
prescriptions; the squarefree unit-window case is uncharted. Novelty: first
structure theorem on a non-interval window; delimits KLMS failure exactly.
**X1**: at SQUAREFREE n: w : ℕ→ℤ vanishes at every unit exponent ⟺ w ∈ ℤ-span
of proper-level pullbacks {f∘(·%(n/p)) : p ∣ n}. At non-squarefree n: false.
Prove-out: probe (Smith-normal-form rank+saturation at 30,42,70,105 vs
controls 12,36,60); Lean via O109-peel if ranks match.

## X2 — The negative-mass invariant of minimal sums
Constraints: O115 ℤ-components always; O105 negativity unavoidable at ≥3
primes; minimality should bound it. Anti-larp: Steinberger studied large
coefficients, not decomposition negativity; invariant only definable since the
ℤ-classification (days old). Novelty: new invariant; new conditional route to
Lam–Leung independent of CJ. **X2**: minimal sums at n=30 have
negmass ≤ 2 (uniformly small in the prime signature).
Prove-out: probe (enumerate ALL minimal sums at 30 from the census; ILP min
negative mass; report spectrum).

## X3 — The exact alternating union formula
Constraints: ALL j-fold intersections known exactly — inclusion–exclusion has
no unknown terms; resummation by union-size with Möbius-type integer
coefficients. Anti-larp: exactness-of-all-terms unexploited in either lane;
generic union literature assumes unknown intersections. Novelty: an EXACT
Conjecture-D level-1 count. **X3**: |⋃S_Z| = Σ_m c(N,z₀,m) q^(k−2m) + trunc,
with explicit alternating integer c; ≥ (1−N²/q)·first-term for q ≥ 2N².
Prove-out: probe (brute-force exact unions small (q,N,k,z₀), verify the
coefficient law and the 1−N²/q bound).

## X4 — Smooth-domain triple-moment deviation (toward δ*)
Constraints: pair moments are MDS-exact = domain-free (why arguments stall at
Johnson); third moments are the first place the domain can enter; joint zero
patterns on μ_n are divisor-coset-constrained. Anti-larp: the parallel lane
NAMES third moments as the open direction with no result; Chai–Fan is a
group-action route, not moments; no pin computes smooth triple moments.
Novelty: first domain-specific moment computation in the prize band; even a
null result is a real no-go. **X4**: on μ_n ⊂ F_q^×, the centered triple
agreement moment deviates from the random-domain model by
Θ(divisor-coincidence count), with onset at k > largest proper divisor of n.
Prove-out: probe (exact enumeration q ∈ {31,61}, n ∣ q−1 smooth, k small;
compare vs sampled random domains; report deviation and k-threshold).

## X5 — The Conway–Jones route: conditional collapse of Lam–Leung
Constraints: O116 + semigroup collapse leave CJ's inequality as the only
analytic input; Mann alone kills gaps < p₁. Anti-larp: no CJ/Mann/Lam–Leung in
any proof assistant (O91 search); the gap-exclusion REDUCTION is not in the
papers either (they prove the span directly); the 6∣n triviality appears
nowhere. Novelty: a new unconditional theorem (a) and the hypothesis-clean
bridge (b) making positivity = one classical inequality.
**X5**: (a) Lam–Leung holds at every n with 6 ∣ n [unconditional];
(b) the CJ inequality (as hypothesis) ⟹ Lam–Leung at every squarefree n.
Prove-out: Lean today — (a) O116 + no_weight_one + w≥2 ⟹ w ∈ ℕ2+ℕ3;
(b) the semigroup case analysis.
