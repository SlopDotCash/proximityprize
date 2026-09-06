# δ\* (#444) — Untried, Non-Wall Angles Census (2026-06-17)

**Prize** (proximityprize.org / 2026/680): determine δ\*_C for Reed–Solomon on a *smooth*
domain, ρ ∈ {1/2, 1/4, 1/8, 1/16}, ε\* = 2⁻¹²⁸, |F| sufficiently large. The MCA face
requires ε_mca ≤ ε\* ≡ list-decoding |Λ(C^{=m}, δ\*)| ≤ ε\*·|F|.

**State.** Char-0 is CLOSED in closed form (Bessel CGF g(t) = ½·log I₀(2t); cumulants
κ_{2r} = c_r·n linear in all r; M_char0 ≤ √(2n·log m)). The value δ\* = 1 − ρ − Θ(1/log n)
survives all negative attacks (no lower bound, no undecidability — the floor is reachable).

**The wall (what a qualifying angle must NOT reduce to).** The prize currently funnels to ONE
object: bound the CHAR-p sup-norm M(n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)| ≤ C·√(n·log m) at depth
r ≈ 89, β = 4 — the BGK / Paley short-character-sum at the Burgess barrier. Every one of the
120+ catalogued routes reduces to this, or equivalently to **BCHKS Conjecture 1.12** (the
cyclotomic additive-energy / minimal-vanishing-weight conjecture), which is the wall in
non-character-sum clothing.

---

## HONEST COUNT

**Genuinely qualifying angles (provably-novel AND verified feasibility > 7/10 AND
non-wall-closing): `0`.**

We did **not** reach 100. We did not reach 1. The fully-specified candidate pool — spanning the
four "off-the-worst-case-M" lenses (L1 choose-F freedom, L2 proof-by-construction, L3
formal/decidability-transfer, L4 specific-FFT-prime) — deduped to **31 distinct angles**
(A001–A031). On adversarial verification against the actual in-tree files, **every** fully
specified candidate is one of:

- **(a) partial-overlap** with proven in-tree content that *characterizes/excludes* but does
  **not close** the prize (e.g. A001, A003);
- **(b) reduces to BCHKS Conj 1.12 / the char-p sup-norm wall** on inspection — frequently per
  the in-tree file's OWN honest verdict (e.g. A010, A011, A012, A013, A021, A022, A031);
- **(c) reduces to a named-open obligation** that is itself the open core (e.g. A005→`OPDescentStep`,
  A006→`OrbitDegreeBelowFold`, A015→interior orbit count, A004→deep-r).

The strongest *genuinely* non-wall provable artifacts that already exist (A001 large-field
characterization; A003 Spur vacuity) are **real theorems** (0 sorry) but are partial-overlap and
**do not reach the prize floor**. This is consistent with the recon corpus: all 120+ tried routes
reduce to the wall or are refuted; the field-choice / proof-by-construction / decidability lenses,
while genuinely off the *worst-case M* framing, all funnel the *per-good-prime FLOOR* back into
BCHKS Conj 1.12.

**Feasibility is therefore reported on a max-5 scale (honest), not padded to uniform 7s.** The
self-reported 8s do not survive verification.

### In-tree ground truth checked (file-by-file)

| Claim | File | Verified |
|---|---|---|
| Large-field combinatorial sufficiency is real, axiom-clean | `ArkLib/Data/CodingTheory/ProximityGap/RSDeltaStarLargeField.lean` | 0 sorry ✓ |
| Deployed census-weld budget is INFEASIBLE at deep central band | `Research/ProximityPrize/Frontier/CensusBudgetInfeasibleDeepBand.lean` | `not_censusDomination_of_budget_lt_centralBinom`; needs K ≥ centralBinom(m−1) = 2^Θ(m) ✓ |
| Field-size lever names census/list bound `K` as the open core | `ArkLib/Data/CodingTheory/ProximityGap/FieldSizeThresholdReduction.lean` | `censusDomination_pin_largeField`; "open core is the census/list bound K" ✓ |
| Spur two-square cut is VACUOUS on smooth primes | `Research/ProximityPrize/Frontier/_SpurEvenValuationTwoSquares.lean` | 0 sorry; vacuous (shows existing p≡3 mod 4 cut empty, not a positive certificate) ✓ |
| Ideal-lattice/Minkowski floor is dimension-vacuous; sharpening IS BCHKS 1.12 | `Research/ProximityPrize/Frontier/_IdealLatticeMinkowskiCorrected.lean` | own verdict: "reduces R1 to itself"; λ₁ collapses to ~1 at d=2²⁹ ✓ |
| Energy/Spur prize-regime transfer's deep-r content = the wall | `Research/ProximityPrize/Frontier/_wfS6_prize_regime_transfer.lean` | self-states "standing open core (the cyclotomic-norm / BGK wall)" ✓ |
| OP single-orbit persistence reduces to named-open `OPDescentStep` | `Research/ProximityPrize/Frontier/_OffBGK_OPSingleOrbitPersistence.lean` | 1 sorry; "the ONE precise descent obligation that remains open" ✓ |
| deg(#bad_r) < r is MACHINE-REFUTED for raw count; open = `OrbitDegreeBelowFold` | `Research/ProximityPrize/Frontier/_OffBGK_DegBadRGrowingSlack.lean` | 1 sorry; "deg(#bad_r) = r EXACTLY at r=3,4" ✓ |
| FRI rbr residual = interior polynomial orbit-count, poly(n) only in Johnson range | `ArkLib/Data/CodingTheory/ProximityGap/BridgeLoop44.lean` | interior case is the open core ✓ |

---

## Ranked candidates, grouped by lens

Ranking is by **honest feasibility (max 5)**. None clears the > 7 bar. `noveltyVerdict` ∈
{`partial-overlap`, `already-tried`}; there is no `provably-novel-and-clean` entry, which is the
whole point of the honest count.

### Lens L1 — exploit freedom to CHOOSE F

| ID | Feas | Novelty | Angle | Why-not-wall (and where it nonetheless funnels) |
|---|---|---|---|---|
| **A002** | 5 | partial-overlap | R4 symmetric-function coset-rigidity at a generic-Galois prime (q-independent, non-W4): choose p where the symmetric-function value-set system has maximally-generic Galois, making char-p count = char-0 count by Lang–Weil good-prime transfer. | Object is a coset count of a symmetric-function value-set (q-independent), not \|η_b\|; confirmed non-W4 by the workbench. **Funnel:** the per-good-prime certificate is the open part. |
| **A007** | 5 | partial-overlap | Designer-chosen field with a CERTIFIED (not existence) good prime per dyadic level: exhibit a specific prime per level, certify goodness by a finite `decide`-checked divisibility on bounded-norm collision resultants. | Object is resultant divisibility (finite, non-archimedean), not the char-p sup-norm. **Funnel:** the goodness certificate at d=2²⁸ reduces to BCHKS 1.12. |
| **A008** | 5 | partial-overlap | Probabilistic method over qualifying primes: use ONLY the proven unconditional bad-prime count upper bound (`card_biUnion_bigPrimeFactors_le`) against the crude unconditional window prime count at β≈5.27 to show a random qualifying prime is good w.h.p. — avoiding the Thorner–Zaman supply LOWER bound. | Bad-prime count is a divisibility count of bounded-norm integers, not a char-sum sup. **Funnel:** needs the supply lower bound to dominate, which it can't unconditionally → still the analytic wall. |
| **A017** | 4 | partial-overlap | Pseudocyclic-scheme defect elimination via designer-chosen semi-primitive prime (∃ j: pʲ ≡ −1 mod n) so Cay(F_p, μ_n) is exactly pseudocyclic, forcing \|η_b\| = √n from intersection numbers (a scheme identity, not a bound). | For an exactly pseudocyclic scheme \|η_b\| = √v is a scheme theorem. **Funnel:** semi-primitivity pʲ≡−1 mod 2^μ likely EXCLUDES prize moduli (v₂ fights semi-primitivity; refuted v₂-gated 2-adic law). |
| **A009** | 4 | partial-overlap | Density-0 converse on the bad-prime set over the designer family (natural density 0 in {p ≡ 1 mod 2³⁰} via per-resultant finiteness + Borel–Cantelli). | Bounds size/density of the bad-prime set, not \|η_b\|. **Funnel:** picking a prime outside the density-0 set is the per-good-prime certificate = BCHKS 1.12. |
| **A011** | 4 | partial-overlap | Probabilistic method over the Solinas family: bad primes = prime divisors of {N(α): α box-short}, a finite explicitly-bounded set; exhibit a Solinas prime above 2¹²⁹ outside it. | Bad set is a finite factorization object, not a char sum. **Funnel:** the per-good-prime FLOOR transfer reduces to BCHKS 1.12 per the in-tree Minkowski verdict. |
| **A014** | 3 | partial-overlap | Information-theoretic converse: at a good prime the e₁-image equals char-0 N₀ exactly, so ε_mca = N₀/p exactly; pins δ\* from both sides = 1 − ρ − Θ(1/log n). | Uses the exact char-0 count at a good prime; non-wall. **Funnel:** entirely contingent on the good-prime certificate (A007/A011) → BCHKS 1.12. |
| **A016** | 3 | partial-overlap | β = log_n(q) decreasing in n: in the q ~ n·2¹²⁸ family β = (log₂n + 128)/log₂n crosses the Burgess threshold near n ~ 2⁴³, so di Benedetto's n^0.989 applies for the bulk; certify the small-n tail. | For large n the bound is an existing theorem (non-wall in the bulk). **DOES NOT REACH FLOOR:** deployed instance is n = 2³⁰ and n^0.989 is a half-power too weak. |
| A018 | 3 | already-tried | Conj 7.1 sparse-dominance via designer rate-choice (ρ in a free SET): pick a rate making the 3-position-sparse witness class dominate the dense bad-set by a rate-monotone margin (proven K ≤ 10 orbit count at ρ=1/4). | Object is an orbit count (`ActionOrbitFRI`, non-char-sum). **Funnel:** `LaneB_Q2_SparsityExclusive` proves the DENSE case has no compression → thrown back on BGK. |
| A021 | 2 | already-tried | Goldilocks/Solinas factorization of p−1 to factor η_b through a small 2-power quotient, reducing the residual char sum to the closed char-0 2-power object via I031 dilation-orbit reduction. | **DISQUALIFIES:** the sup over orbit reps is still a sup of incomplete character sums (the dilation route residual C is unproven = the wall constant). |

### Lens L2 — proof-by-construction

| ID | Feas | Novelty | Angle | Why-not-wall (and where it nonetheless funnels) |
|---|---|---|---|---|
| **A026** | 4 | partial-overlap | Tight (no-√-loss) LD⇒MCA in the n≪\|F\| regime via dimension counting: bound MCA error by L²·codim/\|F\| through the syndrome-space dimension Θ(n), where the ABF26 Thm 5.4 full-domain counterexample provably cannot block. | Object is a code-dimension/field-gap count, not a char sum. **Funnel:** no positive technique exists in the literature for the tight direction (three groups worked this boundary Nov 2025). |
| **A001** | 4 | partial-overlap | Census-vs-smoothness compatibility DECISION: couple the proven `rsCode_mcaDeltaStar_ge_of_large_field` to the smoothness constraint n\|(\|F\|−1) and the "sufficiently large F" clause to extract a decidable per-(ρ,ε\*,n) verdict of which instances reach capacity combinatorially. | Uses only C(n,k+1) (pure binomial) + Dirichlet existence; M never appears — genuinely non-wall. **PARTIAL-OVERLAP:** deployed prize needs \|F\| ~ 2^(10⁹) ≫ 2¹⁵⁸; `CensusBudgetInfeasibleDeepBand` already proves infeasibility at the deep band. Characterizes/excludes, does not close. |
| **A015** | 4 | partial-overlap | Non-CA FRI soundness (Chai–Fan 2026/858 Rem 12): bound per-round soundness by a list-recovery count via multilinear Schwartz–Zippel fold injectivity, without a proximity-gap CA step; read off (c₁,c₂,c₃) from the union bound. | Bounds protocol soundness via fold-consistent codeword counts, not max\|η_b\|. **Funnel:** 858 asserts no such non-CA proof is known; per-round interior count is the open core (`BridgeLoop44`). |
| A028 | 3 | partial-overlap | Per-NTT-prime `decide`-certificate of bad-count ≤ n with 4-adic tower transfer (`QuartetTowerLaw`) across a band of μ via cyclotomic splitting of Φ_n mod p. | Certified object is an integer bad-count via `decide`, not a char-sum sup. **Funnel:** Johnson/floor separation only opens at n ≥ 256 where `decide` over p ~ 2⁶⁴ is infeasible; the finite→infinite transfer across the separation is open. |
| A019 | 3 | partial-overlap | Fixed-ε\* budget rigidity: at fixed ε\*, q·ε\* ~ n is an integer budget, so the predicate is "bad-count ≤ n" — a Σ⁰₁ disjunction monotone in ⌊n⌋, claimed decoupled from C(n). | Reorganizes the predicate as an integer-count comparison (non-wall framing). **Funnel:** whether the comparison holds at the prize point collapses to BGK (B8 unsettled; floor = ceiling at every accessible scale). |
| A030 | 2 | already-tried | Cross-domain transfer: construct the RS instance as an AG-code specialization that provably list-decodes (designer p + curve), inheriting the AG list bound. | **DISQUALIFIES:** plain smooth RS IS the genus-0 AG code; genus-0 list-decoding is exactly Johnson. Capacity-achieving AG needs positive genus/folding → changes the object out of scope. |

### Lens L3 — formal / decidability-per-n + finite→infinite transfer

| ID | Feas | Novelty | Angle | Why-not-wall (and where it nonetheless funnels) |
|---|---|---|---|---|
| **A004** | 4 | partial-overlap | FRI round-by-round soundness composition via per-fold orbit count: per round folds μ_n→μ_{n/2} using only r=1 (a +1 carry), composing soundness multiplicatively over log n rounds via the axiom-clean `ActionOrbitFRI` substrate — never reaching deep r ≈ 89. | Round-by-round soundness is a product of per-round local orbit counts (Class C / p-independent), never the global L∞ sup M. **Funnel:** composing the per-round errors to beat ε\* at the floor still needs the deep-r excess to vanish. |
| **A005** | 4 | partial-overlap | Single-orbit persistence O_P = 1 at the binding d=2 direction via even/odd descent induction (proven rotation-equivariance), pinning #bad = n = budget p-independently. | O_P is a p-independent orbit count (Class C), not a char-sum magnitude. **Funnel:** reduces to the NAMED-OPEN obligation `OPDescentStep` (`_OffBGK_OPSingleOrbitPersistence.lean`, 1 sorry). |
| A023 | 3 | partial-overlap | Bad-γ scheme dimension dichotomy via Ax–Grothendieck / EGA IV.9 spreading-out: transfer the char-0 fiber dimension of the constructible bad-γ subscheme to all good p, settling o(n) vs Θ(n) binding-fold scaling as a p-independent dimension. | Object is a p-independent Krull dimension (Class C), off-wall. **Funnel:** load-bearing step (char-0 fiber dim BELOW Johnson) is the hard open question; shallow Θ(n³) data leans against it. |
| A024 | 3 | already-tried | Reduction-gap B1 as a finite SOS/Positivstellensatz certificate at fixed ε\* budget, lifted across a verified n-window by syntactic certificate-structure induction. | An SOS feasibility certificate is not a sup estimate. **Funnel:** in-tree C2 rigidity (`_DeltaStarBindingRigidity`) shows count and sup are tightly coupled at the binding radius → certificate likely needs the sup anyway. |
| A025 | 3 | already-tried | Self-improving amplification: MCA-bad-count / LD-list-size is a p-independent interleaving multiplicity (via `epsMCA_interleaved_eq`), reducing MCA to LD list-size, claimed decidable per n. | LD list-size is a codeword count. **Funnel:** P8 verdict ("LD face has no lever MCA lacks") + interior LD list-size = the same open equidistribution = the wall. |
| A027 | 3 | already-tried | B4 third-binding-regime search as a decidable orbit-stabilizer classification with exhaustiveness certificate; a third p-independent regime would bind δ\* without M. | Orbit-stabilizer classification is group-theoretic (Class C). **Funnel:** the B6 machine result (floor = ceiling at every scale) is direct evidence there is NO third regime → confirms the wall. |
| A029 | 3 | partial-overlap | Proth/Solinas Spur_r = 0 certified family via Lucas ladder (`CertifiedRungPrime`) + shape-restricted Brun-sieve/Hooley density (h·2^k+1 shape, claimed elementary vs generic Linnik). | Spur_r = 0 is a finite vanishing check. **Funnel:** proving good-Proth-primes have positive density at n^β is still prime-counting-in-AP = the analytic wall in shape-restricted clothing. |
| A006 | 3 | already-tried | deg(#bad_r) < r growing-slack as a Hilbert-polynomial degree bound via Bézout on the divided-difference scheme (proven `_SpecS3` naturality for p-independence). | deg(#bad_r) is a p-independent Krull/Hilbert degree (Class C), categorically not \|η_b\|. **DISQUALIFIES:** `_OffBGK_DegBadRGrowingSlack.lean` MACHINE-REFUTES deg(#bad_r) = r EXACTLY at r=3,4 for the raw count; open part = `OrbitDegreeBelowFold`. |
| A022 | 3 | already-tried | Interval-arithmetic-certified monotone CONTRACTION C(n)² ≤ a·C(n/2)² + b(n) with a < 2 (Liu–Zhou boundary term), lifting a finite verified base to all n. | **DISQUALIFIES:** the output is a bound on M = C(n)·√(n·log m). Measured ratio 2.82 > 2 ⟹ contraction needs the unproven Liu–Zhou saving = the wall itself. |
| A031 | 2 | already-tried | Ultraproduct/Łoś transfer of the closed char-0 Bessel bound to almost-all primes, then descend to one standard good prime. | **DISQUALIFIES:** the wall is a finite-r char-p wraparound phenomenon; M ≤ √(2n·log m) with r = ln q is NOT a fixed first-order sentence, so Łoś does not transfer it; descent to a usable standard prime IS the effective-good-prime wall. |

### Lens L4 — specific FFT-prime arithmetic

| ID | Feas | Novelty | Angle | Why-not-wall (and where it nonetheless funnels) |
|---|---|---|---|---|
| **A003** | 4 | partial-overlap | Spur two-square cut VACUITY on smooth primes (every smooth prime ≡ 1 mod 4 since 2^μ\|p−1) + a Solinas 2-adic replacement cut certifying p ∤ N(α) for the extremal antipodal relation. | Object is p\|N(α), a finite divisibility / collision-ABSENCE fact, not max\|η_b\|; vacuity lemma is genuinely proven (0 sorry). **PARTIAL-OVERLAP:** vacuity is real but the *content* is vacuous (empty existing cut, not a positive good-prime certificate); the replacement cut reduces to BCHKS 1.12. |
| A013 | 4 | partial-overlap | Goldilocks p = Φ₆(2³²): use the Φ₆/Fermat-prime factorization of p−1 to give the order-2^μ generator an explicit 2-adic closed form, turning a collision into a sparse {−2..2}-coefficient polynomial-root existence test. | Sparse-polynomial-root existence is a divisibility object, not max\|η_b\|. **Funnel:** the no-short-root proof at 2¹⁵⁸ IS the open cyclotomic minimal-weight conjecture (BCHKS 1.12). |
| A010 | 3 | already-tried | Class-trivial deployment regime (h=1, m ≤ 32) covering-radius bound for collision absence: lower-bound the shortest principal-ideal generator via the log-unit lattice covering radius. | Shortest-generator in a fixed h=1 ring is a geometry-of-numbers object. **DISQUALIFIES:** `_IdealLatticeMinkowskiCorrected` shows the Minkowski floor is dimension-vacuous (λ₁ → ~1) and the sharpening IS BCHKS 1.12. |
| A012 | 3 | already-tried | Per-prime exactness as fixed-rank ideal-lattice decidability via 2-power ramification rigidity: encode "no box-short generator of p exists" as bounded-quantifier lattice membership, decidable by interval arithmetic, transferred over support strata. | Fixed-rank ideal-lattice membership object. **DISQUALIFIES:** `_IdealLatticeMinkowskiCorrected` proves lattice reach is dimension-vacuous at deployed rank (m=128, rank 63) → reduces to BCHKS 1.12. |
| A020 | 2 | partial-overlap | Q1 conjugate-norm brick at deployed dyadic level d = 2²⁸: lift the d=16 char-free closure (`oddSymmetricVanishing_imp_antipodal`, V₁₆^prim = ∅) via the direct resultant route + designer prime-choice. | Q1 is a Stickelberger divisibility object (non-char-sum). **DISQUALIFIES:** obstruction-variety enumeration at d=2²⁸ is astronomically infeasible; self-similarity breaks in char-p at d=32 (in-tree note); no finite certificate at deployed d. |

---

## Conclusion (honest framing)

These are the **untried-non-wall frontier**. The selection criterion was specifically *not to
reduce to the worst-case M(n) framing*, and at the surface every angle above succeeds on that
narrow test: its primary object is a binomial count, an orbit count, a Krull dimension, a
resultant/norm divisibility, a code-dimension gap, a `decide`-certified integer, or a protocol
soundness product — never max_b |η_b|.

But on adversarial verification, **the per-good-prime FLOOR transfer in every case funnels back
into BCHKS Conjecture 1.12** (the cyclotomic minimal-vanishing-weight / additive-energy
conjecture), which is the wall in non-character-sum clothing — and several of these conclusions
are the in-tree files' OWN honest verdicts (`_IdealLatticeMinkowskiCorrected`,
`_wfS6_prize_regime_transfer`, `_OffBGK_OPSingleOrbitPersistence`, `_OffBGK_DegBadRGrowingSlack`).

**Therefore the honest count of genuinely-novel, non-wall, feasibility > 7 angles is 0.** The two
strongest genuinely-non-wall *artifacts* that already exist as clean theorems —
`RSDeltaStarLargeField.lean` (A001) and `_SpurEvenValuationTwoSquares.lean` (A003) — are real and
0-sorry, but are partial-overlap: they characterize/exclude, they do not reach the prize floor.

The most promising *direction to keep probing* (highest honest feasibility, cleanest non-wall
object, smallest visible gap to a real theorem) is **A002 — R4 symmetric-function coset-rigidity
at a generic-Galois prime** (Lang–Weil good-prime transfer of a q-independent symmetric-function
value-set coset count). Its object is genuinely not a character sum and is confirmed off the W4
route; its only funnel is the good-prime certificate, and unlike the lattice family it has no
in-tree refutation. Honest feasibility: 5/10.
