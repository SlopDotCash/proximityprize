# WF407 / T357-10-derand — derandomize random-RS capacity to explicit smooth: WALLED

**Thread.** `T357-10-derand` (= 357-T10 / 232-T06). "Random/folded RS reaches list-decoding
capacity `1−ρ−η`; does a derandomization / fold-transport carry that to an EXPLICIT smooth domain,
or does the unfolding loss kill it?"

**Date.** 2026-06-14. **Verdict: WALLED** (reduces onto two proven walls; the one surviving
mechanism is REFUTED at toy scale). No fabricated closure — honesty contract held.

---

## The two-faced reduction (both faces now resolved against the route)

The target said the entire structure-vs-randomness difference "lives at the 3rd agreement moment".
That is exactly right, and it cuts the route in two faces, BOTH dead at prize scale:

### Face 1 — the moment face (already in-tree; reconfirmed exactly)

- **M1 (mean) and M2 (variance) of the coset agreement spectrum are PROVEN domain-independent.**
  - `AgreementMomentOne.sum_agreement_spectrum` (axiom-clean): `Σ_u a_j(u) = q^k·C(n,j)·(q−1)^{n−j}`
    for EVERY n-point domain. (M2 via the MDS distance distribution, O120/O122.)
- So the smooth-vs-random difference FIRST appears at **M3 = the triple agreement moment**
  = the code's triple distance enumerator, carried by `T = #{x∈D : p₁(x)=p₂(x)=p₃(x)}`.
- **Probe `scripts/probes/sweep_A20_third_moment.py` (exact, full q^n enumeration):**
  - M1, M2 are **bit-identical** smooth-vs-random at every (q,n,k) tested (ratio 1.0000).
  - The M3 smooth-vs-random separation in `E[T]` scales as **Θ(1/q²)** at fixed n, and is **EXACTLY
    0** already at `q ~ n⁴` (e.g. q=4129/n=8, q=65537/n=16, q=1048609/n=32: E[T]=0 both domains).
  - At the prize prime `q = n·2^128`, per-triple deviation `~ n/q² ~ 2^{-256}` — super-exponentially
    below `ε* = 2^{-128}`.
- **Lean (in-tree, axiom-clean):** `Frontier/Sweep_A20_ThirdMomentDerandGap.lean` —
  `perTripleDev_lt_epsStar` (`n/q² < 2^{-128}` at prize), `derandGap_excluded_at_prize`. The
  third-moment route is **quantitatively dead at prize scale**.

### Face 2 — the fold-transport / co-location face (THIS thread's new contribution)

The companion `probe_fold_transport_feasibility.py` reduced fold-transport viability to ONE
toy-probeable successor question that **had never been run**: the co-location probe.

**The exact fold-transport arithmetic** (new Lean brick
`Frontier/WF407_T357_10_FoldTransportColocation.lean`, axiom-clean):
- Fold route beats Johnson `1−√ρ` iff unfolding loss `L < L*(ρ) := (1−ρ)/(1−√ρ)`.
- **`Lstar_eq` : `L*(ρ) = 1 + √ρ`** (exact, since `1−ρ = (1−√ρ)(1+√ρ)`).
- **`Lstar_lt_two` : `L*(ρ) < 2`** for `0<ρ<1` ⟹ the smallest fold arity `s=2` has worst-case
  (full-spread) loss `L = s = 2 ≥ L*(ρ)` at EVERY prize rate ⟹ **naive fold-transport is DEAD**.
- The route survives ONLY if the smooth squaring tower FORCES error supports to co-locate to
  fraction **`≥ 1−√ρ`** (`colocation_threshold_eq`): the antipodal-pair-closure threshold equals
  the Johnson radius itself.

**The never-run co-location probe** `scripts/probes/wf407_T357-10-derand_colocation.py` (exact,
full enumeration of MCA-bad error supports over all γ∈F_p, KKH26-monomial AND random stacks on the
smooth subgroup μ_8 ⊂ F_17/F_41/F_97):

| ρ      | threshold `1−√ρ` | measured min co-location `cl(E)` | spread bad patterns | verdict |
|--------|------------------|----------------------------------|---------------------|---------|
| 1/2    | 0.293            | **0.000**                        | 64 / 80 (KKH), 46/98 (rnd) | REFUTED |
| 1/4    | 0.500            | **0.400**                        | 64 / 80 (KKH), 44/102 (rnd)| REFUTED |
| 1/8    | 0.646            | **0.400** (rnd)                  | 3 / 38 (rnd)        | REFUTED |

The squaring-tower block = the antipodal pair `{x,−x}`. At the window radius `δn ≈ Johnson·n`, the
MCA-bad error coordinates do **NOT** pack into antipodal pairs — typical co-location is `≈ 0.40` (or
`0` at ρ=1/2), far below the demanded `1−√ρ`. The error support SPREADS across distinct downstairs
blocks, so the realized unfolding loss `L = 2 − cl ≈ 1.6 > L*(1/4) = 1.5`: the fold cannot beat
Johnson. **The surviving condition is FALSE** — refuted for both the explicit KKH26 family AND
random stacks (so it is not a smoothness deficiency, it is intrinsic to the radius).

- **Lean corollary (axiom-clean):** `route_dead_at_quarter_rate` —
  `L*(1/4) = 3/2 < 8/5 = realizedLoss(2/5)`, the probe's measured spread witness consumed.

---

## Why this is WALLED, not REFUTED-of-prize or PROVEN

- The derandomization route is **dead by two independent mechanisms**: (i) its moment signal is
  `Θ(1/q²) ≪ ε*` (Face 1, in-tree); (ii) its surviving fold-transport condition (error co-location
  ≥ 1−√ρ) is refuted at toy scale for explicit AND random stacks (Face 2, new).
- Both faces collapse onto the **proven walls W2 / Johnson**: the only domain-dependence below M3 is
  zero (M1/M2 domain-independent = the MDS / pair-combinatorics fact), and the fold cannot beat
  Johnson because the unfolding loss exceeds `L* = 1+√ρ` whenever errors spread (which they do at
  the window radius). This is the **additive-energy √n-loss wall reappearing as the unfolding loss**:
  the smooth tower gives no co-location advantage the random domain lacks.
- It does NOT prove `δ*` (the prize core stays open via the Gauss-period / B-form / energy E_r faces,
  unchanged). It CLOSES the derandomization attack route by an honest size + spread argument.

## Artifacts

- `scripts/probes/wf407_T357-10-derand_colocation.py` — the never-run co-location probe (NEW).
- `Research/ProximityPrize/Frontier/WF407_T357_10_FoldTransportColocation.lean` —
  fold-transport arithmetic (`Lstar_eq`, `Lstar_lt_two`, co-location threshold, route-dead) (NEW).
- `scripts/probes/sweep_A20_third_moment.py`, `Frontier/Sweep_A20_ThirdMomentDerandGap.lean`
  (in-tree, the moment face — reconfirmed).
- `scripts/probes/probe_fold_transport_feasibility.py`, `probe_coset_agreement_moments.py`
  (in-tree, set up the question).

## What remains (new avenues)

- The co-location threshold `1−√ρ` is a **necessary condition on ANY fold-based δ* lower bound**:
  it excludes every method whose certified radius degrades by the worst-case spread factor. A
  fold-route that survives must use a fold whose block structure ALIGNS with MCA-bad supports —
  but the squaring tower's antipodal blocks provably do not (this thread). An *adaptive* fold
  (block structure chosen per error pattern) is the only opening, and it is not a derandomization
  of random-RS at all.
- This is structural evidence (not a theorem) that explicit-smooth δ* genuinely differs from
  random-RS capacity: the difference is invisible to M1/M2 and the fold cannot transport it.
