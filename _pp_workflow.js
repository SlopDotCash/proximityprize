export const meta = {
  name: 'pp-core-attack',
  description: 'Adversarially validate the proximity-prize research prunes + stress-test the closed-form δ* + generate/filter novel combinatorial routes to the open core',
  phases: [
    { title: 'RedTeam',   detail: 'adversarially try to REVIVE each of the 4 pruned routes' },
    { title: 'StressForm', detail: 'check the closed-form δ* against every ABF26 negative result' },
    { title: 'Generate',  detail: 'propose novel combinatorial routes to the census-domination core' },
    { title: 'Filter',    detail: 'apply the honesty filters (Johnson / trivial / incomputable / regime) to each route' },
    { title: 'Synthesize', detail: 'fuse survivors into the single most promising closed-or-near route' },
  ],
}

// ───────────────────────── shared math context ─────────────────────────
const CTX = `
PROXIMITY PRIZE — the open core (ground truth from ABF26 = IACR eprint 2026/680, Arnon-Boneh-Fenzi).

OBJECT. C = RS[F_q, L, k], L = μ_n a SMOOTH domain = multiplicative coset of a subgroup of order n=2^a
in F_q^*. Rate ρ=k/n ∈ {1/2,1/4,1/8,1/16}. m = n-k. ε* = 2^-128. Parameters: k ≤ 2^40, |F|=q < 2^256.
So n ≈ q^{1/5} (a SMALL subgroup). The OPEN WINDOW is δ ∈ (1−√ρ, 1−ρ) = (Johnson radius, capacity).

THE TWO GRAND CHALLENGES (nearly equivalent in this regime):
 - Grand MCA: pin δ*_C = largest δ with ε_mca(C,δ) ≤ ε*, WITH a two-sided proof (≤ below, > above).
   ε_mca(C,δ)= max_{f1,f2} Pr_{α∈F}[ ∃S,|S|≥(1−δ)n, Δ_S(f1+αf2,C)=0 but Δ_S((f1,f2),C²)>0 ].
 - Grand list-decoding: pin δ*_C = largest δ with |Λ(C^m,δ)| ≤ ε*·|F|, C^m = m-interleaved code.
Bridges: list⟹MCA with a √-PROXIMITY LOSS (Thm 5.1 [GCXK25]); CA⟹list (Thm 5.2/5.3). The √-loss is
why closing list-decoding combinatorially does NOT directly close MCA at the same radius.

THE CORE (census domination). For a far word w ∉ C and δ in the window, the LIST SIZE
  L(w,δ) = #{ c ∈ C : agreement(w,c) ≥ (1−δ)n }.
Equivalently the syndrome line–ball incidence #{γ∈F_q : s0+γ·s1 ∈ S_w}, S_w = H(weight-≤δn ball),
H the parity check. The whole prize = bound max_w L(w,δ) ≤ q·ε* through the window. The conjectured
answer is the CLOSED FORM δ* = H_q^{-1}( (1−ρ) − log_q(1/ε*)/n ), the radius where the equidistributed
list value q^{(H_q(δ)−(1−ρ))·n + 1} crosses q·ε*.

KNOWN POSITIVE/NEGATIVE RESULTS (ABF26 §3–5, all must be respected):
 - δ < δ_min/2 (unique dec.): ε_mca = ε_ca = O(n)/|F|. Below Johnson: known, polynomial list.
 - Thm 4.12 [BCHKS25]: RS MCA up to the Johnson bound, error O(n/δ^5|F|).
 - Thm 4.16 [BCHKS25;KK25]: ∃ EXPLICIT prime-field smooth-domain RS with ε_ca(C, 1−ρ−1/log n) ≥ n^c/|F|.
 - Thm 4.17 [CS25]: ε_ca = 1 once δ exceeds capacity by ~(1/√(n log q)+2/n−1/log q).
 - Thm 4.18 [BCHKS25]: EXACTLY at Johnson, ε_ca ≥ Ω(n²/|F|) (an error jump; stated in char 2).
 - Crites-Stewart: the true ceiling is the q-ary ENTROPY line H_q(δ)=1−ρ (below Singleton); their bad-line
   construction is DOMAIN-GENERIC (applies to μ_n) — the lower-half witness for the two-sided proof.

THE WALL. A worst-case bound on max_w L(w,δ) in the window needs EITHER (a) square-root cancellation of
incomplete subgroup character sums max_{b≠0}|∑_{x∈μ_n}ψ(bx)| ≤ C√n (the "Shaw gap"; OPEN 25y; at
n≈q^{1/5}<p^{1/4} no analytic method gives o(n)-saving, best ≈q^{0.0015} Shkredov, energy ≲n^{49/20}),
OR (b) a purely COMBINATORIAL bound on far-word list size beyond Johnson. The character-sum route is the
recognized analytic wall.

THE 4 PRUNED ROUTES (claimed DEAD for the prize regime — to be red-teamed):
 P1 GM-MDS/higher-order-MDS/Lovett: genericity over F(Y1..Yn)+Schwartz-Zippel on RANDOM points; a fixed
    μ_n is a measure-zero locus where det(M)=0 can vanish identically. (KRZ26 Open Problem 1.)
 P2 Folded/subspace-design (GG25,BCDZ): explicit only for FOLDED RS/multiplicity codes (alphabet
    s=O(1/γ²), kills the win); plain RS over μ_n is not subspace-designable.
 P3 Kong-Tamo point-variety incidence (2408.10977): variety must be GRAPH of a diagonal
    sum-of-permutation-monomials map (gcd(b,q−1)=1); the low-weight ball is none of these; q^{m/2} error vacuous.
 P4 Character sums / additive energy: hopeless analytically at n<p^{1/4}.

HONESTY FILTERS (a route is WORTHLESS unless it passes ALL): must NOT (i) reduce to the Johnson bound,
(ii) reduce to a triviality, (iii) require an incomputable/unprovable lemma, (iv) hold only OUTSIDE the
prize regime (must work at n≈q^{1/5}, window interior, ε*=2^-128), (v) leave residual open math.
`

// ───────────────────────── schemas ─────────────────────────
const PRUNE = {
  type: 'object', additionalProperties: false,
  required: ['route','hardest_revival_attempt','crack_found','verdict','confidence'],
  properties: {
    route: { type: 'string' },
    hardest_revival_attempt: { type: 'string', description: 'the strongest concrete attempt to make this route work for fixed μ_n in the prize regime' },
    crack_found: { type: 'boolean', description: 'true iff a genuine viable path was found despite the stated obstruction' },
    crack_detail: { type: 'string' },
    verdict: { type: 'string', enum: ['dead','crack','uncertain'] },
    confidence: { type: 'number', description: '0-10 confidence in the verdict' },
  },
}
const FORMCHECK = {
  type: 'object', additionalProperties: false,
  required: ['theorem','contradicts_closed_form','reconciliation','closed_form_survives'],
  properties: {
    theorem: { type: 'string' },
    plug_in_numbers: { type: 'string', description: 'evaluate the theorem bound at prize params (ρ=1/2, n=2^30, q=2^256, ε*=2^-128) and compare to the closed-form δ*' },
    contradicts_closed_form: { type: 'boolean' },
    reconciliation: { type: 'string' },
    closed_form_survives: { type: 'boolean' },
  },
}
const ROUTE = {
  type: 'object', additionalProperties: false,
  required: ['name','idea','key_inequality','why_escapes_charsum_wall','prize_regime_valid'],
  properties: {
    name: { type: 'string' },
    idea: { type: 'string', description: 'the mathematical mechanism, concretely' },
    key_inequality: { type: 'string', description: 'the precise inequality that would bound max_w L(w,δ)' },
    why_escapes_charsum_wall: { type: 'string', description: 'why this does NOT secretly require subgroup sqrt-cancellation' },
    prize_regime_valid: { type: 'boolean' },
    novelty_0_10: { type: 'number' },
  },
}
const FILTER = {
  type: 'object', additionalProperties: false,
  required: ['route_name','reduces_to_johnson','reduces_to_trivial','needs_incomputable','regime_valid','survives','fatal_flaw'],
  properties: {
    route_name: { type: 'string' },
    reduces_to_johnson: { type: 'boolean' },
    reduces_to_trivial: { type: 'boolean' },
    needs_incomputable: { type: 'boolean' },
    regime_valid: { type: 'boolean' },
    survives: { type: 'boolean' },
    fatal_flaw: { type: 'string' },
    if_survives_next_concrete_step: { type: 'string' },
  },
}

// ───────────────────────── Phase 1: red-team the prunes ─────────────────────────
phase('RedTeam')
const prunes = [
  ['P1 GM-MDS / higher-order-MDS / Lovett', 'Try HARDEST to certify list-decoding of a FIXED μ_n via GM-MDS / higher-order-MDS. Consider: the SPECIFIC structure of μ_n (it is the FFT/NTT domain, a cyclic group, NOT a generic point set) — does cyclotomic/character structure let one evaluate det(M) on μ_n explicitly (not just generically)? Does any 2024-26 result certify zero patterns for STRUCTURED (not random) points?'],
  ['P2 Folded / subspace-design', 'Try HARDEST to apply folded-RS / subspace-design machinery to PLAIN RS over μ_n. Is plain RS over μ_n secretly a folded/multiplicity code under some re-indexing of the 2^a-smooth domain (the tower structure n=2^a)? Does the alphabet-blowup actually matter for the MCA error bound, or only for the decoder?'],
  ['P3 Kong-Tamo point-variety incidence', 'Try HARDEST to fit the line–ball incidence into Kong-Tamo or a SIMILAR spectral incidence theorem. Is there a DIFFERENT variety (not the raw low-weight ball) — e.g. the syndrome variety, or a monomial-graph reformulation via the parity-check Vandermonde structure of RS — that IS a diagonal permutation-monomial graph and captures the same count?'],
  ['P4 Character sums / additive energy', 'Try HARDEST to get a USABLE worst-case subgroup character-sum / energy bound in the prize regime n≈q^{1/5}. Consider: do we actually NEED worst-case over all b, or only over the SPECIFIC b arising from far RS syndromes (which are structured, not arbitrary)? Could the structured-b restriction beat the generic Shkredov wall?'],
]
const redteam = await parallel(prunes.map(([route, attack]) => () =>
  agent(`${CTX}\n\nYou are an adversarial mathematician. Your job is to REVIVE a route that has been declared dead, by finding any genuine crack. Be rigorous and concrete — a vague "maybe" is not a crack; a crack is a specific viable mechanism. If after your best effort the route is genuinely dead, say so honestly with the precise obstruction.\n\nROUTE: ${route}\nATTACK DIRECTION: ${attack}\n\nReturn the structured verdict.`,
    { label: `redteam:${route.slice(0,12)}`, phase: 'RedTeam', schema: PRUNE })))
const cracks = redteam.filter(Boolean).filter(r => r.verdict === 'crack')
log(`RedTeam: ${cracks.length} cracks found out of 4 prunes`)

// ───────────────────────── Phase 2: stress-test the closed form ─────────────────────────
phase('StressForm')
const negResults = [
  'Thm 4.16 [BCHKS25;KK25]: explicit prime-field smooth-domain RS with ε_ca(C, 1−ρ−1/log n) ≥ n^c/|F|',
  'Thm 4.17 [CS25]: ε_ca = 1 once δ exceeds capacity by ~(1/√(n log q)+2/n−1/log q)',
  'Thm 4.18 [BCHKS25]: exactly at the Johnson bound, ε_ca ≥ Ω(n²/|F|) (error jump, stated char 2)',
  'Crites-Stewart entropy-line ceiling H_q(δ)=1−ρ, and the domain-generic bad-line lower bound',
]
const formChecks = await parallel(negResults.map((thm) => () =>
  agent(`${CTX}\n\nThe leading conjectured answer is the CLOSED FORM δ* = H_q^{-1}((1−ρ)−log_q(1/ε*)/n). Rigorously check it against the following published result, plugging in prize parameters. Does the result CONTRADICT the closed form (e.g. force δ* lower, or make ε_mca > ε* already below the claimed δ*)? Reconcile precisely with numbers. Be quantitative.\n\nRESULT: ${thm}\n\nReturn the structured check.`,
    { label: `form:${thm.slice(0,16)}`, phase: 'StressForm', schema: FORMCHECK })))
const contradictions = formChecks.filter(Boolean).filter(r => r.contradicts_closed_form)
log(`StressForm: ${contradictions.length} potential contradictions of the closed form`)

// ───────────────────────── Phase 3+4: generate novel routes, filter each ─────────────────────────
const angles = [
  'Far-pair SECOND MOMENT of the coherent-core value map: bound Σ_{pairs of codewords} [both agree with w on ≥(1−δ)n] by a rank/incidence argument on paired coherence conditions, controlling the degeneracy strata.',
  'POLYNOMIAL METHOD on the line: the bad γ are roots of a structured resultant/Wronskian; bound their number via degree, exploiting the 2^a-smooth (cyclotomic) structure of the domain.',
  'SUBSET-SUM / vanishing-sums (Li-Wan, Mann, Lam-Leung): the extremal far words are ladder words whose list = N_fib = C(s,r)/s EXACTLY; bound ALL words by the ladder via a census-domination (no word beats the fibre family) argument over F_q, past the char-0 transfer threshold.',
  'DUAL / MacWilliams: translate the far-word list count into a dual-code weight-enumerator statement; use the smooth-domain dual structure (also RS) to bound it.',
  'CONTAINER / hypergraph: the set of far words with large list is a sparse container; bound its size via a supersaturation/container argument keyed to the agreement hypergraph.',
  'INCREMENTS / interleaving stability (eprint 2026/891): exploit that ε_mca(C^m) is exactly controlled at seed-set ≤ q; lift the seed-level exact count to the window bound.',
  'p-ADIC / resultant transfer: make the char-0 exact list law (proven, ladder=N_fib) descend to F_q by bounding the resultant/discriminant threshold explicitly in the prize regime q≈2^256 (n fixed), closing Thread A.',
  'WEIGHTED first moment with a cleverly chosen weight that suppresses the degenerate strata, turning the second-moment obstacle into a positive-definite count (à la Selberg/large-sieve over the line).',
]
log(`Generate+Filter: ${angles.length} novel routes through pipeline`)
const routeResults = await pipeline(
  angles,
  (angle, _orig, i) => agent(`${CTX}\n\nPropose a NOVEL, concrete combinatorial route to bound the worst-case far-word list size max_w L(w,δ) (hence ε_mca) in the prize window, based on the following ANGLE. It must aim to AVOID the subgroup character-sum sqrt-cancellation wall. Give the precise key inequality you would prove and why it escapes the wall. Be a creative but rigorous research mathematician.\n\nANGLE ${i+1}: ${angle}`,
    { label: `gen:${i+1}`, phase: 'Generate', schema: ROUTE }),
  (route, _orig, i) => route ? agent(`${CTX}\n\nYou are a ruthless adversarial referee. Apply the HONESTY FILTERS to the following proposed route. Determine: does it reduce to the Johnson bound? to a triviality? need an incomputable/open lemma (e.g. secretly the character-sum wall, or an unproven RS list conjecture)? does it actually hold in the prize regime n≈q^{1/5}, window interior, ε*=2^-128? A route SURVIVES only if it passes ALL filters. Most will not — say exactly why, and if it survives give the single most concrete next step.\n\nPROPOSED ROUTE:\nname: ${route.name}\nidea: ${route.idea}\nkey_inequality: ${route.key_inequality}\nwhy_escapes_wall: ${route.why_escapes_charsum_wall}\nprize_regime_valid(self-claim): ${route.prize_regime_valid}`,
    { label: `filter:${i+1}`, phase: 'Filter', schema: FILTER }).then(v => ({ route, verdict: v })) : null,
)
const survivors = routeResults.filter(Boolean).filter(r => r.verdict && r.verdict.survives)
log(`Filter: ${survivors.length}/${angles.length} routes survive the honesty filters`)

// ───────────────────────── Phase 5: synthesize ─────────────────────────
phase('Synthesize')
const synthesis = await agent(`${CTX}\n\nYou are the lead. Here is the full output of an exhaustive attack on the proximity prize core.\n\nRED-TEAM of the 4 pruned routes:\n${JSON.stringify(redteam.filter(Boolean), null, 1)}\n\nSTRESS-TEST of the closed-form δ* against published negative results:\n${JSON.stringify(formChecks.filter(Boolean), null, 1)}\n\nNOVEL ROUTES + adversarial filter verdicts:\n${JSON.stringify(routeResults.filter(Boolean).map(r => ({ route: r.route, verdict: r.verdict })), null, 1)}\n\nSURVIVORS: ${survivors.map(s => s.route.name).join('; ') || 'NONE'}\n\nProduce a rigorous synthesis: (1) is the closed-form δ* confirmed as the answer, contradicted, or in need of amendment — and what is the SHARPEST correct statement? (2) which prunes genuinely hold vs which have cracks worth pursuing? (3) of the surviving routes (if any), which single one is the most promising concrete path to a RESIDUAL-FREE closure of the core, and what is the precise next lemma to prove? (4) if NONE survive, state honestly that the core remains the open wall and give the single most defensible sharpened reduction. Do not fabricate closure. Be concrete and quantitative.`,
  { label: 'synthesis', phase: 'Synthesize' })

return {
  cracks: cracks.map(c => ({ route: c.route, detail: c.crack_detail, confidence: c.confidence })),
  closed_form_contradictions: contradictions.length,
  survivors: survivors.map(s => ({ name: s.route.name, next: s.verdict.if_survives_next_concrete_step })),
  synthesis,
}
