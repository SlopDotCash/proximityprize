export const meta = {
  name: 'prize-407-novel-attacks',
  description: '#407: NOVEL untried attack angles (Stickelberger, decoupling/VMT, toric-exact cohomology, Gross-Koblitz, slice-rank-odd, automorphic explicit formula, special-q) — verify + synthesize',
  phases: [
    { title: 'Novel', detail: 'one agent per genuinely-new angle from another domain' },
    { title: 'Verify', detail: 'adversarial skeptics on any non-wall claim' },
    { title: 'Synthesize', detail: 'rank novelty, hunt closure/partial, definitive map' },
  ],
}

const CONTEXT = [
  '# 407 Proximity Prize delta* — NOVEL ATTACK ROUND (user: keep grinding NOVEL attacks)',
  '',
  'The STANDARD faces are EXHAUSTED: a 14-vector adversarial assault proved a CONVERGENCE THEOREM —',
  'dense-Cayley SDP, moment/Markov-Krein LP, cumulant tower, additive energy, Gauss-phase algebra,',
  'Rojas-Leon, NVM/Lovett, effective-Katz, large-sieve-avg-q, ideal-SVP, Fourier-uncertainty, sum-',
  'product all reduce WITH NO LOSS to ONE input. DO NOT re-run those. Your job: a GENUINELY NEW tool',
  'from another domain, not yet tried. Novelty is the point.',
  '',
  '## THE RESIDUAL (the one open input, stated 3 ways)',
  'Prize regime: n=2^mu (mu<=40), q=1 mod n prime, INDEX m=(q-1)/n ~ 2^128 held CONSTANT, mu_n the',
  'order-n subgroup. eta_b = sum_{y in mu_n} psi(by). Prove the UPPER bound',
  '  M := max_{b!=0} |eta_b| <= C*sqrt(n*log m).',
  'Equivalent (all proven-equivalent in-tree):',
  '(1) the unimodular Gauss-phase sequence a_j = tau(psi^j)/sqrt(q), j over the ODD group Z/m, has',
  '    m-DFT sup-norm max_w |sum_j w^{-j} a_j| <= C*sqrt(m log m) (flatness).',
  '(2) cumulant kappa_r := (sum_i|eta_i|^{2r}/m)/((2r-1)!! n^r) <= 1 at depth r ~ ln m.',
  '(3) additive energy E_r(mu_n) = #{sum x_i = sum y_j mod q} <= (2r-1)!! n^r in char p to depth r~ln m.',
  '',
  '## KEY PROVEN FACTS (build on; do not re-derive)',
  '- m=(q-1)/n is ODD in the prize regime (n takes the full 2-part of q-1) — the 2-power is on mu_n,',
  '  the DFT on the COPRIME ODD group Z/m. (prizeIndex_odd, axiom-clean.)',
  '- char-0: E_r^C=(2r-1)!! n^r (Lam-Leung). char-p proven only r<=3 and norm-regime n<=32.',
  '- Jacobi cocycle: a_i a_j = (J(psi^i,psi^j)/sqrt q) a_{i+j}; (a_j) is a projective rep of Z/m.',
  '- DFT self-duality: m-DFT of (tau_j) = m*(eta_b). |a_j|=1 (Weil). Autocorrelation sum_j a_j conj(a_{j+h})',
  '  is itself a Jacobi sum.',
  '- the deep moment E_r IS a point count on a diagonal/Fermat-type toric hypersurface (Adolphson-Sperber).',
  '- best PROVEN sup-norm: BGK n^{1-o(1)}, di Benedetto t^{0.989} — a full half-power short of sqrt(n log m).',
  '',
  '## HONESTY CONTRACT (OVERRIDING): never claim proven what is not; no fabricated/silently-discharged',
  'bound as a theorem; a partial bound states its exact regime + assumptions. A genuinely-new tool that',
  'gives a real partial bound, OR a precise reason a powerful new tool fails, is the WIN. "Proven" is sacred.',
  'Be bold and creative — reach into the named domain hard — but report the true status.',
].join('\n')

const VECTORS = [
  { key: 'stickelberger-padic-digits', prompt: 'NOVEL: Stickelberger theorem. The Gauss sum tau(psi^j) has EXACT P-adic valuation (over the prime P above p in Z[zeta_{q-1}]) given by Stickelberger: v_P(tau(psi^{-j})) = s_p(j)/(p-1)-type digit-sum formula (Gross-Koblitz refines to the unit part). The phases a_j=tau(psi^j)/sqrt q are units, but their GLOBAL factorization (the Stickelberger ideal annihilating the class group) imposes rigid multiplicative relations on the tau(psi^j) across j. QUESTION: can the Stickelberger digit-sum structure of the tau(psi^j) prevent the DFT sum_j w^{-j} a_j from aligning (force cancellation / a lower bound on spread)? Concretely: do the prime-factorization constraints on products of a_j (from Stickelberger) obstruct the |sum| reaching m^{1-epsilon}? This combinatorial P-adic control of Gauss sums has NOT been applied to the prize. Derive what it gives; be precise about archimedean (the prize) vs P-adic (what Stickelberger controls) and whether they connect.' },
  { key: 'decoupling-vinogradov', prompt: 'NOVEL: Bourgain-Demeter-Guth decoupling / the Vinogradov Mean Value Theorem (proven 2016). The deep moment kappa_r = (1/m) sum_w |sum_j w^{-j} a_j|^{2r} is the 2r-th mean value of an exponential sum over Z/m. If the phase of a_j = tau(psi^j)/sqrt q has a controlled POLYNOMIAL-LIKE structure in j (it is NOT a pure quadratic chirp — proven — but the phase arg(a_j) may be a low-complexity/algebraic function of j via Hasse-Davenport/Jacobi recursion), then l^2-decoupling or the VMT bound (sharp: the 2r-th moment of sum_{j<=N} e(P(j)) for degree-d P) could give kappa_r <= the diagonal value to depth r~ln m. Investigate: is arg(a_j) a polynomial / algebraic phase of bounded degree in j (mod 1)? If so, apply VMT/decoupling to bound the moment. If arg(a_j) is genuinely non-polynomial (transcendental in j), say why decoupling is inapplicable. This modern harmonic-analysis tool has NOT been tried.' },
  { key: 'toric-exact-cohomology', prompt: 'NOVEL refinement: the moment/Betti wall said deep moments cap at r=2 because Adolphson-Sperber Betti ~ ambient n^{2r}. But the energy variety V_r = {sum_{i<=r} x_i = sum_{j<=r} y_j, all in mu_n} is a DIAGONAL TORIC hypersurface (a Fermat-type / GKZ A-hypergeometric variety) whose l-adic cohomology may be EXACTLY computable (not just bounded by ambient) via toric/Newton-polytope methods (Denef-Loeser, Adolphson-Sperber exact Betti = normalized volume of the Newton polytope, Batyrev). Compute the EXACT middle Betti number / the number of weight-w eigenvalues of Frobenius for V_r as a function of r and the index m. Is the cohomology of this specific diagonal variety SMALL (so Weil gives genuine cancellation to deep r) or genuinely as big as ambient? The exact toric computation (not the crude ambient bound) is the untried step. Use the Newton-polytope volume.' },
  { key: 'gross-koblitz-gamma', prompt: 'NOVEL: Gross-Koblitz formula expresses tau(psi^j) as a product of p-adic Gamma function values Gamma_p at fractions {j*p^i/(q-1)}. So the phase sequence a_j is a product of p-adic Gamma values, and its variation in j is governed by the p-adic Gamma functional equations (reflection, Gauss multiplication, the Dwork exponential). QUESTION: does the Gross-Koblitz / p-adic Gamma representation reveal a hidden recursion or functional equation for the DFT sum_j w^{-j} a_j that bounds its sup-norm? E.g., does the Gauss-multiplication formula for Gamma_p induce a self-similar (renormalization-group) relation on the phase sequence under the doubling/multiplication map on Z/m? This p-adic-analytic representation of the phases has NOT been exploited. Derive any functional equation and what it implies for flatness.' },
  { key: 'slice-rank-odd-index', prompt: 'NOVEL: the prior slice-rank/Croot-Lev-Pach attempt was on F_q (dense, failed). But the DFT and the phase-alignment relation live on the ODD group Z/m (m=(q-1)/n, proven odd). Slice rank / the polynomial method is strongest on groups (Z/k)^d with k a small fixed prime or prime power, and the ODDNESS of m may admit a cap-set-style bound. Reformulate the deep-moment / alignment count as a tensor/3-term-progression-free or matching count over Z/m, and apply slice rank with the m-odd structure (and the prime factorization of m). Does the polynomial method over Z/m give a nontrivial bound on the number of additive coincidences of the phases, i.e. on kappa_r? Be precise about what the relevant tensor is and whether slice rank applies to the multiplicative-subgroup structure.' },
  { key: 'automorphic-explicit-formula', prompt: 'NOVEL: the Jacobi sums J(psi^i,psi^j) are Hecke Grossencharacters of the cyclotomic field Q(zeta_n) (Weil); the period distribution = the distribution of these Hecke characters / their L-functions. Apply the EXPLICIT FORMULA for Hecke L-functions (sum over zeros = sum over primes) and the best unconditional zero-density / subconvexity bounds (no GRH) to get EFFECTIVE equidistribution of the Gauss periods at the prize conductor. Does the explicit formula, with the conductor of the relevant Hecke L-function being POLYNOMIAL in n (not 2^128), give the period sup-norm M <= C sqrt(n log m)? Compute the conductor of the Hecke characters governing the eta_b and check if the explicit-formula error is non-vacuous at the prize. The automorphic/L-function angle (vs the geometric Deligne-Katz angle) has NOT been tried effectively.' },
  { key: 'special-q-semiprimitive', prompt: 'NOVEL (exploits EXPLICIT-code freedom): the prize lets the prover CHOOSE q (an explicit code). Choose q in a SPECIAL arithmetic class where the Gauss periods of mu_n are EXACTLY KNOWN: (a) semiprimitive case (some power of p = -1 mod n) — periods are explicitly computable, the Cayley graph is strongly regular, eigenvalues known in closed form; (b) index-2/4 subgroups (uniform cyclotomy, Baumert-Mills-Ward); (c) q where mu_n generates a subfield. For each, COMPUTE the exact M and check whether M <= C sqrt(n log m) holds, AND whether such q exist with q ~ n*2^128 and n=2^mu up to 2^40 (a density/existence check). If a good explicit family of (q, n) with provably-bounded periods exists at prize scale, that CLOSES the prize for an explicit code (existence, not worst-case). Assess rigorously: do semiprimitive/uniform-cyclotomy q exist at prize scale with the RIGHT rho, and is M provably bounded there?' },
  { key: 'weil-restriction-genus', prompt: 'NOVEL: view eta_b = sum_{y: y^n=1} psi(by) as a character sum over the curve y^n = 1 (n points) — but lift to the SUPERELLIPTIC / Fermat curve picture: incomplete sums over mu_n relate to the number of points on the Artin-Schreier-Kummer cover z^p - z = b*y, y^n=1. The sup-norm M is then a sup over b of |point-count deviation|, governed by the GENUS and the eigenvalues of Frobenius on the Jacobian of a SPECIFIC curve. For the dyadic n=2^mu, the relevant curve/cover has structured Jacobian (CM by Z[zeta_{2^mu}]); does the CM structure + the specific genus give a Weil bound 2g sqrt(q)/m that beats sqrt(n log m)? The curve/Jacobian-CM angle (vs the abstract character-sum angle) may exploit the dyadic CM structure. Derive the genus and the resulting bound; check non-vacuous at prize scale.' },
]

const VERDICT = {
  type: 'object',
  required: ['vector','verdict','precise_statement','status','key_obstruction','novelty_1to10'],
  properties: {
    vector: { type: 'string' },
    verdict: { type: 'string', enum: ['CLOSES_prize_regime','PARTIAL_new_bound','promising_partial_progress','reconfirms_wall','vacuous_in_regime'] },
    precise_statement: { type: 'string' },
    status: { type: 'string', enum: ['rigorously_proven','conjecture_with_evidence','heuristic_only','refuted'] },
    key_obstruction: { type: 'string' },
    cross_path_lever: { type: 'string' },
    novelty_1to10: { type: 'number' },
  },
}
const VERIFY = {
  type: 'object',
  required: ['vector','holds_up','refutation_or_confirmation','corrected_verdict'],
  properties: {
    vector: { type: 'string' },
    holds_up: { type: 'boolean' },
    refutation_or_confirmation: { type: 'string' },
    corrected_verdict: { type: 'string', enum: ['CLOSES_prize_regime','PARTIAL_new_bound','promising_partial_progress','reconfirms_wall','vacuous_in_regime'] },
  },
}

phase('Novel')
const attacks = (await parallel(VECTORS.map(v => () =>
  agent(CONTEXT + '\n\n## YOUR NOVEL ANGLE: ' + v.key + '\n' + v.prompt +
    '\n\nGo deep into the named tool/domain as a rigorous mathematician. Try to CLOSE or partial-bound; give exact statements + proof sketch + regime. If the new tool fails, give the PRECISE reason (this is valuable — it maps the new domain). Note any cross_path_lever. Honesty contract applies. Return the structured verdict.',
    { schema: VERDICT, label: v.key, phase: 'Novel' })
))).filter(Boolean)

phase('Verify')
const claims = attacks.filter(a => a.verdict === 'CLOSES_prize_regime' || a.verdict === 'PARTIAL_new_bound' || a.verdict === 'promising_partial_progress')
const verifyThunks = []
for (const a of claims) {
  for (const idx of [0, 1]) {
    verifyThunks.push(() =>
      agent(CONTEXT + '\n\n## ADVERSARIAL VERIFICATION (skeptic ' + (idx + 1) + ')\nA novel-angle attack on "' + a.vector + '" claims:\nVERDICT: ' + a.verdict + '\nSTATEMENT: ' + a.precise_statement + '\nSTATUS: ' + a.status +
        '\n\nSet the "vector" field to "' + a.vector + '". You are a hostile referee. Try HARD to REFUTE: hidden assumption? reduces to the recognized open wall? arithmetic/regime error? only on-average/special-q? misreads the cited theorem (Stickelberger/VMT/toric/Gross-Koblitz/Hecke)? A genuine closure would be extraordinary — demand extraordinary rigor; downgrade anything not airtight. Return the structured verdict.',
        { schema: VERIFY, label: 'verify:' + a.vector + ':' + idx, phase: 'Verify' }))
  }
}
const verifs = (await parallel(verifyThunks)).filter(Boolean)

phase('Synthesize')
const survivors = claims.filter(a => {
  const vs = verifs.filter(v => v.vector === a.vector)
  return vs.length > 0 && vs.every(v => v.holds_up)
})
const synthesis = await agent(CONTEXT +
  '\n\n## SYNTHESIS\nNovel-angle attacks (JSON):\n' + JSON.stringify(attacks, null, 1) +
  '\n\nVerifications (JSON):\n' + JSON.stringify(verifs, null, 1) +
  '\n\nSurvivors (passed both skeptics):\n' + JSON.stringify(survivors, null, 1) +
  '\n\nDefinitive report: (A) did ANY novel tool close or partially-bound the prize, airtight? (B) which novel domain is MOST promising for future work and exactly what is the next concrete step there? (C) per-angle one-liner: what the new tool gives + why it stalls (if it does). (D) any cross-angle combination worth trying. (E) the sharpest residual restatement IF a novel angle reframed it. Honesty: report only what survived verification; do not upgrade downgraded claims. If nothing closes, say so plainly and rank the angles by genuine remaining promise.',
  { label: 'synthesize', phase: 'Synthesize' })

return { attacks, verifs, survivors, synthesis }
