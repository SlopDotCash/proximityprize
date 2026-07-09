export const meta = {
  name: 'pp-analytic-attack',
  description: 'Genuine novel-math attack on the open analytic core B(mu_n) <= C sqrt(n log(q/n)) for 2-power subgroups, with ruthless adversarial verification',
  phases: [
    { title: 'Attack', detail: 'each agent attempts the bound via a distinct novel technique' },
    { title: 'Verify', detail: 'ruthlessly scrutinize each claimed proof for standard failure modes' },
    { title: 'Synthesize', detail: 'did anything survive; else the precise obstruction per technique' },
  ],
}

const CTX = [
  'THE OPEN ANALYTIC CORE of the Proximity Prize. Prove, or make genuine novel progress toward:',
  '',
  '  B(mu_n) := max over b != 0 of | sum_{x in mu_n} e_p(b x) |  <=  C * sqrt( n * log(q/n) )',
  '',
  'where mu_n is the multiplicative subgroup of order n = 2^a in F_p (p prime, p == 1 mod 2^a, an',
  'NTT prime), e_p(t) = exp(2 pi i t / p), and the prize regime is n ~ p^{1/5} (n < p^{1/4}), p < 2^256.',
  'EQUIVALENTLY (machine-checked in-tree, bidirectional): the additive energy E(mu_n) and its higher',
  'moments E_r = (1/p) sum_b |eta_b|^{2r} (eta_b = the char sum at frequency b) at their char-0 values.',
  'This is THE single open input on which the entire prize closed-form delta* rests. It is a recognized',
  '~25-year-open problem; no published method reaches n < p^{1/4} (best EXPLICIT saving n^{1-31/2880}',
  'only for n > p^{1/4}; below that only the ineffective BGK epsilon-saving; energy E <= n^{49/20} MRSS).',
  '',
  'EMPIRICAL FACTS (this session, FFT probes, to be EXPLAINED by any real proof):',
  ' - B / sqrt(n log_2(q/n)) ~ 1 across n = 8..64 (the bound holds empirically with C ~ 1).',
  ' - The additive energy E(mu_{2^a}) = 3n^2 - 3n EXACTLY for p >~ n^3 (the char-0 Sidon value).',
  ' - The r-th moment reaches its char-0 value for p > tau_r ~ n^{(r+3)/2} (a clean threshold law).',
  ' - The deep moments (r ~ Theta(n)) have threshold n^{Theta(n)} >> p; B (L-infinity max) grows like',
  '   sqrt(n log(q/n)), NOT O(sqrt n). The wall is the deep-moment / L-infinity behaviour.',
  '',
  'WHAT IS SPECIAL ABOUT THE PRIZE REGIME (exploit this; many true statements fail here):',
  ' - n = 2^a is a POWER OF TWO: mu_n is a 2-adic TOWER mu_2 < mu_4 < ... < mu_{2^a}, squaring is the',
  '   2-to-1 descent. The literature has NOT exploited the 2-power tower for cancellation (untouched).',
  ' - p == 1 mod 2^a (NTT prime): all 2^a-th roots are in F_p (split case); disc(Phi_{2^a}) is a pure',
  '   power of 2, so cyclotomic relations are rigid mod p for weight < p.',
  ' - The Gauss-sum expansion: S(b) = (n/(p-1)) sum_{chi in H-perp} chi-bar(b) tau(chi), |H-perp| =',
  '   (p-1)/n, each |tau(chi)| = sqrt(p). Square-root cancellation in this sum of (p-1)/n Gauss sums',
  '   (random phases) would give |S(b)| <~ (n/p) sqrt((p/n) p) = sqrt(n). The phases of these Gauss',
  '   sums are the crux (Gauss-sum argument / equidistribution).',
  '',
  'HONESTY (CRITICAL): this is an open problem. A claimed proof is almost certainly WRONG. The verifier',
  'must hunt for: (i) circular use of the bound itself or an equivalent unproven input; (ii) reduction',
  'to a known-insufficient bound (MRSS n^{49/20}, completion sqrt(p), BGK) dressed up; (iii) an error',
  'in a cancellation/phase estimate (assuming independence/randomness of Gauss-sum phases without proof);',
  '(iv) a bound that only holds for n > p^{1/4} or asymptotically wrong regime; (v) Johnson/2nd-moment',
  'in disguise. Do NOT accept a proof unless every step is rigorous and regime-correct. Failure with a',
  'precise obstruction is the expected and valuable outcome. Do NOT fabricate a closure.',
].join('\n')

const ATTACK = {
  type: 'object', additionalProperties: false,
  required: ['technique','claim','argument','key_step','claims_proof','regime_correct','where_novel'],
  properties: {
    technique: { type: 'string' },
    claim: { type: 'string', description: 'exactly what is claimed to be proven (the bound, a weaker bound, a special case, or an equivalent reduction)' },
    argument: { type: 'string', description: 'the actual mathematical argument, step by step, concretely' },
    key_step: { type: 'string', description: 'the single load-bearing step (where the cancellation/saving comes from)' },
    claims_proof: { type: 'boolean', description: 'true iff this claims a COMPLETE rigorous proof of the bound (or a prize-relevant special case)' },
    regime_correct: { type: 'string', description: 'does the key step actually work at n < p^{1/4}? be honest' },
    where_novel: { type: 'string', description: 'what is genuinely new vs the known methods (BGK, MRSS, completion, Stepanov)' },
  },
}
const VERDICT = {
  type: 'object', additionalProperties: false,
  required: ['technique','fatal_flaw_found','flaw','survives','what_it_actually_proves'],
  properties: {
    technique: { type: 'string' },
    fatal_flaw_found: { type: 'boolean' },
    flaw: { type: 'string', description: 'the precise fatal flaw (circular / known-insufficient / phase-independence-assumed / wrong-regime / Johnson-in-disguise), OR why it genuinely survives' },
    survives: { type: 'boolean', description: 'true ONLY if this is a complete, rigorous, regime-correct proof with no unproven input' },
    what_it_actually_proves: { type: 'string', description: 'the honest residual content: a weaker bound? a conditional statement? a reduction? nothing?' },
  },
}

const techniques = [
  '2-ADIC TOWER DESCENT: write S(b) over mu_{2^a} as a sum over the squaring fibres of mu_{2^{a-1}}; set up a recursion S_a(b) in terms of S_{a-1} and a square-root twist; look for a contraction / self-similar cancellation that the squaring map induces. Try to prove |S_a| <= sqrt(2)|S_{a-1}|-type descent giving sqrt(n).',
  'GAUSS-SUM PHASE CANCELLATION: expand S(b) = (n/(p-1)) sum_{chi in H-perp} chi-bar(b) tau(chi). Bound the sum of (p-1)/n Gauss sums by controlling their PHASES. Use Stickelberger / the 2-adic valuation of 2-power Gauss sums, or a second-moment over b of |sum chi-bar(b) tau(chi)|^2 to extract sqrt-cancellation. Show the diagonal/Parseval gives sqrt(n) on AVERAGE and bound the max via a 2k-th moment with the transferable moments.',
  'STEPANOV FOR THE DEEP MOMENT: instead of B (L-infinity), bound the r-th moment E_r(mu_n) directly via the Stepanov/polynomial method, exploiting that mu_n is the zero set of X^{2^a}-1 (a sparse 2-power polynomial). Construct an auxiliary polynomial vanishing to high order on the r-fold coincidence variety; the 2-power sparsity may give a better-than-MRSS exponent. Aim for E_r <= (2r-1)!! n^r (sub-Gaussian) for the relevant r.',
  'LARGE-SIEVE / DUALITY: use the large sieve inequality on the subgroup, or the duality between mu_n and its annihilator, exploiting that mu_n in an NTT field has a clean Fourier-dual structure (the FFT). Bound max_b |eta_b| via a sieve over the dual, using the 2-power FFT factorisation (Cooley-Tukey) of the indicator transform.',
  'SUM-PRODUCT WITH 2-POWER STRUCTURE: the BGK saving comes from sum-product expansion. For mu_n a 2-power group, the multiplicative structure interacts with addition via the tower. Try to get an EFFECTIVE (not epsilon) sum-product exponent for 2-power subgroups specifically, beating the ineffective BGK, using the tower of subfields/subgroups.',
  'COMPLETELY FRESH: any genuinely novel idea not in the above — e.g. a deletion/probabilistic argument on the frequencies, an entropy/transportation bound, a connection to a solved analogue (Salie sums, Kloosterman bounds, the FFT condition number), or exploiting the specific NTT prime arithmetic (p = c 2^a + 1).',
]

phase('Attack')
log('Analytic attack: ' + techniques.length + ' novel techniques on the open bound')
const results = await pipeline(
  techniques,
  (t, _o, i) => agent(CTX + '\n\nYou are a world-class analytic number theorist attempting genuine novel math on a recognized open problem. Attempt the bound via this TECHNIQUE. Be bold and concrete and push as far as you can toward a real proof. But be rigorous: identify the exact step where the saving comes from and whether it actually works at n < p^{1/4}. If you reach only a weaker/conditional result, say exactly what.\n\nTECHNIQUE ' + (i+1) + ': ' + t, { label: 'attack:' + (i+1), phase: 'Attack', schema: ATTACK }),
  (a, _o, i) => a ? agent(CTX + '\n\nYou are the ruthless adversarial referee for a claimed advance on a 25-year-open problem. Scrutinize this attempt with extreme skepticism. The prior on it being a complete correct proof is ~0; find the fatal flaw. Check every standard failure mode (circular, known-insufficient-bound-in-disguise, phase-independence-assumed-without-proof, wrong-regime, Johnson/2nd-moment-in-disguise). State precisely what it ACTUALLY proves (likely: a weaker bound, a conditional statement, or nothing new).\n\nATTEMPT:\ntechnique: ' + a.technique + '\nclaim: ' + a.claim + '\nargument: ' + a.argument + '\nkey_step: ' + a.key_step + '\nclaims_proof: ' + a.claims_proof + '\nregime(self): ' + a.regime_correct, { label: 'verify:' + (i+1), phase: 'Verify', schema: VERDICT }).then(v => ({ a, v })) : null,
)
const survivors = results.filter(Boolean).filter(r => r.v && r.v.survives)
log('Verify: ' + survivors.length + '/' + techniques.length + ' attempts survive ruthless verification')

phase('Synthesize')
const synth = await agent(CTX + '\n\nFull output of a novel-math attack on the open analytic core:\n\n' + JSON.stringify(results.filter(Boolean).map(r => ({ technique: r.a.technique, claim: r.a.claim, key_step: r.a.key_step, claims_proof: r.a.claims_proof, verdict: r.v })), null, 1) + '\n\nSurvivors: ' + (survivors.map(s => s.a.technique).join('; ') || 'NONE') + '\n\nSynthesize HONESTLY. (1) Did any technique produce a complete, rigorous, regime-correct proof of the bound or a prize-relevant special case? If YES, state it precisely and completely (this would be the prize). (2) If NO (expected), which technique got CLOSEST, what is the exact remaining gap, and is it the same wall or a genuinely new sub-problem? (3) What is the single most promising direction for a real proof, with the precise next lemma? (4) Be explicit: is the bound B <= C sqrt(n log(q/n)) for 2-power subgroups at n < p^{1/4} reachable by any of these, or does it remain the open wall? Do NOT fabricate a proof; a precise obstruction map is the honest deliverable.', { label: 'synthesis', phase: 'Synthesize' })

return { survivors: survivors.map(s => ({ technique: s.a.technique, proves: s.v.what_it_actually_proves })), synthesis: synth }
