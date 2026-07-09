export const meta = {
  name: 'beyond-johnson-floor-attack-444',
  description: 'Adversarially attack the candidate beyond-Johnson unconditional floor delta* >= capacity - eta_crit for the proximity prize',
  phases: [
    { title: 'Attack', detail: 'find the flaw: R-a (incidence=lacunary), R-b (antipodal recursion exhaustive), numeric' },
    { title: 'Novelty', detail: 'is this floor already known (campaign / 2026/858 RVW)?' },
    { title: 'Verdict', detail: 'does the floor survive? go/no-go' },
  ],
}

const REPO = 'C:/Users/Administrator/arklib'
const CTX = `
CONTEXT (#444 delta* prize). mu_n = order-n (n=2^mu) mult. subgroup of F_p*, proper (m=(p-1)/n>=2, NEVER n=p-1),
prize p~n*2^128 (n~2^30), window delta=1-rho-eta, rho=k/n in {1/2,1/4,1/8,1/16}, budget=q*eps*=n. Johnson radius
delta_J=1-sqrt(rho) (eta=sqrt(rho)-rho, TOP of window); capacity delta=1-rho (eta=0). delta* in between.

THE CANDIDATE RESULT UNDER ATTACK (full argument in docs/kb/deltastar-444-beyond-johnson-floor.md): an
UNCONDITIONAL BEYOND-JOHNSON FLOOR delta* >= (1-rho) - eta_crit, eta_crit = (log s)/(2 log p) ~ mu/(2(128+mu)) ~ 0.09,
which is < sqrt(rho)-rho for every prize rate (so beyond Johnson by ~0.10). The argument:
(1) far-line incidence #bad-gamma = #{size-s subsets S of mu_n: first c=s-k=eta*n power sums vanish mod p} (the
    lacunary count). Derivation: for word x^a+gamma, bad gamma <=> agreement set S with x^a interpolated by deg<k poly
    <=> x^a - V_S (V_S=prod(X-x over S)) has deg<k <=> e_1(S)=..=e_{s-k}(S)=0 <=> (Newton) first c power sums vanish.
(2) Decompose S = (antipodal pairs {x,-x}) DISJOINT-UNION (antipodal-free core C). ODD power sums of pairs vanish
    auto, so odd conditions fall ONLY on C: p_j(C)=0 mod p for ceil(c/2) odd j<=c. Each odd j is a Galois auto of
    Q(zeta_n) (units mod 2^mu = odds), so sigma_j(beta_C)=0 mod distinct primes => p^{ceil(c/2)} | N(beta_C). Trace
    identity Tr(beta_C * conj) = phi(n)*|C| (antipodal-free) + AM-GM => |N(beta_C)| <= |C|^{phi(n)/2}. So
    p^{c/2} <= |C|^{n/4}, p <= |C|^{1/(2eta)}. Defect needs |C| >= p^{2eta}; eta>eta_crit => p^{2eta}>s>=|C|: IMPOSSIBLE.
    NO free-core defect.
(3) No free core => S fully antipodal-balanced => squared half (size s/2, in mu_{n/2}) has first c/2 power sums
    vanish = SAME problem on mu_{n/2}, SAME (rho,delta,eta), eta_crit(level) only DECREASES (prime fixed, s halves).
    So no free core at any level => surviving S = deep-coset unions = char-0 count = C(n/tau, s/tau) ~ poly(1/eta) = O(1).
(4) So #bad-gamma = O(1) << budget n for eta>eta_crit => delta* >= capacity - eta_crit. Beyond Johnson.
The author has made OVERCLAIM errors before (a workflow caught p^c should be p^{ceil(c/2)}); SCRUTINIZE HARD.
Reduces only to: Galois prime-splitting + cyclotomic trace identity (both standard). Honesty: a refutation is a WIN.

Probes (sympy installed): ${REPO}/scripts/probes/probe_444_trace_identity.py, probe_444_defect_search_n32.py,
probe_444_worstword_exponent.py. In-tree: Frontier/Sweep_A10_ActionOrbitBadPrime.lean (norm bound, axiom-clean),
Sweep_A43 (eta_crit no-go), Sweep_A42 (reunification), DISPROOF_LOG.md (Loop40/41 on 861, eprint 858 mention).
Return ONLY the structured fields requested.`

const V = { type:'object', properties:{
  finding:{type:'string'}, verdict:{type:'string',enum:['floor-survives','floor-REFUTED','inconclusive']},
  flaw:{type:'string',description:'the precise flaw if refuted, or "none found"'}, detail:{type:'string'} },
  required:['finding','verdict','flaw','detail'] }

phase('Attack')
const attacks = await parallel([
  () => agent(`${CTX}

YOUR TASK (Attacker R-b: the antipodal decomposition + recursion — the most likely flaw). Scrutinize step (2)-(3).
Is S = pairs DISJOINT free-core C exhaustive AND does the recursion capture ALL defects? Specifically: (i) when C is
non-empty, are the odd conditions REALLY ceil(c/2) independent constraints giving p^{ceil(c/2)}|N(beta_C) (or could
dependencies reduce the exponent, as happened before with p^c vs p^{ceil(c/2)})? (ii) when C is empty and S recurses
to the squared half on mu_{n/2}, is the squared half's "free core" the right object, and does eta_crit REALLY only
decrease (re-derive eta_crit(level))? (iii) Can a defect have a SMALL but nonzero free core that evades the norm
bound (e.g. |C| small enough that |C|^{1/(2eta)} >= p is satisfiable for eta>eta_crit)? Check the |C|>=p^{2eta}
threshold carefully. (iv) Does the even-condition coupling between pairs and C break the clean split? Find any gap.`,
    { label:'attack:recursion', phase:'Attack', schema:V }),

  () => agent(`${CTX}

YOUR TASK (Attacker R-a: is the incidence really the lacunary count, and is the worst direction monomial?).
Scrutinize step (1). (i) Verify the derivation "x^a - V_S has deg<k <=> e_1..e_{s-k}(S)=0" carefully (is a=s the
right/worst choice? what if the agreement set has size > s, giving MORE conditions, or the word has a != s?).
(ii) Is the WORST far-line direction really the monomial pencil x^a+gamma (cite/verify the dilation-symmetry
extremality)? Could a non-monomial direction give a LARGER incidence with FEWER effective conditions (smaller c),
where the norm bound is weaker? (iii) Crucially: at the EXACT delta* (eta=Theta(1/log n)), the binding object has
c=eta*n conditions which is STILL Theta(n/log n) = MANY; but Sweep_A10 claims delta* is pinned by a SINGLE condition
(o_1=0, c=1). Reconcile: is the binding object c=eta*n (floor argument) or c=1 (Sweep_A10)? This determines whether
the floor is valid. Verify numerically at n=16,32 that #bad-gamma for the binding monomial direction equals the
lacunary count with c=s-k conditions.`,
    { label:'attack:incidence', phase:'Attack', schema:V }),

  () => agent(`${CTX}

YOUR TASK (Attacker numeric: try to BREAK the floor computationally). At accessible n (16,32, and 64 for small k),
compute the EXACT worst-case far-line incidence #bad-gamma at radii with eta just ABOVE eta_crit, and verify it
equals the char-0 coset count (O(1), no defect) as the floor predicts. THEN: try to construct a COUNTEREXAMPLE —
a defect (non-coset subset with vanishing power sums mod p) at eta > eta_crit for SOME prime p (search small primes
where the norm ceiling p <= s^{1/(2eta)} might be violated). If you find ANY defect with eta>eta_crit, the floor is
REFUTED. Also sanity-check the eta_crit value and that capacity - eta_crit > Johnson (1-sqrt(rho)) numerically for
all prize rates. Use probe_444_defect_search_n32.py and extend it.`,
    { label:'attack:numeric', phase:'Attack', schema:V }),
])

phase('Novelty')
const novelty = await agent(`${CTX}

YOUR TASK (Novelty). IF the floor survives attack, is it NEW? Check: (i) the campaign's DISPROOF_LOG (Loop39/40/41,
the BGM/Q2 conditional paths, the "unconditional up to Johnson" BCIKS 2025/2055 result) — does anyone already state
an UNCONDITIONAL BEYOND-JOHNSON floor delta* >= capacity - constant? (ii) eprint 2026/858 (RVW Threshold-Halving,
"unconditional soundness above Johnson for FRI/STIR/WHIR") and 2026/861 (Chai-Fan Action-Orbit) — does either already
prove this (web search + the DISPROOF_LOG notes)? (iii) Is "delta* >= capacity - O(1)" via a cyclotomic norm bound +
antipodal recursion a known technique? Give a crisp verdict: novel / already-known / overlaps-858.`,
  { label:'novelty', phase:'Novelty', schema:{ type:'object', properties:{
    status:{type:'string',enum:['novel','already-known','overlaps-858','unclear']}, detail:{type:'string'} },
    required:['status','detail'] } })

phase('Verdict')
const verdict = await agent(`${CTX}

YOUR TASK (Verdict). Collate the three attacks + novelty into a single GO/NO-GO on the beyond-Johnson floor.
Be brutally honest: if ANY attacker found a real flaw, the floor is REFUTED (say exactly which step fails and why).
If all attacks failed to break it, state it SURVIVES and give the precise residual (the two standard facts it rests
on) and its novelty status. Do NOT rubber-stamp; the author has overclaimed before.

ATTACKS: ${JSON.stringify(attacks.map(a=>a&&{v:a.verdict,flaw:a.flaw,f:a.finding}))}
NOVELTY: ${JSON.stringify(novelty)}`,
  { label:'verdict', phase:'Verdict' })

return { attacks, novelty, verdict }
