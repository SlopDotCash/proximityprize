export const meta = {
  name: 'pp-rigidity-transfer',
  description: 'Rigorously test whether the prize floor transfers char-0 to F_p via Lam-Leung weight-<p cyclotomic rigidity (avoiding the character-sum magnitude wall), or has a fatal flaw',
  phases: [
    { title: 'Reconcile', detail: 'is the floor VANISHING (rigidity, weight<p) or MAGNITUDE (wall)?' },
    { title: 'CharZero',  detail: 'is the char-0 arbitrary-word floor provable via rigidity over C?' },
    { title: 'RedTeam',   detail: 'adversarially find the fatal flaw, or confirm the opening' },
    { title: 'Synthesize', detail: 'genuine path or mirage; precise next lemma' },
  ],
}

const CTX = `
PROXIMITY PRIZE FLOOR — a potential OPENING from cyclotomic rigidity (high burden of proof: must
reconcile with a prior MACHINE-CHECKED "this is the character-sum wall" conclusion).

SETUP. C = RS[F_q, mu_n, k], mu_n = order-n=2^a multiplicative subgroup of F_q^* (smooth/NTT domain),
rate rho=k/n in {1/2,1/4,1/8,1/16}, m=n-k, eps*=2^-128, k<=2^40, q=p<2^256 a prime, p == 1 mod 2^a
(NTT prime). n ~ p^{1/5}. Window delta in (1-sqrt(rho), 1-rho) = (Johnson, capacity).

THE FLOOR. For every far word w not in C and delta in the window, the list
  L(w,delta) = #{ c in C : agreement(w,c) >= (1-delta)n }  is at most N_fib (the antipodal ladder
value). N_fib = C(s,r)/s EXACTLY (Li-Wan, axiom-clean in-tree 'subsetSum_fibre_card_mul'). Proving
the floor pins delta* and resolves BOTH grand challenges.

THE PRIOR CONCLUSION TO RECONCILE (machine-checked, do not dismiss lightly):
 - 'CharSumTransferNoGo.transfer_ne_zero_iff' (axiom-clean): the transfer/census object
   prod_i charSum_i = Res(f_c, X^n - 1) is NONZERO iff every incomplete character sum
   sigma_i(c) = sum_j c_j omega^{ij} is NONZERO. (A VANISHING statement.)
 - 'EffectiveTransfer.esymm_eq_zero_iff' (axiom-clean): the char-0 -> F_p transfer "discharges by
   HEIGHT" only when C(w, floor(w/2))^{phi(n)} < p. For n=2^a, phi(n)=2^{a-1}, threshold ~2^{(a-1)w}
   -- astronomically BEYOND any prize prime p<2^256. The prior floor-attack concluded from THIS that
   the transfer fails in the prize regime, hence the floor = the character-sum MAGNITUDE wall
   max_b|sum_{x in mu_n} psi(bx)| <= o(n) (25-year open, n<p^{1/4}).

THE NEW INPUT (from a 2026 literature sweep) that may OVERTURN the prior conclusion:
 - disc(Phi_{2^a}) = +-2^{(a-1)2^{a-1}} is a PURE POWER OF 2. So for EVERY odd prime p, p does not
   divide disc, Phi_{2^a} mod p is SEPARABLE, and the INTEGRAL relation lattice among 2^a-th roots of
   unity transfers ISOMORPHICALLY mod p. There is NO bad odd prime for the integral/linear lattice
   (the only bad prime is 2, excluded by p == 1 mod 2^a). (Mathlib: Cyclotomic.Discriminant.)
 - Lam-Leung char-p theorem: the F_p weight set is W_p(2^a) = N*p + N*2. CONSEQUENCE: every F_p
   vanishing sum of 2^a-th roots of unity of WEIGHT (number of terms) < p is C-RIGID -- forced to be
   a Z-combination of opposite pairs {zeta, -zeta}, the SAME relations as over C. NEW (non-C)
   relations require weight >= p.
 - PRIZE REGIME: the vanishing sums in the floor's structure have weight <= n = 2^a (agreement sets
   have <= n points). And p ~ n*2^128 >> n. So WEIGHT <= n << p -- the rigidity TRANSFERS. The prior
   'esymm_eq_zero_iff' used the CRUDE HEIGHT bound C^{phi(n)} < p; the SHARP criterion is WEIGHT < p
   (Lam-Leung), which the prize SATISFIES. This is the suspected error in the prior conclusion.
 - CONVERSE CONSISTENCY: KKH26 (eprint 2026/782) PROVES proximity gaps FAIL at delta = 1-rho-eta,
   eta = Theta(1/log n), via "a new additive-combinatorics lemma on sums of roots of unity," with
   2^{Omega(1/eta)} = poly(n) close points. This is the bad line ABOVE delta*, matching the closed
   form delta* = (1-rho) - Theta(1/log q). The failure may be exactly the weight >= p regime.

THE PROPOSED ROUTE (II) -- avoids the magnitude wall:
  (a) Prove the CHAR-0 floor: over a CharZero field (or C), no word beats the ladder, L_C(w,delta) <=
      N_fib. Over C the cyclotomic linear independence ("hindep") HOLDS (it only fails in finite
      fields), so the in-tree gated lemma 'LamLeungAntipodalTightness.antipodal_invariant_of_vanishing_sum'
      is dischargeable over C. The open part is EXTENDING from ladder words to ARBITRARY words.
  (b) TRANSFER char-0 -> F_p via Lam-Leung weight-<p rigidity: every relevant vanishing condition has
      weight <= n < p, so the F_p agreement structure EQUALS the C structure (no spurious F_p
      coincidences). Hence L_{F_p}(w,delta) = L_C(w,delta) <= N_fib.
  Route (II) bounds the COUNT via char-0 + rigidity, NOT via direct-F_p character-sum MAGNITUDE.

THE CRUX TO DECIDE: Is the floor (the worst-case COUNT of bad gamma / list size) determined by
(X) VANISHING / linear-rigidity structure of roots of unity [transfers for weight<p, route II works],
or (Y) the MAGNITUDE of incomplete character sums [the 25-year wall, route II fails]? The two faces
were claimed equivalent (BCHKS Thm 1.9) -- but maybe only the DIRECT-F_p route is the magnitude wall,
while the char-0 + rigidity route (II) genuinely escapes it. Decide RIGOROUSLY.

HONESTY: this would OVERTURN a machine-checked conclusion, so the burden of proof is HIGH. Do not
fabricate a closure. If route (II) has a fatal flaw, find it precisely. If it is genuine, say exactly
which lemma closes it and why the prior magnitude-wall conclusion only applied to the direct route.
The honesty filters still apply: no reduction to Johnson, no triviality, must hold at n~p^{1/5},
weight<=n<p, window interior.
`

const RECON = {
  type: 'object', additionalProperties: false,
  required: ['face','reason','route_II_viable','prior_conclusion_status','confidence'],
  properties: {
    face: { type: 'string', enum: ['vanishing-rigidity', 'magnitude-wall', 'both-genuinely', 'depends'] },
    reason: { type: 'string', description: 'rigorous argument: is the worst-case COUNT determined by vanishing structure (transfers) or by char-sum magnitude (wall)?' },
    weight_of_floor_vanishing_sums: { type: 'string', description: 'precisely, what is the max weight (#terms) of the vanishing sums the floor count depends on? is it <= n, or can it reach >= p?' },
    route_II_viable: { type: 'boolean', description: 'does the char-0 + Lam-Leung-weight-<p transfer route genuinely bound the F_p floor, avoiding the magnitude wall?' },
    prior_conclusion_status: { type: 'string', enum: ['prior-correct-route-II-fails', 'prior-used-crude-bound-route-II-opens', 'unresolved'] },
    confidence: { type: 'number' },
  },
}
const CZERO = {
  type: 'object', additionalProperties: false,
  required: ['char0_floor_provable','argument','arbitrary_word_obstacle','key_lemma'],
  properties: {
    char0_floor_provable: { type: 'string', enum: ['yes-full','yes-ladder-only','no','unclear'] },
    argument: { type: 'string', description: 'the concrete char-0 extremality argument (ladder extremal over C via cyclotomic rigidity)' },
    arbitrary_word_obstacle: { type: 'string', description: 'the precise obstacle to extending from ladder words to arbitrary words over C' },
    key_lemma: { type: 'string' },
  },
}
const RED = {
  type: 'object', additionalProperties: false,
  required: ['fatal_flaw_found','flaw','route_II_survives','where_magnitude_actually_enters'],
  properties: {
    fatal_flaw_found: { type: 'boolean' },
    flaw: { type: 'string', description: 'the precise fatal flaw in route II, OR why it survives' },
    route_II_survives: { type: 'boolean' },
    where_magnitude_actually_enters: { type: 'string', description: 'if route II fails, the EXACT step where char-sum magnitude (not vanishing) is unavoidable; if it survives, why magnitude never enters' },
  },
}

phase('Reconcile')
const recon = await parallel([1,2,3].map(i => () =>
  agent(`${CTX}\n\nYou are a rigorous algebraic number theorist / coding theorist. DECIDE THE CRUX: is the proximity-prize floor (worst-case list size over arbitrary words) determined by VANISHING/linear-rigidity structure of 2^a-th roots of unity (which transfers char-0 -> F_p for weight < p, hence route II works in the prize regime) or by the MAGNITUDE of incomplete character sums (the 25-year wall)? Trace the worst-case count to its actual algebraic content. Crucially: what is the maximum WEIGHT (number of terms) of the vanishing sums the floor count depends on -- is it <= n (transfers) or can it reach >= p (Lam-Leung new relations, fails)? Reconcile with the machine-checked transfer_ne_zero_iff (vanishing) and the crude esymm height bound. Be rigorous and decisive; this overturns or confirms a machine-checked conclusion. [perspective ${i}]`,
    { label: `recon:${i}`, phase: 'Reconcile', schema: RECON })))
const viable = recon.filter(Boolean).filter(r => r.route_II_viable).length
log(`Reconcile: ${viable}/3 say route II is viable`)

phase('CharZero')
const czero = await parallel([1,2,3].map(i => () =>
  agent(`${CTX}\n\nFocus ONLY on step (a): is the CHAR-0 arbitrary-word floor provable -- over C (or a CharZero field), is the antipodal ladder the EXTREMIZER of the list size L_C(w,delta) over ALL words w, not just ladder words? Over C the cyclotomic linear independence holds, so vanishing sums of 2^a-th roots are exactly +-pairs (Lam-Leung/Mann rigidity). Attempt a concrete extremality argument (the ladder maximizes the subset-sum fibre among all antipodally-structured agreement configurations). State precisely the obstacle to the arbitrary-word case and the single key lemma. Be a rigorous extremal combinatorialist. [angle ${i}]`,
    { label: `czero:${i}`, phase: 'CharZero', schema: CZERO })))
log(`CharZero: ${czero.filter(Boolean).filter(r => r.char0_floor_provable === 'yes-full').length}/3 claim full char-0 floor provable`)

phase('RedTeam')
const red = await parallel([1,2,3,4].map(i => () =>
  agent(`${CTX}\n\nReconcile-phase verdicts: ${JSON.stringify(recon.filter(Boolean).map(r => ({face:r.face, viable:r.route_II_viable, status:r.prior_conclusion_status})))}\nCharZero verdicts: ${JSON.stringify(czero.filter(Boolean).map(r => ({prov:r.char0_floor_provable, obstacle:r.arbitrary_word_obstacle})))}\n\nYou are the HARSHEST adversarial referee. Route (II) claims to bound the prize floor via char-0 extremality + Lam-Leung weight-<p rigidity transfer, AVOIDING the character-sum magnitude wall, overturning a machine-checked conclusion. Find the FATAL FLAW. Candidate flaws to check rigorously: (1) the worst-case COUNT secretly depends on char-sum MAGNITUDE not just vanishing (e.g. the number of bad gamma is a SUM whose size needs cancellation, not a vanishing pattern); (2) the relevant vanishing sums actually have weight >= p for the worst word (so Lam-Leung rigidity fails); (3) the char-0 arbitrary-word floor is FALSE (a non-ladder word beats the ladder over C); (4) the char-0 -> F_p transfer of the COUNT requires more than vanishing-pattern equality (e.g. the words w over F_p have no char-0 lift); (5) it reduces to Johnson. If you find a fatal flaw, state it precisely. If after maximal scrutiny route II SURVIVES, say so and identify exactly why magnitude never enters. [attack ${i}]`,
    { label: `red:${i}`, phase: 'RedTeam', schema: RED })))
const survives = red.filter(Boolean).filter(r => r.route_II_survives).length
log(`RedTeam: route II survives ${survives}/4 adversarial attacks`)

phase('Synthesize')
const synth = await agent(`${CTX}\n\nFULL OUTPUT:\nReconcile: ${JSON.stringify(recon.filter(Boolean), null, 1)}\n\nCharZero: ${JSON.stringify(czero.filter(Boolean), null, 1)}\n\nRedTeam: ${JSON.stringify(red.filter(Boolean), null, 1)}\n\nSynthesize RIGOROUSLY and HONESTLY. (1) Is route (II) -- char-0 floor + Lam-Leung weight-<p rigidity transfer -- a GENUINE path to the prize floor that avoids the character-sum magnitude wall, or does it have a fatal flaw? Decide with the burden of proof on overturning the machine-checked prior conclusion. (2) If genuine: state the COMPLETE argument, identify the single remaining open lemma (likely the char-0 arbitrary-word floor), and explain precisely WHY the prior "magnitude wall" conclusion only applied to the direct-F_p route, not route II. Is the remaining lemma tractable? (3) If fatal flaw: state exactly where char-sum magnitude is unavoidable, confirming the wall. (4) Either way: what is the single most concrete next step (a Lean lemma to formalize, or a probe to run)? Do NOT fabricate a closure -- but do NOT dismiss a genuine opening out of excess caution either. The prompt's whole point is that this problem IS solvable; if route II is the key, say so decisively.`,
  { label: 'synthesis', phase: 'Synthesize' })

return {
  route_II_viable_votes: viable,
  route_II_survives_redteam: survives,
  char0_floor_status: czero.filter(Boolean).map(r => r.char0_floor_provable),
  synthesis: synth,
}
