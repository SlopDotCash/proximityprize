export const meta = {
  name: 'descent-assault-444',
  description: 'Stress-test / refute the even-odd dyadic descent proof path for explicit 2-power RS window list-decoding (delta* prize SEAM A)',
  phases: [
    { title: 'Refute', detail: 'adversarial attempts to break constant/poly window list + measure branching' },
    { title: 'Literature', detail: 'is the even/odd descent for 2-power RS list-decoding known?' },
    { title: 'Synthesize', detail: 'go/no-go verdict on the descent proof path' },
  ],
}

const REPO = 'C:/Users/Administrator/arklib'
const CTX = `
CONTEXT (#444 delta* prize, SEAM A = the window list-decoding challenge for explicit 2-power RS).
Setting: mu_n = order-n (n=2^mu) multiplicative subgroup of F_p*, proper subgroup (m=(p-1)/n>1, NEVER n=p-1),
window-interior radius delta = 1-rho-eta (rho=k/n the rate), prize-shaped prime p~n^4 (beta~4), MULTIPLE primes,
exclude correlated directions x^{n/2}=+-1. The "window list" L(u,n,k) = # distinct deg<k polynomials over F_p
agreeing with received word u on >= s=(rho+eta)n points of mu_n.

THE CLAIM UNDER TEST (the new math, verified so far at n=16,32, two primes):
(i) DESCENT IDENTITY (exact, verified 200/200): for n=2N, f(x)=F(x^2)+xG(x^2), u(x)=u_e(x^2)+x*u_o(x^2),
    P=F-u_e, Q=G-u_o:  |agreement| = 2*#{y in mu_N: P=Q=0} + #{y in mu_N: Q!=0 and P^2=y*Q^2}.
(ii) MONOMIAL BASE CASE (verified): the window list of a MONOMIAL word y^j on mu_N is CONSTANT in N (<=2 for
     j~N/2; 0 near edges).
(iii) DESCENT RECURSION: a weight-2 word x^a+x^b descends to a MONOMIAL PAIR (if a,b mixed parity) or a
     weight-2 word on mu_{N} (same parity); same-parity halving terminates at a monomial pair after v2(a-b)<=log2(n)
     levels.  => L(weight-2 word) <= branching^{v2(a-b)} * (monomial list)^2.

Existing probes you can run/extend (sympy is installed; python3 -u):
  ${REPO}/scripts/probes/probe_444_nonsym_list_recursion.py   (worst weight-2 word list + sym/nonsym split)
  ${REPO}/scripts/probes/probe_444_monomial_descent.py        (descent identity + monomial constancy)
  ${REPO}/scripts/probes/probe_444_worstword_exponent.py      (unit-factor reduction + true worst word)
HONESTY: exact arithmetic only, multiple primes, proper subgroups, never n=p-1. A refutation (finding a 2-power
word whose window list GROWS with n, or per-level branching that is NOT O(1)) is a WIN. Do not fabricate.
Return ONLY the structured fields requested.`

const VERDICT = {
  type: 'object',
  properties: {
    finding: { type: 'string', description: 'one-paragraph precise finding with exact numbers' },
    verdict: { type: 'string', enum: ['supports-path', 'refutes-path', 'inconclusive'] },
    numbers: { type: 'string', description: 'the exact measured values (n, primes, list sizes, etc.)' },
    reproduce: { type: 'string', description: 'exact command(s) to reproduce' },
  },
  required: ['finding', 'verdict', 'numbers', 'reproduce'],
}

phase('Refute')
const refuters = await parallel([
  () => agent(`${CTX}

YOUR TASK (Refuter A — break constancy by HIGHER WEIGHT). The path assumes the worst window word is low-weight
(weight 2). REFUTE this: at n=16 and n=32, scan weight-3 words x^a+x^b+x^c (and a sample of weight-4) over multiple
primes and the window interior, and find the TRUE worst-case window list over ALL words up to weight 4. Compare to
the weight-2 worst (n=16 rho=1/8 -> L=4; rho=1/16 -> L=7). If any higher-weight word gives a STRICTLY larger or
n-GROWING window list, the path is refuted. Report the worst word, its weight, exponents, list size, at n=16 vs 32.`,
    { label: 'refute:higher-weight', phase: 'Refute', schema: VERDICT }),

  () => agent(`${CTX}

YOUR TASK (Refuter B — measure PER-LEVEL BRANCHING). The poly/constant bound hinges on the descent's per-level
branching factor being O(1). For the true worst weight-2 word at n=16,32,64 (k small so feasible), explicitly run
ONE level of the descent identity: enumerate all (F,G) descended pairs that could lift to a list member, i.e. count
#{list members of u on mu_n} vs #{candidate (F,G) from the monomial/weight-2 lists on mu_N}. Compute the ratio
(branching = parent list size / child list size) at each level. Is it bounded by a small constant (<= ~4) and
stable across n? If branching GROWS with n, the bound degrades. Report branching at each (n, level).`,
    { label: 'refute:branching', phase: 'Refute', schema: VERDICT }),

  () => agent(`${CTX}

YOUR TASK (Refuter C — monomial base case at SCALE). Verify (or break) monomial-word window-list constancy at
N=64 and N=128 (use k'=2,3 only so C(N,k') is feasible: C(128,2)=8128, C(128,3)=341k) across >=4 primes including
a NON-Fermat prime (v2(p-1) small) and a large prime. Word y^j for j in {N/2-1, N/2+1, 3N/4, N-3}. Does any
monomial list exceed the n=16,32 value (which was <=2)? Also: does it stay constant as eta -> 0 (deeper window)?
Report the max monomial list over all (N, j, prime, eta) tested, and whether it grows with N.`,
    { label: 'refute:monomial-scale', phase: 'Refute', schema: VERDICT }),

  () => agent(`${CTX}

YOUR TASK (Refuter D — single-fiber term scaling + the v2(a-b) descent depth). Verify the descent's single-fiber
term |S_1| = #{y: Q!=0, P^2=yQ^2} stays O(k) (NOT O(n)) for the TRUE worst weight-2 word at n=16,32 (and n=64 for
small k), by measuring deg(P^2 - y Q^2) and the actual |S_1| for every list member. ALSO directly verify the
weight-2 descent recursion claim: a weight-2 word x^a+x^b with a,b SAME parity descends to a weight-2 word
x^{a/2}+x^{b/2} on mu_{n/2}, and with MIXED parity descends to a monomial pair; same-parity halving terminates at
a monomial pair after exactly v2(a-b) levels. Confirm by computing both the parent list and the child list and
checking the relationship. NOTE: ignore any 'unit-factor reduction' check in probe_444_worstword_exponent.py --
that probe's list_shifted is buggy (decodes against plain RS[k] not the shifted Laurent code); do NOT use it.
If |S_1| scales with n, or the descent depth/relationship fails, report it as a refutation.`,
    { label: 'refute:single-fiber', phase: 'Refute', schema: VERDICT }),
])

phase('Literature')
const lit = await agent(`${CTX}

YOUR TASK (Literature). Determine whether this even/odd (Kummer/squaring) dyadic descent for list-decoding
Reed-Solomon codes on a 2-POWER multiplicative evaluation domain is KNOWN. Search the literature (Guruswami-Sudan,
Kopparty, Guruswami-Xing, folded RS, Goldberg-Shangguan-Tamo, Brakensiek-Gopi-Makam, Berlekamp, "FFT RS list
decoding", "Reed-Solomon list decoding multiplicative subgroup", "even odd decomposition list decoding", KKH26
arXiv 2604.09724, ABF26 ePrint 2026/680). Is the statement "explicit smooth 2-power RS has constant/poly window
list strictly beyond Johnson" a known THEOREM, a known OPEN problem, or genuinely novel? Cite specific papers.
Be precise about what is known vs open. This determines whether the descent path, if it closes, is a new result.`,
  { label: 'literature', phase: 'Literature', schema: {
      type: 'object',
      properties: {
        known_status: { type: 'string', enum: ['known-theorem', 'known-open', 'novel', 'unclear'] },
        key_papers: { type: 'string' },
        assessment: { type: 'string' },
      }, required: ['known_status', 'key_papers', 'assessment'] } })

phase('Synthesize')
const syn = await agent(`${CTX}

YOUR TASK (Synthesis). Here are the refuter verdicts and the literature finding. Produce a single GO/NO-GO on the
even/odd descent proof path for the explicit-2-power-RS window list-decoding bound, and list the precise remaining
gaps that must be closed for a full proof (and which are now empirically supported vs still open).

REFUTERS: ${JSON.stringify(refuters.map(r => r && {v:r.verdict, f:r.finding, n:r.numbers}))}
LITERATURE: ${JSON.stringify(lit)}`,
  { label: 'synthesis', phase: 'Synthesize' })

return { refuters, lit, synthesis: syn }
