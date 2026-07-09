export const meta = {
  name: 'pp-floor-attack',
  description: 'Constructive novel-combinatorics attack on the proximity-prize FLOOR (no word beats the antipodal ladder N_fib), with adversarial verification',
  phases: [
    { title: 'Generate', detail: 'novel combinatorial routes to prove the floor (compression, entropy, poly-method, ...)' },
    { title: 'Prove',    detail: 'attempt an actual proof / a proof of the simplest prize-relevant case' },
    { title: 'Verify',   detail: 'adversarially check each claimed proof against the honesty filters' },
    { title: 'Synthesize', detail: 'is any case genuinely closed? else the precise obstruction' },
  ],
}

const CTX = `
PROXIMITY PRIZE — the FLOOR (the single open core, [ABF26]=eprint 2026/680; in-tree workbench
PROXIMITY_PRIZE_WORKBENCH.lean: ceiling PROVEN, floor open).

SETUP. C = RS[F_q, μ_n, k], μ_n the order-n=2^a multiplicative subgroup of F_q^* (smooth/NTT domain),
rate ρ=k/n ∈ {1/2,1/4,1/8,1/16}, m=n-k, ε*=2^-128, k≤2^40, |F|=q<2^256, n≈q^{1/5}. Window
δ ∈ (1−√ρ, 1−ρ) = (Johnson, capacity).

THE FLOOR (prove THIS). For EVERY far word w ∉ C and every δ in the window, the list
  L(w,δ) := #{ c ∈ C : agreement(w,c) ≥ (1−δ)n }
is at most the value attained by the ANTIPODAL LADDER words. Equivalently, the ladder family is the
EXTREMIZER of the beyond-Johnson list size. This = BCHKS25 Conjecture 1.12 = "explicit smooth RS does
not over-cluster past Johnson beyond the structured ladder."

WHAT IS ALREADY PROVEN / EXACT (use freely):
 - The ladder words w = x^{rm} + λ·x^{(r−1)m} (collision-maximizing λ) achieve list size = the
   subset-sum fibre count N_fib(s,r) := max_λ #{ T ⊆ μ_s : |T|=r, Σ T = λ } over the relevant tower
   n = s·m. (in-tree 'ladder_list_ge_fibre', axiom-clean — the LOWER bound / supply side.)
 - **N_fib is now EXACT: N_fib(s,r) = C(s,r)/s · (1±o(1))** — Li–Wan equidistribution, formalized
   axiom-clean ('subsetSum_fibre_equidistributed', 'subsetSum_fibre_card_mul'): when c↦k·c is a
   bijection (p∤k case) every subset-sum fibre has EQUAL size C(s,k)/s; deviation super-exp small.
   So the floor's TARGET VALUE is closed; only the upper bound "max_w L(w,δ) ≤ N_fib" is open.
 - Ceiling PROVEN unconditional: δ* ≤ prizeDeltaStar via the ladder (no incomputable lemma).
 - The char-0 exact upper bound L(w,rm)=N_fib is PROVEN for ladder stacks via Mann / 2-power
   Lam–Leung ('ladder_gapBand_antipodal_charZero'); the open part is the char-0→F_q transfer past the
   resultant threshold AND the extension from ladder words to ARBITRARY words.

WHAT IS RULED OUT (do NOT propose these; they are the wall in disguise):
 - Far-pair second moment of the coherent-core value map → it IS the 2nd-moment proof of Johnson,
   VACUOUS in the window (the q-discount is a no-op on all loaded strata).
 - Any incomplete-subgroup-character-sum bound max_{b≠0}|∑_{x∈μ_n}ψ(bx)| ≤ o(n) → the Shkredov wall
   (n<p^{1/4}, best ≈q^{0.0015}); the floor's ANALYTIC face. By BCHKS Thm 1.9 the floor (combinatorial)
   ⟺ this gap (analytic) — they are the SAME wall, two faces.

THE OPENING. The floor's COMBINATORIAL face — "no word beats the antipodal subset-sum-fibre ladder" —
is an EXTREMAL COMBINATORICS / optimality statement, NOT obviously a character-sum statement. The
ladder value is exact (Li–Wan). A direct extremal argument (compression toward the ladder, entropy,
container, polynomial method on the agreement hypergraph) that proves no word exceeds N_fib would
close the floor WITHOUT touching the analytic wall — IF such an argument exists and does not secretly
re-encode the character sum.

HONESTY FILTERS (a proof is WORTHLESS unless it passes ALL): must NOT (i) reduce to the Johnson bound
(2nd-moment/√-loss), (ii) be a triviality, (iii) need an incomputable/open lemma OR secretly re-encode
max_b|∑ψ(bx)| (the character-sum wall), (iv) hold only OUTSIDE the prize regime, (v) leave residual
open math. A proof of a SPECIAL CASE (one rate, the r=2 first-window slice, char-0-then-transfer) that
passes all filters is genuine progress; flag clearly which case.
`

const PROOF = {
  type: 'object', additionalProperties: false,
  required: ['route','target_case','proof_sketch','key_lemma','claims_complete','escapes_charsum'],
  properties: {
    route: { type: 'string' },
    target_case: { type: 'string', description: 'full floor, or which special case (rate, slice, char-0)' },
    proof_sketch: { type: 'string', description: 'the actual argument, concretely, step by step' },
    key_lemma: { type: 'string', description: 'the single crux lemma the proof needs' },
    key_lemma_status: { type: 'string', enum: ['proved-here','in-tree','standard','open'] },
    claims_complete: { type: 'boolean', description: 'true iff the route claims a COMPLETE residual-free proof of its target_case' },
    escapes_charsum: { type: 'string', description: 'why this does NOT re-encode max_b|∑ψ(bx)|' },
  },
}
const VERDICT = {
  type: 'object', additionalProperties: false,
  required: ['route','target_case','reduces_to_johnson','reencodes_charsum','needs_open_lemma','regime_valid','genuinely_closes_case','fatal_flaw'],
  properties: {
    route: { type: 'string' },
    target_case: { type: 'string' },
    reduces_to_johnson: { type: 'boolean' },
    reencodes_charsum: { type: 'boolean' },
    needs_open_lemma: { type: 'boolean' },
    regime_valid: { type: 'boolean' },
    genuinely_closes_case: { type: 'boolean', description: 'true ONLY if this is a complete, honest, residual-free proof of its stated case' },
    fatal_flaw: { type: 'string' },
    salvage: { type: 'string', description: 'if not closed, the single most concrete next step or smaller case that might be' },
  },
}

const angles = [
  'COMPRESSION / SHIFTING: define a compression operator on far words w that pushes the agreement structure toward the antipodal subset-sum fibre (ladder) without decreasing L(w,δ); iterate to the ladder, proving it extremal. Specify the operator and the monotonicity lemma.',
  'ENTROPY / SHEARER: bound L(w,δ) by an entropy/Shearer inequality on the agreement-set hypergraph (each agreeing codeword = a degree-<k poly matching w on ≥(1−δ)n points); show the entropy is maximized by the fibre-union structure.',
  'POLYNOMIAL METHOD on the agreement hypergraph: the agreeing codewords c satisfy w−c vanishes on a large set; the differences c−c′ are low-degree polys vanishing on large overlaps; bound the number via a dimension/rank count specific to the μ_n (cyclotomic) evaluation structure that beats the generic 2nd-moment.',
  'INTERPOLATION-DEFICIENCY: each agreeing codeword is determined by its values on any k points of its agreement set; count the codewords via the number of (≥(1−δ)n)-subsets of μ_n that extend to a degree-<k poss agreeing with w, using the EXACT Li–Wan fibre equidistribution to bound the extensions.',
  'CONTAINER / SUPERSATURATION on the agreement incidence bipartite graph (words × codewords), using the cyclotomic regularity of μ_n to get a container bound tighter than Johnson in the window.',
  'REARRANGEMENT to char 0 + EXACT TRANSFER: prove the floor in char 0 for ARBITRARY words (extending the ladder-only `ladder_gapBand_antipodal_charZero` to all words via a symmetrization), then make the char-0→F_q transfer EXPLICIT in the prize regime q≈2^256 (n fixed) by bounding the single resultant/discriminant threshold — closing the named transfer residual.',
]

phase('Generate')
log(`Floor attack: ${angles.length} constructive routes`)
const results = await pipeline(
  angles,
  (angle, _o, i) => agent(`${CTX}\n\nYou are a world-class extremal/algebraic combinatorialist. CONSTRUCT a concrete proof (or a proof of the simplest prize-relevant special case) of the FLOOR using the following ANGLE. Give the actual argument and the single crux lemma. Be bold and novel — the prompt expects you to attempt genuine new math. But be rigorous: if the argument secretly needs the character-sum wall or reduces to Johnson, say so.\n\nANGLE ${i+1}: ${angle}`,
    { label: `prove:${i+1}`, phase: 'Prove', schema: PROOF }),
  (proof, _o, i) => proof ? agent(`${CTX}\n\nYou are a ruthless adversarial referee. The following is a CLAIMED proof of the floor (or a special case). Apply the HONESTY FILTERS with maximal scrutiny. The most common failure is SECRETLY re-encoding max_b|∑ψ(bx)| (the character-sum wall) or silently invoking the 2nd-moment Johnson bound — hunt for these. Determine whether it genuinely, completely, residual-free closes its stated case. If not, give the single most concrete salvageable smaller case.\n\nCLAIMED PROOF:\nroute: ${proof.route}\ntarget_case: ${proof.target_case}\nsketch: ${proof.proof_sketch}\nkey_lemma: ${proof.key_lemma} [${proof.key_lemma_status}]\nclaims_complete: ${proof.claims_complete}\nescapes_charsum(self-claim): ${proof.escapes_charsum}`,
    { label: `verify:${i+1}`, phase: 'Verify', schema: VERDICT }).then(v => ({ proof, verdict: v })) : null,
)
const closed = results.filter(Boolean).filter(r => r.verdict && r.verdict.genuinely_closes_case)
log(`Verify: ${closed.length}/${angles.length} routes genuinely close their case`)

phase('Synthesize')
const synth = await agent(`${CTX}\n\nFull output of a constructive attack on the floor:\n\n${JSON.stringify(results.filter(Boolean).map(r => ({ route: r.proof.route, case: r.proof.target_case, complete: r.proof.claims_complete, verdict: r.verdict })), null, 1)}\n\nGenuinely-closed cases: ${closed.map(c => c.proof.route + ' / ' + c.proof.target_case).join('; ') || 'NONE'}\n\nSynthesize rigorously and HONESTLY: (1) Did any route genuinely, residual-free close the full floor or a prize-relevant special case? If yes, state the complete proof precisely and which case. (2) If a special case closed (e.g. one rate, the r=2 slice, char-0), is it prize-relevant and is the path to the full floor clear? (3) If nothing closed, state the precise reason the floor resists every extremal-combinatorics route, and whether the floor is PROVABLY equivalent to the character-sum wall (so combinatorics cannot escape it) or whether a genuine combinatorial opening remains. Do NOT fabricate a closure. Give the single most promising concrete next lemma.`,
  { label: 'synthesis', phase: 'Synthesize' })

return {
  closed_cases: closed.map(c => ({ route: c.proof.route, case: c.proof.target_case, lemma: c.proof.key_lemma })),
  synthesis: synth,
}
