export const meta = {
  name: 'attack-407-connections',
  description: 'Attack (prove or refute) the ranked δ* connections (#407) one agent each, adversarially verify, write verdicts into the master file',
  phases: [
    { title: 'Attack', detail: 'one agent per connection: prove / refute / reduce / open (probe or Lean or argument)' },
    { title: 'Verify', detail: 'adversarial check of each PROVEN/REFUTED verdict' },
    { title: 'Report', detail: 'scribe fills verdicts into the master file + writes the leaderboard' },
  ],
}

// args = the JSON array of connections (from scripts/probes/_407_conn/connections_100.json), passed by the parent.
const REPO = 'C:/Users/Administrator/arklib'
const ISSUE = 'scripts/probes/_issue407_full.md'
const CONE = 'ArkLib/Data/CodingTheory/ProximityGap'
const OUTDIR = 'scripts/probes/_407_conn'
const MASTER = `${CONE}/RESEARCH_SYNTHESIS_407_CONNECTIONS.md`

let conns = args
if (typeof conns === 'string') {
  try { conns = JSON.parse(conns) } catch (e) { conns = null }
}
if (conns && !Array.isArray(conns) && Array.isArray(conns.connections)) conns = conns.connections
if (!Array.isArray(conns) || conns.length === 0) {
  throw new Error('attack workflow requires args = non-empty array of connections; got ' + (typeof args))
}

const COMMON = `
You are attacking a candidate connection for the ArkLib Proximity-Gap Grand Prize (issue #407), working dir ${REPO}.
Grounding: ${ISSUE} (full issue + 76 comments), ${CONE}/DISPROOF_LOG.md (already-refuted routes), ${CONE}/RESEARCH_SYNTHESIS_407*.md, docs/kb/deltastar-407-*.md.

PRIZE REGIME (use for ALL numerics; NEVER the full group n=q−1): dyadic μ_n, n=2^μ a PROPER subgroup of F_q*, q prime ≡1 mod n, q≈n^β with β≈4–5 (n≪√q), proper-subgroup + large prime + multiple primes. Full-group / small-prime tests give false positives (the #400 trap).

HONESTY CONTRACT (mandatory, overrides everything): never fabricate a closure. The core (BGK √-cancellation for thin μ_n) is a recognized 25-year-open problem; most connections will NOT close it. A correct honest "OPEN/REDUCED" is a success. Label exactly:
 - PROVEN   : you give a rigorous argument, an already-in-tree axiom-clean Lean lemma, OR a reproducible exact probe that settles the claim affirmatively. (For identities/exact-count claims this is often achievable.)
 - REFUTED  : you exhibit a counterexample (exact probe at a proper subgroup/large prime, or a rigorous disproof). Note it should go to DISPROOF_LOG.
 - PARTIAL  : a piece proven, the rest open (say exactly which).
 - REDUCED  : not closed, but you sharpen it to a strictly cleaner/more-tractable open statement (say to what).
 - OPEN     : survives, no progress beyond restating; or it welds back to BGK/Paley (say which wall).
Prefer a FAST reproducible Python probe (exact integer arithmetic, small n=8/16/32/64, multiple proper-subgroup primes) or a precise mathematical argument. Only attempt Lean (scripts/pg-iterate.sh <file>, ~30-75s, lock-free) if the claim is a clean already-isolated lemma. Time-box: ~15-25 min of effort. Put probe scripts in ${OUTDIR}/ with a clear name.
`

const ATTACK_SCHEMA = {
  type: 'object', additionalProperties: false,
  required: ['id', 'title', 'verdict', 'method', 'evidence', 'honest_note'],
  properties: {
    id: { type: 'string' },
    title: { type: 'string' },
    verdict: { type: 'string', enum: ['PROVEN', 'REFUTED', 'PARTIAL', 'REDUCED', 'OPEN'] },
    method: { type: 'string', enum: ['probe', 'lean', 'argument', 'literature', 'mixed'] },
    evidence: { type: 'string', description: 'concrete: probe path + key numbers, or the argument, or the Lean decl + axiom audit. Be specific and reproducible.' },
    reduced_to: { type: 'string', description: 'if REDUCED/PARTIAL: the sharper open statement; else ""' },
    wall: { type: 'string', description: 'if OPEN and it welds to a wall: which wall; else ""' },
    honest_note: { type: 'string', description: 'caveats, scope, what was NOT shown' },
  },
}

const VERIFY_SCHEMA = {
  type: 'object', additionalProperties: false,
  required: ['id', 'confirmed', 'final_verdict', 'critique'],
  properties: {
    id: { type: 'string' },
    confirmed: { type: 'boolean', description: 'does the attacker verdict survive adversarial scrutiny?' },
    final_verdict: { type: 'string', enum: ['PROVEN', 'REFUTED', 'PARTIAL', 'REDUCED', 'OPEN'] },
    critique: { type: 'string', description: 'what you checked; any downgrade reason (esp. fabricated/overclaimed PROVEN or non-regime REFUTED)' },
  },
}

phase('Attack')
log(`Attacking ${conns.length} ranked connections (one agent each), then adversarial verify`)

const results = await pipeline(
  conns,
  // stage 1: attack
  (c) => agent(
`${COMMON}

== CONNECTION TO ATTACK: ${c.id} (rank ${c.rank}) ==
TITLE: ${c.title}
FIRST: Read ${OUTDIR}/conn/${c.id}.json — it has the FULL record (fields: connection, forms, walls, code_files, why_insightful, attack_plan). That is the precise claim to attack; the title above is only a label.

Carry out the attack honestly. Read the connection record, read any cited code_files / the issue grounding as needed, then run a probe or build the argument and reach a labeled verdict. Then WRITE your verdict JSON to ${OUTDIR}/verdict_${c.id}.json (single object matching the schema; you are the only writer of that file, no race). Return the same object as structured output.`,
    { label: `attack:${c.id}`, phase: 'Attack', schema: ATTACK_SCHEMA }
  ),
  // stage 2: adversarial verify (only meaningfully scrutinizes PROVEN/REFUTED, but runs on all)
  (att, c) => {
    if (!att) return { id: c.id, confirmed: false, final_verdict: 'OPEN', critique: 'attacker returned null' }
    if (att.verdict !== 'PROVEN' && att.verdict !== 'REFUTED') {
      return { id: c.id, confirmed: true, final_verdict: att.verdict, critique: 'non-decisive verdict, accepted as-is' }
    }
    return agent(
`${COMMON}

You are an ADVERSARIAL VERIFIER. An attacker reached a DECISIVE verdict on connection ${c.id} ("${c.title}"). Default to skepticism: try to break it.
ATTACKER VERDICT: ${att.verdict} via ${att.method}
ATTACKER EVIDENCE: ${att.evidence}
ATTACKER NOTE: ${att.honest_note}

CHECK: (a) regime validity — was any probe at a PROPER subgroup + large prime (not full group / not tiny prime)? (b) arithmetic/logic correctness — recompute or re-derive the key step. (c) for PROVEN: is it really rigorous / axiom-clean, or an overclaim? (d) for REFUTED: is the counterexample genuine and in-regime, not an artifact? If the verdict does NOT survive, downgrade it (PROVEN→PARTIAL/OPEN, REFUTED→OPEN) and say why. Return structured output.`,
      { label: `verify:${c.id}`, phase: 'Verify', schema: VERIFY_SCHEMA }
    ).then((v) => v || { id: c.id, confirmed: true, final_verdict: att.verdict, critique: 'verifier null; accepting attacker verdict' })
  }
)

// results[i] is the verifier output (stage 2); pull final verdict
const finals = conns.map((c, i) => ({
  id: c.id,
  title: c.title,
  final_verdict: (results[i] && results[i].final_verdict) || 'OPEN',
  confirmed: results[i] ? results[i].confirmed : false,
  critique: (results[i] && results[i].critique) || '',
}))
const tally = finals.reduce((m, f) => { m[f.final_verdict] = (m[f.final_verdict] || 0) + 1; return m }, {})
log(`Verdict tally: ${JSON.stringify(tally)}`)

phase('Report')
const report = await agent(
`${COMMON}

You are the REPORT SCRIBE for the #407 connection attack campaign. The per-connection verdicts have been written to ${OUTDIR}/verdict_C*.json (one object each, matching: id,title,verdict,method,evidence,reduced_to,wall,honest_note). The adversarial verifier's FINAL verdicts are:
${JSON.stringify(finals)}

DO THIS:
1. Glob ${OUTDIR}/verdict_C*.json and Read them all. Use the VERIFIER's final_verdict above as the authoritative verdict for each id (it may differ from the attacker's self-label after adversarial downgrade); keep the attacker's evidence/reduced_to/wall/honest_note for detail.
2. Update the master file ${MASTER}: for each connection section "### C0xx — ...", replace the "**Verdict:** _pending_" line with:
   **Verdict:** <FINAL_VERDICT> (<method>) — <one-line evidence/reduction/wall summary>
   Do this with the Edit tool per section (or rewrite the file preserving all section content + ranking). Do NOT lose any section.
3. Prepend (right after the intro/legend, before the ranked table) a "## Attack results" block:
   - a tally table (PROVEN / REFUTED / PARTIAL / REDUCED / OPEN counts),
   - a short "Headlines" list: the PROVEN ones, the REFUTED ones (each one line), and the 5 most promising REDUCED ones (sharper open statements worth pursuing).
4. If any REFUTED connection is genuinely new, note (do not necessarily write) that it belongs in DISPROOF_LOG.md.

Return a concise text summary: the tally, the headline PROVEN/REFUTED/REDUCED items (titles + one-line each), and confirm the master file was updated.`,
  { label: 'report-scribe', phase: 'Report' }
)

return { tally, finals, report }
