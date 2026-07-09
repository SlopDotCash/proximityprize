export const meta = {
  name: 'binius-313-plumbing-p1',
  description: 'Wire CoreInteractionPhase Tier-1/2 shells (foldRelay/foldCommit/blocks/sumcheckFold) into real append/seqCompose proofs',
  phases: [
    { title: 'API', detail: 'pin exact composition lemma signatures' },
    { title: 'Wire', detail: 'sequential shell-replacement bricks in CoreInteractionPhase.lean' },
    { title: 'Package', detail: 'full validation + land package' },
  ],
}

const WT = 'C:/Users/Administrator/wt313plumb'
const PROTOCOL = `
## Environment & protocol (READ CAREFULLY)
- Work ONLY in the worktree ${WT} (git worktree of lalalune/ArkLib main; .lake is a JUNCTION to C:/Users/Administrator/ark-pushwt/.lake with prebuilt oleans).
- NEVER run 'lake build'. Validation = 'cd ${WT} && lake env lean ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean' (exit 0 = pass; the file is ~1800 lines, budget 3–12 min per check; if a check exceeds ~20 min, kill and simplify).
- Lean 4.30.0-rc2. autoImplicit=false. Respect the file's existing local linter caps; bump minimally with a comment only if needed.
- Axiom hygiene: NO sorry/admit/new axiom/vacuous True-props. '#print axioms' temporarily on each rewired theorem; expect [propext, Classical.choice, Quot.sound] (+ existing residual classes ONLY where the wired sub-lemmas still consume them — e.g. anything threading finalSumcheckStep before #327 lands must NOT be your target). Remove audit prints before finishing.
- Known gotchas: Fin indices as 'i.val + 1' not '↑i + 1' in binders (isDefEq divergence); Fin.val-of-mk opaque to omega — 'show' first; relation-transport helpers ALREADY EXIST in the file (strictRoundRelation.of_fin_eq:108, roundRelation.of_fin_eq:115, Statement.of_fin_eq, OracleStatement.heq_of_fin_eq, Witness.of_fin_eq) — USE them for the Fin-index side conditions instead of inventing new casts.
- Git: do NOT commit/push — orchestrator lands.
- Report honestly; never claim validation you didn't run.`

phase('API')
const api = await agent(`You are the API-pinning agent for the Binius #313 plumbing wave (ArkLib, Lean 4).
${PROTOCOL}

The goal of this workflow: replace hypothesis-shell theorems in ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean (pattern: 'theorem X (hX : <conclusion>) : <conclusion> := hX') with REAL proofs that compose per-step lemmas via the OracleReduction append/seqCompose API.

Shell inventory (line numbers from the survey; re-verify):
- 159 foldRelayOracleReduction_perfectCompleteness (hyp hFoldRelayPerfectCompleteness)
- 200 foldRelayOracleVerifier_rbrKnowledgeSoundness
- 259 foldCommitOracleReduction_perfectCompleteness
- 305 foldCommitOracleVerifier_rbrKnowledgeSoundness
- 866 nonLastSingleBlockOracleReduction_perfectCompleteness
- 898 lastBlockOracleReduction_perfectCompleteness
- 918 sumcheckFoldOracleReduction_perfectCompleteness
- 948 lastBlockOracleVerifier_rbrKnowledgeSoundness
- 998 nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness
- 1039 nonLastBlocksOracleVerifier_rbrKnowledgeSoundness
- 1072 sumcheckFoldOracleVerifier_rbrKnowledgeSoundness
(EXCLUDED from this wave — blocked on #327: 1137 coreInteractionOracleReduction_perfectCompleteness, 1174 coreInteractionOracleVerifier_rbrKnowledgeSoundness.)

Proven leaves available: foldStep_is_logic_complete (ReductionLogic.lean:386), commitStep_is_logic_complete (ReductionLogic.lean:993), relay-step lemmas (find them), foldRelayKnowledgeError_eq (:189), foldCommitKnowledgeError_eq (:293), and whatever per-step rbr-KS leaf lemmas exist (search ReductionLogic.lean + Steps/ dir).

Your tasks:
1. Read CoreInteractionPhase.lean fully (the def + shell regions): for each shell, record the EXACT statement (relIn/relOut/oracleReduction/verifier instantiations) and the exact definition of the composed object it talks about (foldRelayOracleReduction at :138 = append of WHAT exactly; nonLastSingleBlockOracleReduction at :566 = seqCompose/append of what; etc.).
2. Read the composition API files in ArkLib/OracleReduction/Composition/Sequential/ — pin the EXACT names + full signatures (copy statements verbatim) of the append perfectCompleteness lemma variants (AppendPerfectCompleteness*.lean), seqCompose perfectCompleteness (SeqComposePerfectCompletenessThreaded.lean), and the rbr-KS composition lemmas (AppendRbrKnowledge*.lean, SeqComposeRbrKnowledgeProof.lean). Record their side-condition shapes (relation equalities, Subsingleton/IsFailingDet instances, error-function forms like Sum.elim).
3. Read the RingSwitching precedent (ArkLib/ProofSystem/RingSwitching/RbrKnowledgeWiring.lean + WiringInstances.lean) — how did they discharge the same shape? Record the proof skeleton verbatim for one representative theorem.
4. Check what the per-step IsStronglyComplete → OracleReduction.perfectCompleteness bridge is (how does foldStep_is_logic_complete lift to the OracleReduction layer? grep for IsStronglyComplete consumers; there is likely a 'logic' → 'reduction' adapter — pin its name/signature).
5. Produce the wiring plan: ordered bricks (innermost first), each = (target shells, exact composition lemma to apply, the side conditions to discharge and HOW — which of_fin_eq helpers, what index identities like (ℓ/ϑ-1)*ϑ + ϑ = ℓ, any Nat-arithmetic obligations), plus risks. Note for each brick whether call sites elsewhere in the repo pass the dropped hypothesis explicitly (grep each shell name repo-wide; list files needing call-site fixes — e.g. General.lean).`, {
  label: 'api:pin-signatures', phase: 'API',
  schema: {
    type: 'object',
    required: ['shells', 'composition_api', 'precedent', 'bridge', 'bricks'],
    properties: {
      shells: { type: 'string' },
      composition_api: { type: 'string' },
      precedent: { type: 'string' },
      bridge: { type: 'string' },
      bricks: { type: 'array', minItems: 1, maxItems: 8, items: { type: 'object', required: ['name','targets','route','side_conditions','call_sites','risks'], properties: { name:{type:'string'}, targets:{type:'string'}, route:{type:'string'}, side_conditions:{type:'string'}, call_sites:{type:'string'}, risks:{type:'string'} } } }
    }
  }
})
if (!api) throw new Error('API agent died')
log(`API pinned: ${api.bricks.length} wiring bricks planned`)

phase('Wire')
let progress = 'Nothing wired yet — you are the first brick.'
let failed = null
const results = []
for (let i = 0; i < api.bricks.length; i++) {
  const b = api.bricks[i]
  const res = await agent(`You are wiring brick ${i+1}/${api.bricks.length} ("${b.name}") of the Binius #313 plumbing wave.
${PROTOCOL}

## Lane state
${progress}

## API context (pinned by the API agent — re-verify signatures against source before relying on them)
Composition API: ${api.composition_api}
Logic→Reduction bridge: ${api.bridge}
RingSwitching precedent skeleton: ${api.precedent}

## Your brick
Targets (shells to replace with real proofs): ${b.targets}
Route: ${b.route}
Side conditions to discharge: ${b.side_conditions}
Call sites that pass the dropped hypothesis (fix in the SAME brick): ${b.call_sites}
Risks: ${b.risks}

## Working rules
- Replace each target shell 'theorem X (hX : C) : C := hX' with a real 'theorem X ... : C := <composition proof>' — DROP the shell hypothesis from the signature, fix all call sites you listed (grep again to be sure), and keep statement conclusions IDENTICAL (downstream must not weaken).
- If a side condition is genuinely unprovable as stated (real math gap, not index plumbing), STOP that target, restore it compiling as-was, and report precisely — do not weaken or launder.
- Validate after each target: lake env lean on CoreInteractionPhase.lean (+ any other edited file). Re-validate ALL edited files before finishing. Axiom-audit each rewired theorem.`, {
    label: `wire${i+1}:${b.name.slice(0,28)}`, phase: 'Wire',
    schema: { type: 'object', required: ['validated','summary','rewired','blockers'], properties: { validated: {type:'boolean'}, summary: {type:'string'}, rewired: {type:'array', items:{type:'string'}}, blockers: {type:'string'} } }
  })
  if (!res) { failed = `brick ${i+1} agent died`; break }
  results.push(res)
  progress += `\n\nBrick ${i+1} ("${b.name}") ${res.validated ? 'VALIDATED' : 'NOT validated'}: ${res.summary}\nRewired: ${res.rewired.join(', ')}\nBlockers: ${res.blockers}`
  log(`Wire ${i+1}/${api.bricks.length} ${res.validated ? 'OK' : 'INCOMPLETE'}: ${b.name}`)
  if (!res.validated && results.length >= 2 && !results[results.length-2].validated) { failed = `two consecutive bricks failed: ${res.blockers}`; break }
}

phase('Package')
let pkg = null
if (results.some(r => r.validated)) {
  pkg = await agent(`Package agent for the #313 plumbing wave.
${PROTOCOL}

Lane state:
${progress}

Tasks: enumerate changed files (git status/diff in ${WT}); 'lake env lean' every changed file sequentially (all must exit 0); axiom-audit every rewired theorem via temporary scratch probe (then delete it); hygiene scan the diff (no sorry/admit/axiom/conflict markers; linter caps respected); write ${WT}/_land_package.md with: files, rewired-theorem inventory (shell-hypothesis dropped per item), validation evidence, suggested commit message 'feat(#313): wire CoreInteractionPhase composition shells — <n> hypothesis surfaces dropped', draft issue comment for #313. Do NOT commit/push.`, {
    label: 'package:land-prep', phase: 'Package',
    schema: { type: 'object', required: ['ready','files','evidence','draft_comment'], properties: { ready: {type:'boolean'}, files: {type:'array', items:{type:'string'}}, evidence: {type:'string'}, draft_comment: {type:'string'} } }
  })
}

return { bricks: api.bricks.map(b => b.name), results, failed, package: pkg }
