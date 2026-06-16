export const meta = {
  name: 'mine-407-connections',
  description: 'Fan out lenses to mine 100+ insightful δ* connections (#407), dedup/filter ≥7/7/7, rank, write single markdown + JSON sidecar',
  phases: [
    { title: 'Mine', detail: 'one agent per lens finds candidate connections (≥7/7/7)' },
    { title: 'Synthesize', detail: 'dedup, filter, rank, write the single master file' },
  ],
}

// ---- shared grounding -------------------------------------------------------
const REPO = 'C:/Users/Administrator/arklib'
const ISSUE = 'scripts/probes/_issue407_full.md'  // full issue body + all 76 comments (pre-fetched)
const CONE = 'ArkLib/Data/CodingTheory/ProximityGap'

const FORMS = `
The "irreducible quantities that are all the same δ* wall, seen many ways" (tag each connection with the forms it touches; PREFER connections spanning >=2):
 F1  δ*  = the prize threshold sup{δ : I(δ) ≤ q·ε* ≈ n}
 F2  M(n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)|  (worst incomplete char sum = Gauss-period sup-norm; target ≲ C√(n·log(p/n)))
 F3  I(δ) = max far-line incidence = #bad scalars (γ : u0+γu1 δ-close to RS[k])
 F4  sub-Johnson list size of RS[k+1] / SuperCodeListBridge (the list-decoding grand challenge)
 F5  E_r(μ_n) additive energy / deep moments / cumulant κ_r sub-Wick
 F6  T_h tangent sum = (1/m)Σ_i J(χ^i,χ^h) average of Jacobi sums
 F7  Gauss-period family {η_i} decorrelation / joint sub-Gaussian variance n
 F8  2-adic descent / parallelogram tower  M(n)²≤2M(n/2)² ; cocycle large-deviation ∏r_j, r_j∈[√2,2]
 F9  Action-orbit count K (Chai-Fan 2026/861): bad-α = union of ⟨g^{b-a}⟩-orbits
 F10 Half-Sum Lemma / DyadicLacunaryFloor: #lacBad coset-quantized in units n/gcd(t,n); char-p antipodal vanishing-sum rigidity
 F11 cross-parity leak A≡−g·B mod q / fully-split N(𝔮)=q ideal-SVP short-L1 vectors of P|p in ℤ[ζ_{2^μ}] (Pan-Xu open split case)
 F12 e₂=0 algebraic rigidity / char-p resultant threshold c≈n³ (no BGK wall)
 F13 Bessel even-moment law E_r=(2r)![x^r]I₀(2√x)^{n/2}; odd-moment law Ση^{2k+1}=−n^{2k}; signed-unit-vector additive energy
 F14 sparse-support cyclic code C'_{a,b} list size (BCH/Hartmann-Tzeng/Roos toolbox)
 F15 Schur / complete-homogeneous vanishing: bad ⟺ ∃(k+1)-subset with h_{b-k}(x_S)=0 (cyclic sieving / hook-content)
 F16 N₀(G,r) additive relation count = Σ_b η_b^r/q ; Salem-Zygmund flatness of the Gauss-sum-phase DFT
 F17 NVM / Chebotarev nonvanishing-minors of the compressed Fourier matrix of μ_n (2310.09992; index 2,3 done, large open)
 F18 autocorrelation flatness: max Fourier coeff of r(h)=|μ_n∩(μ_n+h)| ≤ n·log(p/n)
 F19 effective Katz/Rojas-León equidistribution of the coset Gauss-sum family (conductor / monodromy = GL(1)^f, only HD relations)
 F20 constant-index √-cancellation lane (QR index-2, ConstantIndexGaussSumBound ‖η_b‖≤((m−1)√q+1)/m) and where it stops
`

const WALLS = `
The walls (tag connections that LINK two walls, or link a form to a wall in a new way):
 W-BGK     thin-subgroup √-cancellation / Paley graph conjecture (SOTA n^{0.989}, need n^{0.5}, 25-yr open)
 W-Johnson L² ceiling / n^{1/2} energy deficit (n^{2r}≤p·E_r forces (pE_r)^{1/2r}≥n, _MomentMethodNoGo)
 W-anomaly deep-moment char-p anomaly FORCED positive once qE_r^{char0}<n^{2r}, crossover r*≈β+1 ≪ log q
 W-Betti   AG/Deligne Betti/conductor growth: B_prim=((d−1)^{2r}+(d−1))/d, caps moment route at r=2
 W-subspace BCDZ25 Thm1.11 subspace-design quality d(k−d)/(s−d+1) VACUOUS at s=1 (plain RS) ⟹ folding necessary
 W-idealSVP Pan-Xu EUROCRYPT'21: cyclotomic ideal-SVP poly only for non-split q; fully-split N(𝔮)=q (the prize) explicitly open
 W-Mersenne BCHKS Conj 1.12 subgroup-sumset lower bound / "2^p−1 has a large prime factor"
 W-genericity HOMDS/GM-MDS generic (Schwartz-Zippel) vs the FIXED measure-zero μ_n (negation symmetry saturates Singleton)
 W-largesieve dimension obstruction: effective Deligne needs family dim f=(p−1)/n ≤ √q ⟺ n≥√p, but prize n≪√p
 W-LamLeung structure of W_p(m) in char p left explicitly open by Lam-Leung
`

const CONTEXT = `
You are mining INSIGHTFUL CONNECTIONS for the ArkLib Proximity-Gap Grand Prize, GitHub issue #407 (working dir ${REPO}).

== READ FIRST (primary grounding, pre-fetched) ==
- ${ISSUE}  — the FULL issue body + ALL 76 comments. Read the body (regime §0-8) and skim every comment; it is the single best map of the problem, the equivalent forms, the walls, and the dead routes.
- ${CONE}/RESEARCH_SYNTHESIS_407.md and RESEARCH_SYNTHESIS_407_TANGENT.md (if present)
- ${CONE}/DISPROOF_LOG.md — what is already REFUTED. A connection that merely re-proposes a refuted route scores LOW on relevance UNLESS it brings a genuinely new angle (then say why).
- docs/kb/deltastar-407-*.md — knowledge-base notes.
The cone has ~1562 .lean files under ${CONE}. Use Grep/Glob to FIND the real files for your lens (filenames in my hints may be on main, not this branch — verify before citing). Cite only files you confirm exist (Glob/Read).

== THE PRIZE REGIME (pin energy here; never validate on the full group n=q−1) ==
Dyadic FFT μ_n, n=2^μ a PROPER subgroup of F_q*, q=n^β prime with β≈4–5 (n≪√q, thin), constant rate ρ∈{1/2,1/4,1/8,1/16}, ε*=2^−128, budget q·ε*≈n. Window interior (1−√ρ, 1−ρ−Θ(1/log n)) ABOVE Johnson. Conjectured pin δ*=1−ρ−H(ρ)/(β log₂ n).

${FORMS}
${WALLS}

== WHAT COUNTS AS AN INSIGHTFUL CONNECTION ==
A connection is a NON-OBVIOUS structural link that does at least one of:
 (a) bridges >=2 of the forms F1..F20 by an exact identity, reduction, or shared invariant (BEST — the user explicitly wants multi-form links);
 (b) links two walls, or shows why one wall implies/illuminates another;
 (c) links in-tree CODE (a proven lemma / brick) to an open form in a way that could be leveraged;
 (d) exposes a hidden symmetry, quantization, or extremal structure that reframes the open core.
It is NOT just restating a known fact from the issue. Prefer connections that suggest a concrete attack.

== SCORING (rate 1-10 each; ONLY KEEP ideas that are >=7 on ALL THREE) ==
 - insight    : how non-obvious / how much it reveals hidden structure or reframes the problem.
 - research   : how much it could advance understanding, unify forms, or open a tractable sub-problem.
 - relevance  : directness to solving δ* or any underpinning quantity (a refuted-route rehash = low).
Be a harsh, honest grader. A 7 must be genuinely earned. Self-refuted/known-dead ideas: drop them.

== HONESTY CONTRACT (mandatory) ==
Never fabricate closure. These are CANDIDATE connections + attack plans, not proofs. Label honestly.
`

const MINE_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['lens', 'connections'],
  properties: {
    lens: { type: 'string' },
    connections: {
      type: 'array',
      items: {
        type: 'object',
        additionalProperties: false,
        required: ['title', 'forms', 'walls', 'code_files', 'connection', 'why_insightful', 'attack_plan', 'multiform', 'scores'],
        properties: {
          title: { type: 'string', description: 'one crisp line naming the connection' },
          forms: { type: 'array', items: { type: 'string' }, description: 'e.g. ["F2","F7","F16"]' },
          walls: { type: 'array', items: { type: 'string' }, description: 'e.g. ["W-BGK"] or []' },
          code_files: { type: 'array', items: { type: 'string' }, description: 'verified-existing in-tree .lean files (or [])' },
          connection: { type: 'string', description: '2-5 sentences: the exact link/identity/reduction. Be concrete and technical.' },
          why_insightful: { type: 'string', description: '1-3 sentences: why non-obvious / not already in the issue' },
          attack_plan: { type: 'string', description: 'concrete prove-or-refute plan: a probe to run, a Lean target, or a precise argument' },
          multiform: { type: 'boolean', description: 'true if it links >=2 forms' },
          scores: {
            type: 'object', additionalProperties: false,
            required: ['insight', 'research', 'relevance'],
            properties: {
              insight: { type: 'integer', minimum: 1, maximum: 10 },
              research: { type: 'integer', minimum: 1, maximum: 10 },
              relevance: { type: 'integer', minimum: 1, maximum: 10 },
            },
          },
        },
      },
    },
  },
}

// ---- the lenses -------------------------------------------------------------
const LENSES = [
  { key: 'charsum-gaussperiod', focus: 'Bridges between F2 (incomplete char-sum sup-norm), F7 (Gauss-period decorrelation), F16 (N₀ relation count / Salem-Zygmund flatness of the Gauss-phase DFT), and F18 (autocorrelation flatness). The exact duality η_b=(1/k)(−1+S_b); Σ_b|η_b|²=p−n; max-of-m-subgaussians = capacity gap. Hunt new exact identities tying these.', hint: 'SubgroupGaussSum*, GaussPeriod*, LineIncidenceSpectral, ShawOperator, SubgroupGaussSumWorstCase' },
  { key: 'energy-cumulant-bessel', focus: 'F5 (additive energy / cumulant κ_r) ↔ F13 (Bessel even/odd-moment law, signed-unit-vector additive energy) ↔ W-anomaly/W-Johnson. The signed-standard-basis picture μ_n={±e_j}; why E_r caps below diagonal at r*≈β+1; cumulant vs raw moment.', hint: 'DyadicEnergyK1, CharSumMomentDeepWall, AddEnergy*, GaussPeriodMomentBound, SubgroupGaussSum*Moment*' },
  { key: 'tangent-jacobi-katz', focus: 'F6 (tangent sum = Jacobi average) ↔ F19 (Katz/Rojas-León Gauss-sum joint independence, conductor/monodromy). The exact A_h=m·conj(τ_h)·T_h identity (Gauss sums perfectly flat ⟹ house carried by T_h). Effective vs q→∞.', hint: 'TangentSumJacobiAverage, MixedGaussSum*, QR*GaussSum, QuadraticGaussSum*' },
  { key: 'tower-parallelogram-cocycle', focus: 'F8: the 2-adic parallelogram recursion ‖η_b‖²+‖η^χ_b‖²=2(‖A‖²+‖B‖²), real-valuedness from negation symmetry, the cocycle ∏r_j large-deviation (r_j∈[√2,2]), why single-level submaximality fails but a path/Lyapunov bound might.', hint: 'GaussPeriodTower, DyadicHalvingRecursion, SubgroupQuadraticHalving, SubgroupPowerHalvingGeneral, Frontier/_Dyadic*' },
  { key: 'actionorbit-schur', focus: 'F9 (action-orbit count K) ↔ F15 (Schur/complete-homogeneous vanishing h_{b-k}(x_S)=0) ↔ F3. Orbit closure under γ↦g^{b-a}γ; K = dilation-orbit count of e-symm-vanishing subsets; O(1) above δ*, Θ(n) below; the crossover IS δ*.', hint: 'ActionOrbitFRI, MCAEigenstackOrbitLaw, GeneratorMCA, MonomialGammaFibration, EsymmFiber*, BadGammaAffineCount' },
  { key: 'halfsum-lacunary-charp', focus: 'F10 (Half-Sum Lemma, DyadicLacunaryFloor coset quantization, char-p vanishing-sum rigidity) ↔ F3. The char-free crux (all odd e_i=0 ⟹ S=−S); #lacBad ≡0 mod n/gcd; Newton e_t=±p_t/t; why this is off the analytic wall but = a Lam-Leung-open structure problem.', hint: 'DyadicLacunaryDeltaStar, SubgroupSumset*, LamLeung*, EvenOddAntipodal*, CyclotomicVanishing*, GVDvdSuccClosure' },
  { key: 'crossparity-idealSVP-mersenne', focus: 'F11 (cross-parity leak, fully-split ideal-SVP short-L1, r*=½λ₁^{L1,even}(P)) ↔ W-idealSVP ↔ W-Mersenne (Conj 1.12 subgroup sumset, big-prime-factor). The extremal relation α=c·ζ^e has norm c^{φ(n)} with only small prime factors ⟹ prize prime safe. Cyclotomic ideal-lattice / Ring-LWE.', hint: 'SubgroupSumsetLargeFactorReduction, CyclotomicResultantBound, Frontier/CyclotomicNormDefectThreshold, RootSumNormBound' },
  { key: 'e2-rigidity-algebraic', focus: 'F12 (e₂=0 rigidity, char-p resultant threshold) — the ONE face with no BGK wall. e1_eq_zero_of_neg_closed; bad locus {e₂=0,e₁≠0} is OUTSIDE cosets; threshold c=(n²+n)^{n/2} provable but true ≈n³. Connect to the cyclotomic-norm spectrum and to F10/F15.', hint: 'E2VanishRigidityModP, _E2NegationStructure, PairSumRigidityModP, BCHVarietyRigidity, MultiplicativeRigidity*' },
  { key: 'sparse-cyclic-code', focus: 'F14 (sparse-support cyclic code C\'_{a,b}, BCH/HT/Roos) ↔ F3/F4. min distance = window bottom (BCH tight); δ* = beyond-Johnson list growth of a dim-(k+2) cyclic code; whether sparse-structure list bounds beat generic.', hint: 'ReedSolomon*, JohnsonListBound, GSJohnsonWall, SubJohnson*, LineDecoding*, KrawtchoukPoly' },
  { key: 'listsize-supercode-mca', focus: 'F4 (SuperCodeListBridge, sub-Johnson list) ↔ F3 ↔ F1, and MCA=list-decoding collapse. The missing REVERSE bound (I(δ) lower bound matching the upper). interleaved LD⟹MCA circularity (needs Λ(C)≤O(1)).', hint: 'SuperCodeListBridge, MCAJohnsonAssembly, MCADeltaStar*, RSListThreshold*, EpsMCAInterleaved*, InterleavedListMCACollapse' },
  { key: 'johnson-extremevalue', focus: 'W-Johnson ↔ F7: variance(η_i)=n gives ONLY Johnson (the marginal 2nd moment); the capacity gap = max-of-m-decorrelated-periods (extreme value, NOT concentration). MDS-average E_line[I]=C(n,k+m)q^{1−m} astronomically below n ⟹ floor is a measure-zero outlier. Why no Chernoff/union bound bridges worst/avg.', hint: 'JohnsonListBound, JohnsonSecondMomentFrontier, LineSecondMomentSharp, MDSNearCountVolume, MCANearCapacity*' },
  { key: 'subspace-folding-wall', focus: 'W-subspace (BCDZ25 vacuity at s=1, folding necessity) ↔ F4 ↔ multiplicity codes (design-dim collapse τ(r)=1). The SECOND independent wall (Schubert-calculus codim) distinct from BGK. BCDZ25 Thm1.4: explicit folded RS already solves it ⟹ folding is the only gap.', hint: 'SubspaceDesign*, FoldedCurveCloseSetBound, Folding*, GranularityLadderRS, WindowedFolding*' },
  { key: 'anomaly-betti-walls', focus: 'W-anomaly ↔ W-Betti ↔ W-largesieve: three independent reasons the moment/AG/sieve routes die, and whether they share a root cause (rank n/2 lattice ≫ p; f≫√q over-dimension; Betti (d−1)^{2r}). Quantify the per-step deficits and compare crossover depths.', hint: 'CharSumMomentDeepWall, GaussPeriodMomentBound, Frontier/_MomentMethodNoGo, RootSumNormBound' },
  { key: 'equivariance-symmetry-thread', focus: 'The symmetry backbone: negation symmetry (−1=ζ^{n/2}∈μ_n ⟹ periods REAL), Z/n dilation equivariance (e_t(gS)=g^t e_t(S), extremal lines monomial), coset invariance, Frobenius/q≡1. How each symmetry pins/quantizes a different form (F2 real, F3 monomial, F8 tower, F10 coset units).', hint: 'MCAEquivariance, FarLineIncidenceEquivariance, CosetRigidity, RepCountCosetInvariance, GaussPeriodCosetReduction, MCAMonomialEquivariance, FrobeniusImmunityMuN' },
  { key: 'spectral-shaw-autocorr', focus: 'F2 ↔ F18 ↔ W-Johnson via the spectral/Parseval engine. LineIncidenceSpectral charSum_l2_pairing; Shaw operator 𝖲_D spectrum unifying the 7 faces; ShawFlatness ⟺ (R) ⟺ Shkredov wall; autocorrelation r(h) flatness. New: is there a Parseval identity making one face provable?', hint: 'LineIncidenceSpectral, ShawOperator, ShawSecondMoment, ShawFlatnessRefuted, AutocorrelationMax, PROXIMITY_PRIZE_WORKBENCH' },
  { key: 'stepanov-weil-pointcount', focus: 'F13/F19 ↔ point-counting substrate. Stepanov vs Weil regime; Bessel law = additive energy of signed unit vectors = central-binomial sum; modified-Fermat-variety point count (GLT) for E_r; where Stepanov (no Weil) could give a fixed-r theorem the AG route cannot.', hint: 'Stepanov*, WeilRegimeClosure, HasseWeilBoundInstances, GaussPeriodMomentBound, RepCountStepanov*' },
  { key: 'nvm-chebotarev-genericity', focus: 'F17 (NVM/Chebotarev nonvanishing-minors of μ_n compressed Fourier matrix) ↔ W-genericity ↔ F4. Generic GM-MDS (Schwartz-Zippel) CANNOT certify the fixed μ_n; the specific-subgroup NVM = Gauss-sum nonvanishing (index 2,3 done). Connect to e₂=0 (F12) resultant nonvanishing.', hint: 'HOMDSSmoothObstruction, MuTwoPowDerandRefutation, GWInterpolation, VandermondeMCAExtract, LovettSymbolicMinorDischarge' },
  { key: 'cross-issue-389-371-bridge', focus: 'Bridge LANDED #389/#371 results to #407 forms: energy↔character transport chain, sub-Johnson EXACT LINE (nodal cubic Θ(n^k)), all-witness ownership floor C(w−1,d+1), deep-band δ* pins, the 7-form master conjecture (μ_n Rigidity-Transport Law). Which #389 brick is reusable for a #407 form?', hint: 'RESEARCH_SYNTHESIS_389, AllWitnessOwnershipFloor, NodalSupplyGeneralK, DeepBand*, EnergyCharacterTransport, EnergyDilationReduction, SidonModNeg*' },
  { key: 'kkh26-staircase-saturation', focus: 'F1 concrete pins ↔ F3. KKH26 δ* pins (dim-one 1−2/2^μ, ceiling march (1−ρ)−1/n), the granularity staircase whose envelope is prizeDeltaStar, and the I_∞(δ) SATURATION mechanism: δ*(n)=I_∞^{-1}(n)=sup{δ:I_∞(δ)≤n}, a single-variable q- and n-independent cyclotomic function. Asymptotics of I_∞ near capacity.', hint: 'KKH26*, MCAStaircase*, GranularityLadderRS, Mu6DeepRung, DeltaStar*Pin*, interiorCeiling' },
  { key: 'curve-decodability-covering', focus: 'F4 ↔ F3 ↔ F10 via curve-decodability⟹MCA (closed in-tree by root counting, no char sum). The covering number = subgroup distinct r-fold subset-sum |μ_s^{(+r)}| at r≈log q. Why GG25 curve-degree is vacuous in the window; how the covering reduction relates to Half-Sum.', hint: 'GG25*, CurveDecodability, Frontier/CurveDecodability, Jo26*, CoveringFromFarCount, CoveringTransfer' },
  { key: 'within-MCA-structure', focus: 'PURE WITHIN-CODE: the MCA* family (~250 files). Find the structural skeleton — which MCA bricks are the generators (bracket, staircase, equivariance, orbit, second-moment, zero-code) and which are corollaries. Surface non-obvious dependencies/dualities (e.g. MCADualPencilLaw, MCAMobiusInversion, MCAEigenstackOrbitLaw) that could be leveraged for δ*.', hint: 'MCA* (Glob the cone), especially MCADeltaStar*, MCAStaircase*, MCAEigenstackOrbitLaw, MCADualPencilLaw, MCAMobiusInversion, MCASecondMoment, MCAZeroCode*' },
  { key: 'within-Hab25-CS25', focus: 'PURE WITHIN-CODE: the Hab25 capture-kernel cone (~60 files) and CS25 second-moment/ball-intersection cone (~50 files). Find where their reductions MEET δ*/the open core, shared lemmas, and any CS25 ball-intersection second-moment that secretly computes a form (e.g. F5/F7).', hint: 'Hab25*, CS25*, CS25SecondMoment*, CS25BallIntersection*, Hab25Capture*, Hab25Johnson*' },
  { key: 'constant-index-lane', focus: 'F20 ↔ F2 ↔ F19: the constant/polylog-index √-cancellation that IS proven (QR, ConstantIndexGaussSumBound ‖η_b‖≤((m−1)√q+1)/m via m·η_b=Σ gaussSum(χ^j,ψ_b)) and EXACTLY where/why it degrades to trivial √q at the prize growing index. Is there a hybrid (split the index into a proven constant part + a residual)?', hint: 'ConstantIndexGaussSumBound, QRWorstCaseIncompleteSum, SubgroupGaussSumWorstCase, norm_gaussSum_eq_sqrt' },
  { key: 'meta-cross-form-bridges', focus: 'META lens — explicitly hunt for NEW exact identities/reductions bridging >=3 forms that are NOT yet stated in the issue, supporting the thesis "they are all the same thing". Look for surprising equalities between a COUNT form (F3/F9/F10/F15) and an ANALYTIC form (F2/F6/F16) and an ALGEBRAIC form (F11/F12/F13). The "Rosetta stone" connections.', hint: 'RESEARCH_SYNTHESIS_407*, DISPROOF_LOG, docs/kb/deltastar-407-*, PROXIMITY_PRIZE_WORKBENCH, ReverseDictionary' },
]

// ---- phase 1: mine ----------------------------------------------------------
phase('Mine')
log(`Mining ${LENSES.length} lenses for δ* connections (target >=7/7/7, over-generate ~6-8 each)`)

const raw = (await parallel(LENSES.map((L) => () =>
  agent(
`${CONTEXT}

== YOUR LENS: ${L.key} ==
FOCUS: ${L.focus}
SEARCH HINTS (verify each with Glob/Grep before citing — many may be on main, not this branch): ${L.hint}

TASK:
1. Read ${ISSUE} (body + skim comments) for grounding, then Grep/Glob ${CONE} for your lens's real files and Read the most relevant 4-10.
2. Find as many INSIGHTFUL CONNECTIONS as you can that fit your lens and score >=7 on ALL THREE axes. Over-generate: aim for 6-8 strong ones; quality over quantity, but do not stop at 3 if more exist.
3. PREFER connections that link >=2 forms (set multiform=true). Be concrete and technical in each "connection" field — name the exact identity/reduction/invariant.
4. Each must have a concrete attack_plan (a probe you'd run, a Lean target, or a precise argument).
5. Grade harshly and honestly; drop anything below 7 on any axis. Drop pure rehashes of refuted routes (check DISPROOF_LOG) unless you bring a new angle (then explain).

Return ONLY the structured object {lens, connections}.`,
    { label: `mine:${L.key}`, phase: 'Mine', schema: MINE_SCHEMA }
  )
))).filter(Boolean)

const allConns = raw.flatMap((r) => (r && r.connections ? r.connections.map((c) => ({ ...c, lens: r.lens })) : []))
const qualifying = allConns.filter((c) => c.scores && c.scores.insight >= 7 && c.scores.research >= 7 && c.scores.relevance >= 7)
log(`Mined ${allConns.length} raw connections from ${raw.length} lenses; ${qualifying.length} pass the >=7/7/7 bar (pre-dedup)`)

// ---- phase 2: synthesize, dedup, rank, write the single file -----------------
phase('Synthesize')

const summary = await agent(
`${CONTEXT}

You are the SYNTHESIS + SCRIBE agent for issue #407. Below is the pooled set of ${qualifying.length} candidate connections (already pre-filtered to >=7 on all three axes) mined by ${raw.length} lens agents. Your job: dedup, rank, and WRITE the single master file.

POOLED CANDIDATES (JSON):
${JSON.stringify(qualifying)}

DO EXACTLY THIS:
1. DEDUP: merge near-duplicate connections (same underlying link from different lenses). When merging, keep the clearest phrasing, UNION the forms/walls/code_files, and keep the HIGHEST score on each axis (a link found by multiple lenses is corroborated). Assign each merged item a stable id C001, C002, ... .
2. FILTER: keep only items genuinely >=7 on all three axes after your own re-grade (you may demote an over-graded item below 7 and drop it — be honest).
3. RANK by total = insight+research+relevance, descending; tie-break by relevance, then insight.
4. SELECT: if >=100 qualify, keep the TOP 100. If <100 qualify, keep ALL and record the shortfall count clearly.
5. VERIFY code_files: drop any cited path you cannot confirm exists (quick Glob); it's fine to leave code_files empty.

THEN WRITE TWO FILES (use the Write tool):
A) Human master file at:  ${CONE}/RESEARCH_SYNTHESIS_407_CONNECTIONS.md
   Format:
   - H1 title + a 1-paragraph intro (what this is: 100 ranked δ* connections for #407, mined by N lenses, honesty contract).
   - A "Legend" listing the forms F1..F20 and walls used (brief).
   - A ranked table: | rank | id | total | I/R/Rel | multiform | forms | title |
   - Then one H3 section per connection IN RANK ORDER:
     ### C0xx — <title>   [total NN | insight N research N relevance N | multiform yes/no]
     **Forms:** ...  **Walls:** ...  **Code:** ...
     **Connection:** <the technical link>
     **Why insightful:** ...
     **Attack:** <prove-or-refute plan>
     **Verdict:** _pending_   (leave this literal placeholder; the attack phase fills it)
6) Machine sidecar at:  scripts/probes/_407_conn/connections_100.json
   A JSON array of {id, rank, total, scores:{insight,research,relevance}, multiform, forms, walls, code_files, title, connection, why_insightful, attack_plan}. This is consumed by the attack phase — make it valid JSON.

After writing, RETURN a short text summary: how many candidates pooled, how many after dedup, how many written (<=100), whether you hit 100 or fell short (and by how much), the score histogram of totals, and the two file paths.`,
  { label: 'synthesize+scribe', phase: 'Synthesize' }
)

return { pooledQualifying: qualifying.length, rawTotal: allConns.length, lenses: raw.length, summary }
