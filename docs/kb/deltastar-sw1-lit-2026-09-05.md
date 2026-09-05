# SW1 lane LIT — literature and status refresh, 2026-07-01 → 2026-09-05

Lane: LIT (SW1 swarm, 2026-09-05). Classification of this note (dossier v4 §6 vocabulary):
**literature/status refresh — no theorem, no probe; open residual unchanged.** CORE OPEN / ON-BGK.

Question answered: has anything appeared since the v3 dossier (2026-07-01) that gives a genuinely
new tool for (i) the CORE — square-root-scale cancellation for thin `μ_n ⊂ F_p^×`, `n ≈ p^{0.19}`
(Paley / Bourgain–Konyagin subgroup-sum face), (ii) the rate-1/2 strip faces F1/F2/F3, or (iii) the
prize itself (statement, rules, or public solution claims)?

## 0. Executive verdict

1. **CORE: nothing.** Every 2026-07→09 paper on multiplicative subgroups is the Kalmynin /
   Hanson–Petridis "subgroups are not sumsets" structural cluster (exact classifications, no
   quantitative concentration or AP/arc certificate). No Gauss-period, generalized-Paley-eigenvalue,
   BGK, or di Benedetto et al. improvement. The doctrine-v2 "missing non-Fourier certificate" for
   `μ_n` in arcs is still absent from the literature.
2. **Prize LD face: ONE genuinely new tool.** ECCC TR26-164 (Brakensiek–Chen–Putterman–Zhang–Zheng,
   2026-09-04, rev. 1 2026-09-05): deterministic poly-time list decoding of plain RS over PRIME
   fields on EVERY evaluation set up to radius `1−R−δ` for every constant `R`, list
   `q^{O_{R,δ}(1)}`.
   Mechanism is non-Fourier (Hasse-derivative interpolation + Kopparty multiplicity decoder). It is
   asymptotic only — at `R=1/2` the "sufficiently large n" threshold is `≳ 10^{1000}` — so it is
   vacuous at `n = 2^30`, `ε* = 2^-128`, and it never touches the character-sum CORE.
3. **Prize MCA face: reduces-to-wall.** Jo, ePrint 2026/1432 (2026-07-13, rev. 08-19): `h` integer
   error steps beyond the exact Johnson boundary at fixed rate `1/r`, ANY domain, `O_{r,h}(K^6)` bad
   parameters (relative-radius gain `O(1/n)`); certified prize-format instance
   `Q = 2^256 − 255·2^128 + 1`, `K = 2^18`, all four rates, `ε_mca < 2^-128` at the first
   post-Johnson budget. The author states a constant-relative improvement on a prescribed smooth
   subgroup "remains open".
4. **Status.** proximityprize.org: statement, rates, `ε*` unchanged; no deadline; peer-review
   acceptance required; still "preliminary". ABF26 rev. 3 (2026-07-06) added Lemma 4.16
   (`ε_mca ≥ min{⌊δn⌋/|F|, 1}`) and concrete attack tables (rate-1/2 IRS: Elias `δ* ≈ 0.468`,
   antipodal-KKH `δ* ≈ 0.492` at `2^-128`). EF launched `better.codes` (2026-08-20) with the Lean
   repo `proximity-prize/proximity-prize` (profile koalaIRS12: `n = 2^18`, `ρ = 1/2`,
   `F = KoalaBear^6`): lower certificate 64.01 bits (user nasqret, PR #122, 2026-08-27, radius
   `307163/2^20 ≈ 0.29293`, i.e. ~10 positions past Johnson `0.29289`), upper 116.13 bits. No
   public claim of a prize solution was found; Chojecki (ePrint 2026/1463, 2026/1479, GitHub
   `przchojecki/rs-mca`) explicitly disclaims closure.
5. **F1/F2/F3:** nothing in the window touches Hilbert–Burch balance, strip syzygies, or union rank.
   Next concrete step (§5): a numbers-only probe of TR26-164 specialised to `μ_n`, `ρ = 1/2`.

## 1. What was searched (2026-09-05)

Web: WebSearch ×20 and direct listings — arXiv API (date-sorted) for "multiplicative subgroup(s)",
"Gauss period(s)/Gauss sums/Paley graph", "Reed-Solomon ∧ (proximity | correlated agreement |
list decoding)", "exponential/character sums ∧ (subgroup | prime field)", "additive energy /
sum-product / Bourgain ∧ finite field", "Paley ∧ (clique | eigenvalue | pseudorandom)",
"small/thin subgroups / Stepanov / Heath-Brown"; IACR ePrint search for "proximity gap",
"correlated agreement", "Reed-Solomon list decoding", "Johnson bound", "FRI soundness",
"multiplicative subgroup Reed-Solomon"; ECCC 2026 index; proximityprize.org (two reads);
blog.ethereum.org (better.codes); GitHub `proximity-prize/proximity-prize` (+ PR #122) and
`przchojecki/rs-mca`; ZK podcast #393; press coverage of the better.codes leaderboard. Full texts
read via pdftotext: ePrint 2026/1432, 2026/1463, 2026/680 (rev. 3), ECCC TR26-164 (v0 and rev. 1).

Ledger greps (`DISPROOF_LOG.md`, `docs/kb`, `docs/wiki`) run for every candidate before listing it
as new: `2026/1432`, `Sunghyeon`, `2026/1479`, `2026/1463`, `Chojecki`, `2026/1367`,
`Skatharoudis`, `2607.10572`, `Yiwen Gao`, `Gao`, `2025/870`, `2024/1810`, `2607.24270`, `Rudnev`,
`Tyrrell`, `2607.25711`, `2608.02568`, `Yip`, `Semin Yoo`, `2607.24370`, `2607.28559`, `Cochrane`,
`2602.04111`, `2602.20919`, `Kalmynin`, `Hanson`, `Petridis`, `2607.02392`, `Podest`, `Videla`,
`2604.06513`, `Darbar`, `2604.02960`, `Munsch`, `2604.03347`, `Gavalakis`, `2604.20233`, `Lewko`,
`Brakensiek`, `Putterman`, `Zihan Zhang`, `Kai Zhe Zheng`, `Yeyuan Chen`, `TR26-164`,
`low-rate regime`, `better.codes`, `koala`, `proximity-prize/proximity-prize`, `pull/122`,
`crowd-sourced`, `Wootters`, `Sun-Wootters`, `Cassuto`, `2607.08516`, `Kambir`, `2604.09724`,
`KKH`, `Haböck`, `Habock`, `2025/2110`, `2025/2197`, `2026/858`, `2026/861`, `2026/1055`,
`Mohnblatt`, `Okamoto`, `2025/1712`, `Randomstrasse`, `2603.29571`, `Pham`, `Thorner`, `Cilleruelo`,
`peer-review`, `podcast`, `Proth`. Zero-hit ids are marked "not in ledger" below.

## 2. Ranked findings

| # | item | date | face | verdict | ledger |
|---|---|---|---|---|---|
| 1 | ECCC TR26-164 (BCPZZ) | 09-04/05 | LD (prize) | NEW TOOL (asymptotic; vacuous at scale) | no |
| 2 | ePrint 2026/1432 (Jo) | 07-13/08-19 | MCA (prize) | reduces-to-wall (`O(1/n)` past J) | no |
| 3 | better.codes, GH repo, PR #122 | 08-20/08-27 | prize status | control-plane; no closure | no |
| 4 | ePrint 2026/680 rev. 3 (ABF26) | 07-06 | prize status | statement same; attack tables | v2 |
| 5 | arXiv 2607.10572 (Gao–Yang–Xu–Kan) | 07-12 | MCA ceilings | irrelevant (modified code) | no |
| 6 | ePrint 2026/1463, 1479, `rs-mca` | 07-17/20 | MCA (prize) | irrelevant (budget repack) | no |
| 7 | subgroup cluster (§3.7, five arXiv ids) | 07-27..08-03 | NT | irrelevant (structural) | mech |
| 8 | ePrint 2026/891 rev. (Jo) | 08-19 | interleaving | in-ledger (`[Jo26]`) | yes |
| 9 | arXiv 2607.02392 (Wu–Wang) | 07-02/06 | Gauss periods | in-ledger (depth-7 audit) | yes |
| 10 | ePrint 2026/1367, 2026/1371 (SoKs) | 07-02/03 | surveys | irrelevant | no |
| 11 | arXiv 2607.16541 (Jo, quantum) | 07-17 | algorithmic | irrelevant | no |

Pre-window items re-encountered and already ledgered (not re-audited): GGSW 2607.08516, Bordage–
Chiesa–Guan–Manzur 2025/2051 (CCC 2026), Kambiré 2604.09724, KKH 2026/782, Chai–Fan 2026/858,
2026/861, Darbar–Kerr–Munsch–Shparlinski 2604.02960, Podestá–Videla 2604.06513, Randomstrasse
2603.29571, Pham–Xue 2606.03627, Ma 2606.26440, Kalmynin 2504.10202, Cochrane 2602.04111,
Kim–Yip–Yoo 2602.20919, Fenzi–Sanso 2025/2197, Okamoto 2025/1712.

## 3. Item details

### 3.1 ECCC TR26-164 — Brakensiek, Chen, Putterman, Zhang, Zheng, "Algorithmic List Decoding of
Reed–Solomon Codes up to Capacity" (v0 title: "... in the Low-Rate Regime"), 2026-09-04, rev. 1
2026-09-05. https://eccc.weizmann.ac.il/report/2026/164/

Statement (read from the PDF, Thm 4.1 and Cor. 5.1). Thm 4.1: fix `n ≥ k ≥ 1`, `ε, θ ∈ (0,1)` with
`k > ⌈ε^{-3/θ}⌉`, `k/n ≤ (1−θ)ε`, `ε < (θ^3(1−θ)/768)^{(5+θ)/(1−θ)}`, and a prime
`q ≥ max(n, 4ε^{1−9/θ} n/k)`. Then for ANY distinct `α_1..α_n ∈ F_q` and any received word,
Algorithm 1 outputs in time `q^{O(ε^{-12/θ})}` the list of all `deg < k` polynomials with agreement
`≥ εn`, and the list has size `≤ q^{O(ε^{-3/θ})}`. Cor. 5.1 (all rates; reduction credited to
Alrabiah–Goyal–Guruswami, added in rev. 1): for every `R ∈ (0,1)`, `δ ∈ (0,1)` there is `C(R,δ)`
such that for `k/n ≤ R`, prime `q ≥ Cn`, any evaluation set, agreement `≥ (R+δ)n` is decodable in
`q^{O_{R,δ}(1)}` time with list `≤ q^{O_{R,δ}(1)}` (proof: pad to length `N = Θ(n)`, reduce to the
low-rate theorem). Technique: interpolate `Q(X, Y_0, …, Y_d)` with multiplicity `m = d^3` at each
received point using Hasse-derivative "Möbius inversion" `P(X) = Σ P^{[ℓ]}(X+T)(−T)^ℓ`, then
Kopparty's univariate-multiplicity list decoder. Prime field is used so that Hasse derivatives up to
order `d` behave (and so that the BKR subspace obstruction is absent). The authors say they were
inspired by the nasqret better.codes submission (item 3) and used an AI system to help produce the
results, with all proofs "independently verified by the authors".

Regime: prime `q ≥ Cn` (the campaign's `p ≈ n·2^128` qualifies), ANY domain incl. `μ_n`, every
constant rate, constant slack `δ` below capacity, worst-case (every received word).

Quantitative reality at prize scale (numbers-only, from Cor. 5.1's proof): `R = 1/2`, `δ = 0.1`
gives `θ = δ/(2(R+δ)) ≈ 0.083`, forcing `η < (θ^3(1−θ)/768)^{(5+θ)/(1−θ)} ≈ 10^{-34}` and
`k' ≥ η^{-3/θ} ≈ 10^{1200}`; the list bound `q^{O(η^{-3/θ})}` is astronomically above
`2^-128 |F|`. Consistent with KKH (list `≥ n^c` at slack `O(1/log n)`): the exponent must blow up as
`δ → 0`.

Verdict: **NEW TOOL** for the asymptotic Grand List-Decoding question (first beyond-Johnson, indeed
up-to-capacity, combinatorial list bound for plain RS on an arbitrary/structured domain over prime
fields); **not** a tool for CORE (no character sums anywhere; the mechanism is derivative
interpolation, so it says nothing about `Σ_{x∈μ_n} e_p(bx)`), and **vacuous** for production δ*.
Calibration for the doctrine: the campaign's foreclosure ledger concerns the *quantitative*
production statement; TR26-164 shows the *asymptotic* LD statement of ABF26 §3 is now positive over
prime fields by a route that never meets the Paley wall. It is exactly the "list-decoding advance"
the Meta-Theorem demands as a prerequisite for any Johnson-transcending MCA claim; whether it can be
quantified is open (see §5).

### 3.2 ePrint 2026/1432 — Sunghyeon Jo, "Reed–Solomon Mutual Correlated Agreement Beyond the
Johnson Radius", received 2026-07-13, revised 2026-08-19. https://eprint.iacr.org/2026/1432

Statement (Thm 1.1/3.3, Thm 5.1, Thm 5.2 read from the PDF). Fix `r ≥ 2`, `h ≥ 1`; for all
sufficiently large `K`, any `L ⊆ F_q` with `|L| = rK`, `C = RS_{<K}(F_q, L)`, error budget
`E = ⌊rK − √(rK(K−1))⌋ + h` (the `h`-th integer budget strictly above the exact Johnson boundary):
`B_C(E) = O_{r,h}(K^6)` bad parameters per affine line, hence `ε_mca(C,E) = O_{r,h}(K^6/q)`. Proof:
"agreement-set shortening" — shorten `t = t(r,h)` coordinates of a witnessing agreement set so the
shortened code is strictly below its own Johnson boundary, apply the deterministic BCHKS bound, and
pay the transfer factor `C(n,t)/C(T,t)` (bounded for constant `t`). A second, non-asymptotic
"MDS circuit-incidence" bound `B_C(E) ≤ min_a ⌊C(n,a)/C(T_eff−1,a−1)⌋` is exact when `n−E ≤ K+1`.
Certified rows: `Q = 2^256 − 255·2^128 + 1` (Proth prime, `v_2(Q−1) = 128`), `K = 2^18`,
`n = rK`, `L = H_n ⊂ F_Q^×`: first post-Johnson budget has `ε_mca < 2^-128` at rates 1/2 (`E =
153,562`, `t = 29`, `s_C > 128.05` bits), 1/4, 1/8 (also the second budget), 1/16. Four length-64
codes with exact `2^-128` crossings at consecutive integer budgets. Author's own scope (§1.2):
"certifies a fixed number of integer steps beyond Johnson, not a positive constant improvement in
relative radius … Obtaining a constant-relative improvement for Reed–Solomon codes on a prescribed
smooth subgroup remains open"; "no claim about list decoding or end-to-end protocol security".

Regime: any domain, fixed reciprocal-integer rate, `K → ∞`, worst case; gain `O(1/n)` in relative
radius; prize-format instance certified.

Verdict: **reduces-to-wall.** The shortening mechanism cannot move a constant fraction beyond
Johnson (the transfer factor becomes `2^{Θ(n)}`, which is exactly Chojecki's exponent `Ψ_ρ`, item
3.6), so the interior of the Johnson→capacity window — the campaign's object — is untouched. It is,
however, the first certified "beyond exact Johnson" point in prize format and a `[Jo26]`-adjacent
citation the ledger should carry (`2026/1432` had zero ledger hits).

### 3.3 better.codes / `proximity-prize/proximity-prize` / PR #122 (status)

- EF blog 2026-08-20 ("Raising machine-checked security benchmarks…", with Yukon and zkSecurity):
  an autoresearch challenge on the Lean-formalised (ArkLib) profile koalaIRS12 — the ABF26
  Construction-6.2 reduction-error threshold for one interleaved-RS profile — with a soundness track
  (raise the lower certificate) and an attack track (lower the upper certificate), target 128 bits.
- GitHub `proximity-prize/proximity-prize` (Apache-2.0; README: lower track "maximize B" by proving
  `certifiedGammaError(delta) ≤ epsilon*`, upper track by certifying `winningSetDensity(delta) >
  epsilon*`; baselines 53.00 / 128.00 bits; verifier profile `irs-reduction-threshold-v10`).
- PR #122 (merged 2026-08-27, `yukon-autoresearch[bot]`, co-author nasqret): 64.01-bit lower
  certificate; `n = 262,144 = 2^18`, `q = p^6`, `p = 2,130,706,433` (KoalaBear), dimension
  `131,072` (rate 1/2), radius `307,163/1,048,576 ≈ 0.29293` — "crosses the finite-distance Johnson
  boundary `1 − √(w/n)`" — list bound `Λ ≤ 10^17 ≈ 2^{56.5}` (`2^-128 q ≈ 2^58`). Press
  (2026-08-22):
  lower 63.99 → upper 116.13 bits, nine promoted submissions from seven solvers; the "December"
  date in press coverage is the EF zkEVM roadmap deliverable, not a prize deadline.

Assessment: an `O(1/n)`-beyond-Johnson certificate of the Jo type (~10 error positions past
Johnson at `n = 2^18`), machine-checked; no bearing on CORE; it fixes the public "state of the art
beyond Johnson on a smooth domain" at `≈ Johnson + 4·10^{-5}`. Note the profile's field is the
extension `F_{p^6}` with `L ⊂ F_p` — the Crites–Stewart base-field regime — not the campaign's
prime-field regime.

### 3.4 ePrint 2026/680 rev. 3 (ABF26, 2026-07-06; note: "Updated KKH comparison and concrete
estimate of attacks. Added MCA lowerbound.")

Grand MCA / LD challenge statements unchanged (smooth `L`, `ρ ∈ {1/2,1/4,1/8,1/16}`, `ε* = 2^-128`,
`k ≤ 2^40`, `|F| < 2^256`, "assuming |F| sufficiently large"). New Lemma 4.16: for any linear code
and `δ ∈ (0, δ_min)`, `ε_mca(C,δ) ≥ min{⌊δn⌋/|F|, 1}` (explicit two-word construction on `⌊δn⌋`
coordinates outside an information set). New §6.4 tables for the rate-1/2 IRS instantiation: Elias
lower bound forces `δ* ≈ 0.468` (Table 4), antipodal-KKH (Cor. C.6) `δ* ≈ 0.492` (Table 5) as the
smallest distances at which a `≥ 2^-128` soundness error is proved. These are ceilings already of
the campaign's `m_KKH26` type; the v3 dossier was consolidated from rev. 2 (2026-07-01), so the
rev. 3 deltas are not yet in the ledger. Verdict: status only; no new positive tool.

### 3.5 arXiv 2607.10572 — Gao, Yang, Xu, Kan, "List-Decoding Counterexamples Yield Lower Bounds on
Mutual Correlated Agreement Error", 2026-07-12. https://arxiv.org/abs/2607.10572

From an explicit `(p,L)`-list-decoding counterexample for a linear code over `F_q` they build a
code `C'` of the same length and dimension (minimum distance drops by `≤ 1`) with
`err_MCA(C',p) ≥ (1/q)⌈(L+1)q/(q+L)⌉`, with an explicit witnessing pair; AG specialisation
(same function field, adjusted places) and RS via Vandermonde columns. Regime: any radius where an
LD counterexample exists; worst case. Verdict: **irrelevant to CORE** and only adjacent to the
prize: the bound is for a *modified* code `C'`, not the given smooth-domain RS code, so it does not
sharpen KKH/Kambiré/CS ceilings for the prize instance. Not in ledger (`2607.10572`, `Yiwen Gao`
zero hits; the group's 2025/870 and 2024/1810 are ledgered).

### 3.6 ePrint 2026/1463 "Shortening Bounds for Reed-Solomon MCA" (2026-07-17), ePrint 2026/1479
"Conjectures and Barriers for RS-MCA" (2026-07-20), GitHub `przchojecki/rs-mca` — P. Chojecki

Read from the 1463 PDF. Thm 1.1: for `k_n/n → ρ`, `J_ρ < δ < 1−ρ`, `a_n = n − ⌊δn⌋`,
`limsup (1/n) log_2(1 + B^{MCA}(a_n)) ≤ Ψ_ρ(δ) := H_2(τ_ρ(δ)) − αH_2(τ_ρ(δ)/α)`, `Ψ_ρ(J_ρ) = 0`,
`Ψ_ρ(1−ρ) = H_2(ρ)` — i.e. an `2^{Ψ_ρ(δ) n}` (exponential-in-`n`) bad-parameter bound between
Johnson and capacity, obtained by optimising Jo's shortening over `t = Θ(n)` (the author credits Jo
for the transfer theorem). Thm 1.2 imports Jo's MDS envelope; Thm 1.4: if `2^-128|F| ≥ C(n,k+1)`
the official safe set is `[0,1]` (trivial counting saturation — the "four exact-plateau rows" and
the "128-bit circle certificate" `p_0 = 2^127−1`, `q = p_0^2`, Prop. 9.23 are of this kind at
length 512/64, where `C(n,k+1) ≪ |F|`). Cor. 1.10 states that for a fixed 128-bit target the
budget exponent is `λ = 0`, so the exponent machinery yields nothing at prize scale; the paper says
the "unrestricted subexponential-budget smooth/circle frontier remains open". 1479 is a list of
four conjectures plus a "moment obstruction"; the repo README: "does not claim to fully solve" the
prize, an experimental Lean track "should be reviewed … before any towards-prize claim is
advertised", best deployed-field attack `δ ≈ 0.4678` on KoalaBear sextic (matches ABF26 Table 4).
Credibility from the text: imported theorems are cited correctly; the novel parts are
entropy-exponent repackagings of Jo/BCHKS in idiosyncratic vocabulary ("payments", "atlas",
"compiler"); not peer reviewed; no false closure claim. Verdict: **irrelevant / reduces-to-wall**
(`2^{Ψ n}` vs the needed `2^-128|F|`); nothing for CORE.

### 3.7 The structural subgroup cluster (all new to the ledger by id; method already ledgered)

- Rudnev–Tyrrell, arXiv 2607.24270 (2026-07-27, rev. 08-12): if a proper subgroup `H = A + B` then
  a summand is a singleton or `|A| = |B| = 2`, `|H| = 4`; Hanson–Petridis polynomial method plus
  Kalmynin's `|A| = |B|` theorem as structural input.
- Yip–Yoo, arXiv 2607.25711 (07-28): which subgroups are restricted sumsets (sharp thresholds).
- Yoo, arXiv 2607.24370 (07-27): multiplicative irreducibility of `(G−1)∖{0}` in the extremal
  case "from a Stepanov bound in a prime field".
- Cochrane, arXiv 2607.28559 (07-30): sumsets and GAPs in subgroups (extends 2602.04111).
- Yip–Yoo, arXiv 2608.02568 (08-03): self-contained proof of the Kalmynin / Rudnev–Tyrrell
  classification.
Regime: proper subgroups of any order, exact decompositions, prime fields. Verdict: **irrelevant.**
These are exact-structure rigidity theorems, not concentration estimates; they give no bound on
`|μ_n ∩ P|` for an AP `P`, no energy bound, no Gauss-period bound. The underlying Stepanov /
Hanson–Petridis / Kalmynin differential-operator mechanism is already audited in the ledger
(`deltastar-444-arxiv-charp-sweep-new-papers-2026-06-21.md`) as a wraparound-onset certificate that
does not reach `M(μ_n)`.

### 3.8 Not new or not relevant (one line each)

- ePrint 2026/891 rev. 2026-08-19 (`[Jo26]`): acknowledgements/AI disclosure only; claims unchanged.
- arXiv 2607.02392 Wu–Wang (Gauss periods, cyclotomic matrices): identities/determinants; cited in
  the depth-7 per-prime audit (2026-07-11); no bound.
- ePrint 2026/1367, 2026/1371 (Skatharoudis SoKs): surveys of FRI/STIR/WHIR and small-field choice.
- arXiv 2607.16541 (Jo): quantum sampling from the Sun–Wootters distribution; algorithmic only.
- ePrint 2026/680 Table 1 restates the known ladder (`n·poly(1/η)/|F|` below Johnson; `n^{Ω(1)}/|F|`
  at `δ_min − Ω(1/log n)`); the window interior remains the open band.
- arXiv Paley/GP listings 2026-06→09 (2609.00462, 2608.24414, 2608.11211, 2606.07214): quantum
  symmetry, Petersen partitions, Conway 99-graph, Ramsey constructions — no eigenvalue/clique bound.
- ZK podcast #393 (2026-04-03) and the Fenzi "update" post are pre-window.

## 4. Prize statement / rules / claims — exact status 2026-09-05

- proximityprize.org: "$1,000,000 in total awards"; Grand MCA Challenge and Grand List Decoding
  Challenge exactly as in ABF26 (rates `{1/2,1/4,1/8,1/16}`, `ε* = 2^-128`, smooth `L`, constant
  `m`); submissions by email after "scientific peer-review in the form of acceptance to a reputable
  field-appropriate conference or journal", public ePrint/arXiv timestamp = submission date; Lean
  encouraged, not required; judges may deviate; prize may be split; no grant funding; no deadline;
  "The accompanying paper and problem statements are a preliminary version — details may still
  change." No news section, no winners, no listed submissions. Links added: better.codes, Yukon,
  zkSecurity. The ledger (`deltastar-DOSSIER-v3` §1.1) does not record the peer-review clause, so
  whether it is new since 2026-07-01 could not be determined from the ledger.
- Public solution claims in the window: none found on ePrint, arXiv, ECCC, GitHub, or press.
  The only "resolution"-titled item remains Okamoto 2025/1712 (pre-window, ledgered).

## 5. What remains / next lane

CORE OPEN / ON-BGK; literature floor for the analytic wall unchanged since the 2026-07-10 sweep.
One concrete, numbers-only unit for a next lane ("ECCC-quantify"):

1. Specialise TR26-164 Thm 4.1 / Cor. 5.1 to `L = μ_n`, `ρ = 1/2`, `n = 2^30`, prime
   `p ≈ n·2^128`, and compute the smallest admissible `(θ, η, k', N)` and the resulting list
   exponent; compare with `2^-128 p` (expected: over budget by `10^{≫1000}`, i.e. a refutation with
   numbers, to be filed as computational evidence, not a theorem).
2. Check whether ABF26 §5 (LD ⇒ MCA transfer, in-tree as `[ABF26] §5`) composed with TR26-164 gives
   any in-window MCA statement even asymptotically over prime fields; if yes, that is the first
   in-window positive statement for smooth domains and must be recorded as a conditional reduction.
3. Do NOT re-attempt: Jo-type shortening for constant-relative gains (2^{Ψ n} wall, §3.6);
   sumset-rigidity routes to arc concentration (§3.7).

## 6. References (new ids only; everything else is in dossier v3 §11.5)

| tag | id | what |
|---|---|---|
| [BCPZZ26] | ECCC TR26-164 (rev. 1 2026-09-05) | RS list decoding up to capacity, prime fields |
| [Jo26b] | ePrint 2026/1432 | MCA `h` integer steps beyond Johnson; certified `Q`, `K = 2^18` |
| [GYXK26] | arXiv 2607.10572 | MCA-error lower bounds from LD counterexamples (modified code) |
| [Cho26a/b] | ePrint 2026/1463, 2026/1479 | shortening exponent `Ψ_ρ`; conjectures |
| [ABF26-r3] | ePrint 2026/680 rev. 2026-07-06 | Lemma 4.16; attack tables 4–6 |
| [EF-bc] | blog.ethereum.org/2026/08/20/better-codes-challenge | koalaIRS12 leaderboard |
| [PP-gh] | github.com/proximity-prize/proximity-prize, PR #122 | 64.01-bit lower certificate |
| [RT26] | arXiv 2607.24270 | subgroups are not sumsets |
| [YY26a/b] | arXiv 2607.25711, 2608.02568 | restricted sumsets; self-contained classification |
| [Yoo26] | arXiv 2607.24370 | shifted-subgroup irreducibility, extremal case |
| [Coc26b] | arXiv 2607.28559 | sumsets and GAPs in subgroups |

## Verification addendum (independent re-check and repair, 2026-09-05 evening)

`scripts/pg-iterate.sh` was re-run on every `Frontier/_SW1_*.lean` file left untracked by the
SW1 round.  As left, only `_SW1_F3_MasterHypothesisVacuous.lean` and
`_SW1_TRANSV_HeightCeiling.lean` compiled; `_SW1_F1_UniformSylvesterRefuted.lean` (term-level
`X` captured by the trivariate `ArkLib.ProximityGap.X`, plus kernel deep recursion on the
`2^28` production instantiation), `_SW1_F3_UnionRankExact.lean` (a `simp`-shaped iff proof),
`_SW1_HD_HasseDavenportCosetLadder.lean` (unqualified `AddChar.FiniteField.primitiveChar_to_Complex`)
and `_SW1_SPARSE_RootLocusAverage.lean` (two tactic-shape failures) did not, and their headline
theorems fell back to `sorryAx`.  All four were repaired the same evening without changing any
statement (`Polynomial.X` qualification; a two-step `restrictQ_mkQ_eq_zero_iff`; the `AddChar`
namespace; `if_pos/if_neg` and `g ≠ 0` from the primitive root; explicit `congrArg` casts for the
`2^28` numerals).  All six files now compile with axioms `propext, Classical.choice, Quot.sound`
only, so every "axiom-clean" claim above is verified, including
`hrank_false_of_mcaEvent_witness`, `pairJoint_of_hrank`, `not_uniformSylvesterInjective`,
`coset_family_refutes_F1`, `coset_family_production` and `ladder_coset_pair`.
