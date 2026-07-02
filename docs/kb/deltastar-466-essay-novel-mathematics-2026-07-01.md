# The mathematics that would close #466 — an essay on the missing machinery (round 1)

**Scope.** Dossier v3 reduces the prize to one inequality — `M(μ_n) ≤ C·√(n·log(p/n))` for the
dyadic subgroup `μ_n ⊂ F_p^×` at `n ≈ p^{1/4}`, equivalently the DC-subtracted Wick bound
`A_r ≤ K^r(2r−1)‼·n^r` at depth `r ≈ ln p`, equivalently `m*` in `δ* = (1−ρ) − m*/n`. This essay
does three things: (§1) states exactly what any winning mathematics must look like, as forced by
the proven no-go landscape; (§2) develops five NEW candidate machineries, each to its precise gap
or its precise death; (§3) states the refutable conjectures they generate, which round 1's probe
fleet and the follow-on lanes attack. Honesty contract: everything here is *proposal*; nothing is
claimed proven; several proposals are killed within this very essay, and that is their value.

---

## §1. The shape of a winning method (the forced constraints)

Any proof of the core must simultaneously (dossier §4, all machine-checked or double-refereed):

- **(C1) be b-sensitive** — dilation-invariant statistics are constant on the `m = (p−1)/n` cosets
  and cannot split the sup (killed: gap combinatorics, curvature counts, small-ball, zeta framings);
- **(C2) be deterministic-archimedean** — the period family is exchangeable with flat covariance
  `Cov(η_a,η_b) = −Var/(m−1)`, so no probabilistic-EVT structure (log-correlation, branching,
  Gumbel-with-fixed-K) exists to exploit (FHK killed by experiment);
- **(C3) be genuinely L∞** — every L², spectral, LP, SDP, energy-of-fixed-order functional caps at
  Johnson/√p (Meta-Theorem); the L²→L∞ collapse at `r ~ log n` IS the problem;
- **(C4) use thinness load-bearingly** — `Sh > √2` occurs only below β=4; a method blind to
  `n ≤ p^{1/4}` proves something false;
- **(C5) beat bounded complexity** — the object forces unbounded complexity on every classical
  tool (degree-`n/2` cyclotomic field, degree-`2^128` monomial lift, `(2w)^{n/4}` norm heights,
  flat 0-dimensional geometry);
- **(C6) respect the AUP** — a magnitude-only functional needs `√m` more phase information than
  it can carry; the winning method must *manufacture* phase coherence, not observe it.

The tool-shape principle (dossier §6): *an L∞/sup-control method fed by computable second-order
data*. §2 takes five different routes into that needle's eye.

---

## §2. Five new machineries, developed honestly

### §2.1 Chaining is exactly independence-certification (a sharpening, and a redirection)

Talagrand's γ₂ is the canonical L∞-from-increments tool: `E sup_b η_b ≲ γ₂(T, d)` when increments
`η_b − η_{b'}` are sub-Gaussian w.r.t. `d`. For iid-Gaussian-like fields on `m` points,
`γ₂ ≈ √(n log m)` — *numerically exactly the prize target*. So chaining "would" close the core.
What is the input? For any candidate metric: sub-Gaussian increments at scale `√n`. But the
increment second moments are FLAT (`E|η_b − η_{b'}|² ≈ 2n` for all pairs in distinct cosets — the
exchangeability kill C2), so the only admissible `d` is (a multiple of) the discrete metric, and
chaining on a discrete metric space of `m` points *is* the union bound, which *is* the per-period
sub-Gaussian tail to depth `log m`, which *is* form (A) verbatim. **Theorem-shaped conclusion
(provable, worth a gate brick):** on an exchangeable flat-covariance family, γ₂-chaining
degenerates to the union bound; its input is exactly the independence certification of dossier
§2.4. Chaining is not a route *around* the wall; it is the cleanest statement *of* the wall.
**Redirect:** the only way chaining becomes non-trivial is a *non-second-order* metric — a `d`
built from higher structure under which increments have *better-than-generic* tails. The one
candidate structure not killed by C1–C6 is the Jacobi/Hankel positivity data of §2.2.

### §2.2 Christoffel–Markov–Krein edge-crowding: a genuinely new rigidity mechanism

Form (D) treats the empirical spectral measure `μ_emp = (1/(q−1))Σ_{b≠0} δ_{η_b}` (real atoms,
`−1 ∈ μ_n`). The moment data (Wick to depth `2j`) is second-order — but *positivity* of the moment
problem is not. Two classical facts do real work here:

1. **Christoffel function bound.** Every atom of `μ_emp` has mass exactly ≥ `1/(q−1)`, and for ANY
   measure, the mass at a point `x` obeys `μ({x}) ≤ 1/K_j(x,x)`, `K_j(x,x) = Σ_{i≤j} p_i(x)²`
   (orthonormal polynomials of `μ` itself). Applied at `x = M`: `K_j(M, M) ≤ q−1`.
2. **Markov–Krein extremal principle.** Among all measures with the given first `2j` moments, the
   maximal support point is achieved by a canonical principal representation — the constraint is
   *quadrature*, not a single moment inequality.

If the moments were exactly Wick–Hermite to depth `2j`, then `p_i ≈` scaled Hermite and
`K_j(M,M) ≳ p_j(M)² ≈ M^{2j}/(n^j j!)` for `M ≫ √(nj)`, giving `M ≤ √n·(q·j!)^{1/(2j)}
≈ √(n·j)·q^{1/(2j)}/√e` — at `j ≈ log q` this is `≈ √(e n log q)·e^{−1/2}` — **the same order as
the moment bound but with an improved constant, and derived from strictly more information**
(all moments + positivity + the atomic mass floor, not one moment). The genuinely NEW mechanism
this machinery exposes is **edge crowding**: the Christoffel bound is *local*. If ONE atom sits at
`M`, positivity forces the Christoffel mass profile near `M`, and — this is the new refutable
claim — a *lonely* extreme atom is incompatible with Hermite-consistent bulk moments: near-edge
mass must be accompanied, quantitatively, by `Ω(K_j(M,M)/j)`-many neighbors, which then charge
Parseval (`Σ|η_b|² = n(q−n)`) and the fourth moment, closing a pincer that a single moment
inequality cannot. **Conjecture CMK (refutable):** for measures with `q−1` equal atoms, Parseval
mass `n(q−1)`, and moments within factor `K^r` of Wick to depth `2j = 2⌈log q⌉`, the largest atom
obeys `M² ≤ C(K)·n·log q` — *with the crowding argument supplying the step that the bare moment
bound loses*. Status: this is a THEOREM CANDIDATE about abstract moment problems — no arithmetic
in it. If true, it converts the (open) depth-`log q` Wick bound into the prize with an explicit
constant; it does NOT remove the arithmetic input (the moments themselves) — it would replace the
lossy `M^{2r} ≤ q·m_{2r}` step and could turn a *weaker*, `K^r`-slack Wick input into the sharp
target. Probe P4 measures its ingredients (`b_k`, `K_j` growth, near-edge crowding on real data).
**Kill risk:** the crowding constant may degrade with the atom count `q−1 ≫` everything,
reproducing exactly the union-bound loss (then CMK = form (A) again — to be determined *as
mathematics*, not numerics).

### §2.3 Sparse-section transference: the core as a cyclotomic-SIS statement

The wraparound count `W_r` is a lattice point count: relations `a ∈ Z^n`, `‖a‖₁ ≤ 2r`, entries in
`{0,±1}` (supports of the ±1-relation), lying in the **ideal lattice**
`L_𝔭 = ker(Z[x]/(x^n−1) → F_p, x ↦ h)` — the degree-1 prime `𝔭` of the cyclotomic order above
`p`. The prize (form A) says: `L_𝔭` contains *no more* sparse ±1 vectors than the Gaussian
heuristic predicts, up to `K^r`, for `r ≈ log p`. Fix a support `S`, `|S| = 2r ≪ n`: the section
`L_𝔭 ∩ Z^S` is a rank-`2r` lattice of covolume `p` (generically), and the ±1-points of the section
are exactly the wraparounds supported on `S`. **Banaszczyk transference** bounds the number of
short vectors of a lattice by the first minimum of its dual: here the dual section is generated by
`(1/p)·(h^{s})_{s∈S} + Z^S` — so the question becomes: *for how many supports `S` does the vector
of powers `(h^s)_{s∈S}` admit an unexpectedly good simultaneous rational approximation mod p?*
This is a **new, precise, refutable reformulation**: **Conjecture SST:** for all but a
`K^r`-controlled number of `2r`-subsets `S` of `Z/n`, the dual minimum of the section satisfies
`λ₁*(S) ≥ c·p^{−1/(2r)}·(random-lattice value)`. Machinery it imports: transference, counting in
section families, and — the genuinely new possibility — **averaging over sections is NOT the same
as averaging over frequencies** (C1 does not kill it: sections are index sets in `Z/n`, not
`b`-values; the dilation action permutes sections *nontrivially*). Kill risk: summing the
transference bound over all `C(n, 2r)` sections may reintroduce exactly the union-bound loss; the
interesting question is whether the *dilation orbit structure on supports* (an object never used
by any prior lane!) compresses the family. This is the one place in this essay where a symmetry
of the problem exists that NO prior route has consumed: the wall's dilation symmetry acts on
frequencies (used, cosmetic) AND on relation-supports (never used).

### §2.4 Vertical MSS (interlacing over the prime family) — developed to its exact death

The deployer/∃-form of the prize needs only ONE good prime per scale. Marcus–Spielman–Srivastava
prove existence results exactly this shape: if `{χ_p}` (characteristic polynomials of the Paley
adjacency operators over primes `p ≡ 1 mod n`, `p ∈ [X, 2X]`) formed an **interlacing family**,
some `p` would have `M(n,p) ≤ maxroot(E_p[χ_p])`. The expected polynomial's coefficients are
moment data over the family — computable from char-0 counts plus the average wraparound. Here is
the death, derived: the landed first-moment result (`E_p[W_r] ≈ n^{2r−4}/(2r)! ≫ Wick` — *the
average prime is bad*) forces `maxroot(E χ) ≫ √(n log p)`: the expected polynomial's deep moments
are dominated by the bad-prime tail, so even if interlacing held (no mechanism supplies it — no
signing/rank-one structure over the prime index), the guaranteed root is useless. **Sieved
variant:** restrict to primes avoiding the fixed-`r` bad-prime sets (finite per `r` — the
width-four machinery). The sieve must hold simultaneously for all `r ≤ log p`; the number of
resultants to avoid explodes as `n^{2r}` with heights `2^{O(n)}` — the conjugate-count no-go in
sieve clothing. **Verdict (essay-internal, to be gated):** vertical MSS is DEAD at both ends —
no interlacing mechanism, and the expectation is bad-prime-dominated. Worth a formal gate brick
(`_VerticalMSSGate`) recording both kills; its value is that it *also* kills every future
"average the characteristic polynomial over p" proposal in one stroke.

### §2.5 The typical-prime sieve and the median reformulation (the honest ∃-form frontier)

The first moment `E_p[W_r]` is bad, but the mass is carried by few primes: `W_r(p) =
Σ_relations 1[p ∣ N_a]`, and each nonzero resultant `N_a` has only `O(log N_a) = O(n)` prime
divisors spread over `π(X) ≈ X/log X` primes. Bookkeeping: `#relations(2r) ≈ n^{2r}/(r!·2^r)`-ish;
total divisibility mass `≈ #relations · ω(N) ≈ n^{2r}·n`; typical prime receives
`n^{2r+1}·log X/X`. At the prize diagonal `X = n^β`: typical `W_r ≈ n^{2r+1−β}·log n` vs Wick
`(2r−1)‼·n^r` — the typical prime is GOOD as long as `n^{r+1−β} ≪ r^r`, which holds for all
`r ≤ (β−1)·log n / log n = β−1`… and FAILS for `r` beyond `≈ β + r·(stuff)`: solving
`n^{2r+1−β} = n^r·r^{r}` gives failure onset at `r ≈ (β−1)·(log n)/(log n − log r)` — i.e. the
**typical-prime sieve closes depth up to `r ≈ β·(1+o(1))` and no further** — *matching the
DC-crossover and the fixed-`r` closures exactly, by an independent argument*.
**[CONFIRMED by probe, 2026-07-01: `scripts/probes/probe_466_tps_boundary.py` — with the most
sieve-optimistic bookkeeping, `r_cross = 4/5/6` at `β = 4/5/6`, stable across `n = 2^20…2^40`.
Three unrelated methods now place the unconditional boundary at `r ≈ β`.]** This is a clean,
NEW consistency check (worth recording): three unrelated methods (DC-crossover, moment-exponent
threshold θ(r,β), typical-prime sieve) all place the unconditional boundary at `r ≈ β`. Beyond it
the sieve needs the relation count to *not* concentrate its divisibility mass — equidistribution
of the prime divisors of structured cyclotomic resultants — a Duke/Linnik-type equidistribution
question on the Arakelov class group of `Q(ζ_n)`. **Conjecture TPS (refutable in principle):**
the divisor mass of `{N_a : ‖a‖₁ ≤ 2r}` equidistributes over primes `p ≡ 1 (mod n)`, `p ∈ [X,2X]`
up to `K^r` for `r ≤ c·log X`. This is *precisely* the ∃-form's remaining content, now stated as
an equidistribution-of-divisors problem rather than a character-sum problem. It is probably as
hard as the wall — but it is a *different* hardness (multiplicative structure of resultant
divisors vs additive cancellation), and no lane has ever attacked it as such.

---

## §3. The refutable conjecture list generated by this essay

| id | statement (informal) | attack | round-2 status (2026-07-01) |
|---|---|---|---|
| CMK | abstract moment-problem: equal-atom + Parseval + `K^r`-Wick-to-depth-`2log q` ⟹ `M² ≤ C(K)·n·log q` via Christoffel crowding | prove/refute as pure analysis; P4 measures ingredients | **DEAD** — lone-spike countermodel; DISPROOF `466-r2-cmk-lonespike-refuted` + `deltastar-466-cmk-refuted-2026-07-01.md` (see addendum) |
| SST | all-but-`K^r`-many `2r`-sections of `L_𝔭` have random-size dual minima; dilation orbit structure on supports compresses the union | probe dual minima at small n; then transference bookkeeping | **clarified-cosmetic** — orbit compression is exact factor-n bookkeeping; DISPROOF `466-r2-sst-orbit-compression-cosmetic` (see addendum) |
| γ₂-degeneration | on flat-covariance exchangeable families, γ₂ = union bound exactly | provable; gate brick | **machine-checked** — `_GammaTwoDegenerationGate.lean` (axiom-clean, round 1) |
| Vertical-MSS death | no interlacing + bad-prime-dominated expectation | gate brick `_VerticalMSSGate` | **machine-checked** — `_VerticalMSSGate.lean` (axiom-clean, round 1) |
| TPS | typical-prime sieve boundary at `r ≈ β` (provable); divisor-equidistribution beyond (open) | boundary: land as brick; beyond: named Prop | **boundary confirmed** — `probe_466_tps_boundary.py` (`r_cross = β` at β=4/5/6); the beyond-boundary equidistribution Prop stays open, but its CMK∘TPS consumer is dead (addendum) |
| CandidateListExactSuccessor, low-profile `D(t)`, windowed SumsetExtremal, Hankel short-window `k*` predictor | dossier Tier-1 carried forward | P4/P5 + Lean lanes | see dossier v3 §6/§14/§15 re-rank (windowed SumsetExtremal REFUTED at n=16; Hankel bounded-window REFUTED) |

**What would actually close the prize, in one sentence per route** *(round-2 note, 2026-07-01:
route (A) — including the CMK ∘ TPS composition — is DEAD; see the addendum below)*: (A) prove CMK *and* the
`K^r`-Wick input at depth `log q` (the latter is the wall unless CMK's slack tolerance `K^r` is
large enough to be suppliable by the typical-prime sieve at depth — the ONE genuinely new
composition this essay finds: **CMK ∘ TPS**: a constant-degrading Wick bound from sieve methods,
sharpened to the true edge by moment-problem rigidity — neither piece alone suffices; both are
stated refutably above); (B) prove SST with the support-orbit compression; (C) prove the windowed
SumsetExtremal + the line-list low-profile theorem (pure coding-theoretic route, no character
sums — the only route that never touches the analytic wall).

*2026-07-01, round 1. Everything above is proposal or derivation-to-kill; no closure is claimed.
Probes P1–P6 and the Lean lanes decide what survives this round.*

---

## Addendum — round-2 verdicts (2026-07-01)

The round-1 text above is preserved unedited except for status annotations in the §3 table and
the one inline note on the closing route list. Round 2 (dossier v3 §15) decided the essay's two
open proposals and machine-checked its two gate claims:

- **CMK (§2.2) is REFUTED.** The lone-spike countermodel (certified brackets, `q = 2^40…2^120`)
  shows the abstract equal-atom moment problem's sharp answer IS the raw moment bound,
  `C(K) = 2K(1+o(1))`: positivity + equal masses + full moment sequences add nothing, and the
  essay's Hermite–Christoffel constant computation was in error. The kill risk flagged in §2.2
  ("the crowding constant may degrade with the atom count… then CMK = form (A) again") is exactly
  what happened. Consequently the closing route **(A), CMK ∘ TPS, is DEAD** — the spike realizes
  the slack, so a `K^r`-lossy sieve input cannot be sharpened by moment-problem rigidity.
  Standing filter: any future "positivity upgrades a lossy moment input" proposal must first beat
  this countermodel. Citations: DISPROOF_LOG `466-r2-cmk-lonespike-refuted`,
  `docs/kb/deltastar-466-cmk-refuted-2026-07-01.md`; companion depth gate
  `Frontier/_R2B_CMKDepthIrreducibility.lean`.
- **SST (§2.3) is CLARIFIED-COSMETIC.** Orbit-constancy is provable (shift = unit multiple ⟹
  isometry), so the dilation-on-supports compression — the one "never-used symmetry" §2.3 hoped
  for — is exact factor-n bookkeeping, the SST analogue of the I031 cosmetic collapse. The bare
  conjecture as stated is FALSE at 2-power `n` without the antipodal `3^k−1` correction (dyadic
  Lam–Leung); the measured genuine char-p section defect is identically 0 at n=16 (exhaustive,
  r=2,3) and n=32 (full r=2 census). Surviving open residue: the multiplier action `S → kS`
  (not an isometry) cross-orbit correlation. Citation: DISPROOF_LOG
  `466-r2-sst-orbit-compression-cosmetic`.
- **γ₂-degeneration (§2.1) and vertical-MSS death (§2.4) are MACHINE-CHECKED** — landed as
  axiom-clean gate bricks `Frontier/_GammaTwoDegenerationGate.lean` and
  `Frontier/_VerticalMSSGate.lean` (round 1, dossier v3 §14(F)).
- **The TPS boundary (§2.5) is probe-confirmed** — `scripts/probes/probe_466_tps_boundary.py`
  gives `r_cross = 4/5/6` at `β = 4/5/6`, stable across `n = 2^20…2^40`; three independent
  methods (DC-crossover, moment-exponent θ, TPS) place the unconditional boundary at `r ≈ β`.
  The beyond-boundary divisor-equidistribution Prop remains open as a named conjecture, but its
  only proposed prize consumer (CMK ∘ TPS) is dead per the first bullet.

*Net effect on §3's closing routes: (A) dead; (B) survives only as the multiplier-action residue;
(C) is reshaped by the round-1 windowed-SumsetExtremal refutation into the bounded spread-excess
law at C=3 + the line-list low-profile obligations (dossier v3 §15 survivor list). No closure is
claimed; the core stays OPEN, ON-BGK.*
