# After round 1: what mathematics the prize now requires — a post-mortem essay (#466)

Companion to `deltastar-466-essay-novel-mathematics-2026-07-01.md` (the round-1 proposals) and
`deltastar-466-exchange-rate-essay-2026-07-01.md` (the tariff table). This essay records how
round 1's outcomes *change the shape of the missing mathematics*. Everything cited is in the
round-1 record (dossier §14, DISPROOF `466-r1-*`); everything prospective is labeled as such.

## 1. Three deaths, and what each one teaches

**The exponent axis is gone (Tier-1 #5).** The di Benedetto/BGK corpus — the only machinery
that ever engaged the real object with explicit constants — is now closed by three mutually
reinforcing results: the sound multilinear family is *optimal at the published parameters*
(nothing in the swept shape space beats `1 − 31/2880` at β = 4 with proven energies); its
perfect-energy envelope is *identically the moment ladder* (`θ(s,β) = (β+s−1)/(2s)`, an exact
dictionary — the chain is a preprocessor that trades unavailable deep energies for available
shallow ones); and its family infimum under the mass floor `T_k ≥ n^{2k}/p` is
`θ_min = 1 − 1/(2β) = 7/8`. The lesson is structural, not quantitative: **any method whose
output is a fixed power law is now known to be a reparameterization of the moment ladder**, and
the ladder's excess over 1/2 is exactly `(β−1)/(2r)` — the wall in one fraction. Novel
mathematics must therefore produce the `√(n·log)` *scale*, not an exponent; there is no longer
any such thing as "progress by a better exponent" on this problem.

**The bounded-window shortcut is gone (Tier-1 #3).** The Jacobi/Hankel seam survives only as
*global variance certification*: the early recurrence window is ensemble-deterministic
(`1 − q_j = c_j(n)/p` — it reads the prime's size, not its arithmetic), so no O(1) window of
moments can pin the turnover `k*` per-prime. What survives is diagnostic, not probative: the
b₃/b₄ coordinates amplify structured-prime anomalies ~50–1200× over matched raw moments, and
the spacing law `b_j² − b_{j−1}² ≤ (1+ε)·n` held on every instance. If a positivity-based
rigidity exists (CMK below), these are the coordinates it will be visible in.

**The monomial-extremality ansatz is gone (Tier-1 #1).** In-window, at every honestly
discriminating level tested, a two-Fourier-component direction beats every monomial — at three
primes across two v₂ classes, by a stable constant (~1.45×). The windowed SumsetExtremal
conjecture is false as stated. This is the round's most consequential *conceptual* death: the
picture "the adversary's optimal direction is a pure character, so the incidence problem IS
the character-sum problem, term by term" is wrong at the level of exact extremizers. The
identification of δ\* with the Paley object survives — it was proven through
direction-agnostic brackets — but the hoped-for *simplification* of the counting surface
(quantify over n monomials instead of q^n directions) does not exist. The counting surface is
genuinely high-dimensional at its extremes.

## 2. What the deaths jointly force

Combining the three with the standing no-go landscape (Meta-Theorem, Tetrachotomy, AUP,
γ₂-degeneration, vertical-MSS): a winning method must now
(i) produce the `√(n log)` scale directly (no exponent ladders);
(ii) use information beyond any bounded moment window (no Hankel shortcuts);
(iii) quantify over spread directions natively (no monomial reduction);
(iv) still be b-sensitive, deterministic, L∞, thinness-load-bearing.

Two shapes in the current record satisfy all four *in principle*:

**CMK ∘ TPS (the composition, still the best candidate).** The Christoffel–Markov–Krein
edge-crowding mechanism is positivity-based (not a moment window: it uses ALL moments plus
atomicity plus the Parseval mass floor jointly), scale-native (its conclusion is `M² ≤ C·n·log q`,
not a power), and b-blind-immune (it works on the spectral measure, where the sup IS the edge).
Its needed input is a Wick-type bound *with slack* (`K^r`, any constant K) at depth `log q` —
and the typical-prime sieve supplies slack-tolerant bounds precisely because its loss is a
constant-per-depth factor. Round 1 established the sieve's unconditional boundary is `r ≈ β`
(three independent derivations), so the composition's honest form is: **CMK must tolerate
moment inputs that are Wick-with-slack only up to depth β and trivial beyond.** Whether
positivity + atomicity + Parseval can propagate depth-β information to depth-log-q rigidity is
now THE sharpest well-posed open question the campaign owns. It is a question about abstract
moment problems — no arithmetic in it — and it is refutable by an explicit measure. (The
parallel session's lone-spike countermodel attempt is exactly the right first attack.)

**SST with support-orbit compression (the unused symmetry).** The wraparound count is a count
of sparse vectors in ideal-lattice sections; transference converts it to simultaneous
rational approximation of power vectors `(h^s)_{s∈S}` — and the dilation symmetry acts on the
*support sets* S, a symmetry no lane has ever consumed (every prior use of dilation acted on
frequencies, where it is cosmetic). If the orbit structure compresses the union over
`C(n, 2r)` sections below the union-bound cost, the sieve's depth boundary moves. This is the
one place a genuinely unused structural resource is known to sit.

**And the pure-counting route, reshaped.** With monomial extremality dead, the line-list stack
is more important, not less: it is the only machinery that never assumed anything about the
extremal direction. Round 1 turned its prize-facing weld into a real theorem
(`mcaDeltaStar_ge_of_farLineListBudgeted`, far-restriction proven necessary AND satisfiable —
aligned directions have zero bad scalars, so their maximal lists are harmless). Its residual
is now exactly two named objects: the far-line list budget `Λ ≤ L ≲ ρn`, and the large-zero
branch (low-profile `D(t)` fibers). The spread-excess finding *helps* here: the measured
excess is a constant, so a **bounded spread-excess law** (`worst_spread ≤ C·worst_mono`,
C ≤ 2) would restore everything the catalogue route needed, from a strictly weaker premise.
Round 2's W1/W2 lanes attack precisely these.

## 3. The honest scoreboard for "solutions and proofs that close the conjecture"

Every proof-shaped object currently on the table, with its exact gap:

| candidate closure | status of each step | the gap |
|---|---|---|
| CMK ∘ TPS | TPS boundary PROVEN-shape; CMK = open abstract-analysis conjecture | depth-β → depth-log-q propagation |
| SST + orbit compression | transference standard; orbit action well-defined | the compression estimate (untested) |
| weld + far-line budget + D(t) | weld PROVEN; budgets = named Props | the two counting theorems |
| spread-excess law + catalogue | law measured (C ≤ 1.56); catalogue sockets built | prove the law; rebuild catalogue over spread classes |
| n^{8/9} bilinear-DFT (SOTA push) | derivation drafted, skeptic-confirmed | good-prime conditional; and it is an exponent — cannot close (see §1) |
| independence certification (form A) | the wall itself | the wall |

None of these is close. The two that could *in principle* close (CMK∘TPS, SST) are new this
round and survive their first adversarial passes; the two counting theorems are the only ones
whose difficulty is not yet calibrated — they could be elementary or could be the wall in
disguise (the weld's circularity analysis in lane W2 will tell which).

## 4. Method note (why this round moved anything at all)

Round 1's yield came from one discipline applied uniformly: *state the hoped-for lemma
exactly, then spend equal effort on proof and refutation, with a machine adjudicating*. Five
of six sharp statements died — and each death deleted an entire class of future wasted effort
(exponent-pushing, spectral preprocessing, bounded windows, resonance dichotomies, monomial
catalogues), while each survivor emerged with a sharper, weaker, still-useful form. The prize
problem's difficulty is no longer diffuse: it is concentrated in four named objects (CMK
propagation, SST compression, far-line budget, D(t)), each with a designed attack. That
concentration — not any theorem — is the round's real product.

**The core is OPEN and ON-BGK.** Nothing here claims otherwise.

---

## ADDENDUM (same day, hours later): CMK is dead; the essay's own refutability paid off

Round 2's lone-spike countermodel (parallel session, `probe_466_cmk_lonespike.py` +
`probe_466b_cmk_countermeasure.py` + `Frontier/_R2B_CMKDepthIrreducibility.lean`) REFUTES the
abstract-moment form of CMK exactly as §2.2 of the round-1 essay invited: an equal-atom measure
with the Parseval mass and `K^r`-slack Wick moments to any depth can place a lone extreme spike
that REALIZES the full slack — abstract moment-problem rigidity (positivity + atomicity +
Parseval included) can never sharpen a `K^r`-slack input past `√(2K)`. **CMK dies as an
improvement lever, and CMK ∘ TPS dies with it.** Scope: only the abstract-moment form is killed;
a b_k-native variant consuming more than moments is untouched in principle — but the round-1
bounded-window refutation independently squeezes that. §3's table row is superseded accordingly;
what remains of §2's "two shapes" is SST (whose first dual-minima data — every section below the
random-lattice value — looks unfavorable; verdict pending) and the reshaped counting route,
which is now carrying the campaign. The method note in §4 stands: the proposal was stated
refutably, attacked immediately, and killed in under a day — that is the system working.
