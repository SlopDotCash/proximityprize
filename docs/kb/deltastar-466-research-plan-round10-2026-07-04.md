# #466 Round 10 — research plan (2026-07-04): new angles on the LAST surface (the wall)

**State entering (dossier §19).** After 9 rounds (~90 agents), the surviving open surface is EXACTLY
ONE object: the analytic BGK/Paley wall, in its cleanest form

> **(WALL)** `W_r ≤ n^{2r}/p` at `r = β+1` — the wraparound count (sparse ±1 relations of the
> `2^μ`-th roots of unity vanishing mod p *beyond* the char-0 count `E_∞`) stays below its
> mean-field/DC prediction; equivalently `A_r ≤ K^r(2r−1)‼·n^r` at depth `r ≈ ln q`.

`W_r = E_r^(p) − E_∞ ≥ 0` is a **nonnegative integer count** (no magnitude cancellation to exploit —
signed-cancellation REFUTED, `_WallBetaPlusOneLocalization`). The wall is the recognized ≈25-year-open
thin-2-power square-root-cancellation problem. Every other route is decided (§4/§8/§14–19).

**Mission this round.** Per the goal directive ("if all theories refute … look for all new angles,
do more research, and repeat"): find angles on `W_r ≤ n^{2r}/p` that are NOT in the 18,000-line
DISPROOF_LOG or §8 dead ledger, develop each to a proof-gap or a machine refutation, fold honestly.
Bold in exploration; strict only in proof-claims; refutations-with-countermodels are wins. No
fabricated closure — the core stays a named open `Prop`.

## The genuinely-new angles (each checked absent from the dead ledger before launch)

### Lane A — Automatic-sequence / substitutive Fourier analysis of the dyadic-root phase sequence
**Idea.** For `n = 2^μ`, index the roots by `k ∈ Z/2^μ` via `x = ζ^k`, `ζ` a primitive `2^μ`-th root.
`W_r` counts `(k_1,…,k_{2r})` with `Σ ±ζ^{k_i} ≡ 0 (mod p)`. The phase sequence
`k ↦ e_p(b·ζ^k)` is governed by the **2-adic digit structure of k** — the exact setting of
2-automatic / substitutive sequences (Allouche–Shallit; Byszewski–Konieczny–Müllner 2020s Gowers-norm
and correlation bounds for automatic sequences). A nontrivial Gowers-`U^{2r}`-uniformity or
correlation-decay bound for this sequence would bound `W_r` below mean-field.
**Attack.** (1) Make the 2-automatic structure of `k ↦ ζ^k mod p` precise (is the phase sequence
genuinely automatic in p, or does the mod-p reduction break automaticity?). (2) Probe: measure
whether the wraparound solutions correlate with the 2-adic valuation / binary-digit structure of the
`k_i` (if `W_r` solutions are digit-structured, a substitutive bound bites; if digit-uniform, the
angle is b-blind and dies). (3) Check against the dead ledger's "dilation-invariance b-blindness"
(C1) — does the automatic structure survive the coset action, or collapse like every prior statistic?
**Kill criterion.** The wraparound solution set is equidistributed in the 2-adic digits of `(k_i)`
(⇒ automatic-sequence machinery sees nothing the moment method doesn't) OR the mod-p reduction
destroys automaticity (⇒ the tool doesn't apply). Either is a decisive, documentable verdict.

### Lane B — Transfer-operator / dynamical-zeta spectral gap on the exact tower recursion
**Idea.** The dyadic tower `μ_{2^μ} ⊃ μ_{2^{μ-1}} ⊃ …` gives `W_r` a self-similar recursive
structure (the "quartet tower law" is in-tree). Naive per-level √2-descent is REFUTED
(`no_sqrt_two_perLevel_thinning`, growth 1.74/1.54/1.46 > √2). BUT a naive multiplicative descent is
not a transfer operator: encode the wraparound generating function as a **dynamical zeta / transfer
operator** on the doubling map `x ↦ x²` (which is the tower step on μ), and ask whether its leading
eigenvalue / spectral GAP (not a per-level ratio) controls `W_r` asymptotically. A spectral gap below
the mean-field rate would give the wall; a gap AT the rate would prove the wall is tight-not-provable
by this method.
**Attack.** (1) Write the exact tower recursion for `W_r(2^μ)` in terms of `W_{≤r}(2^{μ−1})` (the
doubling-map pushforward). (2) Identify the transfer operator and compute its spectrum numerically at
small μ across ≥2 primes. (3) Decide: is the measured growth a transient converging to the mean-field
rate (wall true, gap = 0, method mute) or a genuine super-rate (would REFUTE the floor — a major
event, cross-check hard)?
**Kill criterion.** The tower "operator" is gauge (its spectrum is a reparameterization of the raw
moments — the Toda/isospectral kill `todaTurnover_not_determined_by_invariants` shape) OR the growth
is a bounded transient (wall true, method mute).

### Lane C — Literature freshness sweep (2024-2026), thin-subgroup √-cancellation + new tools
Targeted sweep for any 2024–2026 result that (i) moves `n^{1−o(1)}` toward `√n` for thin 2-power
multiplicative subgroups, or (ii) supplies a Gowers-norm / automatic-sequence / additive-energy bound
usable at depth `r ≈ ln q`. Cross every hit against the foreclosure ledger (BGK-only survivor; HBK
vacuous below `p^{1/3}`; di Benedetto boundary-vacuous; Paley conjecture open). Report the precise
missing transfer for each near-miss, or confirm the wall is untouched by 2024-2026.

## Verification protocol
Each lane's verdict independently re-checked by an adversarial skeptic: regime discipline (proper
`μ_n ⊊ F_p^×`, `p ≡ 1 mod n`, `p ≥ n^4`, ≥2 primes, exclude `X^{n/2}=±1`), b-blindness (does the new
statistic survive the coset action?), gauge/tautology (is the "new" operator a reparameterization of
moments?), circularity, and DISPROOF_LOG re-attempt. Lean claims: pg-iterate + axiom audit. Probe
verdicts need ≥2 primes and ≥2 octaves where feasible.

## Deliverables
Round-10 essay (`deltastar-466-essay-round10-*`): the wall as it now stands, the two new machineries
developed to their exact gap/death, an honest verdict on whether the surface is still exactly one
object. Dossier §20 round log. DISPROOF tags `466-r10-*`. #466 comment. Memory update.
Termination: both new angles DECIDED (gap or refutation), literature confirmed, dossier updated —
core stays OPEN unless a proof survives the full contract.
