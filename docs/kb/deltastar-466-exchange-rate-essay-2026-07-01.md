# The exchange rate of the wall — what closing Tier-1 item 5 teaches about δ* (#466)

Date: 2026-07-01. Companion to `deltastar-466-bgk-effective-half-plateau-2026-07-01.md` (the
Lean verdict, `Frontier/_BGKEffectiveHalfPlateau.lean`, commit `537959141`) and complementary to
the concurrent round-1 essay (`deltastar-466-essay-novel-mathematics-2026-07-01.md`, §2.1–2.5
machinery proposals). Written after this session and the concurrent session **independently**
reached the same structural verdict on the di Benedetto push (my brick's exact rationals; their
`probe_466_dibenedetto_push.py` dictionary section) — a genuine double-referee convergence.

## 1. Every method is a currency conversion, and the rates are now exact

The campaign's no-go landscape (Meta-Theorem, Tetrachotomy, AUP) says every known method caps
below the prize. Tier-1 item 5's closure sharpens this qualitative statement into a **ledger of
exchange rates**: each mechanism consumes a quantifiable input-depth (the order of additive
energy / moment / multilinear data it needs as input) and delivers a sup-norm saving; the ratio
is now machine-checked at β = 4:

| mechanism | depth consumed | saving delivered | rate quality |
|---|---|---|---|
| pure moment ladder at depth r | r (OPEN for r ≥ ~4) | `(r−3)/(2r)` | **the optimum** — → 1/2 as r → ∞ |
| trilinear sum-product (2003.06165) | {2, 3} (proven, good primes) | ≤ `1/24` (input-slot ceiling, in-tree) | ≈ 1/3 of a moment step |
| iterated sum-product (BGK/Shkredov Cor 16) | `2^k = 4096` at β=4 | `1/2^{k+2} = 1/16384` | **4000× below** the moment rate at equal depth |
| Stepanov/HBK | — | 0 below `p^{1/3}` | vacuous at β = 4 |
| Weil / completion | — | negative (√q ≫ n) | vacuous at thin n |

Two structural laws fall out, both now verified from two independent directions:

* **The moment rate is the ceiling.** The concurrent probe's "dictionary" shows the multilinear
  Bourgain-chain with *perfect* energies at arity s reproduces `θ(s,β) = (β+s−1)/(2s)` exactly —
  the multilinear rounds only trade unavailable deep energies for shallow proven ones. My brick
  shows the same from the constants side: no legal energy input beats `1/24` in the trilinear
  slots, and iteration *collapses* the rate (each squaring halves the remaining yield) rather
  than amplifying it.
* **Structural indirection is exponentially expensive.** The BGK cascade's `2^k` energy depth
  buys `2^{−k−2}` saving: the exchange rate degrades doubly exponentially in the number of
  sum-product rounds. The "o(1) is ineffective" folklore is now two exact integers: the clean
  applicability floor `2^{768}` vs the prize `2^{30}`, and the saving `1/16384` vs `1/2`.

**Refutable conjecture (Exchange-Rate Bound, gate-formalizable).** Any method at β = 4 whose
only analytic inputs are (i) additive energies `T_s`, `s ≤ S`, with any provable values, and
(ii) multilinear exponential-sum bounds with explicit constants, delivers sup-norm saving at
most `max((S−3)/(2S), 1/24)`. Falsifying this with an explicit mechanism would itself be a
SOTA breakthrough; every mechanism in the 2024–2026 sweeps satisfies it.

## 2. The all-or-nothing re-ranking (the practical import)

The in-tree rigidity `deltaStar_determination_all_or_nothing`
(`_DeltaStarBindingRigidity.lean`) says: in the prize regime there is **no partial interior** —
any sup-norm bound `n^{1/2+c}`, `c > 0` fixed, leaves δ* pinned at Johnson; only a bound at the
exact `√(n·log m)` scale moves it. Combined with the ledger above, this yields a re-ranking of
the live frontier that the dossier should adopt:

> **Exponent-pushing work on M is worth zero δ*-side even when it succeeds.** The entire
> "improve the power saving" axis (energies, multilinear lifts, sum-product iteration) cannot
> move δ* off Johnson at any achievable value of its own success metric. The only δ*-relevant
> open surfaces are the **exact/counting** ones, where the target is an integer or an exact
> rational, not an exponent:
> 1. the master-gap integer `m*` (δ* = (1−ρ) − m*/n) — exact-rational determination;
> 2. the line-list low-profile obligations (the weld's residual — a counting theorem);
> 3. the windowed SumsetExtremal crux (an extremality statement, not an exponent);
> 4. the Hankel/turnover seam **only in its exact form** (k* as an integer law, cf. the fresh
>    `probe_466_hankel_turnover.py` data), not as an exponent bound.

This is why re-landing the weld (`LineListMCAWeld`) matters more than any SOTA chase: it is the
one interface where a *finite counting theorem* (`Λ ≤ L ≲ ρn` on far lines) converts without
loss into the prize predicate.

## 3. What could actually beat the exchange rate — the non-energy inputs

The ledger's inputs are all second-order (energies = L² data). The tool-shape principle
(dossier §6) says a survivor must be L∞-control fed by second-order data — but the *conversion*
step is exactly where every method pays. The three known candidate inputs that are NOT energies:

* **Determinantal/positivity data** (Tier-1 item 3): the Jacobi coefficients `b_k` are exact
  functions of moments, but Hankel-PSD is a *constraint*, not a moment — the open question is
  whether positivity + the known exact low moments force the turnover `k*` into `O(log p)`.
  Honest status: pure positivity + low moments provably reproduces the moment bound (the
  moment-problem cap — an atom of mass 1/m at distance T is invisible to depth-r moments below
  `T ≈ (m·(2r−1)‼n^r)^{1/2r}`, the same `θ(r,β)`); so the seam needs the *spectral-shift*
  structure of the specific operator (the η's are eigenvalues of an explicit integer period
  matrix, not an arbitrary measure), which is exactly what no one has used.
* **Counting/fiber data** (the weld residual): `D(t)` fiber bounds for `t < k` on
  large-zero-safe lines — a polynomial-interpolation counting statement with no energy content.
* **Independence certification** (the §2.4 localization): the measured log-field is
  independent-Gaussian; certifying independence is a *joint-distribution* statement, strictly
  stronger than any single-moment bound — the chaining/γ₂ shape consumes it directly (the
  concurrent essay's §2.1 sharpens this to "chaining IS independence-certification").

## 4. Honest close

Nothing here moves CORE. The contribution is metrological: the wall now has a tariff table.
Every explicit mechanism's price is an exact rational; the optimum rate is the (open) Gaussian
one; partial exponent progress is formally worthless to δ*; and the frontier re-ranks toward
the exact/counting surfaces. The prize remains OPEN and ON-BGK.
