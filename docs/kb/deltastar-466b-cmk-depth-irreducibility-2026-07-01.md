# #466 round 2, lane CMK — the abstract moment-problem form of CMK is REFUTED (depth is irreducible)

**Date:** 2026-07-01 · **Lane:** round-2 CMK (round-1 outcomes §E survivor ⑥)
**Artifacts:** `scripts/probes/probe_466b_cmk_countermeasure.py` (+ `_out_466b_cmk_countermeasure.txt`),
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R2B_CMKDepthIrreducibility.lean` (axiom-clean,
5 gate theorems, pg-iterate ✅ 197s), this note.

## 1. The target

Round 1 left "CMK moment-problem rigidity" as the one new machinery not yet refuted
(`deltastar-466-round1-outcomes-2026-07-01.md` §E): the hoped-for abstract theorem

> **(CMK-abstract)** μ = (1/m)·Σᵢ δ_{xᵢ} with m equal real atoms; second moment pinned EXACTLY
> at Parseval, m₂ = P₂; Wick envelope |m_{2r}| ≤ K^r·(2r−1)‼·n^r for all r ≤ R
> ⟹ maxᵢ|xᵢ| ≤ C(K)·√(n·log m),

for some depth **R ≪ log m** (a depth reduction would shortcut the r ≈ ln q obligation of the
open core; the composition CMK ∘ TPS was "the round's one genuinely new closure shape").

## 2. The verdict: REFUTED at every depth R ≪ log m — depth is IRREDUCIBLE

**The refuting measure (symmetric 4-value, m equal atoms, repetitions allowed):** TWO edge atoms
at ±T (one each) and (m−2)/2 atoms at each of ±s, with s² = (m·P₂ − 2T²)/(m−2). Then:

- Parseval is **exact by construction** (m₂ = P₂ is an identity, not a tuning);
- **all odd moments vanish identically** (better than the true η-field, whose per-atom first
  moment is −n/(q−1)) — no odd-moment side constraint can rescue the theorem;
- it is an **actual positive measure**, so every implicit constraint of the moment problem
  (Hankel PSD, Krein conditions, Christoffel function bounds) holds automatically — the
  countermodel kills not just one proof strategy but ANY theorem consuming only these inputs;
- (m−2)/2 is a genuine integer at m = 2^128 and m = 2^40 (no parity fudge);
- the only active constraints on T are the even Wick envelopes r = 1..R, which admit
  **T ≈ √n·√(2R/e)·(m/2)^{1/(2R)}** — the factor m^{1/(2R)} blows up for R ≪ log m.

**Honest P₂** (pinned from the in-tree substrate, not the sketch's approximation): from
`GaussPeriodParsevalFloor.sum_sq_erase_zero` (Σ_{b≠0}‖η_b‖² = qn − n²) and coset-constancy of η
(q−1 = n·m frequencies, n per multiplicative coset), the per-atom second moment of the m-atom
coset-value measure is exactly **P₂ = n(q−n)/(q−1) = n − (n−1)/m** at q = n·m + 1.
(Envelope bookkeeping vs the in-tree DC-subtracted form: `DCSubtractedMoment.sum_nonzero_moment`
gives m_{2r} = q·A_r/(q−1) ≤ (q/(q−1))·K^r(2r−1)‼n^r — a 1 + 2^{−158} slack; verdicts identical.)

## 3. The prize-scale table (exact integer/rational arithmetic; floats display-only)

n = 2^30, m = 2^128 atoms (q = nm+1), P₂ = n − (n−1)/m exact. ln m certified in (88, 89) by an
exact rational series bracket for ln 2 (partial sums of Σ 1/(k·2^k) + geometric tail). Exceed
verdicts certified via T² > α²·n·89 (89 > ln m); the complement via T² < 16·n·88 (88 < ln m).
Tmax = maximal admissible edge (binary search on a CONVEX-in-T² feasible set, certified
ok(Tmax) ∧ ¬ok(Tmax+1)); "bind r" = first constraint violated at Tmax+1.

**K = 1:**

| R | Tmax (exact) | ~T/√(2n·ln m) | bind r | >2√(n ln m) | >4 | >8 |
|---|---|---|---|---|---|---|
| 4 | 3 519 089 267 | 8062.09 | 4 | YES | YES | YES |
| 8 | 19 909 218 | 45.61 | 8 | YES | YES | YES |
| 11 | 5 176 604 | **11.86** | 11 | YES | YES | **YES** |
| 22 | 982 456 | 2.251 | 22 | YES | no | no |
| 44 | 508 968 | 1.166 | 44 | no | no | no |
| 89 | 435 645 | 0.998 | 88 | no | no | no |
| 128 | 435 645 | 0.998 | 88 | no | no | no |
| 178 | 435 645 | 0.998 | 88 | no | no | no |

**K = 1.05 (= 21/20):** same shape (R=11: Tmax = 5 304 440, ratio 12.15; plateau 446 404 at
ratio 1.023, binding r = 88).

**Positive complement (exact):** at R = 178 ≥ 2·ln m, Tmax² < 16·n·88, i.e. the admissible edge
is back below 4·√(n·ln m) — recovering the KNOWN conditional moment bound at log depth
(`GaussPeriodMomentBound` / `prize_scale_bound_at_saddle`; cited, NOT re-landed). The binding
depth plateaus at r\* = 88 ≈ ln(m/2): the depth budget the abstract inputs require is exactly
the wall's r ≈ ln q — no gain.

**Small-r caution (orchestrator's check, decided):** no small-r cap exists. Per-single-constraint
caps at K=1: r=1 alone admits T ≈ 2^78.5 (r=1 is the Parseval identity itself, T-independent);
r=2 alone T = 2^47; r=3 alone T ≈ 2^36.8 — all orders above the prize scale. The constraint
genuinely binds only at r = R (for R ≲ 88).

**Sketch audit:** the orchestrator's sketch is CONFIRMED in all load-bearing respects
(m^{1/(2R)} blow-up; R=11 ratio ≈ 12; binds at r=R; no small-r cap; complement at log depth).
Two refinements made: (i) the 3-point {T, ±s} measure was replaced by the symmetric 4-value
{±T, ±s} measure — same arithmetic, but all odd moments vanish identically, closing the
"hidden odd-moment constraint" escape; (ii) P₂ was pinned to the exact in-tree value
n − (n−1)/m rather than n·(1 − n/q).

## 4. The Lean gate (axiom-clean, matches the probe's toy section verbatim)

`Frontier/_R2B_CMKDepthIrreducibility.lean`, instance n = 2^10, m = 2^40, R = 5 vs
⌈ln m⌉ = 28, T = 900, A = m·n − (n−1) − 2T² = 1125899905221601:

- `parseval_exact` — momentEven 1 = P₂ (exact identity in ℚ);
- `momentEven_wick_bound` — m_{2r} ≤ (2r−1)‼·n^r for all 1 ≤ r ≤ 5 (exact ℚ; tightest r=5 at
  slack 0.597);
- `log_mAtoms_lt_L` — Real.log m < 28 (via `Real.log_two_lt_d9`);
- `edge_exceeds_real` — 16·n·Real.log m < T² (i.e. T > 4√(n·ln m));
- `cmk_abstract_form_countermodel` — the packaged existential: ∃ edge/bulk configuration with
  exact Parseval + full depth-5 Wick envelope + edge² > 16·n·L.

All `#print axioms` = {propext, Classical.choice, Quot.sound}; 0 sorryAx.

## 5. Scope (honest) and fold-back

- **Killed:** ONLY the abstract-moment form of CMK — any theorem whose inputs are {m equal real
  atoms + exact Parseval + K^r-Wick-to-depth-R} (plus anything implied by being a measure:
  positivity, Hankel, Krein) with R ≪ log m. Also killed by composition: **CMK ∘ TPS** (TPS
  supplies only depth r ≈ β = O(1) ≪ log m — round-1 TPS-boundary probe).
- **Not touched:** a b_k-native (Jacobi-recurrence / Hankel-window) CMK variant consuming MORE
  than moments. That route is separately squeezed by round-1 P4 (no O(1)-window Hankel
  functional pins k\* per-prime; only the b₃/b₄ structured-prime sensitivity and the spacing law
  survive as constraints).
- **What a surviving CMK-shaped theorem must now consume:** input that distinguishes the true
  η-field from the 4-value countermeasure at depth ≤ R — i.e. NOT moments. Candidates are
  exactly the known open faces (independence certification / sub-Gaussian tails at depth
  r ≈ ln q), so "CMK rigidity" collapses back onto the wall.
- The open core (M(μ_n) ≤ C√(n·log(p/n)) at β ≈ 4, n = 2^30) is UNTOUCHED and OPEN.

**Fold-back for the survivor list:** round-1 survivor ⑥ "CMK moment-problem rigidity
(+ CMK∘TPS)" → **CLOSED (abstract form refuted by machine countermodel; composition dead;
b_k-native residue merges into survivor ③, the Hankel seam).**
