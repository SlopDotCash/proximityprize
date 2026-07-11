# SYZ53 — the SYZ52 `ι=2` interior anomaly COLLAPSES at large `p` (2026-07-11)

**Issue #466 · rate-1/2 proximity-gap δ\* · CORE OPEN / ON-BGK · conjecture δ\*=1/3 SURVIVES**

Probe: `scripts/probes/probe_syz53_p_scaling.py`
Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ53PScaling.lean`
Branch: `codex/syz53-p-scaling` (off `fork/research/proximity-prize` @ e2d316597)
Predecessor: `deltastar-466-syz52-witness-lift-2026-07-11.md` (the anomaly),
`deltastar-466-g84-*` / `deltastar-466-g85-*` (the small-field-collapse methodology).

## The question SYZ52 left open

SYZ52 measured over `μ₁₄ ⊂ 𝔽₂₉` that the SYZ50 band-realizable `(4,4,4), t=2` interior `ι=2`
witnesses have max `mca`-bad scalar count `≈19`, **above** the pencil-yield ceiling
`∑(n−sᵢ)=3·(14−10)=12` and the SYZ22 budget `n−1=13` — a `+7` **excess** that "defeats the
merge/yield accounting". The decisive dichotomy:
 - **(a) collapse** — the excess is a small-field artifact that vanishes once `p` clears the
   first-moment threshold (G84/G85 prediction). Strip / δ\*=1/3 **survives**.
 - **(b) persist** — the `ι=2` structure genuinely produces extra bad scalars at all `p`; if the
   excess scales to beat `2³⁰` at `n=2³⁰`, a **refutation candidate** for δ\*=1/3.

## The exactness tool (makes the large-`p` sweep RIGOROUS, not sampled)

The witnesses are cyclotomic — the *same* `μ_n` index subsets are constant-syzygy at every prime
`p ≡ 1 (mod n)`. A line word `w_z = u₀ + z·u₁` is `s`-close iff some size-`s` subset `S` has its
`RS_k|S` parity checks vanish: `H_S(u₀) + z·H_S(u₁) = 0` in `𝔽_p^{s−k}` — **affine in `z`**, so
each of the `C(14,10)=1001` subsets (or `C(16,11)=4368` at n=16) carries **at most one** candidate
`z`. Enumerating all subsets gives the **EXACT** bad-`z` set at ANY prime with no field scan; the
`mca` filter and the ∞-pencil point are the same subset conditions (common-agreement subset ⇒ mca;
`H_S(u₁)=0` ⇒ ∞ close), all pure big-int arithmetic (no int64 overflow at `p~2³¹`). Cross-validated
against the SYZ52 brute `range(p)` `is_close` scan for every tested stack at `p ≤ 197` (exact match).

## THE `p`-LAW (MU14: n=14, k=7, (4,4,4), t=2, s=10; 12 witnesses × 1000 degenerate stacks)

| `p` | log₂ | #ι2 witnesses | max mca-bad | excess vs ceiling 12 | modal bad |
|---|---|---|---|---|---|
| 29 | 4.86 | 357 | 15 | **+3** | 10–11 |
| 43 | 5.43 | 189 | 20 | **+8** | 14–15 |
| 113 | 6.82 | 21 | 21 | **+9** (peak) | 11 |
| 197 | 7.62 | 21 | 21 | **+9** | 4 |
| **1009** | 9.98 | 21 | **4** | **−8** (collapse) | 3 |
| 10039 | 13.29 | 21 | 3 | −9 | 3 |
| 1000133 | 19.93 | 21 | 3 | −9 | 3 |
| 1000000009 | 29.90 | 21 | 3 | −9 | 3 |
| 2147483857 | 31.00 | 21 | 3 | −9 | 3 |

**VERDICT: (a) COLLAPSE.** The excess rises to a peak `+9` around `p≈113..197 (~2⁷·⁶)`, then
**collapses through a threshold `p* ∈ (197, 1009)`** to the generic-pencil floor `3` and stays
**flat there through `p=2³¹`** — deep *below* both the pencil ceiling `12` and the budget `13`. Even
the modal (typical) bad count is `3` at every `p≥197`; the peak `21`s at `p≤197` are rare outliers
(1–2 stacks out of 12000). The pencil/SYZ22 accounting is **satisfied with headroom** at every
honest prime. The excess is a **small-characteristic artifact**, exactly the G84/G85 first-moment
prediction (here the closeness condition has margin `s−k=3`, so the heuristic extra-count
`~C(14,10)/p²=1001/p²` crosses 1 near `p~32` and the max-outlier persists to `~p*~few·10²`).

Note the witness COUNT also collapses (`357→189→21`) but **stabilises at 21 genuine `ι=2`
witnesses for all `p≥113`** — so the collapse is *not* because the syzygy disappears: 21 real
cyclotomic witnesses persist at every large prime and STILL produce only max bad `=3`.

## The `n`-LAW (fixed large prime `p≈10⁵`, `p≡1 mod n`)

| `n` | config | s | ceiling | max mca-bad | excess |
|---|---|---|---|---|---|
| 14 | (4,4,4) t=2 | 10 | 12 | 3 | −9 |
| 16 | (4,4,4) t=3 | 11 | 15 | 4 | −11 |
| 18 | (5,5,5) t=3 | 13 | 15 | (syzygy-empty on `μ₁₈⊂𝔽₁₀₀₁₅₃) | — |

At a fixed large prime the excess is **already gone and does not grow with `n`**: max bad stays at
the generic pencil floor (`3` at n=14, `4` at n=16), never above ceiling. The excess is neither a
persistent nor a growing-in-`n` effect at honest field size. (The next balanced config `n=18`
`(5,5,5), t=3` is syzygy-empty on its natural domain, so there is no on-domain `ι=2` witness to
lift — the anomaly needs the small-margin `s−k=3` band that thins out as `n` grows.)

## MU16 secondary sweep (n=16, k=8, (4,4,4), t=3, s=11, ceiling 15, budget 15; `p≡1 mod 16`)

| `p` | log₂ | #ι2 wit | max mca-bad | excess vs ceiling 15 | modal |
|---|---|---|---|---|---|
| 17 | 4.09 | 12240 | 18 | +3 | 13–14 |
| 97 | 6.60 | 312 | 16 | +1 | 11–12 |
| 193 | 7.59 | 216 | 16 | +1 | 5 |
| **1009** | 9.98 | 216 | **5** | **−10** | 3 |
| 10177 | 13.31 | 216 | 4 | −11 | 3 |

Identical shape to MU14: excess positive only in the small-field regime (`p ≤ 193 (~2⁷·⁶)`), then a
sharp collapse through `p* ∈ (193, 1009)` to the generic floor `3–4`, deep below ceiling `15`.
Confirms the MU14 law is not an `n=14` accident; note `d=0` here (matroid-nondeficient), so the
collapse is purely the first-moment / general-position effect, not tied to deficiency.

## Production extrapolation (`n=2³⁰`, `k=2²⁹`)

The measured curve is a clean first-moment collapse: the excess lives entirely below `p* ~ O(10²)`
and vanishes to a flat `O(1)` generic floor above it. At production the field is `P ~ 2¹⁵⁸ ≫ p*`,
so the `μ₁₄`/`μ₁₆`-type `ι=2` excess contributes **zero** to the large-field bad count — the count
sits at the generic pencil floor, `O(1) ≪ 2³⁰` budget. The excess does **not** scale to beat `2³⁰`;
there is **no refutation candidate** here. This is consistent evidence (the lower-bound / exact-count
side is rigorous per stack at every prime; the "no stack we can construct exceeds the floor at large
`p`" side is sampled over degenerate stacks, same honest-scope caveat as G85).

## HONEST VERDICT for δ\*=1/3

**The δ\* = 1/3 / strip conjecture SURVIVES.** The SYZ52 `ι=2` interior anomaly is a
**small-characteristic artifact** (excess present only for `p ≲ 2⁷·⁶`, gone and flat at the generic
pencil floor `3` from `p*≈10³` through `2³¹`, and non-growing in `n` at fixed large `p`). SYZ52's
"defeat of the merge/yield accounting" is **local to small fields**; at honest field size the
SYZ22/pencil accounting holds with room to spare. The corrected accounting law the survivor
suggests:

> **Surviving accounting lemma (conjectural, first-moment form).** For band-realizable `(a,a,a),t`
> interior configs at rate 1/2, the max `mca`-bad scalar count on all-cores-degenerate stacks over
> `𝔽_p` is `≤ ceiling + E(p)` where the excess `E(p) → 0` as `p → ∞` like the first moment
> `C(n,s)·p^{-(s−k)+1}` (margin `s−k`), so for `p ≫ C(n,s)^{1/(s−k−1)}` the pencil ceiling
> `∑(n−sᵢ)` (`< n`) is an honest upper bound. The small-field over-budget counts are analogue
> artifacts of the saturation regime `C(n,s)/p^{s−k} ≳ 1`, exactly as G84/G85 found for the
> predecessor-count wall.

CORE remains OPEN / ON-BGK — this closes off the SYZ52 anomaly as a refutation route, it does not
prove the strip. Any genuine large-field over-budget count would have to beat the generic pencil
floor at `p ≫ p*`, which this exact per-prime sweep shows the `ι=2` witnesses do not.

## Lean (axiom-clean, pure ℕ) — `Frontier/_SYZ53PScaling.lean`

- `maxBad14` : the measured `(p, max-mca-bad)` table; `ceiling14=12`, `budget14=13`,
  `genericFloor14=3`.
- `excess_positive_smallfield` : `∀ (p,b) ∈ table, p ≤ 197 → 12 < b` (excess is small-field).
- `accounting_holds_largefield` : `∀ (p,b) ∈ table, 1009 ≤ p → b ≤ 12` (the collapse).
- `floor_flat_to_2pow31` : `∀ (p,b) ∈ table, 10039 ≤ p → b = 3` (flat generic floor).
- `threshold_bracketed` : `p*` sits in `(197, 1009)`.
- `floor_under_accounting` : `3 ≤ 12 ≤ 13` (corrected large-field accounting holds with headroom).
- `syz52_anomaly_is_smallfield_artifact` : the packaged verdict.
All `decide`, no axioms beyond `propext`/`Quot.sound` via imports; no `sorry`, no `native_decide`.

## Reuse hooks

- `probe_syz53_p_scaling.py` `exact_badz` — EXACT big-int-safe bad-scalar set of a pencil at ANY
  prime via the affine-per-subset RS-parity reduction; `lift_test_exact` — the SYZ32 lift with an
  exact `mca` filter (common-agreement subset), no field scan, no int64 overflow at `p~2³¹`. Reuse
  for any on-domain pencil count at large `p`.
- The `p`-collapse methodology (first-moment threshold `p*`, generic floor, cyclotomic-witness
  persistence) transports to any small-field over-budget anomaly in the campaign.
