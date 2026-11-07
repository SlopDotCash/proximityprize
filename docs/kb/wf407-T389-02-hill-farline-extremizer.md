# wf407 / T389-02-hill — worst-case far-line incidence: the true extremizer

**Verdict: PARTIAL/REFUTED-then-WALLED.** The thread's claim is **confirmed numerically**:
low-exponent / power-word directions are *non-extremal* — they are in fact the *worst*
(minimum-incidence) directions. The true extremal binding direction is a **HIGH monomial**
`X^{a*}` with `a* ≈ w` (the agreement threshold), i.e. `a* ∈ [n/2, n−3]`, **NOT** the
low-exponent `X^k`. **But this does NOT re-open the prize**: the §5.0/R4 workbench assumption is
"extremal direction is a *monomial* `X^a` (any exponent), by Z/n-dilation invariance" — which is
*proven* (`FarLineIncidenceEquivariance.explainableScalars_rs_rotate`) and **unaffected by which
exponent wins**. The "low-exponent `x^k`" phrasing in the thread is a misreading; correcting it
changes the *value* of `a*` but not the structure, and the worst-case far-line incidence still
terminates at the **same recognized open core** (explicit-smooth-RS sub-Johnson list-decoding bound;
walls W1/W4) already isolated in `DISPROOF_LOG` O161/O162/O163.

## What was measured (EXACT, two independent engines)

Object (`FarLineIncidenceEquivariance.lean`): for `C = RS[F_p, μ_n, k]`, direction `u1 = X^a`,
offset `u0 = X^b`, agreement threshold `w = ⌈(1−δ)n⌉`,
`I(dir(a,b)) = #{ γ ∈ F_p : maxAgree(u0 + γ·u1) ≥ w }`.

Two engines, cross-validated to the digit:
1. **Exact list-decode** (`wf407_T389-02-hill_v3.py`): per-γ max-agreement via all `k`-subset
   interpolation.
2. **Exact bad-scalar census** (`wf407_T389-02-hill_thin_v2.py`): per `w`-subset `S`, the unique
   `γ` with `X^b + γ·X^a` a degree-`<k` poly on `S` (divided-difference residuals linear in `γ`);
   `I =` |set of such `γ`|. Works at huge `p` (the thin regime).

### Toy gate `(n,k)=(12,6)`, `δ=1/4`, `w=9`, `p=13` — BOTH engines agree
| direction exp `a` | 6 (=k) | 7 | 8 | **9** | 10 | 11 |
|---|---|---|---|---|---|---|
| max `I` | 1 | 1 | 1 | **12** | 4 | 4 |

Best = `dir(9,8)`, `I=12 = n` (one full dilation orbit). Reproduces synthesis **O138**
(`(X⁹,X⁸)` extremal at (12,6)). Low exponent `a=k=6` gives `I=1` (minimum).

### THIN PRIZE REGIME `(n,k)=(16,8)`, `ρ=1/2`, `p=65537` (`>n⁴=65536`, so `n<p^{1/4}` ✓)
max incidence per direction-exponent `a` (`k=8`, `n/2=8`):

| `a` | 8 (=k) | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---|---|---|---|---|---|---|---|
| `w=9`  (deep) | **1** | 3280 | 9104 | 9536 | **9584** | 9536 | 9584 | 8288 |
| `w=10` (toward window) | **1** | 1 | **40** | 40 | 36 | 24 | 40 | 40 |
| `w=11` (near death radius) | **1** | 1 | 1 | 1 | **4** | 4 | 4 | 4 |

- **`w=9` (deep band):** best `dir(12,9)`/`dir(14,11)`, `I≈9584 ≈ 0.6·C(16,9)`; `a*=12=n−4`.
- **`w=10` (prize-relevant, `O(n)` regime):** best `dir(10,8)`, `I=40≈2.5n`; `a*=10=n−6`.
- **`w=11` (deeper in window):** best `dir(12,8)`, `I=4`; `a*=12`. Incidence collapses toward
  capacity (`9584 → 40 → 4` as `w: 9→10→11`) — the family dies inside the window (matches O140/O141).
- **The low exponent `a=k=8` (and all `a ≤ n/2`) gives `I=1` at EVERY window radius** — it is the
  *worst* (least binding) direction, the exact opposite of the "binding direction = `x^k`" framing.

**Law observed:** the binding exponents are the HIGH half `a ∈ (n/2, n−3]`; the argmax roughly
tracks the agreement threshold (`a* ≳ w`, e.g. `a*=12=w+1` at `w=11`, `a*=10=w` at `w=10`). Always
HIGH, never the rate exponent `k`. Adjacent (`m=1`) is extremal at some radii (toy `(12,6)`);
gap-2/3/4 at others (`(16,8)` `w=9,10,11`) — the "adjacent-pair" conjecture (synthesis O138) is
**not** radius-universal. Consistent with O175's deep-band maximizers `(x⁹,x¹¹)` at `(16,8)`,
`(x¹⁶,x²⁵)`/`(x¹⁷,x³¹)` at `n=32`.

## Why this does NOT re-open the prize (the honest part)

1. The dilation-equivariance lever (`explainableScalars_rs_rotate`, axiom-clean) says `I(δ)` is
   `Z/n`-invariant, so the *bad-scalar set is a union of dilation orbits* and the search may be
   restricted to dilation-fixed (= monomial) lines. **This is exactly as valid for `a=12` as for
   `a=8`.** The proof never used "low exponent"; it used "monomial". So correcting `a*` from `k` to
   `≈w` leaves R4 intact.
2. The far-line incidence in the deep band (`w=9`) is *exponential* (`~0.6·C(n,w)`); toward the
   window (`w=10`) it drops to `O(n)`. The δ*-pinning quantity is the **window-interior** incidence,
   which is `O(n)` and `q`-independent (matches workbench R4 "MEASURED: `O(n)`, `q`-independent") —
   bounding its worst case over directions is the open `O(1)`-coset rigidity conjecture (R4 GAP),
   identical to W1 (per-witness counting exhausted at `C(w−1,d+1)`) and W4 (the incidence/
   incomplete-Gauss-sum wall). Whether `a*=k` or `a*≈w`, the worst-case *value* is the same open
   object.
3. `DISPROOF_LOG` O161/O163 already refuted "power-word/monomial extremal" for the *max-list*
   object and showed the true extremizer is a "combinatorial densest codeword cluster" =
   explicit-RS sub-Johnson list-decoding bound (recognized open). This thread is the far-line-
   incidence face of the same fact.

## The one place the synthesis was internally WRONG (corrected here)

`RESEARCH_SYNTHESIS_407_CONNECTIONS.md` line ~720 calls the canonical extremizer `(x^k, x^{k−1})`
(LOW, rate-boundary). **That is false at every measured instance:** `(X^k, X^{k−1})` gives `I=1`;
the extremizer is `(X^{a*}, X^{b})` with `a*≈w ∈ [n/2, n−3]`. The workbench R4 text (line 154)
already says the cleanest case is `dir(k+1,k+2)` and "the worst non-correlated incidence is `O(n)`",
which is closer; but the exact argmax is `a*≈w`, higher than `k+1`, and radius-dependent. The
PGL₂-orbit attack at line 720 should compute the orbit of `(X^{a*}, X^{b*})` with `a*≈w`, not of
`(x^k,x^{k−1})`.

## Hill-climb over arbitrary words (Q2 — "binding family incomplete")

The thread's headline "hill-climb finds 2.3× higher (43 vs 19) than power-words" is the *max-list*
object (DISPROOF O12 found list 19 with 16 dense extras; O163 strong search beat power-words). For
the *far-line-incidence* object, the monomial-pair already saturates a full dilation orbit
(`I=n=12` at toy; `I=40` at `(16,8)` `w=10`), and arbitrary 2-row hill-climb did not exceed it in
the runs that completed (the full-field hill-climb at `(12,6)` is `O(p·C(n,k))` per move and timed
out — a *throughput* limit, not a finding). This is consistent with: monomial directions are
*extremal* for far-line incidence (dilation-fixed points maximize the orbit-union count), even
though they are *not* extremal for the un-symmetrized max-list. The two objects are **not**
equivalent: `LineCodewordIncidence.line_list_incidence_le` bounds far-line incidence by `⌊n/w⌋`
times the *line-union* list (codewords close to some point of the line), not by a point-centred
list around one received word, and no reduction between the two is proved (see that module's
docstring for an `F₇` example where the union list is `3` while every point-centred list is
at most `1`).

## Artifacts
- `scripts/probes/wf407_T389-02-hill_v3.py` — exact list-decode engine + monomial-pair scan
  (toy gate).
- `scripts/probes/wf407_T389-02-hill_thin_v2.py` — exact bad-scalar census, runs at `p=65537`
  (n=16 thin regime); the decisive per-exponent tables above.
- `scripts/probes/wf407_T389-02-hill_q2.py` — arbitrary-word hill-climb (throughput-limited).
- `scripts/probes/wf407_T389-02-hill_v2.py`, `..._farline_extremizer.py` (v1) — earlier slower
  drafts.

## What remains (new avenues)
- The exact law `a* = w` (argmax direction exponent equals the agreement threshold) is a *clean,
  provable, q-independent* statement — formalizable as: for `dir(a,b)` the bad-scalar census is
  maximized at `a = w`. A Lean brick proving `a*=w` would correctly re-aim the R4/PGL₂ extremizer
  search. (Conjecture, not yet proven; numerics 100% at the measured radii.)
- The window-interior worst-direction incidence (`w=10` row: max `40` at `dir(10,8)`) is the direct
  δ*-pinning quantity; its `O(n)`-coset rigidity is the open R4 GAP = W1/W4.
