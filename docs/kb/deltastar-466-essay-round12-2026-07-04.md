# #466 Round 12 — Essay: the frontal assault on the wall, and the machine-checked capstone certificate

**Date:** 2026-07-04. **Round:** 12 (Opus, two lanes, each adversarially verified).
**Bottom line:** after eleven rounds of no-go cartography the surviving open surface was already **exactly one
object** — the analytic BGK/Paley wall — with every escape route decided (dossier §21, Tetrachotomy, no fifth
door). Round 12 does **not** hunt for a twelfth door. It does two things instead: (Lane F) mounts a **frontal
attack ON the wall itself** via the norm/conjugate-count decomposition, and (Lane K) assembles the already-landed
in-tree bricks into a **machine-checked capstone certificate** that localizes the entire open prize to one named
`Prop`. Lane F **REDUCES-TO-WALL** at an exact, finite, machine-checked step; Lane K **compiles axiom-clean** and
certifies the localization, modulo one explicitly-named glue hypothesis. The wall is **not** claimed closed. It
remains a named open `Prop`, now with a cartographic reduction certificate wrapped around it.

---

## 1. Frame — a frontal attempt, not an escape

Fix `μ = 30`, `n = 2^μ = 2^{30}`, a prime `p ≡ 1 (mod n)` with `p ≈ n^4` (so `β ≈ 4`), and `μ_n = ⟨ζ⟩ ⊊ F_p^×`
the thin order-`n` multiplicative subgroup. The single surviving open core is

> **(WALL)   `W_r ≤ n^{2r}/p`   at   `r = β + 1`,**

where `W_r = E_r^{(p)} − E_∞ ≥ 0` is the **wraparound count**: the number of `(h_1…h_{2r}) ∈ μ_n^{2r}` whose
signed sum `α = Σ ε_i h_i` is a **nonzero** element of the degree-1 prime `𝔭 | p` (equivalently, a sparse `±1`
sum of `≤ 2r` `n`-th roots of unity whose algebraic norm `N(α)` is a nonzero multiple of `p`), minus the char-0
count `E_∞`. Every prior round decided a *method* trying to sidestep this object. Round 12 instead walks straight
at it from two directions and reports the exact obstruction each hits.

---

## 2. Lane F — the frontal norm/conjugate-count assault: REDUCES-TO-WALL, at an exact finite step

The one **unconditional** magnitude tool available on `W_r` is the conjugate/norm-count bound. For a `≤ 2r`-term
root-of-unity sum `α` in the cyclotomic field `K = ℚ(ζ_n)`,

> `|N(α)| ≤ (#terms)^{[K:ℚ]} = (2r)^{φ(n)} = (2r)^{n/2}`   (`φ(2^μ) = n/2`),

the in-tree `RootSumNorm.abs_norm_sum_rootsOfUnity_le`. A wraparound requires `α ≠ 0` and `p | N(α)`, hence
`|N(α)| ≥ p`; so **`(2r)^{n/2} < p ⟹ W_r = 0`** (the in-tree `no_wraparound_at_depth`). This is a genuine
sufficient condition — the frontal tool really does close the wall **wherever the gate fires**. The provable
reach is `r_gate(n,p) = ⌊½·p^{2/n}⌋`.

**What was achieved (the new exact-finite content).** Lane F pins, as an *exact finite arithmetic identity at the
prize point*, precisely where this gate is empty — and it is empty everywhere on the prize surface. At `p = n^4`
we have `p^{2/n} = n^{8/n} → 1`, so `r_gate` collapses `n=8 → 4`, `n=16 → 2`, `n=32 → 1`, and **`n ≥ 64 → 0`**.
The axiom-clean core (`Frontier/_FrontalConjugateGateCollapse.lean`) proves this as a `∀`-statement, not a
small-`n` sample:

- `sixteen_mul_pow_four_lt`: `16·k^4 < 2^k` for every `k ≥ 32` (clean induction; base `k=32` is
  `16·32^4 = 16777216 < 4294967296 = 2^{32}`).
- `two_pow_half_gt_n_pow_four`: for even `n ≥ 64`, `n^4 < 2^{n/2}` — i.e. the `r=1` norm-diameter bound already
  exceeds the prize modulus.
- `gate_vacuous_at_prize`: for even `n ≥ 64` and **every** `r ≥ 1`, `(2r)^{n/2} ≥ n^4`, so the sufficient
  condition `(2r)^{n/2} < p` **fails at every rung** — the norm bound is vacuous everywhere on the prize surface.
- `gate_vacuous_n64_r1`: the concrete checkable witness `2^{32} > 64^4`.

**The exact obstruction (why it REDUCES-TO-WALL).** For any `(n,p,r)` there is a clean dichotomy: EITHER the
conjugate-count gate closes it (`(2r)^{n/2} < p ⟹ W_r = 0`), OR one is in the post-gate region where the sole
open content is the phase-cancellation inequality `WallBetaPlusOne.WraparoundBelowDC` (`p·W_r ≤ n^{2r}`).
`gate_vacuous_at_prize` shows the first disjunct is **unreachable at the prize for every `r ≥ 1`**, so the entire
open region `1 ≤ r ≤ β+1` lies strictly past the gate. A magnitude-only argument provably **cannot enter** it:
the conjugate product `|N| = ∏|σ|` can exceed `p` even when no single conjugate `|σ|` is large; only
inter-conjugate **phase cancellation** (BGK/Paley) controls the count. This sharpens the pre-existing
asymptotic-in-`p` collapse (`_AvND_NormDiameterThreshold.threshold_lt_saddle`) into an *exact finite* boundary,
using the norm-count tool that predates this round.

**Honest Lane F verdict: REDUCES-TO-WALL.** No rung was proven at the prize; no new named glue was introduced.
The frontal norm/conjugate-count assault closes the wall exactly where `(2r)^{n/2} < p`, and that region is
empty for every `r ≥ 1` once `n ≥ 64`. The residual is *precisely* the un-gated `WraparoundBelowDC` inequality,
unchanged. No wall closure.

---

## 3. Lane K — the capstone: the machine-checked "one open Prop" certificate

Lane K assembles the landed in-tree bricks into one file (`Frontier/_WallCapstone.lean`) that **compiles
axiom-clean** — all three theorems `#print axioms = {propext, Classical.choice, Quot.sound}`, no `sorryAx`, no
`sorry`/`admit`/`native_decide` — and localizes the prize to a single named `Prop`.

**The one Prop, on the exact in-tree object.**

> **`WallHolds G := ∀ r, DCEnergyBound G r`**

`DCEnergyBound G r` is reused verbatim from `DCEnergyCorrection` (`q·E_r − |G|^{2r} ≤ q·(2r−1)‼·|G|^r`, i.e.
"the DC-subtracted wraparound is at most its mean-field DC value"). `WallHolds` is the `∀`-`r` closure of `W1`'s
`WraparoundBelowDC` — exactly the wall.

**What is machine-verified.** Two links, each a cited in-tree theorem doing real work:

- **Link 1 (`charSum_of_wallHolds`, PROVEN):** `WallHolds ⟹ ∀ r, ∀ b≠0, ‖η_b‖^{2r} ≤ q·(2r−1)‼·|G|^r`, via
  `DCEnergyCorrection.eta_pow_le_of_dcEnergyBound`. This is the *whole analytic payload* of the wall — it
  discharges the char-sum/energy control `M(n)` axiom-clean, with no open input beyond `WallHolds`. `hwall` is
  genuinely load-bearing here (the per-frequency Wick bound is not an unconditional theorem).
- **Link 2 (`deltaStar_floor_of_charSumBound_of_budget`, PROVEN reduction):** the char-sum bound `B` plus the
  named glue `RealizedIncidenceBudget` ⟹ `δ ≤ mcaDeltaStar C ε*`, via
  `CharSumDeltaStarBridge.le_mcaDeltaStar_of_charSumBound`. This reduction does real work (through
  `epsMCA_le_of_forall_badCount_le` and `le_mcaDeltaStar_of_good`), not a tautology.

The composite `wall_capstone` certifies the **conjunction** of (i) the per-frequency moment bound for every
rung (the wall's analytic payload, the sole consumer of `hwall`) and (ii) the `δ*`-floor from `B` and the glue.

**The one named glue — `RealizedIncidenceBudget` (NOT discharged by the wall).** This packages the two inputs
`le_mcaDeltaStar_of_charSumBound` consumes beyond the char-sum bound itself: the in-tree far-coset structural law
(`hStruct`, plumbing, not analytic content) and the **naive** incidence budget `hBudget`
(`⌈|G| + q·B⌉/q ≤ ε*`). Per the in-tree honesty notes, at the prize budget `q·ε* ≈ n ≈ |G|` the naive budget
forces `B ≈ 0`, so it is **vacuous at the prize for nonzero `B`**: closing it needs the strictly-finer
per-frequency `√q·B` cancellation (Paley-graph / BCHKS Conj 1.12), a different and finer object than the sup-norm
`B = M` the wall supplies. It is kept **explicitly named**, the project's modularity convention — not silently
discharged.

**Honest Lane K verdict: CAPSTONE-PARTIAL.** The wall `WallHolds` discharges the *analytic* half (the char-sum
bound) axiom-clean; the residual `M → δ*` glue is one further named object (`RealizedIncidenceBudget`) that the
wall does not by itself supply. Two honest caveats, both disclosed in-file: (a) the moment-order optimization that
turns the per-rung `2r`-power bounds into a single sup-norm `B` (take `2r`-th roots, minimize over `r ≈ ln q`) is
**not formalized** — `B`/`hB` is passed as a parameter, with the wall certifying the *moment inputs* to that
optimization; and (b) the two capstone conjuncts are not yet chained, so the file proves `WallHolds ⟹
moment-bound` **and** `glue + B ⟹ floor` as two facts glued by `∧`, rather than `wall ⟹ floor` end-to-end. The
prize is localized to `WallHolds ∧ RealizedIncidenceBudget`, machine-checked, with `WallHolds` the wall.

---

## 4. Honest final state after 12 rounds — the cartography is now CAPSTONED

After eleven rounds the no-go cartography was **complete**: the surviving open surface was exactly one object, the
analytic BGK/Paley wall, with every escape route decided. Round 12 leaves that verdict untouched and adds two
things:

1. **A frontal-attack certificate (Lane F).** The one unconditional magnitude tool (norm/conjugate-count) is
   proven — as an exact finite `∀`-statement — to be **vacuous at the prize at every rung** `r ≥ 1` once
   `n ≥ 64`. The wall is *exactly* the un-gated `WraparoundBelowDC` inequality, and no magnitude-only argument
   can enter it. This is a machine-checked statement of *why* the frontal route stops precisely at the wall.
2. **A machine-checked localization certificate (Lane K).** An axiom-clean capstone reduces the entire open prize
   to `WallHolds ∧ RealizedIncidenceBudget`, with the wall discharging the analytic payload and the one residual
   glue explicitly named (and honestly flagged prize-vacuous, requiring the separate `√q·B` incidence face of the
   *same* wall).

So the campaign's cartography is now not just complete but **capstoned**: the sole open core is a single named
`Prop` (`WallHolds`), the frontal magnitude route is machine-certified to bottom out exactly on it, and a
compiled certificate localizes the prize onto it. What remains is genuine, ≈25-year-open analytic number theory —
square-root cancellation for thin `2`-power subgroups (Paley Graph Conjecture; best proven at `β=4` is BGK
`n^{1−o(1)}`) — and it is untouched by any construction in this round.

---

## 5. Honesty contract

No fabricated closure. `WallHolds` is a **named open `Prop`**, carried as such. Nothing in Round 12 proves a rung
of the wall at the prize, discharges `WallHolds`, or silently closes `RealizedIncidenceBudget`; the named glue is
explicitly flagged vacuous-at-prize and pointed at the open `√q·B` cancellation. "Proven"/"axiom-clean" here
means exactly `#print axioms ⊆ {propext, Classical.choice, Quot.sound}` with no `sorryAx`, verified via
`scripts/pg-iterate.sh` on both files. Every other claim is labeled reduction, probe, or conjecture. The wall is
**not** claimed closed; the honest, expected, valuable outcome — "the frontal approach reduces to the wall at
this exact step, and the prize localizes to this exact one Prop" — is what was delivered.
