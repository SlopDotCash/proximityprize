# #466 Round 13 — Essay: tightening the capstone — is the wall ONE analytic statement or TWO?

**Date:** 2026-07-04. **Round:** 13 (Opus, two lanes — moment-order optimization + single-vs-two-Prop —
each adversarially verified by an independent skeptic).
**Bottom line:** Round 12 left the campaign at **CAPSTONE-PARTIAL**: an axiom-clean certificate
(`_WallCapstone.lean`) localizing the entire open prize to `WallHolds ∧ RealizedIncidenceBudget`, but with
**two honest caveats** — (a) the moment-order optimization turning the per-rung Wick family into a single
closed-form sup-norm bound was passed as an *un-formalized parameter* `B`/`hB`, and (b) it was left *open*
whether `RealizedIncidenceBudget` (the second conjunct) is a genuinely distinct input or merely a repackaging
of the wall. Round 13 **settles both**. It does **not** hunt for a new escape route — every door was decided
by round 12 (dossier §21, the Tetrachotomy). It **tightens** the partial capstone at exactly the two points
where it was still soft. Verdict on both lanes: **WORLD II — TWO DISTINCT INPUTS**. The prize localizes to
`WallHolds ∧ RealizedIncidenceBudget`, two irreducibly separate open Props, and neither the wall nor the prize
is claimed closed.

---

## 1. Frame — round 12 was CAPSTONE-PARTIAL; round 13 tightens, does not escape

Fix `μ = 30`, `n = 2^μ = 2^{30}`, a prime `p ≡ 1 (mod n)` with `p ≈ n^4` (so `β ≈ 4`), and `μ_n = ⟨ζ⟩ ⊊ F_p^×`
the thin order-`n` multiplicative subgroup. After twelve rounds the surviving open surface is **exactly one
analytic object** — the DC-subtracted char-`p` Wick wall — captured in-tree as the named Prop

> **`WallHolds G := ∀ r, DCEnergyCorrection.DCEnergyBound G r`**
>   ( `q·E_r(G) − |G|^{2r} ≤ q·(2r−1)‼·|G|^r` at every rung `r`, i.e. `A_r ≤ Wick_r`. )

Round 12's capstone `wall_capstone` (in `_WallCapstone.lean`) is a **conjunction** — so `WallHolds` is genuinely
load-bearing, not a passenger — proving

```
  WallHolds G  ⟹  (∀ r, ∀ b≠0, ‖η_b‖^{2r} ≤ q·Wick_r)   [charSum_of_wallHolds, axiom-clean]
                ∧  δ ≤ mcaDeltaStar C ε*                   [via the NAMED glue RealizedIncidenceBudget]
```

Two things were left honestly soft, and round 13 tightens each:

- **Lane M** attacks caveat (a): can the *closed-form* sup-norm bound `M ≤ C·√(n·log q)` be discharged
  **directly from `WallHolds`**, removing the un-formalized parameter `B`?
- **Lane R** (the crux) attacks caveat (b): does the prize localize to **`WallHolds` ALONE** (a single-Prop
  iff — *World I*, "the wall is one statement"), or does it genuinely need a **second, distinct** open input —
  the `√q·B` per-frequency hyperplane cancellation — that does **not** follow from the Wick bound
  (*World II*, "the wall is two statements")?

Both were attacked, formalized where formalizable, and adversarially reverified. Both land on **World II**.

---

## 2. Lane M — `WallHolds ⟹ M ≤ √(2e·n·(ln q + 1))` is now axiom-clean; caveat (a) is REMOVED

**Exact status: DONE, axiom-clean.** The round-12 parameter `B`/`hB` is gone. The file
`Frontier/_MomentOptimizedSupNorm.lean` lands the moment-order optimization **directly from the wall**, and
`Frontier/_MomentWallWiringCheck.lean` wires it into the capstone's `B`/`hB` slots end-to-end. Both verified
axiom-clean via `pg-iterate` this round (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`;
`_MomentWallWiringCheck` at 28 s, transitively certifying `_MomentOptimizedSupNorm` and `_WallCapstone`).

The optimization is elementary real analysis, cleanly isolated so no analytic step hides inside it:

1. **The per-rung wall bound** `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` (`eta_pow_le_of_dcEnergyBound`, in-tree,
   *unconditional* given `DCEnergyBound G r` — the analytic content lives entirely in that NAMED hypothesis,
   no circularity).
2. **Stirling-free double-factorial bound** `((2r−1)‼ : ℝ) ≤ (2r)^r` (`doubleFactorial_two_sub_one_le`, the one
   genuinely new arithmetic lemma, proved for the Mathlib `Nat.doubleFactorial` via the closed form
   `(2r−1)‼ = ∏_{i<r}(2i+1)` and factorwise monotonicity `2i+1 ≤ 2r`). Hand-checked at `r=1,2,3`: `1≤2`,
   `3≤16`, `15≤216`. Gives `‖η_b‖^{2r} ≤ q·(2nr)^r`.
3. **The saddle estimate** `sq_le_of_pow_ceil`: taking the `r`-th root of the square,
   `‖η_b‖² ≤ q^{1/r}·(2nr)`; choosing depth `r = ⌈ln q⌉ ≥ 1` gives `q^{1/r} = exp((ln q)/r) ≤ e`
   (since `r ≥ ln q`), hence `‖η_b‖² ≤ 2e·n·r ≤ 2e·n·(ln q + 1)`.
4. **Square root**: `‖η_b‖ ≤ √(2e·n·(ln q + 1))` — the Gaussian/Ramanujan target `M ≤ √(c·n·ln q)`,
   `c = 2e ≈ 5.44`.

The result `supNorm_le_of_wallHolds` supplies exactly the `∀ b ≠ 0, ‖η_b‖ ≤ B` that `wall_capstone` demanded as
a parameter; `wall_capstone_moment_closed` composes them so the **only** remaining hypotheses are the two open
Props `hwall : WallHolds G` and `hglue : RealizedIncidenceBudget …`, with `B` = the wall's own optimized
sup-norm. (The two `WallHolds` definitions are *definitionally* equal — `∀ r, DCEnergyBound G r` — so the
composition type-checks with no glue lemma.)

**Honest constant caveat (labeled, not laundered).** The Lean constant `C = √(2e) ≈ 2.33` is the *crude* saddle
value from `(2r−1)‼ ≤ (2r)^r`. Probe `probe_466r13_moment.py` measures the *true* optimized-Wick constant
`≈ 1.43·√(n ln q)`, with the sharp optimum near `r ≈ (ln q)/2` giving `M ≈ √(2·n·ln q)` (the skeptic's log-space
argmin at prize scale `n=2^30, q~2^158` confirms `r≈(ln q)/2`, ratio-to-`√(2n ln q)` = 1.002). The `√(2e)` is an
honest **over-estimate** of that, sufficient for the *order* `√(n·log q)`; the sharper constant is left as a
probe-validated numeric, **not** claimed as a Lean theorem. This is a constant-factor matter living entirely in
the (now-formalized) moment step; it does not touch any axiom-clean claim and does not affect the World-I/II
verdict.

So: **the wall now discharges the FULL analytic sup-norm payload** — both the per-rung moments AND the optimized
closed-form `M ≤ C·√(n·log q)`, machine-verified. Caveat (a) is closed.

---

## 3. Lane R (the crux) — WORLD II: the prize needs a SECOND, distinct input the wall does NOT supply

**The question, precisely.** The `M → δ*` step (via `CharSumDeltaStarBridge.le_mcaDeltaStar_of_charSumBound`)
consumes the signed hyperplane incidence sum

> `I_H(s₀) := ∑_{b ∈ H} conj(η_b) · ψ(b·s₀)`   over the far-coset frequency hyperplane `H` (`|H| ≤ q`).

The in-tree route bounds `I_H` by the **naive** triangle inequality `|G| + q·B` (paid once per annihilating
frequency, NO inter-frequency cancellation), which at the prize budget `q·ε* ≈ n ≈ |G|` forces `B ≈ 0` — i.e.
it is **VACUOUS at the prize** for nonzero `B` (documented in-tree as the honesty note on
`RealizedIncidenceBudget`). The genuine step needs the **per-frequency √-cancellation**
`∀ s₀, ‖I_H(s₀)‖ ≲ √|H|·M = √q·B` (the open Paley-graph / BCHKS Conj 1.12 worst-case bound). **Does this follow
from the wall's sup-norm `M`?**

**The verdict: WORLD II — it does NOT.** The wall's entire analytic payload (`WallHolds ⟹ M`, Lane M) controls
**only the s₀-average** of `‖I_H‖²`, never the worst case. The exact quantitative reason is now axiom-clean in
`Frontier/_R13HyperplaneSecondMoment.lean` (verified this round, 24 s):

> **`incidenceSum_sq_sum_offsets`** (axiom-clean):
>   `∑_{s₀ ∈ F} ‖I_H(s₀)‖² = q · ∑_{b ∈ H} ‖η_b‖²`.

This is a clean second-moment/Parseval identity via `AddChar.sum_mulShift` orthogonality — the same mechanism as
`SubgroupGaussSumSecondMoment`. Dividing by `q`: the **average** over offsets is exactly
`∑_{b∈H}‖η_b‖² ≤ |H|·M²` (`incidenceSum_sq_sum_le_of_supBound`, also axiom-clean), so the **typical** offset
obeys `‖I_H(s₀)‖ ≤ √|H|·M` — the √-cancelled World-I scale. **But this RHS is phase-blind**: it depends only on
the moduli `{‖η_b‖}`, hence only on `M`. It cannot see the worst-case in-phase peak the far-coset adversary
selects.

Two independent lines of evidence pin that the worst case is a strictly finer, **non-derivable** object:

- **The worst case reaches `|H|·M`-scale, not `√|H|·M`.** The independent skeptic computed the EXACT max over
  ALL offsets `s₀` for the real `η` spectrum (`probe_466r13_audit.py`, `_out_466r13_incidence.txt`,
  `_mechanism.txt`): `worst/|H| ≈ 0.98–1.01`, and the ratio `worst/(√|H|·M)` **grows** with `|H|`
  (`6.1` at `|H|=2064` → `13.7` at `|H|=32808`, i.e. `∝ √|H|`, unbounded). The mechanism is genuine arithmetic
  coherence, not a numerical artifact: the worst offset is exactly `s₀ ∈ μ_n`, where
  `I(s₀) = ∑_{y∈μ} G_H(s₀−y)` picks up the diagonal Gauss-period `G_H(0) = |H|`. A phase-blind second moment
  **cannot** see this.

- **The counterexample-to-derivability.** Replacing `{η_b}` by any spectrum of **identical moduli** `‖η_b‖` but
  different phases leaves `M` and the entire RHS of `incidenceSum_sq_sum_offsets` **unchanged**, yet collapses
  `worst‖I_H‖` from `≈|H|·M` down to the √-scale. The skeptic built a self-contained two-spectra witness
  (constant-phase vs random-phase, identical `M` and identical `L²`) whose worst-case sup differs by a factor
  `16.6` at `|H|=2064` → `54.8` at `|H|=32768` (again `∝ √|H|`). Aligned gives exactly `|H|·M`; random gives
  `≈√|H|·M`. **Therefore `worst_{s₀}‖I_H(s₀)‖` is provably NOT a function of `M`** (nor of the moduli multiset at
  all): two spectra with the *same* `M` have worst-case incidence differing by a factor `√|H|`.

**What this means: the wall is TWO analytic statements, not one.**

1. **`WallHolds`** (`∀ r, DCEnergyBound G r`) — the DC-subtracted char-`p` Wick bound. This is a statement about
   the **moduli/energy** `E_r = ∑_b ‖η_b‖^{2r}`; it supplies the sup-norm `M = max_{b≠0}‖η_b‖`. Phase-blind by
   construction (moments are).
2. **`HyperplaneCancellation`** (= the `hglue.2` half of `RealizedIncidenceBudget`, = BCHKS Conj 1.12) —
   `∀ s₀, ‖∑_{b∈H} conj(η_b) ψ(b·s₀)‖ ≤ √|H|·M`, a statement about the **joint phase-correlation** of the
   spectrum across the annihilating hyperplane. This is a strictly finer object; round 13 proves it is **not
   implied by** statement 1.

`RealizedIncidenceBudget` in `_WallCapstone.lean` is therefore **correctly** kept as a separate named Prop — it
is genuine glue, not laundered, not vacuous-by-construction, not `:True`. No single-Prop iff exists.

**Honest scope of the non-implication (disclosed, correct).** The in-tree `V = F` geometry has the *degenerate*
annihilating hyperplane `{b : b·s₁ = 0} = {0}` (which never tests cancellation), so `H` is modelled as a genuine
index-2/4/8 subgroup — the honest higher-dimensional analogue. And the non-implication is established at
**probe/counterexample level** (a witness of two spectra with equal `M` and unequal worst-case `I_H`), NOT as a
formalized Lean meta-statement — which is the correct framing, since "X does not follow from Y" over a semantic
class of spectra is inherently a countermodel claim, not a single-theorem claim. What *is* axiom-clean in Lean is
the load-bearing identity `incidenceSum_sq_sum_offsets` that makes the average/worst gap exact and pins **where**
`M`'s control stops.

---

## 4. Honest final state — the tightest machine-checked reduction after 13 rounds

The prize localizes, **machine-checked and axiom-clean up to two named open Props**, to:

> **`WallHolds G  ∧  RealizedIncidenceBudget`**

with the following now certified (all `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):

| Link | Statement | Status |
|---|---|---|
| Wall → per-rung moments | `WallHolds ⟹ ∀ r,b≠0, ‖η_b‖^{2r} ≤ q·Wick_r` (`charSum_of_wallHolds`) | axiom-clean |
| Wall → closed-form sup-norm | `WallHolds ⟹ M ≤ √(2e·n·(ln q+1))` (`supNorm_le_of_wallHolds`) | axiom-clean **(caveat (a) removed this round)** |
| Wall → δ*-floor (composite) | `WallHolds ∧ RealizedIncidenceBudget ⟹ δ ≤ mcaDeltaStar C ε*` (`wall_capstone_moment_closed`) | axiom-clean; wall supplies its own `B` |
| Average control of `I_H` | `∑_{s₀}‖I_H‖² = q·∑_{b∈H}‖η_b‖²` (`incidenceSum_sq_sum_offsets`) | axiom-clean |
| Non-implication (2nd Prop distinct) | `worst_{s₀}‖I_H‖` not a function of `M` | probe/countermodel, decisive |

**The two open Props, both ON-BGK, both named, neither discharged:**

- **`WallHolds G := ∀ r, DCEnergyCorrection.DCEnergyBound G r`** — the analytic BGK/Paley wall (the ∀-r closure
  of W1's `WraparoundBelowDC`). Supplies the sup-norm `M`. The FIRST open Prop. Consumed as a hypothesis
  throughout, **never** discharged. Same object as every prior round; unchanged.
- **`RealizedIncidenceBudget` / `HyperplaneCancellation`** — the `√q·B` per-frequency worst-case hyperplane
  cancellation (Paley-graph / BCHKS Conj 1.12): `∀ s₀, ‖∑_{b∈H} conj(η_b) ψ(b·s₀)‖ ≤ √|H|·M`. The SECOND open
  Prop, **proven this round to be genuinely distinct from `WallHolds`** (the wall's energy/moment control is
  phase-blind; the worst-case incidence depends on arithmetic phases `M` does not carry). Correctly kept
  explicitly named in `_WallCapstone.lean`.

So the answer to the round-13 question — *is the prize localizable to `WallHolds` alone?* — is a rigorous **NO**.
"The wall," as the entire analytic content the prize needs, is **two** statements: a moment/energy bound (the
BGK wall proper, which the campaign has been calling "the wall") **and** a phase-correlation / worst-case
cancellation bound over the frequency hyperplane. The first does not imply the second. The capstone is tightened
from CAPSTONE-PARTIAL to a **fully-wired two-Prop certificate**: the analytic sup-norm payload is now discharged
end-to-end from `WallHolds` (Lane M), and the residual is exactly one further, provably-distinct open input
(Lane R).

---

## 5. Honesty contract

No closure is fabricated. Neither `WallHolds` nor `RealizedIncidenceBudget` is claimed proven; both remain
explicit named open `Prop`s, ON-BGK, exactly as the modularity convention prescribes. Every "axiom-clean" claim
in this essay was verified this round via `pg-iterate` and shows `[propext, Classical.choice, Quot.sound]` with
no `sorryAx`. The one un-formalized quantity — the sharp moment constant `√2` vs the Lean over-estimate `√(2e)` —
is labeled a probe numeric, not a theorem, and is non-load-bearing. The non-implication of Lane R is honestly
scoped as a countermodel over the spectrum class (the correct framing), with the load-bearing identity
`incidenceSum_sq_sum_offsets` machine-checked. The prize is **not** closed; the wall is **not** closed. The
result of the round is a sharper map: the open surface is precisely **two** named, distinct analytic inputs, and
the entire remaining analytic burden between them and `δ*` is now machine-certified.

---

## Round-13 artifact files

Lean (all axiom-clean, `[propext, Classical.choice, Quot.sound]`, verified this round via `pg-iterate.sh`):

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MomentOptimizedSupNorm.lean` — Lane M: `WallHolds ⟹ M ≤
  √(2e·n·(ln q+1))` (moment-order optimization discharged from the wall; caveat (a) removed).
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MomentWallWiringCheck.lean` — Lane M wiring:
  `wall_capstone_moment_closed`, the capstone with `B` supplied by the wall itself.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R13HyperplaneSecondMoment.lean` — Lane R:
  `incidenceSum_sq_sum_offsets` (second-moment identity) + `incidenceSum_sq_sum_le_of_supBound` (the World-II
  certificate: `M` controls the average, not the worst case).
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_WallCapstone.lean` — the round-12 capstone (unchanged this
  round; re-verified as the composition target).

Probes (numerical evidence; regime `p ≡ 1 mod n`, `p ≥ n^4`, ≥2 primes, `X^{n/2} ≠ ±1` excluded):

- `scripts/probes/probe_466r13_moment.py` → `scripts/probes/_out_466r13_moment.txt` — true optimized-Wick
  constant `≈ 1.43·√(n ln q)`, argmin near `r ≈ (ln q)/2`.
- `scripts/probes/probe_466r13_incidence.py` → `scripts/probes/_out_466r13_incidence.txt` — `worst‖I_H‖ ≈
  |H|·M`, ratio `worst/(√|H|·M) ∝ √|H|` (unbounded).
- `scripts/probes/probe_466r13_mechanism.py` → `scripts/probes/_out_466r13_mechanism.txt` — worst offset
  `s₀ ∈ μ_n` picks up the diagonal Gauss-period `G_H(0) = |H|`.
- `scripts/probes/probe_466r13_audit.py` → `scripts/probes/_out_466r13_audit.txt` — independent skeptic
  re-derivation: second-moment identity to rel.diff `2e-16`; exact-max-over-s₀ and equal-`M` two-spectra witness.
- `scripts/probes/probe_466r13_twoinput.py` → `scripts/probes/_out_466r13_twoinput.txt` — parallel-agent
  cross-check (n=32) concurring on WORLD II.

Docs:

- `docs/kb/deltastar-466-essay-round13-2026-07-04.md` — this essay.
- `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md` entry `[466-r13-two-distinct-inputs]` — the WORLD II
  verdict log.
