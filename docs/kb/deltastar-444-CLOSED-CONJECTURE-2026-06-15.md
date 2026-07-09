# δ\* — the CLOSED-FORM conjecture (issue #444, 2026-06-15)

**Deliverable.** A single closed-form `δ*(ρ,n)` with **no undetermined / open quantity in the
statement** — a definite elementary formula in `ρ` and `n` only. The *proof* remains the
recognized open problem (the Ethereum Proximity Prize, proximityprize.org); per CLAUDE.md §6A
bold closed-form `δ*` conjectures are encouraged. This is a **CONJECTURE**, clearly labeled —
no closure is claimed proven.

This note supersedes the gated capstone (`deltastar-444-CONJECTURE-capstone-2026-06-15.md`,
which left the constant `Θ_ρ` as an undetermined `O(1)`) by pinning the constant to a closed
expression, and consolidates the multi-route arbitration of which closed expression it is.

---

## 1. The conjecture (one closed formula)

For explicit smooth-domain Reed–Solomon `C = RS[F_p, μ_n, k]` with `n = 2^μ`, `μ_n ⊊ F_p^*`,
`n ∣ p−1`, rate `ρ = k/n ∈ {1/2, 1/4, 1/8, 1/16}`, in the **prize regime** `p ≈ n·2^128`
(`m = (p−1)/n = 2^128`, `ε* = 2^{−128}`, budget `q·ε* ≈ n`), window interior
`(1−√ρ, 1−ρ)`:

> ### **Conjecture δ\*.**
> ```
>            δ*(ρ, n)  =  (1 − ρ)  −  H₂(ρ) / log₂ n
> ```
> where  `H₂(ρ) = −ρ·log₂ ρ − (1−ρ)·log₂(1−ρ)`  is the binary entropy (in bits).

`δ*` is the largest `δ` with **both** `ε_mca(C, δ) ≤ ε*` **and** `|Λ(C^m, δ)| ≤ ε*|F|` (the two
grand challenges are one crossover; `badScalars_eq_explainable` proven in-tree). Nothing in the
statement is undetermined: `ρ, n` are inputs, `H₂` is an explicit elementary function. The
closed constant is **`c(ρ) = H₂(ρ)`**.

### Explicit values at the four prize rates, `n = 2^30` (`log₂ n = 30`)

| `ρ` | `1−√ρ` (Johnson) | `1−ρ` (capacity) | `H₂(ρ)` | **`δ*(ρ, 2^30)`** | inside window? |
|---|---|---|---|---|---|
| 1/2   | 0.29289 | 0.50000 | 1.00000 | **0.46667** | yes (strict) |
| 1/4   | 0.50000 | 0.75000 | 0.81128 | **0.72296** | yes (strict) |
| 1/8   | 0.64645 | 0.87500 | 0.54356 | **0.85688** | yes (strict) |
| 1/16  | 0.75000 | 0.93750 | 0.33729 | **0.92626** | yes (strict) |

(For scale: at `n = 2^256`, `δ* = 0.49609 / 0.74683 / 0.87288 / 0.93618` respectively — the
cushion `H₂(ρ)/log₂ n` shrinks and `δ*` rises toward capacity `1−ρ` as `n → ∞`.)

---

## 2. The governing law (proven in-tree) — only the constant is open

The crossover law is in-tree machinery, not a conjecture:

```
δ*  ⟺  L*(δ) crossover                    badScalars_eq_explainable; far-line law (FarCosetExplosion)
    ⟺  worst-case window list  L*(δ) = 2^{c(ρ)/η}    crosses budget ε*|F| ≈ n = 2^μ
```

Setting `2^{c(ρ)/η} = 2^μ` gives `c(ρ)/η* = μ`, i.e. `η* = c(ρ)/log₂ n`, hence with cushion
`η = (1−ρ) − δ`:

```
δ* = (1 − ρ) − c(ρ) / log₂ n .
```

**The only open quantity in the LAW is the single scalar `c(ρ)`** — and §3 pins it to a closed
expression, removing it from the statement. (Contrast: the prior capstone left the constant as
`Θ_ρ`, gated on an undetermined `O(1)` BGK/Paley house constant. The present note replaces that
undetermined `O(1)` by the explicit `H₂(ρ)`.)

---

## 3. Pinning the constant — multi-route arbitration

Four independent derivations were run. Their verdicts on `c(ρ)`:

| Route | `c(ρ)` | class | confidence |
|---|---|---|---|
| **R1** — KKH26 explicit ceiling (ePrint 2026/782, App. A: list-center family `C(s,r) ≈ 2^{sH₂(ρ)}`) | **`H₂(ρ)`** | `c/η` | high |
| **R2** — list-crossover-at-budget (per-window pattern count `C(n,ρn)`) | **`H₂(ρ)`** | `c/η` | medium |
| R3 — dyadic-entropy / in-tree `countRate` half-domain surface `2^r·C(s/2,r)` | `Φ(ρ) = ρ + ½H₂(2ρ)` | `c/η` | medium |
| R4 — EVT / Paley-house `B = C√(n log m)` | — (`ρ`-independent, decays `1/√n`, **wrong class**) | not `c/η` | high (exclusion) |

**Selected headline constant: `c(ρ) = H₂(ρ)`** — supported by R1 (the KKH26 Appendix-A ceiling
of record), R2, and the open-math ledger
(`docs/wiki/open-math-hypotheses-334-deltastar-2026-06.md`, line 10, citing KKH26 ePrint
2026/782 "Appendix-A route with **c = H₂(ρ)**"). The two `c(ρ)` candidates that share the
`c/η` functional class — `H₂(ρ)` and `Φ(ρ)` — agree as `ρ → 0` and diverge at the top of the
range:

| `ρ` | `H₂(ρ)` (R1/R2) | `Φ(ρ) = ρ + ½H₂(2ρ)` (R3) | gap |
|---|---|---|---|
| 1/2   | 1.00000 | 0.50000 | 0.500 (2× apart) |
| 1/4   | 0.81128 | 0.75000 | 0.061 |
| 1/8   | 0.54356 | 0.53064 | 0.013 |
| 1/16  | 0.33729 | 0.33428 | 0.003 |

`Φ(ρ) = ρ + ½H₂(2ρ) = −ρ·log₂ρ − ½(1−2ρ)·log₂(1−2ρ)` (closed algebraic identity, verified to
machine precision). Because `δ* = (1−ρ) − c(ρ)/log₂ n` and a **larger** `c(ρ)` pushes `δ*`
**lower**, the binding (worst-case) ceiling uses the larger constant, and `H₂(ρ) ≥ Φ(ρ)` at
every prize rate (strict except `ρ→0`). Hence the binding closed ceiling is `c(ρ) = H₂(ρ)`.

R4 (the EVT/Paley-house route) does **not** produce a constant of this family at all: its
binding list exponent is `ρ`-independent and flat in `η` (`C²·log m/2 ≈ 64·C²` bits), and the
cushion it implies decays like `1/√n`, strictly faster than `1/log₂ n`. It is honestly
excluded from the `c/η` arbitration.

---

## 4. Honest caveat — the in-tree-native constant is `Φ(ρ)`, not `H₂(ρ)`

The shred audit (recorded faithfully here) found that the **in-tree axiom-clean object** has
native per-symbol rate `Φ(ρ)`, not `H₂(ρ)`:

- `KKH26EntropyForm.lean` (axiom-clean) defines
  `countRate m r = r + m·H₂(r/m)/log 2` with `m = s/2 = 2^{μ−1}`;
- at `r = ρ·s` this gives per-symbol rate `(1/s)·countRate = ρ + ½H₂(2ρ) = Φ(ρ)`, **exactly
  R3** — confirmed against `kkh26_count_corollary` and the count surface
  `2^r·C(2^{μ−1}, r)` of `KKH26WitnessSpread.lean` (`kkh26_epsMCA_lower_bound`, axiom-clean).

So the headline `c(ρ) = H₂(ρ)` is selected by **external citation** to KKH26 Appendix-A
(ePrint 2026/782; the paper notes this list-center route yields "slightly better concrete
bounds"), **not** by the in-tree derivation, whose native rate is `Φ(ρ)`. The two readings
differ on which combinatorial object is the per-window list:

- **`H₂(ρ)`** = agreement-pattern count `C(n, ρn)` over the full domain `μ_n` (App.-A
  list-center; the `2^r` sign and window-choice factors removed by the per-window restriction);
- **`Φ(ρ)`** = the half-domain sign-free dyadic count `2^r·C(s/2, r)` (the raw in-tree
  `WitnessSpread` surface; carries the `2^r` sign degrees of freedom).

**Status of the constant: NOT pinned by a derivation; selected by the cited authority.** This
is the one genuine residual uncertainty in the formula. Both `H₂(ρ)` and `Φ(ρ)` are **fully
closed** definite functions of `ρ`; if a future audit identifies the per-window list with the
half-domain object, the conjecture's constant becomes `Φ(ρ)` and

```
δ*(ρ, n) = (1 − ρ) − (ρ + ½H₂(2ρ)) / log₂ n        [the in-tree-native fallback, also closed].
```

Both are stated for completeness; the headline follows the KKH26 Appendix-A constant of record.

---

## 5. Test results

**(a) Window-interior placement.** `δ*(ρ, n) = (1−ρ) − H₂(ρ)/log₂ n` lands strictly inside the
window interior `(1−√ρ, 1−ρ)` for all four prize rates at `n = 2^30` (table §1) and at every
`n = 2^10 … 2^30`. The window opens (`δ* > 1−√ρ`) at `μ ≥ 5` (`ρ=1/2`), `μ ≥ 4` (`1/4`),
`μ ≥ 3` (`1/8`), `μ ≥ 2` (`1/16`) — consistent with the in-tree note that the prize cushion is
nonvacuous only at `n ≳ 256` (for `n ≤ 64` Johnson ∩ capacity collide, window empty). The
competing `Φ(ρ)` form is *also* interior at `n = 2^30` (0.48333 / 0.72500 / 0.85731 / 0.92636),
so the window-interior test does **not** discriminate the two constants (their gap divided by
`log₂ n = 30` is small relative to the window width).

**(b) Consistency with the KKH26 ceiling `δ* ≤ 1 − r/2^μ` (`kkh26_mcaDeltaStar_le`).** The
conjecture's radius sits strictly below the proven ceiling: at `δ*_conj` the bad-scalar count
exponent is `Θ(n) ≫ μ`, so the count exceeds the budget `n` (verified `μ = 10, 20, 30`). The
conjecture respects the proven upper bracket.

**(c) Consistency with the exact in-tree data (honest: data is OUT of the prize regime).**
- `GranularityLadderRS` `δ* = j/n` bands are at LARGE `ε*` (small `j = ⌊qε*⌋`); the band
  condition `3(j−1)+k ≤ n` fails at the prize point — disjoint regime, no contradiction.
- `DeltaStarExactPinF5` (`δ* = 1/4` at `n=4, ρ=1/2, ε*=2/5`) and `…F17` (`δ* = 1/4` at
  `n=16, ρ=1/4`) are at `ε* = 2/5, 2/17 ≠ 2^{−128}`; the budget there is `O(1)` not `n`, giving
  an `O(1)` cushion, not `H₂/log n`. The conjecture value (0.0 at `n=4`; 0.547 at `n=16`) does
  **not** equal these pins — **as expected out of regime**. These `n ≤ 64` points are exactly
  where the window interior is empty, so they confirm `p`-independence + below-ceiling structure
  but cannot confirm or refute the exact constant.
- GPU oracle `p`-independence to `n = 38` **matches** (the conjecture is manifestly
  `p`-independent).

**(d) Route convergence.** R1 + R2 agree on `H₂(ρ)`; R3 is the in-tree-native competitor
`Φ(ρ)`; R4 is a different functional class (excluded). 2-of-4 `c/η`-class routes plus the
ledger's cited authority select `H₂(ρ)`; R3 is the documented closed competitor.

Numerics: `scripts/probes/probe_444_route2_crho_final.py` (exact, proper subgroups).

---

## 6. Honest status

- **The conjecture (§1) is CLOSED.** `δ*(ρ, n) = (1−ρ) − H₂(ρ)/log₂ n` is a definite
  elementary formula in `ρ, n` only — no `Θ_ρ` placeholder, no named open `Prop`, no
  incomputable lemma inside the formula. For any `(ρ, n)` it evaluates to a specific real. This
  is the deliverable: a complete, closed conjecture with no room for more open math *in the
  statement*.
- **The constant `c(ρ) = H₂(ρ)` is the best-supported value** (R1/R2 + KKH26 App.-A + ledger),
  but is **selected by external citation, not pinned by the in-tree derivation** — whose native
  rate is `Φ(ρ) = ρ + ½H₂(2ρ)` (§4). This is the formula's one genuine residual uncertainty,
  flagged honestly. The in-tree-native fallback `δ* = (1−ρ) − Φ(ρ)/log₂ n` is also fully closed.
- **The PROOF is OPEN — and is the recognized open problem.** The conjecture reduces to the
  question *"does the floor match the ceiling"*: that the worst-case window list actually
  **reaches** the entropy ceiling at the prize prime is the BGK/Paley-house open problem (SOTA
  `n^{1−o(1)}`; the effective range fails exactly at the prize `β ≈ 4`; ~25 years open). **No
  honest closure exists; none is claimed.** Proving the floor = the prize.
- **Axiom hygiene:** every in-tree file cited here (`KKH26EntropyForm.lean`,
  `KKH26WitnessSpread.lean`) was re-read this session and is axiom-clean
  (`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, no `sorryAx`). No new Lean is
  claimed proven by this note; it is a `docs/kb` conjecture writeup (CLAUDE.md §6A).

**One-line verdict:** the conjecture is closed (formula complete in `ρ, n`); the proof reduces
to the recognized open BGK/Paley floor-matches-ceiling question; the headline constant `H₂(ρ)`
is citation-backed (KKH26 App. A) with the in-tree-native `Φ(ρ) = ρ + ½H₂(2ρ)` as the
documented closed competitor.
