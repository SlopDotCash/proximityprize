# #466 lane L2 — the second-witness / multiplicity floor is REFUTED on hard lines; the incidence-cap law explains why (2026-07-02)

**Question (dossier v3 §6 Tier-1 item 2, third bullet, untouched since #464):** on hard far
lines at window-interior `a`, does every bad scalar have ≥ 2 witnessing codewords
(`NoUniqueBadScalarWitness`, ⟺ `LineBadScalarMultiplicityFloor R=2`, buying the discount
`#bad ≤ incidences/2`)?  Or do unique-witness bad scalars exist?  The
pairwise-interpolation intuition ("two singleton bad scalars on a hard line must force a
second witness / an RS dependence / a small classified pencil") was the one graph-route shape
not yet exhausted after the round-1 tautology sweep.

## Verdict

**REFUTED, in the strongest possible sense, with the mechanism proven in Lean.**  On the
extremal far lines the multiplicity histogram is `{1w: all}` — literally EVERY bad scalar is
a singleton — and this is a THEOREM, not an accident: saturation of the direction-blind
ceiling `C(n,a)` forces all-singleton.  The floor and near-extremality are mutually
exclusive; the pairwise-interpolation relation is dead because the extremal object is a
perfect matching between bad scalars and `a`-subsets of coordinates.

## Numerics (probe `scripts/probes/probe_466_second_witness.py`)

Exact complete witness-fiber enumeration per line (per `k`-subset `T` the interpolant of the
line word is affine in `γ`; agreement per position is a linear equation in `γ`), verified
3-way (fiber scan == fast badcounts engine == brute force over all `γ`), plus an independent
full-`q²`-codeword enumeration path at `k = 2`.  Hard lines = P5-machinery worst-`u0`
re-search (shared pool + chained interpolation-adversarial + hill-climb), worst counts
matching the P5-recorded references.  Regime: `dom = μ_n` proper, `p ≡ 1 (mod n)`,
`p ≥ n⁴`, two primes per scale in different `v₂(p−1)` classes, spread directions avoid the
antipodal gap `n/2`.

| scale | q (v₂) | a (δ) | worst lines | histogram | unique-witness fraction |
|---|---|---|---|---|---|
| n=8, k=2 | 4129 (5) | 3 (0.625) | #bad = 56 = C(8,3) **saturated** | `{1w:56}` ×4 dirs | 100% (56/56) |
| n=8, k=2 | 4129 (5) | 3 | near-worst #bad = 54–55 | `{1w:52–54, 2w:1–2}` | ≥ 96% |
| n=8, k=2 | 4129 (5) | 4 (0.500, boundary) | #bad = 9 | `{1w:8, 2w:1}` | 89% |
| n=8, k=2 | 8273 (4) | 3 | #bad = 56 **saturated** | `{1w:56}` (replicated) | 100% |
| n=16, k=4 | 65617 (4) | 7 (0.5625) | #bad = 9 | `{1w:8, 2w:1}` | 89% |
| n=16, k=4 | 65617 (4) | 7 | 5 of 6 lines | all-singleton | 100% |
| n=16, k=4 | 65633 (5) | 7 | #bad = 9 | `{1w:8, 2w:1}` (replicated) | 89% |

Aggregate (first n16 chunk): 33 bad-scalar instances, 32 unique-witness, 1 multi-witness.
Every scanned hard line carries ≥ 1 unique-witness bad scalar; most are ALL-singleton.

**Explicit countermodel** (n=16, q=65617, k=4, a=7, dir `mono_j4`, refined-worst):
`u0=[1, 53314, 51007, 21867, 65616, 12303, 14610, 43750, 1, 53314, 51007, 21867, 65616, 12303, 14610, 43750]`,
`u1 = (x^4 on μ₁₆)`, `γ = 9564`, unique witness `p(x) = 9564 + x²` (agreement 8 ≥ a = 7).
Smaller hand-checkable ones at n=8 in `_out_466_second_witness_n8.txt`.

Outputs: `_out_466_second_witness_n8.txt` (+ `_n8_q8273.txt` completion),
`_out_466_second_witness_n16_q65617_a7_d0.txt`, `_out_466_second_witness_n16_q65633_a7.txt`.

## The mechanism, proven (Lean brick `Frontier/_SecondWitnessFloor.lean`, axiom-clean)

On any line whose DIRECTION is `a`-far from the code (`AgreementFarDirection`: no codeword
agrees with `u₁` on `a` points = the probe's `agreemax < a` guard), with `1 ≤ k ≤ a`:

1. **Incidence cap** (`lineHeavyIncidences_card_le_choose`): the TOTAL incidence count
   `Σ_γ #fiber(γ) ≤ C(n,a)`.  Each incidence privately owns the `a`-subsets of its agreement
   set: sharing across scalars transports `u₁` into the code, sharing within a scalar merges
   the codewords.
2. **Mutual exclusivity** (`lineBadScalars_card_mul_two_le_choose_of_noUniqueBadScalarWitness`):
   `NoUniqueBadScalarWitness ⟹ #bad ≤ C(n,a)/2`.  The floor pays multiplicity out of the same
   budget the scalars consume — no line within factor 2 of the ceiling can satisfy it.
3. **Defect forcing** (`two_mul_lineBadScalars_card_le_choose_add_singletonDefect`):
   `2·#bad ≤ C(n,a) + defect` — singletons are FORCED linearly past `C(n,a)/2`.
4. **Saturation ⟹ all-singleton** (`singletonBadScalars_eq_lineBadScalars_of_choose_le`):
   `#bad = C(n,a)` makes every fiber a singleton — the measured `{1w:56}` histograms as a
   theorem.
5. **The unguarded universal Prop was never viable**
   (`not_noUniqueBadScalarWitness_of_line_through_code`): any line through the code carries a
   singleton fiber `{u₀ + γ·u₁}` at the crossing scalar, for every code/field/level.

Bonus: `lineBadScalars_card_le_choose` = the direction-blind scalar ceiling at EVERY level
`a ≥ k` in the production (`Ownership`) vocabulary, any embedding domain — companion to
`FirstInteriorLevelDirectionBlind.levelBadScalars_card_le_choose` (a = k+1, smooth domain).

## Re-scope answer (task (b))

- Is the defect bounded usefully?  `defect ≤ #bad` always (in-tree), and at saturation
  `defect = #bad` EXACTLY — the chain `2·#bad ≤ incidences + defect` degenerates to the
  undiscounted `#bad ≤ incidences` precisely on the lines that determine the far-line budget.
  The multiplicity route buys a factor `(1 + multi-fraction)⁻¹ → 1`: nothing.
- What survives: (i) the **incidence cap itself** — a clean strengthening of the scalar
  ceiling from #scalars to Σ-multiplicities, free to any future counting chain; (ii) the
  contrapositive **budget split**: on any line class where a floor CAN be proven, `#bad ≤
  C(n,a)/2` holds automatically — but `C(n,a)` is astronomically above the needed budget at
  prize depth, so this is not a route.
- The **pairwise-interpolation relation** (last un-exhausted graph-route shape) is dead: the
  extremal configuration is a perfect matching (bad scalar ↔ private `a`-subset), so no
  relation between two singleton scalars forces anything.

## Status

- Lean: `Frontier/_SecondWitnessFloor.lean` — **compile check PASSED 2026-07-02**
  (`pg-iterate` ✅ OK, 330s, exit 0: no errors, no `sorry`, no `sorryAx` anywhere in the full
  compiler output; `#print axioms` = `[propext, Classical.choice, Quot.sound]`; source audit:
  no `native_decide`, no `axiom` declarations; `autoImplicit false` set file-locally, so the
  fast-path/`lake build` divergence (pitfall (a)) is neutralized). The mechanism is proven.
- Second-prime a=4 boundary replication added 2026-07-02:
  `_out_466_second_witness_n8_q8273_a4.txt` (q=8273, a=4, dirs mono_j2/sp2_0_3) — worst line
  `#bad=9`, histogram `{1w:8, 2w:1}`, identical to q=4129; all 3-way asserts + independent
  full-`q²` fiber checks pass. Every KB-table row is now ≥ 2-prime replicated.
- DISPROOF_LOG: `[466-r4-second-witness-floor-refuted]`.
- Dossier v3 §6 Tier-1 item 2: third bullet DECIDED (refuted-with-mechanism); the remaining
  live bullets there are the low-profile `D(t)` theorem and `CandidateListExactSuccessor`.
