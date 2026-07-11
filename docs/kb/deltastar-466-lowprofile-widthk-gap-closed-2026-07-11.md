# δ* #466 — W15 part 6: the width-k gap closed — the secant-pair strip refuter (2026-07-11)

Lane: `ll:low-profile-fiber`. File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_W15WidthKGapClosed.lean`
(axiom-clean; FULL manual audit: all 10 theorems exactly
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no `ofReduceBool`;
`pg-iterate` 5s). Probe: `scripts/probes/probe_466_w15_widthk_gap.py` (deterministic,
exit 0). Companions: parts 1–5 kb notes (`deltastar-466-lowprofile-*-2026-07-10.md`).

## 0. The task

Part 4's trichotomy decided `L_near = 1` for `LargeZeroSafeLineListBudgeted` outside the
strip `2n < 3a < 2n + k`. Close the strip.

## 1. Failure anatomy of the older proofs (machine-pinned)

* Two-block refuter (part 4): fails at its **large-zero gate** — its zero set has size
  `2(n − a)` and `2(n − a) ≥ a ⟺ 3a ≤ 2n` (`twoBlock_gate_fails_at_11`).
* UD-plus discharge (part 3): fails at its **inclusion-exclusion gate** — two appearing
  codewords force `2a ≤ z + (k − 1) + 2(n − z)`, contradictory for all `z ≥ a` only when
  `3a ≥ 2n + k` (`udplus_gate_fails_at_11`). In the strip, two appearing codewords are
  numerically allowed, but only on a `z`-band of width `< k`.

## 2. The strip refuter: the secant pair

Pair `0` with the monic degree-`(k−1)` codeword `e` with root set `R ⊆ Z`, and let the
two codewords SHARE `k − 1` support votes on a set `W` where `e` is constant `c* ≠ 0` —
possible exactly when `e₁(R) = e₁(W)` and `e₂(R) = e₂(W)` (then `e − ∏(x − w) ≡ c* =
e₃(W) − e₃(R)`, nonzero since `R ≠ W`). At `(n, k, a) = (16, 4, 11)` all budgets are
tight: `Z = R ⊔ D₀ ⊔ D₁` (3+4+4 = 11 = a), support `W ⊔ {i₀, i₁}` (5); `0` appears at
`γ = 0` (11 points), `e` at `γ = c*` (11 points); safety is structural: `0` scores
`|R ∪ D₀| = 7`, `e` scores `≤ (k−1) + |D₁| = 7`, generic codewords `≤ 2(k−1) = 6 < 11`.

Probe found the concrete coincidence over `F₁₇`: `R = {0,1,2}` (`e = X(X−1)(X−2)`),
`W = {3,7,10}` (`e₁ = 3`, `e₂ = 2` both; `c* = 6`), and verified the assembled line
exactly (`Λ = 2`, safe, large-zero). The strip hill-climbs top out at `Λ ∈ {0, 1}`:
random search cannot find this configuration — the symmetric-function design is
essential.

## 3. What is proved

1. `not_budget_one_of_two_appearing` — abstract two-appearing refuter.
2. `secant_zeroDirectionSafeLine` — structural safety of the secant-pair line.
3. `secantPair_not_largeZeroSafeLineListBudgeted_one` — parametric refuter (general in
   `F`, `dom`, `n`, `k`, `a`; the two appearance certificates enter as hypotheses).
4. `strip_shape_16_4_11_L_one_refuted` — CONCRETE: over `ZMod 17` with the standard
   16-point domain, `¬ LargeZeroSafeLineListBudgeted dom17 4 11 1`. All pointwise
   facts by kernel `decide`; `e ∈ rsCode` via the explicit monic cubic.
5. Gate theorems (`strip_gates_16_4_11`, `twoBlock_gate_fails_at_11`,
   `udplus_gate_fails_at_11`).

## 4. Dichotomy status

At `n = 16, k = 4` the `L_near = 1` question is decided at EVERY `a ≥ 9`:

| a        | verdict  | mechanism                    |
|----------|----------|------------------------------|
| 9, 10    | refuted  | two-block (part 4)           |
| 11       | refuted  | secant pair (this file)      |
| ≥ 12     | proved   | UD-plus discharge (part 3)   |

The part-4 trichotomy is now a sharp dichotomy at this shape family: `L_near = 1` holds
iff `2n + k ≤ 3a` (for shapes admitting the refuting configurations).

## 5. Honesty and remaining sliver

* The concrete strip refutation is per-shape (`ZMod 17`, standard domain). The
  parametric theorem covers any field/domain admitting the symmetric coincidence — two
  equations in `2(k−1)` domain unknowns, generically solvable, but the existence lemma
  is NOT proved. A uniform all-fields strip refutation is the remaining (thin) open
  sliver.
* Weld consequence: the safe large-zero branch cannot close at `L = 1` anywhere below
  `2n + k ≤ 3a`; above it the branch is CLOSED (part 3).

## 6. W15 lane final map (parts 1–6)

Floor `n − a` (P1) → ceiling `Λ·|supp|` + residual (P2) → discharge above
doubled-Johnson margin and at UD-plus (P3) → L=1 refuted at `3a ≤ 2n`, secant dichotomy,
trichotomy (P4) → L=2 refuted shape-dependently, campaign shape capped at 2 (P5) →
width-k strip refuted, sharp dichotomy (P6). Open residuals: uniform-fields strip
existence lemma; `Λ ≤ 2` proof (or non-constant refuter) at `3(k−1) ≥ a` shapes;
`hunsafe`; terminal `hfarL`.
