# δ* / #466 — SYZ52: second-syzygy bound closes the balanced-interior `ι≤1` (2026-07-11)

## One line
The open balanced-interior half of `ι≤1` at rate 1/2 is EXACTLY the second μ-basis generator
degree bound `δ₂ ≤ ⌈S/2⌉+1` — proved equivalent to `ι≤1` under SYZ44's degree-sum law. This
converts the referee-measured symmetric interior floor into a calibrated Lean consumer.

## Setting
- `S := a+b+c`, μ-basis generator product-degrees `δ₁ ≤ δ₂`, `δ₁+δ₂=S` (SYZ44 `degree_sum_of_hilbert`).
- Imbalance `ι = SYZ45.imbalance a b c δ₁ = ⌊S/2⌋ − δ₁`.
- SYZ47 imbalance floor `δ₁ ≥ max(a,b,c)` closes `ι≤1` only on the UNBALANCED strip (≈37.7%).
  Balanced interior (≈62.3%): `max ≈ S/3`, floor gives `ι ≲ S/6` — vacuous.

## The gap and its closure
Referee probe `fable_syz47_interior.py` (4800 balanced triples, p∈{61,101,257}, budgets
{5,7,9,11}): `ι>1` never observed — the interior obeys a SYMMETRIC floor `δ₁ ≥ ⌊S/2⌋−1` the
two-term collapse cannot reach (it discharges `s_AB=0` then counts two degrees ⇒ `max`-type).

The symmetric closure needs the SECOND generator degree, not `max`:
`δ₂ ≤ ⌈S/2⌉+1  ⟺  δ₁ = S−δ₂ ≥ ⌊S/2⌋−1  ⟺  ι = ⌊S/2⌋−δ₁ ≤ 1.`

## Landed theorems (`_SYZ52SecondSyzygyInteriorClosure.lean`, axiom-clean)
- `imbalance_le_one_of_second_le` — `δ₂ ≤ ⌈S/2⌉+1 ⟹ ι≤1` on the full interior (no `max` hyp).
- `second_le_iff_imbalance_le_one` — EXACT: `δ₂ ≤ ⌈S/2⌉+1 ⟺ ι≤1`. Calibrated, not lossy.
- `symmetric_floor_of_second_le` — tight `ℕ` floor `δ₁ ≥ ⌊S/2⌋−1`.
  (Referee's `⌈S/2⌉−1` is loose for odd S; ⌊·⌋ is tight — exhaustive `ℕ` check S≤120.)
- `imbalance_le_one_of_second_le_of_hilbert` — packaged from SYZ44 `RankNullity`+`TwoRamp`.
- `ceilHalf_eq` — `(S+1)/2 = S − S/2` (both readings coincide).

Axioms: `[propext, Quot.sound]` (+`Classical.choice` on the iff). No `sorryAx`, no custom axiom.

## Scope / what this does NOT do
- Does NOT prove `δ₂ ≤ ⌈S/2⌉+1` — remaining Hilbert–Burch/commutative-algebra content (SYZ47 kb
  assigns the codimension argument to G56/Opus-core).
- `ι≤1` only discharges SYZ44 `uniformSylvester` (spread branch) at rate 1/2.
- Production δ* still needs SYZ18 disjoint supports, `hrank` realizability union-rank, strip-radius
  transport, and the MCAThresholdLedger BGK/incidence LOWER bound.

## Value
The entire open interior residual is now pinned to ONE inequality provably equivalent to the target.
Next lane (G56/Opus-core) has an exact, decidable-per-cell object to attack:
`δ₂ ≤ ⌈S/2⌉+1` for balanced band triples whose reduced factors `W_AC, W_BC, W_AB` are pairwise
coprime *polynomials* (the coprimality is on the factors, NOT on the integer degrees `a,b,c`). Test
cell `p=101`, balanced reduced *degrees* `a = deg W_AC = b = deg W_BC = c = deg W_AB = 7`, `S = 21`
(realized by distinct-root pairwise-coprime `W_XY`): `⌈S/2⌉+1 = 11+1 = 12`, so predicts `δ₂ ≤ 12`,
tight floor `δ₁ ≥ ⌊S/2⌋−1 = 9`, `ι≤1`.

CORE remains OPEN / ON-BGK.
