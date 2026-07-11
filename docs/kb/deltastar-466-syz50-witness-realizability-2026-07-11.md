# SYZ50 — witness realizability: is the SYZ49 on-domain ι=2 witness band-realizable? (2026-07-11)

**Issue #466 / #507 · rate-1/2 proximity-gap δ\* · CORE OPEN / ON-BGK**

## The question

SYZ49 exhibited an **on-domain** `ι = 2` witness over the *proper subgroup* `μ₁₂ ⊂ 𝔽₃₇^×`:
disjoint `(4,4,4)` sets `S_AC={1,8,27,29}`, `S_BC={6,10,11,31}`, `S_AB={14,23,26,36}` with a
genuine constant syzygy `W_BC − 11·W_AC = −10·W_AB`, and concluded that cyclotomic
domain-membership alone does **not** force `ι ≤ 1`, relocating the shield to **band-realizability**
(SYZ42 superadditive-union / SYZ27–28 Venn geometry). SYZ50 tests that relocation: **is the SYZ49
witness — or its degree profile — band-realizable at rate exactly 1/2?**

## Band Venn model at rate 1/2 (n = 2k)

The three sets are the *pairwise-exclusive overlap regions* of three band cores; `t = |triple
region T|`. SYZ27/28/37/G172 impose:

- **disjointness** `a + b + c + t ≤ n = 2k` (four disjoint domain subsets);
- **budget cap** `max(a,b,c) ≤ k − 1 − t` (SYZ37 uniform window);
- **interior slack** `a + b + c ≥ 2(k − 1 − t) + 3` (G172).

## Decisive verdicts (probe `probe_syz50_witness_realizability.py`)

**A. Polytope — `{balanced interior} ∩ {band-realizable, rate 1/2}` is NONEMPTY.**
Exhaustive integer enumeration (`k ≤ 40`, `a≤b≤c`) finds **65 982** balanced-interior
band-realizable profiles. Smallest: `n = 14, k = 7, (4,4,4), t = 2` (cores `s = a+b+t = 10`,
`δ = 4/14 = 2/7 ∈ (1/4,1/3)`). **⇒ `ι ≤ 1` at rate 1/2 is NOT closed by a pure counting/overflow
argument.**

**B. The specific SYZ49 μ₁₂ witness is NOT band-realizable.** At `n = 12, k = 6` the band forces
`t = 1` (slack ⟹ `t ≥ 1`, budget ⟹ `t ≤ 1`), but disjointness then needs `12 + 1 = 13 ≤ 12` —
impossible. The three `(4,4,4)` sets fill the **entire proper subgroup** `μ₁₂ = μ_{3d}`, leaving
**no room** for the triple region the budget demands. General law: a balanced `(d,d,d)` profile
needs `n ≥ 3d + 1`; `μ_{3d}` misses it by **exactly one domain point**. The witness is a
whole-subgroup domain-membership artifact, not band overlap geometry.

**C. Realizable configs carry FRESH on-domain ι=2 witnesses.** Over `μ₁₄ ⊂ 𝔽₂₉` the realizable
`(4,4,4), t = 2` config yields **357** genuine constant-syzygy level-set witnesses (three disjoint
size-4 sets, a size-4 `R = W_BC/W_AC` level set, 2 points left for `T`). So band-realizability
*counting* does not close the interior either.

**D. Lift ceiling.** On the realizable `n = 14` witness the pencil-yield count is
`∑(n − sᵢ) = 3·(14 − 10) = 12 ≤ 13 = n − 1` (SYZ22/SYZ28 budget). A full bad-lift cannot outrun
the budget; whether the syzygy comes from a genuine **over-budget stack** (SYZ42
syndrome-configuration existence) is the unchanged open gate.

## What was proven (Lean, axiom-clean pure ℕ) — `Frontier/_SYZ50WitnessRealizability.lean`

- `Realizable a b c t k` — the rate-1/2 band predicate (subtraction-free).
- `realizable_forces_triple` : `Realizable … → 1 ≤ t` (rate 1/2 forces a nonempty triple region).
- `balanced_profile_needs_domain` : `Realizable d d d t k → 3d + 1 ≤ 2k` (μ_{3d} is one short).
- `syz49_mu12_witness_not_realizable` : `¬ ∃ t, Realizable 4 4 4 t 6` — **the μ₁₂ witness is
  band-non-realizable**.
- `witness_realizable_n14` / `witness_balanced_interior` / `balanced_interior_meets_realizable` —
  **the polytope intersection is nonempty** (witness `(4,4,4), t = 2, k = 7`).
- `lift_ceiling_le_budget` — pencil ceiling ≤ budget on the realizable witness.

Axiom audit: all theorems depend only on `propext`/`Quot.sound` (+`Classical.choice` via imports);
the four `decide`/existence theorems depend on **no axioms**. No `sorry`, no `native_decide`.

## Honest status

Polytope intersection **nonempty** ⇒ counting/Venn overflow is **not** the closing argument. Newly
pinned: the SYZ49 μ₁₂ witness is a whole-subgroup artifact `n = 3d` short of the band's `n ≥ 3d+1`,
and the genuine gate is neither domain-membership (SYZ48/49) nor Venn-counting (SYZ50) but the
**over-budget-stack lift** (SYZ42 existence core / SYZ28 pencil yield). **CORE remains OPEN /
ON-BGK**, shield located one level deeper than SYZ49 left it.
