# δ* #466 — W15 part 7: the uniform strip existence lemma — a PTE pair, not a counting argument (2026-07-11)

Lane: `ll:low-profile-fiber` (finishing round). File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_W15StripExistenceUniform.lean`
(axiom-clean; FULL manual audit: all 8 theorems exactly
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no `ofReduceBool`;
`pg-iterate` 8s). Probe: `scripts/probes/probe_466_w15_strip_uniform_pte.py`
(deterministic, exit 0). Companions: parts 1–6 kb notes
(`deltastar-466-lowprofile-*`).

## 0. The task

Part 6 refuted `L_near = 1` in the width-`k` strip at `(16, 4, 11)` over `ZMod 17` only,
leaving the uniform-fields existence of the symmetric coincidence (disjoint `R, W` with
`e₁(R) = e₁(W)`, `e₂(R) = e₂(W)`, `e₃` differing) as the thin open sliver.

## 1. The mechanism: a Prouhet–Tarry–Escott pair

The coordinator's fiber-counting route collapses to an explicit family. The integer
triples

    R = {0, 5, 7},   W = {1, 3, 8}

are a degree-2 PTE pair: `0+5+7 = 1+3+8 = 12` and `0·5+0·7+5·7 = 1·3+1·8+3·8 = 35` hold
as INTEGER identities (hence in every commutative ring, every characteristic), while
`e₃` differs by `1·3·8 − 0·5·7 = 24`. Equivalently, the single ring identity

    x(x − 5)(x − 7) − 24 = (x − 1)(x − 3)(x − 8)        (`pte_vieta`, by `ring`)

says the cubic `e = X(X−5)(X−7)` (roots `R`) is CONSTANT `= 24` on `W`. Field-dependent
inputs are only: the domain points `0..15` distinct (characteristic `0` or `≥ 17`) and
`c* = 24 ≠ 0` (characteristic `∉ {2,3}`, implied). Disjointness of `R` and `W` is
automatic — two cubics in the same `(e₁, e₂)`-fiber differ by a nonzero constant and
share no roots.

## 2. What is proved

1. `pte_vieta`, `pte_symmetric_coincidence` — the coincidence identities, char-free.
2. `strip_16_4_11_L_one_refuted_uniform` — for EVERY finite field `F` satisfying
   `CharGe17 F` (`(m : F) ≠ 0` for `1 ≤ m ≤ 15`; any `q = p^e` with `p ≥ 17`):
   `¬ LargeZeroSafeLineListBudgeted (uniDom hchar) 4 11 1` on the standard cast domain.
   Explicit bound `Q₀ = 17` (near-optimal: a 16-point domain needs `q ≥ 16`).
3. `strip_16_4_11_L_one_refuted_zmod` — the prime-field corollary, every `p ≥ 17`.

Probe verification: every prime `17 ≤ p < 200` (exact `Λ = 2` + safety + large-zero for
`p ≤ 31`; certificate-level beyond).

## 3. The dichotomy, now field-uniform

At the `n = 16, k = 4` family (standard domains, characteristic `≥ 17`):

| a        | verdict  | mechanism                     | uniformity            |
|----------|----------|-------------------------------|-----------------------|
| 9, 10    | refuted  | two-block (part 4)            | all fields (as-is)    |
| 11       | refuted  | PTE secant pair (this file)   | all fields, char ≥ 17 |
| ≥ 12     | proved   | UD-plus (part 3)              | all fields (as-is)    |

`L_near = 1 ⟺ 2n + k ≤ 3a` — the width-`k` gap question is closed uniformly.

## 4. Honesty

* Uniformity is in the FIELD, for the STANDARD cast domain. For an arbitrary 16-point
  domain in a large field, a symmetric coincidence inside the domain is a codimension-2
  condition and can genuinely fail; the `dom`-indexed residual cannot be closed
  uniformly in `dom`. The campaign consumes standard domains.
* `k − 1 = 3` (the campaign-relevant case) is what this PTE pair covers; general `k`
  needs higher-degree PTE pairs (Prouhet's construction exists over `ℤ`; not
  formalized).

## 5. W15 lane — FINAL (parts 1–7)

P1 floor `n − a` → P2 ceiling `Λ·|supp|` + residual `LargeZeroSafeLineListBudgeted` +
upgraded weld consumer → P3 discharge (doubled-Johnson margin; `L = 1` at UD-plus; safe
branch CLOSED there) → P4 `L = 1` refuted at `3a ≤ 2n`, secant dichotomy, trichotomy →
P5 `L = 2` refuted shape-dependently (multi-block ladder; campaign shape capped at 2) →
P6 width-`k` strip refuted per-shape (secant pair) → P7 strip refutation made
field-uniform (PTE pair, `Q₀ = 17`).

Remaining open residuals of the lane: `Λ ≤ 2` proof (or non-constant refuter) at
`3(k−1) ≥ a` shapes; general-`k` PTE formalization (mechanical); the unsafe branch
`hunsafe`; the terminal far-branch `hfarL`.
