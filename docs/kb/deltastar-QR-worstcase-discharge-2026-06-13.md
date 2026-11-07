# LANDED (feasibility-9, axiom-clean): the index-2 worst-case per-frequency bound, discharged via the classical Gauss sum (#407)

**Status: PROVEN, axiom-clean, real `lake build` green (3316 jobs).** A genuine beyond-Johnson
discharge of the named open Prop `WorstCaseIncompleteSumBound` that reduces *entirely to proven
number theory* and hits NONE of the prize walls. Not the full prize (it is the index-2 lane), but a
real landed theorem. `ArkLib/Data/CodingTheory/ProximityGap/QRWorstCaseIncompleteSum.lean`.

## What is landed

The δ\* prize's per-frequency core is the named Prop `WorstCaseIncompleteSumBound ψ G M`
(`∀ b ≠ 0, ‖η_b‖² ≤ M`, `η_b = Σ_{y∈G} ψ(b·y)`). For a general 2-power NTT subgroup `μ_n` this is
the open BGK / Paley-graph problem (the prize wall — no proven `√(n·polylog)` worst-case bound).

For the **index-2 (quadratic-residue) subgroup** `QR(p) = {a : χ(a)=1}`, it is discharged
UNCONDITIONALLY, axiom-clean:

* `eta_QR_norm_le` : for `b ≠ 0`, `‖η_b(QR)‖ ≤ (√p + 1)/2`.
* `worstCaseIncompleteSumBound_QR` : `WorstCaseIncompleteSumBound ψ (QR p) ((√p+1)²/4)` — no
  hypothesis beyond `p` an odd prime.
* `addEnergy_QR_le` : the end-to-end additive-energy budget via the in-tree consumer
  `addEnergy_le_of_worstCase`, no regime hypothesis.
* helpers `norm_chiC_unit` (`‖χ(b)‖=1`, `b≠0`), `norm_gaussSum_chiC` (`‖τ‖=√p`).

Since `|QR| = (p−1)/2`, the bound is `‖η_b‖ ≈ √p/2 ≈ √(|QR|/2)` — **genuine square-root
cancellation** (the beyond-Johnson, sub-`√q` per-frequency object the prize needs), EXACT.

## Why it avoids every wall

The mechanism is the *classical quadratic Gauss-sum magnitude* `‖τ‖² = p` (Mathlib `gaussSum_sq`,
in-tree `gaussSum_normSq`): `η_b(QR) = (χ(b)·τ − 1)/2` (in-tree `eta_QR_eq`), and the triangle
inequality with `‖χ(b)‖=1`, `‖τ‖=√p` gives `‖η_b‖ ≤ (√p+1)/2`. No BGK, no Weil-for-thin-subgroups,
no additive-energy sum-product, no moment method — index 2 is the ONE case where √-cancellation is
classical (the Gauss sum is evaluated exactly). *(Superseded 2026-10-28, audit T48: index 2 is not
the only classical square-root case. The companion
`deltastar-constant-index-sqrt-cancellation-2026-06-13.md` / `ConstantIndexGaussSumBound.lean`
generalizes it to every fixed index `m ≥ 2`, with primitive `ψ`, via the classical Gauss-sum
magnitude.)* So `hits_a_wall = false`, and the proof's
correctness is independent of `p`, the regime, or the prime.

## Honest scope

* **Novelty 6 / feasibility 9 (PROVEN) / proximity 3.** Index 2, not the prize 2-power FFT index
  `≈2¹²⁸`; at the prize index the same per-frequency bound IS the open BGK wall (`QR` is the special
  algebraic case). This is the index-2 *lane* of the worst-case incomplete-sum problem, solved.
* It is *new in-tree*: all prior QR consumers (`qr_additive_energy`, the 4th-moment route) take the
  energy/L⁴ path; the **sup-norm discharge** of `WorstCaseIncompleteSumBound` was not written.
* Relation to the cumulant dichotomy (`deltastar-cumulant-dichotomy-2026-06-13.md`): QR is the
  extreme "generic, fully sub-Gaussian" end — index 2 has the cleanest possible spectrum (3 distinct
  Gauss-period values), so the per-frequency bound is exact. The structured 2-power primes are the
  opposite (heavy) end where the same bound is open.

Reduces to: in-tree `eta_QR_eq`, `gaussSum_normSq`, `addEnergy_le_of_worstCase` (all axiom-clean) +
Mathlib `gaussSum_sq`, `quadraticChar_dichotomy`, `norm_sub_le`, `Real.sqrt_sq`. Workflow that
surfaced/verified it: `feasibility9-target-hunt` (candidate F, confirmed LAND-NOW).
