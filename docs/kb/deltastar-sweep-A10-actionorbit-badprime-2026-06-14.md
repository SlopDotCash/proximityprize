# δ* sweep A10 — Action–Orbit Q1 bad-prime bound `p ≤ |B|² ≤ n²/4` (non-BGK lane)

**Date:** 2026-06-14 · **Actionable:** A10 (re-land of 407-T06 `_BadPrimeBoundCore`, absent
from this checkout) · **Status:** PARTIAL (algebraic kernel PROVEN axiom-clean; the two
standard-fact inputs remain cited named hypotheses) · **Lane:** Action–Orbit FRI soundness
(Chai–Fan, ePrint 2026/861) — the only genuinely non-BGK / orbit-counting lane.

## What the lane is

The character-sum face of the δ* prize reduces to the open BGK / Paley-graph-conjecture wall
(W-forms B/energy/halo/list). The **Action–Orbit** route (Chai–Fan 2026/861, "Action–Orbit FRI
Soundness Above the Johnson Radius") routes *around* the char-sum wall using orbit counting
under the dilation action of `μ_n`. Its deepest open gate is **Q1** (the paper's "Norm ≠ 0 on
the primitive gap variety", `R_d ≠ 0` on `V_d^prim`, rigorous in the paper only for `d ∈ {4,8}`,
open for `d ≥ 16`).

For the explicit dyadic eval domain `μ_n` (`n = 2^μ`, prize rate `ρ = 1/4`, `k = n/4`), Q1
char-`p` reduces to a purely **algebraic** statement about *bad primes*:

> A prime `p ≡ 1 (mod n)` is **bad** iff there is a nonempty **antipodal-free** `B ⊆ μ_n`
> (no `u` and `−u` both in `B`) with **odd-window vanishing**
> `o_j(B) := Σ_{b∈B} b^j ≡ 0 (mod p)` for all odd `j ∈ {1,…,k−1}`.
> Then `p ≤ |B|² ≤ (n/2)² = n²/4`.

This **replaces** the `EffectiveTransfer` *exponential* threshold `p > 2^n` with a *polynomial*
threshold `p ≤ n²/4`. Since the prize prime is `p ≈ n·2^128 ≫ n²/4`, every prize prime is
automatically clean for this gate — char-uniformly, with **no Hecke L-values / analytic NT**.

## The reduction (three steps)

Write `β = Σ_{b∈B} ζ^{idx(b)} ∈ ℤ[ζ_n]`, `M := φ(n) = n/2` embeddings, `b := |B|`,
`aᵢ := |σᵢ(β)|² ≥ 0` (the `M` conjugate squared moduli), `K := k/2`.

1. **Galois prime-splitting (standard).** `o_j(B) = σ_j(β)` for the `k/2` automorphisms indexed
   by the odd residues; simultaneous vanishing forces `β` into `k/2` distinct primes above `p`,
   so `p^{k/2} ∣ N(β)`, giving `p^K ≤ |N(β)| = √(∏ aᵢ)`.
2. **2-power cyclotomic trace identity (standard).** `Tr_{ℚ(ζ_n)/ℚ}(β·β̄) = (n/2)·|B| = M·b`,
   i.e. `Σᵢ aᵢ = M·b`, and `|N(β)|² = ∏ᵢ aᵢ`.
3. **AM-GM + arithmetic (the kernel — proven here).** `(∏ aᵢ)^{1/M} ≤ (Σ aᵢ)/M = b`, so
   `∏ aᵢ ≤ b^M`; hence `|N(β)| ≤ b^{M/2} = b^{2K}` (`M = 4K`, i.e. `n/2 = 4·(k/2)`, `k = n/4`).
   Combined with `p^K ≤ |N(β)|`: `p^K ≤ b^{2K} = (b²)^K`, take `K`-th root ⟹ `p ≤ b²`.
   Finally `b = |B| ≤ |μ_n|/2 = n/2` (antipodal-free) ⟹ `p ≤ n²/4`.

Steps 1–2 are standard theorems **not available in Mathlib for this setting**, so — exactly as
the original 407-T06 brick — they are taken as the two cited named-fact hypotheses; the kernel
(step 3, the entire calculus content) is proven in full.

## Artifacts

- **Lean:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A10_ActionOrbitBadPrime.lean`
  — axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`.
  - `prod_le_mean_pow` — AM-GM product form `∏ aᵢ ≤ ((Σ aᵢ)/|s|)^|s|` via
    `Real.geom_mean_le_arith_mean` (all weights `1`).
  - `badPrimeBound_core` — the kernel: `(Σ aᵢ = M·b) ∧ (p^K ≤ √(∏ aᵢ)) ∧ (M = 4K)` ⟹ `p ≤ b²`.
  - `badPrime_le_n_sq_div_four` — corollary `p ≤ n²/4` from `b ≤ n/2`.
  - `prize_prime_exceeds_bound` — concrete: `n ≤ 2^40 ∧ p ≥ 2^128` ⟹ `n²/4 < p` (so no prize
    prime is bad).
- **Probe:** `scripts/probes/sweep_A10_badprime_bound_q1.py`
  - Exhaustive bad-prime search, `n = 8, 16`: the ONLY bad prime found is `p = 17` at `n = 16`
    (with `max|B| = 6`, `|B|² = 36`, `p ≤ |B|² ≤ n²/4 = 64`). NO bad prime above `n²/4` exists in
    the searched range (`p` up to `8·n²/4`). Bound confirmed.
  - Char-0 AM-GM kernel sanity, `n = 8,16,32,64`: worst `∏ aᵢ / b^{M/2} = 1.000, 1.000, 0.621,
    0.017` (all `≤ 1`); trace-identity `Σ aᵢ = M·b` exact and AM-GM violations `= 0` across 3000
    random antipodal-free `B` each.

## Honesty / verdict

**PARTIAL — a soundness-route brick, NOT a δ\* closure.** The two named facts (Galois
prime-splitting + cyclotomic trace) are genuine standard theorems, so this is a *faithful
conditional reduction*, not axiom-laundering: the inputs are real, cited, externally proven, and
the kernel consuming them is fully proved axiom-clean.

But this gate governs the **simultaneous** odd-window orbit count (`k/2`-fold divisibility), not
the **single** far-line incidence `o_1 = 0` that pins δ*. The single incidence stays
`q`-dependent — the additive-energy / thin-subgroup sup-norm wall (the B-form
`B(μ_n) ≤ C√(n log(q/n))`) is **untouched**. So A10 is δ*-irrelevant but a *real* soundness
advance for the Action–Orbit route (polynomial vs the previous exponential `p > 2^n` threshold).

**Collision note.** Prior #407 comments (2026-06-14 08:36, 09:08) claimed this bound on a
parallel worktree (`84d185a4e`); that file (`_BadPrimeBoundCore.lean`) and its substrate
(`EvenOddAntipodalCharFree`, `image_neg_eq_of_prod_comp_neg`, `ActionOrbitFRI.lean`) are **absent
from this checkout**. This re-land is a fresh, self-contained, axiom-clean in-tree representative
of the non-BGK orbit lane, plus the missing exhaustive probe.
