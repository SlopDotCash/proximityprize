# δ* sweep A35 — Shaw-operator unification: all moments collapse to one spectral gap

**Date:** 2026-06-14 · **Actionable:** A35 (merged `371-T02`/`371-T03`) · **Type:** lean-brick
**Status:** PARTIAL (substrate landed axiom-clean; the single open prize input named, not proven)

## What A35 asked

Re-land the Shaw-operator unification workbench: define the Shaw operator `S_D` as
convolution-by-`1_D` on `F_q^+` (the adjacency of `Cay(F_q^+, μ_n)`), prove `shawOp_eigen`
(spectrum = `{η_b}`) and `shaw_offdiag_moment_le` (Hölder), collapsing the below-UDR window lane
**and** the deep-band census lane to the single scalar `B(μ_n) = ‖S_D|_{1^⊥}‖`, with the lone open
conjecture `B(μ_n) ≤ √2·√n`.

## What was already in-tree (do not duplicate)

`ProximityGap/ShawOperator.lean`, `ShawOperatorDual.lean`, `ShawSecondMoment.lean`,
`ShawFlatnessRefuted.lean` formalize a **different** Shaw operator: the *line–ball incidence*
spectral error `𝒮(S; s₀, s₁) = ∑_{ψ⊥s₁, ψ≠0} ∑_{s∈S} ψ(s₀−s)`, living on the additive characters of
the **word space `V = ι→F`**. That object's eigen-data is over `V`, not over `F_q`, and its second
moment is the hyperplane-restricted Krawtchouk mass. The A35 target — the Cayley adjacency on
`F_q^+` whose eigenvalues are literally the Gauss periods `{η_b}` — was **absent** here (it lived on a
parallel worktree). So this is a genuinely new, non-duplicate brick.

## What landed (axiom-clean, `sorry`-free)

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A35_ShawOperator.lean`, namespace
`ArkLib.ProximityGap.Frontier.ShawOperatorA35`, over an abstract finite additive group `G`
(the `F_q^+` model), `D : Finset G` (the `μ_n` model):

- `shawOp D f x := ∑_{d∈D} f (x − d)` — convolution by `1_D`; the Cayley-graph adjacency.
- `gaussPeriod D ψ := ∑_{d∈D} ψ(−d)` — the eigenvalue family `{η_b}`.
- **`shawOp_eigen`**: `S_D ψ = (gaussPeriod D ψ) · ψ` pointwise — every additive character is an
  eigenvector; **spectrum(S_D) = {η_ψ}** exactly. (The operator-level meaning of "the open input is
  `max_b|η_b|`".)
- `gaussPeriod_zero`: `η₀ = |D|` (Perron eigenvalue = Cayley-graph degree).
- **`parseval_gaussPeriod`**: `∑_ψ ‖η_ψ‖² = |D|·|G|` (trace identity / Parseval).
- **`offdiag_secondMoment_eq`**: `∑_{ψ≠0} ‖η_ψ‖² = |D|·|G| − |D|²` (`= q·n − n²` at the prize).
- **`shaw_offdiag_moment_le`** (the unification): with `B := max_{ψ≠0}‖η_ψ‖`, for every `M ≥ 1`,
  `∑_{ψ≠0} ‖η_ψ‖^{2M} ≤ B^{2M−2}·(|D|·|G| − |D|²)`. **Every higher even moment is pinned by the
  single scalar `B` and the proven second moment** — Hölder, pure.
- `shaw_offdiag_moment_le_of_spectralGap`, `ShawSpectralGap D β := ∀ψ≠0, ‖η_ψ‖≤β`,
  `moment_le_of_ShawSpectralGap`: the consumer chain — a single gap certificate `B ≤ β` yields all
  deep moments.
- **`exists_gaussPeriod_sq_ge_avg`** (floor side): some off-trivial `ψ` has
  `‖η_ψ‖² ≥ (|D||G|−|D|²)/(|G|−1) ≈ |D| = n`, so any valid `β` obeys `β ≥ √n`. The L² average alone
  forces `√n` — which is exactly why the conjectured constant is `√2`, not `1`.

Axiom audit: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no `native_decide`.

## Numerical confirmation (`scripts/probes/sweep_A35_shaw_operator.py`)

On prize-shaped cases `(p,n)` with `n ∈ {8,16,32,64,128}`, `n | p−1`:
- **(E)** eigen identity `S_D ψ_b = η_b ψ_b`: max pointwise error `≈ 1e-14` (exact).
- **(P)** Parseval `∑_b|η_b|² = n·p`: exact; off-trivial `= np − n²` exact.
- **(H)** Hölder moment bound `∑_{b≠0}|η_b|^{2M} ≤ B^{2M−2}·(np−n²)`: holds for `M=1..4`, all cases.

## The honest open core (NOT closed)

The lone open input is `ShawSpectralGap μ_n β` for the prize-window `β`. Two important honesty points:

1. **The `B ≤ √2·√n` (Ramanujan) form is numerically FALSE outside the thin prize regime.** The
   probe shows `B/√n` reaching `5.45` (`p=65537, n=64`, a Fermat prime / high 2-adic valuation) and
   `3.65` (`p=786433, n=16`). The `√2`-form is the *idealized Ramanujan* statement, which holds only
   in the asymptotic thin regime `n ≪ √p`, not for thick / structured primes.
2. **The correct prize floor is the `√(n·log(q/n))` form.** `B/√(2·n·log(p/n))` stays in
   `[0.76, 1.46]` across the same cases (matches the `B`-form `B(μ_n) ≤ C·√(n·log(q/n))` and the
   max-of-`m`-sub-Gaussians EVT heuristic in memory `arklib-389-deep-moment-wall`).

So A35's stated `√2` conjecture is a *refuted-as-stated* idealization; the surviving open input is
`ShawSpectralGap μ_n (√(2·n·log(q/n)))`. The moment collapse proven here is exactly the reduction
the moment method needs — but as `shaw_offdiag_moment_le` and `ShawSecondMoment.exists_shawError_sq_ge`
together show, the moment route only brackets `B` up to the `√(log)` / `√|V|` union tax (wall W4 in
`CharSumMomentDeepWall.lean` and the `√(log)`-short wall). **No closure.** This brick is the cleanest
operator substrate for the prize: it reduces both the window lane and the census lane to one named,
falsifiable scalar `B`, with the second moment proven and every higher moment pinned to it.

## Cross-refs

- `ProximityGap/ShawSecondMoment.lean` — the *word-space* incidence operator (different object).
- `Frontier/Sweep_A02_AutocorrelationRecursion.lean` — the energy-side `E_r` recursion (same `B`).
- `Frontier/WF407_DeepMomentDefectWall.lean`, `CharSumMomentDeepWall.lean` — why moments stall (W4).
- memory `arklib-407-gauss-period-house`, `arklib-389-deep-moment-wall`.
