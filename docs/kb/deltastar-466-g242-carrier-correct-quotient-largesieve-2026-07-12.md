# δ* #466 — G242: carrier-correct quotient large sieve (fiber map on `F_p^*`, not `G`)

Date: 2026-07-12
Lane: direct Opus 4.8 CORE cron. Branch `research/proximity-prize`; `main` untouched (#499).
Kind: keystone correctness repair of the input-(A) discharge path. Not a prize move.

## Problem (flagged by the G241 referee probe)

G240 correctly re-typed the quotient-Jacobi operator onto `Q = F_p^*/G` and advertised the lifted
input Parseval

```
∑_{x ∈ F_p^*} ‖F_a(x)‖² = n·m·‖a‖².
```

But the G240 Lean statements `quotient_largesieve_of_fibers` and `l2_mass_floor_of_quotient_fibers`
run the fiber sum over the index set named `G` while demanding

```
hInputParseval : ∑_{u ∈ G} ‖F u‖² = n·m·‖a‖².
```

When `G` is the order-`n` subgroup this hypothesis is **false**: every `u ∈ G` has trivial quotient
class (`cls u = 0`), so `F_a` is constant on `G` and `∑_{u ∈ G} ‖F_a(u)‖² = n·|∑_A a_A|²`, a
rank-one functional of `a`. The G241 probe measured the subgroup sum as `0.0005–0.019 · (n·m·‖a‖²)`
across sponsor cells — a tiny fraction, off by 1.5–4 orders of magnitude. The `n·m` energy lives on
`F_p^*` (cardinality `n·m`), not on `G`. The G240 theorems are *vacuously safe* (the hypothesis is
never discharged), but discharging them as written would smuggle the same carrier error one level up.

## Fix

Run the fiber map `x ↦ class(2 − x)` over the **carrier** `C = F_p^*` (cardinality `n·m`), where:

- the input Parseval `∑_{x ∈ C} ‖F x‖² = n·m·‖a‖²` genuinely holds (G241 `(L)`, exact); and
- the fiber ceiling is `#{x ∈ C : class(2 − x) = d} ≤ n`, because a carrier that is a disjoint union
  of `m` quotient classes each of size `≤ n` has every class-fiber of size `≤ n`.

The `n·(n·m)/m = n²` cancellation is unchanged; only the index set is corrected.

## Probe (`scripts/probes/g242_carrier_correct_quotient_largesieve_probe.py`)

Builds `G = ⟨g^m⟩`, quotient class map `cls(x) = dlog(x) mod m`, and the Fourier polynomial
`F_a(x) = ∑_{j<m} a_j ζ_m^{j·cls(x)}` on `F_p^*`. Checks, on 5 sponsor cells (`2 ∉ G`):

```
n=  8 p=  1009 m=  126  maxfiber=  8 (<=n:True)  L_ok=True  class<=n*input=True  out<=n^2||a||^2=True
n= 16 p=  1297 m=   81  maxfiber= 16 (<=n:True)  L_ok=True  class<=n*input=True  out<=n^2||a||^2=True
n= 32 p=  2593 m=   81  maxfiber= 32 (<=n:True)  L_ok=True  class<=n*input=True  out<=n^2||a||^2=True
n= 16 p=  3617 m=  226  maxfiber= 16 (<=n:True)  L_ok=True  class<=n*input=True  out<=n^2||a||^2=True
n= 64 p=  4673 m=   73  maxfiber= 64 (<=n:True)  L_ok=True  class<=n*input=True  out<=n^2||a||^2=True
```

The fiber ceiling on `F_p^*` is `= n` exactly (each quotient class of `2−x` has exactly `n`
preimages), the `(L)` input Parseval holds exactly, and `outputEnergy ≤ n²‖a‖²` holds — all with the
correct carrier.

## Formal payload (`Frontier/_G242CarrierCorrectQuotientLargeSieve.lean`)

- `fiber_le_of_class_size_bound` — per-class size bound `#(fiber) ≤ n` ⇒ real fiber ceiling `≤ n`.
- `carrier_card_le` — a carrier classifying into `m` classes of size `≤ n` has `#C ≤ n·m`
  (via `card_eq_sum_card_fiberwise`), the structural budget that pins the `n·m` normalization.
- `carrier_largesieve_of_fibers` — the operator bound `outputEnergy ≤ n²·‖a‖²` with the fiber map
  on the carrier `C` and the honest `∑_{x∈C}‖F x‖² = n·m·‖a‖²` input, delegating to G240's
  index-set-agnostic `quotient_largesieve_of_fibers`.
- `l2_mass_floor_of_carrier_fibers` — the G233 coefficient mass floor `m − n ≤ 4·n·‖a‖²` with the
  carrier-correct discharge path.

Axioms (all four): `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Locked build 3302 jobs.

## Scope / frontier

Correctness repair only. It makes the input-(A) discharge path carrier-honest, so the remaining
Mathlib obligation is the `(L)` Parseval on the size-`n·m` carrier (quotient-character orthogonality
on `Q ≅ ℤ/m` lifted over the `n`-fold fibers of `F_p^* → Q`) and the per-class size bound, both true.
Does NOT consume the target, does NOT weaken BGK/Paley, supplies no signed phase estimate. The SOLE
live prize face remains the per-rank signed sponsor-prime estimate
`Re ∑_{χ≠1} Ŵ(χ) conj(R̂_r(χ)) > 0` via explicit cyclotomic Stickelberger/Gross–Koblitz or
large-monodromy phase input, independently at r=5 and r=6. CORE OPEN / ON-BGK.
