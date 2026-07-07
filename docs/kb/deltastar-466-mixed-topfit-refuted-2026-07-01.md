# #466 lane L1 — the mixed-profile top-fit route is REFUTED at prize shape (2026-07-01)

**Verdict: REFUTED as a closure path.** The `z = n` top-endpoint contraction of the mixed-profile
route (`mixedChooseProfileCardSum_le_topCard` → `Low/FullMixedChooseProfileTopSumsFit`,
`FieldPowMixedProfileTopFit`, `FieldPowFullMixedProfileTopFit` in
`LineListAppearanceFiberMixedProfileFit.lean`) is **jointly unsatisfiable** with the downstream
fiber budget `UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits a B ·` at every prize
shape — for **every** exact budget `Mexact`, not just the field-power instantiation. The
low-profile split (dossier §6 Tier-1 item 2, second bullet) is now **mandatory**: no choice of
budget functions can push the mixed choose-profile sums through the weld.

## The arithmetic that was decided

The top fit demands, for each low profile `t < min(a,k)` (all `t < a` in the full form):

```
S(t) := Σ_{r=0}^{a-1} C(n−t, r−t) · (r < k ? Mexact(r) : 1)  ≤  Mcoarse(t)
```

with field-power instantiation `Mexact(r) = q·C(n, a−r)·q^{k∸a}` (`k∸a = 0` in-window since
`a > k`, so `Mexact(r) ≥ q`). The consumer then needs the fiber fit: for every direction `u₁`
with `z = #zeroSet(u₁) ≥ a`,

```
Σ_{t<a} C(z,t) · Mcoarse(t) · ⌊(n−z)/(a−t)⌋  ≤  B ,
```

and the weld `mcaDeltaStar_ge_of_farLineListBudgeted` caps `B ≤ ε*·q` (`ε* = 2^−128`; the
task-shaped budget `B ≈ ρn` is the same order for `q ≈ n·2^128`).

## The countermodel mechanism (two independent kills)

**The step direction `u₁ = (0,…,0,1,…,1)` with exactly `a` zeros** is large-zero
(`¬SupportEligibleLineDirection a u₁`) and, at any `t₀ < a` with `a − t₀ ≤ n − a`, has fiber
coefficient `C(a,t₀)·⌊(n−a)/(a−t₀)⌋ ≥ 1`, so the fiber fit forces **`Mcoarse(t₀) ≤ B`**.
Every prize shape admits such a `t₀ < k`: take `t₀ = max(0, 2a−n)` (`= 0` for `ρ ≤ 1/4` since
in-window `a < √ρ·n ≤ n/2`; for `ρ = 1/2`, `2a−n < k` ⟺ `a < 3n/4` ✓). Against this cap:

1. **Field-power kill (kills `FieldPow*TopFit`).** The same-profile term `r = t₀` of `S(t₀)` is
   `q·C(n, a−t₀)·q^{k∸a} ≥ q`, so the top fit forces `Mcoarse(t₀) ≥ q`. Joint UNSAT whenever
   `B < q` — and the weld gives `B ≤ ε*·q = q/2^128`. **The field-size factor `q` in the
   field-power envelope can never fit below a sub-`q` bad-scalar budget.**
2. **Mexact-independent kill (kills `Low/FullMixedChooseProfileTopSumsFit` for EVERY `Mexact`,
   even `Mexact ≡ 0`).** In-window `a > k`, so the high singleton `r = a−1` charges
   `C(n−t₀, (a−1)−t₀)` regardless of `Mexact`. Joint UNSAT whenever `B < C(n−t₀, a−1−t₀)`
   `≈ 2^{n·H(a/n)}` — astronomically above any polynomial budget.

**Root cause (structural):** the endpoint contraction `mixedChooseProfileCardSum_le_topCard`
majorizes the profile sum at `z = n`, where the fiber coefficients are all **zero** (support
`s = n−z = 0`), and imposes it at `z ≈ a`, where the budget **binds** but the true choose-factors
would only be `C(a−t, r−t)`. The contraction decouples exactly the wrong pair: it evaluates the
sum where the budget is vacuous and pays for it where the budget is live. (Note: the numerics
show the z-aware `FieldPow*CardFit` dies too — kill 1 is z-independent, and even at `z = a` the
high terms `C(a−t, r−t)` for `r ∈ [k,a)` are exponential — so the failure is not an artifact of
the endpoint alone; but the endpoint form is what round-#464 contracted to, and it is dead.)

## Evidence

- **Probe (exact big-int arithmetic, Lean natural-subtraction semantics):**
  `scripts/probes/probe_466_mixed_topfit_endpoint.py` →
  `scripts/probes/_out_466_mixed_topfit_endpoint.txt`.
  - Exact scan `ρ ∈ {1/2,1/4,1/8,1/16}`, `μ = 4..12`, three in-window `a` per shape
    (`k+2`, midpoint, `⌊√ρ·n⌋`), `q ≈ n^4` and `q ≈ n·2^128` (real primes `≡ 1 mod n`),
    `B ∈ {ρn, ⌊ε*q⌋}`: **416/416 FAIL, 0 HOLD**. Smallest violation 22.9 bits
    (ρ=1/16, μ=4); typical violations hundreds to thousands of bits.
  - Binding summand: interior `r` (the product `C(n−t₀,r−t₀)·q·C(n,a−r)` maximizes mid-range);
    the pure `r = t₀` field-power term and the pure `r = a−1` singleton term are each
    *individually* over budget in every row (`lg E_fp`, `lg S_high` columns).
  - `μ = 30` Stirling: violation ≈ **0.36–1.07 ×10⁹ bits** (`lg S_high ≈ n·H(a/n)` vs
    `lg B ≤ 30`), at all four rates and all three `a` anchors.
- **Lean brick (axiom-clean, `[propext, Classical.choice, Quot.sound]`):**
  `ArkLib/Data/CodingTheory/ProximityGap/Frontier/MixedTopFitBudgetIncompatibility.lean`
  - `directionZeroSet_step_card` / `directionSupportSet_step_card` — the step-direction
    countermodel geometry;
  - `mcoarse_le_budget_of_uniformFiberFits` — the fiber cap `Mcoarse(t₀) ≤ B`;
  - `not_fieldPowMixedProfileTopFit_and_uniformFiberFits` (+ `Full` variant) — kill 1 as a
    general-parameter theorem (`B < q` ⟹ joint `False`);
  - `not_exists_lowMixedChooseProfileTopSumsFit_and_uniformFiberFits` (+ `Full` variant) — the
    headline: `∀ Mexact Mcoarse`, joint UNSAT once `B < C(n−t₀, a−1−t₀)` (kill 2);
  - `not_exists_mixedTop_n16_prizeShape` — concrete `ρ = 1/4` scale model (`n=16, k=4, a=7`,
    `B ≤ 4`; binding binomial `C(16,6) = 8008`).

## What this changes on the frontier (dossier §6 Tier-1 item 2)

- The **mixed-profile top-fit sub-obligation is DECIDED (refuted)**: strike the
  "prove/refute `Low/FullMixedChooseProfileTopSumsFit`, `FieldPow*TopFit`" bullet.
- The surviving low-profile obligations are exactly the *other* bullets: the **low-profile
  theorem** (`D(t)` bounds for `t < k` on large-zero-safe lines with the combined
  `puncturedWeight + Σ choose·D(t) ≤ 2B` fit — note it must NOT route the high profiles
  through ambient choose-sums, per the root cause above), the **second-witness/multiplicity
  floor**, and **`CandidateListExactSuccessor`**.
- Any future fiber-budget consumer must keep the `z`-dependence of BOTH sides coupled: envelopes
  monotone in `z` are only usable if the budget coefficient is also evaluated at the same `z`.
  A per-`z` *ratio* fit (sum(z)/budget-coefficient(z)) is the only shape not yet excluded — but
  kill 1 shows any envelope carrying a bare factor `q` is dead at every `z`, so the exact fibers
  themselves must be sub-`q` (which is precisely the low-profile theorem's job).

DISPROOF_LOG tag: `466-r2-mixed-topfit-budget-unsat`.
