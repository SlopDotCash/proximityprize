# Unify-A: the supply Spur_r and demand e2=0 defects are ONE object (consolidation, 2026-06-17)

**Issue #444 · proximity prize.** Task Unify-A: compute the supply-side char-p surplus
`Spur_r = E_r(μ_n) − E_r^{c0}` and the demand-side `e2=0` halo defect at matched parameters and
test whether they are the same object. **Verdict: CONSOLIDATION — same generating object, not a
new bound.** No bound on `Spur_r` is claimed (honesty contract upheld).

Probes (EVIDENCE, exact, not proof):
- `scripts/probes/probe_444_unifyA_supply_demand_identity.py` (both defects, bad-prime sets)
- `scripts/probes/probe_444_unifyA_depth_and_normsupport.py` (depth + norm-support generator)
- `scripts/probes/probe_444_unifyA_verdict.py` (exact identity + BabyBear/KoalaBear proxy)

## 0. CALIBRATION CORRECTION (load-bearing)

The CONTEXT/synthesis claim `E_r^{c0} = (2r−1)!!·n^r` is **NOT exact — it is a leading-order
UPPER bound.** Brute-forced exact char-0 energy (cyclotomic ℚ-basis `1..ζ^{n/2−1}`, matches the
in-tree `probe_char0_energy_check_407.py`):

| n | r | E_r^{c0} brute (EXACT) | (2r−1)!!·n^r |
|---|---|---|---|
| 8  | 2 | **168** | 192 |
| 8  | 3 | **5120** | 7680 |
| 16 | 2 | **720** | 768 |
| 16 | 3 | **50560** | 61440 |
| 32 | 2 | **2976** | 3072 |

`E_1^{c0} = n` exactly (sanity). The `(2r−1)!!` over-counts because diagonal/overlapping pairings
coincide. **The exact baseline for `Spur_r` is the BRUTE value, not the formula.** Using the formula
inflates the baseline and would HIDE real char-p surplus.

## 1. The two defects share the SAME generating object

Define `G_k(n) = { p ≡ 1 mod n : p | N(α) for some α = sparse signed sum of ≤ k of the 2^μ-th
roots, α ≠ 0 in ℤ[ζ_n] }`, where `N(α) = Res(Φ_n, α)` is the cyclotomic field norm. Both defects
are norm-divisor supports of this object:

- **SUPPLY** `Spur_r > 0` ⟺ the additive-energy relation `α = (Σᵢ zᵢ) − (Σⱼ z'ⱼ)` (a `{±1,…,±r}`-
  coefficient combination of ≤ 2r roots) vanishes mod p but not in ℤ[ζ] ⟺ `p ∈` the norm support at
  depth ≤ 2r.
- **DEMAND** `e2=0` RISE carrier on size-w `S` ⟺ `α = e₂(S)` (a +1 sum of `C(w,2)` root-products)
  vanishes mod p but not in ℤ[ζ] ⟺ `p | N(e₂(S))` (the kb `deltastar-407-e2zero-modq-defect`
  carrier-onset law).

## 2. EXACT identity (machine-verified, small n)

At **n = 16, depth 6** (supply r=3 ↔ ≤6-term relations):

```
SUPPLY Spur_3>0 = G_6 = {17,97,113,193,241,257,337,353,401,433,449,577}   EXACTLY EQUAL
```

At n=8 depth 6: `Spur_3 = {17,41,73,89,97,137}` ⊇ `G_6(±1,distinct) = {17,41,73}`. The gap is the
**multiplicity** part of the energy relation: supply allows a root with coefficient 2 (a repeat).
Explicit witnesses (`p | N(α)`):
- n=8, p=41: `α = ζ⁰ − ζ¹ − 2ζ⁴`, `N(α) = 82 = 2·41`.
- n=16, p=193: `α = ζ⁰ − ζ¹ − 2ζ⁸`, `N(α) = 6562 = 2·193`.

So the supply object is `{±1,±2,…}`-coefficient ≤2r-root relations; the pure-±1 distinct-root
generator `G_{2r}` equals it exactly once the depth is large enough to absorb repeats (n=16, r=3).

## 3. DEMAND ⊆ SUPPLY (matched depth) — strict subset of the SAME relations

At **n=16, depth 6**:
```
SUPPLY Spur_3      = {17,97,113,193,241,257,337,353,401,433,449,577}
DEMAND e2=0 (w=6)  = {17,97,113,193,241,257,337,353,        433     }   ⊆ SUPPLY
SUPPLY ∖ DEMAND    = {401, 449, 577}
```
The three missing primes `{401,449,577}` are **exactly** the kb-documented no-carrier primes for the
n=16 `e2=0` object (`deltastar-407-e2zero-modq-defect` §3, cross-validated by a second probe). The
`e2(S)` carrier is a special **+1-only** sum of products and reaches a strict subset of the signed
relations the additive energy reaches; it misses `{401,449,577}` because no `e2(S)` realizes the
signed/repeated relations whose norm those primes divide — but the supply energy does.

## 4. char-0 proxy calibration (BabyBear / KoalaBear)

For huge `2^μ | p−1` (BabyBear `p=2013265921`, `2^27|p−1`; KoalaBear `p=3221225473`, `2^30|p−1`),
`Spur_2(μ_n) = 0` for n=8,16: no ≤4-root relation has small enough norm to vanish mod a ~10⁹ prime.
This is the char-0-proxy regime — the prize wall lives at `r ~ log m ≈ 128`, where the relation
norms reach prize size and `p | N(α)` becomes possible. (Calibrates the proxy; does NOT bound the
prize.)

## 5. Honest verdict

**CONSOLIDATION, not closure.** `Spur_r` (the supply prize wall) and the `e2=0` halo defect (the
demand-side machinery NOT in the §2 no-go map) are the SAME object: short signed `±`-relations of
`2^μ`-th roots that vanish mod p but not in `ℤ[ζ]`, indexed by `{p : p | N(α)}`. Demand is a
strict-subset *reach* of the same relations (it sees fewer α's), so a demand bound does **not**
bound `Spur_r` — demand is too weak (misses signed/repeated relations supply needs). This is a
genuine *unification* of two faces of the wall (the demand machinery was thought possibly
independent; it is not — it is a sub-object of the energy surplus), but it is **not** new movement
on the bound. The open core is unchanged: bound `N(α)` over short `±`-relations at depth `r ~ log m`
= the 25-year thin-subgroup BGK wall.

| axis | score | note |
|---|---|---|
| novelty | 6 | first explicit demand⊆supply nesting + the `{401,449,577}` cross-validation |
| insight | 8 | corrects the `(2r−1)!!` calibration; pins both defects to one norm-divisor object |
| proximity | 5 | consolidates two faces; does NOT bound Spur_r (honestly) |
| feasibility | 4 | the magnitude of `N(α)` at `r~log m`, `n=2^30` is the open residual |

**No closure claimed.** Cross-refs: `deltastar-407-e2zero-modq-defect`,
`deltastar-444-frontier-synthesis-NOLARP-2026-06-16`, memory `arklib-444-onBGK-verdict-settled`.
