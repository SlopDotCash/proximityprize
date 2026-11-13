# δ* #444 — the [padic-newton-spur] 2-ADIC SPUR STRATIFICATION: REDUCES-TO-WALL (B2) (2026-06-17)

**Angle (wall-side, untried slot).** The p-adic / Newton-polygon structure of the SPUR carriers,
stratified by the **2-adic valuation** (Stickelberger digit sums). A spur carrier is a `±1`
relation `α = Σ ε_i ζ_n^{a_i}` of `≤ 2r` `n`-th roots (`n = 2^μ`) with `α ≠ 0` in `ℂ` but
`p ∣ N(α)` (vanishes at `ζ_n ↦ ω ∈ F_p`, `p ≡ 1 mod n`). Since `ζ_n` is a `2^μ`-th root,
`ℚ(ζ_{2^μ})` is **totally ramified at 2** (`(2) = (λ)^{2^{μ−1}}`, `λ = 1−ζ`), so the 2-adic
structure is non-archimedean and rich. **Hope:** does `v_2 / v_λ` of the spur carriers grow with
depth `r` in a way that bounds the deep-`r` spur (a handle the archimedean BGK wall misses)?

**Verdict: REDUCES-TO-WALL (B2, wrong norm).** No non-archimedean handle; not refuted (no false
claim); the `√n`-cancellation open core is untouched. Three exact probes + one axiom-clean Lean file.

## The three machine-confirmed facts (the 2-adic slot is p-blind)

Probes `scripts/probes/probe_444_padic_newton_spur_2adic{,_deep,_realbeta}.py` (exact, PROPER `μ_n`,
`p ≫ n³`, never full group). They extract the GENUINE cyclotomic spur carriers (`α ≠ 0`, `p ∣ N(α)`)
at minimal depth and tabulate `v_2(N(α))` vs `v_p(N(α))`.

1. **The 2-part is a FIXED, p-INDEPENDENT factor.** Minimal-weight carriers (`weight = 8`, `r* = 4`)
   at `n = 16` and `n = 32` have norm **exactly `N(α) = 2·p`**: `v_2(N) = 1`, `v_p(N) = 1`, with the
   two prime slots DISJOINT (`p` odd). The `2` is the totally-ramified `λ = 1−ζ` content; the `p` is
   the F_p-vanishing content. (`..._deep`: `v_2 dist = {1:60}`, `v_p dist = {1:60}`, `N = {2:1, p:1}`.)
2. **`v_2(N)` does NOT grow with depth.** `r* = 4`: `{1:64}`; `r = 5`: `{1:183, 2:9, 4:8}` — bounded
   `O(1)`, NOT `Θ(r)`. No Stickelberger 2-adic lower bound on `|N|` grows with depth, while
   `v_p(N) ≡ 1` is the operative slot at every depth. (`..._realbeta` (ii).)
3. **`v_2` is BLIND to which `p` is bad.** Carrier existence at depth `r` is p-DEPENDENT (faithfulness
   depth law): the Fermat prime `p = 65537 = 2^16+1` has an `r* = 4` carrier; the next 11 primes
   `≡ 1 mod 16` have NONE at `r = 4`. The 2-adic slot `v_2 = 1` is the same constant regardless, so it
   cannot detect the p-dependent badness. (`..._realbeta` (iii).)

## Why B2 (wrong norm) and not a handle

The norm factors `N(α) = 2^{v_2} · p^{v_p} · (rest)` with `p` ODD, so `v_2(N)` and `v_p(N)` are
DISJOINT prime slots: knowing the 2-adic content tells you nothing about the F_p-vanishing slot
`p^{v_p}`, which IS the entire spur signal. The non-archimedean handle is a p-independent BOUNDED
factor — the same verdict as the prior 2-adic Stickelberger sweeps (`_wf407_stickelberger*`: "max
lives in the unit part, valuation-blind") and the vacuous-2-adic-Newton-polygon fact
(`_NewtonPolygonPeriodSpread.lean`). It does NOT supply E1 (it is a magnitude, not the L∞ sup), and
fails E2/E3 (the 2-adic object is orthogonal to the p-slot). Wall-real, no closure.

## Distinct from the sibling p-adic file

`_PadicBakerDefectCeiling.lean` handled the **p-adic** valuation `v_p(N(α))` via Baker/Yu and showed
it (a) is wrong-direction and (b) collapses to the archimedean `(2r)^{n/2}` height wall. THIS file
handles the **2-adic** (Stickelberger) valuation `v_2(N(α))` and shows it is a disjoint p-independent
bounded factor. Complementary slots; same wall.

## Files

- `Frontier/_PadicNewtonSpur2Adic.lean` — 6 axiom-clean thms `[propext, Classical.choice, Quot.sound]`,
  0 `sorryAx`. Key: `minimal_carrier_valuations` (`N = 2p` ⟹ `v_2 = v_p = 1` disjoint),
  `two_adic_content_blind_to_spur` (same 2-adic content, opposite spur status across odd primes),
  `two_adic_undercounts_deep_spur` (bounded 2-content under-counts depth-growing spur),
  `padic_newton_spur_verdict` (packaged).
- `scripts/probes/probe_444_padic_newton_spur_2adic.py` — T1 faithfulness depth law (`SPUR_r`),
  T2/T3 first-carrier `v_2` vs `v_p`.
- `scripts/probes/probe_444_padic_newton_spur_2adic_deep.py` — genuine cyclotomic carriers, `N = 2p`,
  60/60 with `p ∣ N`.
- `scripts/probes/probe_444_padic_newton_spur_2adic_realbeta.py` — p-independence (iii), depth (ii),
  beta robustness (i).
