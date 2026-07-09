# δ\* ceiling constant `c(ρ) = H₂(ρ)` — in-tree formalization (issue #444, 2026-06-15)

**Goal.** Ground the closed-form δ\* ceiling constant `c(ρ) = H₂(ρ)` (binary entropy) **in tree**,
axiom-clean — so the Route-2 conjecture `δ*(ρ,n) = (1−ρ) − H₂(ρ)/log₂ n`
(`deltastar-444-route2-closed-crho-H2-2026-06-15.md`) has its constant derived in-tree, not just
cited. Prior in-tree work (`KKH26EntropyForm.lean`, `KKH26AsymptoticCeiling.lean`) carried only the
weaker dyadic line family with native rate `Φ(ρ) = ρ + ½H₂(2ρ)`; the **binding** (larger) family is
KKH26 (ePrint 2026/782) Appendix-A's **list-center** family, with per-symbol exponent `H₂(ρ)`.

**Deliverable file:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/ListCenterEntropyCeiling.lean`
(namespace `ArkLib.ProximityGap.KKH26`). Validated axiom-clean via `scripts/pg-iterate.sh`
(`✅ OK (32s)`, audit = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no warnings).

---

## The math (KKH26 Appendix A / Remark 5, list-center family)

A single deep-hole-type word `u = x^{rm}` has a large list of close RS codewords: they correspond to
the vanishing polynomials `v_S(X^m)` over `r`-subsets `S` of a size-`s` subgroup `G ⊆ μ_n`. Remark 5
("different subsets give different vanishing polynomials") makes the list size **exactly** `C(s, r)`
— a binomial, **no additive combinatorics**. With `r = ρ·s`, method of types gives
`log₂ C(s, ρs) = s·H₂(ρ)·(1−o(1))`, so the per-symbol exponent is `H₂(ρ)`, **strictly larger** than
the line family's `Φ(ρ) = ρ + ½H₂(2ρ)`. The larger constant **binds** (smaller δ\*), so
`c(ρ) = max(H₂, Φ) = H₂(ρ)`. Crossover at the prize budget `2^{c/η} = ε*·|F| ≈ n = 2^μ` gives the
cushion `η* = c(ρ)/log₂ n` and the closed ceiling value `δ* = (1−ρ) − H₂(ρ)/log₂ n`.

---

## Theorems that landed axiom-clean (exact statements + audit)

All in `ArkLib.ProximityGap.KKH26`. Audit for every one: `[propext, Classical.choice, Quot.sound]`.

Definitions: `listCenterRate ρ := Real.binEntropy ρ / Real.log 2` (= `H₂(ρ)` in bits);
`lineRate ρ := ρ + Real.binEntropy (2ρ)/(2 log 2)` (= `Φ(ρ)`);
`deltaStarCeilingEntropy ρ n := (1−ρ) − listCenterRate ρ / Real.logb 2 n` (= the closed ceiling value).

1. **`listCenter_count_ge`** (UNCONDITIONAL combinatorial count, the method-of-types deliverable):
   for `0 < r < s`,
   `(2:ℝ)^(s · listCenterRate (r/s)) / (s+1) ≤ (s.choose r : ℝ)`.
   Reuses `KKH26EntropyForm.choose_ge_two_rpow_entropy_div` (not re-proved); the entropy exponent
   `s·H₂(r/s)` is exactly `s·listCenterRate (r/s)`. This is `C(s,r) ≥ 2^{s·H₂(r/s)}/(s+1)`.

2. **`listCenterRate_gt_lineRate`** (the BINDING comparison, GENERAL on `(0,1/2]`):
   for `0 < ρ ≤ 1/2`, `lineRate ρ < listCenterRate ρ`, i.e. `Φ(ρ) < H₂(ρ)`.
   Proof: clear `log 2`; the cleared numerator equals (exact identity, via `log_div` splitting + `ring`)
   `½·a·log a − ((1+a)/2)·log((1+a)/2)` with `a = 1−2ρ ∈ [0,1)`; positivity is the **strict-convexity
   midpoint step** for `x ↦ x log x` (`Real.strictConvexOn_mul_log` at the midpoint of `a < 1`,
   `g((a+1)/2) < ½g(a)+½g(1) = ½g(a)`). NOT `norm_num` — a real proof valid for **all** `ρ ∈ (0,1/2]`.

3. **`listCenterRate_gt_lineRate_half`** (closed value at `ρ=1/2`): `lineRate (1/2) < listCenterRate (1/2)`,
   i.e. `Φ(1/2) = 1/2 < 1 = H₂(1/2)`. Supporting: `listCenterRate_half : listCenterRate (1/2) = 1`
   (via `binEntropy_eq_log_two`), `lineRate_half : lineRate (1/2) = 1/2` (via `binEntropy_eq_zero`).

4. **`deltaStar_ceiling_entropy_of_TZ`** (the CONDITIONAL ceiling, packaged on the named hypothesis):
   given `TZPrimeSupply n β supply` (the cited [TZ24] Thorner–Zaman PNT-in-APs input — a named
   `Prop`-hypothesis, NEVER an axiom, the §6 modularity convention, exactly the `kkh26_…_of_TZ`
   pattern) plus the bad-prime budget `hcount`, there is a prime `p = Θ(n^β)` and a smooth domain
   `⟨g⟩ ⊆ F_p^×` of order `n` such that for every `ε*` below the list budget the formal MCA threshold
   `mcaDeltaStar(evalCode g n ((r−2)m), ε*) ≤ 1 − r/2^μ` — the finite-parameter form of the entropy
   ceiling at polynomial field size. A verbatim re-export of `KKH26PolyFieldCeiling.kkh26_mcaDeltaStar_le_of_TZ`.

Supporting lemmas (also axiom-clean): `mul_log_midpoint_lt` (the convexity engine),
`listCenterRate_half`, `lineRate_half`, `deltaStarCeilingEntropy_eq`.

---

## Is `H₂ > Φ` proven for all ρ or just the 4 rates?

**Proven for ALL `ρ ∈ (0, 1/2]`** (`listCenterRate_gt_lineRate`), via strict convexity of `x log x`
— NOT a per-rate `norm_num`. The four prize rates `1/2, 1/4, 1/8, 1/16 ∈ (0,1/2]` are immediate
instances. Numerics (`H₂ − Φ`, exact): `ρ=1/2 → 0.500`, `ρ=1/4 → 0.061`, `ρ=1/8 → 0.013`,
`ρ=1/16 → 0.003`; gap `→ 0` as `ρ → 0` (they agree only in the limit), positive throughout `(0,1/2]`.
The binding constant `c(ρ) = max(H₂,Φ) = H₂(ρ)` at all four prize rates: `1.000, 0.811, 0.544, 0.337`.

---

## Honest status of the conditional ceiling

- **Combinatorial entropy count** (`listCenter_count_ge`) and **binding comparison**
  (`listCenterRate_gt_lineRate`): UNCONDITIONAL, axiom-clean. These ground the constant `H₂(ρ)`
  in tree.
- **Prize-scale ceiling** (`deltaStar_ceiling_entropy_of_TZ`): CONDITIONAL on the single named
  hypothesis `TZPrimeSupply` (+ numeric budget `hcount`), inherited verbatim from the in-tree
  `kkh26_mcaDeltaStar_le_of_TZ`. `TZPrimeSupply` is the cited [TZ24] analytic input (log-free
  zero-density estimates; holds unconditionally for `β > 12/5`, and for every `β > 1` under
  Montgomery's conjecture) — named per §6 modularity, never proved here, never an axiom.
- **The FLOOR is NOT proven.** That the worst-window list actually *reaches* `2^{s·H₂(ρ)}` at the
  prize prime — so the ceiling is *tight* and the conjecture `δ* = (1−ρ) − H₂(ρ)/log₂ n` is an
  *equality* — is the recognized open prize (BGK/Paley house bound, faces 3↔4 of the open core).
  **The conjecture is NOT claimed proven.** Only the ceiling constant is grounded; tightness is open.

**Net.** The constant `c(ρ) = H₂(ρ)` in the Route-2 closed-form conjecture is now grounded in an
in-tree, axiom-clean derivation: the exact list size `C(s,r)` has per-symbol entropy rate `H₂(ρ)`
(`listCenter_count_ge`), and `H₂(ρ)` provably exceeds the in-tree line-family rate `Φ(ρ)` on all of
`(0,1/2]` (`listCenterRate_gt_lineRate`), so it is the binding constant. The δ\* equality remains the
open problem.
