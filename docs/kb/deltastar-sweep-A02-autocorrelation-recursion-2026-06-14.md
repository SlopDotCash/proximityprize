# δ* sweep A02 — char-p autocorrelation recursion E_{r+1}=n·E_r+cross_r and the free deep tail

Date: 2026-06-14 · Actionable A02 (merged 407-T28 ; 389-T28) · type: lean-brick + probe

## Object

`H = μ_n ⊆ G = ℤ/p` (or any finite abelian group). `f_r = 1_H^{*r}` the r-fold sumset count,
`f_r(z) = #{(x_1..x_r)∈H^r : Σx=z}`. The 2r-fold additive energy is the L²-mass

    E_r = Σ_z f_r(z)² = #{(x,y)∈H^{2r} : Σx=Σy} = C_r(0),

where `C_r(z) = Σ_w f_r(w)·f_r(w−z)` is the autocorrelation of `f_r`. `E_r` is the prize quantity:
the 2r-th Parseval moment of the worst incomplete character sum is `Σ_b‖η_b‖^{2r} = q·E_r`
(EnergyCharacterTransport, r=2), and the moment method gives `B = max_{b≠0}‖η_b‖ ≤ (q·E_r)^{1/2r}`
(CharSumMomentDeepWall).

## The exact recursion (PROVEN, axiom-clean, char-free)

Peeling one convolution factor `f_{r+1}(z) = Σ_{u∈H} f_r(z−u)` and expanding the square:

    E_{r+1} = Σ_z f_{r+1}(z)² = Σ_{u,v∈H} C_r(v−u) = n·E_r + cross_r,
    cross_r := Σ_{(u,v)∈H×H, u≠v} C_r(v−u).

The diagonal `u=v` gives `n` copies of `C_r(0)=E_r`; the rest is `cross_r`. This is an IDENTITY in
every characteristic (G arbitrary finite abelian), so it is the genuine char-p recursion.

`Frontier/Sweep_A02_AutocorrelationRecursion.lean :: energy_succ_eq`.

## The trivial cross bound ⟹ crude energy bound (PROVEN)

Autocorrelation is maxed at the origin, `C_r(z) ≤ C_r(0) = E_r` (Cauchy–Schwarz + translation
invariance; `autocorr_le_energy`). There are `n(n−1)` off-diagonal pairs, so `cross_r ≤ (n²−n)E_r`
(`crossTerm_le`), hence the crude recursion bound

    E_{r+1} ≤ n²·E_r            (`energy_succ_le_sq`)

and iterating from `E_1 = n`:  `E_r ≤ n^{2r−1}` (the crude closed form).

## The free deep tail (the A02 deliverable, PROVEN)

Deep-moment-validity DM_r is the char-0 clean / Gaussian energy value (the cone's
`GaussianEnergyBound`; the value that makes the transport `B≤(q·E_r)^{1/2r}` give the prize
`B≲√(n log q)` at the optimum `r≈log q`):

    DM_r:  E_r ≤ (2r−1)‼·n^r.

[Probe confirms the char-0 energy hugs this from below: E_1=n=1‼·n; E_2=3n²−3n ≤ 3n²=3‼·n²;
E_3=5120 ≤ 7680=15‼·8³ at n=8. The earlier `n^{r-1}` form was a mis-division and is FALSE at small r
— corrected here.]

The crude bound `E_r ≤ n^{2r−1}` ALREADY implies DM_r exactly when

    n^{2r−1} ≤ (2r−1)‼·n^r   ⟺   n^{r−1} ≤ (2r−1)‼.       (`free_deep_tail`, `crude ⟹ DM`)

By Stirling `(2r−1)‼ ≈ √2·(2r/e)^r`, so `n^{r−1} ≤ (2r−1)‼` holds for all `r ≥ ⌈e·n/2⌉ ≈ 1.359·n`.

Probe `sweep_A02_autocorr.py`: the exact integer threshold `r*` (crude⟹DM for ALL r≥r*) has
`r*/n = 1.125, 1.188, 1.250, 1.297, 1.320, 1.336` at n=8,16,32,64,128,256 → `e/2 = 1.359`, and
`r* ≤ ⌈e n/2⌉` at every n. Decidable Lean witnesses: `free_tail_n8` (`8^10 ≤ 21‼`), `free_tail_n16`
(`16^21 ≤ 43‼`), below-crossover failure `free_tail_n8_below` (`8^7=2097152 > 2027025=15‼`). So: for
r ≥ ⌈e n/2⌉ ≈ 1.36n the deep-moment-validity DM_r holds UNCONDITIONALLY — no char-0/Lam–Leung input,
no char-p transfer. **This is the free deep tail.**

## HONEST verdict — PARTIAL, prize-irrelevant tail

The free deep tail is genuinely unconditional, but the band it covers (`r ≥ 1.36n`) is
ASTRONOMICALLY above the moment optimum `r ≈ log q` the prize needs. Concretely at the prize
(`q ≈ n·2^128`, `n=2^a`): `ln q ≈ 89..117` for `a∈[25,40]`, so `r_opt ~ a few hundred`, while
`1.36n = 1.36·2^a` is ~2^25..2^40. The free tail is a factor ~2^a/(log q) too deep to help.

So A02 does NOT close the prize. What it establishes:
- the EXACT char-p recursion `E_{r+1}=n·E_r+cross_r` (new in-tree, axiom-clean);
- a closed-form region `[1.36n, ∞)` where DM_r is free (the only region the crude bound suffices);
- the genuine residual is `cross_r` (equivalently `E_r`) in the intermediate band
  `[β·log n, 1.36n)`, which CONTAINS the moment optimum `r ≈ log q`. Stated as the named Prop
  `CrossBandResidual`; non-vacuity recorded (`residual_band_nonempty_n8`,
  `free_tail_n8_below`). This is the SAME wall as `CharSumMomentDeepWall` (the char-p validity
  transfer of the char-0 clean value at the prize prime), now localized to the band below 1.36n.

## What would have to happen to make the tail useful (negative)

To exploit the recursion below 1.36n you need a NON-TRIVIAL `cross_r` bound: the autocorrelation
`C_r(z)` at the `n(n−1)` shifts `v−u` (`u,v∈H`) must be shown to be `o(E_r)` on average, not just
`≤ E_r`. That average-of-autocorrelation control is exactly the square-root cancellation of the
`(p−1)/n` Gauss-sum phases `χ̄(b)τ(χ)` — the open core. The recursion re-expresses, but does not
weaken, that wall.

## Artifacts

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A02_AutocorrelationRecursion.lean`
  (axiom-clean: `energy_succ_eq`, `crossTerm_le`, `energy_succ_le_sq`, `free_deep_tail`,
   `free_tail_n8/n16/n8_below`, `CrossBandResidual`, `residual_band_nonempty_n8`).
- `scripts/probes/sweep_A02_autocorr.py` (exact recursion + autocorr-cap + crude-vs-DM at
   n=8,16,32; free-tail crossover table; prize-relevance check).

## Cross-refs

- `CharSumMomentDeepWall.lean` — the moment transport `B ≤ (q·E_r)^{1/2r}` and the deep-moment wall
  (r_max = 2 log_n p; r_opt ~ log q). A02 supplies the recursion behind `E_r` and the free tail.
- `AutocorrelationMax.lean` — the `C_r(z) ≤ C_r(0)` cap (reproven inline here to keep imports thin).
- memory `arklib-389-deep-moment-wall` — B ≲ n^{3/4+o(1)} provable; r_opt/r_max ≍ a/2.
