# δ* (#407) — Hasse–Weil/Fermat-moments + exact Gauss-period FOLDING recursion: foothold + same wall

**Date:** 2026-06-13. **Author:** δ* lane (#407), route: **hasseweil** (Fermat-curve moments +
2-power tower self-similarity). **Honesty:** the prize core (`B = max_{b≠0}‖η_b(μ_n)‖ ≤
C√(n·log(p/n))`) is NOT closed. This note records (1) a rigorous *foothold* — the Garcia–Lorenz–Todd
fixed-`k` exact 4th moment via Hasse–Weil, machine-confirmed; (2) a NEW axiom-clean Lean brick — the
exact analytic *folding recursion* for the Gauss period; (3) the precise residual = the SAME
deep-moment wall, now with the moment-validity ladder quantified in the fixed-index regime.
Complements [[deltastar-407-limit-law-sqrt2-constant]] (the √2 constant) and
[[deltastar-407-dyadic-2adic-gauss-tower-verdict]] (the character-side refutation) from a third
(moment/curve) angle — same wall, consistent.

## 1. Foothold: the Garcia–Lorenz–Todd EXACT fixed-k 4th moment (Hasse–Weil), confirmed

Paper: `~/papers/arklib/_407/garcia_moments_2112.13886.pdf` (S.R. Garcia, B. Lorenz, G. Todd,
*Moments of Gaussian Periods and Modified Fermat Curves*). **Dictionary:** their `d` = our index
`m`; their `k` = our subgroup order `n`; `p−1 = dk = mn`. Their `V_r(p) = Σ_{s=0}^{d−1}|η_s|^r`
sums over the `m` distinct period values (one per coset). Relation to in-tree all-frequency moments:
`Σ_{b∈F^×}‖η_b‖^{2r} = n·V_{2r}(p)`, and `Σ_{b∈F}‖η_b‖^{2r} = n^{2r} + n·V_{2r}(p)` (the `b=0`
spike `η_0 = n`).

**Their Theorem 1 (FIXED k = fixed n):** for circular `(p,k)` (= all but finitely many `p` at fixed
`n`),
```
V₄(p) = 3p(n−1) − n³      if 2 | n,
V₄(p) = p(2n−1) − n³      if 2 ∤ n.
```
**Machine-confirmed exactly** (`scripts/probes/_wf407_hasseweil_dict.py`) for `n∈{4,8,16,32}` over
many primes — the only mismatch (p=3457, n=32) is a non-circular pair (the finite exceptional set).
This is an **unconditional theorem** (Hasse–Weil on the modified Fermat curve `gix^d+gjy^d=gkz^d`,
genus `(d−1)(d−2)/2`), NOT an empirical fit. Consequence: the per-coset normalized 4th moment
```
E₂ := V₄/m → 3n²    (kurtosis 3, NOT 2),
```
verified rising `1.50→2.25→2.62→2.81→2.90→3.0` as `m=(p−1)/n→∞` (`_wf407_tower_4thmoment.py`).
**This is the rigorous Hasse–Weil anchor of the "kurtosis 3 − 3/n" Edgeworth fact** that
[[deltastar-407-limit-law-sqrt2-constant]] derived from the Bessel `I₀` law — same number, now from
a published curve-point-count theorem. (Garcia Thm 2/3 give `d=3,4` exact via the Fermat curves
`x³+y³=z³`, `x⁴+y⁴=z⁴`; Thm 4 gives all-`d` Hasse–Weil bounds.)

## 2. NEW axiom-clean Lean brick: the analytic FOLDING recursion

File `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_wf407_tower.lean` (Mathlib-only standalone,
`pg-iterate` ✅ OK, axioms = `[propext, Classical.choice, Quot.sound]`). The dyadic-tower analytic
recursion, machine-verified exact (`_wf407_tower_recursion.py`, error `1e-14`):

> **`eta_fold`** : if `μ_{2n} = μ_n ⊔ ζ·μ_n` (`ζ` the dyadic generator, `ζ^n=−1`), then for every `b`
> ```
> η_b(μ_{2n}) = η_b(μ_n) + η_{ζ·b}(μ_n).
> ```

This is the analytic analog of the census duplication `quartet_prod` (`QuartetTowerLaw.lean`) and the
polynomial `pow_two_pow_sub_eq` (`TwoPowerTowerFactorization.lean`), but on the *Gauss-sum* side.
Companions: `eta_smul` (η_b(ζ•G)=η_{ζb}(G)), `eta_fold_norm_le` (triangle ⟹ `B(2n)≤2B(n)`, trivial),
`eta_fold_normSq` (isolates the cross term `2·Re(η_b·conj η_{ζb})`).

**Exact cross-term closed form** (`_wf407_crossterm_exact.py`, all primes/n):
```
Σ_{b∈F^×}  Re( η_b(μ_n) · conj η_{ζb}(μ_n) ) = −n²   (exactly),
Σ_{2n-coset reps}  (same)                     = −n/2  (exactly).
```
Provable in one line of orthogonality: `Σ_{x,y∈μ_n} Σ_{b≠0} e_p(b(x−ζy)) = Σ_{x,y}(−1)` because
`x=ζy` is impossible (`μ_n ∩ ζμ_n = ∅`). So **the second moments add cleanly up the tower**:
`Σ_b‖η_b(μ_{2n})‖² = Σ_b‖η_b(μ_n)‖² + Σ_b‖η_{ζb}(μ_n)‖² − 2n²`, the cross being negligible vs the
diagonal `q·n`. This is the rigorous "√2-per-level on the L² scale" fact. Empirically
`B(μ_{2n})/B(μ_n) ↓ √2` (1.99→1.81→1.59→1.50→…→1.4142, `_wf407_tower_4thmoment.py`), matching the
`C0=√2` extreme-value constant.

## 3. The residual = the SAME deep-moment wall; validity ladder quantified

The folding recursion reduces `B(μ_{2n})` to `‖η_b(μ_n)+η_{ζb}(μ_n)‖`. The √2 (not 2) growth needs
the two summands to be effectively INDEPENDENT (no phase alignment) **at the worst-case frequency**.
The cross-term identity proves L²-orthogonality *on average* (sum `−n²`), but per-frequency
worst-case independence is the open core — folding *re-expresses* the wall one level at a time, it
does not cross it. Consistent with `CharSumMomentDeepWall.lean`: the 2-power tower does not lower the
deep moments (`E_r(μ_{2^a}) ≥ r!·n^r`, the `−1`-closure ADDS solutions — antipodal *upward*
pressure, exactly the [[deltastar-407-dyadic-2adic-gauss-tower-verdict]] Wall-G finding).

**The moment method's reach** (correct, coset-restricted form — drop the `b=0` spike or it pins the
bound at the trivial `B≤n`): `B^{2r} ≤ V_{2r} = m·E_r ⟹ B ≤ (m E_r)^{1/2r}`. With Garcia/Bessel
`E_r ≈ (2r−1)!!·n^r`, the optimum `r ≈ ½ ln m ≈ 44` gives `√(n ln m)` — **but** the char-0/Garcia
`E_r` value is valid only for `r ≤ r_max = 2 log_n p − 3` (p-defect onset), where the curve count
stops being the diagonal value. Quantified in the **fixed-index regime** (m=2^128 fixed, n=2^a,
`_wf407_validity_regime.py`):
```
log_n p = 1 + 128/a   ⟹   r_max = 2 log_n p − 3 = 2(1 + 128/a) − 3 = 2·128/a − 1.
a=16: r_max=15   a=32: r_max=7   a=48: r_max=4.3   a→∞: r_max→−1   (needed r ≈ 44, ALL a)
```
So the validity ladder **shrinks toward 1** as the index is held fixed and `n→∞`. For every realistic
NTT size (`a = log₂ n < 128`, i.e. `n < m`), `n² ≪ p` so Garcia Thm 1 (the `r=2` rung) holds, but the
deep `r ≈ 44` rung needed for the prize is far out of the validity window (`r_max ≤ 15`). **The gap
`r_opt/r_max ≈ a/2`** (half the tower depth) is unchanged from the old `p~n^5` framing — the
fixed-index reframing does NOT move the wall; it just re-coordinatizes it. Best the moment method
*proves* in-regime: `B ≲ n^{3/4+o(1)}` (worse than `√n`), matching the di Benedetto et al
`t^{1−31/2880}` literature ceiling.

## 4. Verdict & reproduce

**Made real progress toward the bound:** NO closure. **New ground:** (i) the Garcia Hasse–Weil
fixed-k exact 4th moment ported into the project as the rigorous anchor of kurtosis-3; (ii) a NEW
axiom-clean Lean brick `eta_fold` (the analytic tower recursion) + the exact `−n²` cross-term; (iii)
the validity-ladder shrinkage `r_max = 2·128/a − 1` pinning that the fixed-index reframing leaves the
deep-moment wall in place. The wall is the per-frequency worst-case independence of the two folded
periods = square-root cancellation among the `m` odd-order Gauss phases.

Probes: `scripts/probes/_wf407_hasseweil_dict.py` (Garcia Thm1), `_wf407_tower_recursion.py` (fold
identity 1e-14), `_wf407_tower_2ndmoment.py` / `_wf407_crossterm_exact.py` (cross-term −n²/−n/2),
`_wf407_tower_4thmoment.py` (E₂→3n², B(2n)/B(n)→√2), `_wf407_momentopt2.py` (coset moment converges),
`_wf407_validity_regime.py` (E_r deviation), `_wf407_selfsim_law.py` (mean ratio ≈√2). Lean:
`Frontier/_wf407_tower.lean` (axiom-clean).
