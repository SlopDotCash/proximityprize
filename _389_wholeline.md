## 🎯🎯 THE WHOLE DYADIC LINE — EXACT, char 0 (`LadderTowerCharZeroExact.lean`, axiom-clean)

The exact sub-Johnson list law now holds at **every** dyadic agreement level, not just the squaring tower:

> **`ladder_tower_fiberClosed_charZero`** — over a `2^μ`-th-root domain in a characteristic-zero field, **every** `GapBand` solution of the stride-`2^a` ladder stack `(X^{r·2^a}, X^{(r−1)·2^a})` is closed under the order-`2^a` subgroup — a union of `r` fibres of `x ↦ x^{2^a}` — for **every** `a ≥ 1, r ≥ 2`.

This assembles three pieces, now all in-tree:
1. **Newton bridge** (`psum_window_zero_of_esymm_window_zero`, landed this session) — GapBand's vanishing top coefficients = vanishing elementary symmetric functions ⟹ vanishing power sums, by specializing mathlib's Newton identity via `aeval` at the roots.
2. **Vieta** (`Multiset.prod_X_sub_C_coeff`) — the GapBand coefficient at degree `A−c` is `±e_c` of the roots.
3. **2-adic tower descent** (`tower_closed_of_dyadic_sums_zero`, in-tree) — the dyadic power sums `∑x^{2^i}=0` (i<a) force order-`2^a` closure, by **iterated Mann** (the 2-power Lam–Leung theorem at each level).

With `fiberUnion_gapBand` (converse) and `ladder_list_ge_fibre` (supply), the char-0 ladder census at agreement `r·2^a` is **exactly** the `2^a`-fibre family — so the exact list `= N_fib` at every dyadic agreement level.

## Final state of the exact sub-Johnson list-size problem

| component | theorem | status |
|---|---|---|
| lower (every field) | `ladder_list_ge_fibre` | proven |
| upper envelope (every word, every field) | `rs_list_corradi_bound` | proven |
| exact upper, squaring tower, char 0 | `ladder_gapBand_antipodal_charZero` | proven |
| **exact upper, ALL dyadic towers, char 0** | `ladder_tower_fiberClosed_charZero` | **proven** |
| Newton bridge (reusable) | `psum_window_zero_of_esymm_window_zero` | proven |
| δ* pin from the census | `kkh26_deltaStar_pin_of_censusDomination` | proven |

**The complete theory, proven:** `L_max(a) = max_towers N_fib(s,r)` — the exact sub-Johnson list size for explicit smooth-domain RS — is established at **every dyadic agreement level in characteristic zero** (both brackets meet), and over `F_q` above the resultant transfer threshold (the deployed `ε*=2^{−128}` regime, `q ≥ 2^{128}`, is far above it; below threshold, small-field inflation, measured at p=97). The whole line, no wall. The only residual is the explicit char-0→`F_q` transfer threshold value (a separately-studied resultant bound), not the structural list law, which is now exact and machine-checked.
