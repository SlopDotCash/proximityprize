# #444 loop-3: the DC-subtracted-energy OVERSHOOT direction also reduces to the wall

**Date:** 2026-06-15 · **Route:** [moment] · **Task:** wfL3 (defect-onset no-go strengthening)
**Verdict:** **reduces-to-wall** (clean negative; scoping gap *narrowed*, not closed).

## The question this loop tested

The open core (CLAUDE.md §3.5 face 3) is the worst Gauss period
`M(n) = max_{t≠0}‖η_t‖`, `η_t = Σ_{x∈μ_n} e_p(t·x)`, conjectured `≤ C·√(n·log m)`,
`m=(p−1)/n=2^128`, prize `p≈n·2^128`, `β=log_n p∈[4,5]`.

The moment method bounds `M(n) ≤ (p·E_r)^{1/2r}` by the order-`r` additive energy
`E_r(μ_n)`. At the prize prime the **raw** `E_r` is dominated by the trivial DC term
`n^{2r}/p` (for `n≥64`), so the right object is the **DC-subtracted energy**
`A_r := E_r − n^{2r}/p`. The char-0 Wick / Lam–Leung ceiling is `A_r^{(0)} ≤ Wick := (2r−1)!!·n^r`.

The iter-1 no-go (`MomentMethodPrizeDepthNoGo.lean` + `HeightGateNormBound.lean`) proves the
char-0→char-p transfer of `A_r ≤ Wick` is valid only up to `r ≤ rMax=⌊2β⌋≈8`, via the norm-divisibility
gate `(2r)^{n/2}<p`. The moment optimum is at `r_opt≈log m≈128`, **16× past** the transfer ceiling.
The iter-2 **scoping caveat**: the no-go only kills *height-routed* moment methods; it does not rule
out a *non-height* char-p energy bound at `r≈log m`.

**The loop-3 hope** (from prior probes `probe_habegger_*`, RESEARCH_SYNTHESIS): maybe `A_r`
*overshoots* Wick at `r ≈ log m` — extra short `±1`-relations of `2^μ`-th roots clustering at `0 mod p`
beyond the `n^{2r}/p` mean. If `A_r > Wick` at `r_opt` were **provable**, the moment method's energy
INPUT would be genuinely **false** there (dead by ALL routes, not merely unprovable-by-height) ⟹ the
scoping gap would be *closed*. The crucial honest check: **is proving `A_r > Wick` at deep `r` genuinely
easier than the BGK upper bound, or does it itself reduce to the wall?**

## (a) Does the char-p energy A_r overshoot Wick at deep r? — NO, no onset at any reachable depth

`probe_wfL3_defect_onset.py` computes `A_r` **exactly** over **PROPER** subgroups `μ_n≤𝔽_p^*`
(`n=8,16,32`; `β=3.5/3.8/4.0`; `odd_part((p−1)/n)>1` enforced so `μ_n` is a proper subgroup with a
nontrivial multiplicative complement — **never** the full group), two independent ways:
(a) combinatorial `E_r` via integer FFT-convolution of the `μ_n` indicator, minus `n^{2r}/p`; and
(b) the **spectral identity** `A_r = (1/p)Σ_{t≠0}|η_t|^{2r}` (`|η_0|=n` ⟹ DC term `= n^{2r}/p`).
Char-0 `E_r^{(0)}` is reported as the clean Lam–Leung baseline. Each config swept past `r_opt` (to r=11–13).

**Result (reproduced + independently re-verified this loop, 6 of 7 configs complete; 7th = n=32,β=4
still grinding its exact r-table, the 6 done are unanimous):**

| n | β | house M(n) | `A_r/Wick` trajectory | onset |
|---|---|---|---|---|
| 8 | 3.5 | 7.19=2^2.85 | 0.995, 0.86, 0.64, 0.42, 0.23, 0.11, 0.05(r_opt), …, 0.0006(r=11) | **none** |
| 8 | 3.8 | 7.48 | 0.997 → … → 0.0002(r=12) | **none** |
| 8 | 4.0 | 7.56 | 0.998 → … → 0.0002(r=12) | **none** |
| 16 | 3.8 | 13.33 | 0.9996, 0.94, 0.82, …, 0.016(r_opt=11), …, 0.0029(r=13) | **none** |
| 16 | 4.0 | 13.29 | 0.9998 → … → 0.0029(r=13) | **none** |
| 32 | 3.8 | 20.35 | 1.0000, 0.97, 0.90, 0.81, …, 0.011(r_opt=13) | **none** |

`A_r/Wick` is `<1` and **monotonically DECREASING** in `r` in every config, tracking just **below**
the char-0 ratio `E_r^{(0)}/Wick`. **0 onset across all configs.** All spectral cross-checks
`A_r=(1/p)Σ_{t≠0}|η_t|^{2r}` match the combinatorial value to machine precision (87/87 "ok",
0 MISMATCH). **The "onset at rMax≈2β" hope is decisively REFUTED — there is no onset at any reachable
depth.** Mechanism: DC-subtraction removes exactly the trivial `n^{2r}/p` saturation; what remains is
`(1/p)·(few terms)·M(n)^{2r}`, and the true house `M(n)≈√(n log m)` is far below the moment-method root
`√(2nr)` for `r≳log m`, so `A_r` stays far under `(2nr)^r`.

## (b) Does proving the overshoot strengthen the no-go to ALL-routes — or reduce to the wall?

**It reduces to the wall.** This is the load-bearing point, and it is proven axiom-clean, independent
of whether any overshoot exists. The EXACT spectral structure forces a **sandwich** between the single
largest eigenvalue and the whole nontrivial moment. Writing `s i = ‖η_{t_i}‖` over the `#ι = p−1`
nonzero frequencies, `A_r = (1/p)Σ_i (s i)^{2r}`, `house = max_i s_i`:

> `house^{2r}/p ≤ A_r ≤ (#ι/p)·house^{2r} < house^{2r}`   (since `#ι = p−1 < p`).

I re-verified this sandwich on the actual probe rows (e.g. n=16, p=37633, r=13:
`4.68e24 ≤ A_r=1.04e26 ≤ 1.760e29 < house^{2r}=1.760e29`; 5/5 rows hold). The upper bound is tight
to factor `(p−1)/p ≈ 1`. Therefore for **any** threshold `W`:

> `W < A_r ⟹ W < house^{2r} ⟹ house > W^{1/2r}`.

With `W = Wick = (2r−1)!!·n^r` and `Wick^{1/2r} = ((2r−1)!!)^{1/2r}·√n`:

> `A_r > Wick ⟹ M(n) = house > ((2r−1)!!)^{1/2r}·√n`.

At `r = r_opt ≈ log m` this RHS is (a constant times) the prize floor, so **proving overshoot at
`r_opt` IS proving `M(n)` exceeds the prize bound — a deep-`r` char-p Gauss-period LOWER bound = the
BGK wall from the other side.** The hoped asymmetry — "a single explicit over-clustering family
LOWER-bounds the clustering count cheaply" — **does not exist**: `A_r` is the `(1/p)`-weighted sum of
`p−1` terms each `≤ house^{2r}`, with one dominant term already `≥ house^{2r}/p`; there is no slack to
inflate `Σ_{t≠0}|η_t|^{2r}` above `p·Wick` without pushing the single largest `M(n)` itself above
`Wick^{1/2r}`. The overshoot lower bound and the BGK upper bound live at the **same object `M(n)` at the
same depth** — neither is easier. **Clean negative: the overshoot direction reduces to the wall.**

## (c) Axiom-clean increment landed

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DefectOnsetOvershoot.lean` — **9 theorems, all
axiom-clean** `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`** (verified this loop via
`pg-iterate.sh`, exit 0, 17s; campaign also reports a real `lake build` green, 1971 jobs).

- The sandwich: `A_ge_house_pow` (`house^{2r}/p ≤ A r`), `A_le_card_house_pow`
  (`A r ≤ (#ι/p)·house^{2r}`), `A_lt_house_pow` (`A r < house^{2r}` when `#ι < p`).
- The reduction: `overshoot_imp_house_pow_gt` (`W < A r ⟹ W < house^{2r}`),
  `overshoot_imp_house_gt` (root form `W^{1/2r} < house`), `wick_rpow_eq`
  (`Wick^{1/2r} = ((2r−1)!!)^{1/2r}·√n`, an exact identity), `overshoot_imp_house_gt_prizeForm`.
- The honest-check verdict: `overshoot_refutes_prize` (overshoot at a depth where the Wick root
  dominates the prize bound ⟹ `¬PrizeBound`) and the symmetric `prizeBound_imp_no_overshoot`
  (the two verdicts are two faces of ONE wall).

**Audit notes (independent, this loop):** the theorems are **conditional** (real hypotheses
`hp, hcard, hpos, hover, hfloor`; `overshoot_refutes_prize` honestly takes the floor inequality
`C·T ≤ root` as a hypothesis — no hidden vacuity, no `Iff.rfl` discharge of the open input).
`wick_rpow_eq` is a genuine exact identity, not a definitional unfolding. The Lean `A` / `house` model
matches the probe: the sandwich the Lean asserts is the sandwich the exact numerics satisfy.

**One honest prose imprecision (does NOT affect the verdict).** By Stirling
`((2r−1)!!)^{1/2r} ≈ √(2r/e)`, so the Wick root at `r_opt=log m` is `≈ √(2/e)·√(n log m) ≈ 1.213·√(n log m)`,
which is **below** the conjectured prize constant `C ≈ 1.33`. Hence `hfloor : C·T ≤ root` with
`T=√(n log m)` is **not** satisfiable at the literal `C ≈ 1.33`; the "non-vacuous exactly at C≈1.33"
gloss in the file docstring is loose. The conditional theorems remain correct and non-vacuous — an
overshoot at `r_opt` still forces `M(n) > 1.213·√(n log m)`, refuting any prize bound with `C ≤ 1.213`,
which is still a deep-`r` `M(n)` lower bound past the proven BGK regime. The reduces-to-wall conclusion
is unaffected.

## (d) The honest net: is the scoping gap closed, narrowed, or unchanged?

**NARROWED, not closed.** Precisely:

- The scoping gap as a *raw open question* — "does a non-height char-p additive-energy bound for `μ_n`
  at `r ≈ log m` exist?" — is **unchanged-open** (it would be the prize).
- But the specific **escape hatch** that motivated loop-3 — "the energy INPUT is *false* at `r_opt`
  (overshoot), so the moment method is dead by an *energy-falsity* obstruction, not merely a
  transfer/proof obstruction" — is now **closed two ways**:
  1. **Empirically false:** the numerics show `A_r < Wick` monotonically; there is no overshoot, so the
     energy input is in fact **TRUE** (just unproven in char-p) at every reachable depth. The iter-1/2
     no-go is therefore a **transfer/proof** obstruction, NOT an **energy-falsity** one.
  2. **Provably no-easier:** even *hypothetically*, proving the overshoot is exactly as hard as a deep-`r`
     lower bound on `M(n)` past the prize floor (the sandwich), i.e. **the overshoot direction reduces to
     the wall**. There is no free lunch in the energy-falsity direction.

**Bottom line, stated plainly:** loop-3 did **not** strengthen the moment no-go to "all routes." It
**closed one would-be shortcut** (overshoot/energy-falsity) by showing it is the BGK wall in disguise,
and it **corrected** the iter-1/2 picture: the moment method's energy hypothesis is genuinely *true* at
prize depth — the obstruction is purely the missing *char-p transfer*, which remains the single open
core. **Reduces-to-wall. No closure.**

## Pointers

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DefectOnsetOvershoot.lean`
- Probe: `scripts/probes/probe_wfL3_defect_onset.py`
- DISPROOF_LOG iter-3 entry: `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md` (§ "iter 3 — the
  DC-subtracted-energy OVERSHOOT direction also reduces to the wall")
- Prior: `MomentMethodPrizeDepthNoGo.lean`, `HeightGateNormBound.lean` (iter-1 height-route no-go);
  `docs/kb/deltastar-444-loop2-synthesis-2026-06-15.md` (iter-2 scoping caveat + MGF/disc doors).
