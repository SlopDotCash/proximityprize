# #466 W1: the first unproven rung `r = β+1` — the char-0/wraparound split, and why β+1 is already the wall (2026-07-03)

**Lane W1 (the analytic wall, independence/energy form).** Verdict: **NO new provable bound past
the frontier; a SHARP NO-GO instead** — `r = β+1` is *already the wall*, and it is sharpened from
the vague "`r ≈ log q`" to an exact scalar object (`WraparoundBelowDC`) at the first past-crossover
rung. Part (b)'s signed-wraparound idea is confirmed dead (as round-4 pre-registered), now with
exact constants. One axiom-clean Lean brick landed (the char-0/wraparound SPLIT of `DCEnergyBound`).

Probe `scripts/probes/probe_466_wall_betaP1.py` → `_out_466_wall_betaP1.txt` (deterministic, exact:
char-0 energy in closed form + int64-exact level counts). Brick
`Frontier/_WallBetaPlusOneLocalization.lean` (3 theorems, all `[propext, Classical.choice,
Quot.sound]`, real build 3320 jobs). DISPROOF tag `466-w1-betaP1-is-the-wall`.

## The exact object

Char-p energy count `E_r^{(p)} = E_∞ + W_r`, `W_r ≥ 0` = wraparound/anomaly, `E_∞` = char-0 energy
(`p`-independent). **New exact closed form for the dyadic subgroup** (`Φ_{2^μ}(x)=x^{n/2}+1`, mapping
`ζ^a ↦ ±e_{a mod n/2}` into `ℤ^{n/2}`):
> `E_∞(n,r) = Σ_{c₁+…+c_{n/2}=r} (2r)!/∏_t (c_t!)²`  (= `(2r)!·[x^r] I₀(2√x)^{n/2}`).

Verified: reproduces `E₂=3n²−3n`, `E₃=15n³−45n²+40n` at n=8,16,32 exactly. By Lam–Leung
`E_∞ ≤ Wick := (2r−1)‼·n^r` (PROVEN; in-tree `zeroSumCount_le_doubleFactorial_dyadic`). Then EXACTLY
`A_r = E_r^{(p)} − n^{2r}/p = E_∞ + D_r`, `D_r := W_r − n^{2r}/p`, and
> `A_r ≤ Wick`  ⟺  `D_r ≤ BUDGET := Wick − E_∞`  ⟺  `W_r ≤ n^{2r}/p + (Wick − E_∞)`.

## Findings (exact, β=4 prize diagonal; n=8,16,32; ≥2 primes each)

1. **`A_r ≈ E_∞` at every rung** — `A_r/Wick` tracks `E_∞/Wick` to within the small `|D_r|`. The
   DC-subtracted energy is carried by the *char-0* (archimedean) term, which is PROVEN ≤ Wick. The
   wraparound is only a correction.
2. **`D_r < 0` at EVERY point** — all n, all primes, all r (2..9), generic **and** generalized-Fermat
   65537. The wraparound is robustly *below* its DC mean (`W_r ≤ n^{2r}/p`). Hence a **double margin**
   `A_r < E_∞ ≤ Wick`: the wall is not violated anywhere, with room to spare. `|D_r|/Wick ≤ 0.03` at
   β=4 (n=16 worst); the level decomposition shows the residue-wraparound share `Σ_{k≠0}N_k/E_r` is
   `≤ 2·10⁻⁴` at r=β+1=5 for n=16 (0 for n=8/32), growing only past crossover.
3. **This confirms round-4 "sub-smooth negative excess" with exact values and extends it to β+1 and
   past crossover** (β=3 accelerant, n=32: `D_r/Wick` reaches −0.33 at r=7, still negative; `D/BUDGET`
   up to −0.97 — i.e. `A_r` sits a full budget below Wick).

## Part (b) verdict — the sign structure is NOT a lever

The hypothesis was: do level-1 wraparounds carry a *sign pattern* giving cancellation the raw count
misses? **No.** `W_r` is a nonnegative COUNT — there is nothing to cancel internally. The favorable
"negative excess" is not signed cancellation; it is the *unsigned* inequality `W_r ≤ n^{2r}/p`
(the wraparound total stays at/below its DC/equidistribution prediction). Proving *that* is the
concentration wall itself. This is exactly the round-4 pre-registered kill of "signed levels",
now confirmed at the β+1 rung with exact data. The generalized-Fermat prime concentrates the
wraparound at the resonant levels (`k=3`, then `k=3,6` — the `2^16` structure) but `D_r` stays
negative — the sign is robust across generic and resonant primes, i.e. there is no *provable*
mechanism, only a robust empirical fluctuation.

## The sharp no-go (frontier sharpening) + prize scale

`r = β+1` is **already the wall**. Given char-0 (proven), the entire open content of the β+1 rung is
the single scalar inequality `WraparoundBelowDC`: `W_{β+1} ≤ n^{2r}/p`. At the prize
(`n=2^30, β=4, r=5`): `DC/Wick = 2^{+20}` (the DC term dominates Wick by `10^6`), the char-0 budget
`(Wick−E_∞)/Wick ~ C(r,2)/n = 2^{−26.7}`, so `A_{β+1} ≤ Wick` demands `W_r` match its DC mean
`n^{2r}/p` to **relative precision `2^{−47}`** — a genuine square-root-cancellation/concentration
statement (r=β+2: `2^{−73}`; r=β+3: `2^{−99}`). **No exact formula** exists: the char-0 ladder is
`p`-independent and captures only the diagonal-adjacent part; `W_r` is genuinely `p`-arithmetic with
no closed form.

**No provable bound past the frontier.** The only provable upper bounds on `A_r` at β+1 are the
trivial `A_r ≤ E_r^{(p)}` (`~ DC ≫ Wick`, useless) or Hölder `A_r ≤ M^{2r−2}·n` (needs the wall's
`M`-bound — circular). The favorable structure (`D_r < 0`) is exactly the open input. So the honest
deliverable is the localization, not a new bound.

## What LANDED (axiom-clean)

`Frontier/_WallBetaPlusOneLocalization.lean`:
- `dcEnergyBound_of_charZero_of_wraparoundBelowDC` — `CharZeroWick ∧ WraparoundBelowDC ⟹ DCEnergyBound`
  (the split: proven char-0 half + the open residual give `A_r ≤ Wick`).
- `dcSubtracted_le_charZero_of_wraparoundBelowDC` — under `WraparoundBelowDC`, `A_r ≤ E_∞` (the
  double margin `A_r ≤ E_∞ ≤ Wick`, matching `A_r < E_∞` at every probe point).
- `dcEnergyBound_iff_wraparound_within_budget` — the EXACT iff `A_r ≤ Wick ⟺ W_r ≤ DC + BUDGET`
  (`E_∞` cancels — a genuine identity).

These refine `DCEnergyCorrection.DCEnergyBound` by discharging its char-0 half unconditionally and
naming the true residual (= the "Anomaly-Suppression inequality" of that file) as the concentration
`WraparoundBelowDC`.

## Composition

Composes with: `DCEnergyCorrection` (the named open `A_r ≤ Wick`), `DCSubtractedMoment` (the DC
identity), `zeroSumCount_le_doubleFactorial_dyadic` (the char-0 half, PROVEN), `466-r4-tsang-levels-
vacuous` (the level decomposition; this sharpens its "negative excess" to exact β+1 values and to the
sign-not-a-lever verdict), the DC-crossover / moment-exponent-θ / TPS-boundary trio (the `r ≤ β`
closure). Does NOT touch the floor (this is the analytic wall). **CORE unchanged: OPEN, ON-BGK.**
