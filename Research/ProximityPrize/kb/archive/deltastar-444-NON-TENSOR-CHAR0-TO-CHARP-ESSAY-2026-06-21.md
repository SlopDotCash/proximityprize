# The Non-Tensor Route: Transferring the Char-0 Wick Mechanism to Char-p (#444)

*ArkLib Proximity-Prize cone. Companion brick: `Frontier/_AvNT_CumulantAdditivityEngine.lean`
(8 theorems, axiom-clean `[propext, Classical.choice, Quot.sound]`, real `lake build` ✓).
Prior bricks: `_AvNonTensorAutocorrAverage.lean`, `_NT_5_scratch.lean`, `_AvW0_BesselWickDomination.lean`,
`_NoExcessOnsetThreshold.lean`. Probes: `scripts/probes/probe_nt6_*.py`.*

---

## 1. Why the dilution theorem forces a non-tensor proof, and the char-0 Wick mechanism as the unique non-tensor source of the r-linear saving

The prize sup-norm object is `M = max_{b≠0} ‖η_b‖`, `η_b = Σ_{y∈μ_n} ψ(b·y)`, the non-principal
eigenvalue of the generalized Paley graph `Cay(F_p, μ_n)` with `μ_n` the `2^a`-th roots in `F_p`,
`p ≈ n^4`. The additive-energy route bounds it through the `2r`-th moment identity
`Σ_b ‖η_b‖^{2r} = q·E_r(μ_n)` (in-tree `subgroup_gaussSum_moment`), so `M^{2r} ≤ q·E_r`, and the
prize bound `M ≤ C√(n log p)` follows from the **Wick floor** `E_r ≤ (2r−1)‼·n^r` reached at the
moment saddle `r ≈ ln p`.

The exact in-tree recursion is `E_{r+1} = n·E_r + cross_r`, `cross_r = Σ_{s} Σ_{t≠s} C_r(s−t)`
(`CharPMomentRecursion.rEnergy_succ`), where `C_r(δ)` is the depth-`r` autocorrelation of the
sum-frequency. The **tensor lift** bounds each off-diagonal `C_r(δ) ≤ C_r(0) = E_r` (the diagonal
bound `autocorr_le_energy`), giving `cross_r ≤ n(n−1)·E_r`, hence `E_{r+1} ≤ n²·E_r`. Chaining this
from `E_1 = n` gives `E_r ≤ n^{2r−1}`, so `M ≤ (q·n^{2r−1})^{1/2r} → √(q·n²)·(…)` — the `M`-exponent
drifts to `1` (`M ~ n`), the trivial bound. This is the content of the new constraint
`_RudnevDilutionFixedSavingStall`: **any tensor-style step carries a FIXED multiplicative saving `κ`
per depth, and a fixed saving cannot reach the Wick floor.** The Wick floor needs the step
`E_{r+1} ≤ (2r+1)·n·E_r` — an `r`-LINEAR saving (the factor `2r+1` grows with depth) — and that
cannot come from any inequality whose per-step constant is depth-independent.

The dilution theorem then asserts: the **only known non-tensor mechanism** delivering the `r`-linear
saving is the **characteristic-0 cumulant-additivity** structure. In char-0, `η_b^{c0} = Σ_{μ_n}
e^{iθ}` is, by Lam–Leung antipodal balance (a vanishing `ℚ`-sum of `2^a`-th roots is a union of
antipodal pairs `{ζ^k, −ζ^k}`), a sum of `m = n/2` **independent** copies of `X = 2cos θ`. The
cumulants of a sum of independent summands are additive, so `κ_{2r}(η_b^{c0}) = m·κ_{2r}(2cos θ)` is
**exactly linear in `n`** at every depth (`κ_2 = n, κ_4 = −3n, κ_6 = 40n, κ_8 = −1155n`, verified
exactly `n=8..64`). Cumulants linear in the number of summands IS the sub-Gaussian/Wick bound
delivered DIRECTLY at every `r` — never by tensoring `E_2`. This file extracts and **proves** that
mechanism from scratch, in its sharpest, most transparent algebraic form.

---

## 2. The exact char-p break point (wraparound) and the single missing lemma

Over `F_p`, the energy splits exactly (`_NoExcessOnsetThreshold.energyCharP_eq_char0_add_wrapExcess`):

> `E_r^{F_p} = E_r^{c0} + W_r`, `W_r = #{char-p collisions that are NOT char-0 collisions}`.

`W_r` counts genuine **wraparounds**: depth-`r` root sums distinct in `ℚ(ζ_n)` yet equal mod `𝔭`.
The char-0 mechanism (cumulant additivity) controls `E_r^{c0}` to the Wick floor at every `r`. The
break is `W_r`: below the onset `r_0(n)` it is `0` (`noWraparound_imp_energy_eq` ⟹ `E_r = E_r^{c0} ≤
Wick` unconditionally), but the prize lives at the saddle `r* ≈ ln p` where `W_{r*}` can be positive.

The naïve localization (prior brick `_NT_5_scratch`) splits the open step at the cross level: from
`E_r^{F_p} = E_r^{c0} + W_r` and `cross_r = E_{r+1} − n·E_r`, one gets the exact `ℤ`-identity
`cross_r^{F_p} = cross_r^{c0} + ΔW_r`, `ΔW_r = W_{r+1} − n·W_r`. The char-0 cross step
`cross_r^{c0} ≤ 2r·n·E_r^{c0}` is the proven non-tensor saving (now `_AvNT...`); the residual is the
**wraparound-only** step `ΔW_r ≤ 2r·n·W_r`, i.e. `W_{r+1} ≤ (2r+1)·n·W_r` (`WrapCrossBounded`).

**A new, brutally honest numerical finding (probe `probe_nt6_wraparound_perstep_fails.py`, `n=8`
and `n=16`).** At EVERY prime, at the FIRST depth where `W_r` turns positive, the residual
`WrapCrossBounded` is **violated — and so is the tensor lift on `W` (`W_{r+1} ≤ n²·W_r`).** Sample
(`n=8`): `p=73`, `W_2 = 0, W_3 = 480, W_4 = 78848`; the step `r=3` needs `W_4 ≤ 7·8·480 = 26880`
(fails, `78848`), and even the tensor `W_4 ≤ 64·480 = 30720` fails. `n=16`: `p=193`,
`W_2 = 64, W_3 = 54240`; `r=2` needs `W_3 ≤ 4·16·64 = 4096` (fails badly), tensor `16²·64 = 16384`
(also fails). The reason is structural: `W_r` is **tiny right when it switches on** (it counts the
sparse new p-adic relations), so any *per-step ratio* `W_{r+1}/W_r` is enormous at onset. **The
wraparound energy obeys NO per-step log-derivative bound — `WrapCrossBounded` is the wrong object.**

The CORRECT prize-relevant residual is the **static** `NoWraparound` at the saddle:

> `W_{r*} = 0` at `r* = ⌈ln p⌉` on the prize prime — `OnsetExceedsSaddle`
> (`_NoExcessOnsetThreshold`).

When this holds, `E_{r*}^{F_p} = E_{r*}^{c0} ≤ Wick` directly, with NO recursion and NO per-step
bound. This is the genuine open BGK/Lam–Leung wall, but it is the right shape: a single
minimal-weight cyclotomic statement, not a depth-recursion on the (badly-behaved) `W_r`.

---

## 3. Each non-tensor candidate attempted — does it beat the tensor lift, the genuine sub-steps proven, the residual

**(e1) Average-autocorrelation `cross_r ≤ 2r·n·E_r` (`_AvNonTensorAutocorrAverage`).** Beats the
tensor lift *as a target* (the strict separation `2r·n·E_r < n(n−1)·E_r` for `2r+1<n` is proven,
`tensor_dilution_gap`). Sub-steps proven: the exact recursion repackaging, the tensor stall
`cross_le_tensor`, and `energyStep_of_autocorrAverage` (the named bound ⟹ the `r`-linear step).
Residual: `AutocorrAverageBounded` itself — the WHOLE cross, char-0 + wraparound lumped. Verdict:
genuine non-tensor localization, but the residual still contains the proven char-0 half.

**(e6) Wraparound-cross split (`_NT_5_scratch`).** Sharpens e1 by discharging the char-0 half as a
named input and isolating the wraparound-only cross `ΔW_r`. Sub-steps proven: `cross_succ_split`
(exact `ℤ` identity), the full reduction `charP_wickStep_of_char0_and_wrap`, vacuity below onset,
the dilution separation. Residual: `WrapCrossBounded`. **Verdict (corrected here):** the reduction is
axiom-clean, but its residual is FALSE near onset (§2). Not a viable per-step object.

**(e2) cumulant transfer / (e3) normalized recursion `a_{r+1}=(a_r+2r c_r)/(1+2r)` / (e4)
shifted-convolution flatness / (e5) two-sided wraparound variance.** All reduce to a char-p control
of the wraparound mass at depth `r ≈ ln p` (the cumulant correction `S ≤ slack`, the flatness of
`f_r` off-DC, or `Var(W_k) ≤ slack²`). None beats the tensor lift unconditionally; each is the same
wall in a different coordinate.

**(NEW — the engine, this file) the cumulant-additivity convolution lemma.** Instead of *naming* the
char-0 step, PROVE the machine that produces it. Define the **log-derivative index**: `u : ℕ → ℚ` has
index `≤ a` iff `(k+1)·u_{k+1} ≤ a·u_k` for all `k` (i.e. `t·U'(t) ⪯ a·U(t)` coefficientwise for
`U(t) = Σ u_k t^k`). Then:

* **Base atom** (`besselCoeff_logDerivIndex_one`): `b_k = 1/(k!)²` has index `≤ 1`
  (`(k+1)b_{k+1} = 1/(k!(k+1)!) ≤ 1/(k!)² = b_k`). `exp` (`e_k = 1/k!`) has index *exactly* `1`.
* **THE ENGINE** (`logDerivIndex_conv`): if `u` has index `≤ a` and `v` index `≤ c` (both `≥ 0`),
  the convolution `w = u ⋆ v` has index `≤ a + c`. **The index ADDS under convolution.** This is
  cumulant additivity reduced to a pure inequality on coefficient sequences (proof: split
  `(r+1) = i + (r+1−i)` inside `(r+1)·Σ_{i} u_i v_{r+1−i}`; the `i`-weighted half reindexes to
  `≤ a·w_r` by `u`'s index, the `(r+1−i)`-weighted half is `≤ c·w_r` by `v`'s index).
* **Iterate** (`cpow_logDerivIndex`, `besselPow_logDerivIndex`): the `m`-fold power `cpow b m` has
  index `≤ m`. With `m = n/2`: `(r+1)·c^{(m)}_{r+1} ≤ m·c^{(m)}_r`.
* **Normalize** (`besselPow_energyStep`): multiplying by `(2r)!` (Bessel identity `E_r^{c0} =
  (2r)!·c^{(m)}_r`, `_AvW0`), `(2r+2)!·c^{(m)}_{r+1} ≤ (2r+1)·(2m)·(2r)!·c^{(m)}_r`, i.e.
  **`E_{r+1}^{c0} ≤ (2r+1)·n·E_r^{c0}`** — the `r`-linear Wick energy step, the dilution-theorem
  target, here a THEOREM.

**Does it beat the tensor lift?** Yes, and the separation is proven (`besselPow_le_tensor_step`):
for `2r+1 < n`, the engine factor `(2r+1)·n` is strictly below the tensor `n²`. The index growing
LINEARLY in `m = n/2` (additive over `m` independent directions) is exactly the `r`-linear saving; a
tensor lift would multiply the index every step (super-linear), the fixed-saving stall.

---

## 4. The sharpest non-tensor partial result and the exact remaining char-p wraparound lemma

**Sharpest partial result (UNCONDITIONAL, fully proven, axiom-clean):** the char-0 `r`-linear Wick
energy step `E_{r+1}^{c0} ≤ (2r+1)·n·E_r^{c0}`, derived from the cumulant-additivity engine. This is
a real advance: the prior bricks carried this step as a *named input*; it is now a theorem with no
open dependency (modulo the Bessel identity `E_r^{c0} = (2r)!·cpow b (n/2) r`, itself the in-tree
`_AvW0` STEP-1, verified exactly at `n=8,16`). It strictly beats the tensor lift in char-0.

**Exact remaining char-p lemma (the open wall, named in its correct STATIC form):**

> `OnsetExceedsSaddle` (`_NoExcessOnsetThreshold`): at `r* = ⌈ln p⌉`, the prize prime admits NO
> nonzero `≤ 2r*`-term `±1`-relation of `2^a`-th roots vanishing mod `𝔭` — equivalently `W_{r*} = 0`.

Under it, `E_{r*}^{F_p} = E_{r*}^{c0} ≤ Wick` with the engine doing all the work on the char-0 side.
This replaces the per-step `WrapCrossBounded` (shown false near onset) with a single minimal-weight
cyclotomic statement. The transfer of the *engine* to char-p is exactly: the engine controls
`E^{c0}`, and char-p agrees with char-0 precisely when `W = 0` (no per-step bound on `W` is needed or
available).

---

## 5. Honest verdict — did any candidate beat the tensor lift unconditionally?

**YES, in characteristic 0 — and that is genuinely new, proven, and landed.** The cumulant-additivity
convolution engine (`_AvNT_CumulantAdditivityEngine.lean`, 8 theorems, real `lake build` ✓,
`[propext, Classical.choice, Quot.sound]`) proves the `r`-linear Wick energy step
`E_{r+1}^{c0} ≤ (2r+1)·n·E_r^{c0}` UNCONDITIONALLY, and proves it is strictly below the tensor
ceiling. This is the non-tensor saving the dilution theorem demands, distilled to a transparent
inequality (the log-derivative index is additive under convolution), and it upgrades the prior
bricks' *named input* to a *theorem*. The char-0 half of the route is no longer a black box.

**NO, in characteristic p — and the honest sharpening is that one prior residual was the wrong
object.** The engine is a char-0 theorem (about Bessel/exp coefficient sequences). Its char-p
transfer is gated entirely by the wraparound `W_r`, which:

1. is `0` below onset (where the engine already gives the prize unconditionally), and
2. obeys NO per-step log-derivative bound at onset — `WrapCrossBounded` (the `_NT_5` residual) and
   even the tensor lift `W_{r+1} ≤ n²·W_r` are BOTH violated at the first positive depth, at every
   tested prime (`n=8,16`). `W_r` is sparse-and-spiky, not a convolution power.

So the correct, irreducible char-p residual is the STATIC minimal-weight statement
`OnsetExceedsSaddle` / `W_{r*} = 0` at the prize prime — the open BGK/Lam–Leung wall. No candidate
crosses it; every dynamic (per-step) localization either lumps in the proven char-0 half (e1) or
posits a per-step bound on `W` that is empirically false (e6). The genuine progress is the engine
itself plus the demotion of `WrapCrossBounded` from "the residual" to "a false per-step object",
re-pinning the wall in its correct static form.

**On non-tensor-vs-disguised-tensor:** the engine is genuinely non-tensor — its saving is the
*additive* index `m = n/2` accumulated once over `m` independent directions, not a per-step
multiplicative constant. A tensor lift corresponds to *multiplying* indices (doubling per step); the
engine *adds* them. That is the precise algebraic signature of cumulant additivity, and it is what
makes the saving `r`-linear rather than fixed.

**On conditional-vs-unconditional:** the char-0 step is unconditional (no `sorry`, no open input
beyond the in-tree Bessel identity). The char-p prize is conditional on `OnsetExceedsSaddle`, which
is NOT discharged and is honestly the wall. This file closes none of #444; it proves the engine the
route needs and corrects the shape of the remaining char-p obligation.

---

### Ledger

| object | status | file |
|---|---|---|
| log-derivative index ADDS under convolution (the engine) | **PROVEN** axiom-clean | `_AvNT_CumulantAdditivityEngine.logDerivIndex_conv` |
| Bessel atom index `≤ 1`, exp atom index `= 1` | **PROVEN** | same, `besselCoeff_/expCoeff_logDerivIndex_one` |
| `cpow b m` index `≤ m` (iterate) | **PROVEN** | same, `besselPow_logDerivIndex` |
| char-0 `r`-linear Wick step `E_{r+1}^{c0} ≤ (2r+1)·n·E_r^{c0}` | **PROVEN** (mod Bessel identity) | same, `besselPow_energyStep` |
| engine step strictly below tensor ceiling | **PROVEN** | same, `besselPow_le_tensor_step` |
| `WrapCrossBounded` (`_NT_5` per-step residual) | **REFUTED near onset** (probe) | `probe_nt6_wraparound_perstep_fails.py` |
| `OnsetExceedsSaddle` / `W_{r*}=0` at prize prime | **OPEN** (the wall, correct static form) | `_NoExcessOnsetThreshold.OnsetExceedsSaddle` |
