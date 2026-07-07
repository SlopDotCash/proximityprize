# #444 δ* — New-Front Synthesis: S6 bounded-Betti Deligne route + Conj 7.1 pivot (2026-06-17)

**Status: HONEST NO-GO on both proposed escapes. The prize is unchanged — it reduces to the
char-p faithfulness of `E_r(μ_n) ≤ K^r·Wick` uniform to `r ≈ ln q`, `n → 2^30` = the BGK/Paley
√-cancellation wall.** Neither the S6 Deligne route nor the Conj-7.1 pivot escapes it. No
fabricated closure; all proven claims are axiom-clean Lean, all open inputs named as hypotheses.

This note consolidates four propose→verify attacks (S6 bounded-Betti Deligne, Conj-7.1 pivot,
K_eff robustness-at-scale, S3/S5 partials). Each independently confirms the same verdict.

---

## 0. The reduction recap (what the prize actually is)

`M(n) = max_{b≠0 mod p} |Σ_{x∈μ_n} e_p(bx)|`, `μ_n` = order-`n` *proper* subgroup of `F_p*`
(`n = 2^μ`, `n | p-1`, never the full group), prize `p ≈ n·2^128`, `β = log_n p ∈ [4,5]`,
index `m = 2^128`, `r_opt = log m ≈ 89–128`. The moment method reduces `M(n)` to the order-`r`
additive energy `E_r(μ_n) = #{x ∈ μ_n^{2r} : Σ ε_i x_i = 0}`. With `Wick = (2r-1)‼·n^r`, the
**entire prize** is the uniform transfer bound `E_r ≤ K^r·Wick`, `K = O(1)`, to depth `r ≈ ln q`.

### ANCHOR CORRECTION (honesty flag — verified this session)

The task statement names three in-tree anchors `char0_prize_moment_bound`,
`prize_of_transfer_slack`, `CharPEnergyTransferWithSlack`. **These do not exist in the Lean tree
on this branch** (grep over `ArkLib/Data/CodingTheory/ProximityGap` returns nothing). The actual
proven bridge is the **conditional** brick `GaussPeriodMomentBound.lean`:

- `eta_pow_le_of_energyBound` / `worstCaseIncompleteSumBound_of_energyBound` — axiom-clean
  (`[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`), prove `‖η_b‖^{2r} ≤ q·(2r-1)‼·n^r`
  **from** the named Prop `GaussianEnergyBound G r := E_r(G) ≤ (2r-1)‼·n^r`.
- `GaussianEnergyBound` is **OPEN** (the named carrier of the entire core). So the in-tree state
  is a *conditional reduction*, not a closure. Treat the prize as reduced-to-a-named-hypothesis,
  NOT proven.

The char-0 substrate that *is* unconditional: `AdditiveEnergySidonModNeg.lean`
(`additiveEnergy_eq_of_sidonModNeg`, exact `E_2 = 3n²−3n`, `E_3 = 15n³−45n²+40n`), and the
char-0 Wick/Lam–Leung ceiling `A_r ≤ Wick` (Bessel `I₀(2y) ≤ exp(y²)`, in-tree
`RungBesselEnergy`). Char-0 is closed; the wall is the char-p **spur** `E_r^{Fp} − E_r^{c0}`.

---

## (a) IS THE TRANSFER PROVABLE VIA BOUNDED-BETTI DELIGNE (S6)? — **REDUCES-TO-WALL (Betti grows with n)**

**Verdict: NO genuine-new-route. The S6 Deligne shortcut is REFUTED at prize depth.** All four
attacks converge on this; the central referee question resolves against the route.

The hope: `V_r = {x ∈ (G_m)^{2r} : x_i^n = 1, Σ ε_i x_i = 0}` is a degree-1 torus hyperplane
slice with total Betti `≤ C(2r,r) ≤ 4^r`, n,p-**independent** (Adolphson–Sperber / Bombieri–Katz
toric bounds) ⟹ Weil-II gives `K ≈ 4` uniformly. **This is wrong, and the flaw is a
dimension/main-term/error mis-assignment:**

1. **Dimension flaw.** The constraint `x^n = 1` makes `V_r` a **0-dimensional finite scheme**
   (μ_n is a finite point set, not a positive-dimensional torus). So `C(2r,r) = 4^r` is the
   **char-0 point count / top-cohomology main term**, which legitimately bounds `E_r^{c0}`
   (`K_{c0} ≤ 1`, already in-tree, axiom-clean) — it does **not** bound the char-p arithmetic
   **excess** (the spur). The toric Betti bounds cited govern only the n-free top term.

2. **The defect IS n-dependent (machine-confirmed, three independent probes).**
   - `probe_s6_K_trend.py`: at prize `β=4`, `spur_r = 0` exactly only for `r ≤ 7` at `n=8` but
     `r ≤ 3` at `n=16` — **spur-onset depth DECREASES as n grows** (opposite of n-independence).
     `K_{Fp} = (E_r/Wick)^{1/r} < 1` antitone in r, but **RISES toward 1 with n** at fixed r
     (`r=4`: `0.815 → 0.907 → 0.955` for `n=8,16,32`); `spur/E_{c0}` GROWS with r
     (`0.001 → 0.33` for `r=4→10` at `n=16`).
   - `probe_s6_beta_band.py`: failure threshold `β*(n,r) ~ (r+3)/2`, **grows with both r and n**
     (`r=7`: `β*=4.0` at `n=8` vs `5.0` at `n=16`). At the `β=4` prize column the spur is nonzero
     (transfer FAILS) for all `r ≥ 4` at `n=16`.
   - The empirical scaling law: spur `~ n^{(r+3)/2}` (equivalently `τ_r ~ n^{(r+3)/2}`,
     `spur ~ n^{2r−4}` at fixed β from the K_eff cut) — **polynomial growth in n**. If the `V_r`
     Betti numbers were genuinely `≤ C(2r,r)` n-free, Weil-II would force a uniformly-controlled
     spur; instead it diverges in n. Reproduced bad-prime sets grow `1 → 2 → 6` primes; effective
     Betti back-solved from the data is `1e12–1e22` with `θ < 0` (incoherent with a 4^r bound).

3. **Internal inconsistency of the hopeful framing.** "spur = 0 at `p = n^4` is consistent with
   `K ≈ 4` (Deligne)" is self-contradictory: `spur = 0` forces `K = K_{c0} < 1`, which is
   incompatible with `K = 4`. Reproduced: `K_{Fp} ~ 0.6–0.96 < 1` everywhere there is no spur.

**Lean (axiom-clean, `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`, verified
`scripts/pg-iterate.sh` EXIT 0): `Frontier/_S6BettiDeligne.lean`** — 7 theorems. The Deligne/AS
input is an **explicit named hypothesis** `structure DeligneBettiTransfer` with `betti` and `τ`
exposed (NOT faked, NOT claimed to hold at prize depth). Key arrows:
- `prize_energy_of_betti`: the clean conditional — *granting* `DeligneBettiTransfer` with an
  n-independent threshold and `p ≥ τ r`, the prize energy bound follows. This is the only arrow
  an AG referee would buy, dependence made transparent.
- `thrExp2_le_iff_le_rMax`: threshold inverts depth cap exactly (`2β ≥ r+3 ⟺ r ≤ 2β−3`).
- `prize_rMax_lt_rOpt : rMax 4 < 128` and `betti_grows_with_n_at_prize : 2*4 < thrExp2 128`
  (the prize-depth transfer would need `β ≥ 65 ≫ 4`).

**Net for (a): Deligne gives `K = O(1)` only to `r ≤ rMax = 2β−3 = 5` at prize `β=4`; the prize
needs `r ~ ln q ~ 128`. Past `2β`, the Weil error `p^{θ_r}` (with `θ_r → r`) exceeds
`Wick ~ p^{r/β}`. S6 deletes a hoped-for AG shortcut; the genuine √-cancellation core is
untouched** (same object as `CharSumMomentDeepWall` `r_max = 2 log_n p − 3`,
`MomentMethodPrizeDepthNoGo`, `_DigitStepanovNoGo`, all in-tree).

---

## (b) IS THE PIVOT REAL? — **NO. Conjecture 7.1 is a CONFLATION of FRI soundness with δ*.**

**Verdict: CONFLATION. Do NOT repivot onto Conj 7.1.** The claim that the #444 prize "moved from
BGK to Chai–Fan ePrint 2026/861 Conj 7.1 (sparse-worst-case dominance for above-Johnson FRI
commit-phase soundness)" misidentifies the prize object.

- **The in-tree canonical prize is unambiguous:** `mcaConjecture` / operational `mcaDeltaStar`
  = `epsMCA`, the MCA correlated-agreement threshold via max-far-line incidence
  (`PROXIMITY_PRIZE_WORKBENCH.lean` §1–2: `mcaDeltaStar C ε* = sup{δ : max-far-line-incidence(δ)
  ≤ q·ε*}`, with `le_mcaDeltaStar_of_good` / `mcaDeltaStar_le_of_bad`). This is a **single-round,
  per-radius, list-non-uniqueness** quantity.

- **Conj 7.1's FRI object is distinct:** FRI commit-phase soundness is an **m-round sum**
  `(1/q)·2^m·C` over fold-rounds — a downstream *consumer* of correlated agreement, a different
  function of δ. Machine-checked separation (`probe_conj71_vs_deltastar.py`, exact, proper μ_n,
  `n=8,k=2,p=17,ρ=1/4`): `eps_mca` held flat at `2/17` across `δ=0.125..0.375` while the FRI
  bad-α fraction `e_FRI` rose `0.059 → 0.118`, and the **sparse-worst** `e_FRI_sp = 1.0` at
  every radius. Two facts: (i) `eps_mca` and `e_FRI` are different functions of δ (distinct Lean
  objects, distinct values); (ii) `e_FRI_sp = 1.0` *is* Conj 7.1's premise (sparse dominance) —
  but it is a property of the **FRI object**, not of `eps_mca`. Pinning FRI soundness via a
  sparse-dominance conjecture does **not** pin `eps_mca` absent an unproven FRI-soundness ⟺
  `eps_mca` bridge.

- **The in-tree bricks already adjudicate this correctly and honestly.** `ProofLoop40`
  (Conj 7.1/Q2 → FRI sum), `ProofLoop42` (2026/858 threshold-halving, *sidesteps* `eps_mca`),
  `BridgeLoop41` (2026/861 Thm 2.1 action-orbit) all disclaim prize resolution: 2026/861 Conj 1.1
  is conditional on Q1+Q2, and the 2026/858 verification note says **KEEP OPEN** — the `O(1)/|F|`
  is Conj 7.1 *itself*, not unconditional. S6 correctly does NOT rely on this pivot.

**Net for (b): Conj 7.1 is a settled, different (FRI-soundness) quantity. The prize remains the
list-decoding / MCA threshold `mcaDeltaStar`. The "off-BGK" claim is the contested-and-wrong half
of the lit scan.**

---

## (c) K_eff EVIDENCE — transfer plausibly TRUE at genuine β=4? **REAL but β-GOVERNED ⟹ WALL.**

**Verdict: the bounded/antitone hope is REAL only in a shallow band `r ≲ r*(β) ~ O(β)`; it does
NOT survive to `r ~ ln q`. The structured-prime robustness sub-claim is OVERSTATED.**

- `K_eff = (E_r/Wick)^{1/r} < 1`, antitone in r, bounded — **confirmed** in the shallow band
  (`probe_keff_robust_scale.py`, FFT & period methods matched exact-integer enumeration to
  `<1e-9` for `n=4,8,16`; char-0 anchors `E_2^0=3n²−3n`, `E_3^0=15n³−45n²+40n` verified).
- **But it crosses 1 and rises with r at fixed β=4**: `β=4, n=128 generic`,
  `K_eff(vs c0) = {r5:1.028, r6:1.186, r7:1.527, r8:1.895}`. The prize needs the bound to depth
  `r ~ ln q ~ 89–128`; index-fixed scaling `r*/ln p = {n32:0.481, n64:0.328, n128:0.251}`
  **shrinks**. At the genuine regime `β = 1 + 128/log2(n) → 1+` as `n → 2^30`, `r*` is crushed to
  `O(1)` while `r_prize` stays large, so `r*/r_prize → 0`. New machine-checked scaling law
  `r* ~ O(β)` — the failure depth tracks β, not n-flat. This is the deep-moment/BGK char-p defect
  re-expressed in K_eff language.
- **K_eff drifts UP with n at fixed β=4** (`0.849 → 0.943`; `B/√n: 3.38 → 4.02`) = the
  vanishing-margin **wall signature**, not an n-flat Deligne constant.
- **HONESTY CORRECTION to the hopeful "structured/rough primes ≤ generic" robustness:** this is a
  **WASH** at fixed β=4 (hi-v2 split: structured marginally `≥` generic, `Δ ~ 2e-4`), not a clean
  robustness win. The discriminating power across distinct-arithmetic primes is real (not a
  shrinking-log artifact), but it does **not** rescue the route — the wall is the **n-scaling**,
  which structured/generic share.
- **Knife-edge caveat:** the spur is largely a knife-edge at the *literal smallest* β=4 prime and
  vanishes by `β ~ 4.5`. The wall is the **existence** of such special primes with n-decreasing
  failure-depth, not a generic-prime failure. Evidence ceiling `n ≤ 128` (n=256 ≈ 68GB FFT, not
  reached), but the monotone n-trends are decisive and consistent across all four cuts (fixed-β,
  fixed-n-vary-β, prize-consistent fixed-index, spur-exponent).

**Net for (c): the transfer is plausibly true to `r ~ O(β)`; it is NOT plausibly true to
`r ~ ln q`. K_eff = O(1) in the shallow band IS the pre-existing BGK wall, not an escape.**

---

## (d) S3 / S5 PARTIALS — both REDUCE-TO-WALL (same deep-r ceiling)

`Frontier/_S3S5Partials.lean` (real lake build PASSED, 1971 jobs, axiom-clean, 0 `sorryAx`).

- **S3 (MAXNORM growth):** `MAXNORM(n,4) = 10^{n/4}` exact (exhaustive integer Bareiss norms;
  collapse-antipode `(a²+1)^{n/4}` confirmed to `n=2^20`). Lean `maxNorm4_succ`, `maxNorm4_sq`,
  `s3_gate_fails_at_prize` — the S3 gate `10^{n/4} < p` is **unsatisfiable** for prize `p ≤ n^5`,
  `n ≥ 32` (the norm grows faster than any fixed-β prime). S3 cannot gate the prize.
- **S5 (θ-count shell base `B(n)`):** char-0 `E_r^∞/Wick` saturates to 1 from below (no growth),
  θ shell base → 0. Char-p: `spur = 0` exactly at `β ≥ 4` for all tested n,r; `spur > 0` only at
  `β ~ 2.6–3`; **onset β increases with order r** (n=16: `r=2/3/4` onset `<2.5 / ~3 / ~4`). Lean
  `s5_onset_below_prize` (`rMax 4 = 8 < r_opt = 128`, depends on NO axioms), `s5_reduces_to_wall`,
  `charZeroShellRatioLe1`.
- **Joint:** `s3_s5_joint_reduce_to_wall` — both handles bottom out at the **same deep-r char-p
  ceiling**. Confirms the Fermat `K=2.28` inflation was a sub-prize (β~2–3) artifact, gone at β=4
  for small r; the residual is the n-dependent error at `r ~ ln q`.

---

## (e) SHARPEST CURRENT STATE OF THE OPEN CORE — does any genuinely-new route survive?

**No genuinely-new route survives this round.** Both proposed escapes are closed:
- **S6 bounded-Betti Deligne** = REFUTED (Betti / the operative count grows with n; the
  n-independent `4^r` bounds only the char-0 main term, not the char-p spur; 0-dim point set, not
  a positive-dim torus slice — toric bounds inapplicable to the excess).
- **Conj-7.1 pivot** = CONFLATION (FRI soundness ≠ `mcaDeltaStar`; settled, off-prize object).

The literal #444 prize is **`epsMCA / mcaDeltaStar`** (line-ball incidence), which reduces to the
char-p faithfulness of `E_r(μ_n) ≤ K^r·Wick` uniform to `r ~ ln q`, `n → 2^30`. That residual is
**precisely the BGK/Paley √-cancellation wall** — the deep-r char-p defect = `#sparse signed μ_n
relations vanishing mod p but not in char 0`. It is:
- **char-0 CLOSED** (Lam–Leung / Bessel, `A_r ≤ Wick`, in-tree axiom-clean);
- **char-p OPEN**, named as the Prop `GaussianEnergyBound` (carrier) and equivalently
  `CharSumMomentDeepWall` `r_max = 2 log_n p − 3` ≪ `r_opt = 128` (16× overshoot, formalized in
  `MomentMethodPrizeDepthNoGo`); consistent with `no_second_order_route` (PrizeEquivalencePin)
  and the `_DigitStepanovNoGo` / defect-cancellation-depth trilogy.

The in-tree bridge to the prize is **conditional** (`GaussPeriodMomentBound` ⇐ `GaussianEnergyBound`),
not a closure. The new contribution of this round is **subtractive and quantitative**: two
plausible AG/protocol escape hatches deleted, plus the machine-checked scaling laws
`spur ~ n^{(r+3)/2}`, `r* ~ O(β)`, `β*(n,r) ~ (r+3)/2` that pin *why* Deligne cannot reach prize
depth. The open core is unchanged and well-localized; the path forward must control the
**n-dependent lower-cohomology defect** (not the n-free top Betti) at depth `r ~ ln q` — for which
no current technique (Deligne top-term, Burgess/large-sieve out-of-regime, action–orbit norm,
2-power rigidity, dyadic Fourier-uncertainty char-p side) is known to suffice.

---

## Artifacts (absolute paths, all verified to exist this session)

Lean (axiom-clean):
- `C:/Users/Administrator/arklib/ArkLib/Data/CodingTheory/ProximityGap/Frontier/_S6BettiDeligne.lean`
- `C:/Users/Administrator/arklib/ArkLib/Data/CodingTheory/ProximityGap/Frontier/_S3S5Partials.lean`
- `C:/Users/Administrator/arklib/ArkLib/Data/CodingTheory/ProximityGap/GaussPeriodMomentBound.lean`
  (the **real** conditional bridge ⇐ open `GaussianEnergyBound`)
- `C:/Users/Administrator/arklib/ArkLib/Data/CodingTheory/ProximityGap/AdditiveEnergySidonModNeg.lean`
  (real char-0 anchor)
- `C:/Users/Administrator/arklib/ArkLib/Data/CodingTheory/ProximityGap/PROXIMITY_PRIZE_WORKBENCH.lean`
  (canonical prize = `mcaConjecture` / `mcaDeltaStar` / `epsMCA`)
- In-tree wall substrate: `CharSumMomentDeepWall.lean`, `Frontier/MomentMethodPrizeDepthNoGo.lean`,
  `Frontier/_DigitStepanovNoGo.lean`, `EnergyExcessStructure.lean`, `HasseWeilBoundInstances.lean`

Probes (exact, proper μ_n, never full group, `p ≫ n^3`):
- `scripts/probes/probe_s6_K_trend.py`, `probe_s6_beta_band.py`, `probe_s6_betti_config.py`
- `scripts/probes/probe_conj71_vs_deltastar.py`
- `scripts/probes/probe_keff_robust_scale.py`
- `scripts/probes/probe_s3_maxnorm_growth.py`, `probe_s5_shell_base.py`

Prior KB notes (companion):
- `ArkLib/Data/CodingTheory/ProximityGap/docs/kb/deltastar-444-s6-betti-deligne-nogo.md`
- `ArkLib/Data/CodingTheory/ProximityGap/docs/kb/deltastar-444-keff-robustness-beta-governed-wall.md`

**Honesty contract intact:** no fabricated closure; every proven claim is axiom-clean Lean
(axioms ⊆ `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`); every open input is a named
hypothesis; the Deligne AG input is an explicit `structure`, not an axiom; the task's three
"anchor" theorem names were verified ABSENT and the real conditional bridge substituted.
