# δ* #444 — the S6 BOUNDED-BETTI DELIGNE route: REDUCES-TO-WALL (2026-06-17)

**Lead (from #444 S6 frontier).** Prove the char-`p` energy transfer `E_r(μ_n) ≤ K^r·Wick`
(`Wick = (2r−1)‼·n^r`) uniformly to `r ≈ log q`, `n → 2^30`, at prize `β = log_n p ≈ 4`, by a
Deligne / Adolphson–Sperber **toric Betti bound** on the configuration variety
`V_r = { x ∈ (G_m)^{2r} : xᵢⁿ = 1, Σ εᵢxᵢ = 0 }`. The hope: total Betti `≤ C(2r,r) ≤ 4^r`,
**independent of `n` and `p`** ⟹ `spur_r(p) = E_r^{Fp} − E_r^{c0} ≤ Betti·p^θ` ⟹ `K = O(1)` (≈4).

**Verdict: REDUCES-TO-WALL.** The Adolphson–Sperber/Deligne top-Betti bound is *genuinely
n-independent*, but it governs only the **main term**; the prize needs the bound at depth
`r ≈ log q ≫ 2β`, where the **error onset is n-DEPENDENT** (`τ_r ≈ n^{(r+3)/2}`). The "strong" form
(`spur = 0` at generic `p = n^4`) is REFUTED past a small, *n-decreasing* depth; the "weak" form
(`K = O(1)`) that survives **is the pre-existing BGK/Paley √-cancellation wall**, which Deligne does
not deliver. No false claim; the genuine √n-cancellation open core is untouched.

## The decomposition that settles it (3 exact probes + 1 axiom-clean Lean file)

Probes (exact, PROPER `μ_n`, `p =` smallest prime `≡ 1 mod n` above `n^β`, never the full group):
`scripts/probes/probe_s6_betti_config.py`, `probe_s6_K_trend.py`, `probe_s6_beta_band.py`.
Char-`0` energy computed EXACTLY via cyclotomic `Z^{n/2}`-coordinates (`n = 2^μ`, `ζ^{n/2} = −1`);
char-`p` via exact convolution / FFT. Lean: `Frontier/_S6BettiDeligne.lean` (axiom-clean
`[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`).

### (1) STRONG claim `spur_r(p) = 0` at `β = 4` — REFUTED, and the onset depth SHRINKS with n.

`spur_r(p) = 0` exactly (char-`p` energy = char-`0` energy on the nose) holds only up to a depth that
*decreases* as `n` grows:

| n  | spur = 0 exactly for r ≤ | breaks at r = |
|----|--------------------------|---------------|
| 8  | 7                        | 8             |
| 16 | 3                        | 4             |

The opposite of n-independence: a uniform (n-independent) Deligne main-term-only picture would keep a
*fixed* onset. (Even sharper than the in-tree `r_max = 2β−3 = 5` cap.)

### (2) The THRESHOLD LAW `τ_r ≈ n^{(r+3)/2}` — machine-confirmed (`probe_s6_beta_band.py`).

`β*(n,r)` := smallest field-exponent band where `spur → 0`, vs `(r+3)/2`:

| r | β*(n=8) | β*(n=16) | (r+3)/2 |
|---|---------|----------|---------|
| 2 | 3.0     | 3.0      | 2.5     |
| 4 | 3.0     | 3.5      | 3.5     |
| 5 | 3.5     | 4.5      | 4.0     |
| 6 | 3.5     | 5.0      | 4.5     |
| 7 | 4.0     | 5.0      | 5.0     |

`β*` climbs with `r` (tracks `(r+3)/2`) AND grows with `n` at fixed `r` (e.g. r=7: 4.0 → 5.0 from
n=8 to n=16). So the spur=0 onset `τ_r ≈ n^{β*}` ⟹ at FIXED prize `β = 4`, the transfer FAILS for
all `r ≥ 4` (n=16 column nonzero from r=4 on). The controlling defect GROWS with n = the wall.

### (3) WEAK claim `K = O(1)` survives — but IS the BGK wall, not a Deligne consequence.

`K_Fp = (E_r^{Fp}/Wick)^{1/r}` at `β = 4` is `< 1` and antitone in `r` (good), BUT:
- **rises toward 1 as n grows** at fixed r: `K_Fp(r=4) = 0.815, 0.907, 0.955` for `n = 8, 16, 32`;
- `spur/E_c0` **grows with r**: `0.0010 → 0.33` for `r = 4 → 10` at `n = 16`.

So `K = O(1)` is empirically plausible (it is the conjectured `E_r ≤ K^r·Wick` = the moment-method
input = the BGK/Paley √-cancellation conjecture) — but it is governed by the n-dependent threshold,
NOT proven by any n-independent Betti number. Deligne's n-independent top-Betti bound is *consistent*
with `K = O(1)` but does not *imply* it at prize depth, because the error term `Betti·p^{θ_r}` (with
`θ_r → r`, the variety's effective exponential-sum dimension growing with r) exceeds `Wick ≍ p^{r/β}`
once `r > ⌊2β⌋`.

## Why the geometry does not save it (the honest AG content)

The variety `V_r` is cut from the `2r`-torus by `2r` binomial constraints `xᵢⁿ = 1` (degree `n`!) and
ONE hyperplane. The `xᵢⁿ = 1` constraints make the relevant character-sum object
`η_b = Σ_{x∈μ_n} e_p(bx)` a sum over an **n-point scheme whose "curve" `y^n = …` has genus `≍ n`**
(cf. in-tree `HasseWeilBoundInstances.lean`: the multiplicative Weil bound is `|Σ χ(f)| ≤ (deg f−1)√p`
— the constant scales with `deg`, i.e. with `n`). The toric *top*-Betti number of the energy count is
n-independent (`≤ 4^r`), but it bounds the leading term; the **defect / lower-cohomology error** that
makes `E_r^{Fp} > E_r^{c0}` is supported on primes dividing cyclotomic norms of sparse vanishing
`2^μ`-th-root relations (in-tree `EnergyExcessStructure.lean`: `spur ⟺ p | N_{a,b,c,d}`, bad-prime
set grows: Bad(4)={5}, Bad(8)={17,41}, Bad(16)={17,97,113,193,257,337}). The number and size of these
relations — hence the threshold `τ_r` — grow with `n`. That is precisely the BGK wall in cohomological
clothing.

## Same wall as the rest of the census

Identical open core to `CharSumMomentDeepWall.lean` (`r_max = 2 log_n p − 3`),
`MomentMethodPrizeDepthNoGo.lean` (`r_max = ⌊2β⌋ = 8 < r_opt = 128`), `BurgessIndexOvershoot.lean`,
`_DigitStepanovNoGo.lean` (Stepanov delivers magnitude not cancellation). S6 is the *cohomological*
restatement of the moment-depth wall: the depth at which the char-0 energy value transfers is capped
by an n-dependent threshold, and the prize optimum sits far past it. Deligne is the right *language*
for the main term and confirms `K_c0 ≤ 1` char-0 side (already in-tree
`RungBesselEnergy.bessel_energy_le_gaussian`), but offers no n-independent handle on the error.

## Files
- `Frontier/_S6BettiDeligne.lean` — named Deligne hypothesis `DeligneBettiTransfer` (NOT proven);
  conditional reduction `prize_energy_of_betti`; threshold diagnostic `thrExp2_le_iff_le_rMax`,
  `prize_depth_cap` (`rMax 4 = 5`), `threshold_caps_depth`, `betti_grows_with_n_at_prize`,
  `prize_rMax_lt_rOpt`. 7 axiom-clean thms.
- `scripts/probes/probe_s6_betti_config.py` — spur at β≈2 vs β≈4 (Fermat artifact gone past n^4).
- `scripts/probes/probe_s6_K_trend.py` — strong-vs-weak split; K_Fp / spur trends to r=13.
- `scripts/probes/probe_s6_beta_band.py` — the `β*(n,r) ≈ (r+3)/2` threshold table.

## References
- Adolphson, Sperber, *Exponential sums and Newton polyhedra*, Ann. Math. 130 (1989).
- Bombieri, *On exponential sums in finite fields*, Amer. J. Math. 88 (1966); Deligne, *Weil II*, 1981.
- In-tree: `CharSumMomentDeepWall`, `MomentMethodPrizeDepthNoGo`, `EnergyExcessStructure`,
  `RungBesselEnergy`, `HasseWeilBoundInstances`, `StepanovWeilEngine` (Weil recovers only Johnson).
