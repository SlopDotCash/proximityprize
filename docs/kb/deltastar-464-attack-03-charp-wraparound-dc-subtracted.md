# Attack 03 — Char-p wraparound: DC-subtracted moment `E_r ≤ Wick` at depth `r ≈ log p`

Issue #464. Angle: prove (or refute) the DC-subtracted Wick bound
`A_r := (1/q)∑_{b≠0}‖η_b‖^{2r} ≤ (2r−1)‼·n^r` at prize depth `r ≈ ln q`, which via the moment
method gives `M(n) ≤ √(2n ln q)` — the prize sup-bound.

Brick: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_Attack03DepthGatedWraparound.lean`
(axiom-clean: `propext, Classical.choice, Quot.sound`; no `sorryAx`).

## 1. The target theorem (what closing this angle would prove)

> **`A_r ≤ Wick_r`** for `μ_n ⊂ F_q^×`, `n = 2^μ`, `q ≈ n·2^128`, at every depth `r ≤ ⌊ln q⌋ + O(1)`.

In-tree this discharges the canonical reduction chain
`DCEnergyCorrection.DCEnergyBound G r ⟹ eta_pow_le_of_dcEnergyBound ⟹ ∀b≠0, ‖η_b‖^{2r} ≤ q·Wick_r`,
optimized at `r ≈ ln q` to `M ≤ √(2n ln q)`. That is exactly input (1) of `_PrizeFloorOfBGK`
(WorstCaseIncompleteSumBound), the BGK sup-bound. (Input (2), the BCHKS-1.12 hyperplane upgrade, is
a separate object this angle does not touch.)

## 2. The substrate, precisely located

- `DCSubtractedMoment.sum_nonzero_moment`: `∑_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}` (exact identity).
- `DCEnergyEssential.not_gaussianEnergyBound_of_deep`: the **raw** `E_r ≤ Wick` is FALSE past the DC
  crossover (`n=64` onward, `+1301` at `n=2^30`) — DC mass `n^{2r}/q` swamps Wick. So the bound MUST
  be DC-subtracted. (This is why the angle says "DC-subtracted" specifically.)
- `_AvW0.besselWick_allR`: the **char-0 ceiling** `E_r^{char0} ≤ Wick_r` is LANDED (Bessel→exp
  coefficientwise domination, the Lam–Leung antipodal-balance shadow). This half is *done*.
- `_AvF3.energyCharP_eq_char0_add_wrapExcess`: `E_r^{F_p} = E_r^{char0} + W_r`, with
  `W_r := #{char-p collisions not char-0 collisions} ≥ 0`.
- `SubgroupGaussSumRawMoment.subgroup_gaussSum_rawMoment`: `∑_b η_b^r = q·N₀(G,r)` (the collision
  count engine).

**Net:** since `E_r^{char0} ≤ Wick` is landed and `A_r = E_r − n^{2r}/q ≈ E_r^{F_p} − (DC)`, the
entire remaining content of `A_r ≤ Wick` is **`W_r ≤ q·Wick_r − (correction)`** — bounding the wrap
surplus `W_r`. Everything reduces to: *do short `±1` relations of `2^μ`-th roots vanish mod the prize
prime `p`, and how many?*

## 3. The proof attempt (and where it lives or dies)

### 3a. The good-prime escape — works at FIXED depth

`_AvCP_AlmostAllPrimesNoWraparound` proves `W_r = 0` for all but finitely many `p`: the bad primes
are exactly the prime divisors of the nonzero integer relation-norms `N i` (a `Finset`), and
`not_dvd_of_not_badPrime` shows `p ∤ N i` off that set. `_AvCP_W3UnconditionalOutsideD3` pushes this
to a genuine prize statement: `max D_3(16) = 41521 < 16^4`, so **every** prize prime `p ≥ n^4` is
outside the depth-3 bad set, giving `W_3 = 0` unconditionally at the prize prime. If this extended to
depth `r ≈ ln q`, the prize would close: `A_r = E_r^{char0} ≤ Wick`, done.

### 3b. Why it does not extend — the depth-gating obstruction (this file's content)

A wraparound is a relation-norm `D = ∑u − ∑v` (lifts of roots, each in `[0,p)`) with `D ≠ 0` as an
integer but `p ∣ D`. By divisibility this forces `p ≤ |D|` (`wraparound_requires_norm_ge_p`). The
escape in 3a works precisely because at depth 3, `|D| ≤ 2(p−1)` and the *distinct* relevant norms
happen to stay `< p` (`< n^4`), so no `D` reaches a multiple of `p`. Formalized abstractly:
`noWraparound_of_range_lt_p` — if `r·(B−1) < p` then no in-range nonzero `D` is a `p`-multiple.

The kill: **the range bound `r·(B−1)` exceeds `p` for every `r ≥ 2`** when `B = p` (lifts live in
`[0,p)`). `subsetSumDiff_abs_le` gives `|D| ≤ r·(p−1)`, and `escape_fails_for_depth_ge_two` proves
`¬(r·(p−1) < p)` for all `r ≥ 2, p ≥ 2`. So the difference range `(−r·p, r·p)` contains `≈ r` distinct
nonzero multiples of `p`. At prize depth `r ≈ ln q ≈ 83`, there are `≈ 83` reachable `p`-multiples per
relation pattern. **Wraparounds are generic for `r ≥ 2`; the finite-bad-set escape is a depth-1
(Parseval) phenomenon.** The cheap route cannot reach prize depth.

## 4. Adversarial self-refutation

- *"Maybe most reachable `p`-multiples are not actually hit by `±1` relations of `2^μ`-roots, so
  `W_r` stays small even though the range is large."* — Correct, and that is **exactly the open
  question**, not an escape. The size law (§3b) only shows wraparounds are *possible*; whether the
  *count* `W_r ≤ q·Wick_r` is the quantitative BGK/Paley statement. My brick does NOT claim `W_r`
  large; it claims the *qualitative* finite-bad-set mechanism cannot apply. Honest.
- *"Could the 2-power structure (Lam–Leung) bound `W_r`?"* — No. Lam–Leung bounds the **char-0** side
  (`E_r^{char0} ≤ Wick`, already landed). `W_r` counts char-`p`-ONLY collisions — relations that
  vanish mod `p` but not in `ℤ[ζ_n]`. These are invisible to any cyclotomic (char-0) relation, so no
  amount of antipodal-balance structure on the roots constrains them. Confirmed by
  `_AvCP_AAPKernelCountermodel`: the sharper `A_K ≤ E_K^{char0}` (`W_K ≤ 0`) is REFUTED at `p=76001`,
  `K=6` (`W_K > 0`, growing through `K = ⌊ln p⌋`).
- *"Is the `r·(B−1)` bound too loose — does the sharper `(r−1)·(B−1)` rescue depth 2?"* — No: even
  `(r−1)·(p−1) ≥ p` for `r ≥ 3`, and depth 2 is the trivial second moment (`W_2 = 0`,
  `eta_quartic_le_uncond`) handled separately. The gate bites at `r ≥ 3`, well below prize depth ~83.

## 5. The exact lever vs. the wall

**Lever that would crack it:** a *quantitative* bound on the wrap count
`W_r = #{(u,v) ∈ μ_n^r × μ_n^r : ∑lift(u) ≡ ∑lift(v) (mod p), ≢ in ℤ}` showing
`W_r ≤ q·Wick_r − (q·E_r^{char0} − n^{2r})` at `r ≈ ln q`. This is precisely the additive-energy /
Heath-Brown–Konyagin object: best proven `O(n^{7/2})` for the integer (geometric-progression) energy,
which is **worse** than the `O(n^3)` Sidon floor the prize needs, and the mod-`p` count `W_r` can
only exceed the integer anomaly (`Ef ≥ Ei ≥ Ec`, `_AvW4.wraparound_decomp`).

**The wall:** bounding `W_r` is the BGK/Paley-graph spectrum question in disguise — equivalently
`M = λ₂(Cay(F_q, μ_n)) ≤ √(2n ln q)` — open, best proven `n^{1−o(1)}` (BGK). The 2-power root
structure does not help because it constrains the char-0 shadow, not the char-`p`-only surplus.

## 6. Verdict

**Reduces to Paley.** This angle does NOT bypass the wall. Contribution: an axiom-clean, exact
certificate (`_Attack03DepthGatedWraparound.lean`) proving that the only *cheap* mechanism for
`W_r = 0` (the finite-bad-set / good-prime escape, which genuinely settles depth ≤ 3 at prize primes)
is **intrinsically depth-1**: the integer relation-norms have range `Θ(r·p)`, exceeding `p` for every
`r ≥ 2`, so prize depth `r ≈ ln q` cannot inherit it. The remaining open content `A_r ≤ Wick_r` at
prize depth is identically the BGK/Paley wall (the quantitative wrap-count question), with the named
open input being the wrap-surplus bound `W_r ≤ q·Wick_r − (q·E_r^{char0} − n^{2r})`. Survives
adversarial self-refutation; honestly labeled as a reduction, not a closure.
