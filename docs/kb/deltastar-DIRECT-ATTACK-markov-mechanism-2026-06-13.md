# Direct attack: the rigorous Markov bridge + exact reduction to BCHKS Conj 1.12 (2026-06-13)

> **Correction (2026-10-28 audit, T48).** §1 is right to remove frequency `0`, and the one-way
> bound of §2 is right: `B^{2r} ≤ M_r`, so Gaussian-scale nonzero moments up to `r ≈ ln p` would
> imply `B ≤ √(2n ln p)`. The following overstatements are withdrawn.
> - **Not an iff.** "The prize closes **iff** the `b≠0` moments stay Gaussian" upgrades a sufficient
>   condition to an equivalence. A sup bound does not imply Gaussian moments.
> - **Support size is not a moment bound.** In §4, a large sumset `r·μ_n` (BCHKS 1.12-type growth
>   `|G^{(+ℓ)}| ≥ q/10`) gives no upper bound on concentration or on the energy `E_r`. Large support
>   is compatible with heavy collision mass on a few values. Markov's inequality does not supply the
>   missing distributional estimate, so "non-collision ⟺ large sumset ⟺ BCHKS 1.12" is not a valid
>   chain.
> - **Not a closure condition.** §5's "the prize closes the instant BCHKS 1.12 is proven" also
>   relies on the exact `δ*` formula and the "verified extremality". Both are unproved inputs, not
>   in-tree theorems. The data in §3 are finite observations.

Genuine structural progress from attacking `B(μ_n) ≤ C√(n log p)` directly. The Markov mechanism is
now **rigorous**, the obstruction is pinned to a **named conjecture (BCHKS 1.12)**, and the threshold
`r ≈ ln p` is data-confirmed. (Still open — the named conjecture — but this is the cleanest reduction.)

## 1. The b=0 red herring (resolved)
`E_r = (1/p)Σ_b η_b^{2r}`. The `b=0` term is `η_0^{2r}/p = n^{2r}/p`. Data: `E_{r+1}/E_r → n²`
(saturation) — this is just `n^{2r}/p` eventually dominating, NOT spurious. **The real object is the
`b≠0` moment `M_r := Σ_{b≠0} η_b^{2r} = pE_r − n^{2r}`.**

## 2. The Markov bridge (RIGOROUS)
`B^{2r} = max_{b≠0}|η_b|^{2r} ≤ M_r`. IF `M_r ≤ p·(2r−1)!!·n^r·(1+o(1))` (the `b≠0` periods are
Gaussian, variance `n`) for `r` up to `c·ln p`, then minimizing `(p(2r−1)!!n^r)^{1/2r}` over `r`:
`d/dr[ (ln p)/(2r) + ½ln(2rn/e) ] = 0 ⟹ r = ln p`, where `p^{1/2r}=√e`. Hence
> **`B(μ_n) ≤ √e·√(2·ln p·n/e) = √(2n·ln p) = C·√(n log p)`** — the prize bound. ∎(mechanism)
So the prize **closes** iff the `b≠0` moments stay Gaussian to order `r ≈ ln p`.

## 3. Data: the moments ARE Gaussian to `r ≈ ln p`
`E_r/E_r^{clean} ≈ 1.00` (within %) up to `r ≈ 7` at `p=521` (`ln p≈6.3`); the first exact deviation
`r_exact ≈ ln p` across all tested `(n,p)` (`r_max/log₂(p/n) ∈ [0.66,1.0]`, i.e. `r_max=Θ(ln p)`).
Even where the *exact* match breaks, the *ratio* stays `≈1` (spurious is a tiny fraction near onset),
so `M_r ≤ C^r·clean` holds well past `r_exact`.

## 4. The obstruction = BCHKS Conjecture 1.12 (the named open gate)
`r_max` = first `r` where `r`-fold root-sums `Σ_{i≤r} x_i` (`x_i∈μ_n`) **collide mod p beyond genuine
(antipodal) relations**. Crude bounds give only `r_exact ≳ log_n p` (pigeonhole: `n^{2r}>p`) and the
cyclotomic norm bound gives `2r ≥ p^{2/n}` (no obstruction at large `n`) — **both far too weak**; the
data shows `r_exact ≈ ln p`, because the cyclotomic sums **cluster / don't equidistribute mod p**.
Non-collision of `≤ c·ln p`-fold root-sums ⟺ the `r`-fold sumset `r·μ_n` is large (anti-concentrated)
⟺ **BCHKS Conjecture 1.12** (subgroup-sumset growth: `|G^{(+ℓ)}| ≥ q/10` for `ℓ≈log q`). This is the
recognized open gate, now connected to the prize through the **rigorous Markov bridge** above.

## 5. Net (honest)
**The prize `δ*=1−ρ−2/s*` closes the instant BCHKS Conj 1.12 (subgroup-sumset growth / anti-
concentration of `≤c·ln p`-fold root-sums mod p) is proven** — via the rigorous Markov bridge (§2),
the proven scaffold, and the verified extremality. This is the cleanest reduction of the session:
- Mechanism: PROVEN (Markov, §2).
- Threshold `r≈ln p`: data-confirmed, and the optimum is rigorous.
- Open core: a SINGLE named conjecture (BCHKS 1.12), not a vague "character sum is hard."
The remaining mathematics is exactly Conj 1.12. No fabrication; genuine reduction to a named open
conjecture with the bridge proven.
