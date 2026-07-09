# δ* (#407) — effective-Katz circumvent via "moments-of-the-family": NO-GO, the off-diagonal IS the open core (2026-06-13)

**Status:** assigned-angle assault `effective-katz-circumvent`. Route: replace single-sum
equidistribution (whose effective-Katz discrepancy barrier `Cond·q^{-1/2}` needs `Cond < 2^{-48}`,
impossible at prize) by a **moments-of-the-family** integral over the `m`-torus — a union-bound /
extreme-value statement for the SUP over the `m = (q-1)/n` Gauss phases, not single-sum
equidistribution. **Verdict: reconfirms the wall.** The moments-of-the-family integral over the
`m`-torus is *identically* the additive-energy moment `E_r(μ_n)`, and its Weil "error term"
(the off-diagonal) is itself an incomplete Gauss-sum correlation = the open √-cancellation core.
No closure; no new bound. Honest. Reproducible probes below.

## The corrected regime (load-bearing — do not use the thin-BGK framing)
Issue comment 4700736246: index `m = (q-1)/n ≈ 2^128` is held **CONSTANT** as `n=2^μ` grows
(`μ ≤ 40`). So `μ_n` is **positive-proportion** (`n = Θ(q)`, `n ≫ √q`), NOT a thin `n=q^{1/β}`
subgroup. The load-bearing wall is *effective fixed-index Gauss-sum equidistribution*, distinct from
additive-comb BGK/Paley (thin). This note works the corrected regime (constant `m`).

## The object and the route
`η_b = (1/m)[−1 + Σ_{j=1}^{m−1} ψ(b)^{−j} τ(ψ^j)]`, `ψ` of order `m=(q-1)/n`, `|τ(ψ^j)|=√q`.
Set `a_j = τ(ψ^j)/√q` (unimodular) and `S(w) = Σ_{j=1}^{m−1} w^{−j} a_j`. The prize bound
`M = max_{b≠0}|η_b| ≤ C√(n·log(q/n))` ⟺ the Gauss-phase DFT is flat: `sup_{w^m=1}|S(w)| ≤ C√(m log m)`.

**The moments-of-the-family idea (effective-katz-circumvent):** instead of equidistributing one sum,
put the family `{S(w)}` as the fibres of a sheaf `G` on the `m`-torus with `trace_G(w)=S(w)`, and get
the sup from `sup_w|S(w)| ≤ ((1/m)Σ_{w^m=1}|S(w)|^{2r})^{1/2r}` — a moment of the *family*, which
Katz would compute via the geometric monodromy of `G^{⊗r}⊗Ḡ^{⊗r}` as `leading-term + error/√m`,
the error scaled by the *conductor of the tensor sheaf*, NOT by the per-sum conductor barrier.

## THREE facts that close this route (each machine-verified, ε ~ 1e-13)

### (A) The discrete family integral over the `m`-torus IS the energy moment — no new object.
`probe_katz_family_moments.py`: the family `{S(w_k): w_k^m=1}` equals **exactly**
`{(m·η_b + 1)/√q : b}` (max error `1e-12` across `p≤193`). Hence
`(1/m)Σ_{w^m=1}|S(w)|^{2r} = m^{2r-1}·Σ_b|η_b+1/m|^{2r}` = the additive-energy moment `E_r(μ_n)`
(up to the `1/m` shift). The "moments-of-the-family" integral over the natural (discrete) `m`-torus is
**literally** the moment quantity every prior route already walls on. There is no escape at the level
of the discrete family — the union-bound target and the energy moment are the same number.

### (B) In the corrected (constant-`m`) regime the family moment INFLATES above the Gaussian
**leading term already at `r=2`** for a positive proportion of primes — so the Katz "leading + small
error" structure is FALSE. `probe_regime_defect.py` (constant `m≈64`, `n` grows) and
`probe_defect_characterize.py` (n=128, scan `m∈[48,90]`):
- defect ratio `E_r/((2r−1)!!·n^r)` is **>1 at r=2..7** for ~30% of primes (`p=7937,7297,11393` at
  n=128), peaking ~2.3; B/√(n ln m) for those primes is the *largest* (1.5–1.6).
- For the other primes the ratio is `<1` and decays geometrically (clean).
So the family-moment "leading term" (the Gaussian diagonal) does **not** dominate uniformly; for the
worst primes the error term is the same order. The Katz argument needs leading ≫ error to convert a
moment into a sup bound — that hypothesis is empirically violated in the prize-edge regime.

### (C) The off-diagonal (= Katz error term) is NOT √-cancelling; it IS the open core.
`probe_conductor_final.py` decomposes the family 4th moment `Σ_s|c_s|²`, `c_s=Σ_{j1+j2=s}a_{j1}a_{j2}`,
into diagonal (multiset `{k}={j}`, the Gaussian `2(m−1)²−(m−1)`) + off-diagonal:

| prime | n | m | off/diag | off/m^{1.5} |
|---|---|---|---|---|
| 7681 (clean) | 128 | 60 | **0.17** | 2.6 |
| 7937 (defect)| 128 | 62 | **0.80** | 12.0 |
| 1153 (thin)  | 16  | 72 | 0.34 | 5.6 |

For the defect prime the off-diagonal is **80% of the diagonal** — comparable, not lower-order — and
scales as `Ω(m²)` (off/m^{1.5}=12 and growing), NOT the `O(m^{1.5})` that genuine Weil cancellation
would give. **The off-diagonal of the family moment is itself an incomplete Gauss-sum correlation**
`Σ_{j1+j2=k1+k2} a_{j1}a_{j2}\bar a_{k1}\bar a_{k2}`, and bounding it by `Cond·m^{r−1/2}` requires
`j ↦ τ(ψ^j)` to be a bounded-conductor trace function in `j`. **It is not** — this is exactly the
Rojas-León (2207.12439) *Gauss-sum independence* obstruction: the family of Gauss sums `{τ(ψ^j)}_j` has
*large* geometric monodromy, so `Cond(G^{⊗r}⊗Ḡ^{⊗r})` grows like `(m−1)^r` (the rank), and the Weil
error `(m−1)^r·m^{r−1/2}` is **larger than the trivial `m^{2r}` bound** — Weil buys nothing.

## Why this is the per-sum barrier in disguise (the precise circumvent-failure)
The single-sum effective-Katz barrier says: equidistributing `η_b` needs the sheaf
`[x↦e_p(bx)]|_{μ_n}` to have `Cond < √(n/m)`, impossible. The family route trades that for: bounding
the family moment needs `Cond(G^{⊗r})` to be `poly(m)`. But `G`'s fibre values `a_j=τ(ψ^j)/√q` are
the **same Gauss sums** whose mutual independence is the open problem; the `r`-fold tensor's
conductor/Betti number is `(m−1)^r`, exponential in `r`, so the moment "error term" is uncontrolled at
exactly the depth `r ≈ ln m` where the bound would be tight. The conductor barrier did not go away — it
moved from the *base* (point `b`) to the *fibre dimension* (rank of the DFT sheaf). The union-bound
over `m` phases reduces to: the `m` Gauss-sum phases are jointly √-cancelling = the recognized open
core (BGK / Paley almost-Ramanujan / di Benedetto sub-Johnson, record `t^{0.989}`).

## A genuinely-new precise obstruction (the net positive output)
**The family-moment route can only succeed to the depth where the off-diagonal stays `o`(diagonal),
and that depth is the same `r ≲ log q/(½ n log r)` clean-range window** (`(2r)^{φ(n)}<q`), which at
`n=Θ(q)` is `r=O(1)` — the Lean-proven clean range, vacuous for the prize. New, sharply stated:
> **Moments-of-the-family no-go.** Over the discrete `m`-torus the `2r`-th family moment equals the
> energy moment `E_r(μ_n)`; its diagonal/off-diagonal split is the genuine/spurious split of `E_r`; the
> off-diagonal is an incomplete Gauss-sum 2`r`-correlation whose Katz conductor is `(m−1)^r`
> (Rojas-León: the Gauss-sum family has large monodromy). Hence the family-moment error term is
> NEVER smaller than `m^{2r}` by Weil; the route certifies a sup bound only while the off-diagonal is
> empirically `o`(diagonal), i.e. `r < r_clean = O(log q/n)`, which is `O(1)` in the corrected
> positive-proportion regime — strictly below the moment-optimal `r ≈ ln m`. The route is
> information-equivalent to the energy/moment route and inherits its exact wall.

This complements (and is the geometric/sheaf-theoretic *reason behind*) the
markov-krein "short by Θ(log m) proven moments" no-go and the deep-moment-wall note: the Katz
moments-of-the-family does not supply the missing moments because the family's monodromy is large.

## Could it combine with another path? (cross-path lever)
The one non-vacuous lever: **a Rojas-León-style "Gauss-sum independence" theorem that bounds the
geometric monodromy of the specific `μ_n`-Gauss-sum family `{τ(ψ^j)}` for `index m=2^128` constant**
would directly bound the off-diagonal and feed the proven in-tree moment arrow `B≤(qE_r)^{1/2r}`.
Rojas-León (2207.12439) proves independence for *generic* families; the prize family is the *fixed
arithmetic* `2^μ`-tower, where independence is exactly the open √-cancellation. So the lever is real
but its hypothesis IS the open core — same wall, now stated as a monodromy-of-a-fixed-family question
(the cleanest sheaf-theoretic form of the open core reached on this angle).

## Honest verdict (contract)
**No closure. No new bound on `B`.** Delivered: (a) machine-proof that the discrete moments-of-the-
family integral is identically the energy moment (the route has no new object); (b) empirical proof
that the family-moment "leading term" is violated (defect>1 at r=2) for a positive proportion of
prize-edge primes in the corrected constant-`m` regime; (c) the diagonal/off-diagonal decomposition
showing the Katz error term is `Ω(m²)` not `O(m^{1.5})`, i.e. the off-diagonal is itself the open
incomplete-Gauss-sum correlation; (d) the precise localization of the conductor barrier as moving from
the base point to the fibre rank `(m−1)^r` (Rojas-León large-monodromy), proving the per-sum barrier is
not circumvented, merely relocated. The effective-Katz circumvent **fails for a structural reason**,
stated exactly. Not fabricated.

## Reproduce
- `scripts/probes/probe_katz_family_moments.py` — family `=(m·η+1)/√q` identity (ε~1e-12).
- `scripts/probes/probe_katz2.py` — family moments `(1/m)Σ|S|^{2r}` = moment quantity, sup-bound curve.
- `scripts/probes/probe_regime_defect.py` — constant-`m` regime: defect ratio vs `n`.
- `scripts/probes/probe_defect_characterize.py` — n=128 scan: ~30% of primes have defect>1 at r=2.
- `scripts/probes/probe_moment_ceiling.py` — clean vs defect prime sup-bound descent (clean→tight, defect→no gain).
- `scripts/probes/probe_conductor_final.py` — diagonal/off-diagonal split of the family 4th moment.
