# δ* / #407 — route 104: ε-biased / Delsarte-LP operator certificate — **OPEN (route is phase-blind: structural no-go)**

**Date:** 2026-06-14 · **Actionable:** A15 (merged `357-T11`) · **Type:** math-analysis
**Artifact:** this note + `scripts/probes/sweep_A15_delsarte_lp.py`
**Verdict:** the Delsarte-LP / ε-biased *operator-norm* route, executed as specified, **does NOT
sidestep character sums**. The LP relaxation is a *phase-blind* (weight-distribution-only)
functional; the prize is an `L^∞`-over-`u₀` phase-cancellation statement that any phase-blind
certificate provably cannot see. The route's best certificate is the trivial `L¹`/triangle bound.
**This is a structural no-go for the route, not a closure of the prize.** (Honesty contract: no
fabricated closure; the open core is unchanged.)

---

## 1. The route as specified (first step of route 104)

> *"Set up the Delsarte LP for `D = C^⊥ ∩ u₁^⊥` at radius `w`; check whether the LP dual
> feasible point gives `S ≤ |Ball|` (`C + ⟨u₁⟩` is ε*-biased at window weight). Equivalently
> place the Krawtchouk-weighted sum over `D` in a low-dim Terwilliger module and seek an
> operator-norm bound."*

The binding object is fixed precisely by the in-tree substrate (this is not a guess — it is the
exact closed form already formalized axiom-clean):

- `ShawOperatorDual.shawError_subgroup_eq`: for the linear (δ=0) base case the Shaw operator is
  `𝒮(u₀) = |H| · Σ_{ψ ∈ C^⊥ ∩ u₁^⊥, ψ ≠ 0} ψ(u₀)` — i.e. the **dual-subcode character sum**.
- The prize ball `S = ⋃ balls` replaces the indicator `[ψ ∈ C^⊥]` by the **Krawtchouk
  ball-Fourier weight** `g(wt ψ) = Σ_{k≤w} K_k(wt ψ)` (`ShellFourierKrawtchouk.shell_fourier`:
  `Σ_{wt e = k} ψ(e) = K_k(charWeight ψ)`).

So the genuine object of route 104 is

```
  S_ball(u₀) = Σ_{ψ ∈ D, ψ ≠ 0}  g(wt ψ) · e_p(ψ·u₀),     D = C^⊥ ∩ u₁^⊥,
```

and the prize target ("ε*-biased at window weight") is

```
  (TARGET)   max_{u₀} | S_ball(u₀) |  ≤  |Ball_w|.            (#)
```

`D` is a *linear* code (dim `n−k−1` over `F_q`), so the Delsarte LP is well-posed: variables are
the weight distribution `(A₀=1, A₁, …, A_n)` of `D`; constraints are `A_i ≥ 0`,
`Σ A_i = |D| = q^{n−k−1}`, and the MacWilliams dual-nonnegativity
`A'_j := |D|^{-1} Σ_i A_i K_j(i) ≥ 0`. A *dual feasible point* of this LP is exactly an
ε-biased / Terwilliger operator-norm certificate.

## 2. The structural obstruction (the no-go)

**Claim.** No LP over the weight distribution of `D` — equivalently no ε-biased / Terwilliger
operator-norm certificate built from `D`'s distance distribution — can certify (#) for any
nontrivial radius `w`. The strongest bound any such certificate yields is the **triangle (`L¹`)
bound**, which is the *trivial* bound and is `√(n/log n)` too weak.

**Why.** The LP / weight-distribution data is a function of the **multiset of weights**
`{wt ψ : ψ ∈ D}` only. It is **invariant under re-phasing**: replace each `e_p(ψ·u₀)` by an
arbitrary unit `χ(ψ)` and the available data `(A_i)` is unchanged. But the target (#) is a
functional of the **phases** `e_p(ψ·u₀)`: its value at the phase-aligned point and at a generic
point differ by the entire √-cancellation the prize is about. Concretely, the only phase-blind
**upper** bound on `|S_ball(u₀)|` is

```
  |S_ball(u₀)| ≤ Σ_{ψ ≠ 0} |g(wt ψ)| = Σ_{i≥1} A_i |g(i)|        (the L¹ / triangle bound),
```

and *any* LP that maximizes a phase-blind linear functional of `(A_i)` returns (at best) this
`L¹` value — it can never return the worst-case-`u₀` value `max_{u₀}|S_ball(u₀)|`, which lies
strictly below it. The LP therefore proves `max|S_ball| ≤ L¹`, never `max|S_ball| ≤ |Ball_w|`.

This is the same wall, viewed from the LP side, as `ShawFlatnessRefuted` / the
worst-vs-average gap isolated by `ShawSecondMoment.shawError_second_moment`: the **average**
(`L²`/Parseval) is phase-blind and is computable (`= √(Parseval mass)`), but the **worst case**
(`L^∞`) is a phase statement the moment method / LP cannot reach.

## 3. Numerical confirmation — `scripts/probes/sweep_A15_delsarte_lp.py`

Two probes on prize-shaped cases (`n ∈ {8,16,32}`, `p ≈ n^β`, `β ∈ {2,3,4}`,
`ρ ∈ {1/2,1/4,1/8}`):

**(a) LP-phase-blind vs |Ball_w|.** The best phase-blind certificate
`|D|·max_i|g(i)|` exceeds the prize target `|Ball_w|` by **5 to 162 orders of magnitude** in
every case, the gap growing monotonically with `|D| = q^{n−k−1}`. (The LP optimum over the
weight distribution can do no better than concentrate mass; it never beats the total mass it must
sum.) The "S ≤ |Ball|" dual feasible point **does not exist** for any nontrivial `D`.

**(b) The `L¹ ≥ MAX ≥ L²` sandwich (the sharp reason).** For the per-frequency binding family
(the genuine prize object, principal term excluded), exact computation gives:

| quantity | value | seen by LP? | vs prize |
|---|---|---|---|
| `L² = AVG = √(Parseval mass)` | `= √n` exactly (Parseval) | **yes** (phase-blind) | too weak (below target) |
| `B = max_{b≠0}\|η_b\|` (true binding) | `≈ √(n·log(q/n))` (e.g. `4.8 … 23.0` over the cases) | **NO** | this is the prize |
| `L¹ = Σ\|g\|` (triangle bound) | `= n` | **yes** (phase-blind, the LP optimum) | too weak (above target by `√(n/log)`) |

The phase-blind LP is **sandwiched**: it computes `AVG = √n` (Parseval, phase-blind, *below* the
binding `B`) and proves `MAX ≤ L¹ = n` (triangle, phase-blind, *above* `B` by `√(n/log n)`).
The binding `B ≈ √(n log)` lives strictly between them, and the `MAX−AVG` gap **is** the
phase-alignment quantity — exactly the data the LP discards. *(Caveat recorded honestly: in the
sub-probe the full-subgroup sum attains `MAX = n` at `u₀ = 0` because all phases align trivially
at the principal term; the prize functional excludes that principal frequency, where the true
binding object is `max_{b≠0}|η_b| ≈ √(n log)` — measured separately in probe (a). The structural
conclusion is identical either way: the LP sees `{√n, n}` but not the `√(n log)` in between.)*

## 4. Does it sidestep character sums? — **No.**

The route was floated (UNFINISHED_THREADS_407 §11, routes 84/85/93/104) as one of the two
never-tried families that could give worst-case `√`-cancellation *without* BGK/GRH, on the hope
that an LP **dual certificate** replaces a character-sum estimate. The analysis shows the hope is
misplaced **as a matter of what the LP can express**, not difficulty:

- The Delsarte LP is the canonical relaxation for bounding `Σ_{c∈D} f(c)` for a **weight-only**
  `f`. The prize functional is `max_{u₀} |Σ_{ψ∈D} g(wt ψ) e_p(ψ·u₀)|`, which is **not**
  weight-only — it is the `L^∞` norm of the dual code's *characters*, i.e. a character sum.
- Placing the Krawtchouk-weighted sum in a **Terwilliger module** does not help: the Terwilliger
  algebra is generated by the distance/weight structure of the **single** code `D`; its
  operator-norm bounds again bound weight-functionals (the `A'_j ≥ 0` constraints), not the
  `L^∞`-over-translates of the dual characters. The translate index `u₀` is precisely the data
  *outside* the Terwilliger algebra of `D`.

**Conclusion.** The LP / ε-biased / Terwilliger certificate **reduces to** the character sum it
was meant to avoid: certifying (#) is *equivalent* to bounding `B = max_{b≠0}|η_b|`, which is the
open Gauss-period / generalized-Paley eigenvalue wall (faces 3↔4 of the open core,
`GeneralizedPaleyRamanujan.lean` / `GaussPeriodMomentBound.lean`). Route 104 does not move the
window.

## 5. What survives / what is honestly left

- **Refuted as a route:** "LP dual feasible point gives `S ≤ |Ball|`" and "Terwilliger
  operator-norm sidesteps character sums." Both fail for the *structural* reason that the
  certificate is phase-blind while the target is a phase (`L^∞`) statement.
- **Not refuted, but reframed:** an LP that is *fed extra phase data* (e.g. a 3-point /
  triple-correlation Delsarte LP on the **product set** `μ_n × μ_n × μ_n`, à la higher-order
  Delsarte / Bachoc–Vallentin) is no longer phase-blind and is **not** what route 104 specifies;
  it coincides with the moment / additive-energy route (`GaussPeriodMomentBound.lean`), which has
  its own (proven, separate) deep-moment wall. So the only way to make an LP see the prize is to
  promote it to the moment hierarchy — and then it inherits the moment wall, gaining nothing.
- **Open core unchanged:** `B(μ_n) ≤ C√(n log(q/n))` (the B-form), equivalently
  `ShawFlatness` / `WorstCaseIncompleteSumBound`. No phase-blind convex certificate reaches it.

## 6. One-line takeaway

The Delsarte/ε-biased/Terwilliger LP optimizes over the **weight distribution** of the dual
subcode; the prize is the **`L^∞`-over-translates phase-cancellation** of that subcode's
characters. Phase-blind ⇒ the LP gives the `L¹` triangle bound (`= n`), never the binding
`√(n log)`. Route 104 collapses onto the character-sum / moment wall it was meant to avoid.
**OPEN — structural no-go for the route, prize core untouched, no closure claimed.**

### Cross-refs
- substrate: `ShawOperatorDual.shawError_subgroup_eq`, `ShellFourierKrawtchouk.shell_fourier`,
  `ShawSecondMoment.shawError_second_moment` (the phase-blind `L²` average), `KrawtchoukPoly.lean`.
- walls: `ShawFlatnessRefuted` (worst-vs-average), open core faces 3↔4 (CLAUDE.md §3.5).
- adjacent: A14 (Katz sheaf-trace, the *other* never-tried `√`-cancellation family — also bounds
  `sup_{u₀}|𝒮|` by an algebraic conductor rather than an LP; not phase-blind, but needs the sheaf
  identified).
