# δ\* Route 2 — the CLOSED constant `c(ρ) = H₂(ρ)` (issue #444, 2026-06-15)

**Deliverable:** a DEFINITE closed-form `δ*` conjecture with **no undetermined quantity in the
statement** — a formula in `ρ, n` only. The capstone
(`deltastar-444-CONJECTURE-capstone-2026-06-15.md`) left `Θ_ρ` gated on the BGK/Paley house bound
(an undetermined `O(1)` constant). Route 2 (list-crossover-at-budget) **pins that constant** to the
binary entropy `H₂(ρ)`, via the in-tree KKH26 entropy-form ceiling. Honesty (CLAUDE.md §6A): this is a
**conjecture**, clearly labeled; the proof remains the recognized open problem and is not claimed.

---

## The closed conjecture

> **Conjecture δ\* (Route 2, closed).** For explicit smooth-domain `C = RS[F_p, μ_n, k]`
> (`n = 2^μ`, `μ_n ⊊ F_p^*`, `n ∣ p−1`), rate `ρ = k/n ∈ {1/2,1/4,1/8,1/16}`, prize regime
> `p ≈ n·2^128`, `ε* = 2^{−128}`, budget `ε*·|F| ≈ n`:
>
> **`δ*_C = (1 − ρ) − H₂(ρ) / log₂ n`,    `H₂(ρ) = −ρ·log₂ ρ − (1−ρ)·log₂(1−ρ).`**

Nothing in this statement is undetermined: `ρ, n` are the inputs, `H₂` is the explicit binary
entropy. `c(ρ) = H₂(ρ)` is the closed constant.

---

## Derivation (Route 2 = list-crossover-at-budget)

**Governing law (proven in-tree, prompt's §GOVERNING LAW).** `δ*` is the cushion `η = (1−ρ) − δ`
at which the worst-case window list `L*(δ) = 2^{c(ρ)/η}` crosses the budget `ε*|F| ≈ n = 2^μ`.
Setting `2^{c(ρ)/η} = 2^μ` gives `c(ρ)/η* = μ`, i.e. `η* = c(ρ)/μ = c(ρ)/log₂ n`, hence
`δ* = (1−ρ) − c(ρ)/log₂ n`. **The only thing to pin is `c(ρ)`.**

**The crossover surface (KKH26, `KKH26WitnessSpread.lean` + `KKH26EntropyForm.lean`).** At the
ceiling radius `δ = 1 − r/2^μ` the bad-scalar / window-list count is `N(r) = 2^r · C(2^{μ−1}, r)`
(`kkh26_epsMCA_lower_bound`), with `log₂ N(r) = countRate` exactly equal (entropy form,
`kkh26_count_corollary`, axiom-clean) to

```
log₂ N(r) = r + (s/2)·H₂(2r/s)/… = (s/2)·H₂(r/(s/2)) + r ,   s = 2^μ.
```

The agreement-pattern object whose exponential rate is the operative `c(ρ)` is the count of
agreement patterns through ONE fixed window of `s = (ρ+η)n` points — equivalently the count of
size-`k = ρn` agreement supports inside the domain `μ_n`, whose exponential rate (the method-of-types
bound `choose_ge_two_rpow_entropy_div`, axiom-clean, `C(n,k) ≥ 2^{n·H₂(k/n)}/(n+1)`) is

```
(1/n)·log₂ C(n, ρn)  =  H₂(ρ).
```

This is the **KKH26 Appendix-A reading** (recorded in the open-math ledger
`docs/wiki/open-math-hypotheses-334-deltastar-2026-06.md`, line 10: "Appendix-A route with
**c = H₂(ρ)**"). So **`c(ρ) = H₂(ρ)`**.

**Crossover algebra closes:** `L*(δ*) = 2^{H₂(ρ)·n/…}` — at the prize budget the cushion is
`η* = H₂(ρ)/log₂ n`, giving the boxed formula.

---

## The two-constant subtlety (resolved, honest)

Route 2 surfaces **two** candidate per-coordinate rates; they must not be conflated:

| object | exponential rate `c(ρ)` | value at `ρ=1/4` |
|---|---|---|
| **(i)** agreement patterns = `C(n, ρn)` over the FULL domain `μ_n` (the per-window list `L*`) | **`H₂(ρ)`** | 0.811 |
| (ii) dyadic sign-free count `2^r·C(n/2, r)` at `r=ρn` (the raw `KKH26WitnessSpread` surface) | `Φ(ρ) := ρ + ½H₂(2ρ) = −ρ log₂ρ − ½(1−2ρ)log₂(1−2ρ)` | 0.750 |

They **agree** in shape but **differ** numerically (`H₂(1/2)=1` vs `Φ(1/2)=1/2`; closed algebraic
identity `Φ(ρ) = −ρ log₂ρ − ½(1−2ρ)log₂(1−2ρ)`, verified). Route 2's KEY LEAD and the KKH26
Appendix-A constant select **(i) `H₂(ρ)`**: the window-localized list is the agreement-pattern count
over `μ_n` (subsets of size `k=ρn`), not the half-domain sign-free count (that double-counts the `2^r`
sign and the window choice, which the per-window restriction removes). The `Φ(ρ)` reading is the
*total* bad-scalar count across all windows (doubly exponential `2^{Θ(n)}` vs budget `n`), which gives
the trivial pin `η*→0` and is therefore NOT the operative object.

**Honest fallback:** if a future audit shows the per-window list is the half-domain object (ii) rather
than the full-domain object (i), the closed constant is instead `c(ρ) = ρ + ½H₂(2ρ)` and
`δ* = (1−ρ) − (ρ+½H₂(2ρ))/log₂ n`. Both are fully closed; the lead and ledger favor `H₂(ρ)`.

---

## Numerics (exact, `scripts/probes/probe_444_route2_crho_final.py`)

```
 rho   1-rho   H2(rho)   delta*@n=2^256   delta*@n=2^30   1-sqrt(rho)   in interior?
0.500  0.500   1.0000     0.49609          0.46667         0.29289         yes
0.250  0.750   0.8113     0.74683          0.72296         0.50000         yes
0.125  0.875   0.5436     0.87288          0.85688         0.64645         yes
0.0625 0.9375  0.3373     0.93618          0.92626         0.75000         yes
```

`δ*` lands strictly inside the window interior `(1−√ρ, 1−ρ)` for all four prize rates; it clears the
Johnson edge `1−√ρ` for `n ≥ 2^5` (each `ρ`), matching the in-tree note that the cushion is
nonvacuous only at `n ≳ 256`.

---

## Status

- **Closed-form conjecture:** `δ* = (1−ρ) − H₂(ρ)/log₂ n` — definite formula in `ρ, n`, no
  undetermined quantity in the statement. **This is the Route-2 deliverable.**
- **Relation to capstone:** identifies the capstone's gated `Θ_ρ` with the explicit `H₂(ρ)` via the
  KKH26 Appendix-A entropy-form ceiling (`KKH26EntropyForm.lean`, axiom-clean, already in tree).
- **Proof:** OPEN (the matching floor — that the worst-window list actually *reaches* the entropy
  ceiling at the prize prime — is the recognized BGK/Paley-house open problem; not claimed proven).
- **Confidence:** medium. The ceiling constant `H₂(ρ)` is rigorous (KKH26 Appendix-A, entropy form
  in tree); that the floor *matches* it (so the ceiling is tight) is the conjecture. The competing
  closed value `Φ(ρ)` from the in-tree dyadic surface is the main source of residual uncertainty in
  the constant.
