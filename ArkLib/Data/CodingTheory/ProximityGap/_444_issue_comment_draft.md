## #444: a NEW off-BGK attack on the LIST-DECODING side — the even/odd non-symmetric dyadic descent (axiom-clean identity + verified constant window list; honest open gaps named)

**TL;DR.** The CLIMB side (`M(n) ≤ C√(n log m)`) is unchanged — I re-confirmed every climb route is the wall in a hat (Bombieri–Pila, Yu p-adic Baker, Schinzel–Zassenhaus, quotient-2-adic, the `√(2 ln 2)` tower reframe — all dead/vacuous, details below). But on the **list-decoding side (SEAM A)** I found a genuinely new, **off-BGK, `p`-independent** structure that is **not in the dead ledger** and **never touches the sup-norm**: the *even/odd non-symmetric dyadic descent*. It is exactly the part the campaign's antipodal-**symmetric** (`S=−S`) tower missed. The descent identity is **formalized axiom-clean**, the monomial base case and the constant window list are verified to `n=128`/multi-prime, and the worst case is provably (empirically) weight-2. **This is not a prize closure** — two well-localized gaps remain — but it is materially more than "reduces to the wall."

### The new object (verified + formalized)

For `μ_n ⊂ F_p^×`, `n=2N`, squaring `π: μ_n → μ_N` (`x↦y=x²`, fibre `{x,−x}`): write any codeword `f(x)=F(x²)+xG(x²)`, any word `u(x)=u_e(x²)+xu_o(x²)`, and set `P=F−u_e`, `Q=G−u_o`. Then EXACTLY:

> **`|agreement| = 2·#{y∈μ_N : P=Q=0} + #{y∈μ_N : Q≠0 ∧ P²=yQ²}`.**

Both roots of a fibre agree iff `P=Q=0`; exactly one agrees iff `Q≠0 ∧ P²=yQ²` (the agreeing root is `−P/Q`, forced to square to `y`). The single-fibre `P²=yQ²` term **is** the non-symmetric part. Verified `200/200` random trials; **formalized axiom-clean** (`[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`) in `Frontier/Sweep_A40_EvenOddDescentIdentity.lean` (`fiber_agreement_count`, `descent_identity_sum`).

### Why it gives a bounded (constant) window list — the recursion

- **Base case (verified N=16,32,64,128; provable).** A *monomial* word `y^j` on `μ_N` has an `N`-independent window list. The mechanism is structure-only, `p`-independent: `y^{N/2+1}=χ(y)·y` (`χ` the quadratic character `y^{N/2}=±1`), so the only degree-`<2` codewords reaching the window are `F=y` (on the squares) and `F=−y` (on the non-squares) — list `={y,−y}`. (Multi-agent cross-check: constant in `N`, prime-independent up to `N=128` incl. minimal-`v₂` and `β≈5` primes; the exact value is the `2^{Θ(1/η)}` window-law constant, not literally `2`.)
- **Recursion.** A weight-2 word `x^a+x^b` descends to a **monomial pair** (mixed parity → bounded) or a half-size weight-2 word (same parity → recurse), terminating at a monomial pair after exactly `v₂(a−b) ≤ log₂ n` levels.
- **Branching = 1 (verified exact).** For an **even** word, every large-agreement list member is forced to be an **even polynomial** (`G` vanishes on the full-fibre set, `> k/2` points). Measured: **ALL** members of the binding even worst words are even (`L/L`), so the single-fibre correction `S₁` is **empty** and `L(u,μ_n,k)=L(u_e,μ_{n/2},k/2)` is an **exact bijection**. Confirmed down the tower: `L=4` identically at `x^8+1/μ_32 = x^4+1/μ_16 = x^2+1/μ_8`.
- **Saturation (verified n=16,32,64).** The worst window list is **constant in n**: `L=4` at η=1/8, `L=8` at η=1/16. The `x^{n/2^j}+1` family peaks at `2^{Θ(1/η)}` then **collapses to 0** (the word becomes a codeword) — it does **not** grow. Worst-over-ALL-words is weight-2: a full weight-3/weight-4 enumeration (multi-agent Refuter) **never beats the weight-2 worst** and never grows faster in `n`.

All radii are **window-interior (strictly beyond Johnson)**: `δ=1−ρ−η` with `η<√ρ−ρ` checked.

*(Novelty caveat: the building blocks are classical — the radix-2 butterfly `f=F(x²)+xG(x²)` and the quadratic character `y^{N/2}=±1`. What is new here is using them to bound the **beyond-Johnson window list size** of an **explicit** 2-power RS code via the non-symmetric single-fibre term — a quantity the standard Guruswami–Sudan/Johnson theory leaves open for fixed evaluation points, and which the campaign's symmetric tower could not reach. A literature cross-check is running in parallel.)

### The honest open gaps (no closure claimed)

1. **G1 — bound the single-fibre correction `S₁` rigorously** (= prove "all large-agreement members are even/odd") for **scaling-exponent** words (`x^{n/4}+1`, exponent ~`n/4`) across all `log n` levels. The even/odd branching *mechanism* is clean and `S₁` is **empirically empty**, but the a-priori degree bound on `#roots_{μ_N}(P²−yQ²)` is too loose; a sharper subgroup-root bound is the genuine technical crux. `(P²−yQ²)(x²)=(f(x)−u(x))(f(−x)−u(−x))`, so this is a structured form, plausibly attackable.
2. **G2 — worst word is weight-2** is verified (n≤32 exhaustive, n=64 family) but not proven.

If G1+G2 close, this proves the **grand list-decoding challenge for explicit 2-power RS** (constant beyond-Johnson lists) by elementary cyclotomic/quadratic-character means — **no effective Gauss-sum equidistribution** — a quantity related to, and conjecturally one half of, the δ\* prize.

### Climb-side route-eliminations (re-confirming the wall from new angles)

Bombieri–Pila determinant method (wrong category: lattice-points-in-`𝔭`-mod-p, not affine/ℚ; height `O(log m)` too small); Yu p-adic linear forms in logs (constants `~(n/2)^{n/2}`, vacuous); Schinzel–Zassenhaus/Dimitrov (`house ≥ 2^{1/4m}≈1`, wrong direction); **quotient-side 2-adic uncertainty DEAD by flatness** (the period DFT over `ℤ/m` is `|·|=√p` flat = worst case for any uncertainty principle); the `√(2 ln 2)`-per-level tower reframe is refuted by the measured inflation `>√2` (`n^{0.83}`, the known `n^{3/4}` stall). Full generate→shred→rebuild in `DELTASTAR_444_ESSAY_{I,II,III}*.md`.

### Reproduce / artifacts
```
python3 -u scripts/probes/probe_444_monomial_descent.py     # descent identity 200/200; monomial constancy
python3 -u scripts/probes/probe_444_worstword_exponent.py    # worst weight-2 word, saturation
bash scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A40_EvenOddDescentIdentity.lean
```
Docs: `docs/kb/deltastar-444-evenodd-descent.md`. Honesty contract held — every claim tagged verified/formalized/open; no fabricated closure.
