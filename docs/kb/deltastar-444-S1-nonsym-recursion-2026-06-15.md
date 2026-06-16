# #444 CRACK D / S1 — the NON-symmetric squaring-tower recursion (singleton-fiber decomposition)

**Date:** 2026-06-15. **Lane:** S1 (the one live combinatorial lead after the §6 shred of the
novel-directions paper). **Verdict:** PARTIAL — I derive the exact fiber-decomposition identity,
prove (axiom-clean) that the non-symmetric defect (singleton fibers) does NOT obstruct
codeword-uniqueness, and characterise the singleton set as `μ_{n/2} ∩ {P² = X·Q²}`. **The headline
empirical claim is window-dependent and I correct it honestly:** at the window MIDPOINT (`η ≈ ρ`)
`s(S) ≤ 2` and flat in `n`, but at the window EDGE (`η` small) the list and `s(S)` BOTH inflate —
the worst word becomes non-consecutive (`x^15+x^4` at n=16, list 273, `s(S)` up to 5), and `s(S)`
is bounded only by `deg R ≤ n−1`, NOT `O(1)`. So **the `κ = O(1)` floor hypothesis (N10) is REFUTED
at the window edge**; it holds only at the midpoint and is word-specific, not structural. The
recursion exists and per-pattern uniqueness is proven; the open core relocates to the pattern count,
unchanged. **No closure claimed.**

## 0. TL;DR

- The non-symmetric recursion **exists and is already largely formalized in-tree** — it is the
  converse-FRI even/odd descent of `DescentKernelLemma.lean` (O13/O14/O35). I did NOT need to invent
  it; I needed to (a) recognise it solves CRACK D's "coupling" and (b) state the singleton bound it
  implies.
- **Fiber-decomposition identity (proven):** writing the squaring map `σ: x↦x²` with fibers
  `{x,−x}` over `z=x²∈μ_{n/2}`, the agreement set `S` of a codeword `g` splits into *double* fibers
  `B` (both `±x` agree, weight 2), *singleton* fibers `O₁` (exactly one agrees, weight 1), and empty
  fibers, with the **budget identity**
  `agreement a = 2·|B| + |O₁|`. The singleton count `s(S) := |O₁|` is the non-symmetric defect;
  `s(S)=0 ⟺ S=−S` (the symmetric, tower-captured case).
- **The crux (proven):** the singleton count does NOT obstruct uniqueness. A codeword is pinned by
  its *pattern* `(B,O₁,σ)` whenever the *weighted* budget `2|B|+|O₁| ≥ k` — **for ANY `|O₁|`**. So
  the worst-case list equals `#{consistent patterns}`, and the singletons merely re-weight the
  agreement budget (1 instead of 2). The "cross-parity constant κ" is NOT a uniqueness obstruction;
  it is the per-`n` count of singleton-bearing patterns.
- **Empirics (exact, multi-prime):** WINDOW-DEPENDENT. At the window MIDPOINT (`η ≈ ρ`), the
  worst word is consecutive `x^a+x^{a−1}` and `s(S) ≤ 1` (flat across n=8,16,32) — the N10 floor
  signal. But at the window EDGE (`η` small, agreement threshold lower), the worst word is
  non-consecutive (`x^15+x^4`, list 273 at n=16) and `s(S)` reaches 5, bounded only by `deg R ≤
  n−1`. So `κ=O(1)` is a midpoint artifact, REFUTED at the edge. The singleton set is `μ_{n/2} ∩
  {P² = X·Q²}` (a curve of degree ≤ n−1), so `s(S)` is genuinely `O(n)`-allowed, not `O(1)`.

## 1. Setup — the squaring map and the fiber decomposition

`μ_n = ⟨ω⟩ ⊆ F_p^*`, `n=2^μ`, `−1 = ω^{n/2} ∈ μ_n`. Squaring `σ: μ_n → μ_{n/2}=:D₁`, `x↦x²`, is
2-to-1 with fibers `{x,−x}`. Pick a square root `y(z)` of each `z∈D₁` (fiber `= {y z, −y z}`).

For a degree-`<k` codeword `g`, the **even/odd split** (`DescentKernel.glue`, characteristic-free):
`g(x) = e(x²) + x·f(x²)`, with `deg e < ⌈k/2⌉ =: κ`, `deg f < ⌊k/2⌋`. On a fiber over `z`:
```
g(y z)  = e(z) + (y z)·f(z)
g(−y z) = e(z) − (y z)·f(z)
```
— a 2×2 linear system in `(e(z), f(z))`. Per fiber:
- **double** `z∈B`: both equations hold (`g(±y z)=w(±y z)`) → 2 agreements, **2 constraints** on
  `(e(z),f(z))` ⇒ `(e(z),f(z))` is fully determined at `z` (the system is invertible since `y z ≠
  −y z`). This is the symmetric, squaring-tower-captured fiber.
- **singleton** `z∈O₁`: exactly one side agrees, at `σ(z)∈{y z,−y z}` → 1 agreement, **1 twisted
  affine constraint** `e(z) + σ(z)·f(z) = w(σ(z))`. This is the NON-symmetric defect.
- **empty**: 0.

**Budget identity (PROVEN, `DescentKernel.agreement_count`):**
`a = #{x∈μ_n : g(x)=w(x)} = 2·|B| + |O₁|`. The symmetric fibers carry weight 2, the non-symmetric
singletons carry weight 1. `s(S) := |O₁|`.

## 2. The coupling of g_even, g_odd on singleton fibers (task #2)

The task asked exactly how singletons couple `e=g_even` and `f=g_odd`. The answer is in the per-fiber
system above:
- a **double** fiber gives the *full* 2×2 invertible system → both `e(z)` and `f(z)` pinned (2 d.o.f.
  consumed). This is the squaring recursion: knowing the codeword on the symmetric fiber is
  equivalent to one constraint each on the half-degree `e`, `f` at the level-1 point `z`.
- a **singleton** fiber gives ONE twisted line `e(z) = w(σ z) − σ(z) f(z)` (1 d.o.f. consumed; it
  ties `e(z)` to `f(z)` linearly with slope `−σ(z)`). The two roots `±σ(z)` give DIFFERENT slopes,
  so the singleton's *side choice* `σ` is genuine pattern data (not redundant).

So the "cross-parity coupling" is precisely: **doubles consume 2 of the `2κ = k` degrees of freedom
of `(e,f)`; singletons consume 1 each.** The whole agreement budget is `2|B|+|O₁|`, and once it
reaches `2κ` the pair `(e,f)` — hence `g` — is over-determined and unique. There is no "absolute
constant κ" governing a *correction*; the correct object is the budget split.

## 3. The non-symmetric rigidity (the key theorem — PROVEN, axiom-clean)

The naive worry (paper's framing): a large `s(S)` "escapes the tower" and inflates the list, so the
floor only holds if `s(S)=O(1)`. **This framing is wrong.** The correct statement:

> **Singleton-stratum uniqueness** (`_S2NonSymTower.singleton_stratum_unique`, axiom-clean
> `[propext, Classical.choice, Quot.sound]`). Two degree-`<k` codewords realizing the SAME pattern
> `(B, O₁, σ)` with weighted budget `2|B| + |O₁| ≥ k` are EQUAL — **for any `|O₁| = s(S)`**.

Mechanism (Lemma K / `kernel_rigidity`): the glued difference `Δ(d) = (e₁−e₂)(d²) + d·(f₁−f₂)(d²)`
has degree `< k` but vanishes at the `2|B|+|O₁| ≥ k` distinct roots harvested at BOTH `±y z` for
`z∈B` (2 each) and at `σ z` for `z∈O₁` (1 each). So `Δ=0`, hence `e₁=e₂, f₁=f₂`, by even/odd
coefficient disjointness. The `d²=z` parametrization supplies unconditional rigidity — the smoothness
substitute for genericity. **Singletons supply exactly one root each; they never weaken uniqueness.**

**Consequence:** the worst-case list is `L*(n) = #{consistent patterns (B,O₁,σ) : 2|B|+|O₁| ≥ k}`.
The symmetric tower is the `O₁=∅` stratum; the non-symmetric part is the `O₁≠∅` strata. This is the
exact non-symmetric recursion (it is NOT "symmetric-tower × κ"; it is a sum over the budget split).

## 4. Is s(S) O(1)? — the singleton curve, and the WINDOW-EDGE refutation (task #3, #4)

**The structural characterization (PROVEN).** For a polynomial word `w` with even/odd parts
`(w_e, w_o)`, set `P = e − w_e`, `Q = f − w_o`. A singleton fiber over `z = x²` needs `g(x)=w(x)` but
`g(−x)≠w(−x)`; the agreeing-side equation `P(z) + σ(z)·Q(z) = 0` (with `σ(z)²=z`) squares to
`P(z)² = z·Q(z)²`. So
> **`s(S) = |O₁| = #( μ_{n/2} ∩ {z : R(z)=0} )`, where `R(X) := P² − X·Q²`** (`singleton_mem_curve`),
and `R ≡ 0 ⟺ P=Q=0` (the symmetric stratum, `singleton_curve_parity`). Hence
**`s(S) ≤ deg R`** (`singletonCount_le_curve_degree`). The DEGREE of `R` is the crux:
- homogeneous (two codewords, `deg P,Q < κ`): `deg R ≤ 2κ−1 = k−1` — used for rigidity, §3;
- inhomogeneous (codeword vs word): `deg w_e, w_o ≤ (n−2)/2`, so `deg R ≤ n−1` — only the trivial
  bound `s(S) ≤ n−1`. **No `O(1)` is implied.**

**Empirical — WINDOW-DEPENDENT (this is the honest finding; corrects N10).**

| regime | worst word | list L | s(S) | bound `deg R` |
|---|---|---|---|---|
| window MIDPOINT `η≈ρ` (n=8,16,32, ρ∈{1/4,1/8,1/16}) | consecutive `x^a+x^{a−1}` | 2–8 | **≤ 1** flat in n | ≤ 4 |
| window EDGE `η` small (n=16, k=4) | NON-consec `x^15+x^4` | **273** | **up to 5** | **15** |

At the window midpoint the worst word is consecutive and `s(S) ≤ 1` flat across three doublings
(probes `probe_444_singleton_fiber_scaling.py`, `_max_singleton_allwords.py`,
`_consec_singleton_scaling.py`). **But at the window edge** (probe `probe_444_refuter_D_singlefiber.py`,
JOB 1) the worst word is no longer consecutive, the list explodes to 273, and `s(S)` reaches 5 with
`deg R = 15`. So:

> **N10's `κ = O(1)` floor hypothesis is REFUTED at the window edge.** `s(S)` is `O(1)` only at the
> window midpoint and only for the consecutive word — a word- and window-specific accident, NOT a
> structural bound. The structural bound is `s(S) ≤ deg R ≤ n−1`, i.e. genuinely `O(n)`.

The earlier "structural argument that `s(S)=O(1)`" (a low-degree `(1±x)`-defect locus) is FALSE in
general: it holds only when `w` itself is low-degree (small `a`), i.e. the consecutive-word midpoint
regime. The prize window interior is `(1−√ρ, 1−ρ−Θ(1/log n))` — the EDGE side, where `s(S)` inflates.

**Two independent reasons the singleton route does NOT floor the list (the honest core).**
(a) `s(S)` itself is NOT `O(1)` — it is `O(deg R) = O(n)` at the window edge (§4 refutation).
(b) Even if `s(S)` WERE bounded, that would not yield "list constant in `n`": by §3 the list is
`#{consistent patterns}`, and a bounded *per-codeword* singleton count bounds neither the number of
double-fiber configs `B` (any large subset of `D₁`) nor the number of distinct patterns. The floor
needs the *pattern count* bounded — the subset-sum/cyclotomic-rarity count of `DISPROOF_LOG`
O14′/Conjecture D, the SAME open question as the symmetric tower's base case
(`SubsetSumSquaringBijection`: "descends but does not terminate").

## 5. The precise obstruction (where it stalls)

1. **Recursion exists** (proven): `L*(n) = #{patterns (B,O₁,σ): 2|B|+|O₁|≥k}`, each pattern pins a
   unique codeword (`singleton_stratum_unique`). The non-symmetric defect is fully accounted by `O₁`.
2. **Singleton count is NOT `O(1)`** at the prize-relevant window edge: `s(S) = #(μ_{n/2} ∩ {P²=X·Q²})
   ≤ deg R ≤ n−1`, and the edge worst word realizes `s(S)` up to 5 (n=16) with `deg R = 15`. The
   `O(1)` is a midpoint/consecutive-word artifact. So N10's `κ=O(1)` is **refuted as stated**.
3. **The real wall is the PATTERN COUNT, not the singleton count.** `#{consistent patterns}` is the
   beyond-Johnson smooth-domain RS list count (DISPROOF_LOG O15: ⟺ the GS99 open problem). Bounding
   `s(S)` would not bound `#patterns` anyway: a single codeword with `s(S)=1` already ranges over all
   `B ⊆ D₁` with `|B| ≥ (k−1)/2`. The non-symmetric recursion *descends to the same open
   subset-sum/consistency-rarity count* as the symmetric tower.

**Net relocation:** CRACK D's "no recursion exists for the non-symmetric word" is FALSE — the
recursion exists (O13/O14/O35 + this file's singleton framing) and per-pattern uniqueness is proven.
But the hoped-for floor mechanism (N10 `κ=O(1)`) is REFUTED at the window edge, and the genuine open
residual is unchanged: the consistency-rarity / pattern count = beyond-Johnson smooth-domain RS list
decoding. The singleton-fiber analysis converts the vague "cross-parity constant κ" into a precise,
machine-checked structure (`s(S) = μ_{n/2} ∩ {P²=X·Q²}`, singletons re-weight budget but never
obstruct uniqueness) AND a sharp negative (it is `O(n)`, not `O(1)`). It does not break the wall.

## 6. Deliverable

- **Lean (axiom-clean, `[propext, Classical.choice, Quot.sound]`, 0 sorry):**
  `Frontier/_S2NonSymTower.lean` —
  `agreement_eq_two_double_plus_singleton` (budget identity `a=2|B|+s(S)`),
  `singletonSet_eq_empty_of_symmetric` / `singletonCount_eq_zero_of_symmetric` (`s(S)=0 ⟺` sym),
  `singleton_stratum_unique` (the non-symmetric rigidity — singletons don't obstruct uniqueness),
  `singleton_curve_parity` (`P²−X·Q²=0 ⟺ P=Q=0`), `singleton_mem_curve` (singletons lie on the
  curve), `singletonCount_le_curve_degree` (`s(S) ≤ deg R`; `≤ 2κ−1` only in the homogeneous case).
  Built on the proven `DescentKernelLemma` engine.
- **Probes:** `probe_444_singleton_fiber_scaling.py`, `probe_444_max_singleton_allwords.py`,
  `probe_444_consec_singleton_scaling.py` (midpoint, `s(S)≤1`); the prior
  `probe_444_refuter_D_singlefiber.py` (window edge, `s(S)=5`, the refutation).

## 7. Honest contract

No closure claimed. The recursion is real and the per-pattern uniqueness is proven; the singleton
bound is empirical (not proven for all `2^μ`); and even a proven singleton bound would not close the
prize because the binding quantity is the pattern count, which is the known open core. This is a
sharpening and relocation of CRACK D, not a resolution.
