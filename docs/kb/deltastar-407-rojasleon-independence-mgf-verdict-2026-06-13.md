# δ* (#407) — verdict on the Rojas-León-independence → MGF-factorization route

**Date:** 2026-06-13. **Author:** δ* lane (#407), route assault: `rojasleon` (Gauss-sum
independence → moment-generating-function factorization → sub-Gaussian sup-norm).
**Honesty:** the core (DGPH `B ≤ C₀√(n·log(p/n))`) remains a recognized OPEN problem. This route
does NOT close it. Verdict = a precise localization + a refuted spoiler hypothesis, with four
reproducible probes and the actual Rojas-León paper (2207.12439) read in full. No closure claimed.

## The object and the route's bet

`η_b = Σ_{x∈μ_n} e_p(bx)`, `B = max_{b≠0}|η_b|`. Via the proven DFT identity the period sequence is
the inverse DFT of the Gauss-sum sequence `τ(ψ^j) = G(ψ^j)`, `j=1..m−1`, `|τ|=√p`. Writing the
unimodular phases `a_j = τ(ψ^j)/√p`, the prize ⟺ the trig-polynomial sup-norm
`‖P‖_∞ = max_c|Σ_{j=1}^{m−1} a_j e(−jc/m)| ≤ C√(m·log m)`.

**The bet:** the only relations among `{τ(ψ^j)}` are conjugation/Galois/Hasse–Davenport
(Rojas-León 2207.12439). If the `a_j` were *jointly independent* unimodular, the MGF of `P(c)`
would FACTOR over `j`, giving a sub-Gaussian proxy `m` and `‖P‖_∞ ≤ √(2m log m)` by Chernoff +
union over the `m` roots. **The route asks: how much of the prize survives the *actual*
(relation-constrained) independence, and does Hasse–Davenport spoil flatness?**

## What Rojas-León 2207.12439 actually proves (read in full)

- **Thm 1 / Cor 2 (qualitative).** For a **FIXED** number `n` of monomials `χ^{d_i}` (here
  `d_i` = the powers `j`) with the `v_i` linearly independent, the normalized Gauss sums
  `q^{−m/2}G_m(χ^{d_i})` become **jointly equidistributed on `(S¹)ⁿ`** with respect to Haar — i.e.
  asymptotically independent unimodular — **as the field `k_m` grows (`m→∞`)**. Katz [Kat88 Thm 9.5]
  is the `r=1` case.
- **Thm 3 (the relations).** Any monomial relation among Gauss sums holding for *almost all*
  characters is a combination of: conjugation `G(χ)G(χ̄)=χ(−1)q`, Galois `G(χ^p)=G(χ)`, and the
  **Hasse–Davenport product** `∏_{ε^d=1}G(χε) = χ(d)^{−d}G(χ^d)·(HD const)`.
- **Thm 4 (effective).** The ONLY quantitative statement. Per fixed Weyl-test frequency `c` with
  `‖c‖₁ = L1-norm`, the equidistribution discrepancy is
  `|S_m|^{−1}|Σ_{χ∈S_m}Λ_c(Φ_m(χ))| ≤ [C·N^{‖c‖−1}A^{‖c‖}(q−1)^r q^{−1/2} + nA(q−1)^{r−1}] /
  [(q−1)^{r−1}(q−1−nA)] ≈ C·N^{‖c‖}A^{‖c‖}·q^{−1/2}`,
  where `A = maxᵢ|a_ij|` (bounded exponents), `N = N(r)` the absolute Forey–Fresán–Kowalski
  complexity constant (`N≥2`). **Weil-strength `q^{−1/2}`, but with geometric blow-up `N^{‖c‖}` in
  the test frequency = the moment order.**

## The three-axis gap (quantified — `_wf407_rl_gap.py`)

RL is geometrically *exactly* the right object, but it is short on all three axes the prize needs:

| Axis | Rojas-León gives | Prize needs | Gap |
|---|---|---|---|
| **G1 #phases** | independence of a **FIXED** tuple of `n` Gauss sums | joint control of **ALL `L=m−1≈2^128`** phases at once | RL's "v_i linearly independent" is a fixed-`n` hypothesis; vacuous/unverifiable at `n=m−1` (and the HD/conjugation relations *do* bind the growing family). **Decisive.** |
| **G2 moment depth** | reliable per-frequency discrepancy only while `N^{‖c‖}<q^{1/2}`, i.e. moment depth `r_RL=(ln q)/(2 ln N)` | `r_need ≈ ln m ≈ ln q` (the MGF/sub-Gaussian sup-norm) | even at the smallest possible `N=2`, `r_RL/r_need = 1/(2 ln N) ≤ 0.72`; at `N=4` it is **0.36** — a constant-fraction shortfall set by the FFK constant `N`, exactly the same shape as the in-tree deep-moment cap `r ≤ 2 log_n p`. |
| **G3 direction** | equidistribution as **`q→∞`** (a *tower* of fields `k_m`) | a **SINGLE fixed `F_p`** | RL has **NO rate at a single `p`**; the prize is one `p≈2^160`. Same wall as Lamzouri's CLT-at-fixed-power. |

### Regime tension (which framing? — it softens G1 but NOT G2/G3)

The newest #407 comment pins `ε*=2^−128`, so the **index `m=(p−1)/n ≈ 2^128` is HELD CONSTANT**
as the FFT domain `n→∞` (positive-proportion subgroup, `β=log_n p → 1`), versus the older thin
framing `n=p^{1/β}` (`m≈p^{1−1/β}` grows). This matters for G1:

- **Thin framing** (my probes): `m−1` GROWS with `p` ⟹ G1 is the decisive blocker (RL's fixed-`n`
  theorem cannot reach a `p`-growing family).
- **Index-fixed framing** (prize spec): `m−1 ≈ 2^128` is a FIXED (huge) constant while `q=p→∞`.
  Then RL's **qualitative Thm 1 nominally APPLIES** to this fixed tuple of `2^128` Gauss sums —
  **G1 softens to "verify the linear-independence hypothesis for these `2^128` specific `v_j`,"** a
  finite (if astronomically large) condition, modulo the binding HD/conjugation relations.

**But G2 and G3 are unchanged and decisive in BOTH framings.** Even granting RL Thm 1 on the fixed
`2^128`-tuple: (G3) it is a `q→∞` statement with **no rate at the single prize `p≈2^160`**; (G2) the
*effective* Thm 4 caps reliable moment depth at `r_RL=(ln q)/(2 ln N)`, and the sup-norm union bound
over `m=2^128` frequencies needs `r≈log m=128 ln2≈89`, while `r_RL≈(160 ln2)/(2 ln2)=80` at `N=2`
(short) and `≈40` at `N=4` (far short). So in the index-fixed regime the route's gap **relocates
from G1 to G2/G3** — a per-frequency Weil discrepancy whose constant `N^{‖c‖}` blows up exactly at
the moment depth the sup-norm needs, at a single fixed field. **The wall does not move.**

**The clean statement of the effective-independence input that WOULD close it** (and how far RL is
from it): *one needs the joint MGF `E_χ[exp(λ·Re(ζ̄ Σ_{j} a_j w_j))] ≤ exp(Cmλ²/2)` uniform over the
`m−1`-character family at a single `F_p` — equivalently `E[|Σ a_j w_j|^{2r}] ≤ (Cm)^r(2r−1)‼` to
depth `r≈ln m`.* This is precisely the in-tree `GaussianEnergyBound` `E_r(μ_n) ≤ (2r−1)‼·n^r`
(`GaussPeriodMomentBound.lean`): **independent unimodular phases ⟹ Wick/Isserlis ⟹ exactly the
real-Gaussian `(2r−1)‼` moments**. So the route is a faithful probabilistic *re-encoding* of the
char-`p` energy-transfer wall, not a way around it. RL supplies this for any fixed tuple as `q→∞`;
the prize needs it for the growing family at fixed `p` — the BGK/deep-moment core, unchanged.

## Hasse–Davenport: NOT a spoiler (machine-verified, `_wf407_hd_structure.py`, `_wf407_hd_exact.py`)

The route's sharpest concrete question: is the HD relation a deterministic *alignment* that inflates
`‖P‖_∞` above the random `√(m log m)` law? **Answer: NO, on two independent grounds.**

1. **HD is a *relation*, not an *alignment*.** The HD `d=2` identity
   `τ(ψ^j)·τ(ψ^jλ) = χ(2)^{−2}τ(ψ^{2j})τ(λ)` is verified **exact to `rel_err ~1e-14`** on every
   tested dyadic prime. But it ties `a_{2j}` to a **PRODUCT** `a_j·a_{j+m/2}`, a *doubling recurrence*
   `θ_{2j}=θ_j+θ_{j+m/2}+c` (mod 2π), **not** an additive character `θ_j=αj+b`. Only an additive
   character would spike the DFT (full alignment). Measured: the top DFT-mode **share**
   `‖P‖_∞²/(m·energy) = 0.0002–0.014`, vs the pure-character value 1 and the random-flat value
   `2 ln m/m` — i.e. **maximally flat**, `‖P‖²/(energy·ln m) ≈ 1.1–1.6 ≈ 2` (the random law). A
   relation that expresses one phase as a *product* of two others **propagates flatness**.
2. **HD's doubling orbits do not concentrate energy.** Tying `a_j↔a_{2j}` builds `j↦2j` orbits;
   the largest single orbit carries only **0.10–0.75%** of `‖P‖²`, top-5 orbits **0.4–3.4%**. The
   coupling is diffuse — no low-dim subspace the sup-norm lives on.
3. **Direct spoiler test:** `‖P‖_∞(real Gauss phases)` vs phase-shuffled control = **inflation
   0.92–1.06** (`n∈{8,16,32,64}`, `β∈{3.5,4,5}`). The structured Gauss-phase sup-norm is
   statistically indistinguishable from (slightly below) the random-phase sup-norm. **HD does not
   raise the floor.**
4. **HD often doesn't even couple the period phases.** `ψ^jλ` is itself a period phase (trivial on
   `μ_n`) **iff `λ` is trivial on `μ_n` iff `v₂(p−1)>μ`** (exact, verified: `p=97,193` close;
   `p=13,29,113` exit to an outside Gauss sum). When `v₂(p−1)=μ` (a coin-flip on the prize
   diagonal), HD relates the `a_j` to OUTSIDE sums — no internal alignment at all. This is exactly
   the dyadic-tower KB's Wall 1/Wall 2 (the 2-power dual block is `O(1)` size `2^{v₂(p−1)−μ}`).

**Net on HD:** the only named relation that could plausibly spoil flatness is verified exact, but it
is the *good* kind of constraint — a multiplicative recurrence that propagates pseudorandomness,
diffuse over doubling orbits, and frequently inert. **The Gauss phases are at least as flat as random
unimodular** (`‖P‖_∞/√(2m log m) = 0.68–0.95` across all cases — *below* the union-bound ceiling).
This is the genuine (small) positive finding: HD is structurally *consistent with* flatness, not
against it.

## Empirical flatness (cross-check, `_wf407_rojasleon_mgf.py`)

`B/√(n·ln m)` measured: `0.96, 1.07, 1.09, 1.19, 1.25, 1.26, 1.35` over `(n,β)∈{(8,5),(8,4),(16,5),
(16,4),(64,4),(32,4),(64,3.5)}` — flat, no trend, reproduces the campaign's `1.1–1.5` plateau. RMS
`=√n` to `1e-4` (Parseval). `|a_j|=1` to `1e-15`.

## Precise wall statement (for the schema)

> The Rojas-León route walls because 2207.12439 proves the *correct* object (joint
> equidistribution = asymptotic independence of normalized Gauss sums, with the relations limited to
> conjugation/Galois/Hasse–Davenport, Weil-strength `q^{−1/2}` discrepancy in Thm 4) but in the
> *wrong asymptotic*: it controls a **FIXED finite tuple** of Gauss sums as **`q→∞` over a field
> tower**, with a per-frequency constant `N^{‖c‖}` that blows up geometrically in the moment order,
> capping reliable depth at `r_RL=(ln q)/(2 ln N) ≤ 0.72·log₂q`. The prize needs the **joint
> sub-Gaussian MGF of all `m−1≈2^128` phases simultaneously at a single fixed `F_p`, to moment depth
> `r≈ln m`** — which is exactly the in-tree `GaussianEnergyBound` char-`p` transfer (Wick/Isserlis:
> independent phases ⟹ `(2r−1)‼` Gaussian moments ⟹ `E_r ≤ (2r−1)‼ n^r`). RL supplies the
> probabilistic content for fixed tuples; the growing-family-at-fixed-`p` version is the BGK /
> deep-moment core, unchanged. **Hasse–Davenport is NOT a spoiler** (it is a flatness-propagating
> multiplicative recurrence, diffuse, often inert, and the measured sup-norm sits at 0.68–0.95× the
> independent union-bound ceiling).

**Made real progress toward the bound:** NO. **New ground:** (a) the exact three-axis localization of
how Rojas-León/Katz independence falls short (fixed-`n` vs growing-`m`; `N^{‖c‖}` depth cap; `q→∞` vs
fixed `p`), pinning the missing input as a single uniform joint-MGF inequality = the in-tree
`GaussianEnergyBound`; (b) the machine-verified refutation of the Hasse–Davenport spoiler hypothesis
with its exact mechanism (product-not-character recurrence; `v₂(p−1)>μ` coupling condition; diffuse
doubling orbits; inflation ≈ 1). Honest scores: novelty 7 / insight 8 / proximity 2 / feasibility 3.

## Reproduce
- `scripts/probes/_wf407_rojasleon_mgf.py` — flatness `B/√(n ln m)`, `‖P‖_∞` vs `√(2m log m)`, HD inflation.
- `scripts/probes/_wf407_hd_structure.py` — HD relation-vs-alignment: top-mode share, doubling-orbit mass.
- `scripts/probes/_wf407_hd_exact.py` — EXACT HD `d=2` identity (`rel_err~1e-14`) + `v₂(p−1)>μ` coupling.
- `scripts/probes/_wf407_rl_gap.py` — the three-axis Rojas-León-vs-prize gap table (G1/G2/G3).
- Paper text: `scripts/probes/_wf407_rojas.txt` (extracted 2207.12439).
- Cross-refs: `deltastar-salem-zygmund-gausssum-chaining`, `deltastar-407-dyadic-2adic-gauss-tower-verdict`,
  `CharSumMomentDeepWall.lean`, `GaussPeriodMomentBound.lean`, `GaussPeriodCosetReduction.lean`.
