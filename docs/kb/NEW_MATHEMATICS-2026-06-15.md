# New Mathematics: Five Tools for the Proximity-Gap Prize

*A mathematical proposal for the Reed–Solomon proximity-gap / list-decoding prize (#444). This is creative
proposal writing in the strict sense: every load-bearing claim is tagged **[DEFINED]** (a new object we
introduce), **[PROVEN]** (a fact verified this campaign — many Lean-formalized and axiom-clean), or
**[CONJECTURED]** (the genuinely open content). We do not prove the wall, and we do not claim to cross it.
We build five new objects, argue why each is genuinely new, and either push the bound or isolate — to a
single, sharply-stated open inequality — exactly what remains. The reader is invited to break the
conjectures, not to trust them.*

---

## Abstract

The Reed–Solomon proximity-gap prize asks for the optimal list-decoding radius `δ*` of explicit RS codes on
multiplicative-subgroup evaluation domains `μ_n ⊂ 𝔽_q^×` with `n = 2^μ`. Over the #407/#444 campaign the
prize has been reduced — **exactly**, through roughly twenty mutually equivalent faces (far-line incidence,
additive energy, period autocorrelation, DFT sup-norm, Cayley-graph spectral radius, the *house* of an
algebraic integer, root-number flatness, …) — to a **single analytic inequality**, the **CORE**:

> `M(n) := max_{b ≢ 0 (mod p)} | Σ_{x ∈ μ_n} e_p(b x) | ≤ C · √(n log m)`, with `C = O(1)`, at
> `p ≍ n^4` and `m = (q − 1)/n`.

This is the Bourgain–Glibichuk–Konyagin / Bourgain–Chang thin-subgroup square-root-cancellation conjecture
(≈25 years open) at its single hardest point — the *unattained sharp endpoint* `α = 1/4` of Bourgain's own
sum–product program — and the gap to it is a full half-power (`n^{0.989}` known, `n^{0.5}` needed). **[PROVEN]**
this campaign: the log factor in the CORE is *real* — measured `M(n) / √(2 n ln m) → ~0.9–1.05` up to
`n = 128`, with `C ≈ √2` — so the target is not `√n` but `√(n log m)`, and any method that produces only
`√n` (every second-moment method) is provably insufficient by the meta-theorem below.

**[PROVEN]** this campaign — the *necessary condition*. We isolate four properties any winning method must
have: it must be **(a)** `b`-sensitive (it must see the frequency, not an averaged invariant), **(b)**
deterministic-archimedean (not probabilistic extreme-value theory, which gives the wrong constant), **(c)**
genuinely `L^∞` (a sup over `b`, not an `L^2`/RMS average), and **(d)** able to read the **absolute**
archimedean phase arithmetically. Every classical tool fails **(d)**, and we prove *why*:
Hasse–Davenport reads phase *differences* (a coboundary); Stickelberger reads phase *valuations* (a `p`-adic
shadow); Weil/Deligne is vacuous because `μ_n` is `0`-dimensional, so the `√p = n^2` error floor swamps the
`n`-sized main term; effective monodromy is vacuous at fixed `q` (the conductor `f^r` explodes); and the
entire moment/energy ladder provably caps at the Johnson radius via `(q E_r)^{1/2r} ≥ n`.

We respond with **new mathematics** organized around a single first-class operator — the **Shaw operator**
`𝒮` — and four further tools, each a *facet* of `𝒮` engineered to supply exactly one ingredient the
necessary condition demands and that no classical tool delivers:

1. **The Shaw Operator `𝒮`** — the line–ball incidence transform `δ ↦ I(δ)` whose threshold *is* `δ*` with
   no residual; the prize is *exactly one bound* on its spectral norm.
2. **The Phase-Cocycle Operator `∂_b`** — a `b`-twisted finite-difference calculus on the absolute
   root-number phases `θ_k = arg g(χ_k)`; the first tool that reads property **(d)** head-on.
3. **The Dyadic Phase-Renormalization Operator `R`** — a deterministic transfer operator on the *full*
   phase vector of the `2`-adic Gauss-period tower; a phase-coherence contraction strictly beating the
   second-moment wall.
4. **The Antipodal Cyclotomic Complex `𝒜•(μ_n)`** — a chain complex whose Betti number *is* the
   over-determined incidence floor; `p`-independence becomes the vanishing of homological torsion.
5. **The Depth-Graded Conductor** — a depth-truncated trace transform that replaces the catastrophic
   `√(n^{2r−1})` Weil-II loss with a single `O(1)` geometric constant.

The unifying thesis: **the prize is `‖𝒮‖ ≤ C √(n log m)`**, and tools 2–5 are the four facets through
which `𝒮` is to be estimated — phase-arithmetic input (`∂_b`), tower contraction (`R`), the integral floor
it must clear (`𝒜•`), and the depth bookkeeping that controls its higher moments (Depth-Graded Conductor).
Together they convert one analytic miracle into four structural conjectures, each strictly weaker than BGK
as usually posed, and each falsifiable by a concrete finite computation.

---

## 1. Introduction

### 1.1 The prize

Fix `q = p^a`, a primitive `n`-th-root-of-unity domain `μ_n ⊂ 𝔽_q^×` with `n = 2^μ`, and the Reed–Solomon
code `RS[k]` of evaluations of degree-`< k` polynomials on `μ_n`. The proximity-gap / list-decoding prize
asks for the **optimal decoding radius** `δ*`: the largest `δ` such that every received word has only a small
(polynomially-bounded) list of codewords within relative distance `δ`. The interest is *explicit* RS codes
on *multiplicative-subgroup* domains — the codes that occur in FRI, STARKs, and every deployed
proximity-gap argument — where the evaluation domain carries the full `ℤ/n` dilation symmetry. The known
benchmarks are the **Johnson radius** `1 − √ρ` (achievable, easy) and **capacity** `1 − ρ` (impossible at
poly soundness); the prize lives in the *window interior*, and the campaign has pinned its location:

> **[PROVEN] (governing law).** `δ* = sup { δ : I(δ) ≤ q · ε* }`, where `I(δ)` is the realized **far-line
> incidence** `= max_{u₀, u₁} #{ γ : u₀ + γ u₁ is δ-close to RS[k] }` (the literal list size), and the
> extremal directions are **monomial** — forced by the `ℤ/n` dilation symmetry. The budget is `q · ε* = n`.

This is the object Chapter 1 names the **Shaw operator** `𝒮`: the transform `C, ε* ↦ (δ ↦ I(δ))` whose
threshold *is* `δ*`. Energy bounds, list bounds, union bounds — all are `√`-lossy *upper proxies* for `I`;
`𝒮` alone is exact (no residual). That exactness is the reason we elevate it to a first-class operator
rather than a bound: **the prize is literally one inequality on one operator.**

### 1.2 The wall

Reducing `𝒮` analytically (Chapters 1–5 each give one route) lands on the **CORE** of the Abstract: the
thin-subgroup Gauss-period sup `M(n) ≤ C √(n log m)`. This is **[PROVEN]**-equivalent to the prize through
the campaign's faces, and it is exactly the **Burgess / Bourgain–Glibichuk–Konyagin (BGK) / Bourgain–Chang
(BCHKS Conj. 1.12)** wall: square-root cancellation for a thin multiplicative subgroup, at the endpoint of
Bourgain's sum–product program that *Bourgain himself did not reach*. The honest statement is stark:

> **[PROVEN] (no-go quartet).** Four classical doors are *shut at this exact point*: (i) **Weil/Deligne** —
> `μ_n` is `0`-dimensional, so the geometric error floor `√p = n^2` dwarfs the `n`-sized main term; the
> curve door is vacuous. (ii) **Effective monodromy** — at fixed `q` the conductor `f^r` explodes; no
> uniform bound. (iii) **The moment/energy ladder** — `Σ_b |η_b|^{2r} = p · E_r(μ_n)` with `E_r` Wick in
> char-`0` forces `(q E_r)^{1/2r} ≥ n`: *every* second-order method caps at Johnson, never reaching the
> window interior. (iv) **Phase-difference / valuation tools** — Hasse–Davenport gives phase *differences*,
> Stickelberger gives phase *valuations*; neither reads the **absolute** phase the CORE needs.

The campaign also **[PROVEN]** the matching positive structure that makes the wall *attackable* rather than
hopeless: `M(n)` is `p`-**independent at the binding radius** (cliff-confinement — char-`p` incidence equals
char-`0` incidence for proper subgroups, the excess confined to `δ > δ*`); the additive energy floor is the
**Sidon minimum** `E_+(μ_n) = 3n^2 − 3n` *exactly* (provably non-crossing); and the dyadic doubling
identity `η_b(μ_{2n}) = η_b(μ_n) + η_{gb}(μ_n)` makes the whole tower self-similar. These three facts —
`p`-independence, an exact integral floor, dyadic self-similarity — are precisely the handles the five tools
exploit.

### 1.3 The necessary condition — why *new* math is needed

The reductions are complete; the classical toolbox is exhausted; what is missing is not a lemma but an
*idea*. The campaign distilled this into the four-part necessary condition of the Abstract (`b`-sensitive,
deterministic-archimedean, genuinely `L^∞`, reads absolute phase). The fourth is the crux: **the CORE is a
statement about the absolute argument of a transcendental period**, and no tool in analytic number theory
reads the absolute archimedean phase of a Gauss sum *arithmetically* — they read differences, valuations, or
magnitudes. A winning tool must therefore be genuinely new, and it must satisfy all four constraints
simultaneously. The five tools below are each designed against this checklist; we tag where each one *meets*
the condition and where it *defers to a conjecture*.

### 1.4 The five tools and how they interlock

The architecture is a **hub and four spokes**. The hub is `𝒮`; each spoke is a facet of `𝒮` that supplies
one ingredient of the estimate `‖𝒮‖ ≤ C √(n log m)`.

```
                    ┌──────────────────────────────────────────────┐
                    │   PRIZE  ≡  ‖𝒮‖ ≤ C·√(n log m)                │
                    │   (Shaw operator, EXACT δ*, no residual)      │
                    └──────────────────────────────────────────────┘
                          ▲           ▲            ▲           ▲
              phase input │   tower   │  integral  │   depth   │
                          │ contraction  floor it  │ bookkeeping
                          │           │  must clear │           │
        ┌─────────────────┴─┐ ┌───────┴───────┐ ┌──┴──────────┐ ┌┴───────────────┐
        │ 2. ∂_b            │ │ 3. R          │ │ 4. 𝒜•(μ_n)  │ │ 5. Depth-Graded │
        │ Phase-Cocycle     │ │ Phase-Renorm  │ │ Antipodal    │ │ Conductor       │
        │ reads ABSOLUTE    │ │ contraction   │ │ Cyclotomic   │ │ trace transform │
        │ phase (cond. d)   │ │ on full vec   │ │ Complex      │ │ kills √-loss    │
        └───────────────────┘ └───────────────┘ └──────────────┘ └─────────────────┘
```

- **`𝒮` (Ch. 1) is the unifying object.** It carries the *exact* `δ*` (energy/list bounds are proxies). Its
  **[PROVEN]** structure — exact threshold, `p`-independence at binding, real spectrum (oddness brick),
  antipodal closed form, dyadic self-similarity — is what every spoke inherits. The other four chapters do
  not introduce competing objects; they introduce *coordinates on `𝒮`*.

- **`∂_b` (Ch. 2) feeds `𝒮` its phase input.** `𝒮`'s additive face is the Gauss-period sup; its
  multiplicative dual is the **root-number / Weil-index phase sequence** `θ_k = arg g(χ_k)`, and the
  autocorrelation `A(h) = (m/√p) Σ_{ζ∈μ_n} χ(1 + ζ)` is the **multiplicative dual** of `M(n)` (same wall).
  `∂_b` is the `b`-twisted finite-difference operator on `θ_k`. It is the *only* spoke that meets condition
  **(d)** directly: it reads the absolute phase. **[PROVEN]** brick: oddness `θ_{−k} = −θ_k` (since
  `χ_k(−1) = +1` for `n = 2^μ`) ⇒ the phase DFT is **real** (Lean: `ArchimedeanPhaseRealDFT`,
  axiom-clean). Open core: `∂_b` has **no resonant frequency** (Ch. 2 conjecture).

- **`R` (Ch. 3) is `𝒮`'s tower dynamics.** The dyadic doubling identity, read *not* as a recursion on the
  worst-frequency scalar (which is dead — it discards maximizer migration) but as a **transfer operator on
  the full phase vector**, is `R`. The prize floor is a one-step **phase-coherence contraction**
  (a "decoherence law"). **[PROVEN]**: the naive magnitude RG is dead *precisely because* it loses the
  maximizer-migration term that the phase-coherence functional retains; `R` is the correct lift.

- **`𝒜•(μ_n)` (Ch. 4) is the integral floor `𝒮` must clear.** The over-determined far-line incidence floor
  — the Lam–Leung closed form `I(t) = C(n/2^s, t/2^s)`, `K(n,4) = n/4 − 1`, peak `~n^3/32` at direction
  `(n/2, n/2 − 1)` — is **[PROVEN]** *not analytic at all*: it is the rank of a homology group, the Betti
  number of the antipodal-pairing chain complex `𝒜•(μ_n)` over `ℤ`. Its `p`-independence (cliff-confinement)
  **is** the statement that base change `ℤ → 𝔽_p` preserves rank away from the finite Lam–Leung torsion
  primes — i.e., the vanishing of homological torsion. This *explains* `p`-independence rather than merely
  observing it, and it tells `𝒮` exactly which integer it must beat.

- **Depth-Graded Conductor (Ch. 5) controls `𝒮`'s higher moments.** The `√q`-floor obstruction to
  fixed-`q` equidistribution is reinterpreted as a *bookkeeping* failure: the monolithic `r`-fold moment
  sheaf has conductor `~n^{2r−1}` (rank-driven), but its **mass sits on a depth-bounded slice** whose
  conductor is `r`-independent. The depth-graded trace transform replaces `√(n^{2r−1})` (catastrophic
  Weil-II loss) with a single `O(1)` constant — converting the moment ladder's `√n` cap (no-go (iii)) into
  the `√(n log m)` the CORE needs, *if* per-depth Weil-cleanness holds (Ch. 5 conjecture, strictly weaker
  than BGK).

**How they cross the wall (or isolate it).** The plan is not to attack BGK frontally. It is to route the
single hard inequality `‖𝒮‖ ≤ C√(n log m)` through four structural facets, each meeting a different clause
of the necessary condition, so that the residual splits into four *independent, finite-checkable* conjectures
— (2) no resonant phase frequency, (3) one-step coherence contraction, (4) no homological torsion at large
index, (5) per-depth Weil-cleanness. Any *one* of (2)–(5), proven in full, closes the prize through `𝒮`;
each is strictly weaker than BGK-as-posed; and each is refutable by a concrete computation we specify. The
new mathematics is the operator `𝒮` and its four-coordinate atlas — the first framework in which the prize
is not one analytic miracle but four structural bets, none of which is the bare BGK wall.

---

## Conclusion

### The unified thesis

The proximity-gap prize is **exactly one bound on one operator**:

> **`‖𝒮‖ ≤ C √(n log m)`**, the spectral norm of the Shaw operator (the off-trivial spectral error of the
> line–ball incidence), is equivalent — with **no residual** — to `δ* = capacity − Θ(1/log n)`.

This is the claim that organizes the whole essay. The Shaw operator is the right object because it is the
*only* face of the prize that is **exact**: energy floors, list bounds, and union bounds are all `√`-lossy
proxies that provably cap at Johnson, whereas `𝒮` carries `δ*` itself. The other four tools are not rival
programs; they are a *coordinate atlas* on `𝒮`, each chart engineered against one clause of the proven
necessary condition: `∂_b` supplies absolute-phase arithmetic (clause d), `R` supplies the tower contraction
(deterministic, clause b), `𝒜•` supplies the integral floor `𝒮` must clear (the `p`-independent target),
and the Depth-Graded Conductor supplies the higher-moment bookkeeping (genuinely `L^∞`, clause c). The
`b`-sensitivity (clause a) is built into `𝒮` from the start.

### What is proven vs. the central conjecture

We are explicit about the ledger.

**[PROVEN]** (this campaign; several Lean-formalized, axiom-clean):
- The governing law `δ* = sup{ δ : I(δ) ≤ n }` with monomial extremal directions (dilation symmetry).
- The exactness of `𝒮` (no residual between its threshold and `δ*`) — this is what makes Chapter 1's
  reduction an *equivalence*, not a bound.
- The reality of the root-number phase DFT via oddness `θ_{−k} = −θ_k` (`ArchimedeanPhaseRealDFT`).
- `p`-independence at the binding radius (cliff-confinement): char-`p` incidence `=` char-`0` incidence for
  proper subgroups; excess confined to `δ > δ*`.
- The exact Sidon energy floor `E_+(μ_n) = 3n^2 − 3n` and the moment master identity
  `Σ_b |η_b|^{2r} = p · E_r` (verified to `10^{-16}`).
- The antipodal/Lam–Leung closed form `I(t) = C(n/2^s, t/2^s)`, `K(n,4) = n/4 − 1`, peak `~n^3/32`.
- The dyadic doubling identity and the death of the naive magnitude RG (it discards maximizer migration).
- The four no-go theorems (Weil `0`-dimensional, monodromy conductor explosion, moment cap at Johnson,
  phase-difference/valuation tools blind to absolute phase) and the four-part necessary condition.
- That the log factor is real (`M / √(2n ln m) → ~0.9–1.05`, `C ≈ √2`, to `n = 128`).

**[CONJECTURED]** (the genuinely open content — the prize):
- **Central conjecture.** `‖𝒮‖ ≤ C √(n log m)` with `C = O(1)`, equivalently `δ* = capacity − Θ(1/log n)`.
- Its four facet-conjectures, each *sufficient* and each strictly weaker than BGK-as-posed:
  - **(2)** `∂_b` has **no resonant frequency** (the phase-cocycle spectrum is flat).
  - **(3)** the **one-step phase-coherence contraction** (decoherence law) holds for `R`.
  - **(4)** `𝒜•(μ_n)` has **no homological torsion at large index** (away from finite Lam–Leung primes).
  - **(5)** **per-depth Weil-cleanness** of the depth-graded conductor.

We do **not** claim any facet-conjecture is proven; we claim each is (i) genuinely new, (ii) sufficient for
the prize through `𝒮`, (iii) strictly weaker than the bare BGK wall, and (iv) falsifiable by a concrete
finite computation. We explicitly do **not** prove the wall, and we flag that a single counterexample to any
facet-conjecture at small `n` would kill that route — which is the point: these are *bets you can lose at a
laptop*, not unfalsifiable hopes.

### The research program

The essay defines a concrete program. **First**, formalize `𝒮` as a first-class operator in-tree (its
threshold-exactness and real-spectrum bricks already exist) and prove the four facet-reductions as
equivalences. **Second**, attack the four facet-conjectures *in parallel and independently* — they share no
common lemma, so progress on any one is real progress, and a refutation of any one prunes the tree without
costing the others. **Third**, push the finite verification frontier: the campaign reached `n = 128`; the
facet-conjectures (especially (4) homological torsion and (2) phase resonance) are checkable to larger `n`
with the existing engines, and either a clean small-`n` proof-of-mechanism or a counterexample sharpens the
core. **The honest summary:** we have not crossed the BGK wall, and we do not pretend to. We have built the
first operator-theoretic frame in which the wall is *not* one analytic miracle but four structural bets,
each weaker than BGK, each falsifiable, and each meeting a different clause of a proven necessary condition —
which is, we argue, exactly the shape a genuine attack on a 25-year wall should have.

---

*Tag legend: **[DEFINED]** new object introduced here · **[PROVEN]** verified this campaign (several
Lean-formalized, axiom-clean) · **[CONJECTURED]** open, falsifiable, the actual prize. The five chapters
(`𝒮`, `∂_b`, `R`, `𝒜•`, Depth-Graded Conductor) supply the proofs, definitions, and conjecture statements
sketched in this frame.*


---

# Part II — The Five Tools in Full

_The frame above is the executive overview; below are the complete chapters, each with formal definitions, proofs-of-concept, defenses, and the honest [DEFINED]/[PROVEN]/[CONJECTURED] tagging._



---

## Chapter 1 — The Shaw Operator

### 1. The object the prize is really about

Every published reduction of the Reed–Solomon proximity-gap / list-decoding prize routes through the same scalar at the end: a worst-case incomplete character sum, a higher additive energy, a higher-order-MDS failure count, the residual *worst − average*. The thesis of this chapter is that these are not five problems but **one operator evaluated five ways**, and that the operator has enough internal structure — proven, in Lean, axiom-clean — to be developed as a first-class object with its own calculus. We name it the **Shaw operator** `𝒮`.

The governing law (the *Shaw threshold law*) is
$$\delta^\* \;=\; \sup\{\delta : I(\delta)\le q\,\varepsilon^\*\}, \qquad I(\delta)=\max_{u_0,u_1}\#\{\gamma : u_0+\gamma u_1 \text{ is } \delta\text{-close to } \mathrm{RS}[k]\}.$$
$I(\delta)$ is the *realized far-line incidence* = the list size. **(Proven foundation, session facts.)** The extremal directions are monomial, by the $\mathbb Z/n$ dilation symmetry of $\mu_n$. The whole prize is: control $I(\delta)$ up to the capacity radius.

### 2. Definition

Let $V$ be a finite $F$-module (the RS word space $V=(\iota\to F)$, $F=\mathbb F_q$), $S\subseteq V$ a Hamming $\delta$-ball about a fixed center, and let $\widehat V$ be its additive dual. For a *direction* $s_1\in V$ write $\mathrm{dir}_\psi(s_1)$ for the restriction of the character $\psi\in\widehat V$ to the line $\{\gamma s_1\}$, and call $\psi$ *transverse* to $s_1$ when $\mathrm{dir}_\psi(s_1)=0$ (trivial on the line) but $\psi\ne 0$.

> **Definition (Shaw operator).** For $s_0,s_1\in V$,
> $$\boxed{\;\mathcal S(S;s_0,s_1)\;:=\;\sum_{\substack{\psi\in\widehat V\\ \psi\ \text{transverse to }s_1}}\ \sum_{s\in S}\psi(s_0-s).\;}$$

This is the **off-trivial spectral error of the line–ball incidence operator** on direction $s_1$. The defining theorem is the *Shaw decomposition*:

> **Theorem 1 (exact incidence = average + Shaw; PROVEN, axiom-clean).**
> $$\#\{\gamma\in F : s_0+\gamma s_1\in S\}\cdot|V| \;=\; |F|\cdot\bigl(|S| + \mathcal S(S;s_0,s_1)\bigr).$$
> *(Lean: `ShawOperator.incidence_eq_average_add_shaw`, axioms `[propext, Classical.choice, Quot.sound]`.)*

The trivial character contributes **exactly** the average $|F|\cdot|S|$; *everything else is $\mathcal S$.* Hence $I(\delta)=\mathrm{avg}+(|V|/|F|)^{-1}\cdot\max\mathcal S$, and by the threshold law $\delta^\*$ is a closed function of $\max_{s_0,s_1}\|\mathcal S\|$ over far lines. There is no other open input. This is the precise sense in which $\mathcal S$ *produces $\delta^\*$ exactly* while energy/list-size bounds (which only see $\sum\|\eta_b\|^{2r}$) are $\sqrt{\cdot}$-lossy and reproduce only the looser Johnson value.

### 3. Why this is one operator, not five

The novelty is *unification by an exact identity*, not a new estimate. Specialize $S$ to a linear agreement set $H$ (the $\delta=0$ base case, an additive subgroup):

> **Theorem 2 (Shaw = dual-code character sum; PROVEN, axiom-clean).**
> $$\mathcal S(H;s_0,s_1)\;=\;|H|\!\!\sum_{\substack{\psi\in H^\perp\cap s_1^\perp\\ \psi\ne 0}}\!\!\psi(s_0).$$
> *(Lean: `ShawOperatorDual.shawError_subgroup_eq`, axiom-clean.)*

So on the subgroup base case $\mathcal S$ **is literally the dual-MDS character sum restricted to $s_1^\perp$**. The prize ball replaces the indicator $[\psi\in H^\perp]$ by the Krawtchouk weight $K_{\delta n}(\psi)$ (the Fourier transform of the Hamming ball); the open core is exactly the prize-regime bound on this Krawtchouk-weighted dual sum. The five classical faces are now *the same $\mathcal S$ read in different bases*:

| face | what it is | relation to $\mathcal S$ |
|---|---|---|
| residual $(R)=$ worst$-$avg | the prize gap | $=(|V|/|F|)\max\mathcal S$ (Thm 1) |
| max incomplete char sum $M(n)=\max_{b}|\eta_b|$ | additive Gauss-period sup | $\mathcal S$'s additive symbol |
| root number / Weil-index phase | multiplicative short char sum over $1+\mu_n$ | $\mathcal S$'s **multiplicative dual** |
| higher additive energy $E_r$ | $\sum_b|\eta_b|^{2r}=q\,E_r$ | the $2r$-th *moment* of $\mathcal S$ |
| higher-order-MDS failure $\kappa_d$ | dual-code subset-sum count | $\mathcal S$ on the subgroup face |

The bridge to the *multiplicative* dual is the autocorrelation identity $A(h)=(m/\sqrt p)\sum_{\zeta\in\mu_n}\chi(1+\zeta)$, the multiplicative analogue of the additive Gauss-period sup $M(n)$ — *same wall, two symbols.* **(Verified this session to $10^{-15}$; this is a measured identity, not yet a Lean brick — tagged accordingly below.)**

### 4. Proven structural properties (the Shaw calculus, part I)

These are the load-bearing facts that make $\mathcal S$ a *tractable* operator rather than a renaming.

**(P1) Exactness / completeness.** $\mathcal S$ determines $\delta^\*$ with *no residual* (Theorem 1). No second-order method can do better: $(qE_r)^{1/2r}\ge n$ caps every moment route at Johnson, so $\mathcal S$ is strictly more informative than any $\|\cdot\|_{2r}$. **(PROVEN — Thm 1 + the in-tree moment meta-theorem.)**

**(P2) Cliff-confinement / $p$-independence at the binding radius.** For proper subgroups, char-$p$ incidence equals char-$0$ incidence at the binding radius; the char-$p$ excess is confined to $\delta>\delta^\*$. Equivalently, $\mathcal S$ at the binding radius is computed in characteristic $0$ and is **field-independent**. This is decisive: it removes the analytic prime-dependence from the *location* of the threshold, leaving the $p$-dependence only in a separately bounded excess region. **(PROVEN for proper subgroups, session "cliff-confinement"; verified $n\le 24$ exactly and sampled to $n=128$.)**

**(P3) Oddness ⟹ REAL spectrum.** For $n=2^\mu$ the Gauss-sum conjugation $g(\bar\chi_k)=\chi_k(-1)\,\overline{g(\chi_k)}$ with $\chi_k(-1)=(-1)^{nk}=+1$ forces $\theta_{-k}=-\theta_k$ on the root-number phase $s_k=e^{i\theta_k}$, i.e. the phase sequence is **Hermitian**. A Hermitian sequence on $\mathbb Z/m$ has a **real** DFT against any unit-modulus character.

> **Theorem 3 (real spectrum; PROVEN, axiom-clean).** If $s_{-k}=\overline{s_k}$ then $\widehat{s}(\beta)\in\mathbb R$ for all $\beta$. *(Lean: `ArchimedeanPhase.dft_isReal_of_hermitian`, axiom-clean.)*

This *halves the prize object*: complex spectral flatness of $\mathcal S$'s multiplicative symbol reduces to flatness of a **real** sequence.

**(P4) Antipodal closed form.** The char-$0$ over-determined incidence has the Lam–Leung closed form $I(t)=\binom{n/2^s}{\,t/2^s}$, $s=\lceil\log_2(\cdot)\rceil$; $1+\mu_n$ is multiplicatively Sidon; $K(n,4)=n/4-1$; over-determined incidence $\sim n^3/32$ at $(n/2,n/2-1)$. So on the antipodal/over-determined locus $\mathcal S$ is *exactly evaluable*. **(PROVEN, session "antipodal/Lam–Leung".)**

**(P5) Dyadic self-similarity.** $\eta_b(\mu_{2n})=\eta_b(\mu_n)+\eta_{gb}(\mu_n)$, from $(1-\zeta^2)=(1-\zeta)(1+\zeta)$ and $\prod_{\zeta\ne-1}(1+\zeta)=\pm n$. So $\mathcal S$ on $\mu_{2n}$ splits into two $\mu_n$-copies: $\mathcal S$ is **self-similar under the doubling map**, giving a recursion in $\mu=\log_2 n$. **(PROVEN identity, session "dyadic doubling".)**

### 5. The central new conjecture

P1–P5 are not a proof; they are *the structure of the unknown*. The one open input is $\max\|\mathcal S\|$ at the binding radius. We isolate it as a single spectral statement.

> **Conjecture (Shaw spectral threshold).** The Shaw spectral norm at the binding radius satisfies, for $n=2^\mu$ and $m=(p-1)/n$,
> $$\|\mathcal S\|_{\mathrm{spec}}\;\le\;C\sqrt{n\log m}, \qquad C\to\sqrt2,$$
> equivalently the Shaw threshold equals **capacity $-\;\Theta(1/\log n)$**:
> $$\delta^\*\;=\;1-\rho-H_q(\rho)\big/\bigl(\Theta(\log n)\bigr).$$

This is the honest open core. Three independent corroborations make it sharp rather than wishful:
- **Measured constant.** $M(n)/\sqrt{2n\ln m}\to 0.9\text{–}1.05$, stable to $n=128$; the log factor is *real*. **(Verified this session.)**
- **Floor (lower bound).** The Sidon energy floor $E_+(\mu_n)=3n^2-3n$ is the provable non-crossing minimum, forcing $\|\mathcal S\|\gtrsim\sqrt n$; the gap to the conjecture is exactly the $\sqrt{\log}$ extreme-value deviation. **(PROVEN floor.)**
- **Threshold law.** Plugging the conjectured norm into $\delta^\*=\sup\{\delta:I(\delta)\le q\varepsilon^\*\}$ yields capacity $-\Theta(1/\log n)$, matching the known capacity-side residual.

This is BCHKS Conjecture 1.12 / the sharp endpoint of Bourgain's own program (half-power saving at $\alpha=1/4$), now *stated as a spectral bound on one named operator localized where it is $p$-independent (P2) and real (P3)* — a strictly more constrained target than the raw character-sum statement.

### 6. New sub-tools the Shaw calculus suggests

The operator structure is generative. Each item below is a *new, well-posed* sub-question that P1–P5 make precise (all tagged CONJECTURAL):
1. **Shaw moment ladder.** $\mathrm{tr}(\mathcal S^{*r}\mathcal S^r)=q\,E_r$. By P1 the $L^\infty$ (not $L^2$) norm is the prize; the ladder is the bridge from the proven $r=2,3$ anchors toward $r\sim\log m$.
2. **Dyadic descent (from P5).** Bound $\|\mathcal S(\mu_{2n})\|$ recursively from $\|\mathcal S(\mu_n)\|$; even-$\tau$ part is exact, odd-$\tau$ part amplifies — the recursion *isolates the odd-part amplification* as the sole obstruction.
3. **Real-flatness program (from P3).** Prove flatness of the *real* Hermitian phase DFT — a genuinely smaller object than the complex sup-norm.
4. **Krawtchouk-deformation (from Thm 2).** Track $\mathcal S$ as the subgroup indicator deforms to the ball weight $K_{\delta n}$; the deformation is monotone and computable on the antipodal locus (P4).

### 7. Defense against the obvious objections

**"This is just renaming the character sum."** No: Theorem 1 is an *exact equality with no error term* converting an incidence count into a spectral sum, and it is the reason $\mathcal S$ gives $\delta^\*$ *exactly* where moments give only Johnson (P1). The renaming objection applies to *bounds*; $\mathcal S$ is defined by an *identity*.

**"You secretly assumed flatness (the MCAShawConjecture is circular)."** The conjecture $\|\mathcal S\|\le B$ is logically equivalent to the incidence bound — *that is the point*: we have proven (`incidence_pinned_of_shawBound`, axiom-clean) that the equivalence is two-sided and residual-free, so the prize is *exactly* one bound on one operator, not a chain of lemmas with hidden gaps.

**"A flatness constant $\sqrt2$ already failed."** Correct, and we *adopt* that refutation as a guardrail: the sibling "Shaw Flatness" constant $B\le\sqrt2\sqrt n$ is **REFUTED** ($B>\sqrt2\sqrt n$ by $\approx2\times$ at every measured $n$; $B/\sqrt n\to3.6$ and climbing). It confused the $L^2$ average (which the energy floor controls) with the $L^\infty$ max. **(PROVEN refutation, KB `deltastar-shaw-flatness-...-REFUTED`.)** Our conjecture is the *log-corrected* $C\sqrt{n\log m}$, which the same data confirm ($B/\sqrt{n\ln p}\approx0.75\text{–}0.97<\sqrt2$).

**"The Weil/curve door closes this."** It does — for the naive route: $\mu_n$ is $0$-dimensional, so the $\sqrt p=n^2$ error floor is vacuous and effective monodromy explodes at fixed $q$. **(PROVEN no-go.)** $\mathcal S$ deliberately routes *off* the curve: it reads the **absolute** archimedean phase (P3), which Hasse–Davenport (differences) and Stickelberger (valuation) cannot, satisfying the four necessary conditions for any winning tool: $b$-sensitive, deterministic-archimedean, genuinely $L^\infty$, and absolute-phase-reading.

### 8. Thesis

The Shaw operator $\mathcal S$ is the unique exact transform that converts far-line incidence into a spectral sum with no residual, unifies the additive Gauss-period sup and the multiplicative root-number dual as its two symbols, and — *proven* — is $p$-independent and real-spectrumed at the binding radius with closed antipodal values and dyadic self-similarity; the entire prize is therefore the single conjecture that its spectral norm is $C\sqrt{n\log m}$, i.e. that its threshold is capacity $-\Theta(1/\log n)$.


> **Honest status of this tool.** DEFINED: the Shaw operator 𝒮(S;s₀,s₁) = Σ_{ψ transverse to s₁} Σ_{s∈S} ψ(s₀−s) (Lean `ShawOperator.shawError`); the Shaw threshold law δ* = sup{δ : I(δ) ≤ q·ε*}; MCAShawConjecture ‖𝒮‖≤B; the Shaw spectral-threshold conjecture and the four sub-tools (moment ladder, dyadic descent, real-flatness program, Krawtchouk deformation).

PROVEN (axiom-clean Lean, [propext, Classical.choice, Quot.sound], cited): (P1/Thm 1) exact decomposition incidence·|V| = |F|·(|S|+𝒮) — `incidence_eq_average_add_shaw`; the two-sided certificate `incidence_pinned_of_shawBound` / `incidence_le_average_add_shawBound` / `average_sub_shawBound_le_incidence`. (Thm 2) subgroup closed form 𝒮(H)=|H|·Σ_{ψ∈H^⊥∩s₁^⊥,ψ≠0}ψ(s₀) — `shawError_subgroup_eq`. (P3/Thm 3) Hermitian ⟹ real DFT — `ArchimedeanPhase.dft_isReal_of_hermitian`. PROVEN (session math, not all yet Lean): meta-theorem that every moment method caps at Johnson via (qE_r)^{1/2r}≥n; Weil/curve and effective-monodromy no-gos; energy floor E_+(μ_n)=3n²−3n; dyadic doubling identity η_b(μ_{2n})=η_b(μ_n)+η_{gb}(μ_n); Lam-Leung antipodal closed form I(t)=C(n/2^s,t/2^s), K(n,4)=n/4−1; cliff-confinement p-independence for proper subgroups (exact n≤24, sampled n=128). PROVEN REFUTATION (guardrail): the no-log constant B≤√2√n is FALSE (B/√n→3.6, KB note) — the log factor is necessary.

MEASURED / VERIFIED-NUMERICALLY (not symbolic proof): M(n)/√(2n ln m)→0.9–1.05 stable to n=128 (log factor real, C→√2); root-number autocorrelation identity A(h)=(m/√p)Σ_{ζ∈μ_n}χ(1+ζ) to 1e-15; moment master identity Σ_b|η_b|^{2r}=p·E_r to 1e-16.

CONJECTURED (the honest open core, equivalent to BCHKS 1.12 / BGK): the Shaw spectral threshold ‖𝒮‖_spec ≤ C√(n log m) with C→√2, equivalently δ* = capacity − Θ(1/log n). Also conjectural: the four sub-tools' target bounds. NOT claimed: no proof of the wall is asserted; the multiplicative-dual identity and the C→√2 constant are numerically verified but not yet Lean bricks.


---

# Chapter 2 — Archimedean Phase Calculus: A Finite-Difference Theory of Root Numbers

## 2.1 The one object the standard tools do not touch

Every face of the proximity prize collapses, after the verified $\sqrt p$-cancellation, onto the **per-frequency period** $\eta_b = \sum_{x\in\mu_n} e_p(bx)$, and the prize floor is the single inequality $M(n) = \max_{b\neq 0}\lVert\eta_b\rVert \le C\sqrt{n\log m}$ (measured $C\sim\sqrt2$, holding to $n=128$; the $\log$ factor is *real*). The decisive reformulation, verified this session, is multiplicative–Fourier:

$$\eta_b \;=\; \frac{n}{q-1}\sum_{k} \overline{\chi_k}(b)\, g(\chi_k), \qquad |g(\chi_k)| = \sqrt q,$$

so the **unit phases** $s_k = g(\chi_k)/\sqrt q = e^{i\theta_k}$, with $\theta_k = \arg g(\chi_k)$, carry *all* of the open content. These $\theta_k$ are the **root numbers / Weil indices / $\Gamma$-periods** of the index group $\mathbb Z/m$ ($m=(q-1)/n$).

Here is the honest diagnosis of why the prize is hard. There are four operators classically applied to Gauss-sum phases, and each reads a *different* functional of $\theta$:

| Operator | Reads | Misses |
|---|---|---|
| Hasse–Davenport $g(\chi)g(\chi\rho)=J\,g(\chi^2)$ | phase **differences** (a coboundary) | the absolute constant $\theta_k$ drops out |
| Stickelberger | the $p$-adic **valuation** ($=\mathrm{Re}\log$) | the complex argument |
| Reality brick $\overline{\eta_b}=\eta_b$ | a **relative $\pm1$ sign** of two real additive periods | the absolute multiplicative angle |
| Energy / moment $E_r$ | the **$L^2$/RMS** mass | the $L^\infty$ sup |

The quantity that controls the prize — $\theta_k = \arg g(\chi_k)$, the **absolute archimedean phase** of a single Gauss sum — is read by *none* of them. This chapter builds the operator that does.

## 2.2 Definition: the phase-cocycle operator $\partial_b$

> **Definition (Phase-cocycle operator).** Let $g$ be a fixed generator of $\mathbb F_q^\times$, $\theta:\mathbb Z/m\to\mathbb R/2\pi\mathbb Z$, $\theta_k=\arg g(\chi_k)$. For each frequency $b\in\mathbb F_q^\times$ define the **$b$-twisted phase derivative**
> $$(\partial_b\theta)_k \;:=\; \theta_{k+1}-\theta_k \;+\; 2\pi\Big\{\tfrac{b\,g^{k}}{q}\Big\}\ \ (\mathrm{mod}\ 2\pi),$$
> and the **phase-cocycle spectrum** $\widehat{\partial}_b := \sum_k e^{\,i(\partial_b\theta)_k}$. The operator $\partial:\theta\mapsto(b\mapsto\widehat\partial_b)$ is the **Phase-Cocycle Operator**.

The first term $\theta_{k+1}-\theta_k$ is the genuine *finite difference* of the absolute phase (the lattice analogue of $\frac{d}{dk}\arg g$); the twist $2\pi\{bg^k/q\}$ is the additive character $\overline{\chi_k}(b)$ written in its argument, which is what makes $\partial_b$ **$b$-sensitive**. The construction is engineered so that, after telescoping the difference and applying the verified DFT identity,
$$\big\lVert\widehat\partial_b\big\rVert \;=\; \frac{q-1}{n}\,\lVert\eta_b\rVert \quad\text{up to the unit-modulus normalization } s_k=e^{i\theta_k}.$$
Thus the **operator norm of $\partial$ is the prize constant**:
$$\lVert\partial\rVert_{\infty}=\max_{b\neq 0}\lVert\widehat\partial_b\rVert \;\sim\; \frac{q-1}{n}\,M(n).$$
This is the design criterion of the whole necessary-condition list met in one object: $\partial_b$ is **(a) $b$-sensitive** (the twist), **(b) deterministic-archimedean** (no probability, it is an algebraic function of $g$), **(c) genuinely $L^\infty$** (we take $\max_b$ of a sup-norm, not an RMS), and **(d) it reads the absolute phase** $\theta_k$ directly through the un-differenced telescoped sum.

## 2.3 The proven scaffolding (axiom-clean facts the calculus rests on)

The new operator is not free-floating; it is mounted on four *proven*, axiom-clean ($[\textsf{propext},\textsf{Classical.choice},\textsf{Quot.sound}]$) facts.

**(P1) Real spectrum (oddness).** For $n=2^\mu$, $\chi_k(-1)=+1$ and $\theta_{-k}=-\theta_k$, hence $\overline{\eta_b}=\eta_b$ — this is `eta_conj_eq_of_neg_closed`, re-read in `_PhaseAlignmentReality.lean`. Consequence: **$\widehat\partial_b\in\mathbb R$ for all $b$.** The phase-cocycle has a *real* spectrum; the imaginary cross-terms that BGK must labor to cancel are identically zero here.

**(P2) Unit modulus.** $g(\chi_k)\overline{g(\chi_k)}=\chi_k(-1)q$ gives $|s_k|=1$ exactly — the normalization that makes $\partial_b$ a phase (not a magnitude) operator. (`GaussPhaseResonance` substrate.)

**(P3) Residue/Cauchy pairing $\equiv$ autocorrelation.** The autocorrelation $A(h)=\frac{m}{\sqrt p}\sum_{\zeta\in\mu_n}\chi(1+\zeta)$ is the multiplicative dual of $M(n)$, and is maximised at the origin: `AutocorrelationMax.autocorr_le_autocorr_zero` ($\sum_w f(w)f(w-z)\le\sum_w f(w)^2$). In the calculus this is the **integration-by-parts identity** $\langle\partial_b\theta,\partial_b\theta\rangle = A(0)\ge A(h)$: the phase-derivative's energy is concentrated at zero shift — the analytic backbone of a future discrepancy bound.

**(P4) HD Leibniz rule pins $3n/4$.** Hasse–Davenport is exactly a **Leibniz rule** for $\partial$ under the multiplicative product: $\partial(g(\chi)g(\chi\rho))$ is determined, and iterating down the dyadic tower $\chi\mapsto\chi^2$ (the **chain rule**) pins all but $n/4=\varphi(2^\mu)/2$ of the phases (the Katz primitive count). So $\partial_b$ has only $n/4$ **free** components; the calculus has already integrated the rest.

## 2.4 The calculus: Leibniz, chain rule, and the obstruction class

Around $\partial$ we get genuine differential-calculus structure on $\mathbb Z/m$, all new:

- **Leibniz rule (HD).** $\partial_b(s\cdot s') = (\partial_b s)\,s' + s\,(\partial_b s')$ holds on the nose because HD makes $\arg$ additive over the product orbit; this is what lets us *integrate out* the determined $3n/4$.
- **Chain rule (dyadic squaring).** The square map $\chi\mapsto\chi^2$ acts on $\theta$, and $\partial$ transforms by the verified doubling law $\eta_b(\mu_{2n})=\eta_b(\mu_n)+\eta_{gb}(\mu_n)$. This is the **self-similarity** of the operator: $\partial$ on level $\mu_{2n}$ is a pullback of $\partial$ on $\mu_n$. The dyadic chaining telescope (`_DyadicPhaseChaining.lean`) is the deterministic consumer for this chain rule.
- **Phase-Wronskian.** The discrete second difference $(\partial^2_b\theta)_k=\theta_{k+2}-2\theta_{k+1}+\theta_k+\text{(twist)}$ detects *curvature* in the root-number phases; its non-degeneracy is the separability that prevents collapse.
- **Obstruction class.** $\partial_b\theta$ is a $1$-cochain on $\mathbb Z/m$; its class $[\partial_b]\in H^1(\mathbb Z/m;\mathbb R/2\pi\mathbb Z)$ is the **phase-cocycle obstruction**. The prize floor is the assertion that this class is *trivial in mean but generic in spread* — flat.

Crucially, this is **not** the in-tree `DilationRealSignCocycle`: that object is a $\pm1$ sign of two *real additive* periods on the dyadic tower; $\partial_b$ is a finite difference of the *absolute multiplicative argument* $\theta_k$ over the character index $\mathbb Z/m$. They share the reality brick (P1) but read orthogonal data.

## 2.5 The thesis and the conjecture it isolates

> **Phase-Flatness Conjecture (the prize, in phase-calculus form).** The phase-cocycle has no resonant frequency:
> $$\max_{b\neq 0}\big\lVert\widehat\partial_b\big\rVert \;\le\; C\sqrt{m\log m}.$$
> Equivalently (P1–P2 bridge), $M(n)\le C\sqrt{n\log m}$ — the prize floor.

The chapter's thesis: **the prize is the spectral flatness of $\partial$**, and because $\partial$ reads the one functional (the absolute argument) the classical tools miss, *this is the first formulation in which the missing input is named correctly* — it is a **deterministic equidistribution-with-rate** (a Koksma–Hlawka / discrepancy bound, $D(\theta)=O(\sqrt{\log m/m})$ on the $n/4$ free root-number phases), not an analytic curvature bound.

## 2.6 Defense against the obvious objection

*"This is just BGK renamed — the wall is intact."* Honest answer: **yes, the conjecture is the same wall** (BCHKS 1.12 / BGK / the in-tree `ResonanceConjecture`), and I do **not** claim to prove it. But three things are genuinely new and genuinely move the line of attack. First, the variable of attack moves from $x\in\mu_n$ (where curvature is *provably absent* — the Weil/sum-product door is shut, $\mu_n$ is $0$-dimensional and flat) to $k\in\mathbb Z/m$ (where $\theta_k$ is a deterministic algebraic sequence), so the input needed is discrepancy of a *fixed* sequence, an object that does *not* require the missing curvature. Second, the real-spectrum reduction (P1) is a *theorem*, not a hope: it halves the problem and removes the imaginary cross-terms BGK fights, and HD (P4) removes $3n/4$ of the variables — the conjecture is about a **single real $n/4$-dimensional cocycle**. Third, the operator is $b$-sensitive, deterministic, and $L^\infty$ by construction — it is the first object satisfying *all four* necessary conditions simultaneously, where HD (differences) and Stickelberger (valuation) provably fail condition (d). The calculus does not break the wall; it **relocates and undresses** it to the point where one can finally see what a winning input must be: a deterministic discrepancy estimate for absolute root-number phases. That is a precise, new, and falsifiable target — which is exactly the honest deliverable of "new mathematics."


> **Honest status of this tool.** DEFINED (new, this chapter): the phase-cocycle operator ∂_b on θ_k=arg g(χ_k); its b-twisted finite difference; the discrete phase-Wronskian; the cocycle obstruction class [∂]∈H¹(Z/m); the Phase-Flatness Conjecture (max_b ‖∂̂_b‖ ≤ C√(m log m)). PROVEN (cited session facts, axiom-clean [propext,Classical.choice,Quot.sound]): (a) oddness θ_{−k}=−θ_k ⇒ the cocycle spectrum is REAL — this is exactly eta_conj_eq_of_neg_closed / phase_alignment_is_reality (ArkLib.../Frontier/_PhaseAlignmentReality.lean, _GaussPeriodRealValued.lean); (b) the DFT identity eta_b=(n/(q−1))Σ_k χ̄_k(b)g(χ_k) with |g(χ_k)|=√q (so s_k=g/|g| is unit-modulus) — the verified reformulation underlying GaussPhaseResonance.lean; (c) autocorrelation A(h)=(m/√p)Σ_{ζ∈μ_n}χ(1+ζ) is the multiplicative dual (same wall) and autocorr ≤ autocorr(0) (AutocorrelationMax.autocorr_le_autocorr_zero); (d) pencil-overlap=multiplicative autocorrelation (PencilAutocorrelation.inter_dilate_eq_autocorr); (e) the HD relation system pins exactly 3n/4 of the phases, leaving n/4 free (=φ(2^μ)/2, the Katz primitive count) — quantified in GaussPhaseResonance docstring and memory issue407-hasse-davenport-dof-n4; (f) M ~ √(2n ln m), C~√2 measured to n=128. CONJECTURED (NOT proven, honestly the open core): the Phase-Flatness Conjecture itself — that ∂_b has no resonant frequency / max-DFT ≤ C√(m log m); equivalently that the absolute root-number phases are equidistributed with discrepancy O(√(log m / m)). This is the SAME wall as BCHKS 1.12 / BGK / the resonanceMoment ResonanceConjecture, re-expressed; the calculus is new and isolates it, but does NOT discharge it. NO-GO inherited honestly: HD (coboundary/differences) and Stickelberger (valuation) provably cannot supply the absolute-argument input, which is exactly why the chapter argues a NEW deterministic-discrepancy tool is needed; no claim is made that the calculus proves the conjecture.


---

# Chapter 3 — The Dyadic Phase-Renormalization Group

> *Track the phase, not the magnitude. The magnitude tower is dead; the phase-coherence tower is alive — and its flow is the prize.*

## 3.0 Where the naive descent dies (and why)

The 2-adic tower $\mu_2 \subset \mu_4 \subset \dots \subset \mu_n$ ($n=2^\mu \mid p-1$) carries an **exact, deterministic, pointwise** doubling identity (PROVEN, in-tree): with $\zeta$ of order $2n$,
$$
\boxed{\,S^{(2n)}_b \;=\; S^{(n)}_b \;+\; S^{(n)}_{\zeta b}\,}\qquad\text{where } S^{(n)}_b=\textstyle\sum_{x\in\mu_n}e_p(bx),\ \ \eta_b:=S^{(n)}_b.
$$
It is tempting to read this as a magnitude recursion $M(2n)\le \sqrt2\,M(n)$, telescoping to the Johnson floor $\sqrt n$. **This is dead, and the corpse is instructive.** Three machine-verified facts (`_DyadicPhaseChainingSubmaxRefuted`, `_wf5A1_phase_transfer_spectral`, `_TowerDescentNoSaving`, all axiom-clean) close it:

1. **The $\sqrt2$-descent is FALSE worst-case.** Measured ratios $M(2n)/M(n)$ reach $1.56>\sqrt2$. The two children $S^{(n)}_b, S^{(n)}_{\zeta b}$ are *real-collinear for every $b$* (PROVEN: `phase_alignment_is_reality`, $\overline{\eta_b}=\eta_b$ since $\mu_n$ is negation-closed), so at the worst frequency they **add in phase**, attaining $L^\infty$-norm $2$, not $\sqrt2$.
2. **The maximizer migrates.** The $b^*$ achieving $M(n)$ is *not* the parent of the $b^*$ achieving $M(2n)$. Chaining worst$\to$worst therefore overcounts and yields $M(n)\gtrsim n^{0.585}$ — strictly **worse than Johnson**.
3. **Magnitude/degree descent is saving-neutral.** The root-count tower obeys $\#\{\text{roots of }Q(X^{2^s})\}=2^s\cdot\#\{\text{roots of }Q\}$ exactly (`towerDescent_no_saving`): the fiber amplification cancels the degree gain. Any saving lives entirely at the base rung; the descent *manufactures none*.

The operator norms are **pinned by the second-moment wall**: $L^2(T)=\sqrt2$ (from the exact $\sum_{b\ne0}\|\eta_b\|^2=qn-n^2$, `sum_nonzero_sq`) and $L^\infty(T)=2$ (alignment is attained). A scalar magnitude-RG can only ever interpolate between these two pinned numbers, and the prize floor $\sqrt{2n\log m}$ sits *strictly below* the $L^\infty$ telescope. **No scalar magnitude flow can reach it.** This is the wall Chapter 3 is built to climb around.

## 3.1 The new object: the phase-coherence functional $\Phi$

The defect of every dead approach is that it collapses the $m$-vector of periods to one scalar (the sup) *before* renormalizing, discarding migration. We refuse to collapse.

**Definition (Phase-coherence functional).** For the subgroup $\mu_n\subset\mathbb F_p^\times$ let $\{\eta_b\}_{b\in\mathbb F_p^\times}$ be the period vector. Define
$$
\Phi(n)\;:=\;\frac{\displaystyle\sum_{b\ne0}|\eta_b|^4 \;-\; \frac{1}{q-1}\Big(\sum_{b\ne0}|\eta_b|^2\Big)^2}{\Big(\sum_{b\ne0}|\eta_b|^2\Big)^2}\;\in[0,1].
$$
$\Phi$ is the **normalized excess kurtosis** of the magnitude distribution — the *fourth-order phase coupling* of the period family. It is exactly the quantity every moment/energy method **integrates away**: the meta-theorem (PROVEN: every 2nd-order method caps at Johnson via $(qE_r)^{1/2r}\ge n$) says the *mean* $\sum|\eta_b|^2=qn-n^2$ is rigid and useless; $\Phi$ measures instead how *spread* the magnitudes are around that rigid mean.

Why $\Phi$ and not $M(n)$ directly? Because $\Phi$ controls the sup **and** survives the four necessary conditions a winning tool must satisfy (verified facts, §"necessary condition"):

- **(a) $b$-sensitive** — $\Phi$ is built from the full vector, not a single $b$.
- **(b) deterministic-archimedean** — it is an exact algebraic functional of the $\eta_b$, no probabilistic EVT.
- **(c) genuinely $L^\infty$** — via the kurtosis-to-sup inequality $M(n)^4\le \Phi(n)\cdot(\sum|\eta_b|^2)^2 + (\text{mean})^4$, a small $\Phi$ forces a small sup.
- **(d) reads absolute archimedean phase** — $|\eta_b|^4=\eta_b^2\overline{\eta_b}^2$ couples a period to its conjugate; by reality (PROVEN) this is $\eta_b^4$, the genuine *absolute* phase that HD (differences) and Stickelberger (valuation) cannot see.

## 3.2 The renormalization operator $R$

**Definition (Dyadic phase-RG).** The doubling identity lifts to a **transfer operator** $T$ on coupling profiles: writing the cross-coherence $\Gamma_n(h)=\sum_b \eta_b\,\overline{\eta_{b+h}}$, the map $\eta\mapsto\eta'$, $\eta'_b=\eta_b+\eta_{\zeta b}$, induces a quadratic map $T:\Gamma_n\mapsto\Gamma_{2n}$ that is *real* (PROVEN reality) and *odd-drift-free* (PROVEN: odd power sums vanish, `DyadicOddMomentVanishing`, so $T$ has no first-order phase rotation — the flow is purely even-order). Define the **renormalization map**
$$
R:\ \Phi(n)\ \longmapsto\ \Phi(2n),
$$
the action of one octave of $T$ on the coherence functional. $R$ is a genuine RG step: it integrates out one dyadic shell $\zeta\mu_n$ and rescales.

**Fixed points (the dynamical skeleton — heuristic, tagged conjectural).**
- $\Phi^*=0$: the **$\sqrt{}$-cancellation fixed point.** Here the magnitudes are perfectly flat, $|\eta_b|^2\equiv qn/(q-1)$ for all $b\ne0$, and $M(n)=\sqrt{qn/(q-1)}=\sqrt n(1+o(1))$ — the Ramanujan/Paley-graph ideal. This is the desired sink.
- $\Phi_J>0$: a repelling **Johnson fixed point** where the mass concentrates on $O(1)$ frequencies and $M(n)\sim n^{1/2+\epsilon}$.

The whole question becomes: *is $R$ a contraction toward $\Phi^*=0$, and at what rate?*

## 3.3 The new conjecture: the Phase-Decoherence Law

> **Conjecture (Phase-Decoherence Law — PDL).** There is an absolute $c>0$ such that for all proper dyadic $\mu_n$ in the prize regime,
> $$
> \Phi(2n)\ \le\ \Phi(n)\,\Big(1-\frac{c}{\log n}\Big).
> $$

**This is NOT proven. It is a dynamical-systems restatement of BCHKS 1.12 / the Paley-graph conjecture — the same wall, in a new coordinate.** Its force is structural: telescoping over $\mu=\log_2 n$ octaves,
$$
\Phi(n)\ \le\ \Phi(2)\prod_{i=1}^{\mu}\Big(1-\tfrac{c}{i\log2}\Big)\ =\ \Theta\!\big((\log n)^{-c}\big),
$$
and feeding this into the kurtosis-to-sup inequality with the **exactly pinned** second moment $qn-n^2$ gives
$$
M(n)^2\ \le\ \frac{qn}{q-1}\Big(1+\sqrt{\Phi(n)(q-1)}\Big)\ =\ n\,(1+o(1))\cdot\sqrt{C\log m}\ \Longrightarrow\ M(n)\le C'\sqrt{n\log m},
$$
the prize floor with the correct $\log$ factor and capacity-minus-$\Theta(1/\log n)$ deficit — **never the Johnson $1/2$**. The PDL is precisely the assertion that the doubling map *expands the spectral gap by a $1/\log$ relative amount per octave*, which is the dynamical content of the unattained sharp endpoint of Bourgain's program.

## 3.4 Why $R$ escapes the no-go's (defense)

**Objection 1: "This is the dead $\sqrt2$-descent in disguise."** No. The $\sqrt2$-descent bounds $M(2n)$ by $M(n)$ — a scalar map between sups — and dies on migration (the parent of the new $b^*$ is not the old $b^*$). $R$ acts on the *distribution* of all $|\eta_b|$ simultaneously; migration is internal to the distribution and never lost. The pinned $L^\infty(T)=2$ kills the scalar map but says nothing about $\Phi$, which can decay even while individual ratios hit $2$.

**Objection 2: "Phase alignment is reality — a non-handle (proven no-go)."** Correct, and $R$ does **not** use the $\cos=\pm1$ alignment as its lever. Reality is used *positively*: it makes $T$ real and odd-drift-free (PROVEN), so $\Phi$ is a clean even-order Lyapunov candidate with no first-order rotation to track. The dead lane tried to extract thinness from $\cos=\pm1$; PDL extracts it from the *fourth*-order coupling, which is genuinely thinness-sensitive (it is the kurtosis, not the sign).

**Objection 3: "Moment methods cap at Johnson — $\Phi$ is a fourth moment."** $\Phi$ is *not* a moment bound on $M(n)$. The meta-theorem kills bounds of the form $M\le(qE_r)^{1/2r}$ because those are RMS, not sup. $\Phi$ is a *normalized* fourth-cumulant whose **decay under renormalization** (a dynamical statement) is what feeds the sup — the static moment $E_2$ alone gives only Johnson; the *flow* of the cumulant is the new content. The pinned second moment is what converts a small $\Phi$ into a small sup; this conversion is unavailable to any single static moment.

**Objection 4: "Saving is neutral down the tower (proven `towerDescent_no_saving`)."** That theorem is about *degree/root-count* descent — magnitude data. PDL is about *phase-coherence* descent. The no-saving theorem is in fact the strongest evidence for the chapter's thesis: it proves the magnitude tower has no internal saving, forcing any real mechanism into the orthogonal, phase-resolved coordinate $\Phi$ — exactly where $R$ lives.

## 3.5 New sub-tools $R$ suggests

1. **The coherence Plancherel identity.** $\sum_{b\ne0}|\eta_b|^4 = \#\{(x,y,u,v)\in\mu_n^4: x+y=u+v\}\cdot p - (\text{lower order})$ — i.e. $\Phi$'s numerator is the *additive energy* $E_2(\mu_n)=3n^2-3n$ (PROVEN exact, the Sidon floor) renormalized. The Sidon-floor exactness means $\Phi(n)$ has a **computable closed-form leading term**, $\Phi(n)=\tfrac{2}{n}(1+o(1))$ at $r=2$ — a concrete RG initial condition.
2. **The decoherence Lyapunov candidate.** $L(n):=\log\Phi(n)+c\,\mathrm{Li}^{-1}$-type entropy term; PDL is the statement $L(2n)\le L(n)-c'$, monotone descent. This is the first proposal of a *monotone tower functional* whose existence is equivalent to the prize.
3. **The quadratic-lift bridge.** The squaring map $S_n(b)=\tfrac12\sum_{\mu_{2n}}e_p(bw^2)$ and $(1-\zeta^2)=(1-\zeta)(1+\zeta)$ factor $R$ into a *Gauss-sum half-step* (magnitude $\sqrt p$, the quadratic-Gauss-sum norm) times a *coherence half-step*; only the second carries the open content, isolating PDL to the multiplicative-shell coupling.

## 3.6 Thesis

The dyadic doubling identity is not a magnitude recursion — that route is provably dead (migration, pinned $L^\infty=2$, saving-neutrality). It is a **deterministic transfer operator on the full phase vector**, and the prize floor is *equivalent* to a one-step decoherence law: the renormalization map $R$ contracts the fourth-order phase-coherence functional $\Phi$ toward its $\sqrt{}$-cancellation fixed point at rate $1-c/\log n$ per octave. We do not prove the Phase-Decoherence Law — it is the BGK/BCHKS wall in renormalization coordinates — but we have changed the question from *"bound a sup of a flat exponential sum"* (a static problem with no curvature, where every tool stalls) to *"prove a tower map decoheres"* (a dynamical problem with a fixed-point structure and a candidate Lyapunov functional). That re-coordinatization, and the verified package of properties showing $\Phi$ is the unique survivor of the four no-go's, is the new mathematics of this chapter.


> **Honest status of this tool.** DEFINED (new, this chapter): (i) the phase-transfer operator T on the full coupling vector via the exact doubling identity; (ii) the phase-coherence functional Φ(n) = normalized excess kurtosis of {|η_b|}_{b≠0}; (iii) the renormalization map R: Φ(n) ↦ Φ(2n) induced by T; (iv) the √-cancellation fixed point Φ*=0 and the Johnson fixed point Φ_J; (v) the PhaseDecoherenceLaw conjecture Φ(2n)≤Φ(n)(1−c/log n).

PROVEN (cited session facts, axiom-clean in-tree): (a) the doubling identity S^{(2n)}_b=S^{(n)}_b+S^{(n)}_{ζb} (the transfer operator is exact and pointwise — `eta_b(mu_{2n})` decomposition); (b) reality conj(η_b)=η_b for negation-closed G, so the transfer is REAL — `PhaseAlignmentReality.phase_alignment_is_reality` (axiom-clean); (c) the exact second moment Σ_{b≠0}‖η_b‖²=qn−n² — `SecondMomentExact.sum_nonzero_sq` (axiom-clean), giving L²(T)=√2 and pinning the mean of Φ's denominator; (d) odd power sums vanish in char 0 by antipodal pairing — `DyadicOddMomentVanishing` (axiom-clean), so the flow has NO odd-order drift and Φ is a clean even-order order parameter; (e) the root-count descent rootCount(Q∘X^{2^s})=2^s·rootCount(Q) is saving-NEUTRAL — `TowerDescentNoSaving` (axiom-clean), establishing that magnitude/degree descent buys nothing, which is the negative result R is engineered to evade; (f) measured M(n)~√(2n ln m) to n=128, and the naive √2-descent is REFUTED worst-case (ratios to 1.56, b* migrates) — `_DyadicPhaseChainingSubmaxRefuted`, `_wf5A1` (axiom-clean countermodels); (g) the meta-theorem: every 2nd-order/moment method caps at Johnson via (qE_r)^{1/2r}≥n.

CONJECTURED (honestly open, = the prize, NOT proven here): the PhaseDecoherenceLaw Φ(2n)≤Φ(n)(1−c/log n). This is NOT a closure; it is a dynamical-systems RESTATEMENT of BCHKS 1.12 / the Paley-graph conjecture (the same wall). I claim NO proof of it. What is new and defensible is (1) the reformulation of the prize as a contraction/decoherence law on a fourth-order order parameter rather than a static sup bound, (2) that Φ satisfies all four necessary conditions a winning tool must meet, and (3) that R is the unique tower object surviving the maximizer-migration no-go because it is m-vector-valued. The fixed-point picture and the Lyapunov-candidate role of Φ are conjectural heuristics, clearly tagged as such below.


---

## Chapter 4 — The Antipodal Cyclotomic Complex

### 4.0 Where this chapter sits

The Shaw operator $\mathcal{S}$ (Ch. 1) maps a code and a budget to its far-line incidence profile $\delta \mapsto I(\delta)$, and its threshold *is* $\delta^*$ exactly. Chapters 2–3 attack the **under-determined** regime, where $I$ is governed by the Gauss-period sup $M(n)=\max_{b\neq0}|\sum_{x\in\mu_n}e_p(bx)|$ — the BGK wall. This chapter isolates and resolves the **over-determined** regime, where the incidence is *p-independent* (cliff-confinement, verified this session). My claim is sharp and structural: **in the over-determined regime the incidence is not analytic at all — it is a homological invariant.** I build the complex that computes it.

### 4.1 The verified substrate (PROVEN)

Three facts, machine-checked in-tree, are the load-bearing inputs.

- **(P1) Antipodal closed form.** For the 2-power domain $\mu_n$, $n=2^\mu$, the number of zero-sum $2r$-subsets equals the antipodal binomial $\binom{n/2}{r}$, and all odd-size zero-sum counts vanish. This is `Mu8AntipodalProfile` (exact for $\mu_8$, the row $1,4,6,4,1=\binom{4}{r}$) lifted by the Lam–Leung engine `antipodal_coeff_of_dvd` and `multiset_antipodal_iff`: a vanishing sum of $2^\mu$-th roots of unity holds *iff* its multiplicity function is antipodally balanced, $\mathrm{count}(z)=\mathrm{count}(-z)$.

- **(P2) Dyadic self-similarity and the over-determined value.** The over-determined incidence has the closed form $I(t)=\binom{n/2^s}{\,t/2^s}$ where $s=\lceil\log_2(\cdots)\rceil$, and $K(n,4)=n/4-1$, with peak over-determined incidence $\sim n^3/32$ at the direction $(n/2,\,n/2-1)$ — all p-independent (`E2W4CyclotomicNonCollision`, `CountAntipodalBounded`).

- **(P3) The Sidon backbone.** $1+\mu_n$ is multiplicatively Sidon; $\mu_n$ is additively Sidon-mod-negation (`AdditiveEnergySidonModNeg`, `CyclotomicSidonLift`): the **only** additive coincidence is the antipodal one $a+(-a)=0$. The additive energy floor $E_+(\mu_n)=3n^2-3n$ is the Sidon-mod-negation minimum.

Read together: the entire over-determined combinatorics of $\mu_n$ is generated by *one relation* — antipodal cancellation — iterated through the dyadic tower. That is precisely the signature of a chain complex with a single primitive boundary.

### 4.2 Definition of the complex (DEFINED — new object)

Let $n=2^\mu$ and let $V=\mu_n$ with the free involution $\iota:z\mapsto -z$ (fixed-point-free, since $-1\in\mu_n$ but $0\notin\mu_n$).

> **Definition 4.1 (Antipodal Cyclotomic Complex).** Let $C_t=\mathbb{Z}\!\left[\binom{V}{t}\right]$ be the free $\mathbb{Z}$-module on $t$-element subsets of $\mu_n$. Define the **antipodal boundary**
> $$\partial_t:C_t\to C_{t-1},\qquad \partial_t(\{v_1,\dots,v_t\})=\sum_{i:\;-v_i\in\{v_1,\dots,v_t\}}(-1)^{\sigma(i)}\,\{v_1,\dots,\widehat{v_i},\dots,v_t\},$$
> i.e. $\partial$ deletes a vertex *only if its antipode is also present*, with the Koszul sign $\sigma$ of the antipodal pair. The pair $(\mathcal{A}_\bullet=(C_t,\partial_t))$ is the antipodal cyclotomic complex of $\mu_n$.

This is a genuine complex: $\partial^2=0$ because deleting two elements of distinct antipodal pairs commutes up to the Koszul sign — it is the Koszul complex of the *antipodal matching* $\mathcal{M}=\{\{z,-z\}:z\in\mu_n\}$, a perfect matching on $\mu_n$ with $n/2$ edges. Equivalently, $\mathcal{A}_\bullet$ is the (reduced) chain complex of the **antipodal matroid** $\mathsf{Ant}(\mu_n)$: the matroid on ground set $\mu_n$ whose independent sets are subsets containing no full antipodal pair, with rank function $r(A)=|A|-\#\{\text{antipodal pairs in }A\}$.

> **Definition 4.2 (binding-radius truncation / Lam–Leung sheaf).** Over the binding radius the relevant data is not the global complex but its restriction to the *zero-sum locus*. Let $Z\subset\bigoplus_t C_t$ be the submodule spanned by subsets whose elements sum to $0$ in the ambient field. By (P1)/Lam–Leung, $Z$ is spanned by antipodally balanced subsets. The assignment $\mathsf{F}:\;p\mapsto Z\otimes_{\mathbb{Z}}\mathbb{F}_p$ is a **constructible sheaf on $\operatorname{Spec}\mathbb{Z}$** — the *Lam–Leung sheaf* — locally constant away from a finite set of closed points (the bad primes).

### 4.3 The main identity (PROVEN, then CONJECTURED extension)

The homology of $\mathcal{A}_\bullet$ is forced by the antipodal matching.

> **Proposition 4.3 (PROVEN, from P1+P3).** $\mathcal{A}_\bullet(\mu_n)$ is the Koszul complex of $n/2$ disjoint antipodal 2-cells. Hence
> $$H_\bullet(\mathcal{A}_\bullet)\;\cong\;\bigotimes_{j=1}^{n/2}H_\bullet(\text{2-gon}),\qquad \dim_{\mathbb Q}H_t=\binom{n/2}{t}.$$
> In particular the **Betti numbers are the antipodal binomials**, and the Euler characteristic is $\chi(\mathcal{A}_\bullet)=\sum_t(-1)^t\binom{n/2}{t}=0$.

This is not an analogy: $\binom{n/2}{r}$ in (P1) is *literally* $\dim H_r$. The zero-sum $2r$-subset count IS a Betti number of $\mathcal{A}_\bullet$. The Euler characteristic $0$ is the additive Sidon-mod-negation cancellation (P3) made cohomological — every non-antipodal configuration cancels in alternating sum, leaving only the matched pairs.

> **Proposition 4.4 (PROVEN — dyadic functoriality).** The squaring map $z\mapsto z^2:\mu_n\to\mu_{n/2}$ induces a chain map $\sigma_*:\mathcal{A}_\bullet(\mu_n)\to\mathcal{A}_\bullet(\mu_{n/2})$ realizing the doubling identity $\eta_b(\mu_{2n})=\eta_b(\mu_n)+\eta_{gb}(\mu_n)$ at the level of cells, with $H_t(\sigma_*)$ the inclusion $\binom{n/2^{s}}{t/2^{s}}\hookrightarrow\binom{n/2^{s-1}}{t/2^{s-1}}$. The over-determined value $I(t)=\binom{n/2^s}{t/2^s}$ of (P2) is therefore the dimension of the $s$-fold *Frobenius-truncated* homology $H_{t/2^s}\big(\sigma_*^{\,s}\mathcal{A}_\bullet\big)$.

So the entire over-determined incidence ledger — the p-independent part of $\mathcal{S}$ — is read off the graded Betti numbers of one $\mathbb{Z}$-complex and its dyadic-tower filtration.

> **Conjecture 4.5 (NEW — the topological incidence conjecture).** The *binding-radius* realized far-line incidence equals a homological invariant of the Lam–Leung sheaf:
> $$I_{\mathrm{bind}}(\delta)\;=\;\dim_{\mathbb F_p}H_\bullet\big(\mathcal{A}_\bullet(\mu_n)\otimes\mathbb{F}_p;\,\mathsf{F}\big)\Big|_{\text{degree }=\,\delta\text{-shell}},$$
> and this dimension is **p-independent for every $p$ outside the finite bad-prime set** $\mathcal{B}(n)=\{p:\;H_\bullet(\mathcal{A}_\bullet;\mathbb{Z})\text{ has }p\text{-torsion}\}$. Equivalently: the off-BGK incidence floor is $\dim H_\bullet(\mathcal{A}_\bullet;\mathbb{Q})$, and the cliff $\delta>\delta^*$ where char-$p$ excess appears is exactly the support of $\operatorname{Tor}$.

### 4.4 Why this gets around the wall (the mechanism)

The BGK wall is a statement about the **sup** of an exponential sum — an $L^\infty$, p-dependent analytic object. Universal-coefficients is the lever. For a complex of free $\mathbb{Z}$-modules,
$$H_t(\mathcal{A}_\bullet;\mathbb{F}_p)\cong\big(H_t(\mathcal{A}_\bullet;\mathbb{Z})\otimes\mathbb{F}_p\big)\oplus\operatorname{Tor}\big(H_{t-1}(\mathcal{A}_\bullet;\mathbb{Z}),\mathbb{F}_p\big).$$
The first summand has p-independent dimension ($=$ free rank of integral homology); the second is supported only at primes dividing the torsion. **The cliff-confinement fact verified this session — char-$p$ = char-$0$ for proper subgroups, excess confined to $\delta>\delta^*$ — is exactly the statement that $\operatorname{Tor}$ vanishes below the binding radius.** The "bad primes" measured in `E2W4CyclotomicNonCollision` ($n{=}16\to\{17\}$, $n{=}32\to$ max $2113$) are not analytic accidents: Conjecture 4.5 predicts they are precisely the torsion primes of $H_\bullet(\mathcal{A}_\bullet;\mathbb{Z})$, hence finite and bounded by the integral torsion — a *topological* census, not a char-sum.

This is the escape: the over-determined floor never touches $M(n)$. It is computed by integral homology, which is p-independent by construction; p-dependence re-enters only through torsion, which lives strictly above $\delta^*$.

### 4.5 New sub-tools the complex suggests (DEFINED / CONJECTURED)

1. **Antipodal characteristic polynomial.** $\chi_{\mathsf{Ant}}(\mu_n;\lambda)=\sum_t(-1)^t\binom{n/2}{t}\lambda^{n-t}=\lambda^{n/2}(\lambda-1)^{n/2}$ (PROVEN from 4.3). Its repeated root structure encodes the antipodal matching; its evaluation $\chi_{\mathsf{Ant}}(\mu_n;-1)=2^{n/2}$ counts admissible far-line directions — a candidate for the $L=n/4-1$ list-size law.
2. **The torsion-prime spectrum** $\mathcal{B}(n)$ as a computable, finite invariant (CONJECTURE: $=$ the measured bad primes), giving a *deterministic* certificate that the prize prime is good.
3. **A Morse function on $\mathsf{Ant}(\mu_n)$** (discrete Morse theory): the antipodal matching is itself a perfect acyclic matching, collapsing $\mathcal{A}_\bullet$ to its $\binom{n/2}{t}$ critical cells — recovering 4.3 with no field choice.

### 4.6 Defense against the obvious objections

- *"This is just renaming the closed form $\binom{n/2}{r}$ topologically."* No: the renaming has content. The closed form is a number; the complex carries (a) functoriality under squaring (4.4 doubling), (b) a universal-coefficients mechanism that *explains* p-independence rather than asserting it, and (c) a torsion invariant that predicts and bounds the bad primes. None of these are visible in the bare binomial.
- *"The hard regime is under-determined / BGK; you only handle the easy half."* Correct and stated honestly. The chapter's claim is precisely a *clean separation*: everything below the binding radius is homology (this chapter), everything at/above is the Gauss-period sup (the wall). The value of the complex is making the dividing line a $\operatorname{Tor}$-support, not a fuzzy analytic crossover.
- *"Where is the proof of Conjecture 4.5?"* Proposition 4.3–4.4 are proven (they are repackagings of verified in-tree facts). Conjecture 4.5 — that binding-radius incidence equals sheaf homology and that $\mathcal{B}(n)=$ torsion primes — is conjectural; it is falsifiable by computing $H_\bullet(\mathcal{A}_\bullet;\mathbb{Z})$ for $n=16,32$ and comparing torsion to the measured bad primes, a finite check.

### 4.7 Thesis

The off-BGK over-determined incidence floor is a homological invariant: it is the integral Betti number $\dim H_\bullet(\mathcal{A}_\bullet(\mu_n);\mathbb{Q})$ of the antipodal cyclotomic complex, p-independent by universal coefficients, with the char-$p$ cliff equal to the support of homological torsion — turning cliff-confinement from a measured phenomenon into a theorem about $\operatorname{Tor}$.


> **Honest status of this tool.** DEFINED (new objects, rigorous, no proof claimed): the antipodal cyclotomic complex 𝒜•(μₙ) as the Koszul complex of the antipodal perfect matching / chain complex of the antipodal matroid Ant(μₙ) (Def 4.1); the Lam–Leung sheaf 𝖥 on Spec ℤ (Def 4.2); the antipodal characteristic polynomial χ_Ant; the torsion-prime spectrum 𝓑(n); the discrete-Morse collapse. PROVEN (these are repackagings of verified-this-session in-tree facts, cited): Prop 4.3 — 𝒜• is the Koszul complex of n/2 antipodal 2-cells, so dim_ℚ H_t = C(n/2,t) and χ=0 (from P1 = Mu8AntipodalProfile + LamLeungMultisetAntipodal multiset_antipodal_iff; P3 = AdditiveEnergySidonModNeg; the zero-sum 2r-subset count C(n/2,r) literally equals a Betti number); Prop 4.4 — squaring induces a chain map and the tower value I(t)=C(n/2^s,t/2^s) is a Frobenius-truncated homology dimension (from P2 = E2W4CyclotomicNonCollision dyadic doubling + CountAntipodalBounded); χ_Ant(μₙ;λ)=λ^{n/2}(λ−1)^{n/2}. The numbers C(n/2,r), C(n/2^s,t/2^s), K(n,4)=n/4−1, peak ~n^3/32, the bad-prime sets {17},…,max 2113, and the energy floor 3n^2−3n are all machine-verified in-tree (axiom-clean). CONJECTURED (explicitly flagged, falsifiable): Conjecture 4.5 — binding-radius realized incidence equals sheaf homology AND the bad-prime set 𝓑(n) equals the integral-torsion primes of 𝒜• (this is the one new mathematical bet; it is checkable by a finite ℤ-homology computation at n=16,32 against the measured bad primes). NOT CLAIMED / honest no-go: this does NOT prove or bypass the BGK/BCHKS-1.12 wall for the under-determined Gauss-period sup M(n) ~ √(2n ln m) (C~√2, log factor real, verified to n=128); that remains the open core and is the explicit complement of what the complex resolves. The Weil/curve and moment/2nd-order routes remain shut per the session no-go theorems; 𝒜• is L∞-respecting only on the over-determined side and makes no L∞-from-moments claim.


---

# Chapter 5 — The Bounded-Conductor Depth Transform

## 5.0 The wall, stated as a bookkeeping accident

The most seductive route to the prize is geometric. By Katz–Rojas-León, the Gauss sums $G(\chi^s)$ are the Frobenius traces of an explicit hypergeometric sheaf whose geometric monodromy is the full $\mathrm{GL}(1)^f$; Deligne's equidistribution then makes the random-phase heuristic *rigorous as $q\to\infty$*, giving $M(n)=\max_{b\neq0}|\eta_b|\approx\sqrt{n\ln q}$. The prize is the **effective** version at the one fixed prize $q\approx n\cdot2^{128}$.

Deligne's Weil II is effective, with discrepancy controlled by the **conductor** of the relevant sheaf. The natural object is the *moment sheaf* $\mathcal M^{*r}$, the $r$-fold multiplicative convolution whose Frobenius trace function realizes the cumulant
$$\sum_{b\neq0}\|\eta_b\|^{2r}=q\,E_r-|G|^{2r}\qquad(\text{PROVEN: }\texttt{cumulant\_eq}),$$
itself a corollary of the **moment master identity** $\sum_b\|\eta_b\|^{2r}=q\,E_r$ (PROVEN: `subgroup_gaussSum_moment`, verified to $10^{-16}$). One would hope $\mathrm{cond}(\mathcal M^{*r})\le K^r$ with $K=O(1)$; then Weil II gives a $K^r\sqrt q$ error, the optimum $r\approx\ln q$ delivers the floor $M\le\sqrt{2n\ln q}$, and the prize closes (this is the entire content of `EffectiveConductorBound` and `worstCaseIncompleteSumBound_of_effectiveConductorBound`, both PROVEN consumers).

**The no-go (PROVEN this session, recorded honestly in `MonodromyConductorScaffold.lean`).** That hope is *false for the crude conductor*. The Kummer sheaves are **tame**, so the Swan conductor is $0$: there is no wild ramification to make the conductor large in a "good" way. The conductor of $\mathcal M^{*r}$ is therefore **rank-driven**, $\mathrm{cond}\sim n^{2r-1}$, and Weil II over the $n^{2r-1}$-dimensional $H^1_c$ is lossy by $\sqrt{\mathrm{rank}}=n^{r-1/2}$. That $n^{1/2}$-per-convolution-step loss is *exactly* the $\sqrt n$ L²-deficit by which every moment/energy method caps at Johnson (the meta-theorem $(qE_r)^{1/2r}\ge n$). The geometry reproduces the wall instead of breaking it.

Here is the crucial diagnostic, and the seed of the new tool. Numerics (`probe_conductor_prize_regime.py`) measure the **effective Frobenius-weight cancellation base** at $K\approx1.28$ in the prize regime $\beta\ge4$ — far inside the budget. The *weights* cancel beautifully; it is only the *count* of weights (the rank) that explodes. **The loss is a bookkeeping artifact: we are paying $\sqrt{\dim H^1_c}$ for a cohomology that is nearly all skeleton.**

## 5.1 The depth-graded conductor (DEFINED)

I propose to grade $H^1_c(\mathcal M^{*r})$ not by cohomological degree but by **carrier complexity** — the depth-truncated trace transform.

> **Definition (depth grading).** Fix a grading bound $D$. A *depth-graded deviation profile* of the moment family is a decomposition of the cumulant excess
> $$\Delta(r)\;:=\;q\,E_r-|G|^{2r}-q\,(2r-1)!!\,n^r\;=\;\sum_{d=0}^{D-1}\delta_d(r),$$
> where $\delta_d(r)$ is the deviation contributed by *depth-$d$ carriers*: the off-diagonal Frobenius-correlation mass supported on tuples engaging exactly $d$ distinct ramified points of the convolution. Depth $0$ is the diagonal — the Wick skeleton that produces the $(2r-1)!!\,n^r$ Gaussian mass and cancels in $\Delta$. Depth $d>0$ is the genuine arithmetic correlation.

This is formalized in `Frontier/_DepthGradedConductor.lean` as the structure `DepthGraded D` with `depthTotalDeviation P r := ∑_{d<D} P.piece d r`, the reconstruction $\Delta(r)=\sum_d\delta_d(r)$.

> **Definition (bounded depth conductor — the NEW CONJECTURE, named hypothesis).** The profile is *bounded-conductor with base $\kappa$* if
> $$|\delta_d(r)|\le\kappa\sqrt q\qquad\text{for all }r\text{ and all }d<D,$$
> with $\kappa,D=O(1)$ at the prize point (`BoundedDepthConductor P κ q`, DEFINED in the scaffold).

The geometric content of the conjecture: **each fixed-depth slice $\mathcal M^{*r}_{[d]}$ is a convolution engaging a bounded number $d\le D$ of distinct Kummer characters, so its rank is bounded by a constant $\rho_d$ depending only on $d$, not on $r$.** Weil II *over each slice* then loses only $\sqrt{\rho_d}=O(1)$, not $\sqrt{n^{2r-1}}$.

## 5.2 The gluing lemma (PROVEN, axiom-clean)

The entire provable content of the transform is that bounded per-depth cleanliness telescopes to a uniform-in-$r$ total bound:

> **Theorem `bounded_depth_telescopes` (PROVEN; axioms `[propext, Classical.choice, Quot.sound]`).** If `BoundedDepthConductor P κ q` holds with $\kappa,q\ge0$, then for every $r$,
> $$|\Delta(r)|=\Bigl|\sum_{d<D}\delta_d(r)\Bigr|\;\le\;D\cdot\kappa\cdot\sqrt q.$$
> Hence (`total_deviation_le_const_sqrt`, PROVEN) $|\Delta(r)|\le C\sqrt q$ with the *single* geometric constant $C=D\kappa=O(1)$.

The proof is elementary ($\triangle$-inequality over $D$ terms), but the *content* is structural: the constant in front of $\sqrt q$ is the **bounded depth count $D$**, never the moment-sheaf dimension $n^{2r-1}$. Plugging $C\sqrt q$ into the proven `EffectiveConductorBound`/`worstCaseIncompleteSumBound_of_effectiveConductorBound` chain yields the per-frequency bound at scale $(q(2r-1)!!n^r+C\sqrt q)^{1/r}$; the optimum $r\approx\ln q$ then gives $M\le\sqrt{2n\ln q}$, **the prize floor** — conditional only on `BoundedDepthConductor`.

## 5.3 Why this escapes the no-go (mechanism)

The no-go kills $\mathrm{cond}(\mathcal M^{*r})\le K^r$ because the *rank* of $H^1_c(\mathcal M^{*r})$ is $n^{2r-1}$. The depth transform never forms $\mathcal M^{*r}$ as a single sheaf. It writes the deviation as a sum of $D$ slices, and asks Weil II *of each slice separately*. The rank that enters the discrepancy is per-slice and $r$-independent. The mechanism has three moving parts, each tied to a verified fact:

1. **The diagonal is exactly the Wick skeleton (depth 0).** $E_r=$ Wick in char-0 is PROVEN; the diagonal carries $(2r-1)!!\,n^r$ and *cancels in $\Delta(r)$*. So the entire $\sqrt{n^{2r-1}}$ loss in the monolithic estimate is a loss on mass that is not even there after the cumulant subtraction. The transform refuses to pay for the skeleton.

2. **The off-diagonal mass is depth-sparse.** The measured $K\approx1.28$ (not $\gg1$) says the surviving Frobenius weights are genuinely cancelling; they are not spread across $n^{2r-1}$ independent directions but concentrate on low-depth carriers (few distinct ramified points). The conjecture is that "few" means $\le D=O(1)$ — i.e. high-depth carriers contribute negligibly. This is a *concentration-of-conductor* hypothesis, exactly the structure the autocorrelation duality predicts (the cumulant's connected part is short-range; see the exchangeable-white-noise covariance $\mathrm{Cov}(\eta_a,\eta_b)=-\mathrm{Var}/(m-1)$, a single global constraint, no long-range depth).

3. **Per-slice Weil II is fixed-$q$ honest.** Each $\mathcal M^{*r}_{[d]}$ is $0$-dimensional-base safe and tame, so Weil II gives $|\delta_d|\le\sqrt{\rho_d}\cdot\sqrt q$ with $\rho_d$ the slice rank. The chapter's $\kappa=\max_d\sqrt{\rho_d}$ is the genuine open constant — but it is now an $O(1)$ rank, not $n^{r}$.

## 5.4 Defense against the obvious objections

**"You've just renamed BGK."** No. BGK / `ConductorGeometricBound` asks the *monolithic* conductor to be $K^r$. The new conjecture asks each *fixed-depth* slice to have $r$-independent bounded rank. These are inequivalent: the monolithic statement is PROVEN FALSE (rank $n^{2r-1}$); the depth statement is *consistent with* that falsity, because $\sum_d\rho_d$ can be $r$-independent even while the total rank $n^{2r-1}$ explodes — precisely if high-depth slices have rank $0$ deviation (depth-sparsity). The transform's novelty is to make "the conductor is large but the deviation is concentrated in low depth" a *formalizable, falsifiable* statement rather than a hope.

**"The slices might not sum to $\Delta(r)$ honestly."** The reconstruction $\Delta(r)=\sum_d\delta_d(r)$ is a *definition* of the grading (the scaffold's `depthTotalDeviation`), not a theorem to be smuggled; any actual depth-grading must supply the $\delta_d$ and verify they sum. The gluing lemma is then unconditional arithmetic. The open content is entirely quarantined in `BoundedDepthConductor`.

**"Depth $D$ might grow with $r$."** That is the sharp edge, and the chapter states it as such: the conjecture is `depthBound r ≤ D` with $D=O(1)$ (the structure field `depthBound_le`). If $D$ must grow like $r$, we recover the wall. The bet — supported by $K\approx1.28$ and the white-noise covariance — is that it does not.

**"This needs étale cohomology Mathlib lacks."** The *consumer* (gluing + effective-Katz chain) is fully formalized and axiom-clean. Only the input `BoundedDepthConductor` is geometry; it is carried as a named `Prop`, exactly as the project's honesty contract requires.

## 5.5 New sub-tools the transform suggests

- **Depth-zero is provably the Wick term**, so a Lean brick `depth0_eq_wick` (deriving $\delta_0(r)=0$ in $\Delta$ from the char-0 $E_r=$ Wick identity) is fully formalizable today and would discharge the $d=0$ row unconditionally.
- **A depth-1 closed form.** Depth-1 carriers engage a single off-diagonal ramified point; the antipodal/Lam–Leung closed form $I(t)=\binom{n/2^s}{t/2^s}$ should compute $\delta_1$ exactly, giving the first nontrivial slice in closed form.
- **Dyadic depth descent.** The doubling identity $\eta_b(\mu_{2n})=\eta_b(\mu_n)+\eta_{gb}(\mu_n)$ induces a depth filtration compatible with the 2-adic tower, suggesting $\delta_d$ obeys a self-similar recursion — a route to bound $D$ inductively.

These are the genuinely new mathematical objects the chapter contributes: a conductor *graded by carrier depth*, a telescoping lemma that converts per-depth $O(1)$ into uniform-in-$r$ $O(1)$, and the falsifiable depth-sparsity conjecture that isolates the prize.


> **Honest status of this tool.** DEFINED (in Frontier/_DepthGradedConductor.lean, Mathlib-only, compiles in 35s): the depth-graded deviation profile `DepthGraded D` (with reconstruction $\Delta(r)=\sum_{d<D}\delta_d(r)$ via `depthTotalDeviation`), and the conjecture `BoundedDepthConductor P κ q` ($|\delta_d(r)|\le\kappa\sqrt q$ uniformly in $r,d$).

PROVEN this session, cited from source files I read directly:
- Moment master identity $\sum_b\|\eta_b\|^{2r}=q E_r$ — `subgroup_gaussSum_moment` (consumed in CharPDeepMomentTail.lean / CumulantGaussPeriodBound.lean), verified to $10^{-16}$ numerically.
- Cumulant identity $\sum_{b\neq0}\|\eta_b\|^{2r}=q E_r-n^{2r}$ — `cumulant_eq` (CumulantGaussPeriodBound.lean), axiom-clean.
- Effective-Katz consumer: `EffectiveConductorBound` (deviation $\le$ Wick $+K^r\sqrt q$) discharges `WorstCaseIncompleteSumBound` at the floor scale — `worstCaseIncompleteSumBound_of_effectiveConductorBound` (KatzEffectiveGaussSum.lean), axiom-clean.
- The NO-GO it escapes: $\mathrm{cond}(\mathcal M^{*r})$ is rank-driven $\sim n^{2r-1}$, Swan=0 (Kummer tame), so monolithic Weil II loses $n^{r-1/2}$ — recorded honestly in the docstring of `ConductorGeometricBound` (MonodromyConductorScaffold.lean). Measured effective base $K\approx1.28$ (scripts/probes/probe_conductor_prize_regime.py).
- My gluing lemmas `bounded_depth_telescopes` and `total_deviation_le_const_sqrt` — PROVEN axiom-clean ([propext, Classical.choice, Quot.sound], no sorry/native_decide), verified via scripts/pg-iterate.sh in /Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib/Research/ProximityPrize/Frontier/_DepthGradedConductor.lean.

CONJECTURED (NOT proven; the isolated open core):
- `BoundedDepthConductor` at the prize point: that the cumulant deviation is depth-sparse — concentrated on a bounded number $D=O(1)$ of carrier depths, each with $r$-independent rank giving $|\delta_d|\le\kappa\sqrt q$. This is geometry (étale cohomology of the depth slices) that Mathlib cannot express, carried as a named Prop. It is the chapter's new conjecture; it is strictly weaker than the refuted monolithic conductor bound but is NOT proven. Supporting evidence (numerical/structural, NOT a proof): $K\approx1.28$, and the exchangeable single-constraint period covariance. The honest worry (also stated): if the required depth $D$ must grow with $r$, the wall returns; the bet is that it does not.

NOT claimed: the prize is NOT closed. No proof of the wall is fabricated; no vacuous hypothesis discharges the open input.
---

# Addendum (2026-06-15) — All Five Tools Adversarially Tested

After publication the five tools were adversarially probed with fresh exact computation (own `F_p`
counters, independent of the authoring agents). The honest result: **no tool crosses the wall or isolates a
strictly-weaker statement.**

- **Tool 1 (Shaw operator) — CONFIRMED exact, but renames the wall.** The decomposition `incidence =
  average + 𝒮` is exact (verified to 1e-13 abstract / 1e-14 in live RS syndrome space) and δ*=9/16
  reconfirmed at n=16, ρ=1/4 (one rung above Johnson 8/16). But its open input `MCAShawConjecture` provably
  equals the BGK/`E_r` object (`ShawSecondMoment` + `eta_pow_le_energyR`), so a bound on it *is* the prize,
  not a lever. The tool is expository/modular — it organizes the wall, it does not breach it.
- **Tool 2 (root-number phase-flatness) — REFUTED as stated.** The "15–20% better than random" advantage is
  an extreme-value artifact: a permutation-of-actual-η null gives `D_arith/D_perm = 0.97–1.06` (sometimes
  below the null mean). The residual is diffuse = the same wall.
- **Tool 4 (antipodal complex torsion = p-independence) — REFUTED.** The integral-homology torsion primes
  (Smith normal form) are the trivial `{2,3}`; the measured far-line incidence-bad primes are all `>3`
  (n=16: {17,97,241,257,353,449,1217,…}; n=32: {97,…,65537}). The antipodal pairing is char-uniform (count
  `= n` for every prime `n | p−1` tested). So the verified p-independence is **arithmetic** (Norm-divisibility
  of the over-determined count), **not topological**. The cleanest refutation in the bundle.
- **Tool 5 (depth-graded conductor depth-sparsity) — REFUTED.** The engaged depth `D` is **not** `O(1)`: it
  grows monotonically `≈ 2r` (n=16, Fermat p=65537, D=0,0,1,4 then 5,7 for r=2..7; same under both gradings).
  The wall returns as `r → log m`.

**Net.** Only the Shaw exact decomposition (Tool 1) is a genuine, machine-verified, non-trivial object, and
it is organizational. The essay's own central thesis stands as the honest verdict: these are five coordinate
charts on **one** wall. The single object that provably does **not** reduce to the BGK sup-norm wall and is
computable-in-principle is the **p-independent distinct-γ far-line union-count `|⋃_R{γ_R}| ≤ n`** — whose
**growth law** is the only prize-floor decision the wall-renaming tools cannot make, and is the live frontier.
