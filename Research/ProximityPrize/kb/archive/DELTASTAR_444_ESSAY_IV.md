> ## ⚠️ CORRECTION BANNER (read first — supersedes the optimistic framing below)
> A parallel rigorous push (on-issue #444 comment 4707955906, and `arklib-444-evenodd-descent.md`)
> established that **G1 ≡ the wall**: at the binding radius the window-list count equals the **dyadic
> lacunary subset count** `#{T⊆μ_n : e₁..e_{n/8}(T)=0}`, whose **char-`p` validity is the
> BGK/additive-energy wall** (char-0 = coset count, CLOSED; char-`p` defect at `n=2^30` = the open
> core). So the descent does **NOT** bypass the wall — it **reunifies** the list-decoding side with the
> sup-norm/BGK side onto **one** object. §2 below ("`M(μ)` is off the wall") is therefore an
> **OVERCLAIM** and is retracted; `M(μ)`'s `p`-independence to `n=64` is "defect = 0 at accessible
> scale," NOT a scale-free bound. The **non-retracted** contributions of this essay are: the `A+Z`
> identity + spine (formalized, `Sweep_A41`), the rigorous **Johnson-packing kill** (§5, consistent with
> G1≡wall), the level-set value `L(x^a+1)=n/gcd(a,n)` (= the char-0 closed coset value), and the
> **reunification insight** (the LD side, via `A+Z`, lands on the same lacunary/BGK object). No closure.

# Essay IV — The descent recursion: converting the grand list-decoding challenge into one per-level combinatorial bound

*Round 2 of the loop (2026-06-15, successor to Essays I→II→III). Essay III left ONE live object —
the even/odd dyadic descent for explicit 2-power RS window list-decoding — with two open gaps
(G1 uniform branching, G2 worst-word-low-weight). This round does not re-generate directions; it
**sharpens the one live object into a theorem-shaped reduction**, formalizes its rigorous core
axiom-clean, confirms its novelty against the literature, and re-shreds. No closure is claimed; the
honest output is that the prize's list-decoding half now reduces to a single, finite-per-level,
`p`-independent, combinatorial quantity `M(μ)`.*

---

## 0. What changed this round (the load-bearing facts)

1. **Literature lock (verified, multi-source).** "Bounded (poly/constant) worst-case list size for
   *plain explicit* Reed–Solomon on the 2-power multiplicative domain `μ_n`, strictly beyond the
   Johnson radius `(1−√ρ, 1−ρ)`" is **genuinely open**. BGM/Guo–Zhang/AGL need *random* points;
   folded/multiplicity/subcode results need *alphabet blow-up*; Shangguan–Tamo's explicit
   beyond-Johnson is only list-size 2–3 just past Johnson; BKR's structured bad words are *additive*
   domains *below* Johnson. BCIKS 2025/169 states the list-decoding radius of RS "is wide open" and
   that improving it is a **prerequisite** for proximity-gap results beyond Johnson — i.e. the
   list-decoding side *is* the gate. Crites–Stewart 2025/2046 **disproved** the up-to-*capacity*
   conjectures (DEEP-FRI, BCIKS correlated-agreement, WHIR mutual-correlated-agreement), so the
   target is necessarily the **sub-capacity band** `(1−√ρ, 1−ρ−Θ(1/log n))` — exactly the prize
   window. The descent attacks exactly this and nothing in the literature subsumes it.

2. **The `A + Z` reformulation (formalized, axiom-clean).** The per-fibre trichotomy
   `2A + B` collapses (since `Q=0 ⟹ P²=yQ²`, giving `Z := #{P²=yQ²} = A + B`) to
   `agreement(f,u) = A + Z`,  `A = #{y: P=Q=0}`,  `Z = #{y: P(y)² = y·Q(y)²} = #{R = 0}`,
   `R(y) = P² − yQ²`,  `P = F − u_e`, `Q = G − u_o`.
   `A` is the **symmetric joint (interleaved) agreement** — what the campaign's antipodal `S=−S`
   tower already captured. `Z` is the **zero-count of the explicit quadratic form `R`** — the new,
   non-symmetric content. (Lean: `Sweep_A41_DescentAZForm.lean`, `fiber_agreement_AZ`,
   `descent_identity_AZ`, `Z_eq_card_quadform`, all `[propext, Classical.choice, Quot.sound]`.)

3. **The descent spine (formalized, axiom-clean).** For an **even word** (`u_o ≡ 0`) the even
   codewords `f = F(x²)` (`G ≡ 0`) agree on `μ_n` at exactly **twice** their level-`μ−1` agreement
   with `u_e`: per fibre the count is `2·⟦P=0⟧` (Lean: `fiber_agreement_even`). Hence the even
   codewords **biject** with the level-`μ−1` window list of `u_e` at the **same rate** and **same
   relative radius `τ`**. This is the rigorous backbone of "branching = 1 along the spine."

---

## 1. The central reduction (this round's main contribution)

Let `Λ(μ)` be the worst-case window-list size for explicit 2-power RS on `μ_{2^μ}`, at fixed rate
`ρ` and window radius `τ ∈ (ρ + Θ(1/μ), √ρ)` (agreement fraction; "beyond Johnson" is
`τ < √ρ`-side, i.e. radius `> 1−√ρ`). Define the **per-level mixed count**

> `M(μ) = max over words u of #{ codewords f with G ≢ u_o (non-spine) and agreement(f,u) ≥ τ·2^μ }`.

**Theorem (Descent Recursion — even-word case, sound; general case modulo the odd leg G1′).**
For an even word `u` (`u_o ≡ 0`):
`#list(u, μ) = #spine(u) + #mixed(u) = #list(u_e, μ−1) + #mixed(u) ≤ Λ(μ−1) + M(μ)`,
where `#spine = #list(u_e, μ−1)` is the level-`μ−1` window list of the even half (same `ρ`, same
`τ`), via the spine bijection (fact 3). Taking the max over even worst words,
`Λ_even(μ) ≤ Λ(μ−1) + M(μ)`. Unrolling from a small base level `μ₀`:

> **`Λ(μ) ≤ Λ(μ₀) + Σ_{j=μ₀+1}^{μ} M(j)`.**

**Consequences (the whole prize-list-challenge, reduced to `M`):**
- **`M(j) ≤ C` (constant)** ⟹ `Λ(μ) ≤ Λ(μ₀) + C·μ = O(log n)` — a **polynomial (logarithmic)
  worst-case list for explicit 2-power RS beyond Johnson**. This *is* the grand list-decoding
  challenge for this family.
- **`M(j) = 0` for `j ≥ μ₁`** ⟹ `Λ(μ) = O(1)` — a **constant** window list (the strongest form;
  matches the empirical `Λ = 4` plateau at `ρ=1/8`, `n=16,32`).
- **`M(j) → ∞`** ⟹ the floor is **refuted** (a publishable negative on the explicit-RS side).

The reduction is exact and `p`-independent. The **only** open input is the per-level mixed count
`M(μ)`. This is the honest, complete reframing: *prove `M(μ) = O(1)` and the explicit-2-power-RS
list-decoding grand challenge falls.*

**Critical deflation (read before celebrating).** `Λ(μ) = Λ(μ−1) + M(μ)` is an *exact
decomposition* (the spine is literally the level-`μ−1` list; `M(μ)` is the increment). It is **not,
by itself, a difficulty reduction**: `M(μ) = Λ(μ) − Λ(μ−1)` is the increment, and I have **no
sub-Johnson bound for it** — the best independent bound on `M(μ)` is the pairwise-packing argument
of §5, which reaches only `τ ≤ √ρ + ρ/2` (Johnson + ε). So the decomposition's value is **structural**
(it is exact, `p`-independent, localises the increment to `G≢0` members on a one-parameter
mid-exponent family, and proves the spine = level-down list), **not yet a closure**. A closure needs
a bound on `M(μ)` that is *not* packing — one that exploits the self-similarity (`u_e` is the same
family one level down) to compound information across levels. Whether such a bound exists is decided
empirically by whether `M(μ) = 0` (the observed `L*` plateau is all-spine) or `M(μ) > 0` and growing.

---

## 2. [RETRACTED — see correction banner] "Why `M(μ)` is off the BGK wall"

**This section is an OVERCLAIM and is retracted.** The argument below ("`M(μ)` is `p`-independent and
combinatorial, hence off the wall") confuses the `p`-independence of the *descent identity* (true —
the agreement count is an exact combinatorial functional) with the `p`-independence of the *list
size at prize scale* (FALSE). The rigorous push shows the binding-radius list size equals the dyadic
lacunary count, whose char-`p` validity at `n=2^30` **is** the BGK/additive-energy wall. The
observed `p`-independence to `n=64` is "the char-`p` defect vanishes at accessible scale," not a
scale-free bound. The descent reunifies the list side onto the wall; it does not sit off it. The
text below is preserved only to mark the exact mistake:

> ~~`M(μ)` is `p`-independent (verified across primes); combinatorial / finite-per-level; not a
> reduction to Johnson because the recursion operates inside `(ρ,√ρ)` where Johnson is silent.~~
> — *The flaw: "finite-per-level and `p`-independent at accessible `n`" does not imply "bounded as
> `n→2^30`"; the per-level count's growth is exactly the char-`p` lacunary defect = the wall.*

---

## 3. The exponent–degree dichotomy (why `x^{n/4}+1` is the worst word)

For an even monomial word `u = x^{2c}` (so `u_e = y^c`, `u_o = 0`), a mixed codeword `(F,G)`,
`G ≢ 0`, contributes `Z = #{y∈μ_N : (F−y^c)² = y·G²}` = zeros in `μ_N` of the **genuine polynomial**
`R(y) = (F−y^c)² − y·G²`, whose degree is `2·max(deg F, c, deg G) + [odd] = 2c` (for `c ≥ k/2`).
By Lagrange, `Z ≤ min(2c, N)`. Then:

- **Small `c`** (low exponent) or **`c` near `N`** (i.e. `x^{−small}`): `deg R = 2c` or the wrap-around
  degree `2(N−c)` is too small to reach the window threshold `≈ 2(τ−ρ)N` for `G≢0` members ⟹
  `#mixed = 0` ⟹ **branching = 1 exactly** ⟹ descent closes (this is the regime where G2 holds and
  the list is provably the spine).
- **Mid exponent `c ≈ N/2`** (`a = 2c ≈ N = n/2`; the family `x^{n/4}+1` sits at `a = n/4`,
  `c = n/8`, `deg R = n/4`, right at the borderline `Z_max = n/4` versus required `≈ 2(τ−ρ)N`):
  the only regime where `#mixed` can be positive. **This is why the empirically-observed worst word
  is `x^{n/4}+1`** — it is the unique exponent class that maximises `deg R` *inside* `μ_N` while
  staying in the window. The dichotomy is `deg R = 2·dist(c, {0,N})`, peaking at mid-exponent.

So the open content of `M(μ)` is concentrated on a **one-parameter family** (mid-exponent
self-similar words), not all `2^{O(n)}` words. This is a dramatic narrowing of the open question.

---

## 4. Three alien / creative angles on `M(μ) = O(1)`

**(α) The descent as a depth-`μ` tree automaton.** A list member is a path down the 2-tower:
at each level it is either the (unique) spine child or one of `#mixed` branch children. The list size
is the number of leaves. Branching `b = 1 + #mixed` per node over `μ = log n` levels gives
`b^{log n} = n^{log b}` leaves. `#mixed = O(1)` ⟹ `b = O(1)` ⟹ **poly(n)** leaves; `#mixed = 0`
eventually ⟹ `O(1)`. The grand challenge is *exactly* "the descent tree has bounded branching."
This is a finite-state property of the squaring map, not an analytic one.

**(β) Sign-pattern injection.** A mixed member's single-fibre agreements pick one of `±x` per fibre,
i.e. a sign pattern `ε : T → {±1}` with `F(y) − y^c = ε(y)·x_y·G(y)` on `T = {R=0}`. Two mixed
members sharing many `T`-points force `F − F' = √y·(εG − ε'G')` — an even polynomial equal to an
odd one on a large set, which (by the descent identity applied to the *difference*) collapses unless
`εG = ε'G'`. This is a **second-order descent on differences**: it should bound `#mixed` by the
number of admissible sign patterns consistent with a bounded-degree polynomial constraint — a
Prouhet–Tarry–Escott / vanishing-sum-of-roots count, which is `O(1)` for bounded degree. *This is the
most promising concrete route to G1* and is `p`-independent.

**(γ) Single-step suffices.** The recursion needs branching bounded *per step*; by induction one only
has to prove the **single-step** bound `Λ(μ) ≤ Λ(μ−1) + O(1)`. So all proof effort collapses onto one
clean lemma — the mixed-count bound at a *generic* level — not an `n`-uniform global estimate.

---

## 5. Self-shred (attack §1–§4)

- **§1 recursion, odd-word leg (G1′).** The spine bijection is proven only for **even** words. A
  general/odd worst word has even codewords with their *own* `Z`-term (`(F−u_e)² = y·u_o²`), so the
  spine is not a clean level-down list. **Honest gap:** the recursion is sound for even words (incl.
  the observed worst family `x^{n/4}+1`), conjectural for odd words. *Mitigation:* the adversarial
  probe is testing whether any odd/general word beats the even worst; if not, `Λ = Λ_even` and the
  gap is vacuous. **Status: open sub-gap, empirically testable.**
- **§1 "`M(μ)=O(1)` reduces the prize."** True for the **list-decoding** half only. It does **not**
  touch the MCA (`δ*`) half directly; the LD⇒MCA collapse (ABF26 §5, B4) is a *separate* open
  reduction. Claiming this closes "the prize" would be larp. **Honest:** it closes (conditionally) one
  of the two grand challenges — the one BCIKS names the prerequisite.
- **§3 dichotomy "`#mixed=0` for low exponent".** The degree bound `Z ≤ 2c` bounds the agreement of
  *one* member, hence forces `#mixed=0` only when the *maximum possible* `Z` is below threshold —
  rigorous. But at mid-exponent it bounds nothing about the *count*; §3 explains *where* the open part
  lives, it does not bound it. **Not a closure — a localisation.** (Stated correctly above; flagging
  so no later reader over-reads it.)
- **§4(β) sign-pattern — KILLED (reduces to Johnson; rigorous).** I carried the route to the end.
  Two distinct mixed members `(F,G),(F',G')` on their common agreement set satisfy
  `(F−F')² = y(G−σG')²`, `σ = εε' ∈ {±1}` — *again a descent relation*. Since
  `deg[(F−F')² − y(G−σG')²] ≈ k < N` and a perfect square cannot equal `y·(square)` as a
  polynomial identity (LHS even degree, RHS odd degree, so both must be `0`), any overlap `> k`
  forces `F=F', G=±G'`. Hence **distinct mixed members pairwise overlap in `≤ 2k` points of `μ_N`.**
  Double-counting `L` members of size `≥ θ = (2τ−ρ)N` with pairwise intersections `≤ 2k` yields a
  bound on `L` **only when `θ² > 2kN`, i.e. `τ > √ρ + ρ/2`** — which is *just past* the Johnson
  radius `√ρ` and lies **outside the prize window** `τ < √ρ`. So the second-order-descent /
  sign-pattern engine is a **pairwise-packing bound = Johnson + ε**; it recovers Shangguan–Tamo's
  "slightly beyond Johnson, list 2–3" and **nothing more**. By the prize ground rules (discard
  anything that reduces to Johnson), this route is **dead for the full window**. *The descent's
  per-level structure does not, by itself, escape Johnson via packing.*
- **§4(α) tree.** Correct as a *consequence* of bounded branching, but bounded branching **is** the
  open input; the tree picture adds intuition and the `n^{log b}` accounting, not a bound.

**Meta:** nothing here closes the open core. What is *new and solid* is (i) the exact `A+Z`/spine
identities (formalized), (ii) the exact **reduction of the explicit-2-power-RS list challenge to one
`p`-independent per-level count `M(μ)`**, and (iii) the **localisation** of `M(μ)`'s open part to a
one-parameter mid-exponent family. The rest are leads.

---

## 6. Survivors and dispatch (post-kill)

The §5 kill removed the packing route. What remains:

- **S-IV-1 — the decisive empirical fork (→measure now).** Is the observed worst-case `L*` plateau
  (`=4` at `ρ=1/8`, `n=16,32`) **all-spine** (`M(μ)=0`, every list member is an even codeword that
  descends) or does it contain **mixed** (`G≢0`) members? This is the single most informative
  measurement, because:
  - If **all-spine** (`M=0`) at the worst word for `n=16,32,64`: then `Λ(μ)=Λ(μ−1)` exactly, and the
    list is constant **= the base-level list, by induction** — and the remaining task is to *prove
    `M(μ)=0`*, i.e. that **no `G≢0` codeword reaches the window** at the self-similar worst word. The
    degree dichotomy (§3) shows `M=0` is *not* forced (mid-exponent allows `Z` up to `n/4 ≥`
    threshold), so this would need the self-similarity argument — but it is a clean, finite,
    `p`-independent target, and `M=0` is *much* stronger evidence than `L*` constancy alone.
  - If **mixed members are present and `#mixed` grows with `n`**: the floor is **refuted** for the
    explicit family — a publishable negative resolving the open question on the explicit-RS side
    (consistent with Crites–Stewart killing the *capacity* conjectures; this would extend a negative
    into the sub-capacity band for `μ_n`).
  (Background agent "branching mechanism" is computing `#EVEN` vs `#MIXED` and `max B` at the worst
  word, `n=16,32`; the "worst-family" agent is extending to `n=64`.)
- **S-IV-2 — non-packing bound on `M(μ)` (→prove, only if S-IV-1 says `M` bounded).** The ONLY route
  to a full-window closure: a bound on `M(μ)` that compounds the self-similarity across levels rather
  than packing within one level. No such argument is in hand; it is the genuine open mathematics.
- **S-IV-3 (formalized, ✓).** `A+Z` identities + even-spine (`Sweep_A41`, axiom-clean). **Done.**
- **S-IV-4 (no-go, sharpens wall).** §5 kill: second-order descent = Johnson packing, dead for the
  window. The MCA `δ*` half remains the BGK wall; `M(μ)` does not route to it. Record both.

**Honest disposition.** Net new this round: (i) the exact `A+Z`/spine identities (formalized,
axiom-clean); (ii) the exact `p`-independent decomposition `Λ(μ)=Λ(μ−1)+M(μ)` localising the open
increment to mixed members on a one-parameter family; (iii) a **rigorous kill** showing the
second-order-descent/packing engine reaches only Johnson+ε, so the descent does **not** escape
Johnson by elementary packing. **No closure.** The challenge now rests on a single, sharply-posed,
empirically-checkable fork (S-IV-1) and, if it survives, a genuinely-new non-packing argument
(S-IV-2). The loop continues on the empirics, which are the arbiter.
