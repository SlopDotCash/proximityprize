# Pinning δ\* in the Proximity-Prize regime — a directions paper (v1, 2026-06-15)

> **Status discipline.** This is an *exploration* document (CLAUDE.md §6A: bold conjectures
> encouraged, including false ones). Nothing here is claimed *proven*. Every "closed-form"
> below is a **conjecture with its open input named**. The companion §6 (Self-shred) attacks
> this paper; §7 (Survivors) is the honest residue; §8 dispatches agents on the residue.
> No closure of the open core is asserted. Refutations route to `DISPROOF_LOG.md`.

---

## 0. The target, stated once, exactly

Solve the Grand-MCA **and** Grand-list-decoding challenges of [ABF26] (ePrint 2026/680) by pinning
one number per rate:

- Code `C = RS[F_p, μ_n·c, k]`, **smooth** domain (`n = 2^μ`, `μ_n ⊊ F_p^*`, `n ∣ p−1`),
  rate `ρ = k/n ∈ {1/2,1/4,1/8,1/16}`.
- Prize regime: `p ≈ n·2^128` prime, `β = log_n p ∈ [4,5]`, `ε* = 2^{−128}`,
  **budget `q·ε* ≈ n`**, **index `m = (p−1)/n = 2^128` fixed**, `n ~ 2^30`, `n ≪ √p` (THIN).
- Window interior `(1−√ρ, 1−ρ−Θ(1/log n))` (Johnson .. capacity−cushion).
- Output: `δ*_C ∈` window with a **two-sided** proof, reducing only to proven math.

**The airtight open core (≈20 equivalent faces collapse here):**
> `M(n) := max_{b≢0 (p)} |Σ_{x∈μ_n} e_p(bx)| ≤ C√(n·log m)`, `C = O(1)`.

`M(n) = house(η)`, where `η = Σ_{x∈μ_n} ζ_p^x` is a **Gauss period**: a generator of the unique
**cyclic** subfield `K_m ⊂ ℚ(ζ_p)` of degree `m = 2^128` over ℚ. The `m` conjugates of `η` are the
period values `η_b`; `Σ_b |η_b|^2 = pn − n^2 ≈ pn` (Parseval) so the conjugates have RMS `√n`, and
`M(n) ≤ C√(n log m)` is precisely the assertion that the **largest conjugate exceeds RMS by only a
`√log m` factor** — the thin-subgroup **BGK / generalized-Paley sup-norm** wall. SOTA (BGK,
di Benedetto, Kowalski) reaches only `M ≤ n^{1−o(1)}`, and its range fails *exactly* at the prize
point `β = 4` (the Burgess barrier `α(r) = 1/4 + 1/(4r²) > 1/4`). A full half-power gap
(`n^{0.989} → n^{0.5}`) at the single hardest point.

**Two exact structural facts that frame everything below:**
1. **2-adic on both sides.** `n = 2^μ` *and* `m = 2^128` are powers of two. So `K_m/ℚ` is a
   **cyclic 2-extension** and `μ_n` is a 2-power subgroup. The whole object lives in the
   cyclotomic 2-tower. (Underused: the BGK literature treats general thin subgroups; the prize
   is the maximally 2-adic case.)
2. **Phase, not magnitude.** `η_b = (1/m) Σ_{χ∈H^⊥} χ̄(b)·τ(χ)`, `|τ(χ)| = √p` *exactly* for
   `χ≠χ_0` (`H^⊥ =` characters trivial on `μ_n`, cyclic of order `m`). So `M(n) ≤ C√(n log m)`
   ⟺ the `m` unit-modulus phases `{χ̄(b)·τ(χ)/√p}` exhibit `√(m log m)` cancellation. The
   magnitudes are pinned (`√p`); **only the phases (arguments of Gauss sums) are open** — exactly
   the [ABF26]-recognised Katz/Rojas-León equidistribution in effective form.

---

## 1. The route-elimination wall (what is provably dead — do not re-propose)

Established axiom-clean / probe-verified in prior waves (cited so the new directions below avoid them):

- **META-THEOREM (`_MetaTheoremSecondOrderFloor.lean`).** *Every* second-order method
  (additive energy any order, L²/Parseval, spectral λ₂, SDP/Delsarte-LP, cumulant-2, Shaw operator)
  caps at `M ≥ n` via `(q·E_r)^{1/2r} ≥ n`. No third route at second order. LP/SDP duals are all
  moment polynomials (confirmed). **Any winner must be (a) b-sensitive, (b) deterministic-archimedean
  (not probabilistic-EVT), (c) genuinely L^∞ (sup not RMS).**
- **Moment depth gate.** Optimal moment `r* ≈ log m ≈ 89` would give `√(n log m)` (Wick value
  lands on the prize form, `C ≈ 0.858`), but the char-0 energy bound `A_r = E_r − n^{2r}/p ≤ (2r−1)‼ n^r`
  transfers to char-p only for `r ≤ r_max = 2log_n p ≈ 8–10`. Gap `r_max ≪ r*` is *the* wall.
- **Height / norm route is dead.** Full block `S={0..n/2−1}` has *exact* norm `2^{n/2−1}`;
  `(2r)^{n/2} ≫ p` always at prize scale ⟹ norm divisibility vacuous (`arklib-407-heightgate-nogo`).
  Structure-aware refinement (c.157/c.159) also a no-go.
- **Burgess / di Benedetto** need `H > p^{1/4}`; prize sits *on* `p^{1/4}` ⟹ exponent → `n^{0.99998}`.
- **Large-sieve / average-over-q REFUTED** (`arklib-407-largesieve-avgq-refuted`): averaging is
  strictly weaker than fixing one prime.
- **Habegger/KU equidistribution** vacuous (discrepancy `m/√p = 2^48 ≫ 1` at fixed `q`).
- **Probabilistic-EVT crown killed:** periods are exchangeable white noise
  (`Cov(η_a,η_b) = −Var/(m−1)`, distance-independent) ⟹ no log-correlation structure.
- **Antipodal/dyadic-squaring tower is only a LOWER bound** (caveat 2026-06-15): the identity
  `e_{2ℓ}(±z) = (−1)^ℓ e_ℓ(z²)` simplifies *only* for `z→−z`–symmetric agreement sets. It captures
  the **odd** worst word (ρ=1/4) fully but misses the **non-symmetric** worst word at ρ<1/4.
- **50 closed conjectures from 12 lenses → 0 survivors** (2026-06-15): 23 secretly-open (= the wall),
  12 reduce-to-Johnson, 14 refuted, 1 trivial. The Johnson radius is the exact closed/open boundary.

**The single honest open question (combinatorial form):** does the binding radius stay *deeply
over-determined* (a p-independent cyclotomic root-count floor, **off** BGK) or cross into
*under-determined* (re-coupling **to** BGK) as `n → 2^30`? Numerics can't decide it; it needs a proof.

---

## 2. The two genuinely-live cracks (everything new must enter through one of these)

**CRACK D — the non-symmetric consecutive-exponent worst-word list.** On true 2-power `n`, the
worst-case window list is empirically **constant at fixed (ρ,η)** (4 at ρ=1/8 for n=16,32; 7 at
ρ=1/16) and the worst word is the **consecutive lacunary** `x^a + x^{a−1} = x^{a−1}(x+1)` at ρ<1/4
(verified n=16: `x^5+x^4`, list 4; this paper's probe reproduces it). The antipodal tower handles
only symmetric (odd) words. **No recursion / closed count exists for the non-symmetric worst word.**
This is *combinatorial*, possibly **off** the BGK char-sum, and would close the **list-decoding
challenge** directly (a genuine "related quantity").

**CRACK P — phase-aware p-adic leverage (Stickelberger / Gross–Koblitz).** The meta-theorem's three
necessary properties (b-sensitive, deterministic-archimedean, L^∞) are *not* contradicted by
**arguments of Gauss sums of 2-power-order characters**, which Stickelberger's theorem pins p-adically
(via base-p digits of the character exponent) and Gross–Koblitz expresses via the p-adic Γ-function.
`H^⊥` is cyclic of order `m = 2^128` ⟹ all characters have 2-power order ⟹ the entire phase structure
is governed by the 2-adic Stickelberger element in `ℚ(ζ_{2^128})`. **No prior wave used the 2-power
order of `H^⊥` to constrain phases** — they treated periods as a generic algebraic integer.

These are the only two doors the route-elimination has not closed. The 25+25 below are organised so
that each either (i) feeds one crack, or (ii) is a candidate *related quantity* we can actually pin.

---

## 3. Twenty-five closed research directions (reduce only to named/decidable math)

Format: **claim** · novelty · feasibility · **honest horn** (which of {LIVE, →Johnson, →wall,
refuted-risk} it most likely hits). Directions are ordered by promise.

**R1 (LIVE/feed D). Non-symmetric agreement-set recursion via the (x+1) factor.** The consecutive
word is `x^{a−1}(x+1)`; `x^{a−1}` is a unit on `μ_n` (a monomial twist, list-invariant), so the worst
word is **equivalent to `1 + x`** evaluated on a coset. Count codewords agreeing with `eval(1+x)`.
Novelty: reduces the whole worst word to the *fixed* binomial `1+x` up to monomial twist — never
isolated before. Feasible: a degree-`k` interpolation count against a *fixed* target. Horn: LIVE.

**R2 (LIVE/feed D). Monomial-twist orbit collapse of the worst-word set.** `Z/n` dilation acts on
words; `x↦ζx` sends `x^a+x^b ↦ ζ^a x^a + ζ^b x^b`. The list is invariant under `x↦ζx` *and* scalar.
Conjecture: every lacunary worst word lies in the orbit of `1+x^d`, `d = gcd`-reduced, giving
`O(μ)` orbit reps to check, all with **constant** list. Decidable per `n`. Horn: LIVE (this *is* the
non-symmetric structure the caveat asked for).

**R3 (→wall, but cheap to settle). Consecutive-word list ⟺ incomplete Kloosterman.** `eval(1+x)` on
`μ_n`: agreement of a degree-`k` poly `g` means `g(x) = 1+x` on a large set; the bad-direction count is
`Σ_x e_p(b(g(x)−1−x))`. For `g` monomial this is a Kloosterman-type sum over `μ_n`. Novelty: ties D to
a *named* sum. Risk: reduces to the wall if the Kloosterman sum over `μ_n` is itself BGK-hard. Settle
the reduction; if it walls, document and drop.

**R4 (closed, candidate related-quantity). Exact `M(n)` for the minimal-`m` prime per `n≤40`.** GPU
oracle already computes δ\* to n=38, p-independent at binding radius. Formalize the *exact* house for
the smallest prize-shaped prime at each `n` (a finite, decidable algebraic-integer computation), giving
an **unconditional finite δ\* table**. Not the asymptotic prize, but a *proven related quantity* with
the right shape. Horn: closed (finite); value = anchors the constant `C` empirically.

**R5 (closed, →Johnson but worth pinning). The B1 below-Johnson count `= n` exactly.** Already
p-independent and proven (`epsMCA_interleaved_eq`). Extend to the *exact* δ\* below Johnson for all
prize rates as a closed table. Horn: →Johnson (but completes the lower bracket rigorously).

**R6 (closed/decidable). Cyclotomic orbit-count growth law `O(n) ∈ {11,18,33,…}`.** The Lam–Leung
backbone `I(n) = 1 + (n/2)·O(n)`; `O(n)` is a *decidable per-n* cyclotomic count (`_wf3D5`). Conjecture
a closed form `O(n) = an+b` (data: 11,18,33 at n=16,24,32 ⟹ not linear — fit a quadratic-in-√ or
2-adic law). Horn: closed if a pattern exists; may be →wall if `O(n)` is itself the period count.

**R7 (closed). Exact `K(n,4) = n/4 − 1` extended to all even-width strata.** The e2=0 over-determined
census has exact closed forms per width (`K=n/4−1` at w=4, knife-edge `K=1` at w=5). Complete the
width→K map as a closed classification. Horn: closed (shallow, decidable); off-BGK by construction but
shallow ⟹ likely →Johnson at depth.

**R8 (closed Fourier-uncertainty). Dyadic rigidity floor `F(t) = n − n/2^⌊log₂ t⌋`.** Proven exact at
n=8 (`UncertaintyTwoPowerSparseFloor.lean`); conjecture it for all 2-power n via the cyclotomic-factor
divisibility argument (elementary, no Lam–Leung). Horn: closed in char-0; **the prize wall is the
char-p transfer** ⟹ honestly →wall for the *prize*, but the char-0 statement is a clean closed win.

**R9 (closed, decidable). Resultant vanishing of the worst-word agreement system at fixed n.** The
agreement of `g` (deg<k) with `1+x` on ≥t points is a determinantal/resultant condition; `Res(...) = 0`
is decidable per n. Conjecture the number of solutions is `≤ poly(n)` and exhibit the closed count.
Horn: closed per-n; asymptotic step needs a structural bound (R2).

**R10 (closed). MacWilliams/Plotkin proxy as a rigorous UPPER bound.** `δ*_far-line = ½ + (1/(2ρ)−1)/n`
is a *proven Plotkin proxy upper bound* (c.4705521894). Pin it as the rigorous ceiling and prove it
equals Johnson at ρ=¼, drops below for ρ<¼. Horn: →Johnson (upper only; can't pin the floor) — but a
*clean two-sided bracket ingredient*.

**R11 (closed group action). Action-orbit `O(1)/|F|` (Chai–Fan 2026/861 Thm 2.1) on the smooth
domain.** Its *unconditional* core (verified sound, Loop41) gives above-Johnson `O(1)/q` for plain RS
on the cyclic domain. Port it fully and check whether the budget `q·ε*≈n` absorbs the `O(1)`. Horn:
closed (unconditional Thm 2.1); but its prize Conjecture 1.1 needs Q1/Q2 ⟹ the *window* part →wall.

**R12 (closed). Threshold-halving (Chai–Fan 2026/858 result (A)) as an unconditional FRI bound.**
Already gives the first unconditional prize-shaped commit-phase bound `(1/q)(2^m)²` by *avoiding*
`ε_mca`. Formalize as a *related quantity* (FRI soundness above Johnson) — genuinely closed. Horn:
closed but **sidesteps** the literal MCA prize (bounds `ε_FRI` not `ε_mca`).

**R13 (decidable). Li–Wan exact `N_fib = C(s,r)/s`.** The fibre count is an *exact closed form*
(Li–Wan, JCTA). Use it to pin the *near-coset* list exactly. Horn: closed; the *far-coset* explosion
band is where the wall hides ⟹ partial.

**R14 (closed). Sperner / antichain ceiling on the bad-scalar family.** `SpernerCeiling.lean` gives a
proven ceiling. Conjecture it is tight at the worst word. Horn: closed; likely →Johnson (combinatorial
ceiling, not the analytic floor).

**R15 (closed). Hasse–Davenport product-relation telescope to pin a single period ratio.** The HD
relations are the *only* algebraic relations among Gauss sums (Katz). Telescope `τ(χ^2)` vs `τ(χ)²`
to reduce `m = 2^128` periods to a chain. Horn: →wall (HD is exactly the relation set that leaves the
phases free — c.4705297066) but the telescope is closed; settle whether it collapses or stalls.

**R16 (closed). Exact `crossCell(n,4) = 3n²/2` extended to a closed `crossCell(n,2r)`.** The dyadic
cross-cell has exact small-r forms. A closed all-r form would pin the DC-subtracted energy `A_r`
recursively. Horn: closed in char-0; **the char-p validity is the wall** ⟹ →wall for prize.

**R17 (closed). Two-sided δ\* bracket gap `= 1/8 = const`.** `DeltaStarPinchBracketD3` proves the
floor/ceiling gap is a *constant* `(s*−(k+1))/n` that does **not** shrink. Pin this as a theorem:
**the bracket alone cannot close** (a proven no-go, valuable). Horn: closed no-go.

**R18 (decidable). Crossing-depth `c*(n)` rate-constant law.** `DecouplingCrossingDepthRateConstant`
proves `c*(n,k) = c*(n)` (constant in rate). Conjecture a closed `c*(n)` (data needed). If `c*(n) =
Θ(1)` then `δ* = (1−ρ) − Θ(1/n)` — *above* the `Θ(1/log n)` cushion ⟹ would **beat** KKH26 ceiling,
contradiction ⟹ `c*(n) = Θ(n/log n)`. Pin which. Horn: decidable; resolves window location.

**R19 (closed). Stickelberger 2-adic valuation table for `τ(χ)`, `χ` of 2-power order.** The p-adic
valuation of `τ(χ)` is `(p−1)·s(a)/(...)` via base-p digit sums — a *closed, computable* function of
the exponent. Tabulate for `H^⊥` (order 2^128). Horn: closed (valuations); feeds CRACK P (but
valuation ≠ argument).

**R20 (closed). Gross–Koblitz argument formula for the 2-power phases.** `τ(χ)/√p = ` explicit p-adic
Γ-product. Closed expression for each phase. Horn: closed *formula*; whether the phases *equidistribute*
(the wall) is not closed by having the formula — but the formula is the right object for CRACK P.

**R21 (closed/decidable). Newton-polygon stratification of the agreement polynomial.** The p-adic
Newton polygon of `g(x) − (1+x)` is decidable and controls the number of `μ_n`-roots by slope. Conjecture
a slope bound forcing `≤ poly(n)` agreement. Horn: decidable per-n; asymptotic = open but *different*
tool than moments (passes the meta-theorem's L^∞ test).

**R22 (closed). Exact δ\* second pin generalization.** `DeltaStarSecondPinF17Maximal` pins
`δ* = 1/4` on a maximal ε\*-interval. Generalize to a closed family of `(p,n,ρ)` exact pins (decidable).
Horn: closed finite pins; not asymptotic, but a *proven related-quantity family*.

**R23 (closed). KKH26 `s=128` ceiling rows via the Thorner–Zaman input as a named hypothesis.**
`effectiveTZ_to_supply` already bridges it axiom-clean; the TZ effective PNT-in-APs is a *known theorem*
(not Mathlib-formalizable, but proven mathematics). Pin the s=128 ceiling *conditionally on a cited
theorem* — closed modulo a literature citation, not modulo open math. Horn: closed-mod-citation
(legitimate per §6 modularity).

**R24 (decidable). GG25 Def 3.1 curve-decodability bricks (B2).** A multi-brick but *fully specified*
formalization (no open input). Closed. Horn: closed (formalization labor, not new math) — a real
related-quantity deliverable.

**R25 (closed no-go, valuable). Prove the moment method *cannot* close at the prize, as a theorem.**
Formalize `r_max = 2log_n p < r* = log m` as an axiom-clean obstruction:
`CleanRegime(n,p) → False` at prize params. Horn: closed no-go (sharpens the wall; prevents wasted
re-tries). Partially done (`_MomentMethodNoGo`); complete the prize-instance.

---

## 4. Twenty-five brand-new mathematical objects / methods (with novelty defense)

Format: **object** · why new · why tractable · why never seen · **what it would buy**.

**N1. The 2-adic Gauss-period house functional `H_2(μ; m)`.** *New:* the house of a generator of the
*cyclic 2-extension* `K_{2^128} ⊂ ℚ(ζ_p)`, studied as a function on the cyclotomic Z_2-tower (Iwasawa
layers), not as a generic thin-subgroup char-sum. *Tractable:* the tower has a `Z_2`-action; layer-by-
layer the period satisfies a norm-compatible recursion (`η^{(μ+1)} ↦ η^{(μ)}`). *Unseen:* BGK literature
never restricts to *both* sides 2-power; Iwasawa theory never asks for the *archimedean house* of layer
generators. *Buys:* if the house is monotone/controlled up the tower, an inductive `√log` bound.

**N2. Phase-transport cocycle of Gauss-sum arguments.** *New:* define `θ_j = arg τ(χ^j)` for `χ`
generating `H^⊥`; the Hasse–Davenport relation gives a *cocycle* `θ_{2j} = 2θ_j + c_j` with `c_j` a
*computable* Stickelberger correction. Study the orbit of `θ` under doubling `j↦2j mod m` (m=2^128). *
Tractable:* doubling on `Z/2^128` is the dyadic odometer — fully understood dynamics. *Unseen:* nobody
has written the Gauss-sum phase as a doubling-cocycle on the 2-adic index. *Buys:* equidistribution of
`{θ_j}` ⟺ the wall, but now as a *dynamical* (b-sensitive, deterministic) statement passing the
meta-theorem's three filters.

**N3. The consecutive-word transfer operator.** *New:* a linear operator `T` on functions on `μ_n`
whose top eigenvalue is the worst-word list size, built from the `(1+x)`-multiplication on the dyadic
tower. *Tractable:* dyadic squaring `e_{2ℓ}(±z)=(−1)^ℓ e_ℓ(z²)` makes `T` block-triangular over the
2-tower; the *non-symmetric* block (the caveat's gap) is a single explicit off-diagonal coupling.
*Unseen:* the tower has only ever been used on symmetric subsets; the operator formalism captures the
non-symmetric part as a perturbation. *Buys:* directly closes CRACK D if the off-diagonal block has
bounded norm.

**N4. Signed-digit additive-energy defect generating function.** *New:* `D(z) = Σ_r A_r^{defect} z^r`
where `A_r^{defect} = E_r^{F_p} − E_r^{char0}` counts *mod-p-only* sparse vanishings; conjecture `D(z)`
is **rational** with denominator a cyclotomic polynomial in `z` determined by `ord_2`-structure.
*Tractable:* the defect carriers are short ±1 relations; their generating function is a constrained
walk on `Z/p`. *Unseen:* the defect has been measured pointwise (r=4 first failure), never assembled
into a generating function. *Buys:* a closed radius-of-convergence = the depth `r` at which char-p
transfer fails = decides if `r*=log m` is reachable.

**N5. Product-formula deficiency bound for sparse cyclotomic values.** *New:* for `f` a ≤2r-term ±1
polynomial, `∏_v |f(ω)|_v = 1`; bound the number of `f` with `|f(ω)|_p ≤ p^{−1}` (i.e. `f(ω)≡0`) by the
*archimedean mass* `∫ |f(ζ)|`-distribution, using that sparse ±1 polys have controlled archimedean
distribution (Salem–Zygmund). *Tractable:* Salem–Zygmund gives `max|f(ζ)| ≍ √(r log n)` for random
signs — a *probabilistic-but-archimedean* input (passes filter (b) if derandomized). *Unseen:* combines
product formula with random-polynomial sup-norm — the height literature uses worst-case heights (the
dead route), not the *typical* archimedean mass. *Buys:* a defect *upper* bound `≤ (#f)·(typical
archimedean)/p` that could beat the worst-case norm wall. **(Risk: derandomization = the open part.)**

**N6. The mod-2 Reed–Muller shadow of the agreement set.** *New:* since `n=2^μ`, identify `μ_n ≅ (Z/2)^μ`
additively via the dyadic FFT; the agreement set of a low-degree poly becomes an `RM(k', μ)` codeword
shadow. *Tractable:* Reed–Muller weight distributions are known closed forms. *Unseen:* the RS↔RM
correspondence on dyadic domains has not been used to *count agreement sets* (only for FFT speed).
*Buys:* a closed agreement-set count from RM weight enumerators — off-BGK and exact.

**N7. Khovanskii-type fewnomial bound over `μ_n` with the *correct* (multiplicative) ambient.** *New:*
the real fewnomial bound was refuted (C20) because it's over ℝ; redo it over the *cyclic group* `μ_n`
where a `t`-term poly has `≤ ?` roots — a *finite-field fewnomial* count. *Tractable:* the dyadic
structure restricts root multiplicities. *Unseen:* finite-field fewnomial bounds exist (Kelley–Owen,
CLP) but not specialized to a 2-power multiplicative subgroup with the dyadic recursion. *Buys:* a
root-count `≤ f(t,μ)` bounding agreement directly. **(Risk: CLP gives n^{0.92} ≫ floor — must beat it.)**

**N8. The "argument increment" L-function.** *New:* `L_θ(s) = Σ_{j} e^{iθ_j} j^{−s}` packaging the
Gauss-sum arguments; conjecture its analytic continuation / functional equation from Hasse–Davenport.
*Tractable:* `θ_j` doubling-cocycle (N2) gives a *self-similar* Dirichlet series. *Unseen:* phases of
Gauss sums have never been packaged into an L-function with its own functional equation. *Buys:*
`M(n) ≤ C√(n log m)` ⟺ a sub-convexity-type bound for `L_θ` — relocates to a *different* analytic
object that might have its own approachable theory.

**N9. Dyadic-tower norm-compatible system of houses.** *New:* `house(η^{(μ)})` as `μ` grows with `m`
fixed — a *projective system* with `Z_2`-norm maps. *Tractable:* Iwasawa's main theorem controls
norm-compatible systems via characteristic ideals. *Unseen:* houses (archimedean) are never studied in
the Iwasawa (p-adic) tower. *Buys:* if the char. ideal forces house growth `O(√μ) = O(√log n)`, that's
*exactly* the `√log m` shape (m fixed, so `√log m` is a constant — wait: the relevant growth is in the
*combined* `√(n log m)`; the tower controls the `n`-direction). *Buys:* the n-dependence inductively.

**N10. The cross-parity coupling constant `κ`.** *New:* the single number measuring how much the
non-symmetric (mixed-parity) worst word's list exceeds the symmetric tower prediction; conjecture `κ`
is an *absolute constant* (independent of n). *Tractable:* `κ = 3` measured at n=16 (3 of 4 list elts
escape the tower). Measure across 2-power n; if constant, the non-symmetric list is `tower + κ = O(1)`.
*Unseen:* the caveat *identified* the gap but never quantified it as a constant. *Buys:* closes CRACK D
if `κ = O(1)` provably (an absolute additive correction to the tower).

**N11. Determinant-method point count for `{f : f(ω) ≡ 0}`.** *New:* Bombieri–Pila / Heath-Brown
determinant method counts integer points on `f(ω)=0` of bounded height in *few* auxiliary curves.
*Tractable:* the determinant method gives bounds *polynomial in the height's log* — and sparse ±1 polys
have height `O(r)`. *Unseen:* the determinant method has been applied to char-sum *moment* counts only
asymptotically; never to the *exact* sparse-vanishing defect at fixed depth. *Buys:* a defect bound
that scales with `log(height)` not `height` — could dodge the `(2r)^{n/2}` norm wall. **(Risk: needs
the right auxiliary variety; may hit the same height.)**

**N12. The B_h[g]-set energy of `μ_n` mod p.** *New:* treat `μ_n ⊂ F_p` as a `B_h` set; the additive
energy defect = failure of the `B_h` property mod p; conjecture `μ_n` is `B_h` mod p up to `h = r_max`
exactly. *Tractable:* `B_h` failure = a sparse relation = the same defect carriers, but the `B_h`
framework has *threshold theorems*. *Unseen:* `μ_n` as a `B_h` set mod p, with `h` tied to moment depth,
is a new framing. *Buys:* a *threshold* `h*` for `B_h`-ness = the depth the moment method reaches. **
(Risk: `h* = r_max` is exactly the wall — settle whether `B_h` theory gives anything beyond it.)**

**N13. Cyclotomic-unit regulator obstruction.** *New:* the periods `η_b` generate a subring; their
*multiplicative* relations (cyclotomic units) impose a regulator lower bound forcing the house up or
down. *Tractable:* cyclotomic-unit regulators have closed forms (analytic class number formula).
*Unseen:* using the *regulator* (not the norm) to bound the house. *Buys:* a *multiplicative*
constraint orthogonal to the additive energy — might pass where additive (norm) failed.

**N14. The dyadic odometer equidistribution kernel.** *New:* doubling `j↦2j mod 2^128` on the index is
the dyadic odometer; its unique invariant measure is Haar; quantify the *discrepancy* of `{χ̄(b)τ(χ^j)}`
under the odometer using the *finite-depth* (128-step) orbit. *Tractable:* finite-depth odometer
discrepancy is computable (no `q→∞` limit needed — dodges the Habegger vacuity). *Unseen:* the
finite-depth (m=2^128, not asymptotic) odometer discrepancy is exactly the *effective* equidistribution
the prize needs, never isolated. *Buys:* an *effective* (fixed-m) discrepancy bound = the wall in
finitary form, possibly amenable to direct 2-adic estimation.

**N15. Restriction/decoupling for the `μ_n` exponential sum with multiplicative weights.** *New:*
Bourgain–Demeter decoupling for the *multiplicative* curve `{(x,x²,…) : x∈μ_n}`. *Tractable:* the dyadic
subgroup is a perfect "well-separated" set for decoupling. *Unseen:* decoupling is used for additive
(arithmetic-progression) frequencies, not multiplicative subgroups. *Buys:* an `L^{2r}` bound — **but
likely reduces to moments** (filter (c) fails: decoupling is L^p = RMS). Assess and probably drop.

**N16. The "two-value normalizer" exact spectral correction.** *New:* the EVT crown died because of a
"two-value normalizer spike" matching all bulk moments but differing in the tail. *Turn the bug into the
tool:* model the periods as bulk-Gaussian *plus* an explicit two-point atom; the atom's mass is a closed
function of `(n,m)`. *Tractable:* a two-component mixture has closed tail. *Unseen:* the spike was
treated as an obstruction, never as a *computable* correction term. *Buys:* the exact tail (= house)
as `bulk + atom`, with the atom giving the `√log m` deviation. **(Risk: the atom mass IS the wall.)**

**N17. Galois-module structure of the bad-scalar set.** *New:* the bad scalars form a `Gal(K_m/ℚ) =
Z/2^128`-set; decompose it into Galois orbits and bound each orbit's contribution. *Tractable:* a
cyclic 2-group has a known subgroup lattice (a chain). *Unseen:* the bad set has been counted, never
*Galois-decomposed*. *Buys:* the bad-set size as a sum over the 128-element subgroup chain — possibly
telescoping.

**N18. The p-adic L-function of the period.** *New:* attach a Kubota–Leopoldt-style 2-adic L-function
to the cyclic 2-extension; its special values control the period's arithmetic. *Tractable:* 2-adic
L-functions of cyclotomic 2-towers are constructed (Iwasawa). *Unseen:* connecting the *archimedean
house* to a *2-adic L-value* via a comparison (Coleman map). *Buys:* a transcendence/comparison bound —
speculative but genuinely novel cross-place input.

**N19. Sidon-defect threshold via the dyadic FFT.** *New:* `μ_n ≅ (Z/2)^μ`; the Sidon (B_2) defect is
the number of additive quadruples; the FFT diagonalizes it. *Tractable:* `E_2(μ_n) = 3n²−3n` exactly
(proven). *Unseen:* using the *FFT-diagonal* to get *all-r* energy from the `r=2` case via a closed
recursion on `(Z/2)^μ`. *Buys:* the full energy tower from the group structure (off the analytic wall)
— **if** the recursion is char-p valid (the wall again, but via a *group-theoretic* not analytic route).

**N20. The "list = fixed point" categorification.** *New:* the worst-case list is the fixed-point count
of the dyadic-squaring endofunctor on agreement sets; conjecture a *Lefschetz-type* trace formula giving
the count as an Euler characteristic. *Tractable:* the squaring map on `(Z/2)^μ`-indexed agreement sets
has computable fixed points. *Unseen:* a categorical/Lefschetz framing of the list. *Buys:* a closed
fixed-point count = the list, *including* non-symmetric sets (the trace sees all of them). Speculative
but directly targets CRACK D's gap.

**N21. Effective Chebotarev on the splitting field of the defect polynomials.** *New:* the defect
carriers `f(ω)≡0 mod p` correspond to `p` splitting in a specific way in the splitting field of `f`;
effective Chebotarev (under GRH, or unconditional log-free) bounds the density of such `p`. But we *fix*
`p` — so invert: for fixed `p`, count `f` whose splitting field has `p` with that Frobenius. *Tractable:*
the splitting fields are abelian (cyclotomic) ⟹ Frobenius is explicit. *Unseen:* the inversion (fix p,
vary f) is the *explicit-code* direction nobody took. *Buys:* defect count via explicit Frobenius —
**closed because abelian** (no GRH needed for cyclotomic fields!). **Most promising N-item.**

**N22. The dyadic Mahler measure of the agreement system.** *New:* `m(g − (1+x))` over `μ_n` as a
*finite* Mahler measure (product over `μ_n` of `|g−(1+x)|`); relate to the list via Jensen. *Tractable:*
finite Mahler measures over roots of unity are resultants (closed). *Unseen:* finite/cyclic Mahler
measure as a list-counting device. *Buys:* `list ≤ ` a resultant-height bound (closed per n).

**N23. Quadratic-form rank of the energy matrix mod p.** *New:* `E_r` is `‖A_r‖` for an explicit
0/1 matrix `A_r` (incidence of sparse sums); its *rank mod p* drops exactly when the defect appears.
*Tractable:* rank-mod-p is decidable; conjecture full rank up to `r_max`. *Unseen:* the *rank* (not the
norm) of the energy incidence matrix as the defect detector. *Buys:* a *linear-algebra* (not analytic)
defect threshold = decidable per n, possibly with a closed rank formula from the dyadic structure.

**N24. The interleaved (m-fold) joint-agreement contraction.** *New:* the list-decoding challenge is for
`C^m`; the joint agreement of `m` functions is far more constrained than single (each extra function
multiplies constraints). Conjecture the joint list is `single-list / |F|^{m−1}`-suppressed, making the
budget trivially met. *Tractable:* joint agreement = intersection of agreement sets, a closed
inclusion–exclusion. *Unseen:* the *m-fold suppression* has not been exploited — prior work treats
`C^m` via the single-code house. *Buys:* if the m-fold suppression is real, the list-decoding challenge
closes *without* the house bound. **Genuinely could bypass the wall.**

**N25. The "phase budget" conservation law.** *New:* a conjectured identity `Σ_b arg(η_b)·w(b) = 0` for
an explicit weight `w`, expressing that the Gauss-sum phases *cannot all align* (a conservation law from
the trace `Σ η_b ∈ ℤ`). *Tractable:* `Σ_b η_b = ` an explicit small integer (a Gauss-sum trace); the
imaginary part vanishes ⟹ a phase constraint. *Unseen:* using the *integrality of the trace* as a phase
conservation law to cap the maximum phase alignment = cap the house. *Buys:* a *deterministic
archimedean L^∞* constraint (passes all three filters) — the maximum `|η_b|` is limited by the phases'
forced cancellation in the integer trace.

---

## 5. Pre-emptive honest scoring (before the shred)

| Tier | Items | Verdict |
|---|---|---|
| **Genuinely live, feeds a crack** | R1, R2, N3, N10, N21, N24, N25 | not yet reduced to wall |
| **Closed/decidable, related-quantity wins** | R4, R5, R11, R12, R22, R23, R24, N6, N22 | proven sub-results, not the prize |
| **Closed no-go (sharpens wall)** | R17, R25, N1(partial) | valuable negative |
| **Likely →wall on inspection** | R3,R6,R8,R15,R16,R19, N4,N7,N12,N13,N14,N16,N18,N19,N23 | the BGK core in disguise |
| **Likely →Johnson** | R7,R10,R13,R14, N15 | caps at/below Johnson |

The honest expectation: **R1/R2/N3/N10 (CRACK D) and N21/N24/N25 (phase/interleaving) are the only
items that can survive a serious attack.** Everything else is a related-quantity deliverable or a
disguised wall. §6 now tries to kill even these seven.
