# SYNTHESIS: the prize = explicit-RS list-decoding past Johnson — full 16-angle army result (#444)

The RS-list-decoding army (16 angles, 27 agents, 4M tokens, cross-verified by independent engines + closed forms
+ external papers) attacked the prize in its TRUE reduced form. Verdict: **poly-supported (floor likely true), not
proven**. The map is now coherent and sharp.

## CLAIMED RESULTS (per-item status; item 2 is an engine observation, item 3 is corrected below)

1. **The reduction is EXACT:** proximity-gap FLOOR ⟺ explicit-RS list-decoding past Johnson (BChKS 2025/2055,
   soundness a < q/(2n)); the in-tree super-code/far-line bridge makes it √-free (q·ε* = n). So the prize IS the
   list-decoding problem.
2. **Observed, not proved: the tested worst-case word is 2-SPARSE** (affine-line/dilation, x^a+γx^b):
   listscan/sparsescan max coincides at a 2-sparse word at every tested (n,k,δ). This is a finite search result,
   not a universal worst-word theorem.
3. **ANTIPODAL-TOWER recursion — CORRECTED (2026-10-28 audit, T124).** The earlier claim that the worst-word list
   is self-similar, `L*(μ_n,k,t) = L*(μ_{n/2}, ⌊k/2⌋, ⌈t/2⌉)`, with the list "EXACTLY CONSTANT in n" at a fixed
   dyadic window ratio, is **false as stated**; the earlier "brute-verified n≤16, partial n=32" label cannot have
   covered all received words. Counterexample (exhaustive, evidence
   `docs/audits/repository-review-2026-10-28/kb41-worst-list-recursion-counterexample.json`): over `F_65537`
   (`65537 > 8^4`), `μ_8` with domain `[1,16,256,4096,65536,65521,65281,61441]`, `k=2`, `t=3`, received word
   `[1,0,0,0,1,1,65281,61441]` has affine-codeword list exactly `{0, 1, X}` (all 28 interpolation pairs
   enumerated), so `L*(μ_8,2,3) ≥ 3`; the half problem `(n,k,t)=(4,1,2)` has worst list exactly `2` (distinct
   constants have disjoint agreement sets of size ≥ 2 out of 4). Same rate `1/4`, `3 > 2`. (Over `F_17` the analogous
   word has list `4`.) Arbitrary words and odd polynomial components break the claimed bijection.

   What squaring *does* give (char ≠ 2, `n` even, `x ↦ x²` is 2-to-1 from `μ_n` onto `μ_{n/2}`):
   - **Exact restricted relation (even words, even subcode).** If `u = v(x²)` is an even word and we only count even
     codewords `c = d(x²)` with `deg d < ⌈k/2⌉`, then `agr(c,u) = 2·agr(d,v)`, so this even-subcode list of `u` at
     threshold `t` equals the list of `v` in `RS[μ_{n/2}, ⌈k/2⌉]` at threshold `⌈t/2⌉`.
   - **One-sided worst-word bound.** Lifting `d ↦ d(x²)` is injective, so
     `L*(μ_n,k,t) ≥ L*(μ_{n/2}, ⌈k/2⌉, ⌈t/2⌉)`. No reverse inequality (and hence no equality or n-constancy of the
     worst-word list) is proved; the counterexample (`k=2`, where `⌊k/2⌋ = ⌈k/2⌉ = 1`) shows the reverse fails.

## ALL "import-from-known-capacity-results" ROUTES ELIMINATED (rigorous, domain-blind)

- **Subspace-design derandomization: DEAD** (caps at Johnson; τ-parameter domain-blind, requires folding depth
  m≥d; plain RS has m=1). `derand-subspace-route-DEAD-caps-at-johnson.md`.
- **GG25 extension: DEAD** (caps at Johnson; same τ; radius 1/n−(ρ+ℓ)/r).
- **FRS folding: DEAD** (Folding Decorrelation Barrier, exact algebraic identity).
- **Guruswami–Sudan past Johnson: DEAD** (μ_n cyclic/dyadic structure REMOVES interpolation room).
- **Curve-decodability (GG25): caps strictly below Johnson** for plain RS, no domain dependence.
- **Literature sweep: NO published result** reaches past Johnson for explicit plain RS over a smooth subgroup; the
  2026 survey (arXiv:2603.03841) lists this as **Open Question #1 (p.85), verbatim the prize, recognized open Mar-2026.**

## THE BEST CONJECTURE (two-sided anchored): the EXPLICIT-RS WINDOW LIST LAW

For RS[μ_n,k], η := (1−ρ)−δ (distance below capacity), the worst-case list over ALL words is
> **L*(δ) = 2^{Θ_ρ(1/η)}**, attained by a 2-sparse word, with `log₂(L*)·η → C(ρ)` (measured C(1/16)≈0.23,
> C(1/8)≈0.27, C(1/4)≈0.43).

Consequences: for η ≥ c/log n (window interior), **L* = 2^{O(log n)} = poly(n)** ⟹ explicit smooth RS list-decodes
past Johnson (floor HOLDS). **KKH26 / ePrint 2026/782 provides the matching LOWER bound** — so the law is two-sided.
My independent broad-scan (rs-listscan: ρ=1/4 n=16,20,24 → L=7,22,34; log₂L·η ≈ 0.35–0.67) is roughly consistent
with C(1/4)≈0.43.

## OPEN (the genuine prize core) + the most promising path

- **OPEN:** the UPPER bound `L*(δ) ≤ 2^{O_ρ(1/η)}` for ALL words, all window-interior δ. KKH26 gives the lower
  bound; the upper bound is unproven. Residuals: (a) general-γ 2-sparse (γ=1 engine-worst, not proven worst ∀n);
  (b) at r=t−k≥2 rungs the count involves ADDITIVE symmetric-function constraints e_1(S)=…=e_{r−1}(S) over F_q;
  proving these cut independently is the core.
- **CANDIDATE PATH (potentially off the BGK wall; restricted, unproved):** try to prove the upper half for the
  2-sparse (antipodal/walking-Laurent) family via an antipodal-tower descent, which would reduce that family's count
  to a **prime-decoupled Z/n subset-sum / elementary-symmetric-function count rather than a character sum.** The
  dyadic squaring identity `e_{2l}(±z) = (−1)^l e_l(z²)`, `e_odd = 0` holds for antipodally closed sets `±z` and
  descends `(n,D,j) → (n/2, D/2, ⌊j/2⌋)` for those sets only. It does **not** give a worst-word list recursion (see
  item 3: the unrestricted equality is refuted, and only `L*(μ_n,k,t) ≥ L*(μ_{n/2},⌈k/2⌉,⌈t/2⌉)` follows from
  squaring). Using it for the upper bound still needs (i) proof that the worst word lies in the antipodal family,
  (ii) control of non-antipodally-closed agreement sets and odd components, and (iii) the resulting count bound.
  Finite lower bounds from this family stay separate from the open universal upper bound.

## HONEST CAVEAT

The window list law is conjectural; my broad-scan shows mild n-growth at fixed η (L=7@n=16 vs 34@n=24 both at
η=0.125), so the Θ(1/η) constant may carry mild n-dependence — poly-vs-superpoly remains undecided at feasible n
(the recurring scale-confounding). The law is *consistent with* the floor (poly) and has a published lower-bound
anchor, but the upper bound is the open core. NOT a closure. The antipodal-tower prime-decoupled symmetric-function
count remains a candidate attack surface for the antipodal 2-sparse family only; the unrestricted worst-word tower
equality is refuted (item 3), so it cannot by itself carry the universal upper bound.
