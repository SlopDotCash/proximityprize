# HBK/Stepanov subgroup-addition bound — formalization-ready extraction (2026-06-11)

Full deep-research report (agent-extracted from HBK 2000 fulltext, Konyagin CRM lectures,
Cochrane–Pinner 2011, Mattarei math/0511339, Shkredov–Vyugin 1102.1172, Shteinikov 1008.0723).

## Canonical citation + the conflation warning
The pointwise bound is **HBK 2000 Lemma 5 (T=1)**; window **|G| ≍ p^{3/4}** (HBK: h⁴T < p³).
The **p^{2/3} window belongs to the ENERGY bound** E(G) ≤ (16/3)|G|^{5/2} (CP Thm 2.1) — sharp
(Hua–Vandiver/Weil: E = |G|⁴/p + O(p|G|) so |G| ≫ p^{2/3} kills it). Don't conflate.
BGK06 JLMS is paywalled — never cite its internal lemma numbers unverified.

## The formalization target (recommended): CP Lemma 2.3 → Lemma 2.4 (s = 1)
**CP Lemma 2.3** (= KS99 Lemma 3.2 corrected): a,b,d,s positive integers, s ≤ n,
`s·a·d + s·d(d−1)/2 < a·b²`, `a·b ≤ t`, `t·b < p` ⟹ Σ_{j≤s} N_j ≤ (a − 1 + 2t(b−1))/d.
**CP Lemma 2.4 (s=1)**: b := ⌊(4t)^{1/3}⌋+1, a := ⌊t/b⌋, d := 2a; under `t·b < p`:
N(λ) = #{(x,y) ∈ G² : x+y = λ} ≤ b². (b² ≥ t ⟹ trivial since N ≤ t; no |G| lower bound needed.)
Best constant known: Mattarei 3·2^{−2/3}|G|^{2/3} (different proof, Stöhr–Voloch route).

## Proof skeleton (single shift)
Normalization: x ↦ z = x/(λ−x) bijects {x ∈ G : λ−x ∈ G} ↔ {z ∈ G : z+1 ∈ λG}; invariants on
R_j = {x ∈ G : x−1 ∈ G_j}: x^t = 1, (x−1)^t = a_j (a_j = y^t const on coset), x ∉ {0,1}.
Direct (λ−x)-form also fine: Ψ(X, X^t, (λ−X)^t), multiplier X(λ−X), roots ∉ {0,λ}, monomial
lemma mod (X−λ)^t.

1. **Aux space**: Ψ(X,Y,Z) = Σ_{u<a,v<b,w<b} λ_{uvw} X^u Y^v Z^w; ψ(X) := Ψ(X, X^t, (X−1)^t).
   Free coeffs ab²; deg ψ ≤ a−1+2t(b−1).
2. **Derivative mechanism** (ordinary derivatives + multiplier {X(X−1)}^k; falling factorials):
   {X(X−1)}^k (d/dX)^k [X^{u+tv}(X−1)^{tw}] = X^{tv}(X−1)^{tw}·P_{k,u,v,w}(X),
   P_{k,u,v,w}(X) = Σ_{i≤k} C(k,i)(u+tv)_i(tw)_{k−i} X^{u+k−i}(X−1)^i, deg ≤ u+k.
   At x ∈ R_j: {x(x−1)}^k ψ^{(k)}(x) = P_{k,j}(x) where P_{k,j} = Σ λ_{uvw} a_j^w P_{k,u,v,w},
   deg < a+k.
3. **Dimension count**: demand P_{k,j} ≡ 0 identically ∀ k<d, j≤s: constraints
   s(ad + d(d−1)/2) < ab² unknowns ⟹ nonzero Ψ exists. [in-tree: exists_nonzero_vanishing_combination]
4. **Multiplicity**: P_{k,j} ≡ 0 ⟹ ψ^{(k)}(x) = 0 ∀k<d at each x ∈ R_j (x(x−1) invertible).
   CHAR-p CAVEAT: ordinary-derivative ⟹ (X−x)^d | ψ needs d ≤ p (k! ≠ 0); d ≈ 2t/b < p in window.
   OR use Hasse derivatives throughout (binomials C(u,k) replace falling factorials) —
   unconditional. [in-tree: HasseMultiplicityBridge, le_rootMultiplicity_iff_hasseDeriv]
5. **Count**: R_j pairwise disjoint (x−1 determines coset); ψ ≢ 0 ⟹ d·ΣN_j ≤ deg ψ.
   [in-tree: stepanov_card_mul_mult_le_natDegree]
6. **NON-VANISHING (the heart)**: Ψ ≠ 0 ⟹ ψ ≢ 0, given ab ≤ t, tb ≤ p.
   w₀ := min w with Ψ_{w₀} ≢ 0; ψ ≡ 0 ⟹ Ψ_{w₀}(X, X^t) ≡ 0 mod (X−1)^t. But Ψ_{w₀}(X,X^t)
   = Σ λ_{u,v,w₀} X^{u+tv} has DISTINCT exponents (u < a ≤ t: base-t digits), N ≤ ab ≤ t
   monomials, deg < tb ≤ p. Contradiction with:
   **MONOMIAL LEMMA (HBK Lemma 6)**: P a sum of N ≥ 1 distinct monomials, deg P < p ⟹
   (X−1)^N ∤ P. Induction on N: N=1 clear; else g := X·P′ − l₀·P (l₀ = top exponent) is a
   nonzero sum of N−1 distinct monomials (l−l₀ ≢ 0 mod p NEEDS deg < p), and (X−1)^N | P ⟹
   (X−1)^{N−1} | g via P = (X−1)^N Q ⟹ g = (X−1)^{N−1}[NXQ + (X−1)(XQ′−l₀Q)].
   Counterexample without deg < p: (X−1)^p = X^p − 1 (N=2). Same lemma for (X−λ)^N, λ ≠ 0.
7. **Parameters** (CP): b = ⌊(4st)^{1/3}⌋+1, a = ⌊t/b⌋, d = 2a; checks: 4st ≤ b³ ⟹ dim count;
   ab ≤ t; tb < p assumed; conclusion ≤ ½ + b² ⟹ ≤ b² (integer); b² ≥ t trivial case built in.

## Misc facts
- 2-power |G|: −1 ∈ G ⟹ λ−G = λ+G (only smooth-specific simplification; Stepanov is blind to
  factorization of t).
- k ≥ 2 shifts need char-p Wronskian over F((x^p)) (F.K. Schmidt) — NOT needed for single shift.
- Truth threshold: max_λ N(λ) ≥ (|G|²−|G|)/(p−1) ⟹ |G|^{2/3} bound FALSE for |G| ≫ p^{3/4}.
- Energy assembly (E(G) ≤ (16/3)t^{5/2}, t < p^{2/3}): sweep s ≤ t^{1/2}/3 of CP-2.4 + dyadic;
  bigger second-stage project.
- Deployed relevance: n = 2^40 ≪ p^{2/3} — both windows comfortably satisfied. The bound feeds
  the AVERAGE side only (per the posted corrections) — real math, not prize-closing.

## Sources (verified free)
- HBK 2000: https://ora.ox.ac.uk/objects/uuid:f2d980d4-ef1d-4b72-89a9-3d9d8527a024
- Konyagin CRM lectures: https://mathtube.org/sites/default/files/lecture-notes/Konyagin_Lectures.pdf
- Cochrane–Pinner: https://www.math.ksu.edu/~cochrane/research/binsum7.pdf
- Mattarei: arXiv math/0511339 · Shkredov–Vyugin: 1102.1172 · SSV: 1302.3839 ·
  Shteinikov: 1008.0723 · Green: 0904.2075 · Kalmynin: 2504.10202

## Brick plan (Lean)
A. **MonomialLemma.lean** — HBK Lemma 6, mathlib-only, ~100 lines. NEW to Mathlib. FIRST.
B. **StepanovSubgroupCore.lean** — CP Lemma 2.3 (aux space + derivative reduction + dim count
   + non-vanishing via A + engine). The big brick.
C. **SubgroupAdditionBound.lean** — CP Lemma 2.4 s=1 + the N(λ) ≤ (⌊(4t)^{1/3}⌋+1)² form.
D. Wiring: r(c) bound (SubgroupRepresentationRoots) ⟹ normalizedEnergyCount sub-quadratic ⟹
   E(G) < |G|³ strict — average-side sharpening, honest scope flags throughout.
