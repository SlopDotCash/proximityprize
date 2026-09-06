# Essay III — The no-larp rewrite (what actually survived the shred)

*Essay I generated 50 directions; Essay II killed 47 as wall-in-a-hat, vacuous import, or
larp. This is what remains after the cut, stated with zero embellishment and with the exact
verified/open boundary. The honest headline: there is ONE live, non-trivial, off-BGK research
object, it is the **grand list-decoding challenge approached through an elementary cyclotomic
descent**, and this session produced **real, verified, new structure on it** — not a closure.*

## 1. The single surviving object

**SEAM A — the window list, not the sup-norm.** Pin the worst-case window list
`L*(ρ,η,n) = max_u L(u,n,k)` for explicit 2-power RS, and show it is bounded (constant or poly
in `n`) strictly inside the window `(1−√ρ, 1−ρ−Θ(1/log n))`. This is one of the two grand prize
challenges (list-decoding), it is genuinely open, and — crucially — it does **not** route
through `M(n)=max|η_b|`. Everything else from Essay I (climb-candidates R6–R8,R13,R17,R19,R21–R22;
SEAM C/R5; SEAM B/R12; constructs M6,M11,M17,M22,M25; the Kolmogorov/Mahler/Schinzel larps) is
dead or vacuous — re-confirmed by independent argument in Essay II.

## 2. The new math this session actually produced (verified)

The **even/odd non-symmetric dyadic descent**. Full derivation in
`docs/kb/deltastar-444-evenodd-descent.md`; the load-bearing facts, all exact and p-independent:

1. **Descent identity (verified 200/200).** For `n=2N`, `f(x)=F(x²)+xG(x²)`,
   `u(x)=u_e(x²)+xu_o(x²)`, `P=F−u_e`, `Q=G−u_o`:
   `|agreement| = 2·#{y∈μ_N: P=Q=0} + #{y∈μ_N: Q≠0 ∧ P²=yQ²}`. The single-fibre term is
   `≤ deg(P²−yQ²)`.
2. **Monomial base case = 2, constant in N (verified N=16,32,64; provable).** `y^{N/2+1}=χ(y)·y`
   (`χ` the quadratic character `y^{N/2}=±1`); a degree-`<2` codeword can only reach the window
   as `F=y` (on the squares) or `F=−y` (on the non-squares) ⟹ list `={y,−y}`, exactly 2. This
   is **structure-only, p-independent** — no character-sum magnitude.
3. **The descent closes on monomials.** A weight-2 word descends to a monomial pair (mixed
   parity → bounded) or a half-size weight-2 word (same parity → recurse), terminating at a
   monomial pair after exactly `v₂(a−b) ≤ log₂ n` levels.
4. **Branching = 1 for even in-range words (proved, modulo the correction).** For an even word,
   large full-fibre agreement forces the odd part `G≡0` (it vanishes at `>k/2` points), so every
   window list member is an even polynomial and `L(u,n,k)=L(u_e,N,k/2)` up to the bounded
   single-fibre correction `|S₁|≤max(k,a)`. **Branching 1 ⟹ the list is preserved down the
   whole `log n`-deep tower.**
5. **3-point constancy (verified).** `L*=4` at ρ=1/8 for `n=16,32`; `~7–8` at ρ=1/16. The worst
   word is `x^{n/4}+1` (exponent scales as a power of 2, full descent depth) — and the list is
   **constant despite the depth**, the exact empirical signature of branching 1.

This is precisely the structure the campaign's antipodal-symmetric tower **missed**: the
symmetric (`S=−S`) tower captures only `1` of `L` list members (measured this session, a sharper
refutation than the prior caveat). The descent's single-fibre `P²=yQ²` term **is** the
non-symmetric part.

## 3. The honest open boundary (what a full proof still needs)

The descent is a **reduction**; its base case (monomials) is closed, but two gaps remain before
`L*=O(1)` is a theorem:

- **G1 — uniform branching `=1` (incl. odd words + the single-fibre correction).** §2.4 proves
  it for even in-range words; the odd-word leg and a uniform bound on the `|S₁|` correction across
  all `log n` levels are unproven. *This is the crux and it is concrete/finite-per-level.*
- **G2 — the worst word is low-weight (weight 2) / Laurent-low-exponent.** Verified worst is
  weight-2 (`x^{n/4}+1`) at `n=16,32`; a higher-weight word beating it at larger `n` would force
  the single-fibre term up. *Under adversarial test by the workflow Refuters now.*

If G1 and G2 close, this is a proof of the explicit-2-power-RS window list-decoding bound by
elementary means — **a related quantity to the prize, conjecturally one half of it** — with no
appeal to effective Gauss-sum equidistribution. That would be a genuine result. It is **not**
claimed proven; G1/G2 are open.

## 4. Why this is not a re-derivation of the dead ledger

The dead ledger eliminated every route *to the sup-norm `M(n)`*. The descent never touches
`M(n)`: its base case is the quadratic character `y^{N/2}=±1` (a sign, not a magnitude), and its
recursion is exact polynomial agreement counting. It is `p`-independent (verified across primes).
The campaign's prior "tower" work (a) used the symmetric `S=−S` restriction (captures `1/L`,
useless) and (b) tried to descend the *energy/sup-norm*, which inflates (the `√(2 ln 2)` per
level). The descent here descends the *list-agreement count* with the **non-symmetric single-
fibre term retained**, and that term is exactly what makes branching 1 instead of inflating.

## 5. Disposition

- **Prove G1** (the branching/correction lemma) — the highest-value next step; finite per level.
- **Refute or confirm G2** (worst-word weight) — workflow Refuters A/C/D in flight.
- **Formalize** the descent identity (§2.1) axiom-clean (the rigorous foundation) — this session.
- **Loop**: if Refuters surface a growing-list word, G2 fails and SEAM A weakens to "bounded for
  low-weight words only"; if they confirm constancy + branching 1, push G1 to a proof.

No closure is claimed. The prize core `M(n)≤C√(n log m)` remains open; but SEAM A is now a
*live, structured, off-BGK* attack with verified new machinery and two precisely-located gaps —
which is materially more than "it reduces to the wall."
