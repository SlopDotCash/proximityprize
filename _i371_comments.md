=== lalalune @ 2026-06-12T01:32:59Z
## H-RC: the Hankel-pencil / ratio-census hypothesis (attack vector 1, instantiated)

The first grind target, derived top-down from the incidence face (`epsMCA_ge_far_incidence`) via the key equation.

**The mechanism.** A syndrome `s` decodes to weight ≤ w iff the syndrome sequence satisfies a linear recurrence of order ≤ w — iff the `(n−k−w) × (w+1)` Hankel matrix `H(s)` has nontrivial kernel. Along a line `s₀ + γs₁` this is a **linear matrix pencil** `H_γ = H(s₀) + γ·H(s₁)`:

- **Below UDR** (`n−k ≥ 2w+1`): nontrivial kernel ⟺ all `(w+1)`-minors vanish — each a degree-≤(w+1) polynomial in γ. One nonvanishing minor bounds the bad count by `w+1`. (This re-derives the ladder regime determinantally.)
- **At the first beyond-UDR slice** (`n−k = 2w`): the square pencil has nontrivial kernel generically; decodability instead requires the kernel polynomial `Λ_γ` — whose coefficients are `w×w` minors, degree ≤ w in γ — to be a TRUE locator: **all w roots in the smooth domain ⟨g⟩**. The equation `Λ_γ(x) = 0` is a bidegree-`(w,w)` curve in `(γ,x)`; each x ∈ ⟨g⟩ gives ≤ w roots γ, so total curve–domain incidences ≤ `w·n`; each fully-split γ consumes w of them:

  **#bad scalars at the slice ≤ wn/w = n.**

**Confirmed prediction.** At RS[F₁₇,⟨2⟩,4], δ = 1/4: w = 2, n−k = 4 = 2w — exactly the slice. Predicted bound: ≤ n = 8. The exhaustively computed exact value: **B6 = 7 ≤ 8**, nearly tight. The far-coset extremal stack is one incidence short of saturating the curve bound.

**The programme.**
1. **Prove slice 1 in Lean**: the bidegree-curve incidence bound ⟹ ε_mca ≤ (n + near-coset correction)/q at the first beyond-UDR radius, unconditionally, every smooth RS. This extends the unconditional good side past the ladder by a new (determinantal) method.
2. **Iterate the slices**: at `n−k = 2w − j` the kernel is (j+1)-dimensional; the locator family is a (j+1)-parameter variety; measure (probe) and bound (curve/variety–subgroup incidence) the split count as j grows. **Where the poly(n) bound first breaks is the discovery** — it must break before Johnson-capacity coupling, or it marches the unconditional floor toward (and past) Johnson.
3. **Probe slice 2** at an instance with `n−k = 2w−1` (e.g. RS[F₁₇,⟨2⟩,3], w = 3, n−k = 5) — exact bad-count vs the predicted variety bound.

Red-team note: the smooth structure has not been used yet — the slice-1 bound holds for any domain; smoothness should enter at higher slices through the subgroup structure of the root sets (the quartet-tower/census machinery applies to locator root patterns). If the slice bounds stay domain-generic too long, that is itself evidence the method caps at a generic-incidence wall — to be located precisely.


=== lalalune @ 2026-06-12T01:41:50Z
## H-RC refined: the Welch–Berlekamp pencil theorem — slice-2 data + the below-UDR law

**Slice-2 verdict (probe, RS[F₁₇,⟨2⟩,3], w = 3, n−k = 5):** sampled far-stack bad counts reach **9 > n = 8** — the slice-1 bound does not extend by the same counting; the kernel dimension enters. (Consistent: at `n−k = 2w−1` the locator family is 2-parameter.)

**The sharper reformulation.** Work with the Welch–Berlekamp system instead of Hankel matrices. `γ` is bad at slack `w` iff there exist a split monic `ℓ_γ` (deg ≤ w, roots in the domain) and `R_γ` (deg ≤ w+k−1) with

  `ℓ_γ(x_i)·(u₀ᵢ + γ·u₁ᵢ) = R_γ(x_i)` for ALL i —

(the `ℓ·f ≡ 0` absorption of the error set). This is linear in `(ℓ, R)` with `2w+k+1` unknowns and `n` equations, and the matrix is a **linear pencil** `M₀ + γM₁` (γ enters only the `w+1` locator columns).

**Theorem WB-1 (below UDR, far directions).** If `n ≥ 2w+k+1` (strictly below the unique-decoding slack) and `u₁` is `FarFromCode` at slack `w`, then `#bad γ ≤ w+1`.
*Proof.* Bad ⟹ the evaluated system has a nontrivial kernel ⟹ every maximal minor of the polynomial matrix vanishes at γ. Each minor has γ-degree ≤ w+1 (only `w+1` columns carry γ). If ALL minors vanish identically, the pencil has a polynomial kernel vector `(ℓ(γ,·), R(γ,·))` identically in γ; extracting the top γ-coefficient gives `ℓ_top·u₁ ≡ R_top` on the domain — `u₁` within `w` of the code on a co-`w` set, contradicting far. So some minor is a nonzero polynomial of degree ≤ w+1: at most `w+1` roots. ∎

**The far hypothesis is exactly pencil nondegeneracy** — the same object `FarCosetExplosion.FarFromCode` that makes every explainable scalar bad also makes the pencil count them.

**Consequences.**
1. With the near-coset side handled by pencil deflation (the degenerate pencil's Kronecker structure: deflate the γ-identical solution, repeat — each deflation costs one `w+1` block), the target is: **ε_mca(δ) ≤ O(δn)/q for ALL δ strictly below (1−ρ)/2, all stacks, unconditionally** — the complete below-UDR MCA theorem by pure pencil algebra, no decoding theory.
2. At production shape this moves the **unconditional** floor from the ladder reach ≈(1−ρ)/3 to **UDR = (1−ρ)/2**: `δ* ≥ (1−ρ)/2 − 1/n` for every smooth RS with `n/q ≤ ε*` — no named residual.
3. At the UDR boundary slice (`n = 2w+k`) the kernel is generically 1-dimensional and the count is the split-locus of the bidegree-`(w+1, w)` kernel curve — the B6 = 7 ≤ 8 instance. Beyond, the kernel dimension grows by one per slice and the split-locus question becomes the genuine open core in pencil form: **how many members of a j-parameter pencil of degree-w polynomials split completely over the smooth domain?** This is the cleanest finite formulation of the window question this programme has produced: the quartet-tower/census machinery applies directly to the root-pattern side, and the far-coset law guarantees the count IS ε_mca.

**Lean plan** (`WBPencilBound.lean`, staged): (i) the absorption lemma (explainable ⟹ WB-solvable); (ii) minors of the polynomial matrix: γ-degree ≤ w+1 + evaluation commutes (`RingHom.map_det`); (iii) the nondegeneracy extraction (top-γ-coefficient ⟹ far violation); (iv) Theorem WB-1; (v) the near-coset deflation; (vi) the production floor corollary.


=== lalalune @ 2026-06-12T02:19:29Z
# Round 3a landed: the staircase BAND THEOREM — δ* = e/n on every sub-saturation band at the literal ε*

(Continuing the #357 top-down campaign in its new home; rounds 1–2 are in the #357 record and the compiled KB.)

`StaircaseBandTheorem.lean` (`fc2ec584c`, 6 declarations, axiom-clean, full build):

> **`mcaDeltaStar_staircase_band`**: for `1 ≤ e`, `3(e−1)+k ≤ n`, `e+1+k ≤ n`, and `e·2¹²⁸ ≤ q < (e+1)·2¹²⁸`: `mcaDeltaStar(RS[F,dom,k], 2⁻¹²⁸) = e/n` **exactly** — with ZMod, smooth-⟨g⟩, and production-shape (n = 2²⁵, k = 2²⁴: **every rung 1 ≤ e ≤ 5,592,406**, i.e. every field size up to ≈ 2¹⁵⁰·⁴) corollaries.

The staircase law is now **theorem** on the entire region `e ≲ (n−k)/3` — the in-tree granularity ladder supplied the per-level counts (good side `badScalars_card_le`, bad side the (e+1)-spike floor), and only the literal-ε* band arithmetic was new. The rung-1 pin re-derives as the e = 1 instance with the band edge closed (GF(2¹²⁸) itself now covered).

**Convention note (recorded for the KB):** the proven normalization is Λ(e) = worst count strictly inside radius e/n, budget band `ε*·q ∈ [e, e+1)` — δ* = first bad radius.

**Honest scope:** the reach caps at `q ≲ ((n−k)/3)·2¹²⁸`; the production-core parameterization `q ≥ n²·2¹²⁸` (where Λ's growth through the (Johnson·n, capacity·n) window is the open core, faces 1–4) is untouched.

**Round 4 (launching, per the research map's ranked vectors):** vector 1 — the ratio-census identity (line–ball incidence ⟹ multiplicity profile of the GRS syndrome-ratio rational function on the subgroup orbit, level-sets-are-root-sets degree bound) — and vector 2 — the BGK Fourier bridge named-Prop + reduction inequality.


=== lalalune @ 2026-06-12T02:27:47Z
## THEOREM WB-1 PROVEN (axiom-clean): the Welch–Berlekamp pencil bound

`WBPencilBound.lean` + `WBPencilSubmatrix.lean` + `WBPencilAbsorption.lean`, all `[propext, Classical.choice, Quot.sound]`:

**`wbSolvable_line_card_le`** — if the direction u₁ is not itself WB-solvable at slack w, then at most **w + 2** scalars γ make the line u₀ + γ·u₁ WB-solvable, for every offset u₀.

The proof chain, with no decoding theory anywhere:
1. `wbSolvable_iff_exists_kernel` — WB solvability ⟺ nontrivial kernel of the n × (2w+k+1) coefficient matrix (the ℓ = 0 branch collapses by n distinct roots);
2. `exists_invertible_row_submatrix` — the far direction's matrix is injective, so some 2w+k+1 rows are invertible (generic linear algebra, ToMathlib candidate);
3. `pencilE` — the reversed pencil E(ε) = det(wbMatrix(ε·u₀ + u₁)[I]) as a polynomial of degree ≤ w+1 with E(0) = det M₁[I] ≠ 0;
4. `det_line_eq_pow_mul_pencilE` — the diagonal factorization det(line-matrix[I]) = γ^{w+1}·E(γ⁻¹);
5. root counting: every nonzero solvable γ inverts into a root of E.

With `wbSolvable_of_explainable` (absorption), every mcaEvent-bad scalar is WB-solvable, so **every below-UDR radius has bad-count ≤ w + 2 for WB-far directions, unconditionally** — at production shape this contributes mass ≤ (w+2)/q ≪ 2^{−128}. Remaining to extend the unconditional production floor to UDR: the near-direction side (u₁ WB-solvable: pencil deflation / Kronecker structure) — next target. The hypothesis is sharp: when n ≤ 2w+k the system is underdetermined and every direction is WB-solvable, so the theorem lives exactly on the below-UDR range.

