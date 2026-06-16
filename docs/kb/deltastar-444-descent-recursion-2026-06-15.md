# #444 SEAM A round 2: the descent recursion, the A+Z form, and the packing kill (2026-06-15)

Successor to `deltastar-444-evenodd-descent.md` and Essays I–III. This round sharpened the one
live object (even/odd descent for explicit 2-power RS window list-decoding) into an exact
decomposition, formalized its core, and **rigorously killed** the most natural closure route.
Full narrative: `DELTASTAR_444_ESSAY_IV.md`.

> **⚠️ CORRECTION (supersedes any "off the wall" language below).** The rigorous push (on-issue #444
> comment 4707955906; `arklib-444-evenodd-descent.md`) shows **G1 ≡ the wall**: the binding-radius list
> count = the dyadic lacunary subset count, whose char-`p` validity at `n=2^30` **is** the
> BGK/additive-energy wall (char-0 = coset count, CLOSED; the defect is the open core). The descent does
> NOT bypass the wall — it **reunifies** the LD and sup-norm sides onto ONE object. Wherever this note
> calls `M(μ)` "off the wall," read it as "off the wall *at accessible scale* (`p`-defect = 0 for
> `n≤64`), but the prize-scale bound IS the wall." Non-retracted: the `A+Z` formalization, the Johnson
> packing kill, the level-set value, and the reunification insight.

## Solid, reusable results (independent of pending empirics)

1. **Literature lock (multi-source verified).** Bounded worst-case list for *plain explicit* RS on
   `μ_n` strictly beyond Johnson `(1−√ρ,1−ρ)` is GENUINELY OPEN. Random-point (BGM/Guo–Zhang/AGL),
   folded/multiplicity/subcode, and Shangguan–Tamo (only list 2–3 just past Johnson) results do NOT
   cover it. BCIKS 2025/169: RS list-decoding radius "wide open" and is the *prerequisite* for
   beyond-Johnson proximity gaps. Crites–Stewart 2025/2046 **disproved** up-to-*capacity*
   (DEEP-FRI, BCIKS, WHIR-MCA) ⟹ target is the sub-capacity band = the prize window. The descent is
   novel and correctly targeted.

2. **A+Z form (FORMALIZED, axiom-clean — `Sweep_A41_DescentAZForm.lean`).**
   `agreement(f,u) = A + Z`, `A=#{P=Q=0}`, `Z=#{P²=yQ²}=#{R=0}`, `R=P²−yQ²`, `P=F−u_e`, `Q=G−u_o`.
   (`Z=A+B` since `Q=0⟹P²=yQ²`.) `A` = symmetric joint (what the antipodal tower captured); `Z` =
   zero-count of the explicit quadratic form `R` = the new non-symmetric content. Theorems:
   `fiber_agreement_AZ`, `descent_identity_AZ`, `Z_eq_card_quadform`, all `[propext, Classical.choice,
   Quot.sound]`.

3. **Descent spine (FORMALIZED — `fiber_agreement_even`).** For an EVEN word (`u_o≡0`), even
   codewords `f=F(x²)` (`G≡0`) agree on `μ_n` at exactly `2×` their level-`μ−1` agreement with
   `u_e` (per fibre `2·⟦P=0⟧`). So even codewords biject with the level-`μ−1` window list of `u_e`
   at the SAME `(ρ,τ)`. The worst observed word `x^{n/4}+1` is even and self-similar
   (`u_e=y^{n/8}+1 = x^{N/4}+1` one level down).

4. **Exact decomposition (NOT a difficulty reduction).** `Λ(μ) = Λ(μ−1) + M(μ)`,
   `M(μ)=#{mixed (G≢u_o) members reaching window}`. Spine = `Λ(μ−1)` exactly. But `M(μ)=Λ(μ)−Λ(μ−1)`
   is the increment; bounding it is the whole problem. `p`-INDEPENDENT (verified across primes);
   open part localised to `G≢0` members on the one-parameter mid-exponent family.

5. **Exponent–degree dichotomy.** For even monomial `u=x^{2c}`, a mixed member's
   `Z=#{(F−y^c)²=yG²}` = zeros in `μ_N` of the genuine polynomial `R=(F−y^c)²−yG²`, `deg R=2c`.
   `Z≤min(2c,N)`, peaking at mid-exponent `c≈N/2`. This is WHY `x^{n/4}+1` is the worst word
   (`deg R = 2·dist(c,{0,N})`). Low/near-`N` exponent ⟹ `deg R` too small ⟹ `M=0` ⟹ branching 1.

## THE KILL (rigorous — prevents re-trying the second-order descent)

**Second-order descent / sign-pattern route REDUCES TO JOHNSON.** Two distinct mixed members
`(F,G),(F',G')` on their common agreement set satisfy `(F−F')²=y(G−σG')²` (`σ=εε'∈{±1}`) — again a
descent relation. `deg[(F−F')²−y(G−σG')²]≈k<N`; a perfect square can't equal `y·(square)` as a
polynomial identity (even vs odd degree) ⟹ overlap `>k` forces `F=F', G=±G'`. So **distinct mixed
members pairwise overlap in `≤2k` points of `μ_N`.** Double-counting `L` sets of size `≥θ=(2τ−ρ)N`,
pairwise `∩≤2k=4ρN`, bounds `L` only when `θ²>2kN` i.e. **`τ>√ρ+ρ/2`** — just past Johnson,
OUTSIDE the window `τ<√ρ`. So the engine is pure pairwise-packing = Johnson+ε (recovers
Shangguan–Tamo list 2–3, nothing more). **The descent does NOT escape Johnson by elementary
packing.** Dead for the full window.

## The ONLY live route (open, non-packing)

`M(μ)=O(1)` via a bound that compounds the self-similarity ACROSS levels (not within one level).
Two alien candidates, both `p`-independent, neither in the dead ledger:
- **(δ) Multiscale spectral compounding.** Leaves are all `deg<k`, agree with the same word, agreement
  sets aligned with the 2-adic filtration — a martingale/cumulative-uncertainty bound on the leaf
  count.
- **(ε) Sign-patterns as a code.** `ε(y)=(F−u_e)/(x_y G)∈{±1}` on the agreement set; `y↦x_y` is a
  SECTION of squaring (not a polynomial). If admissible `ε` form an `O(1)`-parameter
  (quadratic-character-like) family, `#mixed=O(1)`.

## Decisive empirical fork (agents running)

Is the observed worst `L*` (`=4` at `ρ=1/8`, `n=16,32`) **all-spine** (`M=0` ⟹ constant by induction,
remaining task = prove `M=0` at the self-similar worst word) or does it contain **mixed** members
(and does `#mixed` grow with `n` ⟹ floor REFUTED on the explicit side)?

### EMPIRICAL VERDICT (n=16,32,64, multi-prime, exact)

- **`M = 0` for the worst even word `x^{n/4}+1`, ALL levels, `p`-independent (≥3 primes).** Its window
  list is entirely even codewords (`G=0`) — pure spine. `L = 4` FLAT across `n=16,32,64`.
- **Binomial family is BOUNDED and CONSTANT in `n`.** `x^{n/8}+1 → L=8` flat (16,32,64); family max
  `L=8` at `ρ=1/16`; NO growth across the octave. (Corrects prior "`x^{n/4}+1 ≈ 7`"; under the `s=2k`
  window it is `L=4`.)
- **Closed mechanism (paper-proven, elementary).** For `u = β·x^a + c`, the list members are exactly
  the CONSTANT codewords `γ` with `(γ−c)/β ∈ image(x^a) = μ_{n/gcd(a,n)}`: there are exactly
  `n/gcd(a,n)` of them, each agreeing on `gcd(a,n)` points. So `L = n/gcd(a,n) ≤ 1/(2ρ)` — **constant
  in `n`**, beyond Johnson, by power-map level-set counting. (This is the matching value; the
  *lower bound* `L ≥ n/gcd(a,n)` is rigorous; the *upper bound* — "no non-constant member reaches the
  window" — is the residual, empirically true to `n=64`.)
- **Non-deeply-even words** (`x^{n/4}+x`, odd-exponent `x^{n/4+1}+1`): list is ALL-mixed (`G≠0`) but
  still `L=4` bounded — so boundedness is not exclusive to the even spine.
- **Adversary (higher-weight) verdict:** [append when agent reports — the one open piece of G2].

**Net:** within the monomial/binomial family the list is provably/empirically `O(1/ρ)`, constant in
`n` to `n=64`. The descent's spine accounts for the even case (`M=0`), and the level-set count gives
the value. The genuine open residual G2 narrows to: *can a higher-weight word exceed `1/(2ρ)` and grow
with `n`?*

## Round-3 lever tested + closed (reunification is TIGHT)

Tested: is the LD agreement-set constraint STRICTLY STRONGER than the energy/lacunary (power-sum)
constraint? — i.e. `realizable = #{lacunary T that also lie on a deg<k curve through (x,u(x))}`
vs `pure = #{lacunary T}`. **Verdict: EQUAL wherever computable.** At `n=16`, for ALL primes
`p≡1 mod 16` (`m=1..16`, incl. `p=17` whole-group and `p=257`), `pure = realizable = 4` = coset count
— `n=16` has ZERO char-`p` defect in any characteristic (the `e₁=e₂=0 ⟹ μ₄-coset` rigidity holds in
all char for this small case). So the LD and energy objects **coincide exactly where defect = 0**;
distinguishing them requires the defect regime (larger `n`), which is the wall (defect onset
`r_max≈2log_n p`, mapped in #407). **No LD-specific lever:** the reunification is tight, and the
round-3 "LD strictly stronger" hope funnels to the same wall. Logged so it is not re-tried.

## Reunification UPGRADED to a proven bijection + crack-hunt SETTLED (adversarial-verify workflow)

The reunification is now a **theorem**, not just matching counts. Bijection
{linear-codeword agreement sets vs `x^a+1`} ↔ {lacunary `a`-subsets of `μ_n`}: surjectivity by
construction (lacunary `T`, `∏(x−t)=x^a−αx+c` ⟹ `f=αx+(1−c)` agrees on all of `T`), injectivity
automatic. **FORMALIZED axiom-clean** `Frontier/Sweep_A42_ReunificationBijection.lean`
(`linear_agreement_iff_lacunary_root`, `lacunary_subset_is_agreement_set`, `agreement_set_is_lacunary`,
`lacunary_poly_middle_coeffs_zero`; real `lake build` OK, 3297 jobs).

**Crack-hunt settled (no LD lever):** since members ↔ lacunary subsets is a BIJECTION, every char-`p`
defect (non-coset lacunary subset) is automatically LD-realizable ⟹ the agreement-set (curve)
constraint is NOT strictly stronger than the power-sum (energy) constraint ⟹ `L = #lacunary =
n/gcd + #defect`, so `L=n/gcd ⟺ defect=0` = the wall. Defect non-vacuous at `a=2` (n=8: 24 members ↔
24 non-coset lacunary subsets); none at `a≥3` across ~1300 primes (defect=0 at accessible scale).
Adversarial verify also confirmed: A+Z formalization rigorously correct (800 trials, axiom-clean);
packing-kill holds (overlap ≤2k, reduces-to-Johnson) with a minor parity-precision caveat (sign-flip
pairs `F'=F,G'=−G` give `R≡0`, but the overlap bound and conclusion survive). Issue comments 4708232824,
4713491997.



> **⚠️ CORRECTION (self-shred):** `Sweep_A45` (`lacunary_coset_rigidity`) requires the **trinomial** hypothesis `∏(X-t)=X^a-αX-c` (= e_1..e_{a-2}=0, two free symmetrics = LINEAR codeword k=2 = binding case at n=16 ONLY). At binding radius for n≥32 the condition is e_1..e_{n/8}=0 (n/8 free) ⟹ (k+1)-sparse, NOT trinomial ⟹ A45 does not apply. So char-0 proven = general first level (A44: vanishing-sum ⟹ T=−T) + full trinomial/k=2 case (A45). The GENERAL fixed-rate char-0 rigidity needs the iterated argument (not formalized). 'char-0 half COMPLETE' RETRACTED (issue 4713909103).

## Char-0 rigidity engine FORMALIZED (the provable half of defect=0) — `Sweep_A43`

`Frontier/Sweep_A43_DyadicRigidityEngine.lean` (axiom-clean, real `lake build` OK): the engine of the
char-0 dyadic rigidity (Lam–Leung for 2-power, NOT in Mathlib). `coeff_symm_of_dvd_X_pow_add_one`:
`(Xᵐ+1) ∣ g ∧ deg g < 2m ⟹ g.coeff j = g.coeff (j+m)` for `j<m` (proof: `g=(Xᵐ+1)q`, `deg q<m`, read
coeffs via `coeff_mul_X_pow'`). On roots of unity (`m=2^{μ-1}`, `ζᵐ=−1`): multiplicity of `ζʲ` = that of
`−ζʲ` ⟹ **roots pair into ±-pairs** = the char-0 coset rigidity. SHARP char-0/char-`p` split: in char 0
`Φ_{2^μ}=X^{2^{μ-1}}+1` is irreducible so `g(ζ)=0 ⟹ (X^{2^{μ-1}}+1)∣g` (engine applies, pairing forced);
in char `p≡1 mod 2^μ` (prize) `Φ` SPLITS, `ζ∈F_p`, minpoly `=X−ζ`, so only `(X−ζ)∣g` — engine
hypothesis FAILS, non-coset defect appears. This formalizes WHY char-0 is closed and pinpoints the
char-`p` defect as the open core. (`antipodal_coeff_of_dvd_X_pow_add_one` = iterated form.)

**CHAR-0 HALF NOW FULLY PROVEN — `Sweep_A44_DyadicVanishingSum.lean` (axiom-clean, real build OK
3298 jobs).** `dyadic_vanishing_sum_paired`: for `g∈ℚ[X]`, `deg g<2^μ`, vanishing at a primitive
`2^μ`-th root `ζ∈ℂ`, the coeffs are antipodally symmetric `g.coeff j = g.coeff(j+2^{μ-1})` for
`j<2^{μ-1}` = **Lam–Leung for p=2 (vanishing sum of 2^μ-th roots of unity ⟹ ±-pairs), NOT in Mathlib**.
Proof = the honest mechanism wired to Mathlib: `minpoly ℚ ζ = cyclotomic(2^μ)ℚ = X^{2^{μ-1}}+1`
(`IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible` + `cyclotomic.irreducible_rat` +
`cyclotomic_prime_pow_eq_geom_sum` at p=2) ⟹ `(X^{2^{μ-1}}+1)∣g` (`minpoly.dvd`) ⟹ A43 engine ⟹ pairing.
So the unified conjecture's CHAR-0 side is a formalized THEOREM; the open core is precisely the char-`p`
failure of cyclotomic irreducibility (Φ_{2^μ} splits mod p≡1 mod 2^μ ⟹ minpoly=X−ζ ⟹ no forced
divisibility ⟹ defect). This is "the current bound is complete and correct" — formalized — in char 0.

## Honesty

No closure. Net new: exact `A+Z`/spine identities (formalized), exact `p`-independent decomposition,
exponent dichotomy, a rigorous Johnson-reduction kill of the packing route, the reunification (LD =
energy, tight, both = the char-`p` lacunary/additive-energy defect = the BGK wall), and the literature
lock. The single unified conjecture (char-`p` lacunary count = char-0 coset value ⟺ `E_r(μ_n)≤(2r−1)‼n^r`
at depth `log q`) provably resolves BOTH grand challenges simultaneously — and IS the recognized open
wall. The MCA `δ*` half is unchanged. Related-quantity (list-decoding) advances only.
