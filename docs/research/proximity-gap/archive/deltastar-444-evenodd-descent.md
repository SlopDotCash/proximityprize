# The even/odd dyadic descent for explicit 2-power RS window list-decoding (#444, SEAM A)

*Status: NEW math, partially verified, NOT yet a closed proof. Honesty contract holds — the
descent identity and the monomial base case are exact/verified; the per-level branching bound
and the higher-weight case are the remaining open pieces. This is progress on the grand
list-decoding challenge for explicit 2-power RS (a quantity related to, and conjecturally
equivalent to one half of, the δ\* prize), NOT a claimed prize closure.*

## 0. Object

`μ_n ⊂ F_p^×`, `n = 2^μ`, proper subgroup (`m=(p-1)/n>1`, never `n=p-1`), prize-shaped
`p ~ n^4`. Window-interior radius `δ = 1−ρ−η`, rate `ρ=k/n`. The **window list**
`L(u,n,k) = #{ deg<k polynomials f over F_p : #{x∈μ_n : f(x)=u(x)} ≥ s }`, `s=(ρ+η)n`.
The grand list-decoding challenge: is `L` bounded (constant or poly in `n`) for ALL words `u`,
for explicit 2-power `μ_n`, in the window interior (strictly beyond Johnson)?

## 1. The descent identity (EXACT — verified 200/200 random trials, `probe_444_monomial_descent.py`)

Write `n = 2N`, squaring `π: μ_n → μ_N`, `x ↦ y = x²`, fibres `{x,−x}`. Decompose into
even/odd parts: any polynomial `f(x) = F(x²) + x·G(x²)`, any word `u(x) = u_e(x²) + x·u_o(x²)`.
Set `P = F − u_e`, `Q = G − u_o` (polynomials on `μ_N`). Then the agreement set
`S = {x∈μ_n : f(x)=u(x)}` satisfies, EXACTLY:

> **`|S| = 2·#{y∈μ_N : P(y)=Q(y)=0} + #{y∈μ_N : Q(y)≠0 ∧ P(y)² = y·Q(y)²}`.**

*Proof.* Over the fibre `{x,−x}` above `y=x²`: `f(x)−u(x) = P(y)+xQ(y)`,
`f(−x)−u(−x) = P(y)−xQ(y)`. Both vanish ⟺ `P(y)=Q(y)=0` (since `x≠0`). Exactly one vanishes:
the agreeing root is `x=−P(y)/Q(y)` (needs `Q≠0`), which must satisfy `x²=y`, i.e.
`P(y)²=y·Q(y)²`; if `P=0,Q≠0` neither root agrees, and `P≠0,Q=0` ⟹ neither. ∎

The second ("single-fibre") term is the count of `μ_N`-roots of `P²−yQ²`, hence
`≤ deg(P²−yQ²) ≤ max(2deg P, 1+2deg Q)`.

## 2. The monomial base case (EXACT — list `= 2`, constant in N, and PROVABLE)

The window list of a MONOMIAL word `y^j` on `μ_N` is constant in `N` (verified `N=16,32,64`,
`kp=2,3,4`, two primes each: list `= 2` for the balanced `j≈N/2`, `= 0` near the edges).

**Why `= 2` (clean proof for `j = N/2+1`, `kp=2`).** On `μ_N`, `y^{N/2} = ±1` (it is the
quadratic character `χ(y)`: `+1` on squares `μ_{N/2}`, `−1` on non-squares). So
`y^{N/2+1} = χ(y)·y`. A degree-`<2` codeword `F = c₀+c₁y` agrees with `χ(y)y` on
`{y : c₀+(c₁−χ(y))y = 0}`: on squares this forces `(c₀,c₁)=(0,1)` (else `≤1` point); on
non-squares `(c₀,c₁)=(0,−1)`. Hence the only two members reaching the window are `F=y`
(agrees on all `N/2` squares) and `F=−y` (all `N/2` non-squares); every other `F` agrees on
`≤2` points `≪ s`. **List `= {y,−y}`, exactly 2.** The same character-twist argument bounds
general far monomials `y^{N/2+r} = χ(y)·y^r` (list ≤ small constant). **Monomials descend to
monomials**, so the base of the recursion is closed.

## 3. The recursion (the new content)

A weight-2 word `u = x^a + x^b` splits by the parity of `(a,b)`:
- **mixed parity** (one even, one odd): `u_e`, `u_o` are MONOMIALS → list `≤` (monomial list)²
  `= O(1)`. **Terminates, bounded.**
- **same parity** (both even / both odd): one of `u_e,u_o` is a weight-2 word on `μ_N`, the
  other is `0`. **Recurse on the half-size group.**

Same-parity halving `(a,b) ↦ (a/2,b/2)` (both even) or `(a,b)↦((a-1)/2,(b-1)/2)` (both odd)
strictly reduces `v₂(a−b)`; after **exactly `v₂(a−b) ≤ log₂ n` levels** the pair reaches mixed
parity → monomial pair. So
> `L(x^a+x^b, n) ≤ (branching)^{v₂(a−b)} · (monomial list)²`.

## 4. The branching is EXACTLY 1 for in-range even words (the key lemma)

Take `u` **even** (`u(−x)=u(x)`, both exponents even), so `u_o = 0`, `Q = G`. Consider any list
member `f` with full-fibre agreement `|S₂| = #{P=Q=0}`. On full fibres, `Q=G=0`; if
`|S₂| > k_o = ⌊k/2⌋`, then `G` (degree `<k_o`) vanishes at `>deg` points ⟹ **`G ≡ 0`**, i.e.
`f(x)=F(x²)` is an **even polynomial**, and `F` agrees with `u_e` on `S₂` ⟹ `F ∈ L(u_e, N, k/2)`.

When does every member have `|S₂| > k_o`? `|S| = 2|S₂| + |S₁|`, `|S₁| ≤ deg(P²−yQ²) ≤ max(k, a)`
(for the even word). For `|S| ≥ s` we get `|S₂| ≥ (s−|S₁|)/2 ≥ (s − max(k,a))/2`. This exceeds
`k_o = k/2` iff `s − max(k,a) > k`, i.e. `s > k + max(k,a)`. With `s=(ρ+η)n`, `k=ρn`: for words
with bounded exponent `a < ηn` this is `(ρ+η)n > 2ρn`, i.e. `η > ρ` — and even when `η≤ρ`, the
weaker `a<ηn` form holds in the window for the empirically-binding low-exponent words.

> **Consequence.** For even weight-2 words of exponent `< ηn`: every window list member is an
> even polynomial, and `L(u, n, k) = L(u_e, N, k/2)` **up to the bounded single-fibre
> correction `|S₁| ≤ max(k,a)`**. Branching `= 1`. Iterating down `v₂(a−b)` levels lands on a
> monomial pair (list `≤2` each) ⟹ **`L = O(1)` for in-range words.**

## 4b. Multi-agent cross-checks (`wf_444_descent_assault.js`, this session)

- **Branching = 1, sharpest form (verified):** for the binding even worst words, **ALL** window
  list members are even polynomials (`even = L/L` at every config: `n=16/32`, η=1/8,1/16). So the
  single-fibre correction `S₁` is **empty** and `L(u,μ_n,k) = L(u_e,μ_{n/2},k/2)` is an **exact
  bijection** — branching exactly 1, recursing to the base case. Confirmed exact down the tower:
  `L=4` at `x^8+1/μ_32 = x^4+1/μ_16 = x^2+1/μ_8` (identical).
- **G2 supported (Refuter A):** the true worst-case window list over ALL weight-3 and weight-4
  words **exactly equals the weight-2 worst** — never strictly larger, never growing faster in
  `n` (full exponent enumeration at `n=16,32`, two prize-shaped primes each). The worst word is
  low-weight.
- **Monomial constancy at scale (Refuter C):** the monomial window list is `N`-independent and
  prime-independent up to `N=128`, over 4 primes per `N` including a minimal-`v₂` (odd-index) and
  a `β≈5` prime. *Correction:* the exact value is not always `2` — at genuine window radii it is a
  small constant depending on `j` and `η` (the `2^{Θ(1/η)}` law), not literally `2`. The
  **constancy** is what the proof needs and it holds.

## 5. What is verified vs open

**Verified (exact, multi-prime, p-independent):**
- §1 descent identity (200/200).
- §2 monomial list `= 2` constant at `N=16,32,64`.
- §3 the worst weight-2 word at `n=16` is `x^4+1` / `x^5+x^4`, `L=4 = 2·2` (product of two
  monomial lists — the descent prediction).
- Window list constant `4` (ρ=1/8) / `7` (ρ=1/16) at `n=16` (and `32`, pending re-confirm).

**Open (the honest remaining gaps):**
1. **Per-level branching `=1` (or `O(1)`)** rigorously, including the single-fibre correction
   — §4 argues it for in-range even words; needs the odd-word case and a uniform bound on the
   correction. (Workflow Refuter B/D measuring this.)
2. **Worst word is low-weight / low-exponent.** If the true worst window word over ALL words is
   weight-2 with exponent `< ηn` (or reducible to one via the Laurent/unit-factor isometry —
   which is theoretically valid but was coded wrongly in `probe_444_worstword_exponent.py`),
   §1–§4 give a constant bound. If a high-weight or high-exponent word beats it, the single-fibre
   term grows and the descent needs strengthening. (Workflow Refuter A/C.)
3. **The Laurent/unit-factor reduction** `L(x^{a-1}(1+x),RS[k]) = L((1+x), x^{−(a−1)}RS[k])`
   is a genuine per-coordinate Hamming isometry, but reduces to a SHIFTED (generalized-RS /
   Laurent) code; the clean weight-2 descent above avoids needing it.

## 5c. ⚠️ THE RIGOROUS OUTCOME — G1 ≡ the wall (no bypass; corrected)

Pushing G1 to a rigorous conclusion **reconnects it to the known wall**. For the binding word
`x^{n/4}+1` at the window radius `s = n/4 = deg(f−u)` (ρ=η=1/8), agreement `≥ s` forces `f−u`
(degree exactly `n/4`, since `deg f < k = n/8`) to have **all `n/4` roots in `μ_n`** with the
coefficients in degrees `[n/8, n/4−1]` equal to zero (because `deg f < n/8`). By Newton's
identities the root set `T` (`|T|=n/4`) satisfies `e₁(T)=⋯=e_{n/8}(T)=0`, and every such `T`
yields a valid `f ∈ RS[k]`. Therefore, **exactly** (verified n=16, two primes: list = count = 4):

> `window-list(x^{n/4}+1) = #{ (n/4)-subsets T ⊆ μ_n : e₁(T)=⋯=e_{n/8}(T)=0 }`.

This object **is** the campaign's `DyadicLacunaryFloor` (first `t−1` power sums vanishing on a
2-power subset; `DyadicFourierUncertainty.lean`). Hence:
- **Char 0:** the count is a closed **coset count** (constant) — already proven. ✅ but known.
- **Char p:** `list = (char-0 coset count) + defect`, with the defect = non-coset mod-`p`
  vanishing-power-sum solutions = the **additive-energy / mod-`q` defect = the BGK wall**. The
  p-independence to `n=64` (§4b) is exactly the "defect = 0 at accessible scale" the campaign
  already observed; prize `n = 2^30` is the open wall.

**So G1 ≡ the char-p validity of the dyadic lacunary count = the wall.** The descent does NOT
bypass the wall. (Earlier framing that closing G1 needs "no effective equidistribution" was an
overclaim — corrected on issue #444, comment 4707955906.)

**What genuinely stands (non-retracted):** (1) the descent identity (§1), axiom-clean formalized,
a reusable tool; (2) a NEW derivation **from the list-decoding side** that the binding window list
= the dyadic lacunary count — the sup-norm/BGK side and the list side provably reach the **same**
object (the all-even branching makes this explicit), reunifying the two grand challenges from a new
direction; (3) the char-0 constancy re-derived cleanly. No bypass.

## 6. Why this is the dyadic lacunary count (not a NEW off-BGK object)

The descent is **combinatorial and `p`-independent** (the monomial base case is governed by the
quadratic character `y^{N/2}=±1`, structure-only, NOT a character-sum magnitude). It does NOT
pass through `M(n) = max|η_b|` — there is no sup-norm anywhere. This is exactly the §0 "SEAM A:
the list, not the sup." It is also exactly the part the campaign's antipodal-symmetric tower
MISSED: the descent handles **non-symmetric** agreement sets (the single-fibre `P²=yQ²` term),
which the `S=−S` tower (capturing only `1/L` members, measured this session) cannot. **If** the
branching and worst-word-weight pieces close, this is a proof of the explicit-2-power-RS window
list-decoding bound — the grand list-decoding challenge — by elementary cyclotomic/quadratic-
character means, with no appeal to effective Gauss-sum equidistribution.

## 6b. Clean reformulation of the wall (the one genuinely useful lens this gives)

Verified (n=16 exhaustive; n=32 binomial side): the size-`n/4` subsets `T⊆μ_n` with
`e₁(T)=⋯=e_{n/8}(T)=0` are **exactly** the root-sets of the 4 binomials `X^{n/4}−c`, `c∈μ_4`
(the 4 cosets of `μ_{n/4}`). Equivalently, a degree-`n/4` factor `g_T(X)=∏_{x∈T}(X−x)` of
`X^n−1` has the "coefficient gap" (zero in degrees `[n/8, n/4−1]`, forced by `e₁..e_{n/8}=0`)
iff `g_T = X^{n/4}−c`. Hence:

> **PRIZE WALL, restated:** is the only way for a degree-`n/4` factor of `X^n−1` over `F_p`
> (`p≡1 mod n`, `n=2^μ`) to have vanishing coefficients in degrees `[n/8, n/4−1]` to be a
> binomial `X^{n/4}−c`? Char-0 YES (the 4 binomials). Char-`p` defect = extra non-binomial
> gap-factors = the additive-energy / BGK wall. Verified defect `= 0` for `n≤64`; prize `n=2^30`
> open.

This is the same wall, but a clean *algebraic* statement (gap-factors of `X^n−1` mod `p`) rather
than an analytic one (character-sum √-cancellation) — possibly a more tractable lens for a future
attack, though it does not, by itself, move the wall.

**Sharpest algebraic form.** A gap-factor is `g = X^{n/4} + h(X)` with `deg h < n/8`; since
`X^{n/4} ≡ −h (mod g)`, `g | X^n−1 ⟺ g | h⁴−1`. The binomials are `h = c ∈ μ_4` (constant). So:

> **PRIZE DEFECT (sharpest form):** does there exist a **non-constant** `h ∈ F_p[X]`, `deg h < n/8`,
> with `(X^{n/4} + h(X)) | (h(X)⁴ − 1)`?  Char-0: NO (only `h∈μ_4` constant). Char-`p` at
> `n=2^30`: the open prize.

Caveat (why this is still the wall, not a crack): on the roots `β` of `g`, the condition says the
polynomial `−h` agrees with the group homomorphism `π:μ_n→μ_4`, `β↦β^{n/4}` (a *monomial*) on a
size-`n/4` subset — i.e. it is **list-decoding the monomial `X^{n/4}` against `deg<n/8` polys**,
the §2 monomial base case, on a self-referentially-chosen subset. The reduction closes into a
fixed point — the signature of a genuine wall. Recorded as the actionable residual; not moved.

## 7. Reproduce
```
python3 -u scripts/probes/probe_444_monomial_descent.py        # descent identity 200/200; monomial list=2 @N=16,32,64
python3 -u scripts/probes/probe_444_nonsym_list_recursion.py 16 # window list 4/7; sym/total=1/L (symmetric tower useless)
python3 -u scripts/probes/probe_444_worstword_exponent.py       # true worst weight-2 word (ignore the buggy unit-factor check)
```
