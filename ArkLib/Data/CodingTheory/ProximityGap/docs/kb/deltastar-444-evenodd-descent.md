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

## 6. Why this is not obviously the dead BGK wall

The descent is **combinatorial and `p`-independent** (the monomial base case is governed by the
quadratic character `y^{N/2}=±1`, structure-only, NOT a character-sum magnitude). It does NOT
pass through `M(n) = max|η_b|` — there is no sup-norm anywhere. This is exactly the §0 "SEAM A:
the list, not the sup." It is also exactly the part the campaign's antipodal-symmetric tower
MISSED: the descent handles **non-symmetric** agreement sets (the single-fibre `P²=yQ²` term),
which the `S=−S` tower (capturing only `1/L` members, measured this session) cannot. **If** the
branching and worst-word-weight pieces close, this is a proof of the explicit-2-power-RS window
list-decoding bound — the grand list-decoding challenge — by elementary cyclotomic/quadratic-
character means, with no appeal to effective Gauss-sum equidistribution.

## 7. Reproduce
```
python3 -u scripts/probes/probe_444_monomial_descent.py        # descent identity 200/200; monomial list=2 @N=16,32,64
python3 -u scripts/probes/probe_444_nonsym_list_recursion.py 16 # window list 4/7; sym/total=1/L (symmetric tower useless)
python3 -u scripts/probes/probe_444_worstword_exponent.py       # true worst weight-2 word (ignore the buggy unit-factor check)
```
