# The far-line binding object = subset sums / Schur-ratios of μ_n (#444, sharpening)

*Status: VERIFIED reframing of the c=1 binding object; reduces to the additive structure of μ_n =
the BGK wall. Honest: a clean concrete identity, not a closure.*

## The identity (verified exact, n=16, k=2/3/4)

The far-line MCA incidence `#bad γ` for the non-symmetric binomial direction `x^{k+1}+γx^k`
(agreement `s=k+1`, so `c=s−k=1`) equals **EXACTLY** the number of distinct `(k+1)`-subset sums
of `μ_n`:
> `#bad γ = #{ Σ_{t∈T} t : T ⊆ μ_n, |T|=k+1 }` (verified: 464/1233/2256 at n=16, k=2/3/4, p=65537).

*Derivation:* a bad `γ` ⟺ some `(k+1)`-subset `T` has `x^{k+1}+γx^k` interpolable by deg-`<k`,
i.e. the order-`(k+1)` divided difference vanishes: `DD(x^{k+1}) + γ·DD(x^k) = 0`. Since
`DD_{k+1}(x^{k+1}) = h_1(T) = Σ_{t∈T} t` and `DD_{k+1}(x^k) = h_0(T) = 1`, this gives
`γ = −Σ_{t∈T} t`. So distinct bad `γ` ⟺ distinct subset sums. ∎

For a general binomial `x^a+γx^b`: `γ = −h_{a−k}(T)/h_{b−k}(T)` (ratio of complete homogeneous
symmetric functions = Schur `s_{(a−k)}/s_{(b−k)}`), so `#bad γ = #distinct Schur-ratios over T`.

## Why this is the wall (not a crack)

- At `c=1` (`s=k+1`) the count is `#distinct subset sums ≈ C(n,k+1) − (additive-energy correction) ≫ n`
  (verified `464 ≫` budget `16`). So `c=1` is FAR over budget — a bad (sub-δ*) radius.
- δ* sits at **deeper `c = s−k = Θ(n/log n)`**, where the binding object is the count of
  `s`-subsets `T` for which the `c` divided-difference conditions on `x^a+γx^b` are *simultaneously
  consistent* for some `γ` (an over-determined, codimension-`(c−1)` condition on `T`). This is the
  **additive energy of `μ_n` at depth `c`** = the BGK / thin-subgroup character-sum wall.
- The number of distinct subset sums (and its concentration as `s` grows) is governed by the
  additive structure / additive energy of `μ_n`, which is exactly the open object.

## What this adds

A clean, classical-flavored framing: the prize binding object is the **subset-sum / Schur-ratio
distribution of the multiplicative subgroup `μ_n`** — connecting it to additive-combinatorics
literature on subset sums of structured sets (Erdős–Heilbronn, Davenport constant, sumsets of
subgroups). It does NOT bypass the wall (the concentration of these sums = the additive energy),
but it is a concrete reformulation that may invite tools from that literature. δ\* OPEN.
Reproduce: `python3 -u scripts/probes/probe_444_subsetsum_binding.py`.

## UNIFICATION with the O_P orbit thread (Schur-ratio dilation-equivariance ⟹ the orbit formula)

The bad-γ Schur-ratio is a **dilation eigenvector**: under `T ↦ gT` (`g∈μ_n`),
`γ(gT) = −h_{a−k}(gT)/h_{b−k}(gT) = g^{(a−k)−(b−k)}·γ(T) = g^{a−b}·γ(T)`. So the dilation `×g`
acts on bad-γ values by `×g^{a−b}`, and the bad set is a union of orbits of the cyclic group
`⟨g^{a−b}⟩` of size `n/d`, `d=gcd(a−b,n)`. Therefore:

> **`#bad γ = [γ=0 is bad] + (n/d)·O_P`**, where `O_P` = # distinct nonzero Schur-ratio cosets.

VERIFIED exact (n=16, k=2, p=65537): `x^5+γx^3` (d=2): `233 = 1 + 8·29`; `x^9+γx^7` (d=2):
`129 = 1 + 8·16`; `x^6+γx^4` (d=2): `232 = 0 + 8·29`; `x^3+γx^2` (d=1): `464 = 0 + 16·29`.

This **DERIVES the campaign's orbit law `#bad = 1 + (n/2)·orbits`** (the `d=2` / imprimitive case,
0xSolace/lalalune) from the Schur-ratio's dilation-equivariance — a cleaner, additive-side reason
for it. The open **`O_P=1` persistence** (binding `d=2` direction = a single Schur-ratio coset for
all `n=2^μ`) is exactly "the nonzero bad Schur-ratios `−h_{a−k}(T)/h_{b−k}(T)` collapse to one
`μ_{n/2}`-coset." A descent attack: under squaring `μ_n→μ_{n/2}`, `h_j(T)` of antipodal-symmetric
`T` relates to `h` on the squared half (the even/odd descent), so the single-coset structure may be
provable by induction — a concrete route to `O_P=1` (the Johnson-proxy face; the p-dependent BGK
sup-norm prize stays separate/open).

## The symmetric-function descent identity (VERIFIED — the engine for an O_P=1 proof)

For any `T ⊆ μ_n` closed under negation (`T = −T`, antipodal-symmetric), with half-set `H` (one of
each `±` pair, so `T = H ⊔ (−H)`):
> **`h_{2j}(T) = h_j(H²)` and `h_{2j+1}(T) = 0`** (where `H² = {t² : t∈H} ⊆ μ_{n/2}`).
*Proof:* `Σ_j h_j(T) x^j = ∏_{t∈T} 1/(1−tx) = ∏_{t∈H} 1/((1−tx)(1+tx)) = ∏_{t∈H} 1/(1−t²x²) =
Σ_j h_j(H²) x^{2j}`. ∎ VERIFIED exact: 180/180 trials (n=16, j=1,2,3, antipodal-symmetric T).

**Consequence for `O_P=1`.** The bad Schur-ratio `γ(T) = −h_{a−k}(T)/h_{b−k}(T)`: for
antipodal-symmetric `T` with `a−k, b−k` even, `γ(T) = −h_{(a−k)/2}(H²)/h_{(b−k)/2}(H²)` = the
Schur-ratio of the descended direction on `μ_{n/2}`. So if the binding bad set is antipodal-symmetric
(or reduces to it) and the descended direction's `O_P` is `1`, then `O_P(n) = O_P(n/2)` and `O_P=1`
follows by induction from a small base case. **This is a concrete proof ENGINE for the open `O_P=1`
persistence statement** — NOT a completed proof (it still needs: (i) the binding `d=2` direction's
exact `(a,b)` and agreement; (ii) that its bad set is antipodal-symmetric with even `a−k,b−k`; (iii)
the base case). Offered as a tool. (Johnson-proxy face; the BGK sup-norm prize stays separate/open.)

## The binding O_P=1 configuration, PINNED (verified n=16)

The far-line binding direction is **`x^{n/2+1} + γ·x^{n/2−1}`** (`a=n/2+1, b=n/2−1`, `d=gcd(a−b,n)=2`).
Verified (n=16, k=4, p=65537): the γ-orbit count `O_P` collapses with agreement depth `c`:
`c=1: O_P=196 → c=2: 9 → c=3: O_P=1 (#bad=9=1+8·1) → c=4: 1`. The binding is `c=m*=3`, where
`O_P=1` and `#bad = 1 + (n/2)·1 = 9 ≤` budget (lalalune's benign-plateau / orbit law confirmed
from the Schur-ratio side). `O_P=1` ⟺ **all bad `T` (size `s=k+c`) form a single dilation orbit**.

**Obstruction for the descent proof (honest).** At the binding, `a−k = n/2+1−k` and `b−k = n/2−1−k`
are both **ODD** (e.g. 5, 3 at n=16). For antipodal-symmetric `T`, `h_{odd}(T)=0`, so the Schur-ratio
`−h_{a−k}(T)/h_{b−k}(T) = 0/0` is undefined — the bad `T` are therefore **non-antipodal-symmetric**.
So the clean `h_{2j}(T)=h_j(H²)` engine (which needs even `a−k,b−k`) does NOT directly apply; proving
`O_P=1` persistence requires the **full even/odd NON-symmetric descent** (`Sweep_A40`,
`|S| = 2·#{P=Q=0} + #{Q≠0 ∧ P²=yQ²}`) applied to the bad-`T` orbit structure. That is the precise
remaining gap for an `O_P=1` proof: show the single bad-`T` dilation orbit persists under the
non-symmetric squaring descent. (Johnson-proxy face; BGK sup-norm prize separate/open.)

## The binding = character-twisted NODAL direction (structural insight + why easy descent fails)

Since `x^{n/2} = χ(x)` (quadratic character, `±1`), the binding direction factors:
> **`x^{n/2+1} + γ·x^{n/2−1} = χ(x)·(x + γ/x) = χ(x)·(x²+γ)/x`** — the **character-twisted nodal
> direction** (`x+γ/x` = the campaign's nodal far-direction, `[[arklib-389-subjohnson-exact-line]]`).

`x+γ/x` is ODD under `x→−x`; on a full fibre `{x,−x}` the agreement `f·x^{n/2+1}=x²+γ` forces
`f(x)=−f(−x)`, i.e. `f` is an **odd** codeword `f=x·G(x²)`. The even/odd descent (`y=x²`,
`χ(x)=χ'(y)=y^{n/4}`) then reduces the agreement to `G(y)·χ'(y)·y = y+γ` on `μ_{n/2}`, i.e. `G`
agrees with the word **`χ'(y)·(1+γ/y)`** on `μ_{n/2}`.

**Why the easy descent does NOT close `O_P=1` (honest).** The descended word `χ'(y)·(1+γ/y)` is
NOT the same form as the original `χ(x)·(x+γ/x)` — the monomial part changed `x → 1` (`x+γ/x`
became `1+γ/y`). So the recursion is **not self-similar**, and `O_P=1` does not follow by a naive
induction `n→n/2`. A proof needs to track the changing word-form down the tower (or a direct
single-orbit argument on the bad-`T` set). This is the precise remaining obstruction — a real
sharpening of the open `O_P=1` statement, now reduced to "does the single bad-`T` orbit persist
under the non-self-similar nodal descent `χ(x+γ/x) → χ'(1+γ/y)`." (Proxy face; BGK prize separate.)

## CONFIRMED: binding bad-T are all non-symmetric ⟹ O_P=1 proof needs the single-fibre term

Verified (n=16, binding `x^9+γx^7`, c=3, s=7): the 64 nonzero-bad `T` are **ALL non-antipodal-
symmetric** (0 symmetric), giving 8 distinct bad γ = `(n/2)·O_P`, `O_P=1`. So the agreement sets are
single-fibre. The clean full-fibre descent (odd word ⟹ `P=0` ⟹ odd codeword ⟹ collapse to a
monomial pair, which would prove `O_P=1` trivially) **does NOT apply** — it requires full-fibre
(symmetric) agreement, which these bad `T` are not. The proof of `O_P=1` therefore genuinely requires
the **single-fibre `#{Q≠0 ∧ P²=yQ²}` term** of the even/odd descent (`Sweep_A40`): track how the
non-symmetric bad-`T` orbit collapses to a single coset under the single-fibre map. This is the
precise, confirmed remaining obstruction for an `O_P=1` proof — neither the clean symmetric descent
(`h_{2j}=h_j(H²)`) nor naive self-similar induction closes it. (Proxy face; BGK sup-norm prize open.)

## ⚠️ CORRECTION + CRACK: the obstruction above was WRONG — O_P=1 at n=16 is PROVEN (char-0)

*The "non-symmetric T ⟹ need single-fibre term" note above looked at the WRONG object (the
size-`s` agreement set `T`), not the natural invariant (the size-`s+1` LEVEL SET / the gapped
polynomial). The level set IS antipodal-symmetric and descends cleanly. Below supersedes it.
Probes: `probe_444_gapped_product.py`, `probe_444_gapped_structure.py`, `probe_444_odd_descent.py`,
`probe_444_e2_reduction.py`, `probe_444_e2_charzero.py`, `probe_444_descent_n32.py`.*

**Step 1 — the gapped-polynomial reformulation (verified 64/64, n=16).** Multiplying the binding
agreement `f = χ(x)(x+γ/x)` by `x^{n/2+1}` (using `χ=x^{n/2}`, `χ²=1`) gives `ψ_f(x) := f(x)·x^{n/2+1}
− x² = γ` on `T`. So **`T` is a level set of `ψ_f`**, and `ψ_f − γ = V_T·W` is a polynomial with
support `{0,2} ∪ [n/2+1, n/2+k]` — heavily GAPPED. The full level set has size `s+1 = n/2 = 8`
(`T` is any `s`-subset of it; `W` has 1 root in `μ_n`, explaining the `C(8,7)=8`-fold `T`-overcount:
8 configs × 8 sub-`T` = 64 bad `T`).

**Step 2 — bad `f` are ODD ⟹ even descent (verified 100%).** The support `{0,2,10,12}` is **all
even** ⟹ `ψ_f − γ` is an even polynomial ⟹ **the bad `f` are exactly the ODD polynomials**
`f = c₁x + c₃x³` (since `x^{n/2+1}` is odd, `f` odd makes `f·x^{n/2+1}` even, matching `−x²−γ`). The
level set is therefore **antipodal-symmetric** and descends to `Φ_γ(y)` on `μ_{n/2}=μ_8` (`y=x²`).
*This is the resolution of the bogus obstruction: the natural object is symmetric; only the chopped
size-`s` `T` is not.*

**Step 3 — the `e₂=0` Vieta reduction (verified MATCH=True vs direct).** Clearing `Φ_γ(y)=c₃y⁶+c₁y⁵
−y−γ` by `y³` on `μ_8` (`y⁶=y⁻²,y⁵=y⁻³`) gives the **monic degree-`n/4=4`** polynomial
`y⁴+γy³+0·y²−c₃y−c₁`, which must split completely over `μ_8`. By Vieta:
> **bad γ ⟺ ∃ 4-subset `{η_j}⊆μ_8` with `e₂(η)=0`, and `γ = −e₁(η)`.**

**Step 4 — `e₂=0` is CHAR-0, and the subsets form ONE shift-orbit (PROVEN).** `e₂=0` on `μ_8` is the
cyclotomic vanishing `M_r=M_{r+4}` of pairwise-sum multiplicities (`ζ⁴=−1`), **p-independent**
(verified identical at p=17,41,73,97,65537). The 10 such 4-subsets split as **2 with `e₁=0`** (the
`μ_4`-cosets `{0,2,4,6},{1,3,5,7}` ⟹ trivial `γ=0`) **+ 8 with `e₁≠0`**, and those 8 are exactly the
single shift-orbit `{0,1,2,5} + t (mod 8)`. One dilation orbit ⟹ **`O_P=1`, char-0. ∎**

> **This is a genuine CLOSED proof of the binding `O_P=1` at n=16** (the Johnson-proxy face), via a
> new mechanism: **odd-descent + `e₂=0` cyclotomic rigidity**. It does not use the size-`s` single-
> fibre term at all.

**Step 5 — HONEST boundary: it does NOT generalize cleanly; the wall intrudes at n=32.** The same
reciprocal-to-monic descent for general `n` gives a monic degree-`n/4` poly over `μ_{n/2}` with
`J = n/4 − 1 − k/2` forced-zero conditions `e₂=…=e_{J+1}=0`, `γ=−e₁`. At **n=32** (`μ_16`,
8-subsets): the natural `J=1` object (`e₂=0`) is **char-`p` DEPENDENT** — counts 150/118/**70** and
`O_P` = 9/7/**4** at p=97/193/65537 (NOT 1, and not p-independent); `J=2,3` over-constrain to only the
2–6 trivial `e₁=0` subsets (`O_P=0`). So **no integer condition-depth lands a clean char-0 `O_P=1` at
n=32** — the char-`p` defect (the BGK wall) is already present in the descended object. *Caveat: the
n≥32 descent model is NOT yet validated against a direct computation (infeasible brute-force), so the
"char-`p` at n=32" is a property of the natural descended object, not a proven statement about the true
binding.* **Net:** the clean char-0 `O_P=1` is established at **n=16 only**; its persistence to all
`n=2^μ` (the full proxy claim) is **not** closed by this descent, and the char-`p` intrusion at n=32
is consistent with the prize being the char-`p` additive-energy defect. (BGK sup-norm prize: open.)

## Step 6 — DECISIVE: `O_P=1` FAILS in char-0 by n=32; defect onset at μ₁₆ (`probe_444_OP1_persistence.py`)

Settling Step 5 at the cyclotomic (model-independent) level — the `e₂=0` object compared
char-0 (`M_r=M_{r+N/2}` balance) vs char-`p` (`e₂≡0 mod p`) across primes:

| `n` (descent group) | char-0 `e₂=0` count | char-0 `O_P` | char-`p` counts (small→large `p`) | defect onset |
|---|---|---|---|---|
| `n=16` (`μ_8`, 4-subsets) | 10 (= 2 triv + 8) | **1** | 10,10,10,10,10 (p=17..65537) | **none** |
| `n=32` (`μ_16`, 8-subsets) | 70 (= 6 triv + 64) | **3** | 150,118,86,**70** (p=97,193,257,65537) | **yes (→0 by 65537)** |

**One model-independent conclusion stands; the "refutation" framing is RETRACTED.**
1. **(STANDS) The char-`p` additive-energy defect (the BGK wall) has its ONSET at `μ_16`.** On `μ_8`,
   `e₂=0` has zero defect at every prime (char-0 = char-`p` = 10). On `μ_16` the char-`p` count
   exceeds char-0 at small `p` (`70` char-0; char-`p` `150/118/86/70` at p=97/193/257/65537; defect
   `{80,48,16,0}`), killed only once `p` is large enough — a clean small-scale picture of the wall,
   with the defect-killing threshold = the norm bound (`Sweep_A10`).
2. **(⚠️ RETRACTED) "`O_P=1` fails in char-0 by `n=32`" was OVERSTATED.** The `char-0 O_P = 3` figure
   is for the `e₂=0` 8-subsets of `μ_16` — but that object is the **`J=1` / `level-set=n/2` config at
   rate `ρ=3/8`** (the `J=1` instance drifts `ρ=1/4 → 3/8` as `n: 16 → 32`), **not** the prize-rate
   `ρ=1/4` binding (which in the model is `J=3`, where the bad set *vanishes*, `O_P=0`). And crucially
   the model's identification with the *true* `n=32` binding rung is unvalidated.

**Why the retraction (`probe_444_OP_direct_sweep.py`, direct, no model).** Direct `O_P(c)` sweeps:
`n=8` (`x^5+γx^3`): `c=1` O_P=4 → `c=2` **O_P=1** (level-set=4=`n/2`, binding) → `c≥3` O_P=0 (bad set
vanishes). `n=16` (`x^9+γx^7`): `c=1` O_P=196 → `c=2` O_P=9 → `c=3` **O_P=1** (level-set=8=`n/2`,
binding) → `c=4` O_P=1 → `c=5` O_P=0. So **(a)** the `O_P=1` onset coincides exactly with
`level-set = n/2` (the config this descent encodes — validating the `n=16` brick), **(b)** `O_P=1`
holds on a finite `c`-window then the bad set vanishes (`O_P → 0`, not `> 1`), and **(c)** NubsCarson's
direct sweep + lalalune/0xSolace's Schur-ratio orbit law independently confirm `O_P=1` at the binding
for `n=8,16`. **Net honest status:** `O_P=1` at the binding is *directly confirmed* for `n ≤ 16`;
persistence to `n ≥ 32` is **OPEN** (the descent model's `n=32` behavior is rate-dependent and not
validated as the binding rung; direct brute-force is infeasible). The model-independent `μ_16` char-`p`
defect onset is the one solid new fact, and it is consistent with the prize being the char-`p`
additive-energy wall. NO prize closure; the BGK wall stands.
