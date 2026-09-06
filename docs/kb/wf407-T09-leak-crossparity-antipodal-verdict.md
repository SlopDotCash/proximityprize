# #407 T09-leak — the cross-parity leak `A ≡ −g·B` is the antipodal char-0 structure; count = additive-energy excess (W2 / Pan–Xu ideal-SVP)

**Status:** thread T09-leak driven to a `walled` verdict. The cross-parity leak is *reproduced and
re-defined precisely*, then shown to be the **char-0 antipodal (sum-zero) symmetry**, NOT a handle
on genuine spurious mod-`p` defects; its count is exactly the char-`p` additive-energy excess
`E₂^{(p)} − E₂^{(0)}` (wall **W2**), and the fully-split `N(𝔭)=p` short-vector count is the
**Pan–Xu ideal-SVP open gap**. One axiom-clean Lean brick lands the reflection engine. Honesty
contract held: **no closure, no bound on the genuine defect count**. Author: #407 T09-leak lane,
2026-06-14.

## What the leak actually is (precise definition, reproduced)

An `E₂` *collision* of `μ_n ⊂ F_q^×` is `x₁ + x₂ = y₁ + y₂ (mod p)` with `{x₁,x₂} ≠ {y₁,y₂}`.
The `A ≡ −g·B` cross-parity leak, at this depth, is the **multiplicative reflection**
`{x₁, x₂} = c · {y₁, y₂}` (setwise) with `c = −g`, a torus-normalizer image of the pair.

Measured fractions (`scripts/probes/wf407_T09-leak_e2_reflection.py`, exact enumeration):

| n | β=2 (sub-prize) | β≥3 (prize regime `p ≫ n²`) |
|---|---|---|
| 16 | 47 % | **100 %** |
| 32 | 56 % | **100 %** |
| 64 | 72 % | **100 %** |

So the "96–100 % of defects obey `A ≡ −g·B`" is reproduced as a *prize-regime* fact: once
`p ≫ n²`, **every** `E₂` collision is the reflection.

## The structural collapse (the decisive finding)

Decomposing the 100 %-reflection set (`wf407_T09-leak_antipodal.py`, exact):

| n | β | sum-0 (antipodal) | g=−1 neg-sym | **genuine spurious** |
|---|---|---|---|---|
| 16 | ≥2.5 | 100 % | 0 % | **0 %** |
| 32 | ≥3 | 100 % | 0 % | **0 %** |
| 64 | ≥3 | 100 % | 0 % | **0 %** |

The 100 %-reflection collisions are **entirely the antipodal `x₂ = −x₁`, `y₂ = −y₁` (sum-zero)
pairs** — i.e. the char-0 Lam–Leung matchings. And the converse (`wf407_T09-leak_genuine_at_onset.py`,
`wf407_T09-leak_conjugate.py`): the *genuine* spurious defects (nonzero sum) realize the reflection
**0 %** of the time. The leak does NOT see genuine defects.

**Why (the engine, one line, now formalized).** Sum the setwise identity `{x₁,x₂}=c·{y₁,y₂}`:
`x₁+x₂ = c·(y₁+y₂)`. With sum-preservation `x₁+x₂ = y₁+y₂ = s` this is `s = c·s`, so
`(c−1)·s = 0`, hence **`c = 1` or `s = 0`**. A genuine collision has `s ≠ 0` and is not the trivial
`c=1`, so it is *not* a nontrivial reflection. (`WF407_T09Leak.lean :
sum_preserving_dilation_forces_zero`, `genuine_collision_not_reflection`.)

## Turning the leak into a count — the wall (part 2)

`wf407_T09-leak_count_identity.py` (exact): the genuine spurious `E₂` defect count is exactly the
char-`p` additive-energy excess
`#genuine = E₂^{(p)} − E₂^{(0)}`, `E₂^{(0)} = 3n²−3n` (even `n`, antipodal char-0).
Verified: n=16,β=2,p=257 → excess `192` = measured genuine count; excess `→ 0` once `p` exceeds the
`r=2` onset `4^{n/2}`. The product-unit `g = x₁x₂/(y₁y₂)` of genuine defects takes only `4`–`6`
distinct values (clustered, all in `μ_n`) — structured, but **not a single relation**: counting the
leak is `∑_g |μ_n ∩ g·μ_n|`-type, which Cauchy–Schwarz returns to the energy `E₂(μ_n)`. **No count
below the additive-energy / BGK wall (W2, the √n loss).**

## The fully-split / ideal-SVP reduction (part 3)

`q ≡ 1 (mod n)` (the smooth-domain hypothesis) ⟺ `p` splits completely in `ℚ(ζ_n)`: degree-1 primes
`𝔭`, `N(𝔭)=p` (the **fully-split** case). Each genuine `E₂` defect `α = x₁+x₂−y₁−y₂` (a signed sum of
`≤4` roots of unity) is a nonzero element of `𝔭`. The genuine defect count is the count of short
`±1`-combination vectors of the fully-split prime ideal — i.e. enumerating short vectors of `𝔭`.
**Pan–Xu**: cyclotomic ideal-SVP is poly-time only for *non-split* `q`; the fully-split `N(𝔭)=p`
case (exactly ours) is the **OPEN hard case**. The leak's count therefore sits *on* the Pan–Xu wall,
not below it. (This matches the in-tree `SparseSupportIdealSVPLowerBound.lean` /
`CyclotomicNormDefectThreshold.lean`: house `≥ p^{1/φ(n)}` is the Minkowski floor; vacuous at prize
scale; the open part is the *representation mass* of the bounded-house orbit, i.e. the count.)

## Is the leak exploitable below the wall? — NO

Three independent reductions all return the same wall: (i) the reflection is the antipodal char-0
structure (W2 = clean range), (ii) the genuine count is the additive-energy excess (W2), (iii) the
fully-split short-vector count is Pan–Xu ideal-SVP. The leak is a **re-expression** of these walls,
not a lever. The earlier cumulant KB sub-route (A) (`deltastar-407-cumulant-deep-nonbetti-verdict`)
reached the same conclusion from the cumulant side ("`A=−gB` = `|S₀∩(−g)S₀|` = sum-product = BGK; no
cumulant descent"). This lane *proves the engine* (sum-preserving dilation ⟹ sum-zero) and pins the
genuine-vs-antipodal split numerically and rigorously.

## Verdict: `walled`

- **to W2** (additive-energy √n loss): leak count `= E₂^{(p)} − E₂^{(0)}`.
- **to Pan–Xu ideal-SVP** (fully-split `N(𝔭)=p` open case): genuine defects = short vectors of the
  fully-split cyclotomic prime; counting them is the open hard SVP case.

**Delivered (not fabricated):** (1) precise reproduction + correct definition of the leak;
(2) the decisive antipodal-vs-genuine split (100 % reflection = sum-zero, genuine = 0 % reflection);
(3) the exact count identity leak `= E₂^{(p)}−E₂^{(0)}`; (4) axiom-clean Lean reflection engine
`sum_preserving_dilation_forces_zero` proving the leak's 100 %-feature is char-0 antipodal symmetry.
**No bound on the genuine defect count is claimed.**

## Artifacts

- `scripts/probes/wf407_T09-leak_crossparity_bound.py` — support-dilate reading (0 %, rules it out)
- `scripts/probes/wf407_T09-leak_parity_split.py` — `|S₀ ∩ g·S₀|` direct (`|S₀|=3^{half/2}` law)
- `scripts/probes/wf407_T09-leak_e2_reflection.py` — reflection reading → **100 % in prize regime**
- `scripts/probes/wf407_T09-leak_antipodal.py` — **the split: 100 % reflection = antipodal sum-0**
- `scripts/probes/wf407_T09-leak_genuine_at_onset.py` — genuine defects: 0 % reflection
- `scripts/probes/wf407_T09-leak_conjugate.py` — genuine product-unit `g` ∈ small set, not fixed
- `scripts/probes/wf407_T09-leak_count_identity.py` — leak count `= E₂^{(p)} − E₂^{(0)}` (exact)
- `Research/ProximityPrize/Frontier/WF407_T09Leak.lean` — axiom-clean reflection engine

Cross-refs: `deltastar-407-cumulant-deep-nonbetti-verdict-2026-06-13.md` (sub-route A),
`deltastar-407-sparse-support-ideal-svp-verdict-2026-06-13.md`,
`RESEARCH_SYNTHESIS_407_CONNECTIONS.md` C042/C032/C068, `SumProductBridge.lean`,
`CyclotomicNormDefectThreshold.lean`, `SparseSupportIdealSVPLowerBound.lean`.
