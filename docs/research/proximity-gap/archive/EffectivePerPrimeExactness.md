# Effective per-prime exactness for subgroup subset-sum images
### (P-A lower half, issue #232 — removing the averaging and the Siegel–Walfisz/GRH input on an explicit field range)

Lane: `nubs/issue232-effective-pa` (claimed in #232 before work began). Date: 2026-06-09.
Author: nubs. Status: **paper proof, complete; verified numerically by
`scripts/probes/probe_norm_threshold.py` (deterministic, exit-0 = all checks pass).**
This note is self-contained: it restates the pieces of the averaged lower-half chain it
builds on (the char-0 image formula and the Lift Lemma, due to the prior #232 research
cycle — research-KB Entries 5–9, mirrored in DISPROOF_LOG as the O11′–O15 arc) with
proofs, then adds the new effective per-prime theorems. Nothing here touches the upper
half (P-B / descent program O13–O13″).

---

## 0. Setting

Fix `m = 2^k ≥ 8`. Let `ζ = ζ_m` be a primitive m-th root of unity, `K = ℚ(ζ)`,
`φ(m) = m/2`, `O_K = ℤ[ζ]`, with power basis `{ζ^j : 0 ≤ j < m/2}` (a ℤ-basis of `O_K`),
and `ζ^{j+m/2} = −ζ^j`, so `μ_m` consists of the `m/2` pairs `±ζ^j`.

For a prime `p ≡ 1 (mod m)`, `p` splits completely in `K`; fix `𝔭 | p` with
`O_K/𝔭 ≅ F_p`. Reduction mod `𝔭` maps `μ_m` bijectively onto the order-`m` subgroup
`G ⊆ F_p^×` (injectivity: for `0 < d < m`, `N_{K/ℚ}(1 − ζ^d)` is a power of 2 while
`p` is odd, so `ζ^d − 1 ∉ 𝔭`; the image is then all `m` roots of `x^m − 1` in `F_p`).
For an `r`-subset `S ⊆ G` write `e₁(S) = Σ_{x∈S} x ∈ F_p`.

**Pattern parametrization (char-0 image formula; prior work, restated).** Choosing an
`r`-subset of `μ_m` = choosing, per basis pair `{ζ^j, −ζ^j}`: none / `+ζ^j` / `−ζ^j` /
both ("both" sums to 0). So every subset sum equals `σ(ε) := Σ_j ε_j ζ^j` for a sign
pattern `ε ∈ {−1,0,1}^{m/2}`, where `s := |supp ε|` must satisfy

    s ≡ r (mod 2),   and   r − s = 2·#both ≤ 2(m/2 − s)   ⟺   s ≤ m − r,

together with `s ≤ r` (from `#both = (r−s)/2 ≥ 0`), i.e.
`s ≤ s_max(m,r) := min(r, m−r)` (and `s ≤ m/2` never binds separately, since
`min(r, m−r) ≤ m/2`). By ℤ-linear
independence of the power basis, `σ` is injective on patterns, so in characteristic 0
the image size is exactly

    N₀(m,r) = Σ_{s ≡ r (2), s ≤ min(r, m−r)} C(m/2, s) · 2^s.

(Numerically confirmed many times over: 41 = N₀(8,4), 3281 = N₀(16,8), 3280 = N₀(16,9),
21,523,360 = N₀(32,17), …)

**Definition (modular collision).** Distinct admissible patterns `ε ≠ ε′` at layer `r`
with `σ(ε) ≡ σ(ε′) (mod 𝔭)`. No collisions ⟺ the `e₁`-image on `r`-subsets of `G` has
size exactly `N₀(m,r)` (and all fibers match the char-0 fibers).

---

## 1. Theorem E1 (second-moment identity and the AM–GM norm bound)

**Theorem E1.** Let `α = Σ_{j<m/2} c_j ζ^j` with `c ∈ ℤ^{m/2}`, `α ≠ 0`. Then:

**(i)** `Σ_{i ∈ (ℤ/m)^×} |σ_i(α)|² = (m/2) · Σ_j c_j²`  (exact identity), and

**(ii)** `|N_{K/ℚ}(α)| ≤ (Σ_j c_j²)^{m/4}`.

*Proof.* (i) The embeddings of `K` are `σ_i : ζ ↦ ζ^i` for the `m/2` odd residues
`i (mod m)`. Expand, using `conj(σ_i(α)) = Σ_{j'} c_{j'} ζ^{−ij'}`:

    Σ_i |σ_i(α)|² = Σ_{j,j'} c_j c_{j'} · Σ_{i odd (mod m)} ζ^{i(j−j')}.

Fix `d = j − j'`, `|d| ≤ m/2 − 1`. For `d = 0` the inner sum is `m/2`. For `d ≠ 0`:
the full sum `Σ_{i mod m} ζ^{id} = 0` (since `m ∤ d`), and the even-index sum
`Σ_{i even} ζ^{id} = Σ_{t mod m/2} (ζ^{2d})^t = 0` as well, because `ζ^{2d} ≠ 1`
(`m ∤ 2d` since `0 < |d| < m/2`). Subtracting, the odd-index sum is `0`. Only the
diagonal `j = j'` survives, giving `(m/2) Σ_j c_j²`.

(ii) `|N_{K/ℚ}(α)|² = Π_{i} |σ_i(α)|²` over the `m/2` embeddings. By AM–GM applied to
the `m/2` nonnegative reals `|σ_i(α)|²` and (i):

    |N(α)|^{4/m} = (Π_i |σ_i(α)|²)^{2/m} ≤ (2/m) Σ_i |σ_i(α)|² = Σ_j c_j². ∎

**Remark (what this replaces, and sharpness).** The sup-norm argument
(`|σ_i(α)| ≤ Σ|c_j| ≤ m` for `c ∈ {−2..2}^{m/2}`) gives `|N(α)| ≤ m^{m/2}`; the KK25
sketch's resultant bound needs `p > φ(m)^{φ(m)} = (m/2)^{m/2}`. E1(ii) with
`Σc² ≤ 2m` gives `(2m)^{m/4}` — the exponent is halved and the base improved. Two
side facts: `K` is totally imaginary, so `N_{K/ℚ}(α) > 0` always (the absolute values
are cosmetic); and E1(ii) is attained with *exact equality* on the family
`α = 2(ζ^0 − ζ^{m/4})` (e.g. `α = 2 − 2i`: all conjugates have `|σ_i(α)|² = 8`, so
`N(α) = 8^{m/4} = (Σc²)^{m/4}` exactly) — the inequality has no slack to give in
general:

| m | sup-norm `m^{m/2}` | KK25 `(m/2)^{m/2}` | **E1: `(2m)^{m/4}`** |
|---|---|---|---|
| 16 | 2^32 | 2^24 | **2^20** |
| 32 | 2^80 | 2^64 | **2^48** |
| 64 | 2^192 | 2^160 | **2^112** |
| 128 | 2^448 | 2^384 | **2^256** |

---

## 2. Corollary E2 (per-prime exactness thresholds)

For a layer-`r` collision the difference vector `c = ε − ε′ ∈ {−2,…,2}^{m/2}` satisfies

    Σ_j c_j² ≤ 4·min(r, m−r).

*Proof.* With `A = supp ε`, `A' = supp ε'`, `t = |A ∩ A'|`, `s = |A| ≤ s_max`,
`s' = |A'| ≤ s_max`: each `j ∈ A ∩ A'` contributes `(ε_j − ε'_j)² ≤ 4`, each `j` in the
symmetric difference contributes `1`, so `Σ c² ≤ 4t + (s−t) + (s'−t) = s + s' + 2t`.
Since `s ≤ s_max`, `s' ≤ s_max`, and `t ≤ min(s, s') ≤ s_max`, this is
`≤ 4·s_max = 4·min(r, m−r)`. ∎ (Tight: `ε' = −ε` with `s = s_max` and all-opposite
signs attains it — and exhaustive enumeration over all admissible same-layer pairs at
m = 8 (every r) and m = 16 (every r) confirms the maximum of `Σc²` equals
`4·min(r, m−r)` exactly at every layer. An earlier draft asserted the intermediate
step `s + s' + 2t ≤ 4·min(s,s')`, which is false for `s ≠ s'`; the bound above is the
corrected chain — caught in adversarial review, statement unaffected.)

**Corollary E2.** Define `T(m,r) := (4·min(r, m−r))^{m/4}` and `T_all(m) := (2m)^{m/4}`.
Let `p ≡ 1 (mod m)` be prime.

**(a)** If `p > T(m,r)`, there are **no layer-`r` modular collisions**: the `e₁`-image on
`r`-subsets of the order-`m` subgroup `G ⊆ F_p^×` has size **exactly `N₀(m,r)`**, with
char-0 fibers.

**(b)** If `p > T_all(m)`, this holds for **every `r ≤ m` simultaneously**, including no
cross-layer coincidences beyond the char-0 ones.

**(c)** (support-graded) If `p > (4t)^{m/4}`, every collision relation `c` (any layers)
has `|supp(c)| > t`.

*Proof.* A collision gives `α = σ(ε) − σ(ε′) = σ(c) ∈ 𝔭 ∖ {0}` (nonzero by power-basis
independence). Then `𝔭 | (α)` as ideals, so `p = N𝔭` divides `N((α)) = |N_{K/ℚ}(α)|`,
hence `p ≤ |N(α)| ≤ (Σc²)^{m/4}` by E1(ii). For (a) apply the layer-`r` support bound
above; for (b) note any two distinct patterns from any layers satisfy the full-box
bound `Σc² ≤ 4·(m/2) = 2m`; for (c) use `Σc² ≤ 4·|supp c|`. Take contrapositives. ∎

**Thresholds at the prize layers** `r = ρm + 1`:

| ρ | m=16 | m=32 | m=64 | m=128 |
|---|---|---|---|---|
| 1/2 | T=28⁴=614,656 ≈ 2^19.2 | 60⁸ ≈ 2^47.3 | 124¹⁶ ≈ 2^111.3 | 252³² ≈ 2^255.3 |
| 1/4 | 20⁴ ≈ 2^17.3 | 36⁸ ≈ 2^41.4 | 68¹⁶ ≈ 2^97.4 | 132³² ≈ 2^225.4 |
| 1/8 | — | 20⁸ ≈ 2^34.6 | 36¹⁶ ≈ 2^82.7 | 68³² ≈ 2^194.80 |
| 1/16 | — | — | 20¹⁶ ≈ 2^69.15 | 36³² ≈ 2^165.44 |

Three immediate reality checks (all confirmed by the 2026-06-09 probe run, all PASS,
exit 0; independently re-run and re-derived by a four-lens adversarial review panel):

1. `T(16,9) ≈ 2^19.23` is consistent with — and explains — the previously observed
   exactness at the probe prime `p = 786,433 ≈ 2^19.6`. The exhaustive scan of *all*
   primes `≡ 1 (mod 16)` up to 2.2·10⁶ at layers r ∈ {5, 8, 9} pins the true onset:
   the largest deficient prime is `205,553 ≈ 2^17.65` (layers 8 and 9; `43,793` at
   layer 5), and every prime above it is exact. So `T` is a *sufficient* threshold,
   ~3× loose at m=16 — it does not claim to be the exact onset.
2. `T(32,17) ≈ 2^47.3 < 2^64`: m=32 exactness **at Goldilocks is now a theorem**, and
   the probe confirms both predictions *exactly*: image(r=17) = N₀ = 21,523,360 and
   image(r=16) = N₀ = 21,523,361 (full MITM enumeration, no sampling).
3. BabyBear (`≈2^30.9`) sits **below** `T(32,17)`, and the probe finds genuine
   deficiency there: exact image `21,477,408` = 99.787% of N₀ (45,952 values lost).
   The transition zone is real, not an artifact of a loose bound (see §4).

---

## 3. Corollary E3 (unconditional per-prime lower bounds for the Grand MCA determination)

**Lift Lemma (prior work — restated with proof for self-containedness).** Let
`n = 2^a | p − 1`, `k = ρn ∈ ℤ`, gap `η = 1/m'` with `m' | n` a 2-power, `c = n/m'`,
`r = ρm' + 1`, `δ = 1 − ρ − η`. Let `H ⊆ F_p^×` be the order-`n` subgroup (smooth
domain), `G = {x^c : x ∈ H}` the order-`m'` subgroup, `C = RS[F_p, H, k]`, and the line
`λ ↦ u₀ + λu₁` with `u₀ = (x^{rc})_{x∈H}`, `u₁ = (x^{(r−1)c})_{x∈H}`.

**(i)** *(far-ness)* `(r−1)c = ρn = k`, and for any codeword `ĉ` (`deg ĉ < k`) the
polynomial `X^k − ĉ(X)` is nonzero of degree `k`, so `u₁` agrees with any codeword on
`≤ k < k + c = (1−δ)n` points of `H`. Hence the pair `(u₀, u₁)` has **no** joint
`(1−δ)n`-agreement set, and *every* `δ`-close point of the line is MCA-bad.

**(ii)** *(bad scalars)* For an `r`-subset `Ŝ ⊆ G`, division with remainder by
`Π_{a∈Ŝ}(X−a) = X^r − e₁(Ŝ)X^{r−1} + e₂X^{r−2} − …` gives
`X^r − e₁(Ŝ)X^{r−1} ≡ u_Ŝ(X) (mod Π)` with `deg u_Ŝ ≤ r−2`. Substituting `X ↦ X^c`:
the codeword `u_Ŝ(X^c)` (degree `(r−2)c = k − c < k`) agrees with `u₀ + λu₁` at
`λ = −e₁(Ŝ)` on the `c`-fold preimage of `Ŝ` in `H` — exactly `rc = (ρ+η)n = (1−δ)n`
points. So `λ = −e₁(Ŝ)` is a `δ`-close, hence MCA-bad, point.

**(iii)** Distinct `e₁`-values give distinct bad `λ`, so
`ε_mca(C, 1−ρ−η) ≥ (#e₁-image on r-subsets of G)/p`. ∎

**Theorem E3 (effective per-prime window lower bound).** For every prime `p` with
`p ≡ 1 (mod n)` and

    T(m', ρm'+1)  <  p  <  2^128 · N₀(m', ρm'+1),

the code `C = RS[F_p, H_n, ρn]` (any 2-power `n` with `m' | n | p−1`) satisfies

    ε_mca(C, 1 − ρ − 1/m')  ≥  N₀(m', ρm'+1)/p  >  2^−128,

hence `δ*_C < 1 − ρ − 1/m'` whenever `δ*_C` exists. **Unconditional, effective,
per-prime** — no averaging over primes, no Siegel–Walfisz, no GRH. ∎ (E2(a) + Lift.)

**Existence caveat (important for honest reading).** Two floors limit when the prize
threshold `δ*_C` (largest `δ` with `ε_mca ≤ 2^−128`) exists at all: unconditionally,
the machine-checked general bound `ε_mca(C, δ) ≥ 1/|F|` for all `δ` up to capacity
(issue #232, §7) makes `δ*_C` nonexistent for `|F| < 2^128`; and the Table-1 row
`ε_mca(C, 0) = 2/|F|` pushes this to `|F| ≥ 2^129` under the natural monotonicity of
`δ ↦ ε_mca` (the prize's own "largest δ with…" framing presumes the sub-level set is an
interval). The prize text accordingly assumes "`|F|` sufficiently large". Therefore:

- For `p ∈ [2^129, ceiling)` the statement above **is** a `δ*` pin.
- For production-size fields (`p < 2^129`: BabyBear, KoalaBear, Goldilocks…) the content
  is the **quantitative ε_mca floor** `ε_mca(C, 1−ρ−1/m') ≥ N₀/p` (≈ `2^−39.64` at
  Goldilocks, ρ=1/2, η=1/32 — astronomically above 2^−128); no `δ*` exists there at all.

**Per-prime windows at the prize layers** (`window = (max(T, 2^129), 2^{128+log₂N₀})`,
empty if the lower end exceeds the upper):

| ρ | η=1/32 (m'=32) | η=1/64 (m'=64) | η=1/128 (m'=128) |
|---|---|---|---|
| 1/2 | [2^129, 2^152.36) | [2^129, 2^177.72) | empty (T≈2^255.27 > ceil≈2^228.44) |
| 1/4 | [2^129, 2^150.83) | [2^129, 2^174.45) | empty (T≈2^225.42 > ceil≈2^222.01) |
| 1/8 | [2^129, 2^145.14) | [2^129, 2^161.78) | **(2^194.80, 2^195.33) — nonempty, thin** |
| 1/16 | [2^129, 2^140.14)ᵃ | [2^129, 2^150.63) | **(2^165.44, 2^171.69) — nonempty** |

(endpoints from probe Part 5 — which prints the raw `log₂T` ends; the `2^129`
existence clamp is applied here, per the caveat above; ᵃ m'=32 at ρ=1/16 means r=3.
Hypotheses, all satisfied at the twelve prize combinations: `ρm′ ∈ ℤ` so that
`r = ρm′+1 ∈ ℤ`, `8 ≤ m′`, `2 ≤ r ≤ m′−1`, `m′ | n | p−1` with `n` a 2-power and
`k = ρn ∈ ℤ`; the `δ*` reading additionally uses monotonicity of `δ ↦ ε_mca`,
immediate from the witness-set definition. Prize-conformant lengths `k ≤ 2^40` exist
in every window — `n = m′` already works.) The qualitative picture: **at every prize
rate, every smooth prime field (`64 | p−1`) in `[2^129, ≈2^150]` (and up to `≈2^177`
at ρ=1/2) has `δ*_C < 1 − ρ − 1/64`, per-prime and unconditionally** — and at the two
low rates the pin even reaches `η = 1/128` on thin high windows (e.g. every smooth
prime in `(2^194.8, 2^195.3)` has `δ*_C < 7/8 − 1/128` at ρ=1/8). This is, to our
knowledge, the first *per-prime* **exponential-count** bad-scalar lower bound inside
the prize's `|F| < 2^256` window at fixed dyadic gap. (Hedge, for the tracker: Table-1
row 4's proven near-capacity lower bounds — BCHKS25/KK25/CGHLL26, and arXiv 2604.09724
over prime fields — give `ε_mca ≥ n^{Ω(1)}/|F|` within `O(1/log n)` of capacity: a
*polynomial* count in an *n-linked* gap regime, which is a different statement; we
have not audited those papers' constants beyond their issue-#232 representation, so
priority is claimed only against that record.) The KK25 rigorous route needs
`p > (m/2)^{m/2}` (`= 2^160`
at m'=64) *and* its subset count `C(φ(m'), r)` **vanishes entirely at ρ = 1/2**
(`r = m'/2 + 1 > φ(m')`), while the averaged chain (Thms B–D) covers *most* primes only,
with an ineffective Siegel–Walfisz denominator. E3 covers **all** primes in the stated
range, with the full signed count `N₀`.

**Route-1 corollary (derandomization no-go in the windows, stated at the ε_mca
level).** GG25 (Thm 1.2/1.3) proves *random-evaluation* RS achieves
`ε_mca ≤ poly(n, 1/η)/|F|` up to capacity. E3 shows *deterministic smooth-domain* RS
has `ε_mca ≥ N₀(m′, ρm′+1)/p = 2^{Ω(m′)}/p` at `δ = 1−ρ−1/m′` throughout the windows
above. So at the same `(n, ρ, δ, q)`, smoothness provably costs an **exponential**
ε_mca penalty over random domains — per-prime and unconditional: issue-§6 route 1
("derandomize GG25/GZ23 to the explicit smooth domain") is impossible at these
parameters with the poly numerator intact. Smoothness is not weak randomness; it is
adversarial. Scope honestly noted: the windows top out near `2^177.7`, so whether the
penalty persists at `q` near `2^256` is exactly the η=1/128 / transition residual of
§5. (We deliberately state this at the ε_mca level, not through the line-decodability
parameter: the black-box "`(δ,a,n+1)`-line-decodable ⟹ `ε_mca ≤ a/q`" bridge is
**refuted in-tree** — `LineDecodingRefutation` / `LineDecodingCoverage.lean`, the
antitone-witness obstruction — so a separation phrased in that parameter would rest
on a false bridge.)

**What this does *not* do:** it does not move the upper half (P-B); it does not pin
`δ*` for `|F|` near `2^256` (the η=1/128 windows at ρ ∈ {1/2, 1/4} are empty — see §5
for why no norm-size sharpening can change that); and below `T` it makes no exactness
claim (see §4).

---

## 4. The transition zone (below `T`): structure + exact measurements

For `p < T(m,r)` collisions can and do occur. What survives unconditionally:

- **Support-graded floor (E2(c)):** at BabyBear and m=32, `(4t)^8 > 2^31` forces
  `t ≥ 4` — every collision relation involves ≥ 4 basis coordinates. Single-pair or
  double-pair relations are impossible at 31 bits.
- **Multiplicity bound:** a fixed relation vector `c` with `|supp c| = t` collides at
  most `2^t·3^{m/2−t}` admissible pairs (per `j ∈ supp c`: `|c_j| = 2` forces `ε_j`,
  `|c_j| = 1` leaves ≤ 2 choices; elsewhere ≤ 3). So few low-support relations cannot
  crater the image; many mid-support relations can dent it.
- **Exact measurements (probe Part 4, MITM enumeration — no sampling):** the full
  m=32, r=17 image along a ladder of primes (smallest prime `≡ 1 (mod 32)` above each
  2-power; BabyBear inserted at its true size):

  | p ≈ | 2^26 | 2^28 | 2^30.9 (BabyBear) | 2^34 | 2^38–2^56 (7 samples) | 2^64 (Goldilocks) |
  |---|---|---|---|---|---|---|
  | image/N₀ | 87.377% | 97.196% | **99.787%** | **100% exact** | 100% exact | **100% exact** |

  Empirical exactness onset for (m,r) = (32,17) lies in `(2^30.9, 2^34]`, vs the proven
  sufficient `T ≈ 2^47.26` (~2^13–16 of slack — same loose-but-sufficient shape as the
  m=16 scans). Two corrections to earlier program data: **(a)** BabyBear's exact image
  `21,477,408` refines the old sampled `≈5.6M` estimate, which coupon-collector
  saturation had biased ~4× low; **(b)** the Entry-9-style "m=32 spot-check exact"
  claim was about the zero fiber only — the *full* m=32 image at BabyBear is genuinely
  deficient (by 45,952 values), so finite verification at production 31-bit primes
  stops at m=16 for full-image exactness.

A per-prime theory of the transition zone (e.g. lattice-point counts of
`𝔭 ∩ {−2..2}^{m/2}` controlling the deficiency) is the remaining open piece of P-A at
production field sizes; it is sharply localized and now bracketed by data on both sides.

---

## 5. Open residuals after this note (honest ledger)

1. **η = 1/128 per-prime windows at ρ ∈ {1/2, 1/4} are empty — and provably cannot be
   opened by sharpening the norm inequality.** Opening the ρ=1/2 window would need an
   effective threshold below the ceiling `2^228.4`, i.e. a `≈2^27` improvement on
   `T(128,65) ≈ 2^255.3`. But E1 is *essentially tight on the actual difference set*:
   hill-climbing (`scripts/probes/probe_e1_saturation.py`) exhibits an explicit
   difference vector `c` (entries in `{0,±2}`, support 62, `Σc² = 248`) with
   `log₂|N(c)| ≈ 252.4` — within 2.15 bits of E1's value `32·log₂(248) ≈ 254.5` — and
   `c` is realizable as `ε − ε′` with both patterns admissible at layer 65 (take
   `ε = c/2` plus a shared padding coordinate `ε_{j₀} = ε′_{j₀} = 1` on one of the two
   free slots: supports 63, odd, `≤ min(65, 63)` ✓). Since *any* norm-size argument
   must dominate `max |N|` over the difference set `≥ 2^252.4 ≫ 2^228.4`, no
   inequality-side sharpening (moments, Hölder, difference-set restriction…) can open
   the window. What could: showing `p ∤ N(α)` *arithmetically* for the specific primes
   (divisibility/splitting structure, not size), or a different bad-scalar
   construction. (At ρ ∈ {1/8, 1/16} the η=1/128 windows are already nonempty — §3.)
2. **Transition zone `N₀ ≲ p < T`:** open per-prime; bracketed by §4 data.
3. **The analytic denominator disappears only above `T`.** Below `T`, the averaged
   chain (most-primes, Siegel–Walfisz caveat) remains the best statement.
4. **P-B (the upper half, the believed-true `2^{O(H(ρ)/η)}` budget) is untouched** —
   see the descent program (O13–O13″) for the live attack.

## 6. Verification & reproduction

    python3 scripts/probes/probe_norm_threshold.py     # ~2–4 min, exit 0 = all PASS

Checks: the orthogonality identity (T1) and AM–GM bound (T2) numerically at
m ∈ {8,16,32,64}; pattern-parametrization vs brute-force subset enumeration; exhaustive
collision-onset scans over **all** primes `≡ 1 (mod m)` — for m=8 up to 1,100
(> 4·T(8,r) for every layer), for m=16 up to 2.2·10⁶ (≈ 3.6·T(16,9)) — against
`T(m,r)` (the theorem requires: no deficient prime above `T`; the scan also reports
how *tight* `T` is); the Goldilocks m=32 exact-image predictions (a genuine
falsification target: 21,523,360 / 21,523,361); the m=32 transition ladder (rows
`p ≥ 2^34` gated as an empirical regression lock, labeled as such — they are data,
not consequences of E2); and the E1-saturation companion (`probe_e1_saturation.py`).

2026-06-09 run: **all checks PASS, exit 0** (~4 min; reviewer re-runs 239–397 s on the
same box reproduced every figure, including a Goldilocks MITM re-implementation with a
different modular-reduction algorithm — bit-identical counts). Deterministic — no
seeds besides the fixed rng(232) used only for T1/T2 spot vectors. This note survived
a four-lens adversarial review panel (algebraic number theory / combinatorics /
prize-statement fidelity / numerics audit): zero fatal findings; the one major — a
false intermediate inequality in the E2 support-bound proof (`≤ 4·min(s,s′)` where
only `≤ 4·max(s,s′)` holds; final bound unaffected and exhaustively tight) — is
corrected above, and all minors (check-count, scan-range prose, two table roundings,
floor-rounding direction, implicit hypotheses) are incorporated.
