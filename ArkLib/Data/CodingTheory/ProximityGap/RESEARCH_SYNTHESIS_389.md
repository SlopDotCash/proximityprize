# Proximity-Prize research synthesis (2026-06-13) — exhaustive sweep + prune verdicts + sharpened reduction

Goal: solve the grand MCA challenge **and** the grand list-decoding challenge simultaneously
([ABF26], proximityprize.org) with a *closed-form, residual-free* conjecture for the smooth-domain
Reed–Solomon MCA threshold `δ*`. This file records the 2026-06-13 literature sweep (six parallel
deep digests), the ground-truth prize statement, the four routes the sweep **kills** for the prize
regime, the two decisive positive connections, and the resulting maximally-sharpened reduction. The
formal content lands in [`PROXIMITY_PRIZE_WORKBENCH.lean`](../../../../PROXIMITY_PRIZE_WORKBENCH.lean).
**The complete closed-form conjecture (both challenges) is in
[`PROXIMITY_PRIZE_CONJECTURE.lean`](../../../../PROXIMITY_PRIZE_CONJECTURE.lean)** — verified
axiom-clean: the closed-form crossover `listValue_at_deltaStar` and the budget reduction
`deltaStar_le_of_listBound` are *proven*; the single open input is the empirically-confirmed
`ShawGapLaw: B(μ_n) ≤ C·√(n·log(q/n))` (= the recognized open character-sum wall). The conjecture's
*statement* is complete and closed; its *proof* is the open problem.

---

## 0. Ground truth — what the prize actually asks (ABF26, IACR eprint 2026/680)

Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement* (2026), §4–6.
Retrieved in full (Wayback snapshot of `eprint.iacr.org/2026/680.pdf`). Verbatim setup:

- **Code:** `C := RS[F, L, k]`, `L ⊆ F` a **smooth** domain = a multiplicative coset of a subgroup
  whose order is a **power of two** (Def 2.12), so `n = |L| = 2^a`. Constant rate
  `ρ = k/n ∈ {1/2, 1/4, 1/8, 1/16}`. Parameters of interest: `k ≤ 2^40`, `|F| < 2^256`.
- **Capacity / Johnson:** `δ_min(C) = 1 − ρ + 1/n` ("capacity"); Johnson radius
  `J(δ_min) = 1 − √(1 − δ_min) ≈ 1 − √ρ`. The open **window is `(1 − √ρ, 1 − ρ)`** = (Johnson, capacity).
- **Grand MCA challenge (verbatim):** for `ε* = 2^{−128}`, *determine the largest `δ*_C ∈ [0,1]`
  such that `ε_mca(C, δ*_C) ≤ ε*`* (|F| large enough that `δ*_C` exists), **together with a proof
  that for all `δ > δ*_C`, `ε_mca(C, δ) > ε*`.** (A two-sided pin, not just an upper bound.)
- **Grand list-decoding challenge (verbatim):** for `ε* = 2^{−128}` and a constant `m`, *determine
  the largest `δ*_C` with `|Λ(C^m, δ*_C)| ≤ ε*·|F|`*, `C^m` = the `m`-interleaved code. No efficient
  decoder required — only the value `δ*_C` plus the matching two-sided proof.
- **ε_mca (Def 4.3, in-tree `mcaEvent`/`epsMCA` in `Errors.lean`):**
  `ε_mca(C,δ) = max_{f₁,f₂} Pr_{α∈F}[ ∃ S, |S| ≥ (1−δ)n, Δ_S(f₁+αf₂, C)=0 but Δ_S((f₁,f₂),C²)>0 ]`.
- **Why the two challenges are one** (§5): list-decoding `⟹` MCA (Thm 5.1 [GCXK25], with a
  **√-proximity loss**) and CA `⟹` list-decoding (Thms 5.2/5.3 [BCHKS25,CS25]). In the
  `|F| ≫ n` smooth-domain regime they pin the **same** `δ*_C`. The toy-protocol soundness
  (Lemma 6.6/6.10) is `max(ε_mca(C,δ) + |Λ(C²,δ)|/|F|, (1−δ)^t)` — both grand quantities.

**Net:** "solve the prize" = produce one number `δ*_C ∈ (1−√ρ, 1−ρ]` for each
`ρ ∈ {1/2,1/4,1/8,1/16}` at `ε* = 2^{−128}`, smooth domain, with a two-sided proof. The whole
difficulty is pushing `δ*_C` **above the Johnson radius toward capacity** for *explicit prime-field
smooth-domain* RS — exactly where the standing obstructions (Thm 4.16/4.18, the √-loss reduction
Thm 5.1) bite.

---

## 1. The exhaustive search list (what was fetched + digested)

| # | source | acquired | role |
|---|---|---|---|
| ABF26 | eprint 2026/680 (Arnon–Boneh–Fenzi) | full PDF (Wayback) | **prize ground truth** |
| KT24 | arXiv:2408.10977 (Kong–Tamo, point-variety incidence) | HTML | candidate (R)-tool — **killed** |
| KRZ26 | arXiv:2603.03841 (Kumar–Ron-Zewi survey) | full text | GM-MDS barrier — **kills route** |
| BCDZ25 | arXiv:2510.13777 (Brakensiek–Chen–Dhar–Zhang) | full text | folded-only — **kills route** |
| CS25 | eprint 2025/2046 (Crites–Stewart) | HackMD + abstract | **entropy-line wall (anchors closed form)** |
| ST20 | arXiv:1911.01502 (Shangguan–Tamo gen. Singleton) | abstract | band law `ρ ≤ (L/(L+1))(1−R)` |
| BGM23 | arXiv:2206.05256 (Brakensiek–Gopi–Makam) | abstract | generic-RS capacity (not fixed) |
| dBGGGS20 | arXiv:2003.06165 (di Benedetto et al.) | text | char-sum exponent (range `>p^{1/4}`) |
| HBK00 / MRSS19 | Heath-Brown–Konyagin / Murphy-Rudnev-Shkredov-Shteinikov | text | subgroup energy `n^{5/2}`, `n^{49/20}` |
| Shk17 | arXiv:1705.09703 (Shkredov) | text | sharpest explicit BGK char-sum `ν(γ)` |
| LiWan12 | Li–Wan, JCTA 119(1) (subset sums of finite abelian groups) | extract | **exact N_fib closed form** |
| LamLeung | arXiv:math/9511209 (vanishing sums of roots of unity) | extract | `W(2^a) = 2ℕ` structure |
| FXZ24 / GWZ25 | arXiv:2403.11436, 2509.08526 (twisted-RS deep holes) | abstract | covering-radius only (not band) |
| BKR10 | (subspace-polynomial fixed-domain clustering) | survey §3.4 | the *additive* super-poly lower bound |
| BCIKS20 | eprint 2020/654 | `_bciks20_fulltext.txt` (in repo) | proximity-gap home, `n/q` below Johnson |

---

## 2. FOUR routes the sweep KILLS for the prize regime (the "throw away" directive)

### 2.1 GM-MDS / higher-order-MDS / generalized-Singleton — DEAD for fixed `μ_n`
The Lovett GM-MDS chain (`arXiv:1803.02523`) being ground in the issue comments **cannot pin the
prize**. KRZ26 §5.1.1–5.1.3: GM-MDS (Thm 5.10) is stated over the **rational-function field
`F(Y₁,…,Y_n)` with the evaluation points `Yᵢ` kept symbolic**; the only bridge to actual points is
**Schwartz–Zippel over RANDOM points** (Cor 5.11, field size `≳ 2^{kn}`). A fixed multiplicative
subgroup `μ_n` is one specific algebraic locus on which the bad set `det(M)=0` **can vanish
identically** — SZ gives no control. KRZ26 **Open Problem 1 (verbatim):** "find explicit evaluation
points for which Reed–Solomon Codes are list decodable up to capacity" is stated as **the major open
problem**. There is even an *exponential field-size lower bound* for higher-order MDS ([BGM22
Cor 4.2]). ⇒ **No amount of Lovett-machinery certifies list decoding of a fixed smooth `μ_n`.**
The GM-MDS lane is task-1 machinery only, orthogonal to the prize.

### 2.2 Folded / subspace-design codes (GG25, BCDZ25) — DEAD for *plain* RS
BCDZ25 makes **folded RS / multiplicity codes** explicit (alphabet `F_q^s`, `s ≥ b(R/ε+1)`), by
derandomizing the *subspace-design* structure — **not** the evaluation points of plain RS. Searched
full text: zero occurrences of "multiplicative subgroup / root of unity / cyclic". Plain RS over
`μ_n` is **not subspace-designable**; the authors explicitly warn the strong FRS list bounds
([KRSW23/Tam24]) **do not transfer** through their reduction. ABF26 §6.3 independently notes the
GG25 up-to-capacity MCA result needs alphabet `s = O(1/γ²)`, which **kills the concrete prize win**.

### 2.3 Kong–Tamo point-variety incidence (arXiv:2408.10977) — INAPPLICABLE to the low-weight ball
KT24's incidence bound `|I(P,V) − |P||V|/q^d| ≤ q^{n/2}√(|P||V|)(1+|V|/q)^{1/2}` requires `V` to be
the **graph of a diagonal sum-of-permutation-monomials map** (`x_{n+i} = Σ_j a_{ij} x_j^{b_{ij}}`,
**`gcd(b_{ij}, q−1)=1`**, complete-intersection). The line `P` is fine, but the syndrome/Hamming
low-weight locus `S_w` is **(i)** not a graph `y=g(x)`, **(ii)** not diagonal/permutation
(support-counting is intrinsically degree-`≈m`, and the permutation condition *excludes* the very
exponent `q−1` that detects zero coordinates), **(iii)** high-codimension and reducible. The
character-diagonalization that is the entire engine never engages; with the natural reading the
`q^{n/2}=q^{m/2}` error is astronomically **larger than the average** `q|S_w|/q^m` ⇒ vacuous. The
"right type of tool" intuition in the issue comment is **refuted**: it is the wrong tool.

### 2.4 Character sums / additive energy over `μ_n` — HOPELESS in the prize regime (the 25-year wall)
Prize regime: `n = 2^32…2^40`, `q ≈ 2^{160…256}`, so **`n ≈ q^{1/5} < p^{1/4}`**. Below `p^{1/4}`:
- Every *clean-exponent* char-sum bound (di Benedetto `31/2880`, Bourgain–Garaev) **requires
  `H > p^{1/4}`** — out of range.
- The applicable regime is BGK "very small subgroup": cancellation **exists** but the exponent is
  microscopic. Sharpest explicit (Shkredov Cor 16): saving `≤ q^{δ²/(27+2δ)} ≈ q^{0.0015}`
  (best case) down to `n^{−1/2^{27}} ≈` trivial (actual construction).
- Best additive energy `E(μ_n) ≲ n^{49/20} = n^{2.45}` (MRSS), **no 2026 improvement**; trivial is
  `n^2`. Nothing beats trivial for `n ≥ p^{2/3}`.
- **√-cancellation `√n` is unattainable; the gap is a factor `≈ n^{0.4}`.**

⇒ **Any (R)-style residual that needs `√q`-type character-sum cancellation is the recognized 25-year
wall and is NOT closable by current analytic methods in this regime.** The closed form must avoid
character sums entirely (see §4).

---

## 3. TWO decisive positive connections

### 3.1 Crites–Stewart (CS25): the true wall is the **q-ary entropy line `H_q(δ) = 1 − ρ`**
CS25 *disproves* the to-Singleton proximity-gap conjectures (BCIKS23 Conj 8.4, DEEP-FRI 2.3,
WHIR 4.12): a gap beyond the **q-ary entropy line** `H_q(δ) = 1−ρ` would force list sizes below the
combinatorial list-decoding lower bound — impossible. Their argument uses lines
`{u⁰ + λu¹}` with `u⁰ = ev(x^k)` and is **domain-generic** (no smoothness needed) ⇒ the
*impossibility* side **applies to `μ_n`** and gives the **lower half of the two-sided pin**
(an explicit bad line above the entropy line ⇒ `ε_mca > ε*`). It also confirms the closed form's
anchor: as `ε* → 1`, `δ* → H_q^{−1}(1−ρ)` = the CS25 wall. The CA⟺list bridge: small CA error
`ε ⇒ list size `L ≤ 2εq`.

### 3.2 Li–Wan (exact subset-sum fibre) + Lam–Leung — pins the **extremal list value** exactly
Li–Wan (JCTA 119(1), Cor 1.4) gives the subset-sum fibre `N(k,b) = #{T ⊆ G : |T|=k, ΣT=b}` over a
finite abelian group `G` (`|G|=s`) **exactly**:
- **`p ∤ k`:**  `N(k,b) = C(s,k)/s` — *perfectly equidistributed, deviation exactly 0, ∀ b*.
- **`p | k`:**  `N(k,b) = (1/s)[C(s,k) + (−1)^{k+k/p} v(b) C(s/p, k/p)]`, `v(0)=s−1`, else `−1`.

So **`N_fib(s,r) = C(s,r)/s · (1 + o(1))`** with super-exponentially small deviation (e.g.
`2.6·10^{−8}` at `s=256, k=8`); the maximizing `λ` is `0` when `r ≡ 0 (mod 4)`. The clean
equidistribution `p∤k` case has a **one-line proof via the translation bijection** `T ↦ T+c`
(sum-shift `k·c`; `c↦k·c` bijective ⇒ all fibres equal) — **formalized in the workbench**
(`subsetSum_fibre_equidistributed`). Lam–Leung (`W(2^a)=2ℕ`) explains the parity correction: for
`2^a`-th roots of unity, minimal vanishing sums are ± pairs, so the `b=0` fibre dominates.

This **upgrades the #389 Thread-A target value** `L_max(a) = max_towers N_fib(s,r)` from a
conjectured shape to an **exact closed form** `≈ C(s,r)/s`, and it equals the "equidistributed /
average" list value — so census domination becomes the sharp statement **"no far word beats the
equidistributed list size."**

---

## 4. The maximally-sharpened reduction (post-sweep) — what the closed form really is

The character-sum framing of the old residual (R) ("worst line incidence `≤` average via a spectral
bound") is the dead wall of §2.4 — **and it is also literally false in general**, since CS25 +
Thm 4.16 exhibit lines whose incidence is `n^c ≫` the (tiny) average of a *typical* line. The
correct object is the **worst-case list size**, not the average:

> `ε_mca(C,δ) ≤ (1/q)·max_{lines} #{γ : f₁+γf₂ is δ-close to C} ≤ (1/q)·L_max(C,δ)`,
> where `L_max(C,δ) = max_{far w} #{c ∈ C : agree(w,c) ≥ (1−δ)n}` is the **max far-word list size**.

(The first `≤` is exact from `mcaEvent ⟹ δ-closeness`; in-tree, `Errors.lean`.) Hence

> **`δ*_C = sup{ δ : L_max(C,δ) ≤ q·ε* }`.**

Because the *equidistributed* list value at radius `δ` is `q^{(H_q(δ)−(1−ρ))·n}·q`, setting it to
`q·ε*` gives **exactly**

> **CLOSED FORM.  `H_q(δ*_C) = (1−ρ) − log_q(1/ε*) / n`,  i.e. `δ*_C = H_q^{−1}(1−ρ − log_q(1/ε*)/n).`**

This is a single computable number — no `∃`-over-objects, no incomputable lemma. It lands exactly
where it must: `ε*→1 ⇒` the CS25 entropy-capacity wall; prize budget `q ≈ n·2^{128}` ⇒
`δ* = 1−ρ − Θ(1/log n)`, strictly **inside** `(1−√ρ, 1−ρ)` (matching the BCHKS25 bracket), not
collapsing to Johnson, not to constant-alphabet capacity.

### The single remaining residual — now in its sharpest, character-sum-free form
> **(CensusDomination).** For every far word `w` (`w ∉ C`) over the smooth domain `μ_n`, and every
> `δ` in the window `(1−√ρ, 1−ρ)`, `#{c ∈ C : agree(w,c) ≥ (1−δ)n} ≤ q^{(H_q(δ)−(1−ρ))·n}·(1+o(1))`
> — i.e. **no far word beats the equidistributed (= ladder = Li–Wan `N_fib`) list size.**

- **Supply (lower) half — value PROVEN, list-equality NOT assembled.** ⚠️ **Honesty correction
  (2026-06-13 floor-audit):** `ladder_list_ge_fibre` and `ladder_gapBand_antipodal_charZero` are
  cited across the campaign (issue body, memory, `FiberEnergyListBound` docstring prose) as
  "in-tree, axiom-clean" but **do NOT exist as compiled Lean theorems** (grep-verified). The only
  compiled, axiom-clean fact is the **value** `N_fib = C(s,r)/s` (`subsetSum_fibre_card_mul`,
  `LiWanSubsetSumEquidistribution.lean`); the *list-size equality* `L(w,rm)=N_fib` that they assert
  is unassembled. Do not cite them as proven. The honest in-reach increment is
  `ladder_list_charZero_eq_fibre` (char-0, ladder-only, via discharging the `hindep` of
  `LamLeungAntipodalTightness.antipodal_invariant_of_vanishing_sum`) — replaces the phantom with a
  real theorem, but is **not prize-relevant** (char-0 + ladder-only).
- **Upper half:** the named open core — and now **machine-checked to BE the character-sum wall** (see
  §7). The "far-pair second moment" live route is `(list size)² ≤ E` (`maxRep_sq_le_addEnergy`) = the
  Johnson 2nd-moment engine; making it sharp needs `E=O(n²)`, supplied only by the character-sum
  input `‖η_b‖≤C√n`. So the upper half does not escape the wall.
- This **fuses both grand challenges**: the same `L_max(C,δ)` bounds `ε_mca` (challenge 1) and *is*
  `|Λ(C,δ)|` (challenge 2); `|Λ(C^m,δ)| ≤ |Λ(C,δ)|^m` closes the interleaved version.

---

## 5. What is and is not done (honesty ledger)

- **Done (this sweep):** prize ground truth pinned (ABF26); 4 dead routes pruned with precise
  obstructions; closed-form `δ*` re-derived from the *worst-case list* (not the false average
  residual); Li–Wan exact `N_fib` connected and the equidistribution `p∤k` case formalized; the
  reduction `CensusDomination ⇒ ε_mca(δ*) ≤ ε*` formalized (workbench).
- **Open (named, not fabricated):** the **upper** half of `CensusDomination` over `F_q` in the
  window — equivalently the char-0→`F_q` transfer of the proven char-0 exact list law past the
  resultant threshold. This is the one residual; everything else is closed or pruned. Per the
  project honesty contract, it is named, not claimed solved.

Primary sources are listed in §1; extracted texts cached under `/tmp` during the sweep
(`pp680.txt`, `survey.txt`, `bcdz.txt`, `bgk.txt`, `dbg.txt`, `shk.txt`).

---

## 6. Adversarial workflow validation (2026-06-13, 25 agents, every kill checked vs an in-tree artifact)

A 5-phase adversarial workflow (red-team the prunes · stress-test δ* vs every ABF26 negative result ·
generate+filter 7 novel routes · synthesize) returned a decisive, honest result.

- **All 4 prunes HOLD** (confidence 9 each), each refuted by a *verified* in-tree artifact
  (`folding_transfer_no_go`, `abs_norm_le=B^{φ(n)}=B^{n/2}`, `SubsetSumEsymmVanishing`,
  `Lambda_interleaved_arity_mono`, `deep_band_failure_closed_form`). No crack.
- **Closed-form δ* — two amendments (the sharp statement):**
  1. The `log_q(1/ε*)/n` term is a **red herring** at prize params; the binding correction is the
     **CS25 (Thm 4.17) `Θ(1/log q)` collapse slab**: `δ*_safe = (1−ρ) − max(log_q(1/ε*)/n, c/log q)
     = (1−ρ) − Θ(1/log q)`, valid only up to the collapse line (for `ρ≤1/4` log₂, naive δ* sits
     *above* it).
  2. δ* is the **CA/list** crossing radius, **not** a Grand-MCA answer at the same radius: the
     list⟹MCA √-bridge (Thm 5.1) drops `δ*=0.496` to MCA-radius `0.290 < Johnson`. The MCA window is
     the open analytic wall, orthogonal to all four negative theorems.
- **0 of 7 novel routes survive** the honesty filters — all collapse to the **single** wall
  `B(μ_n)=o(n)` (subgroup √-cancellation) through different doors; the workflow caught fabricated
  lemmas in several. Lone sub-crack: `ListIncidencePolyMethod.incidence_numeric_F7` (slice-rank/CLP
  beats Johnson in the interior without a character sum, F7 |L|≤7 vs 24) — field-blind, can't reach
  `ε*·q`, but the only non-Johnson non-analytic foothold.
- **The single residual-free next deliverable — the irreducibility no-go.** Smoothness ⟹ `p≡1 mod n`
  ⟹ p splits completely in `ℚ(ζ_n)`, so `v_p(N(σ(c))) = Σ_{i∈(ℤ/n)^×} [σ_i(c)≡0 mod 𝔭_i]`. Hence
  the census-domination upper half is **equivalent** to per-embedding incomplete-char-sum
  nonvanishing. Target `census_transfer_iff_charsum_nonvanishing` (wire
  `resultant_X_pow_sub_one_eq_bgk_prod` [`AdditiveEnergyResultantProduct.lean:152`] to `abs_norm_le`
  [`EffectiveTransfer.lean`]): **every** transfer route to the upper half provably *is* the Shaw gap
  — an equivalence that certifies the wall's irreducibility (does not cross it). The clean
  Mathlib-only core (char-sum/DFT-eigenvalue product nonvanishing) is in
  `CharSumTransferNoGo.lean`.

**Net.** The prize core is `B(μ_n) = o(n)` (25-year open). The closed form is the right *CA/list*
conjecture with the `1/log q` amendment; the *MCA* version at the same radius is the open wall. Every
known route is the same wall. Nothing fabricated.

---

## 7. The floor ⟺ character-sum wall equivalence is now MACHINE-CHECKED (2026-06-13 floor-attack)

A second 13-agent workflow attempted six *constructive* extremal-combinatorics proofs of the floor
(compression, entropy/Shearer, polynomial method, interpolation-deficiency, container,
char-0→F_q transfer). **0/6 closed any prize-relevant case.** The decisive, verified outcome:

**The floor is PROVABLY the character-sum wall — certified by compiled, axiom-clean in-tree
theorems (not a heuristic):**
- `CharSumTransferNoGo.transfer_ne_zero_iff` (this session) — the transfer/census object
  `∏_i charSum_i = Res(f_c, X^n−1)` is non-zero **iff** every incomplete character sum
  `σ_i(c)=∑_j c_j ω^{ij}` is non-zero. So separating main term from error in any window count *is*
  bounding `max_b|∑_{x∈μ_n}ψ(bx)|`.
- `EffectiveTransfer.esymm_eq_zero_iff` (`:266`) — the char-0→F_q transfer can be "discharged by
  height" only when `C(w,⌊w/2⌋)^{φ(n)} < p`; for `n=2^a`, `φ(n)=2^{a−1}`, so the threshold is
  `~2^{(a−1)w}` — **astronomically beyond any prize prime** `p < 2^256`. The transfer fires only
  *outside* the prize regime.
- `AdditiveEnergyFermat.one_mem_bgk_iff_exists_fermat_dvd` (`:72`) — the bad primes (where the
  resultant vanishes) are *exactly* divisors of the Fermat numbers `F_0…F_{k−1}`: an enumerable
  family that the prize `F_q` lands in, **not** a measure-zero height event.

This *machine-checks* BCHKS Thm 1.9: the floor's combinatorial face (no word beats the ladder) and
its analytic face (`B(μ_n)=o(n)`) are the **same wall, two faces**.

**The dichotomy (independently rediscovered by all six angles):** every route is *either* field-blind
+ super-polynomial in the window (the lone proven non-Johnson artifact,
`ListIncidencePolyMethod.poly_method_subset_incidence_bound`, is field-blind, super-poly, witnessed
at `n=7` — outside the prize regime) *or* uses `μ_n`-regularity (= the character sum). **No third
option.** Every route that became non-vacuous in the window re-encoded `∏_i charSum_i`; every
charsum-free route is field-blind/super-poly or char-0-only.

**Honest verdict:** the prize floor cannot be closed by extremal combinatorics — it is, in-tree and
axiom-clean, the incomplete-subgroup character-sum √-cancellation wall. No closure is fabricated; the
single in-reach increment (`ladder_list_charZero_eq_fibre`) is char-0-and-ladder-only, an honesty fix
(replacing a phantom citation), **not** prize progress.

---

## 8. Targeted deep sweep (2026) + a rigidity-transfer LEAD that may overturn the wall conclusion

A second, *targeted* sweep on the exact bottleneck (3 focused agents). New facts:

**8.1 The Nov-2025 research sprint + 2026 (the prize is open; capacity is dead).**
- Capacity proximity-gap conjectures **DISPROVED**: Crites–Stewart (2025/2046), BCHKS (2025/2055,
  STOC'26), Diamond–Gruen (2025/2010). The true ceiling is the q-ary entropy line, ~3.2% below
  Singleton.
- **KKH26 (eprint 2026/782)** — the *only* on-point smooth-domain result: proximity gaps **FAIL** at
  `δ = 1−ρ−η`, `η = Θ(1/log n)`, with `2^{Ω(1/η)} = poly(n)` close points, via "a new
  additive-combinatorics lemma on sums of roots of unity." This is the **converse / lower-half
  witness**, and it matches the closed form `δ* = (1−ρ) − Θ(1/log q)` exactly.
- BCHKS **Thm 1.18**: any gap beyond Johnson ⟹ improved RS list-decoding (the floor). BCHKS §7
  prime-field-subgroup limitation rests on the *unproven* Conj 1.12 (multiplicative-subgroup sumsets).
- Positive capacity results (Goyal–Guruswami 2025/2054; folded RS 2601.10047) are **random/folded**,
  not fixed smooth. ⚠️ eprint 2025/1712 ("Syndrome-Space Lens") *claims* to resolve CA to capacity —
  **contradicts all three disproofs; non-credible, discount.** **The $1M prize is unclaimed.**

**8.2 No √n character-sum cancellation (magnitude wall confirmed, maximal coverage).** At `n≈p^{1/5}<p^{1/4}`:
best explicit saving is `n^{1−0.011}` (di Benedetto, and only for `|H|>p^{1/4}`); below `p^{1/4}` only
the ineffective BGK ε-saving. Best subgroup energy `n^{49/20}` (no 2024–26 improvement). **2-power
order / dyadic tower gives NOTHING for magnitude** (untouched but the Gauss/Salié objects are the wrong
ones — `S(b)` is the untwisted subgroup indicator, not a Gauss sum). `√n` is unprovable by any method.

**8.3 ⚠️ THE RIGIDITY-TRANSFER LEAD (under rigorous test — may overturn §7).** The §7 "transfer fails"
conclusion used the **crude HEIGHT bound** `esymm_eq_zero_iff: C(w,⌊w/2⌋)^{φ(n)} < p`. But the **sharp
criterion is the Lam–Leung WEIGHT bound**, which the prize *satisfies*:
- `disc(Φ_{2^a}) = ±2^{(a−1)2^{a−1}}` is a **pure power of 2** ⟹ for **every odd `p`** the integral
  cyclotomic relation lattice among `2^a`-th roots transfers **isomorphically** mod `p` (Φ_{2^a} mod p
  separable; only bad prime is 2, excluded by `p≡1 mod 2^a`). **No Fermat-divisor exclusion for the
  integral lattice.** (Mathlib `Cyclotomic.Discriminant` is the load-bearing input.)
- Lam–Leung char-`p`: `W_p(2^a) = ℕp + ℕ2` ⟹ **every F_p vanishing sum of `2^a`-th roots of weight
  `< p` is ℂ-rigid** (forced ± pairs); new relations need weight `≥ p`.
- **Prize: floor vanishing sums have weight `≤ n = 2^a`, and `p ≈ n·2^128 ≫ n`, so weight `≪ p`** —
  the rigidity transfers. This suggests **route (II): bound the char-0 floor (extremal combinatorics
  over ℂ, where rigidity holds) and transfer to F_p via weight-`<p` rigidity — avoiding the
  magnitude wall entirely.** The crux being tested (workflow `wriedmtvt`): is the worst-case floor
  COUNT determined by *vanishing/linear-rigidity* (transfers, route II) or by char-sum *magnitude*
  (the wall)? KKH26's failure at weight-`≥ p`-scale (`η=Θ(1/log n)`) is a consistency check. **Not yet
  resolved — recorded as the most promising lead, not a closure.**

**8.4 ⛔ The rigidity-transfer lead (8.3) is REFUTED — a LEVEL ERROR** (workflow `wriedmtvt`: 0/4
red-team, 0/3 reconcile, machine-checked). It equivocates between two orthogonal faces:
- **Vanishing face** ("which subsets `A⊆μ_n` have `∑ζ^a=0`"): Lam–Leung weight-`<p` rigidity *does*
  transfer this (8.3 is correct for this face).
- **Magnitude face** (the floor `L_max = max_w #{c:agree≥(1−δ)n}` = level-set SIZE = energy `E(μ_n)`):
  this is what the floor IS, and rigidity transfers the **wrong** face.

Three axiom-clean in-tree facts make it fatal: **(1)** the energy bridge is **bidirectional** —
`maxRep_sq_le_addEnergy` (list²≤E) *and the converse* `EnergyCharacterTransport.exists_charSum_ge_of_energy'`
(`max_b‖η_b‖⁴ ≥ (qE−n⁴)/(q−1)`), so `E(μ_n)=O(n²)` is **LOGICALLY EQUIVALENT (iff)** to the wall
`B(μ_n)=O(√n)` — and char-0-valid, so even over ℂ the arbitrary-word max is a magnitude quantity.
**(2)** `antipodal_invariant_of_vanishing_sum` needs a *homogeneous* `{−1,0,1}` vanishing sum (only the
ladder); arbitrary words give *inhomogeneous* symmetric constraints, no rigidity theorem. **(3) KILLER
RECEIPT:** `SubgroupRepCountFiniteFieldCounterexample.char0_repBound_fails_over_finite_field`
(kernel-`decide`, axiom-clean) — over F₁₇ the 8th roots `{±1,±2,±4,±8}` have a shift `t=1` with
`repCount=3 > 2`, an F_q coincidence with **no char-0 analogue at weight 2 ≪ p**, invisible to the
weight argument. So weight-`<p` does NOT prevent energy inflation; `"weight≥p"` is a **red herring**.

**Net (sharpened, the strongest irreducibility statement):** the prize floor is not merely *reducible
to* but **logically EQUIVALENT (iff, machine-checked via the bidirectional transport)** to the 25-year
wall `B(μ_n)=O(√n)`. The char-0 *arbitrary-word* floor is itself the grand challenge (= RS
list-decoding to capacity; the only proven every-word char-0 envelope, Corrádi/Fisher, is *strictly
larger* than `N_fib`). The honest in-reach increment is `ladder_list_charZero_eq_fibre`
(char-0+ladder-only, deletes the phantom citations, **not** prize progress). No fabrication.

---

## 9. (#407, 2026-06-14) The Gauss-period sharpening — law pinned to constant 1, residual = the period *house*

A from-scratch re-derivation (independent probes `scripts/probes/probe_moment_growth_law_407.py`,
results in `scripts/probes/RESULTS-407-GAUSS-PERIOD-LAW.md`) confirms the §7/§8 wall and sharpens it:

- **New proven structural brick** (`GaussPeriodCosetReduction.lean`, axiom-clean): the frequency
  function `b ↦ η_b` is **constant on μ_n-cosets** (`eta_mul_invariant`). So `B = max` over exactly
  `m=(p−1)/n` values — the **Gauss periods** of the order-`n` subgroup (= generalized Paley-graph
  eigenvalues). This is the rigorous reason the law carries `log((p−1)/n)`, **not** `log p`.
- **Law sharpened to constant 1**: `B(μ_n) = (1+o(1))·√(n·log₂((p−1)/n))`; measured
  `B/√(n·log₂(p/n)) ∈ [0.97, 1.07]`, `n=8..128`. (Sharpens `ShawGapLaw`: argument of the log is the
  coset count `m`; constant ≈ 1.)
- **Threshold law re-confirmed**: `E_r/(r!n^r)` matches the char-0 Gaussian `(2r−1)‼/r!` exactly for
  `r ≤ r_max=2log_n p−3`, inflates beyond — the char-0→F_p energy transfer caps at `r_max ≈ 2 log_n p`
  ≪ `r_opt ≈ ln q`.
- **Moment-arrow NO-GO (quantitative)**: with true F_p moments, `min_r (p·E_r)^{1/2r}` is stuck at the
  **trivial ≈ n**, and `arrow_min/trueB` **diverges** (1.20→2.92, n=8..128). The only elementary
  handle provably cannot reach the prize bound.
- **Residual named (classical)**: `B = ` the **house** (max conjugate modulus) of the order-`n` Gauss
  period = the Paley eigenvalue. Fixed-`n` solved (Kowalski–Untrau hypocycloid); growing-`n`
  quantitative tail = open (Wasserstein, arXiv:2505.22059), house/norm = Myerson/Habegger
  (arXiv:1611.07287). 5 precise new papers cataloged in `PAPERS_NEEDED.md` §2026-06-14.

**Net:** the conjecture's *statement* is now maximally sharp (closed-form `δ*`, constant-1 input,
log-argument pinned to `m=(p−1)/n`), and its single open input is identified with a *named classical
object* (the growing-`n` Gauss-period house / Paley eigenvalue). The proof of that input is the open
prize; per the honesty contract it is named, not fabricated. No route in or out of this session's
work crosses it.
