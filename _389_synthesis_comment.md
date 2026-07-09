## Literature sweep (2026-06-13): prize ground-truth pinned, FOUR routes killed, the gap residual externally confirmed as THE wall

Six parallel deep digests (full extractions cached). Net: the workbench's isolation of the prize to
the **Shaw spectral gap `B(μ_n) ≤ √2·√n`** is *correct and now externally validated* — and four
tempting routes (one of them being actively ground in this thread) are **dead** for the prize regime.
Full writeup: `ArkLib/Data/CodingTheory/ProximityGap/RESEARCH_SYNTHESIS_389.md`.

### Prize ground truth ([ABF26] = eprint **2026/680**, retrieved in full)
Both grand challenges = pin **one** `δ*_C ∈ (1−√ρ, 1−ρ]` for `ρ ∈ {1/2,1/4,1/8,1/16}`, `ε*=2⁻¹²⁸`,
smooth domain (`n=2ᵃ`, **`k ≤ 2⁴⁰`, `|F| < 2²⁵⁶`**), **with a two-sided proof** (`ε_mca ≤ ε*` below,
`> ε*` above). The whole difficulty is pushing `δ*_C` **above Johnson toward capacity** for explicit
prime-field smooth-domain RS. The two challenges are nearly equivalent in this regime via Thm 5.1
(list⟹MCA, **√-loss**) and Thm 5.2/5.3 (CA⟹list). The closed form `δ*=H_q⁻¹(1−ρ−log_q(1/ε*)/n)` and
the gap residual are consistent with this verbatim statement.

### FOUR routes the sweep KILLS (please stop mining these)
1. **GM-MDS / higher-order-MDS / Lovett (being ground in recent comments) — DEAD for fixed `μ_n`.**
   Kumar–Ron-Zewi survey (arXiv:2603.03841) **Open Problem 1**: explicit-evaluation-point capacity
   list decoding is *the* major open problem. GM-MDS (Thm 5.10) is stated over `F(Y₁…Y_n)` with the
   points symbolic; the only bridge to actual points is Schwartz–Zippel over **random** points
   (field `≳2^{kn}`). A fixed `μ_n` is one algebraic locus on which `det(M)=0` can vanish
   identically — no control. Plus an exponential field-size lower bound [BGM22 Cor 4.2]. **The
   Lovett chain, however far pushed, cannot pin `δ*` for `μ_n`.** It is task-1 machinery only.
2. **Folded / subspace-design (GG25, BCDZ25 arXiv:2510.13777) — DEAD for plain RS.** Explicit only
   for *folded* RS / multiplicity codes (alphabet `s=O(1/γ²)`, which [ABF26] §6.3 says kills the
   concrete win). Plain RS over `μ_n` is not subspace-designable; the strong FRS list bounds *do not
   transfer* (the authors warn this explicitly).
3. **Kong–Tamo point-variety incidence (arXiv:2408.10977) — INAPPLICABLE** (the "promising new
   surface" from the prior scan is refuted as a drop-in). Their variety must be the **graph of a
   diagonal sum-of-permutation-monomials map** (`gcd(b,q−1)=1`, complete-intersection). The
   low-weight Hamming/syndrome ball is neither a graph, nor diagonal, nor low-codimension; the
   permutation condition even *excludes* the exponent `q−1` that detects zero coordinates. The
   character-diagonalization (the whole engine) never engages and the `q^{m/2}` error is vacuous
   (≫ average). Wrong tool.
4. **Character sums / additive energy — HOPELESS analytically in-regime (the wall, confirmed).**
   Prize regime `n ≈ q^{1/5} < p^{1/4}`. Below `p^{1/4}` *every* clean-exponent char-sum bound
   (di Benedetto `31/2880`, Bourgain–Garaev) is out of range; the applicable BGK regime gives a
   microscopic saving (Shkredov Cor 16: best `≈ q^{0.0015}`, actual construction `≈ n^{−1/2²⁷}`).
   Best additive energy `E(μ_n) ≲ n^{49/20}=n^{2.45}`, **no 2026 improvement**. `√n`-cancellation is
   `≈ n^{0.4}` out of reach. **⇒ `ShawFlatness` / `WorstCaseIncidenceBound` is the genuine 25-year
   wall; it will not yield to a character-sum/spectral bound. It must be closed combinatorially.**

### Two positive connections that sharpen the workbench
- **Crites–Stewart (eprint 2025/2046):** the true ceiling is the **q-ary entropy line `H_q(δ)=1−ρ`**,
  strictly below Singleton; their line construction is **domain-generic** ⇒ it gives the **lower
  half of the two-sided pin for `μ_n`** (explicit bad line above the entropy line ⇒ `ε_mca>ε*`), and
  it confirms `δ*→H_q⁻¹(1−ρ)` as `ε*→1`. This is the missing converse direction for the prize's
  required two-sided proof.
- **Li–Wan (JCTA 119(1), Cor 1.4) + Lam–Leung:** the extremal list value `N_fib(s,r)` is now an
  **exact closed form** `C(s,r)/s·(1±o(1))` (deviation super-exp small; `2.6·10⁻⁸` at `s=256,k=8`).
  The `p∤k` perfect-equidistribution case has a clean translation-bijection proof, **formalized
  axiom-clean** (`subsetSum_fibre_equidistributed`, `subsetSum_fibre_card_mul`). This pins Form-4 /
  `SmallSubgroupGoodList`'s target value exactly (additive realization / BKR10-side; the
  multiplicative `μ_n` case is the same lattice via in-tree Mann, the transfer residual).

### Bottom line
The workbench's `ShawFlatnessConjecture ⟺ WorstCaseIncidenceBound` is, per the 2026 literature, the
**correct and unique** open core — and it is the *combinatorial* wall, not an analytic one (char
sums are dead in-regime). Redirect: drop the GM-MDS/folded/Kong–Tamo/character-sum lanes; the live
route is the far-pair second moment of the Shaw spectrum targeting the now-exact Li–Wan value.
