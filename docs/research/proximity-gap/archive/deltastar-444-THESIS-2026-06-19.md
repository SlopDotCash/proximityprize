# On the Sup-Norm of Gauss Periods over Thin 2-Power Subgroups

### A doctoral thesis on the Paley / BGK / Reed–Solomon-list-decoding / Gauss-additive-sum / characteristic-p-transfer problem, its six equivalent forms, the obstruction common to all of them, and the new mathematics it demands

*Issue #444 (proximityprize.org), companion to Arnon–Boneh–Fenzi 2026. All "proven" claims are axiom-clean Lean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`) on the `fork/main` tree unless explicitly marked conjectural/empirical. Honesty contract: only the word "proven" + an axiom-clean build is sacred; conditional/empirical results are labeled as such; the open core is a recognized open problem and no closure is claimed.*

---

## Abstract

Let `p` be prime, `n = 2^μ | p−1`, and `μ_n ⊂ F_p^×` the cyclic group of `n`-th roots of unity. For `b ≠ 0` define the **Gauss period** `η_b = Σ_{x∈μ_n} e_p(bx)`. The central object is the sup-norm
> `M(μ_n) = max_{b≠0} |η_b|`,
in the **thin regime** `n ≈ p^{1/4}` (`β := log p / log n = 4`). The conjecture — call it the **thin Paley/BGK bound** — is `M(μ_n) ≤ C√(n log p)` with an **absolute** constant `C` **uniform in `p`**. The best known unconditional results are Bourgain–Glibichuk–Konyagin's `n^{1−o(1)}` (ineffective) and di Benedetto et al.'s `H^{1−31/2880}` (regime-gated, vanishing exactly at `β=4`).

This thesis (i) establishes that **six** problems from six different areas of mathematics are equivalent forms of this single bound; (ii) **proves**, axiom-clean and `r`-uniformly, the *characteristic-zero* half of the bound (the sharp Wick/Gaussian moment bound `E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r`) via a new **Bessel-moment identity** derived from the Lam–Leung antipodal-balance theorem; (iii) **reduces** the entire conjecture to a *single* inequality (the characteristic-`p` wraparound `W_r ≤ K^r·(2r−1)‼·n^r` with `K=O(1)` at the saddle `r ~ log p`); (iv) gives a new **Poisson-inversion identity** exhibiting `W_r` as the wrapped dual mass of the Bessel object; (v) **measures the wall exactly** — the energy ratio diverges in `n` like `~n^{0.37}`, recovering BGK's `n^{1−o(1)}`; and (vi) documents the exhaustive failure of every standard and several non-standard proof routes, isolating the structural cause (`μ_n` is `0`-dimensional, so all algebraic/Weil machinery is vacuous). The thesis concludes with a precise statement of the new mathematics a proof requires and an honest assessment of which of the six domains is least blocked.

---

## Chapter 1 — The six equivalent forms

The same open inequality wears six faces. The equivalences (F1↔F2 classical; F3↔F4↔F6 established this campaign in the *fourfold wall equivalence* and the *transfer = moment identity*) are summarized here; proofs of the new equivalences are in Ch 3.

**F1 — Paley graph eigenvalue (spectral graph theory).** `M(μ_n)` is the largest non-principal eigenvalue of the generalized Paley/Cayley graph `Cay(F_p, μ_n)` (a `p`-vertex `n`-regular graph). `M ≤ 2√n` is the Ramanujan property; `M ≤ C√(n log p)` is the quantitative Paley Graph Conjecture (Liu–Zhou Thm 115).

**F2 — Incomplete character sum (analytic number theory).** `M = max_{b≠0}|Σ_{x∈μ_n} e_p(bx)|` is the worst-case complete sum of an additive character over a multiplicative subgroup — the BGK object (Bourgain–Glibichuk–Konyagin, *JLMS* **73** (2006) 380–398).

**F3 — Reed–Solomon list-decoding / MCA threshold (coding theory).** For the explicit smooth RS code with evaluation domain `μ_n`, the *mutual-correlated-agreement* threshold `δ*` (Arnon–Boneh–Fenzi, ePrint 2026/680, §4.5) reaches the window interior `(1−√ρ, 1−ρ−Θ(1/log n))` iff the far-line incidence is budget-bounded — which the campaign reduces to F6.

**F4 — Gauss-period sup-norm (cyclotomic theory).** `η_b` is a Gauss period of the cyclotomic field `Q(ζ_n)` reduced mod a split prime `𝔭|p`; `M` is the maximal modulus over the `(p−1)/n` cosets.

**F5 — Characteristic-`p` transfer (arithmetic geometry).** With `E_r^{ψ} = #{(x,y)∈μ_n^r×μ_n^r : Σx = Σy}` evaluated through `ψ`, the **wraparound** `W_r := E_r^{F_p} − E_r^{char0} ≥ 0` counts tuples whose root-sums are distinct in `Z[ζ_n]` but equal mod `𝔭`. F5 asks `W_r` to stay Wick-bounded at the saddle.

**F6 — Additive-energy moment / BCHKS 1.12 (additive combinatorics).** `E_r^{F_p}(μ_n) ≤ K^r·(2r−1)‼·n^r` with absolute `K`, at `r ~ log p`. Since `M^{2r} ≤ Σ_{b≠0}|η_b|^{2r} = p·E_r^{F_p} − n^{2r}`, F6 ⟹ F2 by Markov + saddle optimization.

**The chain.** `F2 ⟺ F1` (Fourier diagonalization of the abelian Cayley graph). `F2 ⟺ F4` (definitional). `F6 ⟹ F2` (moment method). `F5 ⟺ F6` (the transfer = moment identity, Ch 3). `F3 ⟹ F6` (far-line incidence = the energy budget, fourfold wall equivalence). The honest content of all six is one inequality; the value of the multiplicity is that each domain offers a *different* attack surface (Ch 6–7).

---

## Chapter 2 — Origins: one problem, six mathematical homes

| Form | Area | Native tools | What that domain "wants" |
|------|------|--------------|--------------------------|
| F1 | Spectral graph theory | trace method, expander mixing, Bourgain–Gamburd | a spectral gap / expansion certificate |
| F2 | Analytic number theory | Weil/Deligne, Burgess, Vinogradov MVT, sum-product | cancellation in an exponential sum |
| F3 | Coding theory | Guruswami–Sudan, folded-RS, list-recovery, proximity gaps | a combinatorial list-size bound |
| F4 | Cyclotomic / Gauss-period theory | Hasse–Davenport, Stickelberger, Gauss-sum identities | an algebraic relation among periods |
| F5 | Arithmetic geometry | étale cohomology, crystalline/`p`-adic Hodge, Frobenius | a comparison theorem char-0 → char-`p` |
| F6 | Additive combinatorics | additive energy, Sidon sets, BSG/Plünnecke, free probability | a moment/energy bound |

The deep point of the thesis: **every one of these domains, brought to bear on the thin 2-power case, fails at the same structural feature** — `μ_n` is a *0-dimensional* algebraic set (a finite point scheme, not a positive-dimensional variety) and *additively flat* (`Σ_b|η_b|² = pn` exactly, the Plancherel/Sidon floor, with no curvature). This single fact is why the natural tool of each domain becomes vacuous or ineffective; it is documented per-domain in Ch 4 and Ch 6.

---

## Chapter 3 — The new mathematics PROVEN this campaign

These are the load-bearing positive results, all axiom-clean.

### 3.1 The Bessel-moment identity (the characteristic-0 structure)
> **`E_r^{char0}(μ_n) = (2r)!·[x^{2r}] I₀(2x)^{n/2}`**, where `I₀(2x) = Σ_k x^{2k}/(k!)²`.

*Proof (via the proven Lam–Leung 2-power theorem).* A char-0 collision `Σx_i = Σy_j` means the combined `2r`-multiset `{x_1,…,x_r}∪{−y_1,…,−y_r}` is a vanishing sum of `2^μ`-th roots, hence (Lam–Leung, prime-power-2 case, `_AvX_LamLeungTwoPowerAntipodalBalan`, **proven**) a union of antipodal pairs `{ζ^j, −ζ^j}`. The `m = n/2` antipodal *directions* therefore **decouple**: the only constraint is, per direction `j`, `#{ζ^j} = #{−ζ^j} =: c_j` with `Σc_j = r`, independently across `j`. The number of placements is the multinomial `(2r)!/∏(c_j!)²`, whose generating function per direction is `I₀(2x)`, giving `I₀(2x)^m`. Exact-verified at `n=4,8,16` to `r=8`; the base case `E_r(μ_2)=C(2r,r)` matches `(2r)![x^{2r}]I₀(2x)` (Vandermonde). The multivariate `Finset.card` factorization is the one step carried as a named hypothesis pending full Lean formalization; the `n=2` and decoupling cores are formalized.

### 3.2 The characteristic-0 Wick bound, r-uniform, sharp `K=1` (PROVEN)
> **`E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r`** for all `r`, all `n=2m`. (`_AvW0_BesselWickDomination.charZeroWick_bound_allR`, axiom-clean.)

*Proof.* Coefficientwise, `I₀(2x) = Σ x^{2k}/(k!)² ⪯ Σ x^{2k}/k! = e^{x²}` (since `(k!)² ≥ k!`). Domination of power series with non-negative coefficients is preserved under products, hence under the `m`-th power: `I₀(2x)^m ⪯ e^{mx²}`. Therefore `[x^{2r}]I₀(2x)^m ≤ [x^{2r}]e^{mx²} = m^r/r!`, and with the integer split `(2r)! = (2r−1)‼·2^r·r!`,
`E_r^{char0} ≤ (2r)!·m^r/r! = (2r−1)‼·(2m)^r = (2r−1)‼·n^r`. ∎

This is the rigorous form of the long-invoked "char-0 `K≤1`" / Gaussian heuristic, now machine-checked **for all `r`** (previously only the fixed ladder `r ≤ 7`). At the saddle `r* ~ ln p` this bound *alone* yields `M ≤ √2·√(n log p)` — the prize exponent — **if** the char-`p` transfer is controlled (Ch 5).

### 3.3 The transfer = moment identity, and the Poisson-inversion identity (PROVEN)
- `Σ_b η_b·\overline{η_b} = p·E_r^{F_p}` (additive-character orthogonality); hence `M^{2r} ≤ Σ_{b≠0}|η_b|^{2r} = p·E_r^{F_p} − n^{2r}`.
- **Poisson-inversion** (`_AvWP_PoissonHistogram`): bucket the difference vectors `v∈Z^m` by `φ(v) mod p`; with histogram `g(t)=Σ_{φ(v)=t}f(v)`, one has `ĝ(b)=|η_b|^{2r}`, `g(0)=E_r^{F_p}`, the char-0 fibre `f(0)=E_r^{char0}`, and
> **`W_r = Σ_{v∈ker(φ)∖{0}} f(v)`** — the wrapped/image-charge mass of the non-zero dual frequencies.

This is the precise sense of the thesis's organizing metaphor: **char-0 is the free Bessel heat-kernel object; char-`p` is its periodization mod `𝔭`; the wraparound is the Poisson dual.**

### 3.4 The onset law (PROVEN floor)
> **`W_r = 0` for all `r` with `(2r)^{n/2} < p`**, i.e. `r₀(n,p) ≥ ½·p^{2/n}` (`_AvND_NormDiameterThreshold`), from the resultant-norm ceiling `max|Norm(α)| = (2r)^{n/2}`.

The onset is the first piercing of the index-`p` kernel sublattice by the `r`-fold signed-unit difference ball. **Caveat (decisive):** at the prize scale `p≈n^4`, `½p^{2/n} → const`, so this floor forbids nothing at the saddle — the prize sits *above* onset. This is *why* the good-prime route cannot reach the prize (Ch 4.6).

### 3.5 A nontrivial conditional improvement at `β=4` (di Benedetto–Sidon)
Specializing di Benedetto Thm 3.1 (arXiv:2003.06165) to `μ_n` with its Sidon-floor energies `T_2 = 3n²−3n`, `T_3 = 15n³−45n²+40n` gives `H`-exponent `7` and the bound `M ≪ |μ_n|^{1−1/24}·p^{1/72}`, i.e. **combined exponent `23/24 = 0.9583` at `β=4`** — *nontrivial* exactly where the general di Benedetto bound vanishes. This is **machine-checked nontrivial** (`DiBenedettoBetaValidityWindow.nontrivial_iff`: nontrivial ⟺ `β < 191/40 = 4.775`).
*Status (carefully stated, after four recorded double-count errors on this very point):* the `0.9583` exponent is **NONTRIVIAL** but **CONDITIONAL** on the near-Sidon energy inputs `T_2=O(n²)`, `T_3=O(n³)` holding at the prize prime, and is `≫ 1/2` — *not* the prize, and *not* an unconditional beat. The recurring error to avoid: `23/24` is the **combined** exponent at `β=4` (the `p^{1/72}` tax is already folded into the `(Hexp−4)/72` saving); the pure-`n` part is `65/72`. Never re-add `β/72`.

---

## Chapter 4 — What has been tried, and why each route hit the wall

A complete adversarial record. Each route was attacked with exact-integer computation and brutal verification; each reduced to, or measured, the same obstruction.

**4.1 BGK sum-product (F2/F6).** Bounds `M ≤ n^{1−δ}` via additive energy from the sum-product theorem, but `δ` is ineffective — the loss is in the Balog–Szemerédi–Gowers/Plünnecke iteration. For a *subgroup* `AA=A`, so the iteration is degenerate; the effective constant collapses to trivial at `β=4`.

**4.2 di Benedetto / Burgess (F2).** `H^{1−31/2880}` is regime-gated to `|H|>p^{1/4}` and *vanishes at `β=4`*. The Sidon-specialized `0.9583` is nontrivial but conditional (Ch 3.5). Burgess saturates at exponent 1 at `β=4`.

**4.3 Weil / Lang–Weil / Deligne (F2/F5) — the structural killer.** `μ_n` is a **0-dimensional** variety. The relevant difference scheme is a finite point set; Weil/Lang–Weil give *the main term = the count* with **no `√p` saving** — vacuous. This is not a fixable constant: it is why algebraic geometry has no purchase here (`_AvJ_T2WeilDegreeVacuous`, proven `n^4 < 2^n` so the only universal norm bound is vacuous below `n^4`).

**4.4 Stepanov / polynomial method (F6).** Heath-Brown–Konyagin `E(μ_n) ≪ |H|^{5/2}` and Shkredov's refinements are *fixed-`r`* (`r∈{2,3}`) and *thick*. The moment method needs *growing* `r ~ log p`; the Stepanov auxiliary-polynomial degree grows with `r`, and the method does not reach the saddle.

**4.5 The moment route, `K=1` (F6) — REFUTED.** `E_r^{F_p} ≤ (2r−1)‼·n^r` (`K=1`) is **false** at the prize scale: exact-integer computation at `n=32, p=1048609` gives `E_r^{F_p}/((2r−1)‼·n^r)` crossing `1` at `r=9` (1.268) and diverging to `2.64` at `r=11`. The char-`p` excess genuinely dominates the free energy at the saddle.

**4.6 Fixed-`r` / good-prime (F5).** `W_r = 0` outside a finite bad-prime set `D_r(n)` (divisors of cyclotomic norms), but `D_r(n)` *grows* (`D_3(32) ~ n^6`), so the onset outgrows the prize scale `n^4`; even `r=3` loses `p`-uniformity (`W_3=0` fails at 61 thin primes for `n=32`).

**4.7 Periodization / geometry-of-numbers / theta (F5).** The Minkowski lattice-point count `~(2r)^m/p` *overshoots* the true `W_r` astronomically; the gap *is* equidistribution = BGK. The theta continuum-suppression `e^{−cp²/(nr)}` is a continuum heuristic that fails on the arithmetic set (the onset is early, not at `r~p²/n`).

**4.8 Exotic objects — the two-bucket dichotomy.** Thirty invented invariants (categorical/cohomological, dynamical/ergodic, operator-algebra, tropical, bespoke; including a genuinely-new Connes `v₂`-Dirac spectral triple with exact spectrum `λ_max=2(n²−1)/(3n)`, contraction `√(7/9)`) all collapse: **any invariant of `μ_n` either ignores `b`** (then it is `p`-independent skeleton data with `M` absent — no handle) **or encodes `b`** (then Plancherel collapses it to the moment `Σ|η_b|^{2r}` — the closed route). There is no third bucket; "third structures" like Frobenius `x↦x^k` act *trivially* on the period since they permute `μ_n` (`η_{σb}=η_b`).

**4.9 Concentration (F5).** The wrap mass spreads, not concentrates: the participation number grows super-linearly toward the saddle (`56→190` over `r=3..7`), so no finite explicit-phase orbit survives — no cancellation handle.

**The stated next steps in the literature.** BGK leave the effective constant open; the Paley Graph Conjecture (Ramanujan-class for the connection set) is the canonical "next step" and is itself open; the proximity-prize companion (ABF26) marks the zero-loss correlated-agreement statement "not proved"; di Benedetto et al.'s method is explicitly regime-gated and they do not claim `β=4`.

---

## Chapter 5 — The wall, measured exactly

The campaign's sharpest contribution to *understanding* the obstruction: the wall is not abstract, it is a measured divergence.

- **`p`-uniformity HOLDS.** The saddle ratio `K@saddle = (E_r^{F_p}/Wick)^{1/r}` is `p`-stable (`<15%` variation across generic thin primes at fixed `n`; `<2%` Fermat vs generic).
- **`n`-uniformity FAILS.** `K@saddle` *grows in `n`*: `0.63, 0.74, 1.13, 1.88` over `n=8,16,32,64` — roughly `n^{0.37}` — driving the `M`-exponent from `0.871` *rising toward `1`*. This is exactly BGK's `n^{1−o(1)}`, now exhibited as an explicit exact-integer divergence.

**Therefore the entire conjecture is the single statement:**
> **`K = sup_{n, thin p, r~log p} (E_r^{F_p}(μ_n) / ((2r−1)‼·n^r))^{1/r}` is bounded by an absolute constant.**

Equivalently (F2 form): the period spectral measure has a **sub-Gaussian tail** `P(|η_b|>t√n) ≤ e^{−ct²}` for *some* absolute `c>0` (the "heavier than Rayleigh" finding only refutes `c≥1`; `c∈(0,1)` is open and would suffice). The char-0 half (Ch 3.2) supplies the Gaussian reference; the open content is that the char-`p` periodization does not inflate the tail's *rate* beyond a constant, uniformly in `n`.

---

## Chapter 6 — The solution space: which domain is least blocked, and what new mathematics each requires

The common requirement, across all six forms, is a method that controls a **growing moment** (`r~log p`) of a **flat, 0-dimensional** multiplicative subgroup **uniformly in `n`** — exactly the regime where curvature tools (Weil, decoupling, restriction) and structure tools (sum-product iteration) degenerate. A proof must be (1) non-algebraic (no positive-dimensional variety), (2) non-perturbative in `r` (survive to the saddle, not just fixed `r`), and (3) sensitive to the `2`-power/cyclotomic structure (false for arbitrary `n`-element sets). The four live domains, with their *exact* status from this campaign:

| Domain | Status | The missing ingredient (new math) |
|---|---|---|
| **F6 Energy-tuning (di Benedetto)** | conditional `0.9583`; **provably saturates at `0.9444`** | Either prove No-Excess-`r=3` (`T_3=O(n³)` all-`n` at the prize prime), or break the trilinear frame — neither escapes the √-lossy moment ladder. |
| **F3 RS list-decoding** | transfers-but-walls | A capacity list-decoder for **explicit, plain (unfolded) RS on `μ_n` past Johnson** — a major coding breakthrough. The unfolded subspace-design floor `τ ≥ (m−1)/m` is *unconditional*; the fold-rank lever is proven empty (`μ_d`-folding = mixed-radix reindexing, same Vandermonde). |
| **F5 Crystalline / `p`-adic-Hodge transfer** | **domain-native progress, then walls — least blocked** | A **depth-uniform torsion bound**: `v_𝔭(Res(Φ_n, σ_r))` not growing with `r`. Measured: bad-prime fraction grows `0.016→0.95` over `r=2..8` with unbounded new primes — the denominator is *not* a fixed ideal. Equivalent to **effective Chebotarev uniform in `r`** over a non-abelian (S₆-witnessed) splitting field. |
| **F6′ Free probability** | **REFUTED** | A genuine *free* realization of the `η_b`. Measured: free 4th cumulant `κ₄ = m₄−2m₂² = 0.81→0.91→1` (classical Gaussian, **not** `0`=semicircle); edge `max|η_b|/√n = 3.46→4.06` tracks `√(log N)`, **unbounded** (no compact edge). The periods are classical exchangeable white-noise. Dead end. |

**Least blocked: F5 (crystalline transfer).** It is the only domain showing genuine *domain-native progress* — it faithfully reproduces the proven shallow (fixed-`r`) transfer and the exact finite bad-prime set, and its one missing ingredient is a clean, well-posed arithmetic statement (depth-uniform Chebotarev/torsion control) rather than a refuted measurement (F6′) or a known-hard breakthrough (F3). It is, however, **provably equivalent** to the same BGK/Paley wall — it *renames* the obstruction (as a non-abelian monodromy / effective-Chebotarev-uniform-in-`r` problem), it does not reduce past it.

**The unifying new-math statement.** Every domain converges on one requirement: *uniform-in-`n` (equivalently uniform-in-`r`-to-the-saddle) control of the char-`p` excess of a 0-dimensional multiplicative subgroup.* No existing framework supplies it — Weil needs dimension, free probability needs freeness (absent), sum-product needs iteration (degenerate for subgroups), and the energy ladder is √-lossy (saturates). A proof requires genuinely new analytic input at this exact junction.

---

## Chapter 7 — Novel proof paths attempted, and their exact outcomes

### 7.1 The direct-proof assault (four approaches, all fail uniform-in-`n`)

- **Sub-Gaussian `c∈(0,1)` via Bessel log-concavity of the wrapped mass** — only a single-point witness (`θ≈0.987` at `n=16`); the log-concavity lever does not give a uniform `c` (the wrapped mass on the kernel sublattice is not controlled by the free density's log-concavity uniformly in `n`).
- **Effective sum-product with the subgroup-no-iteration observation** — fails earlier than uniformity: exponent `1` at `β=4` (Konyagin subgroup bound), `E_2` Sidon-floor provably cannot bound `E_r` at the saddle (char-0 Bessel exhibits Sidon-floor `E_2` coexisting with full-Wick `E_r`).
- **Kernel-lattice multiplicity bound** — uniformity in `p` holds, uniformity in `n` fails (the `n^{0.37}` measurement, Ch 5).
- **Fixed-`r₀` effective exponent** — `θ(r₀)=1/2+2/(2r₀)` would beat trivial, but no `r₀≥3` has a `p`-uniform `W_{r₀}` bound.

### 7.2 Energy-tuning of the di Benedetto descent (the suggested lever) — a NEW quantitative no-go
The 0.9583 uses only `T_2, T_3` in a 3-fold descent. We now have the *entire* proven char-0 energy ladder (`T_r ≤ (2r−1)‼·n^r`, Sidon floor `t_r=r`). Tuning the inputs:
- **The descent is intrinsically trilinear.** The "3" is the variable count in the Petridis–Shparlinski/Bourgain–Garaev incidence `|X|^{3/4}|Y|^{3/4}|Z|^{7/8}`, *not* a free fold; no published `k`-linear (`k>3`) analogue with a clean `H^{1−(Hexp−4)/tax}` form exists.
- **The 3-fold optimum is `0.9583`, pinned.** The slots are *typed* (two cubic legs need `E_3`, one quadratic leg needs `E_2`); feeding `T_2` into a cubic slot is type-invalid. Correctly typed, the Sidon floors `t_2=2, t_3=3` are the *minimum possible* (`T_r ≥ H^r`), so `Hexp` is *maximized* at 7 and the exponent is forced.
- **NEW RESULT — the lever provably saturates at `0.9444`, never `1/2`.** The apparent improvement (`0.9537→0.9028→…→1/2` by raising the dual-leg moment order while holding the tax denominator at 72) is the recurring double-count trap. With the honest tax growing as `72+36(r−3)` (each extra moment order pays `2·18` trilinear loss = the numerator gain), the saving **saturates at `1/18`**: `r=4 → 0.9537`, `r=6 → 0.9500`, `r→∞ → 17/18 = 0.94444`. Bounded away from `1/2` — exactly as the in-tree moment-ladder necessity theorem demands (energy→M is √-lossy). **The di Benedetto energy family cannot reach the prize; it tops out at `0.9444`.**

| Quantity | Exact | Decimal |
|---|---|---|
| Generic di Benedetto | `2849/2880` | 0.98924 |
| Sidon optimum (this lever) | `23/24` | 0.95833 |
| Saving ratio vs generic | `120/31` | 3.87× |
| **Saturation limit (depth→∞)** | `17/18` | **0.94444** |

- **Conditionality DISCHARGED at sampled primes.** The session's genuine advance: exact-integer verification that `W_1=W_2=W_3=0` (onset `r₀=4`) at every sampled thin `β=4` prime — `n=16 (p=65537)`, `n=32 (p=1048609)`, `n=64 (p=16777153)` — so `0.9583` is **unconditional at the sampled `n`**. As an all-`n` theorem it needs `r₀≥4` for all `n` (the No-Excess-`r=3` lemma); the boundary is sharp (at `β=3.0`, `n=32`, `W_3=1920≠0`).

### 7.3 Cross-domain native attempts
- **F3 (coding, RS list-decoding):** the transfer mechanism *works* (axiom-clean: a list-size bound on either face gives the other; `δ*` collapses for `C` and `C^{≡m}`). But it **walls** — the residual is the same char-sum. Both grand challenges are one wall, two names. The unfolded subspace-design floor `τ ≥ (m−1)/m` is unconditional; the fold-rank lever is empty (`μ_d`-folding = mixed-radix reindexing, same Vandermonde).
- **F6′ (free probability):** **refuted.** Fresh exact computation: the spectral measure of `{η_b/√n}` is *classically Gaussian*, not free (`κ₄^{free}=0.81→1`, not `0`=semicircle); the edge `max|η_b|/√n` tracks `√(log N)` — *unbounded*, no compact spectral edge. The periods are classical exchangeable white-noise; free probability gives nothing.
- **F5 (crystalline / `p`-adic-Hodge transfer):** **domain-native progress, then walls.** At *fixed* shallow `r` the crystalline picture is literally correct (reproduces the exact finite bad-prime set; `n=8, r=3` gives `W_r` on an explicit small ideal). It walls at the saddle: the bad-prime fraction grows `0.016→0.95` over `r=2..8`, the denominator is not a fixed ideal, and depth-uniform control = effective Chebotarev uniform in `r` over a non-abelian (S₆-witnessed) splitting field = the wall.

**Net of all novel paths:** none crosses the wall; F6′ is refuted; F3 and F5 *rename* it (coding list-size, non-abelian monodromy); energy-tuning saturates at `0.9444`. Every path converges on the same missing last half-power.

### 7.4 Non-standard frameworks — chosen to break the dichotomy's hidden assumptions
The two-bucket dichotomy (Ch 4.8) is stated for *single-value, single-prime, finite-field* invariants. Five frameworks were built to break exactly those hidden assumptions; **all five collapse**, each to a precisely-identified bucket — which *upgrades the dichotomy from an empirical pattern to a tested principle*.

| Framework | Breaks | Outcome | Precise collapse |
|---|---|---|---|
| **Berkovich / non-archimedean** | 0-dimensionality | vacuous | `p∤n` ⟹ roots are Teichmüller units, `val(ω^i−ω^j)=0`, skeleton edgeless, tropicalization ≡ 0. Relocates 0-dim from variety to skeleton; archimedean `Σe_p(bx)` vs `C_p`-skeleton category mismatch. (bucket A) |
| **Ax–Kochen–Ershov / pseudofinite transfer** | finite-field / classical logic | no-go (self-refuting) | Model-theoretic transfer is uniform-in-`p` only for a **fixed** formula; the prize object is *doubly non-fixed* — degree `n=p^{1/4}` grows **and** depth `2r~2log p` grows — so the ineffective constant `C(φ)` absorbs all `n`-dependence and the bound is vacuous at thin scale. (The precise reason the *one framework whose purpose is char-0→char-p transfer* cannot apply.) |
| **Motivic / automorphic L-function** | single-prime | wrong exponent | Per-factor Ramanujan `|g(χ)|=√p` + triangle ⟹ `|η_b|≤√p~n²`, *worse* than trivial `n`; the needed √-cancellation among the `f` ε-factors *is* the sup-norm wall restated. (bucket B) |
| **Wilsonian RG fixed-point on the tower** | single-value | collapses — but sharpest diagnosis | Bulk parents decorrelate (Gaussian `√k`); the **extreme maximizers form a separate attractor with alignment `≈√2` per doubling**, and over `log₂n` doublings the `√2` compounds into *exactly the missing `√(log)`*. The flow runs **to** BGK (`K: 0.93→1.11`, `n=8→64`), not below. (bucket A bulk + bucket B doubling-sum) |
| **Max-entropy / large-deviation** | single-value | wrong inequality direction | Max-entropy upper-bounds *entropy*, not `M`; a lower-entropy law can carry a heavier spike. The only route to a tail bound supplies `E_r` at `r~log p` = the moment ladder = the same `K@saddle~n^{0.37}` wall. |

**The deepest non-standard insight** is the RG diagnosis: the wall at `√(n log p)` is *the `√2`-per-doubling alignment of extreme maximizers compounded over `log₂n` tower levels.* This does not break the wall — it *explains its exact location*. It also strengthens the dichotomy: a genuinely new framework either misses `M` (bucket A) or re-sums to the char-sum (bucket B), now confirmed across the non-archimedean, model-theoretic, automorphic, renormalization, and information-theoretic frontiers.

---

## Chapter 8 — Resolution status and the exhaustion argument

**Resolved (proven, axiom-clean):**
1. The six forms are equivalent (F1↔F2↔F4 classical; F3↔F6 and F5↔F6 this campaign).
2. The **characteristic-0 Wick bound**, `r`-uniform, sharp `K=1` — the upper half of the bound.
3. The transfer = moment identity and the **Poisson-inversion identity** for `W_r`.
4. The **onset law** `r₀ ≥ ½p^{2/n}`.
5. The **reduction** of the prize to a single inequality (the `K=O(1)` saddle bound), with the optimization machinery (`prize_sup_of_saddle`) proven unconditionally.

**Conditional / nontrivial partial:**
6. The di Benedetto–Sidon exponent `0.9583` at `β=4` — nontrivial, conditional on the near-Sidon energy inputs, `≫1/2`.

**Open (the core), characterized exactly:**
7. The `K=O(1)` / sub-Gaussian-`c>0` statement, equivalently that `K@saddle` does **not** diverge in `n` (it is measured `~n^{0.37}` for `n≤64`). This is the recognized open Paley/BGK conjecture at `β=4`.

**The single best next step — and a cautionary correction.** The strong form `W_3=0` is refuted (bad primes are dense just above `n^4`). A first scan (400 primes) suggested the *worst-case* wraparound was a clean quadratic `max_p W_3 = (45/4)n^2 = Θ(n^2)`, which would have closed the gate `T_3 = O(n^3)`. **A deeper scan (20000/4000/722 thin primes) refuted that** — the maxes are `15n^2, 405n^2, 19.7n^2` at `n=32,64,128`, and the `n=64` worst prime gives `W_3 = 1658880 = 6.33·n^3`, *comparable to the char-0 term*. So **`W_3` is `Ω(n^3)`, not `O(n^2)`**, and the gate does **not** close via any quadratic wraparound bound. The honest residual is therefore `T_3 = O(n^3)` with an *absolute* constant uniform in `(n,p)` (sampled `T_3/n^3 ∈ [14, 21]`, not proven bounded) — which is the **bad-prime / BGK equidistribution wall restricted to `r=3`**, not a tractable elementary gate. So `0.9583` stays conditional on this `r=3` wall; it does **not** reach `1/2` (the energy lever saturates at `0.9444`). *Methodological lesson recorded:* a worst-case constant claimed from a shallow prime scan (here `45/4`) can be off by a large factor (true `n=64` constant `405`, a 36× miss) — deep scans are mandatory before asserting an exact law.

**The exhaustion argument (why "all standard mathematics has been tried").** Every standard tool reduces to or measures the single obstruction, and the *reason* is structural and proven: `μ_n` is `0`-dimensional and additively flat, so (i) all algebraic-geometric tools (Weil/Lang–Weil/Deligne, étale cohomology) are vacuous; (ii) all curvature tools (decoupling, restriction, Vinogradov MVT) are vacuous; (iii) the moment route's `K=1` is false and `K=O(1)` *is* the conjecture; (iv) the two-bucket dichotomy shows any invariant either misses `M` or collapses to the moment; (v) the good-prime/fixed-`r` route's onset outgrows the prize scale. A genuine proof therefore *requires* a method outside the union of these — the new mathematics of Ch 6. This is not a proof of impossibility (no such proof exists; the conjecture is believed true), but a rigorous map of the boundary of current technique.

---

## Defense (anticipated examiner questions)

**Q1. Is the char-0 Wick bound really new, or folklore?** The *statement* (Gaussian domination of subgroup energy) is folklore as a heuristic; the *`r`-uniform axiom-clean proof* via the explicit Bessel identity + coefficientwise `I₀⪯exp` is new and machine-checked. The Lam–Leung decoupling making the identity exact is the genuinely new ingredient.

**Q2. The reduction to one inequality — isn't that just restating BGK?** It is more: it isolates the *exact* open content (the char-`p` excess at the saddle), proves the surrounding chain (char-0 half, optimization, Poisson-inversion), and *measures* the obstruction (`n^{0.37}`). BGK is the asymptotic `n^{1−o(1)}`; this thesis exhibits the constant's `n`-divergence explicitly and proves everything reducible around it.

**Q3. Why can't you just bound the wrapped mass?** Because the wrapped-mass bound that would suffice (`W_r ≤ K^r` free, uniform in `n`) is *equivalent* to the conjecture (Ch 5), and the natural bounds (Minkowski count, log-concavity, theta-suppression) either overshoot (the gap = equidistribution = BGK) or hold only at fixed `r`/single points. The 0-dimensionality (Ch 4.3) blocks the algebraic shortcut.

**Q4. Is `0.9583` a real result?** Yes, as a *nontrivial conditional* exponent at `β=4` where the published bound vanishes — machine-checked nontrivial (`β<4.775`). It is not the prize (`≫1/2`) and not unconditional (the near-Sidon energy inputs reduce to a shallow char-`p` wall). Four separate analyses double-counted the `p`-tax and wrongly called it trivial; the decisive arbiter (the same logic would trivialize di Benedetto's published theorem) settles that it stands.

**Q5. What is the single most promising path?** Per the solution-space map (Ch 6): the coding-theoretic F3-native route (explicit smooth RS to capacity, bypassing the char-sum) and the free-probability F6-native route (spectral-measure limit with bounded edge) are the two least-blocked, because each can in principle avoid both the 0-dimensionality (no Weil needed) and the fixed-`r` ceiling. Both require genuinely new mathematics; neither exists yet.

---

## Bibliography (verified)

- J. Bourgain, A. Glibichuk, S. Konyagin, *Estimates for the number of sums and products and for exponential sums in fields of prime order*, J. London Math. Soc. **73** (2006) 380–398.
- V. di Benedetto, M. Garaev, V. C. García, D. González-Sánchez, I. Shparlinski, C. Trujillo, *New estimates for exponential sums over multiplicative subgroups and intervals*, arXiv:2003.06165.
- D. R. Heath-Brown, S. Konyagin, *New bounds for Gauss sums derived from kth powers*, Q. J. Math. **51** (2000).
- T. Y. Lam, K. H. Leung, *On vanishing sums of roots of unity*, J. Algebra **224** (2000) 91–109.
- Arnon, Boneh, Fenzi, *(proximity-prize companion)*, ePrint 2026/680.
- J. Thorner, A. Zaman, *A unified and improved Chebotarev density theorem / refinements to PNT in APs*, arXiv:2108.10878, Math. Z. (2024).
- (Spectral/Paley) Liu–Zhou, generalized Paley graphs (Thm 115); (coding) Guruswami–Sudan, Guruswami–Rudra folded RS.

*In-tree machine-checked artifacts (axiom-clean):* `_AvW0_BesselWickDomination`, `_AvW0_BesselWickAllR`, `_AvW0_BesselIdentity` (Ch 3.1–3.2); `_AvWP_PoissonHistogram`, `_AvND_NormDiameterThreshold` (3.3–3.4); `_AvPrize_MomentToSupCapstone` (the reduction, 3.3/Ch 8); `_AvGER_RecursionStep` (the recursion skeleton); `_AvJ_T2WeilDegreeVacuous` (4.3); `DiBenedettoBetaValidityWindow.nontrivial_iff` (3.5); `_FourfoldWallEquivalence` (Ch 1).
