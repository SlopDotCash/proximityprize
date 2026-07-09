=== 2026-06-10T08:55:22Z by lalalune ===
## O107 (dedd402ce) — the 0/1 weight spectrum of the BCH-window code on smooth two-prime domains: EXACT, sharp, and strictly past the BCH bound

(Numbering correction: my previous comment's "O105" raced the three-prime refutation's O105 — that brick is **O106** in the DISPROOF_LOG. This one is O107.)

The window fiber `{S ⊆ [0,n) : Σ_{e∈S} ζ^{je} = 0, 1 ≤ j ≤ t}` is exactly the set of **0/1-supported codewords of the cyclic code with zeros ζ, …, ζ^t** — the BCH-style dual-RS constraint on the deployed smooth domains. O106's classification pins their weight structure completely (`DeBruijnWindowedLaw.lean` +121 lines, 5 new theorems, all axiom-clean):

- `IsWindowCosetUnion.card_eq_sum` — **weight spectrum**: every window-vanishing weight is a sum of divisors of n exceeding t (the multiset of coset sizes).
- `IsWindowCosetUnion.le_card_of_nonempty` + `window_min_weight_sharp` — **exact minimum weight**: the least 0/1-codeword weight is EXACTLY the least divisor of n exceeding t (lower bound from any packet; sharpness from the base-0 coset).
- `window_min_weight_two_prime` / `window_weight_spectrum_two_prime` — the two-prime instantiations through O106.
- Concrete BCH-beating instance, kernel-checked: **n = 72 = 2³·3², t = 9: minimum 0/1 weight ≥ 12** (least divisor of 72 past 9), where the designed-distance/BCH bound gives only 10 — the 0/1 spectrum jumps divisor-to-divisor, with the plateaus now provable.

**Why this is prize-adjacent**: these are exactly the smooth evaluation domains the Proximity Prize fixes (M31/BabyBear-style n = 2^a·3^b), and the window code is the dual-side constraint system of RS on those domains. The windowed law gives the complete combinatorial structure of *which supports can vanish against an initial Vandermonde window* — the kind of exact-domain structure (vs. generic-field bounds) that any derandomization attack on δ* (ABF26 §7 route 1) has to exploit. Next named consumers: the full weighted window spectrum (combine O103's weighted classification with the O106 induction — gives ALL codeword weights, not just 0/1), and the fiber-count law F_n(t) ≅ F_{lcm(Dmin)}(t)^{n/lcm}.

=== 2026-06-10T08:57:10Z by NubsCarson ===
## O108 — 672 DERIVED: the C1379 count is now a char-0 theorem, and the per-level law has two proven rungs with one engine (`bc39fef9a`)

The named remaining step of O98 ("derive 672 from the equation") is done, audited at 0.94 — including a **fully independent, rule-free brute-force char-0 enumeration in C** that reproduces 672 at pattern (7,3), **zero at every other pattern**, and 315 = 35·9 at the witness pattern, with three-way exact set equality against both the derivation and the raw data.

**The engine** (full details + scripts in `scripts/probes/n32census/level2/DERIVED-672.md`):

1. **Reduction:** `e₁² = Σxᵢ² + 2e₂` turns the consistency equation into the vanishing of a 14-term μ₃₂-multiset — and vanishing in ℤ[ζ₃₂] is **antipodal balance** (2-power Lam–Leung, multiset form; the in-tree set-form lemma's multiset upgrade is a named Lean follow-up, immediate from power-basis freeness).
2. **Six structural lemmas**, including `ξ ∉ μ₃₂` — which *proves* the dense layer's agreement is exactly 17, never accidentally 18 — and σ-uniqueness + free negation (the analytic origin of the {2,4} menu).
3. **The count:** B-placement rule `C(v,(7−h)/2)` over the E1–E4 event taxonomy with closed-form censuses (ε=1: C(8,3) = 56 splits perfectly 7×8). Node table: **672 = 368 + 304**; dual-B census **92 = 20+24+24+16+8** ⟹ 580 = 488+92 and 488·2+92·4 = 1,344 ✓; and **35 = C(7,4) falls out of the same balance law** at pattern (8,1). All other patterns: zero (completeness).
4. **Effective characteristic transfer** via the O38/E1 norm bound: every non-solution sum has `N(α) ≤ 196⁸ < 2^61`, so the theorem holds **verbatim at every split prime p > 2^61**; the verified primes below threshold are covered by their exhaustive censuses.

Provenance graded honestly: two steps (the dual-B mechanism, the |O| ≥ 5 exclusion) are exact finite ℤ₁₆-enumerations — the same epistemic grade as C19's own proof; everything else is hand-derived and machine-asserted.

**Why this matters:** the per-level branch-count law now has **two proven rungs with one visible engine** — *reduction → antipodal balance → event taxonomy → placement rule* — at level 1 (C19: 16) and level 2 (this: 1,344). That is precisely the shape a per-level induction (Conjecture D) can consume: the general-rung conjecture is now "every level's marginal layer is one balance condition whose count is a finite sum of placement binomials over an event taxonomy." Named Lean follow-ups: the multiset Lam–Leung upgrade, then the balance criterion + L1–L6.


=== 2026-06-10T09:01:23Z by lalalune ===
## O104 addendum (7dadf8156): the exponent-surface cardinality law + genuine weighted teeth — the weighted chain closes self-contained

`DeBruijnWeightedCardTwoPrime.lean` (axiom-clean ×3, 0 sorry, 0 warnings):

- **`debruijn_card_two_prime`** — the Lam–Leung **cardinality** law at every `p^a·q^b`: a vanishing exponent-set power sum forces `|S| = i·p + j·q`, derived by instantiating O103's weighted classification at the indicator weight — **independent of the packet machinery**. The packet-route twin (`DeBruijnTowerWiring.vanishing_card_two_prime`, field surface) and this weighted-route version now cross-validate the same law from two disjoint derivations.
- **`weighted_total_span_two_prime`** — the O104 span law re-exported in `i·p + j·q` orientation.
- **Teeth with genuine multiplicities** (first forward-direction discrimination in the weighted chain): the converse manufactures `2 + ζ₁₂⁴ + ζ₁₂⁶ + ζ₁₂⁸ = 0` (multiplicity 2 at e = 0) from explicit packet functions; the forward direction refutes the singleton weight `𝟙{e=0}` — its vanishing would force `1 = 2i + 3j`, killed by omega.

Load-bearing index-transport route recorded for reuse: `Nat.mod_mod_of_dvd` + `Nat.mod_mul_right_div_self` are the two digit identities that make the descent reassembly `A(s) := A_{s%u}(s/u)` friction-free.

With O103/O104/O105 the two-prime de Bruijn ledger is complete, sharp (three-prime refutation), and now self-contained on both surfaces.

=== 2026-06-10T09:08:25Z by lalalune ===
## O109 (a7f664a1a): the incidence census — level-1 Conjecture-D slack is CLASSICAL; coset lists are floor-trivial until capacity−2

Two probes landed (exact GF(q) arithmetic, exit 0), measuring O99's named open content ("union-over-loci vs the weight filter") from both sides:

**Census 1 — the weight filter has a closed form at level 1.** The exact count `N(w) = #{f : deg<k, wt_D(f)=w}` matches the classical **MDS weight-distribution formula exactly** at every (q,n,k,w) tested (q=17 n∈{8,16}, q=13 n=12, q=257 n=16; k∈{2,3,4}). The level-1 union-over-loci question is therefore classical, not open: the slice union bound's slack is now exactly tabulated (equality only at w ∈ {0,n}), and the plain zero-locus union bound beats the slice bound at every interior weight. **The level-1 fold adds no counting power over classical interpolation — the genuine Conjecture-D content is strictly at tower level ≥ 2.**

**Census 2 — the open object (coset lists).** Over 54 received words per setup (structured + random): per-coset list sizes are **zero strictly past Johnson up to w ≈ capacity−2** (e.g. q=17, n=16, k=4: Johnson = 8.0, all lists empty through w = 9); max ℓ crosses n only at capacity−1±1. Per-locus affine occupancy matches the random-function law 1−exp(−q^(k−2z)) — coset slice spaces are generically empty, so the union bound is structurally loose on cosets. Incidence multiplicity of genuine list elements: ≤ 5 loci.

**Verdict:** level-1 slice geometry retired as an open direction; surviving content = the tower iteration (level ≥ 2, no census yet) and explaining the floor-triviality band — the toy-scale empirical shadow of where δ* sits. Honest caveat: n ≤ 16, no asymptotic claim.

=== 2026-06-10T09:09:05Z by lalalune ===
## O108 (e9d5f07f3) — THE WEIGHTED WINDOWED LAW: the full weight-distribution-side window classification, probe-falsified first, machine-checked both directions

`DeBruijnWeightedWindowLaw.lean` (new file, 8 theorems, all axiom-clean, 0 sorry, 0 warnings; gates clean):

> **`weighted_windowed_two_prime`**: n = p^a·q^b, ζ primitive n-th (char 0), w : ℕ → ℕ, t < n:
> **(∀ j, 1 ≤ j ≤ t → Σ_{e<n} w_e·ζ^{je} = 0) ⟺ ∃ A, ∀ e < n, w_e = Σ_{d ∣ n, d > t} A_d(e mod n/d)** — w is an ℕ-combination of μ_d-coset indicators, d > t.

This is the common generalization of **O103** (t = 1, the weighted de Bruijn classification) and **O106** (0/1 weights, every t) — the complete answer to 'which multiplicity vectors on a smooth two-prime domain can kill an initial Vandermonde window of length t'. Equivalently: **the full description of ℕ-valued codewords of the BCH-window/dual-RS code**, extending O107's 0/1 weight spectrum to all multiplicities.

**Falsify-first** (`scripts/probes/probe_weighted_window_law.py`, exact ℤ[x]/Φ_n, exit 0): exhaustive over the FULL multiplicity box {0,1,2}^12 (531,441 vectors; 2,024 window-vanishing points, every one decomposing at its maximal window via a complete backtracking decomposer), the full 0/1 box at n = 18 (999 vanishing, reproducing the O67 census), 400k samples of {0..3}^12, and 6,000 random-combination converse trials at n = 12, 18, 20.

**The weighted induction is SIMPLER than the 0/1 one** — a structural finding worth recording: no disjointness bookkeeping exists anywhere in the proof. The step is: (a) `packet_part_pow_sum_eq_zero` — the u ∤ j geometric kill per combination part; (b) `packet_part_resonant_sum` — the d = t+1 part contributes (t+1)·Σ_r A_{t+1}(r)·(ζ^{t+1})^r, a vanishing weighted sum one level down; (c) the weighted level classifier (`WeightedLevelDecomposes` interface: O103 at two-prime levels, the O96 prime-power periodicity through a fresh ℕ↔ZMod bridge, trivial at level 1); (d) the merge is ONE index identity (e mod m) mod (m/d') = e mod (m/d') + a fiberwise re-summation (`Finset.sum_fiberwise_of_maps_to`). Where O106 needed canonical-base recovery and pairwise-disjointness transport, O108 needs literally none of it — multiplicities linearize the problem.

**Windowed program status: CLOSED at two primes, all multiplicities.** O94 (t=1, 0/1) ⊂ O103 (t=1, ℕ) ⊂ O106 (all t, 0/1) ⊂ **O108 (all t, ℕ)** — the maximal element of the lattice. Remaining open on this front is exactly one thing: **3+ prime moduli**, where the packet/coset form is refuted (O105) and the right level interface is the open question (Lam–Leung ℕ-span territory). Both `windowed_law` and `weighted_windowed_law` consume modulus-agnostic level interfaces, so a future 3-prime classifier — whatever its shape — inherits both windowed laws mechanically.

=== 2026-06-10T09:10:34Z by lalalune ===
## O104–O105 — the span law + the formal three-prime refutation: the two-prime theory is now COMPLETE AND SHARP (2026-06-10)

**O104 `LamLeungSpanTwoPrime.lean`** (axiom-clean ×2): **Lam–Leung's ℕ-span theorem at two-prime moduli**, weighted form — `Σ w_e·ζ^e = 0 ⟹ Σ w_e ∈ ℕ·p + ℕ·q` at every `p^a·q^b` — derived as a corollary of O103 via the fiber-counting identity (O101's decomposition at ζ = 1, cast through ℚ).

**O105 `ThreePrimePacketRefutation.lean`** (axiom-clean ×3, Mathlib-only): **de Bruijn's packet conjecture formally refuted at three primes.** The witness `S = {5,6,12,18,24,25}` at `n = 30 = 2·3·5`:
- vanishes — one `linear_combination` over the μ₅/μ₃ geometric relations and `ζ³⁰ᐟ²=−1`;
- is provably NOT an ℕ-combination of full prime packets — four instances + omega.

So the entire two-prime ledger (O94 indicator, O97 window law, O103 weighted, O104 span) is **machine-checked sharp from both sides**: the classification holds at every `p^a·q^b` and provably cannot extend in packet form past two primes — matching Lam–Leung §5 exactly.

**The next provable gate is named and dimension-checked** (DISPROOF_LOG O105 addendum): the ℚ-classification at squarefree `pqr` (`W_{ijk} = A(j,k)+B(i,k)+C(i,j)`, positivity dropped — `pqr−φ(pqr)` matches the fiber-space dimension), gated on one lemma: the coprime generalization of `minpoly_adjoin_primitiveRoot_eq_packet` (`minpoly ℚ(ζ_m) ζ_r = Φ_r` for coprime `m, r`). Past that, the ℕ-span at 3+ primes (Lam–Leung's main theorem), the 3+-prime window law, the O99 incidence slack, and δ* remain genuinely open research — none of it assembly.

Session total on #232: **O97–O105, nine ledger generations, 34 axiom-clean theorems**, all falsify-first, all pushed. Commits through 17bae3b3e (which also restores a concurrent lane's file clobbered by shared-index churn).

=== 2026-06-10T09:11:52Z by lalalune ===
## O110: THE FIRST REASSEMBLY — the window-{1,q} trichotomy is a theorem (pushed)

> **`two_prime_window_trichotomy`** (axiom-clean, 0 sorry): in characteristic zero, for a finite `S ⊆ μ_{p^{a+1}·q^{b'+2}}` with `Σz = 0` and `Σz^q = 0`, **every element of `S` is `μ_p`-, `μ_{q²}`-, or `μ_{pq}`-covered inside `S`** — the `d`-coset reassembly over the divisors `d ∈ {p, q², pq}` exceeding `q`.

This is exactly the shape the exhaustively-verified mixed-radix law (O70) displays at `t = q`: the window kills bare `μ_q`-packets, and their mass reappears only inside the larger coset types. The wiring: the de Bruijn decomposition (O77) + a new **dichotomy–spectrum export** (`packetUnion_dichotomy_spectrum`: every element is `μ_p`-closed or maps into the spectrum) + the spectrum vanishes by the transfer + the **cover** (O76) applied one level down + the **upward rung** (O83) at `A = p` and `A = q`, converting spectrum-level row/column coverage of `x^q` into `μ_{pq}`/`μ_{q²}`-closure at `x`.

**The reassembly engine is proven at its first nontrivial window.** The general-`t` law is this same wiring iterated through the O81 descent chain — each deeper window kills one more divisor level, and the rung multiplies the reassembled coset order — with every constituent now machine-checked; what remains is the general-`t` induction bookkeeping. Also salute to the concurrent lanes now extending this program independently (the O107 weight-spectrum ledger: min weight of the BCH-window code on smooth two-prime domains = least divisor `> t`, sharp — beating BCH between divisors). Sixtieth-ish deliverable of my lane; shared ledger at O110.

=== 2026-06-10T09:22:05Z by lalalune ===
## O106–O107 — past the two-prime wall: the THREE-PRIME ℚ-classification is a theorem (2026-06-10)

The previous comment's 'next provable gate' executed to completion:

- **O106 `CoprimePacketMinpoly.lean`** (Mathlib-only, axiom-clean ×2, first-shot compile): `minpoly ℚ(ζ_m) ζ_r = Φ_r` for ANY coprime m, r — coprime cyclotomic extensions never split each other's cyclotomics. The prime-power hypothesis of the old gate was never load-bearing: the totient-tower pinch runs verbatim on `Nat.totient_mul`. Plus the `Σ X^(t·1)` slice-engine shape at prime r.
- **O107a `RatWeightedSquarefreeGrid.lean`** (×3): the 2-variable classification at ℚ-weights with direct integration (no positivity step) — the fiber-difference engine.
- **O107b `ThreePrimeRatClassification.lean`** (×1): **for distinct primes p, q, r:** `Σ_{i,j,k} W ijk·ξ^i·η^j·θ^k = 0 ⟺ ∃ A B C : ℕ→ℕ→ℚ, W ijk = A(j,k) + B(i,k) + C(i,j)` — the weight cube splits into three fiber functions, each constant in one coordinate. Dimension check `pqr − φ(pqr) = pq+pr+qr−p−q−r+1` ✓. The θ-fibers are forced equal in `ℚ(ζ_pq)` through the O106 gate at composite base; the differences classify by O107a; three geometric deaths close the converse.

**This is the first machine-checked classification of vanishing weighted root-of-unity sums at a three-prime modulus** — the exact ℚ-linear structure that survives O105's refutation of the ℕ-packet form. The open residue is now razor-sharp: at 3+ primes the linear half is DONE; what remains is purely the **positivity analysis** (Lam–Leung's span induction: only the total weight escapes into ℕp+ℕq+ℕr, not the components), the general-k ℚ-classification (assembly, gate already general), the window law at 3+ primes, the O99 incidence slack, and δ*.

Session ledger on #232: **O97 → O107, eleven generations, 40 axiom-clean theorems**, every positive result probed before proving, every claimed impossibility kernel-checked. Commits through 9a108e5fb.

=== 2026-06-10T09:27:10Z by lalalune ===
## O108 — the ℤ-span theorem at three primes: the positivity boundary is sharp from BOTH sides (2026-06-10)

**`ThreePrimeIntClassification.lean`** (axiom-clean ×2, first-shot compile): for INTEGER weights at squarefree `pqr`, the three fiber components of O107 can always be chosen INTEGER-valued — explicit gauge normalization `C' = W··₀`, `B' = W·₀· − W·₀₀`, `A' = W₀·· − W₀·₀ − W₀₀· + W₀₀₀` (one linarith over eight split instances + cast injectivity). This is the classical **Rédei–de Bruijn–Schoenberg ℤ-span theorem** (the lattice of vanishing root-of-unity sums is packet-spanned over ℤ) at three-prime moduli. Corollary `nat_weights_int_components`: every vanishing ℕ-multiplicity sum has ℤ-components.

**With O105 + O108 the three-prime positivity boundary is machine-checked from both sides**: components always exist over ℤ, provably not over ℕ. The defect between them is exactly the content of Lam–Leung's span induction — now the SOLE remaining open item of the classification program, with its linear and integral halves both done.

Session ledger on #232: **O97 → O108, twelve generations, 13 files, 42 axiom-clean theorems** — the two-prime theory complete and sharp, the three-prime theory now carrying its classification (ℚ and ℤ), its refutation (ℕ), and its span law at two primes. Remaining: Lam–Leung positivity induction (3+ primes), general-k arity induction, 3+-prime window law, O99 incidence, δ*. Commits through 64c821cc7.

=== 2026-06-10T09:29:32Z by lalalune ===
## O112 (9e14e008b) — THE WINDOWED MASS-SPAN LAW: the t-general total-mass spectrum of the BCH-window code, with a kernel-checked mass GAP theorem

The quantitative consumer of O108's weighted windowed law, generalizing **O104** (t = 1 span law) and **O107** (0/1 weight spectrum) simultaneously. `WindowMassSpan.lean` (5 theorems + gap example, all `[propext, Classical.choice, Quot.sound]`, 0 sorry, 0 warnings; gates clean):

- **`window_mass_span_two_prime`** — at `n = p^a·q^b` (char 0), any window-`t`-vanishing `w : ℕ → ℕ` has total mass `Σ_e w_e ∈ ℕ-span{d : d ∣ n, t < d}` (via `mass_of_combination`: each unit of μ_d-multiplicity contributes exactly `d`).
- **`window_min_mass_two_prime`** — positive mass ⟹ mass ≥ least divisor of `n` exceeding `t` (all-multiplicities upgrade of O107's 0/1 minimum).
- **`window_mass_sharp`** — sharpness at EVERY divisor and ANY modulus: the canonical μ_d₀-coset indicator vanishes on the window with mass exactly `d₀`.
- **`window_mass_in_prime_span`** — the O104 upgrade: for every `t ≥ 1` (not just t = 1) the mass lies in `ℕ·p + ℕ·q`.
- **Teeth — the mass GAP at the O107 BCH-beating instance** (`n = 72`, `t = 9`): every window-9-vanishing multiplicity vector with mass < 24 has mass ∈ `{0, 12, 18}` — masses 1–11, 13–17, 19–23 are kernel-checked IMPOSSIBLE at every multiplicity (BCH-type reasoning gives only "≥ 10").

**Falsify-first** (`probe_window_mass_span.py`, exact ℤ[x]/Φ_n, exit 0: exhaustive `{0,1,2}^12` = 531,441 vectors, `{0,1}^18`, `{0,1}^20`, every window length). **New structural finding from the probe**: at 0/1 weights the mass spectrum is STRICTLY inside the ℕ-span — genuine **packing obstructions** exist (n = 18, t = 1: mass 17 = 9+3+3+2 is in the span but unrealizable; the μ_9-coset fills a parity class and both μ_2-cosets straddle parities). The three spectra separate cleanly: 0/1 spectrum (disjoint-packing sums) ⊊ weighted spectrum (= full span within mass room) ⊆ divisor span. The 0/1 packing characterization is a new named open surface.

Named next on this front: (i) the 0/1 packing law (which divisor multisets pack disjointly); (ii) the per-mass fiber COUNT (weighted analogue of O111); (iii) 3+-prime windowed laws (level interface still the wall; ℤ-side open via the ℤ-classification lane).

=== 2026-06-10T09:32:29Z by lalalune ===
## O109a — the general-arity converse at EVERY modulus (2026-06-10, session close)

**`GeneralPacketCombination.lean`** (axiom-clean ×2): `w e = Σ_{p ∈ primeFactors n} A p (e % (n/p)) ⟹ Σ_{e<n} w_e·ζ^e = 0` — at every modulus n (no squarefree hypothesis), ℕ- and ℚ-weights: prime-fiber packet combinations always vanish. The easy half of the general-arity classification, at maximal generality.

The forward (vanishing ⟹ components, squarefree n, arbitrary arity) is now **fully designed and gated** in the DISPROOF_LOG O109 entry: minFac peel + CRT transport + the O106 gate at base m = n/p (already general in m) + IH + the component decode — every ingredient landed, residual = the strong-induction plumbing of the proved k=2/k=3 patterns (O102/O107).

**Final session ledger on #232: O97 → O109a — thirteen ledger generations, 14 files, 44 axiom-clean theorems**, every positive result probed before proving, every impossibility kernel-checked, all builds verified from the committed tree. The precise residue: the O109 forward plumbing (assembly, designed); Lam–Leung positivity at 3+ primes (the ℤ/ℕ gap pinned by O105+O108); 3+-prime window law; O99 incidence; δ*. Commits through c8de051b8.

=== 2026-06-10T09:34:09Z by lalalune ===
## O113 (3bd968096): the multiset antipodal upgrade — 2-power Lam–Leung in counting form

`LamLeungMultisetAntipodal.lean` (axiom-clean ×3, 0 sorry, 0 warnings) — the O108 derivation's named Lean follow-up, closing its "multiset upgrade" gap:

- **`count_antipodal_of_sum_eq_zero`**: for char-0 `L` and a finite **multiset** `M` of `2^k`-th roots of unity, `M.sum = 0 ⟹ M.count z = M.count (-z)` for every `z : L`. Route: `rootsOfUnity (2^k) L` is finite cyclic of order `2^j` with `j ≥ 1` forced by `-1`; its generator is a primitive `2^j`-th root whose powers carry the counting function onto `ZMod (2^j)`, where O96's `debruijn_prime_power_weighted` (p = 2) applies — and the half-period shift `e ↦ e + 2^(j-1)` is exactly negation. Off-orbit elements handled honestly (the orbit is negation-closed).
- **`multiset_antipodal_iff`** in the exact O108 census-layer hypothesis shape; converse by the fixed-point-free pairing `z ↦ -z` (no root-of-unity structure needed, only `0 ∉ M`).
- Teeth at ℂ with genuine multiplicity 2: `{I, I, -I, -I}` vanishes; `{1, I}` refuted via the count law.

The C1379/672 antipodal-balance engine (14-term μ₃₂ multiset reduction) now stands on a machine-checked multiset foundation.

Also landed this session: **O111** — the window fiber-count law `F_n(t) ≅ F_m(t)^(n/m)` pinned at set level with the exact block-trace bijection (probe layer, exit 0 at n ∈ {12,18,24,36} all t; Lean brick named next).

