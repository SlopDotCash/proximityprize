# #466 lane N5 (SoS duality): the COLLAPSE theorem — SoS degree is NOT the wall; the seed conjecture d\* ≳ ln q is FALSE; the wall relocates to certificate UNIFORMITY

**Date:** 2026-07-01, novel-math round, lane N5-sos-duality (proposer).
**Probe:** `scripts/probes/probe_466_novel_sos_collapse.py` → `scripts/probes/_out_466_novel_sos_collapse.txt`.
**Verdict class: SELF-REFUTATION-WITH-STRUCTURE.** The lane's assigned goal — prove the minimal
SoS degree for `M ≤ C√(n log(p/n))` over the phase encoding is `d* ≳ 2 ln q`, making the wall an
SoS lower bound — is **FALSE, provably**: at fixed `β = log_n p`, degree-`O(1)` SoS is COMPLETE
for all true inequalities on the variety (Theorem A below), because dyadic-subgroup **thinness
itself** forces the encoding's algebra to saturate at `O(1)` degree (BGK ⟹ `O(1)`-fold sumset
covering). The lone-spike measure does NOT extend to a valid low-degree pseudo-expectation unless
the prize is false — the extension question is EQUIVALENT to the prize (Corollary A1), so
pseudo-distribution methods cannot produce a wall-explanation here. What the lane delivers
instead: (i) a new exact dictionary (SoS degree-d visible arithmetic = ℓ¹-norm-≤d elements of the
cyclotomic prime `𝔭`), (ii) the collapse theorem with explicit constants, (iii) the corrected map
of where the hardness actually lives (certificate uniformity / SDP size, not degree), and (iv) one
new well-posed finite invariant with probe data: the **ℓ¹-generation radius** `d_gen(𝔭)`.
**No closure of anything arithmetic is claimed. CORE unchanged: OPEN, ON-BGK.**

---

## 1. The proof system, fixed precisely

**Variables.** `z_j` (`j ∈ ℤ/n`), complex (formally `2n` real variables `x_j, y_j`); intended
solution `z_j = e_p(b·x_j)`, where `x_j = h^j`, `h = g^{(p−1)/n}` a generator of `μ_n`.

**Axioms (the semantic encoding `E_sem`).**
- circle: `z_j z̄_j − 1 = 0` for all `j`;
- relation binomials: `z^{a⁺} − z^{a⁻} = 0` for every `a ∈ L := ker(ℤ^n → 𝔽_p, a ↦ Σ_j a_j h^j)`
  (negative components via `z̄`; the binomial has degree `‖a‖₁`).

The solution set is exactly `V = {(e_p(b x_j))_j : b ∈ 𝔽_p}` (`p` points: the torus points killed
by all of `L` = the dual of `ℤ^n/L ≅ ℤ/p`). A **degree-d SoS proof** of `G ≥ 0` is an identity
`G = σ + Σ_i m_i·A_i` with `σ` a real sum of squares, `A_i` axioms, and every product of degree
≤ d. A **degree-d pseudo-expectation** is a linear functional on degree-≤d polynomials, `Ẽ[1]=1`,
`Ẽ[h²] ≥ 0` for `deg h ≤ d/2`, `Ẽ[m·A] = 0` for visible axiom multiples. Weak duality: a degree-d
certificate for `G` kills every degree-d `Ẽ` with `Ẽ[G] < 0`.

**Target polynomial (the b=0-safe dichotomy form).** With `τ := C²·n·log(p/n)`:
`G_τ(z) := (|η(z)|² − τ)·(|η(z)|² − n²)`, `η(z) = Σ_j z_j` (degree 4). On `V`: `G_τ ≥ 0` ⟺
every `b` has `|η_b|² ≤ τ` or `|η_b|² = n²` (the latter only at `b = 0`) — i.e. `G_τ ≥ 0` on `V`
IS the prize inequality at constant `C`. (Extracting the literal `max_{b≠0}` form needs only the
degree-2 SoS fact `n² − |η|² = Σ_{j<k}|z_j − z_k|²`·(1/n)-normalized, plus strictness at `b≠0`;
we certify the dichotomy polynomial — that is the prize content.)

## 2. The dictionary (new, exact)

Everything a degree-d proof can see is indexed by short vectors of the relation lattice:

1. **Monomial classes ↔ frequencies.** Modulo circle axioms, a degree-≤k monomial is a Laurent
   monomial `z^a`, `‖a‖₁ ≤ k`; on `V` it evaluates to `e_p(b·S(a))`, `S(a) := Σ_j a_j h^j mod p`.
   The degree-k frequency reach is `Σ_k := S(B₁(k))` = the k-fold **signed sumset of μ_n**
   (signed = plain, since `−1 ∈ μ_n`).
2. **Visible arithmetic = short vectors of `𝔭`.** The identifications forced at degree d are the
   binomials of relation vectors with `‖a‖₁ ≤ d`. Under `ℤ^n ↠ ℤ[x]/(x^n−1)` and the antipodal
   quotient `x^{n/2} = −1`, `L` maps onto the **degree-one prime `𝔭 = ker(ℤ[ζ_n] → 𝔽_p, ζ ↦ h)`**
   of the `2^μ`-th cyclotomic order — the SAME ideal-lattice as essay §2.3 (SST). Degree-d SoS
   knows exactly: the antipodal (Lam–Leung char-0) relations + the elements of `𝔭` of ℓ¹-norm ≤ d.
   Note it sees UNBALANCED relations too (odd-moment arithmetic), not just the energy ladder's
   balanced ones.
3. **The energy is the visible constant term.** Reducing `|η(z)|^{2r}` modulo the visible ideal at
   degree `2r + O(1)`: the coefficient of the trivial class is exactly the raw energy `E_r`
   (# of 2r-tuples summing to 0 mod p). The depth-r moment data is embedded in degree-2r SoS —
   the moment ladder is the dilation-symmetric sector of the SoS cone. (Consistent with the
   in-tree "SOS=moment wall" disproof-log entry and `_WallSOSPositivityPerK`.)

## 3. Theorem A (the collapse): degree-O(1) SoS is complete at fixed β

> **Theorem A.** Fix `β > 2` and let `n = 2^μ`, `p ≡ 1 (mod n)`, `p ≈ n^β`, `p` large. Let
> `k₀ = k₀(n,p) := min{k : Σ_k = 𝔽_p}`. Then EVERY polynomial `G` of degree `g` with `G ≥ 0` on
> `V` has an SoS certificate over `E_sem` of degree ≤ `4k₀ + 2g`. Moreover
> `k₀ ≤ 2 + ⌈(β−1)/ε_BGK(1/β)⌉ = O(1)` (independent of `n`), where `ε_BGK` is the
> Bourgain–Glibichuk–Konyagin exponent.

**Proof, step-numbered.**

- **(A1) Covering.** BGK: `max_{b≠0}|η_b| ≤ n^{1−ε}`, `ε = ε_BGK(1/β) > 0`, for `p ≥ p₀(β)`. The
  k-fold representation count is `r_k(x) = n^k/p + (1/p)Σ_{b≠0} η_b^k e_p(−bx)`, and
  `|tail| ≤ (1/p)·M^{k−2}·Σ_{b≠0}η_b² = M^{k−2}·n(p−n)/p < M^{k−2}n`. So `r_k(x) > 0` for all `x`
  once `n^{k−1} > p·n^{(1−ε)(k−2)}`, i.e. `k > 2 + (β−1)/ε`. Hence `Σ_{k₀} = 𝔽_p` at
  `k₀ = O(1)`. (Explicit ε available for β ≤ ~4.7 via Shkredov's iterated bound; at the literal
  prize diagonal β ≈ 5.27 the constant is O(1)-ineffective — inherited from BGK. Measured at real
  scales: `k₀ = 9` at generic β=4 primes, §6.)
- **(A2) Interpolation.** Pick per frequency `s ∈ 𝔽_p` a representative `a(s) ∈ B₁(k₀)` with
  `S(a(s)) = s` (exists by A1). Set `f(b) := √(G(b))` on `V` (well-defined: `G ≥ 0` on `V`), let
  `x_s` be its 𝔽_p-Fourier coefficients, and `F(z) := Σ_s x_s z^{a(s)}` (degree ≤ k₀). Then
  `|F|² = G` pointwise on `V`, and `|F|² = (Re F)² + (Im F)²` is a real SoS of degree `2k₀`.
- **(A3) Ideal membership at bounded degree.** `H := G − |F|²` vanishes on `V`. Reduce every
  monomial of `H` (degree ≤ max(g, 2k₀)) to the canonical representative of its frequency class:
  each rewriting uses circle axioms plus ONE relation binomial of norm ≤ `max(g,2k₀) + k₀ ≤ 3k₀+g`
  — a valid axiom — with monomial multipliers; all products of degree ≤ `4k₀ + 2g`. The reduced
  form is `Σ_{s} ĥ(s)·z^{a(s)}` over ≤ p distinct frequencies; it vanishes on `V`, and the
  characters `{b ↦ e_p(bs)}` for distinct `s` are linearly independent, so `ĥ ≡ 0`. Hence
  `H` lies in the visible ideal at degree `4k₀ + 2g`. ∎

With `g = 4` (our `G_τ`): **certificate degree `d₀ ≤ 4k₀ + 8`**. At β = 4 with the measured
`k₀ = 9`: `d₀ ≤ 44`. At the prize point (`n = 2^30`, `q ≈ 2^158`): `d₀ = O(1)`, versus the seed's
conjectured threshold `2 ln q ≈ 219`. **The seed conjecture is false; there is no SoS-degree
wall over this encoding.**

## 4. Corollaries — the seed's two deliverables, answered

- **A1 (seed (a): the lone-spike does NOT give an SoS lower bound; the extension question IS the
  prize).** For `D ≥ 4k₀ + 16`: *a valid degree-D pseudo-expectation with `Ẽ[G_τ] < 0` exists ⟺
  some `b ≠ 0` has `|η_b|² > τ`* (prize-false at τ). [⟸: point evaluation at the witness is a
  valid pseudo-expectation at ALL degrees. ⟹: prize-true ⟹ Theorem A certificate ⟹ weak
  duality.] So checking whether the lone-spike (or any spiked Wick functional) extends over the
  phase encoding is not a wedge — it is verbatim the open question. Pseudo-distribution /
  planted-moment technology is structurally unable to certify the wall here, because the
  encoding's algebra has no intermediate regime for it to live in (see §5). This is the
  phase-encoding echo of the round-2 CMK verdict ("positivity adds nothing"): there, positivity
  post-processing of moment data computes back to the moment bound; here, SoS-positivity of the
  full encoding computes back to the truth itself.
- **A2 (seed (b): yes — degree-O(1) identity certificates exist, but they are epistemically
  empty).** The certificate exists at degree `4k₀+8` whenever the prize is true — but its
  coefficients are the 𝔽_p-Fourier transform of `√(G(b))`, i.e. they ENCODE the full spectrum
  `{|η_b|²}` (`p ≈ 2^158` values). Existence is non-constructive relative to the very data at
  issue. The wall relocates from degree to **uniformity**: no poly(log p)-describable certificate
  family is known, and producing one would essentially BE a proof of the prize.
- **A3 (unconditional content).** With `τ_BGK = n^{2−2ε}`, `G_{τ_BGK} ≥ 0` on `V` is BGK's
  theorem, so **BGK admits a degree-O(1) SoS certificate over `E_sem`** — unconditionally, no
  valid degree-`(4k₀+16)` pseudo-expectation can pretend `|η| > n^{1−ε_BGK}`. Degree-O(1) SoS
  already knows BGK; a fortiori "moments + positivity to depth log q" is not the frontier of what
  low-degree SoS sees — the frontier is exactness (A1).

## 5. Theorem B (honest axiom sets) + the size picture: why the hierarchy has NO useful regime

The collapse might be suspected to be an artifact of the axiom scheme (all binomials). It is not,
but the honest accounting introduces the lane's one genuinely new invariant.

- **(B1) Zero arithmetic axioms (circle + antipodal only).** The relaxed variety is the antipodal
  sub-torus (`z_{j+n/2} = z̄_j`, real dimension n/2), on which `η = 2Σ_{j<n/2} cos θ_j` fills
  `[−n, n]`; `G_τ < 0` is realized; **no certificate at ANY degree** (the statement is false on
  the relaxation). This absorbs and strengthens the in-tree `_wf5A2_sos_blindness` verdict (their
  relation-free circle-Lasserre is this end of the spectrum).
- **(B2) Poly-size honest axiom set: circle + antipodal + relation binomials of norm ≤ D₀.** The
  relaxed variety is the character group of `ℤ^n/L_{D₀}`, `L_{D₀} :=` the lattice spanned by
  relation vectors of norm ≤ D₀ (shift-closure is free, so lattice span = ideal span). Define
  **`d_gen(n,p) := min{D : L_D = L}`** — the ℓ¹-generation radius of `L` (equivalently of `𝔭`
  over the antipodal part). For `D₀ ≥ d_gen` the relaxation is exact and Theorem A applies at
  degree `max(4k₀+8, ~3k₀+D₀)`; for `D₀` below the wraparound onset `d_onset` the relaxation
  contains the sub-torus and nothing is certifiable. So over honest encodings,
  `d*(n,p) ∈ (d_onset, max(4k₀+8, d_gen + O(k₀))]` — and the probe data (§6) puts both ends at
  O(1). The axiom count at `D₀ = d_gen` is `O(n^{d_gen−β+1})`-ish — poly(n).
- **(B3) The size collapse (the sharpest single formulation of the finding).** The number of
  monomial classes saturates at `|Σ_k| = p` already at `k = k₀ = O(1)`. So the SoS hierarchy on
  this object has exactly two regimes: **below `d_onset` it is vacuous (spurious continuum);
  from `O(k₀)` on it is EXACT — and its moment matrix is `p×p`.** There is no intermediate
  regime: the degree-vs-size tradeoff degenerates because thinness makes `μ_n` an O(1)-fold
  additive basis. The SDP that "solves" the prize has size `p^{O(1)} ≈ 2^{158·O(1)}` — brute
  force in disguise. THIS is why no SoS/Lasserre literature ever touched the problem: there is
  no polynomial-size rung on the ladder at all. In this frame the moment ladder (`r ≤ ln q`) is
  the dilation-SYMMETRIC, uniform-coefficient slice of the exact-but-huge cone — and the in-tree
  Meta-Theorem (`MetaTheoremSecondOrderCap`) + symmetrization trap say precisely that the
  tractable slices stall at Johnson/√p. Tractable ⟹ Johnson; exact ⟹ infeasible. The wall is
  the gap between, measured in UNIFORMITY, not degree.

## 6. Probe results (constants at real scales; exact integer computation)

`probe_466_novel_sos_collapse.py`, n ∈ {8,16}, three β≈4 primes each, relation scan to ℓ¹-norm 8
(meet-in-the-middle over the full integer ℓ¹-ball; lattice index via exact integer HNF):

| n | p | β | k₀ (covering) | d_onset (first wraparound) | d_gen |
|---|---|---|---|---|---|
| 8 | 4129/4153/4177 | 4.00 | 12 / 12 / 12 | >8 | >8 |
| 16 | **65537** (Fermat) | 4.00 | **12** | **5** | **5** |
| 16 | 65617 | 4.00 | **9** | >8 | >8 |
| 16 | 65633 | 4.00 | **9** | >8 | >8 |

Readings: (i) `k₀` is flat-to-decreasing in n at fixed β (12 → 9), consistent with `k₀(β) = O(1)`;
the counting floor is `k₀ ≥ β = 4`. (ii) The resonant Fermat prime **covers slower (k₀ = 12) but
generates earlier (d_gen = 5)** — its norm-5 relations are exactly the generalized-Fermat
`η₁ = n − c_B` resonance of round-2 lane F; at the one instance where wraparounds are in scan
range, `d_gen = d_onset` (the first wraparounds already generate: rank jumps 8→16 and the index
lands at exactly `p` in one step). (iii) Generic primes at β=4 have `d_onset > 8`, consistent with
the dossier's balanced onset `r₀ = 5` (norm 10); counting heuristics put `d_gen ≈ 10–12` there,
and ≈ 6–7 at the prize point (β ≈ 5.27, where `n^d/d! ≈ p` at d ≈ 5.5). **Unproven for generic
primes; O(1)-plausible; this is the one open constant in the chain** (a follow-up can push the
scan to norm 10 with the same meet-in-middle at ~2M half-vectors).

## 7. The corrected redirect map (what remains logically possible)

The seed asked: enumerate which techniques are NOT SoS-representable and hence not ruled out.
The collapse inverts the question — every true inequality is representable at O(1) degree, so
**SoS-representability is a vacuous filter**; nothing whatsoever is ruled out by SoS-degree, and
the operative filters remain the dossier's C1–C6. What the collapse adds is a sharp statement of
the real obstruction and two well-posed new questions:

1. **The uniformity question (the honest reformulation of "the wall" in proof-complexity terms).**
   Does there exist a certificate family for `G_τ` (τ at the prize constant) whose coefficient
   vectors are describable in poly(log p) bits (equivalently computable in poly(log p) time from
   `(n, p, g)`)? A YES is essentially a proof of the prize; a NO would be a genuine barrier
   theorem — but note pseudo-expectations cannot prove the NO (they are blind to coefficient
   complexity), so this is Razborov-natural-proofs territory: new machinery would be needed.
   Height/pigeonhole lower bounds on rational certificate coefficients (`h*(n,p)`) are the one
   concrete formulation; nothing is known.
2. **The generation-radius invariant `d_gen(𝔭)`** — new, finite, probe-able, and connected to the
   in-tree floor/width-four machinery (the floor scanners already enumerate short-𝔭 patterns).
   Its uniform-in-(n,p) behavior is a clean lattice question about dyadic cyclotomic degree-one
   primes: *is the shortest-generation radius O(β) uniformly?* Also note the measured
   resonance duality (k₀ up ⟺ d_gen down at the Fermat prime) — a deployment-screening angle.
3. **Tower-recursive certificate composition** — the only technique class the collapse leaves
   with a distinguished status: the ledger kills √2-descent of the VALUES `M(μ_n)` (per-level
   growth 1.74/1.54/1.46 > √2), but recursion at the level of CERTIFICATES (derive a degree-D
   certificate for level n from level n/2 plus O(1) new axioms — `μ_{n/2}`'s relation lattice
   embeds in `μ_n`'s on the even coordinates) is untouched by any registered kill. No mechanism
   is proposed here (honesty: this is a shape, not a method); its value is that certificate
   recursion would AUTOMATICALLY be uniform, i.e. it attacks exactly the relocated wall.
4. Galois/integrality averaging is dead on arrival (Galois of ℚ(ζ_p) acts as `b ↦ ub` — full
   dilation orbit — the in-tree symmetrization trap applies verbatim); entropy-compression on
   coefficients has no known mechanism.

## 8. Honest self-assessment (where this dies, and what it does NOT claim)

- **The collapse theorem is asymptotic at fixed β.** Step (A1) uses BGK with its ineffective
  `p₀(δ)`/`ε(δ)` at the literal prize point (same status as every BGK citation in the campaign).
  At β ≤ ~4.7 the constants can be made explicit (Shkredov Cor. 16 route), but the literal prize
  diagonal β ≈ 5.27 keeps an O(1)-ineffective `k₀`. The probe's `k₀ = 9–12` is evidence the real
  constants are small.
- **The bookkeeping constant `4k₀ + 2g` is hand-counted** (monomial-by-monomial reduction), not
  machine-checked; an off-by-constant would not change any conclusion (everything is O(k₀)).
- **`d_gen = O(1)` at generic primes is measured-bounded (>8) but UNPROVEN** — the honest-axiom
  version of the collapse (B2) is conditional on it; the semantic version (Theorem A) is not.
- **Nothing here touches the arithmetic core.** The collapse does not produce a usable
  certificate (A2: coefficients require the spectrum), does not improve any bound on `M`, and
  does not decide the prize. Its value is purely structural: it PROVES the seed lane's hoped-for
  product (an SoS-degree lower bound explaining the 250+ failures) cannot exist over the natural
  encoding, closes the "SoS hierarchy" door with a theorem-shaped reason (no polynomial-size
  rung), and hands the search two sharper questions (uniformity; `d_gen`) plus one distinguished
  surviving shape (certificate recursion up the dyadic tower).
- **Kill-landscape audit:** uses BGK (proven; allowed), sumset covering (door-ii machinery used
  BELOW its saturation — legitimate), weak SDP duality (standard). Consistent with: the lone-spike
  filter (A1 is its phase-encoding form), γ₂-degeneration (chaining = union bound = the symmetric
  slice), `_wf5A2_sos_blindness` (the zero-axiom end of B1), `_WallSOSPositivityPerK` (spectral
  encoding constrained-cone = the symmetric slice's crossover), and the Meta-Theorem (tractable
  slices ≤ Johnson). No registered kill is re-tripped; no "moments + positivity" ending is used.

**Cross-refs.** Dossier v3 §2.4/§4/§8; `docs/kb/deltastar-466-cmk-refuted-2026-07-01.md`;
`Frontier/_wf5A2_sos_blindness.lean`; `Frontier/_WallSOSPositivityPerK.lean`;
`Frontier/_A1SOSLadderN16.lean`; `MetaTheoremSecondOrderCap.lean`; essay §2.1–§2.3.
**External:** Bourgain–Glibichuk–Konyagin (J. London Math. Soc. 2006); Glibichuk 2006 /
Glibichuk–Konyagin 2007 (subgroup sumset covering, explicit folds for |H| > p^{1/4}); Lam–Leung
2000 (vanishing sums of 2-power roots of unity); Lasserre/Parrilo (moment-SoS duality);
Grigoriev 2001 (knapsack SoS lower bounds — the genre whose analogue is proven impossible here).

<sub>2026-07-01, lane N5 proposer (Claude Fable 5). Self-refutation of the assigned conjecture
with a structural theorem in its place; no arithmetic closure claimed; core OPEN, ON-BGK.</sub>
