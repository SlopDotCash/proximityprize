<!-- #444 / Paley. Authored 2026-06-21 via the monodromy-essay-25tools workflow. Essay on the
growing-rank big-monodromy / phase-equidistribution-with-cancellation 'missing input', the landscape +
why it is unavailable, and 25 NEW invented tools ranked by feasibility x non-reduction. HONEST: no tool
proven; reframing (independently computed) — the period family is iid-Gaussian (moments below Wick,
approaching it), MORE independent than any classical-group monodromy, so the right object is the
sub-Gaussian extreme-value bound, NOT big monodromy. Worth-building set: LDGT (sub-Gaussian rate),
wild p-adic-Hodge twist, Tannakian non-torsion rank-pump, Markoff coupling. -->

# Growing-Rank Big Monodromy and Phase-Equidistribution-with-Cancellation: the Missing Input for the Paley Conjecture

## Abstract and standing of claims

This essay is an honest map, not a solution. It articulates the single missing mathematical input behind the Paley/BGK proximity-gap conjecture at β = 4, locates that input precisely inside the Deligne–Katz equidistribution framework, surveys what the four standard machines (Katz monodromy, Sawin/Fouvry–Kowalski–Michel sup-norm theory, Bourgain–Gamburd–Sarnak expansion, automorphic lifts) actually deliver and where each one provably stops, and then presents twenty-five candidate new objects together with an unsentimental feasibility/non-reduction ranking. Throughout, **proven** statements are marked as such; **conjectural** or **literature-confidence** statements are flagged; and no claim of absolute novelty is made — that would be uncertifiable. The deliverable is the sharpest formulation I can give of the theorem that does not yet exist, plus the small set of probes that have a genuine (not cosmetic) mechanism to evade the known reductions.

---

## 1. Why big monodromy is the needed input

### 1.1 The object

Fix a prime power regime p ≡ 1 (mod n) with n = 2^μ, and let μ_n ⊂ 𝔽_p^× be the unique cyclic subgroup of order n. Write e_p(t) = exp(2πi t/p) for the standard additive character. The **Gauss period** attached to b ∈ 𝔽_p^× is

  η_b = Σ_{x ∈ μ_n} e_p(b x).

The proximity-gap prize floor at the Paley scale reduces — after the full campaign of fourteen workflows recorded in the project memory — to a single analytic statement about the **sup-norm**:

  M(n) := max_{b ≠ 0} |η_b| ≤ C·√(n · log(p/n)),  at β = 4, i.e. p ≈ n^4,

for an absolute constant C. Two elementary facts frame the entire difficulty.

- **The trivial / triangle bound:** |η_b| ≤ n, since there are n terms each of modulus 1. This is also the value of the rank of any single ℓ-adic incarnation: it is "no cancellation."
- **The Plancherel / energy identity (proven):** Σ_{b ∈ 𝔽_p} |η_b|² = p·n. Hence the **root-mean-square** of |η_b| over b is already √n. The average is at the target size; the entire content of the prize is in the **maximum**, i.e. forcing *every* nonzero b below √(n log(p/n)) rather than merely the typical one.

The best unconditional bound is the Bourgain–Garaev–Konyagin / Burgess-type estimate M(n) ≤ n^{1−o(1)}, and the Burgess exponent on a multiplicative-subgroup sum of length L = p^{1/β} is nontrivial only for β < 4 and **vanishes exactly at β = 4**. The remaining gap n^{1−o(1)} → n^{1/2} is a **full half-power**, and — this is the diagnostic theorem of the campaign — it is *pure archimedean phase cancellation*: it cannot be supplied by any bound on the magnitudes |e_p(bx)| = 1, nor by any L² / energy quantity, because every such quantity is floored at exponent 1 by the Plancherel identity above. Concretely, the moment route gives M ≤ (Σ_b |η_b|^{2k})^{1/2k} and the energy floor Σ_b |η_b|^{2k} ≥ p·E_k ≥ n^{2k}/p · p = n^{2k} forces exponent ≥ 1 for every depth k. The in-tree lemma `moment_ladder_exceeds_prize` records this necessity axiom-clean: **no moment method of any depth reaches the target.** The half-power lives in the *phases* of the η_b, and only a mechanism that constrains phases can produce it.

### 1.2 The one machine that produces phase cancellation

There is exactly one general theorem in mathematics that converts geometric structure into square-root cancellation of the **phases** of a complete or incomplete exponential sum: **Deligne's Weil II together with the Katz–Sarnak equidistribution package**, applied to a sheaf with **big geometric monodromy**.

The precise statement we would want is this. Suppose η_b can be written as a trace of Frobenius,

  η_b = Tr(Frob_b | ℱ),  b ∈ U(𝔽_p),

for a middle-extension ℓ-adic sheaf ℱ on an open U ⊂ 𝔸^1/𝔽_p, lisse of rank r on U, **pure of weight 0** after normalization. Deligne's Riemann Hypothesis over finite fields (Weil II, Publ. IHÉS 52, 1980) then gives, for the *completed* sum and for individual traces,

  |Tr(Frob_b | ℱ)| ≤ r,

with equality only in degenerate cases — the rank bound. The cancellation appears when one asks how the normalized traces Tr(Frob_b | ℱ)/√(weight) **distribute** as b ranges over U. The Katz–Sarnak theorem (*Random Matrices, Frobenius Eigenvalues, and Monodromy*, AMS Colloq. 45, 1999) says: if the **geometric monodromy group** G_geom — the Zariski closure of the image of π_1^geom(U) acting on the generic stalk — is a **big classical group** (SL_r, Sp_r, SO_r, SU_r), then the conjugacy classes Frob_b equidistribute, as p → ∞, with respect to Haar measure on the maximal compact of G_geom. For a big classical group of rank → ∞, the Haar-typical trace is O(√r) (a sum of r nearly-independent unit eigenvalues with the cancellation of a random unitary), and the **extreme value** over the |U| ≈ p points is O(√(r · log p)) by the Gumbel tail of p near-independent samples.

That is *exactly* the shape of the prize: with r = n and the log(p/n) range factor, one obtains

  M(n) = max_{b ≠ 0} |η_b| ≤ C·√(n · log(p/n)).

**So the missing input is fully identified and is not vague.** It is: *a geometrically-irreducible, growing-rank (r = r(n) → ∞), pure ℓ-adic local system on the b-line whose Frobenius trace is (a faithful majorant of) η_b and whose geometric monodromy group is a classical group of rank → ∞.* If such an object existed, Deligne + Katz–Sarnak would close the prize. The whole essay is about why the *natural* such object is abelian of rank 1 — giving only |η_b| ≤ n — and why every classical functor that grows the rank collapses back to that abelian object on the thin 2^μ-torsion locus.

The boundary is sharp and worth stating once: **the magnitude side is fully understood** (each Gauss-sum eigenvalue has modulus exactly √p; Weil gives it; Gross–Koblitz/Stickelberger even write the phases explicitly, reproducing η_b to 1e-15 as a relabeling), and **the phase side is entirely open** (the arg of a Gauss/Jacobi sum is itself a √p object with no bilinear linearization, so the explicit formulae are *phase-blind in their provable part* — they pin the p-adic valuation, i.e. the magnitude, and say nothing that forces cancellation in the sum of n unit-modulus-√p phases).

---

## 2. The landscape: four machines and their precise limits

Four bodies of theory could conceivably supply the input. Each is real, powerful, and stops at a precise, identifiable wall.

### 2.1 Katz monodromy theory (the source of the criteria)

The canonical references — Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups* (Ann. Math. Studies 116, 1988; "GKM"); *Exponential Sums and Differential Equations* (AMS 124, 1990; "ESDE"); *Rigid Local Systems* (AMS 139, 1996; "RLS"); *Convolution and Equidistribution* (2012) — give an effective algorithm for certifying that G_geom is a full classical group. In condensed form, a lisse pure sheaf ℱ has big G_geom provided:

- **(C1) geometric irreducibility** — otherwise G_geom is block-diagonal and never a full classical group;
- **(C2) not Kummer/Belyi-induced** — ℱ is not [m]_* of a multiplicative-character family, equivalently not imprimitive; the diagnostic is the **Larsen fourth moment** M_4(G_geom) = lim (1/|U|) Σ_b |Tr Frob_b|^4, which equals 2 (resp. 1 for self-dual) exactly when G_geom contains a classical group, and is *large* when the representation is induced or tensor-decomposable;
- **(C3) not small rank / no exceptional collapse** — rule out the finite Larsen list of small images (finite groups, tori, the G_2 exception for Kloosterman);
- **(C4) the autoduality dichotomy** — if ℱ ≅ ℱ^∨ the pairing is orthogonal (G_geom ⊆ O) or symplectic (G_geom ⊆ Sp), read off from local monodromy at the wild/tame singularities (GKM 4.1.6); if not self-dual the target is SL or SU.

**What it gives:** when (C1)–(C4) hold with r → ∞, exactly the √-cancellation of §1.2.

**Its precise limitation for us:** Katz's own classification *certifies the failure*. The μ_n Gauss-period sheaf is the textbook member of the **Kummer-induced (small-monodromy) class** — the complement of the big class his theorems characterize. It is built from the Artin–Schreier sheaf ℒ_ψ and the order-n power map, and it splits as a direct sum of n rank-1 Kummer eigensheaves (§3.1). Katz tells us, rigorously, that this object is in the wrong bin.

### 2.2 Sawin / Fouvry–Kowalski–Michel sup-norm and bilinear theory

The "trace functions" program (Fouvry–Kowalski–Michel, *Algebraic twists of modular forms and Hecke orbits*, GAFA 2015; *Algebraic trace functions over the primes*, Duke 2014; Kowalski–Michel–Sawin, *Bilinear forms with Kloosterman sums*; and the very recent **Fouvry–Kowalski–Michel–Sawin, *Bilinear forms with trace functions*, arXiv:2511.09459, Nov 2025**), built on **Forey–Fresán–Kowalski–Sawin, *Quantitative sheaf theory* (JAMS, arXiv:2101.00635)**, gives two shapes of bound for sums of trace functions t_ℱ(x):

- **(a) Completed sums:** for ℱ geometrically irreducible, not geometrically trivial and **not Kummer/Artin–Schreier**, RH gives |Σ_{x} t_ℱ(x)| ≤ (c(ℱ) − 1)√p, where c(ℱ) is the conductor. This is the Polya–Vinogradov range (length p).
- **(b) Bilinear / sub-PV sums:** |Σ_m Σ_n α_m β_n t_ℱ(m^b n^c)| ≪ ‖α‖_2 ‖β‖_2 (MN)^{1/2−η} in the range MN ≫ q^{3/4+δ}, with each variable ≫ q^δ. The recent paper isolates the sufficient monodromy hypothesis (one full-text pass surfaced the term **"gallant"**; both passes agreed on the load-bearing content): G_geom acts **irreducibly** on E^r and is **simple** (or finite containing a quasisimple normal subgroup acting irreducibly), the sheaf being light/pure. By Schur this *explicitly excludes* rank-1, torus, and Kummer monodromy.

Sawin's quantitative-sheaf layer makes every constant and the saving η polynomial in the conductor and uniform in p; it is the *enabling engine*, not a new source of cancellation.

**Three precise walls for μ_n** (each independently fatal):
- **(W1) Kummer wall:** the μ_n sheaf is Kummer (abelian rank-1) — the *excluded* class in both (a) and (b). The "bound" these theorems give it is the trivial |η_b| ≤ n.
- **(W2) One-variable wall:** the bilinear savings are structurally two-variable; η_b is a single sum with one parameter b. Factorizing μ_n = μ_{n/2}·{±1} or x = uv inside the subgroup produces a sum *internal to μ_n* whose two ranges are not free — it collapses to the same one-parameter object (the in-tree "imprimitive subgroup-structured → prize-inert" finding).
- **(W3) Length wall:** our sum has length n ≈ p^{1/4} = q^{1/4}, below the PV line q^{1/2} (so (a) is vacuous) and below the q^{3/4} bilinear threshold (so (b) does not even start). β = 4 is precisely the Burgess barrier.

Sawin's separate **geometric sup-norm method** (*A geometric approach to the sup-norm problem for automorphic forms*, arXiv:1907.08098) reduces a sup-norm to polar multiplicities of a characteristic cycle — but for a rank-1 Kummer object the characteristic cycle is that of a rank-1 sheaf and the bound returns the rank. Same wall, cohomological side.

### 2.3 Bourgain–Gamburd–Sarnak expansion

The prize quantity is *literally* a Cayley-graph second eigenvalue: form Cay(𝔽_p, μ_n) on the **additive** group; its adjacency eigenvalues are λ_b = Σ_{x∈μ_n} e_p(bx) = η_b, the trivial one is n, and M = max_{b≠0}|λ_b| is the "expansion." So a spectral gap for this graph *is* the prize, and BGS is the natural expansion machine to try.

BGS (Bourgain–Gamburd, Annals 2008; Bourgain–Gamburd–Sarnak, Invent. 2010, Acta 2011) prove uniform spectral gaps for congruence quotients of a fixed **thin non-abelian Zariski-dense** group, via three pillars: girth/non-concentration (needs a free non-abelian generating *set*), Bourgain–Gamburd ℓ²-flattening (a **non-commutative sum-product / product theorem**, Helfgott/Bourgain–Katz–Tao), and quasirandomness (the target group has **high-dimensional irreps**).

**Why every pillar is vacuous for μ_n** (the combinatorial mirror of §2.1):
- the graph is a Cayley graph of the **abelian** group (𝔽_p, +); its eigenvectors are forced to be the additive characters and its eigenvalues are the character sums themselves — no flattening room. Bounded-degree abelian Cayley graphs are never expanders;
- the connection set μ_n **is a subgroup**: μ_n·μ_n = μ_n, growth exponent 0, the product theorem hypothesis maximally violated; no girth, no escape-from-subgroups;
- all irreps of (𝔽_p, +) are 1-dimensional: no quasirandom amplification.

**And the decisive structural limitation:** even granting a gap, BGS delivers λ_b ≤ (1 − c)·n — a **constant-fraction** bound, of order n. The prize needs order √n. BGS is a *gap* theorem (multiplicative constant), never a *square-root-cancellation* theorem; the latter is an arithmetic/algebraic-geometric phenomenon (Frobenius eigenvalue = √weight), not a combinatorial one. The exponent on n stays at 1 — exactly the recorded n^{1−o(1)} stall. The in-tree witnesses are `_AttackR2_AbelianCayleyNonRamanujan.lean` and `NotRamanujanLowerBound.lean`. Worse, "use expansion to bound the eigenvalue" is *circular* here: the eigenvalue is η_b, the very quantity we started with.

### 2.4 Automorphic lifts and vertical Sato–Tate

Could η_b be a Whittaker/Fourier coefficient of an automorphic object whose Ramanujan bound supplies the half-power? Two sub-routes, both failing for structurally different reasons.

**(A) The lift is GL_1 / Eisenstein.** A Gauss sum is the GL_1 root number — the local ε-factor / Whittaker datum of a Hecke character of 𝔽_p, *not* a GL_{m≥2} cuspidal coefficient. Ramanujan/Deligne saving is (rank)·√(weight); for a GL_1 object the rank is 1 and "Ramanujan" *is* the trivial bound. The honest metaplectic realization — the Weil index of the oscillator representation of Mp(2) is the normalized Gauss sum — is genuine but lands in the **continuous/residual (Eisenstein) spectrum**, where no Ramanujan bound holds or is expected. There is no cuspidal big-rank lift of a μ_n Gauss period in the literature (confident statement, not a theorem; unverifiable as absolute).

**(B) Vertical Sato–Tate controls the distribution, never the sup.** Untrau (*Equidistribution of exponential sums indexed by a subgroup of fixed cardinality*, Math. Proc. Camb. Phil. Soc. 2024) and Kowalski–Untrau (*Refinements on vertical Sato–Tate*, arXiv:2310.08791) prove **exactly the Gauss-period family**: for fixed n, as q → ∞ over q ≡ 1 (mod n), the normalized η_b equidistribute to the pushforward of Haar measure on a torus by a Laurent polynomial — for prime order, the interior of an n-cusp hypocycloid. This is a beautiful theorem and it is *the wrong statement*: it controls the **empirical measure** of {η_b}_b (bulk, average, moments), not the **single extreme value**; and it is asymptotic in q → ∞ with n fixed, whereas the prize is **fixed p ≈ n^4, n → ∞**. The two limits do not commute, and the theorem is silent at a fixed prime. Every refinement (higher moments, Sawin rates, FKM large-sieve) bounds Σ_b |η_b|^{2k} — averages — and the energy floor forces exponent ≥ 1. *Distribution does not imply sup;* this is the analytic incarnation of the phase-blind wall. In-tree: `_JacobiKatzEquidist.lean`, `_wfHK2_katz_sarnak_extreme_value.lean`.

---

## 3. Why the input is unavailable for μ_n at β = 4: four obstructions

The four machines fail for one underlying reason, seen from four angles: **the defining symmetry of μ_n — closure under the dyadic rotation x ↦ ζx, with −1 = ζ^{n/2} ∈ μ_n — forces the natural geometric object to be abelian and forces every growing-rank invariant to vanish on the 2^μ-torsion locus.** Each obstruction below is made precise and each is witnessed axiom-clean in-tree.

### 3.1 (a) The abelian / Kummer obstruction — the natural object is rank 1

Because [n]: u ↦ u^n is a tame étale ℤ/n-Galois cover of 𝔾_m (n prime to p), the pushforward of the Artin–Schreier sheaf splits into the n Kummer eigensheaves (Katz, GKM 4.1 / ESDE 8.3, the multiplicative Fourier/Mellin decomposition):

  ℱ_n = [n]_* ℒ_ψ ≅ ⊕_{χ : χ^n = 𝟙} (ℒ_χ ⊗ "Gauss-sum line"),  Tr(Frob_b) = η_b = Σ_{χ^n=𝟙} G(χ)·χ̄(b).

Each summand ℒ_χ is **rank 1**, with geometric monodromy the image of tame inertia — a **finite cyclic group**. Therefore (C1) fails (ℱ_n is geometrically reducible, n rank-1 pieces), G_geom° is a **torus** (G_geom ⊆ (𝔾_m)^n ⋊ ℤ/n), the Larsen fourth moment is M_4 = n (maximally induced, the polar opposite of the M_4 = 2 that signals a classical group), and (C2) fails *by construction* — ℱ_n is literally [n]_* of a rank-1 sheaf, the defining example of a Kummer-induced sheaf. The eigenvalues of every Frobenius are the n Gauss sums G(χ), each of modulus exactly √p; abelian monodromy constrains *nothing* about their sum beyond Plancherel. This is the phase-blind wall expressed monodromy-theoretically, and it is the same abelianness that kills BGS (§2.3). In-tree: `_NovelEllAdicSheaf.lean`, `_FrontierSheafConductor.lean`, `_FrontierSwanConductor.lean` (the explicit ℱ_n = [n]_*ℒ_ψ, its Gauss-sum decomposition, and its small Artin conductor ~ O(n)); `_AttackR2_AbelianCayleyNonRamanujan.lean`.

### 3.2 (b) The cyclotomic-vanishing obstruction — growing-rank invariants vanish at 2^μ-th roots

The standard way to *grow* the rank is Sym^k, ⊗^k, and **middle convolution** MC_χ (Katz, RLS Ch. 5–6 — the only operation that creates irreducibility from rank-1 inputs, the engine of all rigid hypergeometrics with big monodromy). Each collapses on μ_n:

- **Sym^k / ⊗^k of a sum of characters is again a sum of characters:** Sym^k ℱ_n = ⊕ ℒ_{χ_1⋯χ_k}, each summand still rank-1 Kummer. G_geom stays a torus; the new traces are complete sums of *products* of Gauss sums, i.e. additive relations among 2^μ-th roots of unity, governed by **Lam–Leung** (*Vanishing sums of roots of unity*, J. Algebra 224, 2000): for n = 2^μ every vanishing relation is an ℕ-combination of the single antipodal relation Σ_{ζ²=1} ζ = 0. No irreducible nonabelian constituent is ever produced.
- **Middle convolution** needs the local exponents in *generic / non-resonant* position to manufacture an irreducible big-monodromy hypergeometric. The μ_n input ℒ_χ has all local exponents in (1/n)ℤ/ℤ — **n-torsion, maximally resonant (Kummer)**. The would-be irreducible hypergeometric **degenerates and splits back into Kummer pieces**: the relevant H^1_c drops in dimension exactly because the Euler–Poincaré / Ogg–Shafarevich count's "drop" terms are vanishing sums of n-th roots of unity, forced antipodal-only by Lam–Leung. MC at cyclotomic exponents lands in the finite-Larsen / induced part of the classification, never SL/Sp/SO.

This is the deepest wall: the *very* symmetry one hopes forces equidistribution instead forces the higher invariants to be **identically zero**, so there is no growing-rank trace to equidistribute. Witnesses (all axiom-clean): `_AvX_VanishingTwoPowSumIsAntipodalP.lean` (the 2^μ-sum vanishing *is* the antipodal relation), `_E6OddGradeVanish.lean`, `_Close07c_OddGradeVanishesFull.lean` (odd-grade Schur components vanish), `_DoorIVConnectedCumulantVanishes.lean`, `_DoorIVSixthCumulantVanishes.lean` (the connected higher cumulants — precisely the quantities that would carry growing-rank monodromy information — vanish), `AntipodalVanishingCountLower.lean`, `OverdetVanishingCosetCount.lean`.

### 3.3 (c) The thin-2^μ-torsion obstruction — the 2-power structure forces small monodromy

μ_n is 2-power torsion, with two consequences. First, **antipodal collapse:** −1 = ζ^{n/2} ∈ μ_n, so η_b = Σ_x e_p(bx) pairs x with −x and is a *real* sum of n/2 cosines 2cos(2πbx/p). The antipodal symmetry removes the imaginary part — the natural carrier of cancellation — and reduces the problem to a real cosine sum on a flat (zero-curvature) set. This is why the char-0 model is √2-bounded (Bessel) while the char-p sup is not: the carrier is gone. Witnesses: `_Bridge05_AntipodalOddVanishing.lean`, `EnergyRelationAntipodal.lean`, `AntipodalBalanceBounded.lean`. Second, **non-Zariski-density:** the cyclic 2-power μ_n generates an abelian, *not Zariski-dense* subgroup of any classical group, so the BGS super-strong-approximation machine (which needs Zariski density) does not engage — the Cayley/Paley graph is not Ramanujan (`NotRamanujanLowerBound.lean`). The set is *thin as a subset of 𝔽_p* but *abelian as a group* — thin in the wrong direction. The arithmetic of the bad primes ({2,3}-torsion) is moreover not the topological torsion of any would-be sheaf (the campaign's "T4" refutation), so the smallness is **arithmetic**, not curable by a topological input.

### 3.4 (d) The single-sum-versus-family obstruction — equidistribution needs a family

Deligne equidistribution is a statement about a **family** {η_b}_{b∈U} as Frob_b varies; it controls the *distribution* (average, moments) and the sup only through rank·√weight + conductor. Two failures: (i) the b-family is exactly the FKM algebraic-twist setup, but the twisting sheaf is abelian (§3.1–3.2), so FKM/Sawin yield only the trivial bound (`_wfA07_fkm_sheaf_conductor.lean`, `_JacobiKatzEquidist.lean`); (ii) even a *correct* big-monodromy family yields equidistribution of normalized traces — moments, Katz–Sarnak statistics (`_wfHK2_katz_sarnak_extreme_value.lean`) — whereas the **extreme value at fixed p** is a tail quantity the family machine averages over. The in-tree `moment_ladder_exceeds_prize` is the formal statement that this is a genuine barrier, not a presentation choice.

### 3.5 The wishlist (the four non-negotiables)

A tool that closes the gap must defeat (a)–(d) **simultaneously**:

| # | Requirement | Must beat |
|---|---|---|
| W1 | Growing rank r(n) → ∞ with η_b = Tr(Frob_b\|ℱ_n) (or an honest majorant), so r·√weight = √(n log) is *available* | (a) abelian rank-1 |
| W2 | Geometrically irreducible, **not Kummer-induced**, with growing-rank invariants **nonzero at the 2^μ-th roots** | (b) cyclotomic vanishing |
| W3 | Big classical G_geom (Zariski-dense), manufactured *despite* a 2-power-torsion abelian input | (c) thin 2^μ-torsion |
| W4 | A bound on the **single worst b at fixed p ≈ n^4** (sup, à la Sawin/FKM), not merely the b-average | (d) single-sum-no-family |

**The exact limitation, in one sentence.** The only mechanism that delivers √-phase-cancellation in the sup — Deligne equidistribution with growing-rank big monodromy — requires a geometrically-irreducible, non-Kummer, growing-rank, Zariski-dense local system whose invariants survive at the n-th roots of unity; but μ_n's defining closure under the dyadic rotation forces the natural object to be (a) Kummer/abelian/rank-1, (b) cyclotomically vanishing in every growing-rank invariant, (c) real and non-Zariski-dense, and (d) a single sum the family machine can only average — so the input is not missing by oversight but **structurally excluded by the dyadic symmetry itself.** That is why no paper in twenty-five years crosses n^{0.989} → n^{1/2}.

**Honest caveat.** This is the *standard-literature* obstruction (Katz GKM/RLS/ESDE, Deligne Weil II, Katz–Sarnak; FKM/Sawin; BGS; Lam–Leung), and it certifies that the **natural** input is abelian and the **standard** rank-growing functors reduce via cyclotomic vanishing. It does **not** prove no exotic non-functorial construction exists — that would be a meta-theorem. It pins precisely *where* a genuine new object must live: off the antipodal/odd grades, or coupled to an external Zariski-dense source, with its rank surviving restriction to the cyclotomic locus.

---

## 4. The twenty-five new tools

Each candidate is a *new object* with a *specific* evasion mechanism. I group by lens, then score each on **feasibility** (definable precisely + testable at small n, 0–10) and **non-reduction likelihood** (a specific mechanism to evade abelian/phase-blind/cyclotomic-vanishing, vs. likely reduces, 0–10), with an **honesty downgrade** applied whenever the stated mechanism collapses into one of the five already-closed escapes (abelian/Kummer; cyclotomic-vanishing; phase-blind L²/energy; magnitude/valuation; single-sum-no-family).

### Lens I — Wild / non-torsion ramification (escape (b) and (c) at ∞)

The unifying bet: introduce p-power-order (wild, Artin–Schreier–Witt) or non-torsion data, which lives *wild at ∞* where the dyadic torsion has no jurisdiction and Lam–Leung does not apply.

- **#1 Wild p-adic Hodge twist (Lubin–Tate / Swan-break).** Twist η_b by a length-μ Artin–Schreier–Witt character χ_ASW of p-power order; the Witt phase is orthogonal to Σζ=0 and breaks the resonance. **feas 5, nonRed 5 → adjusted 20.** The deformed period is a *different* object — the load-bearing risk is whether it majorizes the real η_b, and wild twists can still be self-dual into a small group.
- **#5 Tannakian rank-pump via non-torsion twist.** Middle-convolve with a Kummer character of large order d coprime to n (d ~ p^{1/2}, a finite proxy for non-resonance), breaking the (1/n)ℤ resonance that forces MC to degenerate; Larsen M_4 → 2 is the computable monodromy proxy. **feas 4, nonRed 4 → 16.** Non-torsion exponents are provably outside Lam–Leung's domain; risk is the lossy projection back to the trivial summand.
- **#9 Non-self-dual ASW–Witt convolution.** Asymmetric wild ramification (ψ_2 ≠ ψ̄_2 forces SL_N, not O/Sp), with a single clean Euler–Poincaré "no-rank-drop" test. **feas 2, nonRed 5 → 12.**
- **#22 Anti-Kummer fiber functor.** A different fiber functor at the wild point ∞ can yield a larger Tannakian group than the tame stalk; Lam–Leung has no jurisdiction at Swan-1. **feas 2, nonRed 4 → 10.** Mostly conceptual.
- **#2 Drinfeld-shtuka growing Newton-slope.** A cuspidal GL_μ Lafforgue lift *is* Ramanujan, escaping the GL_1 metaplectic theta — but Newton slopes are p-adic (valuation-class) data, borderline the magnitude escape. **feas 3, nonRed 4 → 11.**

### Lens II — Coupling to an external Zariski-dense source (escape (c))

- **#16 Twisted Markoff coupling sheaf.** Couple μ_n to the BGS Markoff-triple expander — a *proven* big-monodromy non-abelian source — then sieve back to η_b with an n-character Möbius/orthogonality sieve. **feas 4, nonRed 4 → 15.** The decisive risk: the sieve may re-impose the abelian projection and wash out the harvested curvature; the relabeling test (does the sieved object reproduce η_b exactly?) is cheap and decisive.
- **#10 Relative trace formula with μ_n-periodic spherical vector.** Recasts the prize as subconvexity of torus-period L-values, a toolbox that genuinely crosses the convexity barrier in its native setting. **feas 3, nonRed 5 → 14.** Risk: η_b may be purely Eisenstein (no L-value); honest residual is full Lindelöf.

### Lens III — Asymmetric / non-rotation-invariant weights (escape (b) by leaving the symmetric kernel)

- **#21 Hodge-asymmetric period filtration.** Weight the trace by the Stickelberger p-adic slope λ(χ) — the unique μ_n datum that is *not* rotation-invariant — so A(b) = Im Σ_χ G(χ)χ̄(b)λ(χ) sits outside the symmetric kernel and survives antipodal killing. **feas 6, nonRed 3 → 15.** Borderline (nonRed < 4): λ is valuation-class data, so watch for collapse into the magnitude escape; directly computable, the cheapest probe.
- **#25 Non-abelian period gerbe / secondary class.** Turn the vanishing *into* the invariant: a secondary (Massey-type) class defined on the locus where the primary cyclotomic invariant vanishes is, by construction, never killed by the same theorem. **feas 2, nonRed 5 → 11.** The trap is that the indeterminacy ideal may *be* the Kummer span.

### Lens IV — Odd-grade desymmetrization (rides the closed cyclotomic-vanishing escape — downgraded)

- **#17 Quaternionic half-lift,** **#3 antipodal-desymmetrized middle convolution,** **#24 crystalline off-diagonal coupling tensor.** Each tries to support the construction on the *odd grades* where antipodal *adds* rather than cancels. **#17 feas 5 nonRed 2 → 10; #24 feas 4 → 9; #3 → 8.** These are squarely the family that `_E6OddGradeVanish` / `_DoorIVConnectedCumulantVanishes` repeatedly show collapse; the make-or-break 4th-moment / "does Frobenius commute with x↦−x?" tests will likely show the off-diagonal block is zero.

### Lens V — Transcendence of the explicit Γ_p phases (substitutes one unavailable input for another)

- **#11 Γ_p Baker linear form,** **#12 three-distance Γ_p rotation,** **#13 Γ_p Mahler-measure height descent,** **#14 stationary-phase Γ_p saddle census.** These attack the *arg* of the Gross–Koblitz Γ_p-product directly. **#11 feas 4 nonRed 2 → 8; #12 → 6; #13 → 5; #14 → 3.** The honest problem: a Baker-type quantitative independence of the Γ_p phases at the needed strength is *as unavailable as* big monodromy (#11), the three-distance/saddle routes self-confirm reduction when the phase is flat/quadratic (μ_n is exactly the flat regime), and height/equidistribution give the average conjugate, not the sup (the §2.4 distribution-vs-sup gap reappears).

### Lens VI — Energy / random-matrix / free-probability (phase-blind by construction — downgraded)

- **#8 Vertical large-deviation rate (LDGT).** Upgrade the *real* Kowalski–Untrau vertical Sato–Tate to an effective upper-tail Cramér rate via Sawin's polynomial-in-conductor Betti bounds, then close the sup by a union bound. **feas 6, nonRed 4 → 24 (top adjusted score).** Crucially *not* a disguised energy floor: the honest residual is a subgaussian rate at fixed p, which is exactly the open input, and it is the most directly testable of all twenty-five.
- **#18 operator-valued free probability,** **#20 non-normal Ginibre ensemble,** **#15 Jacobi-sum doubling,** **#23 tropical coamoeba phase spread,** **#19 dynamical zeta / transfer operator,** **#7 Kuznetsov off-diagonal Poincaré,** **#6 Drinfeld modular theta-lift,** **#4 perverse IC on the energy variety.** Adjusted scores 3–8. Each either self-confirms reduction in its own first test (the diagonal of the doubled Jacobi family *is* the energy floor; the transfer operator's leading eigenvalue *is* |η_b|-type data; the spectral radius of diag(η_b) trivially ≥ max|η_b|), or is phase-blind by construction (scalar free prob is the in-tree energy law), or is a reformulation without a stated mechanism for *why* the controlling quantity is small (the coamoeba spread bound is the cancellation problem in disguise).

### The "worth building" set

Applying the strict bar **non-reduction ≥ 4 AND feasibility ≥ 4** admits exactly four:

1. **#8 LDGT** (6, 4) — top pick: highest raw product, a legitimate non-closed mechanism (effectivize a real theorem), most testable.
2. **#1 Wild p-adic Hodge / LT Swan-break twist** (5, 5) — best mechanism among the buildable; the cheap decisive test is a *nonzero connected 4-cumulant* of the wild-twisted period (vs. the tame η_b where `_DoorIVConnectedCumulantVanishes` forces 0).
3. **#5 Tannakian non-torsion rank-pump** (4, 4) — Larsen M_4 → 2 is a clean computable signal of monodromy growth.
4. **#16 Twisted Markoff coupling** (4, 4) — the strongest "external Zariski-dense" instance; decisive cheap relabeling + scaling test.

Plus one borderline cheap probe, **#21 Hodge-asymmetric filtration** (6, 3) — include it because feasibility 6 and it is directly computable, but it is *not* a core build (nonRed < 4). The two best *mechanisms*, **#9** and **#25** (nonRed 5), are gated by feasibility 2 — flag them as "high value if a feasibility path opens," not buildable now.

---

## 5. The honest verdict

### 5.1 What is genuinely open, and what is closed

The four obstructions of §3 are real, mutually reinforcing, and each independently witnessed axiom-clean in-tree. They close, definitively, the following routes: any tame functorial construction (Sym, ⊗, tame MC) on the μ_n Kummer sheaf; any energy/L²/moment bound (phase-blind, floored at exponent 1); any BGS-style expansion bound on the abelian Cayley graph (constant-factor, never √); any distributional/vertical-Sato–Tate statement used to bound the fixed-p sup (distribution ⊬ sup). None of these is a near-term lever.

What is **not** closed — and what every viable probe in §4 targets — is a single structural bet: *introduce non-torsion, wild, or external-Zariski-dense data that the dyadic 2^μ torsion cannot reach.* This is plausible *precisely because* the prior campaign only refuted **tame** big-monodromy constructions. The wild-at-∞ exponents of #1/#9/#22 are p-adic and non-cyclotomic — Lam–Leung has no jurisdiction there; the non-torsion twist of #5 is provably outside the resonance domain; the external expander of #16 is a *proven* big-monodromy source. Whether any of these survives is unknown.

### 5.2 The load-bearing unverified step (where each probe most likely dies)

For #1, #5, #9, #16, #22 alike, the single most likely failure point is **transfer**: the wild/non-torsion/external object's bound must control the *actual* η_b, not a different deformed period or a sieved proxy. A wild twist deforms the sum; a non-torsion convolution must project back through the lossy trivial-summand map; the Markoff coupling must survive a sieve that can re-impose the abelian projection. Each of these is a concrete, *cheap, machine-checkable* test:

- **#1:** compute the connected 4-cumulant of the wild-twisted period at n = 32; **nonzero** = first signal it escapes cyclotomic vanishing.
- **#5:** compute Larsen M_4 = (Σ_b|trace|^4)/(Σ_b|trace|²)² for the non-torsion-convolved object; **M_4 → 2** (from the abelian value ≈ n) = monodromy is pumping.
- **#16:** check to 1e-12 that the sieved Markoff object reproduces η_b *exactly* (faithfulness), then whether max_b tracks √(n log p) (curvature harvested) or n (sieve re-imposed abelian projection).
- **#8:** fit the empirical upper-tail Cramér rate I_n(t); test whether it is **subgaussian** (~t², good) and whether I_n(C√(n log(p/n)))·n > log p (union bound closes the sup).

Each test is a single exact-𝔽_p computation at n = 16, 32, 64 with p ≈ n^4, and each can *kill* its tool immediately — which is the point. The disciplined posture is: these are probes, not solutions; run the cheap falsifiers first.

### 5.3 The sharpest formulation of the missing theorem

Strip everything down. The Paley/BGK prize at β = 4 is equivalent to the existence of the following object, which I state as a conjecture-shaped target rather than a claim:

> **Missing Theorem (target form).** There exists a sequence of geometrically-irreducible, pure-weight-0, middle-extension ℓ-adic sheaves ℱ_n on an open U_n ⊂ 𝔾_m/𝔽_p (p ≈ n^4, n = 2^μ), with rank r(n) → ∞, such that (i) η_b is a faithful majorant of Tr(Frob_b | ℱ_n) for all b ∈ U_n(𝔽_p); (ii) ℱ_n is **not Kummer-induced** and its order-k Tannakian invariants are **nonzero on the locus of 2^μ-th roots of unity**; (iii) the geometric monodromy group G_geom(ℱ_n) is a classical group (SL/Sp/SO) of rank → ∞; (iv) the conductor c(ℱ_n) grows at most polynomially in n. Then Deligne equidistribution + Katz–Sarnak extreme-value statistics give M(n) ≤ C√(n log(p/n)).

Conditions (i)–(iv) are exactly W1–W4 of §3.5 made into a single geometric demand. The campaign's diagnostic theorems prove that the *natural* ℱ_n (the Kummer sheaf) and all *tame functorial* descendants fail (ii)–(iii) by cyclotomic vanishing. The open question — the entire prize — is whether a **non-tame, non-functorial** ℱ_n satisfying (i)–(iv) exists. The five mechanisms with teeth (#1, #5, #9, #16, #22) are five distinct bets that it does, each betting on a different way to put non-torsion structure into the construction so that the order-k invariants in (ii) survive.

### 5.4 Final honesty statement

No tool here is certified novel — that is impossible — and none is shown to work; the strongest are flagged as probes whose load-bearing transfer step is the most likely point of failure. A tool that genuinely supplied condition (ii)+(iii) — growing-rank big monodromy surviving the 2^μ cyclotomic vanishing — would be historic, and I make no claim that it exists. What this essay does establish, with the obstructions each witnessed axiom-clean in-tree, is the *exact location* of the missing input, the precise reason the four standard machines stop at exponent 1, and a small, honestly-scored, cheaply-falsifiable set of probes (#8, #1, #5, #16, with #21 as a cheap borderline) that are the only candidates in the twenty-five with a *specific* mechanism to evade the closed reductions. The boundary between proven and conjectural is held firm throughout: the obstructions are proven; the escapes are bets.

---

*Relevant in-tree files (absolute paths):* `/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib/Research/ProximityPrize/Frontier/` — `_NovelEllAdicSheaf.lean`, `_FrontierSheafConductor.lean`, `_FrontierSwanConductor.lean` (the explicit ℱ_n=[n]_*ℒ_ψ and its conductor); `_AttackR2_AbelianCayleyNonRamanujan.lean`, `NotRamanujanLowerBound.lean` (abelian/non-Ramanujan); `_AvX_VanishingTwoPowSumIsAntipodalP.lean`, `_E6OddGradeVanish.lean`, `_Close07c_OddGradeVanishesFull.lean`, `_DoorIVConnectedCumulantVanishes.lean`, `_DoorIVSixthCumulantVanishes.lean` (cyclotomic / odd-grade / cumulant vanishing); `_Bridge05_AntipodalOddVanishing.lean`, `EnergyRelationAntipodal.lean`, `AntipodalBalanceBounded.lean` (antipodal / thin-torsion); `_wfA07_fkm_sheaf_conductor.lean`, `_JacobiKatzEquidist.lean`, `_wfHK2_katz_sarnak_extreme_value.lean` (FKM/Katz family = average-not-sup).

*Key references:* Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups* (1988), *Exponential Sums and Differential Equations* (1990), *Rigid Local Systems* (1996), *Convolution and Equidistribution* (2012); Deligne, *La conjecture de Weil II* (Publ. IHÉS 52, 1980); Katz–Sarnak (AMS Colloq. 45, 1999); Fouvry–Kowalski–Michel, *Algebraic twists of modular forms* (GAFA 2015); Fouvry–Kowalski–Michel–Sawin, *Bilinear forms with trace functions* (arXiv:2511.09459, 2025); Forey–Fresán–Kowalski–Sawin, *Quantitative sheaf theory* (arXiv:2101.00635); Sawin, *A geometric approach to the sup-norm problem* (arXiv:1907.08098); Bourgain–Gamburd–Sarnak (Invent. 2010; Acta 2011); Untrau (Math. Proc. Camb. Phil. Soc. 2024), Kowalski–Untrau (arXiv:2310.08791); Lam–Leung, *Vanishing sums of roots of unity* (J. Algebra 224, 2000). Bound landscape: BGK n^{1−o(1)}, Burgess exponent exactly 1 at β = 4.