# N2-weil-rep — the Weil (oscillator) representation / quantum cat map lane, developed to completion (#466 novel-math round, 2026-07-01)

**Lane:** N2-weil-rep (Gurevich–Hadani / Kurlberg–Rudnick / Howe duality).
**Target:** `M(n,p) = max_{b≠0} |η_b| ≤ C√(n·log(p/n))`, `η_b = Σ_{x∈μ_n} e_p(bx)`, `n = 2^30`,
`p ≡ 1 (mod n)`, `m = (p−1)/n ≈ 2^128`.
**Verdict up front (honest):** the lane produces an **exact, machine-verified dictionary** —
η_b IS a matrix-coefficient datum of the Weil representation restricted to the split torus, in
three equivalent exact forms — and then **self-terminates**: every purity/transfer consumer of
that dictionary lands on the wall at a now-**exactly-quantified** point (overshoot `2^60.76` at
the prize point; self-duality preserving the constant C to three decimals). The one move the
seed hoped could evade 0-dimensionality (Howe/theta transfer to a complete orbit of an auxiliary
object) is killed by a three-part mechanism: Stone–von-Neumann central-character pinning, the
primality of F_p (no subfield descent target), and gamma-factor invariance of theta transfer.
**No step of the prize inequality is proven; the chain's value is that the landing is now exact
(constant-preserving identities, not heuristics).** Self-refutation documented at Step 8.

Probe: `scripts/probes/probe_466_novel_n2_weilrep.py`
(output `scripts/probes/_out_466_novel_n2_weilrep.txt`; all four identity families verified to
float precision, residuals ≤ 2·10⁻⁹ at p = 65537).

---

## 0. Prior-kill compliance (what this lane must not re-derive, and doesn't)

Checked against `DISPROOF_LOG.md` + dossier v3 §8 before writing:

- **WEILINDEX-FIBER (2026-06-17, REFUTED):** the "metaplectic fiber identity"
  `η_b = γ_p(b)·√2·η'_{φ(b)}` is FALSE (off by 25%; no completing-the-square for LINEAR phases).
  This lane never uses a fiber descent; its identities are verified exact below.
- **T21 (REDUCES-TO-WALL F5):** `H²(ℤ/n, 𝕋) = 0` — the metaplectic cover splits over the cyclic
  torus; there is no 2-dim "oscillator isotype" over μ_n. Used below AS a kill (Step 5c).
- **O178 (`theta_no_contraction`, axiom-clean):** Fourier-type involutions preserve support size —
  the Poisson/theta transform does not shorten the sum. Step 7's self-duality is the sharp,
  constant-preserving form of this.
- **L5 far-depths completeness:** every Frobenius-trace realization is linear in effective rank;
  theta correspondence / geometric Langlands floored at second-moment rank. This lane's Step 6 is
  the specialization of L5 to the two concrete algebraic presentations of μ_n, with exact numbers.
- **D5 gate (`weil_exceeds_prize_by_2pow60`):** independently reproduced here as `2^60.76`
  (Step 4) — consistency check passed.
- **`effectiveKatz_vacuous_in_thin_regime`** (`Frontier/_AssaultV2_EffectiveSatoTate.lean:135`,
  axiom-clean): the landing point of Step 8 is this named gate, i.e. form (B) of the core.

---

## 1. Setup — the Weil representation and the split torus (standard, stated exactly)

Fix odd `p`, `ψ(z) = e_p(z) = e^{2πiz/p}`. Heisenberg group `H = F_p³` with
`(q,r,z)(q',r',z') = (q+q', r+r', z+z'+(qr'−rq')/2)`. Stone–von Neumann: up to isomorphism there
is a UNIQUE irrep `π_ψ` of H with central character ψ; in the Schrödinger model on
`L²(F_p) = C^p`:

- position translation `π(q,0,0)f(x) = f(x+q)`; **modulation (Weyl operator)
  `π(0,r,0)f(x) = ψ(rx)f(x)`**.

`SL₂(F_p)` acts on H fixing the center; SvN uniqueness gives intertwiners, unique up to scalar
⟹ the **Weil representation** `ρ: SL₂(F_p) → GL(C^p)` (linearizable for finite odd p; Weil 1964,
Gérardin 1977), satisfying the exact covariance `ρ(g)π(w,z)ρ(g)⁻¹ = π(gw, z)`. Schrödinger-model
formulas (σ = Legendre symbol):

- split torus `t_u = diag(u, u⁻¹)`: `ρ(t_u)f(x) = σ(u)·f(u⁻¹x)`;
- unipotent: `ρ([[1,c],[0,1]])f(x) = ψ(cx²)f(x)` (the only place quadratic phases enter);
- Weyl element: normalized DFT (Gauss-sum normalization).

**Torus eigenbasis.** For each multiplicative character χ of `F_p^×` set `f_χ(x) = χ(x)` (x ≠ 0),
`f_χ(0) = 0`. Then `ρ(t_u)f_χ = σ(u)χ̄(u)·f_χ` — the split-torus eigenvectors are exactly the
multiplicative characters, plus `δ_0` (eigencharacter σ). These are the split-case Hecke
eigenfunctions of Kurlberg–Rudnick. Note `‖f_χ‖_∞/‖f_χ‖₂ = 1/√(p−1)`: split eigenfunctions are
PERFECTLY FLAT (the sup-norm theorems below have no content for them).

Since `m = (p−1)/n` is even at the prize point, `μ_n = (F_p^×)^m ⊆ squares`, so **σ|_{μ_n} = 1**:
the thin torus `T_n = {t_u : u ∈ μ_n}` acts without the Legendre twist.

---

## 2. The exact dictionary — η_b as Weil-rep matrix-coefficient data (three forms, all verified)

**(M1) Averaged-observable form (the Kurlberg–Rudnick shape).** Conjugation law (one line from
covariance; Legendre factors cancel: `σ(u)σ(u⁻¹) = 1`):

> `ρ(t_u)⁻¹ π(0,b) ρ(t_u) = π(0, ub)`.

Hence with `A_b := Σ_{u∈μ_n} ρ(t_u)⁻¹ π(0,b) ρ(t_u) = Σ_{u∈μ_n} π(0, ub)`:

> **`η_{ab} = ⟨A_b δ_a, δ_a⟩` for every a ≠ 0; in particular `η_b = ⟨A_b δ_1, δ_1⟩`.**

η_b is EXACTLY the diagonal matrix element, at a position state, of the T_n-average of a single
Weyl operator — the thin-torus analogue of the KR Hecke-averaged observable. Note `A_b` is
diagonal in the position basis with entries `{η_{ab}}_a`; so `‖A_b‖ = M(n,p)` for EVERY b ≠ 0
(dilation-orbit invariance — the operator-norm framing is a tautology, cf. T21's
`affine_fourier_input_norm`; no leverage, flagged and not used).

**(M2) Invariant-sector compression (the symmetry-sector form).** Because σ|_{μ_n} = 1, the
T_n-invariant sector of the Weil rep is `V₀ = span{f_χ : χ ∈ Ann(μ_n)} ⊕ Cδ_0`, `dim V₀ = m+1`,
with coset basis `e_c = n^{-1/2}·1_{cμ_n}` (c over the m cosets). The compressed Weyl operator is
diagonal there:

> **`⟨π(0,1) e_c, e_{c'}⟩ = δ_{cc'} · η_c/n`.**

The prize is a sup-norm bound on a Weyl operator compressed to a rank-(m+1) symmetry sector.
KR/GH technology bounds rank-ONE sectors (single Hecke eigenfunctions) of the FULL torus; the
sector here has rank m = 2^128 and the torus is thin. This is the precise technology gap in
sector language.

**(M3) Annihilator/Gauss decomposition (the constituent form — the load-bearing identity).**
`Ann(μ_n) = {χ : χ|_{μ_n} = 1} ≅ ℤ/m` (the index-m subgroup of the dual). Pointwise on F_p^×,
`1_{μ_n} = (1/m) Σ_{χ∈Ann} χ`. With `⟨π(0,b) f_χ, f_1⟩ = Σ_{x≠0} ψ(bx)χ(x) = χ̄(b)τ(χ)` (χ ≠ 1;
`= −1` for χ = 1), `τ(χ) = Σ_x χ(x)ψ(x)` the Gauss sum:

> **`η_b = (1/m)·⟨π(0,b)(Σ_{χ∈Ann} f_χ), f_1⟩ = (1/m)·(−1 + Σ_{1≠χ∈Ann} χ̄(b)·τ(χ))`.**

Probe-verified exactly (residual ≤ 1.2·10⁻¹⁰ at n=16, p=65537, m=4096, over 64 random b).

**Closure of the dictionary (the lane's structural theorem).** For ANY T_n-eigenvectors
`φ = Σ c_χ f_χ`, `φ' = Σ c'_χ f_χ` (same μ_n-eigencharacter) and any b:
`⟨π(0,b)φ, φ'⟩ = Σ_{χ,χ'} c_χ c̄'_{χ'} · (χχ̄')‾(b)·τ(χχ̄')` with `χχ̄' ∈ Ann(μ_n)`. So:

> **Every T_n-equivariant matrix-coefficient functional of the Weil representation lies in the
> m-dimensional space spanned by `{χ̄(b)τ(χ) : χ ∈ Ann(μ_n)}`.** The lane HAS no other data.
> Purity fixes the m magnitudes exactly (`|τ(χ)| = √p`, Gauss 1801 — probe: max deviation
> 2.3·10⁻¹³); the prize is a statement about the m PHASES `ε_χ = τ(χ)/√p`, and the entire
> representation-theoretic apparatus (SvN intertwiners, theta transfer, doubling) acts on this
> space by permutations and unimodular scalars — it is an **isometry group of the problem, not a
> compression of it** (Steps 5–7 make this precise per move).

---

## 3. What the strongest PROVEN statements give here (exact statements, exact shortfalls)

- **Kurlberg–Rudnick (Duke Math. J. 103 (2000) 47–77).** For Hecke eigenfunctions φ of the full
  torus (order p∓1) and fixed observables: `|⟨Op(f)φ,φ⟩ − ∫f| = O(p^{−1/4})` via the fourth
  moment of Hecke periods. Fourth moment = order-2 energy = `MetaTheoremSecondOrderCap`. Applied
  to the thin sector it is the r = 2 moment — Johnson-locked.
- **Gurevich–Hadani (rate conjecture; Annals of Math. 174 (2011); geometric Weil rep, Selecta 13
  (2007) 465–481).** For every nontrivial torus character χ and `ξ ≠ 0`: the Hecke period
  `a_χ(ξ) = Σ_{t∈T} χ̄(t)⟨π(ξ)ρ(t)φ, φ⟩`-type COMPLETE torus sum satisfies **`|a_χ| ≤ 2√p`** —
  realized as trace of Frobenius on a two-dimensional weight-≤1 cohomology (perverse
  sheaf/purity). Two facts kill the transfer to the thin problem:
  (i) at the prize point the torus is SPLIT, and the split-case periods are literally Gauss/Jacobi
  sums — GH purity specializes to `|τ(χ)| = √p` **which is already exact and elementary**; the
  machinery has ZERO residual slack to give (its entire output is per-constituent magnitude,
  saturated);
  (ii) GH's sheaf lives on the full torus orbit (a 1-dim variety); the thin sub-orbit μ_n is the
  F_p-points of the 0-DIM subscheme `{x^n = 1}` — Grothendieck–Lefschetz over a 0-dim variety has
  no H¹, purity degenerates to per-point bounds, total = n (trivial). Tetrachotomy door (i), hit
  at its exact mechanism.
- **Olofsson (arXiv:math/0601422; Ann. Henri Poincaré 10 (2009) for prime powers).** For N = p
  prime, ALL L²-normalized Hecke eigenfunctions satisfy `‖φ‖_∞ ≤ 2/√(1−1/p)` (split) /
  `2/√(1+1/p)` (inert) — O(1), and for the split torus trivially `= 1/√(p−1)·√p`-flat (§1). Sup
  norms of EIGENFUNCTIONS say nothing about sup norms of thin-averaged OBSERVABLE matrix
  elements: the observables here have frequency b and average length n growing with p, outside
  every cat-map theorem's scope (their f is fixed as p → ∞).

**Summary row for the dossier table:** KR/GH/Olofsson bound (a) complete orbit sums of length
~p at `2√p`, (b) rank-1 full-torus sectors, (c) eigenfunction sup norms. The prize needs the
length-n = p^{1/4} sub-orbit at `√(n log m)`. No proven statement in the cluster touches an
incomplete sub-orbit sum.

---

## 4. The purity floor — exact constants at the prize point

Any consumer of (M3) via per-constituent magnitude (triangle inequality — the ONLY thing
weight/purity theory outputs) gives

> `|η_b| ≤ (1/m)(1 + (m−1)√p) < √p`.

At the prize point: `√q ≈ 2^79` (q ≈ n·2^128 = 2^158); target `C√(n·ln(p/n)) = √(2^30·88.72) ≈
2^18.24`. **Purity overshoot = 2^60.76** (analytic diagonal p ≈ n⁴: `2^60/2^17.98 = 2^42.02`).
Matches the in-tree D5 gate `weil_exceeds_prize_by_2pow60` — independent re-derivation.

**Rank cannot rescue weight.** A weight-1 realization with R constituents gives `R·√p ≥ √p`
(R ≥ 1): the floor is `√p` REGARDLESS of rank reduction — `2^60.76` above target. A weight-0
realization (bounded constituents) needs rank ≥ n to be exact (the b-function η has additive-DFT
support exactly μ_n, i.e. exact trigonometric rank n), giving the trivial bound n. Between the
two sits the arithmetic uncertainty principle (dossier §4.3). There is no weight/rank tradeoff
that reaches `2^18.24`.

---

## 5. The Howe-duality / doubling / theta moves — developed, then killed with mechanism

The seed's central hope: convert the thin sum into a COMPLETE sum of a different object with its
own purity bound. The three available rep-theoretic conversions:

**(5a) Doubling (Piatetski-Shapiro–Rallis; the "oscillator rep of the doubled torus").** The
doubling functional on `φ ⊗ φ̄` computes `Σ |⟨π(ξ)φ, φ⟩|²` — the SECOND MOMENT of the
matrix-coefficient family. This is the rep-theoretic name of the L²/energy functional:
`MetaTheoremSecondOrderCap` applies verbatim — caps at Johnson/√p. Iterating (2r-fold doubling)
is the moment ladder — door (iv), works only at r ≈ ln p where it IS the target. Dead.

**(5b) Theta correspondence / dual-pair transfer (SO(2)_split × SL₂ ⊂ Sp₄, or any
(G, G') pair containing the torus).** Three pins, jointly fatal:
  1. **SvN pinning:** every model of the oscillator rep with central character ψ = e_p is
     unitarily equivalent with intertwiner unique up to scalar; the matrix-coefficient FIELD
     `Q(ζ_p)` and the weight unit `√p` are invariants of ψ. A transfer that changed the ambient
     prime would change ψ — impossible: **F_p is a prime field; there is no subfield to descend
     to; the only field moves go UP (F_{p^k}, worse unit √(p^k))**. The `√p` unit is immovable.
  2. **Gamma-factor invariance:** the theta lift of a character χ of the split SO(2) = F_p^× to
     SL₂ has local factor `γ(χ, ψ) = τ(χ)/√p = ε_χ` — the transfer KERNELS are built from the
     very Gauss angles that are the problem. Transferring re-brackets
     `Σ_{χ∈Ann} χ̄(b)ε_χ` by unimodular scalars; the across-constituent phase problem is
     transported isometrically, never compressed. (This is why "the correspondence preserves
     conductor": the ε-data IS the correspondence's arithmetic content.)
  3. **No projective enhancement over the torus (T21, in-tree, axiom-clean):**
     `H²(ℤ/n, 𝕋) = 0` ⟹ the restriction of the Weil rep to the (cyclic) split torus is a
     multiplicity-≤2 direct sum of 1-dim characters (§1); there is no 2-dim oscillator isotype
     over μ_n whose "purity" could differ from the abelian Gauss data. The finite-field theta
     correspondence literature agrees: Weil-rep character values ARE Gauss sums as exact
     algebraic numbers (Aubert, arXiv:2603.25658 finding from the L5 sweep) — identities, not
     new upper bounds.

**(5c) The 2-power tower / metaplectic fiber descent** (μ_{2k} → μ_k antipodal squaring — the
one structural resonance between DYADIC n and oscillator structure, since the tower is a tower
of square roots and the Weil rep is quadratic-native): **already REFUTED in-tree**
(WEILINDEX-FIBER, exact-arithmetic countermodel, off by 25%: n=8, p=4129: max|η| = 7.5582 >
√2·max|η'| = 5.6501). Mechanism: `e_p(bx) + e_p(−bx) = 2cos(2πbx/p)` depends on x, not x²; a
LINEAR phase does not complete the square. The lane confirms and does not retry.

---

## 6. The two-presentations lemma — every algebraic avatar of μ_n, enumerated

μ_n admits exactly two presentations as an algebro-geometric object over F_p, and each lands on
a documented trivial/vacuous bound:

1. **0-dimensional, degree n:** `μ_n = V(xⁿ − 1)(F_p)`. Lefschetz sum over a 0-dim variety =
   Σ of n Frobenius stalk traces, each |·| = 1, no H¹ to produce cancellation ⟹ bound n
   (trivial). [Tetrachotomy door (i) — 0-dimensionality, exact mechanism.]
2. **1-dimensional image, rank m:** `μ_n = [m](G_m)`, giving the EXACT complete-sum lift
   > `η_b = (1/m)(S_m(b) − 1)`, `S_m(b) = Σ_{y∈F_p} ψ(b·y^m)`
   (probe-verified to 9·10⁻¹⁶). `S_m` is a complete sum of an object of rank/genus ~m = 2^128:
   Weil gives `(m−1)√p ≫ p` — vacuous. [Bounded-complexity kill; the degree-2^128 monomial
   lift.]

A hypothetical third presentation with complexity `R ≤ √(m log m)` and weight-1 constituents is
what a purity proof would need (Step 4 arithmetic) — and Step 4 shows even R = 1 overshoots,
because the unit `√p` itself exceeds the target. **There is no complexity level at which
weight-1 purity meets the prize; the failure is in the WEIGHT UNIT, not the rank.** (This
sharpens L5: not merely "rank forced to n", but "even rank 1 fails by 2^60.76".)

---

## 7. Self-duality with constant preservation (the lane's sharpest exact output)

From (M3), with `ε_χ = τ(χ)/√p` unimodular:

> **Dual identity: `Σ_{1≠χ∈Ann} χ̄(b)·ε_χ = (m·η_b + 1)/√p` for every b ≠ 0.**

So `CORE ⟺ max_b |Σ_{χ∈Ann\{1}} χ̄(b) ε_χ| ≤ C·√(m·log m)` — the SAME √(size·log) inequality
for the m-term Gauss-angle walk on the annihilator group `Ann ≅ ℤ/m`, with the SAME constant:

| n | p | m | C (primal) | C_dual (measured) |
|---|---|---|---|---|
| 8 | 4129 | 516 | 1.069 | 1.069 |
| 16 | 65537 | 4096 | 1.199 | 1.199 |
| 32 | 12289 | 384 | 1.370 | 1.370 |

(probe columns; agreement to 3 decimals — the +1 and (m−1)-vs-m corrections are O(1/√(m log m))).

**One-line swap proof that the dual IS the primal** (so no "large-subgroup" technology applies
on the dual side without unwinding): `Σ_{χ∈Ann} χ(b̄)τ(χ) = Σ_{x} ψ(x) Σ_{χ∈Ann} χ(b̄x) =
m·Σ_{x∈bμ_n} ψ(x) = m·η_b`. The dual sum regenerates η_b verbatim. This is the
constant-preserving sharpening of `theta_no_contraction` (O178): the Weyl-element conjugation
(multiplicative DFT with Gauss kernel) is an ISOMETRY of the problem with the prize functional
as a fixed point. Note the dual object is NOT a subgroup exponential sum (the weights ε_χ are
not multiplicative — they obey the Jacobi-sum cocycle `ε_χε_χ' = ε_{χχ'}·J(χ,χ')/√p`), so
Heath-Brown–Konyagin/Shkredov large-subgroup technology (m ≈ p^{0.81} > p^{2/3}!) does NOT
apply to it; the only handle on the ε-field is the Jacobi cocycle — which is the already-gated
"effective Jacobi-equidistribution house" (#407 tangent-autocorrelation note) and the
non-torsion self-braiding datum of the D0/EVW kill.

---

## 8. The landing (self-refutation of the lane) and the residual demand

Assemble Steps 2–7: every functional the Weil-representation lane can form is a point in the
m-dim span of `{χ̄(b)τ(χ)}` (Step 2 closure); magnitudes are pinned exactly by purity with zero
slack (Step 3); per-constituent consumption floors at `√p` = target × 2^60.76 (Step 4); all
transfers act isometrically on the constituent space (Step 5); all algebraic presentations give
n or (m−1)√p (Step 6); the Fourier/Weyl move is a fixed point preserving C (Step 7). Therefore:

> **The lane's residual demand is exactly: worst-case-in-b square-root-with-log cancellation of
> the m Gauss-angle constituents — i.e., effective worst-case equidistribution of
> `{ε_χ : χ ∈ Ann(μ_n)}` against every character of ℤ/m.** This is form (B) of the core
> (dossier §2.4), with the in-tree gate `effectiveKatz_vacuous_in_thin_regime` proving the
> known effective-Katz technology is vacuous here. The lane lands ON the wall, at the expected
> door, with the landing now exact.

**Why this is a success by the lane's own criterion:** the chain is complete — every step is
either a verified identity (probe residuals ≤ 2·10⁻⁹), a cited proven theorem with hypotheses
checked (KR Duke 2000; GH Annals 174 (2011); Olofsson math/0601422; Gauss; SvN; H²(ℤ/n) = 0),
or an explicit kill — and the final step is the open core, flagged as such. The seed's question
("does the doubled-torus/theta move evade 0-dimensionality?") is answered NO with a
three-part mechanism (5b), which is new at this precision: **the weight unit √p is pinned by
the central character through Stone–von Neumann, and F_p has no subfields — so no intertwining
move can change the purity unit, and the constituent phases are the transfer kernels
themselves.**

## 9. What is bankable from this lane (small, honest)

- The exact dictionary (M1)–(M3) + the sector compression (M2) as a formalizable brick
  (elementary finite linear algebra; would give the dossier a clean "the prize is a compressed
  Weyl-operator sup-norm" face — Lean-friendly, no new axioms).
- The dual identity + swap proof as a one-lemma brick (`selfdual_gauss_walk`): kills, once and
  for all and quantitatively, any future "attack the dual side with large-subgroup technology"
  proposal (the dual IS the primal, constant-preserved — measured 1.199/1.199).
- The purity-floor arithmetic (Step 4) as the sharp form of D5: `even rank-1 weight-1 fails by
  2^60.76`; the failure is the weight unit, not the rank.
- Dossier §3 table row: KR/GH/Olofsson entries with the exact statements and the "complete
  orbit only / rank-1 sector only / eigenfunctions only" scope pins.

## 10. Files

- Probe: `scripts/probes/probe_466_novel_n2_weilrep.py` →
  `scripts/probes/_out_466_novel_n2_weilrep.txt`.
- This note: `docs/kb/deltastar-466-novel-N2-weil-rep-2026-07-01.md`.
- Cited in-tree: `Frontier/_AssaultV2_EffectiveSatoTate.lean` (`effectiveKatz_vacuous_in_thin_regime`),
  DISPROOF entries WEILINDEX-FIBER, T21, O178, L5, D5 gate.

## Sources (external)

- Gurevich–Hadani, *Proof of the Kurlberg–Rudnick rate conjecture*,
  [Annals of Mathematics 174 (2011)](https://annals.math.princeton.edu/2011/174-1/p01);
  announcement [C. R. Acad. Sci. Paris 342 (2006)](https://www.sciencedirect.com/science/article/pii/S1631073X05005091);
  arXiv versions [math-ph/0404074](https://arxiv.org/abs/math-ph/0404074),
  [math-ph/0510027](https://arxiv.org/abs/math-ph/0510027); the eigenfunction/sup-norm companion
  [math-ph/0511036](https://arxiv.org/abs/math-ph/0511036).
- Kurlberg–Rudnick, *Hecke theory and equidistribution for the quantization of linear maps of
  the torus*, Duke Math. J. 103 (2000) 47–77.
- Olofsson, *Bounds on supremum norms for Hecke eigenfunctions of quantized cat maps*,
  [arXiv:math/0601422](https://arxiv.org/abs/math/0601422) (prime N: `2/√(1∓1/N)` bounds);
  *Hecke eigenfunctions of quantized cat maps modulo prime powers*,
  [Ann. Henri Poincaré (2009)](https://link.springer.com/article/10.1007/s00023-009-0011-1);
  *Large supremum norms…*, [arXiv:0711.4509](https://arxiv.org/abs/0711.4509) (prime-power
  N^{1/4} phenomena — not our regime).

<sub>🤖 N2-weil-rep lane, #466 novel-math round, 2026-07-01. No closure claimed; the core is
carried as the named open form (B). Probe-verified identities; all kills cross-checked against
DISPROOF_LOG. DO-NOT-COMMIT discipline respected (working tree only).</sub>
