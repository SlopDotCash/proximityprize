# Teasing apart the prize walls: they are tight-equal at constant RATE (prize), separate only at constant DIMENSION, 2026-06-14

## The question (user direction)
The prize "walls" — δ*, far-line incidence I, list size Λ, character-sum M (=BGK/Paley eigenvalue),
additive energy E_r, Johnson, Gauss-period (Hasse–Davenport) — are "all equal." Tease apart WHICH
equivalences are tight vs lossy, and whether δ* is pinned by a tight chain to a *known/bounded*
quantity (so BGK would be only a lossy over-estimate, not the true δ*).

## The loss-labeled equivalence web (verified)
- **δ* ↔ I (far-line incidence) ↔ Λ (list of dim+1 super-code): TIGHT** (up to O(1) dimension). δ* is
  *definitionally* the radius where worst-case I crosses B=qε*≈n.
- **Λ ↔ M (character sum): √-LOSSY** — the spectral/Weil/Cauchy–Schwarz step that turns M into a list
  bound is exactly the Johnson `n^{1/2}` deficit. M *over-estimates*; M→Λ loses √.
- **M ↔ E_r: exp-lossy / floors** — `M^{2r} ≤ q·E_r`, provably cannot reach the floor at depth r≍log q
  (forced anomaly). E_2 = 3n²−3n exact → Johnson only.
- **M ↔ Gauss (HD): exact identity, but vacuous** — constant-index (prize, index m~2^128) classical
  Gauss bound `M ≤ ((m−1)√q+1)/m ~ √q` is TRIVIAL; HD reduces phase DOF n−1→n/4, residual Θ(n) free.
- **L² floor: M ≥ √n always** (exact). *(Corrected 2026-10-28, audit T48: not exact as stated. The
  nonzero Parseval mean is `n(p − n)/(p − 1)`, so the valid universal floor is
  `M ≥ √(n(p − n)/(p − 1))`, slightly below `√n`. At the proper subgroup `μ₈ ⊆ F₁₇` the two real
  periods are `(−1 ± √17)/2`, so `M = (1 + √17)/2 ≈ 2.56 < √8 ≈ 2.83`. This does not rule out a
  stronger lower bound under additional thin-field assumptions.)*

## The decisive finding (regime dichotomy)
Since δ*↔I↔Λ is **tight**, the whole question is: **is the tight worst-case incidence polynomial or
exponential at the prize?** Answer (verified):

- **Constant DIMENSION (k=O(1)):** the worst-case far-line incidence is **POLYNOMIAL** (I=j on the
  ladder; =C(n,r)/r near capacity with r=O(1); UD-plateau values). ⟹ **the walls SEPARATE**: δ* is a
  clean, computable, q-dependent **polynomial** — pinnable, and BGK/M is merely a √-lossy over-estimate.
- **Constant RATE (ρ fixed — THE PRIZE REGIME):** the worst-case far-line incidence at any fixed
  below-capacity radius is **EXPONENTIAL `2^{nH(ρ+c)}`**. ⟹ δ* genuinely **IS** the exponential-incidence
  threshold = BGK/additive-energy wall, established **via the TIGHT combinatorial side directly** — NOT
  a lossy-M artifact. There is no lossy edge to "escape": the tight quantity itself is the wall.

*(Scope note 2026-10-28, audit T48: the constant-rate "EXPONENTIAL `2^{nH(ρ+c)}`" worst-incidence
assertion lacks its guards. An incidence count of bad scalars is at most `q`, and an exponential
count of subsets does not become an exponential count of distinct scalars or codewords without the
actual codeword, image and field-budget conditions. "δ* is definitionally the radius where worst-case
I crosses B" also conflicts with the later finding that far-line incidence is a proxy, not the MCA
`δ*` (`farline-incidence-is-plotkin-proxy-not-mca-deltastar.md`).)*

## Resolution of the user's hypothesis
The hypothesis "the walls only *appear* equal via the √-lossy edges, and the tight δ* is poly-bounded"
is **TRUE at constant dimension** (walls separate, δ* clean) but **FALSE at the prize's constant-rate
regime**: there the tight combinatorial incidence is itself exponential, so δ* = BGK with no escape.
This sharply characterizes WHY the prize is hard — it is *specifically* the constant-rate regime where
the tight side is exponential; every "wall" is a faithful (tight) image of that one exponential object.

## Net
δ* is pinnable by a clean polynomial **only at constant dimension** (not the prize). At the prize
(constant rate) the tight incidence = BGK, confirmed without the lossy edges. The √-lossy edges
(Λ↔M↔E↔Johnson) are real but irrelevant to the impossibility: even the *tightest* characterization of
δ* (the incidence itself) is exponential at the prize. So no reframing across the wall-web pins δ* by a
known bound in the prize regime. (Reinforces the BGK/BCHKS-1.12 reduction, now via the tight side.)
