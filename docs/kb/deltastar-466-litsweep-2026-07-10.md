# Literature sweep 2026-07-10 (post-doctrine-v2): analytic core UNCHANGED; one same-day protocol-layer pull (GGSW LCL curve-decodability); iterated-KM confirms the G78 failure point

Full sweep by web agent (arXiv + ePrint + ECCC, cutoff 2026-07-10). Prior sweep: round 10
(2026-07-04). Doctrine context: `deltastar-466-tool-shape-doctrine-v2-2026-07-10.md` — the
prize is one missing NON-FOURIER anti-concentration certificate.

## Verdict on the analytic core (CORE / Paley face)

**Nothing.** No 2025–2026 work touches the thin regime `n ≈ p^{1/4}` at square-root scale:
BGK, di Benedetto et al. `H^{1−31/2880+o(1)}`, Hanson–Petridis, Shkredov medium-size bounds
all unimproved. No work anywhere attempts a non-Fourier anti-concentration certificate for
geometric progressions in arcs. The doctrine's missing-ingredient diagnosis stands with an
up-to-date literature floor under it.

Notable adjacent (off-regime but mechanism-novel): Pham–Xue, arXiv:2606.03627 — finite-field
spherical restriction past Stein–Tomas in d=4 via "horizontal slicing + stopping time"
defeating a Kloosterman/Weil obstruction. The ONLY structurally new "beat a Weil-type floor
by non-Fourier slicing" move seen; spheres are additive-character varieties, not
multiplicative subgroups, and the slicing uses the sphere's fibration structure which μ_n
lacks. Watched, not actionable.

## Iterated Kelley–Meka (Raghavan, arXiv:2603.27045, 2026-03-27)

First 3AP exponent improvement past Bloom–Sisask (1/9 → 1/6, iterated sifting + improved
Croot–Sisask bootstrapping). **G78 assessment carries over unchanged:** the iteration
improves the DENSE-regime exponent; the engine still certifies spreadness through
Fourier-side almost-periodicity, so at μ_n the hypothesis remains rank-one circular
(G78's `l1_deviation_of_phase_bias` extraction applies verbatim to the iterated form —
iteration composes constant-loss arrows and cannot create a contraction where none exists).
No sparse/thin extension exists or is claimed.

## THE PULL: Goyal–Guruswami–Sun–Wootters, arXiv:2607.08516 (2026-07-09, one day old)

"Locality of Curve-Decoding and Improved Proximity Gaps."
- Extends the Local Coordinate-wise Linear (LCL) framework to a **row-span-constrained**
  version and casts **curve-decodability directly as a row-span-constrained LCL property**
  (prior work used a proxy).
- Random linear codes, RS with RANDOM evaluation points, and Gallager LDPC now match the
  GG25 subspace-design proximity-gap parameters, with **degree-independent** losses, via
  **black-box transference from subspace-design codes**.
- Plain RS over SMOOTH (structured) domains: not covered — consistent with (and orthogonal
  to) the campaign's theorem that plain-RS δ* in the window IS the Paley object.

**Actions for the lanes:**
1. **B2 (`Frontier/CurveDecodability.lean`, OPEN since #334):** the row-span-constrained LCL
   definition is the missing clean abstraction the lane wanted — [GG25] Def 3.1 →
   [Jo26]-half should be re-planned against 2607.08516's formulation (their Thm casting
   curve-decodability as LCL is exactly the shape `curveDecodable_of_structured_close_set_
   budget` wants to consume). Recommended as the next B2 work unit.
2. **Folded-RS capacity pin (Tier-3 bankable win):** the black-box transference means any
   Lean progress on the subspace-design pin now propagates for free (in paper-land) to three
   random ensembles — the pin's external value went up; priority unchanged-or-higher.
3. No wall contact: nothing in the paper touches the structured-domain character-sum core.

## Protocol-layer confirmations (already integrated, no action)

KKH ePrint 2026/782 = the in-tree `m_KKH26` ceiling (fully consumed since #444);
Kambiré/Crites–Stewart capacity failures known (dossier §1.3); GG25 2025/2054 known
(Tier-3); JLR 2601.10047 withdrawn as subsumed — update citations to point at GG25/GGSW.
Low-confidence FRI-layer ePrints (2026/858, 2026/861, 2025/1712) remain unvetted; treat
claims of Johnson-transcendence with the campaign's standard skepticism (the Meta-Theorem
says any such result must contain a list-decoding advance).
