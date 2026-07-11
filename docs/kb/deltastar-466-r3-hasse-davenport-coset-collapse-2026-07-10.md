# #466 r=3 route (ii): Hasse–Davenport coset triple collapse — exact structure found, calibrated stratum-local (2026-07-10)

Session target: `TripleConvEnergyBound` (the calibrated r=3 open core, `_R23TripleConvEnergyInput.lean`),
route (ii) of the §33 dossier normal form: HD exact angle relations along subgroup cosets of ℤ/m.

## Result (positive half — NEW exact identity on the ladder object)

Write `J_j = jacobiCoeff χ lam j = g(λ^j)g(χ)/g(λ^jχ)` (Gauss-sum form). Applying the classical
Hasse–Davenport **product relation** `∏_{a<k} g(χ'ρ^a) = χ'(k)^{-k} g(χ'^k) ∏_{0<a<k} g(ρ^a)`
(ρ = λ^{m/k}, order k) to numerator and denominator along the coset `{j, j+u, j+2u}`, `u = m/3`,
the auxiliary products cancel:

  **(I3)** `J_j · J_{j+u} · J_{j+2u} = κ · J₃(3j)` for **every** `j : ℤ/m`, with
  `κ = χ(3)³·J(χ,χ)·J(χ²,χ)` (j-independent, `‖κ‖ = q`), `J₃ = jacobiCoeff (χ³) lam`.
  Conditions: `3∣m`, `p ≠ 3`, `χ²,χ³` nontrivial.

Also verified: the k=2 analogue **(I2)** `J_j·J_{j+m/2} = χ(2)²·J(χ,χ)·J₂(2j)`; the aggregate
vertical descent **(AGG3)** `∑_j J_j J_{j+u} J_{j+2u} = κ·m·W_{χ³,G'}(1)` where `G'` is the
index-`(m/3)` coarsening of `G` — the depth-3 coset-diagonal mass IS a depth-1 thin-face value
of `χ³` over the coarser subgroup; and the degenerate branch **(D3a)**: when `χ²` is trivial the
identity holds with the exact correction factor `q` (`lhs = q·κ·J₃(3j)`).

Probe: `scripts/probes/probe_466_r3_hasse_davenport_coset.py` — deterministic, 75 (q,m,χ)
instances (q up to 73, m up to 36, χ in-family and out-of-family), tolerance 1e-8 relative at
scale q^{3/2}. Holds at EVERY index j, including all per-index degeneracies (`λ^{3j}χ³` trivial,
`λ^{3j}` trivial, `λ^{j+au}χ` trivial) — both sides degenerate consistently, no exclusions.

## Result (negative half — refutation with countermodel)

The natural extension candidate — the same κ-collapse for perturbed off-coset triples
`(j, j+u+1, j+2u−1)` — is **FALSE at 0/m indices** in every probed non-vacuous cell (m ≥ 6).
The angle rigidity is exactly the coset structure; it does not leak.

## Calibration verdict for the r=3 rung

- The coset-diagonal stratum of `tripleConv` is pinned at Wick scale by HD: energy
  `∑_j ‖J_j J_{j+u} J_{j+2u}‖² ≤ q²·m·q = m·q³` — i.e. `1/m²` of the budget `C·m³·q³`,
  precisely where the R23 triangle-inequality baseline loses `m²`.
- But the collapse is **stratum-local**: the generic off-coset triples (which carry ~m² of the
  m² decompositions per output index) provably do NOT collapse. Route (ii) alone cannot close
  `TripleConvEnergyBound`; it removes one exact stratum and supplies a new depth-reduction tool
  (level-3 phases ↦ level-1 phases of χ³ along cosets).

## Formal kernel

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R297HasseDavenportCosetTriple.lean` —
axiom-clean (`[propext, Classical.choice, Quot.sound]`, no sorryAx), pg-iterate 7s:
- `HDCosetTripleCollapse` — the named exact input (the Gauss-sum product relation is classical
  but absent from Mathlib; the Prop is pinned to the classical instantiation, probe-verified);
- unconditional: `sum_cosetTripleProduct_eq` (aggregation),
  `sum_jacobiCoeff_subgroup_eq_shiftedSum` (Fubini/indicator subgroup descent),
  `sum_cosetTripleProduct_eq_shiftedSum` (the composed exact depth-3→depth-1 descent),
  `norm_cosetTripleProduct_le`, `cosetTripleProduct_energy_le` (Wick-scale consumers).

## Corrected next target on the r=3 rung

The open content of `TripleConvEnergyBound` now lives entirely on the **off-coset strata** of
the triple convolution. Two successor moves:
1. **HD-twisted second moment across strata**: use (I3) to substitute one coset-collapsed factor
   inside the full energy sum and reduce the sextic energy to a mixed depth-1/depth-3 correlation
   `∑ J₃(3j)·(off-coset pair terms)` — i.e., HD as a change of variables in the energy, not a
   per-term bound (unexplored; the probe infrastructure here computes both objects already).
2. **Katz vertical equidistribution (route i)** for the off-coset angle triples specifically —
   the countermodel shows their phases are NOT HD-rigid, which is consistent with (and needed
   for) equidistribution; the calibrated question is now sharper: square-root cancellation on
   off-coset strata only.

DISPROOF_LOG tag: `466-r3-hasse-davenport-coset-triple-collapse`. CORE OPEN, ON-BGK.
