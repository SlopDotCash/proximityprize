# #466 r=3 R302: trace-formula/point-count reformulation — the DIST rung
# diagonalizes in the DFT; open core reduces to POINTWISE FLATNESS of the full
# Jacobi DFT; the integer phenomenon IS a Möbius-weighted Fermat point count
# (2026-07-10)

Sixth brick of the r=3 route-(ii) session (R297 → R302).  Target set by the R301
observation: the Galois-averaged DIST energy at m = 9 is an exact integer at
every prime — "the signature of a point count".  Both directions are now
resolved: the point-count structure is made exact and probe-verified at m = 9
AND m = 12 (the first open instance), and the formalizable part is landed in
Lean at general m.

## 1. The trace formula (probe-verified exactly; Lean-proved where finite)

Write `m = 3u'`.  The H-cosets of ℤ/m are the fibers of the ring reduction
`label : ℤ/m → ℤ/u'` — u' cosets, EACH OF SIZE 3 (this replaces the "j mod 3"
picture that is special to m = 9; at m = 12 labels live in ℤ/4).

1. **Slice decomposition** (Lean, unconditional, all m):
   `distStratum = ∑_{c⃗ ∈ (ℤ/u')³ pairwise distinct} conv3(slice_{c₁}, slice_{c₂}, slice_{c₃})`.
2. **Mode identity / Newton** (Lean, unconditional): in every DFT mode `a`,
   `D̂(a) = Ŝ(a)³ − 3·Ŝ(a)·P₂(a) + 2·P₃(a)`, with `Âc` the slice transforms,
   `Ŝ = ∑_c Âc`, `P_r = ∑_c Âc^r`.
3. **Parseval** (Lean, unconditional): `m·E_DIST = ∑_a ‖D̂(a)‖²`.
4. **Point-restricted form** (probe, exact): `Ŝ(a) = m·T₋ₐ + 1`,
   `T_α = ∑_{ind t ≡ α (m)} χ(1−t)` — each mode is an incomplete character sum
   over a coset of the index-m subgroup.
5. **The Fu–Wan-style averaged identity** (probe, exact, m = 9 and m = 12, all
   63 primes ≤ 1000, machine precision):
   `∑_{k∈(ℤ/m)^*} ‖T_α⁽ᵏ⁾‖² = ∑_{d∣m} d·μ(m/d)·N_d(α)`,
   `N_d(α) = #{(t,s) ∈ C_α², t,s ≠ 1 : (1−t)/(1−s) ∈ (F_q^*)^d}`, and the
   variety form `m²·d·N_d(α) = #{(x,y,z) ∈ (F_q^*)³ : 1−g^α x^m = (1−g^α y^m)·z^d}`
   verified by direct enumeration.  **The m = 9 integer phenomenon is exactly
   this: a Möbius-weighted point count on Fermat-type surfaces**, and it
   persists at m = 12 (averaged E integer at every probed prime).

## 2. The reduction (the Lean payoff, `_R302TraceFormulaPointCount.lean`)

Because each coset has only 3 elements, `‖Âc(a)‖ ≤ 3√q` UNCONDITIONALLY, so
`P₂, P₃` are already at target scale.  The whole open content of the r=3 rung
collapses onto one pointwise quadratic statement about the FULL DFT:

  `FullDFTFlat K : ∀ a, ‖Ŝ(a)‖ ≤ K·√(mq)`
  ⟹ `DistStratumEnergyBound ((K³ + 9K + 18)²)`
  (`distStratumEnergyBound_of_fullDFTFlat`, axiom-clean, general m = 3u').

Calibration (all Lean, unconditional): `K = √m` always holds
(`fullDFTFlat_sqrt_m` — recovers the baseline); Parseval pins the AVERAGE of
`‖Ŝ‖²` at ≤ m·q exactly (`hatSfun_energy_le` — flat-on-average, K = 1).  Probe:
`sup_a ‖Ŝ(a)‖²/(mq) ∈ [1.06, 4.7]` across all probed primes at BOTH m = 9 and
m = 12, flat in q.  A SEXTIC moment problem became a POINTWISE QUADRATIC bound
on one exponential sum of m Jacobi angles.

m = 12 calibration (first open instance): per-character `C_D ≤ 5.73`, averaged
`C_D ≤ 4.03` over 36 primes p ≡ 1 (12) ≤ 1000 — flat in q, comfortably inside
the conjectured O(1) regime.

## 3. Refutation-with-mechanism (the honest negative)

The Weil main terms of the point counts CANCEL IDENTICALLY:
`∑_{d∣m} μ(m/d) = 0` for m > 1, so the averaged mode energy is PURE error term
— no polynomial(q) main term survives, and the trace formula alone cannot
discharge the rung by "main term + Weil error": per mode, Weil's bound for
`∑_x χ(1−g^α x^m)` gives only `‖Ŝ(a)‖ ≤ (m−1)√q + O(1)`, i.e. `K = O(√m)` —
exactly the unconditional calibration, a factor √m from flat.  The open content
is square-root cancellation ACROSS the m Jacobi angles inside each mode
(Katz vertical equidistribution; see the R300 kb note).  We deliberately do NOT
name a sheaf-theoretic surrogate Prop — the honest Lean-side open objects are
`FullDFTFlat` ⟺ (up to explicit constants) `DistStratumEnergyBound`.

## 4. Formal kernel

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R302TraceFormulaPointCount.lean`
— axiom-clean (`[propext, Classical.choice, Quot.sound]`, no sorryAx),
pg-iterate 17s.  Theorems: `hatF_conv3`, `hatF_parseval` (self-contained DFT +
Parseval over ZMod N via `AddChar.sum_mulShift`), `exists_primitive_addChar`,
`label_eq_zero_iff`, `allCosetsDistinct_iff_labels` (kernel/label bridge),
`distStratum_slice_decomposition`, `newton_distinct_triple`,
`hatF_distStratum` (the mode identity), `distStratum_energy_spectral`,
`norm_hatSlice_le` (3-term slice envelope), `hatSfun_energy_le`,
`fullDFTFlat_sqrt_m`, `distStratumEnergyBound_of_fullDFTFlat` (the reduction).
New named open Prop: `FullDFTFlat` (instantiation-pinned by the calibration
theorems; NOT an axiom).

Probe: `scripts/probes/probe_466_r3_trace_formula_point_count.py`
(output `scripts/probes/_out_466_r3_trace_formula_point_count.txt`) — I1
spectral/Newton, I2 mode = point-restricted sum, I3 Möbius point-count average,
I4 variety enumeration: ALL VERIFIED at m = 9 (27 primes) and m = 12 (36
primes).

## 5. Session arc (R297 → R302) and next target

R300 localized the rung to `DistStratumEnergyBound`; R301 discharged m = 9 by
counting; R302 (this note) diagonalizes the stratum and reduces the general
rung to `FullDFTFlat`.  Next natural probe: per-mode decomposition of `Ŝ(a)`
into the m Jacobi sums `J(ψ', χ)` over the order-m character group and a
direct attack on sup-mode flatness (e.g. fourth-moment interpolation between
the Parseval average and the Weil sup — a `∑_a ‖Ŝ(a)‖⁴ ≤ K·m²·q²` input would
give `E ≤ C·m³·q³·√m`-type intermediate rungs).  CORE OPEN, ON-BGK.
No fabricated closure.

DISPROOF tag: `466-r3-trace-formula-point-count-flatness-reduction`.
