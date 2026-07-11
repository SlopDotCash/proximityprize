# #466 r=3 R304: Fermat fiber products — per-variety Weil–Deligne is a NO-GO
# (Betti ceiling = the unconditional K₄ = O(m) at EVERY q, prize scale
# included); exact diagonal extraction landed; new O(1)-calibrated input
# `OffDiagQuadrupleBound` (2026-07-10)

Eighth brick of the r=3 session (R297 → R304).  Coordinator target: express
the off-diagonal 4th moment as Möbius-weighted Fermat-fiber-product point
counts with main + `B(m)·q^{3/2}` error, and check whether polynomial `B(m)`
makes the 4th-moment rung UNCONDITIONAL at prize scale `q ≈ n·2¹²⁸`.

## 1. The geometry, exact (probe-verified)

Two exact identities (probe `probe_466_r3_fermat_fiber_product.py`):

* **V1 (torus form, direct (t,x,y,z) enumeration)**: per character,
  `m³·∑_α‖T_α‖⁴ = ∑_{t,x,y,z ∈ (F_q^*)⁴} χ((1−t)(1−t·x^m)/((1−t·y^m)(1−t·z^m)))`
  — ONE complete χ-sum over a fixed 4-dimensional torus.  Verified to 1e-11
  at m = 9, 12, 15, 18.
* **V2 (Möbius/point-count form)**: Galois-averaged,
  `∑_k ∑_α‖T_α‖⁴ = ∑_{d∣m} d·μ(m/d)·N₄_d`, `m³·d·N₄_d = #V_d(F_q)` for the
  dim-4 hypersurfaces
  `V_d = {(t,x,y,z,w) ∈ 𝔾_m⁵ : (1−t)(1−t x^m) = (1−t y^m)(1−t z^m)·w^d}`.
  Verified exactly at m = 9, 12 over p ≤ 199.

## 2. THE NO-GO (refutation of the prize-scale hope, with mechanism + numbers)

* The top strata `N₄_d ≈ q⁴/(m³d)` CANCEL under `∑ d·μ(m/d)` — same Möbius
  mechanism as the sextic.  The surviving signal is `q²`-scale
  (measured `signal/q² ∈ [0.35, 0.66]`).
* Each individual `N₄_d` fluctuates at the `q^{7/2}` Weil scale of a 4-fold's
  middle cohomology — measured `|N₄_d − main|/(q^{3.5}/(m³d)) = O(1)`
  (0.5–7 across strata/primes).  **The per-variety errors sit two orders in
  √q ABOVE the signal and never decay relative to it** — there is NO
  main + `B·q^{3/2}` split, hence NO q-threshold and NO unconditional
  prize-scale discharge.  A `FermatFiberErrorBound` Prop would be false at
  the useful scale; none is named.
* Equivalent χ-sum view: the 4-torus sum is PURE middle weight; its
  Betti/Adolphson–Sperber ceiling `4!Vol(Δ) ~ m³` gives
  `∑_α‖T_α‖⁴ ≤ C·q²`, i.e. exactly `K₄ = O(m)` — the triangle-inequality
  calibration.  Measured: `|torus sum|/q² ≈ m²` (m=9: 65–79 vs m² = 81;
  m=12: 112–147 vs 144; m=15: 263 vs 225; m=18: 275–396 vs 324) — the truth
  sits ONE full factor `m` below the Betti ceiling: the missing factor is
  family-level cancellation across the `m³` character tuples (Katz vertical
  territory), invisible to fixed-variety point counting.

## 3. What IS landed (axiom-clean): exact diagonal extraction + new input

The diagonal (`{j₁,j₂} = {k₁,k₂}`, ratio ≡ 1, Möbius weight φ(m)) is priced
EXACTLY: `diagR = 2(∑_{j≠0}‖J_j‖²)² − ∑_{j≠0}‖J_j‖⁴`, with
`0 ≤ diagR ≤ 2m²q²` unconditionally.  New named input:

  `OffDiagQuadrupleBound K : ‖quadTotalC − diagR‖ ≤ K·m²·q²`

* probe (V4): `K_off ≤ 1.21` max, median ≈ 0.25, at m = 9/12/15/18, flat in q;
* reduction: `OffDiagQuadrupleBound K ⟹ FourthMomentBound (2 + K)`
  (`fourthMomentBound_of_offDiagQuadruple`);
* calibration: `K = m + 2` unconditional (`offDiagQuadrupleBound_unconditional`)
  — exactly the fixed-variety Weil–Deligne ceiling, as it must be.

Full graded ladder of the r=3 rung after R302–R304:
`OffDiagQuadrupleBound K (O(1) calib.) ⟹ FourthMomentBound (2+K)
⟹ DistStratumEnergyBound (O((2+K)^{3/2})·√m)`; lossless route stays
`FullDFTFlat`.  Every remaining open input is a cross-term cancellation
statement about the Jacobi angle family — the geometry is exhausted.

## 4. Formal kernel and probe

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R304FermatFiberProduct.lean`
— axiom-clean (`[propext, Classical.choice, Quot.sound]`, no sorryAx),
pg-iterate 10s.  Theorems: `quadTotalC_eq_energy`, `sum_sq_le`,
`sum_pow4_le_sq`, `diagR_nonneg`, `diagR_le`,
`fourthMomentBound_of_offDiagQuadruple`, `offDiagQuadrupleBound_unconditional`.

Probe: `scripts/probes/probe_466_r3_fermat_fiber_product.py`
(`scripts/probes/_out_466_r3_fermat_fiber_product.txt`).

## 5. Status

The point-count/variety program for the r=3 rung is now CLOSED with a
two-sided verdict: exact identities all the way down (V1/V2, plus R302's
I2/I3 and R303's F1), but fixed-variety Weil–Deligne provably tops out at the
unconditional calibrations (`K₄ = O(m)`, `K_off = O(m)`); the open content at
every level of the ladder is the SAME phenomenon — square-root cancellation
across the Jacobi-angle family (Katz vertical equidistribution), now isolated
in its weakest form as `OffDiagQuadrupleBound = O(1)`.  CORE OPEN, ON-BGK.
No fabricated closure.

DISPROOF tag: `466-r3-fermat-fiber-product-pervariety-nogo`.
