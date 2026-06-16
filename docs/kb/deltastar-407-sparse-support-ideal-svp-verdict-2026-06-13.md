# δ* (#407) — sparse-support ideal-SVP angle: SVP-min IS sparse ⟹ reconfirms the wall

**Status:** assigned-angle assault (`ideal-svp-split-newangle`), settled. **No closure**; one
genuinely-new axiom-clean *house lower bound* landed; the sparse-support sub-count is shown
(numerically, with a rigorous companion bound) to **coincide** with the full box/ideal-SVP count, so
support sparsity gives **nothing** beyond the exhausted norm-bound + well-roundedness walls. Author:
#407 ideal-svp-split lane, 2026-06-13. Honesty contract holds.

## The object and the four levers tested

Prize regime: `μ_n ⊂ F_q^×`, `n = 2^μ` (μ≤40), `q ≡ 1 (n)`, index `m = (q-1)/n ≈ 2^128` HELD
CONSTANT. The fully-split prime `𝔭 | p` of `ℤ[ζ_n]` has residue degree 1, `N(𝔭) = p`. A depth-`r`
additive-energy defect is a nonzero `α = Σ_{i≤r} ζ^{a_i} − Σ_{j≤r} ζ^{b_j} ∈ 𝔭` — a **signed sum of
≤ 2r roots of unity** (`ℓ^1 ≤ 2r` in the GROUP-RING basis `ℤ^n`).

Assigned NEW levers (beyond norm-bound + well-roundedness, both exhausted): **(a)** dual lattice +
transference exploiting SPARSE support; **(b)** CVP/BDD; **(c)** explicit basis `(p, ζ−z)` Gram;
**(d)** theta-series / modularity. Central question: can ANY bound the **sparse-support** sub-count
`T(r,p) = #{0≠z∈𝔭 : z = signed sum of ≤2r roots}` strictly BELOW the **full box** count
`F(r,p) = #{0≠z∈𝔭 : ‖σ(z)‖_∞ ≤ 2r}` in-regime?

## What was measured (reproducible probes)

- `probe_407_sparse_support_ideal_svp.py` — T vs F vs representation mass. At onset, `T·p/|T_r| =
  33–578 ≫ 1`: sparse defects are a STRUCTURED EXCESS over random density 1/p (not a deficit).
- `probe_407_sparse_defect_structure.py` — **the structure of the excess.** At the onset depth the
  ENTIRE sparse-defect set is a SINGLE automorphism orbit (`ℤ/n` rotation × Galois `(ℤ/n)^×`) of ONE
  minimal-house vector of `𝔭`, of norm exactly `p` (or small fixed `2p, 4p`). min-house does NOT grow
  with `r` (n=32: 5.108 at both r=4,5) — deeper defects are the SVP-min padded by balanced 0-pairs.
- `probe_407_sparse_vs_lattice_svp.py` — **the crux.** The LATTICE SVP-min of `𝔭` in the house
  (`ℓ^∞`-Minkowski) norm is **already sparse**: its power-basis `ℓ^1` is `8–13` (n=16..64), i.e.
  realizable as a signed sum of `≤2r` roots with `r=4–7`. `h_lat` (LLL) = `h_sparse` (MITM) at every
  cross-checkable `(n,β)`. **Support sparsity does NOT lengthen the shortest vector.**
- `probe_407_house_min_law.py` — `h_lat ≈ 4.5–5.7` at n=64,128 (β=4,5); empirical
  `h_lat ~ 15.5·n^{−0.28}` (β=4) — **bounded/shrinking, NOT `√n`**; `h_lat/Mink_∞ ∈ [0.42,0.68]`
  STABLE ⟹ theta count two-sided pinned (no loose-upper rescue).
- `probe_407_dual_transference.py` — `λ_n/λ_1 → 1.0…1.38` (≈ well-rounded, Fukshansky-Petersen);
  Banaszczyk product `λ_1·λ_1^* ∈ [1.18, 2.85]` (small end of `[1,n]`); transference lower bound
  `1/λ_n^*` captures 28–84% of `λ_1` — **valid but tight, no rescue** beyond the Minkowski value.

## The genuinely-new rigorous result (axiom-clean, landed)

`ArkLib/.../Frontier/SparseSupportIdealSVPLowerBound.lean` (compiles, axioms `[propext,
Classical.choice, Quot.sound]`), the **house LOWER bound** — companion to the existing norm-defect
*upper* threshold:

> For any defect `α = g(ζ_n) ∈ 𝔭` (char-0 nonzero, `≡0 mod 𝔭`): `house(α)^{φ(n)} ≥ |N(α)| ≥ p`,
> hence `house(α) ≥ p^{1/φ(n)}`.  (`prime_le_house_pow_of_cyclotomic_defect`,
> `house_ge_of_cyclotomic_defect`.)

Proof = AM-GM (`|Res(Φ_n,g)| = ∏_ω|g(ω)| ≤ house^{φ}`) ∘ `p`-divisibility + nonvanishing (reused
from `CyclotomicNormDefectThreshold.lean`). With the upper bound `house(α) ≤ 2r` (sparse), a defect
needs `p^{1/φ(n)} ≤ 2r`, i.e. `p ≤ (2r)^{φ(n)}` (`sparse_defect_onset`) — **the IDENTICAL onset as
the box/norm threshold**. This is the formal statement of "sparse-support onset = box onset".

## Verdict: `reconfirms_wall` (and slightly STRENGTHENS the project's understanding)

The sparse-support angle is **dead as a lever**, for a clean structural reason now pinned both
numerically and (the lower half) rigorously: the SVP-min of `𝔭` is sparse, so the box count and the
sparse sub-count have the **same** SVP minimum, the **same** onset `(2r)^{φ(n)} ≥ p`, and (being
≈well-rounded with tight transference) the **same** two-sided theta pin. None of the four levers
(dual/transference, CVP, Gram, theta) separates `T` from `F`.

Net contribution: (1) the new axiom-clean `house ≥ p^{1/φ(n)}` lower bound (the ideal-SVP/Minkowski
floor, dual to the norm threshold); (2) the rigorous identification that the open core is NOT a
short-vector-existence question (the SVP-min is sparse and bounded-house, defects flood at `r=O(1)`
in-regime) but purely the **representation MASS of the bounded-house SVP-min orbit** — i.e. exactly
the `Σ_z R_r(z)` / `max_b|η_b|` equidistribution wall the rest of the campaign localizes. The
bounded (non-`√n`) house of the SVP-min explains WHY defects appear at `r=O(1)` (norm threshold
vacuous) yet `B = max|η_b|` stays `√(n log)` — the mass, not the existence, is the wall.

**In-regime vacuity (honest):** `house ≥ p^{1/φ(n)} = p^{2/n} → 1` in the prize regime (`φ=n/2`),
so the lower bound certifies nothing past the dyadic floor `house ≥ √2`. A real partial bound with
its exact regime, NOT a closure.

## cross_path_lever

The bounded-house, sparse, ≈well-rounded SVP-min orbit means the residual is **mass-on-a-fixed-orbit**:
`E_r − E_r^(0) = Σ_{z ∈ Orbit(α_0)} R_r(z)` where `α_0` is the (few) SVP-min element(s) and `Orbit`
is `ℤ/n × Galois × (balanced-0-pad)`. This is a SHARPER target than the general cyclotomic-halo
non-concentration: it suffices to bound `R_r(α_0)` for the SINGLE shortest sparse defect (and its
`O(n·φ)` images), since deeper-`r` mass is dominated by padding that orbit. Feeds: the
Gauss-period-house lane (`B = max over m Gauss periods`), the tangent-autocorrelation Jacobi-average
lane, and the cumulant-deep-moment lane — all of which need exactly `R_r` of the extremal `z`.

Cross-refs: `CyclotomicNormDefectThreshold.lean`, `SparseSupportIdealSVPLowerBound.lean` (NEW),
`deltastar-cyclotomic-lattice-collision-core-2026-06-13.md`,
`deltastar-407-markovkrein-and-selfimprove-walls-2026-06-13.md`,
`arklib-407-gauss-period-house`, Habegger 1611.07287 (norm-of-period = geometric mean, archimedean),
Untrau 2112.05441 (fixed-index equidistribution = distribution not extreme value), GLT 2112.13886.
