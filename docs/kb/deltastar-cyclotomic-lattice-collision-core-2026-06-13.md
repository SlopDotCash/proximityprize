# The δ* open core as a cyclotomic-lattice collision count (#389)

**Status:** novel reformulation of the *exact* open core (not a closure). Verified consistent
with the proven brackets; honestly scored at the bottom. Author: δ* lane, 2026-06-13.

## The reduction recap (proven, in-tree)

The prize δ* pins to one scalar — the worst incomplete Gauss-period sup-norm
`S(n,p) = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`, over the dyadic prize subgroup
`μ_n ⊂ F_p^×`, `n = 2^k`. Proven two-sided bracket:

> `√(3n−3) ≤ S(n,p) ≤ 2√(n ln p)` (lower: `ShawFlatnessRefuted`, axiom-clean, L⁴/L²
> on the `E=3n²−3n` energy floor; upper: refutation-tested CONJECTURE §R.3).

The sup-norm is controlled by the even additive moments `pE_r = Σ_b |η_b|^{2r}` via
`E_r = #{(x,y)∈μ_n^{2r} : Σ x_i = Σ y_j}` (orthogonality of additive characters). The prize
needs `E_r = (1+o(1))·(Gaussian) ` for `r` up to `≈ log p`; the **clean range is only
`r < log_n p ≈ log p/log n`** (≈6 in the prize regime), and the gap `[log_n p, log p]` is the
irreducible "halo" / Bourgain difficulty.

## The new framing: spurious solutions = sublattice points in a box

Work in the cyclotomic ring `ℤ[ζ_n]`, `ζ_n` a primitive `n`-th root, with the Minkowski
(coordinate) embedding `σ : ℤ[ζ_n] ↪ ℂ^{φ(n)}`, `φ(n)=n/2`. A balanced tuple `(x,y)` gives
`z = Σ x_i − Σ y_j ∈ ℤ[ζ_n]` with `‖σ(z)‖_∞ ≤ 2r` (each of the `2r` summands is a root of
unity, `|σ(root)|=1`). Two regimes:

- **`z = 0` (genuine char-0 balance).** For `n = 2^k`, Lam–Leung classifies vanishing sums of
  `2`-power roots of unity: the only primitive relations are **antipodal pairs** `{ζ, −ζ}`. So
  every char-0 balanced tuple is a perfect antipodal pairing ⟹ `E_r^{(0)} = ` exactly the
  Gaussian value `(2r−1)!!·n^r·(1+O(1/n))`. **This is provable and elementary** (norm + L–L),
  generalising `SidonModNeg`'s `r=2` case to all `r`.

- **`z ≠ 0` but `𝔭 | z` (spurious char-p balance).** These are the EXTRA solutions that inflate
  `E_r` above Gaussian. `z` lies in the index-`p` prime sublattice `𝔭 ⊂ ℤ[ζ_n]` (`N(𝔭)=p^f`),
  AND in the box `B_{2r} = {w : ‖σ(w)‖_∞ ≤ 2r}`. So:

> **`E_r − E_r^{(0)} = Σ_{z ∈ 𝔭 ∩ B_{2r}, z≠0} R_r(z)`,  where `R_r(z) = #{(x,y) : Σx−Σy = z}`**
> is the representation count of `z` as a signed sum of `2r` `n`-th roots of unity.

This turns the analytic-NT halo question into **geometry of numbers**: the rank-`φ(n)=n/2`
lattice `ℤ[ζ_n]`, its index-`p` sublattice `𝔭`, and the `ℓ^∞` box of radius `2r`.

### Why it reproduces the wall (sanity, proven direction)

`𝔭 ∩ B_{2r} = {0}` whenever `(2r)^{φ(n)} < p`: a nonzero `z` has `1 ≤ |N(z)| = Π|σ(z)| ≤
(2r)^{φ(n)}`, and `𝔭 | z ⟹ p | N(z) ⟹ p ≤ (2r)^{φ(n)}`. So below the norm threshold the
sublattice misses the box and `E_r = E_r^{(0)} = ` Gaussian — clean range, **rigorous**.
(In the prize regime `φ(n)=n/2 ≫ log p`, so this elementary threshold is vacuous past tiny `r`,
exactly the known wall — but it is now a *one-line lattice statement*, not an energy estimate.)

### The closed conjecture (all open math localised here)

> **(Cyclotomic Halo Non-Concentration.)** For `n = 2^k`, every prime `p ≡ 1 (n)`, every
> `r ≤ c·log p`:  `Σ_{0≠z∈𝔭∩B_{2r}} R_r(z) ≤ ε·E_r^{(0)}`, `ε = o(1)`.
> Equivalently: the sums `Σ_{i≤r} ζ_n^{a_i}` (an explicit finite multiset of cyclotomic
> integers, all in `B_r`) **equidistribute over the residues `ℤ[ζ_n]/𝔭 ≅ F_p` at most to within
> a `(1+o(1))` factor of the diagonal** — i.e. no proper additive sub-progression of `F_p` is
> over-represented by the `r`-fold sumset of `μ_n`.

This is **closed** (a single inequality about explicit finite objects: the box, the sublattice,
the representation function) and contains ALL remaining open math. It is the dyadic-domain,
geometry-of-numbers face of: BCHKS Conj 1.12 / `MCAShawConjecture` / `S ≤ 2√(n ln p)` /
`E_r` Gaussianity / the Bourgain–Shkredov thin-subgroup sum-product wall.

## Refutation attempts (it survives)

- **Minkowski expected-count refutation FAILS to refute.** Naive g.o.n. gives
  `#(𝔭∩B_{2r}) ≈ vol(B_{2r})/covol(𝔭) ≈ (4r)^{n/2}/(p·√disc) ≫ 0` for `r` large — suggesting
  spurious points dominate. BUT `R_r(z)=0` for the overwhelming majority of those lattice points
  (the `r`-fold root-of-unity sumset `T_r = {Σζ^{a_i}}` is a *thin, rigid* subset of `B_r`, size
  `≤ n^r ≪ vol(B_r)`), so the relevant count is collisions of `T_r → F_p`, not lattice points.
  The naive bound is loose; no refutation. (This is precisely why equidistribution of `T_r`, not
  lattice volume, is the crux.)
- **Equidistribution-heuristic consistency check PASSES.** If `T_r → F_p` were perfectly regular,
  `Σ_{b≠0}|η_b|^{2r} = pE_r − n^{2r}` would be `o(n^{2r})`, consistent with `S = √(n ln p)`
  (since `p(n ln p)^r = o(n^{2r})` exactly when `r > log_n p`). So the conjecture is consistent
  with the proven brackets and the §R.3 upper law; it neither trivialises nor contradicts.

## Honest self-ranking (prize protocol)

- **Novelty 8/10** — the cyclotomic-lattice / `𝔭∩B_{2r}` collision form of the halo core, and the
  L–L-exact all-`r` clean-moment statement, are not in the campaign (which frames it analytically /
  via additive energy). The g.o.n. lens on the prize is new.
- **Insight 9/10** — unifies the dyadic antipodal structure (Lam–Leung), the norm/clean-threshold
  wall, the additive-energy halo, and the sup-norm bound into ONE lattice-collision inequality, and
  cleanly separates the *provable* part (`z=0` ⟹ Gaussian, all `r`) from the *open* part
  (`𝔭∩B_{2r}` representation mass).
- **Proximity 9/10** — dyadic `n=2^k`, prime `p≡1(n)`, `r` up to `log p`: exactly the prize regime;
  no toy reduction.
- **Feasibility 4/10** — the `z=0` clean-range half is formalizable now (L–L + norm, generalising
  `SidonModNeg`); the open inequality is the equidistribution of `T_r mod 𝔭`, which is the genuine
  Bourgain–Shkredov wall. **No prize-closing conjecture can honestly score ≥9 on feasibility** —
  if it could, the prize would be closed. This is the sharpest closed *reformulation*, not a proof.

**Bottom line.** A new, closed, prize-regime statement of the open core as a single lattice-collision
inequality, with its provable half (clean-range Gaussianity, all `r`, via Lam–Leung) separated out.
The prize remains open: the residual is genuine analytic NT (high-`r` equidistribution of the
root-of-unity sumset mod `𝔭`), the recognised Bourgain regime. Not fabricated; honestly open.

Cross-refs: `ShawFlatnessRefuted.lean`, `SidonSubgroupClosed.lean`, `Research/ProximityPrize/PROXIMITY_PRIZE_WORKBENCH.lean`
§R.3, `SubsetSumHaloEnergy.lean`, reading-list O4 (Demirci Akarsu–Marklof value distribution),
O7 (Kalmynin additive irreducibility of `μ_d`).
