# δ* #407/#371 — the lacunary floor object carries a DIHEDRAL D_n symmetry (cyclic + Möbius reflection)

Date: 2026-06-14. Lens: symmetries. Status: NEW connection, numerically verified, NOT yet
Lean-formalized as a joint exploitation (the two halves live in separate files unconnected).

## The finding

The prize-floor object `lacBad(μ_n,a,t) = {e_t(S) : S⊆μ_n, |S|=a, e_1(S)=…=e_{t-1}(S)=0}`
(equivalently the char-0 lacunary index family `{I⊆Z/N : p_1(I)=…=p_{t-1}(I)=0}` of
`DyadicFourierUncertainty.powerSum`, identified via Newton's identities `p_j ↔ e_j`) is
**closed under the full dihedral group D_n**, not just the cyclic Z/n already exploited in-tree:

- **Cyclic half (proven in-tree, exploited):** dilation `x↦g·x` (`g∈μ_n`) acts via the
  e_t-homogeneity `e_t(g·S)=g^t·e_t(S)` (`DyadicLacunary.esymmF_image_mul`), giving
  `lacBad` closed under `γ↦g^t·γ` (`lacBad_smul_closed`); index-level = shift-closure
  `I↦I+c` (`DyadicFourierUncertainty.ShiftClosed`/`powerSum_vanish_of_shiftClosed`).
- **Reflection half (NEW, unexploited):** the Möbius involution σ: `x↦−x⁻¹` (= the RS
  GRS-duality automorphism, `MobiusMCASymmetry.badScalars_mobius_eq`) acts on `e_t` via
  the VERIFIED identity
      `e_t(σS) = (−1)^t · e_{a−t}(S)/e_a(S)`        (Vieta reversal × antipodal)
  hence σ **reflects the bottom-gap vanishing variety onto the top-gap variety**:
  `{e_1=…=e_{t−1}=0} ↦ {e_{a−1}=…=e_{a−t+1}=0}`. Index-level: `i ↦ N/2 − i`.

The two generators satisfy `σρσ = ρ⁻¹` (the dihedral relation) exactly on μ_n, and σ²=id,
and μ_n is closed under `x↦−x⁻¹` for every even n (so for all dyadic n=2^μ).

## Numerical verification (all machine-checked, this session)

- `scripts/probes/_wfU_symmetries_dihedral.py`:
  - dyadic fold `η_b(μ_{2n})=η_b(μ_n)+η_{bζ}(μ_n)` maxerr ~1e-15 (p=17..257).
  - `e_t(−S)=(−1)^t e_t(S)` exact 0.
  - dihedral relation `σρσ=ρ⁻¹` + σ²=id + closure: TRUE for all (p,n) tested
    (17/4, 13/6, 41/8, 41/10, 97/8, 241/16, 257/16).
  - `R_r(0)=E_r` (energy = diagonal autocorrelation mass) exact, and
    `max_z R_r(z)=R_r(0)` — so the proven `AutocorrelationMax.autocorr_le_autocorr_zero`
    cap `R_r(z)≤R_r(0)` IS literally "spurious mass ≤ energy".
- `scripts/probes/_wfU_symmetries_lacbad_dihedral.py`:
  - `e_t(S⁻¹)=e_{a−t}(S)/e_a(S)` and `e_t(σS)=(−1)^t e_{a−t}(S)/e_a(S)` maxerr ~7e-15.
  - σ bijects bottom-gap variety ↔ top-gap variety over F_p: TRUE all cases
    (41/8, 41/10, 97/8, 241/12, 241/16).
- `scripts/probes/_wfU_symmetries_index_reflection.py`:
  - reflection `i↦N/2−i` preserves the ENTIRE char-0 lacunary family at N=8,16, every
    (a,t); `reflClosed=True` always; explicit small fixed-point sets (free ↦ count even
    off the diagonal a=N).

## Leverage (why this could crack the floor)

1. **Search-space halving for `DyadicLacunaryFloor`.** The floor is "every window-interior
   direction `(a,b)=(k+t,k)` has `#lacBad≤C·n`". Under σ, direction (a, gap-t-at-bottom)
   ≡ direction (a, gap-t-at-top): the floor on a fundamental domain of D_n (≈ half the
   directions) implies it everywhere — the dihedral analogue of `MobiusMCASymmetry.
   windowRationalBounded_of_halfFamily` (which only halved the WB family, not the lacunary
   count). The two files are currently disconnected; wiring σ through `esymmF_image_mul` is
   a concrete formalization target.
2. **Forces even counts / parity obstruction.** Off the trivial diagonal a=N, the reflected
   family is fixed-point-poor, so the char-0 count `C(N/τ,a/τ)` decomposes into σ-orbits of
   size 2 — a parity constraint an adversarial bad-family must respect (sharpens the
   "O(1) cosets" floor target to "O(1) σ-orbit-pairs").
3. **Gauss-period side.** `η_b` is constant on μ_n-cosets (cyclic, `GaussPeriodCosetReduction.
   eta_constant_on_mulCoset`); the reflection b↦−b (antipodal) gives reality
   `conj η_b = η_{−b}` (cf. `DyadicHalvingRecursion.conj_eta_nthRoots`), so the (q−1)/n Gauss
   periods themselves carry the D_m action on the quotient F^×/μ_n — the period MAX `B` is a
   max over ≈ (q−1)/(2n) dihedral-orbit representatives, a further halving of the
   Kowalski–Untrau/Paley house.

## Honesty
All identities are numerically checked (maxerr ≤ 8e-15 or exact). The DIHEDRAL CLOSURE of
lacBad/the lacunary family is verified, not yet Lean-proven jointly. The floor itself
(`DyadicLacunaryFloor`) remains OPEN; this is a symmetry that shrinks its search/forces
parity, not a closure. The char-p transfer wall is unchanged.
