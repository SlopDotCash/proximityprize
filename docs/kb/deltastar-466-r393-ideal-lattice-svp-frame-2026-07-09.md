# #466 R393 — the ideal-lattice/Ring-SIS frame: the prize wall as an ℓ∞-SVP statement

## The synthesis (creative frame; formal anchor landed)

A realized vanishing relation is a nonzero `z ∈ ℤ^m`, `ℓ∞(z) ≤ 2r`, with
`Σ z_j g^j ≡ 0 (mod p)`. In lattice language: `z` is a short vector of the rank-`m`
modular lattice

```text
L_g = ker(evalVec) = { z ∈ ℤ^m : Z(g) ≡ 0 mod p } = the ideal ⟨X − g, p⟩ in ℤ[X]/(X^m+1)
```

— literally the NTRU/Ring-SIS one-sample ideal lattice of lattice cryptography, with
`det(L_g) = p` (prime field; evaluation is surjective since g ≠ 0). The landed brick
`_R393KernelIdealLatticeFrame.lean` (axiom-clean) anchors this:
`evalVecHom` (the evaluation as an additive hom), `sectorRelations_mem_ker`,
`sectorRelations_linf_le`, and the SVP-type consumer
**`relationCount_zero_of_no_short_kernel`**: no nonzero kernel vector of `ℓ∞ ≤ 2r` ⟹
`RealizedRelationCountBound g n m r 0` ⟹ (r392) unconditional char-0 moment control.

## What the frame explains (cross-checked against the census)

- **Gaussian heuristic**: `λ₁(L_g) ≈ √(m/2πe)·p^{1/m}`. At prize parameters
  (m = 2²⁹, p ≈ 2¹⁵⁸): `p^{1/m} ≈ 1`, so `λ₁ ≈ √m ≈ 2^{14.5}` (ℓ2), while relations need
  `ℓ∞ ≤ 2r ≈ 220` with ℓ1 ≤ 2r — far BELOW the heuristic minimum. Generic prediction:
  K = 0 at prize shape — matching the census (bad primes are rare and structured).
- **Bad primes = exceptional short vectors**: p = (3¹⁶+1)/2 has the short kernel vector
  `3·e₀ + e₅`-type (ζ⁵ ≡ −3) — exactly a `c + ζ^j` short vector of the ideal lattice;
  the whole r305 obstruction census is the catalogue of ideal lattices ⟨X−g, p⟩ with
  anomalously short vectors, i.e. the "weak instances" of Ring-SIS folklore.
- **The rotation orbit law (r371/r372)** is the standard ideal-lattice symmetry: the
  lattice is closed under multiplication by X (rotation with sign wrap), so short vectors
  come in n-orbits — same statement, two literatures.

## Honest limits (why this is a frame, not a proof)

Lattice cryptography ASSUMES no efficient algorithm FINDS short vectors; it does not prove
their nonexistence — worst-case-to-average-case reductions (Ajtai, Lyubashevsky–Micciancio)
go the wrong direction for us, and for STRUCTURED instances (our g is not random: it is
determined by p and the subgroup) no existence lower bound is known. Proving
`λ₁^{ℓ∞}(⟨X − g, p⟩) > 2r` for the explicit prize primes IS the wall in yet another
costume — but this costume has 25 years of lattice-crypto cryptanalysis tooling
(LLL/BKZ certification at small m, volume arguments, Galois-invariance constraints), a
concrete transfer surface the campaign did not previously have. Actionable next probes:
(i) certify λ₁ for deployment-scale instances (BabyBear/KoalaBear f-lattices) by exact
enumeration/BKZ — an unconditional per-instance K = 0 certificate path;
(ii) the Galois/trace obstruction: short vectors of ⟨X−g,p⟩ give small-norm elements of
the ideal, whose relative norms are constrained — the FS height ledger from the other side.

CORE OPEN, ON-BGK — now with the ideal-lattice SVP dictionary attached and the K = 0
sufficient condition machine-checked.
