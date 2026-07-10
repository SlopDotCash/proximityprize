# #466 R390 — every vanishing relation owns a resultant annihilator (census ⨝ FS ledger)

## What landed (axiom-clean, real locked build 3335 jobs)

`Frontier/_R390RelationResultantCertificate.lean`:

- `relPoly z = Σ_j z_j X^j` with coeff/nonzero/degree structure;
- **`aeval_relPoly`**: the shadow evaluation IS polynomial evaluation at `g`;
- **`relation_resultant_certificate`**: for `m = 2^k`, char `p`, `g^m = −1`, any vanishing
  nonzero relation forces `p ∣ patternResultant m (relPoly z)` with the resultant NONZERO
  (FS2's cyclotomic-irreducibility + common-root divisibility);
- **`sectorRelations_annihilator`**: every member of every r387/r389 sector owns such a
  nonzero integer annihilator divisible by `p`.

## The completed formal chain

wall scalar S (r331) = Σ_{z vanishing} M(z) (r389, exact), and each z in the sum has
N(z) := Res(X^m+1, relPoly z) ≠ 0 with p ∣ N(z) (r390). So which relations contribute at a
given prime is a pure divisibility question on a fixed family of nonzero integers — the FS1
(prime × pattern) double-count and the r305 census obstruction set, now welded end-to-end
to the moment tower with zero informal steps.

Remaining open at prize scale (stated honestly): the HEIGHT ledger (|N(z)| bounds feeding
divisor counting, FS3's remaining named input at this generality) and the uniform count of
contributing relations to r ≈ ln q at n = 2³⁰. CORE OPEN, ON-BGK.
