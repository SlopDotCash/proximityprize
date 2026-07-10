# #466 R389 — the census identity is now a Lean theorem: S = Σ_{z vanishing} M(z)

## What landed (axiom-clean, real locked build 3331 jobs)

`Frontier/_R389CensusIdentityExactFiber.lean`:

- **`classMass n m r z`**: the prime-independent char-0 pair mass of a difference class —
  `Σ_{v realized, v−z realized} NR(v)·NR(v−z)` (this is the census invariant `M(z)`);
- **`evalVec_sub`**: additivity of the shadow evaluation;
- **`fiberMass_eq_classMass`**: for a vanishing nonzero relation (`evalVec g m z = 0`),
  the collision fiber at difference `z` is the FULL realized difference class — both
  inclusions, via a `Finset.sum_nbij'` on `p ↦ p.1` — so the fiber mass equals `M(z)`
  EXACTLY;
- **`sectorMass_eq_sum_classMass`** / **`collisionMass_eq_sum_sum_classMass`**: the r387
  sector masses and the total collision mass are identified as sums of char-0 class masses
  over the vanishing relations.

## Why this is the sharpest brick of the arc

The r305 census formula `excess(p) = Σ_{z ≠ 0, z(g) ≡ 0 (p)} M(z)` — verified bit-exact
against every scan at n=16/32 — is now a THEOREM at every depth `r`, over every finite
field, with zero loss (it supersedes the r388 union bound, which stays as the counting
consumer). The r331 wall scalar `S` is no longer an analytic unknown but an identified
finite sum: prime-independent computable constants `M(z)`, indexed by exactly those sparse
relations that vanish at the prime — i.e. by the divisibility conditions `p ∣ Norm(z)` of
the FS resultant ledger.

Machine-checked chain, end to end: prize wall ⟺ moment tower (r43–r49) ⟺ collision mass
(r312) = Σ sectors (r387) = Σ_{vanishing z} M(z) (r389), with M(z) char-0 computable,
relations orbit-quantized (r371/r372), and each vanishing forcing p ∣ Norm(z) with bounded
height (FS ledger). The single remaining open object: which/how many sparse relations
vanish at the prize prime, uniformly to r ≈ ln q at n = 2³⁰. CORE OPEN, ON-BGK — but the
distance between the open core and a pure norm-divisibility statement is now zero
plumbing.
