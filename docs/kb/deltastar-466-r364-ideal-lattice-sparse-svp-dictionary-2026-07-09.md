# #466 R364 — THEORY: the prize wall is sparse-short-vector avoidance in prime-ideal lattices of ℤ[ζ_{2^k}] (ideal-SVP dictionary)

## The dictionary (exact, from r305–r331 machinery)

For p ≡ 1 mod n, n = 2^k, fix g of order n and let
`L_p = {z ∈ ℤ^{φ(n)} : Σ z_j g^j ≡ 0 (mod p)}` — the evaluation kernel.
`L_p` IS the lattice of the prime ideal 𝔭 = (p, ζ−g) of ℤ[ζ_n]: determinant p,
dimension φ(n) = n/2. The r305/r308/r310 chain gives, exactly:

- depth-r collision surplus `S_r(p) = Σ_{z ∈ L_p \ {0}, z ∈ Z_r} M_r(z)` where `Z_r` = the
  difference-class support (ℓ₁(z) ≤ 2r, realizable as a difference of two r-sum shadows)
  and `M_r(z)` its pair mass;
- the moment tower / wall (WallHolds) ⟺ `S_r(p)` stays sub-Wick to r ≈ ln q — i.e. the
  prime-ideal lattice contains no heavy-mass SPARSE-AND-SHORT vectors up to sparsity 2 ln q.

## Why this is a real reframing (not relabeling)

1. **Minkowski forces short**: λ∞(L_p) ≤ p^{1/φ(n)}. At census scale this is ≤ 6 for every
   p ≤ 6^{φ(n)} — explaining r363's genericity finding (badness ≈ coin-flip 52%: a height-≤6
   kernel vector ALWAYS exists below the norm frontier; badness is whether its SHAPE lands
   in Z₃). At prize scale (n = 2³⁰, p ≈ 2¹⁵⁸): p^{1/2^29} < 1 + 10⁻⁶, so EVERY prize prime's
   ideal lattice contains nonzero {−1,0,1}-vectors. Short is unavoidable; the wall is
   entirely about SPARSITY (ℓ₀ ≤ 2r ≈ 316 out of 2^29 coordinates).
2. **The object is the Ring-LWE / ideal-SVP lattice**: prime ideals of the 2-power
   cyclotomic — the exact lattices of the post-quantum literature (ideal-SVP,
   Cramer–Ducas–Wesolowski, Ducas et al. average-case ideal results, sparse/ternary secret
   analyses). Two transfer directions to mine:
   - average-case ideal-lattice results over random split primes = the FS almost-all-primes
     rung derived from lattice geometry instead of resultant counting (possible constant
     improvements, different uniformity);
   - conversely, a PROOF of the wall for an explicit prime family = an explicit
     no-sparse-short-vector certificate for specific prime ideals — a statement the lattice
     literature considers hard-type; this calibrates which prime families could ever be
     provably good (and suggests the honest route: DESIGN the deployment prime as one whose
     𝔭-lattice provably avoids sparse vectors, e.g. via explicit Galois-equivariant
     constructions, rather than proving it for all/most primes).
3. **Probeable predictions** (next rounds):
   - census badness at n = 16/32 should equal "some ℓ∞-shortest vector of L_p lies in Z₃"
     — testable exactly by lattice enumeration at census scale (r365 candidate);
   - the violation magnitude should track the NUMBER of independent sparse short vectors
     (sublattice structure: the ζ⁵≡−3 web at p=(3¹⁶+1)/2 is a rank-1 relation module and its
     M-mass is the orbit closure of one vector — matches r305's collision-group readout);
   - deployment guidance: sparse-vector content of 𝔭 is computable for REAL deployment
     primes (BabyBear/KoalaBear-scale f) by enumeration — an explicit certificate lane.

## Honesty

This is a FRAMING theorem-schema plus verified-at-census-scale facts; it does not bound
S_r at prize scale. Its value: (a) explains r363's v₂-blindness and the 52% genericity
structurally (Minkowski), (b) connects the wall to a literature (ideal lattices) the
campaign has not yet mined, with concrete transfer targets in both directions. CORE OPEN,
ON-BGK.
