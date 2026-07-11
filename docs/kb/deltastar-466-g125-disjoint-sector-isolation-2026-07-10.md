# Issue #466/#505 G125: disjoint-sector isolation — the energy recursion with kernel constants

Date: 2026-07-11 (UTC)

Capstone of the G121→G123→G124 descent arc.

## Results (`Frontier/_G125DisjointSectorIsolation.lean`, 3 declarations, axiom-clean, 0 sorryAx)

- `factorial_mul_depthFiber_le` (near-diagonal LP row): for every `s ≤ r`,
  `(r−s)!·depthFiber A r s ≤ (r)_{r−s}²·#A^{r−s}·E_s(A)`. At `s = r−1` this is the sharp
  `fiber_{r−1} ≤ r²·#A·E_{r−1}` (one shared value, r² positions) — exactly where the G97
  shallow-oriented envelope was lossy.
- `depthFiber_le_energy_bound`: crude form for summation.
- `addREnergy_le_disjoint_add_descent` (**capstone**):
  `E_r(A) ≤ depthFiber A r r + Σ_{s<r} (r)_{r−s}²·#A^{r−s}·E_s(A)`.

## Reading

Every part of the 2r-th-moment object EXCEPT the fully-disjoint sector is bounded
unconditionally by lower-rung energies with explicit kernel constants. Through G96's weld,
`DCEnergyBound` at any prime reduces — up to these explicit descent terms — to bounding the
fully-disjoint equal-sum census `depthFiber A r r`. "The wall is disjoint-support
cancellation" is now one theorem chain, not a slogan.

## Honest scope

Descent constants are crude in the summed form; the disjoint sector itself is untouched
(the wall). CORE remains OPEN.
