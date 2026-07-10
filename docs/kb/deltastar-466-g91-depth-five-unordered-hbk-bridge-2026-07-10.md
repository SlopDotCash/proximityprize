# G91: depth-five unordered-core / HBK bridge

Date: 2026-07-10

Issue: #466
Branch: `research/proximity-prize`

## Result

G83's deliberately ordered primitive-core universe first exceeds the production Wick budget at depth five. The miss is not exponent-sized at the fixed saddle. It comes from counting internal endpoint order twice:

- G81C already stores two core-slot embeddings.
- A full-support depth-five core can therefore be stored as a multiset, with canonical order recovered before applying the embeddings.
- This removes `(5!)² = 14400` labels.
- The free subgroup action removes another factor `n`.

The remaining fixed-depth analytic estimate is classical. Fixing the three extra coordinates on each side gives

`E₅(G) ≤ n⁶ E₂(G)`.

The Heath-Brown--Konyagin literature input `E₂(G)² ≤ C n⁵` then gives `E₅(G)² ≤ C n¹⁷`. This is a fixed-depth energy theorem, not the forbidden `r ~ log q` moment wall.

`_G91DepthFiveUnorderedHBKBridge.lean` proves:

- `fifthEnergy_sq_le_of_secondEnergy`, the exact integer-exponent transport above;
- `production_depth_five_unordered_hbk_absorbed`, the production Wick consumer from `14400*n*J ≤ E₅`, `E₅² ≤ C n¹⁷`, and the deliberately loose `C ≤ 2²⁰`;
- `production_depth_five_unordered_of_secondEnergy`, the composed second-energy interface.

All inputs remain explicit. No production closure is claimed.

## Exact arithmetic

At `(n,r,s)=(2³⁰,110,5)`:

- G83's ordered-universe bound exceeds the exact full-Wick allowance by `260673.85...`.
- Internal-order quotient contributes `14400`.
- HBK contributes a `sqrt(n)=32768` saving.
- The consumer accepts an unsquared fifth-energy constant up to about `1810.15`, hence the formal squared allowance `C ≤ 2²⁰` is safe.

This changes the binding inequality at the first G83 cutoff: depth five is no longer arithmetically excluded once the decoder avoids redundant internal order.

## Exact probe

`python3 scripts/probes/probe_466_g91_depth5_unordered_core.py`

enumerates endpoint multisets, disjoint equal-sum pairs, and their exact ordered multiplicities.

- `n=8, p=257`: 424 multiset pairs, 167640 ordered pairs.
- `n=16, p=65537`: 2896 multiset pairs, 1455280 ordered pairs.
- `n=32, p=1048609`: 66688 multiset pairs, 484761600 ordered pairs.
- In the last maximal-2-adic beta-4 cell, the full-support stratum has 13952 multiset pairs and 200908800 ordered pairs, exactly ratio `(5!)² = 14400`.

The smaller cells have no full-support depth-five relations. Their relations have repeated coordinates, so they cannot be divided by `5!`; those must be routed into lower-support strata. This is the remaining combinatorial qualification.

## Honest residual

To turn G91 into an unconditional depth-five sector theorem:

1. tighten G87's landed surjective decoder from the ordered `CorePair A 5` codomain to canonical full-support multiset core pairs, so its two slot embeddings realize the `(5!)²` quotient rather than merely choosing canonical representatives inside an ordered ambient type;
2. split repeated-coordinate cores by support and absorb those lower-dimensional strata separately;
3. instantiate the cited HBK energy theorem, including its size/subfield hypotheses, or carry it as the existing named literature input.

The growing-depth union remains open and ON-BGK. G91 is fixed-depth frontier movement only.
