# FSMF m=10 complete census

Retain the m=10 producer and `scripts/probes/_out_fsmf_m10_threeline.txt`. The current `--full` replay exited 0 and checked all 641 scalars for the fixed n=160,k=40,t=89 construction. Exactly 155 scalars are bad, and all are already in the witness-level set. The complete output and hashes are in the companion JSON.

The historical archive checked the 155 witnessed scalars and only 38 non-witness scalars. Its total-count and holds fields therefore overstated the evidence then available. Its prediction of 154 was also wrong. The earlier reporting correction preserves sampled results as lower bounds; this new complete run independently establishes 155 and 155 <= 160 for this construction. The archive is retained with these qualifications, not treated as an exact full-run transcript.

Independent arithmetic verifies that 641 is prime and that the multiplicity-two interpolation uses 500 monomials for 480 constraints, with weighted degree at most 177 < 2*89. The producer verifies a nonzero kernel vector over exact integers, enumerates candidate polynomial roots, and directly checks agreements and whether each support has a joint explanation. The decoder's independent exhaustive small-field regression is recorded in [the decoder audit](fsmf-decoder-check-2026-09-06.md).

This is a complete scalar census for one fixed pair of words, not an optimization over all words, a production-scale inequality, or a Delta Star proof. Both the source and archive are in the original unreferenced baseline. Their completed reviews advance the corrected aggregate from 66 to 68 of 92, with 24 remaining.
