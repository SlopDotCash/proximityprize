# Transfer probe shift correction

The computation in `scripts/probes/probe_466r10_transfer_skeptic.py` uses `np.roll(A2, -1)`: the primitive-generator adjacent-coset shift. The former explanation incorrectly identified this with the dyadic subgroup tower step.

Write `m=(p-1)/n` and let `g` generate the multiplicative group. If m is even, the subgroup of order 2n splits as the subgroup of order n and its translate by `g^(m/2)`. Thus the corresponding coset-index shift is m/2, not 1 in general. If m is odd, a subgroup of order 2n does not exist in this field.

An independent exact set check at p=97, n=8, g=5 verifies that shift 6 produces the subgroup of order 16, whereas shift 1 does not. The generator order was checked by enumerating all 96 powers. The general decomposition follows directly by separating even and odd powers of `g^(m/2)`.

The reporting also now states that one mixed-moment equality does not prove independence or determination of the joint distribution by its marginals. The arithmetic and numerical loops are unchanged: an AST comparison with the parent commit, removing only docstrings and print statements, passes. Python compilation and whitespace checks pass.

The expensive full transfer replay and its archived output `scripts/probes/_out_466r10_transfer_skeptic.txt` have not been revalidated here. The archived tower interpretation is superseded by this correction. This is a source/reporting correction, not a completed retention review: the count remains 55 of 92 reviewed, with 37 remaining. It does not establish a production spectral bound or a general gauge reduction.
