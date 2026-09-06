# G139 arithmetic contract: leaf-prime verification — 2026-09-06

The old `is_prime_u64` tested only the first seven prime bases and accepted
341550071728321 = 10670053 * 32010157. Its advertised deterministic 64-bit
coverage was therefore false. The corrected helper tests the first twelve
prime bases and rejects inputs outside its documented range.

[Sorenson and Webster, Theorem 1.1](https://arxiv.org/abs/1509.00864)
gives the least composite passing those twelve bases as
318665857834031151167461, above 2^64. The leaf factors used by the fixed
recursive Pocklington certificate fall inside the enforced range.

All four regression checks pass: the explicit composite is rejected,
0..999 agrees with independent trial division, the upper range is rejected,
and the complete fixed arithmetic contract passes. The corrected default
CLI also passes its factorization, Pocklington and exact generator-order
checks. The companion JSON preserves its complete output.

The retained `_out_g139_n2e30_arithmetic_contract.txt` additionally reports
checking two supplied release JSON documents. Those documents were not
available in this replay, and the local repository release listing is empty.
The default replay correctly leaves those flags false and related fields
null. Neither checking their fields nor this arithmetic certificate reads
the 128 chunk binaries or independently re-establishes Phi injectivity.
The archived extended verification is not reproduced by this audit; the
retention-review count is unchanged.
