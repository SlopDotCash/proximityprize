# G101F stage three exact finite census

The complete stage s3 replay exited 0 and exactly reproduced the archive after normalizing newlines and elapsed seconds. Retain `scripts/probes/_out_g101f_s3.txt` as finite exhaustive evidence.

At n=8, k=2, p=17, agreement threshold four, the script checks all monomials x^j for 2 <= j < 8 and all coefficient-one pairs x^j+x^j′ in that range. It explicitly skips directions admitting agreement at least four. For each remaining direction, it exhausts all 17⁵ = 1419857 representatives modulo the span of constant, x, and that direction. The pivot rank is asserted to be three, and each maximizing offset is checked by the brute-force counting routine. The independent small-field quotient regression is documented in [the quotient audit](g101f-quotient-check-2026-09-06.md).

The far monomial maximum is nine for each of j=2,3,6,7; the largest coefficient-one pair maximum is twelve. Thus the maximum ratio in these enumerated classes at this one cell is 12/9. This is not a maximum over arbitrary direction coefficients or a general rate bound. In particular this field is outside p >= n⁴, and no production Delta Star theorem follows.

This archive is in the reconstructed original unreferenced baseline and had not previously been reviewed. The completed aggregate is now 64 of 92, with 28 remaining. Stages s2 and s2s remain separate unfinished reviews.
