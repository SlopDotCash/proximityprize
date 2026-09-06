# G101F stage 1 retention review

Retain `scripts/probes/_out_g101f_s1.txt` as a finite pencil-construction certificate table. The full stage s1 replay exited 0 and matched the archive after newline and elapsed-seconds normalization. The companion JSON records output, source hashes, and primes; independent trial division verified their primality.

The producer checks n = 16, 32, 64, 128, 256, k = 2, 4, and all levels k+2 <= a with a² <= nk, at two primes per n (only the first is printed). For selected j in [k,a) and d < k it verifies core size z = gcd(j-d,n), constructs B = floor((n-z)/(a-z)) disjoint blocks, and directly checks agreement at least a for every scalar 1 through B against codeword (1+gamma)x^d. Monomial farness follows from the stated degree bound j < a. The imported G92 self-test also passed.

These are lower bounds, not exhaustive worst-offset maxima. Fitted endpoint growth exponents are finite numerical summaries, not asymptotic proofs. The primes do not uniformly satisfy p >= n⁴. Stages s2, s2s and s3 were not replayed. No general Delta Star theorem is discharged.

One additional originally unreferenced artifact is reviewed: 61 of 92 reviewed, 31 remaining. The original inventory remains 420 retained and one removed, plus three restored runtime dependencies outside that inventory. Issue #2 remains incomplete.
