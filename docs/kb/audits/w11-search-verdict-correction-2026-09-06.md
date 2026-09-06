# W11 search verdict correction

`probe_w11_c3_kill.py` formerly declared C=3 refuted when a spread witness exceeded three times the largest monomial count found by search. Its own documentation identifies the monomial result as a lower bound. A lower bound on the denominator cannot certify a lower bound on the ratio of the true maxima. For example, the archived spread value 38 and searched baseline 9 do not exclude a true monomial maximum of 13, for which 38<=3*13.

Both stage verdicts now report search separation with C=3 unresolved. Two observed sizes also cannot rule out every constant, so that asymptotic claim is removed. The sextic root argument is restricted to the degree-six family; it does not apply directly to the degree-14 and degree-30 directions.

The computational AST is unchanged after replacing string constants with placeholders. Python compilation and whitespace checks pass. The historical archive `scripts/probes/_out_w11_c3_kill_n16.txt` is preserved; its old refutation verdict is superseded by this correction. This audit does not independently replay the search, verify its spread certificates, or establish a monomial upper bound. Neither the source nor archive is counted as a newly completed retention review; the count remains 56/92.
