# G87V bounded census storage

The larger archive has cases with 18,123,840 rows; storing them as Python row arrays followed by a dense matrix creates unnecessary peak memory. The default producer now processes at most 4,096 census rows at once. After each batch it retains only a row basis modulo each of the three primes and intersects the common-root coverage masks. Replacing processed rows by a basis preserves the span; intersecting masks preserves the universal vanishing condition. Every support and sign pattern is still enumerated.

Twenty root cases, including empty censuses at n=4 and all n=8 roots for primes 17 and 41, match the original materialized implementation in size, all three ranks, and coverage. The regression also checks the batch-size cap. The larger full archive is not yet replayed under this implementation; no new retention completion or mathematical bound is claimed.
