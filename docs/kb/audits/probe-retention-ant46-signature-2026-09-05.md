# Retention mapping: ANT46 signature quotient — 2026-09-05

The full default replay of `scripts/probes/probe_ant46_signature_quotient.py`
exited zero and matched `scripts/probes/_out_ant46_signature_quotient.txt`
byte for byte. The adjacent JSON records hashes and output. These two artifacts
bring the original unreferenced mapping to 27 of 92, with 65 remaining.
No research artifacts are deleted.

The exact integer and modular arithmetic scan covers orders 4, 8, 16, 32, 64,
and 128, and primes at most 500000 satisfying p=1 mod n. Eligible-cell counts
are 20731, 10334, 5169, 2594, 1285, and 638. Positive collision counts occur in
1, 2, 6, 36, 114, and 250 cells respectively. All 409 positive-count cells
agree with independent direct pair enumeration. The script does not run that
independent enumeration at zero-count cells, so this replay alone is not an
independent exhaustive check of the absence of false negatives.

For every signature fibre of size k it computes k²−2k+s, where s counts the
self-inverse element. Witness assertions check subgroup membership, the additive
relation, and exclusion of the specified lawful cases. The finite examples
refute universal cleanliness and the proposed p>n³ shortcut. Divisibility by 12
is checked with the stated exclusion of −3 from the subgroup; the output gives
counterexamples when that exclusion is omitted.

For order 8, the probe evaluates K8 at all scanned inversion-class signatures
and factors its discriminant and self-value with integer trial division.
Eligible prime factors are exactly 17 and 41, matching the finite census.
These calculations retain useful obstruction evidence. They do not supply a
production-order certificate or independently revalidate the referenced Lean
theorem. The Delta Star production question remains open in issue #164.
