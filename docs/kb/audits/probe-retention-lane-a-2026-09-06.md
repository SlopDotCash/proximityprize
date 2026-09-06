# Lane A exact wrap census retention audit

Retain `scripts/probes/_skeptic_466r10_laneA_spotcheck.py` as a finite diagnostic. This reviews one more of the original 92 unreferenced artifacts: 55 reviewed, 37 remaining. The inventory still retains 420 of 421 artifacts after the earlier print-only G104 removal.

The old characteristic-zero helper counted modulo one large prime without a faithful-reduction certificate. The corrected helper counts integer coordinate vectors modulo the dyadic cyclotomic polynomial `X^(n/2)+1`. Its basis has degree `n/2`, so equality of reduced vectors is equality in characteristic zero. Non-dyadic inputs are rejected. The wrap enumerator uses the same exact criterion; finite-field additive-energy counts remain independently computed by residue multiplicities.

The complete original and corrected replays both exit zero, and every numerical row is unchanged. At n=8, characteristic-zero energies are 168 (r=2) and 5120 (r=3). At primes 4129 and 4153 both tested wrap counts vanish. For r=3 at primes 17, 41, 73, 89, 97 the wrap counts are 10440, 3120, 480, 480, 480. Each agrees with the separate total-energy-minus-characteristic-zero calculation. Four regression tests cover the two-root binomial identity, opposite-root cancellation, domain rejection, and an actual extra-solution example modulo 17.

The output now distinguishes total additive energy from wrap count, which subtracts the characteristic-zero energy. Constant additive-character weights on modular zero-sum tuples do not exclude all other frequency-dependent statistics. The two sampled beta=4 primes do not establish a general no-wrap theorem. The reported Fourier magnitudes and normalized deviations remain floating-point quantities. No new Lean compilation, all-prime statement, or production spectral bound is claimed.

Replay: `python3 scripts/probes/_skeptic_466r10_laneA_spotcheck.py`. Tests: `python3 -m unittest discover -s scripts/tests -p test_lane_a_cyclotomic.py`. The companion JSON records the corrected source hash and full output.
