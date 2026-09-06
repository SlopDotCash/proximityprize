# Transfer maximum storage

Stage C of `scripts/probes/probe_466r10_transfer_skeptic.py` needs only a maximum, but previously allocated representative and complex-value arrays across every coset. At its archived p=268437889, n=2 case this meant 134218944 representatives plus multiple arrays of that length.

`max_eta_complex_cosets` carries the running representative and maximum between batches. It visits the same g^i representatives for 0 <= i < (p-1)/n and uses the same modular products and trigonometric sums. It keeps at most 32768 representatives and caps each phase matrix at four million entries. The script now guards its experiments behind main so importing the functions does not start the full replay. Stages A/B still materialize their smaller arrays.

The regression test compares complete maxima against the original materialized computation for p=17,41,97,193 and n=2,4,8 using batch sizes 1,3,17,32768: all 48 comparisons are exactly equal. These include incomplete final batches. Invalid zero batch size is rejected.

The full replay has been started but is not yet verified. This change does not make floating-point maxima certified bounds, validate the historical tower interpretation, or complete a retention review. The reviewed artifact count remains 61 of 92.
