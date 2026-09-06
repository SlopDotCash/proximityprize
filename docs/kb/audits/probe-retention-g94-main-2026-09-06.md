# G94 metric archive review

Retain `scripts/probes/_out_g94_jacobi_cocycle_metric.txt` as numerical experimental output. The full current replay exited 0. Every line after the corrected introduction matches the archive, covering eight field instances and the lone-spike example. Independent trial division verified all eight field primes.

The source constructs greedy nets with sizes 1,4,16,256,65536 (capped at the number of points); its former documentation erroneously inserted size two. That docstring is corrected without changing the computation. As recorded in [the greedy-cost correction](g94-greedy-cost-correction-2026-09-06.md), the resulting cost does not compute the infimum over admissible nets or metrics.

The hard-zero diagnostic uses distance below 1e-12 and value difference above 1e-9; the domination ratio only uses distances above 1e-12. Accordingly, the computed rescaling is a floating-point diagnostic, not a certificate of the exact deterministic tail condition. Stieltjes recurrence, cocycle metrics and spacing checks are also numerical. Reproducing their printed digits does not certify the underlying exact quantities or prove the claimed general collapse theorem.

This archive is in the original unreferenced baseline; the source was already referenced. Its qualified retention review advances the corrected aggregate to 69 of 92, with 23 remaining. The production Delta Star theorem and issue #2 remain incomplete.
