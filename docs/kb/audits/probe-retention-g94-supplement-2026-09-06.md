# Retention mapping: G94 numerical supplement — 2026-09-06

The baseline replay of `scripts/probes/probe_g94_jacobi_cocycle_metric_supplement.py`
matched `scripts/probes/_out_g94_jacobi_cocycle_metric_supplement.txt` byte for byte.
Both original artifacts remain retained. This brings the original unreferenced
artifact review to 34 of 92, with 58 remaining. The helper is recorded by hash
as a dependency; its full standalone experiment is not audited here.

The supplement uses NumPy cosine sums and floating-point Stieltjes recurrence
coefficients. It forms transfer-matrix features from the period values, then
measures numerical pair distances for (p,n)=(761,8) and (6529,16), comprising
95 and 408 cosets. In both cases, zero pairs satisfy the test |Delta eta|<1e-8.
The printed nan is therefore the explicit empty-set sentinel. It provides no
experimental example of vanishing distance on equal period values.

The smallest numerical spacings are 2.314e-3 and 2.573e-4. The largest printed
value-difference/distance ratios are 28.8 and 40.3. These are finite floating-point
diagnostics, without interval error bounds or exact algebraic equality checks.
The feature construction factors through the period value by definition; that
does not establish that distinct cosets have equal period values, or that the
metric is noninjective on either tested set.

The former header called this an exact-value degeneracy check, and the spacing
label claimed an injectivity obstruction. Both are corrected. A second complete
replay matches the baseline after replacing only those explanatory labels;
all printed numerical values are unchanged. The archive keeps its historical
wording for provenance. These experiments establish no universal obstruction,
production proximity-gap bound, or completion of issue #164.
