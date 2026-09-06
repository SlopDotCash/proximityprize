# Retention mapping: G97 finite moments — 2026-09-06

Both complete replays of `scripts/probes/probe_466_g97_census_sup_inflation.py`
passed. The revised output differs only in the label K(tol); every numerical
value is unchanged. This original unreferenced script remains retained, bringing
its review cohort to 35 of 92 mapped, with 57 remaining. The JSON records the
source hash, commands, parameters, and full output.

The six cells are (n,p)=(8,257),(16,257),(16,65537),(32,257),(32,193),(32,577).
Each is evaluated at moment depths 1 through 6. The computed zero-frequency
amplitude n exceeds the computed nonzero maximum in each cell. Counts within
1e-6 of that maximum are 8,16,16,32,32,32. The depth-six nonzero-moment-root to
maximum ratios are 1.2459,1.2613,1.4442,1.3349,1.3449,1.3450.

These are floating-point complex exponential sums. The tolerance count does
not establish exact maximum multiplicity or an exact orbit size. The original
header's exactness language and orbit label are corrected.

Separately, for a finite list of nonnegative amplitudes with exact positive
maximum M attained K>1 times, its 2r-moment sum is at least K*M^(2r), so its
unnormalized 2r-root is strictly above M at finite r. This elementary inequality
does not prevent useful upper bounds greater than M. For a fixed finite list
of q amplitudes, the root lies between M and q^(1/(2r))*M and converges to M as
r increases. The revised header therefore removes the blanket claim that a
census cannot reach the supremum. This replay does not certify exact census
identities, a uniform quantitative bound across growing fields, or issue #164.
