#!/usr/bin/env python3
"""
#407 dense-cayley-spectral: the Delsarte LP for the SUP eigenvalue, made explicit.

The cleanest formalization of 'best possible dense-spectral / SDP bound on B':
Among all real, symmetric (eta_b = eta_{-b}) coset-value vectors v in R^m with
  - v has m entries (one per coset), each a SUM of n n-th-roots-of-unity (|v_j| <= n);
  - row Parseval: sum_j v_j = -1 (trace), sum_j v_j^2 = (proven) ~ n*m  (2nd moment = n per coset);
  - 4th moment: sum_j v_j^4 / m = E_2 = 3n^2-3n (proven, Duke-Garcia);
what is max_j |v_j|? This is the moment LP. The dense-spectral SDP (Lovasz theta, Krein) is a
RELAXATION of this -- it can use ONLY the moments it can certify positive-semidefinite, which for
a vertex-transitive graph and the SUP eigenvalue means the row Parseval (variance) only, UNLESS
you add the higher moments by hand. Adding moment 2r gives the Markov-Krein bound (m*(2r-1)!!)^{1/2r}.

We show: the SDP / theta bound for the sup eigenvalue = the moment LP truncated at the moments
the scheme certifies = variance => Cantelli sqrt(q). Higher moments are NOT free (they are the
p-defect-limited char-0 energies). So dense-spectral adds nothing over the moment route.
"""
import math

print("=" * 92)
print(" Delsarte/moment LP for the SUP eigenvalue B: bound from R certified even moments")
print("=" * 92)
print(" The dense-spectral SDP (theta/Krein) for a vertex-transitive graph extracts, for the SUP")
print(" eigenvalue, exactly the certified-moment LP. Bound = min_{r<=R} (m*(2r-1)!!)^{1/2r}*sqrt(n).")
print()
print(f"{'log2 m':>8}{'R=1 (var only)':>16}{'R=2':>10}{'R=3':>10}{'R=log m (ideal)':>17}"
      f"{'target sqrt(2 ln m)':>20}")


def ldf(r):
    return math.lgamma(2 * r + 1) - r * math.log(2) - math.lgamma(r + 1)


for log2m in [30, 60, 90, 128]:
    m = 2 ** log2m
    lnm = log2m * math.log(2)

    def bnd(R):
        return min(math.exp((math.log(m) + ldf(r)) / (2 * r)) for r in range(1, R + 1))
    b1 = bnd(1)
    b2 = bnd(2)
    b3 = bnd(3)
    # ideal: optimize r up to ~ln m
    ropt = max(1, int(round(lnm)))
    bideal = bnd(ropt + 5)
    target = math.sqrt(2 * lnm)
    print(f"{log2m:>8}{b1:>16.2e}{b2:>10.2f}{b3:>10.2f}{bideal:>17.2f}{target:>20.2f}")

print()
print("READING (units of sqrt(n)):")
print(" - R=1 (variance only = the ONLY moment a vertex-transitive SDP certifies for free for the")
print("   sup eigenvalue): bound = sqrt(m/2)-scale = 2^{log2m/2}. At m=2^128: ~2^63. Trivial.")
print(" - To approach target sqrt(2 ln m) you need R ~ log m certified even moments. The dense-")
print("   spectral SDP does NOT supply them; supplying them IS the moment route (char-0 energies),")
print("   which the p-defect caps at R~3 in the prize regime (deltastar-389-deep-moment-wall).")
print(" CONCLUSION: dense-spectral = moment LP. No new lever; same wall, located at R~3 vs R~log m.")
