"""
C011 deeper audit: do W-anomaly and W-largesieve even use the SAME char-0 validity
threshold? The connection claims they share ONE root crossover. But the two in-tree
files state DIFFERENT thresholds for "E_r equals its char-0 value":

  CharSumMomentDeepWall:  valid for p > tau_r ~ n^{(r+3)/2}  <=> r < 2*log_n p - 3   [r_max]
  ManyTermResultantBound: valid for q > (2r)^{phi(n)} = (2r)^{n/2}                    [resultant]

These are radically different functions of (n,r). The resultant bound is a SUFFICIENT
(worst-case Hadamard) condition; the empirical tau_r ~ n^{(r+3)/2} is the ACTUAL onset.
The resultant threshold (2r)^{n/2} is MUCH larger (needs astronomically large q for any
fixed r once n is large), while the empirical n^{(r+3)/2} needs only polynomial q.

So the two walls have DIFFERENT crossover depths in n:
  - anomaly r_max(n,q) = 2*log_n q - 3            (independent of n's size beyond beta)
  - largesieve r_cap(n,q) = (1/2) q^{2/n}          (collapses to 1/2 as n grows)

Tabulate both as functions of (n,q) at the production beta to show they are not one number.
"""
import math
from sympy import isprime

def find_prime_q(n, beta):
    target = n**beta
    k = (target - 1 + n - 1)//n
    while True:
        q = 1 + k*n
        if q >= target and isprime(q):
            return q
        k += 1

print("Two char-0 validity caps as functions of (n, q=n^beta):")
print(f"{'mu':>3} {'beta':>4} {'r_max_anom=2b-3':>16} {'r_cap_largesieve':>17} "
      f"{'ratio':>10}")
print("-"*60)
for mu in [8,16,24,32]:
    n=2**mu
    for beta in [4,5]:
        q=find_prime_q(n,beta)
        r_max = 2*beta-3
        r_cap = 0.5*math.exp((2.0/n)*math.log(q))
        ratio = r_max/max(r_cap,1e-12)
        print(f"{mu:>3} {beta:>4} {r_max:>16.2f} {r_cap:>17.6f} {ratio:>10.2f}")

print()
print("They diverge: r_max_anom grows linearly in beta (5,7) and is INDEPENDENT of mu;")
print("r_cap_largesieve is ~1/2 for ALL prize n, INDEPENDENT of beta. The ratio r_max/r_cap")
print("grows without bound (10..14). They are NOT one common crossover r*~beta.")
print()
print("What IS shared (the honest residue): all three say 'needed depth ~ log q, reliable")
print("depth << that', so all three are VACUOUS at the prize and weld to the SAME wall (BGK")
print("square-root cancellation for thin mu_n). But that common SHORTFALL is qualitative;")
print("the quantitative 'one root crossover depth r*~beta=log_n q with deficit a/2' is FALSE:")
print("  - only W-anomaly has a crossover ~ beta (actually 2*beta-3), and its deficit IS a/2;")
print("  - W-largesieve crossover is O(1) (=1/2), deficit ~ q^{1-2/n} (NOT a/2);")
print("  - W-KU has no moment-depth crossover at all (it caps the subgroup SIZE d, not r).")
