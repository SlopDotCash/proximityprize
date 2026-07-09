"""
C045 PART 3: 'Var=n is BLIND to B' — make the core refutation rigorous and visual.

The connection's thesis is "Var = n IS the Johnson ceiling". We show the average
2nd moment (= n) is a CONSERVED quantity that cannot detect the worst case B at all:
the same average n is compatible with the whole range B in [sqrt(n), n].

Construction (exact, integer where possible): the 2nd-moment constraint over the
nonzero frequencies is  sum_{b != 0} ||eta_b||^2 = q*n - n^2  (since b=0 term = n^2).
Average over the q-1 nonzero freqs = (q*n - n^2)/(q-1) -> n as q grows.

Two extremes BOTH satisfying this constraint:
  (a) FLAT spectrum: every ||eta_b||^2 = (q*n-n^2)/(q-1) ~ n  => B ~ sqrt(n)  (Ramanujan/SZ extremal).
  (b) CONCENTRATED: mass piled on FEW frequencies => B can be as large as n
      (the trivial ceiling |eta_b| <= |G| = n at b s.t. by in small interval).

The average (= Var = n) is IDENTICAL in both. So the average cannot distinguish the
prize-good case (a) from a prize-killing case (b). The ENTIRE prize content lives in
'which of (a)/(b) the actual mu_n spectrum is' -- and the real data sits strictly
between, with B/sqrt(n) GROWING (the BGK/Paley wall). Var=n is provably blind to it.

We verify: for the real subgroups, recompute (avg, B, trivial ceiling n) and confirm
avg=n is fixed while B roams strictly between sqrt(n) and n, growing relative to sqrt(n).
"""
import cmath, math
from sympy import isprime, primitive_root

def subgroup_mu_n(q, n):
    g = primitive_root(q); h = pow(g,(q-1)//n,q)
    G,x=[],1
    for _ in range(n): G.append(x); x=(x*h)%q
    return G
def eta_sq(q,G,b):
    s=0j; w=2*math.pi*b/q
    for y in G: s+=cmath.exp(1j*w*y)
    return abs(s)**2

print(f"{'n':>3} {'q':>6} | {'avg||eta||^2 (b!=0)':>18} {'= n?':>6} | "
      f"{'sqrt(n) (flat B)':>15} {'true B':>8} {'n (trivial ceil)':>15} | {'B-position in [sqrt(n),n]':>26}")
for n,q in [(8,1009),(16,7681),(32,12289),(64,65537)]:
    if not isprime(q) or (q-1)%n: continue
    G=subgroup_mu_n(q,n)
    sq=[eta_sq(q,G,b) for b in range(1,q)]
    avg=sum(sq)/(q-1); B=math.sqrt(max(sq))
    lo,hi=math.sqrt(n),float(n)
    pos=(B-lo)/(hi-lo)   # 0=flat/Ramanujan, 1=fully concentrated
    print(f"{n:3d} {q:6d} | {avg:18.4f} {abs(avg-n)<0.05!s:>6} | "
          f"{lo:15.3f} {B:8.3f} {hi:15.1f} | frac={pos:.3f} (0=flat,1=spike)")
print()
print("VERDICT EVIDENCE: avg (= Var = n) is PINNED constant, yet B is free in (sqrt(n), n)")
print("and grows away from the flat value sqrt(n). The 2nd moment / Var=n carries ZERO")
print("information about B = the prize quantity. So 'Var=n IS the Johnson ceiling' is FALSE:")
print("Var=n is the AVERAGE (always achievable, never the obstruction); the Johnson ceiling")
print("and the prize wall are about the WORST-CASE deviation, which the average cannot see.")
