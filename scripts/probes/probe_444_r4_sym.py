"""
Check dilation/translation symmetry of the (e,f)-census so the n=32/64 sweep is tractable.

Claim to test: census(#bad, O_P) for line (x^e, x^f) on mu_n depends only on
the UNORDERED multiset {e mod n, f mod n} up to a SHIFT? Specifically test:
  (a) (e,f) vs (f,e): swapping -> gamma -> 1/gamma bijection, same #bad, same O_P.
  (b) (e,f) vs (e+t, f+t) mod n: multiply both witnesses by x^t. On mu_n, x^t is a
      unit-modulus dilation char; does it preserve the bad set count? Test empirically.
  (c) (e,f) vs (-e,-f) mod n (inversion x->x^{-1} on mu_n).
If (b) holds, we only sweep representatives with e fixed (say e in a small set) -> n-fold cut.
"""
import itertools
from math import comb, gcd
from collections import Counter
import sys
sys.path.insert(0, 'scripts/probes')
from probe_444_r4_truemax import w_of_order, census_line, p

def quick(n, r, e, f, mu):
    nz, zb, op, K, _ = census_line(n, r, e % n, f % n, mu)
    return (nz, int(zb), op)

n = 16; r = 4
mu = [pow(w_of_order(n), i, p) for i in range(n)]
base = (8, 5)
print("base (e,f)=", base, "->", quick(n, r, base[0], base[1], mu))
print("swap (f,e)=", (5, 8), "->", quick(n, r, 5, 8, mu))
print("--- translation (e+t,f+t) ---")
for t in range(n):
    print(f"  t={t}: ({(8+t)%n},{(5+t)%n}) -> {quick(n,r,8+t,5+t,mu)}")
print("--- inversion (-e,-f) ---")
print("  (-8,-5)=", ((-8)%n,(-5)%n), "->", quick(n, r, -8, -5, mu))
