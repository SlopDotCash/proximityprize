# Part 8: odd-moment negativity (F13/C076): Sum_i eta_i^{2k+1} = -n^{2k}  (exact, all r)
# and clarify kurtosis direction (char-0 Bessel value vs char-p; "platykurtic" wrt WHAT ref)
import cmath, math
from collections import Counter

def primitive_root(p):
    phi=p-1; fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fac): return g

def periods(p,n):
    g=primitive_root(p); sub=sorted({pow(g,((p-1)//n)*k,p) for k in range(n)})
    etas=[sum(cmath.exp(2j*math.pi*(b*y%p)/p) for y in sub) for b in range(p)]
    return etas

# Odd-moment identity: sum over ALL b (including b=0) of eta_b^{2k+1} = -n^{2k} ?
# (real part; eta_0 = n contributes n^{2k+1})
print("=== odd-moment identity: sum_b eta_b^{2k+1} =?= -n^{2k}  (the claim) ===")
print(f"{'p':>5}{'n':>4}{'2k+1':>5} | {'sum eta^odd (Re)':>18} {'-n^{2k}':>10} {'match':>6}")
for p,n in [(73,8),(97,4),(257,8),(257,16)]:
    if (p-1)%n: continue
    etas=periods(p,n)
    for k in [1,2]:
        odd=2*k+1
        s=sum(e**odd for e in etas)  # all b
        claim=-(n**(2*k))
        print(f"{p:>5}{n:>4}{odd:>5} | {s.real:>18.3f} {claim:>10d} {str(abs(s.real-claim)<1e-3 and abs(s.imag)<1e-3):>6}")

# The above uses sum over all b. Power-sum of eigenvalues of the Paley/Cayley graph =
# trace of adjacency^odd = #closed walks. eta_b are eigenvalues. So this is an exact
# graph-theoretic trace identity. Let me ALSO try sum over b!=0 (the relation count).
print("\n=== sum over b!=0 (subtract eta_0^odd = n^odd) ===")
for p,n in [(73,8),(97,4),(257,8)]:
    if (p-1)%n: continue
    etas=periods(p,n)
    for k in [1,2]:
        odd=2*k+1
        s=sum(etas[b]**odd for b in range(1,p))
        # = -n^{2k} - n^{odd}
        claim=-(n**(2*k)) - n**odd
        print(f"  p={p} n={n} odd={odd}: sum_b!=0 eta^odd = {s.real:.2f}, predict -n^2k-n^odd={claim}, match={abs(s.real-claim)<1e-2}")
