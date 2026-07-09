import numpy as np
from collections import Counter

def is_prime(p):
    if p<2:return False
    for k in range(2,int(p**.5)+1):
        if p%k==0:return False
    return True
def mu_n_Fp(p,n):
    for cand in range(2,p):
        o=1;x=cand%p
        while x!=1: x=(x*cand)%p;o+=1
        if o%n==0:
            gen=pow(cand,o//n,p)
            S=set();x=1
            for _ in range(n):S.add(x);x=(x*gen)%p
            if len(S)==n: return sorted(S)
    return None
def eta(p,S,b):
    return sum(np.exp(2j*np.pi*(b*y % p)/p) for y in S)
def max_eta(p,S):
    return max(abs(eta(p,S,b)) for b in range(1,p))

# PROBE 8: Spectral<->arithmetic Paley transport:
#  B = max|eta_b| = non-principal eigenvalue of Cay(F_q, mu_n).
#  Ramanujan threshold = 2 sqrt(n). Gauss-period law B ~ sqrt(n log(m)), m=(p-1)/n.
#  Verify which holds and how B compares to BOTH thresholds.
print("=== PROBE 8: Paley spectral B vs Ramanujan 2sqrt(n) vs sqrt(n log m) ===")
print(f"{'p':>6}{'n':>4}{'m=(p-1)/n':>10}{'B':>9}{'2sqrt(n)':>10}{'sqrt(n*ln m)':>13}{'B/2sqn':>8}{'B/sqnlnm':>9}")
for (p,n) in [(73,8),(89,8),(113,8),(257,16),(353,16),(577,16),(1153,16),
              (193,32),(449,32),(577,32),(2113,32),(1217,64),(2689,64)]:
    if (p-1)%n: continue
    S=mu_n_Fp(p,n)
    if S is None or len(S)!=n: continue
    m=(p-1)//n
    B=max_eta(p,S)
    ram=2*np.sqrt(n)
    gp=np.sqrt(n*np.log(m)) if m>1 else float('nan')
    print(f"{p:>6}{n:>4}{m:>10}{B:>9.3f}{ram:>10.3f}{gp:>13.3f}{B/ram:>8.3f}{B/gp:>9.3f}")
