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
def addE_Fp(S,p):
    cc=Counter()
    for a in S:
        for b in S: cc[(a+b)%p]+=1
    return sum(v*v for v in cc.values())

# PROBE 6: characterize the actual char-p reach (r=2) law. Linear in n?
print("=== PROBE 6: r=2 char-p reach law (smallest p with E_2=char0) ===")
print(f"{'n':>4}{'char0':>8}{'reach p':>10}{'p/n':>8}{'note':>20}")
prev=None
for n in [4,8,16,32,64]:
    char0 = 3*n*n-3*n if n%2==0 else 2*n*n-n
    first=None
    for p in range(5, 60000):
        if not is_prime(p) or (p-1)%n: continue
        S=mu_n_Fp(p,n)
        if S is None or len(S)!=n: continue
        if addE_Fp(S,p)==char0:
            first=p;break
    if first:
        # the reach p must be > the cyclotomic-prime threshold? check p vs n^2
        note = ""
        print(f"{n:>4}{char0:>8}{first:>10}{first/n:>8.1f}{note:>20}")

# PROBE 7: Is the actual reach simply "first prime p with 2n | p-1 and no
#  SHORT parallelogram"? The Sidon failure mode is u=1 in BGK (2^n=1 mod p),
#  i.e. char | 2^n-1 (Mersenne).  Check: is the reach governed by avoiding
#  small Mersenne/cyclotomic factors, NOT by the (2r)^phi(n) norm bound?
print()
print("=== PROBE 7: failure mode = char | 2^n - 1 (Mersenne), the REAL threshold ===")
for n in [4,8,16,32]:
    char0 = 3*n*n-3*n if n%2==0 else 2*n*n-n
    # smallest prime p with n|p-1 where E > char0 (a defect survives)
    bad=[]
    for p in range(5,3000):
        if not is_prime(p) or (p-1)%n: continue
        S=mu_n_Fp(p,n)
        if S is None or len(S)!=n: continue
        if addE_Fp(S,p)>char0:
            # is p a divisor of 2^n-1 or 2^k-1 for k|n?
            mers = (pow(2,n,p)==1)
            bad.append((p,addE_Fp(S,p),mers))
    print(f" n={n}: defect primes (p,E,2^n=1modp): {bad[:6]}")
