import numpy as np
from collections import Counter

# ============================================================
# PROBE 4: The SLACK in the resultant-threshold transport.
#  in-tree ManyTermResultant: char-0 E_r value guaranteed for p > (2r)^{phi(n)}.
#  Probe 3 showed n=8 reaches char-0 (168) at p=73 << threshold 256.
#  Find the ACTUAL char-p reach (smallest p with E_2=char0 value) and
#  compare to the (2r)^{phi(n)} threshold. The slack is the under-exploited
#  margin: the transport is provable far below the stated bound.
# ============================================================
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
def is_prime(p):
    if p<2:return False
    for k in range(2,int(p**.5)+1):
        if p%k==0:return False
    return True

print("=== PROBE 4: actual char-p reach vs (2r)^phi(n) threshold (r=2) ===")
print(f"{'n':>4}{'char0 E':>10}{'(2r)^phi':>12}{'1st p=char0':>14}{'slack ratio':>14}")
for n in [4,8,16,32]:
    char0 = 3*n*n-3*n if n%2==0 else 2*n*n-n
    thr=(2*2)**(n//2)
    first=None
    for p in range(5, 20000):
        if not is_prime(p): continue
        if (p-1)%n: continue
        S=mu_n_Fp(p,n)
        if S is None or len(S)!=n: continue
        E=addE_Fp(S,p)
        if E==char0:
            first=p; break
    if first:
        print(f"{n:>4}{char0:>10}{thr:>12}{first:>14}{thr/first:>14.1f}")
    else:
        print(f"{n:>4}{char0:>10}{thr:>12}{'>20000':>14}")

# ============================================================
# PROBE 5: connect to the EnergyDilationReduction divisibility n|E.
#   card_dvd_addEnergy: |H| | E(H).  Verify char-0 AND char-p both divisible by n.
#   This is a SYMMETRY transport: the dilation-invariance fingerprint survives the
#   char-0 -> char-p transport (a structural invariant preserved by reduction mod p).
# ============================================================
print()
print("=== PROBE 5: n | E(mu_n) invariant in BOTH char-0 and char-p ===")
for n in [4,8,16]:
    char0 = 3*n*n-3*n if n%2==0 else 2*n*n-n
    print(f" n={n}: char0 E={char0}, n|E? {char0%n==0}", end="  ")
    # char-p sample
    ok=True
    for p in range(5,500):
        if not is_prime(p) or (p-1)%n: continue
        S=mu_n_Fp(p,n)
        if S is None or len(S)!=n: continue
        E=addE_Fp(S,p)
        if E%n!=0: ok=False;print(f"VIOLATION p={p} E={E}",end="")
    print(f" | char-p all n|E: {ok}")
