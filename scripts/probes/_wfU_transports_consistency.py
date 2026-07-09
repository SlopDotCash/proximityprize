import numpy as np, itertools, math
from numpy.polynomial import polynomial as P

# ============================================================
# PROBE 1: consistency of the TWO energy->B routes at r=2.
#  Route A (EnergyCharacterTransport.sidon_order_of_sqrt_charSum):
#    from B = max|eta_b| <= C*sqrt(n), get E(G) <= (1+C^2) n^2   [4th moment]
#  Route B (GaussPeriodMomentBound, r=2):
#    GaussianEnergyBound: E_2(G) <= (2*2-1)!! * n^2 = 3 n^2
#    => |eta_b|^4 <= q * 3 * n^2 => B <= (3 q n^2)^{1/4}
#  These are the SAME 4th moment identity sum_b|eta_b|^4 = q E(G) read
#  in two directions. Verify numerically that E(G)=E_2(G) (the addEnergy
#  in EnergyCharacterTransport IS the r=2 rEnergy in GaussPeriodMomentBound),
#  and that both directions hold for actual mu_n subgroups.
# ============================================================

def mu_n(p, n):
    # multiplicative subgroup of order n in F_p^* (p prime, n | p-1)
    g = None
    for cand in range(2,p):
        # find element of order exactly n
        if pow(cand,(p-1)//1,p)==1:
            # order of cand
            o=1; x=cand%p
            while x!=1:
                x=(x*cand)%p; o+=1
            if o%n==0:
                gen=pow(cand,o//n,p)
                # verify order n
                oo=1;y=gen%p
                while y!=1:
                    y=(y*gen)%p; oo+=1
                if oo==n:
                    g=gen;break
    if g is None: return None
    S=set()
    x=1
    for _ in range(n):
        S.add(x); x=(x*g)%p
    return sorted(S)

def additive_energy(S,p):
    from collections import Counter
    c=Counter()
    for a in S:
        for b in S:
            c[(a+b)%p]+=1
    return sum(v*v for v in c.values())

def eta(p,S,b):
    # eta_b = sum_{y in S} exp(2 pi i b y / p)
    return sum(np.exp(2j*np.pi*(b*y % p)/p) for y in S)

def max_eta(p,S):
    return max(abs(eta(p,S,b)) for b in range(1,p))

print("=== PROBE 1: r=2 energy<->B route consistency ===")
print(f"{'p':>6}{'n':>4}{'E(G)':>8}{'q*E':>10}{'sum|eta|^4':>14}{'B=maxeta':>10}{'(3qn^2)^.25':>12}{'C^2=(E-n^4/q)/n^2':>18}")
for (p,n) in [(17,4),(17,8),(41,8),(73,8),(89,8),(97,8),(113,8),(257,16),(193,16)]:
    if (p-1)%n!=0: continue
    S=mu_n(p,n)
    if S is None or len(S)!=n: continue
    E=additive_energy(S,p)
    qE=p*E
    sB=sum(abs(eta(p,S,b))**4 for b in range(p))  # full sum incl b=0 gives n^4
    B=max_eta(p,S)
    routeB=(3*p*n**2)**0.25
    Csq=(E - n**4/p)/n**2   # from forward transport E <= n^4/q + B^2 n  => B^2 >= (E-n^4/q)/n
    print(f"{p:>6}{n:>4}{E:>8}{qE:>10}{sB:>14.2f}{B:>10.4f}{routeB:>12.4f}{Csq:>18.4f}")
