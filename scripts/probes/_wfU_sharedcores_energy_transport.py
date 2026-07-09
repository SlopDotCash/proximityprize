"""
[shared-cores] probe: verify the EnergyCharacterTransport two-way bridge that unifies
#389 (additive energy E) and #407 (character-sum house B). If true, a bound on ONE wall
transports to the other => they are the SAME wall.
Identity under test (addEnergy_le_of_charSum_bound):
    q*E(H) <= |H|^4 + B^2*(q*|H| - |H|^2)    where B = max_{b!=0}|eta_b|
E(H) = #{(a,b,c,d) in H^4 : a+b = c+d} additive quadruples (additive energy of H<=Z_q).
"""
import numpy as np, itertools

def factor_subgroup(p,n):
    def order(a):
        x=a%p;k=1
        while x!=1: x=(x*a)%p;k+=1
        return k
    g=next(c for c in range(2,p) if order(c)==p-1)
    h=pow(g,(p-1)//n,p); S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S

def add_energy(H,p):
    from collections import Counter
    cnt=Counter(((a+b)%p) for a in H for b in H)
    return sum(v*v for v in cnt.values())

def house_B(H,p):
    w=np.exp(2j*np.pi/p)
    return max(abs(sum(w**((b*x)%p) for x in H)) for b in range(1,p))

print("p     n   q*E         RHS=|H|^4+B^2(q|H|-|H|^2)   holds   E         |H|^4/q+B^2|H|")
for (p,n) in [(17,4),(41,8),(73,8),(97,8),(193,16),(257,16),(337,16)]:
    H=factor_subgroup(p,n); q=p
    E=add_energy(H,p); B=house_B(H,p)
    lhs=q*E
    rhs=n**4 + B**2*(q*n - n**2)
    holds = lhs <= rhs + 1e-6
    rhs2 = n**4/q + B**2*n
    print(f"{p:4d} {n:3d}  {lhs:10.1f}  {rhs:20.1f}     {str(holds):5s}   {E:8.1f}  {rhs2:10.2f} (E={E:.1f})")
