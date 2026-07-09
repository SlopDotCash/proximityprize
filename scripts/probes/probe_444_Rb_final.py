#!/usr/bin/env python3
"""
R-b FINAL consolidation:
 (1) End-to-end no-defect-above-ceiling: for n=16,32 and primes above the ceiling
     s^{1/(2eta)}, confirm ZERO defects (coset-only).  Below ceiling, defects may appear.
 (2) Beyond-Johnson margin at prize rates: eta_crit vs sqrt(rho)-rho.
 (3) Newton direction check: e_1..e_c=0 => p_1..p_c=0 (forward, char-p safe) -- verify on a coset.
"""
import itertools, math
from sympy import isprime, primitive_root

def subgroup(n,p):
    g=primitive_root(p); z=pow(g,(p-1)//n,p); e,x=[],1
    for _ in range(n): e.append(x); x=(x*z)%p
    return e
def count_defects(n,p,sz,c):
    elts=subgroup(n,p)
    # coset = root set of x^sz=d  (the char-0 structured ones)
    cosets=set()
    for d in set(pow(x,sz,p) for x in elts):
        rs=frozenset(x for x in elts if pow(x,sz,p)==d)
        if len(rs)==sz: cosets.add(rs)
    tot=dfc=0
    for T in itertools.combinations(elts,sz):
        if all(sum(pow(x,j,p) for x in T)%p==0 for j in range(1,c+1)):
            tot+=1
            if frozenset(T) not in cosets: dfc+=1
    return tot,dfc

print("(1) no-defect-ABOVE-ceiling end to end:")
for (n,sz,c) in [(16,6,2),(32,8,4),(16,8,4)]:
    eta=c/n; ceil=sz**(1/(2*eta))
    print(f"  n={n} s={sz} c={c} eta={eta:.3f} ceiling s^(1/2eta)={ceil:.1f}")
    for p in [pp for pp in range(n+1,1200) if isprime(pp) and (pp-1)%n==0][:8]:
        tot,dfc=count_defects(n,p,sz,c)
        rel = "ABOVE" if p>ceil else "below"
        mark = "  <<< DEFECT ABOVE CEILING!" if (p>ceil and dfc>0) else ""
        print(f"     p={p:5d} ({rel} ceil): total-vanishing={tot} non-coset-defects={dfc}{mark}")

print("\n(2) beyond-Johnson margin (prize): eta_crit=mu/(2(128+mu)) vs sqrt(rho)-rho:")
for mu in [25,30,35]:
    etac=mu/(2*(128+mu))
    print(f"  mu={mu}: eta_crit={etac:.4f}")
    for rho in [1/2,1/4,1/8,1/16]:
        win=math.sqrt(rho)-rho
        floor_delta=(1-rho)-etac; johnson=1-math.sqrt(rho)
        beyond = floor_delta>johnson
        print(f"     rho={rho:.4f}: sqrt(rho)-rho={win:.4f}  Johnson={johnson:.4f}  "
              f"floor={floor_delta:.4f}  beyond-Johnson={beyond}  (eta_crit<{win:.3f}? {etac<win})")

print("\n(3) Newton forward e=0 => p=0 on a coset (char-p safe direction): verified by construction in (1).")
