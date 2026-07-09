#!/usr/bin/env python3
"""
C094_house_exact.py  (#407, C094)  -- pin the EXACT constants.

We test the headline house formula from RESEARCH_SYNTHESIS_407_TANGENT.md sec3:
    B^2 = n + (sqrt(p)/m) * max_b | Sum_{h!=0} unit_h * T_h * chi^h(b) |,  unit_h = conj(tau_h)/sqrt(p)
in its EXACT per-b form (before the max):
    |eta_b|^2  ?=  n + (sqrt(p)/m) * Re S_b,     S_b = Sum_{h!=0} unit_h T_h chi^h(b).
i.e. claim:  c1 = m/sqrt(p),  c0 = n,  in  S_b.real = c1*|eta_b|^2 - c0   <=>  |eta_b|^2 = n + (sqrt p/m) S_b.

Also report whether the FULL identity (I2) and this tangent route give the SAME spectrum:
    From I2: |eta_b|^2 = (1/m^2) sum_h chi^h(b) A_h.  Split off h=0 term A_0 = sum_j|tau_j|^2 = (m-1)p+1.
    |eta_b|^2 = A_0/m^2 + (1/m^2) sum_{h!=0} chi^h(b) A_h.
    Using A_h = m chi^h(-1) tau_{-h} T_h (I3):
    |eta_b|^2 = A_0/m^2 + (1/m) sum_{h!=0} chi^h(-1) chi^h(b) tau_{-h} T_h.
    chi^h(-1)chi^h(b)=chi^h(-b).  And tau_{-h} relates to unit_h how?  We DIRECTLY measure
    the multiplier k_b so that  |eta_b|^2 - A_0/m^2 == k * (sqrt p/m) Re S_b  -- fit one global k.
"""
import cmath, math, sympy

def primitive_root(p): return int(sympy.primitive_root(p))

def run(p, n):
    m = (p-1)//n
    g = primitive_root(p)
    def psi(x): return cmath.exp(2j*math.pi*(x%p)/p)
    dlog=[0]*p; cur=1
    for k in range(p-1): dlog[cur]=k; cur=(cur*g)%p
    def chi_pow(j,x):
        x%=p
        if x==0: return 0.0
        return cmath.exp(2j*math.pi*(j*dlog[x])/m)
    mu=[pow(g,(m*t)%(p-1),p) for t in range(n)]
    tau=[sum(chi_pow(j,x)*psi(x) for x in range(1,p)) for j in range(m)]
    def eta(c):
        b=pow(g,c,p); return sum(psi((b*w)%p) for w in mu)
    etas=[eta(c) for c in range(m)]
    def T(h): return sum(chi_pow(h,(1-w)%p) for w in mu)
    Th=[T(h) for h in range(m)]
    unit=[tau[h].conjugate()/math.sqrt(p) for h in range(m)]
    uT=[unit[h]*Th[h] for h in range(m)]
    def S(c):
        b=pow(g,c,p); return sum(uT[h]*chi_pow(h,b) for h in range(1,m))
    Sb=[S(c) for c in range(m)]
    e2=[abs(etas[c])**2 for c in range(m)]
    A0 = sum(abs(tau[j])**2 for j in range(m))   # = (m-1)p + 1

    # Test exact: |eta_b|^2  ==  A0/m^2 + (sqrt p / m) * Re S_b   ?  (k=1 prediction)
    pred = [A0/m**2 + (math.sqrt(p)/m)*Sb[c].real for c in range(m)]
    err_house_k1 = max(abs(e2[c]-pred[c]) for c in range(m))

    # also: |eta_b|^2 == n + (sqrt p / m) Re S_b ?  (the sec3 'n' constant form)
    pred_n = [n + (math.sqrt(p)/m)*Sb[c].real for c in range(m)]
    err_house_n = max(abs(e2[c]-pred_n[c]) for c in range(m))

    # average of |eta_b|^2 over ALL b incl 0 = A0/m^2 (Parseval) ; over b!=0 ~ n
    avg_e2_all = sum(e2)/m
    return dict(p=p,n=n,m=m,A0=A0,A0_over_m2=A0/m**2,avg_e2_all=avg_e2_all,
                err_house_k1=err_house_k1, err_house_n=err_house_n)

def find_primes(n,count,start=2):
    out=[];k=start
    while len(out)<count:
        p=k*n+1
        if sympy.isprime(p): out.append(p)
        k+=1
    return out

if __name__=="__main__":
    print("# C094 EXACT house-constant test\n")
    print(f"{'p':>7} {'n':>4} {'m':>5} | {'A0/m^2':>9} {'avg|eta|^2':>10} | {'err(k=1,A0/m^2)':>16} {'err(const=n)':>13}")
    for n in [8,16,32]:
        target=n**4
        ps=find_primes(n,60); cand=sorted(ps,key=lambda p:abs(p-target))
        chosen=[p for p in cand if p<=70000 and n<math.isqrt(p)][:2]
        for p in chosen:
            r=run(p,n)
            print(f"{r['p']:>7} {r['n']:>4} {r['m']:>5} | {r['A0_over_m2']:>9.4f} {r['avg_e2_all']:>10.4f} | "
                  f"{r['err_house_k1']:>16.2e} {r['err_house_n']:>13.2e}")
    print("\nIf err(k=1,A0/m^2) ~ 1e-10: |eta_b|^2 = A0/m^2 + (sqrt p/m) Re S_b EXACTLY")
    print("(b-DFT of unit_h*T_h IS the power spectrum, shift = Parseval mean A0/m^2=(m-1)p/m^2+1/m^2).")
