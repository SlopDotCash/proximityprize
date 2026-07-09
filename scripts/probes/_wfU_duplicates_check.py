import cmath, math, itertools
# ---- Probe 1: Parseval pigeonhole  max_b |eta_b|^2 >= |G|  (the two dup lemmas) ----
# eta_b = sum_{y in G} psi(b*y), psi primitive additive char of F_q (q prime), b ranges over F.
# Mean over b in F of |eta_b|^2 = |G| (Parseval) => exists b with |eta_b|^2 >= |G|.
def parseval(q, G):
    w = cmath.exp(2j*math.pi/q)
    vals=[]
    for b in range(q):
        s=sum(w**((b*y)%q) for y in G)
        vals.append(abs(s)**2)
    return sum(vals)/q, max(vals)
for q in [7,13,17,31]:
    # G = subgroup mu_n (multiplicative) of size n
    g=None
    for cand in range(2,q):
        order=1; x=cand%q
        while x!=1:
            x=(x*cand)%q; order+=1
        if order==q-1: g=cand; break
    for n in [d for d in range(2,q) if (q-1)%d==0]:
        G=set(pow(g,((q-1)//n)*k,q) for k in range(n))
        mean,mx=parseval(q,list(G))
        ok = mx >= len(G)-1e-9 and abs(mean-len(G))<1e-9
        print(f"q={q} n={len(G)}: Parseval mean={mean:.4f} (=|G|={len(G)}? {abs(mean-len(G))<1e-9})  max|eta|^2={mx:.4f}>=|G|? {mx>=len(G)-1e-9}")

print("---- Probe 2: additiveEnergy(mu_n over neg-closed) = 3n^2-3n (even) / 2n^2-n (odd) ----")
# additive energy E(G)=#{(a,b,c,d) in G^4 : a+b=c+d}. For neg-closed Sidon-mod-neg sets the KB formula.
def add_energy(G):
    from collections import Counter
    c=Counter()
    for a in G:
        for b in G:
            c[a+b]+=1
    return sum(v*v for v in c.values())
# Use roots of unity mu_n in C (char 0), neg-closed when n even.
for n in [4,6,8,10,12]:
    G=[cmath.exp(2j*math.pi*k/n) for k in range(n)]
    # round to avoid float key collisions: scale
    Gr=[(round(z.real,6),round(z.imag,6)) for z in G]
    from collections import Counter
    c=Counter()
    for a in Gr:
        for b in Gr:
            c[(round(a[0]+b[0],6),round(a[1]+b[1],6))]+=1
    E=sum(v*v for v in c.values())
    pred = 3*n*n-3*n  # even-parity KB formula
    print(f"n={n}: E={E}  3n^2-3n={pred}  match={E==pred}")
