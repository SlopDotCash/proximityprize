import cmath, math, random
random.seed(21)

def find_gen(p):
    for g in range(2, p):
        s=set(); x=1
        for _ in range(p-1):
            x=x*g%p; s.add(x)
        if len(s)==p-1: return g

def dlog_table(p,g):
    t={}; x=1
    for k in range(p-1):
        t[x]=k; x=x*g%p
    return t

def run(p,n,orders):
    g=find_gen(p); dl=dlog_table(p,g)
    G=[pow(g,(p-1)//n*i,p) for i in range(n)]  # mu_n
    res={}
    for d in orders:
        chi=lambda a,d=d: 0 if a%p==0 else cmath.exp(2j*math.pi*(dl[a%p]%d)/d*( (p-1)//(p-1) )) if False else cmath.exp(2j*math.pi*dl[a%p]/d) if False else None
        # chi of exact order d: chi(g^k)=e^{2pi i k/d}; needs d | p-1
        def chi(a,d=d):
            a%=p
            if a==0: return 0
            return cmath.exp(2j*math.pi*(dl[a]%d)/d)
        # fourth moment
        M=0.0
        for t in range(p):
            T=sum(chi(t-x) for x in G)
            M+=abs(T)**4
        ratio=M/(n*n*p)
        # identity + per-tuple check on random tuples
        maxbad=0.0; idmax=0.0
        for _ in range(300):
            x1,x2,y1,y2=[random.choice(G) for _ in range(4)]
            S=sum(chi(t-x1)*chi(t-x2)*chi(t-y1).conjugate()*chi(t-y2).conjugate() for t in range(p))
            u,v,w=(y2-x1)%p,(y2-x2)%p,(y2-y1)%p
            TS=sum(chi((u*s+1)*(v*s+1)%p)*chi((w*s+1)%p).conjugate() for s in range(p))
            idmax=max(idmax,abs(S-(TS-1)))
            pm=(x1==y1 and x2==y2) or (x1==y2 and x2==y1)
            deg2 = pm or (d==2 and x1==x2 and y1==y2)
            if not deg2:
                maxbad=max(maxbad,abs(S)/math.sqrt(p))
        res[d]=(ratio,idmax,maxbad)
    return res

for (p,n) in [(4177,8),(65537,16) if False else (12289,8),(65537,16)]:
    orders=[d for d in [2,4,8,16] if (p-1)%d==0]
    # ensure n | p-1
    if (p-1)%n: continue
    r=run(p,n,orders)
    for d,(ratio,idmax,mb) in r.items():
        print(f"p={p} n={n} d={d}: 4thmom/(n^2 p)={ratio:.3f}  identity_err={idmax:.2e}  max|S|/sqrt(p) nondeg={mb:.3f}")
