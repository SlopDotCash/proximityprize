import cmath, math

def probe(p, n, deg):
    # find generator
    def isgen(g):
        s={1}; x=1
        for _ in range(p-2):
            x=x*g%p
            if x==1: return False
        return True
    g = next(g for g in range(2,p) if isgen(g))
    ep = lambda a: cmath.exp(2j*cmath.pi*(a%p)/p)
    G = sorted({pow(g,(p-1)//n*k,p) for k in range(n)})
    H = sorted({pow(g,deg*k,p) for k in range((p-1)//deg)})
    assert len(G)==n and len(H)==(p-1)//deg
    eta = lambda S,b: sum(ep(b*x) for x in S)
    M_H = max(abs(eta(H,c)) for c in range(1,p))
    bnd_MH = (1+(deg-1)*math.sqrt(p))/deg
    print(f"p={p} n={n} deg={deg}: M_H={M_H:.6f} <= (1+(deg-1)sqrt p)/deg={bnd_MH:.6f} : {M_H<=bnd_MH+1e-9}")
    bnd = n*bnd_MH   # = n/deg + n sqrt(p)(deg-1)/deg
    worst=0; ok=True
    for s0 in range(p):
        I = sum(eta(G,b).conjugate()*ep(b*s0) for b in H)
        # resummation identity check
        I2 = sum(eta(H,(s0-x)%p) for x in G)
        assert abs(I-I2)<1e-7, (s0,I,I2)
        if s0 in G:
            continue  # diagonal excluded (incl check s0=0 below stays in loop: 0 not in G)
        worst=max(worst,abs(I))
        if abs(I)>bnd+1e-7: ok=False; print("VIOLATION",s0,abs(I))
    print(f"  off-diagonal worst |I_H|={worst:.6f} <= n/deg+n*sqrt(p)*(deg-1)/deg={bnd:.6f} : {ok}")
    # s0=0 explicitly
    I0=sum(eta(G,b).conjugate() for b in H)
    print(f"  s0=0: |I_H(0)|={abs(I0):.6f} (covered, 0 not in mu_n)")
    # diagonal spike sanity
    s0=G[0]; I=sum(eta(G,b).conjugate()*ep(b*s0) for b in H)
    print(f"  diagonal s0={s0}: |I_H|={abs(I):.3f} vs |H|={(p-1)//deg} (spike, excluded)")

probe(41,8,2)
probe(41,8,4)
probe(97,8,2)
probe(97,16,4)
probe(113,16,2)
