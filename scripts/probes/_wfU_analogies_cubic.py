import cmath, math
def primitive_root(p):
    phi=p-1; fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fac): return g
def periods(p,n):
    g=primitive_root(p); sub=sorted({pow(g,((p-1)//n)*k,p) for k in range(n)})
    return [sum(cmath.exp(2j*math.pi*(b*y%p)/p) for y in sub) for b in range(p)]

# cubic case: sum_{b!=0} eta_b^3 = #{(a,b,c) in mu_n^3: a+b+c=0} * p / ??? 
# Actually trace of A^3 / closed walks. Let's just see if sum_{b!=0} eta_b^3 = -n^3 generally
print("=== sum_{b!=0} eta_b^3 across many (p,n) — is it always -n^3? ===")
for p in [17,41,73,89,97,113,193,257,337,769]:
    for n in [4,8,16]:
        if (p-1)%n: continue
        etas=periods(p,n)
        s=sum(etas[b]**3 for b in range(1,p)).real
        # The number of additive triples summing to 0 in mu_n:
        sub=set(); g=primitive_root(p)
        sub={pow(g,((p-1)//n)*k,p) for k in range(n)}
        triples=sum(1 for a in sub for b in sub for c in sub if (a+b+c)%p==0)
        # sum_b eta_b^3 (all b) = p * triples (since (1/p)sum eta^3 e^{...}=count); 
        # all-b sum eta^3 = p*triples? check
        sall=sum(e**3 for e in etas).real
        print(f"  p={p:>4} n={n:>3}: sum_b!=0 eta^3={s:>9.1f}  -n^3={-n**3:>7}  | all-b eta^3={sall:>9.1f}  p*triples={p*triples:>7}")
