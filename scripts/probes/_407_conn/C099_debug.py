"""Debug: reconcile the two inert computations. The 'over F_p' scan used
rep_count_inert_over_Fp which embeds t as (t,0). The 'over F_p^2*' scan should
include those same points. Why does fixed give 8 but all give 2?

Resolution hypothesis: BUG in rep_count_inert_over_Fp -- it computes mu_n IN F_p
incorrectly? No. Let me recompute carefully and find an actual t in F_p with r(t)=8,
then check it against the F_{p^2} scan. Either the lemma is FALSE (unlikely, it's a
clean proof) or my prime-field embedding hits t=0 / the subgroup is wrong.
"""
import sympy
from sympy import isprime

p, n = 71, 8
assert (p+1) % n == 0

# nonresidue
d = None
for cand in range(2, p):
    if pow(cand, (p-1)//2, p) == p-1:
        d = cand; break
print("nonresidue d =", d)

def mul(u, v):
    a,b=u; c,e=v
    return ((a*c+b*e*d)%p, (a*e+b*c)%p)
def mpow(u,k):
    r=(1,0)
    while k:
        if k&1: r=mul(r,u)
        u=mul(u,u); k>>=1
    return r

order=p*p-1
gen=None
for ga in range(2,p):
    for gb in range(1,p):
        g=(ga,gb); ok=True
        for q in sympy.factorint(order):
            if mpow(g, order//q)==(1,0): ok=False;break
        if ok:
            gen=mpow(g, order//n); break
    if gen: break
S=set(); x=(1,0)
for _ in range(n): S.add(x); x=mul(x,gen)
print("mu_n =", sorted(S))
# verify y^n=1 for all
for y in S:
    assert mpow(y,n)==(1,0)
print("all y^n=1 OK, |S|=",len(S))

def sub(u,v):
    a,b=u;c,e=v
    return ((a-c)%p,(b-e)%p)

# scan t over F_p embedded
maxfixed=0; argf=None
for t in range(1,p):
    T=(t,0); c=0
    for y in S:
        if sub(T,y) in S: c+=1
    if c>maxfixed: maxfixed=c; argf=t
print("max over t in F_p (t!=0):", maxfixed, "at t=",argf)

# scan over ALL F_{p^2}*
maxall=0; arga=None
for ta in range(p):
    for tb in range(p):
        if (ta,tb)==(0,0): continue
        T=(ta,tb); c=0
        for y in S:
            if sub(T,y) in S: c+=1
        if c>maxall: maxall=c; arga=(ta,tb)
print("max over t in F_{p^2}*:", maxall, "at t=",arga)

# show the representations for the F_p witness
if argf is not None:
    T=(argf,0)
    reps=[(y, sub(T,y)) for y in S if sub(T,y) in S]
    print(f"\nt=({argf},0): {len(reps)} reps:")
    for y,z in reps:
        print("   ", y, "+", z, "  both in mu_n?", y in S, z in S)
