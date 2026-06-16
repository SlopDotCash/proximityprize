"""C048 minimal decisive probe: at a WINDOW-INTERIOR radius on a proper dyadic subgroup,
is the basic monomial direction u1 = X^k (super-code RS[k+1]) the WORST far direction?
Compare X^k against: other monomials X^a (a>k), random far directions, and report the max.
Prints flushed; small q so it finishes in seconds."""
import itertools, random, math, sys

def primitive_root(q):
    fac=[]; m=q-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,q):
        if all(pow(g,(q-1)//p,q)!=1 for p in fac): return g

def subgroup(q,n):
    g=primitive_root(q); h=pow(g,(q-1)//n,q)
    e=[]; x=1
    for _ in range(n): e.append(x); x=(x*h)%q
    return e

def run(q,n,k,delta,seed=1,nrand=30,nu0=4):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    dom=subgroup(q,n); rng=random.Random(seed)
    ksub=list(itertools.combinations(range(n),k))
    t=max(1,math.ceil((1-delta)*n))
    beta=math.log(q)/math.log(n)
    print(f"q={q} n={n} k={k} delta={delta} t={t}/{n}  beta={beta:.2f}  proper-dyadic n<sqrt(q)={n<math.sqrt(q)}",flush=True)
    def interp_all(xs,ys):
        out=[]
        for X in dom:
            acc=0
            for i in range(len(xs)):
                num=ys[i]; den=1
                for j in range(len(xs)):
                    if j==i: continue
                    num=(num*((X-xs[j])%q))%q; den=(den*((xs[i]-xs[j])%q))%q
                acc=(acc+num*inv[den])%q
            out.append(acc)
        return out
    def badcount(u0,u1):
        bad=set()
        for gm in range(q):
            w=[(u0[i]+gm*u1[i])%q for i in range(n)]
            for sub in ksub:
                vals=interp_all([dom[i] for i in sub],[w[i] for i in sub])
                if sum(1 for i in range(n) if vals[i]==w[i])>=t: bad.add(gm); break
        return len(bad)
    def in_rs(u):
        vals=interp_all([dom[i] for i in range(k)],[u[i] for i in range(k)])
        return all(vals[i]==u[i] for i in range(n))
    def monw(a): return tuple(pow(x,a,q) for x in dom)
    Xk=monw(k); assert not in_rs(Xk)
    for u0i in range(nu0):
        u0=tuple(rng.randrange(q) for _ in range(n))
        bm=badcount(u0,Xk)
        best=-1; bd=None
        for a in range(k+1,n):  # higher monomials (also dilation-fixed)
            ua=monw(a)
            if in_rs(ua): continue
            b=badcount(u0,ua)
            if b>best: best=b; bd=f"X^{a}"
        for _ in range(nrand):
            ur=tuple(rng.randrange(q) for _ in range(n))
            if in_rs(ur): continue
            b=badcount(u0,ur)
            if b>best: best=b; bd="rand"
        flag = "  <<< NON-X^k DIRECTION BEATS X^k" if best>bm else ""
        print(f"  u0#{u0i}: X^k(RS[k+1]) bad={bm}   best other far dir bad={best} ({bd}){flag}",flush=True)

if __name__=="__main__":
    # rate 1/4-ish: n=8, k=2, window interior radius delta=0.625 (a=(1-delta)n=3 -> extremal exp 3, not k=2)
    run(257,8,2,0.625,seed=1,nrand=30,nu0=4)
    print()
    run(337,8,2,0.625,seed=2,nrand=30,nu0=4)  # n=8|336 (dyadic), q=337, beta=2.80, n<sqrt(q)
