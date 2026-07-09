"""C048 fast variant: exact bad-scalar counts on small proper dyadic subgroups,
monomial X^k vs non-monomial far directions. Smaller q so it finishes fast."""
import itertools, random, math

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
    raise RuntimeError

def subgroup(q,n):
    assert (q-1)%n==0
    g=primitive_root(q); h=pow(g,(q-1)//n,q)
    elts=[]; x=1
    for _ in range(n): elts.append(x); x=(x*h)%q
    assert len(set(elts))==n
    return elts

def precompute_inv(q):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    return inv

def interp_eval_all(xs,ys,domain,q,inv):
    k=len(xs); out=[]
    for X in domain:
        acc=0
        for i in range(k):
            num=ys[i]; den=1
            for j in range(k):
                if j==i: continue
                num=(num*((X-xs[j])%q))%q
                den=(den*((xs[i]-xs[j])%q))%q
            acc=(acc+num*inv[den])%q
        out.append(acc)
    return out

def bad_count(domain,k,q,u0,u1,t,inv,ksubsets):
    n=len(domain)
    if t<=k: return q
    bad=set()
    for gamma in range(q):
        w=[(u0[i]+gamma*u1[i])%q for i in range(n)]
        ib=False
        for sub in ksubsets:
            xs=[domain[i] for i in sub]; ys=[w[i] for i in sub]
            vals=interp_eval_all(xs,ys,domain,q,inv)
            if sum(1 for i in range(n) if vals[i]==w[i])>=t:
                ib=True; break
        if ib: bad.add(gamma)
    return len(bad)

def is_in_rs(domain,k,q,u,inv):
    n=len(domain)
    xs=[domain[i] for i in range(k)]; ys=[u[i] for i in range(k)]
    vals=interp_eval_all(xs,ys,domain,q,inv)
    return all(vals[i]==u[i] for i in range(n))

def mono(domain,a,q): return tuple(pow(x,a,q) for x in domain)

def run(q,n,k,deltas,n_random=24,seed=1,n_u0=5):
    domain=subgroup(q,n); inv=precompute_inv(q); rng=random.Random(seed)
    ksub=list(itertools.combinations(range(n),k))
    beta=math.log(q)/math.log(n)
    print(f"=== q={q} n={n} k={k} beta={beta:.2f} n<sqrt(q)={n<math.sqrt(q)} (proper dyadic) ===")
    u1m=mono(domain,k,q); assert not is_in_rs(domain,k,q,u1m,inv)
    for delta in deltas:
        t=max(1,math.ceil((1-delta)*n))
        if t<=k: print(f"  delta={delta}: t={t}<=k skip"); continue
        mvals=[]; ovals=[]
        for _ in range(n_u0):
            u0=tuple(rng.randrange(q) for _ in range(n))
            m=bad_count(domain,k,q,u0,u1m,t,inv,ksub); mvals.append(m)
            best=-1; bd=None
            cand=[("rand",tuple(rng.randrange(q) for _ in range(n))) for _ in range(n_random)]
            cand+=[(f"X^{a}",mono(domain,a,q)) for a in range(k,k+n)]
            for _ in range(n_random//2):
                w=[0]*n; i=rng.randrange(n); j=rng.randrange(n)
                w[i]=rng.randrange(1,q); w[j]=rng.randrange(1,q); cand.append(("2sparse",tuple(w)))
            for desc,u1 in cand:
                if is_in_rs(domain,k,q,u1,inv): continue
                bc=bad_count(domain,k,q,u0,u1,t,inv,ksub)
                if bc>best: best=bc; bd=desc
            ovals.append((best,bd))
        mmax=max(mvals); omax=max(o[0] for o in ovals)
        print(f"  delta={delta} (agree>={t}/{n}): monomial max={mmax}  non-mono max={omax}  "
              f"-> {'NON-MONO BEATS' if omax>mmax else 'mono>=others'}")
        for i in range(n_u0):
            m=mvals[i]; (o,d)=ovals[i]
            mk=f"  <<< {d} beats" if o>m else ""
            print(f"      u0#{i}: mono={m} other={o}({d}){mk}")

if __name__=="__main__":
    # n=8, q=257 (256=2^8): proper dyadic subgroup, beta=2.67, n=8<sqrt257=16
    run(257,8,2,[0.625,0.75],n_random=24,seed=1,n_u0=6)
    print()
    # n=16, q=257 (16|256): proper dyadic, beta=log_16(257)=2.0
    run(257,16,3,[0.6875,0.75],n_random=20,seed=3,n_u0=4)
