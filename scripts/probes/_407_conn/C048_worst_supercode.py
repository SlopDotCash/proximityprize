"""
C048 attack: does the Z/n dilation symmetry PIN the worst-case far super-code to RS[k+1]
(i.e. is the monomial direction u1 = X^k the WORST far direction)?

Connection chain:
  (1) [PROVEN in-tree] I(u0,u1;delta) <= |list(C + <u1>, delta n)|  for any far u1.
  (2) [PROVEN in-tree] dilation g.x fixes RS, so I is Z/n-invariant (cyclic symmetry).
  (3) [THE NEW CLAIM, attacked here] (2) "collapses the max over far directions to the
      SINGLE super-code RS[k+1]" -- worst far direction u1 == monomial X^k.

We compute EXACT bad-scalar counts on PROPER dyadic subgroups mu_n < F_q*:
  I(u0,u1;delta) = #{ gamma in F_q : some deg<k poly p has
                     |{i in mu_n : p(x_i) = u0_i + gamma*u1_i}| >= t },  t=ceil((1-delta)n).
Efficient list-decode: a deg<k poly agreeing on a t-set (t>=k) is the unique interpolant
through ANY k of those coords -> enumerate k-subsets, interpolate, count total agreement.

Compare monomial direction X^k against many non-monomial far directions u1.
If a non-monomial STRICTLY BEATS the monomial -> claim (3) REFUTED.
"""
import itertools, random, math
from functools import lru_cache

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
    return elts,h

def inv(a,q): return pow(a, q-2, q)

def interp_eval_all(xs, ys, domain, q):
    """Lagrange-interpolate the (deg < len(xs)) poly through (xs,ys); return its values on all of domain."""
    k=len(xs)
    out=[]
    for X in domain:
        acc=0
        for i in range(k):
            num=ys[i]; den=1
            for j in range(k):
                if j==i: continue
                num=(num*((X - xs[j])%q))%q
                den=(den*((xs[i]-xs[j])%q))%q
            acc=(acc + num*inv(den,q))%q
        out.append(acc)
    return out

def bad_count(domain,k,q,u0,u1,t):
    """#{gamma : some deg<k poly agrees with (u0+gamma*u1) on >= t coords}."""
    n=len(domain)
    if t<=k:
        # any k coords interpolate; with t<=k essentially every gamma is bad (poly always exists
        # on any k-subset). Treat agreement>=t with t<=k as: there's a deg<k poly through k pts,
        # which trivially agrees on >=k>=t. So all gamma bad. (degenerate, skip.)
        return q
    idx=list(range(n))
    bad=set()
    ksubsets=list(itertools.combinations(idx,k))
    for gamma in range(q):
        w=[(u0[i]+gamma*u1[i])%q for i in range(n)]
        is_bad=False
        for sub in ksubsets:
            xs=[domain[i] for i in sub]; ys=[w[i] for i in sub]
            vals=interp_eval_all(xs,ys,domain,q)
            agree=sum(1 for i in range(n) if vals[i]==w[i])
            if agree>=t:
                is_bad=True; break
        if is_bad: bad.add(gamma)
    return len(bad)

def is_in_rs(domain,k,q,u):
    """u in RS[k]? interpolate deg<k through first k coords; check it matches all coords."""
    n=len(domain)
    xs=[domain[i] for i in range(k)]; ys=[u[i] for i in range(k)]
    vals=interp_eval_all(xs,ys,domain,q)
    return all(vals[i]==u[i] for i in range(n))

def monomial_word(domain,a,q): return tuple(pow(x,a,q) for x in domain)

def run(q,n,k,delta_list,n_random=30,seed=1,n_u0=5):
    domain,h=subgroup(q,n); rng=random.Random(seed)
    beta=math.log(q)/math.log(n)
    print(f"=== q={q} n={n} k={k}  beta=log_n(q)={beta:.2f}  n<sqrt(q)={n<math.sqrt(q)}  (proper dyadic subgroup) ===")
    u1_mono=monomial_word(domain,k,q)
    assert not is_in_rs(domain,k,q,u1_mono),"X^k must be far"
    for delta in delta_list:
        t=math.ceil((1-delta)*n); t=max(t,1)
        if t<=k:
            print(f"  delta={delta}: t={t}<=k={k} degenerate, skipping"); continue
        any_beat=False
        mono_vals=[]; other_vals=[]
        for _ in range(n_u0):
            u0=tuple(rng.randrange(q) for _ in range(n))
            mono=bad_count(domain,k,q,u0,u1_mono,t)
            mono_vals.append(mono)
            best=-1; bestdesc=None
            cand=[]
            for _ in range(n_random): cand.append(("rand",tuple(rng.randrange(q) for _ in range(n))))
            for a in range(k,k+n): cand.append((f"X^{a}",monomial_word(domain,a,q)))  # other dilation-fixed
            for _ in range(n_random//2):
                w=[0]*n; i=rng.randrange(n); j=rng.randrange(n)
                w[i]=rng.randrange(1,q); w[j]=rng.randrange(1,q); cand.append(("2sparse",tuple(w)))
            for desc,u1 in cand:
                if is_in_rs(domain,k,q,u1): continue
                bc=bad_count(domain,k,q,u0,u1,t)
                if bc>best: best=bc; bestdesc=desc
            other_vals.append((best,bestdesc))
            if best>mono: any_beat=True
        mono_max=max(mono_vals); oth_max=max(o[0] for o in other_vals)
        verdict = "NON-MONO STRICTLY BEATS monomial" if oth_max>mono_max else "monomial >= all tested others"
        print(f"  delta={delta} (agree>= {t}/{n}): monomial max bad={mono_max}, non-mono max bad={oth_max}  -> {verdict}")
        for i in range(n_u0):
            mo=mono_vals[i]; (oth,desc)=other_vals[i]
            mark = f"   <<< {desc} beats ({oth}>{mo})" if oth>mo else ""
            print(f"      u0#{i}: mono={mo}  best_other={oth}({desc}){mark}")

if __name__=="__main__":
    # n=8, q=1009 (1008=2^4*3^2*7, 8|1008), beta=3.32, n<<sqrt(q)~31.8. k=2 (RS dim 2).
    run(1009,8,2,[0.625,0.75],n_random=30,seed=1,n_u0=5)
    print()
    # second proper subgroup: n=8, q=2017 (2016=2^5*63), beta=log_8(2017)=3.66
    run(2017,8,2,[0.625,0.75],n_random=24,seed=2,n_u0=4)
