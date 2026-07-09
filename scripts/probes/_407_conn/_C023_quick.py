import itertools, math, sys
def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1):continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1:break
        else:return False
    return True
def prime_1_mod_n(n,beta):
    lo=int(n**beta); lo+=(1-lo)%n; p=lo
    while True:
        if is_prime(p) and ((p-1)&(p-2))!=0: return p
        p+=n
def factorize(m):
    fs=set();d=2
    while d*d<=m:
        while m%d==0:fs.add(d);m//=d
        d+=1
    if m>1:fs.add(m)
    return fs
def order_n_gen(p,n):
    fac=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in fac): return pow(h,(p-1)//n,p)
def esym_all(S,tm,p):
    e=[0]*(tm+1);e[0]=1
    for x in S:
        for j in range(min(tm,len(e)-1),0,-1):
            e[j]=(e[j]+e[j-1]*x)%p
    return e
n=16; beta=4.0
p=prime_1_mod_n(n,beta); g=order_n_gen(p,n)
powg=[pow(g,i,p) for i in range(n)]
print(f"n={n} q={p} beta={math.log(p)/math.log(n):.2f} g={g}", flush=True)
for rho in (0.25,0.5):
    k=int(round(rho*n))
    print(f" rho={rho} k={k}", flush=True)
    for t in range(1,n-k+1):
        a=k+t
        if math.comb(n,a)>3_000_000: continue
        gcd=math.gcd(t,n); unit=n//gcd
        img=set()
        for S in itertools.combinations(range(n),a):
            vals=[powg[j] for j in S]
            e=esym_all(vals,t,p)
            if all(e[j]==0 for j in range(1,t)): img.add(e[t])
        nb=len(img)
        gt=pow(g,t,p)
        closed=all(((x*gt)%p) in img for x in img)
        orb = nb/unit
        print(f"  t={t} a={a} delta={1-a/n:.3f} gcd={gcd} unit={unit} #lacBad={nb} orbits={orb} mult={nb%unit==0} closed={closed} par={'even' if t%2==0 else 'odd'}", flush=True)
