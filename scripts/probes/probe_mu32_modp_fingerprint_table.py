# Additive 64-bit fingerprints of zeta^a - zeta^b in F_p^*: discrete log in the 2-Sylow subgroup, reduced mod 2^64.
# ell(xy) = ell(x) + ell(y) mod 2^64, so equal products have equal fingerprint sums (necessary condition in F_p).
import sys
p=int(sys.argv[1]); N=int(sys.argv[2])
def isprime(n):
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53):
        if n%a==0: return n==a
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
assert isprime(p) and (p-1)%N==0
odd=p-1; e=0
while odd%2==0: odd//=2; e+=1
assert e>=24  # named production primes have 2-adic valuation 36 and 30
c=2
while pow(c,(p-1)//2,p)!=p-1: c+=1
h=pow(c,odd,p)                      # order 2^e
zeta=pow(c,(p-1)//N,p)              # order N
assert pow(zeta,N//2,p)==p-1
hinv=pow(h,p-2,p)
def dlog2(x):                       # full log_h(x^odd) in Z/2^e
    y=pow(x,odd,p); k=0
    for i in range(e):
        # bit i: (y*h^-k)^(2^(e-1-i)) == -1 ?
        t=pow(y*pow(hinv,k,p)%p,1<<(e-1-i),p)
        if t==p-1: k|=1<<i
        else: assert t==1
    return k
pts=[pow(zeta,i,p) for i in range(N)]
with open(sys.argv[3],"w") as f:
    f.write("%d %d\n"%(N,e))
    for a in range(N):
        f.write(" ".join(str(dlog2((pts[a]-pts[b])%p) if a!=b else 0) for b in range(N))+"\n")
print("p bits",p.bit_length(),"2-adic valuation of p-1:",e,"zeta",zeta)
