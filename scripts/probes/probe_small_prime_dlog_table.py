# Full discrete logarithms modulo p-1 of zeta^a - zeta^b for a small prime p = 1 mod N (exact additive keys).
import sys
p=int(sys.argv[1]); N=int(sys.argv[2])
assert (p-1)%N==0 and all(p%q for q in range(2,int(p**0.5)+1))
def order_ok(g):
    m=p-1; q=2
    while q*q<=m:
        if m%q==0:
            if pow(g,(p-1)//q,p)==1: return False
            while m%q==0: m//=q
        q+=1
    return m==1 or pow(g,(p-1)//m,p)!=1
g=2
while not order_ok(g): g+=1
log={}; v=1
for e in range(p-1): log[v]=e; v=v*g%p
zeta=pow(g,(p-1)//N,p); pts=[pow(zeta,i,p) for i in range(N)]
with open(sys.argv[3],"w") as f:
    f.write("%d %d\n"%(N,p-1))
    for a in range(N):
        f.write(" ".join(str(log[(pts[a]-pts[b])%p]) if a!=b else "0" for b in range(N))+"\n")
