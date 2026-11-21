# Four codewords of RS[32,16] on mu_32 over F_p within distance 10 of one word (octagon lift, s=4).
import sys, itertools
p=int(sys.argv[1]); N=32; s=4
c=2
while pow(c,(p-1)//2,p)!=p-1: c+=1
zeta=pow(c,(p-1)//N,p); pts=[pow(zeta,i,p) for i in range(N)]
u=pow(zeta,s,p)  # primitive 8th root; point zeta^j lies over u^(j mod 8)
inv=lambda a: pow(a,p-2,p)
base=[lambda y:0,
      lambda y:(y+1)*(y+u)*(y+u*u)%p,
      lambda y:(y+1)*(y*y+u*u)%p,
      lambda y:(y*y+1)*(y+pow(u,3,p))%p]
norm=[1]+[inv(base[i](1)) for i in (1,2,3)]
heads=[lambda y,i=i:base[i](y)*norm[i]%p for i in range(4)]
wbase={0:1,1:u*u*(1+u)%p*inv((1+u*u)%p)%p}
# base sanity: each nonzero head agrees with the base word at 1 and u
assert all(heads[i](1)==1 and heads[i](u)==wbase[1] for i in (1,2,3))
# common vanisher: one point in each of the fibers over exponents 2,3,5
roots=[2,3,5]            # zeta^2, zeta^3, zeta^5 lie over u^2, u^3, u^5
V=lambda x: (x-pts[2])*(x-pts[3])*(x-pts[5])%p
word=[V(x)*wbase.get(j%8,0)%p for j,x in enumerate(pts)]
errs=[]
for i in range(4):
    cw=[V(x)*heads[i](pow(x,s,p))%p for x in pts]
    errs.append(sum(1 for a,b in zip(cw,word) if a!=b))
# distinctness and degree: heads are V(X)*f_i(X^4), degree <= 3+12 = 15; distinct since the cubics differ
vals=[tuple(V(x)*heads[i](pow(x,s,p))%p for x in pts) for i in range(4)]
print("error counts",errs,"distinct codewords",len(set(vals)))
