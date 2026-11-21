# Filter-free brute force at lengths 8 and 16; expected output 19, 23, 7, 37 (matches the character filters).
import itertools
from probe_mu32_split_pencil_verify import P, gen, poly
def canon(T,N): return min(tuple(sorted((s*t+r)%N for t in T)) for r in range(N) for s in (1,-1))
def pencils(N,m):
    g=gen(N); pts=[pow(g,i,P) for i in range(N)]; out=0
    for B in itertools.combinations(range(N),m):
        if B[0]!=0: break
        if canon(B,N)!=B: continue
        pb=poly([pts[i] for i in B]); R=[i for i in range(N) if i not in B]; d={}
        for A in itertools.combinations(R,m):
            u=[(x-y)%P for x,y in zip(poly([pts[i] for i in A]),pb)]
            i=next(i for i,x in enumerate(u) if x); inv=pow(u[i],P-2,P)
            d.setdefault(tuple(x*inv%P for x in u),[]).append(A)
        for L in d.values():
            for A,C in itertools.combinations(L,2):
                if not set(A)&set(C): out+=1
    return out
def cycles(N):
    b=N//4; g=gen(N); pts=[pow(g,i,P) for i in range(N)]; out=0
    for T in itertools.combinations(range(N),b-1):
        if T[0]!=0: break
        if canon(T,N)!=T: continue
        R=[i for i in range(N) if i not in T]; d={}
        for A in itertools.combinations(R,b):
            v=[]
            for t in T:
                a=1
                for e in A: a=a*(pts[t]-pts[e])%P
                v.append(a)
            inv=pow(v[0],P-2,P); d.setdefault(tuple(x*inv%P for x in v),[]).append(A)
        for L in d.values():
            for A,C in itertools.combinations(L,2):
                if not set(A)&set(C): out+=1
    return out
print("N=8  deg2 pencils",pencils(8,2))
print("N=16 deg4 pencils",pencils(16,4),"deg3",pencils(16,3))
print("N=16 cycle triples",cycles(16))
