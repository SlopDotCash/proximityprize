"""
C081 follow-up: pin the growth of K = #bad-scalars/n on the e2=0 face, and the
window-interior emptiness. Decides O(1) (attack_plan) vs Theta(n)/wall.

We use the DEEP-INTERIOR small-width face a=4 (the comment-57 'w=4' deep face,
which they already found K=n/4-1=Theta(n)) and confirm independently with the
bad-SCALAR count (not just #orbits), plus the e2=0 'quadric' growth law fit,
across n=8,16,32,64 at proper dyadic subgroup primes.

Also: show the e2=0 face at the WINDOW INTERIOR (a ~ n/2) is governed by
Lam-Leung antipodal vanishing (empty for many rows), so a finite quadric
point-count argument cannot reach the prize radius.
"""
import itertools
from math import comb

def sieve(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(2,N+1) if s[i]]
P=sieve(6_000_000)

def find_prime(n,beta):
    t=int(round(n**beta)); best=None
    for q in P:
        if q<4*n or (q-1)%n: continue
        m=q-1
        while m%2==0: m//=2
        if m==1: continue
        if best is None or abs(q-t)<abs(best-t): best=q
        if q>t and best>=t: break
    return best

def mu(q,n,g):
    gen=pow(g,(q-1)//n,q); e=[]; x=1
    for _ in range(n): e.append(x); x=x*gen%q
    return e,gen

def e2(S,q):
    s1=0; s2=0
    for x in S:
        s2=(s2+s1*x)%q; s1=(s1+x)%q
    return s2
def e1(S,q):
    return sum(S)%q

def run():
    from sympy import primitive_root
    print("="*78)
    print("C081: K=#bad/n growth on e2=0 face (deep width-4) + window emptiness")
    print("="*78)
    print(f"{'n':>5} {'q':>9} {'a':>3} | {'#e2=0':>8} {'#bad':>7} {'Kfrac=#alpha/n':>14} "
          f"{'#e2=0 ratio prev':>16}")
    prev=None
    for n,beta in [(8,4),(16,4),(32,4),(64,4)]:
        q=find_prime(n,beta); g=primitive_root(q); elts,_=mu(q,n,g)
        a=4
        cnt=0; bad=0; alphas=set()
        for S in itertools.combinations(elts,a):
            if e2(S,q)!=0: continue
            cnt+=1
            v=e1(S,q)
            if v!=0:
                bad+=1; alphas.add((-pow(v,q-2,q))%q)
        ratio = (cnt/prev) if prev else float('nan')
        print(f"{n:>5} {q:>9} {a:>3} | {cnt:>8} {bad:>7} {len(alphas)/n:>14.3f} "
              f"{ratio:>16.3f}")
        prev=cnt
    print("\nGrowth diagnosis: if #e2=0 ratio ~ 4 per n-doubling => Theta(n^2);")
    print("  K=#bad/n then ~ Theta(n)  => NOT O(1) (attack_plan refuted at deep face).")

    # window interior emptiness (Lam-Leung)
    print("\n--- e2=0 face near window interior a ~ n/2 (feasible n) ---")
    print(f"{'n':>5} {'q':>9} {'a':>3} | {'#e2=0':>8} {'#bad(e1!=0)':>11}")
    for n,beta in [(8,4),(16,4)]:
        q=find_prime(n,beta); g=primitive_root(q); elts,_=mu(q,n,g)
        for a in range(4,n//2+3):
            if comb(n,a)>30_000_000: continue
            cnt=0; bad=0
            for S in itertools.combinations(elts,a):
                if e2(S,q)!=0: continue
                cnt+=1
                if e1(S,q)!=0: bad+=1
            print(f"{n:>5} {q:>9} {a:>3} | {cnt:>8} {bad:>11}")

if __name__=="__main__":
    run()
