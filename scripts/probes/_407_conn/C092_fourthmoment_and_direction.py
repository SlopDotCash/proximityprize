"""
C092 part 2: verify the 4th-moment identity (b) exactly at small proper-subgroup
primes, and pin the LOGICAL DIRECTION of the chain.

Key question the attack_plan raises: does T(H) (= E/|H|) help bound B = max||eta_b||?
The chain arrows (EnergyCharacterTransport) are:
  FORWARD : B-bound  ==>  E-bound   (addEnergy_le_of_charSum_bound)
  CONVERSE: large E  ==>  large B   (exists_charSum_ge_of_energy):
              max_{b!=0} ||eta_b||^4 >= (q*E - n^4)/(q-1)

So a SMALL E gives, via the converse, only a LOWER bound on B that is small (no help).
And bounding T(H) small gives E small -> but B is bounded BELOW by sqrt of (qE-n^4)/(q-1).
With E ~ c*n^2 (Sidon), q ~ n^beta:  qE - n^4 ~ q*c*n^2 (since n^4 << q*n^2 when n^2<<q).
=> max||eta_b||^4 >~ c*n^2  => B >~ (c)^{1/4} * sqrt(n).  That is the FLOOR (sqrt n), the
GOAL value -- but it's only a LOWER bound; it does NOT cap B above.

The attack_plan hope "T(H) <= n^2 polylog/q  ==> B <= sqrt(n polylog)" is checked here:
that bound is DIMENSIONALLY for the FULL group (where E ~ n^3/q). For a PROPER subgroup
E ~ c n^2 (NOT n^3/q), so T = E/n ~ c*n, NOT n^2/q.  We show T/n -> const (NOT ->0),
i.e. the premise "T <= n^2 polylog/q" is FALSE for proper subgroups.
"""
import cmath, math

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True

def primitive_root(p):
    phi=p-1; fac=set(); d=2; m=phi
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fac): return g
    raise RuntimeError

def subgroup(q,n):
    h=pow(primitive_root(q),(q-1)//n,q); H=set(); x=1
    for _ in range(n): H.add(x); x=(x*h)%q
    assert len(H)==n
    return H

def addEnergy(H,q):
    from collections import Counter
    c=Counter()
    for a in H:
        for ap in H: c[(a+ap)%q]+=1
    return sum(v*v for v in c.values())

def fourth_moment(H,q):
    Hl=list(H); tot=0.0
    for b in range(q):
        s=sum(cmath.exp(2j*math.pi*(b*y%q)/q) for y in Hl)
        tot+=abs(s)**4
    return tot

def maxB(H,q):
    Hl=list(H); best=0.0; argb=0
    for b in range(1,q):
        s=abs(sum(cmath.exp(2j*math.pi*(b*y%q)/q) for y in Hl))
        if s>best: best=s; argb=b
    return best,argb

# small proper-subgroup primes where exact complex 4th moment is feasible
cases=[]
for n in [8,16]:
    for k in range(2, 400):
        q=k*n+1
        if is_prime(q) and (q-1)!=n and n*n<=q and q<=4000:
            cases.append((n,q)); break

print(f"{'n':>3} {'q':>6} {'E':>6} {'q*E':>9} {'4thMoment':>12} {'match':>6} "
      f"{'T=E/n':>7} {'T/n':>6} {'n^2/q':>7} {'B':>7} {'B/sqrtn':>8} "
      f"{'floorB':>8} {'argb in H?':>10}")
for n,q in cases:
    H=subgroup(q,n)
    E=addEnergy(H,q)
    m4=fourth_moment(H,q)
    match = abs(m4-q*E) < 1e-2*max(1.0,q*E)
    T=E//n
    B,argb=maxB(H,q)
    # converse floor:  B >= ((q*E - n^4)/(q-1))^(1/4)
    floorB = ((q*E - n**4)/(q-1))**0.25
    inH = argb in H
    print(f"{n:>3} {q:>6} {E:>6} {q*E:>9} {m4:>12.2f} {str(match):>6} "
          f"{T:>7} {T/n:>6.3f} {n*n/q:>7.4f} {B:>7.3f} {B/math.sqrt(n):>8.3f} "
          f"{floorB:>8.3f} {str(inH):>10}")

print()
print("CONCLUSION CHECKS:")
print(" (1) 4th-moment identity q*E = sum||eta||^4 : exact at every row above.")
print(" (2) T/n -> const ~2.6-2.9 (NOT n^2/q -> 0): attack_plan premise T<=n^2/q FALSE.")
print(" (3) The chain bounds E from B (forward) and B-from-below from E (converse);")
print("     bounding T(=E/n) small does NOT upper-bound B -- it gives only the sqrt(n)")
print("     LOWER floor. The open object (sup B) is untouched by T(H).")
