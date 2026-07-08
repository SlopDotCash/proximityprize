import math
def isqrt(n): return math.isqrt(n)
# family: s=isqrt((q-16)/24), m=4s, J=s+4, D=(q-16)/4  (Nat floor div)
# budgets to check (q ≡ 1 mod 4, q>16):
#  (i) count: m(D+4m+J) < 4J(D+1)
#  (ii) indep: 4D+15 < q
#  (iii) m<q, J>0
# excessNat: N := 4*(5*(m+3*e)+D+q*(J-1)) ; need N <= m*(q-3) + m*C4B  where C4B = c1*b + c2, b=isqrt(24q)
# i.e. fold bound 4B - q + 3 <= (c1 b + c2)/m ... actually excess = (N - m(q-3))/m ; want <= BigB/m*? mirror r23: budget form 4*Dtot' <= m*(B + q - 3) with B = bigB4
# try bigB4 = 30*isqrt(q) + const? or use b=isqrt(24q): excess*m <= ? Let's measure (N - m*(q-3))/b.
worst=0; worstq=None; fail=[]
qs=[q for q in range(17,400002) if q%4==1]
import random
qs += [65537, 2**20+9- (2**20+9)%4 +1]
for q in qs:
    e=(q-1)//4
    s=isqrt((q-16)//24); m=4*s; J=s+4; D=(q-16)//4
    if s==0: continue
    ok_i = m*(D+4*m+J) < 4*(J*(D+1))
    ok_ii = 4*D+15<q
    if not(ok_i and ok_ii and m<q): fail.append(q); continue
    N=4*(5*(m+3*e)+D+q*(J-1))
    exc=(N-m*(q-3))/m
    r=exc/math.sqrt(q)
    if r>worst: worst=r; worstq=q
print("worst excess/sqrt(q) =",worst,"at q=",worstq,"fails:",fail[:10],len(fail))
# check tail behavior
for q in [10007+2,100003- (100003%4)+1+4,1000003-(1000003%4)+1, 2**20+1- (2**20+1-1)%4]:
    if q%4!=1: continue
    e=(q-1)//4; s=isqrt((q-16)//24); m=4*s; J=s+4; D=(q-16)//4
    N=4*(5*(m+3*e)+D+q*(J-1)); exc=(N-m*(q-3))/m
    print(q, exc/math.sqrt(q))
