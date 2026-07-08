import math
isqrt=math.isqrt
# family: s=isqrt((q-16)//23), m=4s, J=s+3, D=(q-16)//4, b=isqrt(23q), bigB4=7b, K4=34^2=1156
# checks for all q ≡ 1 mod 4 (odd), q in range:
#  (a) count: m(D+4m+J) < 4J(D+1)
#  (b) indep: 4D+15 < q
#  (c) m<q, s>=1
#  (d) fold-admissibility (Nat): 4*Dtot4 <= m*(bigB4 + q - 3), Dtot4=5(m+3e)+D+q(J-1), e=(q-1)//4
#  (e) bigB4^2 <= 1156*q
failA=[];failD=[];failE=[]
q0_ok_from=None; last_bad=0
for q in range(17, 3000002, 4):
    s=isqrt((q-16)//23)
    if s==0: last_bad=q; continue
    m=4*s; J=s+3; D=(q-16)//4; e=(q-1)//4; b=isqrt(23*q); B=7*b
    if not (m*(D+4*m+J) < 4*(J*(D+1))): failA.append(q); last_bad=q; continue
    if not (4*D+15<q and m<q): last_bad=q; continue
    Dtot=5*(m+3*e)+D+q*(J-1)
    if not (4*Dtot <= m*(B+q-3)): failD.append(q); last_bad=q; continue
    if not (B*B <= 1156*q): failE.append(q); last_bad=q; continue
print("last bad q:", last_bad, "#failA",len(failA),"#failD",len(failD),"#failE",len(failE))
print("failA sample",failA[:5],failA[-5:] if failA else "")
print("failD sample",failD[:5],failD[-5:] if failD else "")
# trivial-branch coverage: need last_bad <= 34^2=1156
